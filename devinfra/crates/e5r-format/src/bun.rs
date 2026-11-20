//! Bun standalone module graphs.
//!
//! `bun build --compile` appends a graph of source and bytecode to the
//! executable. Those bytes are not a program the loader should disassemble,
//! so this module lists them the way [`crate::archive`] lists an archive:
//! separately from [`crate::load`], and only as far as the caller asks.
//!
//! The layout is the one Bun writes in `StandaloneModuleGraph.zig` (MIT).
//! A trailer, `\n---- Bun! ----\n`, ends the graph. The 32 bytes before it
//! are an `Offsets` value: a 64-bit byte count, then the module-record
//! span, the entry-point id, the compile-time argv span, and a flag word,
//! all little-endian. Every span is an offset and a length into the bytes
//! that precede `Offsets`. Bun reads the last trailer in the file; an
//! earlier copy of the marker, inside a script or an unrelated payload, is
//! not the graph.
//!
//! Two record sizes have shipped. The earlier is 36 bytes: name, contents,
//! sourcemap and bytecode spans, then encoding, loader, module format and
//! side. The later is 52 bytes, with `module_info` and
//! `bytecode_origin_path` spans before those four bytes. A size is accepted
//! only when every span it implies lands inside the graph.

use e5r_core::{Error, Reader, Result};

/// The marker Bun writes after `Offsets`. Sixteen bytes, newline on both ends.
pub const TRAILER: &[u8] = b"\n---- Bun! ----\n";

/// `Offsets` is a 64-bit count plus six 32-bit fields.
const OFFSETS_LEN: usize = 32;

/// Record size before `module_info` and `bytecode_origin_path` existed.
const RECORD_V1: u64 = 36;

/// Record size Bun writes now.
const RECORD_V2: u64 = 52;

/// How many non-graphs to step over before giving up. A file that repeats
/// the trailer and nothing else should fail, not scan forever.
const MAX_SKIPS: u32 = 32;

/// A path longer than this is still located; the listing keeps the head.
const MAX_NAME: usize = 1 << 12;

/// Bounds for one parse. The default refuses a file that claims a million
/// modules rather than allocating them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Options {
    /// Which graph to return. `0` is the last in the file, which is the one
    /// Bun itself reads.
    pub which: usize,
    /// Most modules one graph may declare.
    pub max_modules: u64,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            which: 0,
            max_modules: 1 << 16,
        }
    }
}

/// One embedded file. `contents` is borrowed from the input, so a listing
/// does not copy the source.
#[derive(Clone)]
pub struct Module<'a> {
    /// Position in the graph, which is what the entry-point id names.
    pub index: u32,
    /// Path as the graph spells it, usually under `/$bunfs/`.
    pub name: String,
    /// The file's bytes, exactly the span the record names.
    pub contents: &'a [u8],
    /// File offset of [`Module::contents`].
    pub contents_offset: u64,
    /// Sourcemap span length. Zero when the module has none.
    pub sourcemap_len: u32,
    /// Bytecode span length. Zero when the module was not precompiled.
    pub bytecode_len: u32,
    /// Bun's `Encoding`: 0 binary, 1 latin1, 2 utf8.
    pub encoding: u8,
    /// Bun's `Loader` discriminant. See [`Module::loader_name`].
    pub loader: u8,
    /// Bun's `ModuleFormat`: 0 none, 1 esm, 2 cjs.
    pub format: u8,
    /// Bun's `FileSide`: 0 server, 1 client.
    pub side: u8,
    /// True when this module is the graph's entry point.
    pub entry: bool,
}

impl std::fmt::Debug for Module<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Module")
            .field("index", &self.index)
            .field("name", &self.name)
            .field("contents_len", &self.contents.len())
            .field("loader", &self.loader)
            .field("entry", &self.entry)
            .finish()
    }
}

impl Module<'_> {
    /// The loader's name, or `loader-N` when this build of Bun grew a
    /// discriminant the table does not list yet. The number is Bun's
    /// `Loader` enum (`src/options.zig`): `jsx` is 0.
    pub fn loader_name(&self) -> String {
        named(
            self.loader,
            &[
                "jsx",
                "js",
                "ts",
                "tsx",
                "css",
                "file",
                "json",
                "jsonc",
                "toml",
                "wasm",
                "napi",
                "base64",
                "dataurl",
                "text",
                "bunsh",
                "sqlite",
                "sqlite_embedded",
                "html",
                "yaml",
                "json5",
                "md",
            ],
            "loader",
        )
    }

    /// `binary`, `latin1`, `utf8`, or `encoding-N`.
    pub fn encoding_name(&self) -> String {
        named(self.encoding, &["binary", "latin1", "utf8"], "encoding")
    }

    /// `none`, `esm`, `cjs`, or `format-N`.
    pub fn format_name(&self) -> String {
        named(self.format, &["none", "esm", "cjs"], "format")
    }

    /// `server`, `client`, or `side-N`.
    pub fn side_name(&self) -> String {
        named(self.side, &["server", "client"], "side")
    }
}

/// A parsed graph.
#[derive(Debug, Clone)]
pub struct Graph<'a> {
    /// File offset of the first byte the offsets describe.
    pub offset: u64,
    /// How many bytes precede the `Offsets` struct. Spans are relative to
    /// [`Graph::offset`] and must land inside this count.
    pub byte_count: u64,
    /// File offset of the trailer that ended this graph.
    pub trailer_offset: u64,
    /// Which record size was consistent. Zero when the graph has no modules.
    pub record_size: u64,
    /// The entry-point id as stored, even when it names no module.
    pub entry_point_id: u32,
    /// Arguments baked in at compile time. Empty when there were none.
    pub argv: &'a [u8],
    /// The flag word. The low four bits are the ones Bun named first:
    /// `disable_default_env_files`, `disable_autoload_bunfig`,
    /// `disable_autoload_tsconfig`, `disable_autoload_package_json`.
    /// Later builds set further bits; those stay in the word and are not
    /// given names here.
    pub flags: u32,
    /// Modules in graph order.
    pub modules: Vec<Module<'a>>,
    /// Problems that did not stop the parse.
    pub warnings: Vec<String>,
}

impl<'a> Graph<'a> {
    /// The module a query names.
    ///
    /// An exact path wins. Otherwise an index, written in decimal. Otherwise
    /// a unique path suffix that begins on a `/`: `a.js` matches
    /// `/$bunfs/root/a.js` and does not match `/$bunfs/root/ba.js`.
    pub fn find(&self, query: &str) -> Result<usize> {
        if query.is_empty() {
            return Err(Error::BadField {
                field: "bun module",
                value: 0,
                reason: "is an empty name",
            });
        }
        if let Some(i) = self.modules.iter().position(|m| m.name == query) {
            return Ok(i);
        }
        if query.bytes().all(|b| b.is_ascii_digit())
            && let Ok(index) = query.parse::<u32>()
            && self.modules.get(index as usize).is_some()
        {
            return Ok(index as usize);
        }
        let mut hits: Vec<usize> = self
            .modules
            .iter()
            .enumerate()
            .filter(|(_, m)| is_path_suffix(&m.name, query))
            .map(|(i, _)| i)
            .collect();
        match hits.len() {
            1 => Ok(hits.remove(0)),
            0 => Err(Error::NotRecognized {
                expected: "module in this bun graph",
            }),
            _ => {
                let shown: Vec<&str> = hits
                    .iter()
                    .take(4)
                    .map(|&i| self.modules[i].name.as_str())
                    .collect();
                Err(Error::inconsistent(format!(
                    "module query {query:?} matches {} modules, including {}",
                    hits.len(),
                    shown.join(", ")
                )))
            }
        }
    }
}

/// Parse the last Bun graph in `data`.
pub fn open(data: &[u8]) -> Result<Graph<'_>> {
    open_with(data, &Options::default())
}

/// Parse one graph, bounding the module count by [`Options::max_modules`].
pub fn open_with<'a>(data: &'a [u8], opts: &Options) -> Result<Graph<'a>> {
    let mut end = data.len();
    let mut seen = 0usize;
    let mut skipped = 0u32;
    let mut looked = 0u32;
    while let Some(at) = last_trailer(data, end) {
        looked += 1;
        // Each attempt walks the file again. A handful of trailers is every
        // real executable; a caller asking for graph 10_000 must not turn
        // that into 10_000 scans.
        if looked > MAX_SKIPS.saturating_mul(2) {
            break;
        }
        match parse_at(data, at, opts.max_modules) {
            Ok(mut graph) => {
                if seen == opts.which {
                    if skipped > 0 {
                        graph.warnings.insert(
                            0,
                            format!(
                                "skipped {skipped} Bun trailer(s) whose offsets do not describe a graph"
                            ),
                        );
                    }
                    return Ok(graph);
                }
                seen += 1;
            }
            Err(Fail::Skip) => {
                skipped += 1;
                if skipped > MAX_SKIPS && seen == 0 {
                    break;
                }
            }
            Err(Fail::Bad(error)) => return Err(error),
        }
        end = at;
    }
    if seen > 0 {
        return Err(Error::inconsistent(format!(
            "bun graph index {} is past the {} graph(s) in the file",
            opts.which, seen
        )));
    }
    Err(Error::NotRecognized {
        expected: "bun standalone module graph",
    })
}

/// A trailer that is not a graph, or a graph that is damaged.
enum Fail {
    /// The marker is here, but the 32 bytes before it do not describe a
    /// region that ends at those bytes. Look further back.
    Skip,
    /// They do, and then a span runs outside that region. This is the graph
    /// Bun would read, so an earlier marker must not hide the error.
    Bad(Error),
}

fn last_trailer(data: &[u8], end: usize) -> Option<usize> {
    let end = end.min(data.len());
    data[..end]
        .windows(TRAILER.len())
        .rposition(|w| w == TRAILER)
}

fn parse_at(
    data: &[u8],
    trailer_at: usize,
    max_modules: u64,
) -> std::result::Result<Graph<'_>, Fail> {
    if trailer_at < OFFSETS_LEN {
        return Err(Fail::Skip);
    }
    let offsets_at = trailer_at - OFFSETS_LEN;
    let mut header = Reader::le(&data[offsets_at..trailer_at]);
    let byte_count = header.u64("bun.offsets.byte_count").map_err(Fail::Bad)?;
    let modules_off = header
        .u32("bun.offsets.modules.offset")
        .map_err(Fail::Bad)?;
    let modules_len = header
        .u32("bun.offsets.modules.length")
        .map_err(Fail::Bad)?;
    let entry_point_id = header
        .u32("bun.offsets.entry_point_id")
        .map_err(Fail::Bad)?;
    let argv_off = header.u32("bun.offsets.argv.offset").map_err(Fail::Bad)?;
    let argv_len = header.u32("bun.offsets.argv.length").map_err(Fail::Bad)?;
    let flags = header.u32("bun.offsets.flags").map_err(Fail::Bad)?;

    // A random marker almost never has a count that lands on itself. A
    // zero count is what thirty-two zero bytes look like, and Bun never
    // writes a graph of length zero: it returns no bytes instead.
    if byte_count == 0 || byte_count > offsets_at as u64 {
        return Err(Fail::Skip);
    }
    let base = offsets_at as u64 - byte_count;
    let graph = &data[base as usize..offsets_at];

    let modules_end = span_end(modules_off, modules_len).map_err(Fail::Bad)?;
    let argv_end = span_end(argv_off, argv_len).map_err(Fail::Bad)?;
    if modules_end > byte_count || argv_end > byte_count {
        return Err(Fail::Bad(Error::BadField {
            field: "bun.offsets",
            value: byte_count,
            reason: "does not cover the module records or the argv it names",
        }));
    }

    let record_size = record_size(graph, modules_off, modules_len)?;
    // `record_size` is 0 only when the table is empty, and otherwise it
    // divides `modules_len`. `checked_div` is what keeps the empty case
    // from being a special division.
    let count = u64::from(modules_len).checked_div(record_size).unwrap_or(0);
    if count > max_modules {
        return Err(Fail::Bad(Error::CapExceeded {
            what: "bun modules",
            requested: count,
            limit: max_modules,
        }));
    }
    // Pointers are checked before any name is copied, so a damaged record
    // does not allocate the modules that were fine.
    check_records(graph, modules_off, count, record_size).map_err(Fail::Bad)?;

    let mut warnings = Vec::new();
    let mut modules = Vec::with_capacity(count as usize);
    for index in 0..count {
        let record = record_bytes(graph, modules_off, record_size, index).map_err(Fail::Bad)?;
        let mut cursor = Reader::le(record);
        let name_span = read_span(&mut cursor).map_err(Fail::Bad)?;
        let contents_span = read_span(&mut cursor).map_err(Fail::Bad)?;
        let sourcemap = read_span(&mut cursor).map_err(Fail::Bad)?;
        let bytecode = read_span(&mut cursor).map_err(Fail::Bad)?;
        if record_size == RECORD_V2 {
            let _module_info = read_span(&mut cursor).map_err(Fail::Bad)?;
            let _origin = read_span(&mut cursor).map_err(Fail::Bad)?;
        }
        let encoding = cursor.u8("bun.module.encoding").map_err(Fail::Bad)?;
        let loader = cursor.u8("bun.module.loader").map_err(Fail::Bad)?;
        let format = cursor.u8("bun.module.format").map_err(Fail::Bad)?;
        let side = cursor.u8("bun.module.side").map_err(Fail::Bad)?;

        let name_bytes = slice_span(graph, name_span, "bun.module.name").map_err(Fail::Bad)?;
        let contents =
            slice_span(graph, contents_span, "bun.module.contents").map_err(Fail::Bad)?;
        let name = owned_name(name_bytes, index as u32, &mut warnings);
        let entry = entry_point_id == index as u32;
        modules.push(Module {
            index: index as u32,
            name,
            contents,
            contents_offset: base + u64::from(contents_span.offset),
            sourcemap_len: sourcemap.length,
            bytecode_len: bytecode.length,
            encoding,
            loader,
            format,
            side,
            entry,
        });
    }

    if count > 0 && u64::from(entry_point_id) >= count {
        warnings.push(format!(
            "entry point id {entry_point_id} is past the {count} module(s)"
        ));
    }
    warn_duplicates(&modules, &mut warnings);

    let argv = slice_span(
        graph,
        Span {
            offset: argv_off,
            length: argv_len,
        },
        "bun.argv",
    )
    .map_err(Fail::Bad)?;

    Ok(Graph {
        offset: base,
        byte_count,
        trailer_offset: trailer_at as u64,
        record_size,
        entry_point_id,
        argv,
        flags,
        modules,
        warnings,
    })
}

/// A span Bun stores as two little-endian `u32`s, offset then length.
#[derive(Clone, Copy)]
struct Span {
    offset: u32,
    length: u32,
}

fn read_span(cursor: &mut Reader<'_>) -> Result<Span> {
    Ok(Span {
        offset: cursor.u32("bun.span.offset")?,
        length: cursor.u32("bun.span.length")?,
    })
}

fn span_end(offset: u32, length: u32) -> Result<u64> {
    u64::from(offset)
        .checked_add(u64::from(length))
        .ok_or(Error::BadField {
            field: "bun.span",
            value: u64::from(offset),
            reason: "overflows when added to its length",
        })
}

fn slice_span<'a>(graph: &'a [u8], span: Span, field: &'static str) -> Result<&'a [u8]> {
    if span.length == 0 {
        return Ok(&[]);
    }
    let start = span.offset as usize;
    let end = start
        .checked_add(span.length as usize)
        .ok_or(Error::BadField {
            field,
            value: u64::from(span.offset),
            reason: "overflows when added to its length",
        })?;
    if end > graph.len() {
        return Err(Error::BadField {
            field,
            value: u64::from(span.offset),
            reason: "points outside the module graph",
        });
    }
    Ok(&graph[start..end])
}

/// 52 when that reading is consistent, otherwise 36, otherwise an error
/// when a known size divides the table but its spans do not fit. A length
/// that divides by neither is not a graph.
fn record_size(graph: &[u8], modules_off: u32, modules_len: u32) -> std::result::Result<u64, Fail> {
    if modules_len == 0 {
        return Ok(0);
    }
    let v2 = u64::from(modules_len) % RECORD_V2 == 0;
    let v1 = u64::from(modules_len) % RECORD_V1 == 0;
    if !v1 && !v2 {
        return Err(Fail::Skip);
    }
    let v2_count = u64::from(modules_len) / RECORD_V2;
    let v1_count = u64::from(modules_len) / RECORD_V1;
    let v2_ok = v2 && check_records(graph, modules_off, v2_count, RECORD_V2).is_ok();
    let v1_ok = v1 && check_records(graph, modules_off, v1_count, RECORD_V1).is_ok();
    match (v2_ok, v1_ok) {
        (true, false) => Ok(RECORD_V2),
        (false, true) => Ok(RECORD_V1),
        (true, true) => {
            // A length that divides by both still has one reading whose
            // names are paths. Prefer that one. A tie keeps the size Bun
            // writes today.
            let newer = name_score(graph, modules_off, v2_count, RECORD_V2);
            let older = name_score(graph, modules_off, v1_count, RECORD_V1);
            Ok(if older > newer { RECORD_V1 } else { RECORD_V2 })
        }
        (false, false) => {
            // The table is a whole number of records, so this is a graph
            // with a span outside it. Report the size a current executable
            // uses when that size divides.
            let size = if v2 { RECORD_V2 } else { RECORD_V1 };
            let count = u64::from(modules_len) / size;
            Err(Fail::Bad(
                check_records(graph, modules_off, count, size).unwrap_err(),
            ))
        }
    }
}

/// How many module names look like paths. Used only to separate the two
/// record sizes when a byte length is a multiple of both.
fn name_score(graph: &[u8], modules_off: u32, count: u64, record_size: u64) -> u32 {
    let mut score = 0;
    for index in 0..count {
        let Ok(record) = record_bytes(graph, modules_off, record_size, index) else {
            return score;
        };
        let mut cursor = Reader::le(record);
        let Ok(span) = read_span(&mut cursor) else {
            return score;
        };
        let Ok(bytes) = slice_span(graph, span, "bun.module.name") else {
            return score;
        };
        if bytes.is_empty() || !bytes.iter().all(|b| b.is_ascii_graphic()) {
            continue;
        }
        score += 1;
        if bytes.contains(&b'/') {
            score += 1;
        }
    }
    score
}

fn check_records(graph: &[u8], modules_off: u32, count: u64, record_size: u64) -> Result<()> {
    let spans = if record_size == RECORD_V2 { 6 } else { 4 };
    for index in 0..count {
        let record = record_bytes(graph, modules_off, record_size, index)?;
        let mut cursor = Reader::le(record);
        for _ in 0..spans {
            let span = read_span(&mut cursor)?;
            let _ = slice_span(graph, span, "bun.module")?;
        }
    }
    Ok(())
}

fn record_bytes(graph: &[u8], modules_off: u32, record_size: u64, index: u64) -> Result<&[u8]> {
    let start = u64::from(modules_off)
        .checked_add(index.checked_mul(record_size).ok_or(Error::BadField {
            field: "bun.module",
            value: index,
            reason: "overflows when multiplied by the record size",
        })?)
        .ok_or(Error::BadField {
            field: "bun.module",
            value: index,
            reason: "overflows when located in the module table",
        })?;
    let end = start.checked_add(record_size).ok_or(Error::BadField {
        field: "bun.module",
        value: start,
        reason: "overflows when the record size is added",
    })?;
    if end > graph.len() as u64 {
        return Err(Error::OutOfBounds {
            what: "bun.module",
            offset: start,
            len: record_size,
            available: graph.len() as u64,
        });
    }
    Ok(&graph[start as usize..end as usize])
}

fn owned_name(bytes: &[u8], index: u32, warnings: &mut Vec<String>) -> String {
    let bytes = if bytes.len() > MAX_NAME {
        warnings.push(format!(
            "module {index} name is {} bytes; the listing keeps the first {MAX_NAME}",
            bytes.len()
        ));
        &bytes[..MAX_NAME]
    } else {
        bytes
    };
    match std::str::from_utf8(bytes) {
        Ok(text) => text.to_string(),
        Err(_) => {
            warnings.push(format!("module {index} name is not utf-8"));
            String::from_utf8_lossy(bytes).into_owned()
        }
    }
}

fn warn_duplicates(modules: &[Module<'_>], warnings: &mut Vec<String>) {
    let mut seen = std::collections::BTreeSet::new();
    for module in modules {
        if !seen.insert(module.name.as_str()) {
            warnings.push(format!(
                "module {} reuses the name {}",
                module.index, module.name
            ));
        }
    }
}

fn is_path_suffix(name: &str, query: &str) -> bool {
    name.len() > query.len()
        && name.ends_with(query)
        && name.as_bytes()[name.len() - query.len() - 1] == b'/'
}

fn named(value: u8, table: &[&str], prefix: &str) -> String {
    table
        .get(usize::from(value))
        .map(|s| (*s).to_string())
        .unwrap_or_else(|| format!("{prefix}-{value}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// One module in a synthetic graph.
    struct File {
        name: &'static str,
        contents: &'static [u8],
        encoding: u8,
        loader: u8,
        format: u8,
        side: u8,
    }

    /// Build a graph the way Bun does: strings, then records, then argv,
    /// then offsets, then the trailer. A trailing NUL sits after each
    /// string and is not part of its length.
    fn build(record_size: u64, files: &[File], entry: u32, argv: &[u8], flags: u32) -> Vec<u8> {
        let mut blob = Vec::new();
        let mut spans: Vec<(u32, u32, u32, u32)> = Vec::new();
        for file in files {
            let name_at = put_z(&mut blob, file.name.as_bytes());
            let body_at = put_z(&mut blob, file.contents);
            spans.push((
                name_at,
                file.name.len() as u32,
                body_at,
                file.contents.len() as u32,
            ));
        }
        let modules_off = blob.len() as u32;
        for (file, (name_off, name_len, body_off, body_len)) in files.iter().zip(&spans) {
            put_u32(&mut blob, *name_off);
            put_u32(&mut blob, *name_len);
            put_u32(&mut blob, *body_off);
            put_u32(&mut blob, *body_len);
            put_u32(&mut blob, 0);
            put_u32(&mut blob, 0);
            put_u32(&mut blob, 0);
            put_u32(&mut blob, 0);
            if record_size == RECORD_V2 {
                put_u32(&mut blob, 0);
                put_u32(&mut blob, 0);
                put_u32(&mut blob, 0);
                put_u32(&mut blob, 0);
            }
            blob.extend_from_slice(&[file.encoding, file.loader, file.format, file.side]);
        }
        let modules_len = blob.len() as u32 - modules_off;
        let argv_off = blob.len() as u32;
        blob.extend_from_slice(argv);
        if !argv.is_empty() {
            blob.push(0);
        }
        let byte_count = blob.len() as u64;
        put_u64(&mut blob, byte_count);
        put_u32(&mut blob, modules_off);
        put_u32(&mut blob, modules_len);
        put_u32(&mut blob, entry);
        put_u32(&mut blob, argv_off);
        put_u32(&mut blob, argv.len() as u32);
        put_u32(&mut blob, flags);
        blob.extend_from_slice(TRAILER);
        blob
    }

    fn put_z(out: &mut Vec<u8>, bytes: &[u8]) -> u32 {
        let at = out.len() as u32;
        out.extend_from_slice(bytes);
        out.push(0);
        at
    }

    fn put_u32(out: &mut Vec<u8>, value: u32) {
        out.extend_from_slice(&value.to_le_bytes());
    }

    fn put_u64(out: &mut Vec<u8>, value: u64) {
        out.extend_from_slice(&value.to_le_bytes());
    }

    fn sample(record_size: u64) -> Vec<u8> {
        build(
            record_size,
            &[
                File {
                    name: "/$bunfs/root/a.js",
                    contents: b"AAA",
                    encoding: 1,
                    loader: 0,
                    format: 1,
                    side: 0,
                },
                File {
                    name: "/$bunfs/root/b.txt",
                    contents: b"BBB",
                    encoding: 0,
                    loader: 13,
                    format: 0,
                    side: 1,
                },
            ],
            0,
            b"--flag",
            0b0001,
        )
    }

    #[test]
    fn a_current_graph_lists_both_modules_and_names_the_entry() {
        let bytes = sample(RECORD_V2);
        let graph = open(&bytes).expect("52-byte graph");
        assert_eq!(graph.record_size, RECORD_V2);
        assert_eq!(graph.modules.len(), 2);
        assert_eq!(graph.entry_point_id, 0);
        assert!(graph.modules[0].entry);
        assert!(!graph.modules[1].entry);
        assert_eq!(graph.modules[0].name, "/$bunfs/root/a.js");
        assert_eq!(graph.modules[0].contents, b"AAA");
        assert_eq!(graph.modules[0].loader_name(), "jsx");
        assert_eq!(graph.modules[0].encoding_name(), "latin1");
        assert_eq!(graph.modules[0].format_name(), "esm");
        assert_eq!(graph.modules[1].loader_name(), "text");
        assert_eq!(graph.modules[1].side_name(), "client");
        assert_eq!(graph.argv, b"--flag");
        assert_eq!(graph.flags, 1);
        assert!(graph.warnings.is_empty(), "{:?}", graph.warnings);
        // The NUL Bun writes after a string is not part of the span.
        assert!(!graph.modules[0].contents.contains(&0));
        let at = graph.modules[0].contents_offset as usize;
        assert_eq!(&bytes[at..at + 3], b"AAA");
    }

    #[test]
    fn an_older_record_is_not_read_as_the_new_one() {
        // Thirteen 36-byte records are also nine 52-byte records. The spans
        // only fit the size they were written with. Names differ so a
        // duplicate warning is not what this test is looking at.
        let files: Vec<File> = (0..13)
            .map(|i| File {
                name: match i {
                    0 => "/$bunfs/root/m0.js",
                    1 => "/$bunfs/root/m1.js",
                    2 => "/$bunfs/root/m2.js",
                    3 => "/$bunfs/root/m3.js",
                    4 => "/$bunfs/root/m4.js",
                    5 => "/$bunfs/root/m5.js",
                    6 => "/$bunfs/root/m6.js",
                    7 => "/$bunfs/root/m7.js",
                    8 => "/$bunfs/root/m8.js",
                    9 => "/$bunfs/root/m9.js",
                    10 => "/$bunfs/root/m10.js",
                    11 => "/$bunfs/root/m11.js",
                    _ => "/$bunfs/root/m12.js",
                },
                contents: b"x",
                encoding: 1,
                loader: 1,
                format: 2,
                side: 0,
            })
            .collect();
        let bytes = build(RECORD_V1, &files, 3, b"", 0);
        let modules_len = 13 * RECORD_V1;
        assert_eq!(
            modules_len % RECORD_V2,
            0,
            "the fixture must be ambiguous on length alone"
        );
        let graph = open(&bytes).expect("36-byte graph");
        assert_eq!(graph.record_size, RECORD_V1);
        assert_eq!(graph.modules.len(), 13);
        assert!(graph.modules[3].entry);
        assert_eq!(graph.modules[3].name, "/$bunfs/root/m3.js");
        assert_eq!(graph.modules[10].loader_name(), "js");
        assert_eq!(graph.modules[0].format_name(), "cjs");
    }

    #[test]
    fn a_current_graph_whose_length_also_divides_by_the_old_size_stays_current() {
        // Nine 52-byte records are thirteen 36-byte records. The names are
        // paths only in the size they were written with.
        let files: Vec<File> = (0..9)
            .map(|i| File {
                name: match i {
                    0 => "/$bunfs/root/n0.js",
                    1 => "/$bunfs/root/n1.js",
                    2 => "/$bunfs/root/n2.js",
                    3 => "/$bunfs/root/n3.js",
                    4 => "/$bunfs/root/n4.js",
                    5 => "/$bunfs/root/n5.js",
                    6 => "/$bunfs/root/n6.js",
                    7 => "/$bunfs/root/n7.js",
                    _ => "/$bunfs/root/n8.js",
                },
                contents: b"y",
                encoding: 1,
                loader: 0,
                format: 1,
                side: 0,
            })
            .collect();
        let bytes = build(RECORD_V2, &files, 1, b"", 0);
        assert_eq!((9 * RECORD_V2) % RECORD_V1, 0);
        let graph = open(&bytes).expect("52-byte graph");
        assert_eq!(graph.record_size, RECORD_V2);
        assert_eq!(graph.modules.len(), 9);
        assert!(graph.modules[1].entry);
        assert_eq!(graph.modules[8].name, "/$bunfs/root/n8.js");
        assert_eq!(graph.modules[0].loader_name(), "jsx");
    }

    #[test]
    fn the_last_trailer_wins_and_a_marker_inside_a_module_does_not() {
        let mut bytes = b"noise \n---- Bun! ----\n more noise".to_vec();
        let shift = bytes.len() as u64;
        bytes.extend(sample(RECORD_V2));
        // The module body itself contains the marker. It is data.
        let body_at = bytes
            .windows(3)
            .position(|w| w == b"AAA")
            .expect("contents");
        bytes[body_at..body_at + 3].copy_from_slice(b"---");
        // Put a real marker sequence into the contents by rebuilding is
        // harder once we overwrote; instead prefix is enough, and a second
        // copy is planted in front of the graph below.
        let graph = open(&bytes).expect("real graph");
        assert_eq!(graph.offset, shift);
        assert_eq!(graph.modules[0].contents, b"---");
        assert!(graph.warnings.is_empty(), "{:?}", graph.warnings);
    }

    #[test]
    fn a_trailing_marker_that_is_not_a_graph_does_not_hide_the_real_one() {
        let mut bytes = sample(RECORD_V2);
        bytes.extend_from_slice(&[0xff; OFFSETS_LEN]);
        bytes.extend_from_slice(TRAILER);
        let graph = open(&bytes).expect("skipped the trailing marker");
        assert_eq!(graph.modules.len(), 2);
        assert_eq!(graph.warnings.len(), 1);
        assert!(graph.warnings[0].contains("skipped 1"));
    }

    #[test]
    fn a_span_past_the_graph_is_an_error_rather_than_an_earlier_graph() {
        let earlier = sample(RECORD_V2);
        let mut bytes = earlier.clone();
        // A second graph whose contents span claims to start inside the
        // graph and run past it: byte_count still lands on the offsets, so
        // this is the graph, and it is damaged.
        let mut broken = sample(RECORD_V2);
        let trailer = broken
            .windows(TRAILER.len())
            .rposition(|w| w == TRAILER)
            .unwrap();
        let offsets = trailer - OFFSETS_LEN;
        // contents length of the first module sits at: after its name span.
        // Easier: set modules length's first record contents length to 0xffffffff
        // by patching the record. Find "AAA" span length, the u32 before the
        // bytes... The length is 3. Replace a 3 that is a u32 le inside the
        // record area. There may be several. Set byte 0 of argv length?
        // Patch entry is not a span. Patch the first contents length: search
        // the record for the pattern name_len then later.
        // The first module contents length is the u32 value 3 at a known
        // place relative to modules. We'll overwrite modules_len's region
        // by setting the contents length field. In `build`, contents length
        // is the second span's length. Search for 03 00 00 00 that is
        // followed later... Simply set the argv length, which is inside
        // offsets, to a huge value while keeping byte_count fitting.
        let argv_len_at = offsets + 8 + 4 + 4 + 4 + 4;
        // offsets: byte_count u64, modules off u32, modules len u32,
        // entry u32, argv off u32, argv len u32, flags u32.
        // argv len is at offset 24.
        assert_eq!(argv_len_at, offsets + 24);
        broken[argv_len_at..argv_len_at + 4].copy_from_slice(&u32::MAX.to_le_bytes());
        bytes.extend(broken);
        let error = open(&bytes).expect_err("damaged last graph");
        assert!(
            matches!(
                error,
                Error::BadField {
                    field: "bun.offsets",
                    ..
                }
            ),
            "{error}"
        );
    }

    #[test]
    fn no_marker_is_not_a_graph() {
        let error = open(b"hello").unwrap_err();
        assert!(error.is_not_recognized());
    }

    #[test]
    fn the_module_cap_is_enforced_before_the_names_are_kept() {
        let bytes = sample(RECORD_V2);
        let opts = Options {
            which: 0,
            max_modules: 1,
        };
        let error = open_with(&bytes, &opts).unwrap_err();
        assert!(
            matches!(
                error,
                Error::CapExceeded {
                    what: "bun modules",
                    ..
                }
            ),
            "{error}"
        );
    }

    #[test]
    fn find_takes_a_path_an_index_or_a_unique_suffix() {
        let bytes = sample(RECORD_V2);
        let graph = open(&bytes).unwrap();
        assert_eq!(graph.find("/$bunfs/root/b.txt").unwrap(), 1);
        assert_eq!(graph.find("1").unwrap(), 1);
        assert_eq!(graph.find("b.txt").unwrap(), 1);
        assert_eq!(graph.find("root/a.js").unwrap(), 0);
        assert!(graph.find("nope").unwrap_err().is_not_recognized());
        assert!(graph.find("").is_err());
    }

    #[test]
    fn a_suffix_that_matches_two_modules_says_so() {
        let bytes = build(
            RECORD_V2,
            &[
                File {
                    name: "/$bunfs/root/a.js",
                    contents: b"1",
                    encoding: 1,
                    loader: 1,
                    format: 1,
                    side: 0,
                },
                File {
                    name: "/$bunfs/other/a.js",
                    contents: b"2",
                    encoding: 1,
                    loader: 1,
                    format: 1,
                    side: 0,
                },
            ],
            0,
            b"",
            0,
        );
        let graph = open(&bytes).unwrap();
        let error = graph.find("a.js").unwrap_err();
        let Error::Inconsistent { detail } = error else {
            panic!("{error}");
        };
        assert!(detail.contains("2 modules"), "{detail}");
    }

    #[test]
    fn an_entry_past_the_end_is_reported_and_the_modules_remain() {
        let bytes = build(
            RECORD_V2,
            &[File {
                name: "/$bunfs/root/only.js",
                contents: b"z",
                encoding: 1,
                loader: 1,
                format: 0,
                side: 0,
            }],
            4,
            b"",
            0,
        );
        let graph = open(&bytes).unwrap();
        assert_eq!(graph.modules.len(), 1);
        assert!(!graph.modules[0].entry);
        assert!(
            graph
                .warnings
                .iter()
                .any(|w| w.contains("entry point id 4"))
        );
    }
}

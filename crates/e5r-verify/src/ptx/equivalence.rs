//! Direct concrete-program equivalence; supplied-proof replay only.
use super::{Options, Verdict, finish_at, sha, supplied, supplied_route};
use e5r_ptx::ast::{Module, Ty};
use serde::Deserialize;
use serde_json::{Value, json};
use std::time::Instant;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Spec {
    schema: String,
    class: String,
    kernel: String,
    original_ptx: String,
    original_sha256: String,
    input: String,
    output: String,
    length: String,
    #[serde(default)]
    repeats: Option<String>,
    #[serde(default)]
    scalar: Option<String>,
}

#[allow(clippy::too_many_arguments)]
pub fn check(
    o: &Options,
    mut doc: Value,
    started: Instant,
    module: &Module,
    text: &str,
    phash: &str,
    shash: &str,
) -> (Verdict, Value) {
    let finish = |doc, v, r| finish_at(started, doc, v, r);
    doc["class"] = json!("equivalence");
    let sp: Spec = match serde_json::from_str(text) {
        Ok(s) => s,
        Err(e) => {
            return finish(
                doc,
                Verdict::Error,
                Some(format!("equivalence contract: {e}")),
            );
        }
    };
    if sp.schema != super::spec::SCHEMA
        || !matches!(
            sp.class.as_str(),
            "equivalence-unpack4"
                | "equivalence-stencil17"
                | "equivalence-stencil17-pair2"
                | "equivalence-oss-inc"
                | "equivalence-zero-segments"
        )
    {
        return finish(
            doc,
            Verdict::Error,
            Some("invalid equivalence schema/class".into()),
        );
    }
    doc["class"] = json!(sp.class);
    let family = if sp.class == "equivalence-zero-segments" {
        "ZeroSegments"
    } else if sp.class == "equivalence-oss-inc" {
        "OssInc"
    } else if sp.class == "equivalence-stencil17-pair2" {
        "StencilPair"
    } else if sp.class == "equivalence-stencil17" {
        "Stencil"
    } else {
        "Equivalence"
    };
    if sp.input == sp.output || sp.input == sp.length || sp.output == sp.length {
        return finish(
            doc,
            Verdict::Error,
            Some("parameter names must differ".into()),
        );
    }
    let original_path = o
        .spec
        .parent()
        .unwrap_or_else(|| std::path::Path::new("."))
        .join(&sp.original_ptx);
    let (bytes, original_hash) = match sha(&original_path) {
        Ok(x) => x,
        Err(e) => return finish(doc, Verdict::Error, Some(e)),
    };
    doc["input"]["original_ptx"] = json!({"path":original_path,"sha256":original_hash});
    if original_hash != sp.original_sha256 {
        return finish(
            doc,
            Verdict::Unknown,
            Some("frozen original PTX hash mismatch".into()),
        );
    }
    let original = match String::from_utf8(bytes)
        .map_err(|e| e.to_string())
        .and_then(|s| e5r_ptx::roundtrip(&s).map_err(|e| e.to_string()))
    {
        Ok(m) => m,
        Err(e) => {
            return finish(
                doc,
                Verdict::Unsupported,
                Some(format!("original PTX outside subset: {e}")),
            );
        }
    };
    let Some(k0) = original.kernels.iter().find(|k| k.name == sp.kernel) else {
        return finish(doc, Verdict::Error, Some("original kernel missing".into()));
    };
    let Some(k1) = module.kernels.iter().find(|k| k.name == sp.kernel) else {
        return finish(doc, Verdict::Error, Some("candidate kernel missing".into()));
    };
    if !k0.aggregate_params.is_empty() || !k1.aggregate_params.is_empty() {
        return finish(
            doc,
            Verdict::Unsupported,
            Some("scalar equivalence domains do not support aggregate parameter ABI".into()),
        );
    }
    let mut expected = vec![
        (&sp.input, Ty::U64),
        (&sp.output, Ty::U64),
        (&sp.length, Ty::U32),
    ];
    if sp.class == "equivalence-oss-inc" {
        let Some(repeats) = sp.repeats.as_ref() else {
            return finish(
                doc,
                Verdict::Error,
                Some("requires repeats parameter".into()),
            );
        };
        if [&sp.input, &sp.output, &sp.length].contains(&repeats) {
            return finish(
                doc,
                Verdict::Error,
                Some("parameter names must differ".into()),
            );
        }
        expected.push((repeats, Ty::U32));
    } else if sp.repeats.is_some() {
        return finish(
            doc,
            Verdict::Error,
            Some("unexpected repeats parameter".into()),
        );
    }
    if sp.class == "equivalence-zero-segments" {
        let Some(scalar) = sp.scalar.as_ref() else {
            return finish(
                doc,
                Verdict::Error,
                Some("requires scalar parameter".into()),
            );
        };
        if [&sp.input, &sp.output, &sp.length].contains(&scalar) {
            return finish(
                doc,
                Verdict::Error,
                Some("parameter names must differ".into()),
            );
        }
        expected.push((scalar, Ty::U32));
    } else if sp.scalar.is_some() {
        return finish(
            doc,
            Verdict::Error,
            Some("unexpected scalar parameter".into()),
        );
    }
    if k0.params != k1.params
        || k0.params.len() != expected.len()
        || !expected
            .iter()
            .all(|(n, t)| k0.params.iter().any(|p| &p.0 == *n && p.1 == *t))
    {
        return finish(
            doc,
            Verdict::Unsupported,
            Some("requires identical input/output u64 and length u32 parameters".into()),
        );
    }
    doc["kernel"] = json!(sp.kernel);
    let q = |s: &str| serde_json::to_string(s).unwrap();
    let extra = sp
        .repeats
        .as_ref()
        .or(sp.scalar.as_ref())
        .map(|r| format!(", {}", q(r)))
        .unwrap_or_default();
    let definition = format!(
        "def domain : {family}.Spec := ⟨{}, {}, {}{}⟩\n",
        q(&sp.input),
        q(&sp.output),
        q(&sp.length),
        extra
    );
    doc["lean_spec"] = json!(definition);
    let statement = format!(
        "{family}.Spec.Equivalent domain Original.«{}» Optimized.«{}»",
        sp.kernel, sp.kernel
    );
    let pre = format!(
        "import Ptx.Auto.{family}\nnamespace E5rSpec\nopen Ptx Ptx.Auto\nnamespace Original\n{}\nend Original\nnamespace Optimized\n{}\nend Optimized\n{}",
        e5r_ptx::lean::kernel_def(k0),
        e5r_ptx::lean::kernel_def(k1),
        definition
    );
    let stmtmod = supplied::statement_module(&pre, &statement);
    let Some(pf) = &o.proof else {
        return finish(
            doc,
            Verdict::Unknown,
            Some("direct equivalence requires a supplied proof".into()),
        );
    };
    let dir = o.keep.clone().unwrap_or_else(|| {
        std::env::temp_dir().join(format!(
            "e5r-equivalence-{}-{}",
            std::process::id(),
            &phash[..12]
        ))
    });
    if let Err(e) = std::fs::create_dir_all(&dir) {
        return finish(doc, Verdict::Error, Some(e.to_string()));
    }
    let proj = match o.project.canonicalize() {
        Ok(p) => p,
        Err(e) => return finish(doc, Verdict::Error, Some(e.to_string())),
    };
    let (v, why) = supplied_route(
        o,
        &mut doc,
        pf,
        &stmtmod,
        &statement,
        &format!("Ptx.Auto.{family}.Spec.Equivalent"),
        phash,
        shash,
        &proj,
        &dir,
    );
    if o.keep.is_none() {
        let _ = std::fs::remove_dir_all(&dir);
    }
    let (v, mut doc) = finish(doc, v, why);
    if v == Verdict::Proved {
        doc["properties"]["direct_observable_equivalence"] = json!("proved");
        doc["properties"]["functional_correctness"] = json!("not_claimed");
    }
    (v, doc)
}

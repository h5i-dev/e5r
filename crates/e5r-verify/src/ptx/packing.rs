//! Strict, supplied-proof-only contracts for unequal-size byte packing.
//! No proof search fallback and no success for unsupported instructions.
use super::{Options, Verdict, finish_at, supplied, supplied_route};
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
    op: String,
    input: String,
    output: String,
    length: String,
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
    doc["class"] = json!("packing");
    let sp: Spec = match serde_json::from_str(text) {
        Ok(s) => s,
        Err(e) => return finish(doc, Verdict::Error, Some(format!("packing spec: {e}"))),
    };
    if sp.schema != super::spec::SCHEMA || sp.class != "packing" {
        return finish(
            doc,
            Verdict::Error,
            Some("invalid packing schema/class".into()),
        );
    }
    if !matches!(sp.op.as_str(), "pack" | "unpack" | "threshold") {
        return finish(
            doc,
            Verdict::Unsupported,
            Some("unsupported packing operation".into()),
        );
    }
    doc["kernel"] = json!(sp.kernel);
    if sp.input == sp.output || sp.input == sp.length || sp.output == sp.length {
        return finish(
            doc,
            Verdict::Error,
            Some("packing parameter names must differ".into()),
        );
    }
    let Some(k) = module.kernels.iter().find(|k| k.name == sp.kernel) else {
        return finish(doc, Verdict::Error, Some("packing kernel missing".into()));
    };
    let expected = [
        (&sp.input, Ty::U64),
        (&sp.output, Ty::U64),
        (&sp.length, Ty::U32),
    ];
    if k.params.len() != 3
        || !expected
            .iter()
            .all(|(name, ty)| k.params.iter().any(|p| &p.0 == *name && p.1 == *ty))
    {
        return finish(
            doc,
            Verdict::Unsupported,
            Some("packing requires input/output u64 and length u32 parameters".into()),
        );
    }
    let q = |s: &str| serde_json::to_string(s).unwrap();
    let definition = format!(
        "def spec : Packing.Spec := ⟨.{}, {}, {}, {}⟩\n",
        sp.op,
        q(&sp.input),
        q(&sp.output),
        q(&sp.length)
    );
    doc["lean_spec"] = json!(definition);
    let statement = format!("Packing.Spec.Correct spec «{}»", k.name);
    let pre = format!(
        "import Ptx.Auto.Packing\nnamespace E5rSpec\nopen Ptx Ptx.Auto\n{}\n{}",
        e5r_ptx::lean::kernel_def(k),
        definition
    );
    let stmtmod = supplied::statement_module(&pre, &statement);
    let Some(pf) = &o.proof else {
        return finish(
            doc,
            Verdict::Unknown,
            Some("packing requires a supplied proof".into()),
        );
    };
    let dir = o.keep.clone().unwrap_or_else(|| {
        std::env::temp_dir().join(format!(
            "e5r-packing-{}-{}",
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
        "Ptx.Auto.Packing.Spec.Correct",
        phash,
        shash,
        &proj,
        &dir,
    );
    if o.keep.is_none() {
        let _ = std::fs::remove_dir_all(&dir);
    }
    finish(doc, v, why)
}

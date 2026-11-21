import Lean
import NoCompiler.Attr
import NoCompiler.Image

/-!
# Instructions of a chunk image, for the step tactics

An image in chunks (`nocompiler export --format chunks`, NoCompiler/Image.lean)
has no lemma per instruction. The step tactics (NoCompiler/Tactic.lean,
NoCompiler/Auto.lean) read instructions through the `nocompiler_image` simp
set; `chunkInstr`, a simproc in that set, gives them the same equation, made
when it is needed:

  `code.instr pc = some i` (or `= none`)

for `code := Code.ofChunks base chunks` an exported image and `pc` a literal.
It finds the chunk `k` holding `pc` and the instruction `i` with compiled code
(`evalExpr`); neither is trusted. The proof is
`Code.ofChunks_instr chunks_contig hk chunks_bound pc hmem` followed by
`(chunk_k.code base).instr pc = some i`, the last three by `rfl`: the kernel
checks them on chunk `k` alone (`hk` walks the list of chunks up to `k`, never
a word of another chunk).
-/
namespace NoCompiler.ImageSimp
open Lean Meta

deriving instance ToExpr for NoCompiler.BrOp
deriving instance ToExpr for NoCompiler.LdOp
deriving instance ToExpr for NoCompiler.StOp
deriving instance ToExpr for NoCompiler.IOp
deriving instance ToExpr for NoCompiler.ShOp
deriving instance ToExpr for NoCompiler.ShWOp
deriving instance ToExpr for NoCompiler.ROp
deriving instance ToExpr for NoCompiler.RWOp
deriving instance ToExpr for NoCompiler.UOp
deriving instance ToExpr for NoCompiler.Instr

/-- Offsets and lengths of the chunks. -/
def spans (cs : List Chunk) : List (Nat × Nat) := cs.map fun c => (c.off, c.len)

unsafe def evalSpansImpl (e : Expr) : MetaM (List (Nat × Nat)) :=
  do evalExpr (List (Nat × Nat)) (← inferType e) e
@[implemented_by evalSpansImpl] opaque evalSpans (e : Expr) : MetaM (List (Nat × Nat))

unsafe def evalNatImpl (e : Expr) : MetaM Nat := evalExpr Nat (mkConst ``Nat) e
@[implemented_by evalNatImpl] opaque evalNat (e : Expr) : MetaM Nat

unsafe def evalInstrImpl (e : Expr) : MetaM (Option Instr) := do evalExpr (Option Instr) (← inferType e) e
@[implemented_by evalInstrImpl] opaque evalInstr (e : Expr) : MetaM (Option Instr)

/-- `c` is an exported chunk image `ns.code := Code.ofChunks base ns.chunks`
    with `ns.chunks_contig` and `ns.chunks_bound`: its namespace and base. -/
def image? (c : Expr) : MetaM (Option (Name × Expr)) := do
  let .const n _ := c | return none
  let env ← getEnv
  let some (.defnInfo d) := env.find? n | return none
  let_expr Code.ofChunks base cs := d.value | return none
  let ns := n.getPrefix
  unless cs.isConstOf (ns ++ `chunks) && env.contains (ns ++ `chunks_contig) &&
      env.contains (ns ++ `chunks_bound) do
    return none
  return some (ns, base)

/-- `mkExpectedTypeHint` without inferring `p`'s type. -/
def mkExpectedTypeHint' (p ty : Expr) : Expr := mkApp2 (mkConst ``id [Level.zero]) ty p

/-- `code.instr pc = some i` on an exported chunk image, for a literal `pc`. -/
simproc [nocompiler_image] chunkInstr (Code.instr _ _) := fun e => do
  let_expr Code.instr c pc := e | return .continue
  if pc.hasFVar || pc.hasMVar then return .continue
  let some (ns, base) ← image? c | return .continue
  let chunks := mkConst (ns ++ `chunks)
  let sp ← evalSpans (mkApp (mkConst ``spans) chunks)
  let off ← evalNat (← mkAppM ``BitVec.toNat #[← mkAppM ``HSub.hSub #[pc, base]])
  let some k := sp.findIdx? (fun (o, l) => 4 * o ≤ off && off < 4 * (o + l)) | return .continue
  -- The chunk as its own constant, as the exporter names it (`chunk_k`).
  let some (.defnInfo d) := (← getEnv).find? (ns ++ `chunks) | return .continue
  let some ck := (d.value.listLit?.bind (·.2[k]?)) | return .continue
  let cc := mkApp2 (mkConst ``Chunk.code) base ck
  let lhs' := mkApp2 (mkConst ``Code.instr) cc pc
  let rhs := toExpr (← evalInstr lhs')
  -- The kernel checks `hk : chunks[k]? = some ck` and `hmem : Dom.mem [ck.range base] pc`
  -- as `rfl`, from the types `Code.ofChunks_instr` gives them.
  let hk := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) (mkConst ``Chunk))
    (mkApp2 (mkConst ``Option.some [0]) (mkConst ``Chunk) ck)
  let hmem := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let p1 := mkAppN (mkConst ``Code.ofChunks_instr)
    #[base, chunks, mkNatLit k, ck, mkConst (ns ++ `chunks_contig), hk, mkConst (ns ++ `chunks_bound),
      pc, hmem]
  let ty := mkApp3 (mkConst ``Eq [1]) (mkApp (mkConst ``Option [0]) (mkConst ``Instr))
  let p2 := mkExpectedTypeHint' (mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) (mkConst ``Instr)) rhs)
    (ty lhs' rhs)
  let p := mkExpectedTypeHint' (mkApp6 (mkConst ``Eq.trans [1]) (mkApp (mkConst ``Option [0]) (mkConst ``Instr))
    e lhs' rhs p1 p2) (ty e rhs)
  return .done { expr := rhs, proof? := some p }

-- A segment's size in the chunk format, for the permission side goals of
-- NoCompiler/Auto.lean (which use `nocompiler_nat`), as `List.size_toArray`
-- gives it for an array literal.
attribute [nocompiler_nat] Segment.size_bytesOfNat

end NoCompiler.ImageSimp

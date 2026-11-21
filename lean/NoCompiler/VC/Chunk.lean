import NoCompiler.Image
import NoCompiler.Module
import NoCompiler.VC.Frame

/-
The explore path on a chunk image (`nocompiler export --format chunks`).

`explore` reads the words from index `k` on (`fetch k`). On the whole image
(`Code.ofChunks`) that is `c.words.toList.drop k`, which the kernel walks one
cell at a time: measured 175-194 ms for word 1045 of a 1046-word chunk, which
made every explore run on the artifact's large functions cost about 0.1-0.25 s
before its first instruction (lean/NoCompiler/VC/Bench/Art.py). So the run is
over the function's own chunk (`Chunk.code`), whose words from `k` on are read
from the chunk's bits directly (`Chunk.suffix`, 1-6 ms for the same word),
and moved to the whole image by `Reach.congr_code`, from the image's
`<f>_chunk` theorem (the two agree on the chunk's range), and to the function's
domain by `Reach.bind` (the chunk's range is inside it).
-/
namespace NoCompiler.VC.M

/-- The chunk's words from index `k` on, each read from the bits. -/
def Chunk.suffix (ch : NoCompiler.Chunk) (k : Nat) : List (BitVec 32) :=
  (List.range' k (ch.len - k)).map fun i => BitVec.ofNat 32 (ch.bits >>> (32 * i))

theorem Chunk.suffix_eq (base : Word) (ch : NoCompiler.Chunk) (k : Nat) :
    Chunk.suffix ch k = (ch.code base).words.toList.drop k := by
  simp only [Chunk.suffix, NoCompiler.Chunk.code, NoCompiler.Chunk.words, List.toList_toArray,
    ← List.map_drop, List.range_eq_range', List.drop_range', Nat.zero_add, Nat.mul_one]

/-- `Reach.of_exploreCalls`, the run over code `c'` inside `D'` (a chunk), for
    the code `c` that agrees with it there, inside `D ⊇ D'`. -/
theorem Reach.of_exploreCallsOn {c c' : Code} {P : Perm} {D D' : Dom} {Q : State → Prop}
    {facts : List Fact} {cuts ces : List Word} {fuel k : Nat} {p : Word} {s : State}
    {fetch : Nat → List (BitVec 32)}
    (hag : ∀ x, D'.mem x → c.instr x = c'.instr x) (hsub : D'.sub D)
    (hb : 4 * c'.words.size < 2 ^ 64) (hfe : ∀ k, fetch k = c'.words.toList.drop k)
    (hk : p = c'.base + BitVec.ofNat 64 (4 * k)) (hpc : s.pc = p) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P)
    (hvc : exploreVC (ρOf s) s.mem P (fun s' => s'.trace = s.trace → CallQ c P D Q ces s') facts c' D'
      (cuts ++ ces) fuel k p fetch) :
    Reach c P D Q s := by
  have h1 := Reach.of_exploreAtT hb hfe hk hpc hx hf hvc
  have h2 : Reach c P D' (CallQ c P D Q ces) s := Reach.congr_code (fun x hx => (hag x hx)) h1
  exact Reach.bind h2 (Perm.le_refl P) hsub fun s' h => by
    unfold CallQ at h
    split at h
    · exact h
    · exact .done h

end NoCompiler.VC.M

import Projects.thermostat.MainWriteCaller
import Projects.thermostat.WriteInput
import Projects.thermostat.WordRegions
namespace E5R.Thermostat.MainWriteInput
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- Memory obligations before the actual main call. Request bytes/layout
    remain explicit until the upstream HTTP/parser/routing proofs establish them. -/
structure Ready (ram : Word → BitVec 8) (req rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (state : Spec.Snapshot) : Prop where
  layout : WriteInput.Layout B ram 0x80ffeae0#32 req 0x80ffebbc#32 rawPtr pathPtr bodyPtr raw path body entries first true state
  fresh : ram (0x80fffa2c#32+40#32)=0#8
  request : ramRead ram (0x80fffa2c#32+4#32) .w=req
  engine : ramRead ram (0x80fffa2c#32+8#32) .w=0x80ffebbc#32
  pointer : ramRead ram (0x80fffa2c#32+12#32) .w=0x80fff4d4#32
  capacity : ramRead ram (0x80fffa2c#32+16#32) .w=832#32
  requestStack : WordRegions.Disjoint req 372 0x80ffe9f0#32 416
  requestFuture : WordRegions.Disjoint req 372 0x80fffa2c#32 41
  rawStack : WordRegions.Disjoint rawPtr raw.length 0x80ffe9f0#32 416
  rawFuture : WordRegions.Disjoint rawPtr raw.length 0x80fffa2c#32 41
  pathStack : WordRegions.Disjoint pathPtr path.length 0x80ffe9f0#32 416
  pathFuture : WordRegions.Disjoint pathPtr path.length 0x80fffa2c#32 41
  bodyStack : WordRegions.Disjoint bodyPtr body.length 0x80ffe9f0#32 416
  bodyFuture : WordRegions.Disjoint bodyPtr body.length 0x80fffa2c#32 41

theorem avoid {obj n} (hs : WordRegions.Disjoint obj n 0x80ffe9f0#32 416)
    (hf : WordRegions.Disjoint obj n 0x80fffa2c#32 41) : WriteInput.Avoid obj n (0x80ffeae0#32+80#32) 0x80fffa2c#32 := by
  refine ⟨?_,hf⟩
  intro i j
  have h := hs i ⟨320+j.val,by have := j.isLt;omega⟩
  have he : 0x80ffe9f0#32+BitVec.ofNat 32 (320+j.val)=(0x80ffeae0#32+80#32)+BitVec.ofNat 32 j.val := by
    rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
  rw [he] at h;exact h

theorem establishes (c : Core) (ram : Word → BitVec 8) (req rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8))) (state : Spec.Snapshot)
    (hp : c.pc=0x8000195a#32) (h2 : c.get 2=0x80ffeb90#32) (h24 : c.get 24=0x80fffa2c#32)
    (hm : Memory.Block B 0x80ff0000#32 65536) (h : Ready ram req rawPtr pathPtr bodyPtr raw path body entries first state) :
    ∃ a, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨a,ram⟩ ∧ a.get 1=0x8000196c#32 ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠1 → a.get r=c.get r) ∧ a.sameCsr c ∧
      WriteInput.Pre B a ram 0x80ffeae0#32 0x80fffa2c#32 0x80fffd38#32 req 0x80ffebbc#32 rawPtr pathPtr bodyPtr
        raw path body entries first true state := by
  obtain ⟨a,ta,pa,a10,a11,a1,fa,ka⟩ := MainWriteCaller.contract B c ram 0x80ffeb90#32 0x80fffa2c#32 h2 h24 hp
  have block (a : Word) (off n : Nat) (hn : 0<n) (he : 0x80ff0000#32+BitVec.ofNat 32 off=a) (hf : off+n≤65536) : Memory.Block B a n := by
    rw [←he];exact Memory.sub_block hm hn hf
  refine ⟨a,ta,a1,fa,ka,pa,?_,a11,?_,?_,?_,by decide,?_,h.fresh,h.request,h.engine,h.layout,?_,
    avoid h.requestStack h.requestFuture,avoid h.rawStack h.rawFuture,avoid h.pathStack h.pathFuture,avoid h.bodyStack h.bodyFuture⟩
  · rw [fa 2 (by decide) (by decide) (by decide),h2];decide +kernel
  · rw [a10];decide +kernel
  · exact block _ 60208 96 (by decide) (by decide +kernel) (by decide)
  · exact block _ 64044 41 (by decide) (by decide +kernel) (by decide)
  · exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide))
  · exact avoid (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
      (WordRegions.before _ _ _ _ (by decide) (by decide))
end E5R.Thermostat.MainWriteInput

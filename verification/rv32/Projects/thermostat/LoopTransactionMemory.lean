import Projects.thermostat.LoopReceiveRequest
set_option autoImplicit false
namespace E5R.Thermostat.LoopTransactionMemory
open E5R E5R.Thermostat
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32
/-- Exactly the RAM facts needed by completed->next-request execution. -/
structure At (ram : Word → BitVec 8) (used : Word) : Prop where
  headLimit : ramRead ram (fp+76#32) .w=1024#32
  bodyLimit : ramRead ram (fp+80#32) .w=1024#32
  filled : ramRead ram (fp+84#32) .w=used
  consumed : ramRead ram (fp+92#32) .w=used
  bound : used.toNat≤2048
  capacity : ramRead ram 0x80ffeba0#32 .w=2048#32
  routes : MainRouterTable.At ram

theorem preserve {before after : Word → BitVec 8} {used : Word} (h : At before used)
    (low : ViewFrame.Region before after fp 96) (cap : ViewFrame.Region before after 0x80ffeba0#32 4)
    (routes : ViewFrame.Region before after 0x80ffebd8#32 60) : At after used := by
  have capWord := ViewFrame.word cap 0 (by decide)
  simp only [BitVec.add_zero] at capWord
  exact ⟨(ViewFrame.word low 76 (by decide)).trans h.headLimit,(ViewFrame.word low 80 (by decide)).trans h.bodyLimit,
    (ViewFrame.word low 84 (by decide)).trans h.filled,(ViewFrame.word low 92 (by decide)).trans h.consumed,h.bound,
    capWord.trans h.capacity,MainRouterTable.preserve h.routes routes⟩

theorem caller {before after : Word → BitVec 8} {used : Word} (h : At before used)
    (frame : ViewFrame.Region before after sp 3304) : At after used := by
  apply preserve h
  · simpa only [show sp+3204#32=fp by decide +kernel] using HeadRegionFrame.sub frame 3204 96 (by decide)
  · simpa only [show sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub frame 16 4 (by decide)
  · simpa only [show sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub frame 72 60 (by decide)

/-- Reception plus actual Request stores establish filled=used; no leftover
    equality is introduced as an environment assumption. -/
theorem request {r : ApiRequestSpec.Fixed11} {c : Core} {ram : Word → BitVec 8} {s : Spec.Snapshot} {served : Nat}
    (h : MainRequestBuild.Ready c ram r.bytes s r.head r.body.length served)
    (capacity : ramRead ram 0x80ffeba0#32 .w=2048#32) (routes : MainRouterTable.At ram)
    (headLimit : ramRead ram (fp+76#32) .w=1024#32) (bodyLimit : ramRead ram (fp+80#32) .w=1024#32) :
    At ram (BitVec.ofNat 32 r.bytes.length) := by
  have total : r.head.len+r.body.length=r.bytes.length := List.length_append.symm
  have bound : r.bytes.length≤2048 := by
    change (r.headBytes++r.body).length≤2048
    rw [List.length_append];have headBound : r.headBytes.length≤1024 := r.headBound;have := r.bodyBound;omega
  exact ⟨headLimit,bodyLimit,h.stable.filled,h.usedWord.trans (congrArg (BitVec.ofNat 32) total),by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : r.bytes.length<2^32)];exact bound,capacity,routes⟩
end E5R.Thermostat.LoopTransactionMemory

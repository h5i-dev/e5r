import Projects.thermostat.UartWriteFresh
import Projects.thermostat.UartWriteNonempty
import Projects.thermostat.UartWriteMemory
namespace E5R.Thermostat.UartWritePrepare
open E5R E5R.Thermostat

def saved (ram : Word → BitVec 8) (obj io src len : Word) := UartWriteInputs.memory ram obj io src len
def remaining (ram : Word → BitVec 8) (obj io src len : Word) := UartWriteRemaining.memory (saved ram obj io src len) obj src len
def memory (ram : Word → BitVec 8) (obj io src len : Word) := UartWriteActive.memory (remaining ram obj io src len) obj io src len

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj io src len : Word)
    (hp : c.pc=0x80000786#32) (h10 : c.get 10=obj) (hm : Memory.Block B obj 41) (ha : obj.toNat%4=0)
    (hz : ram (obj+40#32)=0#8) (h0 : ramRead ram obj .w=io)
    (h4 : ramRead ram (obj+4#32) .w=src) (h8 : ramRead ram (obj+8#32) .w=len) (hne : len≠0#32) :
    ∃ d, Quiet.Steps B img 22 ⟨c,ram⟩ ⟨d,memory ram obj io src len⟩ ∧ d.pc=0x800007f4#32 ∧
      d.get 10=obj ∧ d.get 11=len ∧ d.get 12=src ∧ d.get 13=0x10000000#32 ∧ d.get 14=src+len ∧ d.get 15=0x10000000#32 ∧
      (∀ r : Reg, r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,_,a13,ar,ac⟩ := UartWriteFresh.contract B c ram obj h10 hm hz hp
  have a10 := (ar 10 (by decide) (by decide)).trans h10
  obtain ⟨b,tb,pb,b14,b11,b12,br,bc⟩ := UartWriteInputs.contract B a ram obj io src len a10 hm ha h0 h4 h8 pa
  have b10 := (br 10 (by decide) (by decide) (by decide)).trans a10
  obtain ⟨u,tu,pu,ur,uc⟩ := UartWriteRemaining.contract B b (saved ram obj io src len) obj src len b10 b11 b12 hm ha pb
  have u12 := (ur 12).trans b12
  obtain ⟨v,tv,pv,vr,vc⟩ := UartWriteNonempty.contract B u (remaining ram obj io src len) len u12 hne pu
  have v10 := (vr 10).trans ((ur 10).trans b10)
  have v11 := (vr 11).trans ((ur 11).trans b11)
  have v12 := (vr 12).trans u12
  have v13 := (vr 13).trans ((ur 13).trans ((br 13 (by decide) (by decide) (by decide)).trans a13))
  have hslot : ramRead (remaining ram obj io src len) (obj+12#32) .w=io :=
    (UartWriteMemory.remaining_io (saved ram obj io src len) obj src len).trans (UartWriteMemory.inputs_io ram obj io src len)
  obtain ⟨d,td,pd,d14,d11,d12,d15,dr,dc⟩ := UartWriteActive.contract B v (remaining ram obj io src len) obj io src len v10 v11 v12 hne hm ha hslot pv
  refine ⟨d,(((ta.trans tb).trans tu).trans tv).trans td,pd,?_,d11,d12,?_,d14,d15,?_,dc.trans (vc.trans (uc.trans (bc.trans ac)))⟩
  · exact (dr 10 (by decide) (by decide) (by decide) (by decide)).trans v10
  · exact (dr 13 (by decide) (by decide) (by decide) (by decide)).trans v13
  · intro reg h11 h12 h13 h14 h15
    exact (dr reg h14 h11 h12 h15).trans ((vr reg).trans ((ur reg).trans ((br reg h14 h11 h12).trans (ar reg h11 h13))))

theorem source (ram : Word → BitVec 8) (obj io src len : Word) : ramRead (memory ram obj io src len) (obj+16#32) .w=src :=
  (UartWriteMemory.active_src (remaining ram obj io src len) obj io src len).trans (UartWriteMemory.remaining_src (saved ram obj io src len) obj src len)

theorem length (ram : Word → BitVec 8) (obj io src len : Word) : ramRead (memory ram obj io src len) (obj+20#32) .w=len :=
  (UartWriteMemory.active_len (remaining ram obj io src len) obj io src len).trans (UartWriteMemory.remaining_len (saved ram obj io src len) obj src len)

theorem frame (ram : Word → BitVec 8) (obj io src len x : Word) (hx : ∀ i : Fin 41, x≠obj+BitVec.ofNat 32 i.val) : memory ram obj io src len x=ram x :=
  (UartWriteMemory.active_frame (remaining ram obj io src len) obj io src len x hx).trans
    ((UartWriteMemory.remaining_frame (saved ram obj io src len) obj src len x hx).trans (UartWriteMemory.inputs_frame ram obj io src len x hx))
end E5R.Thermostat.UartWritePrepare

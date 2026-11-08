import Projects.thermostat.UartWriteFresh
import Projects.thermostat.UartWriteEmpty
import Projects.thermostat.UartWriteMemory
import Projects.thermostat.UartWriteRegs
namespace E5R.Thermostat.UartWriteZero
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (obj io src : Word) :=
  UartWriteReturn.memory (UartWriteRemaining.memory (UartWriteInputs.memory ram obj io src 0#32) obj src 0#32) obj

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj io src : Word)
    (hp : c.pc=0x80000786#32) (h10 : c.get 10=obj) (hm : Memory.Block B obj 41) (ha : obj.toNat%4=0)
    (hz : ram (obj+40#32)=0#8) (h0 : ramRead ram obj .w=io)
    (h4 : ramRead ram (obj+4#32) .w=src) (h8 : ramRead ram (obj+8#32) .w=0#32) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,memory ram obj io src⟩ ∧ FormatCursor.Returned c d := by
  obtain ⟨a,ta,pa,_,_,ar,ac⟩ := UartWriteFresh.contract B c ram obj h10 hm hz hp
  have a10 := (ar 10 (by decide) (by decide)).trans h10
  obtain ⟨b,tb,pb,_,b11,b12,br,bc⟩ := UartWriteInputs.contract B a ram obj io src 0#32 a10 hm ha h0 h4 h8 pa
  have b10 := (br 10 (by decide) (by decide) (by decide)).trans a10
  obtain ⟨u,tu,pu,ur,uc⟩ := UartWriteRemaining.contract B b _ obj src 0#32 b10 b11 b12 hm ha pb
  obtain ⟨v,tv,pv,vr,vc⟩ := UartWriteEmpty.contract B u _ ((ur 12).trans b12) pu
  have v10 := (vr 10).trans ((ur 10).trans b10)
  obtain ⟨d,td,pd,_,dr,dc⟩ := UartWriteReturn.contract B v _ obj pv v10 hm
  have hf : UartWriteRegs.Frame c d := by
    intro reg h11 h12 h13 h14 _ _ _
    exact (dr reg h11).trans ((vr reg).trans ((ur reg).trans ((br reg h14 h11 h12).trans (ar reg h11 h13))))
  have v1 : v.get 1=c.get 1 := (vr 1).trans ((ur 1).trans ((br 1 (by decide) (by decide) (by decide)).trans (ar 1 (by decide) (by decide))))
  refine ⟨d,(((ta.trans tb).trans tu).trans tv).trans td,UartWriteRegs.returned (by rw [pd,v1]) (dc.trans (vc.trans (uc.trans (bc.trans ac)))) hf⟩

theorem source (ram : Word → BitVec 8) (obj io src : Word) : ramRead (memory ram obj io src) (obj+16#32) .w=src := by
  unfold memory UartWriteReturn.memory
  rw [StoreWords.read_other _ _ _ _ .b (StoreWords.offsets obj 16 4 40 1 (by decide) (by decide) (Or.inl (by decide)))]
  exact UartWriteMemory.remaining_src _ obj _ _

theorem length (ram : Word → BitVec 8) (obj io src : Word) : ramRead (memory ram obj io src) (obj+20#32) .w=0#32 := by
  unfold memory UartWriteReturn.memory
  rw [StoreWords.read_other _ _ _ _ .b (StoreWords.offsets obj 20 4 40 1 (by decide) (by decide) (Or.inl (by decide)))]
  exact UartWriteMemory.remaining_len _ obj _ _

theorem complete (ram : Word → BitVec 8) (obj io src : Word) : memory ram obj io src (obj+40#32)=1#8 := UartWriteReturn.complete _ obj

theorem frame (ram : Word → BitVec 8) (obj io src x : Word) (hx : ∀ i : Fin 41, x≠obj+BitVec.ofNat 32 i.val) : memory ram obj io src x=ram x :=
  (UartWriteMemory.returned_frame _ obj x hx).trans ((UartWriteMemory.remaining_frame _ obj src 0#32 x hx).trans (UartWriteMemory.inputs_frame ram obj io src 0#32 x hx))
end E5R.Thermostat.UartWriteZero

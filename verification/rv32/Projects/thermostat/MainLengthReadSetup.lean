import Projects.thermostat.MainLengthCapacityLoad
import Projects.thermostat.MainLengthCapacityBranch
import Projects.thermostat.MainLengthSliceMemory
import Projects.thermostat.MainLengthRoomBranch
import Projects.thermostat.MainHeaderLayout
import Projects.thermostat.HeadTargetMath
import Projects.thermostat.AppState
import Projects.thermostat.WordZero
import Projects.thermostat.HeadRegisterFrame
namespace E5R.Thermostat.MainLengthReadSetup
open E5R E5R.Thermostat
abbrev fp := 0x80fff814#32
abbrev rx := 0x80ffec14#32

def memory (ram : Word → BitVec 8) (filled : Nat) := MainLengthSliceSetup.memory ram fp (BitVec.ofNat 32 filled) rx 0x80ffffc7#32

theorem frame (ram : Word → BitVec 8) (filled : Nat) (x : Word)
    (apart : ∀ i : Fin 13, x≠(fp+456#32)+BitVec.ofNat 32 i.val) : memory ram filled x=ram x := by
  apply MainLengthSliceMemory.frame
  intro i
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using apart i

def writes : List Reg := [10,11,12,13,14]

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (filled : Nat)
    (hp : c.pc=0x80000c3a#32) (h8 : c.get 8=fp) (h10 : c.get 10=BitVec.ofNat 32 filled) (layout : MainHeaderLayout.At ram filled) (room : filled<2048)
    (stack : Memory.Block B 0x80ff0000#32 65536) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,memory ram filled⟩ ∧ d.pc=0x80000c6c#32 ∧
      d.get 12=rx+BitVec.ofNat 32 filled ∧ MainHeaderLayout.At (memory ram filled) filled ∧
      ViewFrame.Region ram (memory ram filled) fp 456 ∧ ViewFrame.Region ram (memory ram filled) rx 2048 ∧
      (∀ state, AppState.At ram state → AppState.At (memory ram filled) state) ∧ HeadRegisterFrame.At c d writes ∧ d.sameCsr c := by
  have object : Memory.Block B fp 469 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63508) (m := 469) stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using block
  obtain ⟨a,ta,apc,a11,ar,ac⟩ := MainLengthCapacityLoad.contract B c ram fp h8 layout.capacity object (by decide +kernel) hp
  have a10 : a.get 10=BitVec.ofNat 32 filled := (ar 10 (by decide)).trans h10
  have space : taken .geu 2048#32 (BitVec.ofNat 32 filled)=true := by
    simpa only [show decide (filled≤2048)=true from decide_eq_true layout.bound] using HeadTargetMath.geu 2048 filled (by decide) layout.bound
  obtain ⟨b,tb,bpc,br,bc⟩ := MainLengthCapacityBranch.contract B a ram 2048#32 _ true apc a11 a10 space
  have bpc' : b.pc=0x80000c44#32 := by simpa only [ite_true] using bpc
  have b8 : b.get 8=fp := (br 8).trans ((ar 8 (by decide)).trans h8)
  obtain ⟨z,tz,zpc,z12,_,_,zr,zc⟩ := MainLengthSliceSetup.contract B b ram fp (BitVec.ofNat 32 filled) rx 0x80ffffc7#32 b8
    ((br 10).trans a10) ((br 11).trans a11) layout.head.rx layout.uartPtr object (by decide +kernel) bpc'
  have notFull : 2048#32≠BitVec.ofNat 32 filled := by
    intro eq
    have same := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show filled<2^32 by omega)] at same
    omega
  have test : taken .ne 2048#32 (BitVec.ofNat 32 filled)=true := by simp [taken,notFull]
  obtain ⟨d,td,dpc,dr,dc⟩ := MainLengthRoomBranch.contract B z _ 2048#32 _ true zpc
    ((zr 11 (by decide) (by decide) (by decide)).trans ((br 11).trans a11))
    ((zr 10 (by decide) (by decide) (by decide)).trans ((br 10).trans a10)) test
  have future : ViewFrame.Region ram (memory ram filled) fp 456 := by
    intro i
    apply MainLengthSliceMemory.frame
    intro j
    exact WordZero.offset_ne fp i.val (456+j.val) (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;omega)
  have rxFrame : ViewFrame.Region ram (memory ram filled) rx 2048 := by
    intro i
    apply frame
    exact WordZero.separated rx (fp+456#32) 2048 13 (by decide +kernel) (by decide +kernel) i
  have appFrame : ∀ state, AppState.At ram state → AppState.At (memory ram filled) state := by
    intro state app
    apply AppState.preserve ram _ state app
    intro i
    apply frame
    exact WordZero.separated 0x80ffebbc#32 (fp+456#32) 25 13 (by decide +kernel) (by decide +kernel) i
  refine ⟨d,((ta.trans tb).trans tz).trans td,by simpa only [ite_true] using dpc,(dr 12).trans z12,
    MainHeaderLayout.preserve layout (fun i => future ⟨i.val,by have := i.isLt;omega⟩),future,rxFrame,appFrame,?_,((dc.trans zc).trans bc).trans ac⟩
  intro r safe
  have ne : ∀ r : Reg, r∉writes → r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠13 ∧ r≠14 := by decide +kernel
  obtain ⟨h10,h11,h12,h13,h14⟩ := ne r safe
  exact (dr r).trans ((zr r h12 h13 h14).trans ((br r).trans (ar r h11)))
end E5R.Thermostat.MainLengthReadSetup

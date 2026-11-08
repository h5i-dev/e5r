import Projects.thermostat.HeadClNumberLoop
import Projects.thermostat.HeadClNumberBound
import Projects.thermostat.HeadClStoreView
namespace E5R.Thermostat.HeadClNumber
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def updated (f : Fields) : Num → Fields
  | .bad _ => f
  | .ok value => {f with hasCl := true, cl := value}
def Post (ram after : Word → BitVec 8) (sp : Word) (d : Core) : Num → Prop
  | .bad status => d.pc=0x8000342c#32 ∧ d.get 1=BitVec.ofNat 32 status ∧ after=ram
  | .ok value => d.pc=0x800033b6#32 ∧ after=HeadClStoreRaw.memory ram sp (BitVec.ofNat 32 value)

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (pos finish length acc : Nat) (f : Fields)
    (hp : c.pc=0x80003206#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp)
    (h10 : c.get 10=buf+BitVec.ofNat 32 pos) (h31 : c.get 31=BitVec.ofNat 32 (length-pos))
    (h11 : c.get 11=BitVec.ofNat 32 (finish-pos))
    (h14 : c.get 14=BitVec.ofNat 32 acc) (h13 : c.get 13=0#32) (h16 : c.get 16=10#32)
    (hlimit : ramRead ram (sp+8#32) .w=1024#32) (inside : pos<finish) (upper : finish≤length)
    (bound : length≤2048) (accepted : acc≤1024) (memory : Memory.Block B buf length)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) (fields : HeadFieldsView.At ram sp f) :
    let result := clLoop (bytes ram buf) finish 1024 acc pos
    ∃ n d after, 0<n ∧ n≤5+30*(finish-pos) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Post ram after sp d result ∧ HeadFieldsView.At after sp (updated f result) ∧
      (∀ r : Reg, r≠1 → r≠30 → r≠12 → r≠29 → r≠14 → r≠13 → r≠11 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  have stack56 : Memory.Block B sp 56 := by
    simpa only [BitVec.add_zero] using (Memory.sub_block stack (off := 0) (m := 56) (by decide) (by decide))
  have stack327 : Memory.Block B sp 327 := by
    simpa only [BitVec.add_zero] using (Memory.sub_block stack (off := 0) (m := 327) (by decide) (by decide))
  obtain ⟨n,a,lo,hi,loop,post,frame,csr⟩ := HeadClNumberLoop.contract B c ram sp buf pos finish length acc hp h1 h2 h10 h31 h11 h14 h13 h16 hlimit inside upper bound accepted memory stack56 aligned
  cases result : clLoop (bytes ram buf) finish 1024 acc pos with
  | bad status =>
    have got : a.pc=0x8000342c#32 ∧ a.get 1=BitVec.ofNat 32 status := by simpa only [HeadClNumberLoop.Post,result] using post
    change ∃ n d after, _
    exact ⟨n,a,ram,lo,by omega,loop,⟨got.1,got.2,rfl⟩,fields,frame,csr⟩
  | ok value =>
    have got : a.pc=0x8000325e#32 ∧ a.get 14=BitVec.ofNat 32 value ∧ a.get 13=0#32 := by simpa only [HeadClNumberLoop.Post,result] using post
    have valueBound : value≤1024 := HeadClNumberBound.bound (bytes ram buf) finish 1024 acc pos value accepted result
    obtain ⟨d,store,pc,one,frame2,csr2⟩ := HeadClStoreRaw.contract B a ram sp (BitVec.ofNat 32 value)
      ((frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2)
      got.2.1 got.2.2 stack327 aligned got.1
    change ∃ n d after, _
    refine ⟨n+5,d,HeadClStoreRaw.memory ram sp (BitVec.ofNat 32 value),by omega,by omega,loop.trans store,
      ⟨pc,rfl⟩,HeadClStoreView.fields fields value valueBound,?_,csr2.trans csr⟩
    intro r h1 h30 h12 h29 h14 h13 h11 h10 h31
    exact (frame2 r h10).trans (frame r h1 h30 h12 h29 h14 h13 h11 h10 h31)
end E5R.Thermostat.HeadClNumber

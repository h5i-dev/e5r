import Projects.thermostat.SharedResponseLoad
import Projects.thermostat.SharedResponseFrame
namespace E5R.Thermostat.SharedResponse
open E5R E5R.Thermostat

def ioWord (ram : Word → BitVec 8) (fp : Word) (off : Nat) := extend .w true (ramRead ram (fp+BitVec.ofNat 32 off) .w)
def byteWord (ram : Word → BitVec 8) (fp : Word) (off : Nat) := extend .b false (ramRead ram (fp+BitVec.ofNat 32 off) .b)

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp sp capacity used status mimeLength mime extra : Word)
    (hp : c.pc=0x80001704#32) (h8 : c.get 8=fp) (h2 : c.get 2=sp) (h22 : c.get 22=1#32)
    (h20 : c.get 20=used) (h10 : c.get 10=status) (h11 : c.get 11=mimeLength) (h12 : c.get 12=mime) (h13 : c.get 13=extra)
    (hm : Memory.Block B fp 753) (ha : fp.toNat%4=0) (hs : Memory.Block B sp 24) (hsa : sp.toNat%4=0)
    (hcap : ramRead ram (fp+488#32) .w=capacity) (hfit : used.toNat≤capacity.toNat)
    (hsep : WordRegions.Disjoint fp 148 sp 24) :
    ∃ d r, DetSteps B img 26 ⟨c,ram⟩ ⟨d,r⟩ ∧ d.pc=0x80001772#32 ∧ d.sameCsr c ∧
      SharedResponseMemory.At r fp
        (ioWord (SharedResponseFlags.memory ram fp) fp 64) (ioWord (SharedResponseFlags.memory ram fp) fp 68)
        (ioWord (SharedResponseFlags.memory ram fp) fp 72) (c.get 6) status mimeLength mime
        (extra ||| byteWord (SharedResponseFlags.memory ram fp) fp 100)
        (byteWord (SharedResponseFlags.memory ram fp) fp 480+0xffffffff#32) used ∧
      (∀ reg : Reg, reg≠5 → reg≠12 → reg≠13 → reg≠14 → reg≠15 → reg≠16 → reg≠17 → d.get reg=c.get reg) ∧
      (∀ x, (∀ i : Fin 753, x≠fp+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 24, x≠sp+BitVec.ofNat 32 i.val) → r x=ram x) := by
  have block (n : Nat) (hn : 0<n) (hb : n≤753) : Memory.Block B fp n := by
    simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := n) hn (by simpa only [Nat.zero_add] using hb)
  let r0 := SharedResponseFlags.memory ram fp
  obtain ⟨a,ta,pa,_,ar,ac⟩ := SharedResponseFlags.contract B c ram fp capacity used hp h8 h22 h20 (block 668 (by decide) (by decide)) ha hcap hfit
  obtain ⟨b,tb,pb,b14,b15,b16,b17,b5,b13,br,bc⟩ := SharedResponseLoad.contract B a r0 fp extra
    ((ar 8 (by decide)).trans h8) ((ar 13 (by decide)).trans h13) (block 484 (by decide) (by decide)) ha pa
  have b2 := (br 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 2 (by decide)).trans h2)
  have b8 := (br 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 8 (by decide)).trans h8)
  have b6 : b.get 6=c.get 6 := (br 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (ar 6 (by decide))
  have b10 := (br 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 10 (by decide)).trans h10)
  have b11 := (br 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 11 (by decide)).trans h11)
  have b12 := (br 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 12 (by decide)).trans h12)
  have b20 := (br 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 20 (by decide)).trans h20)
  obtain ⟨d,td,pd,_,dr,dc⟩ := SharedResponseStore.contract B b r0 sp fp (ioWord r0 fp 64) (ioWord r0 fp 68) (ioWord r0 fp 72)
    (c.get 6) status mimeLength mime (extra ||| byteWord r0 fp 100) (byteWord r0 fp 480+0xffffffff#32) used
    pb b2 b5 b6 b8 b10 b11 b12 b13 b14 b16 b17 b20 (block 148 (by decide) (by decide)) ha hs hsa
  let final := SharedResponseStore.memory r0 sp fp (ioWord r0 fp 64) (ioWord r0 fp 68) (ioWord r0 fp 72)
    (c.get 6) status mimeLength mime (extra ||| byteWord r0 fp 100) (byteWord r0 fp 480+0xffffffff#32) used
  refine ⟨d,final,(ta.trans tb).trans td,pd,dc.trans (bc.trans ac),SharedResponseMemory.stored _ _ _ _ _ _ _ _ _ _ _ _ _ hsep,?_,?_⟩
  · intro reg h5 h12 h13 h14 h15 h16 h17
    exact (dr reg h12).trans ((br reg h14 h15 h16 h17 h5 h13).trans (ar reg h14))
  · intro x hfp hsp
    exact (SharedResponseFrame.stores _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfp hsp).trans (SharedResponseFrame.flags ram fp x hfp)
end E5R.Thermostat.SharedResponse

import Projects.thermostat.HeadZeroEntry271
import Projects.thermostat.HeadZeroWords
import Projects.thermostat.HeadZeroTail3
import Projects.thermostat.HeadZeroRet
namespace E5R.Thermostat.HeadZero271
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (p : Word) :=
  HeadZeroTail3.memory (WordZero.writes ram p 67) (p+268#32)

/-- The actual aligned zero-memset used by the header parser: 268 word bytes
    followed by three real byte stores, including the real ABI return. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (hp : c.pc=0x80005638#32) (h10 : c.get 10=p) (h11 : c.get 11=0#32) (h12 : c.get 12=271#32)
    (ha : p.toNat%4=0) (hm : Memory.Block B p 271) (htop : p.toNat+271<2^32) :
    ∃ d, Quiet.Steps B img 231 ⟨c,ram⟩ ⟨d,memory ram p⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      (∀ r : Reg, r≠12 → r≠13 → r≠14 → r≠15 → r≠16 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,entry,pc,endWord,base,len,zero,tmp,frame1,csr1⟩ := HeadZeroEntry271.contract B c ram p h10 h11 h12 ha htop hp
  have words : Memory.Block B p (4*67) := by
    simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 268) (by decide) (by decide)
  obtain ⟨b,loop,pc2,endWord2,frame2,csr2⟩ := HeadZeroWords.loop B a ram p 67 (by decide) pc base endWord zero ha words (by omega)
  have tailBlock : Memory.Block B (p+268#32) 3 := Memory.sub_block hm (off := 268) (by decide) (by decide)
  have tailTop : (p+268#32).toNat+3<2^32 := by
    rw [WordZero.add_nat p 268 (by omega)]
    omega
  obtain ⟨e,tail,pc3,last,tailEnd,tailPtr,frame3,csr3⟩ := HeadZeroTail3.contract B b (WordZero.writes ram p 67) (p+268#32)
    ((frame2 11 (by decide)).trans ((frame1 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11))
    ((frame2 12 (by decide)).trans len) ((frame2 13 (by decide)).trans endWord) tailBlock tailTop pc2
  obtain ⟨d,ret,pc4,frame4,csr4⟩ := HeadZeroRet.contract B e (memory ram p) pc3
  have source (r : Reg) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) (h15 : r≠15) (h16 : r≠16) : e.get r=c.get r :=
    (frame3 r h12 h14 h13).trans ((frame2 r h14).trans (frame1 r h13 h14 h12 h15 h16))
  refine ⟨d,((entry.trans loop).trans tail).trans ret,?_,?_,csr4.trans (csr3.trans (csr2.trans csr1))⟩
  · exact pc4.trans (congrArg (fun x => x &&& ~~~1) (source 1 (by decide) (by decide) (by decide) (by decide) (by decide)))
  · intro r h12 h13 h14 h15 h16
    exact (frame4 r).trans (source r h12 h13 h14 h15 h16)
end E5R.Thermostat.HeadZero271

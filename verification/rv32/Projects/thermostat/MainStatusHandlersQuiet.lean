-- G5-only Quiet dependency closure for the existing auth/decode refusal handlers.
-- Every original signature is retained, strengthening DetSteps to Quiet.Steps.
import Projects.thermostat.BearerAuthQuiet
import Projects.thermostat.BearerGuardQuiet
import Projects.thermostat.DecodeRefusal
import Projects.thermostat.HeaderCallerQuiet
import Projects.thermostat.OuterReturnQuiet
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.RefusalEntry
import Projects.thermostat.RequestAuthEnd
import Projects.thermostat.RequestAuthQuiet
import Projects.thermostat.RequestPrepare
import Projects.thermostat.RequestRefusal
import Projects.thermostat.StatusResponse
import Projects.thermostat.StatusReturn
import Projects.thermostat.WireCaller
import Projects.thermostat.WireCallerPrefixQuiet
import Projects.thermostat.WireQuiet
import Projects.thermostat.WireReject
import Projects.thermostat.WriteDecodeRefusal
import Projects.thermostat.WriteEntryQuiet
import Projects.thermostat.WriteInputQuiet
import Projects.thermostat.WriteRefusal
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace E5R.Thermostat.StatusResponse
open E5R E5R.Thermostat
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (out f status : Word)
    (hp : c.pc = 0x800005aa#32) (h8 : c.get 8 = f) (h9 : c.get 9 = out)
    (h10 : c.get 10 = 0#32) (h18 : c.get 18 = 0#32) (h20 : c.get 20 = status) (h22 : c.get 22 = 1#32)
    (ho : Memory.Block B out 15) (ha : out.toNat%4 = 0) (hf : Memory.Block B f 41) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,memory ram out f status⟩ ∧ d.pc = 0x800005c4#32 ∧
      (∀ r : Reg, r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 1#32 0x800005ac#32
  let c2 := c1.goto 0x800005ae#32
  let c3 := c2.goto 0x800005b0#32
  let c4 := c3.goto 0x800005b4#32
  let c5 := c4.goto 0x800005b8#32
  let c6 := c5.goto 0x800005bc#32
  let c7 := c6.goto 0x800005c0#32
  let c8 := c7.goto 0x800005c4#32
  let r1 := ramWrite ram (out+0#32) (1#32) .w
  let r2 := ramWrite r1 (out+4#32) (0#32) .w
  let r3 := ramWrite r2 (out+8#32) (0#32) .w
  let r4 := ramWrite r3 (out+12#32) (status) .h
  let r5 := ramWrite r4 (out+14#32) (0#32) .b
  let r6 := ramWrite r5 (f+36#32) (1#32) .b
  let r7 := ramWrite r6 (f+40#32) (1#32) .b
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wh2147485098) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine QuietDet.step_of (by change (0x800005ac#32).getLsbD 0 = false;decide) wh2147485100 fun o => ?_
    have hb : c1.get 9 = out := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c1.get 12 = 1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned out 0 ha) (Memory.block_access ho (off := 0) (width := 4) (by decide) (by decide))];rfl
  have s2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine QuietDet.step_of (by change (0x800005ae#32).getLsbD 0 = false;decide) wh2147485102 fun o => ?_
    have hb : c2.get 9 = out := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c2.get 10 = 0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned out 1 ha) (Memory.block_access ho (off := 4) (width := 4) (by decide) (by decide))];rfl
  have s3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine QuietDet.step_of (by change (0x800005b0#32).getLsbD 0 = false;decide) wh2147485104 fun o => ?_
    have hb : c3.get 9 = out := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c3.get 18 = 0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned out 2 ha) (Memory.block_access ho (off := 8) (width := 4) (by decide) (by decide))];rfl
  have s4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine QuietDet.step_of (by change (0x800005b4#32).getLsbD 0 = false;decide) wh2147485108 fun o => ?_
    have hb : c4.get 9 = out := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c4.get 20 = status := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .h) o
      (Memory.half_aligned out 6 (by omega)) (Memory.block_access ho (off := 12) (width := 2) (by decide) (by decide))];rfl
  have s5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine QuietDet.step_of (by change (0x800005b8#32).getLsbD 0 = false;decide) wh2147485112 fun o => ?_
    have hb : c5.get 9 = out := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c5.get 0 = 0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _) (Memory.block_access ho (off := 14) (width := 1) (by decide) (by decide))];rfl
  have s6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine QuietDet.step_of (by change (0x800005bc#32).getLsbD 0 = false;decide) wh2147485116 fun o => ?_
    have hb : c6.get 8 = f := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c6.get 22 = 1#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _) (Memory.block_access hf (off := 36) (width := 1) (by decide) (by decide))];rfl
  have s7 : Quiet.Step B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    refine QuietDet.step_of (by change (0x800005c0#32).getLsbD 0 = false;decide) wh2147485120 fun o => ?_
    have hb : c7.get 8 = f := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    have hv : c7.get 22 = 1#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h10,h18,h20,h22]
    rw [exec_store,hb,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _) (Memory.block_access hf (off := 40) (width := 1) (by decide) (by decide))];rfl
  refine ⟨c8,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.single s7))))))),rfl,?_,by rfl⟩
  intro r hr
  simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hr]
end E5R.Thermostat.StatusResponse

namespace E5R.Thermostat.RefusalEntry
open E5R E5R.Thermostat
theorem present_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x800005a2#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800005aa#32 ∧ d.get 10 = 0#32 ∧ d.get 18 = 0#32 ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 18 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 18 0#32 0x800005a4#32
  let c2 := c1.wr 10 0#32 0x800005a6#32
  let d := c2.goto 0x800005aa#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact rf2147485090) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005a4#32).getLsbD 0 = false;decide) rf2147485092 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800005a6#32).getLsbD 0 = false;decide) rf2147485094 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c2 0x800005aa#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c2,Core.wr_get]
  · simp [d,c2,c1,Core.wr_get]
  · intro r h10 h18
    simp [d,c2,c1,Core.wr_get_ne,h10,h18]
end E5R.Thermostat.RefusalEntry

namespace E5R.Thermostat.RefusalEntry
open E5R E5R.Thermostat
theorem missing_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x800005a8#32) (hz : c.get 10 = 0#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800005aa#32 ∧ d.get 10 = 0#32 ∧ d.get 18 = 0#32 ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 18 → d.get r = c.get r) ∧ d.sameCsr c := by
  let d := c.wr 18 0#32 0x800005aa#32
  have st : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact rf2147485096) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  refine ⟨d,.single st,rfl,?_,?_,?_,by rfl⟩
  · exact (Core.wr_get_ne _ _ _ _ _ (by decide)).trans hz
  · simp [d,Core.wr_get]
  · intro r h10 h18;exact Core.wr_get_ne _ _ _ _ _ h18
end E5R.Thermostat.RefusalEntry

namespace E5R.Thermostat.RefusalEntry
open E5R E5R.Thermostat
theorem choose_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800005a2#32 ∨ (c.pc = 0x800005a8#32 ∧ c.get 10 = 0#32)) :
    ∃ d n, n ≤ 3 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800005aa#32 ∧ d.get 10 = 0#32 ∧ d.get 18 = 0#32 ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 18 → d.get r = c.get r) ∧ d.sameCsr c := by
  rcases hp with hp|⟨hp,hz⟩
  · obtain ⟨d,ht,hpc,h10,h18,hf,hc⟩ := E5R.Thermostat.RefusalEntry.present_quiet B c ram hp
    exact ⟨d,3,by decide,ht,hpc,h10,h18,hf,hc⟩
  · obtain ⟨d,ht,hpc,h10,h18,hf,hc⟩ := E5R.Thermostat.RefusalEntry.missing_quiet B c ram hp hz
    exact ⟨d,1,by decide,ht,hpc,h10,h18,hf,hc⟩
end E5R.Thermostat.RefusalEntry

namespace E5R.Thermostat.StatusReturn
open E5R E5R.Thermostat
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (out f status : Word)
    (hp : c.pc = 0x800005aa#32) (h8 : c.get 8 = f) (h9 : c.get 9 = out)
    (h10 : c.get 10 = 0#32) (h18 : c.get 18 = 0#32) (h20 : c.get 20 = status) (h22 : c.get 22 = 1#32)
    (ho : Memory.Block B out 15) (ha : out.toNat%4 = 0) (hf : Memory.Block B f 41)
    (hst : Memory.Block B (c.get 2) 96) (hsa : (c.get 2).toNat%4 = 0)
    (hso : WordRegions.Disjoint (c.get 2) 96 out 15) (hsf : WordRegions.Disjoint (c.get 2) 96 f 41)
    (hof : WordRegions.Disjoint out 15 f 41) :
    ∃ d, Quiet.Steps B img 23 ⟨c,ram⟩ ⟨d,StatusResponse.memory ram out f status⟩ ∧
      d.pc = ramRead ram (c.get 2+92#32) .w &&& ~~~1 ∧ d.get 2 = c.get 2+96#32 ∧ d.sameCsr c ∧
      OuterReturn.Restored c d ram ∧ StatusMemory.At (StatusResponse.memory ram out f status) out status ∧
      StatusResponse.memory ram out f status (f+36#32) = 1#8 ∧
      StatusResponse.memory ram out f status (f+40#32) = 1#8 := by
  obtain ⟨a,ta,apc,aframe,acsr⟩ := E5R.Thermostat.StatusResponse.contract_quiet B c ram out f status hp h8 h9 h10 h18 h20 h22 ho ha hf
  have asp : a.get 2 = c.get 2 := aframe 2 (by decide)
  have hr : ViewFrame.Region ram (StatusResponse.memory ram out f status) (c.get 2) 96 := by
    intro i
    exact StatusMemory.frame ram out f status _ (hso i) (hsf i)
  have hw (k : Nat) (hk : k+4 ≤ 96) :
      ramRead (StatusResponse.memory ram out f status) (a.get 2+BitVec.ofNat 32 k) .w =
        ramRead ram (c.get 2+BitVec.ofNat 32 k) .w := by
    rw [asp];exact ViewFrame.word hr k hk
  obtain ⟨d,td,dpc,dsp,dcsr,dsaved⟩ := E5R.Thermostat.OuterReturn.contract_quiet B a (StatusResponse.memory ram out f status) apc
    (by simpa only [asp] using hst) (by simpa only [asp] using hsa)
  refine ⟨d,ta.trans td,?_,by simpa only [asp] using dsp,dcsr.trans acsr,?_,StatusMemory.response ram out f status hof,
    (StatusMemory.flags ram out f status).1,(StatusMemory.flags ram out f status).2⟩
  · rw [dpc,hw 92 (by decide)]
  · constructor
    · exact dsaved.x1 |>.trans (hw 92 (by decide))
    · exact dsaved.x8 |>.trans (hw 88 (by decide))
    · exact dsaved.x9 |>.trans (hw 84 (by decide))
    · exact dsaved.x18 |>.trans (hw 80 (by decide))
    · exact dsaved.x19 |>.trans (hw 76 (by decide))
    · exact dsaved.x20 |>.trans (hw 72 (by decide))
    · exact dsaved.x21 |>.trans (hw 68 (by decide))
    · exact dsaved.x22 |>.trans (hw 64 (by decide))
    · exact dsaved.x23 |>.trans (hw 60 (by decide))
    · exact dsaved.x24 |>.trans (hw 56 (by decide))
    · exact dsaved.x25 |>.trans (hw 52 (by decide))
    · exact dsaved.x26 |>.trans (hw 48 (by decide))
    · exact dsaved.x27 |>.trans (hw 44 (by decide))
end E5R.Thermostat.StatusReturn

namespace E5R.Thermostat.RequestAuthEnd
open E5R E5R.Thermostat
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req rawPtr eng sp : Word)
    (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry) (h : Header.Pre B ram req rawPtr raw entries)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hp : c.pc = 0x8000052e#32) (h21 : c.get 21 = req) (h23 : c.get 23 = eng) (hsp : c.get 2 = sp)
    (hm : Memory.Block B eng 24) (ha : eng.toNat%4 = 0) (hs : Memory.Block B sp 25)
    (hlen : ramRead ram (eng+20#32) .w = 7#32) (hkey : ramRead ram (eng+16#32) .w = 0x80005b7c#32) :
    ∃ d n, n ≤ 212*entries.length+145 ∧ Quiet.Steps B img n ⟨c,ram⟩
      ⟨d,RequestAuth.memory ram sp (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)⟩ ∧
      d.pc = RequestAuth.endPc (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) ∧
      d.get 20 = 401#32 ∧ d.get 22 = 1#32 ∧ RequestAuth.Frame c d ∧ d.sameCsr c ∧
      (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries = none → d.get 10 = 0#32) := by
  obtain ⟨a,n,hn,ta,apc,hresult,aframe,acsr⟩ := E5R.Thermostat.HeaderCaller.contract_quiet B c ram req rawPtr raw entries h hquery hp h21
  have asp : a.get 2 = sp := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp
  have a23 : a.get 23 = eng := (aframe 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23
  cases hv : HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries with
  | none =>
    rw [hv] at hresult
    obtain ⟨d,k,hk,td,dpc,d20,d22,dframe,dcsr⟩ := E5R.Thermostat.BearerGuard.contract_quiet B a ram 0#32 (a.get 11).toNat
      (a.get 11).isLt apc hresult (by simp)
    have dpc' : d.pc = 0x800005a8#32 := by simpa only [ite_true] using dpc
    refine ⟨d,n+k,by omega,?_,by simpa only [hv,RequestAuth.endPc] using dpc',d20,d22,?_,dcsr.trans acsr,?_⟩
    · simpa only [hv,RequestAuth.memory] using ta.trans td
    · intro r h1 h5 h6 h7 h20 h22 h24 h25 h28 h29 hr
      exact (dframe r (Header.outside r 12 hr (by decide)) h20 h22).trans (aframe r h1 h5 h6 h7 h28 h29 hr)
    · intro _;exact (dframe 10 (by decide) (by decide) (by decide)).trans hresult
  | some header =>
    rw [hv] at hresult
    obtain ⟨nonzero,alen,hspan⟩ := hresult
    obtain ⟨d,k,hk,td,dpc,d20,d22,dframe,dcsr⟩ := E5R.Thermostat.BearerAuth.contract_quiet B a ram eng sp (a.get 10) header hspan nonzero
      hprefix hkeybytes apc asp a23 rfl alen hm ha hs hlen hkey
    refine ⟨d,n+k,by omega,?_,?_,d20,d22,?_,dcsr.trans acsr,?_⟩
    · simpa only [hv,RequestAuth.memory] using ta.trans td
    · simpa only [hv,RequestAuth.endPc,BearerAuth.matches_auth_spec] using dpc
    · intro r h1 h5 h6 h7 h20 h22 h24 h25 h28 h29 hr
      exact (dframe r h1 h20 h22 h24 h25 (by omega)).trans (aframe r h1 h5 h6 h7 h28 h29 hr)
    · intro hn;cases hn
end E5R.Thermostat.RequestAuthEnd

namespace E5R.Thermostat.RequestRefusal
open E5R E5R.Thermostat
theorem contract_inv_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr out f : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot)
    (h : TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (h8 : c.get 8 = f) (h9 : c.get 9 = out)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hdeny : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = false)
    (hi : Spec.Inv s)
    (ho : Memory.Block B out 15) (hoa : out.toNat%4 = 0) (hf : Memory.Block B f 41)
    (hst : Memory.Block B (p+80#32) 96)
    (hso : WordRegions.Disjoint (p+80#32) 96 out 15) (hsf : WordRegions.Disjoint (p+80#32) 96 f 41)
    (hof : WordRegions.Disjoint out 15 f 41)
    (heo : WordRegions.Disjoint eng 25 out 15) (hef : WordRegions.Disjoint eng 25 f 41) :
    ∃ d n, n ≤ 212*entries.length+171 ∧ Quiet.Steps B img n ⟨c,ram⟩
      ⟨d,memory ram (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)⟩ ∧
      d.pc = ramRead ram ((p+80#32)+92#32) .w &&& ~~~1 ∧ d.get 2 = (p+80#32)+96#32 ∧ d.sameCsr c ∧
      OuterReturn.Restored c d ram ∧
      StatusMemory.At (memory ram (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) out 401#32 ∧
      Encoding.SnapshotAt (memory ram (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) (eng+4#32) s ∧
      ramRead (memory ram (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) eng .w = 0#32 ∧
      Engine.InvariantAt (memory ram (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries)) eng := by
  let value := HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries
  let aram := RequestAuth.memory ram (p+80#32) value
  have happ24 : Memory.Block B eng 24 := by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 24) h.app (by decide) (by decide)
  obtain ⟨a,n,hn,ta,apc,a20,a22,aframe,acsr,az⟩ := E5R.Thermostat.RequestAuthEnd.contract_quiet B c ram req rawPtr eng (p+80#32) raw entries
    h.headers hquery hprefix hkeybytes h.pc h.request h.engine h.sp happ24 h.appAligned
    (Memory.sub_block h.arena (by decide) (by decide)) h.keyLength h.keyPointer
  have a8 : a.get 8 = f := (aframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
  have a9 : a.get 9 = out := (aframe 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9
  have asp : a.get 2 = p+80#32 := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.sp
  obtain ⟨z,k,hk,tz,zpc,z10,z18,zframe,zcsr⟩ := E5R.Thermostat.RefusalEntry.choose_quiet B a aram (end_branch apc az hdeny)
  have z8 : z.get 8 = f := (zframe 8 (by decide) (by decide)).trans a8
  have z9 : z.get 9 = out := (zframe 9 (by decide) (by decide)).trans a9
  have z20 : z.get 20 = 401#32 := (zframe 20 (by decide) (by decide)).trans a20
  have z22 : z.get 22 = 1#32 := (zframe 22 (by decide) (by decide)).trans a22
  have zsp : z.get 2 = p+80#32 := (zframe 2 (by decide) (by decide)).trans asp
  obtain ⟨d,td,dpc,dsp,dcsr,dsaved,dresponse,_,_⟩ := E5R.Thermostat.StatusReturn.contract_quiet B z aram out f 401#32
    zpc z8 z9 z10 z18 z20 z22 ho hoa hf
    (by simpa only [zsp] using hst) (by simpa only [zsp] using Memory.word_aligned p 20 h.aligned)
    (by simpa only [zsp] using hso) (by simpa only [zsp] using hsf) hof
  have hstack (off : Nat) (ho : 44 ≤ off) (hb : off+4 ≤ 96) :
      ramRead aram (z.get 2+BitVec.ofNat 32 off) .w = ramRead ram (c.get 2+BitVec.ofNat 32 off) .w := by
    rw [zsp,h.sp]
    apply ramRead_w_congr
    intro i hi
    apply RequestAuth.memory_frame
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact Bytes.offset_ne (p+80#32) (off+i) 24 (by omega) (by decide) (by omega)
  have he : ViewFrame.Region ram (memory ram (p+80#32) out f value) eng 25 := by
    intro i
    exact (StatusMemory.frame aram out f 401#32 _ (heo i) (hef i)).trans
      (TxnScratch.auth_region ram p eng 25 value h.appSeparate i)
  have hs := ViewFrame.snapshot h.state he
  have hw : ramRead (memory ram (p+80#32) out f value) eng .w = 0#32 := by
    have hh := ViewFrame.word he 0 (by decide)
    simpa only [BitVec.add_zero,h.borrow] using hh
  refine ⟨d,n+k+23,by omega,(ta.trans tz).trans td,?_,by simpa only [zsp] using dsp,
    (dcsr.trans zcsr).trans acsr,?_,dresponse,hs,hw,⟨s,hs,hi⟩⟩
  · rw [dpc,hstack 92 (by decide) (by decide),h.sp]
  · constructor
    · exact dsaved.x1 |>.trans (hstack 92 (by decide) (by decide))
    · exact dsaved.x8 |>.trans (hstack 88 (by decide) (by decide))
    · exact dsaved.x9 |>.trans (hstack 84 (by decide) (by decide))
    · exact dsaved.x18 |>.trans (hstack 80 (by decide) (by decide))
    · exact dsaved.x19 |>.trans (hstack 76 (by decide) (by decide))
    · exact dsaved.x20 |>.trans (hstack 72 (by decide) (by decide))
    · exact dsaved.x21 |>.trans (hstack 68 (by decide) (by decide))
    · exact dsaved.x22 |>.trans (hstack 64 (by decide) (by decide))
    · exact dsaved.x23 |>.trans (hstack 60 (by decide) (by decide))
    · exact dsaved.x24 |>.trans (hstack 56 (by decide) (by decide))
    · exact dsaved.x25 |>.trans (hstack 52 (by decide) (by decide))
    · exact dsaved.x26 |>.trans (hstack 48 (by decide) (by decide))
    · exact dsaved.x27 |>.trans (hstack 44 (by decide) (by decide))
end E5R.Thermostat.RequestRefusal

namespace E5R.Thermostat.WriteRefusal
open E5R E5R.Thermostat
theorem contract_inv_quiet (c : Core) (ram : Word → BitVec 8) (p f out req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot)
    (h : WriteInput.Pre UartPlatform.board c ram p f out req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hdeny : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = false)
    (hi : Spec.Inv s) (ho : Memory.Block UartPlatform.board out 15) (hoa : out.toNat%4 = 0)
    (hso : WordRegions.Disjoint (p+80#32) 96 out 15) (hof : WordRegions.Disjoint out 15 f 41)
    (heo : WordRegions.Disjoint eng 25 out 15) :
    ∃ d n r, n ≤ 212*entries.length+202 ∧ Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Returned c d ∧ StatusMemory.At r out 401#32 ∧ Encoding.SnapshotAt r (eng+4#32) s ∧
      ramRead r eng .w = 0#32 ∧ Engine.InvariantAt r eng ∧ r (f+36#32) = 1#8 ∧ r (f+40#32) = 1#8 := by
  let r0 := WriteStart.memory ram (p+80#32) f c
  obtain ⟨a,ta,ha,a8,a9,_,_,acsr⟩ := E5R.Thermostat.WriteInput.establishes_quiet h
  obtain ⟨d,n,hn,td,dpc,dsp,dcsr,dsaved,dresponse,ds,db,di⟩ := E5R.Thermostat.RequestRefusal.contract_inv_quiet UartPlatform.board a r0
    p req eng rawPtr pathPtr bodyPtr out f raw path body entries first admin s ha a8 a9
    (AuthLiterals.header _) (AuthLiterals.bearer _) (AuthLiterals.key _) hdeny hi ho hoa h.futureBlock h.stack hso
    (WordRegions.symm h.futureSeparate) hof heo h.appAvoid.2
  have hword (k : Nat) (hk : k+4 ≤ 96) :
      ramRead r0 (a.get 2+BitVec.ofNat 32 k) .w = ramRead (OuterSave.memory ram (p+80#32) c) ((p+80#32)+BitVec.ofNat 32 k) .w := by
    rw [ha.sp]
    exact ViewFrame.word (WriteStart.saved_region ram (p+80#32) f c h.futureSeparate) k hk
  have hs := OuterSave.saved ram (p+80#32) c
  have hra : ramRead r0 ((p+80#32)+92#32) .w = c.get 1 :=
    (ViewFrame.word (WriteStart.saved_region ram (p+80#32) f c h.futureSeparate) 92 (by decide)).trans hs.1
  refine ⟨d,31+n,RequestRefusal.memory r0 (p+80#32) out f (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries),
    by omega,ta.trans td,?_,dresponse,ds,db,di,
    (StatusMemory.flags _ out f 401#32).1,(StatusMemory.flags _ out f 401#32).2⟩
  refine ⟨by rw [dpc,hra],dsp.trans h.sp.symm,dcsr.trans acsr,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact dsaved.x1 |>.trans ((hword 92 (by decide)).trans hs.1)
  · exact dsaved.x8 |>.trans ((hword 88 (by decide)).trans hs.2.1)
  · exact dsaved.x9 |>.trans ((hword 84 (by decide)).trans hs.2.2.1)
  · exact dsaved.x18 |>.trans ((hword 80 (by decide)).trans hs.2.2.2.1)
  · exact dsaved.x19 |>.trans ((hword 76 (by decide)).trans hs.2.2.2.2.1)
  · exact dsaved.x20 |>.trans ((hword 72 (by decide)).trans hs.2.2.2.2.2.1)
  · exact dsaved.x21 |>.trans ((hword 68 (by decide)).trans hs.2.2.2.2.2.2.1)
  · exact dsaved.x22 |>.trans ((hword 64 (by decide)).trans hs.2.2.2.2.2.2.2.1)
  · exact dsaved.x23 |>.trans ((hword 60 (by decide)).trans hs.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x24 |>.trans ((hword 56 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x25 |>.trans ((hword 52 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x26 |>.trans ((hword 48 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x27 |>.trans ((hword 44 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.2.2)
end E5R.Thermostat.WriteRefusal

namespace E5R.Thermostat.WireCaller
open E5R E5R.Thermostat
theorem error_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (status : Nat)
    (hp : c.pc = 0x800005f4#32) (h : WireSpec.ResultWord (c.get 10) (.error status)) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800005a2#32 ∧
      (d.get 20).toNat = status ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 20 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,td,pcd,v20,v10,rd,cd⟩ := E5R.Thermostat.WireCallerPrefix.contract_quiet B c ram (c.get 10) hp rfl
  exact ⟨d,td,by simpa only [ite_eq_left h.1] using pcd,by rw [v20];exact h.2,rd,cd⟩
end E5R.Thermostat.WireCaller

namespace E5R.Thermostat.WireReject
open E5R E5R.Thermostat
theorem rejected_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p req pathPtr bodyPtr : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (status : Nat)
    (hwire : Wire.Pre B c ram (p+64#32) req pathPtr bodyPtr path body first)
    (hlayout : DecodedEngine.Pre B (c.goto 0x800005f4#32) ram p admin s)
    (hra : c.get 1 = 0x800005f4#32) (hdecode : WireSpec.decode path body first = .error status) :
    ∃ n d, n ≤ 18*body.length+307 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,DecodeSave.memory ram (p+64#32) c⟩ ∧
      d.pc = 0x800005a2#32 ∧ (d.get 20).toNat = status ∧
      Encoding.SnapshotAt (DecodeSave.memory ram (p+64#32) c) (c.get 23+4#32) s ∧
      ramRead (DecodeSave.memory ram (p+64#32) c) (c.get 23) .w = 0#32 ∧ d.get 2 = c.get 2 ∧ d.get 8 = c.get 8 ∧ d.get 9 = c.get 9 ∧
      d.get 22 = c.get 22 ∧ d.get 23 = c.get 23 ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ht,hpost⟩ := E5R.Thermostat.Wire.contract_quiet B c ram (p+64#32) req pathPtr bodyPtr path body first hwire
  have hlayout'  := WireEngine.layout B c a ram p path body first admin s hlayout hra hpost
  have he : WireSpec.ResultWord (a.get 10) (.error status) := by
    have hh := hpost.result;rw [hdecode] at hh;exact hh
  obtain ⟨d,td,hpc,hstatus,dframe,dcsr⟩ := E5R.Thermostat.WireCaller.error_quiet B a (DecodeSave.memory ram (p+64#32) c) status hlayout'.pc he
  have h23 : a.get 23 = c.get 23 := hpost.frame 23 (by decide)
  exact ⟨n+4,d,by omega,ht.trans td,hpc,hstatus,by simpa only [h23] using hlayout'.state,
    by simpa only [h23] using hlayout'.borrow,
    (dframe 2 (by decide) (by decide) (by decide)).trans hpost.sp,
    (dframe 8 (by decide) (by decide) (by decide)).trans hpost.s0,
    (dframe 9 (by decide) (by decide) (by decide)).trans hpost.s1,
    (dframe 22 (by decide) (by decide) (by decide)).trans (hpost.frame 22 (by decide)),
    (dframe 23 (by decide) (by decide) (by decide)).trans h23,dcsr.trans hpost.csr⟩
end E5R.Thermostat.WireReject

namespace E5R.Thermostat.RequestPrepare
open E5R E5R.Thermostat
theorem prepare_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot)
    (h : TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
 :
    ∃ b n, n ≤ 212*entries.length+150 ∧ Quiet.Steps B img n ⟨c,ram⟩
      ⟨b,TxnScratch.memory ram (p+80#32) (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) admin⟩ ∧
      Wire.Pre B b (TxnScratch.memory ram (p+80#32) (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) admin)
        (p+64#32) req pathPtr bodyPtr path body first ∧
      DecodedEngine.Pre B (b.goto 0x800005f4#32)
        (TxnScratch.memory ram (p+80#32) (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) admin) p admin s ∧
      b.get 1 = 0x800005f4#32 ∧ b.get 2 = c.get 2 ∧ b.get 23 = c.get 23 ∧ b.sameCsr c ∧ b.get 8 = c.get 8 ∧ b.get 9 = c.get 9 ∧ b.get 22 = 1#32 := by
  let value := HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries
  let aram := RequestAuth.memory ram (p+80#32) value
  let bram := TxnScratch.memory ram (p+80#32) value admin
  have hsp25 : Memory.Block B (p+80#32) 25 := Memory.sub_block h.arena (by decide) (by decide)
  have hsp10 : Memory.Block B (p+80#32) 10 := Memory.sub_block h.arena (by decide) (by decide)
  have happ24 : Memory.Block B eng 24 := by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 24) h.app (by decide) (by decide)
  obtain ⟨a,n,hn,ta,apc,_,a22,aframe,acsr⟩ := E5R.Thermostat.RequestAuth.contract_quiet B c ram req rawPtr eng (p+80#32) raw entries
    h.headers hquery hprefix hkeybytes h.pc h.request h.engine h.sp happ24 h.appAligned hsp25 h.keyLength h.keyPointer
  have apc' : a.pc = 0x800005e2#32 := apc.trans (RequestTransaction.authorized_pc value hallow)
  have asp : a.get 2 = p+80#32 := (aframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.sp
  have a21 : a.get 21 = req := (aframe 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.request
  have a23 : a.get 23 = eng := (aframe 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.engine
  have haAdmin : aram (eng+24#32) = Encoding.boolByte admin := by
    have hr := TxnScratch.auth_region ram p eng 25 value h.appSeparate
    have hh := hr ⟨24,by decide⟩
    exact hh.trans h.principal
  obtain ⟨b,tb,bpc,b10,b1,bframe,bcsr⟩ := E5R.Thermostat.WriteEntry.contract_quiet B a aram eng (p+80#32) req admin apc' a23 asp a21 h.app hsp10 haAdmin
  have bsp : b.get 2 = p+80#32 := (bframe 2 (by decide) (by decide)).trans asp
  have b23 : b.get 23 = eng := (bframe 23 (by decide) (by decide)).trans a23
  have hb23 : b.get 23 = c.get 23 := b23.trans h.engine.symm
  have hwire := TxnInput.wire_pre B c b ram p req eng rawPtr pathPtr bodyPtr raw path body entries first value admin s h bpc bsp b10
  have hlayout := TxnInput.decoded_layout B c b ram p req eng rawPtr pathPtr bodyPtr raw path body entries first value admin s h bsp b23
  have a8 := aframe 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have a9 := aframe 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨b,n+5,by omega,ta.trans tb,hwire,hlayout,b1,bsp.trans h.sp.symm,hb23,bcsr.trans acsr,
    (bframe 8 (by decide) (by decide)).trans a8,(bframe 9 (by decide) (by decide)).trans a9,
    (bframe 22 (by decide) (by decide)).trans a22⟩
end E5R.Thermostat.RequestPrepare

namespace E5R.Thermostat.DecodeRefusal
open E5R E5R.Thermostat
theorem contract_inv_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr out f : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (status : Nat)
    (h : TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (h8 : c.get 8 = f) (h9 : c.get 9 = out)
    (hquery : ReadBytes.Span B img ram 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hprefix : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hkeybytes : ReadBytes.Span B img ram 0x80005b7c#32 (WireSpec.ascii "dev-key"))
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .error status)
    (hi : Spec.Inv s)
    (ho : Memory.Block B out 15) (hoa : out.toNat%4 = 0) (hf : Memory.Block B f 41)
    (hst : Memory.Block B (p+80#32) 96)
    (hso : WordRegions.Disjoint (p+80#32) 96 out 15) (hsf : WordRegions.Disjoint (p+80#32) 96 f 41)
    (hof : WordRegions.Disjoint out 15 f 41)
    (heo : WordRegions.Disjoint eng 25 out 15) (hef : WordRegions.Disjoint eng 25 f 41) :
    ∃ d n r, n ≤ 212*entries.length+18*body.length+483 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = ramRead ram ((p+80#32)+92#32) .w &&& ~~~1 ∧ d.get 2 = (p+80#32)+96#32 ∧ d.sameCsr c ∧
      OuterReturn.Restored c d ram ∧ StatusMemory.At r out (BitVec.ofNat 32 status) ∧
      Encoding.SnapshotAt r (eng+4#32) s ∧ ramRead r eng .w = 0#32 ∧ Engine.InvariantAt r eng ∧ r (f+36#32) = 1#8 ∧ r (f+40#32) = 1#8 := by
  let value := HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries
  let bram := TxnScratch.memory ram (p+80#32) value admin
  obtain ⟨b,n,hn,ta,hwire,hlayout,b1,bsp,hb23,bcsr,b8,b9,b22⟩ := E5R.Thermostat.RequestPrepare.prepare_quiet B c ram p req eng rawPtr pathPtr bodyPtr
    raw path body entries first admin s h hquery hprefix hkeybytes hallow
  let aram := DecodeSave.memory bram (p+64#32) b
  obtain ⟨k,a,hk,tw,apc,astatus,asnap,aborrow,asp',a8',a9',a22',a23',acsr'⟩ :=
    E5R.Thermostat.WireReject.rejected_quiet B b bram p req pathPtr bodyPtr path body first admin s status hwire hlayout b1 hdecode
  have a8 : a.get 8 = f := (a8'.trans b8).trans h8
  have a9 : a.get 9 = out := (a9'.trans b9).trans h9
  have a22 : a.get 22 = 1#32 := a22'.trans b22
  have a20 : a.get 20 = BitVec.ofNat 32 status := by rw [←astatus];simp
  have asp : a.get 2 = p+80#32 := (asp'.trans bsp).trans h.sp
  have b23 : b.get 23 = eng := hb23.trans h.engine
  have acsr : a.sameCsr c := acsr'.trans bcsr
  obtain ⟨z,tz,zpc,z10,z18,zframe,zcsr⟩ := E5R.Thermostat.RefusalEntry.present_quiet B a aram apc
  have z8 : z.get 8 = f := (zframe 8 (by decide) (by decide)).trans a8
  have z9 : z.get 9 = out := (zframe 9 (by decide) (by decide)).trans a9
  have z20 : z.get 20 = BitVec.ofNat 32 status := (zframe 20 (by decide) (by decide)).trans a20
  have z22 : z.get 22 = 1#32 := (zframe 22 (by decide) (by decide)).trans a22
  have zsp : z.get 2 = p+80#32 := (zframe 2 (by decide) (by decide)).trans asp
  obtain ⟨d,td,dpc,dsp,dcsr,dsaved,dresponse,dflag36,dflag40⟩ := E5R.Thermostat.StatusReturn.contract_quiet B z aram out f (BitVec.ofNat 32 status)
    zpc z8 z9 z10 z18 z20 z22 ho hoa hf
    (by simpa only [zsp] using hst) (by simpa only [zsp] using Memory.word_aligned p 20 h.aligned)
    (by simpa only [zsp] using hso) (by simpa only [zsp] using hsf) hof
  have hstack (off : Nat) (ho : 44 ≤ off) (hb : off+4 ≤ 96) :
      ramRead aram (z.get 2+BitVec.ofNat 32 off) .w = ramRead ram (c.get 2+BitVec.ofNat 32 off) .w := by
    rw [zsp,h.sp]
    apply ramRead_w_congr
    intro i hi
    change DecodeSave.memory bram (p+64#32) b (((p+80#32)+BitVec.ofNat 32 off)+BitVec.ofNat 32 i) = _
    rw [DecodeSave.frame bram (p+64#32) b _ (by
      intro j
      have hj := j.isLt
      have hh := Bytes.offset_ne p (80+off+i) (64+j.val) (by omega) (by omega) (by omega)
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hh)]
    apply TxnScratch.frame
    · have hh := Bytes.offset_ne (p+80#32) (off+i) 9 (by omega) (by decide) (by omega)
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hh
    · have hh := Bytes.offset_ne (p+80#32) (off+i) 24 (by omega) (by decide) (by omega)
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hh
  let final := StatusResponse.memory aram out f (BitVec.ofNat 32 status)
  have he : ViewFrame.Region aram final eng 25 := by
    intro i
    exact StatusMemory.frame aram out f (BitVec.ofNat 32 status) _ (heo i) (hef i)
  have hs0 : Encoding.SnapshotAt aram (eng+4#32) s := by simpa only [b23] using asnap
  have hs := ViewFrame.snapshot hs0 he
  have hw : ramRead final eng .w = 0#32 := by
    have hh := ViewFrame.word he 0 (by decide)
    simp only [BitVec.add_zero] at hh
    exact hh.trans (by simpa only [b23] using aborrow)
  refine ⟨d,n+k+26,final,by omega,((ta.trans tw).trans tz).trans td,?_,by simpa only [zsp] using dsp,
    (dcsr.trans zcsr).trans acsr,?_,dresponse,hs,hw,⟨s,hs,hi⟩,dflag36,dflag40⟩
  · rw [dpc,hstack 92 (by decide) (by decide),h.sp]
  · constructor
    · exact dsaved.x1 |>.trans (hstack 92 (by decide) (by decide))
    · exact dsaved.x8 |>.trans (hstack 88 (by decide) (by decide))
    · exact dsaved.x9 |>.trans (hstack 84 (by decide) (by decide))
    · exact dsaved.x18 |>.trans (hstack 80 (by decide) (by decide))
    · exact dsaved.x19 |>.trans (hstack 76 (by decide) (by decide))
    · exact dsaved.x20 |>.trans (hstack 72 (by decide) (by decide))
    · exact dsaved.x21 |>.trans (hstack 68 (by decide) (by decide))
    · exact dsaved.x22 |>.trans (hstack 64 (by decide) (by decide))
    · exact dsaved.x23 |>.trans (hstack 60 (by decide) (by decide))
    · exact dsaved.x24 |>.trans (hstack 56 (by decide) (by decide))
    · exact dsaved.x25 |>.trans (hstack 52 (by decide) (by decide))
    · exact dsaved.x26 |>.trans (hstack 48 (by decide) (by decide))
    · exact dsaved.x27 |>.trans (hstack 44 (by decide) (by decide))
end E5R.Thermostat.DecodeRefusal

namespace E5R.Thermostat.WriteDecodeRefusal
open E5R E5R.Thermostat
theorem contract_inv_quiet (c : Core) (ram : Word → BitVec 8) (p f out req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (status : Nat)
    (h : WriteInput.Pre UartPlatform.board c ram p f out req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .error status)
    (hi : Spec.Inv s) (ho : Memory.Block UartPlatform.board out 15) (hoa : out.toNat%4 = 0)
    (hso : WordRegions.Disjoint (p+80#32) 96 out 15) (hof : WordRegions.Disjoint out 15 f 41)
    (heo : WordRegions.Disjoint eng 25 out 15) :
    ∃ d n r, n ≤ 212*entries.length+18*body.length+514 ∧ Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      WriteRefusal.Returned c d ∧ StatusMemory.At r out (BitVec.ofNat 32 status) ∧ Encoding.SnapshotAt r (eng+4#32) s ∧
      ramRead r eng .w = 0#32 ∧ Engine.InvariantAt r eng ∧ r (f+36#32) = 1#8 ∧ r (f+40#32) = 1#8 := by
  let r0 := WriteStart.memory ram (p+80#32) f c
  obtain ⟨a,ta,ha,a8,a9,_,_,acsr⟩ := E5R.Thermostat.WriteInput.establishes_quiet h
  obtain ⟨d,n,r,hn,td,dpc,dsp,dcsr,dsaved,dresponse,ds,db,di,dflag36,dflag40⟩ := E5R.Thermostat.DecodeRefusal.contract_inv_quiet UartPlatform.board a r0
    p req eng rawPtr pathPtr bodyPtr out f raw path body entries first admin s status ha a8 a9
    (AuthLiterals.header _) (AuthLiterals.bearer _) (AuthLiterals.key _) hallow hdecode hi ho hoa h.futureBlock h.stack hso
    (WordRegions.symm h.futureSeparate) hof heo h.appAvoid.2
  have hword (k : Nat) (hk : k+4 ≤ 96) :
      ramRead r0 (a.get 2+BitVec.ofNat 32 k) .w = ramRead (OuterSave.memory ram (p+80#32) c) ((p+80#32)+BitVec.ofNat 32 k) .w := by
    rw [ha.sp]
    exact ViewFrame.word (WriteStart.saved_region ram (p+80#32) f c h.futureSeparate) k hk
  have hs := OuterSave.saved ram (p+80#32) c
  have hra : ramRead r0 ((p+80#32)+92#32) .w = c.get 1 :=
    (ViewFrame.word (WriteStart.saved_region ram (p+80#32) f c h.futureSeparate) 92 (by decide)).trans hs.1
  refine ⟨d,31+n,r,
    by omega,ta.trans td,?_,dresponse,ds,db,di,dflag36,dflag40⟩
  refine ⟨by rw [dpc,hra],dsp.trans h.sp.symm,dcsr.trans acsr,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact dsaved.x1 |>.trans ((hword 92 (by decide)).trans hs.1)
  · exact dsaved.x8 |>.trans ((hword 88 (by decide)).trans hs.2.1)
  · exact dsaved.x9 |>.trans ((hword 84 (by decide)).trans hs.2.2.1)
  · exact dsaved.x18 |>.trans ((hword 80 (by decide)).trans hs.2.2.2.1)
  · exact dsaved.x19 |>.trans ((hword 76 (by decide)).trans hs.2.2.2.2.1)
  · exact dsaved.x20 |>.trans ((hword 72 (by decide)).trans hs.2.2.2.2.2.1)
  · exact dsaved.x21 |>.trans ((hword 68 (by decide)).trans hs.2.2.2.2.2.2.1)
  · exact dsaved.x22 |>.trans ((hword 64 (by decide)).trans hs.2.2.2.2.2.2.2.1)
  · exact dsaved.x23 |>.trans ((hword 60 (by decide)).trans hs.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x24 |>.trans ((hword 56 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x25 |>.trans ((hword 52 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x26 |>.trans ((hword 48 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.2.1)
  · exact dsaved.x27 |>.trans ((hword 44 (by decide)).trans hs.2.2.2.2.2.2.2.2.2.2.2.2)
end E5R.Thermostat.WriteDecodeRefusal

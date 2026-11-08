import Projects.thermostat.Boot
import Projects.thermostat.Init
import Projects.thermostat.Interrupt
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Startup
open E5R E5R.Thermostat

/-- The actual initial App object, immediately after its principal store.
    Router/buffer initialization and the first loop boundary follow this PC. -/
structure Ready (B : Board) (c : Core) (ram : Word → BitVec 8) : Prop where
  pc : c.pc = 0x800008d8
  sp : c.get 2 = 0x80ffeb90
  stack : Memory.Block B 0x80ffeb90 5232
  state : Encoding.SnapshotAt ram 0x80ffebc0 Spec.initial
  available : ramRead ram 0x80ffebbc .w = 0
  keyPtr : ramRead ram 0x80ffebcc .w = 0x80005b7c
  keyLen : ramRead ram 0x80ffebd0 .w = 7
  principal : ram 0x80ffebd4 = 1

/-- Reset entry to initialized App in the pinned ELF. No initial RAM bytes
    or general-purpose register values are postulated. BSS is empty here.
    This ends before router/buffer initialization, not at the firmware loop. -/
theorem contract_full (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000000) (hm : c.mpp = 0 ∨ c.mpp = 3)
    (hmem : Memory.Block B 0x80ffeb90 5232) :
    ∃ d r, DetSteps B img 44 ⟨c,ram⟩ ⟨d,r⟩ ∧ Ready B d r ∧
      Engine.InvariantAt r 0x80ffebbc ∧ d.mie_ = false ∧ d.mieReg = 0 ∧
      (∀ x, (∀ i : Fin 5232, x ≠ 0x80ffeb90+BitVec.ofNat 32 i.val) → r x = ram x) ∧ d.get 8 = 0x80fff814#32 ∧ d.get 19 = 0x10000000#32 ∧ d.get 22 = 1#32 ∧ d.get 12 = 2048#32 := by
  have hboot := Boot.contract B c ram hp hm
  obtain ⟨d,r,hr,hpc,hsp,hcsr,hstate,hfree,hkey,hlen,hactor,hframe,hfp,huart,hone,hlen2⟩ := Init.contract_full B
    (Boot.mainEntry c) ram (Boot.main_layout c).1 (Boot.main_layout c).2.1 hmem
  have hmie : d.mie_ = (Boot.mainEntry c).mie_ := congrArg Prod.fst hcsr
  have hreg : d.mieReg = (Boot.mainEntry c).mieReg := congrArg (fun t => t.2.2.2.1) hcsr
  refine ⟨d,r,hboot.trans hr,⟨hpc,hsp,hmem,hstate,hfree,hkey,hlen,hactor⟩,
    ⟨Spec.initial,hstate,Spec.initial_inv⟩,hmie.trans (Boot.main_layout c).2.2.1,
    hreg.trans (Boot.main_layout c).2.2.2,hframe,hfp,huart,hone,hlen2⟩

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000000) (hm : c.mpp = 0 ∨ c.mpp = 3)
    (hmem : Memory.Block B 0x80ffeb90 5232) :
    ∃ d r, DetSteps B img 44 ⟨c,ram⟩ ⟨d,r⟩ ∧ Ready B d r ∧
      Engine.InvariantAt r 0x80ffebbc ∧ d.mie_ = false ∧ d.mieReg = 0 ∧
      (∀ x, (∀ i : Fin 5232, x ≠ 0x80ffeb90+BitVec.ofNat 32 i.val) → r x = ram x) := by
  obtain ⟨d,r,hr,hready,hinv,hmie,hmreg,hframe,_,_,_,_⟩ := contract_full B c ram hp hm hmem
  exact ⟨d,r,hr,hready,hinv,hmie,hmreg,hframe⟩

/-- Under the board's reset MIE=0 assumption, all 44 instruction boundaries
    form an IRQ-masked execution certificate for the real platform semantics. -/
theorem closed_contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000000) (hm : c.mpp = 0 ∨ c.mpp = 3)
    (hmask : c.mie_ = false) (hmem : Memory.Block B 0x80ffeb90 5232) :
    ∃ d r, Trace.Closed B img 44 ⟨c,ram⟩ ⟨d,r⟩ ∧ Ready B d r ∧
      Engine.InvariantAt r 0x80ffebbc ∧ d.mie_ = false ∧ d.mieReg = 0 := by
  obtain ⟨d,r,hr,hready,hinv,hmi,hmr,_⟩ := contract B c ram hp hm hmem
  exact ⟨d,r,Interrupt.close hr hmask,hready,hinv,hmi,hmr⟩
end E5R.Thermostat.Startup

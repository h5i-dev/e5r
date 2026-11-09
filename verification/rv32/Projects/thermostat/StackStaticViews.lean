import Projects.thermostat.StackAccess
import Projects.thermostat.AuthLiterals
import Projects.thermostat.ResponseLiterals
set_option autoImplicit false
namespace E5R.Thermostat.StackStaticViews
open E5R E5R.Thermostat

theorem auth_header (ram : Word → BitVec 8) : ReadBytes.Span StackBoard.board img ram 0x80005b68#32 (WireSpec.ascii "authorization") :=
  StackAccess.rom_span (AuthLiterals.header ram) AuthLiterals.header_outside

theorem auth_bearer (ram : Word → BitVec 8) : ReadBytes.Span StackBoard.board img ram 0x80005b75#32 (WireSpec.ascii "Bearer ") :=
  StackAccess.rom_span (AuthLiterals.bearer ram) AuthLiterals.bearer_outside

theorem auth_key (ram : Word → BitVec 8) : ReadBytes.Span StackBoard.board img ram 0x80005b7c#32 (WireSpec.ascii "dev-key") :=
  StackAccess.rom_span (AuthLiterals.key ram) AuthLiterals.key_outside

theorem json (ram : Word → BitVec 8) : ReadBytes.Span StackBoard.board img ram 0x800056a8#32 (WireSpec.ascii "application/json") := by
  apply StackAccess.rom_span (ResponseLiterals.json ram)
  change ∀ i : Fin 16,UartPlatform.board.inRam (0x800056a8#32+BitVec.ofNat 32 i.val) 1=false
  rw [StackBoard.original_board]
  decide +kernel
end E5R.Thermostat.StackStaticViews

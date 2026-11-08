import Projects.thermostat.ReadResponseFullQuiet
import Projects.thermostat.MainWriteSuccessQuiet
import Projects.thermostat.MainWriteErrorQuiet
import Projects.thermostat.MainWriteResponseQuiet
namespace E5R.Thermostat.QuietContractBinding
open E5R E5R.Thermostat

/-- The proposition proved by the actual original theorem constant. -/
def statement {P : Prop} (_ : P) : Prop := P

/-- Kernel-checked erasure from the stronger execution to the exact original contract. -/
theorem read_response : statement (@ReadResponseFull.contract_inv) := by
  intro c ram dst cap s tx io close htx htxcap hio hcloseByte h hi hstack h24 h20 h22 hc hlen hd hw hcap hds hss hdf hdt hkd hed
  obtain ⟨d,n,after,bound,trace,post⟩ := ReadResponseFull.contract_inv_quiet c ram dst cap s tx io close htx htxcap hio hcloseByte h hi hstack h24 h20 h22 hc hlen hd hw hcap hds hss hdf hdt hkd hed
  exact ⟨d,n,after,bound,trace.det,post⟩

/-- Kernel-checked erasure from the stronger execution to the exact original contract. -/
theorem write_success : statement (@MainWriteSuccess.contract) := by
  intro c ram req rawPtr pathPtr bodyPtr raw path body entries first state cmd res hp h2 h8 h18 h22 h24 hm happ hi h hallow hdecode hres
  obtain ⟨d,n,after,bound,trace,post⟩ := MainWriteSuccess.contract_quiet c ram req rawPtr pathPtr bodyPtr raw path body entries first state cmd res hp h2 h8 h18 h22 h24 hm happ hi h hallow hdecode hres
  exact ⟨d,n,after,bound,trace.det,post⟩

/-- Kernel-checked erasure from the stronger execution to the exact original contract. -/
theorem write_error : statement (@MainWriteError.contract) := by
  intro c ram req rawPtr pathPtr bodyPtr raw path body entries first state cmd err hp h2 h8 h18 h22 h24 hm happ hi h hallow hdecode hres
  obtain ⟨d,n,after,bound,trace,post⟩ := MainWriteError.contract_quiet c ram req rawPtr pathPtr bodyPtr raw path body entries first state cmd err hp h2 h8 h18 h22 h24 hm happ hi h hallow hdecode hres
  exact ⟨d,n,after,bound,trace.det,post⟩

/-- Kernel-checked erasure from the stronger execution to the exact original contract. -/
theorem response_object : statement (@MainWriteResponse.contract) := by
  intro c ram state io payload status close hp h2 h8 h18 h22 hm happ hi hbody hst hv hb hcap htx htxc hio hclose
  obtain ⟨d,after,trace,post⟩ := MainWriteResponse.contract_quiet c ram state io payload status close hp h2 h8 h18 h22 hm happ hi hbody hst hv hb hcap htx htxc hio hclose
  exact ⟨d,after,trace.det,post⟩

end E5R.Thermostat.QuietContractBinding

import Projects.thermostat.MainRelayRouterCode
namespace E5R.Thermostat
open E5R
theorem wm2147489916 : fetchDecode img 2147489916#32=some ((.opimm .add 11 0 0#32 : Instr),2#32) := by
  exact PackedFetch.fetchDecode_of 2147489916#32 (by decide) (by decide) (bits := 17793#32) (by decide +kernel) (by decide +kernel)
theorem wm2147489918 : fetchDecode img 2147489918#32=some ((.opimm .add 20 0 0#32 : Instr),2#32) := by
  exact PackedFetch.fetchDecode_of 2147489918#32 (by decide) (by decide) (bits := 18945#32) (by decide +kernel) (by decide +kernel)
theorem wm2147489920 : fetchDecode img 2147489920#32=some ((.opimm .add 13 0 0#32 : Instr),2#32) := by
  exact PackedFetch.fetchDecode_of 2147489920#32 (by decide) (by decide) (bits := 18049#32) (by decide +kernel) (by decide +kernel)
theorem wm2147489922 : fetchDecode img 2147489922#32=some ((.opimm .add 12 0 1#32 : Instr),2#32) := by
  exact PackedFetch.fetchDecode_of 2147489922#32 (by decide) (by decide) (bits := 17925#32) (by decide +kernel) (by decide +kernel)
theorem wm2147489924 : fetchDecode img 2147489924#32=some ((.store .b 8 12 532#32 : Instr),4#32) := by
  exact PackedFetch.fetchDecode_of 2147489924#32 (by decide) (by decide) (bits := 549718563#32) (by decide +kernel) (by decide +kernel)
theorem wm2147489928 : fetchDecode img 2147489928#32=some ((.opimm .add 10 0 405#32 : Instr),4#32) := by
  exact PackedFetch.fetchDecode_of 2147489928#32 (by decide) (by decide) (bits := 424674579#32) (by decide +kernel) (by decide +kernel)
theorem wm2147489932 : fetchDecode img 2147489932#32=some ((.opimm .add 9 2 2047#32 : Instr),4#32) := by
  exact PackedFetch.fetchDecode_of 2147489932#32 (by decide) (by decide) (bits := 2146501779#32) (by decide +kernel) (by decide +kernel)
theorem wm2147489936 : fetchDecode img 2147489936#32=some ((.opimm .add 9 9 1257#32 : Instr),4#32) := by
  exact PackedFetch.fetchDecode_of 2147489936#32 (by decide) (by decide) (bits := 1318356115#32) (by decide +kernel) (by decide +kernel)
theorem wm2147489940 : fetchDecode img 2147489940#32=some ((.opimm .add 24 0 0xfffffffe#32 : Instr),2#32) := by
  exact PackedFetch.fetchDecode_of 2147489940#32 (by decide) (by decide) (bits := 23673#32) (by decide +kernel) (by decide +kernel)
theorem wm2147489942 : fetchDecode img 2147489942#32=some ((.jal 0 0xfffffe92#32 : Instr),2#32) := by
  exact PackedFetch.fetchDecode_of 2147489942#32 (by decide) (by decide) (bits := 48457#32) (by decide +kernel) (by decide +kernel)
end E5R.Thermostat

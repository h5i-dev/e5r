import Projects.thermostat.MainRelayRouterCode
namespace E5R.Thermostat
open E5R
theorem um2147489944 : fetchDecode img 2147489944#32=some ((.opimm .add 11 0 0#32 : Instr), 2#32) := by
  exact PackedFetch.fetchDecode_of 2147489944#32 (by decide) (by decide) (bits := 17793#32) (by decide +kernel) (by decide +kernel)
theorem um2147489946 : fetchDecode img 2147489946#32=some ((.opimm .add 20 0 0#32 : Instr), 2#32) := by
  exact PackedFetch.fetchDecode_of 2147489946#32 (by decide) (by decide) (bits := 18945#32) (by decide +kernel) (by decide +kernel)
theorem um2147489948 : fetchDecode img 2147489948#32=some ((.opimm .add 13 0 0#32 : Instr), 2#32) := by
  exact PackedFetch.fetchDecode_of 2147489948#32 (by decide) (by decide) (bits := 18049#32) (by decide +kernel) (by decide +kernel)
theorem um2147489950 : fetchDecode img 2147489950#32=some ((.opimm .add 9 9 0xfffffffd#32 : Instr), 2#32) := by
  exact PackedFetch.fetchDecode_of 2147489950#32 (by decide) (by decide) (bits := 5365#32) (by decide +kernel) (by decide +kernel)
theorem um2147489952 : fetchDecode img 2147489952#32=some ((.opimm .add 12 0 1#32 : Instr), 2#32) := by
  exact PackedFetch.fetchDecode_of 2147489952#32 (by decide) (by decide) (bits := 17925#32) (by decide +kernel) (by decide +kernel)
theorem um2147489954 : fetchDecode img 2147489954#32=some ((.opimm .sltu 10 9 1#32 : Instr), 4#32) := by
  exact PackedFetch.fetchDecode_of 2147489954#32 (by decide) (by decide) (bits := 1357075#32) (by decide +kernel) (by decide +kernel)
theorem um2147489958 : fetchDecode img 2147489958#32=some ((.store .b 8 12 532#32 : Instr), 4#32) := by
  exact PackedFetch.fetchDecode_of 2147489958#32 (by decide) (by decide) (bits := 549718563#32) (by decide +kernel) (by decide +kernel)
theorem um2147489962 : fetchDecode img 2147489962#32=some ((.opimm .xor 10 10 405#32 : Instr), 4#32) := by
  exact PackedFetch.fetchDecode_of 2147489962#32 (by decide) (by decide) (bits := 425018643#32) (by decide +kernel) (by decide +kernel)
theorem um2147489966 : fetchDecode img 2147489966#32=some ((.opimm .add 9 2 2047#32 : Instr), 4#32) := by
  exact PackedFetch.fetchDecode_of 2147489966#32 (by decide) (by decide) (bits := 2146501779#32) (by decide +kernel) (by decide +kernel)
theorem um2147489970 : fetchDecode img 2147489970#32=some ((.opimm .add 9 9 1257#32 : Instr), 4#32) := by
  exact PackedFetch.fetchDecode_of 2147489970#32 (by decide) (by decide) (bits := 1318356115#32) (by decide +kernel) (by decide +kernel)
theorem um2147489974 : fetchDecode img 2147489974#32=some ((.opimm .add 24 0 0xfffffffe#32 : Instr), 2#32) := by
  exact PackedFetch.fetchDecode_of 2147489974#32 (by decide) (by decide) (bits := 23673#32) (by decide +kernel) (by decide +kernel)
theorem um2147489976 : fetchDecode img 2147489976#32=some ((.load .w true 6 2 20#32 : Instr), 2#32) := by
  exact PackedFetch.fetchDecode_of 2147489976#32 (by decide) (by decide) (bits := 17234#32) (by decide +kernel) (by decide +kernel)
theorem um2147489978 : fetchDecode img 2147489978#32=some ((.jal 0 0xfffffe6e#32 : Instr), 2#32) := by
  exact PackedFetch.fetchDecode_of 2147489978#32 (by decide) (by decide) (bits := 46525#32) (by decide +kernel) (by decide +kernel)
end E5R.Thermostat

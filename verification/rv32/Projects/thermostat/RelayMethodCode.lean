import Projects.thermostat.MainRelayRouterCode
namespace E5R.Thermostat
open E5R

theorem rl2147489904 : fetchDecode img 0x80001870#32=some (.opimm .xor 12 12 1#32,4#32) := by
  exact PackedFetch.fetchDecode_of 0x80001870#32 (by decide) (by decide) (bits := 0x00164613#32) (by decide +kernel) (by decide +kernel)
theorem rl2147489908 : fetchDecode img 0x80001874#32=some (.op .or 12 12 13,2#32) := by
  exact PackedFetch.fetchDecode_of 0x80001874#32 (by decide) (by decide) (bits := 0x00008e55#32) (by decide +kernel) (by decide +kernel)
theorem rl2147489910 : fetchDecode img 0x80001876#32=some (.opimm .sltu 12 12 1#32,4#32) := by
  exact PackedFetch.fetchDecode_of 0x80001876#32 (by decide) (by decide) (bits := 0x00163613#32) (by decide +kernel) (by decide +kernel)
theorem rl2147489914 : fetchDecode img 0x8000187a#32=some (.branch .ne 12 0 172#32,2#32) := by
  exact PackedFetch.fetchDecode_of 0x8000187a#32 (by decide) (by decide) (bits := 0x0000e655#32) (by decide +kernel) (by decide +kernel)
end E5R.Thermostat

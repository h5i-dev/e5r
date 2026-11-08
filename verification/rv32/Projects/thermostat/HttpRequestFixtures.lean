import Projects.thermostat.HttpRequestBytes
import Projects.thermostat.MainWriteWitness
import Projects.thermostat.MainWriteRangeWitness
namespace E5R.Thermostat.HttpRequestFixtures
open E5R E5R.Thermostat HttpRequestSpec

theorem auto_head : HttpRequestBytes.parse MainWriteWitness.raw 1024 1024=
    .done ⟨(0,4),(5,10),1,[⟨21,25,27,28⟩,⟨30,43,45,59⟩,⟨61,75,77,78⟩],82,.length 4⟩ := by decide +kernel

theorem range_head : HttpRequestBytes.parse MainWriteRangeWitness.raw 1024 1024=
    .done ⟨(0,4),(5,14),1,[⟨25,29,31,32⟩,⟨34,47,49,63⟩,⟨65,79,81,82⟩],86,.length 3⟩ := by decide +kernel

/-- The legacy raw handler fixture has no Host field. Its downstream Request
    contract is satisfiable, but it is not an accepted HTTP/1.1 parser fixture. -/
theorem inherited_missing_host : HttpRequestBytes.parse RequestWitness.raw 1024 1024=.reject 400 := by decide +kernel

theorem duplicate_length : HttpRequestBytes.parse (WireSpec.ascii
    "POST /mode HTTP/1.1\r\nHost: x\r\nContent-Length: 4\r\nContent-Length: 4\r\n\r\nauto") 1024 1024=.reject 400 := by decide +kernel

theorem length_and_chunked : HttpRequestBytes.parse (WireSpec.ascii
    "POST /mode HTTP/1.1\r\nHost: x\r\nContent-Length: 4\r\nTransfer-Encoding: chunked\r\n\r\nauto") 1024 1024=.reject 400 := by decide +kernel

theorem bare_lf : HttpRequestBytes.parse (WireSpec.ascii "GET / HTTP/1.1\nHost: x\n\n") 1024 1024=.reject 400 := by decide +kernel

theorem partial_head : HttpRequestBytes.parse (WireSpec.ascii "GET / HTTP/1.1\r\nHost: x\r\n") 1024 1024=.incomplete := by decide +kernel
end E5R.Thermostat.HttpRequestFixtures

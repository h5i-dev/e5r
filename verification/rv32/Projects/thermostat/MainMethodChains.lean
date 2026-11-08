import Projects.thermostat.MainMethodDecodeCode
import Projects.thermostat.MainMethodChain
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainMethodChains
open E5R E5R.Thermostat MainMethodChain

theorem head : Certified [(1,69),(2,65)] 0x80000d86#32 0x80000d9e#32 := by
  have node : Node 0x80000d86#32 (1,69) := by
    refine ⟨0x3d2#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487110
    · simpa only [show 0x80000d86#32+4#32=0x80000d8a#32 by decide +kernel] using re2147487114
    · simpa only [show 0x80000d86#32+8#32=0x80000d8e#32 by decide +kernel] using re2147487118
  refine .cons node ?_
  rw [show 0x80000d86#32+12#32=0x80000d92#32 by decide +kernel]
  have node : Node 0x80000d92#32 (2,65) := by
    refine ⟨0x3c6#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487122
    · simpa only [show 0x80000d92#32+4#32=0x80000d96#32 by decide +kernel] using re2147487126
    · simpa only [show 0x80000d92#32+8#32=0x80000d9a#32 by decide +kernel] using re2147487130
  refine .cons node ?_
  rw [show 0x80000d92#32+12#32=0x80000d9e#32 by decide +kernel]
  exact .nil _

theorem post : Certified [(1,79),(2,83)] 0x8000111e#32 0x80001136#32 := by
  have node : Node 0x8000111e#32 (1,79) := by
    refine ⟨0x3a#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147488030
    · simpa only [show 0x8000111e#32+4#32=0x80001122#32 by decide +kernel] using re2147488034
    · simpa only [show 0x8000111e#32+8#32=0x80001126#32 by decide +kernel] using re2147488038
  refine .cons node ?_
  rw [show 0x8000111e#32+12#32=0x8000112a#32 by decide +kernel]
  have node : Node 0x8000112a#32 (2,83) := by
    refine ⟨0x2e#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147488042
    · simpa only [show 0x8000112a#32+4#32=0x8000112e#32 by decide +kernel] using re2147488046
    · simpa only [show 0x8000112a#32+8#32=0x80001132#32 by decide +kernel] using re2147488050
  refine .cons node ?_
  rw [show 0x8000112a#32+12#32=0x80001136#32 by decide +kernel]
  exact .nil _

theorem patch : Certified [(0,80),(1,65),(2,84),(3,67)] 0x80000e1a#32 0x80000e4a#32 := by
  have node : Node 0x80000e1a#32 (0,80) := by
    refine ⟨0x33e#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487258
    · simpa only [show 0x80000e1a#32+4#32=0x80000e1e#32 by decide +kernel] using re2147487262
    · simpa only [show 0x80000e1a#32+8#32=0x80000e22#32 by decide +kernel] using re2147487266
  refine .cons node ?_
  rw [show 0x80000e1a#32+12#32=0x80000e26#32 by decide +kernel]
  have node : Node 0x80000e26#32 (1,65) := by
    refine ⟨0x332#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487270
    · simpa only [show 0x80000e26#32+4#32=0x80000e2a#32 by decide +kernel] using re2147487274
    · simpa only [show 0x80000e26#32+8#32=0x80000e2e#32 by decide +kernel] using re2147487278
  refine .cons node ?_
  rw [show 0x80000e26#32+12#32=0x80000e32#32 by decide +kernel]
  have node : Node 0x80000e32#32 (2,84) := by
    refine ⟨0x326#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487282
    · simpa only [show 0x80000e32#32+4#32=0x80000e36#32 by decide +kernel] using re2147487286
    · simpa only [show 0x80000e32#32+8#32=0x80000e3a#32 by decide +kernel] using re2147487290
  refine .cons node ?_
  rw [show 0x80000e32#32+12#32=0x80000e3e#32 by decide +kernel]
  have node : Node 0x80000e3e#32 (3,67) := by
    refine ⟨0x31a#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487294
    · simpa only [show 0x80000e3e#32+4#32=0x80000e42#32 by decide +kernel] using re2147487298
    · simpa only [show 0x80000e3e#32+8#32=0x80000e46#32 by decide +kernel] using re2147487302
  refine .cons node ?_
  rw [show 0x80000e3e#32+12#32=0x80000e4a#32 by decide +kernel]
  exact .nil _

theorem delete : Certified [(0,68),(1,69),(2,76),(3,69),(4,84)] 0x80000db0#32 0x80000dec#32 := by
  have node : Node 0x80000db0#32 (0,68) := by
    refine ⟨0x3a8#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487152
    · simpa only [show 0x80000db0#32+4#32=0x80000db4#32 by decide +kernel] using re2147487156
    · simpa only [show 0x80000db0#32+8#32=0x80000db8#32 by decide +kernel] using re2147487160
  refine .cons node ?_
  rw [show 0x80000db0#32+12#32=0x80000dbc#32 by decide +kernel]
  have node : Node 0x80000dbc#32 (1,69) := by
    refine ⟨0x39c#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487164
    · simpa only [show 0x80000dbc#32+4#32=0x80000dc0#32 by decide +kernel] using re2147487168
    · simpa only [show 0x80000dbc#32+8#32=0x80000dc4#32 by decide +kernel] using re2147487172
  refine .cons node ?_
  rw [show 0x80000dbc#32+12#32=0x80000dc8#32 by decide +kernel]
  have node : Node 0x80000dc8#32 (2,76) := by
    refine ⟨0x390#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487176
    · simpa only [show 0x80000dc8#32+4#32=0x80000dcc#32 by decide +kernel] using re2147487180
    · simpa only [show 0x80000dc8#32+8#32=0x80000dd0#32 by decide +kernel] using re2147487184
  refine .cons node ?_
  rw [show 0x80000dc8#32+12#32=0x80000dd4#32 by decide +kernel]
  have node : Node 0x80000dd4#32 (3,69) := by
    refine ⟨0x384#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487188
    · simpa only [show 0x80000dd4#32+4#32=0x80000dd8#32 by decide +kernel] using re2147487192
    · simpa only [show 0x80000dd4#32+8#32=0x80000ddc#32 by decide +kernel] using re2147487196
  refine .cons node ?_
  rw [show 0x80000dd4#32+12#32=0x80000de0#32 by decide +kernel]
  have node : Node 0x80000de0#32 (4,84) := by
    refine ⟨0x378#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487200
    · simpa only [show 0x80000de0#32+4#32=0x80000de4#32 by decide +kernel] using re2147487204
    · simpa only [show 0x80000de0#32+8#32=0x80000de8#32 by decide +kernel] using re2147487208
  refine .cons node ?_
  rw [show 0x80000de0#32+12#32=0x80000dec#32 by decide +kernel]
  exact .nil _

theorem get : Certified [(1,69)] 0x80000e0a#32 0x80000e16#32 := by
  have node : Node 0x80000e0a#32 (1,69) := by
    refine ⟨0x34e#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147487242
    · simpa only [show 0x80000e0a#32+4#32=0x80000e0e#32 by decide +kernel] using re2147487246
    · simpa only [show 0x80000e0a#32+8#32=0x80000e12#32 by decide +kernel] using re2147487250
  refine .cons node ?_
  rw [show 0x80000e0a#32+12#32=0x80000e16#32 by decide +kernel]
  exact .nil _

theorem put : Certified [(1,85)] 0x80001140#32 0x8000114c#32 := by
  have node : Node 0x80001140#32 (1,85) := by
    refine ⟨0x18#32,by decide,by decide,by decide,by decide,by decide +kernel,?_,?_,?_⟩
    · exact re2147488064
    · simpa only [show 0x80001140#32+4#32=0x80001144#32 by decide +kernel] using re2147488068
    · simpa only [show 0x80001140#32+8#32=0x80001148#32 by decide +kernel] using re2147488072
  refine .cons node ?_
  rw [show 0x80001140#32+12#32=0x8000114c#32 by decide +kernel]
  exact .nil _
end E5R.Thermostat.MainMethodChains

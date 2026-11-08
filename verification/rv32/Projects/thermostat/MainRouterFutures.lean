import Projects.thermostat.MainRouterSetup
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.MainRouterFutures
open E5R E5R.Thermostat
abbrev fp : Word := 0x80fff814#32

def address (route field : Fin 5) : Word := fp+BitVec.ofNat 32 (512+44*route.val+4*field.val)
def value (route field : Fin 5) : Word :=
  if field.val=0 then 0x80ffebd8#32+BitVec.ofNat 32 (8*route.val)
  else if field.val=1 then 0x80fff880#32
  else if field.val=2 then 0x80ffebbc#32
  else if field.val=3 then 0x80fff4d4#32 else 832#32

/-- Five actual route futures, with only the five immutable words in each.
    The poll flags in the intervening gaps may be changed by real dispatch. -/
def At (ram : Word → BitVec 8) : Prop := ∀ route field : Fin 5, ramRead ram (address route field) .w=value route field

/-- Derive all twenty-five words from the actual main129a..13ba stores. -/
theorem initialized (ram : Word → BitVec 8) : At (MainRouterSetup.memory ram) := by
  intro route field
  have routes : route.val=0 ∨ route.val=1 ∨ route.val=2 ∨ route.val=3 ∨ route.val=4 := by have := route.isLt;omega
  have fields : field.val=0 ∨ field.val=1 ∨ field.val=2 ∨ field.val=3 ∨ field.val=4 := by have := field.isLt;omega
  rcases routes with hr|hr|hr|hr|hr
  · rcases route with ⟨r,rlt⟩
    dsimp only at hr
    subst r
    rcases fields with hf|hf|hf|hf|hf
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3716#32) .w=2164255704#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3812 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3808 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3804 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3824 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3800 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3796 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3792 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3788 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3784 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3776 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3772 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3768 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3764 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3760 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3780 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3756 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3752 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3748 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3744 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3740 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3736 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3732 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3728 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3724 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3716 3720 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3720#32) .w=2164258944#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3812 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3808 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3804 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3824 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3800 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3796 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3792 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3788 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3784 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3776 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3772 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3768 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3764 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3760 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3780 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3756 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3752 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3748 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3744 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3740 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3736 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3732 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3728 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3720 3724 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3724#32) .w=2164255676#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3812 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3808 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3804 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3824 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3800 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3796 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3792 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3788 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3784 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3776 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3772 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3768 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3764 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3760 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3780 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3756 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3752 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3748 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3744 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3740 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3736 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3732 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3724 3728 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3728#32) .w=2164258004#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3812 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3808 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3804 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3824 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3800 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3796 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3792 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3788 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3784 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3776 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3772 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3768 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3764 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3760 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3780 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3756 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3752 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3748 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3744 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3740 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3736 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3728 3732 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3732#32) .w=832#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3812 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3808 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3804 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3824 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3800 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3796 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3792 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3788 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3784 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3776 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3772 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3768 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3764 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3760 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3780 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3756 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3752 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3748 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3744 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3740 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3732 3736 .b (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
  · rcases route with ⟨r,rlt⟩
    dsimp only at hr
    subst r
    rcases fields with hf|hf|hf|hf|hf
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3760#32) .w=2164255712#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3812 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3808 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3804 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3824 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3800 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3796 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3792 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3788 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3784 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3776 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3772 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3768 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3760 3764 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3764#32) .w=2164258944#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3812 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3808 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3804 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3824 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3800 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3796 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3792 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3788 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3784 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3776 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3772 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3764 3768 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3768#32) .w=2164255676#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3812 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3808 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3804 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3824 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3800 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3796 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3792 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3788 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3784 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3776 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3768 3772 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3772#32) .w=2164258004#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3812 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3808 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3804 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3824 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3800 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3796 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3792 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3788 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3784 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3772 3776 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3776#32) .w=832#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3812 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3808 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3804 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3824 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3800 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3796 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3792 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3788 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3776 3784 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
  · rcases route with ⟨r,rlt⟩
    dsimp only at hr
    subst r
    rcases fields with hf|hf|hf|hf|hf
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3804#32) .w=2164255720#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3812 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3804 3808 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3808#32) .w=2164258944#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3816 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3808 3812 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3812#32) .w=2164255676#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3820 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3812 3816 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3816#32) .w=2164258004#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3828 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3816 3820 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3820#32) .w=832#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3852 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3848 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3868 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3844 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3840 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3836 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3832 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3820 3828 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
  · rcases route with ⟨r,rlt⟩
    dsimp only at hr
    subst r
    rcases fields with hf|hf|hf|hf|hf
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3848#32) .w=2164255728#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3856 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3848 3852 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3852#32) .w=2164258944#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3860 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3852 3856 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3856#32) .w=2164255676#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3864 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3856 3860 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3860#32) .w=2164258004#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3872 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3860 3864 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3864#32) .w=832#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3896 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3892 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3912 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3888 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3884 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3880 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3876 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3864 3872 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
  · rcases route with ⟨r,rlt⟩
    dsimp only at hr
    subst r
    rcases fields with hf|hf|hf|hf|hf
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3892#32) .w=2164255736#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3892 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3892 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3892 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3892 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3892 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3892 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3892 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3892 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3892 3900 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3892 3896 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3896#32) .w=2164258944#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3896 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3896 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3896 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3896 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3896 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3896 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3896 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3896 3904 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3896 3900 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3900#32) .w=2164255676#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3900 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3900 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3900 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3900 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3900 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3900 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3900 3908 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3900 3904 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3904#32) .w=2164258004#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3904 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3904 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3904 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3904 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3904 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3904 3916 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3904 3908 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _
    · rcases field with ⟨f,flt⟩
      dsimp only at hf
      subst f
      change ramRead (MainRouterSetup.memory ram) (MainRouterSetup.sp+3908#32) .w=832#32
      unfold MainRouterSetup.memory
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3908 3936 .b (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3908 3932 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3908 3928 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3908 3924 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3908 3920 .w (by decide) (by decide) (by decide)]
      rw [FrameOffsets.word _ MainRouterSetup.sp _ 3908 3916 .w (by decide) (by decide) (by decide)]
      exact ramRead_ramWrite_w _ _ _

theorem preserve {before after : Word → BitVec 8} (h : At before)
    (frames : ∀ route : Fin 5, ViewFrame.Region before after (fp+BitVec.ofNat 32 (512+44*route.val)) 20) : At after := by
  intro route field
  have word := ViewFrame.word (frames route) (4*field.val) (by have := field.isLt;omega)
  have addressEq : (fp+BitVec.ofNat 32 (512+44*route.val))+BitVec.ofNat 32 (4*field.val)=address route field := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    rfl
  rw [addressEq] at word
  exact word.trans (h route field)
end E5R.Thermostat.MainRouterFutures

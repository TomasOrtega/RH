import Formalism.JumpKernelCokernel.Statement

namespace Formalism.KernelCokernelLengths

/- English proof (translation)
Introduce `s S η t a ht`. Use `⟨fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ?_, fun h1 h2 h3 => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [abs_le]; constructor <;> omega`. Apply the tactic sequence `rw [abs_le]; constructor <;> omega`.
-/
theorem jump_shift_holds : JumpShift := by
  intro s S η t a ht
  refine ⟨fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ?_, fun h1 h2 h3 => ?_⟩
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega

end Formalism.KernelCokernelLengths

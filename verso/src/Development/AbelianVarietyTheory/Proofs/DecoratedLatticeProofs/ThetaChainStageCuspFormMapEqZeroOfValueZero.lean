import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

/- English proof (translation)
Introduce `hM c hc j hj s hs x w hw hx`. Take `⟨ipD, ip, hm⟩` from `hM c hc j hj s hs`. Establish `h1` using `hm.schur x x w w`. Establish `h0 : Lift.pet s.ν s.fd ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) = 0`. Establish `hx' : (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w = 0` using `hx`.

Rewrite using `[hx']`. Simplify using `[Lift.pet]`. Rewrite `h1` using `[h0]`. Establish `hD : ipD w w ≠ 0`. Introduce `h`.

Use `hm.posD w hw` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`. Establish `hip : ip x x = 0`. Break down `mul_eq_zero.mp h1.symm with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h hD`. Assume the negation of the conclusion as `hne`. Use `hm.pos x hne` as an intermediate fact. Rewrite `this` using `[hip]`.

Simplify using `at this`.
-/
theorem val_eq_zero_imp (D : D7) : MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  intro hM c hc j hj s hs x w hw hx
  obtain ⟨ipD, ip, hm⟩ := hM c hc j hj s hs
  have h1 := hm.schur x x w w
  have h0 : Lift.pet s.ν s.fd ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) = 0 := by
    have hx' : (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w = 0 := hx
    rw [hx']
    simp [Lift.pet]
  rw [h0] at h1
  have hD : ipD w w ≠ 0 := by
    intro h
    have := hm.posD w hw
    rw [h] at this
    simp at this
  have hip : ip x x = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hD
  by_contra hne
  have := hm.pos x hne
  rw [hip] at this
  simp at this

end GlobalTheory.ChainOnto

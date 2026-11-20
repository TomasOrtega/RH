import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `F _ K _ _ ι _ J hJ hJtop`. Set `A : Set (Ideal (MRing ι F))` to `{Q | ∃ (f : MRing ι F) (s : K → ℕ), IsMultiHomog f s ∧ f ∉ J ∧ Q = J.colon {f}}`. Establish `hne : A.Nonempty`. Use `⟨J.colon {1}, 1, 0, ?_, ?_, rfl⟩` and prove the remaining obligations. Conclude with `isWeightedHomogeneous_one F (blockWeight ι)`.

Introduce `h`. Conclude with `hJtop ((Ideal.eq_top_iff_one J).2 h)`. Establish `hnoeth : IsNoetherianRing (MRing ι F)` using `inferInstance`. Take `⟨Q, ⟨f, s, hf, hfJ, rfl⟩, hmax⟩` from `(set_has_maximal_iff_noetherian (R := MRing ι F) (M := MRing ι F)).2 hnoeth A hne`. Use `⟨f, s, hf, hfJ, ?_⟩` and prove the remaining obligations.

Apply `h1 F K ι (J.colon {f}) (h2 F K ι J f s hJ hf)` to reduce the goal to its premises. Introduce `htop`. Apply `hfJ` to reduce the goal to its premises. Establish `h1mem : (1 : MRing ι F) ∈ J.colon {f}` using `by rw [htop]; exact Submodule.mem_top`. Simplify using `using (Submodule.mem_colon_singleton.1 h1mem)`.

Introduce `a b sa sb _ hb hab`. Distinguish the cases in `hbQ : b ∈ J.colon {f}`. Conclude with `Or.inr hbQ`. Use `left`. Establish `hbf : b * f ∉ J`.

Introduce `h`. Apply `hbQ` to reduce the goal to its premises. Conclude with `Submodule.mem_colon_singleton.2 (by simpa [smul_eq_mul] using h)`. Establish `hform : IsMultiHomog (b * f) (sb + s)` using `hb.mul hf`. Establish `hle : J.colon {f} ≤ J.colon {b * f}`.

Introduce `x hx`. Establish `hx' : x * f ∈ J` using `by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hx`. Use `Submodule.mem_colon_singleton.2 ?_` and prove the remaining obligations. Establish `: b * (x * f) ∈ J` using `J.mul_mem_left b hx'`. Simplify `this` using `[smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]`.

Establish `heq : J.colon {f} = J.colon {b * f}`. Assume the negation of the conclusion as `hne'`. Conclude with `hmax _ ⟨b * f, sb + s, hform, hbf, rfl⟩ (lt_of_le_of_ne hle hne')`. Rewrite using `[heq]`. Use `Submodule.mem_colon_singleton.2 ?_` and prove the remaining obligations.

Establish `hab' : a * b * f ∈ J` using `by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hab`. Simplify `hab'` using `[smul_eq_mul, mul_assoc]`.
-/
theorem AssociatedMultiHomogPrime.proof (h1 : MultiHomogPrimeCriterion.Statement.{u})
    (h2 : ColonMultiHomog.Statement.{u}) : AssociatedMultiHomogPrime.Statement.{u} := by
  intro F _ K _ _ ι _ J hJ hJtop
  classical

  let A : Set (Ideal (MRing ι F)) :=
    {Q | ∃ (f : MRing ι F) (s : K → ℕ), IsMultiHomog f s ∧ f ∉ J ∧ Q = J.colon {f}}
  have hne : A.Nonempty := by
    refine ⟨J.colon {1}, 1, 0, ?_, ?_, rfl⟩
    · exact isWeightedHomogeneous_one F (blockWeight ι)
    · intro h
      exact hJtop ((Ideal.eq_top_iff_one J).2 h)
  have hnoeth : IsNoetherianRing (MRing ι F) := inferInstance
  obtain ⟨Q, ⟨f, s, hf, hfJ, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := MRing ι F) (M := MRing ι F)).2 hnoeth A hne
  refine ⟨f, s, hf, hfJ, ?_⟩
  apply h1 F K ι (J.colon {f}) (h2 F K ι J f s hJ hf)
  · intro htop
    apply hfJ
    have h1mem : (1 : MRing ι F) ∈ J.colon {f} := by rw [htop]; exact Submodule.mem_top
    simpa using (Submodule.mem_colon_singleton.1 h1mem)
  · intro a b sa sb _ hb hab
    by_cases hbQ : b ∈ J.colon {f}
    · exact Or.inr hbQ
    left
    have hbf : b * f ∉ J := by
      intro h
      apply hbQ
      exact Submodule.mem_colon_singleton.2 (by simpa [smul_eq_mul] using h)
    have hform : IsMultiHomog (b * f) (sb + s) := hb.mul hf
    have hle : J.colon {f} ≤ J.colon {b * f} := by
      intro x hx
      have hx' : x * f ∈ J := by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hx
      refine Submodule.mem_colon_singleton.2 ?_
      have : b * (x * f) ∈ J := J.mul_mem_left b hx'
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this
    have heq : J.colon {f} = J.colon {b * f} := by
      by_contra hne'
      exact hmax _ ⟨b * f, sb + s, hform, hbf, rfl⟩ (lt_of_le_of_ne hle hne')
    rw [heq]
    refine Submodule.mem_colon_singleton.2 ?_
    have hab' : a * b * f ∈ J := by simpa [smul_eq_mul] using Submodule.mem_colon_singleton.1 hab
    simpa [smul_eq_mul, mul_assoc] using hab'

end GroundTheory.Heights₂.Heights.NumbersDVR

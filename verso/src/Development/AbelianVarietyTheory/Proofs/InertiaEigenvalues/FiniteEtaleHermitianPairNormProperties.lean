import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

/- English proof (translation)
Introduce `F E _ _ _ _ _ A`. Take `⟨⟨b⟩, hinj, hN, -, -⟩` from `Et.quadratic_structure F E A`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s`. Simplify using `only [Et.NL]`.

Rewrite using `[Algebra.norm_algebraMap_of_basis b]`. Simplify using the standard rewrite rules. Introduce `y y'`. Simplify using `only [Et.NL]`. Conclude with `map_mul (Algebra.norm A.K) y y'`.

Introduce `t`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hN, map_one]`. Conclude with `t.prop.2`. Introduce `y hy`.

Establish `h` using `hy.map (algebraMap A.K A.L)`. Rewrite `h` using `[hN]`. Conclude with `isUnit_of_mul_isUnit_left h`. Introduce `y hy`. Conclude with `hy.map (Algebra.norm A.K)`.
-/
theorem Et.norm_facts : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) := by
  intro F E _ _ _ _ _ A
  obtain ⟨⟨b⟩, hinj, hN, -, -⟩ := Et.quadratic_structure F E A
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    simp only [Et.NL]
    rw [Algebra.norm_algebraMap_of_basis b]
    simp
  · intro y y'
    simp only [Et.NL]
    exact map_mul (Algebra.norm A.K) y y'
  · intro t
    apply hinj
    rw [hN, map_one]
    exact t.prop.2
  · intro y hy
    have h := hy.map (algebraMap A.K A.L)
    rw [hN] at h
    exact isUnit_of_mul_isUnit_left h
  · intro y hy
    exact hy.map (Algebra.norm A.K)

end GlobalTheory.JR

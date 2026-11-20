import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.NormInt

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

/- English proof (translation)
Use `U.charZero` as an intermediate fact. Take `⟨b, d, hb0, hs, hd, hd0⟩` from `Unram.exists_basis_antifixed F E`. Establish `h2` using `(IsUnit.mk0 (2 : F) two_ne_zero)`. Conclude with `(quadratic_star_structure b d hb0 hs hd U.star_fix (IsUnit.mk0 d hd0) h2).2.2.1 z`.
-/
theorem traceE [U : Unram F E] (z : E) : algebraMap F E (Algebra.trace F E z) = z + star z := by
  have := U.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  have h2 := (IsUnit.mk0 (2 : F) two_ne_zero)
  exact (quadratic_star_structure b d hb0 hs hd U.star_fix (IsUnit.mk0 d hd0) h2).2.2.1 z

/- English proof (translation)
Introduce `F E _ _ _ _ U A ψ hψ x r j hj y hy`. Use `U.charZero` as an intermediate fact. Use `U.ultraE` as an intermediate fact. Establish `hE2 : Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [U.finrank_eq]; norm_num)`. Take `⟨⟨c⟩, hinj, hN, htr, -⟩` from `GlobalTheory.JR.Et.quadratic_structure F E A`.

Establish `: Module.Free A.K A.L` using `Module.Free.of_basis c`. Establish `: Module.Finite A.K A.L` using `Module.Finite.of_basis c`. Establish `: Module.Free E A.L` using `Module.Free.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))`. Establish `: Module.Finite E A.L` using `Module.Finite.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))`. Use `set s : E := star (j y) ⬝ᵥ j y with hs_def`.

Establish `hs1 : ‖s‖ ≤ 1`. Rewrite using `[hs_def, dotProduct]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.star_apply, norm_mul, U.norm_star]`. Conclude with `mul_le_one₀ (hy i) (norm_nonneg _) (hy i)`.

Establish `hss : star s = s`. Rewrite using `[hs_def, dotProduct, star_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.star_apply, star_mul', star_star, mul_comm]`. Establish `hsL : s = Algebra.trace E A.L (algebraMap A.K A.L x * star y * y)` using `hj y y`.

Use `set T : F := Algebra.trace F A.K (x * A.NL y) with hT`. Establish `hz : algebraMap A.K A.L (x * A.NL y) = algebraMap A.K A.L x * star y * y`. Rewrite using `[map_mul, hN, mul_assoc, mul_comm y]`. Establish `htK : ∀ k : A.K, Algebra.trace A.K A.L (algebraMap A.K A.L k) = 2 • k`. Introduce `k`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[htr, A.star_K, map_nsmul, two_nsmul]`. Establish `h1 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = 2 • T`. Rewrite using `[← Algebra.trace_trace (S := A.K), htK, map_nsmul]`. Establish `h2 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = Algebra.trace F E s`.

Rewrite using `[← Algebra.trace_trace (S := E), hz, hsL]`. Establish `h3 : algebraMap F E T = s`. Establish `e` using `congrArg (algebraMap F E) (h1.symm.trans h2)`. Rewrite `e` using `[traceE, hss, map_nsmul, two_nsmul, ← two_mul, ← two_mul]`. Establish `: CharZero E` using `charZero_of_injective_algebraMap (algebraMap F E).injective`.

Establish `h20 : (2 : E) ≠ 0` using `two_ne_zero`. Conclude with `mul_left_cancel₀ h20 e`. Establish `hT1 : ‖T‖ ≤ 1` using `by rw [← norm_algebraMap' E T, h3]; exact hs1`. Conclude with `hψ.1 T hT1`.
-/
theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y : A.L, (∀ i, ‖j y i‖ ≤ 1) → A.psiK ψ (x * A.NL y) = 1 := by
  intro F E _ _ _ _ U A ψ hψ x r j hj y hy
  have := U.charZero
  have := U.ultraE
  have hE2 : Module.Finite F E := Module.finite_of_finrank_pos (by rw [U.finrank_eq]; norm_num)
  obtain ⟨⟨c⟩, hinj, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : Module.Free A.K A.L := Module.Free.of_basis c
  have : Module.Finite A.K A.L := Module.Finite.of_basis c
  have : Module.Free E A.L := Module.Free.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))
  have : Module.Finite E A.L := Module.Finite.of_basis (A.push.out.basis (Module.Free.chooseBasis F A.K))
  set s : E := star (j y) ⬝ᵥ j y with hs_def

  have hs1 : ‖s‖ ≤ 1 := by
    rw [hs_def, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [Pi.star_apply, norm_mul, U.norm_star]
    exact mul_le_one₀ (hy i) (norm_nonneg _) (hy i)

  have hss : star s = s := by
    rw [hs_def, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, star_mul', star_star, mul_comm]
  have hsL : s = Algebra.trace E A.L (algebraMap A.K A.L x * star y * y) := hj y y
  set T : F := Algebra.trace F A.K (x * A.NL y) with hT
  have hz : algebraMap A.K A.L (x * A.NL y) = algebraMap A.K A.L x * star y * y := by
    rw [map_mul, hN, mul_assoc, mul_comm y]
  have htK : ∀ k : A.K, Algebra.trace A.K A.L (algebraMap A.K A.L k) = 2 • k := by
    intro k
    apply hinj
    rw [htr, A.star_K, map_nsmul, two_nsmul]
  have h1 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = 2 • T := by
    rw [← Algebra.trace_trace (S := A.K), htK, map_nsmul]
  have h2 : Algebra.trace F A.L (algebraMap A.K A.L (x * A.NL y)) = Algebra.trace F E s := by
    rw [← Algebra.trace_trace (S := E), hz, hsL]
  have h3 : algebraMap F E T = s := by
    have e := congrArg (algebraMap F E) (h1.symm.trans h2)
    rw [traceE, hss, map_nsmul, two_nsmul, ← two_mul, ← two_mul] at e
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
    have h20 : (2 : E) ≠ 0 := two_ne_zero
    exact mul_left_cancel₀ h20 e
  have hT1 : ‖T‖ ≤ 1 := by rw [← norm_algebraMap' E T, h3]; exact hs1
  exact hψ.1 T hT1

end GlobalTheory.JR.NormInt

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KrullDimQuotientEqOneIffEqBot
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPowReductionCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IsLocalRing Module

universe u

/- English proof (translation)
Apply `Submodule.exists_mem_ne_zero_of_ne_bot` to reduce the goal to its premises. Introduce `hbot`. Establish `h0` using `ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hbot)`. Rewrite `h0` using `[h]`. Conclude with `absurd h0 (by decide)`.
-/
theorem PowSpanFinrankBounded.exists_ne_zero_mem_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    (h : ringKrullDim A = 1) : ∃ x ∈ maximalIdeal A, x ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro hbot
  have h0 := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hbot)
  rw [h] at h0
  exact absurd h0 (by decide)

/- English proof (translation)
Establish `: Module.Finite (A ⧸ maximalIdeal A) (M ⧸ maximalIdeal A • (⊤ : Submodule A M))` using `Module.Finite.of_restrictScalars_finite A _ _`. Rewrite using `[Module.length_eq_of_surjective (S := A) (R := A ⧸ maximalIdeal A) Ideal.Quotient.mk_surjective]`. Set `_ : Field (A ⧸ maximalIdeal A)` to `Ideal.Quotient.field _`. Conclude with `(Module.length_eq_finrank (A ⧸ maximalIdeal A) _).symm`.
-/
theorem PowSpanFinrankBounded.finrank_quotient_eq_length {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (finrank (A ⧸ maximalIdeal A) (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) : ℕ∞) =
      length A (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) := by
  have : Module.Finite (A ⧸ maximalIdeal A) (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ maximalIdeal A) Ideal.Quotient.mk_surjective]
  let _ : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  exact (Module.length_eq_finrank (A ⧸ maximalIdeal A) _).symm

/- English proof (translation)
Establish `hle : LinearMap.range (LinearMap.lsmul A ↥N x) ≤ maximalIdeal A • (⊤ : Submodule A ↥N)`. Introduce and unpack `_ ⟨m, rfl⟩`. Conclude with `Submodule.smul_mem_smul hx Submodule.mem_top`. Rewrite using `[spanFinrank_eq_finrank_quotient N (IsNoetherian.noetherian N), PowSpanFinrankBounded.finrank_quotient_eq_length]`. Conclude with `Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)`.
-/
theorem PowSpanFinrankBounded.spanFinrank_le_length {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (N : Ideal A) {x : A} (hx : x ∈ maximalIdeal A) :
    (N.spanFinrank : ℕ∞) ≤ length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N x)) := by
  have hle : LinearMap.range (LinearMap.lsmul A ↥N x) ≤ maximalIdeal A • (⊤ : Submodule A ↥N) := by
    rintro _ ⟨m, rfl⟩
    exact Submodule.smul_mem_smul hx Submodule.mem_top
  rw [spanFinrank_eq_finrank_quotient N (IsNoetherian.noetherian N),
    PowSpanFinrankBounded.finrank_quotient_eq_length]
  exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

/- English proof (translation)
Introduce `A _ _ _ _ h I`. Take `⟨x, hxm, hx0⟩` from `PowSpanFinrankBounded.exists_ne_zero_mem_maximalIdeal h`. Use `ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq (A := A) h` as an intermediate fact. Establish `hA` using `ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A A x h hx0`. Establish `hfin` using `ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top A hx0`.

Rewrite `hA` using `[finrank_self, Nat.cast_one, one_mul]`. Establish `hord : Ring.ord A x ≠ ⊤` using `hA ▸ hfin`. Use `⟨(Ring.ord A x).toNat, fun n => ?_⟩` and prove the remaining obligations. Establish `hN` using `ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A ↥(I ^ n) x h hx0`. Establish `hr : finrank A ↥(I ^ n) ≤ 1` using `(Submodule.finrank_le (I ^ n)).trans_eq (finrank_self A)`.

Establish `key : ((I ^ n).spanFinrank : ℕ∞) ≤ ((Ring.ord A x).toNat : ℕ∞)`. Rewrite using `[ENat.natCast_toNat hord]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `key` after adjusting the coercions.
-/
theorem PowSpanFinrankBounded.proof : PowSpanFinrankBounded.Statement.{u} := by
  intro A _ _ _ _ h I
  obtain ⟨x, hxm, hx0⟩ := PowSpanFinrankBounded.exists_ne_zero_mem_maximalIdeal h
  have := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq (A := A) h
  have hA := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A A x h hx0
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top A hx0
  rw [finrank_self, Nat.cast_one, one_mul] at hA
  have hord : Ring.ord A x ≠ ⊤ := hA ▸ hfin
  refine ⟨(Ring.ord A x).toNat, fun n => ?_⟩
  have hN := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A ↥(I ^ n) x h hx0
  have hr : finrank A ↥(I ^ n) ≤ 1 := (Submodule.finrank_le (I ^ n)).trans_eq (finrank_self A)
  have key : ((I ^ n).spanFinrank : ℕ∞) ≤ ((Ring.ord A x).toNat : ℕ∞) := by
    rw [ENat.natCast_toNat hord]
    calc ((I ^ n).spanFinrank : ℕ∞)
        ≤ length A (↥(I ^ n) ⧸ LinearMap.range (LinearMap.lsmul A ↥(I ^ n) x)) :=
          PowSpanFinrankBounded.spanFinrank_le_length (I ^ n) hxm
      _ = (finrank A ↥(I ^ n) : ℕ∞) * Ring.ord A x := hN
      _ ≤ 1 * Ring.ord A x := by gcongr; exact_mod_cast hr
      _ = Ring.ord A x := one_mul _
  exact_mod_cast key

end GroundTheory.Heights₂.Heights.NumbersDVR

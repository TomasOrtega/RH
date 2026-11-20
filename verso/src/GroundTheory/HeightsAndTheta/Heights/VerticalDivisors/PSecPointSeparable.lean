import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecPointSeparable
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenericFormsKer
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsDerivSpanTrdeg
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFreeParAlgIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace SecPointSeparable

/- English proof (translation)
Rewrite using `[← Algebra.FormallyUnramified.iff_isSeparable]`. Use `⟨⟨fun a b => ?_⟩⟩` and prove the remaining obligations. Establish `key : ∀ ω : Ω[L⁄K], ω = 0`. Introduce `ω`. Use `(Module.forall_dual_apply_eq_zero_iff L ω).1 fun φ => ?_` and prove the remaining obligations.

Establish `: φ = 0`. Apply `(KaehlerDifferential.linearMapEquivDerivation K L).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `h _`. Rewrite using `[this, LinearMap.zero_apply]`.

Rewrite using `[key a, key b]`.
-/
theorem isSeparable_of_derivation_eq_zero {K L : Type} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (h : ∀ D : Derivation K L L, D = 0) : Algebra.IsSeparable K L := by
  rw [← Algebra.FormallyUnramified.iff_isSeparable]
  refine ⟨⟨fun a b => ?_⟩⟩
  have key : ∀ ω : Ω[L⁄K], ω = 0 := by
    intro ω
    refine (Module.forall_dual_apply_eq_zero_iff L ω).1 fun φ => ?_
    have : φ = 0 := by
      apply (KaehlerDifferential.linearMapEquivDerivation K L).injective
      rw [map_zero]
      exact h _
    rw [this, LinearMap.zero_apply]
  rw [key a, key b]

end SecPointSeparable

open SecPointSeparable in
/- English proof (translation)
Introduce `k _ _ n e L _ _ _ _ _ x hx hU hT htr`. Take `⟨j₀, hj₀⟩ : ∃ j₀, x j₀ ≠ 0` from `by by_contra! h`. Simplify using `[h] at hT`. Use `set z : Fin n → L := fun m => x m * (x j₀)⁻¹ with hz`. Take `⟨r, hre, b, hb⟩` from `h₂ k L (Fin n) z e (htr j₀ hj₀)`.

Establish `hind` using `h₃ k n e L x hx hU hT j₀ hj₀ (htr j₀ hj₀)`. Apply `isSeparable_of_derivation_eq_zero` to reduce the goal to its premises. Introduce `D`. Take `⟨c, hc⟩` from `hb (D.restrictScalars k)`. Establish `hc' : ∀ j, D (z j) = ∑ m, c m * (b m j : L)` using `hc`.

Establish `hDK : ∀ a : GenParField k e n, D (algebraMap (GenParField k e n) L a) = 0` using `fun a => D.map_algebraMap a`. Establish `hlin : ∀ (a : GenParField k e n) (y : L), D (algebraMap (GenParField k e n) L a * y) = algebraMap (GenParField k e n) L a * D y`. Introduce `a y`. Rewrite using `[D.leibniz, hDK, smul_zero, add_zero, smul_eq_mul]`. Establish `hDz₀ : D (z j₀) = 0`.

Simplify using `only [z, mul_inv_cancel₀ hj₀, Derivation.map_one_eq_zero]`. Establish `hUDz : ∀ i : Fin e, ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * D (z j) = 0`. Introduce `i`. Establish `h0 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j = 0`. Simplify using `only [z, ← mul_assoc, ← Finset.sum_mul, hU i, zero_mul]`.

Use `congrArg D h0` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun j _ => (hlin _ _).symm`. Establish `hDz : ∀ j, D (z j) = 0`.

Establish `key` using `h₁ (IntermediateField.adjoin k (Set.range z)) L {j : Fin n // j ≠ j₀} e r hre (fun p => algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1)))) hind (fun m j => b m j.1) c (fun i => ?_)`. Introduce `j`. Distinguish the cases in `hj : j = j₀`. Rewrite using `[hj, hDz₀]`. Rewrite using `[hc' j]`.

Conclude with `key ⟨j, hj⟩`. Use `hUDz i` as an intermediate fact. Rewrite `this` using `[Fintype.sum_eq_add_sum_subtype_ne _ j₀, hDz₀, mul_zero, zero_add]`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hc' j.1]`. Both sides reduce to the same expression. Establish `hx₀ : D (x j₀) = 0`. Establish `hs : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j = (x j₀)⁻¹`. Simplify using `only [z, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]`.

Establish `h1` using `congrArg D hs`. Rewrite `h1` using `[map_sum, Finset.sum_eq_zero fun j _ => by rw [hlin, hDz, mul_zero], Derivation.leibniz_inv, eq_comm, smul_eq_mul, neg_mul, neg_eq_zero, mul_eq_zero]`. Conclude with `h1.resolve_left (pow_ne_zero _ (inv_ne_zero hj₀))`. Establish `hxj : ∀ j, D (x j) = 0`. Introduce `j`.

Establish `hxz : x j = z j * x j₀` using `by simp only [z, mul_assoc, inv_mul_cancel₀ hj₀, mul_one]`. Rewrite using `[hxz, D.leibniz, hx₀, hDz, smul_zero, smul_zero, add_zero]`. Conclude with `Derivation.ext_of_adjoin_eq_top (Set.range x) hx (by rintro _ ⟨j, rfl⟩; simpa using hxj j)`.
-/
theorem SecPointSeparable.proof (h₁ : GenericFormsKer.Statement) (h₂ : DerivSpanTrdeg.Statement)
    (h₃ : FreeParAlgIndep.Statement) : SecPointSeparable.Statement := by
  intro k _ _ n e L _ _ _ _ _ x hx hU hT htr
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, x j₀ ≠ 0 := by
    by_contra! h
    simp [h] at hT
  set z : Fin n → L := fun m => x m * (x j₀)⁻¹ with hz
  obtain ⟨r, hre, b, hb⟩ := h₂ k L (Fin n) z e (htr j₀ hj₀)
  have hind := h₃ k n e L x hx hU hT j₀ hj₀ (htr j₀ hj₀)
  apply isSeparable_of_derivation_eq_zero
  intro D
  obtain ⟨c, hc⟩ := hb (D.restrictScalars k)
  have hc' : ∀ j, D (z j) = ∑ m, c m * (b m j : L) := hc
  have hDK : ∀ a : GenParField k e n, D (algebraMap (GenParField k e n) L a) = 0 :=
    fun a => D.map_algebraMap a
  have hlin : ∀ (a : GenParField k e n) (y : L),
      D (algebraMap (GenParField k e n) L a * y) = algebraMap (GenParField k e n) L a * D y := by
    intro a y
    rw [D.leibniz, hDK, smul_zero, add_zero, smul_eq_mul]
  have hDz₀ : D (z j₀) = 0 := by
    simp only [z, mul_inv_cancel₀ hj₀, Derivation.map_one_eq_zero]
  have hUDz : ∀ i : Fin e,
      ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * D (z j) = 0 := by
    intro i
    have h0 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j = 0 := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hU i, zero_mul]
    have := congrArg D h0
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => (hlin _ _).symm
  have hDz : ∀ j, D (z j) = 0 := by
    have key := h₁ (IntermediateField.adjoin k (Set.range z)) L {j : Fin n // j ≠ j₀} e r hre
      (fun p => algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1)))) hind
      (fun m j => b m j.1) c (fun i => ?_)
    · intro j
      by_cases hj : j = j₀
      · rw [hj, hDz₀]
      · rw [hc' j]
        exact key ⟨j, hj⟩
    · have := hUDz i
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, hDz₀, mul_zero, zero_add] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc' j.1]
      rfl
  have hx₀ : D (x j₀) = 0 := by
    have hs : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j = (x j₀)⁻¹ := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]
    have h1 := congrArg D hs
    rw [map_sum, Finset.sum_eq_zero fun j _ => by rw [hlin, hDz, mul_zero], Derivation.leibniz_inv,
      eq_comm, smul_eq_mul, neg_mul, neg_eq_zero, mul_eq_zero] at h1
    exact h1.resolve_left (pow_ne_zero _ (inv_ne_zero hj₀))
  have hxj : ∀ j, D (x j) = 0 := by
    intro j
    have hxz : x j = z j * x j₀ := by simp only [z, mul_assoc, inv_mul_cancel₀ hj₀, mul_one]
    rw [hxz, D.leibniz, hx₀, hDz, smul_zero, smul_zero, add_zero]
  exact Derivation.ext_of_adjoin_eq_top (Set.range x) hx (by rintro _ ⟨j, rfl⟩; simpa using hxj j)

end

end GroundTheory.Heights₂.Heights.Vertical

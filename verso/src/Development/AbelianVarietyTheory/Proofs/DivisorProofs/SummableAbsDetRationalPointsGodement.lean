import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionLeviGLIsotropicFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBoundDiagonalExponentsRationalPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRationalPointsFixerTorusClassesLeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SummableOfCount
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

open scoped Pointwise

noncomputable section

namespace GlobalTheory.SphEis.Summ

/- English proof (translation)
The claim follows from `Units.ext (by change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _ rw [Matrix.diagonal_mul_diagonal] exact congrArg Matrix.diagonal (funext fun i => congrArg Units.val (_root_.zpow_add _ _ _)))`.
-/
theorem tor_add (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {j : ℕ}
    (μ : Fin j → ℕ) (m₀ : ℕ) :
    tor F E (fun i => (μ i : ℤ) + -(m₀ : ℤ)) = tor F E (fun i => (μ i : ℤ)) * tor F E (fun _ => -(m₀ : ℤ)) :=
  Units.ext (by
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => congrArg Units.val (_root_.zpow_add _ _ _)))

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv ι x p k β K hK hx e hk hβ hi t ht`. Establish `hb : 1 < bse F` using `one_lt_pow₀ (by norm_num) Fintype.card_ne_zero`. Establish `hb0 : 0 < bse F` using `one_pos.trans hb`. Establish `hfp : fixG σ J C ≤ parFlag σ J C (fun _ => 0)` using `fun g hg => ⟨⟨1, Matrix.blockTriangular_one, by rw [Matrix.mul_one]; exact hg⟩, 1, Matrix.blockTriangular_one, by`. Rewrite using `[Matrix.mul_one]`.

Conclude with `inv_mem hg⟩`. Take `⟨W, B, hW, hR⟩` from `GlobalTheory.T.reduction_leviGL_isotropicFrame F E σ n J j m C D Z J₀ hF lv hlv`. Use `choose γ hγ hγP q hq l w hw hred hle using fun i => hR (p i) (β i) (hβ i)`. Establish `hWK : IsCompact (W * K)` using `hW.mul hK`. Take `⟨m₀, hm₀⟩` from `GlobalTheory.T.exists_lowerBound_diagonalExponents_rationalPoint F E σ n J j m C D Z J₀ hF lv hlv (W * K) hWK`.

Establish `hl : ∀ i r, -(m₀ : ℤ) ≤ l i r` using `fun i => hm₀ (q i) (hq i) (l i) (w i * k i) (Set.mul_mem_mul (hw i) (hk i)) (by`. Use `mul_mem (hγ i) (hx i)` as an intermediate fact. Rewrite using `[e, ← mul_assoc, hred, mul_assoc _ (w i)] at this)` and apply the resulting hypothesis. Take `⟨μ, hμ⟩ : ∃ μ : ι → Fin j → ℕ, ∀ i, l i = fun r => (μ i r : ℤ) + -(m₀ : ℤ)` from `⟨fun i r => (l i r + m₀).toNat, fun i => funext fun r => by have := hl i r; beta_reduce; omega⟩`. Take `⟨a, ha⟩ : ∃ a, a = lv (tor F E fun _ => -(m₀ : ℤ))` from `⟨_, rfl⟩`.

Establish `hW' : IsCompact ((fun g => a * g) '' (W * K))` using `hWK.image (continuous_mul_left a)`. Take `⟨N, hN⟩` from `GlobalTheory.T.card_rationalPoints_fixer_torusClasses_le F E σ n J j m C D Z J₀ hF lv hlv _ hW'`. Establish `hz : ∀ i, γ i * x i = q i * lv (tor F E fun r => (μ i r : ℤ)) * (a * (w i * k i))` using `fun i => by`. Rewrite using `[e, ← mul_assoc, hred, hμ, tor_add, map_mul, ← ha]`. Simplify using `only [mul_assoc]`.

Establish `hinj : ∀ i i', γ i' * x i' * (γ i * x i)⁻¹ ∈ fixG σ J C → i = i'` using `fun i i' h => hi i i' (by`. Establish `h2 : x i' * (x i)⁻¹ = (γ i')⁻¹ * (γ i' * x i' * (γ i * x i)⁻¹) * γ i` using `by group`. Rewrite using `[h2]`. Conclude with `mul_mem (mul_mem (inv_mem (hγP i')) (hfp h)) (hγP i))`. Use `GlobalTheory.GodementSectionReduction.summable_of_count ι j (m + j) (bse F) (max (B * bse F ^ (m₀ * j)) N) t μ _ hb ht (fun i => ⟨NNReal.coe_nonneg _, ?_⟩) fun μ' S hS => ?_` and prove the remaining obligations.

Use `le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))` and prove the remaining obligations. Use `(hle i).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[mul_assoc, hμ]`. Simplify using `only [zpow_add₀ hb0.ne', _root_.zpow_neg, zpow_natCast, mul_inv, inv_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]`. Rewrite using `[mul_comm (∏ _, _)]`.

Use `le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))` and prove the remaining obligations. Establish `hc : (S.image fun i => γ i * x i).card = S.card` using `Finset.card_image_of_injOn fun i _ i' _ h => hinj i i' (by`. Rewrite using `[← h, mul_inv_cancel]`. Conclude with `one_mem _)`. Rewrite using `[← hc]`.

Use `hN μ' _ ?_ ?_ ?_` and prove the remaining obligations. Introduce `s hs`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hs`. Conclude with `mul_mem (hγ i) (hx i)`. Introduce `s hs s' hs' h`.

Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hs`. Take `⟨i', -, rfl⟩` from `Finset.mem_image.1 hs'`. Rewrite using `[hinj i i' h]`. Introduce `s hs`. Take `⟨i, hi', rfl⟩` from `Finset.mem_image.1 hs`.

Conclude with `⟨q i, hq i, a * (w i * k i), ⟨w i * k i, Set.mul_mem_mul (hw i) (hk i), rfl⟩, by rw [hz, hS i hi']⟩`.
-/
theorem summable_absDet : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ (ι : Type) (x p k : ι → GAd σ J) (β : ι → GL (Fin j) (AF F ⊗[F] E)) (K : Set (GAd σ J)), IsCompact K → (∀ q, x q ∈ ratPts σ J) → (∀ q, x q = p q * k q) → (∀ q, k q ∈ K) → (∀ q, (matHom _ σ J (p q)).1 * adMat F C = adMat F C * (β q).1) → (∀ q q', x q' * (x q)⁻¹ ∈ parFlag σ J C (fun _ => 0) → q = q') → ∀ t : ℝ, ((m + j : ℕ) : ℝ) < t → Summable fun q => (absE F E (Matrix.GeneralLinearGroup.det (β q)) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv ι x p k β K hK hx e hk hβ hi t ht
  classical
  have hb : 1 < bse F := one_lt_pow₀ (by norm_num) Fintype.card_ne_zero
  have hb0 : 0 < bse F := one_pos.trans hb
  have hfp : fixG σ J C ≤ parFlag σ J C (fun _ => 0) := fun g hg =>
    ⟨⟨1, Matrix.blockTriangular_one, by rw [Matrix.mul_one]; exact hg⟩, 1, Matrix.blockTriangular_one, by
      rw [Matrix.mul_one]; exact inv_mem hg⟩
  obtain ⟨W, B, hW, hR⟩ := GlobalTheory.T.reduction_leviGL_isotropicFrame F E σ n J j m C D Z J₀ hF lv hlv
  choose γ hγ hγP q hq l w hw hred hle using fun i => hR (p i) (β i) (hβ i)
  have hWK : IsCompact (W * K) := hW.mul hK
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.exists_lowerBound_diagonalExponents_rationalPoint F E σ n J j m C D Z J₀ hF lv hlv (W * K) hWK
  have hl : ∀ i r, -(m₀ : ℤ) ≤ l i r := fun i =>
    hm₀ (q i) (hq i) (l i) (w i * k i) (Set.mul_mem_mul (hw i) (hk i)) (by
      have := mul_mem (hγ i) (hx i)
      rwa [e, ← mul_assoc, hred, mul_assoc _ (w i)] at this)
  obtain ⟨μ, hμ⟩ : ∃ μ : ι → Fin j → ℕ, ∀ i, l i = fun r => (μ i r : ℤ) + -(m₀ : ℤ) :=
    ⟨fun i r => (l i r + m₀).toNat, fun i => funext fun r => by have := hl i r; beta_reduce; omega⟩
  obtain ⟨a, ha⟩ : ∃ a, a = lv (tor F E fun _ => -(m₀ : ℤ)) := ⟨_, rfl⟩
  have hW' : IsCompact ((fun g => a * g) '' (W * K)) := hWK.image (continuous_mul_left a)
  obtain ⟨N, hN⟩ := GlobalTheory.T.card_rationalPoints_fixer_torusClasses_le F E σ n J j m C D Z J₀ hF lv hlv _ hW'
  have hz : ∀ i, γ i * x i = q i * lv (tor F E fun r => (μ i r : ℤ)) * (a * (w i * k i)) := fun i => by
    rw [e, ← mul_assoc, hred, hμ, tor_add, map_mul, ← ha]
    simp only [mul_assoc]
  have hinj : ∀ i i', γ i' * x i' * (γ i * x i)⁻¹ ∈ fixG σ J C → i = i' := fun i i' h => hi i i' (by
    have h2 : x i' * (x i)⁻¹ = (γ i')⁻¹ * (γ i' * x i' * (γ i * x i)⁻¹) * γ i := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem (hγP i')) (hfp h)) (hγP i))
  refine GlobalTheory.GodementSectionReduction.summable_of_count ι j (m + j) (bse F) (max (B * bse F ^ (m₀ * j)) N) t μ _ hb ht
    (fun i => ⟨NNReal.coe_nonneg _, ?_⟩) fun μ' S hS => ?_
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    refine (hle i).trans (le_of_eq ?_)
    rw [mul_assoc, hμ]
    simp only [zpow_add₀ hb0.ne', _root_.zpow_neg, zpow_natCast, mul_inv, inv_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [mul_comm (∏ _, _)]
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    have hc : (S.image fun i => γ i * x i).card = S.card :=
      Finset.card_image_of_injOn fun i _ i' _ h => hinj i i' (by
        rw [← h, mul_inv_cancel]
        exact one_mem _)
    rw [← hc]
    refine hN μ' _ ?_ ?_ ?_
    · intro s hs
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      exact mul_mem (hγ i) (hx i)
    · intro s hs s' hs' h
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hs'
      rw [hinj i i' h]
    · intro s hs
      obtain ⟨i, hi', rfl⟩ := Finset.mem_image.1 hs
      exact ⟨q i, hq i, a * (w i * k i), ⟨w i * k i, Set.mul_mem_mul (hw i) (hk i), rfl⟩, by rw [hz, hS i hi']⟩

end GlobalTheory.SphEis.Summ

end

import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBlockDiagMapGenBlock
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane

variable {N : ℕ}

/- English proof (translation)
Establish `e : (S.image σ).card = S.card` using `Finset.card_image_of_injOn hσ.injOn`. Unfold `minorIJ`. Rewrite using `[dif_pos e]`. Establish `hf : (fun i => σ (S.orderEmbOfFin rfl i)) = ⇑((S.image σ).orderEmbOfFin e)`. Apply `Finset.orderEmbOfFin_unique e` to reduce the goal to its premises.

Introduce `i`. Conclude with `Finset.mem_image_of_mem σ (Finset.orderEmbOfFin_mem S rfl i)`. Introduce `i i' hii`. Conclude with `hσ (Finset.orderEmbOfFin_mem S rfl i) (Finset.orderEmbOfFin_mem S rfl i') ((S.orderEmbOfFin rfl).strictMono hii)`. Rewrite using `[← hf, Matrix.det_of_upperTriangular]`.

Simplify using `only [Matrix.submatrix_apply] conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S rfl]`. Rewrite using `[Finset.prod_map]`. Both sides reduce to the same expression. Introduce `i i' hii`. Conclude with `hT _ (Finset.orderEmbOfFin_mem S rfl i) _ (Finset.orderEmbOfFin_mem S rfl i') ((S.orderEmbOfFin rfl).strictMono hii)`.
-/
theorem minorIJ_image_of_tri {R : Type} [CommRing R] (M : Matrix (Fin N) (Fin N) R) (S : Finset (Fin N))
    (σ : Fin N → Fin N) (hσ : StrictMonoOn σ S)
    (hT : ∀ x ∈ S, ∀ y ∈ S, y < x → M (σ x) y = 0) :
    minorIJ M (S.image σ) S = ∏ c ∈ S, M (σ c) c := by
  have e : (S.image σ).card = S.card := Finset.card_image_of_injOn hσ.injOn
  unfold minorIJ
  rw [dif_pos e]
  have hf : (fun i => σ (S.orderEmbOfFin rfl i)) = ⇑((S.image σ).orderEmbOfFin e) := by
    apply Finset.orderEmbOfFin_unique e
    · intro i
      exact Finset.mem_image_of_mem σ (Finset.orderEmbOfFin_mem S rfl i)
    · intro i i' hii
      exact hσ (Finset.orderEmbOfFin_mem S rfl i) (Finset.orderEmbOfFin_mem S rfl i')
        ((S.orderEmbOfFin rfl).strictMono hii)
  rw [← hf, Matrix.det_of_upperTriangular]
  · simp only [Matrix.submatrix_apply]
    conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S rfl]
    rw [Finset.prod_map]
    rfl
  · intro i i' hii
    exact hT _ (Finset.orderEmbOfFin_mem S rfl i) _ (Finset.orderEmbOfFin_mem S rfl i')
      ((S.orderEmbOfFin rfl).strictMono hii)

/- English proof (translation)
Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]`. Use `congr 1`. Distinguish the cases in `hy : y = ca`. Substitute `hy` using the available equality. Simplify using `[Matrix.mul_single_apply_same, mul_comm]`.

Simplify using `[Matrix.mul_single_apply_of_ne, hy]`.
-/
theorem mul_entry (B : Matrix (Fin N) (Fin N) ℂ) (ca cb x y : Fin N) (s : ℂ) :
    (B * (1 + Matrix.single cb ca s)) x y = B x y + if y = ca then s * B x cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hy : y = ca
  · subst hy
    simp [Matrix.mul_single_apply_same, mul_comm]
  · simp [Matrix.mul_single_apply_of_ne, hy]

/- English proof (translation)
Simplify using `[Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]`.
-/
theorem one_entry (ca cb x y : Fin N) (s : ℂ) :
    (1 + Matrix.single cb ca s : Matrix (Fin N) (Fin N) ℂ) x y =
      (if x = y then 1 else 0) + if cb = x ∧ ca = y then s else 0 := by
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

/- English proof (translation)
Establish `hne : ∀ c ∈ S, c ≠ cb` using `fun c hc => ne_of_lt ((hmax c hc).trans_lt hlt)`. Establish `hcaNe : ca ≠ cb` using `ne_of_lt hlt`. Set `σ : Fin N → Fin N` to `fun c => if c = ca then cb else c`. Establish `hσca : σ ca = cb` using `if_pos rfl`. Establish `hσne : ∀ c, c ≠ ca → σ c = c` using `fun c hc => if_neg hc`.

Establish `hσ : StrictMonoOn σ S`. Introduce `x _ y hy hxy`. Establish `hx' : x ≠ ca` using `ne_of_lt (hxy.trans_le (hmax y hy))`. Rewrite using `[hσne x hx']`. Distinguish the cases in `hy' : y = ca`.

Rewrite using `[hy', hσca]`. Conclude with `(hxy.trans_le (hmax y hy)).trans hlt`. Rewrite using `[hσne y hy']`. Conclude with `hxy`. Establish `hge : ∀ x ∈ S, x ≤ σ x`.

Introduce `x hx`. Distinguish the cases in `hx' : x = ca`. Rewrite using `[hx', hσca]`. Conclude with `hlt.le`. Rewrite using `[hσne x hx']`.

Establish `hyne : ∀ x ∈ S, ∀ y, y < x → y ≠ ca` using `fun x hx y hy => ne_of_lt (hy.trans_le (hmax x hx))`. Establish `L1 : minorIJ (B * (1 + Matrix.single cb ca t')) S S = (∏ c ∈ S.erase ca, B c c) * (B ca ca + t' * B ca cb)`. Establish `h0` using `minorIJ_image_of_tri (B * (1 + Matrix.single cb ca t')) S id strictMonoOn_id (by`. Introduce `x hx y _ hy`. Rewrite using `[mul_entry, if_neg (hyne x hx y hy), add_zero]`.

Conclude with `hB hy)`. Rewrite `h0` using `[Finset.image_id]`. Rewrite using `[h0, ← Finset.prod_erase_mul S _ hca]`. Use `congr 1`. Use `Finset.prod_congr rfl fun c hc => ?_` and prove the remaining obligations.

Rewrite using `[id, mul_entry, if_neg (Finset.ne_of_mem_erase hc), add_zero]`. Rewrite using `[id, mul_entry, if_pos rfl]`. Establish `R1 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S S = 1`. Establish `h0` using `minorIJ_image_of_tri (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S id strictMonoOn_id (by`. Introduce `x hx y _ hy`.

Rewrite using `[id, one_entry, if_neg (ne_of_gt hy), if_neg (fun h => hne x hx h.1.symm), add_zero])`. Rewrite `h0` using `[Finset.image_id]`. Rewrite using `[h0]`. Use `Finset.prod_eq_one fun c hc => ?_` and prove the remaining obligations. Rewrite using `[id, one_entry, if_pos rfl, if_neg (fun h => hne c hc h.1.symm), add_zero]`.

Establish `L2 : minorIJ (B * (1 + Matrix.single cb ca t')) (S.image σ) S = (∏ c ∈ S.erase ca, B c c) * (t' * B cb cb)`. Rewrite using `[minorIJ_image_of_tri _ S σ hσ (by`. Introduce `x hx y _ hy`. Rewrite using `[mul_entry, if_neg (hyne x hx y hy), add_zero]`. Conclude with `hB (hy.trans_le (hge x hx))), ← Finset.prod_erase_mul S _ hca]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun c hc => ?_` and prove the remaining obligations. Establish `hc'` using `Finset.ne_of_mem_erase hc`. Rewrite using `[hσne c hc', mul_entry, if_neg hc', add_zero]`. Establish `h0 : B cb ca = 0` using `hB hlt`.

Rewrite using `[hσca, mul_entry, if_pos rfl, h0, zero_add]`. Establish `R2 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (S.image σ) S = t`. Rewrite using `[minorIJ_image_of_tri _ S σ hσ (by`. Introduce `x hx y _ hy`. Rewrite using `[one_entry, if_neg (ne_of_gt (hy.trans_le (hge x hx))), if_neg (fun h => hyne x hx y hy h.2.symm), add_zero]), ← Finset.prod_erase_mul S _ hca]`.

Establish `h1 : ∏ c ∈ S.erase ca, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (σ c) c = 1`. Use `Finset.prod_eq_one fun c hc => ?_` and prove the remaining obligations. Establish `hc'` using `Finset.ne_of_mem_erase hc`. Rewrite using `[hσne c hc', one_entry, if_pos rfl, if_neg (fun h => hne c (Finset.mem_of_mem_erase hc) h.1.symm), add_zero]`. Rewrite using `[h1, one_mul, hσca, one_entry, if_neg (Ne.symm hcaNe), if_pos ⟨rfl, rfl⟩, zero_add]`.

Establish `e1` using `H S`. Establish `e2` using `H (S.image σ)`. Rewrite `e1` using `[L1, R1, mul_one]`. Rewrite `e2` using `[L2, R2]`. Conclude with `⟨e1.symm, e2.symm⟩`.
-/
theorem param_core (S : Finset (Fin N)) (ca cb : Fin N) (hca : ca ∈ S) (hmax : ∀ c ∈ S, c ≤ ca) (hlt : ca < cb)
    (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.BlockTriangular id) (t t' μ : ℂ)
    (H : ∀ J, minorIJ (B * (1 + Matrix.single cb ca t')) J S = μ * minorIJ (1 + Matrix.single cb ca t) J S) :
    μ = (∏ c ∈ S.erase ca, B c c) * (B ca ca + t' * B ca cb) ∧
      μ * t = (∏ c ∈ S.erase ca, B c c) * (t' * B cb cb) := by
  have hne : ∀ c ∈ S, c ≠ cb := fun c hc => ne_of_lt ((hmax c hc).trans_lt hlt)
  have hcaNe : ca ≠ cb := ne_of_lt hlt
  let σ : Fin N → Fin N := fun c => if c = ca then cb else c
  have hσca : σ ca = cb := if_pos rfl
  have hσne : ∀ c, c ≠ ca → σ c = c := fun c hc => if_neg hc
  have hσ : StrictMonoOn σ S := by
    intro x _ y hy hxy
    have hx' : x ≠ ca := ne_of_lt (hxy.trans_le (hmax y hy))
    rw [hσne x hx']
    by_cases hy' : y = ca
    · rw [hy', hσca]
      exact (hxy.trans_le (hmax y hy)).trans hlt
    · rw [hσne y hy']
      exact hxy
  have hge : ∀ x ∈ S, x ≤ σ x := by
    intro x hx
    by_cases hx' : x = ca
    · rw [hx', hσca]
      exact hlt.le
    · rw [hσne x hx']
  have hyne : ∀ x ∈ S, ∀ y, y < x → y ≠ ca := fun x hx y hy => ne_of_lt (hy.trans_le (hmax x hx))

  have L1 : minorIJ (B * (1 + Matrix.single cb ca t')) S S =
      (∏ c ∈ S.erase ca, B c c) * (B ca ca + t' * B ca cb) := by
    have h0 := minorIJ_image_of_tri (B * (1 + Matrix.single cb ca t')) S id strictMonoOn_id (by
      intro x hx y _ hy
      rw [mul_entry, if_neg (hyne x hx y hy), add_zero]
      exact hB hy)
    rw [Finset.image_id] at h0
    rw [h0, ← Finset.prod_erase_mul S _ hca]
    congr 1
    · refine Finset.prod_congr rfl fun c hc => ?_
      rw [id, mul_entry, if_neg (Finset.ne_of_mem_erase hc), add_zero]
    · rw [id, mul_entry, if_pos rfl]
  have R1 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
    have h0 := minorIJ_image_of_tri (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S id strictMonoOn_id (by
      intro x hx y _ hy
      rw [id, one_entry, if_neg (ne_of_gt hy), if_neg (fun h => hne x hx h.1.symm), add_zero])
    rw [Finset.image_id] at h0
    rw [h0]
    refine Finset.prod_eq_one fun c hc => ?_
    rw [id, one_entry, if_pos rfl, if_neg (fun h => hne c hc h.1.symm), add_zero]

  have L2 : minorIJ (B * (1 + Matrix.single cb ca t')) (S.image σ) S =
      (∏ c ∈ S.erase ca, B c c) * (t' * B cb cb) := by
    rw [minorIJ_image_of_tri _ S σ hσ (by
      intro x hx y _ hy
      rw [mul_entry, if_neg (hyne x hx y hy), add_zero]
      exact hB (hy.trans_le (hge x hx))), ← Finset.prod_erase_mul S _ hca]
    congr 1
    · refine Finset.prod_congr rfl fun c hc => ?_
      have hc' := Finset.ne_of_mem_erase hc
      rw [hσne c hc', mul_entry, if_neg hc', add_zero]
    · have h0 : B cb ca = 0 := hB hlt
      rw [hσca, mul_entry, if_pos rfl, h0, zero_add]
  have R2 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (S.image σ) S = t := by
    rw [minorIJ_image_of_tri _ S σ hσ (by
      intro x hx y _ hy
      rw [one_entry, if_neg (ne_of_gt (hy.trans_le (hge x hx))),
        if_neg (fun h => hyne x hx y hy h.2.symm), add_zero]), ← Finset.prod_erase_mul S _ hca]
    have h1 : ∏ c ∈ S.erase ca, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (σ c) c = 1 := by
      refine Finset.prod_eq_one fun c hc => ?_
      have hc' := Finset.ne_of_mem_erase hc
      rw [hσne c hc', one_entry, if_pos rfl,
        if_neg (fun h => hne c (Finset.mem_of_mem_erase hc) h.1.symm), add_zero]
    rw [h1, one_mul, hσca, one_entry, if_neg (Ne.symm hcaNe), if_pos ⟨rfl, rfl⟩, zero_add]
  have e1 := H S
  have e2 := H (S.image σ)
  rw [L1, R1, mul_one] at e1
  rw [L2, R2] at e2
  exact ⟨e1.symm, e2.symm⟩

/- English proof (translation)
Introduce `N j a b ca cb hj hb hab hca hcb h B t t' μ hdet _ hBt hyp`. Establish `hinv : h⁻¹ * h = 1` using `Matrix.nonsing_inv_mul h (isUnit_iff_ne_zero.2 hdet)`. Establish `hcaS : ca ∈ stepCols N j a`. Unfold `lastCol at hca`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`.

Apply the tactic sequence `split_ifs at hca ⊢ <;> omega`. Establish `hmax : ∀ c ∈ stepCols N j a, c ≤ ca`. Introduce `c hc`. Unfold `lastCol at hca`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc`.

Rewrite using `[Fin.le_def]`. Apply the tactic sequence `split_ifs at hca hc <;> omega`. Establish `hlt : ca < cb`. Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers.

Use `param_core _ ca cb hcaS hmax hlt B hBt t t' μ fun J => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc h, ← Matrix.mul_assoc, hinv, Matrix.one_mul]`. Use `_ = ∑ I, minorIJ h⁻¹ J I * minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) := minorIJ_mul_sum _ _ _ _`. Use `_ = μ * ∑ I, minorIJ h⁻¹ J I * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a) := by`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[hyp I]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = μ * minorIJ (h⁻¹ * (h * (1 + Matrix.single cb ca t))) J (stepCols N j a) := by`.

Rewrite using `[minorIJ_mul_sum]`. Use `_ = μ * minorIJ (1 + Matrix.single cb ca t) J (stepCols N j a) := by`. Rewrite using `[← Matrix.mul_assoc, hinv, Matrix.one_mul]`.
-/
theorem param_relation : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h B : Matrix (Fin N) (Fin N) ℂ) (t t' μ : ℂ), h.det ≠ 0 → IsBlockDiag j B → B.BlockTriangular id → (∀ I, minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) = μ * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a)) → μ = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (B ca ca + t' * B ca cb) ∧ μ * t = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (t' * B cb cb) := by
  intro N j a b ca cb hj hb hab hca hcb h B t t' μ hdet _ hBt hyp
  have hinv : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul h (isUnit_iff_ne_zero.2 hdet)
  have hcaS : ca ∈ stepCols N j a := by
    unfold lastCol at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca ⊢ <;> omega
  have hmax : ∀ c ∈ stepCols N j a, c ≤ ca := by
    intro c hc
    unfold lastCol at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Fin.le_def]
    split_ifs at hca hc <;> omega
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  refine param_core _ ca cb hcaS hmax hlt B hBt t t' μ fun J => ?_
  calc minorIJ (B * (1 + Matrix.single cb ca t')) J (stepCols N j a)
      = minorIJ (h⁻¹ * (h * B * (1 + Matrix.single cb ca t'))) J (stepCols N j a) := by
        rw [Matrix.mul_assoc h, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    _ = ∑ I, minorIJ h⁻¹ J I * minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) :=
        minorIJ_mul_sum _ _ _ _
    _ = μ * ∑ I, minorIJ h⁻¹ J I * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [hyp I]
        ring
    _ = μ * minorIJ (h⁻¹ * (h * (1 + Matrix.single cb ca t))) J (stepCols N j a) := by
        rw [minorIJ_mul_sum]
    _ = μ * minorIJ (1 + Matrix.single cb ca t) J (stepCols N j a) := by
        rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane

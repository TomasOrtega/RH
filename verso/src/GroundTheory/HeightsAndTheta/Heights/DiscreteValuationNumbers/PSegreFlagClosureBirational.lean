import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosureBirational
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Lemmas

variable {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω]
  {O : Type*} [CommRing O] [Algebra O Ω] {Φ : Type*} [Field Φ] [Algebra Ω Φ] [Algebra O Φ]
  [IsScalarTower O Ω Φ]

/- English proof (translation)
Simplify using `[segreVec, map_prod]`.
-/
theorem segreVec_algebraMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    segreVec (fun p => algebraMap Ω Φ (y p)) c = algebraMap Ω Φ (segreVec y c) := by
  simp [segreVec, map_prod]

/- English proof (translation)
Establish `hle : chartRing O (segreVec y) c ≤ (chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c).comap (IsScalarTower.toAlgHom O Ω Φ)`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_comap]`. Use `show algebraMap Ω Φ (segreVec y j / segreVec y c) ∈ chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c`.

Rewrite using `[map_div₀, ← segreVec_algebraMap, ← segreVec_algebraMap]`. Conclude with `div_mem_chartRing _ _ _`. Conclude with `hle hz`.
-/
theorem algebraMap_mem_chartRing_segre (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {z : Ω}
    (hz : z ∈ chartRing O (segreVec y) c) :
    algebraMap Ω Φ z ∈ chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c := by
  have hle : chartRing O (segreVec y) c ≤
      (chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c).comap
        (IsScalarTower.toAlgHom O Ω Φ) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    show algebraMap Ω Φ (segreVec y j / segreVec y c) ∈
      chartRing O (segreVec (fun p => algebraMap Ω Φ (y p))) c
    rw [map_div₀, ← segreVec_algebraMap, ← segreVec_algebraMap]
    exact div_mem_chartRing _ _ _
  exact hle hz

end Lemmas

/- English proof (translation)
Use `conv_lhs => rw [← w.sum_repr v]`. Use `Finset.sum_eq_single _ (fun j _ hj => ?_) (by simp)` and prove the remaining obligations. Establish `hlt : (⟨0, h0⟩ : Fin N) < j`. Rewrite using `[Fin.lt_def]`. Establish `: (j : ℕ) ≠ 0` using `fun h => hj (Fin.ext h)`.

Use `show 0 < (j : ℕ)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hv j hlt, zero_smul]`.
-/
theorem eq_repr_smul_basis_first {Ω : Type*} [Field Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (w : Module.Basis (Fin N) Ω E) (h0 : 0 < N) (v : E)
    (hv : ∀ j : Fin N, (⟨0, h0⟩ : Fin N) < j → w.repr v j = 0) :
    v = w.repr v ⟨0, h0⟩ • w ⟨0, h0⟩ := by
  conv_lhs => rw [← w.sum_repr v]
  refine Finset.sum_eq_single _ (fun j _ hj => ?_) (by simp)
  have hlt : (⟨0, h0⟩ : Fin N) < j := by
    rw [Fin.lt_def]
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    show 0 < (j : ℕ)
    omega
  rw [hv j hlt, zero_smul]

/- English proof (translation)
Introduce `O _ _ _ ϖ _ Ω _ _ K _ _ ι _ y d _ N E _ _ B B' _ w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t _ hN c hc c₁ c₂ hc₂`. Use `set i0 : Fin N := ⟨0, hN⟩ with hi0`. Establish `hcΩ : segreVec y c ≠ 0`. Introduce `h`. Apply `hc` to reduce the goal to its premises.

Rewrite using `[segreVec_algebraMap, h, map_zero]`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => Finset.prod_ne_zero_iff.1 hcΩ k (Finset.mem_univ k)`. Establish `hpow : ∀ b : K → ℤ, ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0` using `fun b => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)`. Establish `hmem : ∏ k, y ⟨k, c k⟩ ^ x i0 k ∈ degLat O y (x i0) c` using `⟨1, one_mem _, (one_mul _).symm⟩`. Rewrite `hmem` using `[← hF.flag.graded c hcΩ i0]`.

Take `⟨v, hv, hvj, hv0⟩` from `hmem`. Establish `hmem' : ∏ k, y ⟨k, c k⟩ ^ x' i0 k ∈ degLat O y (x' i0) c` using `⟨1, one_mem _, (one_mul _).symm⟩`. Rewrite `hmem'` using `[← hF.flag'.graded c hcΩ i0]`. Take `⟨v', hv', hvj', hv0'⟩` from `hmem'`. Establish `hv_eq : v = (∏ k, y ⟨k, c k⟩ ^ x i0 k) • w i0`.

Rewrite using `[← hv0]`. Conclude with `eq_repr_smul_basis_first w hN v hvj`. Establish `hv'_eq : v' = (∏ k, y ⟨k, c k⟩ ^ x' i0 k) • w' i0`. Rewrite using `[← hv0']`. Conclude with `eq_repr_smul_basis_first w' hN v' hvj'`.

Establish `hw' : w' i0 = w.repr (w' i0) i0 • w i0` using `eq_repr_smul_basis_first w hN (w' i0) fun j hj => hF.sameFlag i0 j hj`. Use `set u : Ω := w.repr (w' i0) i0 with hudef`. Establish `hu : u ≠ 0`. Introduce `h`. Apply `w'.ne_zero i0` to reduce the goal to its premises.

Rewrite using `[hw', h, zero_smul]`. Use `choose α hα hαeq using fun l => hφ.sections c hcΩ l v hv`. Use `choose β hβ hβeq using fun l => hφ'.sections c hcΩ l v' hv'`. Use `set D : Ω := (∏ k, y ⟨k, c k⟩ ^ x i0 k) * ((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u) with hDdef`. Use `set G : Ω := (∏ k, y ⟨k, c k⟩ ^ a₀ k) * ∏ k, y ⟨k, c k⟩ ^ a₀' k with hGdef`.

Establish `hD : D ≠ 0` using `mul_ne_zero (hpow _) (mul_ne_zero (hpow _) hu)`. Establish `hprod : ∀ (l : Fin M) (m : Fin M'), D * (φ l (w i0) * φ' m (w i0)) = G * (α l * β m)`. Introduce `l m`. Establish `hA : (∏ k, y ⟨k, c k⟩ ^ x i0 k) * φ l (w i0) = α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k`. Rewrite using `[← hαeq l, hv_eq, map_smul, smul_eq_mul]`.

Establish `hB : (∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0) = β m * ∏ k, y ⟨k, c k⟩ ^ a₀' k`. Rewrite using `[← hβeq m, hv'_eq, hw', smul_smul, map_smul, smul_eq_mul]`. Rewrite using `[hDdef, hGdef]`. Take the linear combination `((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0)) * hA + (α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k) * hB`. Establish `hprodΦ : ∀ (l : Fin M) (m : Fin M'), algebraMap Ω Φ D * (algebraMap Ω Φ (φ l (w i0)) * algebraMap Ω Φ (φ' m (w i0))) = algebraMap Ω Φ G * (algebraMap Ω Φ (α l) * algebraMap Ω Φ (β m))`.

Introduce `l m`. Use `congrArg (algebraMap Ω Φ) (hprod l m)` as an intermediate fact. Simplify `this` using `only [map_mul]`. Use `set T : Φ := ∑ i, t i * algebraMap Ω Φ (w.repr (e i) i0) with hT`. Establish `hfc : ∀ j : Fin N, j ≠ i0 → flagCoord w e t 1 j = 0`.

Introduce `j hj`. Establish `: ¬ ((j : ℕ) < 1)`. Introduce `h`. Apply `hj` to reduce the goal to its premises. Use `ext`.

Simplify using `only [hi0]`. Use linear arithmetic over natural numbers and integers. Simplify using `[flagCoord, this]`. Establish `hfc0 : flagCoord w e t 1 i0 = T` using `by simp [flagCoord, hi0, hT]`. Establish `hsome : ∀ l : Fin M, flagLinePt w e φ φ' t 1 ⟨some (), l⟩ = T * algebraMap Ω Φ (φ l (w i0))`.

Introduce `l`. Use `show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ l (w i)) = _`. Rewrite using `[Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]`. Establish `hnone : ∀ l : Fin M', flagLinePt w e φ φ' t 1 ⟨none, l⟩ = T * algebraMap Ω Φ (φ' l (w i0))`. Introduce `l`.

Use `show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ' l (w i)) = _`. Rewrite using `[Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]`. Establish `hseg : ∀ c' : ∀ o, lineBlocks M M' o, segreVec (flagLinePt w e φ φ' t 1) c' = (T * algebraMap Ω Φ (φ' (c' none) (w i0))) * (T * algebraMap Ω Φ (φ (c' (some ())) (w i0)))`. Introduce `c'`. Rewrite using `[segreVec, Fintype.prod_option, Fintype.prod_unique]`.

Conclude with `congrArg₂ (· * ·) (hnone (c' none)) (hsome (c' (some ())))`. Use `⟨algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none)), mul_mem (algebraMap_mem_chartRing_segre y c (hα _)) (algebraMap_mem_chartRing_segre y c (hβ _)), algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none)), mul_mem (algebraMap_mem_chartRing_segre y c (hα _) …` and prove the remaining obligations. Introduce `h0`. Apply `hc₂` to reduce the goal to its premises. Establish `hDΦ : algebraMap Ω Φ D ≠ 0` using `(map_ne_zero _).2 hD`.

Apply `(mul_right_injective₀ hDΦ)` to reduce the goal to its premises. Simplify using `only [mul_zero]`. Rewrite using `[hseg]`. Establish `h2` using `hprodΦ (c₂ (some ())) (c₂ none)`. Take the linear combination `T ^ 2 * h2 + T ^ 2 * algebraMap Ω Φ G * h0`.

Establish `hDΦ : algebraMap Ω Φ D ≠ 0` using `(map_ne_zero _).2 hD`. Apply `(mul_right_injective₀ hDΦ)` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[hseg, hseg]`. Establish `h1` using `hprodΦ (c₁ (some ())) (c₁ none)`.

Establish `h2` using `hprodΦ (c₂ (some ())) (c₂ none)`. Take the linear combination `T ^ 2 * (algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none))) * h1 - T ^ 2 * (algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none))) * h2`.
-/
theorem SegreFlagClosureBirational.proof : SegreFlagClosureBirational.Statement := by
  intro O _ _ _ ϖ _ Ω _ _ K _ _ ι _ y d _ N E _ _ B B' _ w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t _ hN c hc c₁ c₂ hc₂
  set i0 : Fin N := ⟨0, hN⟩ with hi0
  have hcΩ : segreVec y c ≠ 0 := by
    intro h
    apply hc
    rw [segreVec_algebraMap, h, map_zero]
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcΩ k (Finset.mem_univ k)
  have hpow : ∀ b : K → ℤ, ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 :=
    fun b => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)

  have hmem : ∏ k, y ⟨k, c k⟩ ^ x i0 k ∈ degLat O y (x i0) c := ⟨1, one_mem _, (one_mul _).symm⟩
  rw [← hF.flag.graded c hcΩ i0] at hmem
  obtain ⟨v, hv, hvj, hv0⟩ := hmem
  have hmem' : ∏ k, y ⟨k, c k⟩ ^ x' i0 k ∈ degLat O y (x' i0) c := ⟨1, one_mem _, (one_mul _).symm⟩
  rw [← hF.flag'.graded c hcΩ i0] at hmem'
  obtain ⟨v', hv', hvj', hv0'⟩ := hmem'
  have hv_eq : v = (∏ k, y ⟨k, c k⟩ ^ x i0 k) • w i0 := by
    rw [← hv0]; exact eq_repr_smul_basis_first w hN v hvj
  have hv'_eq : v' = (∏ k, y ⟨k, c k⟩ ^ x' i0 k) • w' i0 := by
    rw [← hv0']; exact eq_repr_smul_basis_first w' hN v' hvj'
  have hw' : w' i0 = w.repr (w' i0) i0 • w i0 :=
    eq_repr_smul_basis_first w hN (w' i0) fun j hj => hF.sameFlag i0 j hj
  set u : Ω := w.repr (w' i0) i0 with hudef
  have hu : u ≠ 0 := by
    intro h
    apply w'.ne_zero i0
    rw [hw', h, zero_smul]

  choose α hα hαeq using fun l => hφ.sections c hcΩ l v hv
  choose β hβ hβeq using fun l => hφ'.sections c hcΩ l v' hv'
  set D : Ω := (∏ k, y ⟨k, c k⟩ ^ x i0 k) * ((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u) with hDdef
  set G : Ω := (∏ k, y ⟨k, c k⟩ ^ a₀ k) * ∏ k, y ⟨k, c k⟩ ^ a₀' k with hGdef
  have hD : D ≠ 0 := mul_ne_zero (hpow _) (mul_ne_zero (hpow _) hu)
  have hprod : ∀ (l : Fin M) (m : Fin M'), D * (φ l (w i0) * φ' m (w i0)) = G * (α l * β m) := by
    intro l m
    have hA : (∏ k, y ⟨k, c k⟩ ^ x i0 k) * φ l (w i0) = α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k := by
      rw [← hαeq l, hv_eq, map_smul, smul_eq_mul]
    have hB : (∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0) =
        β m * ∏ k, y ⟨k, c k⟩ ^ a₀' k := by
      rw [← hβeq m, hv'_eq, hw', smul_smul, map_smul, smul_eq_mul]
    rw [hDdef, hGdef]
    linear_combination ((∏ k, y ⟨k, c k⟩ ^ x' i0 k) * u * φ' m (w i0)) * hA +
      (α l * ∏ k, y ⟨k, c k⟩ ^ a₀ k) * hB
  have hprodΦ : ∀ (l : Fin M) (m : Fin M'),
      algebraMap Ω Φ D * (algebraMap Ω Φ (φ l (w i0)) * algebraMap Ω Φ (φ' m (w i0))) =
        algebraMap Ω Φ G * (algebraMap Ω Φ (α l) * algebraMap Ω Φ (β m)) := by
    intro l m
    have := congrArg (algebraMap Ω Φ) (hprod l m)
    simpa only [map_mul] using this

  set T : Φ := ∑ i, t i * algebraMap Ω Φ (w.repr (e i) i0) with hT
  have hfc : ∀ j : Fin N, j ≠ i0 → flagCoord w e t 1 j = 0 := by
    intro j hj
    have : ¬ ((j : ℕ) < 1) := by
      intro h
      apply hj
      ext
      simp only [hi0]
      omega
    simp [flagCoord, this]
  have hfc0 : flagCoord w e t 1 i0 = T := by simp [flagCoord, hi0, hT]
  have hsome : ∀ l : Fin M, flagLinePt w e φ φ' t 1 ⟨some (), l⟩ = T * algebraMap Ω Φ (φ l (w i0)) := by
    intro l
    show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ l (w i)) = _
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]
  have hnone : ∀ l : Fin M', flagLinePt w e φ φ' t 1 ⟨none, l⟩ = T * algebraMap Ω Φ (φ' l (w i0)) := by
    intro l
    show ∑ i, flagCoord w e t 1 i * algebraMap Ω Φ (φ' l (w i)) = _
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hfc j hj, zero_mul]) (by simp), hfc0]
  have hseg : ∀ c' : ∀ o, lineBlocks M M' o, segreVec (flagLinePt w e φ φ' t 1) c' =
      (T * algebraMap Ω Φ (φ' (c' none) (w i0))) * (T * algebraMap Ω Φ (φ (c' (some ())) (w i0))) := by
    intro c'
    rw [segreVec, Fintype.prod_option, Fintype.prod_unique]
    exact congrArg₂ (· * ·) (hnone (c' none)) (hsome (c' (some ())))

  refine ⟨algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none)),
    mul_mem (algebraMap_mem_chartRing_segre y c (hα _)) (algebraMap_mem_chartRing_segre y c (hβ _)),
    algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none)),
    mul_mem (algebraMap_mem_chartRing_segre y c (hα _)) (algebraMap_mem_chartRing_segre y c (hβ _)), ?_, ?_⟩
  · intro h0
    apply hc₂
    have hDΦ : algebraMap Ω Φ D ≠ 0 := (map_ne_zero _).2 hD
    apply (mul_right_injective₀ hDΦ)
    simp only [mul_zero]
    rw [hseg]
    have h2 := hprodΦ (c₂ (some ())) (c₂ none)
    linear_combination T ^ 2 * h2 + T ^ 2 * algebraMap Ω Φ G * h0
  · have hDΦ : algebraMap Ω Φ D ≠ 0 := (map_ne_zero _).2 hD
    apply (mul_right_injective₀ hDΦ)
    simp only
    rw [hseg, hseg]
    have h1 := hprodΦ (c₁ (some ())) (c₁ none)
    have h2 := hprodΦ (c₂ (some ())) (c₂ none)
    linear_combination T ^ 2 * (algebraMap Ω Φ (α (c₂ (some ()))) * algebraMap Ω Φ (β (c₂ none))) * h1 -
      T ^ 2 * (algebraMap Ω Φ (α (c₁ (some ()))) * algebraMap Ω Φ (β (c₁ none))) * h2

end

end GroundTheory.Heights₂.Heights.NumbersDVR

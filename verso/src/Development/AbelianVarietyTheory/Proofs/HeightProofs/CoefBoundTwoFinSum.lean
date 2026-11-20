import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IterateOnePlusCasOfEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRankOneIsAvg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInnerApprox
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum

open GlobalTheory.LowTypeDetermined

section SobSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

/- English proof (translation)
Assemble the required witnesses or components as `⟨[], 0, by simp, fun w _ => by simp⟩`.
-/
theorem sobCont_zero_form : Sobolev₂ (lieSet ε) σ (0 : H →ₗ[ℂ] ℂ) :=
  ⟨[], 0, by simp, fun w _ => by simp⟩

/- English proof (translation)
Take `⟨S, C, hS, hC⟩` from `h`. Take `⟨S', C', hS', hC'⟩` from `h'`. Use `⟨S ++ S', |C| + |C'|, words_append hS hS', fun w hw => ?_⟩` and prove the remaining obligations. Establish `n1` using `sobNorm_nonneg σ S w`. Establish `n2` using `sobNorm_nonneg σ S' w`.

Establish `b1 : ‖ℓ w‖ ≤ C * sobNorm σ S w` using `hC w hw`. Establish `b2 : ‖ℓ' w‖ ≤ C' * sobNorm σ S' w` using `hC' w hw`. Use `show ‖ℓ w + ℓ' w‖ ≤ (|C| + |C'|) * sobNorm σ (S ++ S') w`. Rewrite using `[sobNorm_append]`. Establish `a1 : C * sobNorm σ S w ≤ |C| * sobNorm σ S w` using `mul_le_mul_of_nonneg_right (le_abs_self C) n1`.

Establish `a2 : C' * sobNorm σ S' w ≤ |C'| * sobNorm σ S' w` using `mul_le_mul_of_nonneg_right (le_abs_self C') n2`. Establish `a3` using `abs_nonneg C`. Establish `a4` using `abs_nonneg C'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sobCont_add_form {ℓ ℓ' : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) (h' : Sobolev₂ (lieSet ε) σ ℓ') :
    Sobolev₂ (lieSet ε) σ (ℓ + ℓ') := by
  obtain ⟨S, C, hS, hC⟩ := h
  obtain ⟨S', C', hS', hC'⟩ := h'
  refine ⟨S ++ S', |C| + |C'|, words_append hS hS', fun w hw => ?_⟩
  have n1 := sobNorm_nonneg σ S w
  have n2 := sobNorm_nonneg σ S' w
  have b1 : ‖ℓ w‖ ≤ C * sobNorm σ S w := hC w hw
  have b2 : ‖ℓ' w‖ ≤ C' * sobNorm σ S' w := hC' w hw
  show ‖ℓ w + ℓ' w‖ ≤ (|C| + |C'|) * sobNorm σ (S ++ S') w
  rw [sobNorm_append]
  have a1 : C * sobNorm σ S w ≤ |C| * sobNorm σ S w := mul_le_mul_of_nonneg_right (le_abs_self C) n1
  have a2 : C' * sobNorm σ S' w ≤ |C'| * sobNorm σ S' w := mul_le_mul_of_nonneg_right (le_abs_self C') n2
  have a3 := abs_nonneg C
  have a4 := abs_nonneg C'
  calc ‖ℓ w + ℓ' w‖ ≤ ‖ℓ w‖ + ‖ℓ' w‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

/- English proof (translation)
Take `⟨S, C, hS, hC⟩` from `h`. Use `⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩` and prove the remaining obligations. Establish `b : ‖ℓ w‖ ≤ C * sobNorm σ S w` using `hC w hw`. Use `show ‖c • ℓ w‖ ≤ ‖c‖ * C * sobNorm σ S w`. Rewrite using `[norm_smul, mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left b (norm_nonneg c)`.
-/
theorem sobCont_smul_form (c : ℂ) {ℓ : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) :
    Sobolev₂ (lieSet ε) σ (c • ℓ) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
  have b : ‖ℓ w‖ ≤ C * sobNorm σ S w := hC w hw
  show ‖c • ℓ w‖ ≤ ‖c‖ * C * sobNorm σ S w
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left b (norm_nonneg c)

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `using (sobCont_zero_form (ε := ε) (σ := σ) (H := H))`. Introduce `i s hi ih`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `sobCont_add_form (h i) ih`.
-/
theorem sobCont_sum_form {ι : Type} (s : Finset ι) (f : ι → H →ₗ[ℂ] ℂ) (h : ∀ i, Sobolev₂ (lieSet ε) σ (f i)) :
    Sobolev₂ (lieSet ε) σ (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (sobCont_zero_form (ε := ε) (σ := σ) (H := H))
  · intro i s hi ih
    rw [Finset.sum_insert hi]
    exact sobCont_add_form (h i) ih

end SobSum

/- English proof (translation)
Introduce `n ε H _ _ _ σ h hB N`. Establish `hσ` using `h.1`. Take `⟨a, c, ha0, hc0, haK, hcK, Z, C₀, hZ, hZU, hC₀, hA⟩` from `exists_rank_one_isAvg n ε H σ h`. Establish `ha : Sm ε σ a` using `h.2.2.1 a haK`. Establish `hc : Sm ε σ c` using `h.2.2.1 c hcK`.

Take `⟨S, C₁, hS, hC₁, hb2⟩` from `coefBound_two n ε H σ h hB a c ha ha0 hc hc0 N`. Take `⟨K₀, hK₀⟩` from `hZ.exists_bound_of_continuousOn (f := fun y : Mx n => (1 + hs y) ^ N) ((continuous_const.add continuous_hs).pow N).continuousOn`. Use `set K := max K₀ 0 with hKdef`. Establish `hK0 : 0 ≤ K` using `le_max_right _ _`. Establish `hK : ∀ y ∈ Z, (1 + hs y) ^ N ≤ K` using `fun y hy => ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK₀ y hy)).trans (le_max_left _ _)`.

Use `⟨S, C₁ * C₀ * K, hS, mul_nonneg (mul_nonneg hC₁ hC₀) hK0, ?_⟩` and prove the remaining obligations. Introduce `p ℓ x hℓ hx M hM hgr b w hb hw`. Set `γ : H → H → ℂ` to `fun b w => ∑ j, ⟪b, x j⟫_ℂ * ℓ j w`. Establish `h1 : ∀ b, Sm ε σ b → SobFun ε σ (γ b)`. Introduce `b _`.

Establish `hL` using `sobCont_sum_form (ε := ε) (σ := σ) Finset.univ (fun j => ⟪b, x j⟫_ℂ • ℓ j) (fun j => sobCont_smul_form _ (hℓ j))`. Establish `e : γ b = ⇑(∑ j, ⟪b, x j⟫_ℂ • ℓ j)`. Use function extensionality and compare the values at `w`. Simplify using `[γ, LinearMap.sum_apply]`. Rewrite using `[e]`.

Conclude with `sobFun_of_sobCont hL`. Establish `h2 : ∀ w, Sm ε σ w → SobFun ε σ (fun b => star (γ b w))`. Introduce `w _`. Establish `hL` using `sobCont_sum_form (ε := ε) (σ := σ) Finset.univ (fun j => star (ℓ j w) • (innerSL ℂ (x j) : H →ₗ[ℂ] ℂ)) (fun j => sobCont_smul_form _ (sobCont_inner _))`. Establish `e : (fun b => star (γ b w)) = ⇑(∑ j, star (ℓ j w) • (innerSL ℂ (x j) : H →ₗ[ℂ] ℂ))`.

Use function extensionality and compare the values at `b`. Simplify using `only [γ, star_sum, LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul', mul_comm, ← inner_conj_symm, starRingEnd_apply, star_star]`. Rewrite using `[e]`.

Conclude with `sobFun_of_sobCont hL`. Establish `h3 : ∀ g ∈ UJset ε, ∀ g' ∈ UJset ε, ‖γ (σ g' c) (σ g a)‖ ≤ (C₀ * K * M) * (1 + hs g) ^ N * (1 + hs g') ^ N`. Introduce `g hg g' hg'`. Establish `hg'i` using `inv_mem_UJ hg'`. Establish `hinv : g'⁻¹⁻¹ = g'` using `Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hg'))`.

Establish `e : γ (σ g' c) (σ g a) = ∑ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) ((fun v => ⟪c, v⟫_ℂ • a) (σ g'⁻¹ (x j)))`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hi` using `inner_sigma hσ hg'i c (x j)`. Rewrite `hi` using `[hinv]`. Simplify using `only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]`.

Rewrite using `[hi]`. Establish `P0 : 0 ≤ (1 + hs g) ^ N` using `pow_nonneg (by linarith [hs_nonneg g]) N`. Establish `P1 : 0 ≤ (1 + hs g') ^ N` using `pow_nonneg (by linarith [hs_nonneg g']) N`. Establish `hbd : ∀ y ∈ Z, ‖∑ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (σ y (σ g'⁻¹ (x j)))‖ ≤ M * K * (1 + hs g) ^ N * (1 + hs g') ^ N`. Introduce `y hy`.

Establish `hyU` using `hZU hy`. Establish `hm : g * y * g'⁻¹ ∈ UJset ε` using `mul_mem_UJ (mul_mem_UJ hg hyU) hg'i`. Establish `e2 : ∀ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (σ y (σ g'⁻¹ (x j))) = ℓ j (σ (g * y * g'⁻¹) (x j))` using `fun j => by`. Simplify using `only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]`. Rewrite using `[sigma_mul hσ (mul_mem_UJ hg hyU) hg'i, sigma_mul hσ hg hyU]`.

Simplify using `only [e2]`. Use `(hgr _ hm).trans ?_` and prove the remaining obligations. Establish `q1` using `one_add_hs_mul_le (g * y) g'⁻¹`. Establish `q2` using `one_add_hs_mul_le g y`. Rewrite `q1` using `[hs_inv hg']`.

Establish `hy0` using `hs_nonneg y`. Establish `hgg` using `hs_nonneg g`. Establish `hgg'` using `hs_nonneg g'`. Establish `q : 1 + hs (g * y * g'⁻¹) ≤ (1 + hs g) * (1 + hs y) * (1 + hs g')` using `q1.trans (mul_le_mul_of_nonneg_right q2 (by linarith))`. Establish `qN : (1 + hs (g * y * g'⁻¹)) ^ N ≤ (1 + hs g) ^ N * (1 + hs y) ^ N * (1 + hs g') ^ N`.

Rewrite using `[← mul_pow, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (by linarith [hs_nonneg (g * y * g'⁻¹)]) q N`. Establish `hKy` using `hK y hy`. Combine the equalities or inequalities in the displayed calculation. Establish `key` using `avgBd_sobCont n ε H σ h (fun v => ⟪c, v⟫_ℂ • a) Z C₀ hZ hZU hC₀ hA (Fin p) (fun j => ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (fun j => σ g'⁻¹ (x j)) (fun j => sobCont_translate hσ (hℓ j) hg) (fun j => (hx j).translate hσ hg'i) (fun j => sm_iff.2 ((smooth (Jm ε) σ).smul_mem _ (sm_iff.1 ha))) (M …`.

Rewrite using `[e]`. Conclude with `key.trans (le_of_eq (by ring))`. Establish `fin` using `hb2 γ h1 h2 (C₀ * K * M) (mul_nonneg (mul_nonneg hC₀ hK0) hM) h3 b w hb hw`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem coefBound_two_finSum : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → CoefBound ε σ → ∀ N : ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (p : ℕ) (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H), (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) → (∀ j, Sm ε σ (x j)) → ∀ M : ℝ, 0 ≤ M → (∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y (x j))‖ ≤ M * (1 + hs y) ^ N) → ∀ b w, Sm ε σ b → Sm ε σ w → ‖∑ j, ⟪b, x j⟫_ℂ * ℓ j w‖ ≤ C * M * sobNorm σ S b * sobNorm σ S w := by
  intro n ε H _ _ _ σ h hB N
  have hσ := h.1
  obtain ⟨a, c, ha0, hc0, haK, hcK, Z, C₀, hZ, hZU, hC₀, hA⟩ := exists_rank_one_isAvg n ε H σ h
  have ha : Sm ε σ a := h.2.2.1 a haK
  have hc : Sm ε σ c := h.2.2.1 c hcK
  obtain ⟨S, C₁, hS, hC₁, hb2⟩ := coefBound_two n ε H σ h hB a c ha ha0 hc hc0 N
  obtain ⟨K₀, hK₀⟩ := hZ.exists_bound_of_continuousOn
    (f := fun y : Mx n => (1 + hs y) ^ N) ((continuous_const.add continuous_hs).pow N).continuousOn
  set K := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ y ∈ Z, (1 + hs y) ^ N ≤ K := fun y hy =>
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK₀ y hy)).trans (le_max_left _ _)
  refine ⟨S, C₁ * C₀ * K, hS, mul_nonneg (mul_nonneg hC₁ hC₀) hK0, ?_⟩
  intro p ℓ x hℓ hx M hM hgr b w hb hw
  let γ : H → H → ℂ := fun b w => ∑ j, ⟪b, x j⟫_ℂ * ℓ j w
  have h1 : ∀ b, Sm ε σ b → SobFun ε σ (γ b) := by
    intro b _
    have hL := sobCont_sum_form (ε := ε) (σ := σ) Finset.univ (fun j => ⟪b, x j⟫_ℂ • ℓ j)
      (fun j => sobCont_smul_form _ (hℓ j))
    have e : γ b = ⇑(∑ j, ⟪b, x j⟫_ℂ • ℓ j) := by
      funext w
      simp [γ, LinearMap.sum_apply]
    rw [e]
    exact sobFun_of_sobCont hL
  have h2 : ∀ w, Sm ε σ w → SobFun ε σ (fun b => star (γ b w)) := by
    intro w _
    have hL := sobCont_sum_form (ε := ε) (σ := σ) Finset.univ
      (fun j => star (ℓ j w) • (innerSL ℂ (x j) : H →ₗ[ℂ] ℂ)) (fun j => sobCont_smul_form _ (sobCont_inner _))
    have e : (fun b => star (γ b w)) = ⇑(∑ j, star (ℓ j w) • (innerSL ℂ (x j) : H →ₗ[ℂ] ℂ)) := by
      funext b
      simp only [γ, star_sum, LinearMap.sum_apply, LinearMap.smul_apply,
        ContinuousLinearMap.coe_coe, innerSL_apply_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul', mul_comm, ← inner_conj_symm, starRingEnd_apply, star_star]
    rw [e]
    exact sobFun_of_sobCont hL
  have h3 : ∀ g ∈ UJset ε, ∀ g' ∈ UJset ε,
      ‖γ (σ g' c) (σ g a)‖ ≤ (C₀ * K * M) * (1 + hs g) ^ N * (1 + hs g') ^ N := by
    intro g hg g' hg'
    have hg'i := inv_mem_UJ hg'
    have hinv : g'⁻¹⁻¹ = g' :=
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hg'))
    have e : γ (σ g' c) (σ g a) =
        ∑ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) ((fun v => ⟪c, v⟫_ℂ • a) (σ g'⁻¹ (x j))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hi := inner_sigma hσ hg'i c (x j)
      rw [hinv] at hi
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]
      rw [hi]
    have P0 : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) N
    have P1 : 0 ≤ (1 + hs g') ^ N := pow_nonneg (by linarith [hs_nonneg g']) N
    have hbd : ∀ y ∈ Z, ‖∑ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (σ y (σ g'⁻¹ (x j)))‖ ≤
        M * K * (1 + hs g) ^ N * (1 + hs g') ^ N := by
      intro y hy
      have hyU := hZU hy
      have hm : g * y * g'⁻¹ ∈ UJset ε := mul_mem_UJ (mul_mem_UJ hg hyU) hg'i
      have e2 : ∀ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (σ y (σ g'⁻¹ (x j))) = ℓ j (σ (g * y * g'⁻¹) (x j)) := fun j => by
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        rw [sigma_mul hσ (mul_mem_UJ hg hyU) hg'i, sigma_mul hσ hg hyU]
      simp only [e2]
      refine (hgr _ hm).trans ?_
      have q1 := one_add_hs_mul_le (g * y) g'⁻¹
      have q2 := one_add_hs_mul_le g y
      rw [hs_inv hg'] at q1
      have hy0 := hs_nonneg y
      have hgg := hs_nonneg g
      have hgg' := hs_nonneg g'
      have q : 1 + hs (g * y * g'⁻¹) ≤ (1 + hs g) * (1 + hs y) * (1 + hs g') :=
        q1.trans (mul_le_mul_of_nonneg_right q2 (by linarith))
      have qN : (1 + hs (g * y * g'⁻¹)) ^ N ≤ (1 + hs g) ^ N * (1 + hs y) ^ N * (1 + hs g') ^ N := by
        rw [← mul_pow, ← mul_pow]
        exact pow_le_pow_left₀ (by linarith [hs_nonneg (g * y * g'⁻¹)]) q N
      have hKy := hK y hy
      calc M * (1 + hs (g * y * g'⁻¹)) ^ N ≤ M * ((1 + hs g) ^ N * (1 + hs y) ^ N * (1 + hs g') ^ N) :=
            mul_le_mul_of_nonneg_left qN hM
        _ ≤ M * ((1 + hs g) ^ N * K * (1 + hs g') ^ N) := by gcongr
        _ = _ := by ring
    have key := avgBd_sobCont n ε H σ h (fun v => ⟪c, v⟫_ℂ • a) Z C₀ hZ hZU hC₀ hA (Fin p)
      (fun j => ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (fun j => σ g'⁻¹ (x j))
      (fun j => sobCont_translate hσ (hℓ j) hg) (fun j => (hx j).translate hσ hg'i)
      (fun j => sm_iff.2 ((smooth (Jm ε) σ).smul_mem _ (sm_iff.1 ha)))
      (M * K * (1 + hs g) ^ N * (1 + hs g') ^ N)
      (mul_nonneg (mul_nonneg (mul_nonneg hM hK0) P0) P1) hbd
    rw [e]
    exact key.trans (le_of_eq (by ring))
  have fin := hb2 γ h1 h2 (C₀ * K * M) (mul_nonneg (mul_nonneg hC₀ hK0) hM) h3 b w hb hw
  calc ‖∑ j, ⟪b, x j⟫_ℂ * ℓ j w‖ = ‖γ b w‖ := rfl
    _ ≤ _ := fin
    _ = _ := by ring

end GlobalTheory.TypeSum

end

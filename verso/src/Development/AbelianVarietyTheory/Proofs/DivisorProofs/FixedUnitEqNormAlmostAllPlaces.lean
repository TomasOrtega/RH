import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmallB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisHenselExistsUniqueSqrtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedNormModMaxIdealAdicTensorStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
noncomputable section

namespace GlobalTheory.LocNorm

/- English proof (translation)
Introduce `L _ _ c κ bL θ`. Use `haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL`. Establish `ev` using `fun (q : ℚ) => rat_mem_adicCompletionIntegers_eventually q`. Establish `hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ, algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (bL t.1 * bL t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ` using `Filter.eventually_all.2 fun t => ev _`. Establish `hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ, algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (c (bL t.1)) t.2) ∈ v.adicCompletionIntegers ℚ` using `Filter.eventually_all.2 fun t => ev _`.

Establish `hl : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : Fin 3 × κ, algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (![1, θ, θ⁻¹] t.1) t.2) ∈ v.adicCompletionIntegers ℚ` using `Filter.eventually_all.2 fun t => ev _`. Establish `hfin` using `Filter.eventually_cofinite.1 (((hc.and hs).and hl).and (ev (1 / 2)))`. Use `⟨hfin.toFinset, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not]`. Take `⟨⟨⟨hcv, hsv⟩, hlv⟩, h2v⟩` from `hv`.

Establish `hmem : ∀ a : v.adicCompletion ℚ, a ∈ v.adicCompletionIntegers ℚ ↔ Valued.v a ≤ 1` using `fun a => HeightOneSpectrum.mem_adicCompletionIntegers ..`. Establish `hint : ∀ ℓ : L, (∀ k, algebraMap ℚ (v.adicCompletion ℚ) (bL.repr ℓ k) ∈ v.adicCompletionIntegers ℚ) → IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ℓ)`. Introduce `ℓ hℓ k`. Rewrite using `[repr_tmul_apply, one_mul]`. Conclude with `hℓ k`.

Use `⟨?_, ?_, ?_, ?_, ?_, ?_, hint θ (fun k => hlv (1, k)), hint θ⁻¹ (fun k => hlv (2, k))⟩` and prove the remaining obligations. Establish `hle : Valued.v (2 : v.adicCompletion ℚ) ≤ 1`. Establish `h` using `(v.adicCompletionIntegers ℚ).add_mem 1 1 (one_mem _) (one_mem _)`. Rewrite `h` using `[one_add_one_eq_two]`. Conclude with `(hmem _).1 h`.

Establish `hle' : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) ≤ 1` using `(hmem _).1 h2v`. Establish `hprod : Valued.v (2 : v.adicCompletion ℚ) * Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) = 1`. Rewrite using `[← map_mul, show (2 : v.adicCompletion ℚ) * algebraMap ℚ (v.adicCompletion ℚ) (1 / 2) = 1 by`. Rewrite using `[show (2 : v.adicCompletion ℚ) = algebraMap ℚ _ 2 from (map_ofNat _ 2).symm, ← map_mul]`. Use the proof step `norm_num, map_one]`.

Use `le_antisymm hle ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Algebra.TensorProduct.one_def]`. Conclude with `hint 1 (fun k => hlv (0, k))`. Introduce `y z hy hz k`.

Rewrite using `[eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Finsupp.finset_sum_apply]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]`.

Conclude with `mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))`. Introduce `y z hy hz k`. Rewrite using `[eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]`. Use `Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, Finsupp.finset_sum_apply]`.

Use `Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply, map_mul, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_mul' (mul_le_mul' ((hmem _).1 (hy i)) le_rfl) ((hmem _).1 (hcv (i, j, k)))) (by simpa using hz j)`. Introduce `y hy k`. Rewrite using `[eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finset_sum_apply]`.

Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply]`. Conclude with `mul_mem (hy i) (hsv (i, k))`. Introduce `y hy k`. Rewrite using `[eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finset_sum_apply]`.

Use `Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_mul' le_rfl ((hmem _).1 (hsv (i, k)))) (by simpa using hy i)`.
-/
theorem good_eventually : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L) (κ : Type) (bL : Module.Basis κ ℚ L) (θ : L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      Valued.v (2 : v.adicCompletion ℚ) = 1 ∧ IsIntB v bL 1 ∧
      (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) ∧
      (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) ∧
      (∀ x, IsIntB v bL x → IsIntB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) ∧
      (∀ x, IsSmallB v bL x → IsSmallB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) ∧
      IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] θ) ∧ IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] θ⁻¹) := by
  intro L _ _ c κ bL θ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have ev := fun (q : ℚ) => rat_mem_adicCompletionIntegers_eventually q
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (bL t.1 * bL t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (c (bL t.1)) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hl : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : Fin 3 × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (![1, θ, θ⁻¹] t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hfin := Filter.eventually_cofinite.1 (((hc.and hs).and hl).and (ev (1 / 2)))
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨⟨⟨hcv, hsv⟩, hlv⟩, h2v⟩ := hv
  have hmem : ∀ a : v.adicCompletion ℚ, a ∈ v.adicCompletionIntegers ℚ ↔ Valued.v a ≤ 1 := fun a =>
    HeightOneSpectrum.mem_adicCompletionIntegers ..
  have hint : ∀ ℓ : L, (∀ k, algebraMap ℚ (v.adicCompletion ℚ) (bL.repr ℓ k) ∈ v.adicCompletionIntegers ℚ) →
      IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ℓ) := by
    intro ℓ hℓ k
    rw [repr_tmul_apply, one_mul]; exact hℓ k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hint θ (fun k => hlv (1, k)), hint θ⁻¹ (fun k => hlv (2, k))⟩
  · have hle : Valued.v (2 : v.adicCompletion ℚ) ≤ 1 := by
      have h := (v.adicCompletionIntegers ℚ).add_mem 1 1 (one_mem _) (one_mem _)
      rw [one_add_one_eq_two] at h
      exact (hmem _).1 h
    have hle' : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) ≤ 1 := (hmem _).1 h2v
    have hprod : Valued.v (2 : v.adicCompletion ℚ) * Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) = 1 := by
      rw [← map_mul, show (2 : v.adicCompletion ℚ) * algebraMap ℚ (v.adicCompletion ℚ) (1 / 2) = 1 by
        rw [show (2 : v.adicCompletion ℚ) = algebraMap ℚ _ 2 from (map_ofNat _ 2).symm, ← map_mul]; norm_num, map_one]
    refine le_antisymm hle ?_
    calc (1 : _) = _ := hprod.symm
      _ ≤ Valued.v (2 : v.adicCompletion ℚ) * 1 := mul_le_mul' le_rfl hle'
      _ = _ := mul_one _
  · rw [Algebra.TensorProduct.one_def]; exact hint 1 (fun k => hlv (0, k))
  · intro y z hy hz k
    rw [eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · intro y z hy hz k
    rw [eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [map_sum, Finsupp.finset_sum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_mul' (mul_le_mul' ((hmem _).1 (hy i)) le_rfl) ((hmem _).1 (hcv (i, j, k))))
      (by simpa using hz j)
  · intro y hy k
    rw [eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply]
    exact mul_mem (hy i) (hsv (i, k))
  · intro y hy k
    rw [eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finset_sum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply, map_mul]
    exact lt_of_le_of_lt (mul_le_mul' le_rfl ((hmem _).1 (hsv (i, k)))) (by simpa using hy i)

/- English proof (translation)
Introduce `L _ _ c hc hne κ bL`. Take `⟨x, hx⟩` from `hne`. Use `set θ : L := x - c x with hθdef`. Establish `hθ : θ ≠ 0` using `sub_ne_zero.mpr (Ne.symm hx)`. Establish `hcθ : c θ = -θ` using `by simp [θ, hc]`.

Take `⟨S, hS⟩` from `good_eventually L c κ bL θ`. Use `⟨S, fun v hv e hee hei hei' => ?_⟩` and prove the remaining obligations. Take `⟨h2, h1, hmul, hmulS, hσI, hσS, hθI, hθI'⟩` from `hS v hv`. Use `set σ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c with hσdef`. Establish `hσσ : ∀ a, σ (σ a) = a`.

Introduce `a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r l => simp [σ, hc]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Establish `hσinv : ∀ g : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, σ ↑g = ↑g → σ ↑g⁻¹ = ↑g⁻¹`. Introduce `g hg`. Combine the equalities or inequalities in the displayed calculation. Set `θu : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ` to `⟨1 ⊗ₜ θ, 1 ⊗ₜ θ⁻¹, by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hθ, Algebra.TensorProduct.one_def], by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel₀ hθ, Algebra.TensorProduct.one_def]⟩`. Establish `hσθ : σ ↑θu = -↑θu` using `by simp [θu, σ, hcθ, TensorProduct.tmul_neg]`.

Take `⟨z, hzI, hzS⟩` from `GlobalTheory.T.exists_twistedNorm_mod_maxIdeal_adicTensor v L c hc κ bL h2 h1 hmul hmulS hσI θu hθI hθI' hσθ e hee hei hei'`. Use `set w := z * σ z with hwdef`. Establish `hwσ : σ w = w` using `by simp only [w, map_mul, hσσ]; ring`. Use `set u : v.adicCompletion ℚ ⊗[ℚ] L := ↑e⁻¹ * w with hudef`. Establish `huI : IsIntB v bL u` using `hmul _ _ hei' (hmul _ _ hzI (hσI _ hzI))`.

Establish `huS : IsSmallB v bL (u - 1)`. Establish `: u - 1 = ↑e⁻¹ * (w - ↑e)` using `by simp [u, mul_sub]`. Rewrite using `[this]`. Conclude with `hmulS _ _ hei' hzS`. Take `⟨f, hfI, hfI', hf2, hfS, huniq⟩` from `GlobalTheory.T.adicIntegralTensorBasis_hensel_exists_unique_sqrt v L κ bL h2 h1 hmul hmulS u huI huS`.

Establish `hσu : σ u = u` using `by simp only [u, map_mul, hσinv e hee, hwσ]`. Establish `hσf : σ ↑f = ↑f`. Use `huniq _ (hσI _ hfI) (by rw [← map_pow, hf2, hσu]) ?_` and prove the remaining obligations. Use `hσS _ hfS` as an intermediate fact. Simplify using `using this`.

Establish `hw : w = ↑e * ↑f ^ 2` using `by rw [hf2]; simp [u]`. Establish `hzU : IsUnit z` using `isUnit_of_mul_isUnit_left (x := z) (y := σ z) (by rw [← hwdef, hw]; exact e.isUnit.mul (f.isUnit.pow 2))`. Take `⟨zu, hzu⟩` from `hzU`. Use `⟨zu * f⁻¹, ?_⟩` and prove the remaining obligations. Establish `hf'` using `hσinv f hσf`.

Simplify using `only [Units.val_mul, map_mul, hf', hzu]`. Establish `: (↑e : v.adicCompletion ℚ ⊗[ℚ] L) = w * ↑f⁻¹ * ↑f⁻¹`. Rewrite using `[hw]`. Simplify using `[pow_two, mul_assoc]`. Rewrite using `[this, hwdef]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem unit_fixed_is_norm : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) → (∃ x, c x ≠ x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e → IsIntB v bL ↑e →
        IsIntB v bL ↑e⁻¹ → ∃ y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
          (e : v.adicCompletion ℚ ⊗[ℚ] L) = ↑y * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑y := by
  intro L _ _ c hc hne κ bL
  obtain ⟨x, hx⟩ := hne
  set θ : L := x - c x with hθdef
  have hθ : θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcθ : c θ = -θ := by simp [θ, hc]
  obtain ⟨S, hS⟩ := good_eventually L c κ bL θ
  refine ⟨S, fun v hv e hee hei hei' => ?_⟩
  obtain ⟨h2, h1, hmul, hmulS, hσI, hσS, hθI, hθI'⟩ := hS v hv
  set σ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c with hσdef
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r l => simp [σ, hc]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hσinv : ∀ g : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, σ ↑g = ↑g → σ ↑g⁻¹ = ↑g⁻¹ := by
    intro g hg
    calc σ ↑g⁻¹ = σ ↑g⁻¹ * (↑g * ↑g⁻¹) := by simp
      _ = σ (↑g⁻¹ * ↑g) * ↑g⁻¹ := by rw [map_mul, hg]; ring
      _ = ↑g⁻¹ := by simp
  let θu : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ :=
    ⟨1 ⊗ₜ θ, 1 ⊗ₜ θ⁻¹,
      by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hθ, Algebra.TensorProduct.one_def],
      by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel₀ hθ, Algebra.TensorProduct.one_def]⟩
  have hσθ : σ ↑θu = -↑θu := by simp [θu, σ, hcθ, TensorProduct.tmul_neg]
  obtain ⟨z, hzI, hzS⟩ := GlobalTheory.T.exists_twistedNorm_mod_maxIdeal_adicTensor v L c hc κ bL h2 h1 hmul hmulS hσI θu hθI hθI' hσθ e hee hei hei'
  set w := z * σ z with hwdef
  have hwσ : σ w = w := by simp only [w, map_mul, hσσ]; ring
  set u : v.adicCompletion ℚ ⊗[ℚ] L := ↑e⁻¹ * w with hudef
  have huI : IsIntB v bL u := hmul _ _ hei' (hmul _ _ hzI (hσI _ hzI))
  have huS : IsSmallB v bL (u - 1) := by
    have : u - 1 = ↑e⁻¹ * (w - ↑e) := by simp [u, mul_sub]
    rw [this]; exact hmulS _ _ hei' hzS
  obtain ⟨f, hfI, hfI', hf2, hfS, huniq⟩ := GlobalTheory.T.adicIntegralTensorBasis_hensel_exists_unique_sqrt v L κ bL h2 h1 hmul hmulS u huI huS
  have hσu : σ u = u := by simp only [u, map_mul, hσinv e hee, hwσ]
  have hσf : σ ↑f = ↑f := by
    refine huniq _ (hσI _ hfI) (by rw [← map_pow, hf2, hσu]) ?_
    have := hσS _ hfS
    simpa using this
  have hw : w = ↑e * ↑f ^ 2 := by rw [hf2]; simp [u]
  have hzU : IsUnit z := isUnit_of_mul_isUnit_left (x := z) (y := σ z)
    (by rw [← hwdef, hw]; exact e.isUnit.mul (f.isUnit.pow 2))
  obtain ⟨zu, hzu⟩ := hzU
  refine ⟨zu * f⁻¹, ?_⟩
  have hf' := hσinv f hσf
  simp only [Units.val_mul, map_mul, hf', hzu]
  have : (↑e : v.adicCompletion ℚ ⊗[ℚ] L) = w * ↑f⁻¹ * ↑f⁻¹ := by
    rw [hw]; simp [pow_two, mul_assoc]
  rw [this, hwdef]; ring

end GlobalTheory.LocNorm

import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal

open Complex Filter Topology

namespace GlobalTheory.ArtinKernel

/- English proof (translation)
Use `choose k hk using hcov`. Use `⟨fun z => G (k z) z, fun z => ?_, fun j z hz => hc _ _ _ (hk z) hz⟩` and prove the remaining obligations. Establish `hU : D (k z) ∈ 𝓝 z` using `(hD (k z)).mem_nhds (hk z)`. Establish `hev : (fun w => G (k w) w) =ᶠ[𝓝 z] G (k z)` using `by filter_upwards [hU] with w hw`. Conclude with `hc _ _ _ (hk w) hw`.

Conclude with `((hG (k z)).differentiableAt hU).congr_of_eventuallyEq hev`.
-/
theorem exists_glue {g : ℕ} {J : Type*} (D : J → Set (Fin g → ℂ))
    (G : J → (Fin g → ℂ) → ℂ) (hD : ∀ j, IsOpen (D j)) (hcov : ∀ z, ∃ j, z ∈ D j)
    (hG : ∀ j, DifferentiableOn ℂ (G j) (D j))
    (hc : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z) :
    ∃ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F ∧ ∀ j z, z ∈ D j → F z = G j z := by
  choose k hk using hcov
  refine ⟨fun z => G (k z) z, fun z => ?_, fun j z hz => hc _ _ _ (hk z) hz⟩
  have hU : D (k z) ∈ 𝓝 z := (hD (k z)).mem_nhds (hk z)
  have hev : (fun w => G (k w) w) =ᶠ[𝓝 z] G (k z) := by
    filter_upwards [hU] with w hw
    exact hc _ _ _ (hk w) hw
  exact ((hG (k z)).differentiableAt hU).congr_of_eventuallyEq hev

/- English proof (translation)
The claim follows from `differentiableOn_univ.mp (GlobalTheory.SCV.differentiableOn_fderiv isOpen_univ hF.differentiableOn)`.
-/
theorem differentiable_fderiv {g : ℕ} {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (fderiv ℂ F) := differentiableOn_univ.mp (GlobalTheory.SCV.differentiableOn_fderiv isOpen_univ hF.differentiableOn)

/- English proof (translation)
Establish `hD : Differentiable ℂ (fderiv ℂ F)` using `differentiable_fderiv hF`. Establish `hper : ∀ z, ∀ l ∈ S, fderiv ℂ F (z + l) = fderiv ℂ F z`. Introduce `z l hl`. Establish `h1 : (fun w => F (w + l)) = fun w => F w + b ⟨l, hl⟩` using `funext fun w => hb ⟨l, hl⟩ w`. Rewrite using `[← fderiv_comp_add_right (f := F) l, h1, fderiv_add_const]`.

Establish `hconst : ∀ z, fderiv ℂ F z = fderiv ℂ F 0` using `fun z => GlobalTheory.entire_apply_eq_of_periodic_of_span_real hD hS hper z 0`. Use `set L := fderiv ℂ F 0 with hL`. Establish `hlin : ∀ z, F z = F 0 + L z`. Introduce `z`. Establish `hd : Differentiable ℂ (fun w => F w - L w)` using `hF.sub L.differentiable`.

Establish `h0 : ∀ w, fderiv ℂ (fun w => F w - L w) w = 0`. Introduce `w`. Rewrite using `[fderiv_fun_sub (hF w) L.differentiableAt, L.fderiv, hconst w, sub_self]`. Use `is_const_of_fderiv_eq_zero hd h0 z 0` as an intermediate fact. Rewrite `this` using `[map_zero, sub_zero]`.

Take the linear combination `this`. Use `⟨L.toLinearMap, fun l => ?_⟩` and prove the remaining obligations. Use `hb l 0` as an intermediate fact. Rewrite `this` using `[zero_add, hlin l.1]`. Simplify using `only [ContinuousLinearMap.coe_coe]`.

Take the linear combination `-this`.
-/
theorem exists_linear_of_add_period {g : ℕ} {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {S : Set (Fin g → ℂ)} (hS : Submodule.span ℝ S = ⊤) (b : S → ℂ)
    (hb : ∀ (l : S) z, F (z + l) = F z + b l) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : S, b l = lam l := by
  have hD : Differentiable ℂ (fderiv ℂ F) := differentiable_fderiv hF
  have hper : ∀ z, ∀ l ∈ S, fderiv ℂ F (z + l) = fderiv ℂ F z := by
    intro z l hl
    have h1 : (fun w => F (w + l)) = fun w => F w + b ⟨l, hl⟩ := funext fun w => hb ⟨l, hl⟩ w
    rw [← fderiv_comp_add_right (f := F) l, h1, fderiv_add_const]
  have hconst : ∀ z, fderiv ℂ F z = fderiv ℂ F 0 := fun z =>
    GlobalTheory.entire_apply_eq_of_periodic_of_span_real hD hS hper z 0
  set L := fderiv ℂ F 0 with hL
  have hlin : ∀ z, F z = F 0 + L z := by
    intro z
    have hd : Differentiable ℂ (fun w => F w - L w) := hF.sub L.differentiable
    have h0 : ∀ w, fderiv ℂ (fun w => F w - L w) w = 0 := by
      intro w
      rw [fderiv_fun_sub (hF w) L.differentiableAt, L.fderiv, hconst w, sub_self]
    have := is_const_of_fderiv_eq_zero hd h0 z 0
    rw [map_zero, sub_zero] at this
    linear_combination this
  refine ⟨L.toLinearMap, fun l => ?_⟩
  have := hb l 0
  rw [zero_add, hlin l.1] at this
  simp only [ContinuousLinearMap.coe_coe]
  linear_combination -this

/- English proof (translation)
Establish `hb0 : ∀ l : S, b l ≠ 0`. Introduce `l hl`. Use `hb l 0` as an intermediate fact. Rewrite `this` using `[hl, zero_mul, zero_add]`. Conclude with `h0 _ this`.

Establish `hdF : ∀ (l : S) z, fderiv ℂ F (z + l) = b l • fderiv ℂ F z`. Introduce `l z`. Establish `h1 : (fun w => F (w + l)) = fun w => b l * F w` using `funext fun w => hb l w`. Rewrite using `[← fderiv_comp_add_right (f := F) (l : Fin g → ℂ), h1, fderiv_const_mul (hF z)]`. Use `set H : (Fin g → ℂ) → ((Fin g → ℂ) →L[ℂ] ℂ) := fun z => (F z)⁻¹ • fderiv ℂ F z with hH`.

Establish `hHd : Differentiable ℂ H` using `(hF.inv h0).smul (differentiable_fderiv hF)`. Establish `hper : ∀ z, ∀ l ∈ S, H (z + l) = H z`. Introduce `z l hl`. Simplify using `only [hH]`. Rewrite using `[hb ⟨l, hl⟩ z, hdF ⟨l, hl⟩ z, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (hb0 _), mul_one]`.

Establish `hconst : ∀ z, H z = H 0` using `fun z => GlobalTheory.entire_apply_eq_of_periodic_of_span_real hHd hS hper z 0`. Use `set L := H 0 with hL`. Establish `hDF : ∀ w, fderiv ℂ F w = F w • L`. Introduce `w`. Rewrite using `[← hconst w, hH, smul_smul, mul_inv_cancel₀ (h0 w), one_smul]`.

Establish `hK : ∀ w, fderiv ℂ (fun z => F z * cexp (-L z)) w = 0`. Introduce `w`. Establish `h2 : HasFDerivAt (fun z => F z * cexp (-L z)) (F w • (cexp (-L w) • -L) + cexp (-L w) • fderiv ℂ F w) w` using `(hF w).hasFDerivAt.mul L.hasFDerivAt.neg.cexp`. Rewrite using `[h2.fderiv, hDF w]`. Use extensionality with `v`.

Simplify using `only [add_apply, smul_apply, neg_apply, zero_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hKd : Differentiable ℂ (fun z => F z * cexp (-L z))` using `hF.mul (L.differentiable.neg.cexp)`. Use `⟨L.toLinearMap, fun l => ?_⟩` and prove the remaining obligations. Establish `e1` using `is_const_of_fderiv_eq_zero hKd hK (l : Fin g → ℂ) 0`.

Establish `e2` using `hb l 0`. Rewrite `e2` using `[zero_add]`. Rewrite `e1` using `[e2, map_zero, neg_zero, Complex.exp_zero, mul_one, mul_right_comm]`. Establish `e3 : b l * cexp (-L l) = 1`. Use `mul_right_cancel₀ (h0 0) (e1.trans (one_mul _).symm)` as an intermediate fact.

Conclude with `this`. Rewrite `e3` using `[Complex.exp_neg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)]`. Simplify `e3` using `only [ContinuousLinearMap.coe_coe]`.
-/
theorem exists_linear_of_mul_period {g : ℕ} {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (h0 : ∀ z, F z ≠ 0) {S : Set (Fin g → ℂ)} (hS : Submodule.span ℝ S = ⊤) (b : S → ℂ)
    (hb : ∀ (l : S) z, F (z + l) = b l * F z) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : S, b l = cexp (lam l) := by
  have hb0 : ∀ l : S, b l ≠ 0 := by
    intro l hl
    have := hb l 0
    rw [hl, zero_mul, zero_add] at this
    exact h0 _ this
  have hdF : ∀ (l : S) z, fderiv ℂ F (z + l) = b l • fderiv ℂ F z := by
    intro l z
    have h1 : (fun w => F (w + l)) = fun w => b l * F w := funext fun w => hb l w
    rw [← fderiv_comp_add_right (f := F) (l : Fin g → ℂ), h1, fderiv_const_mul (hF z)]
  set H : (Fin g → ℂ) → ((Fin g → ℂ) →L[ℂ] ℂ) := fun z => (F z)⁻¹ • fderiv ℂ F z with hH
  have hHd : Differentiable ℂ H := (hF.inv h0).smul (differentiable_fderiv hF)
  have hper : ∀ z, ∀ l ∈ S, H (z + l) = H z := by
    intro z l hl
    simp only [hH]
    rw [hb ⟨l, hl⟩ z, hdF ⟨l, hl⟩ z, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (hb0 _), mul_one]
  have hconst : ∀ z, H z = H 0 := fun z =>
    GlobalTheory.entire_apply_eq_of_periodic_of_span_real hHd hS hper z 0
  set L := H 0 with hL
  have hDF : ∀ w, fderiv ℂ F w = F w • L := by
    intro w
    rw [← hconst w, hH, smul_smul, mul_inv_cancel₀ (h0 w), one_smul]
  have hK : ∀ w, fderiv ℂ (fun z => F z * cexp (-L z)) w = 0 := by
    intro w
    have h2 : HasFDerivAt (fun z => F z * cexp (-L z))
        (F w • (cexp (-L w) • -L) + cexp (-L w) • fderiv ℂ F w) w :=
      (hF w).hasFDerivAt.mul L.hasFDerivAt.neg.cexp
    rw [h2.fderiv, hDF w]
    ext v
    simp only [add_apply, smul_apply, neg_apply, zero_apply, smul_eq_mul]
    ring
  have hKd : Differentiable ℂ (fun z => F z * cexp (-L z)) :=
    hF.mul (L.differentiable.neg.cexp)
  refine ⟨L.toLinearMap, fun l => ?_⟩
  have e1 := is_const_of_fderiv_eq_zero hKd hK (l : Fin g → ℂ) 0
  have e2 := hb l 0
  rw [zero_add] at e2
  rw [e2, map_zero, neg_zero, Complex.exp_zero, mul_one, mul_right_comm] at e1
  have e3 : b l * cexp (-L l) = 1 := by
    have := mul_right_cancel₀ (h0 0) (e1.trans (one_mul _).symm)
    exact this
  rw [Complex.exp_neg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at e3
  simpa only [ContinuousLinearMap.coe_coe] using e3

section Artin

variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]

/- English proof (translation)
Establish `hsurj` using `(IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := R ⧸ IsLocalRing.maximalIdeal R))`. Set `e : ℂ ≃ₐ[ℂ] R ⧸ IsLocalRing.maximalIdeal R` to `AlgEquiv.ofBijective (Algebra.ofId ℂ _) hsurj`. Use `⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ _), fun r hr => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `h1 : e.symm (Ideal.Quotient.mk _ r) = 0` using `hr`.

Establish `h2` using `congrArg e h1`. Rewrite `h2` using `[AlgEquiv.apply_symm_apply, map_zero]`. Then use the resulting hypothesis.
-/
theorem exists_residue : ∃ ρ : R →ₐ[ℂ] ℂ, ∀ r, ρ r = 0 → r ∈ IsLocalRing.maximalIdeal R := by
  have hsurj := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := ℂ) (K := R ⧸ IsLocalRing.maximalIdeal R))
  let e : ℂ ≃ₐ[ℂ] R ⧸ IsLocalRing.maximalIdeal R := AlgEquiv.ofBijective (Algebra.ofId ℂ _) hsurj
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ _), fun r hr => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : e.symm (Ideal.Quotient.mk _ r) = 0 := hr
  have h2 := congrArg e h1
  rwa [AlgEquiv.apply_symm_apply, map_zero] at h2

/- English proof (translation)
Establish `: IsArtinianRing R` using `IsArtinianRing.of_finite ℂ R`. Use `⟨fun p q => PrimeSpectrum.ext ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime p.asIdeal), IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime q.asIdeal)]`.
-/
theorem subsingleton_primeSpectrum : Subsingleton (PrimeSpectrum R) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite ℂ R
  refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
  rw [IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime p.asIdeal),
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime q.asIdeal)]

/- English proof (translation)
Use `set m := IsLocalRing.maximalIdeal R`. Use `set N : Submodule ℂ R := Submodule.span ℂ {x | ∃ r ∈ m, ∃ i, x = r * δ i} with hN`. Establish `hex : ∃ i, δ i ∉ N` using `by by_contra! hall set J : Ideal R := Ideal.span (Set.range δ) with hJ`. Establish `hNJ : ∀ x ∈ N, x ∈ m • J`. Introduce `x hx`.

Use `Submodule.span_induction (p := fun x _ => x ∈ m • J) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨r, hr, i, rfl⟩`. Conclude with `Submodule.smul_mem_smul hr (Ideal.subset_span ⟨i, rfl⟩)`. Conclude with `zero_mem _`. Introduce `x y _ _ hx hy`.

Conclude with `add_mem hx hy`. Introduce `c x _ hx`. Conclude with `Submodule.smul_of_tower_mem _ c hx`. Establish `hle : J ≤ m • J`. Rewrite using `[hJ, Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hNJ _ (hall i)`. Establish `: IsArtinianRing R` using `IsArtinianRing.of_finite ℂ R`. Establish `hJ0 : J = ⊥` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m J (IsNoetherian.noetherian J) hle (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)`. Take `⟨i, hi⟩` from `hδ`.

Apply `hi` to reduce the goal to its premises. Establish `: δ i ∈ J` using `Ideal.subset_span ⟨i, rfl⟩`. Rewrite `this` using `[hJ0]`. Conclude with `(Submodule.mem_bot R).mp this`. Take `⟨i, hi⟩` from `hex`.

Take `⟨lam, hlam, hker⟩` from `Submodule.exists_le_ker_of_notMem hi`. Use `⟨lam, ⟨i, hlam⟩, fun j r hr => ?_⟩` and prove the remaining obligations. Conclude with `hker (Submodule.subset_span ⟨r, hr, j, rfl⟩)`.
-/
theorem exists_functional {ι : Type*} (δ : ι → R) (hδ : ∃ i, δ i ≠ 0) :
    ∃ lam : R →ₗ[ℂ] ℂ, (∃ i, lam (δ i) ≠ 0) ∧
      ∀ i, ∀ r ∈ IsLocalRing.maximalIdeal R, lam (r * δ i) = 0 := by
  classical
  set m := IsLocalRing.maximalIdeal R
  set N : Submodule ℂ R := Submodule.span ℂ {x | ∃ r ∈ m, ∃ i, x = r * δ i} with hN
  have hex : ∃ i, δ i ∉ N := by
    by_contra! hall
    set J : Ideal R := Ideal.span (Set.range δ) with hJ
    have hNJ : ∀ x ∈ N, x ∈ m • J := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ => x ∈ m • J) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨r, hr, i, rfl⟩
        exact Submodule.smul_mem_smul hr (Ideal.subset_span ⟨i, rfl⟩)
      · exact zero_mem _
      · intro x y _ _ hx hy
        exact add_mem hx hy
      · intro c x _ hx
        exact Submodule.smul_of_tower_mem _ c hx
    have hle : J ≤ m • J := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hNJ _ (hall i)
    have : IsArtinianRing R := IsArtinianRing.of_finite ℂ R
    have hJ0 : J = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m J
      (IsNoetherian.noetherian J) hle
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
    obtain ⟨i, hi⟩ := hδ
    apply hi
    have : δ i ∈ J := Ideal.subset_span ⟨i, rfl⟩
    rw [hJ0] at this
    exact (Submodule.mem_bot R).mp this
  obtain ⟨i, hi⟩ := hex
  obtain ⟨lam, hlam, hker⟩ := Submodule.exists_le_ker_of_notMem hi
  refine ⟨lam, ⟨i, hlam⟩, fun j r hr => ?_⟩
  exact hker (Submodule.subset_span ⟨r, hr, j, rfl⟩)

omit [IsLocalRing R] in

/- English proof (translation)
Use `set b := Module.Free.chooseBasis ℂ R`. Establish `key : (fun z => lam (F z * G z)) = fun z => ∑ j, ∑ i, b.coord i (F z) * b.coord j (G z) * lam (b i * b j)`. Use function extensionality and compare the values at `z`. Use `conv_lhs => rw [← b.sum_repr (F z), ← b.sum_repr (G z)]`. Simplify using `only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]`.

Rewrite using `[key]`. Use `DifferentiableOn.fun_sum fun j _ => DifferentiableOn.fun_sum fun i _ => ?_` and prove the remaining obligations. Conclude with `((hF (b.coord i)).mul (hG (b.coord j))).mul_const _`.
-/
theorem differentiableOn_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {F G : E → R}
    (hF : ∀ lam : R →ₗ[ℂ] ℂ, DifferentiableOn ℂ (fun z => lam (F z)) S)
    (hG : ∀ lam : R →ₗ[ℂ] ℂ, DifferentiableOn ℂ (fun z => lam (G z)) S) (lam : R →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => lam (F z * G z)) S := by
  classical
  set b := Module.Free.chooseBasis ℂ R
  have key : (fun z => lam (F z * G z)) = fun z =>
      ∑ j, ∑ i, b.coord i (F z) * b.coord j (G z) * lam (b i * b j) := by
    funext z
    conv_lhs => rw [← b.sum_repr (F z), ← b.sum_repr (G z)]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul,
      smul_eq_mul, Module.Basis.coord_apply]
  rw [key]
  refine DifferentiableOn.fun_sum fun j _ => DifferentiableOn.fun_sum fun i _ => ?_
  exact ((hF (b.coord i)).mul (hG (b.coord j))).mul_const _

end Artin

end GlobalTheory.ArtinKernel

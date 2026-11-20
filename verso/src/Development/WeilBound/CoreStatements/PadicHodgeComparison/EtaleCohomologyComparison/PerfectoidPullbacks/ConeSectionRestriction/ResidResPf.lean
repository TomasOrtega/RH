import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaurentPartialDerivationUnique

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [Algebra K R] {n : ℕ}

/- English proof (translation)
Simplify using `only [tpow, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]`.
-/
theorem resRPf_tpow_add (t : Fin (n + 1) → Rˣ) (m m' : Fin (n + 1) → ℤ) :
    tpow t (m + m') = tpow t m * tpow t m' := by
  simp only [tpow, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]

/- English proof (translation)
Unfold `tpow`. Use `congr 1`. Simplify using `only [zpow_neg_one, Finset.prod_inv_distrib]`.
-/
theorem resRPf_tpow_negOne (t : Fin (n + 1) → Rˣ) :
    tpow t (fun _ => -1) = (((∏ k, t k)⁻¹ : Rˣ) : R) := by
  unfold tpow
  congr 1
  simp only [zpow_neg_one, Finset.prod_inv_distrib]

/- English proof (translation)
Unfold `tpow`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single k]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `[hj]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`.
-/
theorem resRPf_tpow_single (t : Fin (n + 1) → Rˣ) (k : Fin (n + 1)) :
    tpow t (-Pi.single k (1 : ℤ)) = (((t k)⁻¹ : Rˣ) : R) := by
  unfold tpow
  congr 1
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hg m0 hm0`. Use `set N : ℤ := ∑ m ∈ s, ∑ j, |m j| with hN`. Establish `hbound : ∀ m ∈ s, ∀ j, 0 ≤ m j + N`. Introduce `m hm j`.

Establish `h1 : |m j| ≤ ∑ j, |m j|` using `Finset.single_le_sum (f := fun j => |m j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)`. Establish `h2 : ∑ j, |m j| ≤ N` using `Finset.single_le_sum (f := fun m : Fin (n + 1) → ℤ => ∑ j, |m j|) (fun m _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) hm`. Establish `h3` using `neg_abs_le (m j)`. Combine the linear equalities and inequalities to obtain the conclusion. Set `e : (Fin (n + 1) → ℤ) → (Fin (n + 1) →₀ ℕ)` to `fun m => Finsupp.equivFunOnFinite.symm (fun j => (m j + N).toNat)`.

Establish `he : ∀ m ∈ s, tpow t (m + fun _ => N) = MvPolynomial.aeval (fun k => (t k : R)) (MvPolynomial.monomial (e m) (1 : K))`. Introduce `m hm`. Rewrite using `[MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]`. Unfold `tpow`. Rewrite using `[Units.coe_prod]`.

Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Simplify using `only [e, Finsupp.coe_equivFunOnFinite_symm, Pi.add_apply]`. Use `conv_lhs => rw [← Int.toNat_of_nonneg (hbound m hm j)]`. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val]`. Establish `hmul : ∑ m ∈ s, g m • tpow t (m + fun _ => N) = 0`.

Repeatedly rewrite using `[resRPf_tpow_add, ← smul_mul_assoc]`. Rewrite using `[← Finset.sum_mul, hg, zero_mul]`. Establish `hpoly : ∑ m ∈ s, MvPolynomial.monomial (e m) (g m) = 0`. Apply `algebraicIndependent_iff_injective_aeval.1 ht` to reduce the goal to its premises. Rewrite using `[map_sum, map_zero, ← hmul]`.

Use `Finset.sum_congr rfl (fun m hm => ?_)` and prove the remaining obligations. Rewrite using `[he m hm]`. Simplify using `only [MvPolynomial.aeval_monomial, map_one, one_mul, Algebra.smul_def]`. Establish `hinj : ∀ m ∈ s, ∀ m' ∈ s, e m = e m' → m = m'`. Introduce `m hm m' hm' h`.

Use function extensionality and compare the values at `j`. Establish `h0` using `DFunLike.congr_fun h j`. Simplify using `only [e, Finsupp.coe_equivFunOnFinite_symm] at h0`. Establish `h1` using `hbound m hm j`. Establish `h2` using `hbound m' hm' j`.

Use linear arithmetic over natural numbers and integers. Establish `hc` using `congrArg (MvPolynomial.coeff (e m0)) hpoly`. Rewrite `hc` using `[MvPolynomial.coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single m0]`. Simplify `hc` using `[MvPolynomial.coeff_monomial]`. Introduce `m hm hne`.

Rewrite using `[MvPolynomial.coeff_monomial, if_neg (fun h => hne (hinj m hm m0 hm0 h))]`. Introduce `h`. Conclude with `absurd hm0 h`.
-/
theorem resRPf_linInd (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R)) :
    LinearIndependent K (tpow t) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg m0 hm0
  set N : ℤ := ∑ m ∈ s, ∑ j, |m j| with hN
  have hbound : ∀ m ∈ s, ∀ j, 0 ≤ m j + N := by
    intro m hm j
    have h1 : |m j| ≤ ∑ j, |m j| :=
      Finset.single_le_sum (f := fun j => |m j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j, |m j| ≤ N :=
      Finset.single_le_sum (f := fun m : Fin (n + 1) → ℤ => ∑ j, |m j|)
        (fun m _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) hm
    have h3 := neg_abs_le (m j)
    linarith
  let e : (Fin (n + 1) → ℤ) → (Fin (n + 1) →₀ ℕ) :=
    fun m => Finsupp.equivFunOnFinite.symm (fun j => (m j + N).toNat)
  have he : ∀ m ∈ s, tpow t (m + fun _ => N) =
      MvPolynomial.aeval (fun k => (t k : R)) (MvPolynomial.monomial (e m) (1 : K)) := by
    intro m hm
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    unfold tpow
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [e, Finsupp.coe_equivFunOnFinite_symm, Pi.add_apply]
    conv_lhs => rw [← Int.toNat_of_nonneg (hbound m hm j)]
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  have hmul : ∑ m ∈ s, g m • tpow t (m + fun _ => N) = 0 := by
    simp_rw [resRPf_tpow_add, ← smul_mul_assoc]
    rw [← Finset.sum_mul, hg, zero_mul]
  have hpoly : ∑ m ∈ s, MvPolynomial.monomial (e m) (g m) = 0 := by
    apply algebraicIndependent_iff_injective_aeval.1 ht
    rw [map_sum, map_zero, ← hmul]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [he m hm]
    simp only [MvPolynomial.aeval_monomial, map_one, one_mul, Algebra.smul_def]
  have hinj : ∀ m ∈ s, ∀ m' ∈ s, e m = e m' → m = m' := by
    intro m hm m' hm' h
    funext j
    have h0 := DFunLike.congr_fun h j
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h0
    have h1 := hbound m hm j
    have h2 := hbound m' hm' j
    omega
  have hc := congrArg (MvPolynomial.coeff (e m0)) hpoly
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single m0] at hc
  · simpa [MvPolynomial.coeff_monomial] using hc
  · intro m hm hne
    rw [MvPolynomial.coeff_monomial, if_neg (fun h => hne (hinj m hm m0 hm0 h))]
  · intro h
    exact absurd hm0 h

def resRPfLogD (D : Derivation K R R) : Rˣ →* Multiplicative R where
  toFun u := Multiplicative.ofAdd ((((u⁻¹ : Rˣ)) : R) * D (u : R))
  map_one' := by simp
  map_mul' u v := by
    rw [← ofAdd_add]
    congr 1
    have hu : (((u⁻¹ : Rˣ)) : R) * u = 1 := Units.inv_mul u
    have hv : (((v⁻¹ : Rˣ)) : R) * v = 1 := Units.inv_mul v
    simp only [mul_inv_rev, Units.val_mul, Derivation.leibniz, smul_eq_mul]
    linear_combination ((((v⁻¹ : Rˣ)) : R) * D (v : R)) * hu + ((((u⁻¹ : Rˣ)) : R) * D (u : R)) * hv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem resRPfLogD_apply (D : Derivation K R R) (u : Rˣ) :
    Multiplicative.toAdd (resRPfLogD D u) = (((u⁻¹ : Rˣ)) : R) * D (u : R) := rfl

/- English proof (translation)
Establish `h` using `congrArg Multiplicative.toAdd (map_prod (resRPfLogD D) (fun j => t j ^ m j) Finset.univ)`. Simplify using `only [map_zpow, toAdd_prod, toAdd_zpow, resRPfLogD_apply] at h`. Conclude with `h`.
-/
theorem resRPf_logD (t : Fin (n + 1) → Rˣ) (D : Derivation K R R) (m : Fin (n + 1) → ℤ) :
    (((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) * D (tpow t m) =
      ∑ j, m j • ((((t j)⁻¹ : Rˣ) : R) * D (t j : R)) := by
  have h := congrArg Multiplicative.toAdd (map_prod (resRPfLogD D) (fun j => t j ^ m j) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow, resRPfLogD_apply] at h
  exact h

/- English proof (translation)
Establish `h` using `resRPf_logD t (D k) m`. Simplify using `only [hD, mul_ite, mul_one, mul_zero, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h`. Establish `hU : tpow t m * (((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) = 1` using `Units.mul_inv _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, hU, one_mul]`.

Use `_ = tpow t m * (m k • (((t k)⁻¹ : Rˣ) : R)) := by rw [h]`. Use `_ = m k • tpow t (m - Pi.single k (1 : ℤ)) := by`. Rewrite using `[mul_smul_comm, sub_eq_add_neg, resRPf_tpow_add, resRPf_tpow_single]`.
-/
theorem resRPf_Dk (t : Fin (n + 1) → Rˣ) (D : Fin (n + 1) → Derivation K R R)
    (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) (k : Fin (n + 1)) (m : Fin (n + 1) → ℤ) :
    D k (tpow t m) = m k • tpow t (m - Pi.single k (1 : ℤ)) := by
  have h := resRPf_logD t (D k) m
  simp only [hD, mul_ite, mul_one, mul_zero, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true] at h
  have hU : tpow t m * (((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) = 1 := Units.mul_inv _
  calc D k (tpow t m) = tpow t m * ((((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) * D k (tpow t m)) := by
        rw [← mul_assoc, hU, one_mul]
    _ = tpow t m * (m k • (((t k)⁻¹ : Rˣ) : R)) := by rw [h]
    _ = m k • tpow t (m - Pi.single k (1 : ℤ)) := by
        rw [mul_smul_comm, sub_eq_add_neg, resRPf_tpow_add, resRPf_tpow_single]

/- English proof (translation)
Establish `hli` using `resRPf_linInd (K := K) t ht`. Take `⟨res, hres⟩` from `LinearMap.exists_extend ((Module.Basis.span hli).coord (fun _ => -1))`. Establish `hval : ∀ m, res (tpow t m) = if m = (fun _ => -1) then 1 else 0`. Introduce `m`. Establish `h1 : tpow t m = ((Module.Basis.span hli m : Submodule.span K (Set.range (tpow t))) : R)` using `congrArg Subtype.val (Module.Basis.span_apply hli m).symm`.

Establish `h2` using `LinearMap.congr_fun hres (Module.Basis.span hli m)`. Rewrite `h2` using `[LinearMap.comp_apply, Submodule.subtype_apply]`. Rewrite using `[h1, h2, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Use `⟨res, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← resRPf_tpow_negOne, hval, if_pos rfl]`.

Introduce `x hx`. Establish `hle : Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}) ≤ LinearMap.ker res`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, hval, if_neg hm]`.

Conclude with `hle hx`. Introduce `k x hx`. Establish `hx' : x ∈ Submodule.span K (Set.range (tpow t))`. Establish `h1 : x ∈ Subalgebra.toSubmodule (torusS K t Finset.univ)` using `hx`. Rewrite `h1` using `[torusS, Algebra.adjoin_eq_span]`.

Use `Submodule.span_mono ?_ h1` and prove the remaining obligations. Introduce `y hy`. Set `M : Submonoid R` to `{ carrier := Set.range (tpow t) mul_mem' := by`. Introduce and unpack `_ _ ⟨a, rfl⟩ ⟨b, rfl⟩`. Conclude with `⟨a + b, resRPf_tpow_add t a b⟩`.

Use the proof step `one_mem' := ⟨0, by simp [tpow]⟩ }`. Conclude with `(Submonoid.closure_le (S := M)).2 (Set.image_subset_range _ _) hy`. Establish `hker : Submodule.span K (Set.range (tpow t)) ≤ LinearMap.ker (res ∘ₗ (D k : R →ₗ[K] R))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨m, rfl⟩`.

Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, Derivation.coeFn_coe, resRPf_Dk t D hD k m, map_zsmul, hval]`. Distinguish the cases in `h : m - Pi.single k (1 : ℤ) = fun _ => -1`. Establish `h'` using `congr_fun h k`. Simplify using `only [Pi.sub_apply, Pi.single_eq_same] at h'`. Establish `h0 : m k = 0` using `by omega`.

Rewrite using `[h0, zero_smul]`. Rewrite using `[if_neg h, smul_zero]`. Establish `h2` using `hker hx'`. Rewrite `h2` using `[LinearMap.mem_ker, LinearMap.comp_apply, Derivation.coeFn_coe]`. Then use the resulting hypothesis.
-/
theorem res_R_pf (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R))
    (D : Fin (n + 1) → Derivation K R R) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) :
    ∃ res : R →ₗ[K] K, res (((∏ k, t k)⁻¹ : Rˣ) : R) = 1 ∧
      (∀ x ∈ Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}), res x = 0) ∧
      ∀ k, ∀ x ∈ torusS K t Finset.univ, res (D k x) = 0 := by
  classical
  have hli := resRPf_linInd (K := K) t ht
  obtain ⟨res, hres⟩ := LinearMap.exists_extend ((Module.Basis.span hli).coord (fun _ => -1))
  have hval : ∀ m, res (tpow t m) = if m = (fun _ => -1) then 1 else 0 := by
    intro m
    have h1 : tpow t m = ((Module.Basis.span hli m : Submodule.span K (Set.range (tpow t))) : R) :=
      congrArg Subtype.val (Module.Basis.span_apply hli m).symm
    have h2 := LinearMap.congr_fun hres (Module.Basis.span hli m)
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h1, h2, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  refine ⟨res, ?_, ?_, ?_⟩
  · rw [← resRPf_tpow_negOne, hval, if_pos rfl]
  · intro x hx
    have hle : Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}) ≤ LinearMap.ker res := by
      rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hval, if_neg hm]
    exact hle hx
  · intro k x hx
    have hx' : x ∈ Submodule.span K (Set.range (tpow t)) := by
      have h1 : x ∈ Subalgebra.toSubmodule (torusS K t Finset.univ) := hx
      rw [torusS, Algebra.adjoin_eq_span] at h1
      refine Submodule.span_mono ?_ h1
      intro y hy
      let M : Submonoid R :=
        { carrier := Set.range (tpow t)
          mul_mem' := by
            rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
            exact ⟨a + b, resRPf_tpow_add t a b⟩
          one_mem' := ⟨0, by simp [tpow]⟩ }
      exact (Submonoid.closure_le (S := M)).2 (Set.image_subset_range _ _) hy
    have hker : Submodule.span K (Set.range (tpow t)) ≤ LinearMap.ker (res ∘ₗ (D k : R →ₗ[K] R)) := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, Derivation.coeFn_coe,
        resRPf_Dk t D hD k m, map_zsmul, hval]
      by_cases h : m - Pi.single k (1 : ℤ) = fun _ => -1
      · have h' := congr_fun h k
        simp only [Pi.sub_apply, Pi.single_eq_same] at h'
        have h0 : m k = 0 := by omega
        rw [h0, zero_smul]
      · rw [if_neg h, smul_zero]
    have h2 := hker hx'
    rwa [LinearMap.mem_ker, LinearMap.comp_apply, Derivation.coeFn_coe] at h2

end CrystallineSemistableComparison.Pb

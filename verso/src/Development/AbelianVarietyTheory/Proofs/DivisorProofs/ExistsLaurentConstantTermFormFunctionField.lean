import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in
/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hg n hn`. Use `set B : ℤ := ∑ m ∈ s, ∑ i, |m i| with hBdef`. Establish `hB : ∀ m ∈ s, ∀ i, 0 ≤ m i + B`. Introduce `m hm i`.

Establish `h1 : |m i| ≤ ∑ i, |m i|` using `Finset.single_le_sum (f := fun i => |m i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)`. Establish `h2 : ∑ i, |m i| ≤ B` using `Finset.single_le_sum (f := fun m : ι → ℤ => ∑ i, |m i|) (fun m _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hm`. Combine the linear relations using `[neg_abs_le (m i)]`. Set `e : (ι → ℤ) → (ι →₀ ℕ)` to `fun m => Finsupp.equivFunOnFinite.symm (fun i => (m i + B).toNat)`. Establish `he : Set.InjOn e s`.

Introduce `m hm m' hm' h`. Use function extensionality and compare the values at `i`. Establish `h'` using `congrArg (fun f : ι →₀ ℕ => f i) h`. Simplify using `only [e, Finsupp.coe_equivFunOnFinite_symm] at h'`. Use `Int.toNat_of_nonneg (hB m hm i)` as an intermediate fact.

Use `Int.toNat_of_nonneg (hB m' hm' i)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `set P : F := ∏ i, y i ^ B with hPdef`. Establish `hkey : ∀ m ∈ s, MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k)) = P * ∏ i, y i ^ m i`. Introduce `m hm`.

Rewrite using `[MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _), hPdef, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ (hy0 i), ← zpow_natCast]`. Use `congr 1`. Simplify using `only [e, Finsupp.coe_equivFunOnFinite_symm]`.

Rewrite using `[Int.toNat_of_nonneg (hB m hm i)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hw : LinearIndependent k (fun a : ι →₀ ℕ => MvPolynomial.aeval y (MvPolynomial.monomial a (1 : k)))`. Use `(MvPolynomial.basisMonomials ι k).linearIndependent.map' (MvPolynomial.aeval y).toLinearMap (LinearMap.ker_eq_bot.mpr hy)` as an intermediate fact. Simplify `this` using `only [MvPolynomial.coe_basisMonomials, Function.comp_def, AlgHom.toLinearMap_apply]`.

Establish `hws : LinearIndependent k (fun m : s => MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k)))` using `hw.comp (fun m : s => e m) (fun a b h => Subtype.ext (he a.2 b.2 h))`. Rewrite `hws` using `[Fintype.linearIndependent_iff]`. Use `hws (fun m => g m) ?_ ⟨n, hn⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[hkey m m.2, mul_smul_comm]`. Use `_ = P * ∑ m ∈ s, g m • ∏ i, y i ^ m i := by`. Rewrite using `[← Finset.mul_sum, Finset.sum_coe_sort s (fun m => g m • ∏ i, y i ^ m i)]`. Use `_ = 0 := by rw [hg, mul_zero]`.
-/
private theorem linearIndependent_laurentMonomials {k F ι : Type} [Field k] [Field F] [Algebra k F]
    [Fintype ι] (y : ι → F) (hy : AlgebraicIndependent k y) (hy0 : ∀ i, y i ≠ 0) :
    LinearIndependent k (fun n : ι → ℤ => ∏ i, y i ^ n i) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg n hn
  set B : ℤ := ∑ m ∈ s, ∑ i, |m i| with hBdef
  have hB : ∀ m ∈ s, ∀ i, 0 ≤ m i + B := by
    intro m hm i
    have h1 : |m i| ≤ ∑ i, |m i| :=
      Finset.single_le_sum (f := fun i => |m i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i, |m i| ≤ B :=
      Finset.single_le_sum (f := fun m : ι → ℤ => ∑ i, |m i|)
        (fun m _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hm
    linarith [neg_abs_le (m i)]
  let e : (ι → ℤ) → (ι →₀ ℕ) := fun m => Finsupp.equivFunOnFinite.symm (fun i => (m i + B).toNat)
  have he : Set.InjOn e s := by
    intro m hm m' hm' h
    funext i
    have h' := congrArg (fun f : ι →₀ ℕ => f i) h
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h'
    have := Int.toNat_of_nonneg (hB m hm i)
    have := Int.toNat_of_nonneg (hB m' hm' i)
    omega
  set P : F := ∏ i, y i ^ B with hPdef
  have hkey : ∀ m ∈ s, MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k)) =
      P * ∏ i, y i ^ m i := by
    intro m hm
    rw [MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _), hPdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_add₀ (hy0 i), ← zpow_natCast]
    congr 1
    simp only [e, Finsupp.coe_equivFunOnFinite_symm]
    rw [Int.toNat_of_nonneg (hB m hm i)]
    ring
  have hw : LinearIndependent k (fun a : ι →₀ ℕ => MvPolynomial.aeval y (MvPolynomial.monomial a (1 : k))) := by
    have := (MvPolynomial.basisMonomials ι k).linearIndependent.map'
      (MvPolynomial.aeval y).toLinearMap (LinearMap.ker_eq_bot.mpr hy)
    simpa only [MvPolynomial.coe_basisMonomials, Function.comp_def, AlgHom.toLinearMap_apply] using this
  have hws : LinearIndependent k
      (fun m : s => MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k))) :=
    hw.comp (fun m : s => e m) (fun a b h => Subtype.ext (he a.2 b.2 h))
  rw [Fintype.linearIndependent_iff] at hws
  refine hws (fun m => g m) ?_ ⟨n, hn⟩
  calc ∑ m : s, g m • MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k))
      = ∑ m : s, P * (g m • ∏ i, y i ^ (m : ι → ℤ) i) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hkey m m.2, mul_smul_comm]
    _ = P * ∑ m ∈ s, g m • ∏ i, y i ^ m i := by
        rw [← Finset.mul_sum, Finset.sum_coe_sort s (fun m => g m • ∏ i, y i ^ m i)]
    _ = 0 := by rw [hg, mul_zero]

open KaehlerDifferential in
/- English proof (translation)
Establish `h0 : m 0 = -∑ i : Fin d, m i.succ`. Rewrite `hm` using `[Fin.sum_univ_succ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpow : ∀ s : Finset (Fin d), ∏ i ∈ s, x 0 ^ m i.succ = x 0 ^ ∑ i ∈ s, m i.succ` using `by classical`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (hx 0)]`. Rewrite using `[Fin.prod_univ_succ, h0]`. Repeatedly rewrite using `[div_zpow]`.

Rewrite using `[Finset.prod_div_distrib, hpow, zpow_neg, div_eq_mul_inv, mul_comm]`.
-/
private theorem prod_zpow_eq_prod_div_zpow_of_sum_eq_zero {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → F)
    (hx : ∀ i, x i ≠ 0) (m : Fin (d + 1) → ℤ) (hm : ∑ j, m j = 0) :
    ∏ j, x j ^ m j = ∏ i : Fin d, (x i.succ / x 0) ^ m i.succ := by
  have h0 : m 0 = -∑ i : Fin d, m i.succ := by
    rw [Fin.sum_univ_succ] at hm
    linarith
  have hpow : ∀ s : Finset (Fin d), ∏ i ∈ s, x 0 ^ m i.succ = x 0 ^ ∑ i ∈ s, m i.succ := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (hx 0)]
  rw [Fin.prod_univ_succ, h0]
  simp_rw [div_zpow]
  rw [Finset.prod_div_distrib, hpow, zpow_neg, div_eq_mul_inv, mul_comm]

open KaehlerDifferential in

/- English proof (translation)
Introduce `k _ F _ _ d x hx`. Set `v : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} → F` to `fun m => ∏ j, x j ^ m.1 j`. Establish `hv : LinearIndependent k v`. Establish `hL` using `linearIndependent_laurentMonomials (k := k) (fun i : Fin d => x i.succ / x 0) hx.indep (fun i => div_ne_zero (hx.ne _) (hx.ne 0))`. Establish `hinj : Function.Injective (fun m : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} => fun i : Fin d => m.1 i.succ)`.

Introduce `a b h`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hs : ∀ i : Fin d, a.1 i.succ = b.1 i.succ` using `fun i => congrFun h i`. Establish `ha` using `a.2`. Establish `hb` using `b.2`.

Rewrite `ha`, `hb` using `[Fin.sum_univ_succ]`. Establish `hsum : ∑ i : Fin d, a.1 i.succ = ∑ i : Fin d, b.1 i.succ` using `Finset.sum_congr rfl fun i _ => hs i`. Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun i => hs i) j` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.

Use `hL.comp _ hinj` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`. Conclude with `prod_zpow_eq_prod_div_zpow_of_sum_eq_zero x hx.ne m.1 m.2`. Set `z₀ : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0}` to `⟨0, by simp⟩`.

Establish `h1 : v z₀ = 1` using `by simp [v, z₀]`. Establish `hnot` using `hv.notMem_span_image (s := {z | z ≠ z₀}) (x := z₀) (by simp)`. Rewrite `hnot` using `[h1]`. Take `⟨f, hf1, hf⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance`. Use `⟨(f 1)⁻¹ • f, ?_⟩` and prove the remaining obligations.

Use `delta _root_.GlobalTheory.PD.IsRes`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf1]`. Introduce `m hm hm0`. Establish `hmem : ∏ j, x j ^ m j ∈ Submodule.span k (v '' {z | z ≠ z₀})` using `Submodule.subset_span ⟨⟨m, hm⟩, fun h => hm0 (congrArg Subtype.val h), rfl⟩`.

Establish `hzero : f (∏ j, x j ^ m j) = 0`. Conclude with `LinearMap.mem_ker.mp ((LinearMap.le_ker_iff_map.mpr hf) hmem)`. Rewrite using `[LinearMap.smul_apply, hzero, smul_zero]`.
-/
theorem _root_.GlobalTheory.exists_isRes : ∀ (k : Type) [Field k] (F : Type) [Field F]
    [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F),
    _root_.GlobalTheory.PD.IsPd k x → ∃ ρ : F →ₗ[k] k, _root_.GlobalTheory.PD.IsRes k x ρ := by
  intro k _ F _ _ d x hx
  classical
  let v : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} → F := fun m => ∏ j, x j ^ m.1 j
  have hv : LinearIndependent k v := by
    have hL := linearIndependent_laurentMonomials (k := k) (fun i : Fin d => x i.succ / x 0)
      hx.indep
      (fun i => div_ne_zero (hx.ne _) (hx.ne 0))
    have hinj : Function.Injective
        (fun m : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} => fun i : Fin d => m.1 i.succ) := by
      intro a b h
      apply Subtype.ext
      have hs : ∀ i : Fin d, a.1 i.succ = b.1 i.succ := fun i => congrFun h i
      have ha := a.2
      have hb := b.2
      rw [Fin.sum_univ_succ] at ha hb
      have hsum : ∑ i : Fin d, a.1 i.succ = ∑ i : Fin d, b.1 i.succ :=
        Finset.sum_congr rfl fun i _ => hs i
      funext j
      refine Fin.cases ?_ (fun i => hs i) j
      linarith
    have := hL.comp _ hinj
    convert this using 1
    funext m
    exact prod_zpow_eq_prod_div_zpow_of_sum_eq_zero x hx.ne m.1 m.2
  let z₀ : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} := ⟨0, by simp⟩
  have h1 : v z₀ = 1 := by simp [v, z₀]
  have hnot := hv.notMem_span_image (s := {z | z ≠ z₀}) (x := z₀) (by simp)
  rw [h1] at hnot
  obtain ⟨f, hf1, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨(f 1)⁻¹ • f, ?_⟩
  delta _root_.GlobalTheory.PD.IsRes
  refine ⟨?_, ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf1]
  · intro m hm hm0
    have hmem : ∏ j, x j ^ m j ∈ Submodule.span k (v '' {z | z ≠ z₀}) :=
      Submodule.subset_span ⟨⟨m, hm⟩, fun h => hm0 (congrArg Subtype.val h), rfl⟩
    have hzero : f (∏ j, x j ^ m j) = 0 := by
      exact LinearMap.mem_ker.mp ((LinearMap.le_ker_iff_map.mpr hf) hmem)
    rw [LinearMap.smul_apply, hzero, smul_zero]

end GlobalTheory

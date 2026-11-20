import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreTor
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFreeness
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Use `set J := (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L`. Rewrite `h` using `[smul_eq_C_mul]`. Establish `h1 : C (u - MvPolynomial.C (eval t u)) * x ∈ J` using `Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])) hx`. Establish `h2 : C (MvPolynomial.C (eval t u)) * x ∈ J`. Use `J.sub_mem h h1` as an intermediate fact.

Rewrite `this` using `[← sub_mul, ← map_sub, sub_sub_cancel]`. Then use the resulting hypothesis. Establish `hunit : IsUnit (C (MvPolynomial.C (eval t u)) : MvPolynomial ι (MvPolynomial σ ℂ))` using `(hu.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)).map (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ))`. Conclude with `(Ideal.unit_mul_mem_iff_mem J hunit).1 h2`.
-/
theorem GenericFibreTor.mem_of_smul_mem {σ ι : Type*} (t : σ → ℂ)
    (L : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))) {x : MvPolynomial ι (MvPolynomial σ ℂ)} (hx : x ∈ L)
    {u : MvPolynomial σ ℂ} (hu : eval t u ≠ 0)
    (h : u • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L) :
    x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L := by
  set J := (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L
  rw [smul_eq_C_mul] at h
  have h1 : C (u - MvPolynomial.C (eval t u)) * x ∈ J :=
    Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])) hx
  have h2 : C (MvPolynomial.C (eval t u)) * x ∈ J := by
    have := J.sub_mem h h1
    rwa [← sub_mul, ← map_sub, sub_sub_cancel] at this
  have hunit : IsUnit (C (MvPolynomial.C (eval t u)) : MvPolynomial ι (MvPolynomial σ ℂ)) :=
    (hu.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ))
  exact (Ideal.unit_mul_mem_iff_mem J hunit).1 h2

/- English proof (translation)
Introduce `σ _ ι _ L`. Take `⟨F, hF0, hfree⟩` from `hGF (MvPolynomial σ ℂ) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)`. Use `⟨F, hF0, fun t ht x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[MvPolynomial.ker_map]`. Take `⟨hxL, hxI⟩` from `Ideal.mem_inf.1 hx`.

Rewrite `hxI` using `[MvPolynomial.mem_map_C_iff]`. Establish `hflat' : Module.Flat (Localization.Away F) (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L))` using `@Module.Flat.of_free _ _ _ _ _ hfree`. Establish `hflatS : Module.Flat (MvPolynomial σ ℂ) (Localization.Away F)` using `IsLocalization.flat _ (Submonoid.powers F)`. Establish `: Module.Flat (MvPolynomial σ ℂ) (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L))` using `Module.Flat.trans (MvPolynomial σ ℂ) (Localization.Away F) _`. Set `g` to `LocalizedModule.mkLinearMap (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)`.

Set `π` to `(Ideal.Quotient.mkₐ (MvPolynomial σ ℂ) L).toLinearMap`. Set `a : x.support → MvPolynomial σ ℂ` to `fun m => coeff m.1 x`. Set `e : x.support → MvPolynomial ι (MvPolynomial σ ℂ)` to `fun m => monomial m.1 1`. Establish `hsum : ∑ m, a m • e m = x`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_coe_sort x.support (fun v => monomial v (coeff v x))]`. Conclude with `(MvPolynomial.as_sum x).symm`. Establish `hrel : ∑ m, a m • g (π (e m)) = 0`. Repeatedly rewrite using `[← map_smul, ← map_sum, hsum]`. Simplify using `[g, π, Ideal.Quotient.eq_zero_iff_mem.2 hxL]`.

Establish `htriv : Module.IsTrivialRelation a (fun m => g (π (e m)))` using `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel`. Take `⟨k, A, y, hy, hA⟩` from `htriv`. Take `⟨b, hb⟩` from `IsLocalizedModule.exist_integer_multiples_of_finite (Submonoid.powers F) g y`. Use `choose q hq using hb`. Use `choose r hr using fun j => Ideal.Quotient.mk_surjective (q j)`.

Establish `hm : ∀ m, ∃ c : Submonoid.powers F, c • π ((b : MvPolynomial σ ℂ) • e m) = c • π (∑ j, A m j • r j)`. Introduce `m`. Apply `IsLocalizedModule.exists_of_eq (S := Submonoid.powers F) (f := g)` to reduce the goal to its premises. Rewrite using `[map_smul, map_smul, show g (π (e m)) = ∑ j, A m j • y j from hy m, Finset.smul_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_comm, ← hq j, ← hr j, map_smul, map_smul]`. Both sides reduce to the same expression. Use `choose c hc using hm`. Use `set V : MvPolynomial σ ℂ := ∏ m, (c m : MvPolynomial σ ℂ)`. Establish `hD : ∀ m, (V * b) • e m - ∑ j, (V * A m j) • r j ∈ L`.

Introduce `m`. Establish `h1` using `hc m`. Rewrite `h1` using `[← sub_eq_zero, ← smul_sub, ← map_sub, Submonoid.smul_def, ← map_smul]`. Establish `h2 : (c m : MvPolynomial σ ℂ) • ((b : MvPolynomial σ ℂ) • e m - ∑ j, A m j • r j) ∈ L` using `Ideal.Quotient.eq_zero_iff_mem.1 h1`. Establish `h3` using `Submodule.smul_of_tower_mem L (∏ m' ∈ Finset.univ.erase m, (c m' : MvPolynomial σ ℂ)) h2`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ m), smul_sub, smul_smul, Finset.smul_sum]`. Repeatedly rewrite using `[smul_smul]`. Both sides reduce to the same expression. Establish `hzero : ∑ m, a m • ∑ j, (V * A m j) • r j = 0`.

Repeatedly rewrite using `[Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Establish `: ∑ m, a m * (V * A m j) = V * ∑ m, a m * A m j`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hA j, mul_zero, zero_smul]`. Establish `hkey : (V * b) • x = ∑ m, a m • ((V * b) • e m - ∑ j, (V * A m j) • r j)`.

Repeatedly rewrite using `[smul_sub, Finset.sum_sub_distrib, hzero, sub_zero, ← hsum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`. Establish `hJ : (V * b) • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L`. Rewrite using `[hkey]`.

Use `Ideal.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_C_mul]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hxI m.1)) (hD m)`. Establish `hpow : ∀ u ∈ Submonoid.powers F, eval t u ≠ 0`. Introduce and unpack `u ⟨n, rfl⟩`.

Rewrite using `[map_pow]`. Conclude with `pow_ne_zero n ht`. Establish `hVb : V * b ∈ Submonoid.powers F` using `(Submonoid.powers F).mul_mem (Submonoid.prod_mem _ fun m _ => (c m).2) b.2`. Conclude with `GenericFibreTor.mem_of_smul_mem t L hxL (hpow _ hVb) hJ`.
-/
theorem GenericFibreTor.proof (hGF : GenericFreeness.Statement.{0, 0, 0}) :
    GenericFibreTor.Statement := by
  classical
  intro σ _ ι _ L
  obtain ⟨F, hF0, hfree⟩ := hGF (MvPolynomial σ ℂ) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
    (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
  refine ⟨F, hF0, fun t ht x hx => ?_⟩
  rw [MvPolynomial.ker_map] at hx ⊢
  obtain ⟨hxL, hxI⟩ := Ideal.mem_inf.1 hx
  rw [MvPolynomial.mem_map_C_iff] at hxI
  have hflat' : Module.Flat (Localization.Away F)
      (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)) :=
    @Module.Flat.of_free _ _ _ _ _ hfree
  have hflatS : Module.Flat (MvPolynomial σ ℂ) (Localization.Away F) := IsLocalization.flat _ (Submonoid.powers F)
  have : Module.Flat (MvPolynomial σ ℂ)
      (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)) :=
    Module.Flat.trans (MvPolynomial σ ℂ) (Localization.Away F) _
  let g := LocalizedModule.mkLinearMap (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
  let π := (Ideal.Quotient.mkₐ (MvPolynomial σ ℂ) L).toLinearMap
  let a : x.support → MvPolynomial σ ℂ := fun m => coeff m.1 x
  let e : x.support → MvPolynomial ι (MvPolynomial σ ℂ) := fun m => monomial m.1 1
  have hsum : ∑ m, a m • e m = x := by
    calc ∑ m, a m • e m = ∑ m : x.support, monomial m.1 (coeff m.1 x) :=
          Finset.sum_congr rfl fun m _ => by simp [a, e, smul_monomial]
      _ = x := by
          rw [Finset.sum_coe_sort x.support (fun v => monomial v (coeff v x))]
          exact (MvPolynomial.as_sum x).symm
  have hrel : ∑ m, a m • g (π (e m)) = 0 := by
    simp_rw [← map_smul, ← map_sum, hsum]
    simp [g, π, Ideal.Quotient.eq_zero_iff_mem.2 hxL]
  have htriv : Module.IsTrivialRelation a (fun m => g (π (e m))) :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨k, A, y, hy, hA⟩ := htriv
  obtain ⟨b, hb⟩ := IsLocalizedModule.exist_integer_multiples_of_finite (Submonoid.powers F) g y
  choose q hq using hb
  choose r hr using fun j => Ideal.Quotient.mk_surjective (q j)
  have hm : ∀ m, ∃ c : Submonoid.powers F,
      c • π ((b : MvPolynomial σ ℂ) • e m) = c • π (∑ j, A m j • r j) := by
    intro m
    apply IsLocalizedModule.exists_of_eq (S := Submonoid.powers F) (f := g)
    rw [map_smul, map_smul, show g (π (e m)) = ∑ j, A m j • y j from hy m, Finset.smul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm, ← hq j, ← hr j, map_smul, map_smul]
    rfl
  choose c hc using hm
  set V : MvPolynomial σ ℂ := ∏ m, (c m : MvPolynomial σ ℂ)
  have hD : ∀ m, (V * b) • e m - ∑ j, (V * A m j) • r j ∈ L := by
    intro m
    have h1 := hc m
    rw [← sub_eq_zero, ← smul_sub, ← map_sub, Submonoid.smul_def, ← map_smul] at h1
    have h2 : (c m : MvPolynomial σ ℂ) • ((b : MvPolynomial σ ℂ) • e m - ∑ j, A m j • r j) ∈ L :=
      Ideal.Quotient.eq_zero_iff_mem.1 h1
    have h3 := Submodule.smul_of_tower_mem L (∏ m' ∈ Finset.univ.erase m, (c m' : MvPolynomial σ ℂ)) h2
    convert h3 using 1
    rw [smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ m), smul_sub, smul_smul,
      Finset.smul_sum]
    simp_rw [smul_smul]
    rfl
  have hzero : ∑ m, a m • ∑ j, (V * A m j) • r j = 0 := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul]
    have : ∑ m, a m * (V * A m j) = V * ∑ m, a m * A m j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_; ring
    rw [this, hA j, mul_zero, zero_smul]
  have hkey : (V * b) • x = ∑ m, a m • ((V * b) • e m - ∑ j, (V * A m j) • r j) := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, hzero, sub_zero, ← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_comm]
  have hJ : (V * b) • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L := by
    rw [hkey]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [smul_eq_C_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hxI m.1)) (hD m)
  have hpow : ∀ u ∈ Submonoid.powers F, eval t u ≠ 0 := by
    rintro u ⟨n, rfl⟩
    rw [map_pow]
    exact pow_ne_zero n ht
  have hVb : V * b ∈ Submonoid.powers F :=
    (Submonoid.powers F).mul_mem (Submonoid.prod_mem _ fun m _ => (c m).2) b.2
  exact GenericFibreTor.mem_of_smul_mem t L hxL (hpow _ hVb) hJ

end

end GroundTheory.Heights₂.Heights

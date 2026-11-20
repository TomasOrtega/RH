import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

section General

variable (F : Type) [Field F] [NumberField F]

abbrev mDiff (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors

/- English proof (translation)
Conclude with `differentIdeal_ne_bot`.
-/
lemma differentIdeal_ne_zero' : differentIdeal ℤ (𝓞 F) ≠ 0 := by
  exact differentIdeal_ne_bot

variable {F}

/- English proof (translation)
Establish `hD : Associates.mk (differentIdeal ℤ (𝓞 F)) ≠ 0` using `Associates.mk_ne_zero.mpr (differentIdeal_ne_zero' F)`. Establish `hirr : Irreducible (Associates.mk v.asIdeal)` using `Associates.irreducible_mk.mpr v.irreducible`. Rewrite using `[← Associates.mk_dvd_mk, Associates.mk_pow]`. Conclude with `(Associates.prime_pow_dvd_iff_le hD hirr).mpr le_rfl`.
-/
lemma pow_mDiff_dvd (v : HeightOneSpectrum (𝓞 F)) :
    v.asIdeal ^ mDiff F v ∣ differentIdeal ℤ (𝓞 F) := by
  have hD : Associates.mk (differentIdeal ℤ (𝓞 F)) ≠ 0 := Associates.mk_ne_zero.mpr (differentIdeal_ne_zero' F)
  have hirr : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  rw [← Associates.mk_dvd_mk, Associates.mk_pow]
  exact (Associates.prime_pow_dvd_iff_le hD hirr).mpr le_rfl

/- English proof (translation)
Establish `hD : Associates.mk (differentIdeal ℤ (𝓞 F)) ≠ 0` using `Associates.mk_ne_zero.mpr (differentIdeal_ne_zero' F)`. Establish `hirr : Irreducible (Associates.mk v.asIdeal)` using `Associates.irreducible_mk.mpr v.irreducible`. Introduce `h`. Rewrite `h` using `[← Associates.mk_dvd_mk, Associates.mk_pow]`. Use `(Associates.prime_pow_dvd_iff_le hD hirr).mp h` as an intermediate fact.

Conclude with `Nat.lt_irrefl _ (Nat.lt_of_succ_le this)`.
-/
lemma not_pow_succ_mDiff_dvd (v : HeightOneSpectrum (𝓞 F)) :
    ¬ v.asIdeal ^ (mDiff F v + 1) ∣ differentIdeal ℤ (𝓞 F) := by
  have hD : Associates.mk (differentIdeal ℤ (𝓞 F)) ≠ 0 := Associates.mk_ne_zero.mpr (differentIdeal_ne_zero' F)
  have hirr : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  intro h
  rw [← Associates.mk_dvd_mk, Associates.mk_pow] at h
  have := (Associates.prime_pow_dvd_iff_le hD hirr).mp h
  exact Nat.lt_irrefl _ (Nat.lt_of_succ_le this)

/- English proof (translation)
Rewrite using `[IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd]`. Conclude with `dvd_trans (pow_mDiff_dvd v) (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx))`.
-/
lemma intValuation_le_of_mem_different (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F}
    (hx : x ∈ differentIdeal ℤ (𝓞 F)) : v.intValuation x ≤ exp (-(mDiff F v : ℤ)) := by
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd]
  exact dvd_trans (pow_mDiff_dvd v) (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx))

/- English proof (translation)
Establish `hnot` using `not_pow_succ_mDiff_dvd v`. Rewrite `hnot` using `[Ideal.dvd_iff_le, SetLike.not_le_iff_exists]`. Take `⟨x, hxD, hxv⟩` from `hnot`. Use `⟨x, hxD, le_antisymm (intValuation_le_of_mem_different v hxD) ?_⟩` and prove the remaining obligations. Establish `h1 : ¬ v.intValuation x ≤ WithZero.exp (-((mDiff F v + 1 : ℕ) : ℤ))`.

Rewrite using `[IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hxv`. Establish `hx0 : v.intValuation x ≠ 0`. Introduce `h0`. Apply `h1` to reduce the goal to its premises.

Rewrite using `[h0]`. Conclude with `zero_le'`. Rewrite `h1`, the goal using `[← WithZero.exp_log hx0]`. Rewrite `h1`, the goal using `[WithZero.exp_le_exp]`. Move the coercions through the operations in `at h1`.

Use linear arithmetic over natural numbers and integers.
-/
lemma exists_mem_different_intValuation_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x ∈ differentIdeal ℤ (𝓞 F), v.intValuation x = exp (-(mDiff F v : ℤ)) := by
  have hnot := not_pow_succ_mDiff_dvd v
  rw [Ideal.dvd_iff_le, SetLike.not_le_iff_exists] at hnot
  obtain ⟨x, hxD, hxv⟩ := hnot
  refine ⟨x, hxD, le_antisymm (intValuation_le_of_mem_different v hxD) ?_⟩
  have h1 : ¬ v.intValuation x ≤ WithZero.exp (-((mDiff F v + 1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem]
    exact hxv
  have hx0 : v.intValuation x ≠ 0 := by
    intro h0
    apply h1
    rw [h0]
    exact zero_le'
  rw [← WithZero.exp_log hx0] at h1 ⊢
  rw [WithZero.exp_le_exp] at h1 ⊢
  push_cast at h1
  omega

/- English proof (translation)
Rewrite using `[← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := F)]`. Conclude with `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)`.
-/
lemma valued_algebraMap_coe (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := by
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)

/- English proof (translation)
Take `⟨x, hxD, hxv⟩` from `exists_mem_different_intValuation_eq v`. Establish `hex : ∃ d, IsDiffVal v d`. Use `⟨algebraMap F (Fv F v) (x : F), ?_, ?_, x, hxD, rfl⟩` and prove the remaining obligations. Introduce `h0`. Use `valued_algebraMap_coe v x` as an intermediate fact.

Rewrite `this` using `[h0, map_zero, hxv]`. Conclude with `WithZero.exp_ne_zero this.symm`. Introduce `y hy`. Rewrite using `[valued_algebraMap_coe, valued_algebraMap_coe, hxv]`. Conclude with `intValuation_le_of_mem_different v hy`.

Establish `hd : IsDiffVal v (dV v)`. Unfold `dV`. Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`. Take `⟨-, hle, y, hyD, hyv⟩` from `hd`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hyv, valued_algebraMap_coe]`. Conclude with `intValuation_le_of_mem_different v hyD`. Use `hle x hxD` as an intermediate fact. Rewrite `this` using `[valued_algebraMap_coe, hxv]`. Then use the resulting hypothesis.
-/
lemma valued_dV (v : HeightOneSpectrum (𝓞 F)) : Valued.v (dV v) = exp (-(mDiff F v : ℤ)) := by
  obtain ⟨x, hxD, hxv⟩ := exists_mem_different_intValuation_eq v
  have hex : ∃ d, IsDiffVal v d := by
    refine ⟨algebraMap F (Fv F v) (x : F), ?_, ?_, x, hxD, rfl⟩
    · intro h0
      have := valued_algebraMap_coe v x
      rw [h0, map_zero, hxv] at this
      exact WithZero.exp_ne_zero this.symm
    · intro y hy
      rw [valued_algebraMap_coe, valued_algebraMap_coe, hxv]
      exact intValuation_le_of_mem_different v hy
  have hd : IsDiffVal v (dV v) := by
    unfold dV
    rw [dif_pos hex]
    exact hex.choose_spec
  obtain ⟨-, hle, y, hyD, hyv⟩ := hd
  apply le_antisymm
  · rw [← hyv, valued_algebraMap_coe]
    exact intValuation_le_of_mem_different v hyD
  · have := hle x hxD
    rwa [valued_algebraMap_coe, hxv] at this

/- English proof (translation)
Establish `hx : Valued.v x ≠ 0`. Rewrite using `[h]`. Conclude with `WithZero.exp_ne_zero`. Unfold `absV`. Rewrite using `[dif_neg hx]`.

Use `congr 1`. Establish `hu : WithZero.unzero hx = Multiplicative.ofAdd n`. Apply `WithZero.coe_injective` to reduce the goal to its premises. Rewrite using `[WithZero.coe_unzero, h]`. Both sides reduce to the same expression.

Rewrite using `[hu, toAdd_ofAdd]`.
-/
lemma absV_of_valued_eq (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) (n : ℤ) (h : Valued.v x = exp n) :
    absV v x = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ n := by
  have hx : Valued.v x ≠ 0 := by
    rw [h]
    exact WithZero.exp_ne_zero
  unfold absV
  rw [dif_neg hx]
  congr 1
  have hu : WithZero.unzero hx = Multiplicative.ofAdd n := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  rw [hu, toAdd_ofAdd]

/- English proof (translation)
Rewrite using `[absV_of_valued_eq v _ _ (valued_dV v), IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow, zpow_neg, zpow_natCast, Nat.cast_pow]`.
-/
lemma absV_dV (v : HeightOneSpectrum (𝓞 F)) :
    absV v (dV v) = ((Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 F))) : ℕ) : ℝ)⁻¹ := by
  rw [absV_of_valued_eq v _ _ (valued_dV v), IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow,
    zpow_neg, zpow_natCast, Nat.cast_pow]

variable (F) in

/- English proof (translation)
Establish `hD` using `differentIdeal_ne_zero' F`. Establish `hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing (differentIdeal ℤ (𝓞 F))).Finite` using `Ideal.finite_mulSupport hD`. Establish `hfac : ∏ v ∈ hfin.toFinset, v.maxPowDividing (differentIdeal ℤ (𝓞 F)) = differentIdeal ℤ (𝓞 F)`. Rewrite using `[← finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hfin.mem_toFinset.mpr hv)]`. Conclude with `Ideal.finprod_heightOneSpectrum_factorization hD`.

Establish `hone : ∀ v ∉ hfin.toFinset, absV v (dV v) = 1`. Introduce `v hv`. Rewrite using `[absV_dV]`. Establish `h1 : v.maxPowDividing (differentIdeal ℤ (𝓞 F)) = 1`. Assume the negation of the conclusion as `hc`.

Conclude with `hv (hfin.mem_toFinset.mpr hc)`. Rewrite using `[h1, map_one]`. Simplify using the standard rewrite rules. Establish `hval : ∏ v ∈ hfin.toFinset, absV v (dV v) = |(discr F : ℝ)|⁻¹`. Rewrite using `[Finset.prod_congr rfl (fun v _ => absV_dV v), Finset.prod_inv_distrib, ← Nat.cast_prod, ← map_prod, hfac, NumberField.absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, Int.cast_abs]`.

Establish `key : HasProd (fun v : HeightOneSpectrum (𝓞 F) => absV v (dV v)) (∏ v ∈ hfin.toFinset, absV v (dV v))` using `hasProd_prod_of_ne_finset_one hone`. Rewrite `key` using `[hval]`. Conclude with `key`.
-/
theorem hasProd_absV_dV :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => absV v (dV v)) (|(discr F : ℝ)|⁻¹) := by
  have hD := differentIdeal_ne_zero' F
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      v.maxPowDividing (differentIdeal ℤ (𝓞 F))).Finite := Ideal.finite_mulSupport hD
  have hfac : ∏ v ∈ hfin.toFinset, v.maxPowDividing (differentIdeal ℤ (𝓞 F)) = differentIdeal ℤ (𝓞 F) := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hfin.mem_toFinset.mpr hv)]
    exact Ideal.finprod_heightOneSpectrum_factorization hD
  have hone : ∀ v ∉ hfin.toFinset, absV v (dV v) = 1 := by
    intro v hv
    rw [absV_dV]
    have h1 : v.maxPowDividing (differentIdeal ℤ (𝓞 F)) = 1 := by
      by_contra hc
      exact hv (hfin.mem_toFinset.mpr hc)
    rw [h1, map_one]
    simp
  have hval : ∏ v ∈ hfin.toFinset, absV v (dV v) = |(discr F : ℝ)|⁻¹ := by
    rw [Finset.prod_congr rfl (fun v _ => absV_dV v), Finset.prod_inv_distrib, ← Nat.cast_prod, ← map_prod, hfac,
      NumberField.absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, Int.cast_abs]
  have key : HasProd (fun v : HeightOneSpectrum (𝓞 F) => absV v (dV v)) (∏ v ∈ hfin.toFinset, absV v (dV v)) :=
    hasProd_prod_of_ne_finset_one hone
  rw [hval] at key
  exact key

end General

section Loc

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Conclude with `hasProd_absV_dV _`.
-/
theorem diffProd_holds : DiffProd X := by
  exact hasProd_absV_dV _

end Loc

end Formalism.L2.SG.Pf.NcVal

import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Rewrite using `[MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `d hd`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, d s ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hd (Finsupp.ext h)`. Establish `hs' : s ∈ d.support` using `Finsupp.mem_support_iff.2 hs`. Rewrite using `[Finsupp.prod, map_prod, Finset.prod_eq_zero hs']`. Simplify using the standard rewrite rules.

Rewrite using `[map_pow, h0 s, zero_pow hs]`.
-/
theorem cc_subst {σ τ R : Type} [CommRing R] {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  classical
  rw [MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (Finsupp.ext h)
    have hs' : s ∈ d.support := Finsupp.mem_support_iff.2 hs
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero hs']
    · simp
    · rw [map_pow, h0 s, zero_pow hs]

/- English proof (translation)
Use `show expS p f 0 = 1`. Simplify using `[expS]`.
-/
theorem cc_expS {ι : Type} (f : MvPowerSeries ι (K0 p)) : MvPowerSeries.constantCoeff (expS p f) = 1 := by
  show expS p f 0 = 1
  simp [expS]

/- English proof (translation)
Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `[logF, PowerSeries.coeff_mk]`.
-/
theorem cc_logF : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logF, PowerSeries.coeff_mk]

/- English proof (translation)
Use `PowerSeries.constantCoeff_subst_eq_zero (by simp) _ ?_` and prove the remaining obligations. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_logF, map_zero]`.
-/
theorem cc_logX {ι : Type} (K1 : Type) [Field K1] [Algebra (K0 p) K1] (i : ι) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) = 0 := by
  refine PowerSeries.constantCoeff_subst_eq_zero (by simp) _ ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_logF, map_zero]

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_logX K1)`.
-/
theorem hasSubst_logX {ι : Type} [Finite ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] :
    MvPowerSeries.HasSubst (fun i : ι => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_logX K1)

/- English proof (translation)
Establish `h0 : ∀ i : ι, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1) (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) = 0`. Introduce `i`. Use `PowerSeries.constantCoeff_subst_eq_zero (by simp) _ ?_` and prove the remaining obligations. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_logF, map_zero]`. Conclude with `cc_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0 f`.
-/
theorem cc_inParamK {ι : Type} [Finite ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] (f : MvPowerSeries ι K1) :
    MvPowerSeries.constantCoeff (inParamK p K1 f) = MvPowerSeries.constantCoeff f := by
  have h0 : ∀ i : ι, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) = 0 := by
    intro i
    refine PowerSeries.constantCoeff_subst_eq_zero (by simp) _ ?_
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_logF, map_zero]
  exact cc_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0 f

/- English proof (translation)
Take `⟨Ph, U, hTh, hU, -⟩` from `h`. Establish `hU0` using `hU 0`. Rewrite `hU0` using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_inParamK]`. Rewrite using `[hTh, map_mul, MvPowerSeries.constantCoeff_map, cc_expS, map_one, one_mul]`. Conclude with `hU0`.
-/
theorem cc_mem_of_K1gen {ι : Type} [Fintype ι] {K1 : Type} [Field K1] [Algebra (K0 p) K1] {R1 : Subring K1}
    {be : MvPowerSeries (Fin 2) (K0 p)} {Th : MvPowerSeries (ι ⊕ ι) K1} (h : ExtensionGeneratorCondition p K1 R1 be Th) :
    MvPowerSeries.constantCoeff Th ∈ R1 := by
  obtain ⟨Ph, U, hTh, hU, -⟩ := h
  have hU0 := hU 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_inParamK] at hU0
  rw [hTh, map_mul, MvPowerSeries.constantCoeff_map, cc_expS, map_one, one_mul]
  exact hU0

/- English proof (translation)
The claim follows from `cc_mem_of_K1gen (ι := Eidx n' r0 r1) h`.
-/
theorem cc_mem_of_K1loc {n' r0 r1 : ℕ} {K1 : Type} [Field K1] [Algebra (K0 p) K1] {R1 : Subring K1}
    {be : MvPowerSeries (Fin 2) (K0 p)} {Th : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1}
    (h : ExtensionLocalCondition p K1 R1 be Th) : MvPowerSeries.constantCoeff Th ∈ R1 :=
  cc_mem_of_K1gen (ι := Eidx n' r0 r1) h

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

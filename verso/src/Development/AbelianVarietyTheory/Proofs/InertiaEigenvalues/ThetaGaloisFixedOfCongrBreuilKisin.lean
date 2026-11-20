import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

/- English proof (translation)
Introduce `l _ K bk x M k s h g`. Take `⟨C⟩` from `GlobalTheory.MemLoc.nonempty_core l`. Take `⟨hfil, -⟩` from `GlobalTheory.MemLoc.seed_fil l C (bk.ev bk.E) bk.span_ev`. Take `⟨-, hker, -, hth, -⟩` from `GlobalTheory.MemLoc.thetaD_props l`. Use `haveI : IsDomain (Per.BdRp l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).1`.

Use `haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)`. Use `set ξ := aDp l (bk.ev bk.E) with hξ`. Establish `hξ0 : ξ ≠ 0`. Introduce `h0`. Establish `h2 : aDp l (bk.ev bk.E) ∈ Per.FilP l 2`.

Rewrite using `[hfil, ← hξ, h0]`. Conclude with `zero_mem _`. Establish `h3` using `((GlobalTheory.AinfEPow.ePow_facts l K bk 2).2.2.1 _).1 h2`. Take `⟨c, hc⟩` from `h3`. Establish `hE` using `GlobalTheory.AinfEPow.evE_ne_zero bk`.

Establish `h4 : bk.ev bk.E * 1 = bk.ev bk.E * (bk.ev bk.E * c)` using `by rw [mul_one]; nth_rewrite 1 [hc]; ring`. Establish `h5` using `mul_left_cancel₀ hE h4`. Establish `h6` using `congrArg (Per.θ l) h5`. Establish `h7 : Per.θ l (bk.ev bk.E) = 0`. Rewrite using `[← RingHom.mem_ker, ← bk.span_ev]`.

Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `h6` using `[map_one, map_mul, h7, zero_mul]`. Conclude with `one_ne_zero h6`. Establish `hsM : aDp l (bk.ev s) ∈ Per.FilP l M`. Establish `h1 : (l : Per.BdRp l) ^ k * ξ ^ M * x ∈ Per.FilP l M`.

Rewrite using `[hfil, Ideal.mem_span_singleton]; exact ⟨(l : Per.BdRp l) ^ k * x, by ring⟩`. Establish `h2 : (l : Per.BdRp l) ^ k * ξ ^ M * x - aDp l (bk.ev s) ∈ Per.FilP l M`. Rewrite `h`, the goal using `[hfil]`. Rewrite `h`, the goal using `[Ideal.mem_span_singleton]`. Conclude with `(pow_dvd_pow _ (Nat.le_succ M)).trans h`.

Use `Ideal.sub_mem _ h1 h2` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Take `⟨s', hs'⟩` from `(GlobalTheory.AinfEPow.ePow_facts l K bk M).2.1 s (((GlobalTheory.AinfEPow.ePow_facts l K bk M).2.2.1 _).1 hsM)`. Establish `hdiff : (l : Per.BdRp l) ^ k * x - aDp l (bk.ev s') ∈ Per.FilP l 1`. Rewrite using `[hfil, pow_one, Ideal.mem_span_singleton]`.

Establish `h'` using `h`. Rewrite `h'` using `[hfil, Ideal.mem_span_singleton, hs', map_mul, map_mul, map_pow, map_pow, ← hξ]`. Take `⟨y, hy⟩` from `h'`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `e : ξ ^ M * ((l : Per.BdRp l) ^ k * x - aDp l (bk.ev s')) = ξ ^ M * (ξ * y)`.

Rewrite using `[← mul_assoc, ← pow_succ, ← hy]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ (pow_ne_zero M hξ0) e`. Rewrite `hdiff` using `[← hker, map_sub, sub_eq_zero, map_mul, map_pow, map_natCast, hth, bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ s')) s' (bk.str.apply_symm_apply _).symm]`. Establish `hfix : Per.σC (g : GQ l) ((intToOC K (bk.str.symm (Ideal.Quotient.mk _ s')) : OC l) : ℂ_[l]) = ((intToOC K (bk.str.symm (Ideal.Quotient.mk _ s')) : OC l) : ℂ_[l])`.

Rewrite using `[coe_intToOC]`. Conclude with `(GlobalTheory.RingBasics.σC_coe (g : GQ l) _).trans (congrArg _ ((IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (_ : ↥K.1).2))`. Establish `hl : ((l : ℂ_[l]) ^ k) ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Apply `mul_left_cancel₀ hl` to reduce the goal to its premises. Establish `e2` using `congrArg (Per.σC (g : GQ l)) hdiff`.

Rewrite `e2` using `[map_mul, map_pow, map_natCast, hfix, ← hdiff]`. Conclude with `e2`.
-/
theorem GlobalTheory.BKLim.theta_gal_fixed_of_congr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Per.BdRp l) (M k : ℕ) (s : bk.S), (l : Per.BdRp l) ^ k * aDp l (bk.ev bk.E) ^ M * x - aDp l (bk.ev s) ∈ Per.FilP l (M + 1) → ∀ g : ↥(GK K), Per.σC (g : GQ l) (Per.θD l x) = Per.θD l x := by
  intro l _ K bk x M k s h g
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  obtain ⟨hfil, -⟩ := GlobalTheory.MemLoc.seed_fil l C (bk.ev bk.E) bk.span_ev
  obtain ⟨-, hker, -, hth, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  haveI : IsDomain (Per.BdRp l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).1
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  set ξ := aDp l (bk.ev bk.E) with hξ

  have hξ0 : ξ ≠ 0 := by
    intro h0
    have h2 : aDp l (bk.ev bk.E) ∈ Per.FilP l 2 := by
      rw [hfil, ← hξ, h0]; exact zero_mem _
    have h3 := ((GlobalTheory.AinfEPow.ePow_facts l K bk 2).2.2.1 _).1 h2
    obtain ⟨c, hc⟩ := h3
    have hE := GlobalTheory.AinfEPow.evE_ne_zero bk
    have h4 : bk.ev bk.E * 1 = bk.ev bk.E * (bk.ev bk.E * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
    have h5 := mul_left_cancel₀ hE h4
    have h6 := congrArg (Per.θ l) h5
    have h7 : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [map_one, map_mul, h7, zero_mul] at h6
    exact one_ne_zero h6

  have hsM : aDp l (bk.ev s) ∈ Per.FilP l M := by
    have h1 : (l : Per.BdRp l) ^ k * ξ ^ M * x ∈ Per.FilP l M := by
      rw [hfil, Ideal.mem_span_singleton]; exact ⟨(l : Per.BdRp l) ^ k * x, by ring⟩
    have h2 : (l : Per.BdRp l) ^ k * ξ ^ M * x - aDp l (bk.ev s) ∈ Per.FilP l M := by
      rw [hfil] at h ⊢
      rw [Ideal.mem_span_singleton] at h ⊢
      exact (pow_dvd_pow _ (Nat.le_succ M)).trans h
    have := Ideal.sub_mem _ h1 h2
    rwa [sub_sub_cancel] at this
  obtain ⟨s', hs'⟩ := (GlobalTheory.AinfEPow.ePow_facts l K bk M).2.1 s (((GlobalTheory.AinfEPow.ePow_facts l K bk M).2.2.1 _).1 hsM)

  have hdiff : (l : Per.BdRp l) ^ k * x - aDp l (bk.ev s') ∈ Per.FilP l 1 := by
    rw [hfil, pow_one, Ideal.mem_span_singleton]
    have h' := h
    rw [hfil, Ideal.mem_span_singleton, hs', map_mul, map_mul, map_pow, map_pow, ← hξ] at h'
    obtain ⟨y, hy⟩ := h'
    refine ⟨y, ?_⟩
    have e : ξ ^ M * ((l : Per.BdRp l) ^ k * x - aDp l (bk.ev s')) = ξ ^ M * (ξ * y) := by
      rw [← mul_assoc, ← pow_succ, ← hy]; ring
    exact mul_left_cancel₀ (pow_ne_zero M hξ0) e
  rw [← hker, map_sub, sub_eq_zero, map_mul, map_pow, map_natCast, hth,
    bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ s')) s' (bk.str.apply_symm_apply _).symm] at hdiff
  have hfix : Per.σC (g : GQ l) ((intToOC K (bk.str.symm (Ideal.Quotient.mk _ s')) : OC l) : ℂ_[l]) =
      ((intToOC K (bk.str.symm (Ideal.Quotient.mk _ s')) : OC l) : ℂ_[l]) := by
    rw [coe_intToOC]
    exact (GlobalTheory.RingBasics.σC_coe (g : GQ l) _).trans (congrArg _
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (_ : ↥K.1).2))
  have hl : ((l : ℂ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  apply mul_left_cancel₀ hl
  have e2 := congrArg (Per.σC (g : GQ l)) hdiff
  rw [map_mul, map_pow, map_natCast, hfix, ← hdiff] at e2
  exact e2

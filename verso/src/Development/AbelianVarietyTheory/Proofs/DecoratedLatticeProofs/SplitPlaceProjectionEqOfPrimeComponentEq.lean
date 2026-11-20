import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharTrivialOnIdempotentIntegralUnits
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SplitProj

open Formalism.IndefR.Datum Formalism.L2.Theta

section Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Use `set r : v.adicCompletion F := algebraMap F _ (π ^ n) with hr_def`. Establish `hr : Valued.v r = WithZero.exp (-(n : ℤ))`. Rewrite using `[hr_def]`. Use `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (π ^ n)).trans ?_` and prove the remaining obligations.

Rewrite using `[map_pow, hπ]`. Rewrite using `[← WithZero.exp_nsmul]`. Use `congr 1`. Simplify using the standard rewrite rules. Establish `hr0 : Valued.v r ≠ 0` using `by rw [hr]; exact WithZero.exp_ne_zero`.

Establish `hN : {y : v.adicCompletion F | Valued.v (c - y) < Valued.v r} ∈ nhds c`. Establish `ho` using `(Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict r)).preimage (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => c - y)`. Simplify using `only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff] at ho`. Use `ho.mem_nhds ?_` and prove the remaining obligations. Use `show Valued.v (c - c) < _`.

Rewrite using `[sub_self, map_zero]`. Conclude with `zero_lt_iff.2 hr0`. Take `⟨k, hk⟩` from `(HeightOneSpectrum.denseRange_algebraMap (K := F) v).mem_nhds hN`. Conclude with `⟨k, (le_of_lt hk).trans_eq hr⟩`.
-/
theorem exists_near (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) (n : ℕ) :
    ∃ k : F, Valued.v (c - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set r : v.adicCompletion F := algebraMap F _ (π ^ n) with hr_def
  have hr : Valued.v r = WithZero.exp (-(n : ℤ)) := by
    rw [hr_def]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (π ^ n)).trans ?_
    rw [map_pow, hπ]
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  have hr0 : Valued.v r ≠ 0 := by rw [hr]; exact WithZero.exp_ne_zero
  have hN : {y : v.adicCompletion F | Valued.v (c - y) < Valued.v r} ∈ nhds c := by
    have ho := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict r)).preimage
      (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => c - y)
    simp only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (c - c) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hr0
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).mem_nhds hN
  exact ⟨k, (le_of_lt hk).trans_eq hr⟩

/- English proof (translation)
Establish `key : ∀ n : ℕ, Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≤ WithZero.exp (-(n : ℤ))` using `fun n => by`. Take `⟨k, hk⟩` from `exists_near (P.under (𝓞 F)) (a (P.under (𝓞 F))) n`. Establish `h1` using `(GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 a k P n hk`. Establish `h2 : Valued.v (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ))`. Rewrite using `[GlobalTheory.AdeleBaseChange.adMap_apply, ← GlobalTheory.AdeleBaseChange.locMap_algebraMap, ← map_sub]`.

Conclude with `GlobalTheory.AdeleBaseChange.locMap_valued P n _ hk`. Establish `e : GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P = (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) - (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k))` using `by ring`. Rewrite using `[e]`. Conclude with `(Valuation.map_sub _ _ _).trans (max_le h1 h2)`. Assume the negation of the conclusion as `hne`.

Establish `h0 : Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `sub_ne_zero.2 hne`. Establish `h2` using `key (1 - WithZero.log (Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P))).toNat`. Use `conv_lhs at h2 => rw [← WithZero.exp_log h0]`.

Rewrite `h2` using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem afIso_one_tmul_apply (a : FiniteAdeleRing (𝓞 F) F) (P : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P = GlobalTheory.AdeleBaseChange.adMap F E a P := by
  have key : ∀ n : ℕ, Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≤
      WithZero.exp (-(n : ℤ)) := fun n => by
    obtain ⟨k, hk⟩ := exists_near (P.under (𝓞 F)) (a (P.under (𝓞 F))) n
    have h1 := (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 a k P n hk
    have h2 : Valued.v (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k)) ≤
        WithZero.exp (-(n : ℤ)) := by
      rw [GlobalTheory.AdeleBaseChange.adMap_apply, ← GlobalTheory.AdeleBaseChange.locMap_algebraMap, ← map_sub]
      exact GlobalTheory.AdeleBaseChange.locMap_valued P n _ hk
    have e : GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P =
        (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) -
          (GlobalTheory.AdeleBaseChange.adMap F E a P - algebraMap E _ (algebraMap F E k)) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le h1 h2)
  by_contra hne
  have h0 : Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P - GlobalTheory.AdeleBaseChange.adMap F E a P) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact sub_ne_zero.2 hne
  have h2 := key (1 - WithZero.log (Valued.v (GlobalTheory.Mem.Col2.afIso F E (1 ⊗ₜ[F] a) P -
    GlobalTheory.AdeleBaseChange.adMap F E a P))).toNat
  conv_lhs at h2 => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp] at h2
  omega

end Base

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul x a`. Rewrite using `[GlobalTheory.StdFrames.toAd_spec]`. Establish `e : (x ⊗ₜ[D.host.F] a : Formalism.L2.DIV.AfE D.host.F D.host.E) = (x ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[e, map_mul, GlobalTheory.Mem.Col2.afIso_tmul_one]`. Use `congr 1`. Conclude with `FiniteAdeleRing.ext _ fun P => (afIso_one_tmul_apply a P).symm`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem toAd_eq_afIso (w : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D) :
    GlobalTheory.StdFrames.toAd D w = GlobalTheory.Mem.Col2.afIso D.host.F D.host.E w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x a =>
    rw [GlobalTheory.StdFrames.toAd_spec]
    have e : (x ⊗ₜ[D.host.F] a : Formalism.L2.DIV.AfE D.host.F D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, GlobalTheory.Mem.Col2.afIso_tmul_one]
    congr 1
    exact FiniteAdeleRing.ext _ fun P => (afIso_one_tmul_apply a P).symm
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Use `show Formalism.UG.evalV D.host.E Q (GlobalTheory.StdFrames.toAd D w) = Formalism.UG.evalV D.host.E Q (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E w)`. Rewrite using `[toAd_eq_afIso]`.
-/
theorem cpt_eq_adAt (Q : HeightOneSpectrum (𝓞 D.host.E)) (w : GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Ef D) :
    GlobalTheory.StdFrames.cpt Q w = GlobalTheory.Mem.Col2.adAt D.host.F Q w := by
  show Formalism.UG.evalV D.host.E Q (GlobalTheory.StdFrames.toAd D w) = Formalism.UG.evalV D.host.E Q (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E w)
  rw [toAd_eq_afIso]

/- English proof (translation)
Introduce `D k _ _ _ _ q PP he z x hz`. Establish `hx : GlobalTheory.StdFrames.cpt PP (toEAf D (incA D x)) = algebraMap D.host.E (PP.adicCompletion D.host.E) x` using `(cpt_eq_adAt PP _).trans (GlobalTheory.Mem.Col2.adAt_inclE D.host.F PP x)`. Establish `hz' : GlobalTheory.StdFrames.cpt PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x` using `(cpt_eq_adAt PP _).trans hz`. Establish `h1 : toEAf D (q.e * z) = toEAf D (q.e * incA D x)`. Rewrite using `[RingHom.map_mul, RingHom.map_mul]`.

Use `GlobalTheory.StdFrames.cpt_ext fun Q => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_mul, RingHom.map_mul]`. Distinguish the cases in `hQ : Q = PP`. Rewrite using `[hQ, hx, hz']`. Rewrite using `[(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 Q hQ, zero_mul, zero_mul]`.

Establish `h2 : q.pr (q.e * z - q.e * incA D x) = 0` using `q.pr_eq_zero_of_toEAf he _ (by rw [RingHom.map_sub, h1, sub_self])`. Rewrite `h2` using `[RingHom.map_sub, sub_eq_zero, ← q.sec_pr, ← q.sec_pr, q.pr_sec, q.pr_sec]`. Conclude with `h2`.
-/
theorem pr_eq_of_adAt : ∀ {D : Formalism.BasicNotions.D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (z : Formalism.L2.Theta.AE D) (x : D.host.E), GlobalTheory.Mem.Col2.adAt D.host.F PP (Formalism.IndefR.Datum.toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x → q.pr z = q.pr (Formalism.L2.Theta.incA D x) := by
  intro D k _ _ _ _ q PP he z x hz
  have hx : GlobalTheory.StdFrames.cpt PP (toEAf D (incA D x)) = algebraMap D.host.E (PP.adicCompletion D.host.E) x :=
    (cpt_eq_adAt PP _).trans (GlobalTheory.Mem.Col2.adAt_inclE D.host.F PP x)
  have hz' : GlobalTheory.StdFrames.cpt PP (toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x :=
    (cpt_eq_adAt PP _).trans hz
  have h1 : toEAf D (q.e * z) = toEAf D (q.e * incA D x) := by
    rw [RingHom.map_mul, RingHom.map_mul]
    refine GlobalTheory.StdFrames.cpt_ext fun Q => ?_
    rw [RingHom.map_mul, RingHom.map_mul]
    by_cases hQ : Q = PP
    · rw [hQ, hx, hz']
    · rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 Q hQ, zero_mul, zero_mul]
  have h2 : q.pr (q.e * z - q.e * incA D x) = 0 :=
    q.pr_eq_zero_of_toEAf he _ (by rw [RingHom.map_sub, h1, sub_self])
  rw [RingHom.map_sub, sub_eq_zero, ← q.sec_pr, ← q.sec_pr, q.pr_sec, q.pr_sec] at h2
  exact h2

end GlobalTheory.SplitProj

end

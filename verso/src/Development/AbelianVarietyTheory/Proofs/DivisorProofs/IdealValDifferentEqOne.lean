import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

noncomputable section

namespace GlobalTheory.CMTorsionTangent

open Filter Topology

def locZ (Λ : PeriodPair) (Ω t : ℂ) : ℂ :=
  2 * Ω * (t + t ^ 3 * Λ.weierstrassPExcept 0 t) / (2 - t ^ 3 * Λ.derivWeierstrassPExcept 0 t)

def locW (Λ : PeriodPair) (Ω t : ℂ) : ℂ :=
  2 * Ω ^ 3 * t ^ 3 / (2 - t ^ 3 * Λ.derivWeierstrassPExcept 0 t)

/- English proof (translation)
Establish `hc : ContinuousAt (fun t : ℂ => 2 - t ^ 3 * Λ.derivWeierstrassPExcept 0 t) 0` using `continuousAt_const.sub ((continuousAt_id.pow 3).mul (Λ.analyticAt_derivWeierstrassPExcept 0).continuousAt)`. Conclude with `hc.eventually_ne (by simp)`.
-/
theorem eventually_den_ne (Λ : PeriodPair) :
    ∀ᶠ t in 𝓝 (0 : ℂ), 2 - t ^ 3 * Λ.derivWeierstrassPExcept 0 t ≠ 0 := by
  have hc : ContinuousAt (fun t : ℂ => 2 - t ^ 3 * Λ.derivWeierstrassPExcept 0 t) 0 :=
    continuousAt_const.sub ((continuousAt_id.pow 3).mul (Λ.analyticAt_derivWeierstrassPExcept 0).continuousAt)
  exact hc.eventually_ne (by simp)

/- English proof (translation)
Establish `hP` using `(Λ.analyticAt_weierstrassPExcept 0).differentiableAt.hasDerivAt`. Establish `hP'` using `(Λ.analyticAt_derivWeierstrassPExcept 0).differentiableAt.hasDerivAt`. Establish `hn` using `((hasDerivAt_id (0 : ℂ)).add ((hasDerivAt_pow 3 (0 : ℂ)).mul hP)).const_mul (2 * Ω)`. Establish `hd` using `(hasDerivAt_const (0 : ℂ) (2 : ℂ)).sub ((hasDerivAt_pow 3 (0 : ℂ)).mul hP')`. Use `((hn.div hd (by simp)).congr_deriv (by simp; ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Simplify using `[locZ]`.
-/
theorem hasDerivAt_locZ (Λ : PeriodPair) (Ω : ℂ) : HasDerivAt (locZ Λ Ω) Ω 0 := by
  have hP := (Λ.analyticAt_weierstrassPExcept 0).differentiableAt.hasDerivAt
  have hP' := (Λ.analyticAt_derivWeierstrassPExcept 0).differentiableAt.hasDerivAt
  have hn := ((hasDerivAt_id (0 : ℂ)).add ((hasDerivAt_pow 3 (0 : ℂ)).mul hP)).const_mul (2 * Ω)
  have hd := (hasDerivAt_const (0 : ℂ) (2 : ℂ)).sub ((hasDerivAt_pow 3 (0 : ℂ)).mul hP')
  refine ((hn.div hd (by simp)).congr_deriv (by simp; ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => ?_)
  simp [locZ]

/- English proof (translation)
Establish `hP'` using `(Λ.analyticAt_derivWeierstrassPExcept 0).differentiableAt.hasDerivAt`. Establish `hn` using `(hasDerivAt_pow 3 (0 : ℂ)).const_mul (2 * Ω ^ 3)`. Establish `hd` using `(hasDerivAt_const (0 : ℂ) (2 : ℂ)).sub ((hasDerivAt_pow 3 (0 : ℂ)).mul hP')`. Use `((hn.div hd (by simp)).congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `[locW]`.
-/
theorem hasDerivAt_locW (Λ : PeriodPair) (Ω : ℂ) : HasDerivAt (locW Λ Ω) 0 0 := by
  have hP' := (Λ.analyticAt_derivWeierstrassPExcept 0).differentiableAt.hasDerivAt
  have hn := (hasDerivAt_pow 3 (0 : ℂ)).const_mul (2 * Ω ^ 3)
  have hd := (hasDerivAt_const (0 : ℂ) (2 : ℂ)).sub ((hasDerivAt_pow 3 (0 : ℂ)).mul hP')
  refine ((hn.div hd (by simp)).congr_deriv (by simp)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => ?_)
  simp [locW]

/- English proof (translation)
Use `filter_upwards [eventually_den_ne Λ, Λ.compl_lattice_sdiff_singleton_mem_nhds 0] with t hden hlat`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc, e⟩ : ∃ c : ℂ, IsUnit c ∧ ![locZ Λ Ω t, -1, locW Λ Ω t] = c • coords Λ Ω t := by`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Use `⟨-1, isUnit_one.neg, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `ext i; fin_cases i <;> simp [coords, locZ, locW]`. Establish `hl : t ∉ Λ.lattice` using `fun h => hlat ⟨h, ht⟩`. Establish `hP` using `Λ.weierstrassPExcept_def 0 t`. Establish `hP'` using `Λ.derivWeierstrassPExcept_def 0 t`. Simplify using `only [ZeroMemClass.coe_zero, sub_zero, div_zero, zero_sub] at hP hP'`.

Establish `hd : Λ.derivWeierstrassP t ≠ 0`. Introduce `h0`. Apply `hden` to reduce the goal to its premises. Rewrite using `[hP', h0]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Use `⟨-(2 * Ω ^ 3 / Λ.derivWeierstrassP t), (neg_ne_zero.2 (div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 3 hΩ)) hd)).isUnit, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Use `fin_cases i`. Simplify using `[coords, hl, locZ]`.

Rewrite using `[hP, hP']`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `[coords, hl]`. Clear the denominators using the available nonvanishing facts.

Simplify using `[coords, hl, locW]`. Rewrite using `[hP']`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `isUnimodularSol_coords Λ Ω t`.

Use `⟨e ▸ h0.smul hc, ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.WeierstrassCurve.ptHom_smul _ _ _ h0 hc).symm.trans (GlobalTheory.WeierstrassCurve.ptHom_congr _ _ _ _ rfl e.symm _)`.
-/
theorem pt_eq_ptHom (Λ : PeriodPair) {Ω : ℂ} (hΩ : Ω ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℂ), ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((curve Λ Ω).map (RingHom.id ℂ))
      ![locZ Λ Ω t, -1, locW Λ Ω t],
      pt Λ Ω t = GlobalTheory.WeierstrassCurve.ptHom (curve Λ Ω) (RingHom.id ℂ) _ h := by
  filter_upwards [eventually_den_ne Λ, Λ.compl_lattice_sdiff_singleton_mem_nhds 0] with t hden hlat
  obtain ⟨c, hc, e⟩ : ∃ c : ℂ, IsUnit c ∧ ![locZ Λ Ω t, -1, locW Λ Ω t] = c • coords Λ Ω t := by
    by_cases ht : t = 0
    · subst ht
      refine ⟨-1, isUnit_one.neg, ?_⟩
      ext i; fin_cases i <;> simp [coords, locZ, locW]
    · have hl : t ∉ Λ.lattice := fun h => hlat ⟨h, ht⟩
      have hP := Λ.weierstrassPExcept_def 0 t
      have hP' := Λ.derivWeierstrassPExcept_def 0 t
      simp only [ZeroMemClass.coe_zero, sub_zero, div_zero, zero_sub] at hP hP'
      have hd : Λ.derivWeierstrassP t ≠ 0 := by
        intro h0
        apply hden
        rw [hP', h0]
        field_simp
        ring
      refine ⟨-(2 * Ω ^ 3 / Λ.derivWeierstrassP t), (neg_ne_zero.2 (div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 3 hΩ)) hd)).isUnit, ?_⟩
      ext i; fin_cases i
      · simp [coords, hl, locZ]
        rw [hP, hP']
        field_simp
        ring
      · simp [coords, hl]
        field_simp
      · simp [coords, hl, locW]
        rw [hP']
        field_simp
        ring
  have h0 := isUnimodularSol_coords Λ Ω t
  refine ⟨e ▸ h0.smul hc, ?_⟩
  exact (GlobalTheory.WeierstrassCurve.ptHom_smul _ _ _ h0 hc).symm.trans
    (GlobalTheory.WeierstrassCurve.ptHom_congr _ _ _ _ rfl e.symm _)

end GlobalTheory.CMTorsionTangent

namespace GlobalTheory.CMTorsionTangent

open Filter Topology
open GlobalTheory.WeierstrassCurve (ptHom OriginRing originEval originZ originW chartY coordOpen originPolynomial)

variable (Λ : PeriodPair) (Ω : ℂ)

def epsEval (c : ℂ) : OriginRing (curve Λ Ω) →+* DualNumber ℂ :=
  originEval (curve Λ Ω) (algebraMap ℂ (DualNumber ℂ)) (c • DualNumber.eps) 0
    (isUnimodularSol_tan (curve Λ Ω) c).equation

open Classical in

def locEval (t : ℂ) (r : OriginRing (curve Λ Ω)) : ℂ :=
  if h : ((curve Λ Ω).map (RingHom.id ℂ)).toProjective.Equation ![locZ Λ Ω t, -1, locW Λ Ω t] then
    originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h r else 0

/- English proof (translation)
Establish `: (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsEval Λ Ω c) = originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h0`. Apply the tactic sequence `refine GlobalTheory.WeierstrassCurve.origin_hom_ext _ (fun a => ?_) ?_ ?_ <;>`. Simplify using `[epsEval, locZ, locW]`. Conclude with `congrArg (fun φ : OriginRing (curve Λ Ω) →+* ℂ => φ r) this`.
-/
theorem epsEval_fst (c : ℂ) (r : OriginRing (curve Λ Ω)) (h0 : ((curve Λ Ω).map (RingHom.id ℂ)).toProjective.Equation
    ![locZ Λ Ω 0, -1, locW Λ Ω 0]) :
    (epsEval Λ Ω c r).fst = originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h0 r := by
  have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsEval Λ Ω c) =
      originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h0 := by
    refine GlobalTheory.WeierstrassCurve.origin_hom_ext _ (fun a => ?_) ?_ ?_ <;>
      simp [epsEval, locZ, locW]
  exact congrArg (fun φ : OriginRing (curve Λ Ω) →+* ℂ => φ r) this

/- English proof (translation)
Establish `: (epsScaleR c).comp (epsEval Λ Ω 1) = epsEval Λ Ω c`. Apply the tactic sequence `refine GlobalTheory.WeierstrassCurve.origin_hom_ext _ (fun a => ?_) ?_ ?_ <;>`. Simplify using `[epsEval, epsScaleR]`. Conclude with `TrivSqZeroExt.ext (by simp) (by simp)`. Rewrite using `[← this]`.

Simplify using `[epsScaleR]`.
-/
theorem epsEval_snd (c : ℂ) (r : OriginRing (curve Λ Ω)) :
    (epsEval Λ Ω c r).snd = c * (epsEval Λ Ω 1 r).snd := by
  have : (epsScaleR c).comp (epsEval Λ Ω 1) = epsEval Λ Ω c := by
    refine GlobalTheory.WeierstrassCurve.origin_hom_ext _ (fun a => ?_) ?_ ?_ <;>
      simp [epsEval, epsScaleR]
    exact TrivSqZeroExt.ext (by simp) (by simp)
  rw [← this]
  simp [epsScaleR]

variable {Λ Ω}

/- English proof (translation)
Use `filter_upwards [pt_eq_ptHom Λ hΩ] with t ⟨h, _⟩`. Conclude with `h.equation`.
-/
theorem eventually_equation (hΩ : Ω ≠ 0) : ∀ᶠ t in 𝓝 (0 : ℂ),
    ((curve Λ Ω).map (RingHom.id ℂ)).toProjective.Equation ![locZ Λ Ω t, -1, locW Λ Ω t] := by
  filter_upwards [pt_eq_ptHom Λ hΩ] with t ⟨h, _⟩
  exact h.equation

/- English proof (translation)
Establish `hev` using `eventually_equation (Λ := Λ) hΩ`. Establish `h0` using `hev.self_of_nhds`. Establish `hE : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ a b : OriginRing (curve Λ Ω), locEval Λ Ω t (a * b) = locEval Λ Ω t a * locEval Λ Ω t b ∧ locEval Λ Ω t (a + b) = locEval Λ Ω t a + locEval Λ Ω t b ∧ locEval Λ Ω t (-a) = - locEval Λ Ω t a` using `by filter_upwards [hev] with t ht a b`. Simplify using `only [locEval, dif_pos ht, map_mul, map_add, map_neg, and_self]`. Establish `hE0 : ∀ a, locEval Λ Ω 0 a = (epsEval Λ Ω 1 a).fst` using `fun a => by`.

Rewrite using `[locEval, dif_pos h0, epsEval_fst Λ Ω 1 a h0]`. Establish `hconst : ∀ a : ℂ, HasDerivAt (fun t => locEval Λ Ω t (algebraMap ℂ _ a)) (Ω * (epsEval Λ Ω 1 (algebraMap ℂ _ a)).snd) 0` using `fun a => by`. Use `((hasDerivAt_const (0 : ℂ) a).congr_deriv (by simp [epsEval, TrivSqZeroExt.algebraMap_eq_inl])).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hev] with t ht`. Rewrite using `[locEval, dif_pos ht]`.

Simplify using the standard rewrite rules. Set `S : Subring (OriginRing (curve Λ Ω))` to `{ carrier := {r | HasDerivAt (fun t => locEval Λ Ω t r) (Ω * (epsEval Λ Ω 1 r).snd) 0} mul_mem' := fun {a b} ha hb => by`. Use `((ha.mul hb).congr_deriv ?_).congr_of_eventuallyEq ?_` and prove the remaining obligations. Simplify using `only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, hE0]`. Expand and normalize the polynomial expressions, which then agree.

Use `filter_upwards [hE] with t ht`. Conclude with `(ht a b).1`. Use the proof step `one_mem' := by simpa using hconst 1`. Use the proof step `add_mem' := fun {a b} ha hb => by`. Use `((ha.add hb).congr_deriv ?_).congr_of_eventuallyEq ?_` and prove the remaining obligations.

Simplify using `only [map_add, TrivSqZeroExt.snd_add]`. Expand and normalize the polynomial expressions, which then agree. Use `filter_upwards [hE] with t ht`. Conclude with `(ht a b).2.1`. Use the proof step `zero_mem' := by simpa using hconst 0`.

Use the proof step `neg_mem' := fun {a} ha => by`. Use `(ha.neg.congr_deriv ?_).congr_of_eventuallyEq ?_` and prove the remaining obligations. Simplify using `only [map_neg, TrivSqZeroExt.snd_neg]`. Expand and normalize the polynomial expressions, which then agree. Use `filter_upwards [hE] with t ht`.

Conclude with `(ht a a).2.2 }`. Establish `hC : ∀ a : ℂ, algebraMap ℂ (OriginRing (curve Λ Ω)) a ∈ S` using `hconst`. Establish `hZ : originZ (curve Λ Ω) ∈ S`. Express the relevant statement in the definitionally equal form `HasDerivAt _ _ _`. Use `((hasDerivAt_locZ Λ Ω).congr_deriv (by simp [epsEval])).congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards [hev] with t ht`. Rewrite using `[locEval, dif_pos ht]`. Simplify using the standard rewrite rules. Establish `hW : originW (curve Λ Ω) ∈ S`. Express the relevant statement in the definitionally equal form `HasDerivAt _ _ _`.

Use `((hasDerivAt_locW Λ Ω).congr_deriv (by simp [epsEval])).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hev] with t ht`. Rewrite using `[locEval, dif_pos ht]`. Simplify using the standard rewrite rules. Establish `hCa : ∀ a : Polynomial ℂ, AdjoinRoot.mk (originPolynomial (curve Λ Ω)) (Polynomial.C a) ∈ S`.

Introduce `a`. Proceed by induction on `a using Polynomial.induction_on with`. Consider the case `C b => exact hC b`. Consider the case `add p q hp hq => rw [Polynomial.C_add, map_add]`. Conclude with `S.add_mem hp hq`.

Consider the case `monomial n b _`. Rewrite using `[Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]`. Conclude with `S.mul_mem (hC b) (S.pow_mem hW _)`. Establish `hall : ∀ x, x ∈ S`. Introduce `x`.

Use `AdjoinRoot.induction_on (f := originPolynomial (curve Λ Ω)) x fun p => ?_` and prove the remaining obligations. Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C a => exact hCa a`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `S.add_mem hp hq`.

Consider the case `monomial n a _`. Rewrite using `[map_mul, map_pow]`. Conclude with `S.mul_mem (hCa a) (S.pow_mem hZ _)`. Conclude with `hall r`.
-/
theorem hasDerivAt_locEval (hΩ : Ω ≠ 0) (r : OriginRing (curve Λ Ω)) :
    HasDerivAt (fun t => locEval Λ Ω t r) (Ω * (epsEval Λ Ω 1 r).snd) 0 := by
  have hev := eventually_equation (Λ := Λ) hΩ
  have h0 := hev.self_of_nhds
  have hE : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ a b : OriginRing (curve Λ Ω),
      locEval Λ Ω t (a * b) = locEval Λ Ω t a * locEval Λ Ω t b ∧
      locEval Λ Ω t (a + b) = locEval Λ Ω t a + locEval Λ Ω t b ∧
      locEval Λ Ω t (-a) = - locEval Λ Ω t a := by
    filter_upwards [hev] with t ht a b
    simp only [locEval, dif_pos ht, map_mul, map_add, map_neg, and_self]
  have hE0 : ∀ a, locEval Λ Ω 0 a = (epsEval Λ Ω 1 a).fst := fun a => by
    rw [locEval, dif_pos h0, epsEval_fst Λ Ω 1 a h0]
  have hconst : ∀ a : ℂ, HasDerivAt (fun t => locEval Λ Ω t (algebraMap ℂ _ a))
      (Ω * (epsEval Λ Ω 1 (algebraMap ℂ _ a)).snd) 0 := fun a => by
    refine ((hasDerivAt_const (0 : ℂ) a).congr_deriv (by simp [epsEval, TrivSqZeroExt.algebraMap_eq_inl])).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [locEval, dif_pos ht]
    simp
  let S : Subring (OriginRing (curve Λ Ω)) :=
    { carrier := {r | HasDerivAt (fun t => locEval Λ Ω t r) (Ω * (epsEval Λ Ω 1 r).snd) 0}
      mul_mem' := fun {a b} ha hb => by
        refine ((ha.mul hb).congr_deriv ?_).congr_of_eventuallyEq ?_
        · simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
            MulOpposite.unop_op, hE0]
          ring
        · filter_upwards [hE] with t ht
          exact (ht a b).1
      one_mem' := by simpa using hconst 1
      add_mem' := fun {a b} ha hb => by
        refine ((ha.add hb).congr_deriv ?_).congr_of_eventuallyEq ?_
        · simp only [map_add, TrivSqZeroExt.snd_add]
          ring
        · filter_upwards [hE] with t ht
          exact (ht a b).2.1
      zero_mem' := by simpa using hconst 0
      neg_mem' := fun {a} ha => by
        refine (ha.neg.congr_deriv ?_).congr_of_eventuallyEq ?_
        · simp only [map_neg, TrivSqZeroExt.snd_neg]
          ring
        · filter_upwards [hE] with t ht
          exact (ht a a).2.2 }
  have hC : ∀ a : ℂ, algebraMap ℂ (OriginRing (curve Λ Ω)) a ∈ S := hconst
  have hZ : originZ (curve Λ Ω) ∈ S := by
    change HasDerivAt _ _ _
    refine ((hasDerivAt_locZ Λ Ω).congr_deriv (by simp [epsEval])).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [locEval, dif_pos ht]
    simp
  have hW : originW (curve Λ Ω) ∈ S := by
    change HasDerivAt _ _ _
    refine ((hasDerivAt_locW Λ Ω).congr_deriv (by simp [epsEval])).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [locEval, dif_pos ht]
    simp
  have hCa : ∀ a : Polynomial ℂ, AdjoinRoot.mk (originPolynomial (curve Λ Ω)) (Polynomial.C a) ∈ S := by
    intro a
    induction a using Polynomial.induction_on with
    | C b => exact hC b
    | add p q hp hq => rw [Polynomial.C_add, map_add]; exact S.add_mem hp hq
    | monomial n b _ =>
      rw [Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
      exact S.mul_mem (hC b) (S.pow_mem hW _)
  have hall : ∀ x, x ∈ S := by
    intro x
    refine AdjoinRoot.induction_on (f := originPolynomial (curve Λ Ω)) x fun p => ?_
    induction p using Polynomial.induction_on with
    | C a => exact hCa a
    | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
    | monomial n a _ =>
      rw [map_mul, map_pow]
      exact S.mul_mem (hCa a) (S.pow_mem hZ _)
  exact hall r

end GlobalTheory.CMTorsionTangent

namespace GlobalTheory.CMTorsionTangent

open Filter Topology
open GlobalTheory.WeierstrassCurve (ptHom OriginRing originEval originZ originW chartY coordOpen originPolynomial)
open GlobalTheory.TangentOrigin (evalPt evalPt_res evalPt_spMap_comp fstC)

variable {Λ : PeriodPair} {Ω : ℂ}

/- English proof (translation)
Rewrite using `[← GlobalTheory.WeierstrassCurve.opensRange_chartY]`. Simplify using the standard rewrite rules.
-/
theorem top_le_chartY : ⊤ ≤ chartY (curve Λ Ω) ⁻¹ᵁ coordOpen (curve Λ Ω) 1 := by
  rw [← GlobalTheory.WeierstrassCurve.opensRange_chartY]
  simp

/- English proof (translation)
Rewrite using `[Scheme.Hom.comp_preimage]`. Conclude with `fun p _ => top_le_chartY (Set.mem_univ (g.base p))`.
-/
theorem top_le_comp_chartY {X : Scheme.{0}} (g : X ⟶ Sp (OriginRing (curve Λ Ω))) :
    ⊤ ≤ (g ≫ chartY (curve Λ Ω)) ⁻¹ᵁ coordOpen (curve Λ Ω) 1 := by
  rw [Scheme.Hom.comp_preimage]
  exact fun p _ => top_le_chartY (Set.mem_univ (g.base p))

def chartVal : Γ(scheme (curve Λ Ω), coordOpen (curve Λ Ω) 1) →+* OriginRing (curve Λ Ω) :=
  evalPt (chartY (curve Λ Ω)) _ top_le_chartY

/- English proof (translation)
The claim follows from `evalPt_spMap_comp e _ _ top_le_chartY h G`.
-/
theorem evalPt_chart {R : Type} [CommRing R] (e : OriginRing (curve Λ Ω) →+* R)
    (h : ⊤ ≤ (spMap e ≫ chartY (curve Λ Ω)) ⁻¹ᵁ coordOpen (curve Λ Ω) 1)
    (G : Γ(scheme (curve Λ Ω), coordOpen (curve Λ Ω) 1)) :
    evalPt (spMap e ≫ chartY (curve Λ Ω)) _ h G = e (chartVal G) :=
  evalPt_spMap_comp e _ _ top_le_chartY h G

/- English proof (translation)
The claim follows from `(GlobalTheory.WeierstrassCurve.SpecMap_originEval_chartY _ _ _ _ _).symm`.
-/
theorem tan_eq (c : ℂ) : tan (curve Λ Ω) c = spMap (epsEval Λ Ω c) ≫ chartY (curve Λ Ω) :=
  (GlobalTheory.WeierstrassCurve.SpecMap_originEval_chartY _ _ _ _ _).symm

/- English proof (translation)
Use `filter_upwards [pt_eq_ptHom Λ hΩ] with t ⟨h, e⟩`. Conclude with `⟨h.equation, e.trans (GlobalTheory.WeierstrassCurve.SpecMap_originEval_chartY _ _ _ _ _).symm⟩`.
-/
theorem eventually_pt_eq (hΩ : Ω ≠ 0) : ∀ᶠ t in 𝓝 (0 : ℂ), ∃ h : ((curve Λ Ω).map (RingHom.id ℂ)).toProjective.Equation
    ![locZ Λ Ω t, -1, locW Λ Ω t],
    pt Λ Ω t = spMap (originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h) ≫ chartY (curve Λ Ω) := by
  filter_upwards [pt_eq_ptHom Λ hΩ] with t ⟨h, e⟩
  exact ⟨h.equation, e.trans (GlobalTheory.WeierstrassCurve.SpecMap_originEval_chartY _ _ _ _ _).symm⟩

/- English proof (translation)
Use `filter_upwards [eventually_pt_eq (Λ := Λ) hΩ] with t ⟨h, e⟩`. Establish `key : ∀ (x : Sp ℂ ⟶ scheme (curve Λ Ω)), x = spMap (originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h) ≫ chartY (curve Λ Ω) → ⊤ ≤ x ⁻¹ᵁ coordOpen (curve Λ Ω) 1 ∧ valAt' x _ G = locEval Λ Ω t (chartVal G)`. Introduce and unpack `_ rfl`. Use `⟨top_le_comp_chartY _, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ (top_le_comp_chartY _), evalPt_chart, locEval, dif_pos h]`.

Conclude with `key _ e`.
-/
theorem eventually_valAt' (hΩ : Ω ≠ 0) (G : Γ(scheme (curve Λ Ω), coordOpen (curve Λ Ω) 1)) :
    ∀ᶠ t in 𝓝 (0 : ℂ), ⊤ ≤ pt Λ Ω t ⁻¹ᵁ coordOpen (curve Λ Ω) 1 ∧
      valAt' (pt Λ Ω t) _ G = locEval Λ Ω t (chartVal G) := by
  filter_upwards [eventually_pt_eq (Λ := Λ) hΩ] with t ⟨h, e⟩
  have key : ∀ (x : Sp ℂ ⟶ scheme (curve Λ Ω)), x = spMap (originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h) ≫
      chartY (curve Λ Ω) → ⊤ ≤ x ⁻¹ᵁ coordOpen (curve Λ Ω) 1 ∧ valAt' x _ G = locEval Λ Ω t (chartVal G) := by
    rintro _ rfl
    refine ⟨top_le_comp_chartY _, ?_⟩
    rw [GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ (top_le_comp_chartY _), evalPt_chart, locEval, dif_pos h]
  exact key _ e

/- English proof (translation)
Take `⟨h, e⟩` from `(pt_eq_ptHom Λ hΩ).self_of_nhds`. Rewrite using `[e, tan, GlobalTheory.WeierstrassCurve.SpecMap_ptHom]`. Use `GlobalTheory.WeierstrassCurve.ptHom_congr _ _ _ _ (RingHom.ext fun a => by simp) ?_ _` and prove the remaining obligations. Apply the tactic sequence `ext i; fin_cases i <;> simp [locZ, locW]`.
-/
theorem spMap_fst_tan (hΩ : Ω ≠ 0) (c : ℂ) : spMap fstC ≫ tan (curve Λ Ω) c = pt Λ Ω 0 := by
  obtain ⟨h, e⟩ := (pt_eq_ptHom Λ hΩ).self_of_nhds
  rw [e, tan, GlobalTheory.WeierstrassCurve.SpecMap_ptHom]
  refine GlobalTheory.WeierstrassCurve.ptHom_congr _ _ _ _ (RingHom.ext fun a => by simp) ?_ _
  ext i; fin_cases i <;> simp [locZ, locW]

/- English proof (translation)
Use `set U₀ := coordOpen (curve Λ Ω) 1`. Establish `hU₀ : IsAffineOpen U₀` using `GlobalTheory.WeierstrassCurve.isAffineOpen_coordOpen _ _`. Establish `hp0 : ⊤ ≤ pt Λ Ω 0 ⁻¹ᵁ V`. Rewrite using `[← spMap_fst_tan hΩ c]`. Conclude with `(GlobalTheory.TangentOrigin.top_le_preimage_iff _ V).1 hT`.

Establish `hp0U : ⊤ ≤ pt Λ Ω 0 ⁻¹ᵁ U₀` using `(eventually_valAt' hΩ 0).self_of_nhds.1`. Set `q : Sp ℂ` to `(default : PrimeSpectrum ℂ)`. Take `⟨s, hsV, hs⟩` from `hU₀.exists_basicOpen_le (V := V) ⟨(pt Λ Ω 0).base q, hp0 (Set.mem_univ q)⟩ (hp0U (Set.mem_univ q))`. Use `set B := (scheme (curve Λ Ω)).basicOpen s`. Establish `hB0 : ⊤ ≤ pt Λ Ω 0 ⁻¹ᵁ B` using `(GlobalTheory.top_le_preimage_iff_mem _ _).2 hs`.

Establish `hTB : ⊤ ≤ tan (curve Λ Ω) c ⁻¹ᵁ B`. Rewrite using `[GlobalTheory.TangentOrigin.top_le_preimage_iff, spMap_fst_tan hΩ c]`. Conclude with `hB0`. Use `hU₀.isLocalization_basicOpen s` as an intermediate fact. Take `⟨⟨a, m⟩, hm⟩` from `IsLocalization.mk'_surjective (Submonoid.powers s) (resG _ hsV G)`.

Express the relevant statement in the definitionally equal form `IsLocalization.mk' _ a m = _ at hm`. Take `⟨n, hn⟩` from `m.2`. Establish `hkey` using `IsLocalization.mk'_spec Γ(scheme (curve Λ Ω), B) a m`. Rewrite `hkey` using `[hm]`. Express the relevant statement in the definitionally equal form `resG _ hsV G * resG _ ((scheme (curve Λ Ω)).basicOpen_le s) m.1 = resG _ ((scheme (curve Λ Ω)).basicOpen_le s) a at hkey`.

Establish `hX` using `congrArg (evalPt (tan (curve Λ Ω) c) B hTB) hkey`. Establish `hTU : ⊤ ≤ tan (curve Λ Ω) c ⁻¹ᵁ U₀` using `fun p hp => (scheme (curve Λ Ω)).basicOpen_le s (hTB hp)`. Rewrite `hX` using `[map_mul, evalPt_res _ _ hT, evalPt_res _ _ hTU, evalPt_res _ _ hTU]`. Establish `ht : ∀ G' : Γ(scheme (curve Λ Ω), U₀), evalPt (tan (curve Λ Ω) c) U₀ hTU G' = epsEval Λ Ω c (chartVal G')`. Introduce `G'`.

Establish `key : ∀ (x : Sp (DualNumber ℂ) ⟶ scheme (curve Λ Ω)) (hx : ⊤ ≤ x ⁻¹ᵁ U₀), x = spMap (epsEval Λ Ω c) ≫ chartY (curve Λ Ω) → evalPt x U₀ hx G' = epsEval Λ Ω c (chartVal G')`. Introduce and unpack `_ hx rfl`. Conclude with `evalPt_chart _ hx G'`. Conclude with `key _ hTU (tan_eq c)`. Rewrite `hX` using `[ht, ht]`.

Establish `hev` using `eventually_equation (Λ := Λ) hΩ`. Establish `h0` using `hev.self_of_nhds`. Establish `hda` using `hasDerivAt_locEval hΩ (chartVal a)`. Establish `hdm` using `hasDerivAt_locEval hΩ (chartVal m.1)`. Establish `hds` using `hasDerivAt_locEval hΩ (chartVal s)`.

Establish `hm0 : locEval Λ Ω 0 (chartVal m.1) ≠ 0`. Establish `e1` using `(eventually_valAt' hΩ s).self_of_nhds.2`. Establish `e2` using `(GlobalTheory.top_le_preimage_basicOpen_iff (pt Λ Ω 0) U₀ s).1 hB0`. Rewrite `e2` using `[e1]`. Rewrite using `[← hn, map_pow, locEval, dif_pos h0, map_pow]`.

Rewrite `e2` using `[locEval, dif_pos h0]`. Conclude with `pow_ne_zero _ e2`. Establish `hsne : ∀ᶠ t in 𝓝 (0 : ℂ), locEval Λ Ω t (chartVal s) ≠ 0`. Use `hds.continuousAt.eventually_ne ?_` and prove the remaining obligations. Establish `e1` using `(eventually_valAt' hΩ s).self_of_nhds.2`.

Establish `e2` using `(GlobalTheory.top_le_preimage_basicOpen_iff (pt Λ Ω 0) U₀ s).1 hB0`. Rewrite `e2` using `[e1]`. Then use the resulting hypothesis. Establish `hmne : ∀ᶠ t in 𝓝 (0 : ℂ), locEval Λ Ω t (chartVal m.1) ≠ 0` using `hdm.continuousAt.eventually_ne hm0`. Establish `hH : (fun s' => valAt' (pt Λ Ω s') V G) =ᶠ[𝓝 0] fun t => locEval Λ Ω t (chartVal a) / locEval Λ Ω t (chartVal m.1)` using `by filter_upwards [eventually_valAt' hΩ s, eventually_valAt' hΩ a, eventually_valAt' hΩ m.1, hsne, hmne] with t ⟨hU, es⟩ ⟨_, ea⟩ ⟨_, em⟩ hs' hm'`. Establish `hBt : ⊤ ≤ pt Λ Ω t ⁻¹ᵁ B` using `(GlobalTheory.top_le_preimage_basicOpen_iff (pt Λ Ω t) U₀ s).2 (by rwa [es])`.

Establish `e` using `congrArg (valAt' (pt Λ Ω t) B) hkey`. Rewrite `e` using `[GlobalTheory.valAt'_mul, GlobalTheory.valAt'_res _ _ _ hBt, GlobalTheory.valAt'_res _ _ _ hBt, GlobalTheory.valAt'_res _ _ _ hBt, ea, em]`. Rewrite using `[eq_div_iff hm', e]`. Establish `hE0 : ∀ r, locEval Λ Ω 0 r = (epsEval Λ Ω 1 r).fst` using `fun r => by`. Rewrite using `[locEval, dif_pos h0, epsEval_fst Λ Ω 1 r h0]`.

Establish `hF : ∀ r, (epsEval Λ Ω c r).fst = (epsEval Λ Ω 1 r).fst` using `fun r => by`. Rewrite using `[epsEval_fst Λ Ω c r h0, epsEval_fst Λ Ω 1 r h0]`. Establish `hE0a : locEval Λ Ω 0 (chartVal a) = (epsEval Λ Ω 1 (chartVal a)).fst` using `hE0 _`. Establish `hE0m : locEval Λ Ω 0 (chartVal m.1) = (epsEval Λ Ω 1 (chartVal m.1)).fst` using `hE0 _`. Establish `h1` using `congrArg TrivSqZeroExt.fst hX`.

Establish `h2` using `congrArg TrivSqZeroExt.snd hX`. Simplify using `only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, hF, epsEval_snd Λ Ω c] at h1 h2`. Establish `hd` using `(hda.div hdm hm0).congr_of_eventuallyEq hH`. Generalize the expression as in `epsEval Λ Ω 1 (chartVal a) = α at hd hE0a h1 h2`. Generalize the expression as in `epsEval Λ Ω 1 (chartVal m.1) = β at hd hE0m h1 h2`.

Generalize the expression as in `evalPt (tan (curve Λ Ω) c) V hT G = X at h1 h2 ⊢`. Rewrite `hd` using `[hE0a, hE0m]`. Rewrite `hm0` using `[hE0m]`. Use `⟨(α.snd * β.fst - α.fst * β.snd) / β.fst ^ 2, hd.congr_deriv (by field_simp), ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[← eq_div_iff hm0]`.

Rewrite `h2` using `[h1]`. Clear denominators, using `at h2 ⊢` for the nonvanishing conditions. Take the linear combination `h2`.
-/
theorem exists_deriv (hΩ : Ω ≠ 0) (c : ℂ) (V : (scheme (curve Λ Ω)).Opens) (hT : ⊤ ≤ tan (curve Λ Ω) c ⁻¹ᵁ V)
    (G : Γ(scheme (curve Λ Ω), V)) :
    ∃ d : ℂ, HasDerivAt (fun s => valAt' (pt Λ Ω s) V G) (Ω * d) 0 ∧ (evalPt (tan (curve Λ Ω) c) V hT G).snd = c * d := by
  set U₀ := coordOpen (curve Λ Ω) 1
  have hU₀ : IsAffineOpen U₀ := GlobalTheory.WeierstrassCurve.isAffineOpen_coordOpen _ _
  have hp0 : ⊤ ≤ pt Λ Ω 0 ⁻¹ᵁ V := by
    rw [← spMap_fst_tan hΩ c]; exact (GlobalTheory.TangentOrigin.top_le_preimage_iff _ V).1 hT
  have hp0U : ⊤ ≤ pt Λ Ω 0 ⁻¹ᵁ U₀ := (eventually_valAt' hΩ 0).self_of_nhds.1
  let q : Sp ℂ := (default : PrimeSpectrum ℂ)
  obtain ⟨s, hsV, hs⟩ := hU₀.exists_basicOpen_le (V := V) ⟨(pt Λ Ω 0).base q, hp0 (Set.mem_univ q)⟩
    (hp0U (Set.mem_univ q))
  set B := (scheme (curve Λ Ω)).basicOpen s
  have hB0 : ⊤ ≤ pt Λ Ω 0 ⁻¹ᵁ B := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hs
  have hTB : ⊤ ≤ tan (curve Λ Ω) c ⁻¹ᵁ B := by
    rw [GlobalTheory.TangentOrigin.top_le_preimage_iff, spMap_fst_tan hΩ c]; exact hB0
  have := hU₀.isLocalization_basicOpen s
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) (resG _ hsV G)
  change IsLocalization.mk' _ a m = _ at hm
  obtain ⟨n, hn⟩ := m.2
  have hkey := IsLocalization.mk'_spec Γ(scheme (curve Λ Ω), B) a m
  rw [hm] at hkey
  change resG _ hsV G * resG _ ((scheme (curve Λ Ω)).basicOpen_le s) m.1 =
    resG _ ((scheme (curve Λ Ω)).basicOpen_le s) a at hkey

  have hX := congrArg (evalPt (tan (curve Λ Ω) c) B hTB) hkey
  have hTU : ⊤ ≤ tan (curve Λ Ω) c ⁻¹ᵁ U₀ := fun p hp => (scheme (curve Λ Ω)).basicOpen_le s (hTB hp)
  rw [map_mul, evalPt_res _ _ hT, evalPt_res _ _ hTU, evalPt_res _ _ hTU] at hX
  have ht : ∀ G' : Γ(scheme (curve Λ Ω), U₀), evalPt (tan (curve Λ Ω) c) U₀ hTU G' = epsEval Λ Ω c (chartVal G') := by
    intro G'
    have key : ∀ (x : Sp (DualNumber ℂ) ⟶ scheme (curve Λ Ω)) (hx : ⊤ ≤ x ⁻¹ᵁ U₀),
        x = spMap (epsEval Λ Ω c) ≫ chartY (curve Λ Ω) → evalPt x U₀ hx G' = epsEval Λ Ω c (chartVal G') := by
      rintro _ hx rfl; exact evalPt_chart _ hx G'
    exact key _ hTU (tan_eq c)
  rw [ht, ht] at hX

  have hev := eventually_equation (Λ := Λ) hΩ
  have h0 := hev.self_of_nhds
  have hda := hasDerivAt_locEval hΩ (chartVal a)
  have hdm := hasDerivAt_locEval hΩ (chartVal m.1)
  have hds := hasDerivAt_locEval hΩ (chartVal s)
  have hm0 : locEval Λ Ω 0 (chartVal m.1) ≠ 0 := by
    have e1 := (eventually_valAt' hΩ s).self_of_nhds.2
    have e2 := (GlobalTheory.top_le_preimage_basicOpen_iff (pt Λ Ω 0) U₀ s).1 hB0
    rw [e1] at e2
    rw [← hn, map_pow, locEval, dif_pos h0, map_pow]
    rw [locEval, dif_pos h0] at e2
    exact pow_ne_zero _ e2
  have hsne : ∀ᶠ t in 𝓝 (0 : ℂ), locEval Λ Ω t (chartVal s) ≠ 0 := by
    refine hds.continuousAt.eventually_ne ?_
    have e1 := (eventually_valAt' hΩ s).self_of_nhds.2
    have e2 := (GlobalTheory.top_le_preimage_basicOpen_iff (pt Λ Ω 0) U₀ s).1 hB0
    rwa [e1] at e2
  have hmne : ∀ᶠ t in 𝓝 (0 : ℂ), locEval Λ Ω t (chartVal m.1) ≠ 0 :=
    hdm.continuousAt.eventually_ne hm0
  have hH : (fun s' => valAt' (pt Λ Ω s') V G) =ᶠ[𝓝 0]
      fun t => locEval Λ Ω t (chartVal a) / locEval Λ Ω t (chartVal m.1) := by
    filter_upwards [eventually_valAt' hΩ s, eventually_valAt' hΩ a, eventually_valAt' hΩ m.1, hsne, hmne]
      with t ⟨hU, es⟩ ⟨_, ea⟩ ⟨_, em⟩ hs' hm'
    have hBt : ⊤ ≤ pt Λ Ω t ⁻¹ᵁ B := (GlobalTheory.top_le_preimage_basicOpen_iff (pt Λ Ω t) U₀ s).2 (by rwa [es])
    have e := congrArg (valAt' (pt Λ Ω t) B) hkey
    rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_res _ _ _ hBt, GlobalTheory.valAt'_res _ _ _ hBt, GlobalTheory.valAt'_res _ _ _ hBt, ea, em] at e
    rw [eq_div_iff hm', e]
  have hE0 : ∀ r, locEval Λ Ω 0 r = (epsEval Λ Ω 1 r).fst := fun r => by
    rw [locEval, dif_pos h0, epsEval_fst Λ Ω 1 r h0]
  have hF : ∀ r, (epsEval Λ Ω c r).fst = (epsEval Λ Ω 1 r).fst := fun r => by
    rw [epsEval_fst Λ Ω c r h0, epsEval_fst Λ Ω 1 r h0]
  have hE0a : locEval Λ Ω 0 (chartVal a) = (epsEval Λ Ω 1 (chartVal a)).fst := hE0 _
  have hE0m : locEval Λ Ω 0 (chartVal m.1) = (epsEval Λ Ω 1 (chartVal m.1)).fst := hE0 _
  have h1 := congrArg TrivSqZeroExt.fst hX
  have h2 := congrArg TrivSqZeroExt.snd hX
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, hF, epsEval_snd Λ Ω c] at h1 h2
  have hd := (hda.div hdm hm0).congr_of_eventuallyEq hH
  generalize epsEval Λ Ω 1 (chartVal a) = α at hd hE0a h1 h2
  generalize epsEval Λ Ω 1 (chartVal m.1) = β at hd hE0m h1 h2
  generalize evalPt (tan (curve Λ Ω) c) V hT G = X at h1 h2 ⊢
  rw [hE0a, hE0m] at hd
  rw [hE0m] at hm0
  refine ⟨(α.snd * β.fst - α.fst * β.snd) / β.fst ^ 2, hd.congr_deriv (by field_simp), ?_⟩
  rw [← eq_div_iff hm0] at h1
  rw [h1] at h2
  field_simp at h2 ⊢
  linear_combination h2

end GlobalTheory.CMTorsionTangent

namespace GlobalTheory.CMTorsionTangent

open Filter Topology
open GlobalTheory.TangentOrigin (evalPt fstC)

/- English proof (translation)
Unfold `evalPt`. Rewrite using `[Scheme.Hom.comp_appLE]`. Both sides reduce to the same expression.
-/
theorem evalPt_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ X) (f : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ U)) (F : Γ(Y, U)) :
    evalPt (x ≫ f) U h F = evalPt x (f ⁻¹ᵁ U) h' ((f.app U).hom F) := by
  unfold evalPt
  rw [Scheme.Hom.comp_appLE]
  rfl

/- English proof (translation)
Introduce `A _ L n u Λ Ω hΩ f β₁ hf c v hv`. Establish `he0 : (u.ex 0).left = pt Λ Ω 0 ≫ f` using `by simpa using (hf 0).symm`. Establish `hT : IsTangent v`. Express the relevant statement in the definitionally equal form `spMap fstC ≫ v.left = _`. Rewrite using `[hv, ← Category.assoc, spMap_fst_tan hΩ c, ← he0]`.

Conclude with `GlobalTheory.TangentOrigin.ex_zero_left u`. Use `⟨hT, fun U h F => ?_⟩` and prove the remaining obligations. Establish `hTV : ⊤ ≤ tan (curve Λ Ω) c ⁻¹ᵁ (f ⁻¹ᵁ U)`. Rewrite using `[← Scheme.Hom.comp_preimage, ← hv]`. Conclude with `h`.

Establish `hL : ∀ (y : Sp (DualNumber ℂ) ⟶ A.left) (hy : ⊤ ≤ y ⁻¹ᵁ U), y = tan (curve Λ Ω) c ≫ f → evalPt y U hy F = evalPt (tan (curve Λ Ω) c) _ hTV ((f.app U).hom F)`. Introduce and unpack `_ hy rfl`. Conclude with `evalPt_comp _ f U hy hTV F`. Take `⟨d, hd, hsnd⟩` from `exists_deriv hΩ c (f ⁻¹ᵁ U) hTV ((f.app U).hom F)`. Express the relevant statement in the definitionally equal form `(evalPt v.left U h F).snd = _`.

Rewrite using `[hL _ h hv, hsnd]`. Establish `hU0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U`. Rewrite using `[he0, Scheme.Hom.comp_preimage, ← spMap_fst_tan hΩ c]`. Conclude with `(GlobalTheory.TangentOrigin.top_le_preimage_iff _ _).1 hTV`. Establish `hdiff` using `GlobalTheory.TangentOrigin.differentiableAt_val u hU0 F`.

Establish `hchain : HasDerivAt (fun s : ℂ => valAt' (u.ex (s • β₁)).left U F) (fderiv ℂ (fun z => valAt' (u.ex z).left U F) 0 β₁) 0`. Establish `hl : HasDerivAt (fun s : ℂ => s • β₁) β₁ 0`. Simplify using `using (hasDerivAt_id (0 : ℂ)).smul_const β₁`. Establish `h4 : HasFDerivAt (fun z => valAt' (u.ex z).left U F) (fderiv ℂ (fun z => valAt' (u.ex z).left U F) 0) ((0 : ℂ) • β₁)` using `by rw [zero_smul]; exact hdiff.hasFDerivAt`. Conclude with `h4.comp_hasDerivAt (0 : ℂ) hl`.

Establish `heq : (fun s : ℂ => valAt' (u.ex (s • β₁)).left U F) = fun s => valAt' (pt Λ Ω s) (f ⁻¹ᵁ U) ((f.app U).hom F)`. Use function extensionality and compare the values at `s`. Rewrite using `[← hf s, GlobalTheory.valAt'_comp]`. Rewrite `hchain` using `[heq]`. Use `hchain.unique hd` as an intermediate fact.

Rewrite using `[map_smul, this, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem isTangent_and_isDiff : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (n : ℕ) (u : HolUnif A L n)
    (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ (f : scheme (curve Λ Ω) ⟶ A.left) (β₁ : Fin n → ℂ),
    (∀ z, pt Λ Ω z ≫ f = (u.ex (z • β₁)).left) → ∀ (c : ℂ) (v : epsR ℂ ⟶ A),
    v.left = tan (curve Λ Ω) c ≫ f → IsTangent v ∧ u.IsDiff ((c / Ω) • β₁) v := by
  intro A _ L n u Λ Ω hΩ f β₁ hf c v hv
  have he0 : (u.ex 0).left = pt Λ Ω 0 ≫ f := by simpa using (hf 0).symm
  have hT : IsTangent v := by
    change spMap fstC ≫ v.left = _
    rw [hv, ← Category.assoc, spMap_fst_tan hΩ c, ← he0]
    exact GlobalTheory.TangentOrigin.ex_zero_left u
  refine ⟨hT, fun U h F => ?_⟩
  have hTV : ⊤ ≤ tan (curve Λ Ω) c ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← hv]; exact h
  have hL : ∀ (y : Sp (DualNumber ℂ) ⟶ A.left) (hy : ⊤ ≤ y ⁻¹ᵁ U), y = tan (curve Λ Ω) c ≫ f →
      evalPt y U hy F = evalPt (tan (curve Λ Ω) c) _ hTV ((f.app U).hom F) := by
    rintro _ hy rfl; exact evalPt_comp _ f U hy hTV F
  obtain ⟨d, hd, hsnd⟩ := exists_deriv hΩ c (f ⁻¹ᵁ U) hTV ((f.app U).hom F)
  change (evalPt v.left U h F).snd = _
  rw [hL _ h hv, hsnd]
  have hU0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    rw [he0, Scheme.Hom.comp_preimage, ← spMap_fst_tan hΩ c]
    exact (GlobalTheory.TangentOrigin.top_le_preimage_iff _ _).1 hTV
  have hdiff := GlobalTheory.TangentOrigin.differentiableAt_val u hU0 F
  have hchain : HasDerivAt (fun s : ℂ => valAt' (u.ex (s • β₁)).left U F)
      (fderiv ℂ (fun z => valAt' (u.ex z).left U F) 0 β₁) 0 := by
    have hl : HasDerivAt (fun s : ℂ => s • β₁) β₁ 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const β₁
    have h4 : HasFDerivAt (fun z => valAt' (u.ex z).left U F) (fderiv ℂ (fun z => valAt' (u.ex z).left U F) 0)
        ((0 : ℂ) • β₁) := by rw [zero_smul]; exact hdiff.hasFDerivAt
    exact h4.comp_hasDerivAt (0 : ℂ) hl
  have heq : (fun s : ℂ => valAt' (u.ex (s • β₁)).left U F) =
      fun s => valAt' (pt Λ Ω s) (f ⁻¹ᵁ U) ((f.app U).hom F) := by
    funext s; rw [← hf s, GlobalTheory.valAt'_comp]
  rw [heq] at hchain
  have := hchain.unique hd
  rw [map_smul, this, smul_eq_mul]
  field_simp

end GlobalTheory.CMTorsionTangent

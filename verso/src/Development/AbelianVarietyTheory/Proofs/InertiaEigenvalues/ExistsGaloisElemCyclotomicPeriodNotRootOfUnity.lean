import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrobeniusPeriod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrimeUniformizerClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BezoutEisensteinDerivativePrimePow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaAinfPeriodPowNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOneAddPrimePowMulNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootOfUnityPadicComplexMemRangeAlgClosureStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisMovesFlatByUnitRootStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BKLim.ZNotRoot

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`. Take `⟨t, ht⟩` from `ih`. Use `⟨q * t + n, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Take the linear combination `q * ht`.
-/
theorem pow_sub_one_sub {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    ∃ t : R, q ^ n - 1 - (n : R) * (q - 1) = (q - 1) ^ 2 * t := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨q * t + n, ?_⟩
    push_cast
    linear_combination q * ht

/- English proof (translation)
Proceed by induction on `P using Polynomial.induction_on' with`. Consider the case `add P Q hP hQ`. Take `⟨r, hr⟩` from `hP`. Take `⟨r', hr'⟩` from `hQ`. Use `⟨r + r', ?_⟩` and prove the remaining obligations.

Simplify using `only [Polynomial.eval_add, Polynomial.derivative_add]`. Take the linear combination `hr + hr'`. Consider the case `monomial n c`. Take `⟨t, ht⟩` from `pow_sub_one_sub q n`. Use `⟨c * x ^ n * t, ?_⟩` and prove the remaining obligations.

Establish `hd : x * (Polynomial.derivative (Polynomial.monomial n c)).eval x = c * n * x ^ n`. Rewrite using `[Polynomial.derivative_monomial, Polynomial.eval_monomial]`. Break down `n with _ | n` into its components or cases. Simplify using the standard rewrite rules. Simplify using `only [Nat.add_sub_cancel]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Polynomial.eval_monomial]`. Take the linear combination `c * x ^ n * ht - (q - 1) * hd`.
-/
theorem eval_mul_sub {R : Type*} [CommRing R] (P : Polynomial R) (x q : R) :
    ∃ r : R, P.eval (q * x) - P.eval x = (q - 1) * x * (Polynomial.derivative P).eval x + (q - 1) ^ 2 * r := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨r, hr⟩ := hP
    obtain ⟨r', hr'⟩ := hQ
    refine ⟨r + r', ?_⟩
    simp only [Polynomial.eval_add, Polynomial.derivative_add]
    linear_combination hr + hr'
  | monomial n c =>
    obtain ⟨t, ht⟩ := pow_sub_one_sub q n
    refine ⟨c * x ^ n * t, ?_⟩
    have hd : x * (Polynomial.derivative (Polynomial.monomial n c)).eval x = c * n * x ^ n := by
      rw [Polynomial.derivative_monomial, Polynomial.eval_monomial]
      rcases n with _ | n
      · simp
      · simp only [Nat.add_sub_cancel]; push_cast; ring
    simp only [Polynomial.eval_monomial]
    linear_combination c * x ^ n * ht - (q - 1) * hd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

/- English proof (translation)
Proceed by induction on `Q using Polynomial.induction_on' with`. Consider the case `add P Q hP hQ => rw [Polynomial.coe_add, map_add, hP, hQ, Polynomial.map_add, Polynomial.eval_add]`. Consider the case `monomial n c`. Rewrite using `[← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X, map_mul, map_pow, bk.ev_C, bk.ev_X]`. Simplify using the standard rewrite rules.
-/
theorem ev_coe (bk : BK K) (Q : Polynomial (Wq l bk.a)) :
    bk.ev (Q : bk.S) = (Q.map (wA l bk.a : Wq l bk.a →+* Ainf l)).eval (WittVector.teichmuller l bk.flat) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [Polynomial.coe_add, map_add, hP, hQ, Polynomial.map_add, Polynomial.eval_add]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X,
      map_mul, map_pow, bk.ev_C, bk.ev_X]
    simp

end GlobalTheory.BKLim.ZNotRoot

namespace GlobalTheory.BKLim.ZNotRoot
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

/- English proof (translation)
Take `⟨c, A, B, h⟩` from `GlobalTheory.BSP.bezout_Ep_derivative l K bk`. Establish `hE : Per.θ l (bk.ev bk.E) = 0`. Rewrite using `[← RingHom.mem_ker, ← bk.span_ev]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `h2` using `congrArg (fun P : Polynomial (Wq l bk.a) => Per.θ l (bk.ev (P : bk.S))) h`.

Simplify using `only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, map_add, map_mul, bk.ev_C] at h2`. Introduce `h0`. Express the relevant statement in the definitionally equal form `Per.θ l (bk.ev (A : bk.S)) * Per.θ l (bk.ev bk.E) + Per.θ l (bk.ev (B : bk.S)) * Per.θ l (bk.ev _) = _ at h2`. Rewrite `h2` using `[hE, h0, mul_zero, mul_zero, add_zero, map_pow, map_natCast, map_pow, map_natCast]`. Establish `h3` using `congrArg (fun x : OC l => (x : ℂ_[l])) h2`.

Simplify using `only [ZeroMemClass.coe_zero] at h3`. Move the coercions through the operations in `at h3`. Conclude with `pow_ne_zero c (GlobalTheory.RingBasics.p_ne_zero (p := l)) h3.symm`.
-/
theorem theta_deriv_ne (bk : BK K) : Per.θ l (bk.ev (Polynomial.derivative bk.Ep : bk.S)) ≠ 0 := by
  obtain ⟨c, A, B, h⟩ := GlobalTheory.BSP.bezout_Ep_derivative l K bk
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have h2 := congrArg (fun P : Polynomial (Wq l bk.a) => Per.θ l (bk.ev (P : bk.S))) h
  simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, map_add, map_mul, bk.ev_C] at h2
  intro h0
  change Per.θ l (bk.ev (A : bk.S)) * Per.θ l (bk.ev bk.E) + Per.θ l (bk.ev (B : bk.S)) * Per.θ l (bk.ev _) = _ at h2
  rw [hE, h0, mul_zero, mul_zero, add_zero, map_pow, map_natCast, map_pow, map_natCast] at h2
  have h3 := congrArg (fun x : OC l => (x : ℂ_[l])) h2
  simp only [ZeroMemClass.coe_zero] at h3
  push_cast at h3
  exact pow_ne_zero c (GlobalTheory.RingBasics.p_ne_zero (p := l)) h3.symm

end GlobalTheory.BKLim.ZNotRoot

namespace GlobalTheory.BKLim.ZNotRoot
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

abbrev Θ (l : ℕ) [Fact l.Prime] : Ainf l →+* ℂ_[l] := (Per.θD l).comp (aDp l)

/- English proof (translation)
The claim follows from `(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1 x`.
-/
theorem Θ_apply (x : Ainf l) : Θ l x = ((Per.θ l x : OC l) : ℂ_[l]) := (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1 x

/- English proof (translation)
Rewrite using `[Θ_apply]`. Establish `: Per.θ l (bk.ev bk.E) = 0`. Rewrite using `[← RingHom.mem_ker, ← bk.span_ev]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem Θ_E (bk : BK K) : Θ l (bk.ev bk.E) = 0 := by
  rw [Θ_apply]
  have : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  rw [this]; rfl

/- English proof (translation)
Rewrite using `[Θ_apply, WittVector.fontaineTheta_teichmuller, ← (GlobalTheory.BSP.BK.prime_unif l K bk).2, coe_intToOC]`. Introduce `h`. Establish `h1` using `congrArg norm h`. Rewrite `h1` using `[PadicComplex.norm_extends, norm_zero, norm_eq_zero]`. Apply `(GlobalTheory.BSP.BK.prime_unif l K bk).1.ne_zero` to reduce the goal to its premises.

Conclude with `Subtype.ext (Subtype.ext h1)`.
-/
theorem Θ_flat (bk : BK K) : Θ l (WittVector.teichmuller l bk.flat) ≠ 0 := by
  rw [Θ_apply, WittVector.fontaineTheta_teichmuller, ← (GlobalTheory.BSP.BK.prime_unif l K bk).2, coe_intToOC]
  intro h
  have h1 := congrArg norm h
  rw [PadicComplex.norm_extends, norm_zero, norm_eq_zero] at h1
  apply (GlobalTheory.BSP.BK.prime_unif l K bk).1.ne_zero
  exact Subtype.ext (Subtype.ext h1)

end GlobalTheory.BKLim.ZNotRoot

open GlobalTheory.BKLim.ZNotRoot in
/- English proof (translation)
Introduce `l _ K bk`. Take `⟨τ, hτ⟩` from `GlobalTheory.BSP.exists_isPer l K bk`. Take `⟨hφ, ε, η, hε, hη⟩` from `id hτ`. Use `set u : Ainf l := WittVector.teichmuller l bk.flat with hu_def`. Use `set D : Ainf l := bk.ev (Polynomial.derivative bk.Ep : bk.S) with hD_def`.

Use `set a : ℂ_[l] := Θ l ((↑η⁻¹ : Ainf l) * τ * u * D) with ha_def`. Establish `ha : a ≠ 0`. Rewrite using `[ha_def, map_mul, map_mul, map_mul]`. Use `mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) (Θ_flat bk)) ?_` and prove the remaining obligations. Conclude with `((Units.isUnit η⁻¹).map (Θ l)).ne_zero`.

Simplify using `using GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ 1`. Rewrite using `[Θ_apply]`. Introduce `h`. Apply `theta_deriv_ne bk` to reduce the goal to its premises. Conclude with `Subtype.ext h`.

Take `⟨k, hk0, hk⟩` from `GlobalTheory.T.exists_one_add_primePow_mul_not_rootOfUnity l a ha`. Take `⟨g, hg⟩` from `GlobalTheory.T.exists_galois_moves_flat_by_unit_root l (GlobalTheory.T.rootOfUnity_padicComplex_mem_range_algClosure l) K bk (ε ^ (l ^ k)) (by rw [map_pow, hε.1, one_pow])`. Use `set μ : Ainf l := WittVector.teichmuller l ε - 1 with hμ_def`. Use `set E : Ainf l := bk.ev bk.E with hE_def`. Use `set P : Polynomial (Ainf l) := bk.Ep.map (wA l bk.a : Wq l bk.a →+* Ainf l) with hP_def`.

Establish `hEP : E = P.eval u` using `ev_coe bk bk.Ep`. Establish `hDP : D = (Polynomial.derivative P).eval u`. Rewrite using `[hD_def, ev_coe, hP_def, Polynomial.derivative_map]`. Establish `hσu : Per.σA (g : GQ l) u = WittVector.teichmuller l ε ^ (l ^ k) * u`. Rewrite using `[hu_def, GlobalTheory.RingIface.sigA_teich, hg, map_mul, map_pow]`.

Establish `hσE : Per.σA (g : GQ l) E = P.eval (WittVector.teichmuller l ε ^ (l ^ k) * u)`. Rewrite using `[hEP, hP_def, Polynomial.eval_map, Polynomial.hom_eval₂, hσu, ← Polynomial.eval_map]`. Use `congr 2`. Conclude with `RingHom.ext fun w => bk.gal_w g w`. Take `⟨r, hr⟩` from `eval_mul_sub P u (WittVector.teichmuller l ε ^ (l ^ k))`.

Take `⟨s, hs⟩` from `pow_sub_one_sub (WittVector.teichmuller l ε) (l ^ k)`. Establish `hμE : μ = (↑η⁻¹ : Ainf l) * E * τ`. Establish `h1 : (η : Ainf l) * μ = E * τ` using `by rw [hμ_def, ← hη, hφ]`. Combine the equalities or inequalities in the displayed calculation. Use `set L : Ainf l := ((l ^ k : ℕ) : Ainf l) with hL_def`.

Establish `hq : WittVector.teichmuller l ε ^ (l ^ k) - 1 = (↑η⁻¹ : Ainf l) * E * τ * (L + μ * s)`. Rewrite using `[← hμE, hμ_def]`. Take the linear combination `hs`. Use `set w : Ainf l := 1 + (↑η⁻¹ : Ainf l) * τ * (L + μ * s) * u * D + E * ((↑η⁻¹ : Ainf l) * τ) ^ 2 * (L + μ * s) ^ 2 * r with hw_def`. Establish `hw : Per.σA (g : GQ l) E = E * w`.

Rewrite using `[hσE, hw_def, hDP]`. Rewrite `hr` using `[hq]`. Take the linear combination `hr - hEP`. Establish `hΘw : Θ l w = 1 + (l : ℂ_[l]) ^ k * a`. Establish `hΘE : Θ l E = 0` using `Θ_E bk`.

Rewrite using `[hw_def, ha_def, hL_def, hμE]`. Simplify using `only [map_add, map_mul, map_pow, map_one, hΘE, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨g, (Θ l w)⁻¹, ⟨w, hw, ?_⟩, fun i hi => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(Θ l w)⁻¹ * Θ l w = 1`. Rewrite using `[hΘw]`. Conclude with `inv_mul_cancel₀ hk0`. Rewrite using `[inv_pow, Ne, inv_eq_one, hΘw]`. Conclude with `hk i hi`.
-/
theorem GlobalTheory.BKLim.exists_isZ_not_root : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (g : ↥(GK K)) (z : ℂ_[l]), IsZ bk g z ∧ ∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1 := by
  intro l _ K bk
  obtain ⟨τ, hτ⟩ := GlobalTheory.BSP.exists_isPer l K bk
  obtain ⟨hφ, ε, η, hε, hη⟩ := id hτ
  set u : Ainf l := WittVector.teichmuller l bk.flat with hu_def
  set D : Ainf l := bk.ev (Polynomial.derivative bk.Ep : bk.S) with hD_def
  set a : ℂ_[l] := Θ l ((↑η⁻¹ : Ainf l) * τ * u * D) with ha_def
  have ha : a ≠ 0 := by
    rw [ha_def, map_mul, map_mul, map_mul]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) (Θ_flat bk)) ?_
    · exact ((Units.isUnit η⁻¹).map (Θ l)).ne_zero
    · simpa using GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ 1
    · rw [Θ_apply]; intro h
      apply theta_deriv_ne bk
      exact Subtype.ext h
  obtain ⟨k, hk0, hk⟩ := GlobalTheory.T.exists_one_add_primePow_mul_not_rootOfUnity l a ha
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_moves_flat_by_unit_root l (GlobalTheory.T.rootOfUnity_padicComplex_mem_range_algClosure l) K bk (ε ^ (l ^ k)) (by rw [map_pow, hε.1, one_pow])
  set μ : Ainf l := WittVector.teichmuller l ε - 1 with hμ_def
  set E : Ainf l := bk.ev bk.E with hE_def
  set P : Polynomial (Ainf l) := bk.Ep.map (wA l bk.a : Wq l bk.a →+* Ainf l) with hP_def
  have hEP : E = P.eval u := ev_coe bk bk.Ep
  have hDP : D = (Polynomial.derivative P).eval u := by
    rw [hD_def, ev_coe, hP_def, Polynomial.derivative_map]
  have hσu : Per.σA (g : GQ l) u = WittVector.teichmuller l ε ^ (l ^ k) * u := by
    rw [hu_def, GlobalTheory.RingIface.sigA_teich, hg, map_mul, map_pow]
  have hσE : Per.σA (g : GQ l) E = P.eval (WittVector.teichmuller l ε ^ (l ^ k) * u) := by
    rw [hEP, hP_def, Polynomial.eval_map, Polynomial.hom_eval₂, hσu, ← Polynomial.eval_map]
    congr 2
    exact RingHom.ext fun w => bk.gal_w g w
  obtain ⟨r, hr⟩ := eval_mul_sub P u (WittVector.teichmuller l ε ^ (l ^ k))
  obtain ⟨s, hs⟩ := pow_sub_one_sub (WittVector.teichmuller l ε) (l ^ k)
  have hμE : μ = (↑η⁻¹ : Ainf l) * E * τ := by
    have h1 : (η : Ainf l) * μ = E * τ := by rw [hμ_def, ← hη, hφ]
    calc μ = (↑η⁻¹ : Ainf l) * ((η : Ainf l) * μ) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [h1]; ring
  set L : Ainf l := ((l ^ k : ℕ) : Ainf l) with hL_def
  have hq : WittVector.teichmuller l ε ^ (l ^ k) - 1 = (↑η⁻¹ : Ainf l) * E * τ * (L + μ * s) := by
    rw [← hμE, hμ_def]; linear_combination hs
  set w : Ainf l := 1 + (↑η⁻¹ : Ainf l) * τ * (L + μ * s) * u * D +
    E * ((↑η⁻¹ : Ainf l) * τ) ^ 2 * (L + μ * s) ^ 2 * r with hw_def
  have hw : Per.σA (g : GQ l) E = E * w := by
    rw [hσE, hw_def, hDP]
    rw [hq] at hr
    linear_combination hr - hEP
  have hΘw : Θ l w = 1 + (l : ℂ_[l]) ^ k * a := by
    have hΘE : Θ l E = 0 := Θ_E bk
    rw [hw_def, ha_def, hL_def, hμE]
    simp only [map_add, map_mul, map_pow, map_one, hΘE, map_natCast]
    push_cast
    ring
  refine ⟨g, (Θ l w)⁻¹, ⟨w, hw, ?_⟩, fun i hi => ?_⟩
  · change (Θ l w)⁻¹ * Θ l w = 1
    rw [hΘw]; exact inv_mul_cancel₀ hk0
  · rw [inv_pow, Ne, inv_eq_one, hΘw]
    exact hk i hi

end

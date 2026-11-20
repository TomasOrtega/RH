import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.PolMix
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
open scoped Matrix
/- English proof (translation)
Assemble the required witnesses or components as `⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩`.
-/
private theorem alg_closure_of (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k₀ : IntermediateField ℚ Ω) :
    IsAlgClosure k₀ Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω`. Set `j : Ω →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Use `letI : Algebra Ω ℂ := j.toRingHom.toAlgebra`.

Use `haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm`. Set `τ : ℂ ≃ₐ[ℚ] ℂ` to `AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp`. Set `c : Ω ≃ₐ[ℚ] Ω` to `τ.restrictNormal Ω`. Establish `hc : ∀ x, algebraMap Ω ℂ (c x) = starRingEnd ℂ (algebraMap Ω ℂ x)` using `fun x => AlgEquiv.restrictNormal_commutes τ Ω x`. Establish `hfix : ∀ y : k₀, c (y : Ω) = y` using `fun y => by`.

Apply `(algebraMap Ω ℂ).injective` to reduce the goal to its premises. Rewrite using `[hc]`. Set `φ : k₀ →+* ℂ` to `(algebraMap Ω ℂ).comp (algebraMap k₀ Ω)`. Establish `hr : ComplexEmbedding.IsReal φ` using `InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))`. Conclude with `RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hr) y`.

Use `⟨AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun y => hfix y, algebraMap Ω ℂ, fun x => hc x⟩` and prove the remaining obligations.
-/
private theorem conj_el_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k₀ : IntermediateField ℚ Ω) [NumberField k₀]
    [IsTotallyReal k₀] : ∃ c : G k₀ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  let c : Ω ≃ₐ[ℚ] Ω := τ.restrictNormal Ω
  have hc : ∀ x, algebraMap Ω ℂ (c x) = starRingEnd ℂ (algebraMap Ω ℂ x) := fun x => AlgEquiv.restrictNormal_commutes τ Ω x
  have hfix : ∀ y : k₀, c (y : Ω) = y := fun y => by
    apply (algebraMap Ω ℂ).injective
    rw [hc]
    let φ : k₀ →+* ℂ := (algebraMap Ω ℂ).comp (algebraMap k₀ Ω)
    have hr : ComplexEmbedding.IsReal φ :=
      InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))
    exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hr) y
  refine ⟨AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun y => hfix y, algebraMap Ω ℂ, fun x => hc x⟩
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring`.
-/
private theorem pair_two {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
/- English proof (translation)
Set `J : GL (Fin 2) k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])`. Use `⟨J * r c⁻¹, fun s s' h => ?_⟩` and prove the remaining obligations. Establish `h' : s' = c * s * c⁻¹` using `h`. Establish `e : r c⁻¹ * r s' = r s * r c⁻¹` using `by rw [h', ← map_mul, ← map_mul]; congr 1; group`. Establish `e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val` using `congrArg Units.val e`.

Establish `hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val` using `pair_two _`. Establish `hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det` using `rfl`. Rewrite using `[hd, Units.val_mul, ← Matrix.smul_mul, ← hp]`. Simplify using `only [Matrix.mul_assoc, e']`.
-/
private theorem pairing_two {F Ω k : Type} [Field F] [Field Ω] [Algebra F Ω] [Field k] (r : G F Ω →* GL (Fin 2) k) (c : G F Ω) :
    ∃ P, IsPairing c r ((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω)) P := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : s' = c * s * c⁻¹ := h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val := congrArg Units.val e
  have hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val := pair_two _
  have hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det := rfl
  rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
/- English proof (translation)
Introduce `H Ω _ _ _ l _ k₀ _ _ ι x k t r hd hm`. Take `⟨m, hm0, hm⟩` from `hm`. Use `haveI : IsAlgClosure k₀ Ω := alg_closure_of Ω k₀`. Establish `hdet : ∀ s, Matrix.GeneralLinearGroup.det (r s) = cycBar k₀ Ω l s ^ k * x (resQ k₀ s)` using `fun s => DFunLike.congr_fun hd.det s`. Establish `hcont : Continuous (Matrix.GeneralLinearGroup.det.comp r)` using `Matrix.GeneralLinearGroup.continuous_det.comp hd.cont`.

Establish `halg : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp r)`. Use `(_root_.UpperTheory.V.Af.algOfCyc_s H k₀ Ω l ι).1 _ hcont fun w _ => ?_` and prove the remaining obligations. Take `⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w` from `exists_isPlaceOver Ω w`. Use `⟨A, hA, k, m, hm0, fun s _ => ?_⟩` and prove the remaining obligations. Establish `hx : x (resQ k₀ s) ^ m = 1`.

Use `DFunLike.congr_fun hm (resQ k₀ s)` as an intermediate fact. Simplify using `using this`. Rewrite using `[MonoidHom.comp_apply, hdet, zpow_neg, zpow_natCast, mul_comm (cycBar k₀ Ω l s ^ k), mul_inv_cancel_right, hx]`. Establish `hsign : Sol.SameSign (Matrix.GeneralLinearGroup.det.comp r)`. Introduce `c c' hc hc'`.

Establish `hres : ∀ {a : G k₀ Ω}, IsConjEl a → IsConjEl (resQ k₀ a)` using `fun ⟨j, hj⟩ => ⟨j, hj⟩`. Establish `hcj : IsConj (resQ k₀ c) (resQ k₀ c')` using `UpperTheory.complex_conjugations_are_conjugate Ω _ _ (hres hc) (hres hc')`. Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply, hdet, hdet, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c hc, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c' hc', isConj_iff_eq.1 (MonoidHom.map_isConj x hcj)]`. Take `⟨c, hc⟩` from `conj_el_ex Ω k₀`. Take `⟨P, hP⟩` from `pairing_two r c`.

Conclude with `⟨k₀, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, P, halg, hsign, hc, hP⟩`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.polMix_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.PolMix := by
  intro H Ω _ _ _ l _ k₀ _ _ ι x k t r hd hm
  obtain ⟨m, hm0, hm⟩ := hm
  haveI : IsAlgClosure k₀ Ω := alg_closure_of Ω k₀
  have hdet : ∀ s, Matrix.GeneralLinearGroup.det (r s) = cycBar k₀ Ω l s ^ k * x (resQ k₀ s) := fun s =>
    DFunLike.congr_fun hd.det s
  have hcont : Continuous (Matrix.GeneralLinearGroup.det.comp r) :=
    Matrix.GeneralLinearGroup.continuous_det.comp hd.cont
  have halg : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp r) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s H k₀ Ω l ι).1 _ hcont fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    refine ⟨A, hA, k, m, hm0, fun s _ => ?_⟩
    have hx : x (resQ k₀ s) ^ m = 1 := by
      have := DFunLike.congr_fun hm (resQ k₀ s)
      simpa using this
    rw [MonoidHom.comp_apply, hdet, zpow_neg, zpow_natCast, mul_comm (cycBar k₀ Ω l s ^ k), mul_inv_cancel_right, hx]
  have hsign : Sol.SameSign (Matrix.GeneralLinearGroup.det.comp r) := by
    intro c c' hc hc'
    have hres : ∀ {a : G k₀ Ω}, IsConjEl a → IsConjEl (resQ k₀ a) := fun ⟨j, hj⟩ => ⟨j, hj⟩
    have hcj : IsConj (resQ k₀ c) (resQ k₀ c') := UpperTheory.complex_conjugations_are_conjugate Ω _ _ (hres hc) (hres hc')
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hdet, hdet, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c hc, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c' hc',
      isConj_iff_eq.1 (MonoidHom.map_isConj x hcj)]
  obtain ⟨c, hc⟩ := conj_el_ex Ω k₀
  obtain ⟨P, hP⟩ := pairing_two r c
  exact ⟨k₀, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, P, halg, hsign, hc, hP⟩
end

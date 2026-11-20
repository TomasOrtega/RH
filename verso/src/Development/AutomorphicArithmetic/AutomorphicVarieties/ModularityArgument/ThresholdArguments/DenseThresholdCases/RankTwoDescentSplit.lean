import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuspUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DownQuadS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsResidualRepQuadratic

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.Af
open scoped Matrix
/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Set `j : Ω →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Use `letI : Algebra Ω ℂ := j.toRingHom.toAlgebra`. Use `haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm`.

Use `haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω`. Set `τ : ℂ ≃ₐ[ℚ] ℂ` to `AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp`. Conclude with `⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩`.
-/
private theorem cc_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
/- English proof (translation)
Take `⟨j, hj⟩` from `hc`. Apply `j.injective` to reduce the goal to its premises. Establish `h1 : (j ζ) ^ M = 1` using `by rw [← map_pow, h, map_one]`. Rewrite using `[hj, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 (by omega))]`.
-/
private theorem cc_mu {Ω : Type} [Field Ω] [CharZero Ω] {c : G ℚ Ω} (hc : IsConjEl c) {M : ℕ} (hM : 1 ≤ M) {ζ : Ω}
    (h : ζ ^ M = 1) : c ζ = ζ⁻¹ := by
  obtain ⟨j, hj⟩ := hc
  apply j.injective
  have h1 : (j ζ) ^ M = 1 := by rw [← map_pow, h, map_one]
  rw [hj, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 (by omega))]
/- English proof (translation)
Use `hχ (c⁻¹ * c') fun ζ h => by` as an intermediate fact. Rewrite using `[AlgEquiv.mul_apply, cc_mu hc' hM h, ← cc_mu hc hM h]`. Conclude with `c.symm_apply_apply ζ`. Rewrite `this` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `this`.
-/
private theorem kills_cc {Ω : Type} [Field Ω] [CharZero Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M) {χ : G ℚ Ω →* C}
    (hχ : KillsMu M χ) {c c' : G ℚ Ω} (hc : IsConjEl c) (hc' : IsConjEl c') : χ c = χ c' := by
  have := hχ (c⁻¹ * c') fun ζ h => by
    rw [AlgEquiv.mul_apply, cc_mu hc' hM h, ← cc_mu hc hM h]
    exact c.symm_apply_apply ζ
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this
/- English proof (translation)
Use `haveI : NeZero M := ⟨by omega⟩`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Take `⟨μ, hμ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω M`. Use `⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow]`.

Use `hχ _ fun ζ h => ?_` and prove the remaining obligations. Establish `h1` using `hμ.autToPow_spec ℚ (s ^ Fintype.card (ZMod M)ˣ)`. Rewrite `h1` using `[map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one]`. Take `⟨i, -, rfl⟩` from `hμ.eq_pow_of_pow_eq_one h`. Rewrite using `[map_pow, ← h1]`.
-/
private theorem kills_pow {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [CommGroup C] {M : ℕ} (hM : 1 ≤ M)
    {χ : G ℚ Ω →* C} (hχ : KillsMu M χ) : ∃ k : ℕ, 0 < k ∧ ∀ s, χ s ^ k = 1 := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, fun s => ?_⟩
  rw [← map_pow]
  refine hχ _ fun ζ h => ?_
  have h1 := hμ.autToPow_spec ℚ (s ^ Fintype.card (ZMod M)ˣ)
  rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one] at h1
  obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one h
  rw [map_pow, ← h1]
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring`.
-/
private theorem pair2 {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
/- English proof (translation)
Set `J : GL (Fin 2) k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])`. Use `⟨J * r c⁻¹, fun s s' h => ?_⟩` and prove the remaining obligations. Establish `h' : s' = c * s * c⁻¹` using `h`. Establish `e : r c⁻¹ * r s' = r s * r c⁻¹` using `by rw [h', ← map_mul, ← map_mul]; congr 1; group`. Establish `e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val` using `congrArg Units.val e`.

Establish `hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val` using `pair2 _`. Establish `hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det` using `rfl`. Rewrite using `[hd, Units.val_mul, ← Matrix.smul_mul, ← hp]`. Simplify using `only [Matrix.mul_assoc, e']`.
-/
private theorem pairing2 {F Ω k : Type} [Field F] [Field Ω] [Algebra F Ω] [Field k] (r : G F Ω →* GL (Fin 2) k) (c : G F Ω) :
    ∃ P, IsPairing c r ((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω)) P := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : s' = c * s * c⁻¹ := h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val := congrArg Units.val e
  have hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val := pair2 _
  have hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det := rfl
  rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
/- English proof (translation)
The claim follows from `DivisionSemiring.to_moduleIsTorsionFree`.
-/
private theorem tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree
attribute [local instance] tf
/- English proof (translation)
Assemble the required witnesses or components as `⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩`.
-/
private theorem algClosure_up (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
open UpperTheory.V UpperTheory.V.Af in
/- English proof (translation)
Use `haveI : IsAlgClosure K Ω := algClosure_up K Ω`. Use `haveI : IsAlgClosure L Ω := algClosure_up L Ω`. Use `haveI a : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L`. Establish `e : (W.comp (resG ℚ K Ω)).comp (resG K L Ω) = W.comp (resG ℚ L Ω)` using `MonoidHom.ext fun _ => rfl`. Rewrite `hirr`, `haut` using `[← e]`.

Establish `h1` using `(_root_.UpperTheory.V.Z.Bc.solC_alt P cyc K L Ω (isSolvable_of_comm a.is_comm.comm) hC hL l ι 2 one_le_two (W.comp (resG ℚ K Ω)) (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) hirr (UpperTheory.solvable_polarized_restriction ℚ K Ω l ι 2 W hpol)).2 haut`. Conclude with `_root_.UpperTheory.V.Z.Bc.automorphic_rank_two_of_automorphic_restrict_of_finite_det P cyc2 hG (_root_.UpperTheory.V.Z.Bc.exists_residual_rep_quadratic_alt P) K Ω hK hC l ι W hW ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr) hfin h1`.
-/
private theorem via (P : _root_.UpperTheory.V.Af.HypothesesH') (cyc : Z.Bc.CycC) (cyc2 : Z.Bc.DescS) (hG : Z.Bc.GapTwo) (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAbelianGalois ℚ L]
    (hK : Module.finrank ℚ K = 2) (hC : IsCMField K) (hL : IsCMField L) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W) (hirr : IsIrr (W.comp (resG ℚ L Ω))) (hpol : Sol.Pol ι W)
    (hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (W s) ^ N = 1)
    (haut : IsAut ι (W.comp (resG ℚ L Ω))) : IsAut ι W := by
  haveI : IsAlgClosure K Ω := algClosure_up K Ω
  haveI : IsAlgClosure L Ω := algClosure_up L Ω
  haveI a : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  have e : (W.comp (resG ℚ K Ω)).comp (resG K L Ω) = W.comp (resG ℚ L Ω) := MonoidHom.ext fun _ => rfl
  rw [← e] at hirr haut
  have h1 := (_root_.UpperTheory.V.Z.Bc.solC_alt P cyc K L Ω (isSolvable_of_comm a.is_comm.comm) hC hL l ι 2 one_le_two (W.comp (resG ℚ K Ω))
    (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) hirr (UpperTheory.solvable_polarized_restriction ℚ K Ω l ι 2 W hpol)).2 haut
  exact _root_.UpperTheory.V.Z.Bc.automorphic_rank_two_of_automorphic_restrict_of_finite_det P cyc2 hG (_root_.UpperTheory.V.Z.Bc.exists_residual_rep_quadratic_alt P) K Ω hK hC l ι W hW ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr) hfin h1
open UpperTheory.V UpperTheory.V.Af in
/- English proof (translation)
Introduce `L Ω _ _ _ _ _ _ _ _ l _ ι W hW hdet hirr ⟨η, σ, hσ, hησ, hηL⟩ haut`. Use `haveI : IsAlgClosure L Ω := algClosure_up L Ω`. Take `⟨M, χ, hM, hχ, hθ⟩` from `hdet`. Rewrite `hθ` using `[zpow_zero, one_mul]`. Establish `hcont : Continuous (Matrix.GeneralLinearGroup.det.comp W)` using `Matrix.GeneralLinearGroup.continuous_det.comp hW`.

Take `⟨k, hk, hpow⟩` from `kills_pow hM hχ`. Establish `halg : IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W)`. Use `(_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).1 _ hcont fun w _ => ?_` and prove the remaining obligations. Take `⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w` from `exists_isPlaceOver Ω w`. Conclude with `⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hθ, hpow]⟩`.

Take `⟨c, hc⟩` from `cc_ex Ω`. Take `⟨Q, hQ⟩` from `pairing2 W c`. Establish `hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (W s) ^ N = 1` using `⟨k, hk, fun s => by`. Establish `e : Matrix.GeneralLinearGroup.det (W s) = χ s` using `DFunLike.congr_fun hθ s`. Rewrite using `[e, hpow]⟩`.

Take `⟨K, hK, hC⟩` from `Z.Bc.exists_quad L Ω η σ hσ hησ hηL`. Establish `hpol : Sol.Pol ι W` using `⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, Q, halg, fun c c' h h' => by rw [hθ]; exact kills_cc hM hχ h h', hc, hQ⟩`. Conclude with `(_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida P ℚ Ω l ι 2 W).1.1 (via P cyc cyc2 hG K L Ω hK hC inferInstance l ι W hW hirr hpol hfin ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida P L Ω l ι 2 _).2.1.2 haut))`.
-/
theorem UpperTheory.V.Z.Bc.isAutR_of_isAutC_comp_galEmb_of_odd_quadratic_char (P : _root_.UpperTheory.V.Af.HypothesesH') (cyc : Z.Bc.CycC) (cyc2 : Z.Bc.DescS) (hG : Z.Bc.GapTwo) :
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [IsAbelianGalois ℚ L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous W →
    IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) → IsIrr (W.comp (galEmb ℚ L Ω)) →
    (∃ (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω), Sd.IsCC σ ∧ η σ = -1 ∧ ∀ s : G L Ω, η (galEmb ℚ L Ω s) = 1) →
    Sd.IsAutC ι (W.comp (galEmb ℚ L Ω)) → IsAutR ι W := by
  intro L Ω _ _ _ _ _ _ _ _ l _ ι W hW hdet hirr ⟨η, σ, hσ, hησ, hηL⟩ haut
  haveI : IsAlgClosure L Ω := algClosure_up L Ω
  obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
  rw [zpow_zero, one_mul] at hθ
  have hcont : Continuous (Matrix.GeneralLinearGroup.det.comp W) :=
    Matrix.GeneralLinearGroup.continuous_det.comp hW
  obtain ⟨k, hk, hpow⟩ := kills_pow hM hχ
  have halg : IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).1 _ hcont fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hθ, hpow]⟩
  obtain ⟨c, hc⟩ := cc_ex Ω
  obtain ⟨Q, hQ⟩ := pairing2 W c
  have hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (W s) ^ N = 1 :=
    ⟨k, hk, fun s => by
      have e : Matrix.GeneralLinearGroup.det (W s) = χ s := DFunLike.congr_fun hθ s
      rw [e, hpow]⟩
  obtain ⟨K, hK, hC⟩ := Z.Bc.exists_quad L Ω η σ hσ hησ hηL
  have hpol : Sol.Pol ι W := ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, Q, halg,
    fun c c' h h' => by rw [hθ]; exact kills_cc hM hχ h h', hc, hQ⟩
  exact (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida P ℚ Ω l ι 2 W).1.1 (via P cyc cyc2 hG K L Ω hK hC inferInstance l ι W hW hirr hpol hfin ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida P L Ω l ι 2 _).2.1.2 haut))
end
end

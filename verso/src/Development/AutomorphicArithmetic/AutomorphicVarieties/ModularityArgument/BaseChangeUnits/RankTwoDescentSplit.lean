import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsoOfFrobOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ExistsQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge

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

Establish `h1` using `(Z.Bc.solC P cyc K L Ω (isSolvable_of_comm a.is_comm.comm) hC hL l ι 2 one_le_two (W.comp (resG ℚ K Ω)) (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) hirr (UpperTheory.solvable_polarized_restriction ℚ K Ω l ι 2 W hpol)).2 haut`. Conclude with `Z.Bc.downQuadS P cyc2 hG (Z.Bc.galois_rep_rank_two_of_hypotheses P) K Ω hK hC l ι W hW ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr) hfin h1`.
-/
private theorem via (P : HypothesesH) (cyc : Z.Bc.CycC) (cyc2 : Z.Bc.DescS) (hG : Z.Bc.GapTwo) (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L]
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
  have h1 := (Z.Bc.solC P cyc K L Ω (isSolvable_of_comm a.is_comm.comm) hC hL l ι 2 one_le_two (W.comp (resG ℚ K Ω))
    (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) hirr (UpperTheory.solvable_polarized_restriction ℚ K Ω l ι 2 W hpol)).2 haut
  exact Z.Bc.downQuadS P cyc2 hG (Z.Bc.galois_rep_rank_two_of_hypotheses P) K Ω hK hC l ι W hW ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr) hfin h1

end

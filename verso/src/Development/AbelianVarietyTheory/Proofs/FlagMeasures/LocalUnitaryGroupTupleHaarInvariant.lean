import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.LocalUnitaryHaar

open PI.VolSemiDirect.W.Cj Measure
open scoped NNReal Matrix

/- English proof (translation)
Introduce `a b x y h`. Distinguish the cases in `ha : a = 0`. Use `⟨1, ?_⟩` and prove the remaining obligations. Substitute `ha` using the available equality. Establish `hb : b ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at h`. Simplify using `using isUnit_iff_ne_zero.2 hb`. Conclude with `⟨0, by simpa using isUnit_iff_ne_zero.2 ha⟩`.
-/
theorem stableRankOne_field (K : Type) [Field K] : HasStableRangeOne K := by
  intro a b x y h
  by_cases ha : a = 0
  · refine ⟨1, ?_⟩
    subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      simp at h
    simpa using isUnit_iff_ne_zero.2 hb
  · exact ⟨0, by simpa using isUnit_iff_ne_zero.2 ha⟩

/- English proof (translation)
Establish `hd` using `congrArg Matrix.det hXG`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Establish `hdd : X.det * X.det = 1`. Establish `: (X.det * X.det) * G.det = 1 * G.det`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hG.mul_left_inj.1 this`. Establish `hX : IsUnit X.det` using `⟨⟨X.det, X.det, hdd, hdd⟩, rfl⟩`. Set `Xu : GL (Fin k) A` to `Matrix.nonsingInvUnit X hX`. Set `Gu : GL (Fin k) A` to `Matrix.nonsingInvUnit G hG`. Establish `hrel : trG Xu * Gu * Xu = Gu` using `by ext1`.

Conclude with `hXG`. Establish `hm` using `congrArg modM hrel`. Rewrite `hm` using `[modM_mul, modM_mul, modM_tr_of_mem transvection_preserves_haar Xu (gl_generated_transvections_diag A hA k Xu)]`. Establish `hpos : 0 < modM Gu` using `addEquivAddHaarChar_pos (phi Gu)`. Establish `hsq : modM Xu * modM Xu = 1`.

Establish `: (modM Xu * modM Xu) * modM Gu = 1 * modM Gu`. Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_right_cancel₀ hpos.ne' this`. Establish `hmod` using `nnreal_eq_one_of_mul_self hsq`. Establish `e` using `map_phi_of_modM Xu hmod μ`.

Establish `e2 : (phi Xu : (Fin k → A) → (Fin k → A)) = Matrix.mulVec X`. Use function extensionality and compare the values at `v`. Both sides reduce to the same expression. Rewrite `e` using `[e2]`. Conclude with `e`.
-/
theorem map_mulVec_eq_of_preserves_form {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
    [BorelSpace A] (hA : HasStableRangeOne A) (k : ℕ) (G X : Matrix (Fin k) (Fin k) A)
    (hG : IsUnit G.det) (hXG : X.transpose * G * X = G)
    (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure] : μ.map X.mulVec = μ := by
  have hd := congrArg Matrix.det hXG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hdd : X.det * X.det = 1 := by
    have : (X.det * X.det) * G.det = 1 * G.det := by
      calc (X.det * X.det) * G.det = X.det * G.det * X.det := by ring
        _ = 1 * G.det := by rw [hd, one_mul]
    exact hG.mul_left_inj.1 this
  have hX : IsUnit X.det := ⟨⟨X.det, X.det, hdd, hdd⟩, rfl⟩
  let Xu : GL (Fin k) A := Matrix.nonsingInvUnit X hX
  let Gu : GL (Fin k) A := Matrix.nonsingInvUnit G hG
  have hrel : trG Xu * Gu * Xu = Gu := by
    ext1
    exact hXG
  have hm := congrArg modM hrel
  rw [modM_mul, modM_mul, modM_tr_of_mem transvection_preserves_haar Xu (gl_generated_transvections_diag A hA k Xu)] at hm
  have hpos : 0 < modM Gu := addEquivAddHaarChar_pos (phi Gu)
  have hsq : modM Xu * modM Xu = 1 := by
    have : (modM Xu * modM Xu) * modM Gu = 1 * modM Gu := by
      calc (modM Xu * modM Xu) * modM Gu = modM Xu * modM Gu * modM Xu := by ring
        _ = 1 * modM Gu := by rw [hm, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have hmod := nnreal_eq_one_of_mul_self hsq
  have e := map_phi_of_modM Xu hmod μ
  have e2 : (phi Xu : (Fin k → A) → (Fin k → A)) = Matrix.mulVec X := by
    funext v
    rfl
  rw [e2] at e
  exact e

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_eq_succ hCM.2.2.1`. Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _`. Take `⟨eh⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R`. Use `haveI : LocallyCompactSpace (R ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace`.

Use `haveI : SecondCountableTopology (R ⊗[F] E) := eh.secondCountableTopology`. Use `haveI : T2Space (R ⊗[F] E) := eh.isEmbedding.t2Space`. Use `haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩`. Use `set k := Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E))`. Use `set b := bV F E M`.

Use `set bR := bVR F E M R`. Use `set e : (Fin M → R ⊗[F] E) ≃ₗ[R] (Fin k → R) := bR.equivFun`. Establish `c1 : Continuous e.toLinearMap` using `IsModuleTopology.continuous_of_linearMap (R := R) _`. Establish `c2 : Continuous e.symm.toLinearMap` using `IsModuleTopology.continuous_of_linearMap (R := R) _`. Set `ec : (Fin M → R ⊗[F] E) ≃ₜ+ (Fin k → R)` to `{ e.toAddEquiv with continuous_toFun := by simpa using c1 continuous_invFun := by simpa using c2 }`.

Establish `hec : ∀ u, ec u = e u` using `fun _ => rfl`. Establish `hecs : ∀ x, ec.symm x = e.symm x` using `fun _ => rfl`. Use `set μ' := μ.map ec`. Establish `hμ' : μ'.IsAddHaarMeasure` using `ec.isAddHaarMeasure_map μ`. Set `L : (Fin k → R) →ₗ[R] (Fin k → R)` to `e.toLinearMap ∘ₗ ((lin R σ J g).restrictScalars R) ∘ₗ e.symm.toLinearMap`.

Use `set X := LinearMap.toMatrix' L`. Establish `hX : ∀ x, X.mulVec x = e (lin R σ J g (e.symm x))` using `fun x => LinearMap.toMatrix'_mulVec L x`. Use `set G0 : Matrix (Fin k) (Fin k) F := Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))`. Use `set G := G0.map (algebraMap F R)`. Establish `hGu : IsUnit G.det`.

Establish `hd : G.det = algebraMap F R G0.det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[hd]`. Conclude with `(isUnit_iff_ne_zero.2 (trace_gram_nondegenerate F E σ hCM M J hJ k b)).map _`.

Establish `hBG : ∀ i j, Bf σ J (bR i) (bR j) = G i j`. Introduce `i j`. Rewrite using `[bVR_apply, bVR_apply, Bf, trace_basis_holds F E R σ M J]`. Both sides reduce to the same expression. Establish `key : ∀ x y : Fin k → R, Bf σ J (e.symm x) (e.symm y) = x ⬝ᵥ (G *ᵥ y)`.

Introduce `x y`. Rewrite using `[Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Bf_expand]`. Simplify using `only [hBG, dotProduct, Matrix.mulVec, Finset.mul_sum]`. Both sides reduce to the same expression. Establish `e1 : ∀ u w : Fin k → R, u ⬝ᵥ ((X.transpose * G * X) *ᵥ w) = u ⬝ᵥ (G *ᵥ w)`.

Introduce `u w`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, ← key, hX, hX, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, Bf_lin, key]`. Establish `hXG : X.transpose * G * X = G`. Use extensionality with `i j`. Simplify using `using e1 (Pi.single i 1) (Pi.single j 1)`.

Establish `hinv` using `map_mulVec_eq_of_preserves_form hR1 k G X hGu hXG μ'`. Establish `hlin : (lin R σ J g : (Fin M → R ⊗[F] E) → (Fin M → R ⊗[F] E)) = ec.symm ∘ X.mulVec ∘ ec`. Use function extensionality and compare the values at `u`. Simplify using `only [Function.comp_apply, hec, hecs, hX, LinearEquiv.symm_apply_apply]`. Establish `mec : Measurable ec` using `ec.continuous.measurable`.

Establish `mecs : Measurable ec.symm` using `ec.symm.continuous.measurable`. Establish `mX : Measurable X.mulVec` using `(continuous_const.matrix_mulVec continuous_id).measurable`. Rewrite using `[hlin, ← Measure.map_map mecs (mX.comp mec), ← Measure.map_map mX mec, hinv, Measure.map_map mecs mec]`. Establish `: (ec.symm ∘ ec : (Fin M → R ⊗[F] E) → _) = id`. Use function extensionality and compare the values at `u`.

Simplify using the standard rewrite rules. Rewrite using `[this, Measure.map_id]`.
-/
theorem map_lin_eq_of_stableRankOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R] (hR1 : HasStableRangeOne R) (g : HA R σ J)
    (μ : Measure (Fin M → R ⊗[F] E)) [μ.IsAddHaarMeasure] :
    μ.map (lin R σ J g) = μ := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  haveI : LocallyCompactSpace (R ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (R ⊗[F] E) := eh.secondCountableTopology
  haveI : T2Space (R ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  set k := Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E))
  set b := bV F E M
  set bR := bVR F E M R
  set e : (Fin M → R ⊗[F] E) ≃ₗ[R] (Fin k → R) := bR.equivFun
  have c1 : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := R) _
  have c2 : Continuous e.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap (R := R) _
  let ec : (Fin M → R ⊗[F] E) ≃ₜ+ (Fin k → R) :=
    { e.toAddEquiv with
      continuous_toFun := by simpa using c1
      continuous_invFun := by simpa using c2 }
  have hec : ∀ u, ec u = e u := fun _ => rfl
  have hecs : ∀ x, ec.symm x = e.symm x := fun _ => rfl
  set μ' := μ.map ec
  have hμ' : μ'.IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  let L : (Fin k → R) →ₗ[R] (Fin k → R) :=
    e.toLinearMap ∘ₗ ((lin R σ J g).restrictScalars R) ∘ₗ e.symm.toLinearMap
  set X := LinearMap.toMatrix' L
  have hX : ∀ x, X.mulVec x = e (lin R σ J g (e.symm x)) := fun x =>
    LinearMap.toMatrix'_mulVec L x
  set G0 : Matrix (Fin k) (Fin k) F := Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))
  set G := G0.map (algebraMap F R)
  have hGu : IsUnit G.det := by
    have hd : G.det = algebraMap F R G0.det := by
      rw [RingHom.map_det]
      rfl
    rw [hd]
    exact (isUnit_iff_ne_zero.2 (trace_gram_nondegenerate F E σ hCM M J hJ k b)).map _
  have hBG : ∀ i j, Bf σ J (bR i) (bR j) = G i j := by
    intro i j
    rw [bVR_apply, bVR_apply, Bf, trace_basis_holds F E R σ M J]
    rfl
  have key : ∀ x y : Fin k → R, Bf σ J (e.symm x) (e.symm y) = x ⬝ᵥ (G *ᵥ y) := by
    intro x y
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Bf_expand]
    simp only [hBG, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rfl
  have e1 : ∀ u w : Fin k → R, u ⬝ᵥ ((X.transpose * G * X) *ᵥ w) = u ⬝ᵥ (G *ᵥ w) := by
    intro u w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, ← key, hX, hX, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Bf_lin, key]
  have hXG : X.transpose * G * X = G := by
    ext i j
    simpa using e1 (Pi.single i 1) (Pi.single j 1)
  have hinv := map_mulVec_eq_of_preserves_form hR1 k G X hGu hXG μ'
  have hlin : (lin R σ J g : (Fin M → R ⊗[F] E) → (Fin M → R ⊗[F] E)) =
      ec.symm ∘ X.mulVec ∘ ec := by
    funext u
    simp only [Function.comp_apply, hec, hecs, hX, LinearEquiv.symm_apply_apply]
  have mec : Measurable ec := ec.continuous.measurable
  have mecs : Measurable ec.symm := ec.symm.continuous.measurable
  have mX : Measurable X.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [hlin, ← Measure.map_map mecs (mX.comp mec), ← Measure.map_map mX mec, hinv,
    Measure.map_map mecs mec]
  have : (ec.symm ∘ ec : (Fin M → R ⊗[F] E) → _) = id := by
    funext u
    simp
  rw [this, Measure.map_id]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM n J hJ v a μ hμ g`. Use `GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v` as an intermediate fact. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_eq_succ hCM.2.2.1`. Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`.

Use `haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _`. Take `⟨eh⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)`. Use `haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eh.secondCountableTopology`. Use `haveI : T2Space (Fv F v ⊗[F] E) := eh.isEmbedding.t2Space`.

Use `haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩`. Set `ν : Measure (Fin n → Fv F v ⊗[F] E)` to `addHaar`. Establish `hmeas : Measurable (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _)` using `(continuous_const.matrix_mulVec continuous_id).measurable`. Establish `hν : ∀ _ : Fin a, MeasurePreserving (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _) ν ν` using `fun _ => ⟨hmeas, map_lin_eq_of_stableRankOne F E σ hCM n J hJ (Fv F v) (stableRankOne_field _) g ν⟩`. Establish `hpi` using `measurePreserving_pi (fun _ : Fin a => ν) (fun _ => ν) hν`.

Establish `e1 : (fun X : Fin a → Fin n → Fv F v ⊗[F] E => g • X) = fun X i => lin (Fv F v) σ J g (X i)` using `rfl`. Rewrite using `[isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin a => ν), Measure.map_smul, e1, hpi.map_eq]`.
-/
theorem haar_tuple_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure → ∀ g : HA (Fv F v) σ J, μ.map (fun X => g • X) = μ := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ hμ g
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eh.secondCountableTopology
  haveI : T2Space (Fv F v ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  let ν : Measure (Fin n → Fv F v ⊗[F] E) := addHaar
  have hmeas : Measurable (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hν : ∀ _ : Fin a, MeasurePreserving (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _) ν ν :=
    fun _ => ⟨hmeas, map_lin_eq_of_stableRankOne F E σ hCM n J hJ (Fv F v) (stableRankOne_field _) g ν⟩
  have hpi := measurePreserving_pi (fun _ : Fin a => ν) (fun _ => ν) hν
  have e1 : (fun X : Fin a → Fin n → Fv F v ⊗[F] E => g • X) =
      fun X i => lin (Fv F v) σ J g (X i) := rfl
  rw [isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin a => ν), Measure.map_smul, e1,
    hpi.map_eq]

end GlobalTheory.LocalUnitaryHaar

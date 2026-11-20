import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AvgPos

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Apply `isCompact_iff_compactSpace.mp` to reduce the goal to its premises. Establish `hK : IsCompact (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : T => Metric.closedBall (0 : ℂ) 1)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1`. Establish `hof : Continuous (Matrix.of : (Fin a → Fin a → T → ℂ) → Matrix (Fin a) (Fin a) (T → ℂ))` using `continuous_id`. Use `(hK.image hof).of_isClosed_subset isClosed_unitary ?_` and prove the remaining obligations. Introduce `U hU`.

Use `⟨Matrix.of.symm U, ?_, by simp⟩` and prove the remaining obligations. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies]`. Introduce `i j t`. Establish `hM : U.map (fun f => f t) ∈ Matrix.unitaryGroup (Fin a) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff]`.

Use extensionality with `k l`. Establish `h : (U * star U) k l t = (1 : Matrix (Fin a) (Fin a) (T → ℂ)) k l t`. Rewrite using `[Unitary.mul_star_self_of_mem hU]`. Distinguish the cases in `hkl : k = l`. Substitute `hkl` using the available equality.

Simplify `h` using `[Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply]`. Simplify `h` using `[Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, hkl]`. Simplify using `using entry_norm_bound_of_unitary hM i j`.
-/
private theorem compactSpace_unitary_matrix_pi_complex (T : Type) [Fintype T] (a : ℕ) :
    CompactSpace (unitary (Matrix (Fin a) (Fin a) (T → ℂ))) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a =>
      Set.univ.pi fun _ : T => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall 0 1
  have hof : Continuous (Matrix.of : (Fin a → Fin a → T → ℂ) → Matrix (Fin a) (Fin a) (T → ℂ)) :=
    continuous_id
  refine (hK.image hof).of_isClosed_subset isClosed_unitary ?_
  intro U hU
  refine ⟨Matrix.of.symm U, ?_, by simp⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro i j t
  have hM : U.map (fun f => f t) ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext k l
    have h : (U * star U) k l t = (1 : Matrix (Fin a) (Fin a) (T → ℂ)) k l t := by
      rw [Unitary.mul_star_self_of_mem hU]
    by_cases hkl : k = l
    · subst hkl
      simpa [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply] using h
    · simpa [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, hkl] using h
  simpa using entry_norm_bound_of_unitary hM i j

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify `continuous_subtype_val` using `[Function.comp_def, Unitary.val_toUnits_apply]`. Simplify using `only [Unitary.val_inv_toUnits_apply]`. Conclude with `continuous_subtype_val.comp continuous_inv`.
-/
private theorem continuous_unitary_toUnits_matrix_pi_complex (T : Type) [Fintype T] (a : ℕ) :
    Continuous (Unitary.toUnits : unitary (Matrix (Fin a) (Fin a) (T → ℂ)) →
      (Matrix (Fin a) (Fin a) (T → ℂ))ˣ) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · simpa [Function.comp_def, Unitary.val_toUnits_apply] using continuous_subtype_val
  · simp only [Unitary.val_inv_toUnits_apply]
    exact continuous_subtype_val.comp continuous_inv

/- English proof (translation)
Establish `hcd : ∃ c : ℝ → GL (Fin a) (T → ℂ), c 0 = 1 ∧ (∀ s, (c s : Matrix (Fin a) (Fin a) (T → ℂ)) ∈ unitary (Matrix (Fin a) (Fin a) (T → ℂ))) ∧ ∀ (i j : Fin a) (t : T), HasDerivAt (fun s => (c s : Matrix (Fin a) (Fin a) (T → ℂ)) i j t) (Y i j t) 0`. Use `letI : NormedRing (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedAlgebra`. Use `letI : NormedAlgebra ℚ (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedAlgebra`. Use `haveI : CompleteSpace (Matrix (Fin a) (Fin a) (T → ℂ)) := FiniteDimensional.complete ℝ _`.

Set `S : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℝ] Matrix (Fin a) (Fin a) (T → ℂ)` to `{ toFun := star map_add' := star_add map_smul' := fun r M => by simp [star_smul] }`. Use `haveI : @ContinuousStar (Matrix (Fin a) (Fin a) (T → ℂ)) PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ := ⟨S.continuous_of_finiteDimensional⟩`. Establish `hmem : ∀ s : ℝ, NormedSpace.exp (s • Y) ∈ unitary (Matrix (Fin a) (Fin a) (T → ℂ))` using `fun s => NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by`. Rewrite using `[skewAdjoint.mem_iff, star_smul, hY]`. Use the proof step `simp)`.

Use `⟨fun s => Unitary.toUnits ⟨NormedSpace.exp (s • Y), hmem s⟩, ?_, fun s => ?_, ?_⟩` and prove the remaining obligations. Use `ext1`. Simplify using `[Unitary.val_toUnits_apply]`. Simplify `hmem s` using `[Unitary.val_toUnits_apply]`. Introduce `i j t`.

Establish `hexp` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)`. Rewrite `hexp` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Set `L0 : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℝ] ℂ` to `{ toFun := fun M => M i j t map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Set `L : Matrix (Fin a) (Fin a) (T → ℂ) →L[ℝ] ℂ` to `⟨L0, L0.continuous_of_finiteDimensional⟩`. Conclude with `L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hexp`.

Take `⟨c, hc0, hcu, hcd⟩` from `hcd`. Establish `hr` using `hR.der c Y hc0 hcd`. Establish `hconst : ∀ s, (R (c s))ᴴ * G * R (c s) = G`. Introduce `s`. Establish `h` using `hinv ⟨c s, hcu s⟩`.

Establish `hu : Unitary.toUnits ⟨(c s : Matrix (Fin a) (Fin a) (T → ℂ)), hcu s⟩ = c s` using `by ext1`. Simplify using `[Unitary.val_toUnits_apply]`. Rewrite `h` using `[hu]`. Then use the resulting hypothesis. Establish `h1 : R (c 0) = 1` using `by rw [hc0, map_one]`. Use extensionality with `i j`.

Establish `e : ∀ s, ((R (c s))ᴴ * G * R (c s)) i j = ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j`. Introduce `s`. Simplify using `[Matrix.mul_apply, Matrix.conjTranspose_apply]`. Establish `hF` using `HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => ((hr k i).star).mul_const (G k l))).mul (hr l j))`. Establish `hF0 : HasDerivAt (fun s => ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j) 0 0`.

Establish `: (fun s => ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j) = fun _ => G i j`. Use function extensionality and compare the values at `s`. Rewrite using `[← e, hconst]`. Rewrite using `[this]`. Conclude with `hasDerivAt_const _ _`.

Establish `hu` using `hF.unique hF0`. Rewrite `hu` using `[h1]`. Simplify using `[Matrix.one_apply] at hu`. Simplify using `[Matrix.mul_apply, Matrix.conjTranspose_apply]`. Simplify `hu` using `[Finset.sum_add_distrib]`.
-/
private theorem conjTranspose_D_mul_add_mul_D_eq_zero_of_skew {T : Type} [Fintype T] {a d : ℕ}
    {R : GL (Fin a) (T → ℂ) →* Matrix (Fin d) (Fin d) ℂ}
    {D : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hR : IsHolRep R D) (G : Matrix (Fin d) (Fin d) ℂ)
    (hinv : ∀ U : unitary (Matrix (Fin a) (Fin a) (T → ℂ)),
      (R (Unitary.toUnits U))ᴴ * G * R (Unitary.toUnits U) = G)
    (Y : Matrix (Fin a) (Fin a) (T → ℂ)) (hY : star Y = -Y) :
    (D Y)ᴴ * G + G * D Y = 0 := by
  have hcd : ∃ c : ℝ → GL (Fin a) (T → ℂ), c 0 = 1 ∧
      (∀ s, (c s : Matrix (Fin a) (Fin a) (T → ℂ)) ∈ unitary (Matrix (Fin a) (Fin a) (T → ℂ))) ∧
      ∀ (i j : Fin a) (t : T), HasDerivAt (fun s => (c s : Matrix (Fin a) (Fin a) (T → ℂ)) i j t)
        (Y i j t) 0 := by
    letI : NormedRing (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℚ (Matrix (Fin a) (Fin a) (T → ℂ)) := Matrix.linftyOpNormedAlgebra
    haveI : CompleteSpace (Matrix (Fin a) (Fin a) (T → ℂ)) := FiniteDimensional.complete ℝ _
    let S : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℝ] Matrix (Fin a) (Fin a) (T → ℂ) :=
      { toFun := star
        map_add' := star_add
        map_smul' := fun r M => by simp [star_smul] }
    haveI : @ContinuousStar (Matrix (Fin a) (Fin a) (T → ℂ))
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ :=
      ⟨S.continuous_of_finiteDimensional⟩
    have hmem : ∀ s : ℝ, NormedSpace.exp (s • Y) ∈ unitary (Matrix (Fin a) (Fin a) (T → ℂ)) :=
      fun s => NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
        rw [skewAdjoint.mem_iff, star_smul, hY]
        simp)
    refine ⟨fun s => Unitary.toUnits ⟨NormedSpace.exp (s • Y), hmem s⟩, ?_, fun s => ?_, ?_⟩
    · ext1
      simp [Unitary.val_toUnits_apply]
    · simpa [Unitary.val_toUnits_apply] using hmem s
    · intro i j t
      have hexp := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
      rw [zero_smul, NormedSpace.exp_zero, one_mul] at hexp
      let L0 : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℝ] ℂ :=
        { toFun := fun M => M i j t
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      let L : Matrix (Fin a) (Fin a) (T → ℂ) →L[ℝ] ℂ := ⟨L0, L0.continuous_of_finiteDimensional⟩
      exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hexp
  obtain ⟨c, hc0, hcu, hcd⟩ := hcd
  have hr := hR.der c Y hc0 hcd
  have hconst : ∀ s, (R (c s))ᴴ * G * R (c s) = G := by
    intro s
    have h := hinv ⟨c s, hcu s⟩
    have hu : Unitary.toUnits ⟨(c s : Matrix (Fin a) (Fin a) (T → ℂ)), hcu s⟩ = c s := by
      ext1
      simp [Unitary.val_toUnits_apply]
    rwa [hu] at h
  have h1 : R (c 0) = 1 := by rw [hc0, map_one]
  ext i j
  have e : ∀ s, ((R (c s))ᴴ * G * R (c s)) i j =
      ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j := by
    intro s
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hF := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
      (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
        ((hr k i).star).mul_const (G k l))).mul (hr l j))
  have hF0 : HasDerivAt (fun s => ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j) 0 0 := by
    have : (fun s => ∑ l, (∑ k, star (R (c s) k i) * G k l) * R (c s) l j) = fun _ => G i j := by
      funext s
      rw [← e, hconst]
    rw [this]
    exact hasDerivAt_const _ _
  have hu := hF.unique hF0
  rw [h1] at hu
  simp [Matrix.one_apply] at hu
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simpa [Finset.sum_add_distrib] using hu

/- English proof (translation)
Introduce `T _ a d R D hR`. Use `haveI := compactSpace_unitary_matrix_pi_complex T a`. Take `⟨G, hG, hinv⟩` from `avgPos (unitary (Matrix (Fin a) (Fin a) (T → ℂ))) d (R.comp Unitary.toUnits) (fun i j => (hR.cont i j).comp (continuous_unitary_toUnits_matrix_pi_complex T a))`. Use `⟨G, hG, fun Z => ?_⟩` and prove the remaining obligations. Take `⟨X, hXd⟩ : ∃ X : Matrix (Fin a) (Fin a) (T → ℂ), X = (1 / 2 : ℂ) • (Z - star Z)` from `⟨_, rfl⟩`.

Take `⟨V, hVd⟩ : ∃ V : Matrix (Fin a) (Fin a) (T → ℂ), V = (-(Complex.I / 2)) • (Z + star Z)` from `⟨_, rfl⟩`. Establish `hX : star X = -X`. Substitute `hXd` using the available equality. Use extensionality with `i j t`. Simplify using `[Matrix.star_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hV : star V = -V`. Substitute `hVd` using the available equality. Use extensionality with `i j t`. Simplify using `[Matrix.star_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hZ : Z = X + Complex.I • V`. Substitute `hXd hVd` using the available equality. Use extensionality with `i j t`. Simplify using the standard rewrite rules.

Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsZ : star Z = -X + Complex.I • V`. Substitute `hXd hVd` using the available equality.

Use extensionality with `i j t`. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `eX : (D X)ᴴ * G = -(G * D X)` using `eq_neg_of_add_eq_zero_left (conjTranspose_D_mul_add_mul_D_eq_zero_of_skew hR G hinv X hX)`. Establish `eV : (D V)ᴴ * G = -(G * D V)` using `eq_neg_of_add_eq_zero_left (conjTranspose_D_mul_add_mul_D_eq_zero_of_skew hR G hinv V hV)`. Establish `hDZ : D Z = D X + Complex.I • D V` using `by conv_lhs => rw [hZ]`. Rewrite using `[map_add, map_smul]`. Rewrite using `[hDZ, hsZ, map_add, map_neg, map_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.smul_mul, eX, eV, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul]`.

Simplify using `[Complex.star_def]`.
-/
theorem UpperTheory.V.Lit.Bor.admissible_abs_bound :
    UpperTheory.V.Lit.Bor.AdmAbs := by
  intro T _ a d R D hR
  haveI := compactSpace_unitary_matrix_pi_complex T a
  obtain ⟨G, hG, hinv⟩ := avgPos (unitary (Matrix (Fin a) (Fin a) (T → ℂ))) d
    (R.comp Unitary.toUnits) (fun i j => (hR.cont i j).comp (continuous_unitary_toUnits_matrix_pi_complex T a))
  refine ⟨G, hG, fun Z => ?_⟩
  obtain ⟨X, hXd⟩ : ∃ X : Matrix (Fin a) (Fin a) (T → ℂ), X = (1 / 2 : ℂ) • (Z - star Z) := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : Matrix (Fin a) (Fin a) (T → ℂ),
      V = (-(Complex.I / 2)) • (Z + star Z) := ⟨_, rfl⟩
  have hX : star X = -X := by
    subst hXd
    ext i j t
    simp [Matrix.star_apply]
    ring
  have hV : star V = -V := by
    subst hVd
    ext i j t
    simp [Matrix.star_apply]
    ring
  have hZ : Z = X + Complex.I • V := by
    subst hXd hVd
    ext i j t
    simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have hsZ : star Z = -X + Complex.I • V := by
    subst hXd hVd
    ext i j t
    simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have eX : (D X)ᴴ * G = -(G * D X) :=
    eq_neg_of_add_eq_zero_left (conjTranspose_D_mul_add_mul_D_eq_zero_of_skew hR G hinv X hX)
  have eV : (D V)ᴴ * G = -(G * D V) :=
    eq_neg_of_add_eq_zero_left (conjTranspose_D_mul_add_mul_D_eq_zero_of_skew hR G hinv V hV)
  have hDZ : D Z = D X + Complex.I • D V := by
    conv_lhs => rw [hZ]
    rw [map_add, map_smul]
  rw [hDZ, hsZ, map_add, map_neg, map_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.add_mul, Matrix.smul_mul, eX, eV, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul]
  simp [Complex.star_def]

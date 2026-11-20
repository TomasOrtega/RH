import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, TrivSqZeroExt.fst_sum]`.
-/
private theorem rigDiag_fst_mul {K : Type} [Field K] (M N : Matrix (Fin 3) (Fin 3) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.fst = M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.fst := by
  ext i j
  simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, Finset.sum_add_distrib]`.
-/
private theorem rigDiag_snd_mul {K : Type} [Field K] (M N : Matrix (Fin 3) (Fin 3) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.snd =
      M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.snd + M.map TrivSqZeroExt.snd * N.map TrivSqZeroExt.fst := by
  ext i j
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[conjBy, GG.mat, GG.ofGL, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, hs]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units h), Matrix.one_mul]`.
-/
private theorem rigDiag_conj_mat {R D : Type} [CommRing R] [Group D] (h : GL (Fin 3) R) (r : D →* GG 3 R) (s : D)
    (hs : (r s).right = 1) :
    (h : Matrix (Fin 3) (Fin 3) R) * (conjBy h⁻¹ r s).mat = (r s).mat * h := by
  simp [conjBy, GG.mat, GG.ofGL, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, hs]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units h), Matrix.one_mul]

/- English proof (translation)
Introduce `O K D _ _ _ _ _ η Ψ I r y r' h hI hm hd hD`. Use `set H : Matrix (Fin 3) (Fin 3) (DualNumber K) := (h : Matrix (Fin 3) (Fin 3) (DualNumber K)) with hH`. Use `set Hi : Matrix (Fin 3) (Fin 3) (DualNumber K) := (↑h⁻¹ : Matrix (Fin 3) (Fin 3) (DualNumber K)) with hHi`. Use `⟨-(H.map TrivSqZeroExt.snd * Hi.map TrivSqZeroExt.fst), fun s hs => ?_⟩` and prove the remaining obligations. Establish `hη : η s = 1` using `hI s hs`.

Establish `hr1 : (r s).right = 1` using `(hm s).trans hη`. Establish `hd1` using `hd s`. Establish `hr'1 : (r' s).right = 1`. Rewrite using `[hd1.1]`. Simplify `hr1` using `[GG.map]`.

Establish `hmat : (r' s).mat = (1 + (y s).map TrivSqZeroExt.inr) * (r s).mat.map (algebraMap K (DualNumber K))`. Rewrite using `[hd1.2]`. Simplify using `[GG.map, GG.mat]`. Establish `hker : s ∈ η.ker` using `hη`. Establish `hoff : ∀ a b, ((conjBy h⁻¹ r' s).mat a b).snd = 0`.

Introduce `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[hD.ine s hs hη a]`. Both sides reduce to the same expression.

Break down `lt_or_gt_of_ne (show wt a b ≠ 0 by revert a b; decide) with hlt | hlt` into its components or cases. Rewrite using `[hD.tri s hker a b hlt]`. Both sides reduce to the same expression. Rewrite using `[hD.low s hker a b hlt]`. Both sides reduce to the same expression.

Use `set C := (conjBy h⁻¹ r' s).mat with hC`. Use `set R := (r s).mat with hR`. Use `set h0 := H.map TrivSqZeroExt.fst`. Use `set h1 := H.map TrivSqZeroExt.snd`. Use `set g0 := Hi.map TrivSqZeroExt.fst`.

Use `set C0 := C.map TrivSqZeroExt.fst`. Establish `hc : H * C = (r' s).mat * H` using `rigDiag_conj_mat h r' s hr'1`. Establish `hCs : C.map TrivSqZeroExt.snd = 0`. Use extensionality with `a b`. Conclude with `hoff a b`.

Establish `hM0 : (r' s).mat.map TrivSqZeroExt.fst = R`. Rewrite using `[hmat, rigDiag_fst_mul]`. Use extensionality with `a b`. Simplify using `[Matrix.one_apply, Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, apply_ite TrivSqZeroExt.fst, ite_mul]`. Establish `hM1 : (r' s).mat.map TrivSqZeroExt.snd = y s * R`.

Rewrite using `[hmat, rigDiag_snd_mul]`. Use extensionality with `a b`. Simplify using `[Matrix.one_apply, Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, apply_ite TrivSqZeroExt.fst, apply_ite TrivSqZeroExt.snd, ite_mul]`. Establish `e0 : h0 * C0 = R * h0`. Use `congrArg (fun M => M.map TrivSqZeroExt.fst) hc` as an intermediate fact.

Simplify `this` using `only [rigDiag_fst_mul, hM0]`. Establish `e1 : h1 * C0 = R * h1 + y s * R * h0`. Use `congrArg (fun M => M.map TrivSqZeroExt.snd) hc` as an intermediate fact. Simplify using `only [rigDiag_snd_mul, hM0, hM1, hCs, Matrix.mul_zero, zero_add] at this`. Conclude with `this`.

Establish `hinv1 : Hi * H = 1`. Rewrite using `[hHi, hH, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hinv2 : H * Hi = 1`. Rewrite using `[hHi, hH, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hgh : g0 * h0 = 1`.

Use `congrArg (fun M => M.map TrivSqZeroExt.fst) hinv1` as an intermediate fact. Simplify using `only [rigDiag_fst_mul] at this`. Rewrite using `[this]`. Use extensionality with `a b`. Simplify using `[Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> rfl`. Establish `hhg : h0 * g0 = 1`. Use `congrArg (fun M => M.map TrivSqZeroExt.fst) hinv2` as an intermediate fact. Simplify using `only [rigDiag_fst_mul] at this`. Rewrite using `[this]`.

Use extensionality with `a b`. Simplify using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`. Establish `hRR : R * (↑(r s).left⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1`. Rewrite using `[hR, GG.mat, ← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `e2 : C0 = g0 * R * h0`. Rewrite using `[← one_mul C0, ← hgh, mul_assoc, e0, ← mul_assoc]`. Establish `e3 : y s * R = h1 * g0 * R - R * (h1 * g0)`. Establish `k : y s * R * h0 = h1 * C0 - R * h1`. Rewrite using `[e1]`.

Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2]`. Simplify using `only [sub_mul, mul_assoc, hhg, mul_one]`. Establish `e4 : y s = y s * R * (↑(r s).left⁻¹ : Matrix (Fin 3) (Fin 3) K)`.

Rewrite using `[mul_assoc, hRR, mul_one]`. Rewrite using `[e4, e3]`. Simplify using `only [adRep, GG.ad, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, GG.adFun, hr1, if_true]`. Rewrite using `[← hR]`. Simplify using `only [sub_mul, mul_assoc, hRR, mul_one, mul_neg, neg_mul, sub_neg_eq_add]`.

Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.V.UnitaryThreeInertia.rig_diag :
    ∀ {O K D : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K] [Group D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 K) (y : D → Matrix (Fin 3) (Fin 3) K) (r' : D →* GG 3 (DualNumber K)) (h : GL (Fin 3) (DualNumber K)), (∀ s ∈ I, η s = 1) → HasMult η r → IsDeform ((GG.map (algebraMap K (DualNumber K))).comp r) (fun g => (y g).map (TrivSqZeroExt.inr : K → DualNumber K)) r' → DiagIn η Ψ I r' h → ∃ X, ∀ s ∈ I, y s = adRep r s X - X := by
  intro O K D _ _ _ _ _ η Ψ I r y r' h hI hm hd hD
  set H : Matrix (Fin 3) (Fin 3) (DualNumber K) := (h : Matrix (Fin 3) (Fin 3) (DualNumber K)) with hH
  set Hi : Matrix (Fin 3) (Fin 3) (DualNumber K) := (↑h⁻¹ : Matrix (Fin 3) (Fin 3) (DualNumber K)) with hHi
  refine ⟨-(H.map TrivSqZeroExt.snd * Hi.map TrivSqZeroExt.fst), fun s hs => ?_⟩
  have hη : η s = 1 := hI s hs
  have hr1 : (r s).right = 1 := (hm s).trans hη
  have hd1 := hd s
  have hr'1 : (r' s).right = 1 := by
    rw [hd1.1]
    simpa [GG.map] using hr1
  have hmat : (r' s).mat = (1 + (y s).map TrivSqZeroExt.inr) * (r s).mat.map (algebraMap K (DualNumber K)) := by
    rw [hd1.2]
    simp [GG.map, GG.mat]
  have hker : s ∈ η.ker := hη
  have hoff : ∀ a b, ((conjBy h⁻¹ r' s).mat a b).snd = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [hD.ine s hs hη a]
      rfl
    · rcases lt_or_gt_of_ne (show wt a b ≠ 0 by revert a b; decide) with hlt | hlt
      · rw [hD.tri s hker a b hlt]
        rfl
      · rw [hD.low s hker a b hlt]
        rfl
  set C := (conjBy h⁻¹ r' s).mat with hC
  set R := (r s).mat with hR
  set h0 := H.map TrivSqZeroExt.fst
  set h1 := H.map TrivSqZeroExt.snd
  set g0 := Hi.map TrivSqZeroExt.fst
  set C0 := C.map TrivSqZeroExt.fst
  have hc : H * C = (r' s).mat * H := rigDiag_conj_mat h r' s hr'1
  have hCs : C.map TrivSqZeroExt.snd = 0 := by
    ext a b
    exact hoff a b
  have hM0 : (r' s).mat.map TrivSqZeroExt.fst = R := by
    rw [hmat, rigDiag_fst_mul]
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, apply_ite TrivSqZeroExt.fst, ite_mul]
  have hM1 : (r' s).mat.map TrivSqZeroExt.snd = y s * R := by
    rw [hmat, rigDiag_snd_mul]
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, apply_ite TrivSqZeroExt.fst, apply_ite TrivSqZeroExt.snd, ite_mul]
  have e0 : h0 * C0 = R * h0 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hc
    simpa only [rigDiag_fst_mul, hM0] using this
  have e1 : h1 * C0 = R * h1 + y s * R * h0 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.snd) hc
    simp only [rigDiag_snd_mul, hM0, hM1, hCs, Matrix.mul_zero, zero_add] at this
    exact this
  have hinv1 : Hi * H = 1 := by
    rw [hHi, hH, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv2 : H * Hi = 1 := by
    rw [hHi, hH, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgh : g0 * h0 = 1 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hinv1
    simp only [rigDiag_fst_mul] at this
    rw [this]
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> rfl
  have hhg : h0 * g0 = 1 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hinv2
    simp only [rigDiag_fst_mul] at this
    rw [this]
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> rfl
  have hRR : R * (↑(r s).left⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hR, GG.mat, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : C0 = g0 * R * h0 := by
    rw [← one_mul C0, ← hgh, mul_assoc, e0, ← mul_assoc]
  have e3 : y s * R = h1 * g0 * R - R * (h1 * g0) := by
    have k : y s * R * h0 = h1 * C0 - R * h1 := by
      rw [e1]
      abel
    calc y s * R = y s * R * h0 * g0 := by rw [mul_assoc (y s * R), hhg, mul_one]
      _ = (h1 * C0 - R * h1) * g0 := by rw [k]
      _ = h1 * g0 * R - R * (h1 * g0) := by
        rw [e2]
        simp only [sub_mul, mul_assoc, hhg, mul_one]
  have e4 : y s = y s * R * (↑(r s).left⁻¹ : Matrix (Fin 3) (Fin 3) K) := by
    rw [mul_assoc, hRR, mul_one]
  rw [e4, e3]
  simp only [adRep, GG.ad, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, GG.adFun, hr1, if_true]
  rw [← hR]
  simp only [sub_mul, mul_assoc, hRR, mul_one, mul_neg, neg_mul, sub_neg_eq_add]
  abel

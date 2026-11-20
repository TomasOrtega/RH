import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExpFromBlocks

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.UnitaryDecomposition.Com

open Formalism.REAL PI.DSInfCharCap CompanionTheory.D.Upq.Sm

variable {n : ℕ} (e : Fin n ⊕ Unit ≃ Fin (n + 1))

def blk : Matrix (Fin n) (Fin n) ℂ × ℂ →ₐ[ℂ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ where
  toFun p := Matrix.reindex e e (Matrix.fromBlocks p.1 0 0 (p.2 • 1))
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul]
    simp [smul_smul, mul_comm]
  map_zero' := by simp
  map_add' p q := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp [add_smul]
  commutes' c := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blk_apply (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    blk e (A, c) = Matrix.reindex e e (Matrix.fromBlocks A 0 0 (c • 1)) := rfl

/- English proof (translation)
Simplify using `[emb, blk_apply]`.
-/
theorem emb_eq (A : Matrix (Fin n) (Fin n) ℂ) : emb e A = blk e (A, 1) := by simp [emb, blk_apply]

/- English proof (translation)
Simplify using `[blk_apply, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]`.
-/
theorem blk_ct (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) : (blk e (A, c))ᴴ = blk e (Aᴴ, star c) := by
  simp [blk_apply, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

/- English proof (translation)
Use extensionality with `i j`. Take `⟨i, rfl⟩` from `e.surjective i`. Take `⟨j, rfl⟩` from `e.surjective j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [blk_apply, Matrix.single_apply]`.
-/
theorem blk_single (a b : Fin n) :
    blk e (Matrix.single a b 1, 0) = Matrix.single (e (Sum.inl a)) (e (Sum.inl b)) 1 := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [blk_apply, Matrix.single_apply]

variable {e} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool}

/- English proof (translation)
Use extensionality with `i j`. Take `⟨i, rfl⟩` from `e.surjective i`. Take `⟨j, rfl⟩` from `e.surjective j`. Establish `h1 : ε (e (Sum.inr ())) = true` using `hF.1`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [blk_apply, Jm, Matrix.diagonal_apply, hF.2, h1]`.
-/
theorem blk_J (hF : Fits ε ε' e) : Jm ε = blk e (Jm ε', 1) := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  have h1 : ε (e (Sum.inr ())) = true := hF.1
  rcases i with i | i <;> rcases j with j | j <;> simp [blk_apply, Jm, Matrix.diagonal_apply, hF.2, h1]

/- English proof (translation)
Rewrite using `[emb_eq, blk_ct, blk_J hF, ← map_mul, ← map_mul]`. Simplify using `[hh]`.
-/
theorem emb_mem (hF : Fits ε ε' e) {h : Matrix (Fin n) (Fin n) ℂ} (hh : hᴴ * Jm ε' * h = Jm ε') :
    (emb e h)ᴴ * Jm ε * emb e h = Jm ε := by
  rw [emb_eq, blk_ct, blk_J hF, ← map_mul, ← map_mul]
  simp [hh]

/- English proof (translation)
Unfold `thetaJ`. Rewrite using `[blk_ct, blk_J hF, ← map_mul, ← map_mul, ← map_neg]`. Simplify using the standard rewrite rules.
-/
theorem blk_theta (hF : Fits ε ε' e) (Y : Matrix (Fin n) (Fin n) ℂ) : thetaJ ε (blk e (Y, 0)) = blk e (thetaJ ε' Y, 0) := by
  unfold thetaJ
  rw [blk_ct, blk_J hF, ← map_mul, ← map_mul, ← map_neg]
  simp

/- English proof (translation)
Rewrite using `[blk_apply, Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.exp_reindex, Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.exp_fromBlocks, zero_smul, NormedSpace.exp_zero]`. Both sides reduce to the same expression.
-/
theorem exp_blk (X : Matrix (Fin n) (Fin n) ℂ) : NormedSpace.exp (blk e (X, 0)) = emb e (NormedSpace.exp X) := by
  rw [blk_apply, Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.exp_reindex, Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.exp_fromBlocks, zero_smul, NormedSpace.exp_zero]
  rfl

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `h : emb e = fun A => (LinearMap.toContinuousLinearMap (((blk e).toLinearMap ∘ₗ LinearMap.inl ℂ _ ℂ).restrictScalars ℝ)) A + blk e (0, 1)`. Use function extensionality and compare the values at `A`. Use `show _ = blk e (A, 0) + blk e (0, 1)`. Rewrite using `[← map_add, emb_eq]`. Simplify using the standard rewrite rules.

Rewrite using `[h]`. Conclude with `(ContinuousLinearMap.contDiff _).add contDiff_const`.
-/
theorem contDiff_emb : ContDiff ℝ ∞ (emb e) := by
  have h : emb e = fun A => (LinearMap.toContinuousLinearMap
      (((blk e).toLinearMap ∘ₗ LinearMap.inl ℂ _ ℂ).restrictScalars ℝ)) A + blk e (0, 1) := by
    funext A
    show _ = blk e (A, 0) + blk e (0, 1)
    rw [← map_add, emb_eq]; simp
  rw [h]
  exact (ContinuousLinearMap.contDiff _).add contDiff_const

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)} {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} {P : H →L[ℂ] H'}

/- English proof (translation)
Establish `h1 : (Jm ε' * hᴴ * Jm ε') * h = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh, Jm_mul_self]`. Conclude with `hP.2 ⟨⟨h, _, mul_eq_one_comm.1 h1, h1⟩, hh⟩ x`.
-/
theorem intertw_mat (hP : Intertw ε' e π σ P) {h : Matrix (Fin n) (Fin n) ℂ} (hh : hᴴ * Jm ε' * h = Jm ε') (x : H) :
    P (π (emb e h) x) = σ h (P x) := by
  have h1 : (Jm ε' * hᴴ * Jm ε') * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh, Jm_mul_self]
  exact hP.2 ⟨⟨h, _, mul_eq_one_comm.1 h1, h1⟩, hh⟩ x

/- English proof (translation)
Establish `h1 : IsSm (PI.PhMeasCore.UH (Jm ε)) π η` using `hη`. Establish `h2` using `(SmOn.comp h1 (contDiff_emb (e := e)) (B := PI.PhMeasCore.UH (Jm ε')) fun h hh => emb_mem hF hh).clm (P.restrictScalars ℝ)`. Conclude with `SmOn.congr h2 fun h hh => (intertw_mat hP hh η).symm`.
-/
theorem smooth_map (hF : Fits ε ε' e) (hP : Intertw ε' e π σ P) {η : H} (hη : η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π) :
    P η ∈ PI.PhMeasCore.smoothVecs (Jm ε') σ := by
  have h1 : IsSm (PI.PhMeasCore.UH (Jm ε)) π η := hη
  have h2 := (SmOn.comp h1 (contDiff_emb (e := e)) (B := PI.PhMeasCore.UH (Jm ε')) fun h hh => emb_mem hF hh).clm
    (P.restrictScalars ℝ)
  exact SmOn.congr h2 fun h hh => (intertw_mat hP hh η).symm

/- English proof (translation)
Establish `h1` using `(P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt`. Establish `h2 : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (P η)) = (P.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • blk e (X, 0))) η`. Use function extensionality and compare the values at `t`. Establish `e1 : (t : ℂ) • blk e (X, 0) = blk e ((t : ℂ) • X, 0)` using `by rw [← map_smul]; simp`. Use `show _ = P (π (NormedSpace.exp ((t : ℂ) • blk e (X, 0))) η)`.

Rewrite using `[e1, exp_blk]`. Conclude with `(intertw_mat hP (ex_mem_of_lie hX t) η).symm`. Unfold `PI.PhMeasCore.dsig`. Rewrite using `[h2, h1.deriv]`. Both sides reduce to the same expression.
-/
theorem dsig_map (hP : Intertw ε' e π σ P) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε' X) {η : H}
    (hd : DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • blk e (X, 0))) η) 0) :
    P (PI.PhMeasCore.dsig π (blk e (X, 0)) η) = PI.PhMeasCore.dsig σ X (P η) := by
  have h1 := (P.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
  have h2 : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (P η)) =
      (P.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • blk e (X, 0))) η := by
    funext t
    have e1 : (t : ℂ) • blk e (X, 0) = blk e ((t : ℂ) • X, 0) := by rw [← map_smul]; simp
    show _ = P (π (NormedSpace.exp ((t : ℂ) • blk e (X, 0))) η)
    rw [e1, exp_blk]
    exact (intertw_mat hP (ex_mem_of_lie hX t) η).symm
  unfold PI.PhMeasCore.dsig
  rw [h2, h1.deriv]
  rfl

/- English proof (translation)
Unfold `inG at hX ⊢`. Rewrite using `[blk_ct, blk_J hF, ← map_mul, ← map_mul, ← map_add]`. Simplify using `[hX, ← Prod.zero_eq_mk]`.
-/
theorem blk_inG (hF : Fits ε ε' e) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε' X) : inG ε (blk e (X, 0)) := by
  unfold inG at hX ⊢
  rw [blk_ct, blk_J hF, ← map_mul, ← map_mul, ← map_add]
  simp [hX, ← Prod.zero_eq_mk]

/- English proof (translation)
Establish `hJ : (Jm ε')ᴴ = Jm ε'`. Unfold `Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `by_cases h : ε' a <;> simp [h]`. Establish `a1 : Jm ε' * Y * Jm ε' * Jm ε' = Jm ε' * Y` using `by rw [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]`. Establish `a2 : Jm ε' * (Jm ε' * Yᴴ * Jm ε') = Yᴴ * Jm ε'`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]`. Establish `hθ : (thetaJ ε' Y)ᴴ * Jm ε' = -(Jm ε' * Y)`.

Unfold `thetaJ`. Rewrite using `[Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose, Matrix.neg_mul, ← Matrix.mul_assoc, a1]`. Establish `hθ' : Jm ε' * thetaJ ε' Y = -(Yᴴ * Jm ε')`. Unfold `thetaJ`. Rewrite using `[Matrix.mul_neg, a2]`.

Unfold `inG`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, hθ, hθ', show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_add]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, hθ, hθ', show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul, ← sub_eq_neg_add, ← smul_sub]`.

Simplify using `[add_comm]`.
-/
theorem inG_parts (Y : Matrix (Fin n) (Fin n) ℂ) :
    inG ε' ((1 / 2 : ℂ) • (Y + thetaJ ε' Y)) ∧ inG ε' ((1 / (2 * Complex.I)) • (Y - thetaJ ε' Y)) := by
  have hJ : (Jm ε')ᴴ = Jm ε' := by
    unfold Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε' a <;> simp [h]
  have a1 : Jm ε' * Y * Jm ε' * Jm ε' = Jm ε' * Y := by rw [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
  have a2 : Jm ε' * (Jm ε' * Yᴴ * Jm ε') = Yᴴ * Jm ε' := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have hθ : (thetaJ ε' Y)ᴴ * Jm ε' = -(Jm ε' * Y) := by
    unfold thetaJ
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose,
      Matrix.neg_mul, ← Matrix.mul_assoc, a1]
  have hθ' : Jm ε' * thetaJ ε' Y = -(Yᴴ * Jm ε') := by
    unfold thetaJ
    rw [Matrix.mul_neg, a2]
  unfold inG
  constructor
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
      Matrix.mul_add, hθ, hθ', show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_add]
    simp
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.mul_sub, hθ, hθ', show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul, ← sub_eq_neg_add,
      ← smul_sub]
    simp [add_comm]

/- English proof (translation)
Establish `e1 : (1 / 2 : ℂ) • (blk e (Y, 0) + thetaJ ε (blk e (Y, 0))) = blk e ((1 / 2 : ℂ) • (Y + thetaJ ε' Y), 0)`. Rewrite using `[blk_theta hF, ← map_add, ← map_smul]`. Simplify using the standard rewrite rules. Establish `e2 : (1 / (2 * Complex.I)) • (blk e (Y, 0) - thetaJ ε (blk e (Y, 0))) = blk e ((1 / (2 * Complex.I)) • (Y - thetaJ ε' Y), 0)`. Rewrite using `[blk_theta hF, ← map_sub, ← map_smul]`.

Simplify using the standard rewrite rules. Unfold `dsigC`. Rewrite using `[e1, e2, map_add, map_smul, dsig_map hP (inG_parts Y).1 (hd _ (blk_inG hF (inG_parts Y).1)), dsig_map hP (inG_parts Y).2 (hd _ (blk_inG hF (inG_parts Y).2))]`.
-/
theorem dsigC_map (hF : Fits ε ε' e) (hP : Intertw ε' e π σ P) {η : H}
    (hd : ∀ X, inG ε X → DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) η) 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) : P (dsigC ε π (blk e (Y, 0)) η) = dsigC ε' σ Y (P η) := by
  have e1 : (1 / 2 : ℂ) • (blk e (Y, 0) + thetaJ ε (blk e (Y, 0))) = blk e ((1 / 2 : ℂ) • (Y + thetaJ ε' Y), 0) := by
    rw [blk_theta hF, ← map_add, ← map_smul]; simp
  have e2 : (1 / (2 * Complex.I)) • (blk e (Y, 0) - thetaJ ε (blk e (Y, 0))) =
      blk e ((1 / (2 * Complex.I)) • (Y - thetaJ ε' Y), 0) := by
    rw [blk_theta hF, ← map_sub, ← map_smul]; simp
  unfold dsigC
  rw [e1, e2, map_add, map_smul, dsig_map hP (inG_parts Y).1 (hd _ (blk_inG hF (inG_parts Y).1)),
    dsig_map hP (inG_parts Y).2 (hd _ (blk_inG hF (inG_parts Y).2))]

end PositivityTheory.UnitaryDecomposition.Com

import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.BurGapOfHyp
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGapAlt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsIsCayleyUIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.HermitianFormPosCongruentIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.IsFrameExistsIsotropicDualColumns
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.HyperbolicFrameCongruentSplitHermGram
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SylvesterInertiaSignFormCongrSplitHermitian
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.ContIrredCompactUnitaryGroupRepIsUnitarizable
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.IrreducibleUnitaryRepIsoHarishChandraType
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.ContragredientConjDefiniteUnitaryIsContIrred
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SmoothVecConjugateUnitaryGroupIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SobolevContOfConjGramForm
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.CasselmanWallachContFiniteSumSobolevForms
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.MemBesselUnipotentRadicalOfMemCoordGroup
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.IsometryConjMapsUnipotentRadical
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.BlockEmbedConjIsUnitaryEmbedding
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.SmoothVecStableUnderUnitaryGroup

noncomputable section

namespace UpperTheory.Lit.Bur.BurPos

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

/- English proof (translation)
Distinguish the cases in `h0 : S = ⊥`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h0`. Use `rank_le_one_iff.2 ⟨⟨x, hx⟩, fun y => ?_⟩` and prove the remaining obligations.

Take `⟨a, b, hab, e⟩` from `h x hx y y.2`. Establish `hb : b ≠ 0`. Introduce and unpack `rfl`. Break down `hab with ha | hb` into its components or cases. Simplify using `only [zero_smul, add_zero] at e`.

Conclude with `(smul_ne_zero ha hx0) e`. Conclude with `hb rfl`. Use `⟨-(b⁻¹ * a), Subtype.ext ?_⟩` and prove the remaining obligations. Establish `e' : (y : V) = -(b⁻¹ * a) • x`. Establish `: b • (y : V) = -(a • x)` using `by rw [eq_neg_iff_add_eq_zero, add_comm]; exact e`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `using e'.symm`.
-/
theorem rank_le_one_of_dep {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V)
    (h : ∀ x ∈ S, ∀ y ∈ S, ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • x + b • y = 0) : Module.rank ℂ S ≤ 1 := by
  by_cases h0 : S = ⊥
  · subst h0; simp
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  refine rank_le_one_iff.2 ⟨⟨x, hx⟩, fun y => ?_⟩
  obtain ⟨a, b, hab, e⟩ := h x hx y y.2
  have hb : b ≠ 0 := by
    rintro rfl
    rcases hab with ha | hb
    · simp only [zero_smul, add_zero] at e
      exact (smul_ne_zero ha hx0) e
    · exact hb rfl
  refine ⟨-(b⁻¹ * a), Subtype.ext ?_⟩
  have e' : (y : V) = -(b⁻¹ * a) • x := by
    have : b • (y : V) = -(a • x) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact e
    calc (y : V) = b⁻¹ • (b • (y : V)) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = -(b⁻¹ * a) • x := by rw [this, smul_neg, smul_smul, neg_smul]
  simpa using e'.symm

/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det fr).1 hfr`. Establish `g1 : (fr * Q) * (Qi * fr⁻¹) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc Q, h1, Matrix.one_mul, mul_nonsing_inv _ hd]`. Establish `g2 : (Qi * fr⁻¹) * (fr * Q) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc fr⁻¹, nonsing_inv_mul _ hd, Matrix.one_mul, h2]`.

Establish `gg : (fr * Q)ᴴ * Formalism.REAL.Jm ε * (fr * Q) = Formalism.QuantumDeterminants.Hpk m r`. Rewrite using `[← hg, ← hJ]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Establish `hc` using `UpperTheory.Lit.Bur.sylvester_inertia_signForm_congr_splitHermitian ε g1 g2 gg`. Take `⟨P, hP⟩` from `(GlobalTheory.UnitaryCayley.exists_isCayleyU_iff m r ε).2 hc`.

Use `⟨P, hP, ?_⟩` and prove the remaining obligations. Use `Formalism.L2.SG.Pf.Choice.dsHpk_tr rfl ε ε (fun _ => rfl) lam lam (fun _ => rfl) _ hds (fr * Q) (Qi * fr⁻¹) g1 gg P hP` as an intermediate fact. Establish `e : (fun g => σ (fr⁻¹ * (fr * Q * (P⁻¹ * g * P) * (Qi * fr⁻¹)) * fr)) = fun g => σ (Q * (P⁻¹ * g * P) * Qi)`. Use function extensionality and compare the values at `g`. Use `congr 1`.

Establish `e1 : fr⁻¹ * (fr * Q * (P⁻¹ * g * P) * (Qi * fr⁻¹)) * fr = (fr⁻¹ * fr) * Q * (P⁻¹ * g * P) * Qi * (fr⁻¹ * fr)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e1, nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_one]`. Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem isDSHpk_tr {m r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ → (H →L[ℂ] H)}
    {J Q Qi fr : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} {ε : Fin (2 * r + m + 1) → Bool}
    {lam : Fin (2 * r + m + 1) → ℝ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r)
    (hfr : IsUnit fr) (hJ : frᴴ * Formalism.REAL.Jm ε * fr = J) (hds : Formalism.MainNotions.S.IsDS ε lam (fun g => σ (fr⁻¹ * g * fr))) :
    PI.UpqRep.IsDSHpk m r ε lam (fun g => σ (Q * g * Qi)) := by
  have hd := (Matrix.isUnit_iff_isUnit_det fr).1 hfr
  have g1 : (fr * Q) * (Qi * fr⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, h1, Matrix.one_mul, mul_nonsing_inv _ hd]
  have g2 : (Qi * fr⁻¹) * (fr * Q) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc fr⁻¹, nonsing_inv_mul _ hd, Matrix.one_mul, h2]
  have gg : (fr * Q)ᴴ * Formalism.REAL.Jm ε * (fr * Q) = Formalism.QuantumDeterminants.Hpk m r := by
    rw [← hg, ← hJ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
  have hc := UpperTheory.Lit.Bur.sylvester_inertia_signForm_congr_splitHermitian ε g1 g2 gg
  obtain ⟨P, hP⟩ := (GlobalTheory.UnitaryCayley.exists_isCayleyU_iff m r ε).2 hc
  refine ⟨P, hP, ?_⟩
  have := Formalism.L2.SG.Pf.Choice.dsHpk_tr rfl ε ε (fun _ => rfl) lam lam (fun _ => rfl) _ hds (fr * Q) (Qi * fr⁻¹) g1 gg P hP
  have e : (fun g => σ (fr⁻¹ * (fr * Q * (P⁻¹ * g * P) * (Qi * fr⁻¹)) * fr)) = fun g => σ (Q * (P⁻¹ * g * P) * Qi) := by
    funext g
    congr 1
    have e1 : fr⁻¹ * (fr * Q * (P⁻¹ * g * P) * (Qi * fr⁻¹)) * fr = (fr⁻¹ * fr) * Q * (P⁻¹ * g * P) * Qi * (fr⁻¹ * fr) := by
      simp only [Matrix.mul_assoc]
    rw [e1, nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_one]
  rw [e] at this
  exact this

/- English proof (translation)
Establish `h0 : J₀ᴴ = J₀`. Rewrite using `[← hf.gram]`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hf.herm, Matrix.mul_assoc]`. Take `⟨A, Ai, a1, a2, a3⟩` from `UpperTheory.Lit.Bur.hermitian_form_pos_congruent_identity h0 hp`. Take `⟨f, f1, f2, f3, f4⟩` from `UpperTheory.Lit.Bur.isFrame_exists_isotropic_dual_columns hf`.

Establish `hreal : Formalism.QuantumDeterminants.herm J z z = (((Formalism.QuantumDeterminants.herm J z z).re : ℝ) : ℂ)`. Establish `hc : star (Formalism.QuantumDeterminants.herm J z z) = Formalism.QuantumDeterminants.herm J z z`. Unfold `Formalism.QuantumDeterminants.herm`. Use `conv_rhs => rw [star_dotProduct, star_mulVec, hf.herm, ← dotProduct_mulVec]`. Conclude with `(Complex.conj_eq_iff_re.1 hc).symm`.

Use `set T : ℝ := -(Formalism.QuantumDeterminants.herm J z z).re with hT`. Establish `hTp : 0 < T` using `by simpa [hT] using hz`. Use `set t : ℝ := Real.sqrt T with ht`. Establish `htp : 0 < t` using `Real.sqrt_pos.2 hTp`. Establish `htc : (t : ℂ) ≠ 0` using `by exact_mod_cast htp.ne'`.

Establish `hsq : t * t = T` using `Real.mul_self_sqrt hTp.le`. Take `⟨Q, Qi, q1, q2, qg, qe, qw, qy⟩` from `UpperTheory.Lit.Bur.hyperbolic_frame_congruent_splitHermGram (Fa := F * A) (e := e) (f := f) (y := (t⁻¹ : ℂ) • z) hf.herm (by rw [conjTranspose_mul]; calc _ = Aᴴ * (Fᴴ * J * F) * A := by simp only [Matrix.mul_assoc] _ = 1 := by rw [hf.gram, a3]) hf.e_iso f2 f1 (by rw [conjTranspo …`. Establish `e1 : Formalism.QuantumDeterminants.herm J ((t⁻¹ : ℂ) • z) ((t⁻¹ : ℂ) • z) = (t⁻¹ : ℂ) * (t⁻¹ : ℂ) * Formalism.QuantumDeterminants.herm J z z`. Unfold `Formalism.QuantumDeterminants.herm`. Rewrite using `[mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]`.

Simplify using `[mul_assoc]`. Rewrite using `[e1, hreal]`. Establish `e2 : (((Formalism.QuantumDeterminants.herm J z z).re : ℝ) : ℂ) = -((t : ℂ) * t)`. Establish `: (Formalism.QuantumDeterminants.herm J z z).re = -(t * t)` using `by rw [hsq, hT]; ring`. Rewrite using `[this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Use the proof step `field_simp)`. Use `⟨Q, Qi, A, Ai, t, q1, q2, a1, a2, a3, qg, qe, qw, htp, ?_⟩` and prove the remaining obligations.

Rewrite using `[mulVec_smul, qy, smul_smul, mul_inv_cancel₀ htc, one_smul]`.
-/
theorem frame_normal {m r : ℕ} {J : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ}
    {F : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {e : Matrix (Fin (2 * r + m + 1)) (Fin r) ℂ}
    {z : Fin (2 * r + m + 1) → ℂ} (hf : IsFrame J J₀ F e z) (hz : (Formalism.QuantumDeterminants.herm J z z).re < 0)
    (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) :
    ∃ (Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ) (A Ai : Matrix (Fin m) (Fin m) ℂ) (t : ℝ),
      Q * Qi = 1 ∧ Qi * Q = 1 ∧ A * Ai = 1 ∧ Ai * A = 1 ∧ Aᴴ * J₀ * A = 1 ∧ Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r ∧
      Q * colE m r = e ∧ Q * colW m r = F * A ∧ 0 < t ∧
      Q *ᵥ ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = z := by
  have h0 : J₀ᴴ = J₀ := by
    rw [← hf.gram]; simp only [conjTranspose_mul, conjTranspose_conjTranspose, hf.herm, Matrix.mul_assoc]
  obtain ⟨A, Ai, a1, a2, a3⟩ := UpperTheory.Lit.Bur.hermitian_form_pos_congruent_identity h0 hp
  obtain ⟨f, f1, f2, f3, f4⟩ := UpperTheory.Lit.Bur.isFrame_exists_isotropic_dual_columns hf
  have hreal : Formalism.QuantumDeterminants.herm J z z = (((Formalism.QuantumDeterminants.herm J z z).re : ℝ) : ℂ) := by
    have hc : star (Formalism.QuantumDeterminants.herm J z z) = Formalism.QuantumDeterminants.herm J z z := by
      unfold Formalism.QuantumDeterminants.herm
      conv_rhs => rw [star_dotProduct, star_mulVec, hf.herm, ← dotProduct_mulVec]
    exact (Complex.conj_eq_iff_re.1 hc).symm
  set T : ℝ := -(Formalism.QuantumDeterminants.herm J z z).re with hT
  have hTp : 0 < T := by simpa [hT] using hz
  set t : ℝ := Real.sqrt T with ht
  have htp : 0 < t := Real.sqrt_pos.2 hTp
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast htp.ne'
  have hsq : t * t = T := Real.mul_self_sqrt hTp.le
  obtain ⟨Q, Qi, q1, q2, qg, qe, qw, qy⟩ := UpperTheory.Lit.Bur.hyperbolic_frame_congruent_splitHermGram (Fa := F * A) (e := e) (f := f) (y := (t⁻¹ : ℂ) • z) hf.herm
    (by rw [conjTranspose_mul]; calc _ = Aᴴ * (Fᴴ * J * F) * A := by simp only [Matrix.mul_assoc]
                                     _ = 1 := by rw [hf.gram, a3])
    hf.e_iso f2 f1
    (by rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, hf.e_perp]; simp)
    (by rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, f3]; simp)
    (by rw [mulVec_smul, conjTranspose_mul, Matrix.mul_assoc, ← mulVec_mulVec, hf.z_perpF]; simp)
    (by rw [mulVec_smul, hf.z_perpE]; simp)
    (by rw [mulVec_smul, f4]; simp)
    (by
      have e1 : Formalism.QuantumDeterminants.herm J ((t⁻¹ : ℂ) • z) ((t⁻¹ : ℂ) • z) = (t⁻¹ : ℂ) * (t⁻¹ : ℂ) * Formalism.QuantumDeterminants.herm J z z := by
        unfold Formalism.QuantumDeterminants.herm
        rw [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
        simp [mul_assoc]
      rw [e1, hreal]
      have e2 : (((Formalism.QuantumDeterminants.herm J z z).re : ℝ) : ℂ) = -((t : ℂ) * t) := by
        have : (Formalism.QuantumDeterminants.herm J z z).re = -(t * t) := by rw [hsq, hT]; ring
        rw [this]; push_cast; ring
      rw [e2]
      field_simp)
  refine ⟨Q, Qi, A, Ai, t, q1, q2, a1, a2, a3, qg, qe, qw, htp, ?_⟩
  rw [mulVec_smul, qy, smul_smul, mul_inv_cancel₀ htc, one_smul]

/- English proof (translation)
Establish `hb : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk m r) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = -1`. Unfold `Formalism.QuantumDeterminants.herm Formalism.QuantumDeterminants.bvec`. Simplify using `[dotProduct, Pi.single_apply, mulVec, Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.wI]`. Rewrite using `[Finset.sum_eq_single (⟨r + m, by omega⟩ : Fin (2 * r + m + 1))]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Unfold `Formalism.QuantumDeterminants.Tz`. Establish `e1 : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk m r) ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = …`.

Unfold `Formalism.QuantumDeterminants.herm`. Rewrite using `[mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]`. Simplify using `[mul_assoc]`. Rewrite using `[e1, hb]`. Simplify using `[pow_two, ← Complex.ofReal_mul]`.
-/
theorem tz_last (m r : ℕ) (t : ℝ) :
    Formalism.QuantumDeterminants.Tz m r ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = t ^ 2 := by
  have hb : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk m r) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = -1 := by
    unfold Formalism.QuantumDeterminants.herm Formalism.QuantumDeterminants.bvec
    simp [dotProduct, Pi.single_apply, mulVec, Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.wI]
    rw [Finset.sum_eq_single (⟨r + m, by omega⟩ : Fin (2 * r + m + 1))]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  unfold Formalism.QuantumDeterminants.Tz
  have e1 : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk m r) ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = (t : ℂ) * t * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk m r) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) := by
    unfold Formalism.QuantumDeterminants.herm
    rw [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
    simp [mul_assoc]
  rw [e1, hb]
  simp [pow_two, ← Complex.ofReal_mul]

/- English proof (translation)
Introduce `i hi`. Establish `: i ≠ Formalism.QuantumDeterminants.wI m r (Fin.last m)`. Introduce `h`. Substitute `h` using the available equality. Simplify using `[Formalism.QuantumDeterminants.wI] at hi`.

Simplify using `[Formalism.QuantumDeterminants.bvec, this]`.
-/
theorem inWb_last (m r : ℕ) (t : ℝ) :
    Formalism.QuantumDeterminants.inWb m r ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) := by
  intro i hi
  have : i ≠ Formalism.QuantumDeterminants.wI m r (Fin.last m) := by
    intro h; subst h; simp [Formalism.QuantumDeterminants.wI] at hi
  simp [Formalism.QuantumDeterminants.bvec, this]

/- English proof (translation)
Use `⟨?_, fun a => ⟨one_mulVec _, one_mulVec _⟩, ?_⟩` and prove the remaining obligations. Use `show (1 : Matrix _ _ ℂ)ᴴ * _ * 1 = _`. Simplify using the standard rewrite rules. Use `tz_last m r t` as an intermediate fact. Rewrite using `[one_mulVec]`.

Use `show ((Real.sqrt (Formalism.QuantumDeterminants.Tz m r _) : ℝ) : ℂ) • _ = _`. Rewrite using `[this, Real.sqrt_sq ht.le]`. Both sides reduce to the same expression.
-/
theorem isFrameW_one (m r : ℕ) {t : ℝ} (ht : 0 < t) :
    PI.UpqRep.IsFrameW m r ((t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m))) 1 := by
  refine ⟨?_, fun a => ⟨one_mulVec _, one_mulVec _⟩, ?_⟩
  · show (1 : Matrix _ _ ℂ)ᴴ * _ * 1 = _
    simp
  · have := tz_last m r t
    rw [one_mulVec]
    show ((Real.sqrt (Formalism.QuantumDeterminants.Tz m r _) : ℝ) : ℂ) • _ = _
    rw [this, Real.sqrt_sq ht.le]
    rfl

/- English proof (translation)
Take `⟨a, ha⟩` from `hf'.exists_coords hu`. Rewrite using `[isCharWith hz' c u hu a ha, hχ _ (UpperTheory.Lit.Bur.isometry_conj_maps_unipotentRadical q1 q2 qg qe hu) a fun j => ?_]`. Establish `hfl : flagVec e z j.succ = Q *ᵥ flagVec (colE m r) z' j.succ`. Use `Fin.lastCases ?_ (fun i => ?_) j.succ` and prove the remaining obligations. Simplify using `[flagVec, qz]`.

Simplify using `only [flagVec, Fin.snoc_castSucc]`. Rewrite using `[← qe]`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mul_apply, mulVec, dotProduct]`. Establish `hq : Q * u * Qi - 1 = Q * (u - 1) * Qi`.

Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, q1]`. Rewrite using `[hfl, hq, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, q2, Matrix.mul_one, ← mulVec_mulVec, ha j, ← qe, mulVec_mulVec]`.
-/
theorem chi_eq {m r : ℕ} {J Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ}
    {e : Matrix (Fin (2 * r + m + 1)) (Fin r) ℂ} {z z' : Fin (2 * r + m + 1) → ℂ} {c : Fin r → ℂ}
    {χ : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ → ℂ} (q1 : Q * Qi = 1) (q2 : Qi * Q = 1)
    (qg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r) (qe : Q * colE m r = e) (qz : Q *ᵥ z' = z) (hz' : Formalism.QuantumDeterminants.inWb m r z')
    (hf' : IsFrame (Formalism.QuantumDeterminants.Hpk m r) 1 ((1 : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ) * colW m r) (colE m r) z') (hχ : IsCharWith J e z c χ)
    {u : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (hu : u ∈ unipRad (Formalism.QuantumDeterminants.Hpk m r) (colE m r)) :
    χ (Q * u * Qi) = PI.BesselMapUniq.psiGen m r z' c u := by
  obtain ⟨a, ha⟩ := hf'.exists_coords hu
  rw [isCharWith hz' c u hu a ha, hχ _ (UpperTheory.Lit.Bur.isometry_conj_maps_unipotentRadical q1 q2 qg qe hu) a fun j => ?_]
  have hfl : flagVec e z j.succ = Q *ᵥ flagVec (colE m r) z' j.succ := by
    refine Fin.lastCases ?_ (fun i => ?_) j.succ
    · simp [flagVec, qz]
    · simp only [flagVec, Fin.snoc_castSucc]
      rw [← qe]
      funext k
      simp [Matrix.mul_apply, mulVec, dotProduct]
  have hq : Q * u * Qi - 1 = Q * (u - 1) * Qi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, q1]
  rw [hfl, hq, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, q2, Matrix.mul_one, ← mulVec_mulVec, ha j, ← qe,
    mulVec_mulVec]

/- English proof (translation)
Introduce `hB n m r J J₀ F e z hf hm hz hp χ hχ H _ _ _ σ hU hI h hh hgap W _ _ _ π₀ hπ`. Take `rfl : n = 2 * r + m + 1` from `by have := hf.codim; omega`. Distinguish the cases in `hW : Nontrivial W`. Use `swap`. Establish `: Subsingleton W` using `not_nontrivial_iff_subsingleton.1 hW`.

Use `rank_le_one_of_dep _ fun x _ y _ => ⟨1, 0, Or.inl one_ne_zero, ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Simplify using `[Subsingleton.elim w 0]`. Take `⟨ε, lam, fr, hfrU, hfrJ, hHC, hG, hDS⟩` from `hgap`. Take `⟨c, hc, hχc⟩` from `hχ`.

Take `⟨Q, Qi, A, Ai, t, q1, q2, a1, a2, a3, qg, qe, qw, ht, qz⟩` from `frame_normal hf hz hp`. Use `set z' : Fin (2 * r + m + 1) → ℂ := (t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m)) with hz'`. Establish `hzW : Formalism.QuantumDeterminants.inWb m r z'` using `inWb_last m r t`. Establish `hTz : 0 < Formalism.QuantumDeterminants.Tz m r z'` using `by rw [hz', tz_last]; positivity`. Establish `hfw : PI.UpqRep.IsFrameW m r z' 1` using `isFrameW_one m r ht`.

Establish `hf'` using `isFrame hfw hzW hTz`. Use `set σ' : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ → (H →L[ℂ] H) := fun g => σ (Q * g * Qi) with hσ'`. Establish `hDSH : PI.UpqRep.IsDSHpk m r ε lam σ'` using `isDSHpk_tr q1 q2 qg hfrU hfrJ hDS`. Take `⟨-, hU', -⟩` from `rep_of_isDSHpk hDSH`. Establish `hsm : ∀ v, v ∈ PI.UpqRep.smoothVecs (k` using `m) (r := r) σ' ↔ v ∈ smSub J σ := fun v => (smoothOnH_iff_mem PI.HwUniqW.Hpk_conjTranspose PI.HwUniqW.Hpk_mul_self hU' v).trans (UpperTheory.Lit.Bur.smoothVec_conjugate_unitaryGroup_iff σ q1 q2 qg v)`.

Establish `hπ'` using `UpperTheory.Lit.Bur.contragredient_conj_definiteUnitary_isContIrred a1 a2 a3 hπ`. Take `⟨Wp, _, _, _, ρ, T1, hρ, hT1, hirr⟩` from `UpperTheory.Lit.Bur.contIrred_compactUnitaryGroup_rep_isUnitarizable hπ'`. Establish `hD : Nontrivial (Module.Dual ℂ W)` using `(Module.nontrivial_dual_iff ℂ).2 hW`. Establish `: Nontrivial Wp` using `T1.symm.toEquiv.nontrivial`. Take `⟨u, Wq, _, _, ρ', T2, hty, hT2⟩` from `UpperTheory.Lit.Bur.irreducible_unitary_rep_iso_harishChandraType hρ hirr`.

Use `set T : Module.Dual ℂ W ≃ₗ[ℂ] Wq := T1.trans T2 with hTdef`. Establish `hone : ∀ s ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ), s ∈ PI.UpqRep.UJset (PI.UpqRep.allPos m)` using `fun s hs => PI.HwUniqW.mem_UJset_allPos.2 (mem_UH_one.1 hs)`. Establish `hT : ∀ s ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ), ∀ l : Module.Dual ℂ W, T ((π₀ (A * sᴴ * Ai)).dualMap l) = ρ' s (T l)` using `fun s hs l => by`. Simplify using `only [hTdef, LinearEquiv.trans_apply]`. Rewrite using `[hT1 s hs l, hT2 s (hone s hs)]`.

Use `set π : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ → (Wq →L[ℂ] Wq) := fun g => ρ' (PI.HwUniqW.sub m r g) with hπdef`. Establish `hty' : PI.UpqRep.IsHCTypeW m r z' u π`. Use `⟨1, hfw, ?_⟩` and prove the remaining obligations. Establish `e1 : (fun h => π (1 * PI.UpqRep.blockW m r h * (1 : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ)⁻¹)) = ρ'`. Use function extensionality and compare the values at `h`.

Simplify using `[hπdef, PI.HwUniqW.sub_blockW]`. Rewrite using `[e1]`. Conclude with `hty`. Establish `key : ∀ β ∈ besselForms J J₀ F e χ σ π₀ (smSub J σ), ∃ B : H → Wq, PI.BesselMapUniq.IsBesselMapSm (k` using `m) (r := r) z' (PI.BesselMapUniq.psiGen m r z' c) σ' π B ∧ ∀ x : smSub J σ, B x = T (β.flip x) := by`. Introduce `β hβ`.

Establish `hBm : ∃ B : H → Wq, ∀ x : smSub J σ, B x = T (β.flip x)` using `by classical`. Conclude with `⟨fun v => if hv : v ∈ smSub J σ then T (β.flip ⟨v, hv⟩) else 0, fun x => dif_pos x.2⟩`. Take `⟨B, hBx⟩` from `hBm`. Use `⟨B, ⟨fun v hv w hw => ?_, fun a v hv => ?_, fun h' hh' u' hu' v hv => ?_, ?_⟩, hBx⟩` and prove the remaining obligations. Establish `hv'` using `(hsm v).1 hv`.

Establish `hw'` using `(hsm w).1 hw`. Establish `e0` using `hBx (⟨v, hv'⟩ + ⟨w, hw'⟩)`. Rewrite `e0` using `[map_add, map_add, ← hBx, ← hBx]`. Conclude with `e0`. Establish `hv'` using `(hsm v).1 hv`.

Establish `e0` using `hBx (a • ⟨v, hv'⟩)`. Rewrite `e0` using `[map_smul, map_smul, ← hBx]`. Conclude with `e0`. Establish `hv'` using `(hsm v).1 hv`. Establish `hfix : PI.HwUniqW.FixEW m r h'`.

Use `⟨hh'.2.1, ?_⟩` and prove the remaining obligations. Establish `e0` using `hh'.2.2`. Rewrite `e0` using `[hz', mulVec_smul]`. Conclude with `smul_right_injective _ (by exact_mod_cast ht.ne' : (t : ℂ) ≠ 0) e0`. Take `⟨hs, hbl⟩` from `PI.HwUniqW.fix_block hh'.1 hfix`.

Use `set s := PI.HwUniqW.sub m r h' with hsdef`. Establish `hs1 : sᴴ * s = 1` using `PI.HwUniqW.mem_UJset_allPos.1 hs`. Establish `hs2 : s * sᴴ = 1` using `mul_eq_one_comm.1 hs1`. Establish `hsU : s ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ)` using `mem_UH_one.2 hs1`. Establish `hJ₀ : Aiᴴ * Ai = J₀`.

Establish `e0 : Aiᴴ * (Aᴴ * J₀ * A) * Ai = (A * Ai)ᴴ * J₀ * (A * Ai)`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Rewrite `e0` using `[a3, a1]`. Simplify using `using e0`. Establish `hmem : ∀ y : Matrix (Fin m) (Fin m) ℂ, yᴴ * y = 1 → A * y * Ai ∈ Formalism.QuantumDeterminants.UH J₀` using `fun y hy => by show (A * y * Ai)ᴴ * J₀ * (A * y * Ai) = J₀`.

Establish `e0 : (A * y * Ai)ᴴ * J₀ * (A * y * Ai) = Aiᴴ * (yᴴ * (Aᴴ * J₀ * A) * y) * Ai`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[e0, a3, Matrix.mul_one, hy, Matrix.mul_one, hJ₀]`. Establish `hh0` using `hmem s hs1`. Establish `hh1` using `hmem sᴴ (by rw [conjTranspose_conjTranspose]; exact hs2)`.

Establish `h01 : (A * s * Ai) * (A * sᴴ * Ai) = 1`. Establish `e0 : (A * s * Ai) * (A * sᴴ * Ai) = A * s * (Ai * A) * sᴴ * Ai` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[e0, a2, Matrix.mul_one, Matrix.mul_assoc A, hs2, Matrix.mul_one, a1]`. Establish `hinv : ∀ w, π₀ (A * s * Ai) (π₀ (A * sᴴ * Ai) w) = w` using `fun w => by`. Establish `e0` using `hπ.1.2 _ hh0 _ hh1`.

Rewrite `e0` using `[h01, hπ.1.1]`. Conclude with `(LinearMap.congr_fun e0 w).symm`. Establish `hgu` using `UpperTheory.Lit.Bur.isometry_conj_maps_unipotentRadical q1 q2 qg qe (UpperTheory.Lit.Bur.mem_besselUnipotentRadical_of_mem_coordGroup hu')`. Establish `hQi : Qiᴴ * Formalism.QuantumDeterminants.Hpk m r * Qi = J`. Rewrite using `[← qg]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hgh : Q * h' * Qi ∈ Formalism.QuantumDeterminants.UH J` using `by show (Q * h' * Qi)ᴴ * J * (Q * h' * Qi) = J`. Establish `hh2 : h'ᴴ * Formalism.QuantumDeterminants.Hpk m r * h' = Formalism.QuantumDeterminants.Hpk m r` using `hh'.1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = J := by rw [qg, hh2, hQi]`. Establish `hE : IsEmb J F (Q * h' * Qi) (A * s * Ai)`. Use `UpperTheory.Lit.Bur.blockEmbed_conj_isUnitaryEmbedding (s := s) q1 q2 qg qw a1` as an intermediate fact. Rewrite `this` using `[← hbl]`. Then use the resulting hypothesis. Establish `e1 : σ' (h' * u') v = σ (Q * h' * Qi) (σ (Q * u' * Qi) v)`.

Establish `e0 : Q * (h' * u') * Qi = (Q * h' * Qi) * (Q * u' * Qi)`. Establish `: (Q * h' * Qi) * (Q * u' * Qi) = Q * h' * (Qi * Q) * u' * Qi` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[this, q2, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`. Use `show σ (Q * (h' * u') * Qi) v = _`.

Rewrite using `[e0, hU.1.2 _ hgh _ hgu.1]`. Both sides reduce to the same expression. Set `x : smSub J σ` to `⟨v, hv'⟩`. Set `y1 : smSub J σ` to `⟨σ (Q * u' * Qi) v, UpperTheory.Lit.Bur.smoothVec_stable_under_unitaryGroup hf.unit hU hgu.1 hv'⟩`. Set `y2 : smSub J σ` to `⟨σ (Q * h' * Qi) y1, UpperTheory.Lit.Bur.smoothVec_stable_under_unitaryGroup hf.unit hU hgh y1.2⟩`.

Establish `hflip : β.flip y2 = χ (Q * u' * Qi) • (π₀ (A * sᴴ * Ai)).dualMap (β.flip x)`. Use extensionality with `w`. Establish `i1` using `hβ.inv _ hh0 _ hgh hE (π₀ (A * sᴴ * Ai) w) y1 y2 rfl`. Establish `i2` using `hβ.equiv _ hgu (π₀ (A * sᴴ * Ai) w) x y1 rfl`. Rewrite `i1` using `[hinv]`.

Simplify using `only [LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.dualMap_apply, smul_eq_mul]`. Rewrite using `[i1, i2]`. Establish `hχe` using `chi_eq q1 q2 qg qe qz hzW hf' hχc (UpperTheory.Lit.Bur.mem_besselUnipotentRadical_of_mem_coordGroup hu')`. Rewrite using `[e1]`. Use `show B (y2 : H) = _`.

Rewrite using `[hBx y2, hflip, map_smul, hT s hsU, hχe, ← hBx x]`. Set `b` to `Module.finBasis ℂ W choose l hl1 hl2 using fun i => hβ.cont (b i)`. Use `UpperTheory.Lit.Bur.casselmanWallachCont_finite_sum_sobolev_forms (fun v hv => (UpperTheory.Lit.Bur.smoothVec_conjugate_unitaryGroup_iff σ q1 q2 qg v).2 ((hsm v).1 hv)) l (fun i => T (b.coord i)) (fun i => UpperTheory.Lit.Bur.sobolevCont_of_conj_gram_form σ q1 q2 qg (hl1 i)) (fun …` and prove the remaining obligations. Establish `hv'` using `(hsm v).1 hv`. Establish `e0` using `hBx ⟨v, hv'⟩`.

Rewrite `e0` using `[← b.sum_dual_apply_smul_coord (β.flip ⟨v, hv'⟩), map_sum]`. Use `e0.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.flip_apply, ← hl2 i ⟨v, hv'⟩]`. Use `rank_le_one_of_dep _ fun β₁ h₁ β₂ h₂ => ?_` and prove the remaining obligations. Take `⟨B₁, m₁, e₁⟩` from `key β₁ h₁`.

Take `⟨B₂, m₂, e₂⟩` from `key β₂ h₂`. Take `⟨a, b, hab, hz0⟩` from `hB m r ε lam h H σ' z' c u Wq π hm hG hh hHC hDSH hzW hTz hc hty' B₁ B₂ m₁ m₂`. Use `⟨a, b, hab, ?_⟩` and prove the remaining obligations. Use extensionality with `w x`. Establish `h0` using `hz0 x ((hsm x).2 x.2)`.

Rewrite `h0` using `[e₁ x, e₂ x]`. Establish `h1 : T (a • β₁.flip x + b • β₂.flip x) = 0` using `by rw [map_add, map_smul, map_smul]; exact h0`. Use `LinearMap.congr_fun (T.map_eq_zero_iff.1 h1) w` as an intermediate fact. Simplify using `using this`.
-/
theorem burGapPos_of_bmu : CompanionTheory.Bmu.BesselMapUniqGap → UpperTheory.Lit.Bur.BurGapPos := by
  intro hB n m r J J₀ F e z hf hm hz hp χ hχ H _ _ _ σ hU hI h hh hgap W _ _ _ π₀ hπ
  obtain rfl : n = 2 * r + m + 1 := by have := hf.codim; omega
  by_cases hW : Nontrivial W
  swap
  · have : Subsingleton W := not_nontrivial_iff_subsingleton.1 hW
    refine rank_le_one_of_dep _ fun x _ y _ => ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    ext w
    simp [Subsingleton.elim w 0]
  obtain ⟨ε, lam, fr, hfrU, hfrJ, hHC, hG, hDS⟩ := hgap
  obtain ⟨c, hc, hχc⟩ := hχ
  obtain ⟨Q, Qi, A, Ai, t, q1, q2, a1, a2, a3, qg, qe, qw, ht, qz⟩ := frame_normal hf hz hp
  set z' : Fin (2 * r + m + 1) → ℂ := (t : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m)) with hz'
  have hzW : Formalism.QuantumDeterminants.inWb m r z' := inWb_last m r t
  have hTz : 0 < Formalism.QuantumDeterminants.Tz m r z' := by rw [hz', tz_last]; positivity
  have hfw : PI.UpqRep.IsFrameW m r z' 1 := isFrameW_one m r ht
  have hf' := isFrame hfw hzW hTz
  set σ' : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ → (H →L[ℂ] H) := fun g => σ (Q * g * Qi) with hσ'
  have hDSH : PI.UpqRep.IsDSHpk m r ε lam σ' := isDSHpk_tr q1 q2 qg hfrU hfrJ hDS
  obtain ⟨-, hU', -⟩ := rep_of_isDSHpk hDSH
  have hsm : ∀ v, v ∈ PI.UpqRep.smoothVecs (k := m) (r := r) σ' ↔ v ∈ smSub J σ := fun v =>
    (smoothOnH_iff_mem PI.HwUniqW.Hpk_conjTranspose PI.HwUniqW.Hpk_mul_self hU' v).trans (UpperTheory.Lit.Bur.smoothVec_conjugate_unitaryGroup_iff σ q1 q2 qg v)
  have hπ' := UpperTheory.Lit.Bur.contragredient_conj_definiteUnitary_isContIrred a1 a2 a3 hπ
  obtain ⟨Wp, _, _, _, ρ, T1, hρ, hT1, hirr⟩ := UpperTheory.Lit.Bur.contIrred_compactUnitaryGroup_rep_isUnitarizable hπ'
  have hD : Nontrivial (Module.Dual ℂ W) := (Module.nontrivial_dual_iff ℂ).2 hW
  have : Nontrivial Wp := T1.symm.toEquiv.nontrivial
  obtain ⟨u, Wq, _, _, ρ', T2, hty, hT2⟩ := UpperTheory.Lit.Bur.irreducible_unitary_rep_iso_harishChandraType hρ hirr
  set T : Module.Dual ℂ W ≃ₗ[ℂ] Wq := T1.trans T2 with hTdef
  have hone : ∀ s ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ), s ∈ PI.UpqRep.UJset (PI.UpqRep.allPos m) := fun s hs =>
    PI.HwUniqW.mem_UJset_allPos.2 (mem_UH_one.1 hs)
  have hT : ∀ s ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ), ∀ l : Module.Dual ℂ W,
      T ((π₀ (A * sᴴ * Ai)).dualMap l) = ρ' s (T l) := fun s hs l => by
    simp only [hTdef, LinearEquiv.trans_apply]
    rw [hT1 s hs l, hT2 s (hone s hs)]
  set π : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ → (Wq →L[ℂ] Wq) := fun g => ρ' (PI.HwUniqW.sub m r g) with hπdef
  have hty' : PI.UpqRep.IsHCTypeW m r z' u π := by
    refine ⟨1, hfw, ?_⟩
    have e1 : (fun h => π (1 * PI.UpqRep.blockW m r h * (1 : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ)⁻¹)) = ρ' := by
      funext h
      simp [hπdef, PI.HwUniqW.sub_blockW]
    rw [e1]
    exact hty
  have key : ∀ β ∈ besselForms J J₀ F e χ σ π₀ (smSub J σ), ∃ B : H → Wq,
      PI.BesselMapUniq.IsBesselMapSm (k := m) (r := r) z' (PI.BesselMapUniq.psiGen m r z' c) σ' π B ∧
      ∀ x : smSub J σ, B x = T (β.flip x) := by
    intro β hβ
    have hBm : ∃ B : H → Wq, ∀ x : smSub J σ, B x = T (β.flip x) := by
      classical
      exact ⟨fun v => if hv : v ∈ smSub J σ then T (β.flip ⟨v, hv⟩) else 0, fun x => dif_pos x.2⟩
    obtain ⟨B, hBx⟩ := hBm
    refine ⟨B, ⟨fun v hv w hw => ?_, fun a v hv => ?_, fun h' hh' u' hu' v hv => ?_, ?_⟩, hBx⟩
    · have hv' := (hsm v).1 hv
      have hw' := (hsm w).1 hw
      have e0 := hBx (⟨v, hv'⟩ + ⟨w, hw'⟩)
      rw [map_add, map_add, ← hBx, ← hBx] at e0
      exact e0
    · have hv' := (hsm v).1 hv
      have e0 := hBx (a • ⟨v, hv'⟩)
      rw [map_smul, map_smul, ← hBx] at e0
      exact e0
    · have hv' := (hsm v).1 hv
      have hfix : PI.HwUniqW.FixEW m r h' := by
        refine ⟨hh'.2.1, ?_⟩
        have e0 := hh'.2.2
        rw [hz', mulVec_smul] at e0
        exact smul_right_injective _ (by exact_mod_cast ht.ne' : (t : ℂ) ≠ 0) e0
      obtain ⟨hs, hbl⟩ := PI.HwUniqW.fix_block hh'.1 hfix
      set s := PI.HwUniqW.sub m r h' with hsdef
      have hs1 : sᴴ * s = 1 := PI.HwUniqW.mem_UJset_allPos.1 hs
      have hs2 : s * sᴴ = 1 := mul_eq_one_comm.1 hs1
      have hsU : s ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ) := mem_UH_one.2 hs1
      have hJ₀ : Aiᴴ * Ai = J₀ := by
        have e0 : Aiᴴ * (Aᴴ * J₀ * A) * Ai = (A * Ai)ᴴ * J₀ * (A * Ai) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
        rw [a3, a1] at e0
        simpa using e0
      have hmem : ∀ y : Matrix (Fin m) (Fin m) ℂ, yᴴ * y = 1 → A * y * Ai ∈ Formalism.QuantumDeterminants.UH J₀ := fun y hy => by
        show (A * y * Ai)ᴴ * J₀ * (A * y * Ai) = J₀
        have e0 : (A * y * Ai)ᴴ * J₀ * (A * y * Ai) = Aiᴴ * (yᴴ * (Aᴴ * J₀ * A) * y) * Ai := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
        rw [e0, a3, Matrix.mul_one, hy, Matrix.mul_one, hJ₀]
      have hh0 := hmem s hs1
      have hh1 := hmem sᴴ (by rw [conjTranspose_conjTranspose]; exact hs2)
      have h01 : (A * s * Ai) * (A * sᴴ * Ai) = 1 := by
        have e0 : (A * s * Ai) * (A * sᴴ * Ai) = A * s * (Ai * A) * sᴴ * Ai := by simp only [Matrix.mul_assoc]
        rw [e0, a2, Matrix.mul_one, Matrix.mul_assoc A, hs2, Matrix.mul_one, a1]
      have hinv : ∀ w, π₀ (A * s * Ai) (π₀ (A * sᴴ * Ai) w) = w := fun w => by
        have e0 := hπ.1.2 _ hh0 _ hh1
        rw [h01, hπ.1.1] at e0
        exact (LinearMap.congr_fun e0 w).symm
      have hgu := UpperTheory.Lit.Bur.isometry_conj_maps_unipotentRadical q1 q2 qg qe (UpperTheory.Lit.Bur.mem_besselUnipotentRadical_of_mem_coordGroup hu')
      have hQi : Qiᴴ * Formalism.QuantumDeterminants.Hpk m r * Qi = J := by
        rw [← qg]
        calc Qiᴴ * (Qᴴ * J * Q) * Qi = (Q * Qi)ᴴ * J * (Q * Qi) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
          _ = J := by rw [q1]; simp
      have hgh : Q * h' * Qi ∈ Formalism.QuantumDeterminants.UH J := by
        show (Q * h' * Qi)ᴴ * J * (Q * h' * Qi) = J
        have hh2 : h'ᴴ * Formalism.QuantumDeterminants.Hpk m r * h' = Formalism.QuantumDeterminants.Hpk m r := hh'.1
        calc (Q * h' * Qi)ᴴ * J * (Q * h' * Qi) = Qiᴴ * (h'ᴴ * (Qᴴ * J * Q) * h') * Qi := by
              simp only [conjTranspose_mul, Matrix.mul_assoc]
          _ = J := by rw [qg, hh2, hQi]
      have hE : IsEmb J F (Q * h' * Qi) (A * s * Ai) := by
        have := UpperTheory.Lit.Bur.blockEmbed_conj_isUnitaryEmbedding (s := s) q1 q2 qg qw a1
        rwa [← hbl] at this
      have e1 : σ' (h' * u') v = σ (Q * h' * Qi) (σ (Q * u' * Qi) v) := by
        have e0 : Q * (h' * u') * Qi = (Q * h' * Qi) * (Q * u' * Qi) := by
          have : (Q * h' * Qi) * (Q * u' * Qi) = Q * h' * (Qi * Q) * u' * Qi := by simp only [Matrix.mul_assoc]
          rw [this, q2, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
        show σ (Q * (h' * u') * Qi) v = _
        rw [e0, hU.1.2 _ hgh _ hgu.1]
        rfl
      let x : smSub J σ := ⟨v, hv'⟩
      let y1 : smSub J σ := ⟨σ (Q * u' * Qi) v, UpperTheory.Lit.Bur.smoothVec_stable_under_unitaryGroup hf.unit hU hgu.1 hv'⟩
      let y2 : smSub J σ := ⟨σ (Q * h' * Qi) y1, UpperTheory.Lit.Bur.smoothVec_stable_under_unitaryGroup hf.unit hU hgh y1.2⟩
      have hflip : β.flip y2 = χ (Q * u' * Qi) • (π₀ (A * sᴴ * Ai)).dualMap (β.flip x) := by
        ext w
        have i1 := hβ.inv _ hh0 _ hgh hE (π₀ (A * sᴴ * Ai) w) y1 y2 rfl
        have i2 := hβ.equiv _ hgu (π₀ (A * sᴴ * Ai) w) x y1 rfl
        rw [hinv] at i1
        simp only [LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.dualMap_apply, smul_eq_mul]
        rw [i1, i2]
      have hχe := chi_eq q1 q2 qg qe qz hzW hf' hχc (UpperTheory.Lit.Bur.mem_besselUnipotentRadical_of_mem_coordGroup hu')
      rw [e1]
      show B (y2 : H) = _
      rw [hBx y2, hflip, map_smul, hT s hsU, hχe, ← hBx x]
    · let b := Module.finBasis ℂ W
      choose l hl1 hl2 using fun i => hβ.cont (b i)
      refine UpperTheory.Lit.Bur.casselmanWallachCont_finite_sum_sobolev_forms (fun v hv => (UpperTheory.Lit.Bur.smoothVec_conjugate_unitaryGroup_iff σ q1 q2 qg v).2 ((hsm v).1 hv)) l (fun i => T (b.coord i))
        (fun i => UpperTheory.Lit.Bur.sobolevCont_of_conj_gram_form σ q1 q2 qg (hl1 i)) (fun v hv => ?_)
      have hv' := (hsm v).1 hv
      have e0 := hBx ⟨v, hv'⟩
      rw [← b.sum_dual_apply_smul_coord (β.flip ⟨v, hv'⟩), map_sum] at e0
      refine e0.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [map_smul, LinearMap.flip_apply, ← hl2 i ⟨v, hv'⟩]
  refine rank_le_one_of_dep _ fun β₁ h₁ β₂ h₂ => ?_
  obtain ⟨B₁, m₁, e₁⟩ := key β₁ h₁
  obtain ⟨B₂, m₂, e₂⟩ := key β₂ h₂
  obtain ⟨a, b, hab, hz0⟩ := hB m r ε lam h H σ' z' c u Wq π hm hG hh hHC hDSH hzW hTz hc hty' B₁ B₂ m₁ m₂
  refine ⟨a, b, hab, ?_⟩
  ext w x
  have h0 := hz0 x ((hsm x).2 x.2)
  rw [e₁ x, e₂ x] at h0
  have h1 : T (a • β₁.flip x + b • β₂.flip x) = 0 := by rw [map_add, map_smul, map_smul]; exact h0
  have := LinearMap.congr_fun (T.map_eq_zero_iff.1 h1) w
  simpa using this

end UpperTheory.Lit.Bur.BurPos

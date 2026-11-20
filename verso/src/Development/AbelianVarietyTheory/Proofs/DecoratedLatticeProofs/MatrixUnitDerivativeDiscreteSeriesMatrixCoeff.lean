import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section

namespace GlobalTheory.CoeffEab

variable {p q n : ℕ}

open scoped Matrix.Norms.Operator in
/- English proof (translation)
Conclude with `NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (continuous_id.matrix_reindex e e) A`.
-/
theorem reindex_exp (e : Ix p q ≃ Fin n) (A : Mat p q) :
    Matrix.reindex e e (NormedSpace.exp A) = NormedSpace.exp (Matrix.reindex e e A) := by
  exact NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (continuous_id.matrix_reindex e e) A

/- English proof (translation)
Unfold `Formalism.REAL.inG`. Rewrite using `[← h.reindex_Jm, Matrix.conjTranspose_reindex]`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]`. Use `(Matrix.reindex e e).injective.eq_iff (a := Yᴴ * Jm p q + Jm p q * Y) (b := 0)` as an intermediate fact. Conclude with `this.symm`.
-/
theorem mem_upq_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (Y : Mat p q) :
    Y ∈ upq p q ↔ Formalism.REAL.inG ε (Matrix.reindex e e Y) := by
  unfold Formalism.REAL.inG
  rw [← h.reindex_Jm, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  have := (Matrix.reindex e e).injective.eq_iff (a := Yᴴ * Jm p q + Jm p q * Y) (b := 0)
  exact this.symm

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases h : ε a <;> simp [h]`.
-/
theorem Jm_herm (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

/- English proof (translation)
Unfold `Formalism.REAL.inG`. Establish `: Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← mul_assoc, Formalism.REAL.Jm_mul_self, one_mul]`. Use `_ = -(Formalism.REAL.Jm ε * X) := by rw [h, mul_neg]`.

Rewrite using `[this, neg_add_cancel]`.
-/
theorem inG_of_J {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε = -X) : Formalism.REAL.inG ε X := by
  unfold Formalism.REAL.inG
  have : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := by
    calc Xᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) := by
          rw [← mul_assoc, ← mul_assoc, Formalism.REAL.Jm_mul_self, one_mul]
      _ = -(Formalism.REAL.Jm ε * X) := by rw [h, mul_neg]
  rw [this, neg_add_cancel]

/- English proof (translation)
Apply `inG_of_J` to reduce the goal to its premises. Unfold `Formalism.REAL.cpart1`. Rewrite using `[conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Jm_herm, conjTranspose_conjTranspose]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_assoc]`. Rewrite using `[← mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, one_mul, mul_one]`.

Establish `: star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[this, ← smul_neg, neg_sub]`.
-/
theorem inG_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε (Formalism.REAL.cpart1 ε Z) := by
  apply inG_of_J
  unfold Formalism.REAL.cpart1
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Jm_herm,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_assoc]
  rw [← mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, one_mul, mul_one]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_neg, neg_sub]

/- English proof (translation)
Apply `inG_of_J` to reduce the goal to its premises. Unfold `Formalism.REAL.cpart2`. Rewrite using `[conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Jm_herm, conjTranspose_conjTranspose]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, mul_assoc]`. Rewrite using `[← mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, one_mul, mul_one]`.

Establish `: star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I))`. Rewrite using `[show star (1 / (2 * Complex.I)) = (starRingEnd ℂ) (1 / (2 * Complex.I)) from rfl]`. Simplify using `only [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]`. Rewrite using `[mul_neg, div_neg]`. Rewrite using `[this, neg_smul, add_comm]`.
-/
theorem inG_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε (Formalism.REAL.cpart2 ε Z) := by
  apply inG_of_J
  unfold Formalism.REAL.cpart2
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Jm_herm,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, mul_assoc]
  rw [← mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, one_mul, mul_one]
  have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [show star (1 / (2 * Complex.I)) = (starRingEnd ℂ) (1 / (2 * Complex.I)) from rfl]
    simp only [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]
    rw [mul_neg, div_neg]
  rw [this, neg_smul, add_comm]

/- English proof (translation)
Unfold `Formalism.REAL.cpart1 Formalism.REAL.cpart2`. Rewrite using `[smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp]`. Use `module`.
-/
theorem cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart1 ε Z + Complex.I • Formalism.REAL.cpart2 ε Z = Z := by
  unfold Formalism.REAL.cpart1 Formalism.REAL.cpart2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp]
  module

/- English proof (translation)
Take `⟨Y, rfl⟩` from `(Matrix.reindex e e).surjective X`. Rewrite using `[Equiv.symm_apply_apply]`. Establish `hY : Y ∈ upq p q` using `(mem_upq_iff h Y).2 hX`. Take `⟨x, rfl⟩` from `h.cov_surj T hg`. Establish `hs : ∀ t : ℝ, t • Y ∈ upq p q`.

Introduce `t`. Establish `h0 : Yᴴ * Jm p q + Jm p q * Y = 0` using `hY`. Use `show (t • Y)ᴴ * Jm p q + Jm p q * (t • Y) = 0`. Rewrite using `[conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h0, smul_zero]`. Establish `key : ∀ t : ℝ, σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) * NormedSpace.exp ((t : ℂ) • Matrix.reindex e e Y)) = R.U.π x * R.U.π (T.expt (t • Y))`.

Introduce `t`. Rewrite using `[← map_mul, hF (x * _), map_mul, Units.val_mul, T.expt_cov _ (hs t)]`. Use `congr 1`. Establish `: (t : ℂ) • Matrix.reindex e e Y = Matrix.reindex e e (t • Y)`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Rewrite using `[this, ← reindex_exp]`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]`. Unfold `Formalism.REAL.Rd`. Simplify using `only [key, ← hF x]`.

Establish `hd` using `R.der Y hY v`. Establish `hl` using `(((innerSL ℂ w).comp (R.U.π x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd`. Conclude with `hl.deriv`.
-/
theorem Rd_coeff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} {T : GrpData p q} (R : DSRep T)
    {σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)} (h : BlockOrd e ε) (hF : Factors R.U e σ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) (v : R.HK.V) (w : R.U.H)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    Formalism.REAL.Rd X (fun x => inner ℂ w (σ x (R.ι v))) g =
      inner ℂ w (σ g (R.ι (R.HK.act ((Matrix.reindex e e).symm X) v))) := by
  obtain ⟨Y, rfl⟩ := (Matrix.reindex e e).surjective X
  rw [Equiv.symm_apply_apply]
  have hY : Y ∈ upq p q := (mem_upq_iff h Y).2 hX
  obtain ⟨x, rfl⟩ := h.cov_surj T hg
  have hs : ∀ t : ℝ, t • Y ∈ upq p q := by
    intro t
    have h0 : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
    show (t • Y)ᴴ * Jm p q + Jm p q * (t • Y) = 0
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h0, smul_zero]
  have key : ∀ t : ℝ, σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) *
      NormedSpace.exp ((t : ℂ) • Matrix.reindex e e Y)) = R.U.π x * R.U.π (T.expt (t • Y)) := by
    intro t
    rw [← map_mul, hF (x * _), map_mul, Units.val_mul, T.expt_cov _ (hs t)]
    congr 1
    have : (t : ℂ) • Matrix.reindex e e Y = Matrix.reindex e e (t • Y) := by
      ext i j; simp
    rw [this, ← reindex_exp]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  unfold Formalism.REAL.Rd
  simp only [key, ← hF x]
  have hd := R.der Y hY v
  have hl := (((innerSL ℂ w).comp (R.U.π x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  exact hl.deriv

/- English proof (translation)
Introduce `p q n e ε T R σ h hF a b v w g hg`. Unfold `Formalism.REAL.Eab Formalism.REAL.Ec`. Rewrite using `[Rd_coeff R h hF (inG_cpart1 ε _) v w hg, Rd_coeff R h hF (inG_cpart2 ε _) v w hg]`. Establish `hE : Eab a b = (Matrix.reindex e e).symm (Formalism.REAL.cpart1 ε (Matrix.single (e a) (e b) 1)) + Complex.I • (Matrix.reindex e e).symm (Formalism.REAL.cpart2 ε (Matrix.single (e a) (e b) 1))`. Use extensionality with `i j`.

Use `congrFun (congrFun (cpart_sum ε (Matrix.single (e a) (e b) (1 : ℂ))) (e i)) (e j)` as an intermediate fact. Simplify using `only [Matrix.add_apply, Matrix.smul_apply] at this`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.reindex_symm, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]`. Rewrite using `[this]`. Simplify using `[Eab, Matrix.single_apply]`.

Rewrite using `[hE]`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, inner_add_right, inner_smul_right]`.
-/
theorem eab_coeff : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ (a b : Ix p q) (v : R.HK.V) (w : R.U.H), ∀ g ∈ UJset ε, Formalism.REAL.Eab ε (e a) (e b) (fun x => inner ℂ w (σ x (R.ι v))) g = inner ℂ w (σ g (R.ι (R.HK.act (Eab a b) v))) := by
  intro p q n e ε T R σ h hF a b v w g hg
  unfold Formalism.REAL.Eab Formalism.REAL.Ec
  rw [Rd_coeff R h hF (inG_cpart1 ε _) v w hg, Rd_coeff R h hF (inG_cpart2 ε _) v w hg]
  have hE : Eab a b = (Matrix.reindex e e).symm (Formalism.REAL.cpart1 ε (Matrix.single (e a) (e b) 1)) +
      Complex.I • (Matrix.reindex e e).symm (Formalism.REAL.cpart2 ε (Matrix.single (e a) (e b) 1)) := by
    ext i j
    have := congrFun (congrFun (cpart_sum ε (Matrix.single (e a) (e b) (1 : ℂ))) (e i)) (e j)
    simp only [Matrix.add_apply, Matrix.smul_apply] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.reindex_symm, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm]
    rw [this]
    simp [Eab, Matrix.single_apply]
  rw [hE]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, inner_add_right, inner_smul_right]

end GlobalTheory.CoeffEab

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Formalism.PeriodIntegrals.QuotInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SnMass
open scoped ENNReal

namespace GlobalTheory.GramExp

def GDef {N a : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (X : Fin N → Fin a → ℂ) : Prop :=
  ((Matrix.of X)ᴴ * H * Matrix.of X).det ≠ 0 ∧ PosOnPerp H (Matrix.of X)

def GGram {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (a : ℕ) : Set (HCo a) :=
  {t | ∃ X : Fin N → Fin a → ℂ, (Matrix.of X)ᴴ * H * Matrix.of X = hOf t ∧ GDef H X}

def GLaw {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (a : ℕ) (μ : Measure (Fin N → Fin N → ℂ)) (C : ℝ) : Prop :=
  0 < C ∧ ∀ Φ : (Fin N → Fin a → ℂ) → ℝ≥0∞, Measurable Φ → ∀ s : HCo a → Fin N → Fin a → ℂ,
    (∀ t ∈ GGram H a, (Matrix.of (s t))ᴴ * H * Matrix.of (s t) = hOf t) →
    (2 : ℝ≥0∞) ^ (N * a) * ∫⁻ X in {X | GDef H X}, Φ X =
      (2 : ℝ≥0∞) ^ (a * (a - 1) / 2) * ∫⁻ t in GGram H a,
        ENNReal.ofReal (C * ‖(hOf t).det‖ ^ (N - a)) *
          ∫⁻ g, Φ (Matrix.of.symm (Matrix.of g * Matrix.of (s t))) ∂μ

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem gDef_iff {k r a : ℕ} (X : Tup k r a) : GDef (Hpk k r) X ↔ DefPerp X := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gGram_eq (k r a : ℕ) : GGram (Hpk k r) a = DefGram k r a := rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem gLaw_iff (k r a : ℕ) (μ : Measure (Mt k r)) (C : ℝ) : GLaw (Hpk k r) a μ C ↔ IsGramConst k r a μ C :=
  Iff.rfl

def Sgn {a : ℕ} (d : Fin a → ℂ) : Prop := ∀ i, d i = 1 ∨ d i = -1

def Dg {a : ℕ} (d : Fin a → ℂ) (m : ℕ) : Matrix (Fin (a + m)) (Fin (a + m)) ℂ :=
  Matrix.diagonal (Fin.append d fun _ : Fin m => (1 : ℂ))

def E0 (a m : ℕ) : Matrix (Fin (a + m)) (Fin a) ℂ := fun i j => if i = Fin.castAdd m j then 1 else 0

def embB (a : ℕ) {m : ℕ} (b : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin (a + m)) (Fin (a + m)) ℂ :=
  blockM 1 0 0 b

abbrev MP (a m : ℕ) : Type := (Fin m → Fin a → ℂ) × HCo a

def Ym {a : ℕ} (d : Fin a → ℂ) (m : ℕ) (y : MP a m) : Matrix (Fin (a + m)) (Fin (a + m)) ℂ :=
  Dg d m * (Complex.I • blockM (hOf y.2) (Matrix.of y.1)ᴴ (Matrix.of y.1) 0)

def xu {a : ℕ} (d : Fin a → ℂ) (u : HCo a) : Matrix (Fin a) (Fin a) ℂ :=
  1 + (1 / 2 : ℂ) • (Matrix.diagonal d * hOf u)

def tau {a : ℕ} (d : Fin a → ℂ) (u : HCo a) : HCo a := coOf ((xu d u)ᴴ * Matrix.diagonal d * xu d u)

def chi {a : ℕ} (d : Fin a → ℂ) (m : ℕ) (p : MP a m × HCo a) : Fin (a + m) → Fin a → ℂ :=
  Matrix.of.symm (NormedSpace.exp (Ym d m p.1) * E0 a m * xu d p.2)

def chiD {a : ℕ} (d : Fin a → ℂ) (m : ℕ) (p : MP a m × HCo a) : Fin (a + m) → Fin a → ℂ :=
  Matrix.of.symm (Ym d m p.1 * E0 a m + E0 a m * ((1 / 2 : ℂ) • (Matrix.diagonal d * hOf p.2)))

def tube {a : ℕ} (d : Fin a → ℂ) (m : ℕ) (ρ : ℝ) : Set (PI.MtM (a + m)) :=
  {g | ∃ y ∈ Metric.ball (0 : MP a m) ρ, Matrix.of g * E0 a m = NormedSpace.exp (Ym d m y) * E0 a m}

def psiB (m : ℕ) (v : HCo m) : Matrix (Fin m) (Fin m) ℂ := NormedSpace.exp (Complex.I • hOf v)

def phiG {a : ℕ} (d : Fin a → ℂ) (m : ℕ) (p : MP a m × HCo m) : Matrix (Fin (a + m)) (Fin (a + m)) ℂ :=
  NormedSpace.exp (Ym d m p.1) * embB a (psiB m p.2)

/- English proof (translation)
Introduce `i`. Use `Fin.addCases (fun j => ?_) (fun j => ?_) i` and prove the remaining obligations. Simplify using `using hd j`. Simplify using the standard rewrite rules.
-/
theorem sgn_append {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) (m : ℕ) : Sgn (Fin.append d fun _ : Fin m => (1 : ℂ)) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using hd j
  · simp

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
/- English proof (translation)
Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases hd i with h | h <;> simp [h]`.
-/
theorem _root_.GlobalTheory.GramExp.diag_sq {a : ℕ} {d : Fin a → ℂ}
    (hd : _root_.GlobalTheory.GramExp.Sgn d) : Matrix.diagonal d * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases hd i with h | h <;> simp [h]

/- English proof (translation)
Rewrite using `[Matrix.diagonal_conjTranspose]`. Apply the tactic sequence `congr 1; funext i; rcases hd i with h | h <;> simp [h]`.
-/
theorem diag_herm {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) : (Matrix.diagonal d)ᴴ = Matrix.diagonal d := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1; funext i; rcases hd i with h | h <;> simp [h]

/- English proof (translation)
The claim follows from `diag_sq (sgn_append hd m)`.
-/
theorem Dg_sq {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) (m : ℕ) : Dg d m * Dg d m = 1 := diag_sq (sgn_append hd m)

/- English proof (translation)
The claim follows from `diag_herm (sgn_append hd m)`.
-/
theorem Dg_herm {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) (m : ℕ) : (Dg d m)ᴴ = Dg d m := diag_herm (sgn_append hd m)

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in

/- English proof (translation)
Unfold `_root_.PI.IsMatGroup _root_.Formalism.QuantumDeterminants.UH`. Establish `hdetH : H.det ≠ 0`. Introduce `h0`. Use `congrArg Matrix.det hH` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`.

Conclude with `zero_ne_one this`. Establish `hunit : ∀ a : Matrix (Fin N) (Fin N) ℂ, aᴴ * H * a = H → IsUnit a.det`. Introduce `a ha`. Use `congrArg Matrix.det ha` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul]`.

Establish `h1 : aᴴ.det * a.det = 1`. Establish `: (aᴴ.det * a.det) * H.det = 1 * H.det` using `by linear_combination this`. Conclude with `mul_right_cancel₀ hdetH this`. Conclude with `isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Simplify using the standard rewrite rules. Introduce `a ha b hb`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[Matrix.conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = H := by rw [ha, hb]`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`.

Establish `hu` using `hunit a ha`. Establish `hr : a * a⁻¹ = 1` using `Matrix.mul_nonsing_inv a hu`. Use `⟨?_, hr⟩` and prove the remaining obligations. Establish `hc : (a⁻¹)ᴴ * aᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, hr, Matrix.conjTranspose_one]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem _root_.GlobalTheory.GramExp.isMatGroup_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H * H = 1) : _root_.PI.IsMatGroup (_root_.Formalism.QuantumDeterminants.UH H) := by
  unfold _root_.PI.IsMatGroup _root_.Formalism.QuantumDeterminants.UH
  have hdetH : H.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hH
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hunit : ∀ a : Matrix (Fin N) (Fin N) ℂ, aᴴ * H * a = H → IsUnit a.det := by
    intro a ha
    have := congrArg Matrix.det ha
    rw [Matrix.det_mul, Matrix.det_mul] at this
    have h1 : aᴴ.det * a.det = 1 := by
      have : (aᴴ.det * a.det) * H.det = 1 * H.det := by linear_combination this
      exact mul_right_cancel₀ hdetH this
    exact isUnit_iff_ne_zero.mpr fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · simp
  · intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [ha, hb]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hu := hunit a ha
    have hr : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
    refine ⟨?_, hr⟩
    have hc : (a⁻¹)ᴴ * aᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hr, Matrix.conjTranspose_one]
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha]
      _ = ((a⁻¹)ᴴ * aᴴ) * H * (a * a⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hc, hr, Matrix.one_mul, Matrix.mul_one]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Use `letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _`. Conclude with `NormedSpace.exp_continuous`.
-/
theorem _root_.GlobalTheory.GramExp.exp_cont {n : ℕ} :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Unfold `hOf`. Apply the tactic sequence `split_ifs <;> fun_prop`.
-/
theorem hOf_cont {a : ℕ} : Continuous (hOf : HCo a → Matrix (Fin a) (Fin a) ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold hOf
  split_ifs <;> fun_prop

/- English proof (translation)
Apply the tactic sequence `ext i j; unfold hOf; split_ifs <;> simp`.
-/
theorem hOf_zero {a : ℕ} : hOf (0 : HCo a) = 0 := by
  ext i j; unfold hOf; split_ifs <;> simp

/- English proof (translation)
Apply the tactic sequence `ext i j; simp only [hOf, Matrix.neg_apply]; split_ifs <;> simp`.
-/
theorem hOf_neg {a : ℕ} (v : HCo a) : hOf (-v) = -hOf v := by
  ext i j; simp only [hOf, Matrix.neg_apply]; split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hT i) j`. Rewrite `h` using `[Matrix.conjTranspose_apply]`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Simplify using `[hOf, coOf, hij]`.

Simplify using `only [hOf, coOf, lt_irrefl, dite_false]`. Conclude with `Complex.conj_eq_iff_re.1 h`. Simplify using `only [hOf, coOf, hij, hij.not_gt, dite_false, dite_true]`. Conclude with `h`.
-/
theorem hOf_coOf {a : ℕ} {T : Matrix (Fin a) (Fin a) ℂ} (hT : Tᴴ = T) : hOf (coOf T) = T := by
  ext i j
  have h := congrFun (congrFun hT i) j
  rw [Matrix.conjTranspose_apply] at h
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hOf, coOf, hij]
  · simp only [hOf, coOf, lt_irrefl, dite_false]
    exact Complex.conj_eq_iff_re.1 h
  · simp only [hOf, coOf, hij, hij.not_gt, dite_false, dite_true]
    exact h

/- English proof (translation)
Use `Prod.ext (funext fun i => ?_) (funext fun p => ?_)` and prove the remaining obligations. Simplify using `[coOf, hOf]`. Simplify using `[coOf, hOf, p.2]`.
-/
theorem coOf_hOf {a : ℕ} (t : HCo a) : coOf (hOf t) = t := by
  refine Prod.ext (funext fun i => ?_) (funext fun p => ?_)
  · simp [coOf, hOf]
  · simp [coOf, hOf, p.2]

/- English proof (translation)
The claim follows from `(hP.matrix_fromBlocks hQ hR hS).matrix_reindex _ _`.
-/
theorem blockM_cont {X : Type} [TopologicalSpace X] {a b : ℕ} {P : X → Matrix (Fin a) (Fin a) ℂ}
    {Q : X → Matrix (Fin a) (Fin b) ℂ} {R : X → Matrix (Fin b) (Fin a) ℂ} {S : X → Matrix (Fin b) (Fin b) ℂ}
    (hP : Continuous P) (hQ : Continuous Q) (hR : Continuous R) (hS : Continuous S) :
    Continuous fun x => blockM (P x) (Q x) (R x) (S x) :=
  (hP.matrix_fromBlocks hQ hR hS).matrix_reindex _ _

/- English proof (translation)
Establish `h1 : Continuous fun y : MP a m => (Matrix.of y.1 : Matrix (Fin m) (Fin a) ℂ)` using `continuous_fst`. Conclude with `continuous_const.matrix_mul (Continuous.fun_const_smul (blockM_cont (hOf_cont.comp continuous_snd) h1.matrix_conjTranspose h1 continuous_const) _)`.
-/
theorem Ym_cont {a : ℕ} (d : Fin a → ℂ) (m : ℕ) : Continuous (Ym d m) := by
  have h1 : Continuous fun y : MP a m => (Matrix.of y.1 : Matrix (Fin m) (Fin a) ℂ) := continuous_fst
  exact continuous_const.matrix_mul (Continuous.fun_const_smul
    (blockM_cont (hOf_cont.comp continuous_snd) h1.matrix_conjTranspose h1 continuous_const) _)

/- English proof (translation)
The claim follows from `continuous_const.add (Continuous.fun_const_smul (continuous_const.matrix_mul hOf_cont) _)`.
-/
theorem xu_cont {a : ℕ} (d : Fin a → ℂ) : Continuous (xu d) :=
  continuous_const.add (Continuous.fun_const_smul (continuous_const.matrix_mul hOf_cont) _)

/- English proof (translation)
Use `Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => ?_)` and prove the remaining obligations. Conclude with `Complex.continuous_re.comp (continuous_id.matrix_elem i i)`. Conclude with `continuous_id.matrix_elem _ _`.
-/
theorem coOf_cont {a : ℕ} : Continuous (coOf : Matrix (Fin a) (Fin a) ℂ → HCo a) := by
  refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => ?_)
  · exact Complex.continuous_re.comp (continuous_id.matrix_elem i i)
  · exact continuous_id.matrix_elem _ _

/- English proof (translation)
The claim follows from `coOf_cont.comp (((xu_cont d).matrix_conjTranspose.matrix_mul continuous_const).matrix_mul (xu_cont d))`.
-/
theorem tau_cont {a : ℕ} (d : Fin a → ℂ) : Continuous (tau d) :=
  coOf_cont.comp (((xu_cont d).matrix_conjTranspose.matrix_mul continuous_const).matrix_mul (xu_cont d))

/- English proof (translation)
Establish `: Continuous fun p : MP a m × HCo a => NormedSpace.exp (Ym d m p.1) * E0 a m * xu d p.2` using `((exp_cont.comp ((Ym_cont d m).comp continuous_fst)).matrix_mul continuous_const).matrix_mul ((xu_cont d).comp continuous_snd)`. Conclude with `this`.
-/
theorem chi_cont {a : ℕ} (d : Fin a → ℂ) (m : ℕ) : Continuous (chi d m) := by
  have : Continuous fun p : MP a m × HCo a => NormedSpace.exp (Ym d m p.1) * E0 a m * xu d p.2 :=
    ((exp_cont.comp ((Ym_cont d m).comp continuous_fst)).matrix_mul continuous_const).matrix_mul
      ((xu_cont d).comp continuous_snd)
  exact this

/- English proof (translation)
The claim follows from `exp_cont.comp (hOf_cont.fun_const_smul _)`.
-/
theorem psiB_cont (m : ℕ) : Continuous (psiB m) := exp_cont.comp (hOf_cont.fun_const_smul _)

/- English proof (translation)
Simplify using `[xu, hOf_zero]`.
-/
theorem xu_zero {a : ℕ} (d : Fin a → ℂ) : xu d 0 = 1 := by simp [xu, hOf_zero]

/- English proof (translation)
The claim follows from `hOf_coOf (by simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, diag_herm hd, Matrix.mul_assoc])`.
-/
theorem hOf_tau {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) (u : HCo a) :
    hOf (tau d u) = (xu d u)ᴴ * Matrix.diagonal d * xu d u :=
  hOf_coOf (by simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, diag_herm hd,
    Matrix.mul_assoc])

/- English proof (translation)
Simplify using `only [blockM, Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]`.
-/
theorem blockM_herm {a b : ℕ} (P : Matrix (Fin a) (Fin a) ℂ) (Q : Matrix (Fin a) (Fin b) ℂ)
    (R : Matrix (Fin b) (Fin a) ℂ) (S : Matrix (Fin b) (Fin b) ℂ) :
    (blockM P Q R S)ᴴ = blockM Pᴴ Rᴴ Qᴴ Sᴴ := by
  simp only [blockM, Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]

/- English proof (translation)
Simplify using `only [blockM, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`.
-/
theorem blockM_mul {a b : ℕ} (P P' : Matrix (Fin a) (Fin a) ℂ) (Q Q' : Matrix (Fin a) (Fin b) ℂ)
    (R R' : Matrix (Fin b) (Fin a) ℂ) (S S' : Matrix (Fin b) (Fin b) ℂ) :
    blockM P Q R S * blockM P' Q' R' S' =
      blockM (P * P' + Q * R') (P * Q' + Q * S') (R * P' + S * R') (R * Q' + S * S') := by
  simp only [blockM, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>`. Apply the tactic sequence `simp [Dg, blockM, Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff] <;> omega`.
-/
theorem Dg_eq {a : ℕ} (d : Fin a → ℂ) (m : ℕ) : Dg d m = blockM (Matrix.diagonal d) 0 0 1 := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [Dg, blockM, Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff] <;> omega

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_mul, h1, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h2, Matrix.conjTranspose_smul, hA]`. Simplify using the standard rewrite rules.
-/
theorem lie_of_herm {N : ℕ} {H A : Matrix (Fin N) (Fin N) ℂ} (h1 : Hᴴ = H) (h2 : H * H = 1) (hA : Aᴴ = A) :
    (H * (Complex.I • A))ᴴ * H + H * (H * (Complex.I • A)) = 0 := by
  rw [Matrix.conjTranspose_mul, h1, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h2, Matrix.conjTranspose_smul, hA]
  simp

/- English proof (translation)
The claim follows from `CCRuleCW.exp_mem_UH _ _ (lie_of_herm (Dg_herm hd m) (Dg_sq hd m) (by rw [blockM_herm, (hOf_isHermitian y.2).eq]; simp))`.
-/
theorem exp_Ym_mem {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) (m : ℕ) (y : MP a m) :
    NormedSpace.exp (Ym d m y) ∈ UH (Dg d m) :=
  CCRuleCW.exp_mem_UH _ _ (lie_of_herm (Dg_herm hd m) (Dg_sq hd m) (by
    rw [blockM_herm, (hOf_isHermitian y.2).eq]; simp))

/- English proof (translation)
Use `lie_of_herm (H := (1 : Matrix (Fin m) (Fin m) ℂ)) (by simp) (by simp) (hOf_isHermitian v).eq` as an intermediate fact. Rewrite `this` using `[Matrix.one_mul (Complex.I • hOf v)]`. Conclude with `CCRuleCW.exp_mem_UH _ _ this`.
-/
theorem psiB_mem (m : ℕ) (v : HCo m) : psiB m v ∈ UH (1 : Matrix (Fin m) (Fin m) ℂ) := by
  have := lie_of_herm (H := (1 : Matrix (Fin m) (Fin m) ℂ)) (by simp) (by simp) (hOf_isHermitian v).eq
  rw [Matrix.one_mul (Complex.I • hOf v)] at this
  exact CCRuleCW.exp_mem_UH _ _ this

/- English proof (translation)
Rewrite using `[psiB, psiB, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, (hOf_isHermitian v).eq, hOf_neg]`. Simplify using the standard rewrite rules.
-/
theorem psiB_neg (m : ℕ) (v : HCo m) : psiB m (-v) = (psiB m v)ᴴ := by
  rw [psiB, psiB, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, (hOf_isHermitian v).eq, hOf_neg]
  simp

/- English proof (translation)
Establish `hb' : bᴴ * 1 * b = 1` using `hb`. Use `show (embB a b)ᴴ * Dg d m * embB a b = Dg d m`. Rewrite using `[Dg_eq, embB, blockM_herm, blockM_mul, blockM_mul]`. Simplify using `only [Matrix.mul_one] at hb'`. Simplify using `[hb']`.
-/
theorem embB_mem {a : ℕ} (d : Fin a → ℂ) {m : ℕ} {b : Matrix (Fin m) (Fin m) ℂ}
    (hb : b ∈ UH (1 : Matrix (Fin m) (Fin m) ℂ)) : embB a b ∈ UH (Dg d m) := by
  have hb' : bᴴ * 1 * b = 1 := hb
  show (embB a b)ᴴ * Dg d m * embB a b = Dg d m
  rw [Dg_eq, embB, blockM_herm, blockM_mul, blockM_mul]
  simp only [Matrix.mul_one] at hb'
  simp [hb']

/- English proof (translation)
The claim follows from `CCRuleCW.UH_mul _ _ _ (exp_Ym_mem hd m _) (embB_mem d (psiB_mem m _))`.
-/
theorem phiG_mem {a : ℕ} {d : Fin a → ℂ} (hd : Sgn d) (m : ℕ) (p : MP a m × HCo m) : phiG d m p ∈ UH (Dg d m) :=
  CCRuleCW.UH_mul _ _ _ (exp_Ym_mem hd m _) (embB_mem d (psiB_mem m _))

/- English proof (translation)
Simplify using `[embB, blockM]`.
-/
theorem embB_one (a m : ℕ) : embB a (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  simp [embB, blockM]

/- English proof (translation)
Establish `: (Matrix.of (0 : Fin m → Fin a → ℂ) : Matrix (Fin m) (Fin a) ℂ) = 0` using `rfl`. Simplify using `[Ym, blockM, hOf_zero, this]`.
-/
theorem Ym_zero {a : ℕ} (d : Fin a → ℂ) (m : ℕ) : Ym d m 0 = 0 := by
  have : (Matrix.of (0 : Fin m → Fin a → ℂ) : Matrix (Fin m) (Fin a) ℂ) = 0 := rfl
  simp [Ym, blockM, hOf_zero, this]

/- English proof (translation)
Simplify using `[psiB, hOf_zero]`.
-/
theorem psiB_zero (m : ℕ) : psiB m 0 = 1 := by simp [psiB, hOf_zero]

/- English proof (translation)
Simplify using `[phiG, Ym_zero, psiB_zero, embB_one]`.
-/
theorem phiG_zero {a : ℕ} (d : Fin a → ℂ) (m : ℕ) : phiG d m 0 = 1 := by
  simp [phiG, Ym_zero, psiB_zero, embB_one]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd m j)]`. Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>`. Simplify using `[E0, embB, blockM, Matrix.one_apply, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.

Introduce `l _ hl`. Simplify using `[E0, hl]`. Simplify using the standard rewrite rules.
-/
theorem block_embed_mul_E0 (a : ℕ) {m : ℕ} (b : Matrix (Fin m) (Fin m) ℂ) : embB a b * E0 a m = E0 a m := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd m j)]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp [E0, embB, blockM, Matrix.one_apply, Fin.ext_iff]
    omega
  · intro l _ hl; simp [E0, hl]
  · simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd m j)]`. Rewrite using `[Dg, Matrix.mul_diagonal]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[E0]`. Establish `: ¬ j = i` using `fun e => h e.symm`. Simplify using `[E0, h, this]`. Introduce `l _ hl`. Simplify using `[E0, hl]`.

Simplify using the standard rewrite rules.
-/
theorem gram_E0_diagonal {a : ℕ} (d : Fin a → ℂ) (m : ℕ) : (E0 a m)ᴴ * Dg d m * E0 a m = Matrix.diagonal d := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd m j)]
  · rw [Dg, Matrix.mul_diagonal]
    by_cases h : i = j
    · subst h; simp [E0]
    · have : ¬ j = i := fun e => h e.symm
      simp [E0, h, this]
  · intro l _ hl; simp [E0, hl]
  · simp

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in

/- English proof (translation)
Establish `hb : Metric.ball x ρ = ⋃ k : ℕ, Metric.closedBall x (ρ - 1 / ((k : ℝ) + 1))`. Use extensionality with `y`. Simplify using `only [Metric.mem_ball, Set.mem_iUnion, Metric.mem_closedBall]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨k, hk⟩` from `exists_nat_one_div_lt (sub_pos.mpr h)`. Conclude with `⟨k, by linarith⟩`. Introduce and unpack `⟨k, hk⟩`. Establish `: 0 < 1 / ((k : ℝ) + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hb, Set.image_iUnion]`. Conclude with `MeasurableSet.iUnion fun k => ((isCompact_closedBall x _).image hf).isClosed.measurableSet`.
-/
theorem _root_.GlobalTheory.GramExp.measurableSet_image_ball {X Y : Type} [PseudoMetricSpace X] [ProperSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {f : X → Y}
    (hf : Continuous f) (x : X) (ρ : ℝ) :
    MeasurableSet (f '' Metric.ball x ρ) := by
  have hb : Metric.ball x ρ = ⋃ k : ℕ, Metric.closedBall x (ρ - 1 / ((k : ℝ) + 1)) := by
    ext y
    simp only [Metric.mem_ball, Set.mem_iUnion, Metric.mem_closedBall]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hb, Set.image_iUnion]
  exact MeasurableSet.iUnion fun k =>
    ((isCompact_closedBall x _).image hf).isClosed.measurableSet

end GlobalTheory.GramExp

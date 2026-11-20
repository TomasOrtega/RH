import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitary
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFacts

noncomputable section

open Matrix MeasureTheory Finset
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.GradLine

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S GlobalTheory.FlagMeas Formalism.MainNotions.S GlobalTheory.CompanionTheory.GradFlag

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Unfold `pM`. Rewrite using `[mul_smul_comm, ← smul_neg]`. Use `congr 1`. Simplify using `only [mul_sub, ← mul_assoc, h3]`. Normalize the expressions using the abelian group laws.
-/
theorem A_mul_pM (h3 : A * A * A = A) : A * pM A = -pM A := by
  unfold pM
  rw [mul_smul_comm, ← smul_neg]
  congr 1
  simp only [mul_sub, ← mul_assoc, h3]
  abel

/- English proof (translation)
Unfold `pM qM`. Use `module`.
-/
theorem qM_sub_pM : qM A - pM A = A := by
  unfold pM qM
  module

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Express the relevant statement in the definitionally equal form `pM A *ᵥ (pM A *ᵥ z) = pM A *ᵥ z`. Rewrite using `[mulVec_mulVec, pM_idem h3]`. Introduce `h`.

Conclude with `⟨y, h⟩`.
-/
theorem mem_Vm (h3 : A * A * A = A) {y : Fin n → ℂ} : y ∈ Vm A ↔ pM A *ᵥ y = y := by
  constructor
  · rintro ⟨z, rfl⟩
    change pM A *ᵥ (pM A *ᵥ z) = pM A *ᵥ z
    rw [mulVec_mulVec, pM_idem h3]
  · intro h
    exact ⟨y, h⟩

/- English proof (translation)
Rewrite using `[← (mem_Vm h3).1 hy, mulVec_mulVec, A_mul_pM h3, neg_mulVec]`.
-/
theorem A_mulVec_of_mem (h3 : A * A * A = A) {y : Fin n → ℂ} (hy : y ∈ Vm A) : A *ᵥ y = -y := by
  rw [← (mem_Vm h3).1 hy, mulVec_mulVec, A_mul_pM h3, neg_mulVec]

/- English proof (translation)
Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [Matrix.toLin'_apply]`. Use `(mem_Vm h3).1 (hg _ ((mem_Vm h3).2 (show pM A *ᵥ (pM A *ᵥ v) = pM A *ᵥ v by` as an intermediate fact. Rewrite using `[mulVec_mulVec, pM_idem h3])))`.

Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec]`. Conclude with `this`.
-/
theorem pM_mul_of_keeps (h3 : A * A * A = A) {g : Matrix (Fin n) (Fin n) ℂ} (hg : ∀ y ∈ Vm A, g *ᵥ y ∈ Vm A) :
    pM A * (g * pM A) = g * pM A := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  simp only [Matrix.toLin'_apply]
  have := (mem_Vm h3).1 (hg _ ((mem_Vm h3).2 (show pM A *ᵥ (pM A *ᵥ v) = pM A *ᵥ v by
    rw [mulVec_mulVec, pM_idem h3])))
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  exact this

/- English proof (translation)
Establish `h1` using `pM_mul_of_keeps h3 hg`. Establish `h2` using `congrArg conjTranspose (pM_mul_of_keeps h3 hg')`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, pM_conjTranspose hH] at h2`. Rewrite using `[← h1, ← mul_assoc, h2]`.
-/
theorem commute_pM (h3 : A * A * A = A) (hH : Aᴴ = A) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : ∀ y ∈ Vm A, g *ᵥ y ∈ Vm A) (hg' : ∀ y ∈ Vm A, gᴴ *ᵥ y ∈ Vm A) : g * pM A = pM A * g := by
  have h1 := pM_mul_of_keeps h3 hg
  have h2 := congrArg conjTranspose (pM_mul_of_keeps h3 hg')
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, pM_conjTranspose hH] at h2
  rw [← h1, ← mul_assoc, h2]

/- English proof (translation)
Rewrite using `[J_mul_pM hG, mul_assoc, Formalism.REAL.Jm_mul_self, mul_one]`.
-/
theorem J_pM_J (hG : IsGrad ε A) : Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε = qM A := by
  rw [J_mul_pM hG, mul_assoc, Formalism.REAL.Jm_mul_self, mul_one]

/- English proof (translation)
Establish `h3` using `hG.2.2.1`. Establish `hH` using `hG.2.1`. Establish `hJJ` using `Formalism.REAL.Jm_mul_self ε`. Establish `hqp` using `J_pM_J hG`. Establish `hU : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε` using `m.2`.

Generalize the expression as in `Formalism.REAL.Jm ε = J at *`. Establish `hm : uMat m * pM A = pM A * uMat m` using `commute_pM h3 hH h1 h2`. Establish `hmH : (uMat m)ᴴ * pM A = pM A * (uMat m)ᴴ`. Use `congrArg conjTranspose hm` as an intermediate fact. Simplify `this.symm` using `only [conjTranspose_mul, pM_conjTranspose hH]`.

Establish `hinv : (uMat m)ᴴ * (J * uMat m * J) = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hinv' : (J * uMat m * J) * (uMat m)ᴴ = 1` using `mul_eq_one_comm.1 hinv`. Establish `hc : (J * uMat m * J) * pM A = pM A * (J * uMat m * J)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hinv, mul_one]`. Use `_ = (J * uMat m * J) * ((uMat m)ᴴ * pM A) * (J * uMat m * J) := by`. Rewrite using `[hmH]`. Simplify using `only [mul_assoc]`. Use `_ = ((J * uMat m * J) * (uMat m)ᴴ) * pM A * (J * uMat m * J) := by simp only [mul_assoc]`.

Use `_ = pM A * (J * uMat m * J) := by rw [hinv', one_mul]`. Establish `hp : uMat m * qM A = qM A * uMat m`. Rewrite using `[← hqp]`. Establish `e1 : uMat m * (J * pM A * J) = J * ((J * uMat m * J) * pM A) * J`. Establish `: J * ((J * uMat m * J) * pM A) * J = (J * J) * uMat m * (J * pM A * J)` using `by simp only [mul_assoc]`.

Rewrite using `[this, hJJ, one_mul]`. Establish `e2 : (J * pM A * J) * uMat m = J * (pM A * (J * uMat m * J)) * J`. Establish `: J * (pM A * (J * uMat m * J)) * J = (J * pM A * J) * uMat m * (J * J)` using `by simp only [mul_assoc]`. Rewrite using `[this, hJJ, mul_one]`. Rewrite using `[e1, e2, hc]`.

Rewrite using `[← qM_sub_pM (A := A), mul_sub, sub_mul, hm, hp]`.
-/
theorem commute_A (hG : IsGrad ε A) {m : Formalism.REAL.UJ ε} (h1 : ∀ y ∈ Vm A, uMat m *ᵥ y ∈ Vm A)
    (h2 : ∀ y ∈ Vm A, (uMat m)ᴴ *ᵥ y ∈ Vm A) : uMat m * A = A * uMat m := by
  have h3 := hG.2.2.1
  have hH := hG.2.1
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hqp := J_pM_J hG
  have hU : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  generalize Formalism.REAL.Jm ε = J at *
  have hm : uMat m * pM A = pM A * uMat m := commute_pM h3 hH h1 h2
  have hmH : (uMat m)ᴴ * pM A = pM A * (uMat m)ᴴ := by
    have := congrArg conjTranspose hm
    simpa only [conjTranspose_mul, pM_conjTranspose hH] using this.symm
  have hinv : (uMat m)ᴴ * (J * uMat m * J) = 1 := by
    calc (uMat m)ᴴ * (J * uMat m * J) = ((uMat m)ᴴ * J * uMat m) * J := by simp only [mul_assoc]
      _ = 1 := by rw [hU, hJJ]
  have hinv' : (J * uMat m * J) * (uMat m)ᴴ = 1 := mul_eq_one_comm.1 hinv
  have hc : (J * uMat m * J) * pM A = pM A * (J * uMat m * J) := by
    calc (J * uMat m * J) * pM A = (J * uMat m * J) * (pM A * ((uMat m)ᴴ * (J * uMat m * J))) := by
          rw [hinv, mul_one]
      _ = (J * uMat m * J) * ((uMat m)ᴴ * pM A) * (J * uMat m * J) := by
          rw [hmH]; simp only [mul_assoc]
      _ = ((J * uMat m * J) * (uMat m)ᴴ) * pM A * (J * uMat m * J) := by simp only [mul_assoc]
      _ = pM A * (J * uMat m * J) := by rw [hinv', one_mul]
  have hp : uMat m * qM A = qM A * uMat m := by
    rw [← hqp]
    have e1 : uMat m * (J * pM A * J) = J * ((J * uMat m * J) * pM A) * J := by
      have : J * ((J * uMat m * J) * pM A) * J = (J * J) * uMat m * (J * pM A * J) := by simp only [mul_assoc]
      rw [this, hJJ, one_mul]
    have e2 : (J * pM A * J) * uMat m = J * (pM A * (J * uMat m * J)) * J := by
      have : J * (pM A * (J * uMat m * J)) * J = (J * pM A * J) * uMat m * (J * J) := by simp only [mul_assoc]
      rw [this, hJJ, mul_one]
    rw [e1, e2, hc]
  rw [← qM_sub_pM (A := A), mul_sub, sub_mul, hm, hp]

open scoped Matrix.Norms.Operator in
/- English proof (translation)
Establish `hp : ∀ k : ℕ, (M ^ k) *ᵥ y = c ^ k • y`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, h, smul_smul, pow_succ]`.

Establish `h1` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) M`. Establish `h2` using `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const y`. Set `L : Matrix (Fin n) (Fin n) ℂ →+ (Fin n → ℂ)` to `AddMonoidHom.mk' (fun N => N *ᵥ y) (fun a b => add_mulVec a b y)`. Establish `hL : Continuous L` using `continuous_id.matrix_mulVec continuous_const`. Establish `h3` using `h1.map L hL`.

Rewrite `h2` using `[← Complex.exp_eq_exp_ℂ]`. Use `h3.unique ?_` and prove the remaining obligations. Use `h2 using 2 with k` and compare the differences between its conclusion and the goal. Simplify using `[L, smul_mulVec, hp, smul_smul]`.
-/
theorem exp_mulVec_of_eigen {M : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℂ} {c : ℂ} (h : M *ᵥ y = c • y) :
    NormedSpace.exp M *ᵥ y = Complex.exp c • y := by
  have hp : ∀ k : ℕ, (M ^ k) *ᵥ y = c ^ k • y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, h, smul_smul, pow_succ]
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) M
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const y
  let L : Matrix (Fin n) (Fin n) ℂ →+ (Fin n → ℂ) :=
    AddMonoidHom.mk' (fun N => N *ᵥ y) (fun a b => add_mulVec a b y)
  have hL : Continuous L := continuous_id.matrix_mulVec continuous_const
  have h3 := h1.map L hL
  rw [← Complex.exp_eq_exp_ℂ] at h2
  refine h3.unique ?_
  convert h2 using 2 with k
  simp [L, smul_mulVec, hp, smul_smul]

def eT (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp ((t : ℂ) • A)

/- English proof (translation)
Unfold `eT`. Rewrite using `[Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute]`. Conclude with `((Commute.refl A).smul_left _).smul_right _`.
-/
theorem eT_add (s t : ℝ) : eT A (s + t) = eT A s * eT A t := by
  unfold eT
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl A).smul_left _).smul_right _

/- English proof (translation)
Simplify using `[eT]`.
-/
theorem eT_zero : eT A 0 = 1 := by simp [eT]

/- English proof (translation)
Use `open scoped Matrix.Norms.Operator in`. Conclude with `NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)`.
-/
theorem continuous_eT : Continuous (eT A) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)

/- English proof (translation)
Unfold `eT`. Rewrite using `[← Matrix.exp_conjTranspose]`. Simplify using `[conjTranspose_smul, hH]`.
-/
theorem eT_herm (hH : Aᴴ = A) (t : ℝ) : (eT A t)ᴴ = eT A t := by
  unfold eT
  rw [← Matrix.exp_conjTranspose]
  simp [conjTranspose_smul, hH]

/- English proof (translation)
Establish `h : ((t : ℂ) • A) *ᵥ y = (-(t : ℂ)) • y`. Rewrite using `[smul_mulVec, A_mulVec_of_mem h3 hy, smul_neg, neg_smul]`. Rewrite using `[eT, exp_mulVec_of_eigen h]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem eT_mulVec (h3 : A * A * A = A) {y : Fin n → ℂ} (hy : y ∈ Vm A) (t : ℝ) :
    eT A t *ᵥ y = ((Real.exp (-t) : ℝ) : ℂ) • y := by
  have h : ((t : ℂ) • A) *ᵥ y = (-(t : ℂ)) • y := by
    rw [smul_mulVec, A_mulVec_of_mem h3 hy, smul_neg, neg_smul]
  rw [eT, exp_mulVec_of_eigen h]
  push_cast
  rfl

/- English proof (translation)
Introduce `y hy` and use `by rw [eT_mulVec h3 hy] exact (Vm A).smul_mem _ hy`.
-/
theorem eT_keeps (h3 : A * A * A = A) (t : ℝ) : ∀ y ∈ Vm A, eT A t *ᵥ y ∈ Vm A := fun y hy => by
  rw [eT_mulVec h3 hy]
  exact (Vm A).smul_mem _ hy

def aLine (hG : IsGrad ε A) (t : ℝ) : Formalism.REAL.UJ ε :=
  ⟨⟨eT A t, eT A (-t), by rw [← eT_add, add_neg_cancel, eT_zero], by rw [← eT_add, neg_add_cancel, eT_zero]⟩,
    Formalism.REAL.exp_indefinite_unitary_holds n ε A hG.1 t⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uMat_aLine (hG : IsGrad ε A) (t : ℝ) : uMat (aLine hG t) = eT A t := rfl

/- English proof (translation)
Use `continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `continuous_eT`. Conclude with `continuous_eT.comp continuous_neg`.
-/
theorem continuous_aLine (hG : IsGrad ε A) : Continuous (aLine hG) := by
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact continuous_eT
  · exact continuous_eT.comp continuous_neg

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext (eT_add s t))`.
-/
theorem aLine_add (hG : IsGrad ε A) (s t : ℝ) : aLine hG (s + t) = aLine hG s * aLine hG t :=
  Subtype.ext (Units.ext (eT_add s t))

/- English proof (translation)
Establish `key` using `eT_keeps hG.2.2.1 t`. Establish `: ∀ i : Fin 2, ∀ y ∈ W A i, eT A t *ᵥ y ∈ W A i ∧ (eT A t)ᴴ *ᵥ y ∈ W A i`. Rewrite using `[Fin.forall_fin_two]`. Use `⟨fun y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hy0 : y = 0` using `hy`.

Substitute `hy0` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[eT_herm hG.2.1]`. Conclude with `⟨key y hy, key y hy⟩`. Conclude with `this`.
-/
theorem aLine_mem (hG : IsGrad ε A) (t : ℝ) : aLine hG t ∈ flagM ε (W A) := by
  have key := eT_keeps hG.2.2.1 t
  have : ∀ i : Fin 2, ∀ y ∈ W A i, eT A t *ᵥ y ∈ W A i ∧ (eT A t)ᴴ *ᵥ y ∈ W A i := by
    rw [Fin.forall_fin_two]
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hy0 : y = 0 := hy
      subst hy0
      simp
    · rw [eT_herm hG.2.1]
      exact ⟨key y hy, key y hy⟩
  exact this

/- English proof (translation)
Introduce `y hy` and use `(hm 1 y hy).1`.
-/
theorem keeps_of_mem {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) : ∀ y ∈ Vm A, uMat m *ᵥ y ∈ Vm A :=
  fun y hy => (hm 1 y hy).1

/- English proof (translation)
Introduce `y hy` and use `(hm 1 y hy).2`.
-/
theorem keepsH_of_mem {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) : ∀ y ∈ Vm A, (uMat m)ᴴ *ᵥ y ∈ Vm A :=
  fun y hy => (hm 1 y hy).2

/- English proof (translation)
Establish `hc : Commute (uMat m) ((t : ℂ) • A)` using `Commute.smul_right (commute_A hG (keeps_of_mem hm) (keepsH_of_mem hm)) _`. Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations. Use `show uMat m * eT A t = eT A t * uMat m`. Use `open scoped Matrix.Norms.Operator in`. Conclude with `hc.exp_right`.
-/
theorem aLine_comm (hG : IsGrad ε A) (t : ℝ) {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) :
    m * aLine hG t = aLine hG t * m := by
  have hc : Commute (uMat m) ((t : ℂ) • A) :=
    Commute.smul_right (commute_A hG (keeps_of_mem hm) (keepsH_of_mem hm)) _
  refine Subtype.ext (Units.ext ?_)
  show uMat m * eT A t = eT A t * uMat m
  open scoped Matrix.Norms.Operator in
  exact hc.exp_right

/- English proof (translation)
Unfold `detOn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem detOn_nonneg (g : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)) : 0 ≤ detOn g V := by
  unfold detOn
  split_ifs <;> simp

/- English proof (translation)
Establish `hk : ∀ y ∈ Vm A, Matrix.toLin' (eT A t) y ∈ Vm A` using `eT_keeps h3 t`. Establish `hr : (Matrix.toLin' (eT A t)).restrict hk = ((Real.exp (-t) : ℝ) : ℂ) • LinearMap.id`. Use extensionality with `y : 2`. Simplify using `only [LinearMap.restrict_coe_apply, Matrix.toLin'_apply, eT_mulVec h3 y.2]`. Both sides reduce to the same expression.

Unfold `detOn`. Rewrite using `[dif_pos hk, hr, LinearMap.det_smul, LinearMap.det_id, mul_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]`. Use `congr 1`. Simplify using `only [rk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem detOn_eT (h3 : A * A * A = A) (t : ℝ) : detOn (eT A t) (Vm A) = Real.exp (-((rk A : ℝ) * t)) := by
  have hk : ∀ y ∈ Vm A, Matrix.toLin' (eT A t) y ∈ Vm A := eT_keeps h3 t
  have hr : (Matrix.toLin' (eT A t)).restrict hk = ((Real.exp (-t) : ℝ) : ℂ) • LinearMap.id := by
    ext y : 2
    simp only [LinearMap.restrict_coe_apply, Matrix.toLin'_apply, eT_mulVec h3 y.2]
    rfl
  unfold detOn
  rw [dif_pos hk, hr, LinearMap.det_smul, LinearMap.det_id, mul_one, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 1
  simp only [rk]
  ring

/- English proof (translation)
Take `⟨-, -, h3, -⟩` from `id hG`. Establish `hs : A * A = pM A + qM A`. Unfold `pM qM`. Use `module`. Establish `hi : IsIdempotentElem (Matrix.toLin' (A * A))`.

Establish `e : A * A * (A * A) = A * A` using `by rw [← mul_assoc, h3]`. Express the relevant statement in the definitionally equal form `Matrix.toLin' (A * A) * Matrix.toLin' (A * A) = _`. Rewrite using `[Module.End.mul_eq_comp, ← Matrix.toLin'_mul, e]`. Establish `ht` using `(LinearMap.IsIdempotentElem.isProj_range _ hi).trace`. Rewrite `ht` using `[Matrix.trace_toLin'_eq]`.

Establish `h2 : Matrix.trace (A * A) = ((2 * rk A : ℕ) : ℂ)`. Rewrite using `[hs, Matrix.trace_add, trace_qM hG, trace_pM h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e : 2 * rk A = Module.finrank ℂ (LinearMap.range (Matrix.toLin' (A * A)))`.

Conclude with `h2.symm.trans ht` after adjusting the coercions. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem two_rk_le (hG : IsGrad ε A) : 2 * rk A ≤ n := by
  obtain ⟨-, -, h3, -⟩ := id hG
  have hs : A * A = pM A + qM A := by
    unfold pM qM
    module
  have hi : IsIdempotentElem (Matrix.toLin' (A * A)) := by
    have e : A * A * (A * A) = A * A := by rw [← mul_assoc, h3]
    change Matrix.toLin' (A * A) * Matrix.toLin' (A * A) = _
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, e]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  rw [Matrix.trace_toLin'_eq] at ht
  have h2 : Matrix.trace (A * A) = ((2 * rk A : ℕ) : ℂ) := by
    rw [hs, Matrix.trace_add, trace_qM hG, trace_pM h3]
    push_cast
    ring
  have e : 2 * rk A = Module.finrank ℂ (LinearMap.range (Matrix.toLin' (A * A))) := by
    exact_mod_cast h2.symm.trans ht
  rw [e]
  calc Module.finrank ℂ (LinearMap.range (Matrix.toLin' (A * A))) ≤ Module.finrank ℂ (Fin n → ℂ) :=
        Submodule.finrank_le _
    _ = n := by simp

/- English proof (translation)
Use `show (detOn g (Vm A) / detOn g ⊥) ^ (-(1 : ℝ) / rk A) = _`. Rewrite using `[GlobalTheory.RealInd.detOn_bot, div_one]`.
-/
theorem locSize_eq (g : Matrix (Fin n) (Fin n) ℂ) :
    locSize (fun _ : Fin 1 => rk A) (W A) g 0 = detOn g (Vm A) ^ (-(1 : ℝ) / rk A) := by
  show (detOn g (Vm A) / detOn g ⊥) ^ (-(1 : ℝ) / rk A) = _
  rw [GlobalTheory.RealInd.detOn_bot, div_one]

/- English proof (translation)
Simplify using `[GlobalTheory.Count.layerProd, Finset.filter_singleton]`.
-/
theorem layer_eq (j : ℕ) (τ : Fin 1 → ℝ) :
    GlobalTheory.Count.layerProd n 1 (fun _ : Fin 1 => j) τ id = τ 0 ^ (2 * j * (n - 2 * j)) * (τ 0 ^ 2) ^ (j ^ 2) := by
  simp [GlobalTheory.Count.layerProd, Finset.filter_singleton]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `detOn (uMat m * eT A t) (Vm A) = _`. Rewrite using `[GlobalTheory.RealInd.detOn_mul (keeps_of_mem hm) (eT_keeps hG.2.2.1 t), detOn_eT hG.2.2.1]`.
-/
theorem detOn_mul_line (hG : IsGrad ε A) {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) (t : ℝ) :
    detOn (uMat (m * aLine hG t)) (Vm A) = detOn (uMat m) (Vm A) * Real.exp (-((rk A : ℝ) * t)) := by
  change detOn (uMat m * eT A t) (Vm A) = _
  rw [GlobalTheory.RealInd.detOn_mul (keeps_of_mem hm) (eT_keeps hG.2.2.1 t), detOn_eT hG.2.2.1]

/- English proof (translation)
Take `⟨hj, -, hρ⟩` from `flagFacts n ε A hG`. Establish `h2` using `two_rk_le hG`. Establish `hj0 : (rk A : ℝ) ≠ 0`. Establish `: 1 ≤ (rk A : ℝ)` using `by exact_mod_cast hj`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set x := detOn (uMat m) (Vm A) ^ (-(1 : ℝ) / rk A) with hx`. Establish `hx0 : 0 ≤ x` using `Real.rpow_nonneg (detOn_nonneg _ _) _`. Establish `hloc : detOn (uMat (m * aLine hG t)) (Vm A) ^ (-(1 : ℝ) / rk A) = x * Real.exp t`. Rewrite using `[detOn_mul_line hG hm, Real.mul_rpow (detOn_nonneg _ _) (Real.exp_pos _).le, ← Real.exp_mul]`. Use `congr 2`.

Clear the denominators using the available nonvanishing facts. Establish `hexp : Real.exp t ^ (2 * rk A * (n - 2 * rk A)) * (Real.exp t ^ 2) ^ (rk A ^ 2) = Real.exp (2 * rhoA A * t)`. Rewrite using `[← pow_mul, ← pow_add, ← Real.exp_nat_mul, hρ]`. Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub h2]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `modA`. Rewrite using `[layer_eq, layer_eq, locSize_eq, locSize_eq, hloc, ← hx, ← ENNReal.ofReal_mul (by positivity), ← hexp]`. Use `congr 1`. Simplify using `only [mul_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem modA_line (hG : IsGrad ε A) {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) (t : ℝ) :
    modA A (m * aLine hG t) = modA A m * ENNReal.ofReal (Real.exp (2 * rhoA A * t)) := by
  obtain ⟨hj, -, hρ⟩ := flagFacts n ε A hG
  have h2 := two_rk_le hG
  have hj0 : (rk A : ℝ) ≠ 0 := by
    have : 1 ≤ (rk A : ℝ) := by exact_mod_cast hj
    linarith
  set x := detOn (uMat m) (Vm A) ^ (-(1 : ℝ) / rk A) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg (detOn_nonneg _ _) _
  have hloc : detOn (uMat (m * aLine hG t)) (Vm A) ^ (-(1 : ℝ) / rk A) = x * Real.exp t := by
    rw [detOn_mul_line hG hm, Real.mul_rpow (detOn_nonneg _ _) (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    field_simp
  have hexp : Real.exp t ^ (2 * rk A * (n - 2 * rk A)) * (Real.exp t ^ 2) ^ (rk A ^ 2) =
      Real.exp (2 * rhoA A * t) := by
    rw [← pow_mul, ← pow_add, ← Real.exp_nat_mul, hρ]
    congr 1
    push_cast [Nat.cast_sub h2]
    ring
  unfold modA
  rw [layer_eq, layer_eq, locSize_eq, locSize_eq, hloc, ← hx, ← ENNReal.ofReal_mul (by positivity), ← hexp]
  congr 1
  simp only [mul_pow]
  ring

def tau (A : Matrix (Fin n) (Fin n) ℂ) (g : Formalism.REAL.UJ ε) : ℝ :=
  -(1 / (rk A : ℝ)) * Real.log (detOn (uMat g) (Vm A))

/- English proof (translation)
Establish `hf : Continuous fun g : Formalism.REAL.UJ ε => uMat g` using `Units.continuous_val.comp continuous_subtype_val`. Conclude with `measurable_const.mul (Real.measurable_log.comp (measurable_detOn_comp _ hf _))`.
-/
theorem measurable_tau : Measurable (tau A : Formalism.REAL.UJ ε → ℝ) := by
  have hf : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact measurable_const.mul (Real.measurable_log.comp (measurable_detOn_comp _ hf _))

/- English proof (translation)
Establish `hi : m⁻¹ ∈ flagM ε (W A)` using `(GlobalTheory.FlagLeviGroup.leviSub ε (W A)).inv_mem hm`. Establish `h` using `GlobalTheory.RealInd.detOn_mul (keeps_of_mem hm) (keeps_of_mem hi)`. Establish `e : uMat m * uMat m⁻¹ = 1` using `by simp [uMat]`. Rewrite `h` using `[e, GlobalTheory.RealInd.detOn_one]`. Introduce `h0`.

Rewrite `h` using `[h0, zero_mul]`. Conclude with `one_ne_zero h`.
-/
theorem detOn_ne_zero {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) : detOn (uMat m) (Vm A) ≠ 0 := by
  have hi : m⁻¹ ∈ flagM ε (W A) := (GlobalTheory.FlagLeviGroup.leviSub ε (W A)).inv_mem hm
  have h := GlobalTheory.RealInd.detOn_mul (keeps_of_mem hm) (keeps_of_mem hi)
  have e : uMat m * uMat m⁻¹ = 1 := by simp [uMat]
  rw [e, GlobalTheory.RealInd.detOn_one] at h
  intro h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

/- English proof (translation)
Take `⟨hj, hW, -⟩` from `flagFacts n ε A hG`. Establish `hj0 : (rk A : ℝ) ≠ 0`. Establish `: 1 ≤ (rk A : ℝ)` using `by exact_mod_cast hj`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd : detOn (uMat u) (Vm A) = 1` using `GlobalTheory.RealInd.detOn_flagN hW hu 1`.

Establish `hfix : ∀ y ∈ Vm A, uMat u *ᵥ y ∈ Vm A` using `fun y hy => by`. Establish `h0 : uMat u *ᵥ y - y ∈ (⊥ : Submodule ℂ (Fin n → ℂ))` using `hu.1 0 y hy`. Rewrite using `[sub_eq_zero.1 h0]`. Conclude with `hy`. Establish `hk : ∀ y ∈ Vm A, (uMat m * eT A t) *ᵥ y ∈ Vm A` using `fun y hy => by`.

Rewrite using `[← mulVec_mulVec]`. Conclude with `keeps_of_mem hm _ (eT_keeps hG.2.2.1 t y hy)`. Establish `e : detOn (uMat (u * m * aLine hG t)) (Vm A) = detOn (uMat m) (Vm A) * Real.exp (-((rk A : ℝ) * t))`. Express the relevant statement in the definitionally equal form `detOn (uMat u * uMat m * eT A t) (Vm A) = _`. Rewrite using `[mul_assoc, GlobalTheory.RealInd.detOn_mul hfix hk, hd, one_mul, GlobalTheory.RealInd.detOn_mul (keeps_of_mem hm) (eT_keeps hG.2.2.1 t), detOn_eT hG.2.2.1]`.

Unfold `tau`. Rewrite using `[e, Real.log_mul (detOn_ne_zero hm) (Real.exp_pos _).ne', Real.log_exp]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tau_line (hG : IsGrad ε A) {u m : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε (W A)) (hm : m ∈ flagM ε (W A)) (t : ℝ) :
    tau A (u * m * aLine hG t) = tau A m + t := by
  obtain ⟨hj, hW, -⟩ := flagFacts n ε A hG
  have hj0 : (rk A : ℝ) ≠ 0 := by
    have : 1 ≤ (rk A : ℝ) := by exact_mod_cast hj
    linarith
  have hd : detOn (uMat u) (Vm A) = 1 := GlobalTheory.RealInd.detOn_flagN hW hu 1
  have hfix : ∀ y ∈ Vm A, uMat u *ᵥ y ∈ Vm A := fun y hy => by
    have h0 : uMat u *ᵥ y - y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hu.1 0 y hy
    rw [sub_eq_zero.1 h0]
    exact hy
  have hk : ∀ y ∈ Vm A, (uMat m * eT A t) *ᵥ y ∈ Vm A := fun y hy => by
    rw [← mulVec_mulVec]
    exact keeps_of_mem hm _ (eT_keeps hG.2.2.1 t y hy)
  have e : detOn (uMat (u * m * aLine hG t)) (Vm A) = detOn (uMat m) (Vm A) * Real.exp (-((rk A : ℝ) * t)) := by
    change detOn (uMat u * uMat m * eT A t) (Vm A) = _
    rw [mul_assoc, GlobalTheory.RealInd.detOn_mul hfix hk, hd, one_mul,
      GlobalTheory.RealInd.detOn_mul (keeps_of_mem hm) (eT_keeps hG.2.2.1 t), detOn_eT hG.2.2.1]
  unfold tau
  rw [e, Real.log_mul (detOn_ne_zero hm) (Real.exp_pos _).ne', Real.log_exp]
  field_simp
  ring

/- English proof (translation)
Introduce `n ε A hG`. Conclude with `⟨aLine hG, tau A, continuous_aLine hG, measurable_tau, fun t => rfl, aLine_add hG, aLine_mem hG, fun t m hm => aLine_comm hG t hm, fun m hm t => modA_line hG hm t, fun u hu m hm t => tau_line hG hu hm t⟩`.
-/
theorem lineFacts : LineFacts := by
  intro n ε A hG
  exact ⟨aLine hG, tau A, continuous_aLine hG, measurable_tau, fun t => rfl, aLine_add hG, aLine_mem hG,
    fun t m hm => aLine_comm hG t hm, fun m hm t => modA_line hG hm t, fun u hu m hm t => tau_line hG hu hm t⟩

end GlobalTheory.CompanionTheory.GradLine

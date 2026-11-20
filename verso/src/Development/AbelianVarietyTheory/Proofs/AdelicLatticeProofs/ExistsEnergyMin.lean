import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EntriesBoundedOfConjSpanningBoundedStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsClosedIsHermitianLogOfPosDefStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixEntriesBoundedOfHermitianLogTraceSqLeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsHermitianLogOfPosDefGramStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EnergyMin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Take `⟨U, d, -, hH, -⟩` from `h`. Establish `hh : Hᴴ = H`. Rewrite using `[hH]`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc]`. Use `congr 3`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `h1` using `(Matrix.posSemidef_conjTranspose_mul_self H).trace_nonneg`. Rewrite `h1` using `[hh]`. Conclude with `(Complex.le_def.mp h1).1`.
-/
theorem energy_nonneg {H A : Matrix ι ι ℂ} (h : IsLog H A) : 0 ≤ (Matrix.trace (H * H)).re := by
  obtain ⟨U, d, -, hH, -⟩ := h
  have hh : Hᴴ = H := by
    rw [hH]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    funext i
    simp
  have h1 := (Matrix.posSemidef_conjTranspose_mul_self H).trace_nonneg
  rw [hh] at h1
  exact (Complex.le_def.mp h1).1

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Establish `h : IsCompact (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Establish `e : {x : ι → ι → ℂ | ∀ i j, ‖x i j‖ ≤ C} = Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C`. Use extensionality with `x`. Simplify using `[Set.mem_pi]`. Rewrite `h` using `[← e]`.

Conclude with `h`.
-/
theorem isCompact_box (C : ℝ) : IsCompact {x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C} := by
  have h : IsCompact (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {x : ι → ι → ℂ | ∀ i j, ‖x i j‖ ≤ C} =
      Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C := by
    ext x
    simp [Set.mem_pi]
  rw [← e] at h
  exact h

/- English proof (translation)
Break down `isEmpty_or_nonempty ι with hι | hι` into its components or cases. Conclude with `⟨P, Matrix.det_isEmpty, fun _ => rfl⟩`. Take `⟨c, hc⟩` from `IsAlgClosed.exists_pow_nat_eq P.det (Fintype.card_pos (α := ι))`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hc` using `[zero_pow Fintype.card_ne_zero]`. Conclude with `hP.ne_zero hc.symm`. Use `⟨c⁻¹ • P, ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_smul, ← hc, ← mul_pow, inv_mul_cancel₀ hc0, one_pow]`. Establish `: (c⁻¹ • P)⁻¹ = c • P⁻¹`.

Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul, Matrix.mul_nonsing_inv _ hP]`. Rewrite using `[this, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]`.
-/
theorem exists_det_one (P : Matrix ι ι ℂ) (hP : IsUnit P.det) :
    ∃ Q : Matrix ι ι ℂ, Q.det = 1 ∧ ∀ x : Matrix ι ι ℂ, Q * x * Q⁻¹ = P * x * P⁻¹ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨P, Matrix.det_isEmpty, fun _ => rfl⟩
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq P.det (Fintype.card_pos (α := ι))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow Fintype.card_ne_zero] at hc
    exact hP.ne_zero hc.symm
  refine ⟨c⁻¹ • P, ?_, fun x => ?_⟩
  · rw [Matrix.det_smul, ← hc, ← mul_pow, inv_mul_cancel₀ hc0, one_pow]
  · have : (c⁻¹ • P)⁻¹ = c • P⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.mul_nonsing_inv _ hP]
    rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/- English proof (translation)
Rewrite using `[Matrix.inv_def, hP]`. Simplify using the standard rewrite rules.
-/
theorem inv_eq_adj {P : Matrix ι ι ℂ} (hP : P.det = 1) : P⁻¹ = P.adjugate := by
  rw [Matrix.inv_def, hP]
  simp

end GlobalTheory.ClassFin.EnergyMin

open GlobalTheory.ClassFin.EnergyMin in

/- English proof (translation)
Introduce `ι _ _ σ _ g hg hspan`. Use `choose H₀ hH₀ using fun s => GlobalTheory.T.exists_isHermitianLogOfPosDef_gram ι (g s) (hg s)`. Set `En : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) → ℝ` to `fun p => ∑ s, (Matrix.trace (p.2 s * p.2 s)).re`. Establish `hEn : Continuous En`. Use `continuous_finset_sum _ fun s _ => Complex.continuous_re.comp ?_` and prove the remaining obligations.

Establish `h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s` using `(continuous_apply s).comp continuous_snd`. Conclude with `(h.matrix_mul h).matrix_trace`. Set `E₀ : ℝ` to `En (1, H₀)`. Set `Z : Set (Matrix ι ι ℂ × (σ → Matrix ι ι ℂ))` to `{p | p.1.det = 1 ∧ (∀ s, IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))) ∧ En p ≤ E₀}`. Establish `hZc : IsClosed Z`.

Use `IsClosed.inter (isClosed_eq continuous_fst.matrix_det continuous_const) (IsClosed.inter ?_ (isClosed_le hEn continuous_const))` and prove the remaining obligations. Establish `: IsClosed (⋂ s, {p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) | IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))})`. Use `isClosed_iInter fun s => ?_` and prove the remaining obligations. Establish `h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s` using `(continuous_apply s).comp continuous_snd`. Establish `h2 : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.1 * g s * p.1.adjugate` using `(continuous_fst.matrix_mul continuous_const).matrix_mul continuous_fst.matrix_adjugate`.

Conclude with `(GlobalTheory.T.isClosed_isHermitianLogOfPosDef ι).preimage (h.prodMk (h2.matrix_conjTranspose.matrix_mul h2))`. Rewrite `this` using `[← Set.setOf_forall]`. Conclude with `this`. Take `⟨C, hC⟩` from `GlobalTheory.T.matrix_entries_bounded_of_hermitian_log_trace_sq_le ι E₀`. Take `⟨C', hC'⟩` from `GlobalTheory.T.entries_bounded_of_conj_spanning_bounded' ι σ g hspan C`.

Establish `hK : IsCompact ({x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C'} ×ˢ (Set.pi Set.univ fun _ : σ => {x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C}))` using `(isCompact_box C').prod (isCompact_univ_pi fun _ => isCompact_box C)`. Establish `hZ : IsCompact Z`. Use `hK.of_isClosed_subset hZc ?_` and prove the remaining obligations. Introduce and unpack `⟨P, H⟩ ⟨hd, hl, hE⟩`. Establish `hb : ∀ s i j, ‖(P * g s * P.adjugate) i j‖ ≤ C ∧ ‖H s i j‖ ≤ C`.

Introduce `s`. Use `hC _ _ (hl s) (le_trans ?_ hE)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun s => (Matrix.trace (H s * H s)).re) (fun t _ => energy_nonneg (hl t)) (Finset.mem_univ s)`. Use `⟨hC' P hd fun s i j => ?_, fun s _ i j => (hb s i j).2⟩` and prove the remaining obligations. Rewrite using `[inv_eq_adj hd]`.

Conclude with `(hb s i j).1`. Establish `h0 : ((1, H₀) : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ)) ∈ Z`. Use `⟨Matrix.det_one, fun s => ?_, le_rfl⟩` and prove the remaining obligations. Simplify using `using hH₀ s`. Take `⟨⟨P, H⟩, ⟨hd, hl, hE⟩, hmin⟩` from `hZ.exists_isMinOn ⟨_, h0⟩ hEn.continuousOn`.

Establish `hd' : P.det = 1` using `hd`. Use `⟨P, H, by rw [hd']; exact isUnit_one, fun s => by rw [inv_eq_adj hd']; exact hl s, ?_⟩` and prove the remaining obligations. Introduce `P' H' hP' hl'`. Take `⟨Q, hQ, hQx⟩` from `exists_det_one P' hP'`. Express the relevant statement in the definitionally equal form `En (P, H) ≤ En (Q, H')`.

Distinguish the cases in `hle : En (Q, H') ≤ E₀`. Use `hmin (a := (Q, H')) ⟨hQ, fun s => ?_, hle⟩` and prove the remaining obligations. Use `hl' s` as an intermediate fact. Rewrite `this` using `[← hQx, inv_eq_adj hQ]`. Conclude with `this`.

Conclude with `hE.trans (not_le.mp hle).le`.
-/
theorem GlobalTheory.ClassFin.exists_energy_min : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), (∀ s, IsUnit (g s).det) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ (P : Matrix ι ι ℂ) (H : σ → Matrix ι ι ℂ), IsUnit P.det ∧ (∀ s, IsLog (H s) ((P * g s * P⁻¹)ᴴ * (P * g s * P⁻¹))) ∧ ∀ (P' : Matrix ι ι ℂ) (H' : σ → Matrix ι ι ℂ), IsUnit P'.det → (∀ s, IsLog (H' s) ((P' * g s * P'⁻¹)ᴴ * (P' * g s * P'⁻¹))) → ∑ s, (Matrix.trace (H s * H s)).re ≤ ∑ s, (Matrix.trace (H' s * H' s)).re := by
  intro ι _ _ σ _ g hg hspan
  choose H₀ hH₀ using fun s => GlobalTheory.T.exists_isHermitianLogOfPosDef_gram ι (g s) (hg s)
  let En : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) → ℝ := fun p => ∑ s, (Matrix.trace (p.2 s * p.2 s)).re
  have hEn : Continuous En := by
    refine continuous_finset_sum _ fun s _ => Complex.continuous_re.comp ?_
    have h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s :=
      (continuous_apply s).comp continuous_snd
    exact (h.matrix_mul h).matrix_trace
  let E₀ : ℝ := En (1, H₀)
  let Z : Set (Matrix ι ι ℂ × (σ → Matrix ι ι ℂ)) := {p | p.1.det = 1 ∧
    (∀ s, IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))) ∧ En p ≤ E₀}
  have hZc : IsClosed Z := by
    refine IsClosed.inter (isClosed_eq continuous_fst.matrix_det continuous_const)
      (IsClosed.inter ?_ (isClosed_le hEn continuous_const))
    have : IsClosed (⋂ s, {p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) |
        IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))}) := by
      refine isClosed_iInter fun s => ?_
      have h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s :=
        (continuous_apply s).comp continuous_snd
      have h2 : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.1 * g s * p.1.adjugate :=
        (continuous_fst.matrix_mul continuous_const).matrix_mul continuous_fst.matrix_adjugate
      exact (GlobalTheory.T.isClosed_isHermitianLogOfPosDef ι).preimage (h.prodMk (h2.matrix_conjTranspose.matrix_mul h2))
    rw [← Set.setOf_forall] at this
    exact this
  obtain ⟨C, hC⟩ := GlobalTheory.T.matrix_entries_bounded_of_hermitian_log_trace_sq_le ι E₀
  obtain ⟨C', hC'⟩ := GlobalTheory.T.entries_bounded_of_conj_spanning_bounded' ι σ g hspan C
  have hK : IsCompact ({x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C'} ×ˢ
      (Set.pi Set.univ fun _ : σ => {x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C})) :=
    (isCompact_box C').prod (isCompact_univ_pi fun _ => isCompact_box C)
  have hZ : IsCompact Z := by
    refine hK.of_isClosed_subset hZc ?_
    rintro ⟨P, H⟩ ⟨hd, hl, hE⟩
    have hb : ∀ s i j, ‖(P * g s * P.adjugate) i j‖ ≤ C ∧ ‖H s i j‖ ≤ C := by
      intro s
      refine hC _ _ (hl s) (le_trans ?_ hE)
      exact Finset.single_le_sum (f := fun s => (Matrix.trace (H s * H s)).re)
        (fun t _ => energy_nonneg (hl t)) (Finset.mem_univ s)
    refine ⟨hC' P hd fun s i j => ?_, fun s _ i j => (hb s i j).2⟩
    rw [inv_eq_adj hd]
    exact (hb s i j).1
  have h0 : ((1, H₀) : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ)) ∈ Z := by
    refine ⟨Matrix.det_one, fun s => ?_, le_rfl⟩
    simpa using hH₀ s
  obtain ⟨⟨P, H⟩, ⟨hd, hl, hE⟩, hmin⟩ := hZ.exists_isMinOn ⟨_, h0⟩ hEn.continuousOn
  have hd' : P.det = 1 := hd
  refine ⟨P, H, by rw [hd']; exact isUnit_one, fun s => by rw [inv_eq_adj hd']; exact hl s, ?_⟩
  intro P' H' hP' hl'
  obtain ⟨Q, hQ, hQx⟩ := exists_det_one P' hP'
  change En (P, H) ≤ En (Q, H')
  by_cases hle : En (Q, H') ≤ E₀
  · refine hmin (a := (Q, H')) ⟨hQ, fun s => ?_, hle⟩
    have := hl' s
    rw [← hQx, inv_eq_adj hQ] at this
    exact this
  · exact hE.trans (not_le.mp hle).le

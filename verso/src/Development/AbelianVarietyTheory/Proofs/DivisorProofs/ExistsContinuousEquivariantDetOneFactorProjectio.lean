import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.Proj

variable {p q r : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Jpq_eq_diagonal, Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases i with i | i <;> simp`.
-/
theorem det_Jpq_ne (p q : ℕ) : (Formalism.UG.Jpq p q).det ≠ 0 := by
  rw [Jpq_eq_diagonal, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rcases i with i | i <;> simp

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (GlobalTheory.UpqExpChart.mat_unitary u)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Establish `hJ` using `det_Jpq_ne p q`. Apply `mul_left_cancel₀ hJ` to reduce the goal to its premises. Take the linear combination `h`.
-/
theorem star_det_mul_det (u : UpqT p q) : star (UpqT.mat u).det * (UpqT.mat u).det = 1 := by
  have h := congrArg Matrix.det (GlobalTheory.UpqExpChart.mat_unitary u)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ := det_Jpq_ne p q
  apply mul_left_cancel₀ hJ
  linear_combination h

/- English proof (translation)
Introduce `h`. Use `star_det_mul_det u` as an intermediate fact. Rewrite `this` using `[h, mul_zero]`. Conclude with `zero_ne_one this`.
-/
theorem det_mat_ne (u : UpqT p q) : (UpqT.mat u).det ≠ 0 := by
  intro h
  have := star_det_mul_det u
  rw [h, mul_zero] at this
  exact zero_ne_one this

/- English proof (translation)
Rewrite using `[Jpq_eq_diagonal, dg, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = a₀`. Substitute `h` using the available equality.

Simplify using `only [Pi.star_apply, Function.update_self]`. Take the linear combination `(Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i) * hz`. Simplify using `[Function.update_of_ne h]`.
-/
theorem dg_unitary (a₀ : Fin p ⊕ Fin q) (z : ℂ) (hz : star z * z = 1) :
    (dg a₀ z)ᴴ * Formalism.UG.Jpq p q * dg a₀ z = Formalism.UG.Jpq p q := by
  rw [Jpq_eq_diagonal, dg, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = a₀
  · subst h
    simp only [Pi.star_apply, Function.update_self]
    linear_combination (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i) * hz
  · simp [Function.update_of_ne h]

/- English proof (translation)
Rewrite using `[sMat, Matrix.det_mul, det_dg, mul_inv_cancel₀ (det_mat_ne u)]`.
-/
theorem det_sMat (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) : (sMat a₀ u).det = 1 := by
  rw [sMat, Matrix.det_mul, det_dg, mul_inv_cancel₀ (det_mat_ne u)]

/- English proof (translation)
Establish `hz : star (UpqT.mat u).det⁻¹ * (UpqT.mat u).det⁻¹ = 1`. Rewrite using `[star_inv₀, ← mul_inv, star_det_mul_det, inv_one]`. Establish `h1` using `GlobalTheory.UpqExpChart.mat_unitary u`. Establish `h2` using `dg_unitary a₀ _ hz`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [sMat, Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [h1, h2]`.
-/
theorem sMat_unitary (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) :
    (sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u = Formalism.UG.Jpq p q := by
  have hz : star (UpqT.mat u).det⁻¹ * (UpqT.mat u).det⁻¹ = 1 := by
    rw [star_inv₀, ← mul_inv, star_det_mul_det, inv_one]
  have h1 := GlobalTheory.UpqExpChart.mat_unitary u
  have h2 := dg_unitary a₀ _ hz
  calc _ = (dg a₀ (UpqT.mat u).det⁻¹)ᴴ * ((UpqT.mat u)ᴴ * Formalism.UG.Jpq p q * UpqT.mat u) *
        dg a₀ (UpqT.mat u).det⁻¹ := by
        simp only [sMat, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

/- English proof (translation)
Unfold `sMat dg`. Use `GlobalTheory.UpqExpChart.continuous_mat.matrix_mul (Continuous.matrix_diagonal ?_)` and prove the remaining obligations. Conclude with `continuous_const.update a₀ (GlobalTheory.UpqExpChart.continuous_mat.matrix_det.inv₀ det_mat_ne)`.
-/
theorem continuous_sMat (a₀ : Fin p ⊕ Fin q) : Continuous (sMat a₀ : UpqT p q → _) := by
  unfold sMat dg
  refine GlobalTheory.UpqExpChart.continuous_mat.matrix_mul (Continuous.matrix_diagonal ?_)
  exact continuous_const.update a₀
    (GlobalTheory.UpqExpChart.continuous_mat.matrix_det.inv₀ det_mat_ne)

/- English proof (translation)
Establish `h : UpqT.mat (u * v) = UpqT.mat u * UpqT.mat v` using `rfl`. Rewrite using `[sMat, sMat, h, Matrix.det_mul, hu, one_mul, Matrix.mul_assoc]`.
-/
theorem sMat_mul (a₀ : Fin p ⊕ Fin q) (u v : UpqT p q) (hu : (UpqT.mat u).det = 1) :
    sMat a₀ (u * v) = UpqT.mat u * sMat a₀ v := by
  have h : UpqT.mat (u * v) = UpqT.mat u * UpqT.mat v := rfl
  rw [sMat, sMat, h, Matrix.det_mul, hu, one_mul, Matrix.mul_assoc]

/- English proof (translation)
Establish `h1 : (B * S * A).submatrix e e = B.submatrix e id * S * A.submatrix id e`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`. Establish `h2 : A.submatrix id e * B.submatrix e id = 1`. Rewrite using `[Matrix.submatrix_mul_equiv, hAB]`.

Both sides reduce to the same expression. Rewrite using `[← Matrix.det_submatrix_equiv_self e, h1, Matrix.det_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]`.
-/
theorem det_conj {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin r) (A : Matrix ι (Fin r) ℂ)
    (B : Matrix (Fin r) ι ℂ) (hAB : A * B = 1) (S : Matrix ι ι ℂ) : (B * S * A).det = S.det := by
  have h1 : (B * S * A).submatrix e e = B.submatrix e id * S * A.submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  have h2 : A.submatrix id e * B.submatrix e id = 1 := by
    rw [Matrix.submatrix_mul_equiv, hAB]
    rfl
  rw [← Matrix.det_submatrix_equiv_self e, h1, Matrix.det_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

def gl (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (u : UpqT p q) : GL (Fin r) ℂ where
  val := B * sMat a₀ u * A
  inv := B * (sMat a₀ u).adjugate * A
  val_inv := by
    calc _ = B * (sMat a₀ u * (A * B) * (sMat a₀ u).adjugate) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.mul_adjugate, det_sMat, one_smul, Matrix.mul_one, hBA]
  inv_val := by
    calc _ = B * ((sMat a₀ u).adjugate * (A * B) * sMat a₀ u) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.adjugate_mul, det_sMat, one_smul, Matrix.mul_one, hBA]

section
variable (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gl_val (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = B * sMat a₀ u * A := rfl

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(continuous_const.matrix_mul (continuous_sMat a₀)).matrix_mul continuous_const`. Conclude with `(continuous_const.matrix_mul (continuous_sMat a₀).matrix_adjugate).matrix_mul continuous_const`.
-/
theorem continuous_gl : Continuous (gl a₀ A B hAB hBA) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_const.matrix_mul (continuous_sMat a₀)).matrix_mul continuous_const
  · exact (continuous_const.matrix_mul (continuous_sMat a₀).matrix_adjugate).matrix_mul continuous_const

/- English proof (translation)
Rewrite using `[gl_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.one_mul]`.
-/
theorem mul_gl (u : UpqT p q) :
    A * (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = sMat a₀ u * A := by
  rw [gl_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.one_mul]

/- English proof (translation)
Establish `hm` using `mul_gl a₀ A B hAB hBA u`. Generalize the expression as in `(gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = g at hm ⊢`. Establish `h : gᴴ * (-Hᵀ) * g = -Hᵀ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hH]`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Aᴴ * ((sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u) * A := by`. Rewrite using `[hm]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [sMat_unitary, hH]`.

Rewrite `h` using `[Matrix.mul_neg, Matrix.neg_mul, neg_inj]`. Establish `h'` using `congrArg Matrix.transpose h`. Rewrite `h'` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]`. Conclude with `h'`.
-/
theorem gl_keeps (H : Matrix (Fin r) (Fin r) ℂ) (hH : Aᴴ * Formalism.UG.Jpq p q * A = -Hᵀ) (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ)ᵀ * H *
      (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = H := by
  have hm := mul_gl a₀ A B hAB hBA u
  generalize (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = g at hm ⊢
  have h : gᴴ * (-Hᵀ) * g = -Hᵀ := by
    calc _ = (A * g)ᴴ * Formalism.UG.Jpq p q * (A * g) := by
          rw [← hH]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Aᴴ * ((sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u) * A := by
          rw [hm]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [sMat_unitary, hH]
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h'
  exact h'

end

/- English proof (translation)
Introduce `E _ _ _ r κ _ p q Ψ G x σ A e a₀ hI`. Set `B : ∀ ρ, Matrix (Fin r) (Fin (p ρ) ⊕ Fin (q ρ)) ℂ` to `fun ρ => mat x (σ ρ) * (permM (e ρ))ᵀ`. Establish `hAB : ∀ ρ, A ρ * B ρ = 1` using `fun ρ => by`. Simplify using `only [B]`. Rewrite using `[← Matrix.mul_assoc, (hI ρ).2, permM_mul_transpose]`.

Establish `hBA : ∀ ρ, B ρ * A ρ = 1` using `fun ρ => (Matrix.mul_eq_one_comm_of_equiv (e ρ)).1 (hAB ρ)`. Set `F : (∀ ρ, UpqT (p ρ) (q ρ)) → κ → GL (Fin r) ℂ` to `fun b ρ => gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ)`. Establish `hF : ∀ b ρ, F b (σ.symm (σ ρ)) = gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ)` using `fun b ρ => by`. Rewrite using `[Equiv.symm_apply_apply]`. Establish `hmem : ∀ b, (fun τ => F b (σ.symm τ)) ∈ realSU Ψ G` using `fun b => by`.

Rewrite using `[DensOne.mem_realSU_iff]`. Introduce `τ`. Take `⟨ρ, rfl⟩` from `σ.surjective τ`. Simplify using `only [hF]`. Conclude with `⟨gl_keeps _ _ _ _ _ _ (hI ρ).1 _, by rw [gl_val, det_conj (e ρ) _ _ (hAB ρ), det_sMat]⟩`.

Use `⟨fun b => ⟨_, hmem b⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Continuous.subtype_mk (continuous_pi fun τ => ?_) _` and prove the remaining obligations. Conclude with `(continuous_gl _ _ _ _ _).comp (continuous_apply _)`. Introduce `b ρ`. Simplify using `only [hF]`.

Conclude with `mul_gl _ _ _ _ _ _`. Introduce `s b₀ hs b`. Use `Subtype.ext (funext fun τ => ?_)` and prove the remaining obligations. Take `⟨ρ, rfl⟩` from `σ.surjective τ`. Apply `Units.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `((F (b₀ * b) (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (s.1 (σ ρ) : GL (Fin r) ℂ) * ((F b (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)`. Establish `h1 : ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = B ρ * UpqT.mat (b₀ ρ) * A ρ`. Rewrite using `[Matrix.mul_assoc, hs ρ, ← Matrix.mul_assoc, hBA, Matrix.one_mul]`. Establish `h2 : (UpqT.mat (b₀ ρ)).det = 1`. Rewrite using `[← det_conj (e ρ) _ _ (hAB ρ), ← h1]`.

Conclude with `(((DensOne.mem_realSU_iff Ψ G _).1 s.2) (σ ρ)).2`. Rewrite using `[hF, hF, gl_val, gl_val, h1, Pi.mul_apply, sMat_mul _ _ _ h2]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hAB]`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]`.

Use `_ = _ := by simp only [Matrix.mul_assoc]`.
-/
theorem exists_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)), IsIdent p q Ψ G x σ A e → ∃ π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G, Continuous π ∧ IsProj p q Ψ G σ A a₀ π ∧ (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ hI
  let B : ∀ ρ, Matrix (Fin r) (Fin (p ρ) ⊕ Fin (q ρ)) ℂ := fun ρ => mat x (σ ρ) * (permM (e ρ))ᵀ
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ => by
    simp only [B]
    rw [← Matrix.mul_assoc, (hI ρ).2, permM_mul_transpose]
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => (Matrix.mul_eq_one_comm_of_equiv (e ρ)).1 (hAB ρ)
  let F : (∀ ρ, UpqT (p ρ) (q ρ)) → κ → GL (Fin r) ℂ :=
    fun b ρ => gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ)
  have hF : ∀ b ρ, F b (σ.symm (σ ρ)) = gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ) := fun b ρ => by
    rw [Equiv.symm_apply_apply]
  have hmem : ∀ b, (fun τ => F b (σ.symm τ)) ∈ realSU Ψ G := fun b => by
    rw [DensOne.mem_realSU_iff]
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    simp only [hF]
    exact ⟨gl_keeps _ _ _ _ _ _ (hI ρ).1 _, by rw [gl_val, det_conj (e ρ) _ _ (hAB ρ), det_sMat]⟩
  refine ⟨fun b => ⟨_, hmem b⟩, ?_, ?_, ?_⟩
  · refine Continuous.subtype_mk (continuous_pi fun τ => ?_) _
    exact (continuous_gl _ _ _ _ _).comp (continuous_apply _)
  · intro b ρ
    simp only [hF]
    exact mul_gl _ _ _ _ _ _
  · intro s b₀ hs b
    refine Subtype.ext (funext fun τ => ?_)
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    apply Units.ext
    change ((F (b₀ * b) (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (s.1 (σ ρ) : GL (Fin r) ℂ) * ((F b (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
    have h1 : ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = B ρ * UpqT.mat (b₀ ρ) * A ρ := by
      rw [Matrix.mul_assoc, hs ρ, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
    have h2 : (UpqT.mat (b₀ ρ)).det = 1 := by
      rw [← det_conj (e ρ) _ _ (hAB ρ), ← h1]
      exact (((DensOne.mem_realSU_iff Ψ G _).1 s.2) (σ ρ)).2
    rw [hF, hF, gl_val, gl_val, h1, Pi.mul_apply, sMat_mul _ _ _ h2]
    calc _ = B ρ * UpqT.mat (b₀ ρ) * (A ρ * B ρ) * sMat (a₀ ρ) (b ρ) * A ρ := by
          rw [hAB]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.CovTop.VolUp.Proj

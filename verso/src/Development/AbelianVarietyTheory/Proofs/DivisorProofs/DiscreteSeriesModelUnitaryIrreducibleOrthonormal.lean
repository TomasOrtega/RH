import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.ModelRep

section Conj

variable {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Establish `hg' : gᴴ * G * g = G` using `hg`. Use `show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by`. Rewrite using `[hG, hg', ← hG]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [h1]; simp`.
-/
theorem conj_mem (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : P * g * P⁻¹ ∈ UJset ε := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have hg' : gᴴ * G * g = G := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [hG, hg', ← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Establish `hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε` using `hg`. Use `show (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hG]`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = G := by`. Rewrite using `[h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hg', hG]`.
-/
theorem conj_mem_inv (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH G := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  show (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G
  calc (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * ((P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹)) * g) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by
        rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hg', hG]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Establish `h2 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Take `⟨⟨ha, hb⟩, hc, hd⟩` from `hσ`. Use `⟨⟨?_, ?_⟩, fun g hg v => hc _ (conj_mem hP hG hg) v, fun v => ?_⟩` and prove the remaining obligations. Simplify `ha` using `only [Matrix.mul_one, h1]`.

Introduce `a ha' b hb'`. Establish `e : P * (a * b) * P⁻¹ = (P * a * P⁻¹) * (P * b * P⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Use `show σ (P * (a * b) * P⁻¹) = _`. Rewrite using `[e]`.

Conclude with `hb _ (conj_mem hP hG ha') _ (conj_mem hP hG hb')`. Establish `hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => P * g * P⁻¹` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Conclude with `(hd v).comp hc.continuousOn fun g hg => conj_mem hP hG hg`.
-/
theorem isURepOn_conj (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ) :
    IsURepOn (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  obtain ⟨⟨ha, hb⟩, hc, hd⟩ := hσ
  refine ⟨⟨?_, ?_⟩, fun g hg v => hc _ (conj_mem hP hG hg) v, fun v => ?_⟩
  · simpa only [Matrix.mul_one, h1] using ha
  · intro a ha' b hb'
    have e : P * (a * b) * P⁻¹ = (P * a * P⁻¹) * (P * b * P⁻¹) := by
      calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by rw [h2]; simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = _ := by simp only [Matrix.mul_assoc]
    show σ (P * (a * b) * P⁻¹) = _
    rw [e]
    exact hb _ (conj_mem hP hG ha') _ (conj_mem hP hG hb')
  · have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact (hd v).comp hc.continuousOn fun g hg => conj_mem hP hG hg

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Introduce `S hS h`. Use `hσ S hS fun g hg v hv => ?_` and prove the remaining obligations. Use `h _ (conj_mem_inv hP hG hg) v hv` as an intermediate fact. Establish `e : P * (P⁻¹ * g * P) * P⁻¹ = g`.

Combine the equalities or inequalities in the displayed calculation. Simplify `this` using `only [e]`.
-/
theorem isIrredOn_conj (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsIrredOn (UJset ε) σ) :
    IsIrredOn (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  intro S hS h
  refine hσ S hS fun g hg v hv => ?_
  have := h _ (conj_mem_inv hP hG hg) v hv
  have e : P * (P⁻¹ * g * P) * P⁻¹ = g := by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h1]; simp
  simpa only [e] using this

/- English proof (translation)
Introduce `a b h`. Establish `h'` using `congrArg Fin.val h`. Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Apply `Fin.ext` to reduce the goal to its premises.

Unfold `arr at h'`. Apply the tactic sequence `split_ifs at h' <;> simp only at h' <;> omega`.
-/
theorem arr_injective {q : ℕ} (hq : q ≤ n) : Function.Injective (arr q : Fin n → Fin n) := by
  intro a b h
  have h' := congrArg Fin.val h
  have := a.2
  have := b.2
  apply Fin.ext
  unfold arr at h'
  split_ifs at h' <;> simp only at h' <;> omega

def arrEquiv {q : ℕ} (hq : q ≤ n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (arr q) (Finite.injective_iff_bijective.1 (arr_injective hq))

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Establish `h3 : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hG]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = _ := by rw [h1]; simp`. Rewrite using `[← h3]`. Both sides reduce to the same expression.
-/
theorem orth_sub (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (f : Fin n → Fin n) :
    ((P⁻¹).submatrix id f)ᴴ * G * (P⁻¹).submatrix id f = (Formalism.REAL.Jm ε).submatrix f f := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h3 : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  rw [← h3]
  rfl

/- English proof (translation)
Establish `h2 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)`. Establish `h3 : ((P⁻¹).submatrix id e)⁻¹ = P.submatrix e id`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[Matrix.submatrix_mul_equiv, h2]`. Both sides reduce to the same expression.

Establish `h4 : (Matrix.single a c 1 : Matrix (Fin n) (Fin n) ℂ) = (Matrix.single (e a) (e c) 1).submatrix e e`. Use extensionality with `i j`. Simplify using `[Matrix.single_apply]`. Rewrite using `[h3, h4, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]`. Both sides reduce to the same expression.
-/
theorem conj_single (hP : IsUnit P) (e : Fin n ≃ Fin n) (a c : Fin n) :
    (P⁻¹).submatrix id e * Matrix.single a c 1 * ((P⁻¹).submatrix id e)⁻¹ =
      P⁻¹ * Matrix.single (e a) (e c) 1 * P := by
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h3 : ((P⁻¹).submatrix id e)⁻¹ = P.submatrix e id := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.submatrix_mul_equiv, h2]
    rfl
  have h4 : (Matrix.single a c 1 : Matrix (Fin n) (Fin n) ℂ) = (Matrix.single (e a) (e c) 1).submatrix e e := by
    ext i j
    simp [Matrix.single_apply]
  rw [h3, h4, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

end Conj

/- English proof (translation)
Introduce `D V S M τ`. Take `⟨h1, -, h3, h4, -⟩` from `M.ds τ`. Use `⟨h1, isURepOn_conj (M.fr_unit τ) (M.fr_gram τ) h3, isIrredOn_conj (M.fr_unit τ) (M.fr_gram τ) h4, fun hs => ⟨⟨nNeg_le _, ?_⟩, fun a c => ?_⟩⟩` and prove the remaining obligations. Take `⟨-, p, hp, h⟩` from `hs τ`. Use `orth_sub (M.fr_unit τ) (M.fr_gram τ) (arr (nNeg (M.ε τ)))` as an intermediate fact.

Use `this.trans ?_` and prove the remaining obligations. Establish `hinj` using `arr_injective (nNeg_le (M.ε τ))`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.submatrix_diagonal _ _ hinj]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Use `a.2` as an intermediate fact. Simplify using `only [Function.comp, h, nNeg_shape hp h, ReciprocityTheory.ChartRestriction.G.FD.sgn, arr, decide_eq_true_eq]`. Apply the tactic sequence `split_ifs <;> first | (simp; done) | (exfalso; simp only at *; omega)`. Conclude with `conj_single (M.fr_unit τ) (arrEquiv (nNeg_le (M.ε τ))) a c`.
-/
theorem model_rep : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), CompleteSpace (M.H τ) ∧ IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ (HolShape M → OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) ∧ ∀ a c, x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹ = (M.fr τ)⁻¹ * Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1 * M.fr τ) := by
  intro D V S M τ
  obtain ⟨h1, -, h3, h4, -⟩ := M.ds τ
  refine ⟨h1, isURepOn_conj (M.fr_unit τ) (M.fr_gram τ) h3, isIrredOn_conj (M.fr_unit τ) (M.fr_gram τ) h4, fun hs => ⟨⟨nNeg_le _, ?_⟩, fun a c => ?_⟩⟩
  · obtain ⟨-, p, hp, h⟩ := hs τ
    have := orth_sub (M.fr_unit τ) (M.fr_gram τ) (arr (nNeg (M.ε τ)))
    refine this.trans ?_
    have hinj := arr_injective (nNeg_le (M.ε τ))
    unfold Formalism.REAL.Jm
    rw [Matrix.submatrix_diagonal _ _ hinj]
    congr 1
    funext a
    have := a.2
    simp only [Function.comp, h, nNeg_shape hp h, ReciprocityTheory.ChartRestriction.G.FD.sgn, arr, decide_eq_true_eq]
    split_ifs <;> first | (simp; done) | (exfalso; simp only at *; omega)
  · exact conj_single (M.fr_unit τ) (arrEquiv (nNeg_le (M.ε τ))) a c

end GlobalTheory.HolDict.ModelRep

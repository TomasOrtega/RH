import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSumUnitarySubstitutionsEqRowLieStatement

noncomputable section

open Matrix

namespace GlobalTheory.DefLift.ColComb

variable {ι : Type} {m n : ℕ}

def sw (ι : Type) (m n : ℕ) : ι × Fin m × Fin n → ι × Fin n × Fin m := fun v => (v.1, v.2.2, v.2.1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sw_sw (v : ι × Fin m × Fin n) : sw ι n m (sw ι m n v) = v := rfl

/- English proof (translation)
The claim follows from `Function.LeftInverse.injective sw_sw`.
-/
theorem sw_injective : Function.Injective (sw ι m n) := Function.LeftInverse.injective sw_sw

/- English proof (translation)
Establish `: (MvPolynomial.rename (sw ι n m)).comp (subst a b) = (subst (fun ρ => (b ρ)ᵀ) (fun ρ => (a ρ)ᵀ)).comp (MvPolynomial.rename (sw ι n m))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨ρ, c, i⟩`. Simplify using `only [subst, AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.rename_X, map_sum, map_smul, sw, Matrix.transpose_apply]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [mul_comm]`. Conclude with `AlgHom.congr_fun this Q`.
-/
theorem rename_subst (a : ι → Matrix (Fin m) (Fin m) ℂ) (b : ι → Matrix (Fin n) (Fin n) ℂ) (Q : Pol ι n m) :
    MvPolynomial.rename (sw ι n m) (subst a b Q) =
      subst (fun ρ => (b ρ)ᵀ) (fun ρ => (a ρ)ᵀ) (MvPolynomial.rename (sw ι n m) Q) := by
  have : (MvPolynomial.rename (sw ι n m)).comp (subst a b) =
      (subst (fun ρ => (b ρ)ᵀ) (fun ρ => (a ρ)ᵀ)).comp (MvPolynomial.rename (sw ι n m)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨ρ, c, i⟩
    simp only [subst, AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.rename_X, map_sum, map_smul, sw,
      Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  exact AlgHom.congr_fun this Q

def cj (u : Matrix.unitaryGroup (Fin n) ℂ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨star (u : Matrix (Fin n) (Fin n) ℂ)ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff', star_star]
    have h : star (u : Matrix (Fin n) (Fin n) ℂ) * u = 1 := Matrix.mem_unitaryGroup_iff'.1 u.2
    have e : star (u : Matrix (Fin n) (Fin n) ℂ)ᵀ = (star (u : Matrix (Fin n) (Fin n) ℂ))ᵀ := rfl
    rw [e, ← Matrix.transpose_mul, h, Matrix.transpose_one]⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[cj]`.
-/
theorem cj_cj (u : Matrix.unitaryGroup (Fin n) ℂ) : cj (cj u) = u := by
  apply Subtype.ext
  ext i j
  simp [cj]

/- English proof (translation)
Simplify using `only [rowSub, colSub, AlgHom.toLinearMap_apply, rename_subst]`. Use `congr 2`. Apply the tactic sequence `funext ρ split_ifs <;> simp [cj]`. Use function extensionality and compare the values at `ρ`. Simplify using the standard rewrite rules.
-/
theorem rename_rowSub (τ : ι) (u : Matrix.unitaryGroup (Fin n) ℂ) (Q : Pol ι n m) :
    MvPolynomial.rename (sw ι n m) (rowSub m τ u Q) = colSub m τ (cj u) (MvPolynomial.rename (sw ι n m) Q) := by
  simp only [rowSub, colSub, AlgHom.toLinearMap_apply, rename_subst]
  congr 2
  · funext ρ
    split_ifs <;> simp [cj]
  · funext ρ
    simp

/- English proof (translation)
Rewrite using `[rowLie_apply, colLie_apply, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, MvPolynomial.rename_X, ← MvPolynomial.pderiv_rename sw_injective]`. Both sides reduce to the same expression.
-/
theorem rename_rowLie (τ : ι) (k l : Fin n) (Q : Pol ι n m) :
    MvPolynomial.rename (sw ι n m) (rowLie m τ k l Q) = colLie m τ k l (MvPolynomial.rename (sw ι n m) Q) := by
  rw [rowLie_apply, colLie_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPolynomial.rename_X, ← MvPolynomial.pderiv_rename sw_injective]
  rfl

end GlobalTheory.DefLift.ColComb

namespace GlobalTheory.DefLift

open ColComb in

/- English proof (translation)
Introduce `ι _ m n d τ k l`. Take `⟨s, c, h⟩` from `GlobalTheory.T.exists_sum_unitarySubstitutions_eq_rowLie ι n m d τ k l`. Use `⟨s.map ⟨cj, Function.LeftInverse.injective cj_cj⟩, fun g => c (cj g), fun P hP => ?_⟩` and prove the remaining obligations. Establish `e : MvPolynomial.rename (sw ι n m) (MvPolynomial.rename (sw ι m n) P) = P`. Rewrite using `[MvPolynomial.rename_rename]`.

Conclude with `MvPolynomial.rename_id_apply P`. Establish `h1` using `congrArg (MvPolynomial.rename (sw ι n m)) (h (MvPolynomial.rename (sw ι m n) P) ((MvPolynomial.totalDegree_rename_le _ _).trans hP))`. Rewrite `h1` using `[rename_rowLie, map_sum, e]`. Rewrite using `[← h1, Finset.sum_map]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, rename_rowSub, e]`. Simplify using `[cj_cj]`.
-/
theorem colLie_eq_sum_colSub : ∀ (ι : Type) [Fintype ι] (m n d : ℕ) (τ : ι) (k l : Fin n),
    ∃ (s : Finset (Matrix.unitaryGroup (Fin n) ℂ)) (c : Matrix.unitaryGroup (Fin n) ℂ → ℂ),
      ∀ P : Pol ι m n, P.totalDegree ≤ d → ∑ g ∈ s, c g • colSub m τ g P = colLie m τ k l P := by
  intro ι _ m n d τ k l
  obtain ⟨s, c, h⟩ := GlobalTheory.T.exists_sum_unitarySubstitutions_eq_rowLie ι n m d τ k l
  refine ⟨s.map ⟨cj, Function.LeftInverse.injective cj_cj⟩, fun g => c (cj g), fun P hP => ?_⟩
  have e : MvPolynomial.rename (sw ι n m) (MvPolynomial.rename (sw ι m n) P) = P := by
    rw [MvPolynomial.rename_rename]
    exact MvPolynomial.rename_id_apply P
  have h1 := congrArg (MvPolynomial.rename (sw ι n m))
    (h (MvPolynomial.rename (sw ι m n) P) ((MvPolynomial.totalDegree_rename_le _ _).trans hP))
  rw [rename_rowLie, map_sum, e] at h1
  rw [← h1, Finset.sum_map]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_smul, rename_rowSub, e]
  simp [cj_cj]

end GlobalTheory.DefLift

end

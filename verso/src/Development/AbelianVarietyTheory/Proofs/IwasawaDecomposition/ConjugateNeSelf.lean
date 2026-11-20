import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace GlobalTheory.AlgWtHW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

/- English proof (translation)
Use `set g := Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀ with hgdef`. Establish `hg : g ∈ GA L n` using `by show g.val * conjT (conjAL L) g.val = 1`. Establish `e : conjT (conjAL L) g.val = (conjT (IsCMField.complexConj L : L →+* L) γ₀.val).map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)`. Use extensionality with `i j`. Simplify using `[conjT, g, conjAL, Algebra.TensorProduct.map_tmul]`.

Rewrite using `[e]`. Establish `h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1` using `h`. Use `show γ₀.val.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) * _ = 1`. Rewrite using `[← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `⟨⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.2 ⟨γ₀, h, rfl⟩⟩, rfl⟩`.
-/
theorem exists_gq (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) :
    ∃ γ : GQ L n, (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
  set g := Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀ with hgdef
  have hg : g ∈ GA L n := by
    show g.val * conjT (conjAL L) g.val = 1
    have e : conjT (conjAL L) g.val =
        (conjT (IsCMField.complexConj L : L →+* L) γ₀.val).map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
      ext i j
      simp [conjT, g, conjAL, Algebra.TensorProduct.map_tmul]
    rw [e]
    have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
    show γ₀.val.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) * _ = 1
    rw [← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.2 ⟨γ₀, h, rfl⟩⟩, rfl⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem conj_conj (φ : L →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  ext x; simp

/- English proof (translation)
Introduce `h` and use `IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)`.
-/
theorem conjugate_ne_self (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)

/- English proof (translation)
Introduce `σ`. Establish `h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1` using `h`. Establish `e : ratPt γ₀.val (ComplexEmbedding.conjugate σ) = (γ₀.val.map (IsCMField.complexConj L : L →+* L)).map σ`. Use extensionality with `i j`. Simplify using `[ratPt, IsCMField.complexEmbedding_complexConj]`.

Rewrite using `[e]`. Use `congrArg (fun M => M.map σ) h'` as an intermediate fact. Simplify `this` using `[ratPt, conjT, Matrix.map_mul, Matrix.transpose_map]`.
-/
theorem isUPt_ratPt (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) : IsUPt (ratPt γ₀.val) := by
  intro σ
  have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
  have e : ratPt γ₀.val (ComplexEmbedding.conjugate σ) = (γ₀.val.map (IsCMField.complexConj L : L →+* L)).map σ := by
    ext i j
    simp [ratPt, IsCMField.complexEmbedding_complexConj]
  rw [e]
  have := congrArg (fun M => M.map σ) h'
  simpa [ratPt, conjT, Matrix.map_mul, Matrix.transpose_map] using this

open Classical in

def tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ =>
  if σ = τ then B.val else if σ = ComplexEmbedding.conjugate τ then (B⁻¹).valᵀ else 1

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [evPt, upt, tauPt]`. Apply the tactic sequence `split_ifs <;> simp [Matrix.one_apply, *]`.
-/
theorem evPt_eq_upt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : evPt τ B = upt (tauPt τ B) := by
  funext p
  simp only [evPt, upt, tauPt]
  split_ifs <;> simp [Matrix.one_apply, *]

/- English proof (translation)
Introduce `σ`. Establish `hne` using `conjugate_ne_self τ`. Distinguish the cases in `h1 : σ = τ`. Substitute `h1` using the available equality. Simplify using `[tauPt, hne, Matrix.transpose_transpose]`.

Distinguish the cases in `h2 : σ = ComplexEmbedding.conjugate τ`. Substitute `h2` using the available equality. Simplify using `only [tauPt, if_neg h1, conj_conj, if_true]`. Rewrite using `[← Matrix.transpose_transpose (B.val), ← Matrix.transpose_mul, Matrix.transpose_transpose, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]`. Establish `h3 : ComplexEmbedding.conjugate σ ≠ τ` using `fun e => h2 (by rw [← e, conj_conj])`.

Establish `h4 : ComplexEmbedding.conjugate σ ≠ ComplexEmbedding.conjugate τ` using `fun e => h1 (by`. Simplify using `using congrArg ComplexEmbedding.conjugate e)`. Simplify using `[tauPt, h1, h2, h3, h4]`.
-/
theorem isUPt_tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : IsUPt (tauPt τ B) := by
  intro σ
  have hne := conjugate_ne_self τ
  by_cases h1 : σ = τ
  · subst h1
    simp [tauPt, hne, Matrix.transpose_transpose]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp only [tauPt, if_neg h1, conj_conj, if_true]
      rw [← Matrix.transpose_transpose (B.val), ← Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
    · have h3 : ComplexEmbedding.conjugate σ ≠ τ := fun e => h2 (by rw [← e, conj_conj])
      have h4 : ComplexEmbedding.conjugate σ ≠ ComplexEmbedding.conjugate τ := fun e => h1 (by
        simpa using congrArg ComplexEmbedding.conjugate e)
      simp [tauPt, h1, h2, h3, h4]

end GlobalTheory.AlgWtHW

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStep

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

/- English proof (translation)
Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem conj_conj (τ : L →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x; simp

/- English proof (translation)
Establish `h : ¬ ComplexEmbedding.IsReal τ`. Rewrite using `[← InfinitePlace.isComplex_mk_iff]`. Conclude with `IsTotallyComplex.isComplex _`. Rewrite `h` using `[ComplexEmbedding.isReal_iff]`. Then use the resulting hypothesis.
-/
theorem conj_ne (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := by
  have h : ¬ ComplexEmbedding.IsReal τ := by
    rw [← InfinitePlace.isComplex_mk_iff]; exact IsTotallyComplex.isComplex _
  rwa [ComplexEmbedding.isReal_iff] at h

def W0 (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R := (Fin.revPerm.toPEquiv).toMatrix

/- English proof (translation)
Rewrite using `[W0, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem longest_element_conj {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) :
    W0 R n * M * W0 R n = M.submatrix Fin.rev Fin.rev := by
  rw [W0, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j; simp

/- English proof (translation)
Establish `h` using `longest_element_conj (R := R) (n := n) 1`. Rewrite `h` using `[Matrix.mul_one]`. Rewrite using `[h]`. Conclude with `Matrix.submatrix_one_equiv Fin.revPerm`.
-/
theorem longest_element_mul_self {R : Type} [CommRing R] : W0 R n * W0 R n = 1 := by
  have h := longest_element_conj (R := R) (n := n) 1
  rw [Matrix.mul_one] at h
  rw [h]; exact Matrix.submatrix_one_equiv Fin.revPerm

/- English proof (translation)
Apply the tactic sequence `ext i j; simp only [W0, Matrix.map_apply, PEquiv.toMatrix_apply]; split_ifs <;> simp`.
-/
theorem lattice_model_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : (W0 R n).map f = W0 S n := by
  ext i j; simp only [W0, Matrix.map_apply, PEquiv.toMatrix_apply]; split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [W0, Matrix.transpose_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Fin.revPerm_apply]`. Apply the tactic sequence `congr 1; apply propext; constructor <;> (rintro rfl; simp)`.
-/
theorem longest_element_transpose {R : Type} [CommRing R] : (W0 R n)ᵀ = W0 R n := by
  ext i j; simp only [W0, Matrix.transpose_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Fin.revPerm_apply]
  congr 1; apply propext; constructor <;> (rintro rfl; simp)

def w0L : GL (Fin n) L := ⟨W0 L n, W0 L n, longest_element_mul_self, longest_element_mul_self⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `W0 L n * conjT _ (W0 L n) = 1`. Rewrite using `[conjT, lattice_model_map, longest_element_transpose, longest_element_mul_self]`.
-/
theorem longest_element_mem : (w0L : GL (Fin n) L) ∈ GQ0 L n := by
  change W0 L n * conjT _ (W0 L n) = 1
  rw [conjT, lattice_model_map, longest_element_transpose, longest_element_mul_self]

/- English proof (translation)
Simplify using `[conjAL, Algebra.TensorProduct.map_tmul]`.
-/
theorem conjAL_incl (x : L) : conjAL L (Algebra.TensorProduct.includeLeftRingHom x) =
    Algebra.TensorProduct.includeLeftRingHom ((IsCMField.complexConj L : L →+* L) x) := by
  simp [conjAL, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(g.val.map _) * conjT (conjAL L) (g.val.map _) = 1`. Establish `hg' : g.val * conjT _ g.val = 1` using `hg`. Establish `: conjT (conjAL L) (g.val.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)) = (conjT (IsCMField.complexConj L : L →+* L) g.val).map Algebra.TensorProduct.includeLeftRingHom`. Use extensionality with `i j`. Simplify using `only [conjT, Matrix.transpose_apply, Matrix.map_apply]`.

Conclude with `conjAL_incl _`. Rewrite using `[this, ← Matrix.map_mul, hg', Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem map_mem_GA (g : GL (Fin n) L) (hg : g ∈ GQ0 L n) :
    Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) g ∈ GA L n := by
  change (g.val.map _) * conjT (conjAL L) (g.val.map _) = 1
  have hg' : g.val * conjT _ g.val = 1 := hg
  have : conjT (conjAL L) (g.val.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)) =
      (conjT (IsCMField.complexConj L : L →+* L) g.val).map Algebra.TensorProduct.includeLeftRingHom := by
    ext i j; simp only [conjT, Matrix.transpose_apply, Matrix.map_apply]; exact conjAL_incl _
  rw [this, ← Matrix.map_mul, hg', Matrix.map_one _ (map_zero _) (map_one _)]

def toGQ (g : GL (Fin n) L) (hg : g ∈ GQ0 L n) : GQ L n :=
  ⟨⟨_, map_mem_GA g hg⟩, ⟨g, hg, rfl⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toGQ_val (g : GL (Fin n) L) (hg : g ∈ GQ0 L n) :
    ((((toGQ g hg : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      g.val.map Algebra.TensorProduct.includeLeftRingHom := rfl

end

end PI.UnitaryGroupMassFormula.HwConjInf

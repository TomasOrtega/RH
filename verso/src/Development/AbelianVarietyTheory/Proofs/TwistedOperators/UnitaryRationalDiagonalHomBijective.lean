import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TwistRatBij

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Simplify using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.lid_symm_apply]`.
-/
theorem inclR_eq (e : E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F e = (Algebra.TensorProduct.lid F E).symm e := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.lid_symm_apply]

/- English proof (translation)
Rewrite using `[inclR_eq]`. Conclude with `(Algebra.TensorProduct.lid F E).symm_apply_apply x`.
-/
theorem inclR_lid (x : F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F (Algebra.TensorProduct.lid F E x) = x := by
  rw [inclR_eq]; exact (Algebra.TensorProduct.lid F E).symm_apply_apply x

/- English proof (translation)
Rewrite using `[inclR_eq]`. Conclude with `(Algebra.TensorProduct.lid F E).apply_symm_apply e`.
-/
theorem lid_inclR (e : E) :
    Algebra.TensorProduct.lid F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F e) = e := by
  rw [inclR_eq]; exact (Algebra.TensorProduct.lid F E).apply_symm_apply e

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem lid_sigR (σ : E →ₐ[F] E) (x : F ⊗[F] E) :
    σ (Algebra.TensorProduct.lid F E x) =
      Algebra.TensorProduct.lid F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

abbrev matOf {R : Type} [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA R σ J) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (((show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR R σ J from x) : GL (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagH_val (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : Formalism.UG.UJ (σ : E →+* E) J) (i j : Fin n) :
    matOf (diagH σ J F g) i j =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR F (((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) := rfl

/- English proof (translation)
Introduce `F E _ _ _ σ n J`. Prove the components needed by the constructor for the conclusion. Introduce `g h hgh`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Establish `h1` using `congrArg (fun x => matOf x i j) hgh`. Simplify using `only [diagH_val] at h1`. Establish `h2` using `congrArg (Algebra.TensorProduct.lid F E) h1`. Rewrite `h2` using `[lid_inclR, lid_inclR]`. Then use the resulting hypothesis.

Introduce `h`. Set `h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR F σ J` to `h`. Set `L : F ⊗[F] E →+* E` to `(Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom`. Set `g : GL (Fin n) E` to `Formalism.UG.bc L h'.1`. Establish `hL : ∀ x, (σ : E →+* E) (L x) = L (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ x)` using `fun x => lid_sigR σ x`.

Establish `hmem : g ∈ Formalism.UG.UJ (σ : E →+* E) J`. Establish `hh : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ) ((h'.1 : GL (Fin n) (F ⊗[F] E)) : Matrix (Fin n) (Fin n) (F ⊗[F] E)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J * ((h'.1 : GL (Fin n) (F ⊗[F] E)) : Matrix (Fin n) (Fi …` using `h'.2`. Establish `hJ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J).map L = J`. Use extensionality with `r s`. Conclude with `lid_inclR (J r s)`.

Use `show Formalism.UG.cT (σ : E →+* E) ((h'.1 : Matrix (Fin n) (Fin n) (F ⊗[F] E)).map L) * J * ((h'.1 : Matrix (Fin n) (Fin n) (F ⊗[F] E)).map L) = J`. Generalize the expression as in `((h'.1 : GL (Fin n) (F ⊗[F] E)) : Matrix (Fin n) (Fin n) (F ⊗[F] E)) = M at hh ⊢`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ) (σ : E →+* E) L hL, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hh]`. Use `⟨⟨g, hmem⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `inclR_lid _`.
-/
theorem diagH_bijective : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), Function.Bijective (diagH σ J F) := by
  intro F E _ _ _ σ n J
  constructor
  · intro g h hgh
    apply Subtype.ext; apply Units.ext; ext i j
    have h1 := congrArg (fun x => matOf x i j) hgh
    simp only [diagH_val] at h1
    have h2 := congrArg (Algebra.TensorProduct.lid F E) h1
    rwa [lid_inclR, lid_inclR] at h2
  · intro h
    let h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR F σ J := h
    let L : F ⊗[F] E →+* E := (Algebra.TensorProduct.lid F E).toRingEquiv.toRingHom
    let g : GL (Fin n) E := Formalism.UG.bc L h'.1
    have hL : ∀ x, (σ : E →+* E) (L x) = L (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ x) := fun x => lid_sigR σ x
    have hmem : g ∈ Formalism.UG.UJ (σ : E →+* E) J := by
      have hh : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ) ((h'.1 : GL (Fin n) (F ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (F ⊗[F] E)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J *
          ((h'.1 : GL (Fin n) (F ⊗[F] E)) : Matrix (Fin n) (Fin n) (F ⊗[F] E)) =
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J := h'.2
      have hJ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR F J).map L = J := by
        ext r s; exact lid_inclR (J r s)
      show Formalism.UG.cT (σ : E →+* E) ((h'.1 : Matrix (Fin n) (Fin n) (F ⊗[F] E)).map L) * J *
        ((h'.1 : Matrix (Fin n) (Fin n) (F ⊗[F] E)).map L) = J
      generalize ((h'.1 : GL (Fin n) (F ⊗[F] E)) : Matrix (Fin n) (Fin n) (F ⊗[F] E)) = M at hh ⊢
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR F σ) (σ : E →+* E) L hL, ← hJ,
        ← Matrix.map_mul, ← Matrix.map_mul, hh]
    refine ⟨⟨g, hmem⟩, ?_⟩
    apply Subtype.ext; apply Units.ext; ext i j
    exact inclR_lid _

end GlobalTheory.TwistRatBij

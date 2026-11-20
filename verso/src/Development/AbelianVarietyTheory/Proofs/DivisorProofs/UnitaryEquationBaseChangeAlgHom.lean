import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneStrongApproxGeneratorImports
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

namespace GlobalTheory

/- English proof (translation)
Introduce `h`. Use `set φ' : R ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom with hφ'`. Establish `hsig : ∀ x, φ' (sigR R σ x) = sigR K σ (φ' x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r e => simp [hφ', sigR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hJ : (JR R J).map φ' = JR K J`. Use extensionality with `i j`.

Simplify using `[JR, inclR, hφ']`. Establish `hcT : (Formalism.UG.cT (sigR R σ) g).map φ' = Formalism.UG.cT (sigR K σ) (g.map φ')`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hsig]`. Establish `h2` using `congrArg (fun A => A.map φ') h`.

Simplify using `only [Matrix.map_mul] at h2`. Rewrite `h2` using `[hcT, hJ]`. Conclude with `h2`.
-/
theorem unitaryEq_baseChange {F E R K : Type} [Field F] [Field E] [Algebra F E] [CommRing R]
    [Algebra F R] [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] K) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :
    Formalism.UG.cT (sigR R σ) g * JR R J * g = JR R J →
    Formalism.UG.cT (sigR K σ) (g.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) * JR K J *
      g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) = JR K J := by
  intro h
  set φ' : R ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
    with hφ'
  have hsig : ∀ x, φ' (sigR R σ x) = sigR K σ (φ' x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [hφ', sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hJ : (JR R J).map φ' = JR K J := by
    ext i j
    simp [JR, inclR, hφ']
  have hcT : (Formalism.UG.cT (sigR R σ) g).map φ' = Formalism.UG.cT (sigR K σ) (g.map φ') := by
    ext i j
    simp [Formalism.UG.cT, hsig]
  have h2 := congrArg (fun A => A.map φ') h
  simp only [Matrix.map_mul] at h2
  rw [hcT, hJ] at h2
  exact h2

end GlobalTheory

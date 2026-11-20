import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ImaginaryRootNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.FlatSec

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tri_trans {R k : Type} [CommRing R] [Field k] {φ : c.F →+* R} {φ' φ'' : c.F →+* k} {x : Sp R ⟶ Z.X}
    {x' x'' : Sp k ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* k} {g : EigFrame Z φ' x'} {g' : EigFrame Z φ'' x''}
    {t d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ} (h : f.Tri ψ g t) (h' : g.Tri (RingHom.id k) g' d) :
    f.Tri ψ g' (fun τ i => t τ i * d τ i) := by
  have h1 : spMap (RingHom.id k) = 𝟙 _ := Spec.map_id _
  have h3 : spMap (dualMap (RingHom.id k)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  obtain ⟨rfl, rfl, h⟩ := h
  obtain ⟨e1, e2, h'⟩ := h'
  rw [h1, Category.id_comp] at e1
  subst e1
  refine ⟨rfl, e2, fun τ i => ?_⟩
  choose a a1 a2 a3 using h τ
  obtain ⟨cf, b1, b2, b3⟩ := h' τ i
  simp only [h3, Category.id_comp] at b3
  let A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) k := fun j i => a i j
  have hA : A.BlockTriangular id := fun j k hk => a2 k j hk
  obtain ⟨c1, c2⟩ := Guard.tri_mulVec hA b2
  refine ⟨A.mulVec cf, ?_, c1, tanLinG _ (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ (f.tan τ j)) _ A cf _ a3 b3⟩
  rw [c2, b1, show A i i = t τ i from a1 i, Units.val_mul]

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
  {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
  {n : Letter Dw → ℤ} {σ : Y.Y.Fn}

variable {K : Type} [Field K] (d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ)

end Gen

end GlobalTheory.ShFam.FlatSec

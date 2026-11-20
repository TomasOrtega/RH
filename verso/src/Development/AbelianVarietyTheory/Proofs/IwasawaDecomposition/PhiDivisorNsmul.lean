import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef.PhiNsmul

/- English proof (translation)
Simplify using `only [InvFun.evalZ, InvFun.eval, comb]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evalZ_comb_self {O : Type} [CommRing O] (φ : InvFun O) (n : ℕ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] (be : LinearMap.BilinForm ℤ X) :
    (comb n φ 0 φ).evalZ be = n * φ.evalZ be := by
  simp only [InvFun.evalZ, InvFun.eval, comb]
  push_cast
  ring

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Z φ D₁ u h`. Introduce `W _ _ _ hW ϖ hϖ χ t ht P hχ be hbe hmon`. Take `⟨n, hn, hI⟩` from `h W hW ϖ hϖ χ t ht P hχ be hbe hmon`. Use `⟨u * n, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[evalZ_comb_self, ← hn]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨i, hi⟩` from `D₁.exists_mem (χ (closedPoint W))`. Unfold `idlAlong at hI ⊢`. Rewrite `hI` using `[D₁.stalkId_idealSheaf i _ hi, Ideal.map_span, Set.image_singleton]`.

Rewrite using `[(D₁.nsmul u).stalkId_idealSheaf i _ hi, Ideal.map_span, Set.image_singleton]`. Express the relevant statement in the definitionally equal form `Ideal.span {(Scheme.stalkClosedPointTo χ).hom ((Z.X.presheaf.germ _ _ hi).hom (D₁.f i ^ u))} = _`. Rewrite using `[map_pow, map_pow, ← Ideal.span_singleton_pow, hI, Ideal.span_singleton_pow, ← pow_mul, mul_comm]`.
-/
theorem isPhiDiv_nsmul_self : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (φ : InvFun (𝓞 E))
    (D₁ : GlobalTheory.EffCartierData Z.X) (n : ℕ), IsPhiDiv φ Z D₁ → IsPhiDiv (comb n φ 0 φ) Z (D₁.nsmul n) := by
  intro E _ _ _ H D l Xo c O _ β Z φ D₁ u h
  intro W _ _ _ hW ϖ hϖ χ t ht P hχ be hbe hmon
  obtain ⟨n, hn, hI⟩ := h W hW ϖ hϖ χ t ht P hχ be hbe hmon
  refine ⟨u * n, ?_, ?_⟩
  · rw [evalZ_comb_self, ← hn]
    push_cast
    ring
  · obtain ⟨i, hi⟩ := D₁.exists_mem (χ (closedPoint W))
    unfold idlAlong at hI ⊢
    rw [D₁.stalkId_idealSheaf i _ hi, Ideal.map_span, Set.image_singleton] at hI
    rw [(D₁.nsmul u).stalkId_idealSheaf i _ hi, Ideal.map_span, Set.image_singleton]
    change Ideal.span {(Scheme.stalkClosedPointTo χ).hom ((Z.X.presheaf.germ _ _ hi).hom (D₁.f i ^ u))} = _
    rw [map_pow, map_pow, ← Ideal.span_singleton_pow, hI, Ideal.span_singleton_pow, ← pow_mul, mul_comm]

end GlobalTheory.TorRef.PhiNsmul

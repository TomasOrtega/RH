import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFactorResidueFieldOfClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `g hg`. Take `⟨p, hp⟩ : ∃ p, p = E.H.ι g` from `⟨_, rfl⟩`. Rewrite `hg` using `[← hp]`. Set `Ω` to `G'.left.residueField p`.

Set `x0 : Sp Ω ⟶ G'.left` to `G'.left.fromSpecResidueField p`. Set `x : Sp Ω ⟶ S` to `x0 ≫ G'.hom`. Establish `hx : ∀ w, (x ≫ π) w = closedPoint R`. Introduce `w`. Simplify using `only [x, x0, Scheme.Hom.comp_apply]`.

Rewrite using `[Scheme.fromSpecResidueField_apply]`. Conclude with `hg`. Take `⟨κ, hκ⟩` from `spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx`. Take `⟨Ω', _, io, e, l, -, hl1, hl2⟩` from `E.fib Ω x κ hκ`. Set `w : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ x)` to `pullback.lift (spMap io ≫ x0) (𝟙 _) (by simp [x])`.

Set `w0 : Sp Ω'` to `closedPoint Ω'`. Establish `hw : pullback.fst G'.hom (spMap io ≫ x) (w w0) = p`. Rewrite using `[← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]`. Conclude with `Scheme.fromSpecResidueField_apply _ _`. Establish `hlw : l (w w0) = g`.

Apply `E.H.ι.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[← Scheme.Hom.comp_apply, hl1, ← hp]`. Conclude with `hw`. Use `⟨pullback.fst E.Y.hom (spMap (io.comp κ)) (e.hom.left (w w0)), ?_⟩` and prove the remaining obligations. Rewrite using `[← hlw, ← Scheme.Hom.comp_apply, hl2]`.

Simplify using `only [Scheme.Hom.comp_apply]`. Introduce `hπ y`. Take `⟨s, hs⟩` from `hπ.surj (closedPoint R)`. Set `Ω` to `S.residueField s`. Set `x : Sp Ω ⟶ S` to `S.fromSpecResidueField s`.

Establish `hx : ∀ w, (x ≫ π) w = closedPoint R`. Introduce `w`. Simplify using `only [x, Scheme.Hom.comp_apply]`. Rewrite using `[Scheme.fromSpecResidueField_apply]`. Conclude with `hs`.

Take `⟨κ, hκ⟩` from `spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx`. Take `⟨Ω', _, io, e, l, -, hl1, hl2⟩` from `E.fib Ω x κ hκ`. Take `⟨w', hw'⟩` from `(pullback.fst E.Y.hom (spMap (io.comp κ))).surjective y`. Set `w` to `e.inv.left w'`. Establish `hew : e.hom.left w = w'`.

Simplify using `only [w]`. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, e.inv_hom_id]`. Both sides reduce to the same expression. Use `⟨l w, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply l E.H.ι, hl1, ← Scheme.Hom.comp_apply (pullback.fst G'.hom (spMap io ≫ x)) G'.hom, pullback.condition]`.

Simplify using `only [Scheme.Hom.comp_apply, x]`. Rewrite using `[Scheme.fromSpecResidueField_apply]`. Conclude with `hs`. Rewrite using `[← Scheme.Hom.comp_apply, hl2]`. Simplify using `only [Scheme.Hom.comp_apply]`.

Rewrite using `[hew, hw']`.
-/
theorem Emb.range_closed (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (E : Emb π G') :
    (∀ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R → ∃ y : E.Y.left, E.f g = E.j y) ∧
    (Surjective π → ∀ y : E.Y.left, ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g = E.j y) := by
  constructor
  · intro g hg
    obtain ⟨p, hp⟩ : ∃ p, p = E.H.ι g := ⟨_, rfl⟩
    rw [← hp] at hg
    let Ω := G'.left.residueField p
    let x0 : Sp Ω ⟶ G'.left := G'.left.fromSpecResidueField p
    let x : Sp Ω ⟶ S := x0 ≫ G'.hom
    have hx : ∀ w, (x ≫ π) w = closedPoint R := by
      intro w
      simp only [x, x0, Scheme.Hom.comp_apply]
      rw [Scheme.fromSpecResidueField_apply]
      exact hg
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx
    obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω x κ hκ
    let w : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ x) :=
      pullback.lift (spMap io ≫ x0) (𝟙 _) (by simp [x])
    let w0 : Sp Ω' := closedPoint Ω'
    have hw : pullback.fst G'.hom (spMap io ≫ x) (w w0) = p := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    have hlw : l (w w0) = g := by
      apply E.H.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hl1, ← hp]
      exact hw
    refine ⟨pullback.fst E.Y.hom (spMap (io.comp κ)) (e.hom.left (w w0)), ?_⟩
    rw [← hlw, ← Scheme.Hom.comp_apply, hl2]
    simp only [Scheme.Hom.comp_apply]
  · intro hπ y
    obtain ⟨s, hs⟩ := hπ.surj (closedPoint R)
    let Ω := S.residueField s
    let x : Sp Ω ⟶ S := S.fromSpecResidueField s
    have hx : ∀ w, (x ≫ π) w = closedPoint R := by
      intro w
      simp only [x, Scheme.Hom.comp_apply]
      rw [Scheme.fromSpecResidueField_apply]
      exact hs
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx
    obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω x κ hκ
    obtain ⟨w', hw'⟩ := (pullback.fst E.Y.hom (spMap (io.comp κ))).surjective y
    let w := e.inv.left w'
    have hew : e.hom.left w = w' := by
      simp only [w]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e.inv_hom_id]
      rfl
    refine ⟨l w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply l E.H.ι, hl1,
        ← Scheme.Hom.comp_apply (pullback.fst G'.hom (spMap io ≫ x)) G'.hom, pullback.condition]
      simp only [Scheme.Hom.comp_apply, x]
      rw [Scheme.fromSpecResidueField_apply]
      exact hs
    · rw [← Scheme.Hom.comp_apply, hl2]
      simp only [Scheme.Hom.comp_apply]
      rw [hew, hw']

end GlobalTheory.Mum

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

/- English proof (translation)
Use `haveI := N.isOpen`. Set `X₁ : Over.mk q ⟶ G` to `Over.homMk (pullback.lift a q ha ≫ N.u) (by`. Express the relevant statement in the definitionally equal form `(pullback.lift a q ha ≫ N.u) ≫ G.hom = q`. Rewrite using `[Category.assoc, N.u_over, pullback.lift_snd])`. Set `X₂ : Over.mk q ⟶ G` to `Over.homMk (pullback.lift b q hb ≫ N.u) (by`.

Express the relevant statement in the definitionally equal form `(pullback.lift b q hb ≫ N.u) ≫ G.hom = q`. Rewrite using `[Category.assoc, N.u_over, pullback.lift_snd])`. Set `m : Z ⟶ G.left` to `(X₁ * X₂).left`. Establish `hm : m ≫ G.hom = q` using `Over.w (X₁ * X₂)`. Set `O : Z.Opens` to `m ⁻¹ᵁ N.u.opensRange`.

Establish `hO : Set.range (O.ι ≫ m) ⊆ Set.range N.u`. Introduce and unpack `_ ⟨z, rfl⟩`. Establish `hz : O.ι z ∈ O` using `z.2`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `hz`.

Set `h' : O.toScheme ⟶ pullback N.U.hom π` to `IsOpenImmersion.lift N.u (O.ι ≫ m) hO`. Establish `hh : h' ≫ N.u = O.ι ≫ m` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hs : h' ≫ pullback.snd N.U.hom π = O.ι ≫ q`. Rewrite using `[← N.u_over, ← Category.assoc, hh, Category.assoc, hm]`. Use `⟨O, h' ≫ pullback.fst _ _, fun z hz => ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `N.all (m z) ?_` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply m G.hom, hm]`. Conclude with `hz`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hs, Category.assoc]`. Introduce and unpack `T t s x y hts ⟨x₀, hx₁, hx₂, hx₃⟩ ⟨y₀, hy₁, hy₂, hy₃⟩`.

Set `τ : Over.mk s ⟶ Over.mk q` to `Over.homMk (t ≫ O.ι) (by`. Express the relevant statement in the definitionally equal form `(t ≫ O.ι) ≫ q = s`. Rewrite using `[Category.assoc, hts])`. Establish `ex : x = τ ≫ X₁` using `by ext1`. Express the relevant statement in the definitionally equal form `x.left = (t ≫ O.ι) ≫ pullback.lift a q ha ≫ N.u`.

Rewrite using `[← hx₃, ← Category.assoc]`. Use `congr 1`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[hx₁, Category.assoc, pullback.lift_fst, Category.assoc]`. Rewrite using `[hx₂, Category.assoc, pullback.lift_snd, Category.assoc, hts]`.

Establish `ey : y = τ ≫ X₂` using `by ext1`. Express the relevant statement in the definitionally equal form `y.left = (t ≫ O.ι) ≫ pullback.lift b q hb ≫ N.u`. Rewrite using `[← hy₃, ← Category.assoc]`. Use `congr 1`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[hy₁, Category.assoc, pullback.lift_fst, Category.assoc]`. Rewrite using `[hy₂, Category.assoc, pullback.lift_snd, Category.assoc, hts]`. Use `⟨t ≫ h', Category.assoc _ _ _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hs, hts]`. Rewrite using `[ex, ey, ← MonObj.comp_mul, Category.assoc, hh]`.

Conclude with `(Category.assoc _ _ _).symm`.
-/
theorem Near.exists_mul_pt {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]
    (N : Near π G) {Z : Scheme.{0}} (q : Z ⟶ S) (a b : Z ⟶ N.U.left) (ha : a ≫ N.U.hom = q ≫ π)
    (hb : b ≫ N.U.hom = q ≫ π) :
    ∃ (O : Z.Opens) (h : O.toScheme ⟶ N.U.left), (∀ z : Z, π (q z) = closedPoint R → z ∈ O) ∧
      h ≫ N.U.hom = O.ι ≫ q ≫ π ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), t ≫ O.ι ≫ q = s →
        N.Pt s (t ≫ O.ι ≫ a) x.left → N.Pt s (t ≫ O.ι ≫ b) y.left → N.Pt s (t ≫ h) (x * y).left := by
  haveI := N.isOpen
  let X₁ : Over.mk q ⟶ G := Over.homMk (pullback.lift a q ha ≫ N.u) (by
    change (pullback.lift a q ha ≫ N.u) ≫ G.hom = q
    rw [Category.assoc, N.u_over, pullback.lift_snd])
  let X₂ : Over.mk q ⟶ G := Over.homMk (pullback.lift b q hb ≫ N.u) (by
    change (pullback.lift b q hb ≫ N.u) ≫ G.hom = q
    rw [Category.assoc, N.u_over, pullback.lift_snd])
  let m : Z ⟶ G.left := (X₁ * X₂).left
  have hm : m ≫ G.hom = q := Over.w (X₁ * X₂)
  let O : Z.Opens := m ⁻¹ᵁ N.u.opensRange
  have hO : Set.range (O.ι ≫ m) ⊆ Set.range N.u := by
    rintro _ ⟨z, rfl⟩
    have hz : O.ι z ∈ O := z.2
    rw [Scheme.Hom.comp_apply]
    exact hz
  let h' : O.toScheme ⟶ pullback N.U.hom π := IsOpenImmersion.lift N.u (O.ι ≫ m) hO
  have hh : h' ≫ N.u = O.ι ≫ m := IsOpenImmersion.lift_fac _ _ _
  have hs : h' ≫ pullback.snd N.U.hom π = O.ι ≫ q := by
    rw [← N.u_over, ← Category.assoc, hh, Category.assoc, hm]
  refine ⟨O, h' ≫ pullback.fst _ _, fun z hz => ?_, ?_, ?_⟩
  · refine N.all (m z) ?_
    rw [← Scheme.Hom.comp_apply m G.hom, hm]
    exact hz
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.assoc]
  · rintro T t s x y hts ⟨x₀, hx₁, hx₂, hx₃⟩ ⟨y₀, hy₁, hy₂, hy₃⟩
    let τ : Over.mk s ⟶ Over.mk q := Over.homMk (t ≫ O.ι) (by
      change (t ≫ O.ι) ≫ q = s
      rw [Category.assoc, hts])
    have ex : x = τ ≫ X₁ := by
      ext1
      change x.left = (t ≫ O.ι) ≫ pullback.lift a q ha ≫ N.u
      rw [← hx₃, ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · rw [hx₁, Category.assoc, pullback.lift_fst, Category.assoc]
      · rw [hx₂, Category.assoc, pullback.lift_snd, Category.assoc, hts]
    have ey : y = τ ≫ X₂ := by
      ext1
      change y.left = (t ≫ O.ι) ≫ pullback.lift b q hb ≫ N.u
      rw [← hy₃, ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · rw [hy₁, Category.assoc, pullback.lift_fst, Category.assoc]
      · rw [hy₂, Category.assoc, pullback.lift_snd, Category.assoc, hts]
    refine ⟨t ≫ h', Category.assoc _ _ _, ?_, ?_⟩
    · rw [Category.assoc, hs, hts]
    · rw [ex, ey, ← MonObj.comp_mul, Category.assoc, hh]
      exact (Category.assoc _ _ _).symm

/- English proof (translation)
Take `⟨O, h, h₁, h₂, h₃⟩` from `N.exists_mul_pt (pullback.snd (N.U ⊗ N.U).hom M.π) (pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left) (pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left) (by rw [Category.assoc, Over.w (fst N.U N.U), pullback.condition]) (by rw [Category.assoc, Over.w (snd N.U N.U), pull …`. Use `⟨O, h, fun z hz => h₁ z ?_, ?_, h₃⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]`. Conclude with `hz`. Rewrite using `[h₂, pullback.condition]`.
-/
theorem Near.exists_mul_pt_pullback (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S)
    [GrpObj G'] (N : Near M.π G') :
    ∃ (O : (pullback (N.U ⊗ N.U).hom M.π).Opens) (h : O.toScheme ⟶ N.U.left),
      (∀ z : ↥(pullback (N.U ⊗ N.U).hom M.π),
        (N.U ⊗ N.U).hom (pullback.fst (N.U ⊗ N.U).hom M.π z) = closedPoint R → z ∈ O) ∧
      h ≫ N.U.hom = O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (N.U ⊗ N.U).hom ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ M.S) (x y : Over.mk s ⟶ G'),
        t ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π = s →
        N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left) x.left →
        N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left) y.left →
        N.Pt s (t ≫ h) (x * y).left := by
  obtain ⟨O, h, h₁, h₂, h₃⟩ := N.exists_mul_pt (pullback.snd (N.U ⊗ N.U).hom M.π)
    (pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left)
    (pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left)
    (by rw [Category.assoc, Over.w (fst N.U N.U), pullback.condition])
    (by rw [Category.assoc, Over.w (snd N.U N.U), pullback.condition])
  refine ⟨O, h, fun z hz => h₁ z ?_, ?_, h₃⟩
  · rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hz
  · rw [h₂, pullback.condition]

end GlobalTheory.Mum

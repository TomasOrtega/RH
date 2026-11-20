import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.LatPush

open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (mu : SABMap t' t f)

/- English proof (translation)
Substitute `h` using the available equality. Use `⟨MulEquiv.ofBijective (pushHom mu.cart (Over.mk q)) ⟨fun a b hab => ?_, fun a => ?_⟩, fun g => rfl⟩` and prove the remaining obligations. Conclude with `Over.OverMorphism.ext (mu.cart.1.hom_ext (congrArg (fun z => z.left) hab) ((Over.w a).trans (Over.w b).symm))`. Take `⟨w, h1, h2⟩` from `OpenReg.exists_lift mu q a.left (Over.w a)`. Conclude with `⟨Over.homMk w h1, Over.OverMorphism.ext h2⟩`.
-/
theorem exists_ptEquiv {T : Scheme.{0}} (q : T ⟶ X') (q' : T ⟶ X) (h : q ≫ f = q') :
    ∃ e : (Over.mk q ⟶ t'.G) ≃* (Over.mk q' ⟶ t.G), ∀ g, (e g).left = g.left ≫ mu.φ := by
  subst h
  refine ⟨MulEquiv.ofBijective (pushHom mu.cart (Over.mk q)) ⟨fun a b hab => ?_, fun a => ?_⟩, fun g => rfl⟩
  · exact Over.OverMorphism.ext (mu.cart.1.hom_ext (congrArg (fun z => z.left) hab)
      ((Over.w a).trans (Over.w b).symm))
  · obtain ⟨w, h1, h2⟩ := OpenReg.exists_lift mu q a.left (Over.w a)
    exact ⟨Over.homMk w h1, Over.OverMorphism.ext h2⟩

/- English proof (translation)
Rewrite using `[OpenReg.spMap_comp]`. Use `congr 1`. Conclude with `RingHom.ext fun a => φ.commutes a`.
-/
theorem spMap_alg {O B B' : Type} [CommRing O] [CommRing B] [CommRing B'] [Algebra O B] [Algebra O B']
    (φ : B →ₐ[O] B') : spMap φ.toRingHom ≫ spMap (algebraMap O B) = spMap (algebraMap O B') := by
  rw [OpenReg.spMap_comp]
  congr 1
  exact RingHom.ext fun a => φ.commutes a

/- English proof (translation)
Rewrite using `[OpenReg.spMap_comp, OpenReg.spMap_comp, GlobalTheory.Frames.FramedBaseChange.dualMap_comp_alg]`.
-/
theorem dualMap_alg {O O' : Type} [CommRing O] [CommRing O'] (φ : O →+* O') :
    spMap (dualMap φ) ≫ spMap (algebraMap O (DualNumber O)) =
      spMap (algebraMap O' (DualNumber O')) ≫ spMap φ := by
  rw [OpenReg.spMap_comp, OpenReg.spMap_comp, GlobalTheory.Frames.FramedBaseChange.dualMap_comp_alg]

/- English proof (translation)
Use `choose e he using fun (B : Type) [CommRing B] [Algebra O B] => exists_ptEquiv mu (spMap (algebraMap O B) ≫ x) (spMap (algebraMap O B) ≫ x ≫ f) (Category.assoc _ _ _)`. Prove the components needed by the constructor for the conclusion. Introduce `h n c g hg`. Set `c' : TorsChar t' x (p ^ n)` to `{ χ := fun B _ _ _ g => c.χ B (e B g) mul := fun B _ _ _ g g' h1 h2 => by`. Rewrite using `[map_mul]`.

Conclude with `c.mul B _ _ (by rw [← map_pow, h1, map_one]) (by rw [← map_pow, h2, map_one])`. Use `nat := fun B B' _ _ _ _ _ _ φ g g' h1 h2 => c.nat B B' φ _ _ (by rw [← map_pow, h1, map_one]) (by rw [he, he, h2, Category.assoc]) }`. Take `⟨g', rfl⟩` from `(e _).surjective g`. Use `h n c' g' (mu.cart.1.hom_ext ?_ ?_)` and prove the remaining obligations. Rewrite using `[← he, hg, Category.assoc]`.

Rewrite using `[Over.w, Category.assoc, hv, ← Category.assoc, OpenReg.spMap_comp] show spMap _ ≫ x = spMap _ ≫ x`. Use `congr 2`. Apply the tactic sequence `ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']`. Introduce `h n c g hg`. Set `c' : TorsChar t (x ≫ f) (p ^ n)` to `{ χ := fun B _ _ _ g => c.χ B ((e B).symm g) mul := fun B _ _ _ g g' h1 h2 => by`.

Rewrite using `[map_mul]`. Conclude with `c.mul B _ _ (by rw [← map_pow, h1, map_one]) (by rw [← map_pow, h2, map_one])`. Use `nat := fun B B' _ _ _ _ _ _ φ g g' h1 h2 => c.nat B B' φ _ _ (by rw [← map_pow, h1, map_one]) (mu.cart.1.hom_ext (by rw [← he, Category.assoc, ← he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, h2]) (by`. Rewrite using `[Over.w, Category.assoc, Over.w]`. Use `show spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x`.

Rewrite using `[← Category.assoc, spMap_alg])) }`. Use `h n c' (e _ g) (by rw [he, hg, Category.assoc])` as an intermediate fact. Simplify `this` using `only [c', MulEquiv.symm_apply_apply]`.
-/
theorem dlogDvd_iff {O : Type} [CommRing O] (x : Sp O ⟶ X') (p m : ℕ) (v : Sp (DualNumber O) ⟶ t'.G.left)
    (hv : v ≫ t'.G.hom = spMap (algebraMap O (DualNumber O)) ≫ x) :
    DlogDvd t' x p m v ↔ DlogDvd t (x ≫ f) p m (v ≫ mu.φ) := by
  choose e he using fun (B : Type) [CommRing B] [Algebra O B] =>
    exists_ptEquiv mu (spMap (algebraMap O B) ≫ x) (spMap (algebraMap O B) ≫ x ≫ f) (Category.assoc _ _ _)
  constructor
  · intro h n c g hg
    let c' : TorsChar t' x (p ^ n) :=
      { χ := fun B _ _ _ g => c.χ B (e B g)
        mul := fun B _ _ _ g g' h1 h2 => by
          rw [map_mul]
          exact c.mul B _ _ (by rw [← map_pow, h1, map_one]) (by rw [← map_pow, h2, map_one])
        nat := fun B B' _ _ _ _ _ _ φ g g' h1 h2 =>
          c.nat B B' φ _ _ (by rw [← map_pow, h1, map_one]) (by rw [he, he, h2, Category.assoc]) }
    obtain ⟨g', rfl⟩ := (e _).surjective g
    refine h n c' g' (mu.cart.1.hom_ext ?_ ?_)
    · rw [← he, hg, Category.assoc]
    · rw [Over.w, Category.assoc, hv, ← Category.assoc, OpenReg.spMap_comp]
      show spMap _ ≫ x = spMap _ ≫ x
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']
  · intro h n c g hg
    let c' : TorsChar t (x ≫ f) (p ^ n) :=
      { χ := fun B _ _ _ g => c.χ B ((e B).symm g)
        mul := fun B _ _ _ g g' h1 h2 => by
          rw [map_mul]
          exact c.mul B _ _ (by rw [← map_pow, h1, map_one]) (by rw [← map_pow, h2, map_one])
        nat := fun B B' _ _ _ _ _ _ φ g g' h1 h2 =>
          c.nat B B' φ _ _ (by rw [← map_pow, h1, map_one]) (mu.cart.1.hom_ext
            (by rw [← he, Category.assoc, ← he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, h2])
            (by
              rw [Over.w, Category.assoc, Over.w]
              show spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
              rw [← Category.assoc, spMap_alg])) }
    have := h n c' (e _ g) (by rw [he, hg, Category.assoc])
    simpa only [c', MulEquiv.symm_apply_apply] using this

/- English proof (translation)
Introduce `E _ _ _ H X X' t t' f mu C _ _ p b xO hu v hv`. Consider the cases of `b`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, vO, h1, h2⟩`. Conclude with `⟨y ≫ f, by rw [← Category.assoc, hy, Category.assoc], vO ≫ mu.φ, (OpenReg.tan_iff mu rfl h1.1).2 h1, by rw [← Category.assoc, h2]⟩`.

Introduce and unpack `⟨y, hy, vO, h1, h2⟩`. Take `rfl` from `hu y hy`. Take `⟨w, a1, rfl⟩` from `OpenReg.exists_lift mu (spMap (algebraMap _ (DualNumber ↥(intO C))) ≫ xO) vO (by rw [h1.1, Category.assoc])`. Use `⟨xO, rfl, w, (OpenReg.tan_iff mu rfl a1).1 h1, mu.cart.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h2]`.

Rewrite using `[Category.assoc, a1, hv.1, ← Category.assoc, dualMap_alg, Category.assoc]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, m, vO, h1, h2, h3⟩`. Conclude with `⟨y ≫ f, by rw [← Category.assoc, hy, Category.assoc], m, vO ≫ mu.φ, (OpenReg.tan_iff mu rfl h1.1).2 h1, by rw [← Category.assoc, h2, Category.assoc], (dlogDvd_iff mu y p m vO h1.1).1 h3⟩`. Introduce and unpack `⟨y, hy, m, vO, h1, h2, h3⟩`.

Take `rfl` from `hu y hy`. Take `⟨w, a1, rfl⟩` from `OpenReg.exists_lift mu (spMap (algebraMap _ (DualNumber ↥(intO C))) ≫ xO) vO (by rw [h1.1, Category.assoc])`. Use `⟨xO, rfl, m, w, (OpenReg.tan_iff mu rfl a1).1 h1, mu.cart.1.hom_ext ?_ ?_, (dlogDvd_iff mu xO p m w a1).2 h3⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h2, Category.assoc]`. Rewrite using `[Category.assoc, a1, Category.assoc, hv.1, ← Category.assoc, dualMap_alg, ← Category.assoc, ← Category.assoc, OpenReg.epsMul_over]`.
-/
theorem lat_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (mu : SABMap t' t f) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (b : Bool) (xO : Sp ↥(intO C) ⟶ X'), (∀ y : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ xO ≫ f → y = xO ≫ f) → ∀ v, IsTanAtG t' (spMap (intO C).subtype ≫ xO) v → (v ∈ lat t' p (spMap (intO C).subtype ≫ xO) b ↔ v ≫ mu.φ ∈ lat t p (spMap (intO C).subtype ≫ xO ≫ f) b) := by
  intro E _ _ _ H X X' t t' f mu C _ _ p b xO hu v hv
  cases b
  · constructor
    · rintro ⟨y, hy, vO, h1, h2⟩
      exact ⟨y ≫ f, by rw [← Category.assoc, hy, Category.assoc], vO ≫ mu.φ,
        (OpenReg.tan_iff mu rfl h1.1).2 h1, by rw [← Category.assoc, h2]⟩
    · rintro ⟨y, hy, vO, h1, h2⟩
      obtain rfl := hu y hy
      obtain ⟨w, a1, rfl⟩ := OpenReg.exists_lift mu (spMap (algebraMap _ (DualNumber ↥(intO C))) ≫ xO) vO
        (by rw [h1.1, Category.assoc])
      refine ⟨xO, rfl, w, (OpenReg.tan_iff mu rfl a1).1 h1, mu.cart.1.hom_ext ?_ ?_⟩
      · rw [Category.assoc, h2]
      · rw [Category.assoc, a1, hv.1, ← Category.assoc, dualMap_alg, Category.assoc]
  · constructor
    · rintro ⟨y, hy, m, vO, h1, h2, h3⟩
      exact ⟨y ≫ f, by rw [← Category.assoc, hy, Category.assoc], m, vO ≫ mu.φ,
        (OpenReg.tan_iff mu rfl h1.1).2 h1, by rw [← Category.assoc, h2, Category.assoc],
        (dlogDvd_iff mu y p m vO h1.1).1 h3⟩
    · rintro ⟨y, hy, m, vO, h1, h2, h3⟩
      obtain rfl := hu y hy
      obtain ⟨w, a1, rfl⟩ := OpenReg.exists_lift mu (spMap (algebraMap _ (DualNumber ↥(intO C))) ≫ xO) vO
        (by rw [h1.1, Category.assoc])
      refine ⟨xO, rfl, m, w, (OpenReg.tan_iff mu rfl a1).1 h1, mu.cart.1.hom_ext ?_ ?_,
        (dlogDvd_iff mu xO p m w a1).2 h3⟩
      · rw [Category.assoc, h2, Category.assoc]
      · rw [Category.assoc, a1, Category.assoc, hv.1, ← Category.assoc, dualMap_alg, ← Category.assoc,
          ← Category.assoc, OpenReg.epsMul_over]

end GlobalTheory.ShFam.LatPush

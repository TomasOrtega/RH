import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.ChgOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

/- English proof (translation)
Simplify using `[scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]`.
-/
theorem scal_mul' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

/- English proof (translation)
Simplify using `[scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]`.
-/
theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

/- English proof (translation)
Take `⟨a, ha, -⟩` from `hs s'`. Take `⟨b, hb, -⟩` from `hs' s`. Take `⟨c1, -, hc1⟩` from `hs s`. Establish `h1 : b * a = 1`. Establish `e1 : ∀ i, s.f i = scal x (b * a) i * s.f i` using `fun i => by`.

Rewrite using `[scal_mul', _root_.mul_assoc, ← ha i, ← hb i]`. Establish `e2 : ∀ i, s.f i = scal x 1 i * s.f i` using `fun i => by rw [scal_one', _root_.one_mul]`. Conclude with `(hc1 _ e1).trans (hc1 _ e2).symm`. Conclude with `⟨⟨a, b, by rw [mul_comm]; exact h1, h1⟩, ha⟩`.
-/
theorem gen_unit' {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i)
    (hs' : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s'.f i) :
    ∃ u : Sˣ, ∀ i, s'.f i = scal x (u : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c1, -, hc1⟩ := hs s
  have h1 : b * a = 1 := by
    have e1 : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
      rw [scal_mul', _root_.mul_assoc, ← ha i, ← hb i]
    have e2 : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one', _root_.one_mul]
    exact (hc1 _ e1).trans (hc1 _ e2).symm
  exact ⟨⟨a, b, by rw [mul_comm]; exact h1, h1⟩, ha⟩

/- English proof (translation)
Simplify using `only [Scheme.Hom.appLE]`. Establish `e : (homOfLE h).op = 𝟙 _` using `Subsingleton.elim _ _`. Rewrite using `[e]`. Use `erw [CategoryTheory.Functor.map_id, Category.comp_id]`. Both sides reduce to the same expression.
-/
theorem appLE_id' {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (f : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom f = f := by
  simp only [Scheme.Hom.appLE]
  have e : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [e]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/- English proof (translation)
Unfold `spMap`. Conclude with `Spec.map_id _`.
-/
theorem spMap_id' (S : Type) [CommRing S] : spMap (RingHom.id S) = 𝟙 (Sp S) := by
  unfold spMap
  exact Spec.map_id _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨pm, h1, h2, h3⟩ i`. Establish `hp : pm = 𝟙 _`. Rewrite `h2` using `[spMap_id']`. Use `erw [Category.comp_id] at h2`.

Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Conclude with `h2.trans (Category.id_comp _).symm`. Conclude with `h1.trans (Category.id_comp _).symm`. Substitute `hp` using the available equality. Rewrite using `[← h3 i le_rfl]`.

Conclude with `appLE_id' _ _ _`. Introduce `h`. Use `⟨𝟙 _, Category.id_comp _, ?_, fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[spMap_id']`. Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm`.

Rewrite using `[h i]`. Conclude with `appLE_id' _ _ _`.
-/
theorem secBC_id_iff {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s t : LB.Sec (PPx x)) :
    SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i := by
  constructor
  · rintro ⟨pm, h1, h2, h3⟩ i
    have hp : pm = 𝟙 _ := by
      rw [spMap_id'] at h2
      erw [Category.comp_id] at h2
      refine pullback.hom_ext ?_ ?_
      · exact h2.trans (Category.id_comp _).symm
      · exact h1.trans (Category.id_comp _).symm
    subst hp
    rw [← h3 i le_rfl]
    exact appLE_id' _ _ _
  · intro h
    refine ⟨𝟙 _, Category.id_comp _, ?_, fun i hi => ?_⟩
    · rw [spMap_id']; exact (Category.id_comp _).trans (Category.comp_id _).symm
    · rw [h i]; exact appLE_id' _ _ _

end GlobalTheory.Frames.ChgOf

open GlobalTheory.Frames.ChgOf in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c S _ _ y y'`. Take `⟨x', hover', u', tan', eig', basis', s', gen'⟩` from `y'`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Simplify using `only at hx`.

Substitute `hx` using the available equality. Take `⟨N, _, _, v, ρ, hv, htan, hcomb, -, -⟩` from `GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S y.x`. Use `choose g hg using fun τ i => (y.basis τ (u' τ i) (tan' τ i) (eig' τ i)).exists`. Use `choose h hh using fun τ i => (basis' τ (y.u τ i) (y.tan τ i) (y.eig τ i)).exists`. Take `⟨a, ha⟩` from `gen_unit' y.s s' y.gen gen'`.

Use `⟨fun τ => Matrix.of (g τ), a, fun τ => ?_, rfl, fun τ i => hg τ i, (secBC_id_iff _ _ _ _).2 ha⟩` and prove the remaining obligations. Use `choose b hb using fun i => (htan _).1 (y.tan τ i)`. Use `choose b' hb' using fun i => (htan _).1 (tan' τ i)`. Establish `eb : y.u τ = fun i => v (b i)` using `funext fun i => (hb i).symm`. Establish `eb' : u' τ = fun i => v (b' i)` using `funext fun i => (hb' i).symm`.

Establish `h1 : ∀ i, b' i = ∑ j, g τ i j • b j` using `fun i => by`. Use `hg τ i` as an intermediate fact. Rewrite `this` using `[eb, hcomb, ← hb' i]`. Conclude with `hv this`. Establish `h2 : ∀ i, b i = ∑ j, h τ i j • b' j` using `fun i => by`.

Use `hh τ i` as an intermediate fact. Rewrite `this` using `[eb', hcomb, ← hb i]`. Conclude with `hv this`. Establish `hm : Matrix.of (h τ) * Matrix.of (g τ) = 1`. Use function extensionality and compare the values at `i`.

Use `(y.basis τ (y.u τ i) (y.tan τ i) (y.eig τ i)).unique ?_ ?_` and prove the remaining obligations. Rewrite using `[← hb i, eb, hcomb]`. Use `congr 1`. Rewrite using `[h2 i]`. Simplify using `only [h1, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]`.

Conclude with `Finset.sum_comm`. Rewrite using `[← hb i, eb, hcomb]`. Use `congr 1`. Simplify using `[Matrix.one_apply]`. Conclude with `Matrix.isUnit_det_of_left_inverse hm`.

Introduce and unpack `g g' a a' ⟨hx, h1, h2⟩ ⟨-, h1', h2'⟩`. Simplify using `only at hx h1 h2 h1' h2'`. Substitute `hx` using the available equality. Use `⟨funext fun τ => funext fun i => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(y.basis τ (u' τ i) (tan' τ i) (eig' τ i)).unique (h1 τ i) (h1' τ i)`.

Conclude with `(y.gen s').unique ((secBC_id_iff _ _ _ _).1 h2) ((secBC_id_iff _ _ _ _).1 h2')`.
-/
theorem GlobalTheory.Frames.frChg_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), (y'.x = y.x → ∃ (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ), (∀ τ, IsUnit (g τ).det) ∧ FrChg g (a : S) y y') ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y y' → g = g' ∧ a = a' := by
  intro E _ _ _ H Dw l Xo c S _ _ y y'
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  constructor
  · intro hx
    simp only at hx
    subst hx
    obtain ⟨N, _, _, v, ρ, hv, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S y.x
    choose g hg using fun τ i => (y.basis τ (u' τ i) (tan' τ i) (eig' τ i)).exists
    choose h hh using fun τ i => (basis' τ (y.u τ i) (y.tan τ i) (y.eig τ i)).exists
    obtain ⟨a, ha⟩ := gen_unit' y.s s' y.gen gen'
    refine ⟨fun τ => Matrix.of (g τ), a, fun τ => ?_, rfl, fun τ i => hg τ i, (secBC_id_iff _ _ _ _).2 ha⟩
    choose b hb using fun i => (htan _).1 (y.tan τ i)
    choose b' hb' using fun i => (htan _).1 (tan' τ i)
    have eb : y.u τ = fun i => v (b i) := funext fun i => (hb i).symm
    have eb' : u' τ = fun i => v (b' i) := funext fun i => (hb' i).symm
    have h1 : ∀ i, b' i = ∑ j, g τ i j • b j := fun i => by
      have := hg τ i
      rw [eb, hcomb, ← hb' i] at this
      exact hv this
    have h2 : ∀ i, b i = ∑ j, h τ i j • b' j := fun i => by
      have := hh τ i
      rw [eb', hcomb, ← hb i] at this
      exact hv this
    have hm : Matrix.of (h τ) * Matrix.of (g τ) = 1 := by
      funext i
      refine (y.basis τ (y.u τ i) (y.tan τ i) (y.eig τ i)).unique ?_ ?_
      · rw [← hb i, eb, hcomb]
        congr 1
        rw [h2 i]
        simp only [h1, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
        exact Finset.sum_comm
      · rw [← hb i, eb, hcomb]
        congr 1
        simp [Matrix.one_apply]
    exact Matrix.isUnit_det_of_left_inverse hm
  · rintro g g' a a' ⟨hx, h1, h2⟩ ⟨-, h1', h2'⟩
    simp only at hx h1 h2 h1' h2'
    subst hx
    refine ⟨funext fun τ => funext fun i => ?_, ?_⟩
    · exact (y.basis τ (u' τ i) (tan' τ i) (eig' τ i)).unique (h1 τ i) (h1' τ i)
    · exact (y.gen s').unique ((secBC_id_iff _ _ _ _).1 h2) ((secBC_id_iff _ _ _ _).1 h2')

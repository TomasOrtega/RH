import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.LieCombBaseChange

variable {R R' : Type} [CommRing R] [CommRing R']

/- English proof (translation)
Unfold `spMap`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (k : B →+* C) : spMap k ≫ spMap g = spMap (k.comp g) := by
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
Rewrite using `[spMap_comp_moduli_spaces, spMap_comp_moduli_spaces]`. Use `congr 1`. Apply the tactic sequence `refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>`. Simplify using `[epsScaleR, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, mul_comm]`.
-/
theorem dualMap_epsScale (f : R →+* R') (c : R) :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ spMap (epsScaleR c) =
      spMap (epsScaleR (f c)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
  rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [epsScaleR, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, mul_comm]

/- English proof (translation)
Simplify using `only [epsR, Over.mk_hom]`. Rewrite using `[spMap_comp_moduli_spaces, spMap_comp_moduli_spaces]`. Use `congr 1`. Apply the tactic sequence `refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>`. Simplify using `[ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dualMap_over (f : R →+* R') :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  simp only [epsR, Over.mk_hom]
  rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Simplify using `only [epsR, Over.mk_hom]`. Rewrite using `[spMap_comp_moduli_spaces]`. Use `congr 1`. Apply the tactic sequence `refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>`. Simplify using `[epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem epsScale_over (c : R) : spMap (epsScaleR c) ≫ (epsR R).hom = (epsR R).hom := by
  simp only [epsR, Over.mk_hom]
  rw [spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Establish `hd' : d ≫ T.hom = (Over.mk (T'.hom ≫ f)).hom` using `by simpa using hd`. Establish `hsq : φ ≫ G.hom = G'.hom ≫ f` using `h.1.w`. Establish `hone : (1 : T' ⟶ G').left ≫ φ = (1 : Over.mk (T'.hom ≫ f) ⟶ G).left`. Set `x₀ : Over.mk (T'.hom ≫ f) ⟶ G` to `Over.homMk ((1 : T' ⟶ G').left ≫ φ) (by`. Simplify using `only [Over.mk_hom, Category.assoc, hsq]`.

Rewrite using `[← Category.assoc, Over.w])`. Establish `hx : x₀ * x₀ = x₀`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[h.2 T' 1 1 x₀ x₀ rfl rfl, _root_.mul_one]`. Both sides reduce to the same expression.

Establish `h1 : x₀ = 1` using `by simpa using hx`. Rewrite using `[← h1]`. Both sides reduce to the same expression. Establish `key : ∀ (m : ℕ) (u : Fin m → (T ⟶ G)) (u' : Fin m → (T' ⟶ G')), (∀ i, (u' i).left ≫ φ = d ≫ (u i).left) → (List.ofFn u').prod.left ≫ φ = ((Over.homMk d hd' : Over.mk (T'.hom ≫ f) ⟶ T) ≫ (List.ofFn u).prod).left`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero`. Introduce `u u' _`. Simplify using `only [List.ofFn_zero, List.prod_nil, MonObj.comp_one, hone]`. Consider the case `succ m ih`.

Introduce `u u' hu`. Rewrite using `[List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul]`. Use `(h.2 T' _ _ _ _ ?_ ?_).symm` and prove the remaining obligations. Rewrite using `[Over.comp_left]`. Conclude with `(hu 0).symm`.

Conclude with `(ih _ _ fun i => hu i.succ).symm`. Use `key n u u' hu` as an intermediate fact. Rewrite `this` using `[Over.comp_left]`. Conclude with `this`.
-/
theorem prod_left_comp {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (d : T'.left ⟶ T.left)
    (hd : d ≫ T.hom = T'.hom ≫ f) {n : ℕ} (u : Fin n → (T ⟶ G)) (u' : Fin n → (T' ⟶ G'))
    (hu : ∀ i, (u' i).left ≫ φ = d ≫ (u i).left) :
    (List.ofFn u').prod.left ≫ φ = d ≫ (List.ofFn u).prod.left := by
  have hd' : d ≫ T.hom = (Over.mk (T'.hom ≫ f)).hom := by simpa using hd
  have hsq : φ ≫ G.hom = G'.hom ≫ f := h.1.w

  have hone : (1 : T' ⟶ G').left ≫ φ = (1 : Over.mk (T'.hom ≫ f) ⟶ G).left := by
    let x₀ : Over.mk (T'.hom ≫ f) ⟶ G := Over.homMk ((1 : T' ⟶ G').left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, hsq]
      rw [← Category.assoc, Over.w])
    have hx : x₀ * x₀ = x₀ := by
      apply Over.OverMorphism.ext
      rw [h.2 T' 1 1 x₀ x₀ rfl rfl, _root_.mul_one]
      rfl
    have h1 : x₀ = 1 := by simpa using hx
    rw [← h1]
    rfl

  have key : ∀ (m : ℕ) (u : Fin m → (T ⟶ G)) (u' : Fin m → (T' ⟶ G')),
      (∀ i, (u' i).left ≫ φ = d ≫ (u i).left) →
        (List.ofFn u').prod.left ≫ φ = ((Over.homMk d hd' : Over.mk (T'.hom ≫ f) ⟶ T) ≫ (List.ofFn u).prod).left := by
    intro m
    induction m with
    | zero =>
      intro u u' _
      simp only [List.ofFn_zero, List.prod_nil, MonObj.comp_one, hone]
    | succ m ih =>
      intro u u' hu
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul]
      refine (h.2 T' _ _ _ _ ?_ ?_).symm
      · rw [Over.comp_left]
        exact (hu 0).symm
      · exact (ih _ _ fun i => hu i.succ).symm
  have := key n u u' hu
  rw [Over.comp_left] at this
  exact this

end GlobalTheory.LieCombBaseChange

namespace GlobalTheory

open LieCombBaseChange

/- English proof (translation)
Introduce `R R' _ _ f G _ G' _ φ h n v w a v' w' hv hc`. Take `⟨u, hu, rfl⟩` from `hc`. Establish `hcomp : ∀ i, (spMap (epsScaleR (f (a i))) ≫ (v' i).left) ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (u i).left`. Introduce `i`. Rewrite using `[Category.assoc, hv i, hu i, ← Category.assoc, ← Category.assoc, LieCombBaseChange.dualMap_epsScale]`.

Establish `hprod : ∀ u'' : Fin n → (epsR R' ⟶ G'), (∀ i, (u'' i).left = spMap (epsScaleR (f (a i))) ≫ (v' i).left) → (List.ofFn u'').prod.left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (List.ofFn u).prod.left` using `fun u'' hu'' => LieCombBaseChange.prod_left_comp h _ (LieCombBaseChange.dualMap_over f) u u'' (fun i => by rw [hu'' i]; exact hcomp i)`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Set `u' : Fin n → (epsR R' ⟶ G')` to `fun i => Over.homMk (spMap (epsScaleR (f (a i))) ≫ (v' i).left) (by`. Rewrite using `[Category.assoc, Over.w]`.

Conclude with `LieCombBaseChange.epsScale_over _)`. Use `⟨u', fun i => rfl, ?_⟩` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `h.1.hom_ext` to reduce the goal to its premises. Rewrite using `[hw, hprod u' fun i => rfl]`.

Rewrite using `[Over.w w', Over.w]`. Introduce and unpack `⟨u'', hu'', rfl⟩`. Conclude with `hprod u'' hu''`.
-/
theorem lieComb_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G] (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap f) φ → ∀ (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) (a : Fin n → R) (v' : Fin n → (epsR R' ⟶ G')) (w' : epsR R' ⟶ G'), (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (v j).left) → IsLieComb a v w → (w'.left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left ↔ IsLieComb (fun i => f (a i)) v' w') := by
  intro R R' _ _ f G _ G' _ φ h n v w a v' w' hv hc
  obtain ⟨u, hu, rfl⟩ := hc

  have hcomp : ∀ i, (spMap (epsScaleR (f (a i))) ≫ (v' i).left) ≫ φ =
      spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (u i).left := by
    intro i
    rw [Category.assoc, hv i, hu i, ← Category.assoc, ← Category.assoc,
      LieCombBaseChange.dualMap_epsScale]
  have hprod : ∀ u'' : Fin n → (epsR R' ⟶ G'),
      (∀ i, (u'' i).left = spMap (epsScaleR (f (a i))) ≫ (v' i).left) →
        (List.ofFn u'').prod.left ≫ φ =
          spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (List.ofFn u).prod.left := fun u'' hu'' =>
    LieCombBaseChange.prod_left_comp h _ (LieCombBaseChange.dualMap_over f) u u''
      (fun i => by rw [hu'' i]; exact hcomp i)
  constructor
  · intro hw
    let u' : Fin n → (epsR R' ⟶ G') := fun i =>
      Over.homMk (spMap (epsScaleR (f (a i))) ≫ (v' i).left) (by
        rw [Category.assoc, Over.w]
        exact LieCombBaseChange.epsScale_over _)
    refine ⟨u', fun i => rfl, ?_⟩

    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [hw, hprod u' fun i => rfl]
    · rw [Over.w w', Over.w]
  · rintro ⟨u'', hu'', rfl⟩
    exact hprod u'' hu''

end GlobalTheory

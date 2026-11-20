import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.TorsionList

/- English proof (translation)
Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem pow_exp (n k : ℕ) (c : Multiplicative (Fin k → ZMod n)) : c ^ n = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp

/- English proof (translation)
Simplify using `[spMap]`.
-/
theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap]

/- English proof (translation)
Use `⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ?_), fun y => ?_⟩` and prove the remaining obligations. Conclude with `(Over.w x).trans (Over.w y).symm`. Conclude with `⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩`.
-/
theorem pushHom_bij {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ?_), fun y => ?_⟩
  · exact (Over.w x).trans (Over.w y).symm
  · exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

/- English proof (translation)
Simplify using `only [spMap_comp, Category.assoc]`.
-/
theorem spMap_comp_assoc {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] {X : Scheme.{0}}
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (y : Sp A ⟶ X) :
    spMap (h.comp g) ≫ spMap f ≫ y = spMap h ≫ spMap (g.comp f) ≫ y := by
  simp only [spMap_comp, Category.assoc]

abbrev lft {S X : Scheme.{0}} {G : Over S} {a : X ⟶ S} (p : Over.mk a ⟶ G) : X ⟶ G.left := p.left

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[Over.OverMorphism.ext hx]`.
-/
theorem pow_lft_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (y : Over.mk b ⟶ G) (hx : lft x = lft y) (n : ℕ) : lft (x ^ n) = lft (y ^ n) := by
  subst h
  rw [Over.OverMorphism.ext hx]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem one_lft_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) :
    lft (1 : Over.mk a ⟶ G) = lft (1 : Over.mk b ⟶ G) := by
  subst h
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨p, rfl⟩`.
-/
theorem transport {S X : Scheme.{0}} {G : Over S} {a b : X ⟶ S} (h : a = b) (p : Over.mk b ⟶ G) :
    ∃ p' : Over.mk a ⟶ G, lft p' = lft p := by
  subst h
  exact ⟨p, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lft_pushHom {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {X : Scheme.{0}} (t : X ⟶ S') (y : Over.mk t ⟶ A') :
    lft (pushHom h (Over.mk t) y) = y.left ≫ φ := rfl

/- English proof (translation)
The claim follows from `(Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk f)))`.
-/
theorem toUnit_mk_left {X Y : Scheme.{0}} (f : Y ⟶ X) : (toUnit (Over.mk f)).left = f :=
  (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk f)))

/- English proof (translation)
The claim follows from `(Category.comp_id _).symm.trans (Over.w (toUnit T))`.
-/
theorem toUnit_left {X : Scheme.{0}} (T : Over X) : (toUnit T).left = T.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit T))

/- English proof (translation)
Introduce `S G _ _ L g m N R _ _ x hm hmu hN hP`. Take `⟨P, α, hg, hp, -⟩` from `hP`. Use `haveI := P.isAb.comm`. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact absurd hm (by decide)`. Use `haveI : NeZero (m ^ 2) := ⟨pow_ne_zero _ hm0⟩`.

Establish `hsm : SmoothOfRelativeDimension g P.A.hom` using `hg ▸ P.smoothDim`. Establish `hu : IsUnit (((m ^ 2 : ℕ)) : R)` using `by rw [Nat.cast_pow]; exact hmu.pow 2`. Take `⟨R₁, _, _, ⟨hfin, -, hff⟩, H⟩` from `GlobalTheory.TorsionCover.exists_torsion_basis_cover R P.A g (m ^ 2) P.isAb hsm hu`. Set `b` to `spMap (algebraMap R R₁)`. Set `A₁` to `(Over.pullback b).obj P.A`.

Use `haveI : IsCommMonObj A₁ := Functor.isCommMonObj_obj`. Establish `h₁` using `isGrpPullback_pullback P.A b`. Take `⟨ψ, hψ⟩` from `H A₁ _ h₁`. Establish `hc` using `h₁.comp hp`. Establish `hcard : Fintype.card (Multiplicative (Fin (2 * g) → ZMod (m ^ 2))) = N`.

Rewrite using `[hN]`. Simplify using `[Fintype.card_fun, ZMod.card, ← pow_mul]`. Put the polynomial expressions in normal form. Set `e` to `(Fintype.equivFinOfCardEq hcard).symm`. Set `U : Over.mk (b ≫ x) ⟶ Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ b ≫ x)` to `Over.homMk (𝟙 _) (by simp)`.

Set `Q` to `(preHom (G := G) U).comp ((pushHom hc (𝟙_ (Over (Sp R₁)))).comp ψ)`. Establish `hQ : ∀ c, (Q c).left = (ψ c).left ≫ pullback.fst P.A.hom b ≫ α` using `fun c => by`. Simplify using `[Q, U, pushHom, pushPt, preHom]`. Use `⟨R₁, inferInstance, inferInstance, fun a => Q (e a), hfin, hff, fun a => by` and prove the remaining obligations. Rewrite using `[← map_pow, pow_exp, map_one], ?_⟩`.

Introduce `K _ i₁ pt hpt`. Establish `key : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R₁) c d, t ≫ (Q c).left = t ≫ (Q d).left → c = d`. Introduce `k _ _ t c d h`. Establish `hinj : Function.Injective ((preHom (G` using `A₁) (toUnit (Over.mk t))).comp ψ) := by`. Rewrite using `[injective_iff_map_eq_one]`.

Conclude with `fun c hc => (hψ k t).2 c hc`. Apply `hinj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show (toUnit (Over.mk t) ≫ ψ c).left = (toUnit (Over.mk t) ≫ ψ d).left`. Rewrite using `[Over.comp_left, Over.comp_left, toUnit_left]`.

Apply `hc.1.hom_ext` to reduce the goal to its premises. Rewrite `h` using `[hQ, hQ]`. Simplify `h` using `[Category.assoc]`. Establish `e1` using `Over.w (ψ c)`. Establish `e2` using `Over.w (ψ d)`.

Simplify using `only [Category.assoc]`. Use `erw [e1, e2]`. Use `⟨fun a a' h => ?_, ?_⟩` and prove the remaining obligations. Establish `h'` using `congrArg (fun z => z.left) h`. Simplify using `only [hpt] at h'`.

Set `k` to `AlgebraicClosure K`. Use `key k (spMap ((algebraMap K k).comp i₁)) (e a) (e a') (by` as an intermediate fact. Rewrite using `[spMap_comp, Category.assoc, Category.assoc]`. Conclude with `congrArg (spMap (algebraMap K k) ≫ ·) h')`. Conclude with `e.injective this`.

Introduce `K' _ _ i' p hp2`. Establish `ht : spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x = spMap (i'.comp i₁) ≫ b ≫ x` using `(spMap_comp_assoc (algebraMap R R₁) i₁ i' x).symm`. Take `⟨p', hp'⟩` from `transport ht.symm p`. Take `⟨p₁, hp₁⟩` from `(pushHom_bij hc (Over.mk (spMap (i'.comp i₁)))).2 p'`. Establish `hk : p₁ ^ (m ^ 2) = 1`.

Apply `(pushHom_bij hc _).1` to reduce the goal to its premises. Rewrite using `[map_pow, hp₁, map_one]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `lft _ = lft _`. Rewrite using `[pow_lft_congr ht.symm p' p hp', hp2]`.

Conclude with `one_lft_congr ht`. Take `⟨c, rfl⟩` from `((hψ K' _).1 p₁).1 hk`. Use `⟨e.symm c, ?_⟩` and prove the remaining obligations. Rewrite using `[hpt]`. Simplify using `only [Equiv.apply_symm_apply]`.

Express the relevant statement in the definitionally equal form `lft p = _`. Establish `h2` using `congrArg lft hp₁`. Rewrite using `[← hp', ← h2, lft_pushHom, hQ, Over.comp_left, toUnit_mk_left, spMap_comp]`. Simplify using `only [Category.assoc]`.
-/
theorem exists_cover_torsion_list : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ (∀ a, q a ^ (m ^ 2) = 1) ∧ ∀ (K : Type) [Field K] (i₁ : R₁ →+* K) (pt : Fin N → (Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G)), (∀ a, (pt a).left = spMap i₁ ≫ (q a).left) → Function.Injective pt ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i' : K →+* K') (p : Over.mk (spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i' ≫ (pt a).left := by
  intro S G _ _ L g m N R _ _ x hm hmu hN hP
  obtain ⟨P, α, hg, hp, -⟩ := hP
  haveI := P.isAb.comm
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  haveI : NeZero (m ^ 2) := ⟨pow_ne_zero _ hm0⟩
  have hsm : SmoothOfRelativeDimension g P.A.hom := hg ▸ P.smoothDim
  have hu : IsUnit (((m ^ 2 : ℕ)) : R) := by rw [Nat.cast_pow]; exact hmu.pow 2
  obtain ⟨R₁, _, _, ⟨hfin, -, hff⟩, H⟩ :=
    GlobalTheory.TorsionCover.exists_torsion_basis_cover R P.A g (m ^ 2) P.isAb hsm hu
  let b := spMap (algebraMap R R₁)
  let A₁ := (Over.pullback b).obj P.A
  haveI : IsCommMonObj A₁ := Functor.isCommMonObj_obj
  have h₁ := isGrpPullback_pullback P.A b
  obtain ⟨ψ, hψ⟩ := H A₁ _ h₁
  have hc := h₁.comp hp
  have hcard : Fintype.card (Multiplicative (Fin (2 * g) → ZMod (m ^ 2))) = N := by
    rw [hN]
    simp [Fintype.card_fun, ZMod.card, ← pow_mul]
    ring_nf
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let U : Over.mk (b ≫ x) ⟶ Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ b ≫ x) := Over.homMk (𝟙 _) (by simp)
  let Q := (preHom (G := G) U).comp ((pushHom hc (𝟙_ (Over (Sp R₁)))).comp ψ)
  have hQ : ∀ c, (Q c).left = (ψ c).left ≫ pullback.fst P.A.hom b ≫ α := fun c => by
    simp [Q, U, pushHom, pushPt, preHom]
  refine ⟨R₁, inferInstance, inferInstance, fun a => Q (e a), hfin, hff, fun a => by
    rw [← map_pow, pow_exp, map_one], ?_⟩
  intro K _ i₁ pt hpt
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R₁) c d,
      t ≫ (Q c).left = t ≫ (Q d).left → c = d := by
    intro k _ _ t c d h
    have hinj : Function.Injective ((preHom (G := A₁) (toUnit (Over.mk t))).comp ψ) := by
      rw [injective_iff_map_eq_one]
      exact fun c hc => (hψ k t).2 c hc
    apply hinj
    apply Over.OverMorphism.ext
    show (toUnit (Over.mk t) ≫ ψ c).left = (toUnit (Over.mk t) ≫ ψ d).left
    rw [Over.comp_left, Over.comp_left, toUnit_left]
    apply hc.1.hom_ext
    · rw [hQ, hQ] at h
      simpa [Category.assoc] using h
    · have e1 := Over.w (ψ c)
      have e2 := Over.w (ψ d)
      simp only [Category.assoc]
      erw [e1, e2]
  refine ⟨fun a a' h => ?_, ?_⟩
  · have h' := congrArg (fun z => z.left) h
    simp only [hpt] at h'
    let k := AlgebraicClosure K
    have := key k (spMap ((algebraMap K k).comp i₁)) (e a) (e a') (by
      rw [spMap_comp, Category.assoc, Category.assoc]; exact congrArg (spMap (algebraMap K k) ≫ ·) h')
    exact e.injective this
  · intro K' _ _ i' p hp2
    have ht : spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x = spMap (i'.comp i₁) ≫ b ≫ x :=
      (spMap_comp_assoc (algebraMap R R₁) i₁ i' x).symm
    obtain ⟨p', hp'⟩ := transport ht.symm p
    obtain ⟨p₁, hp₁⟩ := (pushHom_bij hc (Over.mk (spMap (i'.comp i₁)))).2 p'
    have hk : p₁ ^ (m ^ 2) = 1 := by
      apply (pushHom_bij hc _).1
      rw [map_pow, hp₁, map_one]
      apply Over.OverMorphism.ext
      change lft _ = lft _
      rw [pow_lft_congr ht.symm p' p hp', hp2]
      exact one_lft_congr ht
    obtain ⟨c, rfl⟩ := ((hψ K' _).1 p₁).1 hk
    refine ⟨e.symm c, ?_⟩
    rw [hpt]
    simp only [Equiv.apply_symm_apply]
    change lft p = _
    have h2 := congrArg lft hp₁
    rw [← hp', ← h2, lft_pushHom, hQ, Over.comp_left, toUnit_mk_left, spMap_comp]
    simp only [Category.assoc]

end GlobalTheory.UMin.TorsionList

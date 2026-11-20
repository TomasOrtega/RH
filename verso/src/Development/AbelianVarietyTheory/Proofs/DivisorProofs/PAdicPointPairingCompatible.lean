import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.RetractionModules

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P : Point p v O Λ}
  {X : Scheme.{0}} {G : Over X} [GrpObj G] {yb : Sp O ⟶ X} {π : P.G.left ⟶ G.left}

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (hπ.1.hom_ext h ((Over.w f).trans (Over.w g).symm))`.
-/
theorem hom_ext_pb (hπ : IsGrpPullback P.G G yb π) {R : Type} [CommRing R] [Algebra O R]
    {f g : specO O R ⟶ P.G} (h : f.left ≫ π = g.left ≫ π) : f = g :=
  Over.OverMorphism.ext (hπ.1.hom_ext h ((Over.w f).trans (Over.w g).symm))

/- English proof (translation)
Assemble the required witnesses or components as `⟨Over.homMk (hπ.1.lift u (spMap (algebraMap O R)) hu) (hπ.1.lift_snd _ _ hu), hπ.1.lift_fst _ _ hu⟩`.
-/
theorem exists_lift (hπ : IsGrpPullback P.G G yb π) {R : Type} [CommRing R] [Algebra O R]
    (u : Sp R ⟶ G.left) (hu : u ≫ G.hom = spMap (algebraMap O R) ≫ yb) :
    ∃ f : specO O R ⟶ P.G, f.left ≫ π = u :=
  ⟨Over.homMk (hπ.1.lift u (spMap (algebraMap O R)) hu) (hπ.1.lift_snd _ _ hu), hπ.1.lift_fst _ _ hu⟩

/- English proof (translation)
Set `x₀ : Over.mk (T.hom ≫ yb) ⟶ G` to `Over.homMk ((1 : T ⟶ P.G).left ≫ π) (by`. Rewrite using `[Category.assoc, hπ.1.w, ← Category.assoc, Over.w]`. Use the proof step `rfl)`. Establish `h` using `hπ.2 T 1 1 x₀ x₀ rfl rfl`. Establish `h2 : x₀ * x₀ = x₀` using `by ext1`.

Rewrite using `[h, _root_.mul_one]`. Both sides reduce to the same expression. Establish `h3 : (x₀ : Over.mk (T.hom ≫ yb) ⟶ G) = 1` using `mul_eq_left.1 h2`. Conclude with `congrArg (fun f : Over.mk (T.hom ≫ yb) ⟶ G => f.left) h3`.
-/
theorem one_left_comp (hπ : IsGrpPullback P.G G yb π) (T : Over (Sp O)) :
    (1 : T ⟶ P.G).left ≫ π = (1 : Over.mk (T.hom ≫ yb) ⟶ G).left := by
  let x₀ : Over.mk (T.hom ≫ yb) ⟶ G := Over.homMk ((1 : T ⟶ P.G).left ≫ π) (by
    rw [Category.assoc, hπ.1.w, ← Category.assoc, Over.w]; rfl)
  have h := hπ.2 T 1 1 x₀ x₀ rfl rfl
  have h2 : x₀ * x₀ = x₀ := by
    ext1
    rw [h, _root_.mul_one]
    rfl
  have h3 : (x₀ : Over.mk (T.hom ≫ yb) ⟶ G) = 1 := mul_eq_left.1 h2
  exact congrArg (fun f : Over.mk (T.hom ≫ yb) ⟶ G => f.left) h3

end GlobalTheory.FlatModel.RetractionModules

namespace GlobalTheory.FlatModel.RetractionModules

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P : Point p v O Λ}
  {X : Scheme.{0}} {yb : Sp O ⟶ X}

/- English proof (translation)
Rewrite using `[one_left_comp hπ (specO O O)]`. Express the relevant statement in the definitionally equal form `((specO O O).hom ≫ yb) ≫ _ = yb ≫ _`. Rewrite using `[show (specO O O).hom = 𝟙 _ from ?_, Category.id_comp]`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (algebraMap O O)) = _`. Rewrite using `[Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]`.

Both sides reduce to the same expression.
-/
theorem one_left_mk {G : Over X} [GrpObj G] {π : P.G.left ⟶ G.left} (hπ : IsGrpPullback P.G G yb π) :
    (1 : specO O O ⟶ P.G).left ≫ π = (1 : Over.mk yb ⟶ G).left := by
  rw [one_left_comp hπ (specO O O)]
  change ((specO O O).hom ≫ yb) ≫ _ = yb ≫ _
  rw [show (specO O O).hom = 𝟙 _ from ?_, Category.id_comp]
  change Spec.map (CommRingCat.ofHom (algebraMap O O)) = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rfl

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {t : SAB H X}
  {π : P.G.left ⟶ t.G.left}

/- English proof (translation)
Take `⟨f, hf⟩` from `exists_lift hπ u hu.1`. Use `⟨⟨f, hom_ext_pb hπ ?_⟩, hf⟩` and prove the remaining obligations. Rewrite using `[Over.comp_left, Category.assoc, hf]`. Conclude with `hu.2.trans (one_left_mk hπ).symm`.
-/
theorem tan_lift (hπ : IsGrpPullback P.G t.G yb π) {u : Sp (DualNumber O) ⟶ t.G.left} (hu : IsTanAtG t yb u) :
    ∃ xG : LieG P.G, xG.1.left ≫ π = u := by
  obtain ⟨f, hf⟩ := exists_lift hπ u hu.1
  refine ⟨⟨f, hom_ext_pb hπ ?_⟩, hf⟩
  rw [Over.comp_left, Category.assoc, hf]
  exact hu.2.trans (one_left_mk hπ).symm

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hπ.1.w, ← Category.assoc, Over.w]`. Both sides reduce to the same expression. Rewrite using `[← Category.assoc, ← one_left_mk hπ]`. Express the relevant statement in the definitionally equal form `(ptMap (TrivSqZeroExt.fstHom O O O) ≫ xG.1).left ≫ π = _`.

Rewrite using `[xG.2]`. Both sides reduce to the same expression.
-/
theorem tan_of_lie (hπ : IsGrpPullback P.G t.G yb π) (xG : LieG P.G) : IsTanAtG t yb (xG.1.left ≫ π) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hπ.1.w, ← Category.assoc, Over.w]
    rfl
  · rw [← Category.assoc, ← one_left_mk hπ]
    change (ptMap (TrivSqZeroExt.fstHom O O O) ≫ xG.1).left ≫ π = _
    rw [xG.2]
    rfl

end Tan

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

/- English proof (translation)
Use `haveI := P.isLocalRing`. Use `haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)`. Establish `hp : ¬ IsUnit (p : DualNumber O)` using `fun h => (Fact.out : ¬ IsUnit (p : O)) (by simpa using h.map (TrivSqZeroExt.fstHom O O O))`. Conclude with `(existsUnique_left hp (isAdicComplete_dualNumber p) y).unique h h'`.
-/
theorem corr_left_unique {x x' : specO O (DualNumber O) ⟶ P.Gt} {y : specO O (DualNumber O) ⟶ P.G}
    (h : Corr P x y) (h' : Corr P x' y) : x = x' := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp : ¬ IsUnit (p : DualNumber O) := fun h =>
    (Fact.out : ¬ IsUnit (p : O)) (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  exact (existsUnique_left hp (isAdicComplete_dualNumber p) y).unique h h'

/- English proof (translation)
Use `haveI := P.isLocalRing`. Use `haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)`. Establish `hp : ¬ IsUnit (p : DualNumber O)` using `fun h => (Fact.out : ¬ IsUnit (p : O)) (by simpa using h.map (TrivSqZeroExt.fstHom O O O))`. Conclude with `(existsUnique_right hp (isAdicComplete_dualNumber p) x).unique h h'`.
-/
theorem corr_right_unique {x : specO O (DualNumber O) ⟶ P.Gt} {y y' : specO O (DualNumber O) ⟶ P.G}
    (h : Corr P x y) (h' : Corr P x y') : y = y' := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp : ¬ IsUnit (p : DualNumber O) := fun h =>
    (Fact.out : ¬ IsUnit (p : O)) (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  exact (existsUnique_right hp (isAdicComplete_dualNumber p) x).unique h h'

/- English proof (translation)
Use `haveI := P.isLocalRing`. Use `haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)`. Establish `hp₀ : ¬ IsUnit (p : O)` using `Fact.out`. Establish `hp : ¬ IsUnit (p : DualNumber O)` using `fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))`. Take `⟨x, hx, -⟩` from `existsUnique_left (P := P) hp (isAdicComplete_dualNumber p) xG.1`.

Use `⟨⟨x, (existsUnique_left (P := P) hp₀ inferInstance 1).unique ?_ Corr.one⟩, hx⟩` and prove the remaining obligations. Establish `h` using `hx.comp (TrivSqZeroExt.fstHom O O O)`. Rewrite `h` using `[xG.2]`. Conclude with `h`.
-/
theorem exists_corr_left (xG : LieG P.G) : ∃ x : LieG P.Gt, Corr P x.1 xG.1 := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  obtain ⟨x, hx, -⟩ := existsUnique_left (P := P) hp (isAdicComplete_dualNumber p) xG.1
  refine ⟨⟨x, (existsUnique_left (P := P) hp₀ inferInstance 1).unique ?_ Corr.one⟩, hx⟩
  have h := hx.comp (TrivSqZeroExt.fstHom O O O)
  rw [xG.2] at h
  exact h

/- English proof (translation)
Use `haveI := P.isLocalRing`. Use `haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)`. Establish `hp₀ : ¬ IsUnit (p : O)` using `Fact.out`. Establish `hp : ¬ IsUnit (p : DualNumber O)` using `fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))`. Take `⟨y, hy, -⟩` from `existsUnique_right (P := P) hp (isAdicComplete_dualNumber p) x.1`.

Use `⟨⟨y, (existsUnique_right (P := P) hp₀ inferInstance 1).unique ?_ Corr.one⟩, hy⟩` and prove the remaining obligations. Establish `h` using `hy.comp (TrivSqZeroExt.fstHom O O O)`. Rewrite `h` using `[x.2]`. Conclude with `h`.
-/
theorem exists_corr_right (x : LieG P.Gt) : ∃ xG : LieG P.G, Corr P x.1 xG.1 := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  obtain ⟨y, hy, -⟩ := existsUnique_right (P := P) hp (isAdicComplete_dualNumber p) x.1
  refine ⟨⟨y, (existsUnique_right (P := P) hp₀ inferInstance 1).unique ?_ Corr.one⟩, hy⟩
  have h := hy.comp (TrivSqZeroExt.fstHom O O O)
  rw [x.2] at h
  exact h

end GlobalTheory.FlatModel.RetractionModules

namespace GlobalTheory.FlatModel.RetractionModules

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P : Point p v O Λ}
  {X : Scheme.{0}} {yb : Sp O ⟶ X}

/- English proof (translation)
The claim follows from `| 0, _, _, _ => by simp only [List.ofFn_zero, List.prod_nil] exact (one_left_comp hπ T).symm | m + 1, ws, w, h => by rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons] exact hπ.2 T _ _ _ _ (h 0) (prod_left_comp hπ (fun i => ws i.succ) (fun i => w i.succ) fun i => …`.
-/
theorem prod_left_comp {G : Over X} [GrpObj G] {π : P.G.left ⟶ G.left} (hπ : IsGrpPullback P.G G yb π)
    {T : Over (Sp O)} : ∀ {m : ℕ} (ws : Fin m → (T ⟶ P.G)) (w : Fin m → (Over.mk (T.hom ≫ yb) ⟶ G)),
      (∀ i, (w i).left = (ws i).left ≫ π) → ((List.ofFn w).prod).left = ((List.ofFn ws).prod).left ≫ π
  | 0, _, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil]
    exact (one_left_comp hπ T).symm
  | m + 1, ws, w, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact hπ.2 T _ _ _ _ (h 0) (prod_left_comp hπ (fun i => ws i.succ) (fun i => w i.succ) fun i => h i.succ)

/- English proof (translation)
The claim follows from `| 0, _, _, _ => by simp only [List.ofFn_zero, List.prod_nil] exact Corr.one | m + 1, xs, ys, h => by rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons] exact (h 0).mul (corr_prod (fun i => xs i.succ) (fun i => ys i.succ) fun i => h i.succ)`.
-/
theorem corr_prod {R : Type} [CommRing R] [Algebra O R] : ∀ {m : ℕ} (xs : Fin m → (specO O R ⟶ P.Gt))
    (ys : Fin m → (specO O R ⟶ P.G)), (∀ i, Corr P (xs i) (ys i)) → Corr P (List.ofFn xs).prod (List.ofFn ys).prod
  | 0, _, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil]
    exact Corr.one
  | m + 1, xs, ys, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact (h 0).mul (corr_prod (fun i => xs i.succ) (fun i => ys i.succ) fun i => h i.succ)

noncomputable def combLie (G : Over (Sp O)) [GrpObj G] : ∀ m : ℕ, (Fin m → O) → (Fin m → LieG G) → LieG G
  | 0, _, _ => lieZero G
  | m + 1, cf, xs => lieAdd (AvDefs.lieScale G (cf 0) (xs 0)) (combLie G m (fun i => cf i.succ) fun i => xs i.succ)

/- English proof (translation)
The claim follows from `| 0, _, _ => rfl | m + 1, cf, xs => by rw [List.ofFn_succ, List.prod_cons, ← combLie_val G m] rfl`.
-/
theorem combLie_val (G : Over (Sp O)) [GrpObj G] : ∀ (m : ℕ) (cf : Fin m → O) (xs : Fin m → LieG G),
    (combLie G m cf xs).1 = (List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xs i).1).prod
  | 0, _, _ => rfl
  | m + 1, cf, xs => by
    rw [List.ofFn_succ, List.prod_cons, ← combLie_val G m]
    rfl

/- English proof (translation)
The claim follows from `| 0, _, _ => by simp [combLie, P.bLie_zero] | m + 1, cf, xs => by rw [combLie, P.bLie_add, P.bLie_scale, bLie_combLie P m, Fin.sum_univ_succ] congr 1`.
-/
theorem bLie_combLie {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : PtP E p) :
    ∀ (m : ℕ) (cf : Fin m → 𝓞_ℂ_[p]) (xs : Fin m → LieG P.Gt),
      P.bLie (combLie P.Gt m cf xs) = ∑ i, (cf i : ℂ_[p]) • P.bLie (xs i)
  | 0, _, _ => by simp [combLie, P.bLie_zero]
  | m + 1, cf, xs => by
    rw [combLie, P.bLie_add, P.bLie_scale, bLie_combLie P m, Fin.sum_univ_succ]
    congr 1

end GlobalTheory.FlatModel.RetractionModules

namespace GlobalTheory.FlatModel

open RetractionModules in

/- English proof (translation)
Introduce `E _ _ _ H Dw p _ _ l' Xo' c' W Y yb yy P π ψ hP`. Establish `hπ` using `hP.2.1`. Use `⟨fun u hu => ?_, fun x => ?_, fun m vv xs cf u x _ hxs hu hx => ?_, fun σ x u _ hx => ?_⟩` and prove the remaining obligations. Take `⟨xG, hxG⟩` from `tan_lift hπ hu`. Take `⟨x, hx⟩` from `exists_corr_left xG`.

Use `⟨x, ⟨xG, hx, hxG⟩, fun x' hx' => ?_⟩` and prove the remaining obligations. Take `⟨xG', hc', hxG'⟩` from `hx'`. Establish `e : xG'.1 = xG.1` using `hom_ext_pb hπ (hxG'.trans hxG.symm)`. Rewrite `hc'` using `[e]`. Conclude with `Subtype.ext (corr_left_unique hc' hx)`.

Take `⟨xG, hx⟩` from `exists_corr_right x`. Conclude with `⟨xG.1.left ≫ π, tan_of_lie hπ xG, xG, hx, rfl⟩`. Use `choose xG hxc hxG using hxs`. Take `⟨w, hw, hwu⟩` from `hu`. Take `⟨yG, hyc, hyG⟩` from `hx`.

Establish `h1 : ((List.ofFn w).prod).left = ((List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xG i).1).prod).left ≫ π` using `prod_left_comp hπ (T := specO 𝓞_ℂ_[p] (DualNumber 𝓞_ℂ_[p])) (fun i => ptMap (dualScale (cf i)) ≫ (xG i).1) w fun i => by`. Rewrite using `[hw i, Over.comp_left, Category.assoc, hxG i]`. Both sides reduce to the same expression. Establish `h2 : yG.1 = (List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xG i).1).prod` using `hom_ext_pb hπ (hyG.trans (hwu.symm.trans h1))`. Establish `h3 : Corr P (combLie P.Gt m cf xs).1 yG.1`.

Rewrite using `[combLie_val, h2]`. Conclude with `corr_prod _ _ fun i => (hxc i).comp (dualScale (cf i))`. Establish `h4 : x = combLie P.Gt m cf xs` using `Subtype.ext (corr_left_unique hyc h3)`. Rewrite using `[h4, bLie_combLie]`. Take `⟨xG, hxc, hxG⟩` from `hx`.

Establish `hact : ∀ a, (P.oG.act a).left ≫ π = π ≫ (Y.t.act.act a).left` using `hP.2.2.1`. Establish `tA : ∀ a, (xG.1 ≫ P.oG.act a).left ≫ π = u ≫ (Y.t.act.act a).left` using `fun a => by`. Rewrite using `[Over.comp_left, Category.assoc, hact, ← Category.assoc, hxG]`. Establish `tS : ∀ a, (ptMap (dualScale (σ a)) ≫ xG.1).left ≫ π = spMap (epsMul (σ a)) ≫ u` using `fun a => by`. Rewrite using `[Over.comp_left, Category.assoc, hxG]`.

Both sides reduce to the same expression. Establish `cA : ∀ a, Corr P (AvDefs.lieAct P.Gt P.oGt a x).1 (xG.1 ≫ P.oG.act a)` using `fun a => corr_act hxc a`. Establish `cS : ∀ a, Corr P (AvDefs.lieScale P.Gt (σ a) x).1 (ptMap (dualScale (σ a)) ≫ xG.1)` using `fun a => hxc.comp _`. Prove the components needed by the constructor for the conclusion. Introduce `h a`.

Establish `e` using `hom_ext_pb hπ ((tA a).trans ((h a).trans (tS a).symm))`. Establish `c2` using `cA a`. Rewrite `c2` using `[e]`. Conclude with `Subtype.ext (corr_left_unique c2 (cS a))`. Introduce `h a`.

Establish `c2` using `cS a`. Rewrite `c2` using `[← h a]`. Establish `e` using `corr_right_unique (cA a) c2`. Rewrite using `[← tA a, ← tS a, e]`.
-/
theorem tanTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)] (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    (∀ u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left, IsTanAtG Y.t yb u → ∃! x : LieG P.Gt, ITie P π x u) ∧
    (∀ x : LieG P.Gt, ∃ u, IsTanAtG Y.t yb u ∧ ITie P π x u) ∧
    (∀ (m : ℕ) (v : Fin m → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (xs : Fin m → LieG P.Gt) (cf : Fin m → 𝓞_ℂ_[p])
      (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left) (x : LieG P.Gt), (∀ i, IsTanAtG Y.t yb (v i)) →
      (∀ i, ITie P π (xs i) (v i)) → IsCombAtG Y.t yb v cf u → ITie P π x u →
      P.bLie x = ∑ i, (cf i : ℂ_[p]) • P.bLie (xs i)) ∧
    ∀ (σ : 𝓞 E →+* 𝓞_ℂ_[p]) (x : LieG P.Gt) (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left), IsTanAtG Y.t yb u →
      ITie P π x u → (IsEigG Y.t σ u ↔ AvDefs.IsEig P.Gt P.oGt σ x) := by
  intro E _ _ _ H Dw p _ _ l' Xo' c' W Y yb yy P π ψ hP
  have hπ := hP.2.1
  refine ⟨fun u hu => ?_, fun x => ?_, fun m vv xs cf u x _ hxs hu hx => ?_, fun σ x u _ hx => ?_⟩
  · obtain ⟨xG, hxG⟩ := tan_lift hπ hu
    obtain ⟨x, hx⟩ := exists_corr_left xG
    refine ⟨x, ⟨xG, hx, hxG⟩, fun x' hx' => ?_⟩
    obtain ⟨xG', hc', hxG'⟩ := hx'
    have e : xG'.1 = xG.1 := hom_ext_pb hπ (hxG'.trans hxG.symm)
    rw [e] at hc'
    exact Subtype.ext (corr_left_unique hc' hx)
  · obtain ⟨xG, hx⟩ := exists_corr_right x
    exact ⟨xG.1.left ≫ π, tan_of_lie hπ xG, xG, hx, rfl⟩
  · choose xG hxc hxG using hxs
    obtain ⟨w, hw, hwu⟩ := hu
    obtain ⟨yG, hyc, hyG⟩ := hx
    have h1 : ((List.ofFn w).prod).left =
        ((List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xG i).1).prod).left ≫ π :=
      prod_left_comp hπ (T := specO 𝓞_ℂ_[p] (DualNumber 𝓞_ℂ_[p]))
        (fun i => ptMap (dualScale (cf i)) ≫ (xG i).1) w fun i => by
        rw [hw i, Over.comp_left, Category.assoc, hxG i]
        rfl
    have h2 : yG.1 = (List.ofFn fun i => ptMap (dualScale (cf i)) ≫ (xG i).1).prod :=
      hom_ext_pb hπ (hyG.trans (hwu.symm.trans h1))
    have h3 : Corr P (combLie P.Gt m cf xs).1 yG.1 := by
      rw [combLie_val, h2]
      exact corr_prod _ _ fun i => (hxc i).comp (dualScale (cf i))
    have h4 : x = combLie P.Gt m cf xs := Subtype.ext (corr_left_unique hyc h3)
    rw [h4, bLie_combLie]
  · obtain ⟨xG, hxc, hxG⟩ := hx
    have hact : ∀ a, (P.oG.act a).left ≫ π = π ≫ (Y.t.act.act a).left := hP.2.2.1
    have tA : ∀ a, (xG.1 ≫ P.oG.act a).left ≫ π = u ≫ (Y.t.act.act a).left := fun a => by
      rw [Over.comp_left, Category.assoc, hact, ← Category.assoc, hxG]
    have tS : ∀ a, (ptMap (dualScale (σ a)) ≫ xG.1).left ≫ π = spMap (epsMul (σ a)) ≫ u := fun a => by
      rw [Over.comp_left, Category.assoc, hxG]
      rfl
    have cA : ∀ a, Corr P (AvDefs.lieAct P.Gt P.oGt a x).1 (xG.1 ≫ P.oG.act a) := fun a => corr_act hxc a
    have cS : ∀ a, Corr P (AvDefs.lieScale P.Gt (σ a) x).1 (ptMap (dualScale (σ a)) ≫ xG.1) := fun a =>
      hxc.comp _
    constructor
    · intro h a
      have e := hom_ext_pb hπ ((tA a).trans ((h a).trans (tS a).symm))
      have c2 := cA a
      rw [e] at c2
      exact Subtype.ext (corr_left_unique c2 (cS a))
    · intro h a
      have c2 := cS a
      rw [← h a] at c2
      have e := corr_right_unique (cA a) c2
      rw [← tA a, ← tS a, e]

end GlobalTheory.FlatModel

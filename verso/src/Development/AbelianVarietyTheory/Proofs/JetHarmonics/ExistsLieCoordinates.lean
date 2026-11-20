import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersDlogMinorsGe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacter

open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (Pt comp1)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

abbrev specV {V O : Type} [CommRing V] [CommRing O] (f : V →+* O) (A : Type) [CommRing A] [Algebra O A] :
    Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)))

/- English proof (translation)
Use `⟨fun i => const_map (hα.1 i), fun n a y hy => ?_⟩` and prove the remaining obligations. Take `⟨Θ, t, hΘ, ht, e⟩` from `exists_move hπ hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)`. Establish `H` using `hα.2 1 _ _ (ht 0)`. Establish `hFe : comp1 α (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n` using `1) d 0) = α := funext fun i => germEval_oneStandardPoint_self _`. Rewrite `H` using `[hFe]`.

Use `(rep_iff hπ hJ hx' (single_point_zero_constant hy.1) hΘ H _).2 fun m => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← e 0 m]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show ((y m).left ≫ f'.left) ≫ π = ((y m).left ≫ π) ≫ f.left`. Rewrite using `[Category.assoc, Category.assoc, hf]`.
-/
theorem isMapOf_baseChange {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
    {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
    (hJ : JetAlgSt) {d : ℕ} {x : JetSer.Fam G (Fin d)} {x' : JetSer.Fam G' (Fin d)}
    (hx' : ∀ m, push hπ (x' m) = Chart.spMap (jetCoeff R R' (Fin d) m) ≫ x m)
    (f : G ⟶ G) (f' : G' ⟶ G') (α : Pt R 1 d) (hf : f'.left ≫ π = π ≫ f.left) (hα : IsMapOf x x f α) :
    IsMapOf x' x' f' (fun i => MvPowerSeries.map (algebraMap R R') (α i)) := by
  refine ⟨fun i => const_map (hα.1 i), fun n a y hy => ?_⟩
  obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)
  have H := hα.2 1 _ _ (ht 0)
  have hFe : comp1 α (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) = α := funext fun i => germEval_oneStandardPoint_self _
  rw [hFe] at H
  refine (rep_iff hπ hJ hx' (single_point_zero_constant hy.1) hΘ H _).2 fun m => ?_
  rw [← Category.assoc, ← e 0 m]
  apply Over.OverMorphism.ext
  show ((y m).left ≫ f'.left) ≫ π = ((y m).left ≫ π) ≫ f.left
  rw [Category.assoc, Category.assoc, hf]

section Transfer
variable {O : Type} [CommRing O] {Gt G' : Over (Spec (CommRingCat.of O))} [GrpObj Gt] [GrpObj G']
  (K : (specO O (DualNumber O) ⟶ Gt) → (specO O (DualNumber O) ⟶ G'))
  (hmul : ∀ w w', K (w * w') = K w * K w') (hinj : Function.Injective K)
  (hnat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w, K (ptMap φ ≫ w) = ptMap φ ≫ K w)

include hmul hinj hnat in
/- English proof (translation)
Establish `h1 : K 1 = 1`. Use `hmul 1 1` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `left_eq_mul.mp this`. Establish `key : ∀ {G : Over (Spec (CommRingCat.of O))} [GrpObj G] (z : specO O (DualNumber O) ⟶ G), IsTan z ↔ ptMap (scaleD (0 : O)) ≫ z = 1` using `fun z => ⟨fun h => spMap_scaleD_zero h, fun h => by`.

Establish `e : (fstD O).comp (scaleD (0 : O)) = fstD O`. Use `ext`. Conclude with `TrivSqZeroExt.fst_map _ _`. Use `congrArg (Chart.spMap (fstD O) ≫ ·) h` as an intermediate fact. Simplify using `only [MonObj.comp_one] at this`.

Use `Eq.trans ?_ this` and prove the remaining obligations. Use `show _ = Chart.spMap (fstD O) ≫ Chart.spMap (scaleD (0 : O)) ≫ z`. Rewrite using `[← Category.assoc, Chart.spMap_comp, e]⟩`. Rewrite using `[key, key, ← hnat, ← h1]`. Conclude with `hinj.eq_iff.symm`.
-/
theorem isTan_iff (w : specO O (DualNumber O) ⟶ Gt) : IsTan w ↔ IsTan (K w) := by
  have h1 : K 1 = 1 := by
    have := hmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.mp this
  have key : ∀ {G : Over (Spec (CommRingCat.of O))} [GrpObj G] (z : specO O (DualNumber O) ⟶ G),
      IsTan z ↔ ptMap (scaleD (0 : O)) ≫ z = 1 := fun z => ⟨fun h => spMap_scaleD_zero h, fun h => by
    have e : (fstD O).comp (scaleD (0 : O)) = fstD O := by
      ext
      exact TrivSqZeroExt.fst_map _ _
    have := congrArg (Chart.spMap (fstD O) ≫ ·) h
    simp only [MonObj.comp_one] at this
    refine Eq.trans ?_ this
    show _ = Chart.spMap (fstD O) ≫ Chart.spMap (scaleD (0 : O)) ≫ z
    rw [← Category.assoc, Chart.spMap_comp, e]⟩
  rw [key, key, ← hnat, ← h1]
  exact hinj.eq_iff.symm

end Transfer

/- English proof (translation)
Use `letI : Algebra V O := f.toAlgebra`. Use `letI alg : Algebra V (DualNumber O) := ((algebraMap O (DualNumber O)).comp f).toAlgebra`. Use `haveI tow : @IsScalarTower V O (DualNumber O) _ _ alg.toSMul := IsScalarTower.of_algebraMap_eq (R := V) (S := O) (A := DualNumber O) fun _ => rfl`. Set `j` to `Spec.map (CommRingCat.ofHom (algebraMap V O))`. Set `G'` to `(Over.pullback j).obj G`.

Establish `hπ : IsGrpPullback G' G j (pullback.fst G.hom j)` using `isGrpPullback_pullback G j`. Use `choose x' hx' using fun m => push_surjective hπ (Chart.spMap (jetCoeff V O (Fin d) m) ≫ x m)`. Establish `hu` using `isUnivChart_baseChange hπ hx hx'`. Use `choose K hK using fun w => push_surjective (A := DualNumber O) hπ (J w)`. Establish `hK' : ∀ w, (K w).left ≫ pullback.fst G.hom j = (J w).left` using `fun w => congrArg (·.left) (hK w)`.

Establish `Kmul : ∀ w w', K (w * w') = K w * K w'` using `fun w w' => push_injective hπ (by rw [push_mul, hK, hK, hK]; exact hmul w w')`. Establish `Kinj : Function.Injective K` using `fun w w' h => hinj (by rw [← hK, ← hK, h])`. Establish `Knat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w, K (ptMap φ ≫ w) = ptMap φ ≫ K w` using `fun φ w => push_injective hπ (Over.OverMorphism.ext (by`. Rewrite using `[push_left, push_left, hK', hnat, Over.comp_left, Category.assoc, hK']`. Use the proof step `rfl))`.

Establish `htan` using `isTan_iff K Kmul Kinj Knat`. Establish `lie : ∀ w : specO O (DualNumber O) ⟶ Gt, (ptMap (TrivSqZeroExt.fstHom O O O) ≫ w = toUnit (specO O O) ≫ η[Gt]) ↔ IsTan w` using `fun w => Iff.rfl`. Establish `ex : ∀ b : Fin d → O, ∃ w : LieG Gt, K w.1 = Chart.spMap (dualLift b) ≫ x' 1` using `fun b => by`. Take `⟨w, hw⟩` from `hsurj (push hπ (Chart.spMap (dualLift b) ≫ x' 1)) (by`. Establish `h` using `congrArg (·.left ≫ pullback.fst G.hom j) (isTan_dualLift hu b)`.

Establish `h1` using `congrArg (·.left) (push_one (A := DualNumber O) hπ)`. Establish `h2 : Chart.spMap (fstD O) ≫ (1 : sp (R₀` using `O) (DualNumber O) ⟶ G') = 1 := MonObj.comp_one _`. Rewrite `h` using `[← h2]`. Simplify using `only [Over.comp_left, Category.assoc] at h`. Rewrite `h1` using `[push_left]`.

Rewrite `h` using `[h1]`. Conclude with `h)`. Establish `e : K w = Chart.spMap (dualLift b) ≫ x' 1` using `push_injective hπ ((hK w).trans hw)`. Conclude with `⟨⟨w, (lie w).2 ((htan w).2 (e ▸ isTan_dualLift hu b))⟩, e⟩`. Use `choose tv htv using ex`.

Set `co : LieG Gt → Fin d → O` to `fun w => tcoord hu (K w.1) ((htan _).1 ((lie _).1 w.2))`. Establish `hco : ∀ b, co (tv b) = b` using `fun b => tcoord_eq hu _ _ b (htv b)`. Use `⟨co, tv, fun s => ⟨fun w w' h => ?_, fun a w h => ?_⟩, hco, fun b => ?_, ?_⟩` and prove the remaining obligations. Use `tcoord_mul hu ((htan _).1 ((lie _).1 w.2)) ((htan _).1 ((lie _).1 w'.2))` as an intermediate fact. Conclude with `(congrFun (Chart.tcoord_congr hu (Kmul _ _) _ _) s).trans (congrFun this s)`.

Use `tcoord_scale hu a ((htan _).1 ((lie _).1 w.2))` as an intermediate fact. Conclude with `(congrFun (Chart.tcoord_congr hu (Knat _ _) _ _) s).trans (congrFun this s)`. Use `⟨(dualLift b).toRingHom.comp (jetCoeff V O (Fin d) 1).toRingHom, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `show dualLift b (jetCoeff V O (Fin d) 1 (zR 1 i)) = _`. Rewrite using `[jetCoeff_zR, dualLift_zR]`.

Establish `h : (x' 1).left ≫ pullback.fst G.hom j = _` using `congrArg (·.left) (hx' 1)`. Rewrite using `[← hK', htv, Over.comp_left, Category.assoc, h, Over.comp_left, ← Category.assoc, Chart.spMap_left, Chart.spMap_left, ← Spec.map_comp]`. Both sides reduce to the same expression. Introduce `u _ ut α hα hut b a hb`. Set `u' : G' ⟶ G'` to `(Over.pullback j).map u`.

Establish `hu' : u'.left ≫ pullback.fst G.hom j = pullback.fst G.hom j ≫ u.left` using `pullback.lift_fst _ _ _`. Establish `hm` using `isMapOf_baseChange hπ hJ hx' u u' α hu' hα`. Establish `ht` using `(htan _).1 ((lie _).1 (tv b).2)`. Establish `h` using `hD O G' G' d x' x' hu hu u' _ hm (K (tv b).1) ht (Chart.isTan_comp ht u')`. Establish `h2 : dLin (fun i => MvPowerSeries.map (algebraMap V O) (α i)) = (dLin α).map f`.

Use extensionality with `i k`. Simplify using `[dLin, RingHom.algebraMap_toAlgebra]`. Establish `h3 : tcoord hu (K (tv b).1) ht = b` using `hco b`. Rewrite `h` using `[h2, h3, hb]`. Establish `h4` using `tcoord_scale hu a ht`.

Rewrite `h4` using `[h3]`. Apply `Kinj` to reduce the goal to its premises. Rewrite using `[Knat]`. Establish `e1 : K ((tv b).1 ≫ ut) = K (tv b).1 ≫ u'` using `push_injective hπ (Over.OverMorphism.ext (by`. Rewrite using `[push_left, push_left, hK', hut, Over.comp_left, Over.comp_left, Category.assoc, hu', ← Category.assoc, hK']))`.

Rewrite using `[e1, tcoord_spec hu _ (Chart.isTan_comp ht u'), h, ← h4]`. Conclude with `(tcoord_spec hu _ _).symm`.
-/
theorem exists_lie_coordinates (hJ : JetAlgSt) (hD : DLinSt) {V O : Type} [CommRing V] [IsLocalRing V] [CommRing O]
    (f : V →+* O) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] {d : ℕ} (x : JetSer.Fam G (Fin d))
    (hx : IsUnivChart G d x) (Gt : Over (Spec (CommRingCat.of O))) [GrpObj Gt]
    (J : (specO O (DualNumber O) ⟶ Gt) → (specV f (DualNumber O) ⟶ G))
    (hmul : ∀ w w', J (w * w') = J w * J w') (hinj : Function.Injective J)
    (hnat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w,
      (J (ptMap φ ≫ w)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J w).left)
    (hsurj : ∀ g : specV f (DualNumber O) ⟶ G, Spec.map (CommRingCat.ofHom (fstD O).toRingHom) ≫ g.left =
      Spec.map (CommRingCat.ofHom (fstD O).toRingHom) ≫ (1 : specV f (DualNumber O) ⟶ G).left → ∃ w, J w = g) :
    ∃ (co : LieG Gt → Fin d → O) (tv : (Fin d → O) → LieG Gt), (∀ s, (fun w => co w s) ∈ omega Gt) ∧
      (∀ b, co (tv b) = b) ∧
      (∀ b, ∃ φ : JetR V (Fin d) 1 →+* DualNumber O, (∀ i, φ (zR 1 i) = TrivSqZeroExt.inr (b i)) ∧
        (J (tv b).1).left = Spec.map (CommRingCat.ofHom φ) ≫ (x 1).left) ∧
      ∀ (u : G ⟶ G) [IsMonHom u] (ut : Gt ⟶ Gt) (α : Pt V 1 d), IsMapOf x x u α → (∀ w, J (w ≫ ut) = J w ≫ u) →
        ∀ (b : Fin d → O) (a : O), ((dLin α).map f).mulVec b = a • b →
          (tv b).1 ≫ ut = ptMap (dualScale a) ≫ (tv b).1 := by
  letI : Algebra V O := f.toAlgebra
  letI alg : Algebra V (DualNumber O) := ((algebraMap O (DualNumber O)).comp f).toAlgebra
  haveI tow : @IsScalarTower V O (DualNumber O) _ _ alg.toSMul :=
    IsScalarTower.of_algebraMap_eq (R := V) (S := O) (A := DualNumber O) fun _ => rfl
  let j := Spec.map (CommRingCat.ofHom (algebraMap V O))
  let G' := (Over.pullback j).obj G
  have hπ : IsGrpPullback G' G j (pullback.fst G.hom j) := isGrpPullback_pullback G j
  choose x' hx' using fun m => push_surjective hπ (Chart.spMap (jetCoeff V O (Fin d) m) ≫ x m)
  have hu := isUnivChart_baseChange hπ hx hx'
  choose K hK using fun w => push_surjective (A := DualNumber O) hπ (J w)
  have hK' : ∀ w, (K w).left ≫ pullback.fst G.hom j = (J w).left := fun w => congrArg (·.left) (hK w)
  have Kmul : ∀ w w', K (w * w') = K w * K w' := fun w w' =>
    push_injective hπ (by rw [push_mul, hK, hK, hK]; exact hmul w w')
  have Kinj : Function.Injective K := fun w w' h => hinj (by rw [← hK, ← hK, h])
  have Knat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w, K (ptMap φ ≫ w) = ptMap φ ≫ K w := fun φ w =>
    push_injective hπ (Over.OverMorphism.ext (by
      rw [push_left, push_left, hK', hnat, Over.comp_left, Category.assoc, hK']; rfl))
  have htan := isTan_iff K Kmul Kinj Knat
  have lie : ∀ w : specO O (DualNumber O) ⟶ Gt,
      (ptMap (TrivSqZeroExt.fstHom O O O) ≫ w = toUnit (specO O O) ≫ η[Gt]) ↔ IsTan w := fun w => Iff.rfl
  have ex : ∀ b : Fin d → O, ∃ w : LieG Gt, K w.1 = Chart.spMap (dualLift b) ≫ x' 1 := fun b => by
    obtain ⟨w, hw⟩ := hsurj (push hπ (Chart.spMap (dualLift b) ≫ x' 1)) (by
      have h := congrArg (·.left ≫ pullback.fst G.hom j) (isTan_dualLift hu b)
      have h1 := congrArg (·.left) (push_one (A := DualNumber O) hπ)
      have h2 : Chart.spMap (fstD O) ≫ (1 : sp (R₀ := O) (DualNumber O) ⟶ G') = 1 := MonObj.comp_one _
      rw [← h2] at h
      simp only [Over.comp_left, Category.assoc] at h
      rw [push_left] at h1
      rw [h1] at h
      exact h)
    have e : K w = Chart.spMap (dualLift b) ≫ x' 1 := push_injective hπ ((hK w).trans hw)
    exact ⟨⟨w, (lie w).2 ((htan w).2 (e ▸ isTan_dualLift hu b))⟩, e⟩
  choose tv htv using ex
  let co : LieG Gt → Fin d → O := fun w => tcoord hu (K w.1) ((htan _).1 ((lie _).1 w.2))
  have hco : ∀ b, co (tv b) = b := fun b => tcoord_eq hu _ _ b (htv b)
  refine ⟨co, tv, fun s => ⟨fun w w' h => ?_, fun a w h => ?_⟩, hco, fun b => ?_, ?_⟩
  · have := tcoord_mul hu ((htan _).1 ((lie _).1 w.2)) ((htan _).1 ((lie _).1 w'.2))
    exact (congrFun (Chart.tcoord_congr hu (Kmul _ _) _ _) s).trans (congrFun this s)
  · have := tcoord_scale hu a ((htan _).1 ((lie _).1 w.2))
    exact (congrFun (Chart.tcoord_congr hu (Knat _ _) _ _) s).trans (congrFun this s)
  · refine ⟨(dualLift b).toRingHom.comp (jetCoeff V O (Fin d) 1).toRingHom, fun i => ?_, ?_⟩
    · show dualLift b (jetCoeff V O (Fin d) 1 (zR 1 i)) = _
      rw [jetCoeff_zR, dualLift_zR]
    · have h : (x' 1).left ≫ pullback.fst G.hom j = _ := congrArg (·.left) (hx' 1)
      rw [← hK', htv, Over.comp_left, Category.assoc, h, Over.comp_left, ← Category.assoc, Chart.spMap_left, Chart.spMap_left, ← Spec.map_comp]
      rfl
  · intro u _ ut α hα hut b a hb
    let u' : G' ⟶ G' := (Over.pullback j).map u
    have hu' : u'.left ≫ pullback.fst G.hom j = pullback.fst G.hom j ≫ u.left := pullback.lift_fst _ _ _
    have hm := isMapOf_baseChange hπ hJ hx' u u' α hu' hα
    have ht := (htan _).1 ((lie _).1 (tv b).2)
    have h := hD O G' G' d x' x' hu hu u' _ hm (K (tv b).1) ht (Chart.isTan_comp ht u')
    have h2 : dLin (fun i => MvPowerSeries.map (algebraMap V O) (α i)) = (dLin α).map f := by
      ext i k
      simp [dLin, RingHom.algebraMap_toAlgebra]
    have h3 : tcoord hu (K (tv b).1) ht = b := hco b
    rw [h2, h3, hb] at h
    have h4 := tcoord_scale hu a ht
    rw [h3] at h4
    apply Kinj
    rw [Knat]
    have e1 : K ((tv b).1 ≫ ut) = K (tv b).1 ≫ u' := push_injective hπ (Over.OverMorphism.ext (by
      rw [push_left, push_left, hK', hut, Over.comp_left, Over.comp_left, Category.assoc, hu', ← Category.assoc, hK']))
    rw [e1, tcoord_spec hu _ (Chart.isTan_comp ht u'), h, ← h4]
    exact (tcoord_spec hu _ _).symm

end GlobalTheory.TorsionCharacter

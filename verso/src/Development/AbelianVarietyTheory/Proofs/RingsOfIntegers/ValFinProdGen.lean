import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsValGenHasVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.QBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

def kap (ξ : Spec (CommRingCat.of (FractionRing V))) :
    FractionRing V →+* (Spec (CommRingCat.of (FractionRing V))).presheaf.stalk ξ :=
  ((Spec (CommRingCat.of (FractionRing V))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

omit [IsDiscreteValuationRing V] in
/- English proof (translation)
Rewrite using `[gs_eq _ ξ ⊤ trivial]`. Both sides reduce to the same expression.
-/
theorem gs_scal (ξ : Spec (CommRingCat.of (FractionRing V))) (c : FractionRing V) :
    gs (𝟙 _) ξ ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) = kap ξ c := by
  rw [gs_eq _ ξ ⊤ trivial]
  rfl

def SV (ϖ : V) (ξ : Spec (CommRingCat.of (FractionRing V)))
    (s : ((Spec (CommRingCat.of (FractionRing V))).presheaf.stalk ξ)ˣ) (n : ℤ) : Prop :=
  ∃ c, HasVal ϖ c n ∧ s.val = kap ξ c

/- English proof (translation)
Take `⟨c, ⟨u, hu⟩, hc⟩` from `hs`. Take `⟨d, ⟨v, hv⟩, hd⟩` from `ht`. Use `⟨c * d, ⟨u * v, ?_⟩, by rw [Units.val_mul, hc, hd, map_mul]⟩` and prove the remaining obligations. Rewrite using `[hu, hv, zpow_add₀ ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero), Units.val_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem SV.mul (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {s t} {n m : ℤ}
    (hs : SV ϖ ξ s n) (ht : SV ϖ ξ t m) : SV ϖ ξ (s * t) (n + m) := by
  obtain ⟨c, ⟨u, hu⟩, hc⟩ := hs
  obtain ⟨d, ⟨v, hv⟩, hd⟩ := ht
  refine ⟨c * d, ⟨u * v, ?_⟩, by rw [Units.val_mul, hc, hd, map_mul]⟩
  rw [hu, hv, zpow_add₀ ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2
      hϖ.ne_zero), Units.val_mul, map_mul]; ring

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, ⟨1, by simp⟩, by simp⟩`. Consider the case `insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `(hs a).mul hϖ ih`.
-/
theorem SV.prod (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {T : Type} (S : Finset T)
    {s : T → _} {n : T → ℤ} (hs : ∀ i, SV ϖ ξ (s i) (n i)) : SV ϖ ξ (∏ i ∈ S, s i) (∑ i ∈ S, n i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, ⟨1, by simp⟩, by simp⟩
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha]; exact (hs a).mul hϖ ih

/- English proof (translation)
Take `⟨c, hc, e⟩` from `hs`. Take `⟨d, hd, e'⟩` from `ht`. Establish `: c = d` using `(kap ξ).injective (e.symm.trans e')`. Conclude with `hasVal_unique hϖ hc (this ▸ hd)`.
-/
theorem SV.unique (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {s} {n m : ℤ}
    (hs : SV ϖ ξ s n) (ht : SV ϖ ξ s m) : n = m := by
  obtain ⟨c, hc, e⟩ := hs
  obtain ⟨d, hd, e'⟩ := ht
  have : c = d := (kap ξ).injective (e.symm.trans e')
  exact hasVal_unique hϖ hc (this ▸ hd)

/- English proof (translation)
Take `rfl` from `eq_top_of_closedPoint_mem U hU`. Use `⟨algebraMap V _ ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom a : Vˣ) : V), ⟨_, by rw [zpow_zero, _root_.one_mul]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[gm_val _ ξ ⊤ trivial]`. Establish `hnat` using `congrArg (fun f => (CommRingCat.Hom.hom f) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a.val)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat`.

Use `congrArg ((Spec (CommRingCat.of (FractionRing V))).presheaf.germ ⊤ ξ trivial).hom (Eq.trans ?_ hnat.symm)` and prove the remaining obligations. Rewrite using `[Iso.hom_inv_id_apply]`. Both sides reduce to the same expression.
-/
theorem sv_unit (ξ : Spec (CommRingCat.of (FractionRing V))) (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (closedPoint V : Spec (CommRingCat.of V)) ∈ U) (a : Γ(Spec (CommRingCat.of V), U)ˣ) :
    SV ϖ ξ (gm (jK V) ξ U a) 0 := by
  obtain rfl := eq_top_of_closedPoint_mem U hU
  refine ⟨algebraMap V _ ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom a : Vˣ) : V),
    ⟨_, by rw [zpow_zero, _root_.one_mul]⟩, ?_⟩
  rw [gm_val _ ξ ⊤ trivial]
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a.val))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  refine congrArg ((Spec (CommRingCat.of (FractionRing V))).presheaf.germ ⊤ ξ trivial).hom
    (Eq.trans ?_ hnat.symm)
  rw [Iso.hom_inv_id_apply]
  rfl

/- English proof (translation)
Establish `h : p (jK V ξ) ∈ U`. Use `eq_top_of_closedPoint_mem (p ⁻¹ᵁ U) hU` as an intermediate fact. Establish `h2 : jK V ξ ∈ p ⁻¹ᵁ U` using `by rw [this]; trivial`. Conclude with `h2`. Rewrite using `[← gm_pull (jK V) p ξ U h]`.

Conclude with `sv_unit ξ _ hU _`.
-/
theorem sv_unit' (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} (p : Spec (CommRingCat.of V) ⟶ X)
    (U : X.Opens) (hU : p (closedPoint V) ∈ U) (a : Γ(X, U)ˣ) :
    SV ϖ ξ (gm (jK V ≫ p) ξ U a) 0 := by
  have h : p (jK V ξ) ∈ U := by
    have := eq_top_of_closedPoint_mem (p ⁻¹ᵁ U) hU
    have h2 : jK V ξ ∈ p ⁻¹ᵁ U := by rw [this]; trivial
    exact h2
  rw [← gm_pull (jK V) p ξ U h]
  exact sv_unit ξ _ hU _

/- English proof (translation)
Take `⟨e, c, -, hcv, H⟩` from `SectionScalarValuation.exists_val_genHasVal hn`. Establish `H1` using `H _ (𝟙 _) ξ J hJ`. Rewrite `H1` using `[gs_scal, Category.id_comp]`. Take `⟨d, ⟨u, hu⟩, hd⟩ : SV ϖ ξ (val e (jK V) ξ J) 0` from `sv_unit ξ _ (Set.mem_iInter.2 hc) _`. Use `⟨c * d, ?_, by rw [H1, hd, map_mul]⟩` and prove the remaining obligations.

Rewrite using `[hu, zpow_zero, _root_.one_mul]`. Conclude with `hasVal_mul_unit hcv u`.
-/
theorem sv_gen (hϖ : Irreducible ϖ) (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} {L : LB X}
    {Ix : Type} [Fintype Ix]
    {φ : Ix → (Spec (CommRingCat.of V) ⟶ X)} {φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    {hφ : ∀ k, φ' k = jK V ≫ φ k} {ε : Ix → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)} {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) {J} (hJ : Good L ξ J)
    (hc : ∀ k, φ k (closedPoint V) ∈ L.U (J (jK V ≫ φ k))) : SV ϖ ξ (val t (𝟙 _) ξ J) n := by
  obtain ⟨e, c, -, hcv, H⟩ := SectionScalarValuation.exists_val_genHasVal hn
  have H1 := H _ (𝟙 _) ξ J hJ
  rw [gs_scal, Category.id_comp] at H1
  obtain ⟨d, ⟨u, hu⟩, hd⟩ : SV ϖ ξ (val e (jK V) ξ J) 0 :=
    sv_unit ξ _ (Set.mem_iInter.2 hc) _
  refine ⟨c * d, ?_, by rw [H1, hd, map_mul]⟩
  rw [hu, zpow_zero, _root_.one_mul]
  exact hasVal_mul_unit hcv u

/- English proof (translation)
Use `haveI : IsDominant (jK V) := isDominant_jK`. Use `choose pick hpk using fun p : Spec (CommRingCat.of V) ⟶ X => exists_chart hL (p (closedPoint V))`. Take `⟨J, hJ, e⟩` from `exists_good L hL ξ (K := {p : Spec (CommRingCat.of V) ⟶ X // p ≫ s = 𝟙 _}) (fun p => jK V ≫ p.1) (fun p => pick p.1) (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK V) h)) (fun p => by`. Use `eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)` as an intermediate fact. Establish `h2 : jK V ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1)` using `by rw [this]; trivial`.

Conclude with `h2)`. Conclude with `⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩`.
-/
theorem exists_goodV (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ Spec (CommRingCat.of V)) [IsSeparated s] :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of V) ⟶ X, p ≫ s = 𝟙 _ →
      p (closedPoint V) ∈ L.U (J (jK V ≫ p)) := by
  haveI : IsDominant (jK V) := isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of V) ⟶ X => exists_chart hL (p (closedPoint V))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of V) ⟶ X // p ≫ s = 𝟙 _})
    (fun p => jK V ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK V) h))
    (fun p => by
      have := eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK V ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

section Box

variable {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

/- English proof (translation)
Establish `hm' : p y ∈ LB.wchart M pr (fun i => J (p ≫ pr i)) ⊓ M'.U (J' p)` using `⟨Set.mem_iInter.2 fun i => hJ (p ≫ pr i), hJ' p⟩`. Establish `hm : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ (LB.div (LB.LinComb M pr (fun _ => 1)) M').U (fun i => J (p ≫ pr i), J' p)` using `hm'`. Establish `E` using `congrArg (gm (𝟙 Y) y _) (H (fun i => J (p ≫ pr i)) (J' p))`. Rewrite using `[val_of b _ y J (fun i => J (p ≫ pr i)) (fun i => by rw [Category.id_comp]), val_of a _ y J' (fun _ => J' p) (fun i => by rw [Category.id_comp])]`. Use `(gm_res _ y _ hm _).symm.trans (E.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ n) ?_)) (gm_res _ y _ hm _))))` and prove the remaining obligations.

Conclude with `gm_pull (𝟙 Y) p y _ hm' _`.
-/
theorem mapsAt_val (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb M' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p ≫ pr i) (fun _ => n)))
    (H : GeneratorPullback.MapsAt M M' pr w p n a b) (y : Y) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    val b (𝟙 _) y J = bw w p y (fun i => J (p ≫ pr i)) (J' p) ^ n * val a (𝟙 _) y J' := by
  have hm' : p y ∈ LB.wchart M pr (fun i => J (p ≫ pr i)) ⊓ M'.U (J' p) :=
    ⟨Set.mem_iInter.2 fun i => hJ (p ≫ pr i), hJ' p⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ (LB.div (LB.LinComb M pr (fun _ => 1)) M').U (fun i => J (p ≫ pr i), J' p) := hm'
  have E := congrArg (gm (𝟙 Y) y _) (H (fun i => J (p ≫ pr i)) (J' p))
  rw [val_of b _ y J (fun i => J (p ≫ pr i)) (fun i => by rw [Category.id_comp]),
    val_of a _ y J' (fun _ => J' p) (fun i => by rw [Category.id_comp])]
  refine (gm_res _ y _ hm _).symm.trans (E.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ n) ?_)) (gm_res _ y _ hm _))))
  exact gm_pull (𝟙 Y) p y _ hm' _

/- English proof (translation)
The claim follows from `(map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)`.
-/
theorem val_finProdGen {K I : Type} [Fintype K] [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good M z J) :
    val (GeneratorPullback.finProdGen M φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Box

/- English proof (translation)
Introduce `V _ _ _ ϖ hϖ j D D' pD Q hQ x`. Take `⟨m, hm⟩` from `QForm.exists_QVal hϖ D' x`. It suffices to establish `h : m = ∑ i, Q (pD.xe x i) by rw [h] at hm; exact hm`. Take `⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V)))` from `⟨⟨⊥, Ideal.isPrime_bot⟩⟩`. Take `⟨J, hJ, hJc⟩` from `exists_goodV ξ D.toPre.P.isLB D.toPre.P.A.hom`.

Take `⟨J', hJ', hJc'⟩` from `exists_goodV ξ D'.toPre.P.isLB D'.toPre.P.A.hom`. Take `⟨b, hb, hcorr⟩` from `pD.w_psi x`. Establish `e1` using `mapsAt_val pD.w _ _ _ b hb ξ hJ hJ'`. Establish `e2` using `(val_corr hJ hcorr (𝟙 _)).trans (val_finProdGen _ _ _ _ _ hJ)`. Establish `s1 : SV ϖ ξ (val (D'.toPre.psi x) (𝟙 _) ξ J') m` using `sv_gen hϖ ξ hm hJ' fun _ => hJc' _ (Over.w _)`.

Establish `s2` using `SV.prod hϖ Finset.univ fun i : Fin j => sv_gen hϖ ξ (hQ (pD.xe x i)) hJ fun _ => hJc _ (Over.w _)`. Establish `hx : D'.toPre.xK x = jK V ≫ (D'.toPre.c x).left` using `QForm.ptK_eq _ x`. Establish `s3 : SV ϖ ξ (bw pD.w (D'.toPre.xK x) ξ (fun i => J (D'.toPre.xK x ≫ (pD.pw.pr i).left)) (J' (D'.toPre.xK x))) 0`. Rewrite using `[hx]`. Use `sv_unit' ξ _ _ ?_ _` and prove the remaining obligations.

Use `⟨Set.mem_iInter.2 fun i => ?_, hJc' _ (Over.w _)⟩` and prove the remaining obligations. Conclude with `hJc ((D'.toPre.c x).left ≫ (pD.pw.pr i).left) (QForm.over_sec _ _)`. Establish `s4` using `s3.mul hϖ s2`. Rewrite `s4` using `[← e2, zero_add]`. Establish `e3` using `e1`.

Rewrite `e3` using `[zpow_neg_one, eq_inv_mul_iff_mul_eq]`. Conclude with `s1.unique hϖ (e3 ▸ s4)`.
-/
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → QForm.IsQ D'.toPre ϖ (fun x => ∑ i, Q (pD.xe x i)) := by
  intro V _ _ _ ϖ hϖ j D D' pD Q hQ x
  obtain ⟨m, hm⟩ := QForm.exists_QVal hϖ D' x
  suffices h : m = ∑ i, Q (pD.xe x i) by rw [h] at hm; exact hm
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_goodV ξ D.toPre.P.isLB D.toPre.P.A.hom
  obtain ⟨J', hJ', hJc'⟩ := exists_goodV ξ D'.toPre.P.isLB D'.toPre.P.A.hom
  obtain ⟨b, hb, hcorr⟩ := pD.w_psi x
  have e1 := mapsAt_val pD.w _ _ _ b hb ξ hJ hJ'
  have e2 := (val_corr hJ hcorr (𝟙 _)).trans (val_finProdGen _ _ _ _ _ hJ)
  have s1 : SV ϖ ξ (val (D'.toPre.psi x) (𝟙 _) ξ J') m :=
    sv_gen hϖ ξ hm hJ' fun _ => hJc' _ (Over.w _)
  have s2 := SV.prod hϖ Finset.univ fun i : Fin j =>
    sv_gen hϖ ξ (hQ (pD.xe x i)) hJ fun _ => hJc _ (Over.w _)
  have hx : D'.toPre.xK x = jK V ≫ (D'.toPre.c x).left := QForm.ptK_eq _ x
  have s3 : SV ϖ ξ (bw pD.w (D'.toPre.xK x) ξ (fun i => J (D'.toPre.xK x ≫ (pD.pw.pr i).left))
      (J' (D'.toPre.xK x))) 0 := by
    rw [hx]
    refine sv_unit' ξ _ _ ?_ _
    refine ⟨Set.mem_iInter.2 fun i => ?_, hJc' _ (Over.w _)⟩
    exact hJc ((D'.toPre.c x).left ≫ (pD.pw.pr i).left) (QForm.over_sec _ _)
  have s4 := s3.mul hϖ s2
  rw [← e2, zero_add] at s4
  have e3 := e1
  rw [zpow_neg_one, eq_inv_mul_iff_mul_eq] at e3
  exact s1.unique hϖ (e3 ▸ s4)

end GlobalTheory.QBox

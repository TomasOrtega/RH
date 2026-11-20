import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SquareUnits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaScalar

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

section General

variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

/- English proof (translation)
Establish `hm` using `hJ.mem φ r`. Use `(congrArg (gs r z _) (h _)).trans ?_` and prove the remaining obligations. Conclude with `(gs_eq r z _ hm _).trans ((congrArg _ (map_zero _)).trans (map_zero _))`.
-/
theorem sval_eq_zero (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : sval s r z J = 0 := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ?_
  exact (gs_eq r z _ hm _).trans ((congrArg _ (map_zero _)).trans (map_zero _))

/- English proof (translation)
The claim follows from `sec_ext_val hL (s' := secZero _) (fun y J hJ => (h y J hJ).trans (sval_eq_zero (secZero _) (fun _ => rfl) _ y hJ).symm) j`.
-/
theorem eq_zero_of_sval (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j : K → L.ι) : s.f j = 0 :=
  sec_ext_val hL (s' := secZero _) (fun y J hJ => (h y J hJ).trans
    (sval_eq_zero (secZero _) (fun _ => rfl) _ y hJ).symm) j

/- English proof (translation)
Establish `inj : ∀ (i : K → L.ι) (w : Y), w ∈ LB.wchart L φ i → gs (𝟙 Y) w (LB.wchart L φ i) (s.f i) = 0 → s.f i = 0` using `fun i w hw e => germ_injective_of_isIntegral Y (U := LB.wchart L φ i) w hw (((gs_eq (𝟙 Y) w _ hw _).symm.trans e).trans (map_zero _).symm)`. Establish `hm` using `hJ.mem φ (𝟙 Y)`. Establish `h0` using `inj _ y hm h`. Distinguish the cases in `hj : (LB.wchart L φ j : Set Y).Nonempty`. Take `⟨w, hw, hw'⟩` from `nonempty_preirreducible_inter (LB.wchart L φ j).isOpen (LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k))).isOpen hj ⟨y, hm⟩`.

Use `inj j w hw ((sec_trans s (𝟙 Y) w hw hw').trans ?_)` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `(congrArg _ ((gs_eq (𝟙 Y) w _ hw' _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))).trans (MulZeroClass.mul_zero _)`. Conclude with `fn_ext fun w hw => absurd ⟨w, hw⟩ hj`.
-/
theorem eq_zero_of_germ [IsIntegral Y] (s : LB.Sec (LB.LinComb L φ ε)) (y : Y)
    {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) (h : sval s (𝟙 Y) y J = 0) (j : K → L.ι) : s.f j = 0 := by
  have inj : ∀ (i : K → L.ι) (w : Y), w ∈ LB.wchart L φ i → gs (𝟙 Y) w (LB.wchart L φ i) (s.f i) = 0 → s.f i = 0 :=
    fun i w hw e => germ_injective_of_isIntegral Y (U := LB.wchart L φ i) w hw
      (((gs_eq (𝟙 Y) w _ hw _).symm.trans e).trans (map_zero _).symm)
  have hm := hJ.mem φ (𝟙 Y)
  have h0 := inj _ y hm h
  by_cases hj : (LB.wchart L φ j : Set Y).Nonempty
  · obtain ⟨w, hw, hw'⟩ := nonempty_preirreducible_inter (LB.wchart L φ j).isOpen
      (LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k))).isOpen hj ⟨y, hm⟩
    refine inj j w hw ((sec_trans s (𝟙 Y) w hw hw').trans ?_)
    rw [h0]
    exact (congrArg _ ((gs_eq (𝟙 Y) w _ hw' _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))).trans
      (MulZeroClass.mul_zero _)
  · exact fn_ext fun w hw => absurd ⟨w, hw⟩ hj

end General

section Theta

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}

def secVal (s : LB.Sec (LPow A L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    Z.presheaf.stalk z :=
  sval (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) s r z J

def thetaVal (θ : ThetaGrp A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  val (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ r z J

def ActVal (θ : ThetaGrp A L k T) (s s' : LB.Sec (LPow A L k T)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
    secVal s' r z J = (thetaVal θ r z J).val * secVal s (r ≫ (translT A θ.pt).left) z J

/- English proof (translation)
Rewrite using `[← Over.comp_left, translT, lift_snd]`.
-/
theorem translT_snd_left (x : T ⟶ A) :
    (translT A x).left ≫ (snd T A).left = (translPt A x).left := by
  rw [← Over.comp_left, translT, lift_snd]

/- English proof (translation)
Take `⟨s', hs'⟩` from `exists_sec hL (K' := Fin 1) (φ' := fun _ => (snd T A).left) (ε' := fun _ => k) (formEq_of_add fun U _ h => by`. Simplify using `[Fintype.sum_sum_type, Fin.sum_univ_succ, ← translT_snd_left])`. Use the proof step `(pullMulSec (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) s (translT A θ.pt).left (φ₃ := ![(snd T A).left, (translPt A θ.pt).left]) (ε₃ := ![k, -k]) θ.φ θ.isGen)`. Conclude with `⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans (mul_comm _ _))⟩`.
-/
theorem exists_actVal (hL : L.IsLB) (θ : ThetaGrp A L k T) (s : LB.Sec (LPow A L k T)) : ∃ s', ActVal θ s s' := by
  obtain ⟨s', hs'⟩ := exists_sec hL (K' := Fin 1) (φ' := fun _ => (snd T A).left) (ε' := fun _ => k)
    (formEq_of_add fun U _ h => by
      simp [Fintype.sum_sum_type, Fin.sum_univ_succ, ← translT_snd_left])
    (pullMulSec (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) s (translT A θ.pt).left
      (φ₃ := ![(snd T A).left, (translPt A θ.pt).left]) (ε₃ := ![k, -k]) θ.φ θ.isGen)
  exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans (mul_comm _ _))⟩

/- English proof (translation)
Introduce `j`. Use `fn_ext fun y hy => ?_` and prove the remaining obligations. Use `choose I hI using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)`. Establish `hI' : Good L y I` using `hI`. Establish `e` using `h _ (𝟙 _) y I hI'`.

Establish `h0` using `chart_le_zero A L (translPt A θ.pt) j hy`. Establish `h1` using `chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j hy`. Use `(gs_res (𝟙 _) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) ((gs_res (𝟙 _) y _ hy _).trans (gs_pull (𝟙 _) _ y _ h1 _)))).symm)` and prove the remaining obligations. Establish `a` using `sec_trans (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y h0 (hI'.mem _ _)`. Establish `b` using `sec_trans (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) s (𝟙 _ ≫ (translT A θ.pt).left) y h1 (hI'.mem _ _)`.

Establish `c` using `gen_trans (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.isGen (𝟙 _) y hy (hI'.mem _ _)`. Use `a.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val c) b).symm)` and prove the remaining obligations. Use `(congrArg _ e).trans ?_` and prove the remaining obligations. Establish `d : trF (L` using `L) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] (𝟙 _) y j (fun i => I (𝟙 _ ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) * trF (L := L) (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _ ≫ (translT A θ.pt).left) y (fun _ => j 1) (fun _ => I ((𝟙 _ ≫ (translT A θ.pt).left) …`. Establish `e₁ : (𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left = 𝟙 _ ≫ (translPt A θ.pt).left`.

Rewrite using `[Category.assoc, translT_snd_left]`. Unfold `trF`. Rewrite using `[Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one, e₁]`. Use `show _ ^ k * _ ^ (-k) * _ ^ k = _ ^ k`. Rewrite using `[zpow_neg]`.

Conclude with `inv_mul_cancel_right _ _`. Rewrite using `[← d, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]`. Simplify using `only [_root_.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem ActVal.isActOf (hL : L.IsLB) {θ : ThetaGrp A L k T} {s s' : LB.Sec (LPow A L k T)} (h : ActVal θ s s') :
    IsActOf A L k θ s s' := by
  intro j
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have hI' : Good L y I := hI
  have e := h _ (𝟙 _) y I hI'
  have h0 := chart_le_zero A L (translPt A θ.pt) j hy
  have h1 := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j hy
  refine (gs_res (𝟙 _) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·)
    (gs_unit (𝟙 _) y _ hy _) ((gs_res (𝟙 _) y _ hy _).trans (gs_pull (𝟙 _) _ y _ h1 _)))).symm)
  have a := sec_trans (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y h0 (hI'.mem _ _)
  have b := sec_trans (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) s
    (𝟙 _ ≫ (translT A θ.pt).left) y h1 (hI'.mem _ _)
  have c := gen_trans (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.isGen (𝟙 _) y
    hy (hI'.mem _ _)
  refine a.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val c) b).symm)
  refine (congrArg _ e).trans ?_
  have d : trF (L := L) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] (𝟙 _) y j
        (fun i => I (𝟙 _ ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) *
      trF (L := L) (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _ ≫ (translT A θ.pt).left) y (fun _ => j 1)
        (fun _ => I ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left)) =
      trF (L := L) (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _) y (fun _ => j 0)
        (fun _ => I (𝟙 _ ≫ (snd T A).left)) := by
    have e₁ : (𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left = 𝟙 _ ≫ (translPt A θ.pt).left := by
      rw [Category.assoc, translT_snd_left]
    unfold trF
    rw [Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one, e₁]
    show _ ^ k * _ ^ (-k) * _ ^ k = _ ^ k
    rw [zpow_neg]
    exact inv_mul_cancel_right _ _
  rw [← d, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]
  simp only [_root_.mul_assoc]
  rfl

/- English proof (translation)
Establish `e₀ : (e ▷ A).left ≫ (snd T A).left = (snd T' A).left` using `by rw [← Over.comp_left, whiskerRight_snd]`. Establish `e₁ : (e ▷ A).left ≫ (translPt A θ.pt).left = (translPt A (e ≫ θ.pt)).left`. Rewrite using `[← Over.comp_left]`. Use `congr 1`. Simplify using `only [translPt, comp_lift_assoc, whiskerRight_snd, whiskerRight_fst_assoc]`.

Take `⟨t, ht, hv⟩` from `exists_gen hL (K' := Fin 2) (φ' := ![(snd T' A).left, (translPt A (e ≫ θ.pt)).left]) (ε' := ![k, -k]) (formEq_of_add fun U _ h => by`. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₀, e₁])`. Use the proof step `(LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (e ▷ A).left)`. Use the proof step `(DVR.pullGen_isGen L _ _ θ.φ θ.isGen _)`. Conclude with `⟨⟨e ≫ θ.pt, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩`.
-/
theorem exists_theta_pull (hL : L.IsLB) {T' : Over S} (e : T' ⟶ T) (θ : ThetaGrp A L k T) :
    ∃ θ' : ThetaGrp A L k T', θ'.pt = e ≫ θ.pt ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) J, Good L z J →
      thetaVal θ' r z J = thetaVal θ (r ≫ (e ▷ A).left) z J := by
  have e₀ : (e ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  have e₁ : (e ▷ A).left ≫ (translPt A θ.pt).left = (translPt A (e ≫ θ.pt)).left := by
    rw [← Over.comp_left]
    congr 1
    simp only [translPt, comp_lift_assoc, whiskerRight_snd, whiskerRight_fst_assoc]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(snd T' A).left, (translPt A (e ≫ θ.pt)).left])
    (ε' := ![k, -k]) (formEq_of_add fun U _ h => by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₀, e₁])
    (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (e ▷ A).left)
    (DVR.pullGen_isGen L _ _ θ.φ θ.isGen _)
  exact ⟨⟨e ≫ θ.pt, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

/- English proof (translation)
The claim follows from `((val_mul hJ _ _ _).trans (congrArg (thetaVal θx r z J * ·) (val_pull hJ _ _ _))).symm.trans ((val_corr hJ h r).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg (thetaVal θy r z J * ·) (val_pull hJ _ _ _))) (val_constGen L c r z J))))`.
-/
theorem commIsOf_val {θx θy : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (h : CommIsOf A L k θx θy c)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    thetaVal θx r z J * thetaVal θy (r ≫ (translT A θx.pt).left) z J =
      thetaVal θy r z J * thetaVal θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c :=
  ((val_mul hJ _ _ _).trans (congrArg (thetaVal θx r z J * ·) (val_pull hJ _ _ _))).symm.trans
    ((val_corr hJ h r).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg (thetaVal θy r z J * ·) (val_pull hJ _ _ _))) (val_constGen L c r z J))))

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `[translT]`. Simplify using `only [translT, translPt, Category.assoc, whiskerRight_snd, lift_snd, comp_lift_assoc, whiskerRight_fst_assoc]`.
-/
theorem translT_comp {T' : Over S} (e : T' ⟶ T) (x : T ⟶ A) :
    translT A (e ≫ x) ≫ e ▷ A = e ▷ A ≫ translT A x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, translPt, Category.assoc, whiskerRight_snd, lift_snd, comp_lift_assoc, whiskerRight_fst_assoc]

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `[translT]`. Rewrite using `[Category.assoc, translT, translT, translT, lift_snd, lift_snd] show lift (fst T A) (translPt A x) ≫ ((fst T A ≫ y) * snd T A) = (fst T A ≫ (y * x)) * snd T A`. Rewrite using `[MonObj.comp_mul, MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst, _root_.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem translT_mul (x y : T ⟶ A) : translT A x ≫ translT A y = translT A (y * x) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, translT, translT, translT, lift_snd, lift_snd]
    show lift (fst T A) (translPt A x) ≫ ((fst T A ≫ y) * snd T A) = (fst T A ≫ (y * x)) * snd T A
    rw [MonObj.comp_mul, MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst, _root_.mul_assoc]
    rfl

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `[translT]`. Rewrite using `[translT, lift_snd, Category.id_comp] show (fst T A ≫ (1 : T ⟶ A)) * snd T A = _`. Rewrite using `[MonObj.comp_one, _root_.one_mul]`.
-/
theorem translT_one : translT A (1 : T ⟶ A) = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [translT, lift_snd, Category.id_comp]
    show (fst T A ≫ (1 : T ⟶ A)) * snd T A = _
    rw [MonObj.comp_one, _root_.one_mul]

end Theta

section Local

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}

/- English proof (translation)
Establish `h : T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι = 𝟙 _` using `T.left.toIso_inv_ι`. Use `⟨Over.homMk T.left.topIso.inv ?_, Over.OverMorphism.ext h⟩` and prove the remaining obligations. Use `show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom`. Rewrite using `[← Category.assoc, h, Category.id_comp]`.
-/
theorem exists_section_overResι (T : Over S) : ∃ e : T ⟶ overRes (T := T) ⊤, e ≫ overResι ⊤ = 𝟙 T := by
  have h : T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι = 𝟙 _ := T.left.toIso_inv_ι
  refine ⟨Over.homMk T.left.topIso.inv ?_, Over.OverMorphism.ext h⟩
  show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
  rw [← Category.assoc, h, Category.id_comp]

/- English proof (translation)
Take `⟨V, hV, ⟨θx, θy, hx, -⟩, -⟩` from `h p`. Take `rfl` from `hp V hV`. Take `⟨e, he⟩` from `exists_section_overResι T`. Take `⟨θ, hθ, -⟩` from `exists_theta_pull hL e θx`. Conclude with `⟨θ, by rw [hθ, hx, ← Category.assoc, he, Category.id_comp]⟩`.
-/
theorem exists_theta_of_weilIs (hL : L.IsLB) (p : T.left) (hp : ∀ V : T.left.Opens, p ∈ V → V = ⊤) {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : WeilIs A L k x y c) : ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  obtain ⟨V, hV, ⟨θx, θy, hx, -⟩, -⟩ := h p
  obtain rfl := hp V hV
  obtain ⟨e, he⟩ := exists_section_overResι T
  obtain ⟨θ, hθ, -⟩ := exists_theta_pull hL e θx
  exact ⟨θ, by rw [hθ, hx, ← Category.assoc, he, Category.id_comp]⟩

/- English proof (translation)
Take `⟨V, hV, ⟨-, θy, -, hy⟩, hc⟩` from `h p`. Take `rfl` from `hp V hV`. Take `⟨e, he⟩` from `exists_section_overResι T`. Take `⟨θy', hθy, vy⟩` from `exists_theta_pull hL e θy`. Take `⟨θx', hθx, vx⟩` from `exists_theta_pull hL (overResι ⊤) θx`.

Establish `back : (e ▷ A).left ≫ (overResι ⊤ ▷ A).left = 𝟙 _`. Rewrite using `[← Over.comp_left, ← comp_whiskerRight, he, id_whiskerRight, Over.id_left]`. Establish `ex : e ≫ θx'.pt = θx.pt` using `by rw [hθx, ← Category.assoc, he, Category.id_comp]`. Use `⟨θy', by rw [hθy, hy, ← Category.assoc, he, Category.id_comp], fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `H` using `commIsOf_val (hc θx' θy hθx hy) (r ≫ (e ▷ A).left) z hJ`.

Establish `t₁ : (r ≫ (e ▷ A).left) ≫ (translT A θx'.pt).left = (r ≫ (translT A θx.pt).left) ≫ (e ▷ A).left`. Rewrite using `[Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, ← translT_comp, ex]`. Establish `t₂ : (r ≫ (e ▷ A).left) ≫ (translT A θy.pt).left = (r ≫ (translT A θy'.pt).left) ≫ (e ▷ A).left`. Rewrite using `[Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, ← translT_comp, hθy]`. Establish `t₃ : gm ((r ≫ (e ▷ A).left) ≫ (fst (overRes (T` using `T) ⊤) A).left) z ⊤ (unitRes ⊤ c) = gm (r ≫ (fst T A).left) z ⊤ c := by`.

Use `(gm_pull _ (overResι (T := T) ⊤).left z ⊤ trivial c).trans ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst_assoc, he, Category.comp_id]`. Rewrite `H` using `[t₁, t₂, t₃, vx _ _ z J hJ, vx _ _ z J hJ, ← vy _ _ z J hJ, ← vy _ _ z J hJ, Category.assoc, Category.assoc _ _ (overResι ⊤ ▷ A).left, back, Category.comp_id, Category.comp_id]`. Conclude with `H`.
-/
theorem exists_comm_of_weilIs (hL : L.IsLB) (p : T.left) (hp : ∀ V : T.left.Opens, p ∈ V → V = ⊤)
    (θx : ThetaGrp A L k T) {y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (h : WeilIs A L k θx.pt y c) :
    ∃ θy : ThetaGrp A L k T, θy.pt = y ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J, Good L z J →
      thetaVal θx r z J * thetaVal θy (r ≫ (translT A θx.pt).left) z J =
        thetaVal θy r z J * thetaVal θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c := by
  obtain ⟨V, hV, ⟨-, θy, -, hy⟩, hc⟩ := h p
  obtain rfl := hp V hV
  obtain ⟨e, he⟩ := exists_section_overResι T
  obtain ⟨θy', hθy, vy⟩ := exists_theta_pull hL e θy
  obtain ⟨θx', hθx, vx⟩ := exists_theta_pull hL (overResι ⊤) θx
  have back : (e ▷ A).left ≫ (overResι ⊤ ▷ A).left = 𝟙 _ := by
    rw [← Over.comp_left, ← comp_whiskerRight, he, id_whiskerRight, Over.id_left]
  have ex : e ≫ θx'.pt = θx.pt := by rw [hθx, ← Category.assoc, he, Category.id_comp]
  refine ⟨θy', by rw [hθy, hy, ← Category.assoc, he, Category.id_comp], fun Z r z J hJ => ?_⟩
  have H := commIsOf_val (hc θx' θy hθx hy) (r ≫ (e ▷ A).left) z hJ
  have t₁ : (r ≫ (e ▷ A).left) ≫ (translT A θx'.pt).left = (r ≫ (translT A θx.pt).left) ≫ (e ▷ A).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, ← translT_comp, ex]
  have t₂ : (r ≫ (e ▷ A).left) ≫ (translT A θy.pt).left = (r ≫ (translT A θy'.pt).left) ≫ (e ▷ A).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, ← translT_comp, hθy]
  have t₃ : gm ((r ≫ (e ▷ A).left) ≫ (fst (overRes (T := T) ⊤) A).left) z ⊤ (unitRes ⊤ c) =
      gm (r ≫ (fst T A).left) z ⊤ c := by
    refine (gm_pull _ (overResι (T := T) ⊤).left z ⊤ trivial c).trans ?_
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst_assoc, he,
      Category.comp_id]
  rw [t₁, t₂, t₃, vx _ _ z J hJ, vx _ _ z J hJ, ← vy _ _ z J hJ, ← vy _ _ z J hJ, Category.assoc, Category.assoc _ _
    (overResι ⊤ ▷ A).left, back, Category.comp_id, Category.comp_id] at H
  exact H

/- English proof (translation)
The claim follows from `gs_add r z _ (hJ.mem (fun _ : Fin 1 => (snd T A).left) r) _ _`.
-/
theorem secVal_add (f g : SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    secVal (SecM.toSec A (f + g)) r z J = secVal (SecM.toSec A f) r z J + secVal (SecM.toSec A g) r z J :=
  gs_add r z _ (hJ.mem (fun _ : Fin 1 => (snd T A).left) r) _ _

/- English proof (translation)
Establish `hm` using `hJ.mem (fun _ : Fin 1 => (snd T A).left) r`. Conclude with `(congrArg (gs r z _) (h _)).trans ((gs_mul r z _ hm _ _).trans (congrArg (· * _) ((gs_res r z le_top hm _).trans (gs_pull r (fst T A).left z ⊤ trivial c))))`.
-/
theorem secVal_of_eq_mul {s s' : LB.Sec (LPow A L k T)} {c : Γ(T.left, ⊤)} (h : ∀ j, s'.f j = liftFun A _ c * s.f j)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    secVal s' r z J = gs (r ≫ (fst T A).left) z ⊤ c * secVal s r z J := by
  have hm := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  exact (congrArg (gs r z _) (h _)).trans ((gs_mul r z _ hm _ _).trans (congrArg (· * _)
    ((gs_res r z le_top hm _).trans (gs_pull r (fst T A).left z ⊤ trivial c))))

/- English proof (translation)
The claim follows from `secVal_of_eq_mul (fun _ => rfl) r z hJ`.
-/
theorem secVal_smul (c : Γ(T.left, ⊤)) (f : SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) :
    secVal (SecM.toSec A (c • f)) r z J = gs (r ≫ (fst T A).left) z ⊤ c * secVal (SecM.toSec A f) r z J :=
  secVal_of_eq_mul (fun _ => rfl) r z hJ

/- English proof (translation)
Use `choose a ha using exists_actVal hL θ`. Establish `ext : ∀ f g : SecM A L k T, (∀ y J, Good L y J → secVal (SecM.toSec A f) (𝟙 _) y J = secVal (SecM.toSec A g) (𝟙 _) y J) → f = g` using `fun f g h => Subtype.ext (funext fun j => sec_ext_val (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) hL (s := SecM.toSec A f) (s' := SecM.toSec A g) h j)`. Establish `hb : ∀ f : SecM A L k T, ActVal θ (SecM.toSec A f) (SecM.toSec A (SecM.ofSec A (a (SecM.toSec A f))))` using `fun f => ha _`. Use `⟨⟨⟨fun f => SecM.ofSec A (a (SecM.toSec A f)), fun f g => ext _ _ fun y J hJ => ?_⟩, fun c f => ext _ _ fun y J hJ => ?_⟩, hb⟩` and prove the remaining obligations. Rewrite using `[secVal_add _ _ _ y hJ, hb _ _ _ y J hJ, hb _ _ _ y J hJ, hb _ _ _ y J hJ, secVal_add _ _ _ y hJ, mul_add]`.

Establish `e : (𝟙 _ ≫ (translT A θ.pt).left) ≫ (fst T A).left = 𝟙 _ ≫ (fst T A).left`. Rewrite using `[Category.assoc, ← Over.comp_left, translT, lift_fst]`. Use `(hb (c • f) _ _ y J hJ).trans (Eq.trans ?_ (secVal_smul c _ _ y hJ).symm)` and prove the remaining obligations. Rewrite using `[hb f _ _ y J hJ, secVal_smul c f _ y hJ, e, mul_left_comm]`.
-/
theorem exists_linear_act (hL : L.IsLB) (θ : ThetaGrp A L k T) :
    ∃ Φ : SecM A L k T →ₗ[Γ(T.left, ⊤)] SecM A L k T, ∀ f, ActVal θ (SecM.toSec A f) (SecM.toSec A (Φ f)) := by
  choose a ha using exists_actVal hL θ
  have ext : ∀ f g : SecM A L k T, (∀ y J, Good L y J → secVal (SecM.toSec A f) (𝟙 _) y J =
      secVal (SecM.toSec A g) (𝟙 _) y J) → f = g := fun f g h => Subtype.ext (funext fun j =>
    sec_ext_val (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) hL
      (s := SecM.toSec A f) (s' := SecM.toSec A g) h j)
  have hb : ∀ f : SecM A L k T, ActVal θ (SecM.toSec A f) (SecM.toSec A (SecM.ofSec A (a (SecM.toSec A f)))) :=
    fun f => ha _
  refine ⟨⟨⟨fun f => SecM.ofSec A (a (SecM.toSec A f)), fun f g => ext _ _ fun y J hJ => ?_⟩,
    fun c f => ext _ _ fun y J hJ => ?_⟩, hb⟩
  · rw [secVal_add _ _ _ y hJ, hb _ _ _ y J hJ, hb _ _ _ y J hJ, hb _ _ _ y J hJ, secVal_add _ _ _ y hJ, mul_add]
  · have e : (𝟙 _ ≫ (translT A θ.pt).left) ≫ (fst T A).left = 𝟙 _ ≫ (fst T A).left := by
      rw [Category.assoc, ← Over.comp_left, translT, lift_fst]
    refine (hb (c • f) _ _ y J hJ).trans (Eq.trans ?_ (secVal_smul c _ _ y hJ).symm)
    rw [hb f _ _ y J hJ, secVal_smul c f _ y hJ, e, mul_left_comm]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Take `⟨u, hu⟩` from `hT.mul_inv_cancel (sub_ne_zero.2 fun e : (c : Γ(T.left, ⊤)) = 1 => hc (Units.ext e))`. Take `⟨f, hf⟩` from `exists_ne (0 : SecM A L k T)`. Take `⟨θy, rfl, comm⟩` from `exists_comm_of_weilIs hL p hp θ h`. Use `hf (Subtype.ext (funext fun j => eq_zero_of_sval (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) hL (SecM.toSec A f) (fun z J hJ => ?_) j))` and prove the remaining obligations.

Use `set s := SecM.toSec A f`. Take `⟨s₁, h₁⟩` from `exists_actVal hL θy s`. Take `⟨s₂, h₂⟩` from `exists_actVal hL θ s₁`. Take `⟨s₃, h₃⟩` from `exists_actVal hL θ s`. Set `r` to `(translT A (θy.pt * θ.pt)⁻¹).left`.

Establish `r₁ : (r ≫ (translT A θ.pt).left) ≫ (translT A θy.pt).left = 𝟙 _`. Rewrite using `[← Over.comp_left, ← Over.comp_left, translT_mul, translT_mul, ← _root_.mul_assoc, mul_inv_cancel, translT_one, Over.id_left]`. Establish `r₂ : (r ≫ (translT A θy.pt).left) ≫ (translT A θ.pt).left = 𝟙 _`. Rewrite using `[← Over.comp_left, ← Over.comp_left, translT_mul, translT_mul, ← _root_.mul_assoc, mul_comm θ.pt, mul_inv_cancel, translT_one, Over.id_left]`. Establish `r₃ : (r ≫ (translT A θy.pt).left) ≫ (fst T A).left = r ≫ (fst T A).left`.

Rewrite using `[Category.assoc, ← Over.comp_left, translT, lift_fst]`. Establish `a₁` using `h₂ _ r z J hJ`. Establish `a₃` using `h₃ _ (r ≫ (translT A θy.pt).left) z J hJ`. Rewrite `a₁` using `[secVal_of_eq_mul (hθ _ _ h₂) r z hJ, h₁ _ _ z J hJ, h₁ _ _ z J hJ, r₁]`. Rewrite `a₃` using `[secVal_of_eq_mul (hθ _ _ h₃) _ z hJ, r₂, r₃]`.

Establish `a₄` using `congrArg Units.val (comm _ r z J hJ)`. Rewrite `a₄` using `[Units.val_mul, Units.val_mul, Units.val_mul, ← gs_unit _ z ⊤ trivial]`. Establish `a₅ : (gs (r ≫ (fst T A).left) z ⊤ (c : Γ(T.left, ⊤)) - 1) * gs (r ≫ (fst T A).left) z ⊤ u = 1`. Use `congrArg (gs (r ≫ (fst T A).left) z ⊤) hu` as an intermediate fact. Simplify `this` using `only [gs_eq (r ≫ (fst T A).left) z ⊤ trivial, map_mul, map_sub, map_one]`.

Establish `key : ((thetaVal θy r z J * thetaVal θ (r ≫ (translT A θy.pt).left) z J).val) * secVal s (𝟙 _) z J = 0`. Rewrite using `[Units.val_mul]`. Take the linear combination `(-gs (r ≫ (fst T A).left) z ⊤ u) * (a₁ - (thetaVal θy r z J).val * a₃ + secVal s (𝟙 _) z J * a₄) - (thetaVal θy r z J).val * (thetaVal θ (r ≫ (translT A θy.pt).left) z J).val * secVal s (𝟙 _) z J * a₅`. Conclude with `(Units.mul_right_eq_zero _).1 key`.
-/
theorem weil_eq_one_of_scalar [IsCommMonObj A] (hL : L.IsLB) (p : T.left) (hp : ∀ V : T.left.Opens, p ∈ V → V = ⊤)
    (hT : IsField Γ(T.left, ⊤)) [Nontrivial (SecM A L k T)] (θ : ThetaGrp A L k T) (a : Γ(T.left, ⊤))
    (hθ : ∀ s s', ActVal θ s s' → ∀ j, s'.f j = liftFun A _ a * s.f j)
    {y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (h : WeilIs A L k θ.pt y c) : c = 1 := by
  by_contra hc
  obtain ⟨u, hu⟩ := hT.mul_inv_cancel (sub_ne_zero.2 fun e : (c : Γ(T.left, ⊤)) = 1 => hc (Units.ext e))
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM A L k T)
  obtain ⟨θy, rfl, comm⟩ := exists_comm_of_weilIs hL p hp θ h
  refine hf (Subtype.ext (funext fun j => eq_zero_of_sval (K := Fin 1) (φ := fun _ => (snd T A).left)
    (ε := fun _ => k) hL (SecM.toSec A f) (fun z J hJ => ?_) j))
  set s := SecM.toSec A f
  obtain ⟨s₁, h₁⟩ := exists_actVal hL θy s
  obtain ⟨s₂, h₂⟩ := exists_actVal hL θ s₁
  obtain ⟨s₃, h₃⟩ := exists_actVal hL θ s
  let r := (translT A (θy.pt * θ.pt)⁻¹).left
  have r₁ : (r ≫ (translT A θ.pt).left) ≫ (translT A θy.pt).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.comp_left, translT_mul, translT_mul, ← _root_.mul_assoc, mul_inv_cancel,
      translT_one, Over.id_left]
  have r₂ : (r ≫ (translT A θy.pt).left) ≫ (translT A θ.pt).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.comp_left, translT_mul, translT_mul, ← _root_.mul_assoc, mul_comm θ.pt,
      mul_inv_cancel, translT_one, Over.id_left]
  have r₃ : (r ≫ (translT A θy.pt).left) ≫ (fst T A).left = r ≫ (fst T A).left := by
    rw [Category.assoc, ← Over.comp_left, translT, lift_fst]
  have a₁ := h₂ _ r z J hJ
  have a₃ := h₃ _ (r ≫ (translT A θy.pt).left) z J hJ
  rw [secVal_of_eq_mul (hθ _ _ h₂) r z hJ, h₁ _ _ z J hJ, h₁ _ _ z J hJ, r₁] at a₁
  rw [secVal_of_eq_mul (hθ _ _ h₃) _ z hJ, r₂, r₃] at a₃
  have a₄ := congrArg Units.val (comm _ r z J hJ)
  rw [Units.val_mul, Units.val_mul, Units.val_mul, ← gs_unit _ z ⊤ trivial] at a₄
  have a₅ : (gs (r ≫ (fst T A).left) z ⊤ (c : Γ(T.left, ⊤)) - 1) * gs (r ≫ (fst T A).left) z ⊤ u = 1 := by
    have := congrArg (gs (r ≫ (fst T A).left) z ⊤) hu
    simpa only [gs_eq (r ≫ (fst T A).left) z ⊤ trivial, map_mul, map_sub, map_one] using this
  have key : ((thetaVal θy r z J * thetaVal θ (r ≫ (translT A θy.pt).left) z J).val) * secVal s (𝟙 _) z J = 0 := by
    rw [Units.val_mul]
    linear_combination (-gs (r ≫ (fst T A).left) z ⊤ u) * (a₁ - (thetaVal θy r z J).val * a₃ + secVal s (𝟙 _) z J * a₄) -
      (thetaVal θy r z J).val * (thetaVal θ (r ≫ (translT A θy.pt).left) z J).val * secVal s (𝟙 _) z J * a₅
  exact (Units.mul_right_eq_zero _).1 key

end Local

section Field

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}

/- English proof (translation)
Use `letI : Field R := (e.toMulEquiv.isField (Field.toIsField F)).toField`. Use `haveI : IsAlgClosed R := IsAlgClosed.of_ringEquiv F R e.symm`. Use `haveI : Module.Finite R M := Module.finite_of_finrank_pos h`. Use `haveI : Nontrivial M := Module.nontrivial_of_finrank_pos h`. Take `⟨a, ha⟩` from `Module.End.exists_eigenvalue (K := R) (V := M) Φ`.

Take `⟨v, hv⟩` from `ha.exists_hasEigenvector`. Conclude with `⟨a, v, hv.2, hv.apply_eq_smul⟩`.
-/
theorem exists_eigenvector {R F M : Type} [CommRing R] [Field F] [IsAlgClosed F] (e : R ≃+* F) [AddCommGroup M]
    [Module R M] (h : 0 < Module.finrank R M) (Φ : M →ₗ[R] M) : ∃ (a : R) (v : M), v ≠ 0 ∧ Φ v = a • v := by
  letI : Field R := (e.toMulEquiv.isField (Field.toIsField F)).toField
  haveI : IsAlgClosed R := IsAlgClosed.of_ringEquiv F R e.symm
  haveI : Module.Finite R M := Module.finite_of_finrank_pos h
  haveI : Nontrivial M := Module.nontrivial_of_finrank_pos h
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (K := R) (V := M) Φ
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  exact ⟨a, v, hv.2, hv.apply_eq_smul⟩

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `exists_linear_act hL θ`. Take `⟨a, v, hv, hav⟩` from `exists_eigenvector e h0 Φ`. Use `⟨a, fun s s' hs j => sec_ext_val (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) hL (s := s') (s' := SecM.toSec A (a • SecM.ofSec A s)) (fun y J hJ => ?_) j⟩` and prove the remaining obligations. Establish `hne : secVal (SecM.toSec A v) (𝟙 _) y J ≠ 0` using `fun e0 => hv (Subtype.ext (funext fun i => eq_zero_of_germ (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) (SecM.toSec A v) y hJ e0 i))`. Establish `H` using `h s s' _ _ hs (hΦ v) y J hJ`.

Rewrite `H` using `[hav, secVal_smul a v _ y hJ]`. Use `(mul_right_cancel₀ hne ?_ : secVal s' (𝟙 _) y J = _).trans (secVal_smul a (SecM.ofSec A s) _ y hJ).symm` and prove the remaining obligations. Rewrite using `[H, mul_right_comm]`. Both sides reduce to the same expression.
-/
theorem exists_scalar (hL : L.IsLB) [IsIntegral (T ⊗ A).left] {F : Type} [Field F] [IsAlgClosed F]
    (e : Γ(T.left, ⊤) ≃+* F) (h0 : 0 < Module.finrank Γ(T.left, ⊤) (SecM A L k T)) (θ : ThetaGrp A L k T)
    (h : ∀ s s' t t', ActVal θ s s' → ActVal θ t t' → ∀ y J, Good L y J →
      secVal s' (𝟙 _) y J * secVal t (𝟙 _) y J = secVal t' (𝟙 _) y J * secVal s (𝟙 _) y J) :
    ∃ a : Γ(T.left, ⊤), ∀ s s', ActVal θ s s' → ∀ j, s'.f j = liftFun A _ a * s.f j := by
  obtain ⟨Φ, hΦ⟩ := exists_linear_act hL θ
  obtain ⟨a, v, hv, hav⟩ := exists_eigenvector e h0 Φ
  refine ⟨a, fun s s' hs j => sec_ext_val (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) hL
    (s := s') (s' := SecM.toSec A (a • SecM.ofSec A s)) (fun y J hJ => ?_) j⟩
  have hne : secVal (SecM.toSec A v) (𝟙 _) y J ≠ 0 := fun e0 => hv (Subtype.ext (funext fun i =>
    eq_zero_of_germ (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) (SecM.toSec A v) y hJ e0 i))
  have H := h s s' _ _ hs (hΦ v) y J hJ
  rw [hav, secVal_smul a v _ y hJ] at H
  refine (mul_right_cancel₀ hne ?_ : secVal s' (𝟙 _) y J = _).trans (secVal_smul a (SecM.ofSec A s) _ y hJ).symm
  rw [H, mul_right_comm]
  rfl

/- English proof (translation)
Establish `mul : ∀ a b : LB.Sec (LPow A L k T), ∃ u : SecM A L (k + k) T, ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J, Good L z J → secVal (SecM.toSec A u) r z J = secVal a r z J * secVal b r z J` using `fun a b => by`. Take `⟨u, hu⟩` from `exists_sec hL (K' := Fin 1) (φ' := fun _ => (snd T A).left) (ε' := fun _ => k + k) (formEq_of_add fun U _ h => by simp [Fintype.sum_sum_type, add_smul, two_nsmul]) (mulSec (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) (K' := Fin 1) (φ' := fun _ => (snd T A).left) …`. Conclude with `⟨SecM.ofSec A u, fun Z r z J hJ => (hu Z r z J hJ).trans (sval_mulSec _ _ r z hJ)⟩`. Take `⟨u, hu⟩` from `mul s' t`. Take `⟨v, hv⟩` from `mul t' s`.

Establish `sub : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J, Good L z J → secVal (SecM.toSec A (u - v)) r z J = secVal s' r z J * secVal t r z J - secVal t' r z J * secVal s r z J` using `fun Z r z J hJ => by`. Rewrite using `[← hu Z r z J hJ, ← hv Z r z J hJ, eq_sub_iff_add_eq, ← secVal_add _ _ r z hJ, sub_add_cancel]`. Establish `h0` using `dense (SecM.toSec A (u - v)) fun i => by`. Rewrite using `[sub _ _ z J₀ hJ₀, hs _ _ z J₀ hJ₀, ht _ _ z J₀ hJ₀, _root_.mul_assoc, ratio, _root_.mul_assoc, sub_self]`. Rewrite using `[← sub_eq_zero, ← sub _ _ y J hJ]`.

Conclude with `sval_eq_zero (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k + k) _ h0 _ y hJ`.
-/
theorem cross_of_dense (hL : L.IsLB) (θ : ThetaGrp A L k T) {I : Type*} {Z : Scheme.{0}} (z : Z)
    (r : I → (Z ⟶ (T ⊗ A).left)) (J₀ : (Z ⟶ A.left) → L.ι) (hJ₀ : Good L z J₀)
    (dense : ∀ u : LB.Sec (LPow A L (k + k) T), (∀ i, secVal u (r i) z J₀ = 0) → ∀ j, u.f j = 0)
    (ratio : ∀ s t : LB.Sec (LPow A L k T), ∀ i,
      secVal s (r i ≫ (translT A θ.pt).left) z J₀ * secVal t (r i) z J₀ =
        secVal t (r i ≫ (translT A θ.pt).left) z J₀ * secVal s (r i) z J₀)
    (s s' t t' : LB.Sec (LPow A L k T)) (hs : ActVal θ s s') (ht : ActVal θ t t') (y : (T ⊗ A).left)
    (J : ((T ⊗ A).left ⟶ A.left) → L.ι) (hJ : Good L y J) :
    secVal s' (𝟙 _) y J * secVal t (𝟙 _) y J = secVal t' (𝟙 _) y J * secVal s (𝟙 _) y J := by
  have mul : ∀ a b : LB.Sec (LPow A L k T), ∃ u : SecM A L (k + k) T,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J, Good L z J →
        secVal (SecM.toSec A u) r z J = secVal a r z J * secVal b r z J := fun a b => by
    obtain ⟨u, hu⟩ := exists_sec hL (K' := Fin 1) (φ' := fun _ => (snd T A).left) (ε' := fun _ => k + k)
      (formEq_of_add fun U _ h => by simp [Fintype.sum_sum_type, add_smul, two_nsmul])
      (mulSec (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) (K' := Fin 1)
        (φ' := fun _ => (snd T A).left) (ε' := fun _ => k) a b)
    exact ⟨SecM.ofSec A u, fun Z r z J hJ => (hu Z r z J hJ).trans (sval_mulSec _ _ r z hJ)⟩
  obtain ⟨u, hu⟩ := mul s' t
  obtain ⟨v, hv⟩ := mul t' s
  have sub : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J, Good L z J →
      secVal (SecM.toSec A (u - v)) r z J = secVal s' r z J * secVal t r z J - secVal t' r z J * secVal s r z J :=
    fun Z r z J hJ => by
      rw [← hu Z r z J hJ, ← hv Z r z J hJ, eq_sub_iff_add_eq, ← secVal_add _ _ r z hJ, sub_add_cancel]
  have h0 := dense (SecM.toSec A (u - v)) fun i => by
    rw [sub _ _ z J₀ hJ₀, hs _ _ z J₀ hJ₀, ht _ _ z J₀ hJ₀, _root_.mul_assoc, ratio, _root_.mul_assoc, sub_self]
  rw [← sub_eq_zero, ← sub _ _ y J hJ]
  exact sval_eq_zero (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k + k) _ h0 _ y hJ

end Field

section Points

/- English proof (translation)
Rewrite using `[valF, dif_pos ((top_le_iff_mem x U z).2 h), gs_eq x z U h]`. Use `show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _`. Rewrite using `[Iso.hom_inv_id_apply]`. Conclude with `TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _`.
-/
theorem toStk_valF_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valF x U a) = gs x z U a := by
  rw [valF, dif_pos ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

/- English proof (translation)
Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises. Simplify using `[translT, ptSecT]`. Rewrite using `[Category.assoc, translT, lift_snd, ptSecT, ptSecT, lift_snd] show lift (𝟙 T) x ≫ ((fst T A ≫ d) * snd T A) = _`. Rewrite using `[MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst, Category.id_comp]`.
-/
theorem ptSecT_translT {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (x d : T ⟶ A) :
    ptSecT A x ≫ translT A d = ptSecT A (d * x) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT, ptSecT]
  · rw [Category.assoc, translT, lift_snd, ptSecT, ptSecT, lift_snd]
    show lift (𝟙 T) x ≫ ((fst T A ≫ d) * snd T A) = _
    rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst, Category.id_comp]

variable {S : Scheme.{0}} {F : Type} [Field F]

/- English proof (translation)
The claim follows from `eq_top_iff.2 fun q _ => by rw [spec_pt_eq (k := F) q p]; exact h`.
-/
theorem opens_eq_top (t : Sp F ⟶ S) (p : (Over.mk t).left) (V : (Over.mk t).left.Opens) (h : p ∈ V) : V = ⊤ :=
  eq_top_iff.2 fun q _ => by rw [spec_pt_eq (k := F) q p]; exact h

/- English proof (translation)
The claim follows from `haveI := P.isAb.smooth haveI := P.isAb.geomConnected (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom).geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip`.
-/
theorem isIntegral_fibre (P : PolAV S) (t : Sp F ⟶ S) : IsIntegral (Over.mk t ⊗ P.A).left :=
  haveI := P.isAb.smooth
  haveI := P.isAb.geomConnected
  (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom).geometrically_isIntegral t _ _
    (IsPullback.of_hasPullback t P.A.hom).flip

end Points

section Main

variable {F : Type} [Field F] [IsAlgClosed F]

/- English proof (translation)
Establish `hk1 : 1 ≤ k` using `Nat.one_le_iff_ne_zero.2 fun e => hk (by rw [e, Nat.cast_zero])`. Rewrite using `[hH F P k hk1]`. Conclude with `Nat.pow_pos hk1`.
-/
theorem finrank_pos_of_laws (hH : GlobalSectionsRankAlgClosed) (P : PolAV (Spec (CommRingCat.of F))) {k : ℕ} (hk : (k : F) ≠ 0) :
    0 < Module.finrank Γ((baseOver (Spec (CommRingCat.of F))).left, ⊤)
      (SecM P.A P.L (k : ℕ) (baseOver (Spec (CommRingCat.of F)))) := by
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 fun e => hk (by rw [e, Nat.cast_zero])
  rw [hH F P k hk1]
  exact Nat.pow_pos hk1

/- English proof (translation)
The claim follows from `haveI : Nontrivial Γ((baseOver (Spec (CommRingCat.of F))).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial Module.nontrivial_of_finrank_pos (finrank_pos_of_laws hH P hk)`.
-/
theorem nontrivial_of_laws (hH : GlobalSectionsRankAlgClosed) (P : PolAV (Spec (CommRingCat.of F))) {k : ℕ} (hk : (k : F) ≠ 0) :
    Nontrivial (SecM P.A P.L (k : ℕ) (baseOver (Spec (CommRingCat.of F)))) :=
  haveI : Nontrivial Γ((baseOver (Spec (CommRingCat.of F))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  Module.nontrivial_of_finrank_pos (finrank_pos_of_laws hH P hk)

omit [IsAlgClosed F] in

/- English proof (translation)
The claim follows from `exists_theta_of_weilIs P.isLB (T := baseOver (Spec (CommRingCat.of F))) (IsLocalRing.closedPoint F) (opens_eq_top (𝟙 _) _) ((hW _ P k _).2.2.1 d hd)`.
-/
theorem exists_theta (hW : WeilSt) (P : PolAV (Spec (CommRingCat.of F))) (k : ℕ)
    (d : baseOver (Spec (CommRingCat.of F)) ⟶ P.A) (hd : d ^ k = 1) :
    ∃ θ : ThetaGrp P.A P.L k (baseOver (Spec (CommRingCat.of F))), θ.pt = d :=
  exists_theta_of_weilIs P.isLB (T := baseOver (Spec (CommRingCat.of F))) (IsLocalRing.closedPoint F)
    (opens_eq_top (𝟙 _) _) ((hW _ P k _).2.2.1 d hd)

/- English proof (translation)
Use `haveI := P.isAb.comm`. Use `haveI := nontrivial_of_laws hH P hk`. Use `hN F P k hk θ.pt hd fun y hy => ?_` and prove the remaining obligations. Take `⟨c, hc, -⟩` from `(hW _ P k _).1 θ.pt y hd hy`. Take `rfl` from `weil_eq_one_of_scalar P.isLB (T := baseOver (Spec (CommRingCat.of F))) (IsLocalRing.closedPoint F) (opens_eq_top (𝟙 _) _) ((Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField F)) θ a hθ hc`.

Conclude with `hc`.
-/
theorem theta_pt_eq_one_of_actVal (hW : WeilSt) (hN : WeilNondegSt) (hH : GlobalSectionsRankAlgClosed)
    (P : PolAV (Spec (CommRingCat.of F))) (k : ℕ) (hk : (k : F) ≠ 0)
    (θ : ThetaGrp P.A P.L k (baseOver (Spec (CommRingCat.of F)))) (hd : θ.pt ^ k = 1)
    (a : Γ((baseOver (Spec (CommRingCat.of F))).left, ⊤))
    (hθ : ∀ s s', ActVal θ s s' → ∀ j, s'.f j = liftFun P.A _ a * s.f j) : θ.pt = 1 := by
  haveI := P.isAb.comm
  haveI := nontrivial_of_laws hH P hk
  refine hN F P k hk θ.pt hd fun y hy => ?_
  obtain ⟨c, hc, -⟩ := (hW _ P k _).1 θ.pt y hd hy
  obtain rfl := weil_eq_one_of_scalar P.isLB (T := baseOver (Spec (CommRingCat.of F))) (IsLocalRing.closedPoint F)
    (opens_eq_top (𝟙 _) _)
    ((Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField F)) θ a hθ hc
  exact hc

end Main

end GlobalTheory.ThetaScalar

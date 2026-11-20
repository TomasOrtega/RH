import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul

noncomputable section

namespace GlobalTheory.TorusModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusExt GlobalTheory.FormalPoint

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Spec (CommRingCat.of R))}

abbrev cv (g : GtPt D T) (χ : D.X) (y : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) :
    (T.left.presheaf.stalk y)ˣ := val (g.s χ) (𝟙 T.left) y J

/- English proof (translation)
Take `⟨b, s, hs, _, _⟩` from `g`. Take `⟨b', s', hs', _, _⟩` from `g'`. Take `rfl : b = b'` from `hb`. Take `rfl : s = s'` from `funext fun χ => TorusCoord.gen_eq_of_corr D.P.isLB (hs χ) (hs' χ) (corr_of_val D.P.isLB (h χ))`. Both sides reduce to the same expression.
-/
theorem pt_ext {g g' : GtPt D T} (hb : g.b = g'.b)
    (h : ∀ χ y J, Good D.P.L y J → cv g χ y J = cv g' χ y J) : g = g' := by
  obtain ⟨b, s, hs, _, _⟩ := g
  obtain ⟨b', s', hs', _, _⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ => TorusCoord.gen_eq_of_corr D.P.isLB (hs χ) (hs' χ)
    (corr_of_val D.P.isLB (h χ))
  rfl

/- English proof (translation)
Simplify using `[DegPre.gtφT, DegPre.gtε, Fin.prod_univ_four]`. Both sides reduce to the same expression.
-/
theorem prod_pt (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφT D T b χ i) ^ DegPre.gtε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  simp [DegPre.gtφT, DegPre.gtε, Fin.prod_univ_four]
  rfl

/- English proof (translation)
Use `val_cub D.cub (𝟙 T) hJ x x' w` as an intermediate fact. Rewrite `this` using `[Category.id_comp, Category.id_comp, Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem val_cubAtT {y : T.left} {J} (hJ : Good D.P.L y J) (x x' w : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T x x' w) (𝟙 _) y J = th D y J x x' w := by
  have := val_cub D.cub (𝟙 T) hJ x x' w
  rwa [Category.id_comp, Category.id_comp, Category.id_comp] at this

/- English proof (translation)
The claim follows from `(val_corr hJ g.s_zero _).trans (val_one _)`.
-/
theorem cv_zero (g : GtPt D T) {y J} (hJ : Good D.P.L y J) : cv g 0 y J = 1 :=
  (val_corr hJ g.s_zero _).trans (val_one _)

/- English proof (translation)
The claim follows from `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAtT hJ _ _ _))).symm.trans ((val_corr hJ (g.mult χ χ') _).trans (val_mul hJ _ _ _))`.
-/
theorem cv_add (g : GtPt D T) {y J} (hJ : Good D.P.L y J) (χ χ' : D.X) :
    cv g (χ + χ') y J * th D y J (cP D _ χ) (cP D _ χ') g.b = cv g χ y J * cv g χ' y J :=
  ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAtT hJ _ _ _))).symm.trans
    ((val_corr hJ (g.mult χ χ') _).trans (val_mul hJ _ _ _))

/- English proof (translation)
Use `choose s hs vs using fun χ => exists_gen D.P.isLB (hF χ) (v χ) (hv χ)`. Use `⟨⟨b, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl, fun χ Z r y J hJ => vs χ _ _ y J hJ⟩` and prove the remaining obligations. Conclude with `(vs 0 _ _ y J hJ).trans ((h₀ y J hJ).trans (val_one _).symm)`. Conclude with `(val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (vs _ _ _ y J hJ) (val_cubAtT hJ _ _ _)).trans ((hm χ χ' y J hJ).trans ((congrArg₂ (· * ·) (vs _ _ _ y J hJ) (vs _ _ _ y J hJ)).symm.trans (val_mul hJ _ _ _).symm)))`.
-/
theorem exists_pt (b : T ⟶ D.P.A) {K : Type} [Fintype K] {φ : D.X → K → (T.left ⟶ D.P.A.left)}
    {ε : K → ℤ} (v : ∀ χ, LB.Gen (LB.LinComb D.P.L (φ χ) ε)) (hv : ∀ χ, (v χ).IsGen)
    (hF : ∀ χ, FormEq (φ χ) ε (DegPre.gtφT D T b χ) DegPre.gtε)
    (h₀ : ∀ y J, Good D.P.L y J → val (v 0) (𝟙 _) y J = 1)
    (hm : ∀ χ χ' y J, Good D.P.L y J → val (v (χ + χ')) (𝟙 _) y J * th D y J (cP D _ χ) (cP D _ χ') b =
      val (v χ) (𝟙 _) y J * val (v χ') (𝟙 _) y J) :
    ∃ g : GtPt D T, g.b = b ∧ ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      val (g.s χ) r y J = val (v χ) r y J := by
  choose s hs vs using fun χ => exists_gen D.P.isLB (hF χ) (v χ) (hv χ)
  refine ⟨⟨b, s, hs, corr_of_val D.P.isLB fun y J hJ => ?_, fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl,
    fun χ Z r y J hJ => vs χ _ _ y J hJ⟩
  · exact (vs 0 _ _ y J hJ).trans ((h₀ y J hJ).trans (val_one _).symm)
  · exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (vs _ _ _ y J hJ) (val_cubAtT hJ _ _ _)).trans
      ((hm χ χ' y J hJ).trans
      ((congrArg₂ (· * ·) (vs _ _ _ y J hJ) (vs _ _ _ y J hJ)).symm.trans (val_mul hJ _ _ _).symm)))

/- English proof (translation)
The claim follows from `and_congr Iff.rfl (forall_congr' fun _ => ⟨fun h _ _ hJ => ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAtT hJ _ _ _))).symm.trans ((val_corr hJ h _).trans (val_mul hJ _ _ _)), fun h => corr_of_val D.P.isLB fun y J hJ => ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rf …`.
-/
theorem isAdd_iff (g g' g'' : GtPt D T) : g.IsAdd g' g'' ↔ g''.b = g.b * g'.b ∧ ∀ χ y J, Good D.P.L y J →
    cv g'' χ y J * th D y J (cP D _ χ) g.b g'.b = cv g χ y J * cv g' χ y J :=
  and_congr Iff.rfl (forall_congr' fun _ => ⟨fun h _ _ hJ =>
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAtT hJ _ _ _))).symm.trans
      ((val_corr hJ h _).trans (val_mul hJ _ _ _)),
    fun h => corr_of_val D.P.isLB fun y J hJ => ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_cubAtT hJ _ _ _))).trans ((h y J hJ).trans (val_mul hJ _ _ _).symm)⟩)

/- English proof (translation)
Rewrite `e`, `e'` using `[isAdd_iff]`. Conclude with `pt_ext (e.1.trans e'.1.symm) fun χ y J hJ => mul_right_cancel ((e.2 χ y J hJ).trans (e'.2 χ y J hJ).symm)`.
-/
theorem isAdd_unique {g g' h h' : GtPt D T} (e : g.IsAdd g' h) (e' : g.IsAdd g' h') : h = h' := by
  rw [isAdd_iff] at e e'
  exact pt_ext (e.1.trans e'.1.symm) fun χ y J hJ => mul_right_cancel ((e.2 χ y J hJ).trans (e'.2 χ y J hJ).symm)

/- English proof (translation)
The claim follows from `and_congr ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩ (forall_congr' fun _ => ⟨fun h _ _ hJ => (val_corr hJ h _).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])), fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans ((val_pull hJ _ _ _).tr …`.
-/
theorem isPull_iff (k : T' ⟶ T) (g : GtPt D T) (g' : GtPt D T') : GtPt.IsPull k.left g g' ↔
    g'.b = k ≫ g.b ∧ ∀ χ y J, Good D.P.L y J → cv g' χ y J = val (g.s χ) k.left y J :=
  and_congr ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩ (forall_congr' fun _ =>
    ⟨fun h _ _ hJ => (val_corr hJ h _).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])),
      fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans
        ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm⟩)

/- English proof (translation)
Rewrite `e`, `e'` using `[isPull_iff]`. Conclude with `pt_ext (e.1.trans e'.1.symm) fun χ y J hJ => (e.2 χ y J hJ).trans (e'.2 χ y J hJ).symm`.
-/
theorem isPull_unique {k : T' ⟶ T} {g : GtPt D T} {h h' : GtPt D T'} (e : GtPt.IsPull k.left g h)
    (e' : GtPt.IsPull k.left g h') : h = h' := by
  rw [isPull_iff] at e e'
  exact pt_ext (e.1.trans e'.1.symm) fun χ y J hJ => (e.2 χ y J hJ).trans (e'.2 χ y J hJ).symm

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (hG : GlobalFnsSt) (oa : D.OAct O)

/- English proof (translation)
The claim follows from `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull_pair u k hJ _ _).trans (by rw [comp_cP])))`.
-/
theorem val_smul (a : O) (g : GtPt D T)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (χ : D.X)
    (k : T' ⟶ T) {y J} (hJ : Good D.P.L y J) : val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) k.left y J =
      val (g.s (star a • χ)) k.left y J * val₂ u y J (cP D _ χ) (k ≫ g.b) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull_pair u k hJ _ _).trans (by rw [comp_cP])))

/- English proof (translation)
Simplify using `using val_smul oa a g u χ (𝟙 T) hJ`.
-/
theorem val_smul' (a : O) (g : GtPt D T)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (χ : D.X)
    {y J} (hJ : Good D.P.L y J) : val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 T.left) y J =
      cv g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b := by
  simpa using val_smul oa a g u χ (𝟙 T) hJ

/- English proof (translation)
Use `and_congr Iff.rfl ⟨fun h χ y J hJ => ?_, fun h u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩` and prove the remaining obligations. Conclude with `(val_corr hJ (h _ (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 χ) _).symm.trans (val_smul' oa a g _ χ hJ)`. Conclude with `(val_smul' oa a g u χ hJ).trans ((congrArg₂ (· * ·) rfl (IsRos.unique hG D.P.isAb D.P.isLB ⟨hu, u₀⟩ (rosGen_isRos hG oa a) hJ _ _)).trans (h χ y J hJ).symm)`.
-/
theorem isSmulPt_iff (a : O) (g g' : GtPt D T) :
    IsSmulPt oa a g g' ↔ g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ y J, Good D.P.L y J →
      cv g' χ y J = cv g (star a • χ) y J * val₂ (rosGen hG oa a) y J (cP D _ χ) g.b := by
  refine and_congr Iff.rfl ⟨fun h χ y J hJ => ?_, fun h u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · exact (val_corr hJ (h _ (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 χ) _).symm.trans
      (val_smul' oa a g _ χ hJ)
  · exact (val_smul' oa a g u χ hJ).trans ((congrArg₂ (· * ·) rfl
      (IsRos.unique hG D.P.isAb D.P.isLB ⟨hu, u₀⟩ (rosGen_isRos hG oa a) hJ _ _)).trans (h χ y J hJ).symm)

include hG in
/- English proof (translation)
Use `oa.onB.hom (star a)` as an intermediate fact. Establish `vv` using `fun χ y J (hJ : Good D.P.L y J) => val_smul' oa a g (rosGen hG oa a) χ hJ`. Take `⟨g', hb, hv⟩` from `exists_pt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ)) (LB.pullGen D.P.L _ _ (rosGen hG oa a) (lift (cP D _ χ) g.b).left)) (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ (rosGen_isRos hG oa a).1 _)) (fun χ U _ h => by`. Use `(prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_pt g.b (star a • χ) h) (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_` and prove the remaining obligations. Rewrite using `[prod_pt, cPoint_smul oa]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Use the proof step `abel) (fun y J hJ => by`. Establish `C : IsCub (th D (T` using `T) y J) := isCub_cubV D.cub hJ`. Establish `e` using `(rosGen_add hG oa a hJ 1 1 g.b).1`.

Rewrite `e` using `[_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul]`. Use `(vv 0 y J hJ).trans ?_` and prove the remaining obligations. Rewrite using `[smul_zero, cPoint_zero, mul_eq_left.1 e.symm, _root_.mul_one, cv_zero g hJ]) (fun χ χ' y J hJ => by`. Establish `e₁` using `congrArg Additive.ofMul (rosGen_add hG oa a hJ (cP D _ χ) (cP D _ χ') g.b).1`. Establish `e` using `cv_add g hJ (star a • χ) (star a • χ')`.

Rewrite `e` using `[cPoint_smul oa, cPoint_smul oa]`. Establish `e₂` using `congrArg Additive.ofMul e`. Use `(congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)` and prove the remaining obligations. Rewrite using `[smul_add, cPoint_add]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul] at e₁ e₂ ⊢`. Take the linear combination `(norm := abel) e₁ + e₂)`. Conclude with `⟨g', (isSmulPt_iff hG oa _ _ _).2 ⟨hb, fun χ y J hJ => (hv χ _ _ y J hJ).trans (vv χ y J hJ)⟩⟩`.
-/
theorem exists_isSmulPt (a : O) (g : GtPt D T) : ∃ g', IsSmulPt oa a g g' := by
  have := oa.onB.hom (star a)
  have vv := fun χ y J (hJ : Good D.P.L y J) => val_smul' oa a g (rosGen hG oa a) χ hJ
  obtain ⟨g', hb, hv⟩ := exists_pt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
      (LB.pullGen D.P.L _ _ (rosGen hG oa a) (lift (cP D _ χ) g.b).left))
    (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ (rosGen_isRos hG oa a).1 _))
    (fun χ U _ h => by
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_pt g.b (star a • χ) h)
        (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
      rw [prod_pt, cPoint_smul oa]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (fun y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      have e := (rosGen_add hG oa a hJ 1 1 g.b).1
      rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
      refine (vv 0 y J hJ).trans ?_
      rw [smul_zero, cPoint_zero, mul_eq_left.1 e.symm, _root_.mul_one, cv_zero g hJ]) (fun χ χ' y J hJ => by
      have e₁ := congrArg Additive.ofMul (rosGen_add hG oa a hJ (cP D _ χ) (cP D _ χ') g.b).1
      have e := cv_add g hJ (star a • χ) (star a • χ')
      rw [cPoint_smul oa, cPoint_smul oa] at e
      have e₂ := congrArg Additive.ofMul e
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      rw [smul_add, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at e₁ e₂ ⊢
      linear_combination (norm := abel) e₁ + e₂)
  exact ⟨g', (isSmulPt_iff hG oa _ _ _).2 ⟨hb, fun χ y J hJ => (hv χ _ _ y J hJ).trans (vv χ y J hJ)⟩⟩

def smulPt (a : O) (g : GtPt D T) : GtPt D T := (exists_isSmulPt hG oa a g).choose

/- English proof (translation)
The claim follows from `(exists_isSmulPt hG oa a g).choose_spec`.
-/
theorem isSmulPt_smulPt (a : O) (g : GtPt D T) : IsSmulPt oa a g (smulPt hG oa a g) :=
  (exists_isSmulPt hG oa a g).choose_spec

/- English proof (translation)
The claim follows from `((isSmulPt_iff hG oa a g _).1 (isSmulPt_smulPt hG oa a g)).1`.
-/
theorem smulPt_b (a : O) (g : GtPt D T) : (smulPt hG oa a g).b = g.b ≫ oa.onB.act a :=
  ((isSmulPt_iff hG oa a g _).1 (isSmulPt_smulPt hG oa a g)).1

/- English proof (translation)
The claim follows from `((isSmulPt_iff hG oa a g _).1 (isSmulPt_smulPt hG oa a g)).2 χ y J hJ`.
-/
theorem smulPt_val (a : O) (g : GtPt D T) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    cv (smulPt hG oa a g) χ y J = cv g (star a • χ) y J * val₂ (rosGen hG oa a) y J (cP D _ χ) g.b :=
  ((isSmulPt_iff hG oa a g _).1 (isSmulPt_smulPt hG oa a g)).2 χ y J hJ

/- English proof (translation)
Take `⟨b, v⟩` from `(isPull_iff _ _ _).1 h`. Use `(isPull_iff _ _ _).2 ⟨by rw [smulPt_b, smulPt_b, b, Category.assoc], fun χ y J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[smulPt_val hG oa a _ χ hJ, v _ y J hJ, b]`. Conclude with `(val_smul oa a g _ χ k hJ).symm.trans (val_corr hJ ((isSmulPt_smulPt hG oa a g).2 _ (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 χ) _)`.
-/
theorem smulPt_pull (a : O) (k : T' ⟶ T) {g : GtPt D T} {g' : GtPt D T'} (h : GtPt.IsPull k.left g g') :
    GtPt.IsPull k.left (smulPt hG oa a g) (smulPt hG oa a g') := by
  obtain ⟨b, v⟩ := (isPull_iff _ _ _).1 h
  refine (isPull_iff _ _ _).2 ⟨by rw [smulPt_b, smulPt_b, b, Category.assoc], fun χ y J hJ => ?_⟩
  rw [smulPt_val hG oa a _ χ hJ, v _ y J hJ, b]
  exact (val_smul oa a g _ χ k hJ).symm.trans (val_corr hJ ((isSmulPt_smulPt hG oa a g).2 _
    (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 χ) _)

/- English proof (translation)
Use `oa.onB.hom a` as an intermediate fact. Take `⟨b, v⟩` from `(isAdd_iff _ _ _).1 h`. Use `(isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[smulPt_b, smulPt_b, smulPt_b, b, MonObj.mul_comp]`. Establish `e₁` using `congrArg Additive.ofMul (rosGen_add hG oa a hJ g.b g'.b (cP D _ χ)).2`.

Establish `e` using `v (star a • χ) y J hJ`. Rewrite `e` using `[cPoint_smul oa]`. Establish `e₂` using `congrArg Additive.ofMul e`. Rewrite using `[smulPt_val hG oa a _ χ hJ, smulPt_val hG oa a _ χ hJ, smulPt_val hG oa a _ χ hJ, smulPt_b, smulPt_b, b]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul] at e₁ e₂ ⊢`. Take the linear combination `(norm := abel) e₁ + e₂`.
-/
theorem smulPt_add (a : O) {g g' g'' : GtPt D T} (h : g.IsAdd g' g'') :
    (smulPt hG oa a g).IsAdd (smulPt hG oa a g') (smulPt hG oa a g'') := by
  have := oa.onB.hom a
  obtain ⟨b, v⟩ := (isAdd_iff _ _ _).1 h
  refine (isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [smulPt_b, smulPt_b, smulPt_b, b, MonObj.mul_comp]
  · have e₁ := congrArg Additive.ofMul (rosGen_add hG oa a hJ g.b g'.b (cP D _ χ)).2
    have e := v (star a • χ) y J hJ
    rw [cPoint_smul oa] at e
    have e₂ := congrArg Additive.ofMul e
    rw [smulPt_val hG oa a _ χ hJ, smulPt_val hG oa a _ χ hJ, smulPt_val hG oa a _ χ hJ, smulPt_b, smulPt_b, b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at e₁ e₂ ⊢
    linear_combination (norm := abel) e₁ + e₂

/- English proof (translation)
The claim follows from `pt_ext (by rw [smulPt_b, oa.onB.map_one, Category.comp_id]) fun χ y J hJ => by rw [smulPt_val hG oa _ _ χ hJ, IsRos.val_id hG D.P.isAb D.P.isLB (by rw [star_one, oa.onB.map_one]) oa.onB.map_one (rosGen_isRos hG oa 1) hJ, star_one, one_smul, _root_.mul_one]`.
-/
theorem one_smulPt (g : GtPt D T) : smulPt hG oa 1 g = g :=
  pt_ext (by rw [smulPt_b, oa.onB.map_one, Category.comp_id]) fun χ y J hJ => by
    rw [smulPt_val hG oa _ _ χ hJ, IsRos.val_id hG D.P.isAb D.P.isLB (by rw [star_one, oa.onB.map_one])
      oa.onB.map_one (rosGen_isRos hG oa 1) hJ, star_one, one_smul, _root_.mul_one]

/- English proof (translation)
Use `oa.onB.hom a'` as an intermediate fact. Use `oa.onB.hom (star a)` as an intermediate fact. Use `pt_ext (by rw [smulPt_b, smulPt_b, smulPt_b, oa.onB.map_mul, Category.assoc]) fun χ y J hJ => ?_` and prove the remaining obligations. Rewrite using `[smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ _ hJ, IsRos.val_comp hG D.P.isAb D.P.isLB (by rw [star_mul, oa.onB.map_mul]) (oa.onB.map_mul a a') (rosGen_isRos hG oa (a * a')) (rosGen_isRos hG oa a) (rosGen_isRos hG oa a') hJ, smulPt_b, cPoint_smul oa …`.
-/
theorem mul_smulPt (a a' : O) (g : GtPt D T) : smulPt hG oa (a * a') g = smulPt hG oa a (smulPt hG oa a' g) := by
  have := oa.onB.hom a'
  have := oa.onB.hom (star a)
  refine pt_ext (by rw [smulPt_b, smulPt_b, smulPt_b, oa.onB.map_mul, Category.assoc]) fun χ y J hJ => ?_
  rw [smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ _ hJ,
    IsRos.val_comp hG D.P.isAb D.P.isLB (by rw [star_mul, oa.onB.map_mul]) (oa.onB.map_mul a a')
      (rosGen_isRos hG oa (a * a')) (rosGen_isRos hG oa a) (rosGen_isRos hG oa a') hJ,
    smulPt_b, cPoint_smul oa, star_mul, mul_smul, _root_.mul_assoc]

/- English proof (translation)
Use `oa.onB.hom a` as an intermediate fact. Use `oa.onB.hom (star a)` as an intermediate fact. Use `(isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[smulPt_b, smulPt_b, smulPt_b, oa.onB.map_add]`. Conclude with `MonObj.comp_mul _ _ _`.

Establish `e₁` using `congrArg Additive.ofMul (IsRos.val_sum hG D.P.isAb D.cub (by rw [star_add]; exact oa.onB.map_add _ _) (oa.onB.map_add a a') (rosGen_isRos hG oa (a + a')) (rosGen_isRos hG oa a) (rosGen_isRos hG oa a') hJ (cP D _ χ) g.b)`. Establish `e` using `cv_add g hJ (star a • χ) (star a' • χ)`. Rewrite `e` using `[cPoint_smul oa, cPoint_smul oa, ← add_smul, ← star_add]`. Establish `e₂` using `congrArg Additive.ofMul e`. Rewrite using `[smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_b, smulPt_b]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, th] at e₁ e₂ ⊢`. Take the linear combination `(norm := abel) e₁ + e₂`.
-/
theorem add_smulPt (a a' : O) (g : GtPt D T) :
    (smulPt hG oa a g).IsAdd (smulPt hG oa a' g) (smulPt hG oa (a + a') g) := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  refine (isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [smulPt_b, smulPt_b, smulPt_b, oa.onB.map_add]; exact MonObj.comp_mul _ _ _
  · have e₁ := congrArg Additive.ofMul (IsRos.val_sum hG D.P.isAb D.cub
      (by rw [star_add]; exact oa.onB.map_add _ _) (oa.onB.map_add a a')
      (rosGen_isRos hG oa (a + a')) (rosGen_isRos hG oa a) (rosGen_isRos hG oa a') hJ (cP D _ χ) g.b)
    have e := cv_add g hJ (star a • χ) (star a' • χ)
    rw [cPoint_smul oa, cPoint_smul oa, ← add_smul, ← star_add] at e
    have e₂ := congrArg Additive.ofMul e
    rw [smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_val hG oa _ _ χ hJ, smulPt_b, smulPt_b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, th] at e₁ e₂ ⊢
    linear_combination (norm := abel) e₁ + e₂

def Represents {H : Over (Spec (CommRingCat.of R))} [GrpObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T) : Prop :=
  (∀ (T' T : Over (Spec (CommRingCat.of R))) (k : T' ⟶ T) (x : T ⟶ H),
    GtPt.IsPull k.left (Φ T x) (Φ T' (k ≫ x))) ∧
  ∀ (T : Over (Spec (CommRingCat.of R))) (x x' : T ⟶ H), GtPt.IsAdd (Φ T x) (Φ T x') (Φ T (x * x'))

include hG in

/- English proof (translation)
Set `act : O → (H ⟶ H)` to `fun a => (Φ H).symm (smulPt hG oa a (Φ H (𝟙 H)))`. Establish `key : ∀ (a : O) {T} (x : T ⟶ H), Φ T (x ≫ act a) = smulPt hG oa a (Φ T x)` using `fun a T x => by`. Establish `e₁` using `h.1 T H x (act a)`. Establish `e₂` using `smulPt_pull hG oa a x (h.1 T H x (𝟙 H))`. Rewrite `e₂` using `[Category.comp_id]`.

Rewrite `e₁` using `[Equiv.apply_symm_apply]`. Conclude with `isPull_unique e₁ e₂`. Establish `mul : ∀ (a : O) {T} (x x' : T ⟶ H), (x * x') ≫ act a = (x ≫ act a) * (x' ≫ act a)` using `fun a T x x' => by`. Establish `e₁` using `h.2 T (x ≫ act a) (x' ≫ act a)`. Rewrite `e₁` using `[key, key]`.

Conclude with `(Φ T).injective ((key a _).trans (isAdd_unique (smulPt_add hG oa a (h.2 T x x')) e₁))`. Use `⟨⟨act, fun a => ⟨?_, ?_⟩, ?_, fun a b => ?_, fun a b => ?_⟩, fun a T x => ?_⟩` and prove the remaining obligations. Establish `e` using `mul a (1 : 𝟙_ _ ⟶ H) 1`. Rewrite `e` using `[_root_.mul_one]`. Establish `e'` using `mul_eq_left.1 e.symm`.

Simplify `e'` using `[Hom.one_def]`. Establish `e` using `mul a (fst H H) (snd H H)`. Rewrite `e` using `[Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp]`. Rewrite using `[e]`. Use `congr 1`.

Conclude with `(Φ H).injective (by rw [← Category.id_comp (act 1), key, one_smulPt])`. Conclude with `(Φ H).injective (by`. Rewrite using `[← Category.id_comp (act (a * b)), key, mul_smulPt, key, ← Category.id_comp (act b), key])`. Establish `e₁` using `h.2 H (act a) (act b)`. Establish `k` using `fun a => (congrArg (Φ H) (Category.id_comp (act a))).symm.trans (key a (𝟙 H))`.

Rewrite `e₁` using `[k, k]`. Conclude with `(Φ H).injective ((k _).trans (isAdd_unique (add_smulPt hG oa a b _) e₁))`. Rewrite using `[key]`. Conclude with `isSmulPt_smulPt hG oa a _`.
-/
theorem exists_ringAct {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H]
    {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T} (h : Represents Φ) :
    ∃ ρ : RingAct H O, ∀ (a : O) (T) (x : T ⟶ H), IsSmulPt oa a (Φ T x) (Φ T (x ≫ ρ.act a)) := by
  let act : O → (H ⟶ H) := fun a => (Φ H).symm (smulPt hG oa a (Φ H (𝟙 H)))
  have key : ∀ (a : O) {T} (x : T ⟶ H), Φ T (x ≫ act a) = smulPt hG oa a (Φ T x) := fun a T x => by
    have e₁ := h.1 T H x (act a)
    have e₂ := smulPt_pull hG oa a x (h.1 T H x (𝟙 H))
    rw [Category.comp_id] at e₂
    rw [Equiv.apply_symm_apply] at e₁
    exact isPull_unique e₁ e₂
  have mul : ∀ (a : O) {T} (x x' : T ⟶ H), (x * x') ≫ act a = (x ≫ act a) * (x' ≫ act a) := fun a T x x' => by
    have e₁ := h.2 T (x ≫ act a) (x' ≫ act a)
    rw [key, key] at e₁
    exact (Φ T).injective ((key a _).trans (isAdd_unique (smulPt_add hG oa a (h.2 T x x')) e₁))
  refine ⟨⟨act, fun a => ⟨?_, ?_⟩, ?_, fun a b => ?_, fun a b => ?_⟩, fun a T x => ?_⟩
  · have e := mul a (1 : 𝟙_ _ ⟶ H) 1
    rw [_root_.mul_one] at e
    have e' := mul_eq_left.1 e.symm
    simpa [Hom.one_def] using e'
  · have e := mul a (fst H H) (snd H H)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at e
    rw [e]
    congr 1
  · exact (Φ H).injective (by rw [← Category.id_comp (act 1), key, one_smulPt])
  · exact (Φ H).injective (by
      rw [← Category.id_comp (act (a * b)), key, mul_smulPt, key, ← Category.id_comp (act b), key])
  · have e₁ := h.2 H (act a) (act b)
    have k := fun a => (congrArg (Φ H) (Category.id_comp (act a))).symm.trans (key a (𝟙 H))
    rw [k, k] at e₁
    exact (Φ H).injective ((k _).trans (isAdd_unique (add_smulPt hG oa a b _) e₁))
  · rw [key]
    exact isSmulPt_smulPt hG oa a _

end GlobalTheory.TorusModel

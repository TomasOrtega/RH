import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace PositivityTheory.Xgn.HodgeGramConjugation

open scoped CategoryTheory.Obj

/- English proof (translation)
Establish `e` using `Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ h le_top`. Establish `e' : (spMap σ).appLE ⊤ ⊤ le_top = (spMap σ).appTop` using `(Scheme.Hom.app_eq_appLE _).symm`. Rewrite using `[← e, e']`. Conclude with `congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))`.
-/
theorem val_spMap {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} (σ : R →+* R') (x : Sp R ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (((spMap σ ≫ x).appLE U ⊤ h').hom f) =
      σ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((x.appLE U ⊤ h).hom f)) := by
  have e := Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ h le_top
  have e' : (spMap σ).appLE ⊤ ⊤ le_top = (spMap σ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  rw [← e, e']
  exact congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

/- English proof (translation)
Rewrite using `[← Scheme.Hom.appLE_comp_appLE x ψ U V ⊤ e h]`. Both sides reduce to the same expression.
-/
theorem appLE_comp {T X Y : Scheme.{0}} (x : T ⟶ Y) (ψ : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (e : V ≤ ψ ⁻¹ᵁ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U) (f : Γ(X, U)) :
    ((x ≫ ψ).appLE U ⊤ h').hom f = (x.appLE V ⊤ h).hom ((ψ.appLE U V e).hom f) := by
  rw [← Scheme.Hom.appLE_comp_appLE x ψ U V ⊤ e h]
  rfl

/- English proof (translation)
Establish `k : ∀ y : T ⟶ X, ⊤ ≤ y ⁻¹ᵁ U → ⊤ ≤ (c ≫ y) ⁻¹ᵁ U` using `fun y hy t _ => hy (show c t ∈ (⊤ : T.Opens) from trivial)`. Use `⟨fun h => ?_, k x⟩` and prove the remaining obligations. Use `k _ h` as an intermediate fact. Rewrite `this` using `[← Category.assoc, hc, Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem top_le_invol {T X : Scheme.{0}} {c : T ⟶ T} (hc : c ≫ c = 𝟙 T) (x : T ⟶ X) (U : X.Opens) :
    ⊤ ≤ (c ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  have k : ∀ y : T ⟶ X, ⊤ ≤ y ⁻¹ᵁ U → ⊤ ≤ (c ≫ y) ⁻¹ᵁ U := fun y hy t _ => hy (show c t ∈ (⊤ : T.Opens) from trivial)
  refine ⟨fun h => ?_, k x⟩
  have := k _ h
  rwa [← Category.assoc, hc, Category.id_comp] at this

abbrev cj : Sp ℂ ⟶ Sp ℂ := spMap (starRingEnd ℂ)

abbrev dj : Sp (DualNumber ℂ) ⟶ Sp (DualNumber ℂ) := spMap (dualMap (starRingEnd ℂ))

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Use extensionality with `z`. Simplify using the standard rewrite rules.
-/
theorem cj_cj : cj ≫ cj = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext z
  simp

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Use `CommRingCat.hom_ext (RingHom.ext fun z => ?_)` and prove the remaining obligations. Use `show dualMap (starRingEnd ℂ) (dualMap (starRingEnd ℂ) z) = z`. Apply the tactic sequence `ext <;> simp [dualMap]`.
-/
theorem dj_dj : dj ≫ dj = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  show dualMap (starRingEnd ℂ) (dualMap (starRingEnd ℂ) z) = z
  ext <;> simp [dualMap]

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use `CommRingCat.hom_ext (RingHom.ext fun z => ?_)` and prove the remaining obligations. Use `show dualMap (starRingEnd ℂ) (algebraMap ℂ (DualNumber ℂ) z) = algebraMap ℂ (DualNumber ℂ) (starRingEnd ℂ z)`. Apply the tactic sequence `ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dj_eps : dj ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ cj := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  show dualMap (starRingEnd ℂ) (algebraMap ℂ (DualNumber ℂ) z) = algebraMap ℂ (DualNumber ℂ) (starRingEnd ℂ z)
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Unfold `valAt'`. Distinguish the cases in `h : ⊤ ≤ x ⁻¹ᵁ U`. Rewrite using `[dif_pos h, dif_pos ((top_le_invol cj_cj x U).2 h)]`. Conclude with `val_spMap _ x U h _ f`. Rewrite using `[dif_neg h, dif_neg (fun h' => h ((top_le_invol cj_cj x U).1 h')), star_zero]`.
-/
theorem valAt'_cj {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valAt' (cj ≫ x) U f = star (valAt' x U f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [dif_pos h, dif_pos ((top_le_invol cj_cj x U).2 h)]
    exact val_spMap _ x U h _ f
  · rw [dif_neg h, dif_neg (fun h' => h ((top_le_invol cj_cj x U).1 h')), star_zero]

/- English proof (translation)
Unfold `valAt'`. Distinguish the cases in `h : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U)`. Rewrite using `[dif_pos h, dif_pos (show ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U from h)]`. Unfold `valAt`. Rewrite using `[appLE_comp x ψ U _ le_rfl h]`.

Rewrite using `[dif_neg h, dif_neg (show ¬ ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U from h)]`.
-/
theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (ψ : Y ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valAt' (x ≫ ψ) U f = valAt' x (ψ ⁻¹ᵁ U) ((ψ.appLE U _ le_rfl).hom f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (ψ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U from h)]
    unfold valAt
    rw [appLE_comp x ψ U _ le_rfl h]
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ U from h)]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h t ht => (mem_pull (F := ψ) (x := x t)).1 (h ht), fun h t ht => (mem_pull (F := ψ) (x := x t)).2 (h ht)⟩`.
-/
theorem top_le_pull {T X Y : Scheme.{0}} (L : LB X) (x : T ⟶ Y) (ψ : Y ⟶ X) (J : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull ψ).U J ↔ ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (J PUnit.unit) :=
  ⟨fun h t ht => (mem_pull (F := ψ) (x := x t)).1 (h ht), fun h t ht => (mem_pull (F := ψ) (x := x t)).2 (h ht)⟩

/- English proof (translation)
Establish `le : (L.pull ψ).U I ⊓ (L.pull ψ).U J ≤ ψ ⁻¹ᵁ (L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit))` using `fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩`. Establish `h' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ (L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit))` using `fun t ht => le (h ht)`. Unfold `valAt'`. Rewrite using `[dif_pos h, dif_pos h']`. Unfold `valAt`.

Rewrite using `[appLE_comp x ψ _ _ le h h']`. Use `congr 2`. Establish `e : (L.pull ψ).g I J = res le (pullU ψ _ (L.g (I PUnit.unit) (J PUnit.unit)))`. Establish `k : ∀ {M : Type} [CommGroup M] (a : PUnit.{1} → M), ∏ i, a i ^ (1 : ℤ) = a PUnit.unit` using `fun a => by`. Rewrite using `[Fintype.prod_unique, zpow_one]`.

Conclude with `k (fun _ => res le (pullU ψ _ (L.g (I PUnit.unit) (J PUnit.unit))))`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem valAt'_pull_g {X Y : Scheme.{0}} (L : LB X) (x : Sp ℂ ⟶ Y) (ψ : Y ⟶ X) (I J : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull ψ).U I ⊓ (L.pull ψ).U J)) :
    valAt' x ((L.pull ψ).U I ⊓ (L.pull ψ).U J) ((L.pull ψ).g I J).val =
      valAt' (x ≫ ψ) (L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit)) (L.g (I PUnit.unit) (J PUnit.unit)).val := by
  have le : (L.pull ψ).U I ⊓ (L.pull ψ).U J ≤ ψ ⁻¹ᵁ (L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit)) :=
    fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  have h' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ (L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit)) := fun t ht => le (h ht)
  unfold valAt'
  rw [dif_pos h, dif_pos h']
  unfold valAt
  rw [appLE_comp x ψ _ _ le h h']
  congr 2
  have e : (L.pull ψ).g I J = res le (pullU ψ _ (L.g (I PUnit.unit) (J PUnit.unit))) := by
    have k : ∀ {M : Type} [CommGroup M] (a : PUnit.{1} → M), ∏ i, a i ^ (1 : ℤ) = a PUnit.unit := fun a => by
      rw [Fintype.prod_unique, zpow_one]
    exact k (fun _ => res le (pullU ψ _ (L.g (I PUnit.unit) (J PUnit.unit))))
  rw [e]
  rfl

/- English proof (translation)
Introduce `z hz`. Use `(hF.differentiableAt (hs.mem_nhds hz)).star_star` as an intermediate fact. Rewrite `this` using `[star_star]`. Conclude with `this.differentiableWithinAt`.
-/
theorem diffOn_star {g : ℕ} {F : (Fin g → ℂ) → ℂ} {s : Set (Fin g → ℂ)} (hs : IsOpen s) (hF : DifferentiableOn ℂ F s) :
    DifferentiableOn ℂ (fun z => star (F (star z))) {z | star z ∈ s} := by
  intro z hz
  have := (hF.differentiableAt (hs.mem_nhds hz)).star_star
  rw [star_star] at this
  exact this.differentiableWithinAt

/- English proof (translation)
Distinguish the cases in `h : DifferentiableAt ℂ F 0`. Use `h.hasFDerivAt.star_star` as an intermediate fact. Rewrite `this` using `[star_zero]`. Establish `e` using `this.fderiv`. Express the relevant statement in the definitionally equal form `fderiv ℂ (star ∘ F ∘ star) 0 (star w) = _`.

Rewrite using `[e]`. Simplify using the standard rewrite rules. Establish `h' : ¬ DifferentiableAt ℂ (fun z => star (F (star z))) (0 : Fin g → ℂ)` using `fun h' => h (by`. Use `h'.star_star` as an intermediate fact. Rewrite `this` using `[star_zero]`.

Establish `e : (star ∘ (fun z => star (F (star z))) ∘ star) = F`. Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[e] at this)` and apply the resulting hypothesis. Rewrite using `[fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h']`.

Simplify using the standard rewrite rules.
-/
theorem fderiv_star_star {g : ℕ} (F : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    fderiv ℂ (fun z => star (F (star z))) 0 (star w) = star (fderiv ℂ F 0 w) := by
  by_cases h : DifferentiableAt ℂ F 0
  · have := h.hasFDerivAt.star_star
    rw [star_zero] at this
    have e := this.fderiv
    change fderiv ℂ (star ∘ F ∘ star) 0 (star w) = _
    rw [e]
    simp
  · have h' : ¬ DifferentiableAt ℂ (fun z => star (F (star z))) (0 : Fin g → ℂ) := fun h' => h (by
      have := h'.star_star
      rw [star_zero] at this
      have e : (star ∘ (fun z => star (F (star z))) ∘ star) = F := by
        ext z
        simp
      rwa [e] at this)
    rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h']
    simp

/- English proof (translation)
Use `⟨⟨fun p => M.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩` and prove the remaining obligations. Use `(gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_div M M (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))` and prove the remaining obligations. Establish `e₁` using `gm_cocycle hM (𝟙 X) y (i := p.1) (j := q.1) (k := q.2) hy.1.1 hy.2.1 hy.2.2`. Establish `e₂` using `gm_cocycle hM (𝟙 X) y (i := p.1) (j := p.2) (k := q.2) hy.1.1 hy.1.2 hy.2.2`. Use `show gm (𝟙 X) y _ (M.g p.1 q.1) * (gm (𝟙 X) y _ (M.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (M.g q.1 q.2) = gm (𝟙 X) y _ (M.g p.1 p.2)`.

Rewrite using `[mul_right_comm, e₁, ← e₂, mul_inv_cancel_right]`.
-/
theorem lbIso_refl {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) : LBIso M M := by
  refine ⟨⟨fun p => M.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_div M M (𝟙 X) y p q hy)
    (gm_res _ y _ hy _)).trans ?_)))
  have e₁ := gm_cocycle hM (𝟙 X) y (i := p.1) (j := q.1) (k := q.2) hy.1.1 hy.2.1 hy.2.2
  have e₂ := gm_cocycle hM (𝟙 X) y (i := p.1) (j := p.2) (k := q.2) hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (M.g p.1 q.1) * (gm (𝟙 X) y _ (M.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (M.g q.1 q.2) =
    gm (𝟙 X) y _ (M.g p.1 p.2)
  rw [mul_right_comm, e₁, ← e₂, mul_inv_cancel_right]

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

/- English proof (translation)
Establish `e` using `congrArg (fun z => z.left) (map_inv (pushHom h A') (𝟙 A'))`. Establish `e₁ : (𝟙 A' : A' ⟶ A')⁻¹ = GrpObj.inv` using `by rw [Hom.inv_def]; simp`. Rewrite `e` using `[e₁]`. Use `e.trans ?_` and prove the remaining obligations. Rewrite using `[Hom.inv_def, Over.comp_left]`.

Use `show (𝟙 _ ≫ φ) ≫ _ = _`. Rewrite using `[Category.id_comp]`.
-/
theorem inv_comm (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h A') (𝟙 A'))
  have e₁ : (𝟙 A' : A' ⟶ A')⁻¹ = GrpObj.inv := by rw [Hom.inv_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  rw [Hom.inv_def, Over.comp_left]
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

/- English proof (translation)
Take `⟨t, ht⟩` from `hL`. Conclude with `gen_chartPull (chartPullLinComb L φ (fun _ : PUnit => eSec A') (fun _ => eSec A) (fun _ => 1) f fun _ => (cubeMapOf h).e_comm) t ht`.
-/
theorem rigid_pull [IsCommMonObj A] [IsCommMonObj A'] (h : IsGrpPullback A' A f φ) {L : LB A.left} (hL : Out.Rigidified A L) :
    Out.Rigidified A' (L.pull φ) := by
  obtain ⟨t, ht⟩ := hL
  exact gen_chartPull (chartPullLinComb L φ (fun _ : PUnit => eSec A') (fun _ => eSec A) (fun _ => 1) f
    fun _ => (cubeMapOf h).e_comm) t ht

/- English proof (translation)
Introduce `s`. Take `⟨U, hU, t, ht⟩` from `hL (f s)`. Use `⟨f ⁻¹ᵁ U, hU, ?_⟩` and prove the remaining obligations. Establish `le : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U)` using `fun y hy => (congrArg (fun q => q y ∈ U) h.1.w).mpr hy`. Establish `hψ` using `Scheme.Hom.resLE_comp_ι φ le`.

Use `gen_chartPull (chartPullLinComb L φ _ _ _ (φ.resLE _ _ le) fun k => ?_) t ht` and prove the remaining obligations. Use `fin_cases k`. Use `show (_ ≫ _) ≫ φ = _ ≫ _ ≫ _`. Rewrite using `[Category.assoc, inv_comm h, ← Category.assoc, ← hψ, Category.assoc]`. Conclude with `hψ.symm`.
-/
theorem sym_pull (h : IsGrpPullback A' A f φ) {L : LB A.left} (hL : Out.Sym A L) : Out.Sym A' (L.pull φ) := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := hL (f s)
  refine ⟨f ⁻¹ᵁ U, hU, ?_⟩
  have le : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy => (congrArg (fun q => q y ∈ U) h.1.w).mpr hy
  have hψ := Scheme.Hom.resLE_comp_ι φ le
  refine gen_chartPull (chartPullLinComb L φ _ _ _ (φ.resLE _ _ le) fun k => ?_) t ht
  fin_cases k
  · show (_ ≫ _) ≫ φ = _ ≫ _ ≫ _
    rw [Category.assoc, inv_comm h, ← Category.assoc, ← hψ, Category.assoc]
  · exact hψ.symm

end Grp

def pullPol {S : Scheme.{0}} {K : Type} [Field K] (f : Sp K ⟶ S) (P : Out.PolAV S) : Out.PolAV (Sp K) where
  A := (Over.pullback f).obj P.A
  isAb := Out.TLinPf.isAb_pullback f P.A P.isAb
  g := P.g
  smoothDim :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := P.g)).of_isPullback (.of_hasPullback _ f) P.smoothDim
  L := P.L.pull (pullback.fst P.A.hom f)
  isLB := pull_isLB P.isLB _
  rigid := rigid_pull (isGrpPullback_pullback P.A f) P.rigid
  sym := sym_pull (isGrpPullback_pullback P.A f) P.sym
  ample := (amplePt S K f P.A _ _ (isGrpPullback_pullback P.A f) P.L _ P.isLB (pull_isLB P.isLB _)
    (lbIso_refl (pull_isLB P.isLB _)) P.ample P.ktriv).1
  ktriv := (amplePt S K f P.A _ _ (isGrpPullback_pullback P.A f) P.L _ P.isLB (pull_isLB P.isLB _)
    (lbIso_refl (pull_isLB P.isLB _)) P.ample P.ktriv).2

section Conj

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} [IsIso φ]

/- English proof (translation)
Rewrite using `[IsIso.inv_comp_eq, ← Category.assoc, h.1.w, Category.assoc, cj_cj, Category.comp_id]`.
-/
theorem inv_hom (h : IsGrpPullback A' A cj φ) : inv φ ≫ A'.hom = A.hom ≫ cj := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, h.1.w, Category.assoc, cj_cj, Category.comp_id]

def twPt (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) : 𝟙_ (Over (Sp ℂ)) ⟶ A' :=
  Over.homMk (cj ≫ y.left ≫ inv φ) (by
    have e : y.left ≫ A.hom = 𝟙 _ := Over.w y
    show (cj ≫ y.left ≫ inv φ) ≫ A'.hom = 𝟙 _
    rw [Category.assoc, Category.assoc, inv_hom h, reassoc_of% e, cj_cj])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twPt_left (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    (twPt h y).left = cj ≫ y.left ≫ inv φ := rfl

/- English proof (translation)
Rewrite using `[twPt_left]`. Use `erw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]`.
-/
theorem twPt_comp (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    (twPt h y).left ≫ φ = cj ≫ y.left := by
  rw [twPt_left]
  erw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/- English proof (translation)
Set `U : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ cj) ⟶ 𝟙_ (Over (Sp ℂ))` to `Over.homMk cj ((Category.comp_id _).trans (Category.id_comp _).symm)`. Establish `e` using `h.2 _ (twPt h x) (twPt h y) (U ≫ x) (U ≫ y) (twPt_comp h x).symm (twPt_comp h y).symm`. Rewrite `e` using `[← MonObj.comp_mul]`. Use `Over.OverMorphism.ext ((cancel_mono φ).1 ?_)` and prove the remaining obligations. Conclude with `(twPt_comp h _).trans e`.
-/
theorem twPt_mul (h : IsGrpPullback A' A cj φ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    twPt h (x * y) = twPt h x * twPt h y := by
  let U : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ cj) ⟶ 𝟙_ (Over (Sp ℂ)) :=
    Over.homMk cj ((Category.comp_id _).trans (Category.id_comp _).symm)
  have e := h.2 _ (twPt h x) (twPt h y) (U ≫ x) (U ≫ y) (twPt_comp h x).symm (twPt_comp h y).symm
  rw [← MonObj.comp_mul] at e
  refine Over.OverMorphism.ext ((cancel_mono φ).1 ?_)
  exact (twPt_comp h _).trans e

/- English proof (translation)
Introduce `x y e`. Establish `e₁ : cj ≫ x.left = cj ≫ y.left` using `by rw [← twPt_comp h, ← twPt_comp h, e]`. Establish `e₂` using `congrArg (cj ≫ ·) e₁`. Simplify using `only [← Category.assoc, cj_cj, Category.id_comp] at e₂`. Conclude with `Over.OverMorphism.ext e₂`.
-/
theorem twPt_inj (h : IsGrpPullback A' A cj φ) : Function.Injective (twPt h) := by
  intro x y e
  have e₁ : cj ≫ x.left = cj ≫ y.left := by rw [← twPt_comp h, ← twPt_comp h, e]
  have e₂ := congrArg (cj ≫ ·) e₁
  simp only [← Category.assoc, cj_cj, Category.id_comp] at e₂
  exact Over.OverMorphism.ext e₂

/- English proof (translation)
Introduce `y`. Establish `e : y.left ≫ A'.hom = 𝟙 _` using `Over.w y`. Use `⟨Over.homMk (cj ≫ y.left ≫ φ) ?_, Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Use `show (cj ≫ y.left ≫ φ) ≫ A.hom = 𝟙 _`. Rewrite using `[Category.assoc, Category.assoc, h.1.w, reassoc_of% e, cj_cj]`.

Use `show cj ≫ (cj ≫ y.left ≫ φ) ≫ inv φ = y.left`. Rewrite using `[Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id, ← Category.assoc, cj_cj, Category.id_comp]`.
-/
theorem twPt_surj (h : IsGrpPullback A' A cj φ) : Function.Surjective (twPt h) := by
  intro y
  have e : y.left ≫ A'.hom = 𝟙 _ := Over.w y
  refine ⟨Over.homMk (cj ≫ y.left ≫ φ) ?_, Over.OverMorphism.ext ?_⟩
  · show (cj ≫ y.left ≫ φ) ≫ A.hom = 𝟙 _
    rw [Category.assoc, Category.assoc, h.1.w, reassoc_of% e, cj_cj]
  · show cj ≫ (cj ≫ y.left ≫ φ) ≫ inv φ = y.left
    rw [Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id, ← Category.assoc, cj_cj, Category.id_comp]

/- English proof (translation)
The claim follows from `map_eq_one_iff (MonoidHom.mk' (twPt h) (twPt_mul h)) (twPt_inj h)`.
-/
theorem twPt_eq_one (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) : twPt h y = 1 ↔ y = 1 :=
  map_eq_one_iff (MonoidHom.mk' (twPt h) (twPt_mul h)) (twPt_inj h)

def conjLat {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) : Submodule ℤ (Fin g → ℂ) where
  carrier := {z | star z ∈ Λ}
  add_mem' ha hb := by
    show star (_ + _) ∈ Λ
    rw [star_add]; exact Λ.add_mem ha hb
  zero_mem' := by
    show star (0 : Fin g → ℂ) ∈ Λ
    rw [star_zero]; exact Λ.zero_mem
  smul_mem' c z hz := by
    show star (c • z) ∈ Λ
    rw [star_zsmul]; exact Λ.smul_mem c hz

/- English proof (translation)
The claim follows from `top_le_invol cj_cj (y.left ≫ inv φ) U`.
-/
theorem top_le_tw (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (U : A'.left.Opens) :
    ⊤ ≤ (twPt h y).left ⁻¹ᵁ U ↔ ⊤ ≤ y.left ⁻¹ᵁ (inv φ ⁻¹ᵁ U) :=
  top_le_invol cj_cj (y.left ≫ inv φ) U

/- English proof (translation)
The claim follows from `(valAt'_cj (y.left ≫ inv φ) U f).trans (congrArg star (valAt'_comp y.left (inv φ) U f))`.
-/
theorem valAt'_tw (h : IsGrpPullback A' A cj φ) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (U : A'.left.Opens) (f : Γ(A'.left, U)) :
    valAt' (twPt h y).left U f = star (valAt' y.left (inv φ ⁻¹ᵁ U) (((inv φ).appLE U _ le_rfl).hom f)) :=
  (valAt'_cj (y.left ≫ inv φ) U f).trans (congrArg star (valAt'_comp y.left (inv φ) U f))

/- English proof (translation)
Use `(top_le_pull L (twPt h y).left φ J).trans ?_` and prove the remaining obligations. Rewrite using `[twPt_comp]`. Conclude with `top_le_invol cj_cj y.left _`.
-/
theorem top_le_tw_pull (h : IsGrpPullback A' A cj φ) (L : LB A.left) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (J : PUnit → L.ι) :
    ⊤ ≤ (twPt h y).left ⁻¹ᵁ (L.pull φ).U J ↔ ⊤ ≤ y.left ⁻¹ᵁ L.U (J PUnit.unit) := by
  refine (top_le_pull L (twPt h y).left φ J).trans ?_
  rw [twPt_comp]
  exact top_le_invol cj_cj y.left _

def conjUnif (h : IsGrpPullback A' A cj φ) {L : LB A.left} {g : ℕ} (u : HolUnif A L g) : HolUnif A' (L.pull φ) g where
  ex z := twPt h (u.ex (star z))
  ex_add z w := by rw [star_add, u.ex_add, twPt_mul]
  ex_onto := (twPt_surj h).comp (u.ex_onto.comp star_involutive.surjective)
  Λ := conjLat u.Λ
  ker z := (twPt_eq_one h _).trans (u.ker _)
  discrete := by
    have := u.discrete
    refine DiscreteTopology.of_continuous_injective (β := u.Λ) (f := fun z => ⟨star z.1, z.2⟩)
      (Continuous.subtype_mk (continuous_star.comp continuous_subtype_val) _) ?_
    intro a b e
    exact Subtype.ext (star_injective (congrArg Subtype.val e))
  full := by
    have k : ∀ w ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)),
        star w ∈ Submodule.span ℝ (conjLat u.Λ : Set (Fin g → ℂ)) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (show star (star x) ∈ u.Λ by rw [star_star]; exact hx)
      | zero => rw [star_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [star_smul, star_trivial a]; exact Submodule.smul_mem _ _ hx
    refine eq_top_iff.2 fun z _ => ?_
    have := k (star z) (by rw [u.full]; trivial)
    rwa [star_star] at this
  hol U f := by
    obtain ⟨h₁, h₂⟩ := u.hol (inv φ ⁻¹ᵁ U) (((inv φ).appLE U _ le_rfl).hom f)
    simp only [top_le_tw, valAt'_tw]
    exact ⟨h₁.preimage continuous_star, diffOn_star h₁ h₂⟩
  fr J z := star (u.fr (J PUnit.unit) (star z))
  fr_hol J := by
    exact (diffOn_star (u.hol _ 0).1 (u.fr_hol (J PUnit.unit))).mono
      fun z hz => (top_le_tw_pull h L _ J).1 hz
  fr_ne J z hz := star_ne_zero.2 (u.fr_ne _ _ ((top_le_tw_pull h L _ J).1 hz))
  fr_compat I J z hz := by
    have hI := (top_le_tw_pull h L _ I).1 (fun t ht => (hz ht).1)
    have hJ := (top_le_tw_pull h L _ J).1 (fun t ht => (hz ht).2)
    rw [u.fr_compat _ (J PUnit.unit) (star z) (fun t ht => ⟨hI ht, hJ ht⟩), star_mul']
    congr 1
    refine Eq.symm ((valAt'_pull_g L _ φ I J hz).trans ?_)
    rw [twPt_comp]
    exact valAt'_cj _ _ _

/- English proof (translation)
Simplify using `[dotProduct, Matrix.mulVec, Finset.mul_sum]`.
-/
theorem form_star {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    z ⬝ᵥ (Hm.map star).mulVec (star w) = star (star z ⬝ᵥ Hm.mulVec (star (star w))) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum]

/- English proof (translation)
Take `⟨h₁, h₂, h₃, h₄⟩` from `H`. Use `⟨h₁.map _ (fun _ => rfl), fun z hz => ?_, fun l => by rw [norm_star, h₃], fun l J z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[form_star, Complex.star_def, Complex.conj_re]`. Conclude with `h₂ _ (star_ne_zero.2 hz)`. Establish `e` using `h₄ ⟨star l.1, l.2⟩ (J PUnit.unit) (star z) ((top_le_tw_pull h L _ J).1 hz) show star (u.fr _ (star z)) = _ * star (u.fr _ (star (z + l.1)))`.

Rewrite using `[e, form_star, form_star, star_add]`. Simplify using `only [Complex.star_def, map_mul, ← Complex.exp_conj, map_add, map_div₀, Complex.conj_ofReal, map_ofNat]`.
-/
theorem conj_isAH (h : IsGrpPullback A' A cj φ) {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (H : u.IsAH Hm χ) :
    (conjUnif h u).IsAH (Hm.map star) (fun l => star (χ ⟨star l.1, l.2⟩)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := H
  refine ⟨h₁.map _ (fun _ => rfl), fun z hz => ?_, fun l => by rw [norm_star, h₃], fun l J z hz => ?_⟩
  · rw [form_star, Complex.star_def, Complex.conj_re]
    exact h₂ _ (star_ne_zero.2 hz)
  · have e := h₄ ⟨star l.1, l.2⟩ (J PUnit.unit) (star z) ((top_le_tw_pull h L _ J).1 hz)
    show star (u.fr _ (star z)) = _ * star (u.fr _ (star (z + l.1)))
    rw [e, form_star, form_star, star_add]
    simp only [Complex.star_def, map_mul, ← Complex.exp_conj, map_add, map_div₀, Complex.conj_ofReal, map_ofNat]

def twVec (h : IsGrpPullback A' A cj φ) (v : epsR ℂ ⟶ A) : epsR ℂ ⟶ A' :=
  Over.homMk (dj ≫ v.left ≫ inv φ) (by
    have e : v.left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w v
    show (dj ≫ v.left ≫ inv φ) ≫ A'.hom = spMap (algebraMap ℂ (DualNumber ℂ))
    rw [Category.assoc, Category.assoc, inv_hom h, reassoc_of% e, reassoc_of% dj_eps, cj_cj, Category.comp_id])

/- English proof (translation)
Use `show (dj ≫ v.left ≫ inv φ) ≫ φ = _`. Rewrite using `[Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]`.
-/
theorem twVec_comp (h : IsGrpPullback A' A cj φ) (v : epsR ℂ ⟶ A) : (twVec h v).left ≫ φ = dj ≫ v.left := by
  show (dj ≫ v.left ≫ inv φ) ≫ φ = _
  rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/- English proof (translation)
Introduce `U hU f`. Establish `hU' : ⊤ ≤ (v.left ≫ inv φ) ⁻¹ᵁ U` using `(top_le_invol dj_dj (v.left ≫ inv φ) U).1 hU`. Establish `e` using `H (inv φ ⁻¹ᵁ U) hU' (((inv φ).appLE U _ le_rfl).hom f)`. Establish `e₁` using `val_spMap (dualMap (starRingEnd ℂ)) (v.left ≫ inv φ) U hU' hU f`. Establish `e₂` using `appLE_comp v.left (inv φ) U _ le_rfl hU' hU' f`.

Establish `e₃ : (fun z => valAt' ((conjUnif h u).ex z).left U f) = fun z => star (valAt' (u.ex (star z)).left (inv φ ⁻¹ᵁ U) (((inv φ).appLE U _ le_rfl).hom f))`. Use function extensionality and compare the values at `fun z => valAt'_tw h _ U f`. Rewrite using `[e₃]`. Use `Eq.trans ?_ ((congrArg star e).trans (fderiv_star_star _ w).symm)` and prove the remaining obligations. Use `(congrArg TrivSqZeroExt.snd e₁).trans ?_` and prove the remaining obligations.

Rewrite using `[e₂]`. Simplify using `[dualMap]`.
-/
theorem conj_isDiff (h : IsGrpPullback A' A cj φ) {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (H : u.IsDiff w v) : (conjUnif h u).IsDiff (star w) (twVec h v) := by
  intro U hU f
  have hU' : ⊤ ≤ (v.left ≫ inv φ) ⁻¹ᵁ U := (top_le_invol dj_dj (v.left ≫ inv φ) U).1 hU
  have e := H (inv φ ⁻¹ᵁ U) hU' (((inv φ).appLE U _ le_rfl).hom f)
  have e₁ := val_spMap (dualMap (starRingEnd ℂ)) (v.left ≫ inv φ) U hU' hU f
  have e₂ := appLE_comp v.left (inv φ) U _ le_rfl hU' hU' f
  have e₃ : (fun z => valAt' ((conjUnif h u).ex z).left U f) =
      fun z => star (valAt' (u.ex (star z)).left (inv φ ⁻¹ᵁ U) (((inv φ).appLE U _ le_rfl).hom f)) :=
    funext fun z => valAt'_tw h _ U f
  rw [e₃]
  refine Eq.trans ?_ ((congrArg star e).trans (fderiv_star_star _ w).symm)
  refine (congrArg TrivSqZeroExt.snd e₁).trans ?_
  rw [e₂]
  simp [dualMap]

end Conj

end PositivityTheory.Xgn.HodgeGramConjugation

end

open PositivityTheory.Xgn.HodgeGramConjugation in
/- English proof (translation)
Introduce `S G _ L x x' k v v' Γ hx hv ⟨Q, ψ, t, u, Hm, χ, W, hψ, hL, hAH, ht, hΓ⟩`. Establish `: IsIso cj` using `⟨cj, cj_cj, cj_cj⟩`. Establish `h : IsGrpPullback (pullPol cj Q).A Q.A cj (pullback.fst Q.A.hom cj)` using `isGrpPullback_pullback Q.A cj`. Establish `: IsIso (X` using `(pullPol cj Q).A.left) (pullback.fst Q.A.hom cj) := inferInstanceAs (IsIso (pullback.fst Q.A.hom cj))`. Use `⟨pullPol cj Q, pullback.fst Q.A.hom cj ≫ ψ, fun i => twVec h (t i), conjUnif h u, Hm.map star, _, fun i => star (W i), (h.comp hψ).congr hx.symm rfl, ?_, conj_isAH h u hAH, fun i => ⟨?_, conj_isDiff h u (ht i).2⟩, fun i j => ?_⟩` and prove the remaining obligations.

Conclude with `hL.chartPull (chartPullSame L _ _ _ (pullback.fst Q.A.hom cj) fun _ => rfl) (chartPullPull Q.L _ _ rfl)`. Rewrite using `[hv, ← (ht i).1]`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) (twVec_comp h (t i))).trans (Category.assoc _ _ _))`. Establish `e : hermForm (Hm.map star) (star (W i)) (star (W j)) = star (hermForm Hm (W i) (W j))`. Unfold `hermForm`.

Rewrite using `[form_star]`. Simplify using `only [star_star]`. Use `Eq.trans ?_ (congrArg ((Real.pi : ℂ) * ·) e).symm` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, hΓ, star_mul', Complex.star_def, Complex.conj_ofReal]`.
-/
theorem PositivityTheory.Xgn.hodge_gram_complex_conjugate_alt : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Sp ℂ ⟶ S) (k : ℕ) (v : Fin k → (epsAt x ⟶ G)) (v' : Fin k → (epsAt x' ⟶ G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ a, (v' a).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v a).left) → IsHodgeGram G L x v Γ → IsHodgeGram G L x' v' (Γ.map star) := by
  intro S G _ L x x' k v v' Γ hx hv ⟨Q, ψ, t, u, Hm, χ, W, hψ, hL, hAH, ht, hΓ⟩
  have : IsIso cj := ⟨cj, cj_cj, cj_cj⟩
  have h : IsGrpPullback (pullPol cj Q).A Q.A cj (pullback.fst Q.A.hom cj) := isGrpPullback_pullback Q.A cj
  have : IsIso (X := (pullPol cj Q).A.left) (pullback.fst Q.A.hom cj) :=
    inferInstanceAs (IsIso (pullback.fst Q.A.hom cj))
  refine ⟨pullPol cj Q, pullback.fst Q.A.hom cj ≫ ψ, fun i => twVec h (t i), conjUnif h u, Hm.map star, _,
    fun i => star (W i), (h.comp hψ).congr hx.symm rfl, ?_, conj_isAH h u hAH,
    fun i => ⟨?_, conj_isDiff h u (ht i).2⟩, fun i j => ?_⟩
  · exact hL.chartPull (chartPullSame L _ _ _ (pullback.fst Q.A.hom cj) fun _ => rfl) (chartPullPull Q.L _ _ rfl)
  · rw [hv, ← (ht i).1]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) (twVec_comp h (t i))).trans (Category.assoc _ _ _))
  · have e : hermForm (Hm.map star) (star (W i)) (star (W j)) = star (hermForm Hm (W i) (W j)) := by
      unfold hermForm
      rw [form_star]
      simp only [star_star]
    refine Eq.trans ?_ (congrArg ((Real.pi : ℂ) * ·) e).symm
    rw [Matrix.map_apply, hΓ, star_mul', Complex.star_def, Complex.conj_ofReal]

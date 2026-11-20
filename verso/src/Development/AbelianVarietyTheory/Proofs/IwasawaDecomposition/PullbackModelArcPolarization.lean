import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameOfFreeSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntStepZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.PolFin
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.DRFlag (basPull basPull_apply basPull_repr tanPull_tanPull exists_affine_basis)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitGen

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `⟨b.map (tanEquiv m.cart x'), fun i => tanPush_left m.cart x' (b i)⟩`.
-/
theorem exists_basis_push {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
    {S : Type} [CommRing S] {x' : Sp S ⟶ X'} {x : Sp S ⟶ X} (e : x' ≫ f = x) {n : ℕ}
    (b : Module.Basis (Fin n) S (TanM x' t'.G)) :
    ∃ b' : Module.Basis (Fin n) S (TanM x t.G), ∀ i, (tv (b' i)).left = (tv (b i)).left ≫ m.φ := by
  subst e
  exact ⟨b.map (tanEquiv m.cart x'), fun i => tanPush_left m.cart x' (b i)⟩

/- English proof (translation)
Substitute `e` using the available equality. Use `⟨b.map (tanEquiv m.cart x').symm, fun i => (tanPush_left m.cart x' _).symm.trans ?_⟩` and prove the remaining obligations. Conclude with `congrArg (fun v => (tv v).left) ((tanEquiv m.cart x').apply_symm_apply (b i))`.
-/
theorem exists_basis_lift {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
    {S : Type} [CommRing S] (x' : Sp S ⟶ X') {x : Sp S ⟶ X} (e : x' ≫ f = x) {n : ℕ}
    (b : Module.Basis (Fin n) S (TanM x t.G)) :
    ∃ b' : Module.Basis (Fin n) S (TanM x' t'.G), ∀ i, (tv (b' i)).left ≫ m.φ = (tv (b i)).left := by
  subst e
  refine ⟨b.map (tanEquiv m.cart x').symm, fun i => (tanPush_left m.cart x' _).symm.trans ?_⟩
  exact congrArg (fun v => (tv v).left) ((tanEquiv m.cart x').apply_symm_apply (b i))

/- English proof (translation)
The claim follows from `Over.w (tv v)`.
-/
theorem tv_hom {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} (v : TanM x t.G) :
    (tv v).left ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x := Over.w (tv v)

/- English proof (translation)
Take `⟨U, n, hU, hb⟩` from `exists_affine_basis t (closedPoint R)`. Take `⟨bR⟩` from `hb R (𝟙 _) ((IsLocalRing.closed_point_mem_iff (U := U)).1 hU).ge`. Take `⟨bu, hbu⟩` from `exists_basis_lift aT (𝟙 _) (Category.id_comp _) (basPull (algebraMap R (FractionRing R)) (Category.comp_id _) bR)`. Take `⟨b, hb⟩` from `exists_basis_push aC (Category.id_comp _) bu`. Use `⟨n, b, fun V _ _ _ hV ψ gam hg χ h => ?_⟩` and prove the remaining obligations.

Take `⟨Dd, tW, c0, mm, a1, a3, -, e₁, e₂⟩` from `exists_trait_map hu aT aC hV ψ gam hg χ h`. Take `⟨bw, hbw⟩` from `exists_basis_lift a1 (𝟙 _) (Category.id_comp _) (basPull ψ (Category.comp_id _) bR)`. Take `⟨b', hb'⟩` from `exists_basis_push a3 (Category.id_comp _) bw`. Use `⟨b', fun i => tan_ext_left ?_⟩` and prove the remaining obligations. Simplify using `only [basPull_apply, tanPull_left] at hbu hbw`.

Rewrite using `[tanPull_left, tanPull_left, hb, hb']`. Establish `w : (spMap (dualMap gam) ≫ (tv (bu i)).left) ≫ u.G.hom = spMap (algebraMap _ (DualNumber (FractionRing V))) ≫ spMap gam`. Rewrite using `[Category.assoc, tv_hom, Category.comp_id, spMap_comp', spMap_comp', PullbackSections.dualMap_comp_alg]`. Take `⟨ρ, ρ₁, ρ₂⟩ : ∃ ρ : Sp (DualNumber (FractionRing V)) ⟶ Dd.G.left, ρ ≫ c0.φ = spMap (dualMap gam) ≫ (tv (bu i)).left ∧ ρ ≫ Dd.G.hom = spMap (algebraMap _ (DualNumber (FractionRing V)))` from `⟨c0.cart.1.lift _ _ w, c0.cart.1.lift_fst _ _ w, c0.cart.1.lift_snd _ _ w⟩`. Establish `hc : gam.comp (algebraMap R _) = (algebraMap V _).comp ψ` using `RingHom.ext hg`.

Establish `k : ρ ≫ mm.φ = spMap (dualMap (algebraMap V (FractionRing V))) ≫ (tv (bw i)).left`. Apply `a1.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, ← e₁, reassoc_of% ρ₁, hbu, Category.assoc, hbw, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', ← FlagMod.dualMap_comp, ← FlagMod.dualMap_comp, hc]`. Rewrite using `[Category.assoc, mm.cart.1.w, reassoc_of% ρ₂, Category.assoc, tv_hom, Category.comp_id, spMap_comp', spMap_comp', PullbackSections.dualMap_comp_alg]`. Rewrite using `[← reassoc_of% ρ₁, e₂, reassoc_of% k]`.
-/
theorem exists_basis_extends {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {Z : Scheme.{0}} {t : SAB H (Sp R)}
    {tC : SAB H Z} {u : SAB H (Sp (FractionRing R))} {x : Sp (FractionRing R) ⟶ Z} (hu : IsProper u.G.hom)
    (aT : SABMap u t (jK R)) (aC : SABMap u tC x) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (FractionRing R) (TanM x tC.G)),
      ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V), (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ (χ : Sp V ⟶ Z) (h : spMap gam ≫ x = jK V ≫ χ), ∃ b' : Module.Basis (Fin n) V (TanM χ tC.G), ∀ i,
        tanPull gam h (b i) = tanPull (algebraMap V (FractionRing V)) rfl (b' i) := by
  obtain ⟨U, n, hU, hb⟩ := exists_affine_basis t (closedPoint R)
  obtain ⟨bR⟩ := hb R (𝟙 _) ((IsLocalRing.closed_point_mem_iff (U := U)).1 hU).ge
  obtain ⟨bu, hbu⟩ := exists_basis_lift aT (𝟙 _) (Category.id_comp _)
    (basPull (algebraMap R (FractionRing R)) (Category.comp_id _) bR)
  obtain ⟨b, hb⟩ := exists_basis_push aC (Category.id_comp _) bu
  refine ⟨n, b, fun V _ _ _ hV ψ gam hg χ h => ?_⟩
  obtain ⟨Dd, tW, c0, mm, a1, a3, -, e₁, e₂⟩ := exists_trait_map hu aT aC hV ψ gam hg χ h
  obtain ⟨bw, hbw⟩ := exists_basis_lift a1 (𝟙 _) (Category.id_comp _) (basPull ψ (Category.comp_id _) bR)
  obtain ⟨b', hb'⟩ := exists_basis_push a3 (Category.id_comp _) bw
  refine ⟨b', fun i => tan_ext_left ?_⟩
  simp only [basPull_apply, tanPull_left] at hbu hbw
  rw [tanPull_left, tanPull_left, hb, hb']
  have w : (spMap (dualMap gam) ≫ (tv (bu i)).left) ≫ u.G.hom =
      spMap (algebraMap _ (DualNumber (FractionRing V))) ≫ spMap gam := by
    rw [Category.assoc, tv_hom, Category.comp_id, spMap_comp', spMap_comp', PullbackSections.dualMap_comp_alg]
  obtain ⟨ρ, ρ₁, ρ₂⟩ : ∃ ρ : Sp (DualNumber (FractionRing V)) ⟶ Dd.G.left,
      ρ ≫ c0.φ = spMap (dualMap gam) ≫ (tv (bu i)).left ∧
      ρ ≫ Dd.G.hom = spMap (algebraMap _ (DualNumber (FractionRing V))) :=
    ⟨c0.cart.1.lift _ _ w, c0.cart.1.lift_fst _ _ w, c0.cart.1.lift_snd _ _ w⟩
  have hc : gam.comp (algebraMap R _) = (algebraMap V _).comp ψ := RingHom.ext hg
  have k : ρ ≫ mm.φ = spMap (dualMap (algebraMap V (FractionRing V))) ≫ (tv (bw i)).left := by
    apply a1.cart.1.hom_ext
    · rw [Category.assoc, ← e₁, reassoc_of% ρ₁, hbu, Category.assoc, hbw, ← Category.assoc, ← Category.assoc,
        spMap_comp', spMap_comp', ← FlagMod.dualMap_comp, ← FlagMod.dualMap_comp, hc]
    · rw [Category.assoc, mm.cart.1.w, reassoc_of% ρ₂, Category.assoc, tv_hom, Category.comp_id, spMap_comp',
        spMap_comp', PullbackSections.dualMap_comp_alg]
  rw [← reassoc_of% ρ₁, e₂, reassoc_of% k]

end Lie

/- English proof (translation)
Establish `e' : (r.appLE U ⊤ h).hom a.val = (r'.appLE U' ⊤ h').hom a'.val` using `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).hom).1 e`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[gm_val r z U (h trivial), gm_val r' z U' (h' trivial)]`. Conclude with `((Sp F).presheaf.germ_res_apply (homOfLE h) z trivial _).symm.trans ((congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom e').trans ((Sp F).presheaf.germ_res_apply (homOfLE h') z trivial _))`.
-/
theorem gm_eq_of_ev {F : Type} [Field F] {X X' : Scheme.{0}} (r : Sp F ⟶ X) (r' : Sp F ⟶ X') (z : Sp F) {U : X.Opens}
    {U' : X'.Opens} (h : ⊤ ≤ r ⁻¹ᵁ U) (h' : ⊤ ≤ r' ⁻¹ᵁ U') {a : Γ(X, U)ˣ} {a' : Γ(X', U')ˣ}
    (e : ev r U h a.val = ev r' U' h' a'.val) : gm r z U a = gm r' z U' a' := by
  have e' : (r.appLE U ⊤ h).hom a.val = (r'.appLE U' ⊤ h').hom a'.val :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).hom).1 e
  apply Units.ext
  rw [gm_val r z U (h trivial), gm_val r' z U' (h' trivial)]
  exact ((Sp F).presheaf.germ_res_apply (homOfLE h) z trivial _).symm.trans
    ((congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom e').trans
      ((Sp F).presheaf.germ_res_apply (homOfLE h') z trivial _))

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {S : Type} [CommRing S]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Spec.preimage z).hom, Spec.map_preimage z⟩`.
-/
theorem exists_spMap {T : Type} [CommRing T] (z : Sp T ⟶ Sp S) : ∃ φ : S →+* T, spMap φ = z :=
  ⟨(Spec.preimage z).hom, Spec.map_preimage z⟩

/- English proof (translation)
Establish `ha : IsAffineOpen (y ⁻¹ᵁ M.U)`. Use `GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj` as an intermediate fact. Establish `h` using `isAffineOpen_inf_preimage Z.s y M.hU (isAffineOpen_top (Sp S))`. Rewrite `h` using `[top_inf_eq]`. Then use the resulting hypothesis. Take `⟨τ, hτ⟩` from `exists_spMap (tau ha)`.

Establish `h₀ : ⊤ ≤ (spMap τ ≫ y) ⁻¹ᵁ M.U` using `by rw [hτ]; exact le_preimage_map y le_rfl (tau_le _ le_rfl)`. Use `⟨(isUnit_rdet_toMatrix (basPull τ rfl b) (lieBasis M (spMap τ ≫ y) h₀)).unit, fun T _ φ h x e h' => ?_⟩` and prove the remaining obligations. Establish `e₀ : spMap (ev (spMap φ) _ h) ≫ spMap τ = spMap φ` using `by rw [hτ]; exact spMap_ev _ ha h`. Establish `e₁ : spMap (ev (spMap φ) _ h) ≫ spMap τ ≫ y = x` using `by rw [reassoc_of% e₀, e]`. Establish `e₂ : (ev (spMap φ) _ h).comp τ = φ` using `congrArg CommRingCat.Hom.hom (Spec.map_injective ((spMap_comp' _ _).symm.trans e₀))`.

Establish `e₃ : basPull φ e b = basPull _ e₁ (basPull τ rfl b)` using `Module.Basis.eq_of_apply_eq fun i => by`. Rewrite using `[basPull_apply, basPull_apply, basPull_apply, tanPull_tanPull _ _ _ _ (by rw [e₂, e])]`. Apply `tan_ext_left` to reduce the goal to its premises. Rewrite using `[tanPull_left, tanPull_left, e₂]`. Use `(map_rdet _ _).trans (congrArg rdet ?_)` and prove the remaining obligations.

Use extensionality with `i j`. Rewrite using `[e₃, Module.Basis.toMatrix_apply, ← tanPull_lieBasis M _ e₁ h₀ h', basPull_repr]`. Both sides reduce to the same expression.
-/
theorem exists_unit_chart (y : Sp S ⟶ Z.X) {n : ℕ} (b : Module.Basis (Fin n) S (TanM y Z.t.G)) (M : MChart Z) :
    ∃ u : Γ(Sp S, y ⁻¹ᵁ M.U)ˣ, ∀ (T : Type) [CommRing T] (φ : S →+* T) (h : ⊤ ≤ spMap φ ⁻¹ᵁ (y ⁻¹ᵁ M.U))
      (x : Sp T ⟶ Z.X) (e : spMap φ ≫ y = x) (h' : ⊤ ≤ x ⁻¹ᵁ M.U),
      ev (spMap φ) _ h u.val = rdet ((basPull φ e b).toMatrix (lieBasis M x h')) := by
  have ha : IsAffineOpen (y ⁻¹ᵁ M.U) := by
    have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
    have h := isAffineOpen_inf_preimage Z.s y M.hU (isAffineOpen_top (Sp S))
    rwa [top_inf_eq] at h
  obtain ⟨τ, hτ⟩ := exists_spMap (tau ha)
  have h₀ : ⊤ ≤ (spMap τ ≫ y) ⁻¹ᵁ M.U := by rw [hτ]; exact le_preimage_map y le_rfl (tau_le _ le_rfl)
  refine ⟨(isUnit_rdet_toMatrix (basPull τ rfl b) (lieBasis M (spMap τ ≫ y) h₀)).unit, fun T _ φ h x e h' => ?_⟩
  have e₀ : spMap (ev (spMap φ) _ h) ≫ spMap τ = spMap φ := by rw [hτ]; exact spMap_ev _ ha h
  have e₁ : spMap (ev (spMap φ) _ h) ≫ spMap τ ≫ y = x := by rw [reassoc_of% e₀, e]
  have e₂ : (ev (spMap φ) _ h).comp τ = φ :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((spMap_comp' _ _).symm.trans e₀))
  have e₃ : basPull φ e b = basPull _ e₁ (basPull τ rfl b) := Module.Basis.eq_of_apply_eq fun i => by
    rw [basPull_apply, basPull_apply, basPull_apply, tanPull_tanPull _ _ _ _ (by rw [e₂, e])]
    apply tan_ext_left
    rw [tanPull_left, tanPull_left, e₂]
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  rw [e₃, Module.Basis.toMatrix_apply, ← tanPull_lieBasis M _ e₁ h₀ h', basPull_repr]
  rfl

/- English proof (translation)
Use `choose u hu using exists_unit_chart y b`. Establish `le : ∀ j : PUnit → MChart Z, ((detOm Z).pull y).U j ≤ y ⁻¹ᵁ (j PUnit.unit).U` using `fun j => LB.wchart_le (detOm Z) (fun _ : PUnit => y) j PUnit.unit`. Establish `v : ∀ (j : PUnit → MChart Z) (T : Type) [CommRing T] (φ : S →+* T) (h : ⊤ ≤ spMap φ ⁻¹ᵁ ((detOm Z).pull y).U j) (x : Sp T ⟶ Z.X) (e : spMap φ ≫ y = x) (h' : ⊤ ≤ x ⁻¹ᵁ (j PUnit.unit).U), ev (spMap φ) _ h (res (le j) (u (j PUnit.unit))).val = rdet ((basPull φ e b).toMatrix (lieBasi …` using `fun j T _ φ h x e h' => (ev_res _ (le j) h (le_preimage_mono (le j) h) _).trans (hu _ T φ _ x e h')`. Use `⟨⟨fun j => res (le j) (u (j PUnit.unit))⟩, fun i j => Units.ext (ext_ev fun T _ z hz => ?_), v⟩` and prove the remaining obligations. Take `⟨φ, rfl⟩` from `exists_spMap z`.

Establish `hi` using `le_preimage_mono inf_le_left hz`. Establish `hj` using `le_preimage_mono inf_le_right hz`. Establish `hi'` using `le_preimage_map y (le i) hi`. Establish `hj'` using `le_preimage_map y (le j) hj`. Establish `g` using `ev_pull_g (detOm Z) y (spMap φ) i j hz (le_preimage_inf hi' hj')`.

Establish `d` using `ev_detChg (i PUnit.unit) (j PUnit.unit) _ hi' hj' (le_preimage_inf hi' hj')`. Establish `o : ev (spMap φ ≫ y) _ (le_preimage_inf hi' hj') ((detOm Z).g (i PUnit.unit) (j PUnit.unit)).val * ev (spMap φ ≫ y) _ (le_preimage_inf hi' hj') (detChg (i PUnit.unit) (j PUnit.unit)).val = 1` using `(map_mul _ _ _).symm.trans ((congrArg _ (detChg (i PUnit.unit) (j PUnit.unit)).inv_mul).trans (map_one _))`. Use `((ev_res _ _ hz hi _).trans (v i T φ hi _ rfl hi')).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) g ((ev_res _ _ hz hj _).trans (v j T φ hj _ rfl hj')))).symm)` and prove the remaining obligations. Rewrite using `[← rdet_toMatrix_mul _ (lieBasis (i PUnit.unit) _ hi') (lieBasis (j PUnit.unit) _ hj'), ← d, _root_.mul_left_comm]`. Conclude with `(_root_.mul_one _).symm.trans (congrArg _ o.symm)`.
-/
theorem exists_gen_basis (y : Sp S ⟶ Z.X) {n : ℕ} (b : Module.Basis (Fin n) S (TanM y Z.t.G)) :
    ∃ g : LB.Gen ((detOm Z).pull y), g.IsGen ∧ ∀ (j : PUnit → MChart Z) (T : Type) [CommRing T] (φ : S →+* T)
      (h : ⊤ ≤ spMap φ ⁻¹ᵁ ((detOm Z).pull y).U j) (x : Sp T ⟶ Z.X) (e : spMap φ ≫ y = x)
      (h' : ⊤ ≤ x ⁻¹ᵁ (j PUnit.unit).U),
      ev (spMap φ) _ h (g.s j).val = rdet ((basPull φ e b).toMatrix (lieBasis (j PUnit.unit) x h')) := by
  choose u hu using exists_unit_chart y b
  have le : ∀ j : PUnit → MChart Z, ((detOm Z).pull y).U j ≤ y ⁻¹ᵁ (j PUnit.unit).U := fun j =>
    LB.wchart_le (detOm Z) (fun _ : PUnit => y) j PUnit.unit
  have v : ∀ (j : PUnit → MChart Z) (T : Type) [CommRing T] (φ : S →+* T)
      (h : ⊤ ≤ spMap φ ⁻¹ᵁ ((detOm Z).pull y).U j) (x : Sp T ⟶ Z.X) (e : spMap φ ≫ y = x)
      (h' : ⊤ ≤ x ⁻¹ᵁ (j PUnit.unit).U),
      ev (spMap φ) _ h (res (le j) (u (j PUnit.unit))).val =
        rdet ((basPull φ e b).toMatrix (lieBasis (j PUnit.unit) x h')) := fun j T _ φ h x e h' =>
    (ev_res _ (le j) h (le_preimage_mono (le j) h) _).trans (hu _ T φ _ x e h')
  refine ⟨⟨fun j => res (le j) (u (j PUnit.unit))⟩, fun i j => Units.ext (ext_ev fun T _ z hz => ?_), v⟩
  obtain ⟨φ, rfl⟩ := exists_spMap z
  have hi := le_preimage_mono inf_le_left hz
  have hj := le_preimage_mono inf_le_right hz
  have hi' := le_preimage_map y (le i) hi
  have hj' := le_preimage_map y (le j) hj
  have g := ev_pull_g (detOm Z) y (spMap φ) i j hz (le_preimage_inf hi' hj')
  have d := ev_detChg (i PUnit.unit) (j PUnit.unit) _ hi' hj' (le_preimage_inf hi' hj')
  have o : ev (spMap φ ≫ y) _ (le_preimage_inf hi' hj') ((detOm Z).g (i PUnit.unit) (j PUnit.unit)).val *
      ev (spMap φ ≫ y) _ (le_preimage_inf hi' hj') (detChg (i PUnit.unit) (j PUnit.unit)).val = 1 :=
    (map_mul _ _ _).symm.trans ((congrArg _ (detChg (i PUnit.unit) (j PUnit.unit)).inv_mul).trans (map_one _))
  refine ((ev_res _ _ hz hi _).trans (v i T φ hi _ rfl hi')).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) g ((ev_res _ _ hz hj _).trans (v j T φ hj _ rfl hj')))).symm)
  rw [← rdet_toMatrix_mul _ (lieBasis (i PUnit.unit) _ hi') (lieBasis (j PUnit.unit) _ hj'), ← d, _root_.mul_left_comm]
  exact (_root_.mul_one _).symm.trans (congrArg _ o.symm)

/- English proof (translation)
Take `⟨n, b, hb⟩` from `exists_basis_extends hu aT aC`. Take `⟨e, he, ve⟩` from `exists_gen_basis x b`. Use `⟨e, he, fun V _ _ _ hV ψ gam hg χ h => ?_⟩` and prove the remaining obligations. Take `⟨b', hb'⟩` from `hb V hV ψ gam hg χ h`. Take `⟨e', he', ve'⟩` from `exists_gen_basis χ b'`.

Use `⟨e', he', fun z J hJ => ?_⟩` and prove the remaining obligations. Establish `top : ∀ {X : Scheme.{0}} (r : Sp (FractionRing V) ⟶ X) (U : X.Opens), r z ∈ U → ⊤ ≤ r ⁻¹ᵁ U` using `fun r U hz p _ => by`. Rewrite using `[Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) p z]`. Conclude with `hz`. Establish `h₀` using `top _ _ (hJ (jK V ≫ χ))`.

Establish `h₁ : ⊤ ≤ spMap gam ⁻¹ᵁ ((detOm Z).pull x).U fun _ => J (jK V ≫ χ)` using `top _ _ (mem_pull.2 (show (spMap gam ≫ x) z ∈ _ by rw [h]; exact hJ _))`. Establish `h₂ : ⊤ ≤ jK V ⁻¹ᵁ ((detOm Z).pull χ).U fun _ => J (jK V ≫ χ)` using `top _ _ (mem_pull.2 (hJ (jK V ≫ χ)))`. Rewrite using `[val_of e _ z J (fun _ => J (jK V ≫ χ)) (fun _ => by rw [h]), val_of e' _ z J (fun _ => J (jK V ≫ χ)) (fun _ => rfl)]`. Use `gm_eq_of_ev _ _ z h₁ h₂ ((ve _ _ gam h₁ _ h h₀).trans (Eq.trans ?_ (ve' _ _ _ h₂ _ rfl h₀).symm))` and prove the remaining obligations. Rewrite using `[show basPull gam h b = basPull (algebraMap V (FractionRing V)) rfl b' from Module.Basis.eq_of_apply_eq fun i => by rw [basPull_apply, basPull_apply, hb']]`.
-/
theorem exists_detOm_gen_extAt {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {t : SAB H (Sp R)}
    {u : SAB H (Sp (FractionRing R))} {x : Sp (FractionRing R) ⟶ Z.X} (hu : IsProper u.G.hom)
    (aT : SABMap u t (jK R)) (aC : SABMap u Z.t x) :
    ∃ e : LB.Gen ((detOm Z).pull x), e.IsGen ∧ ExtAt (detOm Z) x e := by
  obtain ⟨n, b, hb⟩ := exists_basis_extends hu aT aC
  obtain ⟨e, he, ve⟩ := exists_gen_basis x b
  refine ⟨e, he, fun V _ _ _ hV ψ gam hg χ h => ?_⟩
  obtain ⟨b', hb'⟩ := hb V hV ψ gam hg χ h
  obtain ⟨e', he', ve'⟩ := exists_gen_basis χ b'
  refine ⟨e', he', fun z J hJ => ?_⟩
  have top : ∀ {X : Scheme.{0}} (r : Sp (FractionRing V) ⟶ X) (U : X.Opens), r z ∈ U → ⊤ ≤ r ⁻¹ᵁ U := fun r U hz p _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) p z]
    exact hz
  have h₀ := top _ _ (hJ (jK V ≫ χ))
  have h₁ : ⊤ ≤ spMap gam ⁻¹ᵁ ((detOm Z).pull x).U fun _ => J (jK V ≫ χ) :=
    top _ _ (mem_pull.2 (show (spMap gam ≫ x) z ∈ _ by rw [h]; exact hJ _))
  have h₂ : ⊤ ≤ jK V ⁻¹ᵁ ((detOm Z).pull χ).U fun _ => J (jK V ≫ χ) := top _ _ (mem_pull.2 (hJ (jK V ≫ χ)))
  rw [val_of e _ z J (fun _ => J (jK V ≫ χ)) (fun _ => by rw [h]), val_of e' _ z J (fun _ => J (jK V ≫ χ)) (fun _ => rfl)]
  refine gm_eq_of_ev _ _ z h₁ h₂ ((ve _ _ gam h₁ _ h h₀).trans (Eq.trans ?_ (ve' _ _ _ h₂ _ rfl h₀).symm))
  rw [show basPull gam h b = basPull (algebraMap V (FractionRing V)) rfl b' from
    Module.Basis.eq_of_apply_eq fun i => by rw [basPull_apply, basPull_apply, hb']]

end Gen

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c p W _ _ Z Y bV hbV f t m₁ m₂ _ _ _ O' _ _ _ b' ϖ a χ₀ hO _ x₀ hx`. Establish `: IsLocalRing O'`. Break down `hO with ⟨h, -⟩ | ⟨h, -⟩` into its components or cases. Conclude with `h.toField.instIsLocalRing`. Use `infer_instance`.

Take `⟨tR, ⟨mt⟩⟩` from `exists_sabPull χ₀ Y.t`. Take `⟨u, ⟨n₀⟩⟩` from `exists_sabPull x₀ Z.oF.t`. Take `⟨aC, -⟩` from `LevelCover.sab_comp n₀ Z.m (e := x₀ ≫ Z.j) rfl`. Take `⟨n₁, -⟩` from `LevelCover.sab_comp n₀ Z.m0.toSABMap rfl`. Take `⟨n₂, -⟩` from `LevelCover.sab_cancel Y.m0.toSABMap n₁ x₀ rfl`.

Take `⟨n₃, -⟩` from `LevelCover.sab_comp n₂ Y.m (e := x₀ ≫ Y.j) rfl`. Take `⟨aT, -⟩` from `LevelCover.sab_cancel mt n₃ (jK _) hx`. Establish `hu : IsProper u.G.hom` using `MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper`. Conclude with `exists_detOm_gen_extAt hu aT aC`.
-/
theorem exists_detOm_gen_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ e : LB.Gen ((GlobalTheory.FlagMod.detOm Z).pull (x₀ ≫ Z.j)), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.FlagMod.detOm Z) (x₀ ≫ Z.j) e := by
  intro E _ _ _ H D l Xo c p W _ _ Z Y bV hbV f t m₁ m₂ _ _ _ O' _ _ _ b' ϖ a χ₀ hO _ x₀ hx
  have : IsLocalRing O' := by
    rcases hO with ⟨h, -⟩ | ⟨h, -⟩
    · exact h.toField.instIsLocalRing
    · infer_instance
  obtain ⟨tR, ⟨mt⟩⟩ := exists_sabPull χ₀ Y.t
  obtain ⟨u, ⟨n₀⟩⟩ := exists_sabPull x₀ Z.oF.t
  obtain ⟨aC, -⟩ := LevelCover.sab_comp n₀ Z.m (e := x₀ ≫ Z.j) rfl
  obtain ⟨n₁, -⟩ := LevelCover.sab_comp n₀ Z.m0.toSABMap rfl
  obtain ⟨n₂, -⟩ := LevelCover.sab_cancel Y.m0.toSABMap n₁ x₀ rfl
  obtain ⟨n₃, -⟩ := LevelCover.sab_comp n₂ Y.m (e := x₀ ≫ Y.j) rfl
  obtain ⟨aT, -⟩ := LevelCover.sab_cancel mt n₃ (jK _) hx
  have hu : IsProper u.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper
  exact exists_detOm_gen_extAt hu aT aC

end GlobalTheory.TraitGen

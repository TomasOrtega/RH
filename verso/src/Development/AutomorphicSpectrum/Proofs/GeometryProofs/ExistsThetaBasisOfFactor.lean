import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SecTheta

section Charts

variable {X Y : Scheme.{0}}

/- English proof (translation)
Rewrite using `[GlobalTheory.top_le_preimage_iff_mem]`. Simplify using `only [GlobalTheory.top_le_preimage_comp, GlobalTheory.top_le_preimage_iff_mem]`. Conclude with `Set.mem_iInter`.
-/
theorem top_le_wchart_iff (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (y : Sp ℂ ⟶ Y)
    (j : K → L.ι) : ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  rw [GlobalTheory.top_le_preimage_iff_mem]
  simp only [GlobalTheory.top_le_preimage_comp, GlobalTheory.top_le_preimage_iff_mem]
  exact Set.mem_iInter

/- English proof (translation)
Use `(GlobalTheory.valAt'_units_prod y h _ _).trans (Finset.prod_congr rfl fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[zpow_one]`. Conclude with `(GlobalTheory.valAt'_map y _ _ h).trans (GlobalTheory.valAt'_comp y (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val)`.
-/
theorem val_linComb_g (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (y : Sp ℂ ⟶ Y)
    (j j' : K → L.ι) (h : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' y (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ (fun _ => 1)).g j j').val =
      ∏ k, valAt' (y ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val := by
  refine (GlobalTheory.valAt'_units_prod y h _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
  rw [zpow_one]
  exact (GlobalTheory.valAt'_map y _ _ h).trans (GlobalTheory.valAt'_comp y (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val)

/- English proof (translation)
Establish `e : W ≤ m ⁻¹ᵁ (m ''ᵁ W)` using `by rw [Scheme.Hom.preimage_image_eq]`. Use `⟨m ''ᵁ W, (m.appIso W).inv.hom f, fun y => ⟨?_, fun h => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.top_le_preimage_comp, Scheme.Hom.preimage_image_eq]`. Rewrite using `[← GlobalTheory.valAt'_appLE y m _ W e _ h]`. Use `congr 1`.

Use `Scheme.Hom.appIso_inv_appLE m e` as an intermediate fact. Express the relevant statement in the definitionally equal form `f = ((m.appIso W).inv ≫ m.appLE _ W e).hom f`. Rewrite using `[this]`. Establish `h2 : (homOfLE (le_refl W)).op = 𝟙 _` using `rfl`. Use `erw [h2]`.

Simplify using the standard rewrite rules.
-/
theorem exists_transport (m : Y ⟶ X) [IsOpenImmersion m] (W : Y.Opens) (f : Γ(Y, W)) :
    ∃ (U : X.Opens) (f' : Γ(X, U)), ∀ y : Sp ℂ ⟶ Y,
      (⊤ ≤ y ⁻¹ᵁ W ↔ ⊤ ≤ (y ≫ m) ⁻¹ᵁ U) ∧ (⊤ ≤ y ⁻¹ᵁ W → valAt' y W f = valAt' (y ≫ m) U f') := by
  have e : W ≤ m ⁻¹ᵁ (m ''ᵁ W) := by rw [Scheme.Hom.preimage_image_eq]
  refine ⟨m ''ᵁ W, (m.appIso W).inv.hom f, fun y => ⟨?_, fun h => ?_⟩⟩
  · rw [GlobalTheory.top_le_preimage_comp, Scheme.Hom.preimage_image_eq]
  · rw [← GlobalTheory.valAt'_appLE y m _ W e _ h]
    congr 1
    have := Scheme.Hom.appIso_inv_appLE m e
    change f = ((m.appIso W).inv ≫ m.appLE _ W e).hom f
    rw [this]
    have h2 : (homOfLE (le_refl W)).op = 𝟙 _ := rfl
    erw [h2]
    simp

/- English proof (translation)
Use `GlobalTheory.TangentOrigin.ext_evalPt hW h₁ h₂ (RingHom.ext fun f => ?_)` and prove the remaining obligations. Take `⟨p, rfl⟩` from `hs f`. Establish `key : (GlobalTheory.valAtHom y₁ W h₁).comp (MvPolynomial.eval₂Hom (h.appLE ⊤ W le_top).hom r) = (GlobalTheory.valAtHom y₂ W h₂).comp (MvPolynomial.eval₂Hom (h.appLE ⊤ W le_top).hom r)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]`. Rewrite using `[← GlobalTheory.valAt'_eq_valAtHom y₁ h₁, ← GlobalTheory.valAt'_eq_valAtHom y₂ h₂, GlobalTheory.valAt'_appLE y₁ h ⊤ W le_top a h₁, GlobalTheory.valAt'_appLE y₂ h ⊤ W le_top a h₂, hb]`. Introduce `j`. Simplify using `only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]`. Rewrite using `[← GlobalTheory.valAt'_eq_valAtHom y₁ h₁, ← GlobalTheory.valAt'_eq_valAtHom y₂ h₂, hr]`.

Conclude with `RingHom.congr_fun key p`.
-/
theorem eq_of_generators {B : Scheme.{0}} (h : Y ⟶ B) {W : Y.Opens} (hW : IsAffineOpen W) {n : ℕ}
    (r : Fin n → Γ(Y, W))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (h.appLE ⊤ W le_top).hom r))
    {y₁ y₂ : Sp ℂ ⟶ Y} (h₁ : ⊤ ≤ y₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ y₂ ⁻¹ᵁ W) (hb : y₁ ≫ h = y₂ ≫ h)
    (hr : ∀ j, valAt' y₁ W (r j) = valAt' y₂ W (r j)) : y₁ = y₂ := by
  refine GlobalTheory.TangentOrigin.ext_evalPt hW h₁ h₂ (RingHom.ext fun f => ?_)
  obtain ⟨p, rfl⟩ := hs f
  have key : (GlobalTheory.valAtHom y₁ W h₁).comp (MvPolynomial.eval₂Hom (h.appLE ⊤ W le_top).hom r) =
      (GlobalTheory.valAtHom y₂ W h₂).comp (MvPolynomial.eval₂Hom (h.appLE ⊤ W le_top).hom r) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [← GlobalTheory.valAt'_eq_valAtHom y₁ h₁, ← GlobalTheory.valAt'_eq_valAtHom y₂ h₂,
        GlobalTheory.valAt'_appLE y₁ h ⊤ W le_top a h₁, GlobalTheory.valAt'_appLE y₂ h ⊤ W le_top a h₂, hb]
    · intro j
      simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      rw [← GlobalTheory.valAt'_eq_valAtHom y₁ h₁, ← GlobalTheory.valAt'_eq_valAtHom y₂ h₂, hr]
  exact RingHom.congr_fun key p

end Charts

section Frames

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def lp (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) : Sp ℂ ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme :=
  IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left (by
    rw [Scheme.Opens.range_ι]
    intro _ _
    trivial)

/- English proof (translation)
The claim follows from `IsOpenImmersion.lift_fac _ _ _`.
-/
theorem lp_comp (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) : lp x ≫ (A.hom ⁻¹ᵁ ⊤).ι = x.left :=
  IsOpenImmersion.lift_fac _ _ _

/- English proof (translation)
Rewrite using `[← cancel_mono (⊤ : (Sp ℂ).Opens).ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc, ← Category.assoc, lp_comp, lp_comp, Over.w x, Over.w x']`.
-/
theorem lp_base (x x' : 𝟙_ (Over (Sp ℂ)) ⟶ A) : lp x ≫ (A.hom ∣_ ⊤) = lp x' ≫ (A.hom ∣_ ⊤) := by
  rw [← cancel_mono (⊤ : (Sp ℂ).Opens).ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, ← Category.assoc, lp_comp, lp_comp, Over.w x, Over.w x']

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← lp_comp x, ← lp_comp x', h]`.
-/
theorem lp_injective {x x' : 𝟙_ (Over (Sp ℂ)) ⟶ A} (h : lp x = lp x') : x = x' := by
  apply Over.OverMorphism.ext
  rw [← lp_comp x, ← lp_comp x', h]

/- English proof (translation)
Use `(top_le_wchart_iff L _ (lp x) j).trans ?_` and prove the remaining obligations. Simplify using `only [lp_comp]`.
-/
theorem chart_iff {N : ℕ} (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (j : (Out.powOver A L ⊤ N).ι) :
    ⊤ ≤ (lp x) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j ↔ ∀ k, ⊤ ≤ x.left ⁻¹ᵁ L.U (j k) := by
  refine (top_le_wchart_iff L _ (lp x) j).trans ?_
  simp only [lp_comp]

/- English proof (translation)
Establish `hmem : x.left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i`. Rewrite using `[hL.cover]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hmem`. Conclude with `⟨fun _ => i, (chart_iff x _).2 fun _ => (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi⟩`.
-/
theorem exists_chart (hL : L.IsLB) (N : ℕ) (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) :
    ∃ j : (Out.powOver A L ⊤ N).ι, ⊤ ≤ (lp x) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j := by
  have hmem : x.left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
    rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  exact ⟨fun _ => i, (chart_iff x _).2 fun _ => (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi⟩

variable (u : HolUnif A L g)

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun k _ => u.fr_ne _ z ((chart_iff _ j).1 hj k)`.
-/
theorem frame_ne {N : ℕ} (z : Fin g → ℂ) (j : (Out.powOver A L ⊤ N).ι)
    (hj : ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j) : ∏ k, u.fr (j k) z ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => u.fr_ne _ z ((chart_iff _ j).1 hj k)

/- English proof (translation)
Establish `hW : ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ ((Out.powOver A L ⊤ N).U j ⊓ (Out.powOver A L ⊤ N).U j')` using `(GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨hj, hj'⟩`. Establish `hc` using `congrArg (valAt' (lp (u.ex z)) _) (s.compat j j')`. Rewrite `hc` using `[GlobalTheory.valAt'_mul, GlobalTheory.valAt'_map _ _ _ hW, GlobalTheory.valAt'_map _ _ _ hW]`. Establish `hg` using `val_linComb_g L (fun _ : Fin N => (A.hom ⁻¹ᵁ ⊤).ι) (lp (u.ex z)) j j' hW`. Simplify using `only [lp_comp] at hg`.

Establish `hF : ∏ k, u.fr (j k) z = (∏ k, valAt' (u.ex z).left (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val) * ∏ k, u.fr (j' k) z`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => u.fr_compat _ _ z ((GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨(chart_iff _ j).1 hj k, (chart_iff _ j').1 hj' k⟩)`. Establish `hne` using `frame_ne u z j hj`. Rewrite `hne`, the goal using `[hF]`.

Establish `hG` using `left_ne_zero_of_mul hne`. Establish `hc' : valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j) (s.f j) = (∏ k, valAt' (u.ex z).left (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val) * valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j') (s.f j')`. Rewrite using `[← hg]`. Conclude with `hc`. Rewrite using `[hc', mul_div_mul_left _ _ hG]`.
-/
theorem quot_eq {N : ℕ} (s : LB.Sec (Out.powOver A L ⊤ N)) (z : Fin g → ℂ)
    (j j' : (Out.powOver A L ⊤ N).ι) (hj : ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j)
    (hj' : ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j') :
    valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j) (s.f j) / ∏ k, u.fr (j k) z =
      valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j') (s.f j') / ∏ k, u.fr (j' k) z := by
  have hW : ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ ((Out.powOver A L ⊤ N).U j ⊓ (Out.powOver A L ⊤ N).U j') :=
    (GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨hj, hj'⟩
  have hc := congrArg (valAt' (lp (u.ex z)) _) (s.compat j j')
  rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_map _ _ _ hW, GlobalTheory.valAt'_map _ _ _ hW] at hc
  have hg := val_linComb_g L (fun _ : Fin N => (A.hom ⁻¹ᵁ ⊤).ι) (lp (u.ex z)) j j' hW
  simp only [lp_comp] at hg
  have hF : ∏ k, u.fr (j k) z =
      (∏ k, valAt' (u.ex z).left (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val) *
        ∏ k, u.fr (j' k) z := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => u.fr_compat _ _ z
      ((GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨(chart_iff _ j).1 hj k, (chart_iff _ j').1 hj' k⟩)
  have hne := frame_ne u z j hj
  rw [hF] at hne ⊢
  have hG := left_ne_zero_of_mul hne
  have hc' : valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j) (s.f j) =
      (∏ k, valAt' (u.ex z).left (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val) *
        valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j') (s.f j') := by
    rw [← hg]; exact hc
  rw [hc', mul_div_mul_left _ _ hG]

/- English proof (translation)
Take `⟨U, f', h⟩` from `exists_transport (A.hom ⁻¹ᵁ ⊤).ι W f`. Establish `hset : {z | ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ W} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U}`. Use extensionality with `z`. Use `(h (lp (u.ex z))).1` as an intermediate fact. Rewrite `this` using `[lp_comp]`.

Conclude with `this`. Take `⟨ho, hd⟩` from `u.hol U f'`. Rewrite using `[hset]`. Use `⟨ho, hd.congr fun z hz => ?_⟩` and prove the remaining obligations. Establish `h2` using `(h (lp (u.ex z))).2 (by rw [← Set.mem_setOf_eq (p := fun z => ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ W), hset]; exact hz)`.

Rewrite `h2` using `[lp_comp]`. Conclude with `h2`.
-/
theorem hol_lp (W : (A.hom ⁻¹ᵁ ⊤).toScheme.Opens) (f : Γ((A.hom ⁻¹ᵁ ⊤).toScheme, W)) :
    IsOpen {z | ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ W} ∧
      DifferentiableOn ℂ (fun z => valAt' (lp (u.ex z)) W f) {z | ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ W} := by
  obtain ⟨U, f', h⟩ := exists_transport (A.hom ⁻¹ᵁ ⊤).ι W f
  have hset : {z | ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ W} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} := by
    ext z
    have := (h (lp (u.ex z))).1
    rw [lp_comp] at this
    exact this
  obtain ⟨ho, hd⟩ := u.hol U f'
  rw [hset]
  refine ⟨ho, hd.congr fun z hz => ?_⟩
  have h2 := (h (lp (u.ex z))).2 (by rw [← Set.mem_setOf_eq (p := fun z => ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ W), hset]; exact hz)
  rw [lp_comp] at h2
  exact h2

/- English proof (translation)
Use `choose c hc using fun z => exists_chart (L := L) hL N (u.ex z)`. Conclude with `⟨fun z => valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U (c z)) (s.f (c z)) / ∏ k, u.fr (c z k) z, fun z j hj => quot_eq u s z _ _ (hc z) hj⟩`.
-/
theorem exists_theta (hL : L.IsLB) {N : ℕ} (s : LB.Sec (Out.powOver A L ⊤ N)) :
    ∃ Θ : (Fin g → ℂ) → ℂ, ∀ z j, ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j →
      Θ z = valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j) (s.f j) / ∏ k, u.fr (j k) z := by
  choose c hc using fun z => exists_chart (L := L) hL N (u.ex z)
  exact ⟨fun z => valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U (c z)) (s.f (c z)) /
    ∏ k, u.fr (c z k) z, fun z j hj => quot_eq u s z _ _ (hc z) hj⟩

variable {u}

/- English proof (translation)
Introduce `z` and use `by obtain ⟨j, hj⟩ := exists_chart (L := L) hL N (u.ex z) obtain ⟨ho, hd⟩ := hol_lp u _ (s.f j) have hn := ho.mem_nhds hj have hF : DifferentiableOn ℂ (fun w => ∏ k, u.fr (j k) w) {w | ⊤ ≤ (lp (u.ex w)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j} := by have key : ∀ t : Finset (Fin N), Differen …`.
-/
theorem theta_differentiable (hL : L.IsLB) {N : ℕ} {s : LB.Sec (Out.powOver A L ⊤ N)}
    {Θ : (Fin g → ℂ) → ℂ}
    (hΘ : ∀ z j, ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j →
      Θ z = valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j) (s.f j) / ∏ k, u.fr (j k) z) :
    Differentiable ℂ Θ := fun z => by
  obtain ⟨j, hj⟩ := exists_chart (L := L) hL N (u.ex z)
  obtain ⟨ho, hd⟩ := hol_lp u _ (s.f j)
  have hn := ho.mem_nhds hj
  have hF : DifferentiableOn ℂ (fun w => ∏ k, u.fr (j k) w)
      {w | ⊤ ≤ (lp (u.ex w)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j} :=
    by
    have key : ∀ t : Finset (Fin N), DifferentiableOn ℂ (fun w => ∏ k ∈ t, u.fr (j k) w)
        {w | ⊤ ≤ (lp (u.ex w)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j} := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using differentiableOn_const (1 : ℂ)
      | insert a t ha ih =>
        simp only [Finset.prod_insert ha]
        exact ((u.fr_hol _).mono fun w hw => (chart_iff _ j).1 hw a).mul ih
    exact key _
  have hq := (hd.differentiableAt hn).mul ((hF.differentiableAt hn).inv (frame_ne u z j hj))
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [hn] with w hw
  exact (hΘ w j hw).trans (div_eq_mul_inv _ _)

/- English proof (translation)
Take `⟨j, hj⟩` from `exists_chart (L := L) hL N (u.ex z)`. Establish `he : u.ex (z + l) = u.ex z` using `GlobalTheory.SectionTheta.ex_add_lattice u z l`. Establish `hj' : ⊤ ≤ (lp (u.ex (z + l))) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j` using `by rw [he]; exact hj`. Establish `h1` using `hΘ z j hj`. Establish `h2` using `hΘ (z + l) j hj'`.

Rewrite `h2` using `[he]`. Establish `hF : ∏ k, u.fr (j k) z = a ^ N * ∏ k, u.fr (j k) (z + l)`. Establish `: a ^ N = ∏ _k : Fin N, a` using `by simp`. Rewrite using `[this, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => hlaw _ ((chart_iff _ j).1 hj k)`.

Establish `hne` using `frame_ne u z j hj`. Rewrite `hne` using `[hF]`. Establish `ha` using `left_ne_zero_of_mul hne`. Establish `hb` using `right_ne_zero_of_mul hne`. Rewrite using `[h1, h2, hF]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem theta_add (hL : L.IsLB) {N : ℕ} {s : LB.Sec (Out.powOver A L ⊤ N)}
    {Θ : (Fin g → ℂ) → ℂ}
    (hΘ : ∀ z j, ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j →
      Θ z = valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j) (s.f j) / ∏ k, u.fr (j k) z)
    (l : u.Λ) (z : Fin g → ℂ) (a : ℂ)
    (hlaw : ∀ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a * u.fr i (z + l)) :
    Θ (z + l) = a ^ N * Θ z := by
  obtain ⟨j, hj⟩ := exists_chart (L := L) hL N (u.ex z)
  have he : u.ex (z + l) = u.ex z := GlobalTheory.SectionTheta.ex_add_lattice u z l
  have hj' : ⊤ ≤ (lp (u.ex (z + l))) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j := by rw [he]; exact hj
  have h1 := hΘ z j hj
  have h2 := hΘ (z + l) j hj'
  rw [he] at h2
  have hF : ∏ k, u.fr (j k) z = a ^ N * ∏ k, u.fr (j k) (z + l) := by
    have : a ^ N = ∏ _k : Fin N, a := by simp
    rw [this, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => hlaw _ ((chart_iff _ j).1 hj k)
  have hne := frame_ne u z j hj
  rw [hF] at hne
  have ha := left_ne_zero_of_mul hne
  have hb := right_ne_zero_of_mul hne
  rw [h1, h2, hF]
  field_simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨j, hj⟩` from `exists_chart (L := L) hL N (u.ex z)`. Rewrite `h` using `[hΘ z j hj]`. Establish `hv` using `left_ne_zero_of_mul (by rwa [div_eq_mul_inv] at h)`.

Establish `hb` using `(GlobalTheory.top_le_preimage_basicOpen_iff _ _ _).2 hv`. Conclude with `GlobalTheory.top_le_preimage_mono _ (le_iSup (fun k => _ : _ → _) j) hb`. Introduce `h`. Establish `hm` using `(GlobalTheory.top_le_preimage_iff_mem _ _).1 h`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 hm`.

Establish `hb` using `(GlobalTheory.top_le_preimage_iff_mem _ _).2 hk`. Establish `hv` using `(GlobalTheory.top_le_preimage_basicOpen_iff _ _ _).1 hb`. Establish `hj` using `GlobalTheory.top_le_preimage_of_valAt'_ne_zero _ hv`. Rewrite using `[hΘ z k hj]`. Conclude with `div_ne_zero hv (frame_ne u z k hj)`.
-/
theorem theta_ne_zero_iff (hL : L.IsLB) {N : ℕ} {s : LB.Sec (Out.powOver A L ⊤ N)}
    {Θ : (Fin g → ℂ) → ℂ}
    (hΘ : ∀ z j, ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j →
      Θ z = valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j) (s.f j) / ∏ k, u.fr (j k) z)
    (z : Fin g → ℂ) : Θ z ≠ 0 ↔ ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ Out.nonzeroLocus s := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_chart (L := L) hL N (u.ex z)
    rw [hΘ z j hj] at h
    have hv := left_ne_zero_of_mul (by rwa [div_eq_mul_inv] at h)
    have hb := (GlobalTheory.top_le_preimage_basicOpen_iff _ _ _).2 hv
    exact GlobalTheory.top_le_preimage_mono _ (le_iSup (fun k => _ : _ → _) j) hb
  · intro h
    have hm := (GlobalTheory.top_le_preimage_iff_mem _ _).1 h
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    have hb := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hk
    have hv := (GlobalTheory.top_le_preimage_basicOpen_iff _ _ _).1 hb
    have hj := GlobalTheory.top_le_preimage_of_valAt'_ne_zero _ hv
    rw [hΘ z k hj]
    exact div_ne_zero hv (frame_ne u z k hj)

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_chart (L := L) hL N (u.ex z)`. Establish `hW : ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ (Out.nonzeroLocus si ⊓ (Out.powOver A L ⊤ N).U k)` using `(GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨hz, hk⟩`. Establish `hc` using `congrArg (valAt' (lp (u.ex z)) _) (hr k)`. Rewrite `hc` using `[GlobalTheory.valAt'_mul, GlobalTheory.valAt'_map _ _ _ hW, GlobalTheory.valAt'_map _ _ _ hW, GlobalTheory.valAt'_map _ _ _ hW]`. Rewrite using `[hi z k hk, hj z k hk, hc, mul_div_assoc]`.
-/
theorem val_ratio (hL : L.IsLB) {N : ℕ} {si sj : LB.Sec (Out.powOver A L ⊤ N)}
    {Θi Θj : (Fin g → ℂ) → ℂ}
    (hi : ∀ z j, ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j →
      Θi z = valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j) (si.f j) / ∏ k, u.fr (j k) z)
    (hj : ∀ z j, ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ (Out.powOver A L ⊤ N).U j →
      Θj z = valAt' (lp (u.ex z)) ((Out.powOver A L ⊤ N).U j) (sj.f j) / ∏ k, u.fr (j k) z)
    (r : Γ((A.hom ⁻¹ᵁ ⊤).toScheme, Out.nonzeroLocus si))
    (hr : ∀ k, ((A.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus si ⊓ (Out.powOver A L ⊤ N).U k ≤ (Out.powOver A L ⊤ N).U k)).op).hom
                (sj.f k) =
            ((A.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_left :
              Out.nonzeroLocus si ⊓ (Out.powOver A L ⊤ N).U k ≤ Out.nonzeroLocus si)).op).hom r *
            ((A.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus si ⊓ (Out.powOver A L ⊤ N).U k ≤ (Out.powOver A L ⊤ N).U k)).op).hom
                (si.f k))
    (z : Fin g → ℂ) (hz : ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ Out.nonzeroLocus si) :
    valAt' (lp (u.ex z)) (Out.nonzeroLocus si) r * Θi z = Θj z := by
  obtain ⟨k, hk⟩ := exists_chart (L := L) hL N (u.ex z)
  have hW : ⊤ ≤ (lp (u.ex z)) ⁻¹ᵁ (Out.nonzeroLocus si ⊓ (Out.powOver A L ⊤ N).U k) :=
    (GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨hz, hk⟩
  have hc := congrArg (valAt' (lp (u.ex z)) _) (hr k)
  rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_map _ _ _ hW, GlobalTheory.valAt'_map _ _ _ hW, GlobalTheory.valAt'_map _ _ _ hW] at hc
  rw [hi z k hk, hj z k hk, hc, mul_div_assoc]

end Frames

/- English proof (translation)
Assume the negation of the conclusion as `hw`. Take `⟨ε, hε, hb⟩` from `Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set Λ)) 0 rfl`. Establish `hwn : 0 < ‖w‖` using `norm_pos_iff.2 hw`. Establish `hp : 0 < ε / (2 * ‖w‖)` using `by positivity`. Establish `h1 : (⟨((ε / (2 * ‖w‖) : ℝ) : ℂ) • w, hm _⟩ : Λ) ∈ Metric.ball (0 : Λ) ε`.

Rewrite using `[Metric.mem_ball, Subtype.dist_eq]`. Express the relevant statement in the definitionally equal form `dist (((ε / (2 * ‖w‖) : ℝ) : ℂ) • w) 0 < ε`. Rewrite using `[dist_zero_right, norm_smul, Complex.norm_real, Real.norm_of_nonneg hp.le]`. Establish `: ε / (2 * ‖w‖) * ‖w‖ = ε / 2` using `by field_simp`. Rewrite using `[this]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ((ε / (2 * ‖w‖) : ℝ) : ℂ) • w = 0` using `congrArg Subtype.val (hb h1)`. Break down `smul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `hp.ne' (Complex.ofReal_eq_zero.1 h3)`. Conclude with `hw h3`.
-/
theorem eq_zero_of_smul_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (hΛ : DiscreteTopology Λ)
    (w : Fin g → ℂ) (hm : ∀ t : ℂ, t • w ∈ Λ) : w = 0 := by
  by_contra hw
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set Λ)) 0 rfl
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hp : 0 < ε / (2 * ‖w‖) := by positivity
  have h1 : (⟨((ε / (2 * ‖w‖) : ℝ) : ℂ) • w, hm _⟩ : Λ) ∈ Metric.ball (0 : Λ) ε := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    change dist (((ε / (2 * ‖w‖) : ℝ) : ℂ) • w) 0 < ε
    rw [dist_zero_right, norm_smul, Complex.norm_real, Real.norm_of_nonneg hp.le]
    have : ε / (2 * ‖w‖) * ‖w‖ = ε / 2 := by field_simp
    rw [this]
    linarith
  have h2 : ((ε / (2 * ‖w‖) : ℝ) : ℂ) • w = 0 := congrArg Subtype.val (hb h1)
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact hp.ne' (Complex.ofReal_eq_zero.1 h3)
  · exact hw h3

/- English proof (translation)
Introduce `A _ L g u Hm χ hL _ hamp hlaw`. Take `⟨N, hN, M, s, hcov, H⟩` from `hamp ⊤ (isAffineOpen_top _)`. Use `choose Θ hΘ using fun i => exists_theta u hL (s i)`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi0⟩ : ∃ i, Θ i 0 ≠ 0 := by`. Establish `hm : (lp (u.ex 0)) (default : PrimeSpectrum ℂ) ∈ ⨆ i, Out.nonzeroLocus (s i)`.

Rewrite using `[hcov]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hm`. Conclude with `⟨i, (theta_ne_zero_iff hL (hΘ i) 0).2 ((GlobalTheory.top_le_preimage_iff_mem _ _).2 hi)⟩`. Use `⟨N, Fin (M + 1), Θ, hN, fun i => theta_differentiable hL (hΘ i), fun i l z => theta_add hL (hΘ i) l z _ fun i' h => hlaw l i' z h, ⟨i, fun h => hi0 (by rw [h]; rfl)⟩, fun w hw hinv => hw ?_⟩` and prove the remaining obligations.

Take `⟨haff, r, hr, hs⟩` from `H i`. Establish `hconst : ∀ j (t : ℂ), Θ j (t • w) = Θ j 0` using `fun j t => by simpa using hinv j t 0`. Establish `hD0` using `(theta_ne_zero_iff hL (hΘ i) 0).1 hi0`. Establish `hD : ∀ t : ℂ, ⊤ ≤ (lp (u.ex (t • w))) ⁻¹ᵁ Out.nonzeroLocus (s i)` using `fun t => (theta_ne_zero_iff hL (hΘ i) _).1 (by rw [hconst]; exact hi0)`. Establish `hy : ∀ t : ℂ, lp (u.ex (t • w)) = lp (u.ex 0)` using `fun t => eq_of_generators (A.hom ∣_ ⊤) haff r hs (hD t) hD0 (lp_base _ _) fun j => by`.

Establish `h1` using `val_ratio hL (hΘ i) (hΘ j) (r j) (hr j) (t • w) (hD t)`. Establish `h2` using `val_ratio hL (hΘ i) (hΘ j) (r j) (hr j) 0 hD0`. Rewrite `h1` using `[hconst, hconst]`. Conclude with `mul_right_cancel₀ hi0 (h1.trans h2.symm)`. Use `eq_zero_of_smul_mem u.Λ u.discrete w fun t => (u.ker _).1 ?_` and prove the remaining obligations.

Rewrite using `[lp_injective (hy t)]`. Conclude with `(u.ker 0).2 (zero_mem _)`.
-/
theorem exists_theta_family : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsAbelianScheme A → Out.RelAmple A L → (∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)) → ∃ (N : ℕ) (J : Type) (Θ : J → (Fin g → ℂ) → ℂ), 0 < N ∧ (∀ i, Differentiable ℂ (Θ i)) ∧ (∀ i (l : u.Λ) z, Θ i (z + l) = (χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ N * Θ i z) ∧ (∃ i, Θ i ≠ 0) ∧ ∀ w : Fin g → ℂ, w ≠ 0 → ¬ ∀ i (t : ℂ) z, Θ i (z + t • w) = Θ i z := by
  intro A _ L g u Hm χ hL _ hamp hlaw
  obtain ⟨N, hN, M, s, hcov, H⟩ := hamp ⊤ (isAffineOpen_top _)
  choose Θ hΘ using fun i => exists_theta u hL (s i)
  obtain ⟨i, hi0⟩ : ∃ i, Θ i 0 ≠ 0 := by
    have hm : (lp (u.ex 0)) (default : PrimeSpectrum ℂ) ∈ ⨆ i, Out.nonzeroLocus (s i) := by
      rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨i, (theta_ne_zero_iff hL (hΘ i) 0).2 ((GlobalTheory.top_le_preimage_iff_mem _ _).2 hi)⟩
  refine ⟨N, Fin (M + 1), Θ, hN, fun i => theta_differentiable hL (hΘ i),
    fun i l z => theta_add hL (hΘ i) l z _ fun i' h => hlaw l i' z h,
    ⟨i, fun h => hi0 (by rw [h]; rfl)⟩, fun w hw hinv => hw ?_⟩
  obtain ⟨haff, r, hr, hs⟩ := H i
  have hconst : ∀ j (t : ℂ), Θ j (t • w) = Θ j 0 := fun j t => by simpa using hinv j t 0
  have hD0 := (theta_ne_zero_iff hL (hΘ i) 0).1 hi0
  have hD : ∀ t : ℂ, ⊤ ≤ (lp (u.ex (t • w))) ⁻¹ᵁ Out.nonzeroLocus (s i) := fun t =>
    (theta_ne_zero_iff hL (hΘ i) _).1 (by rw [hconst]; exact hi0)
  have hy : ∀ t : ℂ, lp (u.ex (t • w)) = lp (u.ex 0) := fun t =>
    eq_of_generators (A.hom ∣_ ⊤) haff r hs (hD t) hD0 (lp_base _ _) fun j => by
      have h1 := val_ratio hL (hΘ i) (hΘ j) (r j) (hr j) (t • w) (hD t)
      have h2 := val_ratio hL (hΘ i) (hΘ j) (r j) (hr j) 0 hD0
      rw [hconst, hconst] at h1
      exact mul_right_cancel₀ hi0 (h1.trans h2.symm)
  refine eq_zero_of_smul_mem u.Λ u.discrete w fun t => (u.ker _).1 ?_
  rw [lp_injective (hy t)]
  exact (u.ker 0).2 (zero_mem _)

end GlobalTheory.CompanionTheory.Ar.SecTheta

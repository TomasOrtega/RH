import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LBGerm

/- English proof (translation)
Rewrite using `[Scheme.Hom.appLE, CommRingCat.comp_apply, gs_res (𝟙 Z) w h trivial, gs_pull (𝟙 Z) r w U (h trivial) a, Category.id_comp]`.
-/
theorem ratMap_gs_appLE {Z S : Scheme.{0}} (r : Z ⟶ S) (U : S.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (w : Z) (a : Γ(S, U)) :
    gs r w U a = gs (𝟙 Z) w ⊤ ((r.appLE U ⊤ h).hom a) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, gs_res (𝟙 Z) w h trivial, gs_pull (𝟙 Z) r w U (h trivial) a,
    Category.id_comp]

/- English proof (translation)
Establish `hf : ⊤ ≤ g₁ ⁻¹ᵁ U` using `fun w _ => h₁ w`. Establish `hg : ⊤ ≤ g₂ ⁻¹ᵁ U` using `fun w _ => h₂ w`. Establish `key : ∀ (r : T ⟶ S) (hr : ⊤ ≤ r ⁻¹ᵁ U), (⊤ : T.Opens).ι ≫ r = (⊤ : T.Opens).toSpecΓ ≫ Spec.map (r.appLE U ⊤ hr) ≫ hU.fromSpec`. Introduce `r hr`. Rewrite using `[Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, hU.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]`.

Establish `e : g₁.appLE U ⊤ hf = g₂.appLE U ⊤ hg`. Use extensionality with `a`. Conclude with `fn_ext fun w _ => (ratMap_gs_appLE g₁ U hf w a).symm.trans ((h a w).trans (ratMap_gs_appLE g₂ U hg w a))`. Conclude with `Scheme.hom_ext_of_forall g₁ g₂ fun w => ⟨⊤, trivial, by rw [key g₁ hf, key g₂ hg, e]⟩`.
-/
theorem ratMap_eq_of_gs_eq {T S : Scheme.{0}} (g₁ g₂ : T ⟶ S) {U : S.Opens} (hU : IsAffineOpen U)
    (h₁ : ∀ w, g₁ w ∈ U) (h₂ : ∀ w, g₂ w ∈ U) (h : ∀ (a : Γ(S, U)) (w : T), gs g₁ w U a = gs g₂ w U a) :
    g₁ = g₂ := by
  have hf : ⊤ ≤ g₁ ⁻¹ᵁ U := fun w _ => h₁ w
  have hg : ⊤ ≤ g₂ ⁻¹ᵁ U := fun w _ => h₂ w
  have key : ∀ (r : T ⟶ S) (hr : ⊤ ≤ r ⁻¹ᵁ U),
      (⊤ : T.Opens).ι ≫ r = (⊤ : T.Opens).toSpecΓ ≫ Spec.map (r.appLE U ⊤ hr) ≫ hU.fromSpec := by
    intro r hr
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, hU.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]
  have e : g₁.appLE U ⊤ hf = g₂.appLE U ⊤ hg := by
    ext a
    exact fn_ext fun w _ => (ratMap_gs_appLE g₁ U hf w a).symm.trans ((h a w).trans (ratMap_gs_appLE g₂ U hg w a))
  exact Scheme.hom_ext_of_forall g₁ g₂ fun w => ⟨⊤, trivial, by rw [key g₁ hf, key g₂ hg, e]⟩

/- English proof (translation)
Establish `h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U` using `hU.fromSpec_preimage_self.ge`. Establish `h' : ⊤ ≤ (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) ⁻¹ᵁ U` using `fun z _ => h0 (Set.mem_univ ((u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) z))`. Establish `h : ⊤ ≤ (u ≫ V.ι) ⁻¹ᵁ V` using `fun z _ => (u z).2`. Use `⟨h' trivial, fun b => ?_⟩` and prove the remaining obligations. Establish `h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv`.

Rewrite using `[Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]`. Conclude with `Category.comp_id _`. Establish `h2 : (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec).appLE U ⊤ h' = hU.fromSpec.appLE U ⊤ h0 ≫ (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop`. Use `by`. Establish `e` using `Scheme.Hom.appLE_comp_appLE (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) hU.fromSpec U ⊤ ⊤ h0 le_rfl`.

Rewrite `e` using `[show (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appLE ⊤ ⊤ le_rfl = (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop from Scheme.Hom.appLE_eq_app (f := u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) (U := ⊤)]`. Simplify `e.symm` using `only [Category.assoc]`. Establish `h3 : (u ≫ V.ι).appLE V ⊤ h = V.topIso.inv ≫ u.appTop`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE u V.ι V ⊤ ⊤ (fun x _ => x.2) le_rfl]`. Use `erw [Scheme.Opens.ι_appLE]`.

Simplify using `only [Scheme.Opens.topIso_inv]`. Use `congr 1`. Conclude with `Scheme.Hom.appLE_eq_app (f := u) (U := ⊤)`. Establish `h4 : (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec).appLE U ⊤ h' = CommRingCat.ofHom θ ≫ (u ≫ V.ι).appLE V ⊤ h`. Rewrite using `[h2, h1, h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]`.

Simplify using `only [Category.assoc]`. Rewrite using `[Scheme.ΓSpecIso_naturality_assoc]`. Conclude with `Iso.inv_hom_id_assoc _ _`. Rewrite using `[ratMap_gs_appLE _ U h' w b, ratMap_gs_appLE _ V h w (θ b), h4]`. Both sides reduce to the same expression.
-/
theorem ratMap_gs_ofRingHom {X Y : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (V : Y.Opens)
    (θ : Γ(X, U) →+* Γ(Y, V)) {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z) :
    (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) w ∈ U ∧ ∀ b : Γ(X, U),
      gs (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) w U b = gs (u ≫ V.ι) w V (θ b) := by
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h' : ⊤ ≤ (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec) ⁻¹ᵁ U :=
    fun z _ => h0 (Set.mem_univ ((u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) z))
  have h : ⊤ ≤ (u ≫ V.ι) ⁻¹ᵁ V := fun z _ => (u z).2
  refine ⟨h' trivial, fun b => ?_⟩
  have h1 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact Category.comp_id _
  have h2 : (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec).appLE U ⊤ h' =
      hU.fromSpec.appLE U ⊤ h0 ≫ (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop :=
by
    have e := Scheme.Hom.appLE_comp_appLE (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) hU.fromSpec U ⊤ ⊤ h0 le_rfl
    rw [show (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appLE ⊤ ⊤ le_rfl =
      (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop from Scheme.Hom.appLE_eq_app (f := u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) (U := ⊤)] at e
    simpa only [Category.assoc] using e.symm
  have h3 : (u ≫ V.ι).appLE V ⊤ h = V.topIso.inv ≫ u.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE u V.ι V ⊤ ⊤ (fun x _ => x.2) le_rfl]
    erw [Scheme.Opens.ι_appLE]
    simp only [Scheme.Opens.topIso_inv]
    congr 1
    exact Scheme.Hom.appLE_eq_app (f := u) (U := ⊤)
  have h4 : (u ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec).appLE U ⊤ h' =
      CommRingCat.ofHom θ ≫ (u ≫ V.ι).appLE V ⊤ h := by
    rw [h2, h1, h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality_assoc]
    exact Iso.inv_hom_id_assoc _ _
  rw [ratMap_gs_appLE _ U h' w b, ratMap_gs_appLE _ V h w (θ b), h4]
  rfl

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp only [MvPolynomial.eval₂Hom_C]`. Conclude with `hc a`. Consider the case `add p q hp hq => rw [map_add, map_add, gs_add _ _ _ hw₁, gs_add _ _ _ hw₂, hp, hq]`. Consider the case `mul_X p n hp => rw [map_mul, map_mul, gs_mul _ _ _ hw₁, gs_mul _ _ _ hw₂, hp, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', hr n]`.
-/
theorem ratMap_gs_eval₂ {K : Type} [CommRing K] {Z S S' : Scheme.{0}} {Idx : Type} (g₁ : Z ⟶ S) (g₂ : Z ⟶ S')
    {U₁ : S.Opens} {U₂ : S'.Opens} (w : Z) (hw₁ : g₁ w ∈ U₁) (hw₂ : g₂ w ∈ U₂) (f₁ : K →+* Γ(S, U₁))
    (f₂ : K →+* Γ(S', U₂)) (r₁ : Idx → Γ(S, U₁)) (r₂ : Idx → Γ(S', U₂))
    (hc : ∀ a, gs g₁ w U₁ (f₁ a) = gs g₂ w U₂ (f₂ a)) (hr : ∀ l, gs g₁ w U₁ (r₁ l) = gs g₂ w U₂ (r₂ l))
    (P : MvPolynomial Idx K) :
    gs g₁ w U₁ (MvPolynomial.eval₂Hom f₁ r₁ P) = gs g₂ w U₂ (MvPolynomial.eval₂Hom f₂ r₂ P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂Hom_C]; exact hc a
  | add p q hp hq => rw [map_add, map_add, gs_add _ _ _ hw₁, gs_add _ _ _ hw₂, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, gs_mul _ _ _ hw₁, gs_mul _ _ _ hw₂, hp, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_X', hr n]

/- English proof (translation)
Rewrite using `[AbLaw.cst, RingHom.comp_apply, RingHom.comp_apply, AbLaw.rs, gs_res g w le_top hw]`. Conclude with `gs_pull g p w ⊤ trivial _`.
-/
theorem ratMap_gs_cst {K : Type} [CommRing K] {Z S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of K)) (g : Z ⟶ S)
    (U : S.Opens) (w : Z) (hw : g w ∈ U) (a : K) :
    gs g w U (AbLaw.cst p U a) = gs (g ≫ p) w ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) := by
  rw [AbLaw.cst, RingHom.comp_apply, RingHom.comp_apply, AbLaw.rs, gs_res g w le_top hw]
  exact gs_pull g p w ⊤ trivial _

/- English proof (translation)
Take `⟨l₀, hl₀⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show z w ∈ ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) by rw [hcov]; trivial)`. Take `⟨j, hj⟩` from `exists_chart hL (π (z w))`. Set `c' : Fin 1 → L.ι` to `fun _ => j`. Establish `hc' : (z ≫ π) w ∈ secChart L c'` using `Set.mem_iInter.2 fun _ => hj`. Establish `germ` using `fun i => secRatioEq_iff_germ.1 (hrat i) w c' c hc' hc`.

Establish `uσ : IsUnit (secGerm (z ≫ π) w (σ l₀) c')` using `(GlobalTheory.mem_nonzeroLocus_iff_pull (σ l₀) (z ≫ π) w hc').1 hl₀`. Establish `us₀ : IsUnit (secGerm (z ≫ π) w s₀ c')`. Establish `h` using `uσ.mul ht₀`. Rewrite `h` using `[germ l₀]`. Conclude with `isUnit_of_mul_isUnit_left h`.

Establish `uσi : IsUnit (secGerm (z ≫ π) w (σ i₀) c')`. Establish `h` using `us₀.mul hti`. Rewrite `h` using `[← germ i₀]`. Conclude with `isUnit_of_mul_isUnit_left h`. Establish `hD : z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀)` using `(GlobalTheory.mem_nonzeroLocus_iff_pull (σ i₀) (z ≫ π) w hc').2 uσi`.

Use `⟨hD, fun l ρ hρ => ?_⟩` and prove the remaining obligations. Establish `hrl` using `congrArg (z.stalkMap w).hom (hr l c' (z w) hD hc')`. Rewrite `hrl` using `[map_mul, ← secGerm_comp z π w _ hc', ← secGerm_comp z π w _ hc', ← gs_stalkMap z w _ hD]`. Use `(us₀.mul hti).mul_right_cancel ?_` and prove the remaining obligations. Take the linear combination `(-(gs z w (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r l))) * germ i₀ + (-(secGerm (g ≫ π) w t₀ c)) * hrl + germ l + (-(secGerm (z ≫ π) w s₀ c')) * hρ`.
-/
theorem ratMap_key {A X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (π : A ⟶ X) {k k' m : ℕ}
    (σ : Fin (m + 1) → H0 L k) (hcov : ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) = ⊤) (s₀ : H0 L k) (t₀ : H0 L k')
    (t : Fin (m + 1) → H0 L k') (i₀ : Fin (m + 1)) (r : Fin (m + 1) → Γ(A, π ⁻¹ᵁ nonzeroLocus (σ i₀)))
    (hr : ∀ (j : Fin (m + 1)) (c : Fin 1 → L.ι) (a : A), π a ∈ nonzeroLocus (σ i₀) → π a ∈ secChart L c →
      secGerm π a (σ j) c = gs (𝟙 A) a (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r j) * secGerm π a (σ i₀) c)
    (c : Fin 1 → L.ι) (g z : Z ⟶ A) (w : Z) (hc : (g ≫ π) w ∈ secChart L c)
    (ht₀ : IsUnit (secGerm (g ≫ π) w t₀ c)) (hti : IsUnit (secGerm (g ≫ π) w (t i₀) c))
    (hrat : ∀ i, SecRatioEq L (z ≫ π) (g ≫ π) (σ i) s₀ (t i) t₀) :
    z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧ ∀ (l : Fin (m + 1)) (ρ : Z.presheaf.stalk w),
      ρ * secGerm (g ≫ π) w (t i₀) c = secGerm (g ≫ π) w (t l) c →
        gs z w (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r l) = ρ := by
  obtain ⟨l₀, hl₀⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show z w ∈ ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) by rw [hcov]; trivial)
  obtain ⟨j, hj⟩ := exists_chart hL (π (z w))
  let c' : Fin 1 → L.ι := fun _ => j
  have hc' : (z ≫ π) w ∈ secChart L c' := Set.mem_iInter.2 fun _ => hj
  have germ := fun i => secRatioEq_iff_germ.1 (hrat i) w c' c hc' hc
  have uσ : IsUnit (secGerm (z ≫ π) w (σ l₀) c') := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ l₀) (z ≫ π) w hc').1 hl₀
  have us₀ : IsUnit (secGerm (z ≫ π) w s₀ c') := by
    have h := uσ.mul ht₀
    rw [germ l₀] at h
    exact isUnit_of_mul_isUnit_left h
  have uσi : IsUnit (secGerm (z ≫ π) w (σ i₀) c') := by
    have h := us₀.mul hti
    rw [← germ i₀] at h
    exact isUnit_of_mul_isUnit_left h
  have hD : z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ i₀) (z ≫ π) w hc').2 uσi
  refine ⟨hD, fun l ρ hρ => ?_⟩
  have hrl := congrArg (z.stalkMap w).hom (hr l c' (z w) hD hc')
  rw [map_mul, ← secGerm_comp z π w _ hc', ← secGerm_comp z π w _ hc', ← gs_stalkMap z w _ hD] at hrl
  refine (us₀.mul hti).mul_right_cancel ?_
  linear_combination (-(gs z w (π ⁻¹ᵁ nonzeroLocus (σ i₀)) (r l))) * germ i₀ + (-(secGerm (g ≫ π) w t₀ c)) * hrl +
    germ l + (-(secGerm (z ≫ π) w s₀ c')) * hρ

/- English proof (translation)
Introduce `K _ A _ X L hL π k k' m σ hva s₀ t₀ t ⟨a, ha⟩ Y x y hdom hrat`. Use `haveI := hdom`. Take `⟨hcov, hloc⟩` from `hva`. Take `⟨q, hq⟩` from `x.left.denseRange.exists_mem_open (π ⁻¹ᵁ nonzeroLocus t₀).isOpen ⟨a, ha⟩`. Take `⟨i₀, hi₀⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show y.left q ∈ ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) by rw [hcov]; trivial)`.

Take `⟨hD, r, hr, hsurj⟩` from `hloc i₀`. Take `⟨jx, hjx⟩` from `exists_chart hL (π (x.left q))`. Take `⟨jy, hjy⟩` from `exists_chart hL (π (y.left q))`. Set `c : Fin 1 → L.ι` to `fun _ => jx`. Set `c' : Fin 1 → L.ι` to `fun _ => jy`.

Establish `hcx : (x.left ≫ π) q ∈ secChart L c` using `Set.mem_iInter.2 fun _ => hjx`. Establish `hcy : (y.left ≫ π) q ∈ secChart L c'` using `Set.mem_iInter.2 fun _ => hjy`. Establish `e` using `secRatioEq_iff_germ.1 (hrat i₀) q c' c hcy hcx`. Establish `u1 : IsUnit (secGerm (y.left ≫ π) q (σ i₀) c')` using `(GlobalTheory.mem_nonzeroLocus_iff_pull (σ i₀) (y.left ≫ π) q hcy).1 hi₀`. Establish `u2 : IsUnit (secGerm (x.left ≫ π) q t₀ c)` using `(GlobalTheory.mem_nonzeroLocus_iff_pull t₀ (x.left ≫ π) q hcx).1 hq`.

Establish `u3 : IsUnit (secGerm (x.left ≫ π) q (t i₀) c)`. Establish `h` using `u1.mul u2`. Rewrite `h` using `[e]`. Conclude with `isUnit_of_mul_isUnit_right h`. Set `W₀ : A.left.Opens` to `π ⁻¹ᵁ secChart L c`.

Set `b : H0 L k' → Γ(A.left, W₀)` to `fun s => (π.app (secChart L c)).hom (s.f c)`. Set `V : A.left.Opens` to `A.left.basicOpen (b t₀ * b (t i₀))`. Establish `hVW : V ≤ W₀` using `A.left.basicOpen_le _`. Establish `hb : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z) (_ : g w ∈ W₀) (s : H0 L k'), gs g w W₀ (b s) = secGerm (g ≫ π) w s c` using `fun g w hw s => gs_pull g π w _ hw _`. Establish `memV : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z), g w ∈ V → (g ≫ π) w ∈ secChart L c ∧ IsUnit (secGerm (g ≫ π) w t₀ c) ∧ IsUnit (secGerm (g ≫ π) w (t i₀) c)`.

Introduce `Z g w hw`. Establish `hW : g w ∈ W₀` using `hVW hw`. Establish `h` using `(GlobalTheory.LBGerm.isUnit_gs_iff g w W₀ hW _).2 hw`. Rewrite `h` using `[gs_mul g w W₀ hW, hb g w hW, hb g w hW]`. Conclude with `⟨hW, isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩`.

Establish `hxq : x.left q ∈ V` using `(GlobalTheory.LBGerm.isUnit_gs_iff x.left q W₀ hcx (b t₀ * b (t i₀))).1 (by rw [gs_mul _ q W₀ hcx, hb _ q hcx, hb _ q hcx]; exact u2.mul u3)`. Establish `hu : IsUnit ((A.left.presheaf.map (homOfLE hVW).op).hom (b (t i₀)))`. Establish `h` using `A.left.toRingedSpace.isUnit_res_basicOpen (b t₀ * b (t i₀))`. Rewrite `h` using `[map_mul]`. Conclude with `isUnit_of_mul_isUnit_right h`.

Set `ρ : Fin (m + 1) → Γ(A.left, V)` to `fun l => (A.left.presheaf.map (homOfLE hVW).op).hom (b (t l)) * ↑hu.unit⁻¹`. Establish `hρ : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z) (_ : g w ∈ V) (l : Fin (m + 1)), gs g w V (ρ l) * secGerm (g ≫ π) w (t i₀) c = secGerm (g ≫ π) w (t l) c`. Introduce `Z g w hw l`. Establish `hW : g w ∈ W₀` using `hVW hw`. Establish `one : gs g w V 1 = 1` using `by rw [gs_eq g w V hw, map_one, map_one]`.

Rewrite using `[← hb g w hW, ← hb g w hW, ← gs_res g w hVW hw (b (t i₀)), ← gs_res g w hVW hw (b (t l)), gs_mul g w V hw, _root_.mul_assoc, ← gs_mul g w V hw, hu.val_inv_mul, one, _root_.mul_one]`. Set `ev` to `MvPolynomial.eval₂Hom (AbLaw.cst A.hom (π ⁻¹ᵁ nonzeroLocus (σ i₀))) r`. Set `ev'` to `MvPolynomial.eval₂Hom (AbLaw.cst A.hom V) ρ`. Establish `transfer : ∀ {Z : Scheme.{0}} (g z : Z ⟶ A.left) (w : Z), g w ∈ V → g ≫ A.hom = z ≫ A.hom → (∀ i, SecRatioEq L (z ≫ π) (g ≫ π) (σ i) s₀ (t i) t₀) → z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧ ∀ P, gs g w V (ev' P) = gs z w _ (ev P)`. Introduce `Z g z w hw hp hrt`.

Take `⟨hc, h0, hi⟩` from `memV g w hw`. Take `⟨hzD, hR⟩` from `ratMap_key hL π σ hcov s₀ t₀ t i₀ r hr c g z w hc h0 hi hrt`. Use `⟨hzD, ratMap_gs_eval₂ g z w hw hzD _ _ ρ r (fun a => ?_) (fun l => (hR l _ (hρ g w hw l)).symm)⟩` and prove the remaining obligations. Rewrite using `[ratMap_gs_cst A.hom g V w hw, ratMap_gs_cst A.hom z _ w hzD, hp]`. Establish `hker : RingHom.ker ev ≤ RingHom.ker ev'`.

Introduce `P hP`. Rewrite `hP`, the goal using `[RingHom.mem_ker]`. Apply `app_injective_of_isDominant x.left V` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `fn_ext fun w hw => ?_` and prove the remaining obligations.

Establish `tr` using `transfer x.left y.left w hw ((Over.w x).trans (Over.w y).symm) hrat`. Rewrite using `[gs_pull (𝟙 _) x.left w V hw, Category.id_comp, tr.2 P, hP, GlobalTheory.LBGerm.gs_zero _ _ _ tr.1, GlobalTheory.LBGerm.gs_zero _ _ _ hw]`. Set `θ` to `(RingHom.liftOfSurjective ev hsurj) ⟨ev', hker⟩`. Establish `hθ : ∀ P, θ (ev P) = ev' P` using `RingHom.liftOfSurjective_comp_apply ev hsurj ⟨ev', hker⟩`. Set `f₀ : V.toScheme ⟶ A.left` to `V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hD.fromSpec`.

Establish `hf₀ : ∀ {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z), (u ≫ f₀) w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧ ∀ P, gs (u ≫ f₀) w _ (ev P) = gs (u ≫ V.ι) w V (ev' P)` using `fun u w => by`. Take `⟨h1, h2⟩` from `ratMap_gs_ofRingHom hD V θ u w`. Conclude with `⟨h1, fun P => (h2 (ev P)).trans (by rw [hθ])⟩`. Establish `hmem : ∀ {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z), (u ≫ V.ι) w ∈ V` using `fun u w => (u w).2`. Establish `hover : f₀ ≫ A.hom = V.ι ≫ A.hom`.

Use `ratMap_eq_of_gs_eq _ _ (isAffineOpen_top (Sp K)) (fun _ => trivial) (fun _ => trivial) fun a w => ?_` and prove the remaining obligations. Take `⟨a', rfl⟩ : ∃ a' : K, (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a' = a` from `⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom a, by simp⟩`. Establish `h` using `hf₀ (𝟙 V.toScheme) w`. Establish `hc` using `h.2 (MvPolynomial.C a')`. Rewrite `hc` using `[MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ratMap_gs_cst _ _ _ w h.1, ratMap_gs_cst _ _ _ w (hmem (𝟙 _) w)]`.

Simplify `hc` using `only [Category.id_comp]`. Use `⟨Over.mk (V.ι ≫ A.hom), Over.homMk V.ι rfl, Over.homMk f₀ hover, ?_, ⟨⟨x.left q, hxq⟩⟩, ?_⟩` and prove the remaining obligations. Conclude with `(inferInstance : IsOpenImmersion V.ι)`. Introduce `Z u z hz`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `u.left ≫ f₀ = z.left`. Establish `hz' : ∀ i, SecRatioEq L (z.left ≫ π) ((u.left ≫ V.ι) ≫ π) (σ i) s₀ (t i) t₀` using `hz`. Establish `hp : (u.left ≫ V.ι) ≫ A.hom = z.left ≫ A.hom`. Rewrite using `[Category.assoc]`. Conclude with `(Over.w u).trans (Over.w z).symm`.

Use `ratMap_eq_of_gs_eq _ _ hD (fun w => (hf₀ u.left w).1) (fun w => (transfer _ _ w (hmem u.left w) hp hz').1) fun b' w => ?_` and prove the remaining obligations. Take `⟨P, rfl⟩` from `hsurj b'`. Conclude with `((hf₀ u.left w).2 P).trans ((transfer _ _ w (hmem u.left w) hp hz').2 P)`.
-/
theorem exists_morphism_of_secRatio : ∀ (K : Type) [Field K] (A : Over (Sp K)) [IsIntegral A.left] (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (π : A.left ⟶ X) (k k' m : ℕ) (σ : Fin (m + 1) → H0 L k), VeryAmpleAlong A.hom π L σ → ∀ (s₀ : H0 L k) (t₀ : H0 L k') (t : Fin (m + 1) → H0 L k'), (∃ a : A.left, π a ∈ nonzeroLocus t₀) → ∀ (Y : Over (Sp K)) (x y : Y ⟶ A), IsDominant x.left → (∀ i, SecRatioEq L (y.left ≫ π) (x.left ≫ π) (σ i) s₀ (t i) t₀) → ∃ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left ∧ Nonempty V.left ∧ ∀ (Z : Over (Sp K)) (u : Z ⟶ V) (z : Z ⟶ A), (∀ i, SecRatioEq L (z.left ≫ π) ((u ≫ j).left ≫ π) (σ i) s₀ (t i) t₀) → u ≫ f = z := by
  intro K _ A _ X L hL π k k' m σ hva s₀ t₀ t ⟨a, ha⟩ Y x y hdom hrat
  haveI := hdom
  obtain ⟨hcov, hloc⟩ := hva
  obtain ⟨q, hq⟩ := x.left.denseRange.exists_mem_open (π ⁻¹ᵁ nonzeroLocus t₀).isOpen ⟨a, ha⟩
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show y.left q ∈ ⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hloc i₀
  obtain ⟨jx, hjx⟩ := exists_chart hL (π (x.left q))
  obtain ⟨jy, hjy⟩ := exists_chart hL (π (y.left q))
  let c : Fin 1 → L.ι := fun _ => jx
  let c' : Fin 1 → L.ι := fun _ => jy
  have hcx : (x.left ≫ π) q ∈ secChart L c := Set.mem_iInter.2 fun _ => hjx
  have hcy : (y.left ≫ π) q ∈ secChart L c' := Set.mem_iInter.2 fun _ => hjy
  have e := secRatioEq_iff_germ.1 (hrat i₀) q c' c hcy hcx
  have u1 : IsUnit (secGerm (y.left ≫ π) q (σ i₀) c') := (GlobalTheory.mem_nonzeroLocus_iff_pull (σ i₀) (y.left ≫ π) q hcy).1 hi₀
  have u2 : IsUnit (secGerm (x.left ≫ π) q t₀ c) := (GlobalTheory.mem_nonzeroLocus_iff_pull t₀ (x.left ≫ π) q hcx).1 hq
  have u3 : IsUnit (secGerm (x.left ≫ π) q (t i₀) c) := by
    have h := u1.mul u2
    rw [e] at h
    exact isUnit_of_mul_isUnit_right h
  let W₀ : A.left.Opens := π ⁻¹ᵁ secChart L c
  let b : H0 L k' → Γ(A.left, W₀) := fun s => (π.app (secChart L c)).hom (s.f c)
  let V : A.left.Opens := A.left.basicOpen (b t₀ * b (t i₀))
  have hVW : V ≤ W₀ := A.left.basicOpen_le _
  have hb : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z) (_ : g w ∈ W₀) (s : H0 L k'),
      gs g w W₀ (b s) = secGerm (g ≫ π) w s c := fun g w hw s => gs_pull g π w _ hw _
  have memV : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z), g w ∈ V → (g ≫ π) w ∈ secChart L c ∧
      IsUnit (secGerm (g ≫ π) w t₀ c) ∧ IsUnit (secGerm (g ≫ π) w (t i₀) c) := by
    intro Z g w hw
    have hW : g w ∈ W₀ := hVW hw
    have h := (GlobalTheory.LBGerm.isUnit_gs_iff g w W₀ hW _).2 hw
    rw [gs_mul g w W₀ hW, hb g w hW, hb g w hW] at h
    exact ⟨hW, isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩
  have hxq : x.left q ∈ V :=
    (GlobalTheory.LBGerm.isUnit_gs_iff x.left q W₀ hcx (b t₀ * b (t i₀))).1
      (by rw [gs_mul _ q W₀ hcx, hb _ q hcx, hb _ q hcx]; exact u2.mul u3)
  have hu : IsUnit ((A.left.presheaf.map (homOfLE hVW).op).hom (b (t i₀))) := by
    have h := A.left.toRingedSpace.isUnit_res_basicOpen (b t₀ * b (t i₀))
    rw [map_mul] at h
    exact isUnit_of_mul_isUnit_right h
  let ρ : Fin (m + 1) → Γ(A.left, V) := fun l =>
    (A.left.presheaf.map (homOfLE hVW).op).hom (b (t l)) * ↑hu.unit⁻¹
  have hρ : ∀ {Z : Scheme.{0}} (g : Z ⟶ A.left) (w : Z) (_ : g w ∈ V) (l : Fin (m + 1)),
      gs g w V (ρ l) * secGerm (g ≫ π) w (t i₀) c = secGerm (g ≫ π) w (t l) c := by
    intro Z g w hw l
    have hW : g w ∈ W₀ := hVW hw
    have one : gs g w V 1 = 1 := by rw [gs_eq g w V hw, map_one, map_one]
    rw [← hb g w hW, ← hb g w hW, ← gs_res g w hVW hw (b (t i₀)), ← gs_res g w hVW hw (b (t l)),
      gs_mul g w V hw, _root_.mul_assoc, ← gs_mul g w V hw, hu.val_inv_mul, one, _root_.mul_one]
  let ev := MvPolynomial.eval₂Hom (AbLaw.cst A.hom (π ⁻¹ᵁ nonzeroLocus (σ i₀))) r
  let ev' := MvPolynomial.eval₂Hom (AbLaw.cst A.hom V) ρ
  have transfer : ∀ {Z : Scheme.{0}} (g z : Z ⟶ A.left) (w : Z), g w ∈ V → g ≫ A.hom = z ≫ A.hom →
      (∀ i, SecRatioEq L (z ≫ π) (g ≫ π) (σ i) s₀ (t i) t₀) →
      z w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧ ∀ P, gs g w V (ev' P) = gs z w _ (ev P) := by
    intro Z g z w hw hp hrt
    obtain ⟨hc, h0, hi⟩ := memV g w hw
    obtain ⟨hzD, hR⟩ := ratMap_key hL π σ hcov s₀ t₀ t i₀ r hr c g z w hc h0 hi hrt
    refine ⟨hzD, ratMap_gs_eval₂ g z w hw hzD _ _ ρ r (fun a => ?_) (fun l => (hR l _ (hρ g w hw l)).symm)⟩
    rw [ratMap_gs_cst A.hom g V w hw, ratMap_gs_cst A.hom z _ w hzD, hp]
  have hker : RingHom.ker ev ≤ RingHom.ker ev' := by
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢
    apply app_injective_of_isDominant x.left V
    rw [map_zero]
    refine fn_ext fun w hw => ?_
    have tr := transfer x.left y.left w hw ((Over.w x).trans (Over.w y).symm) hrat
    rw [gs_pull (𝟙 _) x.left w V hw, Category.id_comp, tr.2 P, hP, GlobalTheory.LBGerm.gs_zero _ _ _ tr.1,
      GlobalTheory.LBGerm.gs_zero _ _ _ hw]
  let θ := (RingHom.liftOfSurjective ev hsurj) ⟨ev', hker⟩
  have hθ : ∀ P, θ (ev P) = ev' P := RingHom.liftOfSurjective_comp_apply ev hsurj ⟨ev', hker⟩
  let f₀ : V.toScheme ⟶ A.left := V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hD.fromSpec
  have hf₀ : ∀ {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z), (u ≫ f₀) w ∈ π ⁻¹ᵁ nonzeroLocus (σ i₀) ∧
      ∀ P, gs (u ≫ f₀) w _ (ev P) = gs (u ≫ V.ι) w V (ev' P) := fun u w => by
    obtain ⟨h1, h2⟩ := ratMap_gs_ofRingHom hD V θ u w
    exact ⟨h1, fun P => (h2 (ev P)).trans (by rw [hθ])⟩
  have hmem : ∀ {Z : Scheme.{0}} (u : Z ⟶ V.toScheme) (w : Z), (u ≫ V.ι) w ∈ V := fun u w => (u w).2
  have hover : f₀ ≫ A.hom = V.ι ≫ A.hom := by
    refine ratMap_eq_of_gs_eq _ _ (isAffineOpen_top (Sp K)) (fun _ => trivial) (fun _ => trivial) fun a w => ?_
    obtain ⟨a', rfl⟩ : ∃ a' : K, (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a' = a :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom a, by simp⟩
    have h := hf₀ (𝟙 V.toScheme) w
    have hc := h.2 (MvPolynomial.C a')
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ratMap_gs_cst _ _ _ w h.1,
      ratMap_gs_cst _ _ _ w (hmem (𝟙 _) w)] at hc
    simpa only [Category.id_comp] using hc
  refine ⟨Over.mk (V.ι ≫ A.hom), Over.homMk V.ι rfl, Over.homMk f₀ hover, ?_, ⟨⟨x.left q, hxq⟩⟩, ?_⟩
  · exact (inferInstance : IsOpenImmersion V.ι)
  · intro Z u z hz
    apply Over.OverMorphism.ext
    change u.left ≫ f₀ = z.left
    have hz' : ∀ i, SecRatioEq L (z.left ≫ π) ((u.left ≫ V.ι) ≫ π) (σ i) s₀ (t i) t₀ := hz
    have hp : (u.left ≫ V.ι) ≫ A.hom = z.left ≫ A.hom := by
      rw [Category.assoc]
      exact (Over.w u).trans (Over.w z).symm
    refine ratMap_eq_of_gs_eq _ _ hD (fun w => (hf₀ u.left w).1)
      (fun w => (transfer _ _ w (hmem u.left w) hp hz').1) fun b' w => ?_
    obtain ⟨P, rfl⟩ := hsurj b'
    exact ((hf₀ u.left w).2 P).trans ((transfer _ _ w (hmem u.left w) hp hz').2 P)

end GlobalTheory.Mum

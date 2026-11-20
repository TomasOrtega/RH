import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormNonlocalDvrStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ChartOrder

/- English proof (translation)
Take `⟨N, s, hs⟩` from `Module.Finite.exists_fin' (𝓞 E) X`. Use `show (comb d (resInt (𝓞 E) φs) 0 φ).eval _ _ = d * (resInt (𝓞 E) φs).eval _ _`. Rewrite using `[InvFun.eval_eq _ hs, InvFun.eval_eq _ hs]`. Simplify using `[comb]`.
-/
theorem comb_evalZ {E : Type} [Field E] [NumberField E] (φs : InvFun ℤ) (φ : InvFun (𝓞 E)) (d : ℕ) {X : Type}
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (be : LinearMap.BilinForm ℤ X) :
    (comb d (resInt (𝓞 E) φs) 0 φ).evalZ be = d * (resInt (𝓞 E) φs).evalZ be := by
  obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin' (𝓞 E) X
  show (comb d (resInt (𝓞 E) φs) 0 φ).eval _ _ = d * (resInt (𝓞 E) φs).eval _ _
  rw [InvFun.eval_eq _ hs, InvFun.eval_eq _ hs]
  simp [comb]

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c X Y g φs 𝒩 φ d k DX hg hfan hRef hpol R _ _ _ ξ t mξ P m γ hR hEt hFU hTors hCone hIn y hy V _ _ _ hV ϖ hϖ ψ gam hgam χ hχ be hbe hForm`. Use `hV.1` as an intermediate fact. Establish `hψi : Function.Injective ψ` using `fun a b e => IsFractionRing.injective R (FractionRing R) (gam.injective (by rw [hgam, hgam, e]))`. Establish `hZ : jK V ≫ χ = (spMap gam ≫ y) ≫ X.j` using `by rw [Category.assoc]; exact hχ.symm`. Distinguish the cases in `hloc : IsLocalHom ψ`.

Establish `hCNV : IsCN V` using `⟨inferInstance, inferInstance, hV.2.1, hV.2.2⟩`. Take `⟨t', m₀, P', e, -, hcoord⟩` from `pullSt E H R V ψ t P hR hCNV hψi hloc hTors`. Take `⟨m₁⟩` from `GlobalTheory.TraitOrder.comp rfl mξ m₀`. Establish `hY : jK V ≫ spMap ψ ≫ ξ = (spMap gam ≫ y) ≫ Y.j`. Rewrite using `[← Category.assoc, ← ArcExtends.spMap_jK hgam, Category.assoc, Category.assoc, hy]`.

Take `⟨mX⟩` from `GlobalTheory.ArcOrder.exists_sabMap_of_generic X Y hV (spMap gam ≫ y) χ (spMap ψ ≫ ξ) hZ hY m₁`. Set `es : P'.D.toPre.X →ₗ[ℤ] P.D.toPre.X` to `e.toLinearMap.toAddMonoidHom.toIntLinearMap`. Set `be' : LinearMap.BilinForm ℤ P'.D.toPre.X` to `be.compl₁₂ es es`. Establish `hbe'v : ∀ a b, be' a b = be (e a) (e b)` using `fun a b => rfl`. Establish `hbe' : be' ∈ levelForms H 1 P'.D.toPre.X`.

Use `⟨fun a b => ?_, fun x a b => ?_, fun a b => one_dvd _⟩` and prove the remaining obligations. Rewrite using `[hbe'v, hbe'v]`. Conclude with `hbe.1 _ _`. Rewrite using `[hbe'v, hbe'v, LinearEquiv.map_smul, LinearEquiv.map_smul]`. Conclude with `hbe.2.1 x _ _`.

Establish `hmon : IsMonomial P'.D.toPre ![ϖ] ![be']`. Introduce `y'`. Take `⟨r, n, hr, hn, w, hw⟩` from `hForm (e y')`. Take `⟨u, hu⟩` from `hcoord y' r hr`. Use `⟨u * w⁻¹, fun _ => n, fun i => ?_, ?_⟩` and prove the remaining obligations.

Use `fin_cases i`. Simplify `hn` using `[hbe'v]`. Establish `: (↑(u * w⁻¹) : V) * ∏ i : Fin 1, ![ϖ] i ^ (fun _ => n) i = u * ψ r`. Simplify using `only [Fin.prod_univ_one, Matrix.cons_val_zero, Units.val_mul]`. Rewrite using `[← hw]`.

Take the linear combination `(↑u * ψ r) * w.inv_mul`. Rewrite using `[this]`. Conclude with `hu`. Establish `hr : Set.range (jK V ≫ χ) ⊆ Set.range X.j`. Introduce and unpack `_ ⟨p, rfl⟩`.

Conclude with `⟨(spMap gam ≫ y) p, by rw [hZ]; rfl⟩`. Take `⟨n, hn, hid⟩` from `hpol.1 V hV ϖ hϖ χ t' mX P' hr be' hbe' hmon`. Use `⟨n, hn.trans ?_, hid⟩` and prove the remaining obligations. Rewrite using `[show (comb d (resInt (𝓞 E) φs) 0 φ).evalZ be' = (comb d (resInt (𝓞 E) φs) 0 φ).evalZ be from (comb d (resInt (𝓞 E) φs) 0 φ).eval_equiv e fun a b => ((be a b : ℤ) : ℝ)]`. Conclude with `GlobalTheory.ChartOrder.comb_evalZ φs φ d be`.

Take `⟨V', _, _, _, f, hV', hfi, hfl, hfϖ, t', m₀, P', be', ρ, hbe', hρ, hρbe, hmon⟩` from `GlobalTheory.T.boundary_form_nonlocal_dvr E H R t P hR hTors V hV ϖ hϖ ψ hψi hloc be hbe hForm`. Use `hV'.1` as an intermediate fact. Establish `j : Function.Injective ((algebraMap V' (FractionRing V')).comp f)` using `(IsFractionRing.injective V' _).comp hfi`. Set `gam' : FractionRing V →+* FractionRing V'` to `IsFractionRing.lift j`. Establish `hgam' : ∀ r, gam' (algebraMap V _ r) = algebraMap V' _ (f r)` using `fun r => IsFractionRing.lift_algebraMap j r`.

Establish `hgg : ∀ r, (gam'.comp gam) (algebraMap R _ r) = algebraMap V' _ ((f.comp ψ) r)` using `fun r => by`. Simplify using `only [RingHom.comp_apply, hgam, hgam']`. Establish `hsp : spMap gam' ≫ spMap gam = spMap (gam'.comp gam)` using `GlobalTheory.ArcPointDescent.sp_comp fun _ => rfl`. Take `⟨m₁⟩` from `GlobalTheory.TraitOrder.comp rfl mξ m₀`. Establish `hY : jK V' ≫ spMap (f.comp ψ) ≫ ξ = (spMap (gam'.comp gam) ≫ y) ≫ Y.j`.

Rewrite using `[← Category.assoc, ← ArcExtends.spMap_jK hgg, Category.assoc, Category.assoc, hy]`. Establish `hZ' : jK V' ≫ spMap f ≫ χ = (spMap (gam'.comp gam) ≫ y) ≫ X.j`. Rewrite using `[← Category.assoc, ← ArcExtends.spMap_jK hgam', Category.assoc, hZ, ← hsp]`. Simplify using `only [Category.assoc]`. Take `⟨mX⟩` from `GlobalTheory.ArcOrder.exists_sabMap_of_generic X Y hV' (spMap (gam'.comp gam) ≫ y) (spMap f ≫ χ) (spMap (f.comp ψ) ≫ ξ) hZ' hY m₁`.

Establish `hr : Set.range (jK V' ≫ spMap f ≫ χ) ⊆ Set.range X.j`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `⟨(spMap (gam'.comp gam) ≫ y) p, by rw [hZ']; rfl⟩`. Take `⟨n, hn, hid⟩` from `hpol.1 V' hV' (f ϖ) hfϖ (spMap f ≫ χ) t' mX P' hr be' hbe' hmon`. Use `⟨n, hn.trans ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← GlobalTheory.ChartOrder.comb_evalZ φs φ d be] show (comb d (resInt (𝓞 E) φs) 0 φ).eval _ _ = (comb d (resInt (𝓞 E) φs) 0 φ).eval _ _`. Rewrite using `[← (comb d (resInt (𝓞 E) φs) 0 φ).eval_comp hρ]`. Simplify using `only [hρbe]`. Rewrite `hid` using `[GlobalTheory.TraitOrder.idlAlong_comp]`. Use `GlobalTheory.TraitOrder.map_injective f hfi (hid.trans ?_)` and prove the remaining obligations.

Rewrite using `[Ideal.map_span, Set.image_singleton, map_pow]`.
-/
theorem order_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ)
    (φ : InvFun (𝓞 E)) (d k : ℕ) (DX : GlobalTheory.EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs →
    Refines H (min D.p D.q) φs 𝒩 φ → IsPol (comb d (resInt _ φs) 0 φ) k X DX →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (mξ : SABMap t Y.t ξ)
      (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
      IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso →
      ConeO H φ P.D.toPre.X m γ → InCone P.D.toPre γ →
      ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V), (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ χ : Sp V ⟶ X.X, spMap gam ≫ y ≫ X.j = jK V ≫ χ → ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be →
        ∃ n : ℕ, (n : ℝ) = d * (resInt (𝓞 E) φs).evalZ be ∧ idlAlong DX.idealSheaf χ = Ideal.span {ϖ ^ n} := by
  intro E _ _ _ H D l Xo c X Y g φs 𝒩 φ d k DX hg hfan hRef hpol R _ _ _ ξ t mξ P m γ hR hEt hFU hTors hCone hIn y hy
    V _ _ _ hV ϖ hϖ ψ gam hgam χ hχ be hbe hForm
  have := hV.1
  have hψi : Function.Injective ψ := fun a b e =>
    IsFractionRing.injective R (FractionRing R) (gam.injective (by rw [hgam, hgam, e]))
  have hZ : jK V ≫ χ = (spMap gam ≫ y) ≫ X.j := by rw [Category.assoc]; exact hχ.symm
  by_cases hloc : IsLocalHom ψ
  · have hCNV : IsCN V := ⟨inferInstance, inferInstance, hV.2.1, hV.2.2⟩
    obtain ⟨t', m₀, P', e, -, hcoord⟩ := pullSt E H R V ψ t P hR hCNV hψi hloc hTors
    obtain ⟨m₁⟩ := GlobalTheory.TraitOrder.comp rfl mξ m₀
    have hY : jK V ≫ spMap ψ ≫ ξ = (spMap gam ≫ y) ≫ Y.j := by
      rw [← Category.assoc, ← ArcExtends.spMap_jK hgam, Category.assoc, Category.assoc, hy]
    obtain ⟨mX⟩ := GlobalTheory.ArcOrder.exists_sabMap_of_generic X Y hV (spMap gam ≫ y) χ (spMap ψ ≫ ξ) hZ hY m₁
    let es : P'.D.toPre.X →ₗ[ℤ] P.D.toPre.X := e.toLinearMap.toAddMonoidHom.toIntLinearMap
    let be' : LinearMap.BilinForm ℤ P'.D.toPre.X := be.compl₁₂ es es
    have hbe'v : ∀ a b, be' a b = be (e a) (e b) := fun a b => rfl
    have hbe' : be' ∈ levelForms H 1 P'.D.toPre.X := by
      refine ⟨fun a b => ?_, fun x a b => ?_, fun a b => one_dvd _⟩
      · rw [hbe'v, hbe'v]; exact hbe.1 _ _
      · rw [hbe'v, hbe'v, LinearEquiv.map_smul, LinearEquiv.map_smul]; exact hbe.2.1 x _ _
    have hmon : IsMonomial P'.D.toPre ![ϖ] ![be'] := by
      intro y'
      obtain ⟨r, n, hr, hn, w, hw⟩ := hForm (e y')
      obtain ⟨u, hu⟩ := hcoord y' r hr
      refine ⟨u * w⁻¹, fun _ => n, fun i => ?_, ?_⟩
      · fin_cases i; simpa [hbe'v] using hn
      · have : (↑(u * w⁻¹) : V) * ∏ i : Fin 1, ![ϖ] i ^ (fun _ => n) i = u * ψ r := by
          simp only [Fin.prod_univ_one, Matrix.cons_val_zero, Units.val_mul]
          rw [← hw]
          linear_combination (↑u * ψ r) * w.inv_mul
        rw [this]; exact hu
    have hr : Set.range (jK V ≫ χ) ⊆ Set.range X.j := by
      rintro _ ⟨p, rfl⟩
      exact ⟨(spMap gam ≫ y) p, by rw [hZ]; rfl⟩
    obtain ⟨n, hn, hid⟩ := hpol.1 V hV ϖ hϖ χ t' mX P' hr be' hbe' hmon
    refine ⟨n, hn.trans ?_, hid⟩
    rw [show (comb d (resInt (𝓞 E) φs) 0 φ).evalZ be' = (comb d (resInt (𝓞 E) φs) 0 φ).evalZ be from
      (comb d (resInt (𝓞 E) φs) 0 φ).eval_equiv e fun a b => ((be a b : ℤ) : ℝ)]
    exact GlobalTheory.ChartOrder.comb_evalZ φs φ d be
  · obtain ⟨V', _, _, _, f, hV', hfi, hfl, hfϖ, t', m₀, P', be', ρ, hbe', hρ, hρbe, hmon⟩ :=
      GlobalTheory.T.boundary_form_nonlocal_dvr E H R t P hR hTors V hV ϖ hϖ ψ hψi hloc be hbe hForm
    have := hV'.1
    have j : Function.Injective ((algebraMap V' (FractionRing V')).comp f) :=
      (IsFractionRing.injective V' _).comp hfi
    let gam' : FractionRing V →+* FractionRing V' := IsFractionRing.lift j
    have hgam' : ∀ r, gam' (algebraMap V _ r) = algebraMap V' _ (f r) := fun r => IsFractionRing.lift_algebraMap j r
    have hgg : ∀ r, (gam'.comp gam) (algebraMap R _ r) = algebraMap V' _ ((f.comp ψ) r) := fun r => by
      simp only [RingHom.comp_apply, hgam, hgam']
    have hsp : spMap gam' ≫ spMap gam = spMap (gam'.comp gam) := GlobalTheory.ArcPointDescent.sp_comp fun _ => rfl
    obtain ⟨m₁⟩ := GlobalTheory.TraitOrder.comp rfl mξ m₀
    have hY : jK V' ≫ spMap (f.comp ψ) ≫ ξ = (spMap (gam'.comp gam) ≫ y) ≫ Y.j := by
      rw [← Category.assoc, ← ArcExtends.spMap_jK hgg, Category.assoc, Category.assoc, hy]
    have hZ' : jK V' ≫ spMap f ≫ χ = (spMap (gam'.comp gam) ≫ y) ≫ X.j := by
      rw [← Category.assoc, ← ArcExtends.spMap_jK hgam', Category.assoc, hZ, ← hsp]
      simp only [Category.assoc]
    obtain ⟨mX⟩ := GlobalTheory.ArcOrder.exists_sabMap_of_generic X Y hV' (spMap (gam'.comp gam) ≫ y) (spMap f ≫ χ)
      (spMap (f.comp ψ) ≫ ξ) hZ' hY m₁
    have hr : Set.range (jK V' ≫ spMap f ≫ χ) ⊆ Set.range X.j := by
      rintro _ ⟨p, rfl⟩
      exact ⟨(spMap (gam'.comp gam) ≫ y) p, by rw [hZ']; rfl⟩
    obtain ⟨n, hn, hid⟩ := hpol.1 V' hV' (f ϖ) hfϖ (spMap f ≫ χ) t' mX P' hr be' hbe' hmon
    refine ⟨n, hn.trans ?_, ?_⟩
    · rw [← GlobalTheory.ChartOrder.comb_evalZ φs φ d be]
      show (comb d (resInt (𝓞 E) φs) 0 φ).eval _ _ = (comb d (resInt (𝓞 E) φs) 0 φ).eval _ _
      rw [← (comb d (resInt (𝓞 E) φs) 0 φ).eval_comp hρ]
      simp only [hρbe]
    · rw [GlobalTheory.TraitOrder.idlAlong_comp] at hid
      refine GlobalTheory.TraitOrder.map_injective f hfi (hid.trans ?_)
      rw [Ideal.map_span, Set.image_singleton, map_pow]

end GlobalTheory.ChartOrder

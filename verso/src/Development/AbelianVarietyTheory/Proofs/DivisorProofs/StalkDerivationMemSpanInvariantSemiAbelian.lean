import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLieBasisCoeffsOfDerivationAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFieldCoefficientsOfLinearVectorFi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDerSpan

open GlobalTheory.TangentOrigin

/- English proof (translation)
Introduce `R _ _ _ _ G _ _ hsa n v dd hinv p _ D hD δ hadd hmul hbase`. Use `haveI : Smooth G.hom := hsa.smooth`. Establish `hv` using `GlobalTheory.VertCoeffRing.isLieBasis_tvE v`. Establish `hdd` using `fun (B : Type) [CommRing B] [Algebra R B] e he z O h => GlobalTheory.VertCoeffRing.evalPt_lieExp (fun a => v a) dd hinv B e he z O h`. Set `ψ : ∀ (V : G.left.Opens), p ∈ V → Γ(G.left, V) →+* ResidueField (G.left.presheaf.stalk p)` to `fun V hpV => (residue _).comp (G.left.presheaf.germ V p hpV).hom`.

Establish `germ_res : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V') (f : Γ(G.left, V)), G.left.presheaf.germ V' p hpV' (resG G.left e f) = G.left.presheaf.germ V p hpV f`. Introduce `V V' e hpV hpV' f`. Conclude with `TopCat.Presheaf.germ_res_apply _ (homOfLE e) p hpV' f`. Establish `loc : ∀ (V : G.left.Opens) (hpV : p ∈ V), IsAffineOpen V → ∃! c : Fin n → ResidueField (G.left.presheaf.stalk p), ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f)`. Introduce `V hpV hV`.

Take `⟨t, ht, et⟩` from `exists_evalPt_eq hV (ψ V hpV)`. Use `letI : Algebra R (ResidueField (G.left.presheaf.stalk p)) := (Spec.preimage (t ≫ G.hom)).hom.toAlgebra`. Set `y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀` to `R) (ResidueField (G.left.presheaf.stalk p)) ⟶ G := Over.homMk t (Spec.map_preimage (t ≫ G.hom)).symm`. Establish `h : ⊤ ≤ y.left ⁻¹ᵁ V` using `ht`. Establish `ev : ∀ s, evalPt y.left V h s = ψ V hpV s` using `fun s => by`.

Express the relevant statement in the definitionally equal form `evalPt t V ht s = _`. Rewrite using `[et]`. Establish `hconst : ∀ r, G.left.presheaf.germ V p hpV (constFn G.hom V r) = (G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))`. Introduce `r`. Establish `e1 : constFn G.hom V r = resG G.left (le_top : V ≤ ⊤) ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))`.

Unfold `constFn`. Use `first`. Consider the case `rfl`. Consider the case `(rw [Scheme.Hom.appLE_eq_app_comp_map] ; rfl)`. Consider the case `(simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; rfl)`.

Rewrite using `[e1]`. Conclude with `germ_res ⊤ V le_top trivial hpV _`. Use `GlobalTheory.VertCoeffRing.existsUnique_coeff_alg hv hdd y hV h (fun f => δ (G.left.presheaf.germ V p hpV f)) (fun f f' => by simp only [map_add, hadd]) (fun f f' => by simp only [map_mul, hmul, ev]; rfl) (fun r => by rw [hconst]; exact hbase r)` as an intermediate fact. Simplify `this` using `only [ev]`. Establish `down : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V') (c : Fin n → ResidueField (G.left.presheaf.stalk p)), (∀ f, δ (G.left.presheaf.germ V' p hpV' f) = ∑ a, c a * ψ V' hpV' (dd a V' f)) → ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f)`.

Introduce `V V' e hpV hpV' c hc f`. Rewrite using `[← germ_res V V' e hpV hpV' f, hc]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Express the relevant statement in the definitionally equal form `residue _ (G.left.presheaf.germ V' p hpV' (dd a V' (resG G.left e f))) = residue _ (G.left.presheaf.germ V p hpV (dd a V f))`.

Rewrite using `[(hinv a).1.2.2 V V' e le_top f, germ_res]`. Take `⟨V₀, hV₀, hpV₀, -⟩` from `exists_isAffineOpen_mem_and_subset (show p ∈ (⊤ : G.left.Opens) from trivial)`. Take `⟨c₀, hc₀, hu₀⟩` from `loc V₀ hpV₀ hV₀`. Use `choose c hc using fun a => residue_surjective (R := G.left.presheaf.stalk p) (c₀ a)`. Use `⟨c, fun y => ?_⟩` and prove the remaining obligations.

Take `⟨W, hpW, g, rfl⟩` from `TopCat.Presheaf.germ_exist _ y`. Take `⟨V', hV', hpV', hle⟩` from `exists_isAffineOpen_mem_and_subset (show p ∈ V₀ ⊓ W from ⟨hpV₀, hpW⟩)`. Take `⟨c', hc', -⟩` from `loc V' hpV' hV'`. Establish `hcc : c' = c₀` using `hu₀ c' (down V₀ V' (hle.trans inf_le_left) hpV₀ hpV' c' hc')`. Substitute `hcc` using the available equality.

Establish `eW : V' ≤ W` using `hle.trans inf_le_right`. Rewrite using `[← germ_res W V' eW hpW hpV' g, hc', map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hc, hD]`. Both sides reduce to the same expression.
-/
theorem stalk_derivation_span : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∀ (δ : G.left.presheaf.stalk p → ResidueField (G.left.presheaf.stalk p)), (∀ u w, δ (u + w) = δ u + δ w) → (∀ u w, δ (u * w) = residue _ u * δ w + residue _ w * δ u) → (∀ r : R, δ ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = 0) → ∃ c : Fin n → G.left.presheaf.stalk p, ∀ y, δ y = residue _ (∑ a, c a * D a y) := by
  intro R _ _ _ _ G _ _ hsa n v dd hinv p _ D hD δ hadd hmul hbase
  haveI : Smooth G.hom := hsa.smooth
  have hv := GlobalTheory.VertCoeffRing.isLieBasis_tvE v
  have hdd := fun (B : Type) [CommRing B] [Algebra R B] e he z O h =>
    GlobalTheory.VertCoeffRing.evalPt_lieExp (fun a => v a) dd hinv B e he z O h

  let ψ : ∀ (V : G.left.Opens), p ∈ V → Γ(G.left, V) →+* ResidueField (G.left.presheaf.stalk p) :=
    fun V hpV => (residue _).comp (G.left.presheaf.germ V p hpV).hom
  have germ_res : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V') (f : Γ(G.left, V)),
      G.left.presheaf.germ V' p hpV' (resG G.left e f) = G.left.presheaf.germ V p hpV f := by
    intro V V' e hpV hpV' f
    exact TopCat.Presheaf.germ_res_apply _ (homOfLE e) p hpV' f

  have loc : ∀ (V : G.left.Opens) (hpV : p ∈ V), IsAffineOpen V →
      ∃! c : Fin n → ResidueField (G.left.presheaf.stalk p),
        ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f) := by
    intro V hpV hV
    obtain ⟨t, ht, et⟩ := exists_evalPt_eq hV (ψ V hpV)
    letI : Algebra R (ResidueField (G.left.presheaf.stalk p)) := (Spec.preimage (t ≫ G.hom)).hom.toAlgebra
    let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (ResidueField (G.left.presheaf.stalk p)) ⟶ G :=
      Over.homMk t (Spec.map_preimage (t ≫ G.hom)).symm
    have h : ⊤ ≤ y.left ⁻¹ᵁ V := ht
    have ev : ∀ s, evalPt y.left V h s = ψ V hpV s := fun s => by
      change evalPt t V ht s = _
      rw [et]
    have hconst : ∀ r, G.left.presheaf.germ V p hpV (constFn G.hom V r) =
        (G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
      intro r
      have e1 : constFn G.hom V r = resG G.left (le_top : V ≤ ⊤)
          ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
        unfold constFn
        first
          | rfl
          | (rw [Scheme.Hom.appLE_eq_app_comp_map] ; rfl)
          | (simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; rfl)
      rw [e1]
      exact germ_res ⊤ V le_top trivial hpV _
    have := GlobalTheory.VertCoeffRing.existsUnique_coeff_alg hv hdd y hV h
      (fun f => δ (G.left.presheaf.germ V p hpV f))
      (fun f f' => by simp only [map_add, hadd])
      (fun f f' => by simp only [map_mul, hmul, ev]; rfl)
      (fun r => by rw [hconst]; exact hbase r)
    simpa only [ev] using this

  have down : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V')
      (c : Fin n → ResidueField (G.left.presheaf.stalk p)),
      (∀ f, δ (G.left.presheaf.germ V' p hpV' f) = ∑ a, c a * ψ V' hpV' (dd a V' f)) →
      ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f) := by
    intro V V' e hpV hpV' c hc f
    rw [← germ_res V V' e hpV hpV' f, hc]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    change residue _ (G.left.presheaf.germ V' p hpV' (dd a V' (resG G.left e f))) =
      residue _ (G.left.presheaf.germ V p hpV (dd a V f))
    rw [(hinv a).1.2.2 V V' e le_top f, germ_res]
  obtain ⟨V₀, hV₀, hpV₀, -⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ (⊤ : G.left.Opens) from trivial)
  obtain ⟨c₀, hc₀, hu₀⟩ := loc V₀ hpV₀ hV₀
  choose c hc using fun a => residue_surjective (R := G.left.presheaf.stalk p) (c₀ a)
  refine ⟨c, fun y => ?_⟩
  obtain ⟨W, hpW, g, rfl⟩ := TopCat.Presheaf.germ_exist _ y
  obtain ⟨V', hV', hpV', hle⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ V₀ ⊓ W from ⟨hpV₀, hpW⟩)
  obtain ⟨c', hc', -⟩ := loc V' hpV' hV'
  have hcc : c' = c₀ := hu₀ c' (down V₀ V' (hle.trans inf_le_left) hpV₀ hpV' c' hc')
  subst hcc
  have eW : V' ≤ W := hle.trans inf_le_right
  rw [← germ_res W V' eW hpW hpV' g, hc', map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, hc, hD]
  rfl

end GlobalTheory.StalkDerSpan

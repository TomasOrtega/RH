import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalkStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef.TanLoc

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem ev_congr {R : Type} [CommRing R] {X : Scheme.{0}} {b b' : Sp R ⟶ X} (e : b = b') {U : X.Opens}
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U) (f : Γ(X, U)) : evAt b h f = evAt b' h' f := by
  subst e; rfl

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]`. Simplify using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_one_mul {E : Type} [CommRing E] (P Q : PowerSeries E) :
    PowerSeries.coeff 1 (P * Q) = PowerSeries.constantCoeff (R := E) P * PowerSeries.coeff 1 Q +
      PowerSeries.constantCoeff (R := E) Q * PowerSeries.coeff 1 P := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  ring

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {E : Type} [CommRing E] (b : Sp E ⟶ S) {n : ℕ}
  {V : S.Opens} (τ : Fin n → Γ(Lie G, V)) (w : Fin n → E)

/- English proof (translation)
Take `⟨-, -, ev_res, -⟩` from `GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `h1 : dUnit G heb (G.left.presheaf.map (homOfLE k).op g) = resM _ hab (dUnit G hea g)`. Rewrite using `[resM_dUnit]`.

Conclude with `dUnit_resG G heb k g`. Rewrite using `[h1]`. Establish `h2` using `dualApp_resM (τ i) hVa hab (dUnit G hea g)`. Rewrite using `[h2]`. Conclude with `ev_res E S b Va Vb hab hba hbb _`.
-/
theorem rhs_res {Ua Ub : G.left.Opens} (k : Ub ≤ Ua) {Va Vb : S.Opens} (hVa : Va ≤ V) (hVb : Vb ≤ V)
    (hab : Vb ≤ Va) (hea : Va ≤ unitSec G ⁻¹ᵁ Ua) (heb : Vb ≤ unitSec G ⁻¹ᵁ Ub) (hba : ⊤ ≤ b ⁻¹ᵁ Va)
    (hbb : ⊤ ≤ b ⁻¹ᵁ Vb) (g : Γ(G.left, Ua)) :
    ∑ i, w i * evAt b hbb (dualApp (τ i) hVb (dUnit G heb (G.left.presheaf.map (homOfLE k).op g))) =
      ∑ i, w i * evAt b hba (dualApp (τ i) hVa (dUnit G hea g)) := by
  obtain ⟨-, -, ev_res, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have h1 : dUnit G heb (G.left.presheaf.map (homOfLE k).op g) = resM _ hab (dUnit G hea g) := by
    rw [resM_dUnit]; exact dUnit_resG G heb k g
  rw [h1]
  have h2 := dualApp_resM (τ i) hVa hab (dUnit G hea g)
  rw [h2]
  exact ev_res E S b Va Vb hab hba hbb _

/- English proof (translation)
Take `⟨ev_map, ev_comp, -, -⟩` from `GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk`. Establish `hc : ⊤ ≤ (b ≫ unitSec G) ⁻¹ᵁ U₂`. Introduce `x _`. Use `show (b ≫ unitSec G) x ∈ U₂`. Rewrite using `[← hz, Scheme.Hom.comp_apply]`.

Conclude with `hU₂ (show _ ∈ (⊤ : (Sp (PowerSeries E)).Opens) from trivial)`. Establish `hc' : ⊤ ≤ (spMap (PowerSeries.constantCoeff (R` using `E)) ≫ ξ) ⁻¹ᵁ U₂ := hz ▸ hc`. Establish `hε : ∀ f : Γ(G.left, U₂), evAt b hb₂ ((unitSec G).appLE U₂ V₂ he₂ f) = PowerSeries.constantCoeff (R` using `E) (evAt ξ hU₂ f) := by`. Introduce `f`. Rewrite using `[← ev_comp E S G.left b (unitSec G) V₂ U₂ hb₂ hc he₂ f, ← ev_congr hz hc' hc, ev_map (PowerSeries E) E G.left (PowerSeries.constantCoeff (R := E)) ξ U₂ hU₂ hc' f]`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[dUnit_mul, map_add, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hε, hε]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhs_mul (ξ : Sp (PowerSeries E) ⟶ G.left)
    (hz : spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ = b ≫ unitSec G) {U₂ : G.left.Opens}
    (hU₂ : ⊤ ≤ ξ ⁻¹ᵁ U₂) {V₂ : S.Opens} (hV₂ : V₂ ≤ V) (he₂ : V₂ ≤ unitSec G ⁻¹ᵁ U₂)
    (hb₂ : ⊤ ≤ b ⁻¹ᵁ V₂) (g k : Γ(G.left, U₂)) :
    ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ (g * k))) =
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ g) * ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ k)) +
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ k) * ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ g)) := by
  obtain ⟨ev_map, ev_comp, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  have hc : ⊤ ≤ (b ≫ unitSec G) ⁻¹ᵁ U₂ := by
    intro x _
    show (b ≫ unitSec G) x ∈ U₂
    rw [← hz, Scheme.Hom.comp_apply]
    exact hU₂ (show _ ∈ (⊤ : (Sp (PowerSeries E)).Opens) from trivial)
  have hc' : ⊤ ≤ (spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ) ⁻¹ᵁ U₂ := hz ▸ hc
  have hε : ∀ f : Γ(G.left, U₂), evAt b hb₂ ((unitSec G).appLE U₂ V₂ he₂ f) =
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ f) := by
    intro f
    rw [← ev_comp E S G.left b (unitSec G) V₂ U₂ hb₂ hc he₂ f, ← ev_congr hz hc' hc,
      ev_map (PowerSeries E) E G.left (PowerSeries.constantCoeff (R := E)) ξ U₂ hU₂ hc' f]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dUnit_mul, map_add, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, map_add,
    map_mul, map_mul, hε, hε]
  ring

end GlobalTheory.Nef.TanLoc

namespace GlobalTheory.Nef

open TanLoc in

/- English proof (translation)
Introduce `S G _ E _ c b ξ hξ n V τ w U hUa hU V' hV he hb H U₁ hU₁ V₁ hV₁ he₁ hb₁ f₁`. Take `⟨-, -, ev_res, ev_loc, -⟩` from `GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk`. Establish `hyU` using `(ev_loc (PowerSeries E) G.left ξ U).1 hU`. Establish `hyU₁` using `(ev_loc (PowerSeries E) G.left ξ U₁).1 hU₁`. Take `⟨t, htle, hyt⟩` from `hUa.exists_basicOpen_le ⟨_, hyU₁⟩ hyU`.

Establish `hk : G.left.basicOpen t ≤ U` using `G.left.basicOpen_le t`. Establish `hU₂ : ⊤ ≤ ξ ⁻¹ᵁ G.left.basicOpen t` using `(ev_loc (PowerSeries E) G.left ξ _).2 hyt`. Establish `hV₂ : V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t ≤ V` using `inf_le_left.trans (inf_le_left.trans hV)`. Establish `he₂ : V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t ≤ unitSec G ⁻¹ᵁ G.left.basicOpen t` using `inf_le_right`. Establish `hb₂ : ⊤ ≤ b ⁻¹ᵁ (V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t)`.

Introduce `x hx`. Use `⟨⟨hb hx, hb₁ hx⟩, ?_⟩` and prove the remaining obligations. Use `show unitSec G (b x) ∈ G.left.basicOpen t`. Rewrite using `[← Scheme.Hom.comp_apply, ← hξ.zero, Scheme.Hom.comp_apply]`. Conclude with `hU₂ (show _ ∈ (⊤ : (Sp (PowerSeries E)).Opens) from trivial)`.

Use `set L₂ : Γ(G.left, G.left.basicOpen t) → E := fun g => PowerSeries.coeff 1 (evAt ξ hU₂ g) with hL₂`. Use `set R₂ : Γ(G.left, G.left.basicOpen t) → E := fun g => ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ g)) with hR₂`. Use `set ε : Γ(G.left, G.left.basicOpen t) →+* E := (PowerSeries.constantCoeff (R := E)).comp (evAt ξ hU₂) with hε`. Establish `Lmul : ∀ g k, L₂ (g * k) = ε g * L₂ k + ε k * L₂ g` using `fun g k => by`. Simplify using `only [hL₂, hε, RingHom.comp_apply, map_mul, coeff_one_mul]`.

Establish `Rmul : ∀ g k, R₂ (g * k) = ε g * R₂ k + ε k * R₂ g` using `fun g k => rhs_mul G b τ w ξ hξ.zero hU₂ hV₂ he₂ hb₂ g k`. Establish `hA : ∀ g : Γ(G.left, U), L₂ (G.left.presheaf.map (homOfLE hk).op g) = R₂ (G.left.presheaf.map (homOfLE hk).op g)`. Introduce `g`. Simplify using `only [hL₂, hR₂]`. Rewrite using `[ev_res (PowerSeries E) G.left ξ U _ hk hU hU₂, H g, rhs_res G b τ w hk hV hV₂ (inf_le_left.trans inf_le_left) he he₂ hb hb₂ g]`.

Establish `hk₁ : G.left.basicOpen t ≤ U₁` using `htle`. Establish `hB : L₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) = PowerSeries.coeff 1 (evAt ξ hU₁ f₁) ∧ R₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) = ∑ i, w i * evAt b hb₁ (dualApp (τ i) hV₁ (dUnit G he₁ f₁))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [hL₂]`. Rewrite using `[ev_res (PowerSeries E) G.left ξ U₁ _ hk₁ hU₁ hU₂]`.

Conclude with `rhs_res G b τ w hk₁ hV₁ hV₂ (inf_le_left.trans inf_le_right) he₁ he₂ hb₁ hb₂ f₁`. Rewrite using `[← hB.1, ← hB.2]`. Establish `hl` using `hUa.isLocalization_basicOpen t`. Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers t) (G.left.presheaf.map (homOfLE hk₁).op f₁)`. Establish `hunit : IsUnit (algebraMap Γ(G.left, U) Γ(G.left, G.left.basicOpen t) (s : Γ(G.left, U)))` using `IsLocalization.map_units _ s`.

Establish `hs' : algebraMap Γ(G.left, U) Γ(G.left, G.left.basicOpen t) = (G.left.presheaf.map (homOfLE hk).op).hom` using `rfl`. Rewrite `hs`, `hunit` using `[hs']`. Establish `key` using `congrArg (fun z => L₂ z - R₂ z) hs`. Simplify using `only at key`. Rewrite `key` using `[Lmul, Rmul, hA a, hA s, sub_self]`.

Establish `hne : ε ((G.left.presheaf.map (homOfLE hk).op).hom s) ≠ 0` using `(hunit.map ε).ne_zero`. Establish `: ε ((G.left.presheaf.map (homOfLE hk).op).hom s) * (L₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) - R₂ (G.left.presheaf.map (homOfLE hk₁).op f₁)) = 0`. Rewrite using `[← key]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)`.
-/
theorem hasTan_of_affine_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (E : Type) [Field E] (c : E) (b : Sp E ⟶ S) (ξ : Sp (PowerSeries E) ⟶ G.left), IsPath G c b ξ → ∀ (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → E) (U : G.left.Opens), IsAffineOpen U → ∀ (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V'), (∀ f : Γ(G.left, U), PowerSeries.coeff 1 (evAt ξ hU f) = ∑ i, w i * evAt b hb (dualApp (τ i) hV (dUnit G he f))) → HasTan G b ξ τ w := by
  intro S G _ E _ c b ξ hξ n V τ w U hUa hU V' hV he hb H U₁ hU₁ V₁ hV₁ he₁ hb₁ f₁
  obtain ⟨-, -, ev_res, ev_loc, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  have hyU := (ev_loc (PowerSeries E) G.left ξ U).1 hU
  have hyU₁ := (ev_loc (PowerSeries E) G.left ξ U₁).1 hU₁
  obtain ⟨t, htle, hyt⟩ := hUa.exists_basicOpen_le ⟨_, hyU₁⟩ hyU
  have hk : G.left.basicOpen t ≤ U := G.left.basicOpen_le t
  have hU₂ : ⊤ ≤ ξ ⁻¹ᵁ G.left.basicOpen t := (ev_loc (PowerSeries E) G.left ξ _).2 hyt
  have hV₂ : V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t ≤ V := inf_le_left.trans (inf_le_left.trans hV)
  have he₂ : V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t ≤ unitSec G ⁻¹ᵁ G.left.basicOpen t := inf_le_right
  have hb₂ : ⊤ ≤ b ⁻¹ᵁ (V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t) := by
    intro x hx
    refine ⟨⟨hb hx, hb₁ hx⟩, ?_⟩
    show unitSec G (b x) ∈ G.left.basicOpen t
    rw [← Scheme.Hom.comp_apply, ← hξ.zero, Scheme.Hom.comp_apply]
    exact hU₂ (show _ ∈ (⊤ : (Sp (PowerSeries E)).Opens) from trivial)
  set L₂ : Γ(G.left, G.left.basicOpen t) → E := fun g => PowerSeries.coeff 1 (evAt ξ hU₂ g) with hL₂
  set R₂ : Γ(G.left, G.left.basicOpen t) → E :=
    fun g => ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ g)) with hR₂
  set ε : Γ(G.left, G.left.basicOpen t) →+* E := (PowerSeries.constantCoeff (R := E)).comp (evAt ξ hU₂) with hε
  have Lmul : ∀ g k, L₂ (g * k) = ε g * L₂ k + ε k * L₂ g := fun g k => by
    simp only [hL₂, hε, RingHom.comp_apply, map_mul, coeff_one_mul]
  have Rmul : ∀ g k, R₂ (g * k) = ε g * R₂ k + ε k * R₂ g := fun g k =>
    rhs_mul G b τ w ξ hξ.zero hU₂ hV₂ he₂ hb₂ g k
  have hA : ∀ g : Γ(G.left, U), L₂ (G.left.presheaf.map (homOfLE hk).op g) =
      R₂ (G.left.presheaf.map (homOfLE hk).op g) := by
    intro g
    simp only [hL₂, hR₂]
    rw [ev_res (PowerSeries E) G.left ξ U _ hk hU hU₂, H g,
      rhs_res G b τ w hk hV hV₂ (inf_le_left.trans inf_le_left) he he₂ hb hb₂ g]
  have hk₁ : G.left.basicOpen t ≤ U₁ := htle
  have hB : L₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) = PowerSeries.coeff 1 (evAt ξ hU₁ f₁) ∧
      R₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) =
        ∑ i, w i * evAt b hb₁ (dualApp (τ i) hV₁ (dUnit G he₁ f₁)) := by
    refine ⟨?_, ?_⟩
    · simp only [hL₂]; rw [ev_res (PowerSeries E) G.left ξ U₁ _ hk₁ hU₁ hU₂]
    · exact rhs_res G b τ w hk₁ hV₁ hV₂ (inf_le_left.trans inf_le_right) he₁ he₂ hb₁ hb₂ f₁
  rw [← hB.1, ← hB.2]
  have hl := hUa.isLocalization_basicOpen t
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers t) (G.left.presheaf.map (homOfLE hk₁).op f₁)
  have hunit : IsUnit (algebraMap Γ(G.left, U) Γ(G.left, G.left.basicOpen t) (s : Γ(G.left, U))) :=
    IsLocalization.map_units _ s
  have hs' : algebraMap Γ(G.left, U) Γ(G.left, G.left.basicOpen t) = (G.left.presheaf.map (homOfLE hk).op).hom := rfl
  rw [hs'] at hs hunit
  have key := congrArg (fun z => L₂ z - R₂ z) hs
  simp only at key
  rw [Lmul, Rmul, hA a, hA s, sub_self] at key
  have hne : ε ((G.left.presheaf.map (homOfLE hk).op).hom s) ≠ 0 := (hunit.map ε).ne_zero
  have : ε ((G.left.presheaf.map (homOfLE hk).op).hom s) *
      (L₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) - R₂ (G.left.presheaf.map (homOfLE hk₁).op f₁)) = 0 := by
    rw [← key]; ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)

end GlobalTheory.Nef

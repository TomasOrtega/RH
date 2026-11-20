import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointGenericInjectiveFractionStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `k K E _ _ _ _ _ _ _ _ _ _ C _ x hx G _ hG W r i hi V₀ s hV₀ hs w hw`. Use `haveI := hG`. Use `haveI := hi`. Use `haveI : IsIntegral C := LieSemineg.isIntegral_curve hx.1.1 hx.1.2.2`. Use `haveI : Smooth G.hom := hG.smooth`.

Take `⟨h₀, -, -⟩` from `GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V₀ hV₀`. Establish `hp₀ : x (IsLocalRing.closedPoint K) ∈ V₀` using `(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 K C x V₀).1 h₀`. Take `⟨U₁, n, om, hpU₁, hom⟩` from `exists_isFrame_omega G (x (IsLocalRing.closedPoint K))`. Take `⟨V', U, hpV', hV'le, c⟩` from `GlobalTheory.Conormal.exists_isChart (he := sec_hom η[G]) (show x (IsLocalRing.closedPoint K) ∈ V₀ ⊓ U₁ from ⟨hp₀, hpU₁⟩)`. Establish `hV : V' ≤ V₀` using `hV'le.trans inf_le_left`.

Establish `hVU : V' ≤ U₁` using `hV'le.trans inf_le_right`. Take `⟨hx', hinj, -⟩` from `GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V' ⟨_, hpV'⟩`. Establish `hb : ⊤ ≤ (spMap (algebraMap K E) ≫ x) ⁻¹ᵁ V'` using `fun z _ => hx' (Set.mem_univ _)`. Establish `hev : ∀ g : Γ(C, V'), evAt (spMap (algebraMap K E) ≫ x) hb g = algebraMap K E (evAt x hx' g)` using `fun g => GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 K E C (algebraMap K E) x V' hx' hb g`. Establish `key : ∀ f : Γ(G.left, U), ∑ j, w j * algebraMap K E (evAt x hx' (dualApp (i.app V₀ (s j)) hV (dUnit G c.le f))) = 0`.

Introduce `f`. Establish `h2 : ⊤ ≤ ((spMap (algebraMap K E) ≫ x) ≫ unitSec G) ⁻¹ᵁ U` using `fun z _ => c.le (hb (Set.mem_univ z))`. Establish `hU : ⊤ ≤ (triv G (spMap (algebraMap K E) ≫ x)) ⁻¹ᵁ U` using `fun z _ => h2 (Set.mem_univ _)`. Use `hw U hU V' hV c.le hb f` as an intermediate fact. Simplify using `only [hev] at this`.

Rewrite using `[← this]`. Establish `e1 : evAt (triv G (spMap (algebraMap K E) ≫ x)) hU f = PowerSeries.C (R` using `E) (evAt _ h2 f) := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 E (PowerSeries E) G.left (PowerSeries.C (R := E)) _ U h2 hU f`. Rewrite using `[e1]`. Simplify using the standard rewrite rules. Establish `key2 : ∀ e' : Γ(omega G, V'), ∑ j, w j * algebraMap K E (evAt x hx' (dualApp (i.app V₀ (s j)) hV e')) = 0`.

Introduce `e'`. Take `⟨f, rfl⟩` from `c.d_surjective (sec_hom η[G]) e'`. Conclude with `key f`. Use `haveI : Nonempty V' := ⟨⟨_, hpV'⟩⟩`. Set `N : Matrix (Fin r) (Fin n) Γ(C, V')` to `fun j a => dualApp (i.app V₀ (s j)) hV (resM (omega G) hVU (om a))`.

Establish `hN : LinearIndependent Γ(C, V') N.row`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `hl : (∑ j, g j • resM (Lie G) hV (i.app V₀ (s j))) = 0`. Use `hom.dual_ext hVU (fun a => ?_)` and prove the remaining obligations.

Use `congrFun hg a` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row, N] at this`. Rewrite using `[dualApp_sum, LinearMap.sum_apply, dualApp_zero, LinearMap.zero_apply]`. Simplify `this` using `only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, dualApp_res, GlobalTheory.LB.resG_self]`. Establish `hs' : ∑ j, g j • resM W hV (s j) = 0`.

Apply `QCoh.injective_app_of_mono i V'` to reduce the goal to its premises. Simplify using `only [map_sum, map_zero, Scheme.Modules.Hom.app_smul, Twist.app_resM]`. Conclude with `hl`. Establish `hli` using `(hs.basis hV).linearIndependent`. Rewrite `hli` using `[hs.coe_basis hV, Fintype.linearIndependent_iff]`.

Conclude with `hli g hs'`. Take `⟨σ, hσ⟩` from `LieSemineg.exists_det_ne_zero N hN`. Set `φ : Γ(C, V') →+* E` to `(algebraMap K E).comp (evAt x hx')`. Establish `hφ : Function.Injective φ` using `(algebraMap K E).injective.comp hinj`. Establish `hA : ((N.submatrix id σ).map φ).det ≠ 0`.

Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `fun h => hσ (hφ (h.trans (map_zero φ).symm))`. Use `Matrix.eq_zero_of_vecMul_eq_zero hA ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.submatrix_apply, id, Pi.zero_apply, N, φ, RingHom.comp_apply]`.

Conclude with `key2 _`.
-/
theorem tan_triv_eq_zero : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ w : Fin r → E, HasTan G (spMap (algebraMap K E) ≫ x) (triv G (spMap (algebraMap K E) ≫ x)) (fun j => i.app V₀ (s j)) w → w = 0 := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx G _ hG W r i hi V₀ s hV₀ hs w hw
  haveI := hG
  haveI := hi
  haveI : IsIntegral C := LieSemineg.isIntegral_curve hx.1.1 hx.1.2.2
  haveI : Smooth G.hom := hG.smooth
  obtain ⟨h₀, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V₀ hV₀
  have hp₀ : x (IsLocalRing.closedPoint K) ∈ V₀ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 K C x V₀).1 h₀
  obtain ⟨U₁, n, om, hpU₁, hom⟩ := exists_isFrame_omega G (x (IsLocalRing.closedPoint K))
  obtain ⟨V', U, hpV', hV'le, c⟩ := GlobalTheory.Conormal.exists_isChart (he := sec_hom η[G])
    (show x (IsLocalRing.closedPoint K) ∈ V₀ ⊓ U₁ from ⟨hp₀, hpU₁⟩)
  have hV : V' ≤ V₀ := hV'le.trans inf_le_left
  have hVU : V' ≤ U₁ := hV'le.trans inf_le_right
  obtain ⟨hx', hinj, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V' ⟨_, hpV'⟩
  have hb : ⊤ ≤ (spMap (algebraMap K E) ≫ x) ⁻¹ᵁ V' := fun z _ => hx' (Set.mem_univ _)
  have hev : ∀ g : Γ(C, V'), evAt (spMap (algebraMap K E) ≫ x) hb g = algebraMap K E (evAt x hx' g) :=
    fun g => GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 K E C (algebraMap K E) x V' hx' hb g
  have key : ∀ f : Γ(G.left, U), ∑ j, w j * algebraMap K E (evAt x hx'
      (dualApp (i.app V₀ (s j)) hV (dUnit G c.le f))) = 0 := by
    intro f
    have h2 : ⊤ ≤ ((spMap (algebraMap K E) ≫ x) ≫ unitSec G) ⁻¹ᵁ U := fun z _ => c.le (hb (Set.mem_univ z))
    have hU : ⊤ ≤ (triv G (spMap (algebraMap K E) ≫ x)) ⁻¹ᵁ U := fun z _ => h2 (Set.mem_univ _)
    have := hw U hU V' hV c.le hb f
    simp only [hev] at this
    rw [← this]
    have e1 : evAt (triv G (spMap (algebraMap K E) ≫ x)) hU f = PowerSeries.C (R := E) (evAt _ h2 f) :=
      GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 E (PowerSeries E) G.left (PowerSeries.C (R := E)) _ U h2 hU f
    rw [e1]
    simp
  have key2 : ∀ e' : Γ(omega G, V'), ∑ j, w j * algebraMap K E (evAt x hx'
      (dualApp (i.app V₀ (s j)) hV e')) = 0 := by
    intro e'
    obtain ⟨f, rfl⟩ := c.d_surjective (sec_hom η[G]) e'
    exact key f
  haveI : Nonempty V' := ⟨⟨_, hpV'⟩⟩
  let N : Matrix (Fin r) (Fin n) Γ(C, V') := fun j a => dualApp (i.app V₀ (s j)) hV (resM (omega G) hVU (om a))
  have hN : LinearIndependent Γ(C, V') N.row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hl : (∑ j, g j • resM (Lie G) hV (i.app V₀ (s j))) = 0 := by
      refine hom.dual_ext hVU (fun a => ?_)
      have := congrFun hg a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row, N] at this
      rw [dualApp_sum, LinearMap.sum_apply, dualApp_zero, LinearMap.zero_apply]
      simpa only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, dualApp_res, GlobalTheory.LB.resG_self] using this
    have hs' : ∑ j, g j • resM W hV (s j) = 0 := by
      apply QCoh.injective_app_of_mono i V'
      simp only [map_sum, map_zero, Scheme.Modules.Hom.app_smul, Twist.app_resM]
      exact hl
    have hli := (hs.basis hV).linearIndependent
    rw [hs.coe_basis hV, Fintype.linearIndependent_iff] at hli
    exact hli g hs'
  obtain ⟨σ, hσ⟩ := LieSemineg.exists_det_ne_zero N hN
  let φ : Γ(C, V') →+* E := (algebraMap K E).comp (evAt x hx')
  have hφ : Function.Injective φ := (algebraMap K E).injective.comp hinj
  have hA : ((N.submatrix id σ).map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hσ (hφ (h.trans (map_zero φ).symm))
  refine Matrix.eq_zero_of_vecMul_eq_zero hA ?_
  funext a
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.submatrix_apply, id, Pi.zero_apply, N, φ,
    RingHom.comp_apply]
  exact key2 _

end GlobalTheory.Nef

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalSquaringPathWithTangentVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueOfAgreeLowDegreesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathsBaseChangeAndHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTangentOfSingleAffineChartStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

/- English proof (translation)
Rewrite using `[Scheme.Hom.comp_preimage, top_le_iff.1 h, Scheme.Hom.preimage_top]`.
-/
private theorem top_le_comp_preimage {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ g ⁻¹ᵁ U) :
    ⊤ ≤ (f ≫ g) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage, top_le_iff.1 h, Scheme.Hom.preimage_top]

/- English proof (translation)
Rewrite `h` using `[Scheme.Hom.comp_preimage]`. Then use the resulting hypothesis.
-/
private theorem top_le_of_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ (f ≫ g) ⁻¹ᵁ U) :
    ⊤ ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  rwa [Scheme.Hom.comp_preimage] at h

/- English proof (translation)
Introduce `y _` and use `⟨hA trivial, hB trivial⟩`.
-/
private theorem top_le_preimage_inf {X Y : Scheme.{0}} (f : X ⟶ Y) {A B : Y.Opens} (hA : ⊤ ≤ f ⁻¹ᵁ A)
    (hB : ⊤ ≤ f ⁻¹ᵁ B) : ⊤ ≤ f ⁻¹ᵁ (A ⊓ B) :=
  fun y _ => ⟨hA trivial, hB trivial⟩

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
private theorem evAt_congr {R : Type} [CommRing R] {X : Scheme.{0}} {ξ ξ' : Sp R ⟶ X} (e : ξ = ξ') {U : X.Opens}
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) : evAt ξ h = evAt ξ' h' := by
  subst e; rfl

private def resO {k K E : Type} [Field k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E]
    {ρ : Place k E → Place k K} (hρ : IsRes ρ) (p : Place k E) : (ρ p).O →+* p.O :=
  ((algebraMap K E).comp (ρ p).O.subtype).codRestrict p.O fun y =>
    (Valuation.mem_valuationSubring_iff _ _).2 ((hρ p y).2 ((Valuation.mem_valuationSubring_iff _ _).1 y.2))

private def constO {k E : Type} [Field k] [Field E] [Algebra k E] (p : Place k E) : k →+* p.O :=
  (algebraMap k E).codRestrict p.O fun c => by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (p.2.2 c hc).le

/- English proof (translation)
Introduce `k K E _ _ _ _ _ _ _ _ _ _ C _ x _ G _ hG W r i V₀ s ρ hρ p g hg w u hu hpu ξ hξ hξt`. Establish `hsm : Smooth G.hom` using `hG.smooth`. Establish `hqs : QuasiSeparated G.hom` using `by haveI := hG.separated; infer_instance`. Use `haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective`. Take `⟨b₀, V, t, Vf, h₀, h₁, hxf, M, hb₀, hb₀V, -, hst, rfl⟩` from `hg`.

Use `set xE := spMap (algebraMap K E) ≫ x with hxE`. Set `α` to `resO hρ p`. Set `φ : p.O →+* E` to `p.O.subtype`. Set `b : Sp p.O ⟶ C` to `spMap α ≫ b₀`. Establish `hbx : spMap φ ≫ b = xE`.

Rewrite using `[hxE, ← hb₀]`. Simplify using `only [b, ← Category.assoc, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Use `letI : Algebra ℚ p.O := ((constO p).comp (algebraMap ℚ k)).toAlgebra`. Establish `hbV : ⊤ ≤ b ⁻¹ᵁ V` using `top_le_comp_preimage _ _ hb₀V`.

Set `y : Fin r → E` to `((M.map (evAt x hxf)).map (algebraMap K E)).mulVec w`. Set `eE : Fin r → E` to `fun j => u⁻¹ * y j`. Establish `heO : ∀ j, eE j ∈ p.O`. Introduce `j`. Rewrite using `[Valuation.mem_valuationSubring_iff]`.

Establish `hle : p.1 (y j) ≤ p.1 u`. Rewrite using `[hpu, nrm]`. Conclude with `Finset.le_sup (f := fun i => p.1 (y i)) (Finset.mem_univ j)`. Establish `hu0 : p.1 u ≠ 0` using `(Valuation.ne_zero_iff _).2 hu`. Combine the equalities or inequalities in the displayed calculation.

Set `e : Fin r → p.O` to `fun j => ⟨eE j, heO j⟩`. Take `⟨ζ, hζ, hζt⟩` from `GlobalTheory.T.exists_formalSquaringPath_with_tangentVector C G p.O hsm hqs b r V (fun j => i.app V (t j)) e hbV`. Take `⟨U₀, hU₀a, hζU₀, -⟩` from `Opens.isBasis_iff_nbhd.1 G.left.isBasis_affineOpens (Opens.mem_top (ζ (IsLocalRing.closedPoint (PowerSeries p.O))))`. Establish `hζU : ⊤ ≤ ζ ⁻¹ᵁ U₀` using `(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 (PowerSeries p.O) G.left ζ U₀).2 hζU₀`. Establish `hξ'U : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U₀` using `top_le_comp_preimage _ _ hζU`.

Establish `hξ'path : IsPath G 2 xE (spMap (sc p u) ≫ ζ)`. Use `(GlobalTheory.T.formalSquaringPaths_baseChange_and_hom.1 C G p.O E φ 2 u b ζ hζ).1` as an intermediate fact. Rewrite `this` using `[map_ofNat, hbx]`. Conclude with `this`. Establish `hxEf : ⊤ ≤ xE ⁻¹ᵁ Vf` using `top_le_comp_preimage _ _ hxf`.

Establish `hxE0 : ⊤ ≤ xE ⁻¹ᵁ V₀` using `hxEf.trans (Scheme.Hom.preimage_mono xE h₀)`. Establish `hxEu : ⊤ ≤ xE ⁻¹ᵁ (unitSec G ⁻¹ᵁ U₀)`. Apply `top_le_of_comp` to reduce the goal to its premises. Rewrite using `[← hξ'path.zero]`. Conclude with `top_le_comp_preimage _ _ hξ'U`.

Establish `hbu : ⊤ ≤ b ⁻¹ᵁ (unitSec G ⁻¹ᵁ U₀)`. Apply `top_le_of_comp` to reduce the goal to its premises. Rewrite using `[← hζ.zero]`. Conclude with `top_le_comp_preimage _ _ hζU`. Establish `hxs : ⊤ ≤ xE ⁻¹ᵁ (Vf ⊓ unitSec G ⁻¹ᵁ U₀)` using `top_le_preimage_inf _ hxEf hxEu`.

Establish `hb'' : ⊤ ≤ b ⁻¹ᵁ (V ⊓ unitSec G ⁻¹ᵁ U₀)` using `top_le_preimage_inf _ hbV hbu`. Establish `hxE'' : ⊤ ≤ xE ⁻¹ᵁ (V ⊓ unitSec G ⁻¹ᵁ U₀)` using `by rw [← hbx]; exact top_le_comp_preimage _ _ hb''`. Establish `hsub : Vf ⊓ unitSec G ⁻¹ᵁ U₀ ≤ V ⊓ unitSec G ⁻¹ᵁ U₀` using `inf_le_inf_right _ h₁`. Establish `key : ∀ f : Γ(G.left, U₀), PowerSeries.coeff 1 (evAt (spMap (sc p u) ≫ ζ) hξ'U f) = ∑ j, w j * evAt xE hxs (dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) (dUnit G inf_le_right f))`. Introduce `f`.

Establish `h1` using `(GlobalTheory.T.formalSquaringPaths_baseChange_and_hom.1 C G p.O E φ 2 u b ζ hζ).2 r V (fun j => i.app V (t j)) e hbV U₀ hζU hζt hξ'U (V ⊓ unitSec G ⁻¹ᵁ U₀) inf_le_left inf_le_right hb'' f`. Establish `hD : ∀ τ : Γ(Lie G, V), φ (evAt b hb'' (dualApp τ inf_le_left (dUnit G inf_le_right f))) = evAt xE hxs (dualApp τ (hsub.trans inf_le_left) (dUnit G (hsub.trans inf_le_right) f))`. Introduce `τ`. Rewrite using `[← GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 p.O E C φ b _ hb'' (top_le_comp_preimage _ _ hb''), evAt_congr hbx _ hxE'', ← GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.1 E C xE _ _ hsub hxE'' hxs]`. Use `congr 1`.

Use `dualApp_resM τ (inf_le_left : V ⊓ unitSec G ⁻¹ᵁ U₀ ≤ V) hsub (dUnit G inf_le_right f)` as an intermediate fact. Rewrite `this` using `[resM_dUnit]`. Conclude with `this.symm`. Establish `hR : ∀ j, evAt xE hxs (dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) (dUnit G inf_le_right f)) = ∑ l, algebraMap K E (evAt x hxf (M l j)) * evAt xE hxs (dualApp (i.app V (t l)) (hsub.trans inf_le_left) (dUnit G (hsub.trans inf_le_right) f))`. Introduce `j`.

Establish `e1 : dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) = dualApp (resM _ h₀ (i.app V₀ (s j))) (inf_le_left : Vf ⊓ unitSec G ⁻¹ᵁ U₀ ≤ Vf)` using `(dualApp_res _ _ _).symm`. Establish `e2 : resM _ h₀ (i.app V₀ (s j)) = ∑ l, M l j • resM _ h₁ (i.app V (t l))`. Rewrite using `[← GlobalTheory.Twist.app_resM, hst, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Scheme.Modules.Hom.app_smul, GlobalTheory.Twist.app_resM]`.

Rewrite using `[e1, e2, dualApp_sum, LinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, dualApp_res]`. Use `congr 1`. Conclude with `(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.1 E C xE Vf _ inf_le_left hxEf hxs (M l j)).trans (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 K E C (algebraMap K E) x Vf hxf hxEf (M l j))`.

Establish `he' : ∀ l, u * φ (e l) = ∑ j, algebraMap K E (evAt x hxf (M l j)) * w j`. Introduce `l`. Use `show u * (u⁻¹ * y l) = _`. Rewrite using `[← _root_.mul_assoc, mul_inv_cancel₀ hu, _root_.one_mul]`. Simplify using `[y, Matrix.mulVec, dotProduct]`.

Use `Eq.trans h1 ?_` and prove the remaining obligations. Simplify using `only [hD, hR, he', Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `htan' : HasTan G xE (spMap (sc p u) ≫ ζ) (fun j => i.app V₀ (s j)) w` using `GlobalTheory.T.hasTangent_of_single_affineChart C G E 2 xE _ hξ'path r V₀ _ w U₀ hU₀a hξ'U _ (inf_le_left.trans h₀) inf_le_right hxs key`. Establish `hunit : ∀ j, 2 ≤ j → IsUnit ((2 : E) ^ j - 2)`. Introduce `j hj`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Establish `h4 : 4 ≤ 2 ^ j`.

Combine the equalities or inequalities in the displayed calculation. Establish `hc : ((2 ^ j - 2 : ℕ) : E) = 0`. Rewrite using `[Nat.cast_sub (by omega : 2 ≤ 2 ^ j)]; push_cast; exact h0`. Rewrite `hc` using `[Nat.cast_eq_zero]`. Use linear arithmetic over natural numbers and integers.

Establish `heq : ξ = spMap (sc p u) ≫ ζ`. Use `GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees C G E hqs 2 2 (by norm_num) hunit xE ξ _ hξ hξ'path ?_` and prove the remaining obligations. Introduce `U h h' f j hj0 hj2`. Take `rfl : j = 1` from `by omega`. Establish `hb3 : ⊤ ≤ xE ⁻¹ᵁ (V₀ ⊓ unitSec G ⁻¹ᵁ U)`.

Use `top_le_preimage_inf _ hxE0 ?_` and prove the remaining obligations. Apply `top_le_of_comp` to reduce the goal to its premises. Rewrite using `[← hξ.zero]`. Conclude with `top_le_comp_preimage _ _ h`. Rewrite using `[hξt U h _ inf_le_left inf_le_right hb3 f, htan' U h' _ inf_le_left inf_le_right hb3 f]`.

Conclude with `⟨b, ζ, hbx, hζ, heq⟩`.
-/
theorem genPath_scaling : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G) (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (ρ : Place k E → Place k K), IsRes ρ → ∀ (p : Place k E) (g : Matrix (Fin r) (Fin r) K), LocFrame x s (ρ p) g → ∀ (w : Fin r → E) (u : E), u ≠ 0 → p.1 u = nrm p ((g.map (algebraMap K E)).mulVec w) → ∀ ξ, IsPath G 2 (spMap (algebraMap K E) ≫ x) ξ → HasTan G (spMap (algebraMap K E) ≫ x) ξ (fun j => i.app V₀ (s j)) w → ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p u) ≫ ζ := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x _ G _ hG W r i V₀ s ρ hρ p g hg w u hu hpu ξ hξ hξt
  have hsm : Smooth G.hom := hG.smooth
  have hqs : QuasiSeparated G.hom := by haveI := hG.separated; infer_instance
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  obtain ⟨b₀, V, t, Vf, h₀, h₁, hxf, M, hb₀, hb₀V, -, hst, rfl⟩ := hg
  set xE := spMap (algebraMap K E) ≫ x with hxE
  let α := resO hρ p
  let φ : p.O →+* E := p.O.subtype
  let b : Sp p.O ⟶ C := spMap α ≫ b₀
  have hbx : spMap φ ≫ b = xE := by
    rw [hxE, ← hb₀]
    simp only [b, ← Category.assoc, spMap, ← Spec.map_comp]
    rfl
  letI : Algebra ℚ p.O := ((constO p).comp (algebraMap ℚ k)).toAlgebra
  have hbV : ⊤ ≤ b ⁻¹ᵁ V := top_le_comp_preimage _ _ hb₀V
  let y : Fin r → E := ((M.map (evAt x hxf)).map (algebraMap K E)).mulVec w
  let eE : Fin r → E := fun j => u⁻¹ * y j
  have heO : ∀ j, eE j ∈ p.O := by
    intro j
    rw [Valuation.mem_valuationSubring_iff]
    have hle : p.1 (y j) ≤ p.1 u := by
      rw [hpu, nrm]; exact Finset.le_sup (f := fun i => p.1 (y i)) (Finset.mem_univ j)
    have hu0 : p.1 u ≠ 0 := (Valuation.ne_zero_iff _).2 hu
    calc p.1 (eE j) = (p.1 u)⁻¹ * p.1 (y j) := by simp only [eE, map_mul, map_inv₀]
      _ ≤ (p.1 u)⁻¹ * p.1 u := by gcongr
      _ = 1 := inv_mul_cancel₀ hu0
  let e : Fin r → p.O := fun j => ⟨eE j, heO j⟩
  obtain ⟨ζ, hζ, hζt⟩ := GlobalTheory.T.exists_formalSquaringPath_with_tangentVector C G p.O hsm hqs b r V (fun j => i.app V (t j)) e hbV
  obtain ⟨U₀, hU₀a, hζU₀, -⟩ := Opens.isBasis_iff_nbhd.1 G.left.isBasis_affineOpens
    (Opens.mem_top (ζ (IsLocalRing.closedPoint (PowerSeries p.O))))
  have hζU : ⊤ ≤ ζ ⁻¹ᵁ U₀ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 (PowerSeries p.O) G.left ζ U₀).2 hζU₀
  have hξ'U : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U₀ := top_le_comp_preimage _ _ hζU
  have hξ'path : IsPath G 2 xE (spMap (sc p u) ≫ ζ) := by
    have := (GlobalTheory.T.formalSquaringPaths_baseChange_and_hom.1 C G p.O E φ 2 u b ζ hζ).1
    rw [map_ofNat, hbx] at this
    exact this

  have hxEf : ⊤ ≤ xE ⁻¹ᵁ Vf := top_le_comp_preimage _ _ hxf
  have hxE0 : ⊤ ≤ xE ⁻¹ᵁ V₀ := hxEf.trans (Scheme.Hom.preimage_mono xE h₀)
  have hxEu : ⊤ ≤ xE ⁻¹ᵁ (unitSec G ⁻¹ᵁ U₀) := by
    apply top_le_of_comp
    rw [← hξ'path.zero]; exact top_le_comp_preimage _ _ hξ'U
  have hbu : ⊤ ≤ b ⁻¹ᵁ (unitSec G ⁻¹ᵁ U₀) := by
    apply top_le_of_comp
    rw [← hζ.zero]; exact top_le_comp_preimage _ _ hζU
  have hxs : ⊤ ≤ xE ⁻¹ᵁ (Vf ⊓ unitSec G ⁻¹ᵁ U₀) := top_le_preimage_inf _ hxEf hxEu
  have hb'' : ⊤ ≤ b ⁻¹ᵁ (V ⊓ unitSec G ⁻¹ᵁ U₀) := top_le_preimage_inf _ hbV hbu
  have hxE'' : ⊤ ≤ xE ⁻¹ᵁ (V ⊓ unitSec G ⁻¹ᵁ U₀) := by rw [← hbx]; exact top_le_comp_preimage _ _ hb''
  have hsub : Vf ⊓ unitSec G ⁻¹ᵁ U₀ ≤ V ⊓ unitSec G ⁻¹ᵁ U₀ := inf_le_inf_right _ h₁
  have key : ∀ f : Γ(G.left, U₀), PowerSeries.coeff 1 (evAt (spMap (sc p u) ≫ ζ) hξ'U f) =
      ∑ j, w j * evAt xE hxs (dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) (dUnit G inf_le_right f)) := by
    intro f
    have h1 := (GlobalTheory.T.formalSquaringPaths_baseChange_and_hom.1 C G p.O E φ 2 u b ζ hζ).2 r V (fun j => i.app V (t j)) e hbV U₀ hζU hζt hξ'U
      (V ⊓ unitSec G ⁻¹ᵁ U₀) inf_le_left inf_le_right hb'' f
    have hD : ∀ τ : Γ(Lie G, V), φ (evAt b hb'' (dualApp τ inf_le_left (dUnit G inf_le_right f))) =
        evAt xE hxs (dualApp τ (hsub.trans inf_le_left) (dUnit G (hsub.trans inf_le_right) f)) := by
      intro τ
      rw [← GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 p.O E C φ b _ hb'' (top_le_comp_preimage _ _ hb''), evAt_congr hbx _ hxE'',
        ← GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.1 E C xE _ _ hsub hxE'' hxs]
      congr 1
      have := dualApp_resM τ (inf_le_left : V ⊓ unitSec G ⁻¹ᵁ U₀ ≤ V) hsub (dUnit G inf_le_right f)
      rw [resM_dUnit] at this
      exact this.symm
    have hR : ∀ j, evAt xE hxs (dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) (dUnit G inf_le_right f)) =
        ∑ l, algebraMap K E (evAt x hxf (M l j)) * evAt xE hxs (dualApp (i.app V (t l))
          (hsub.trans inf_le_left) (dUnit G (hsub.trans inf_le_right) f)) := by
      intro j
      have e1 : dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) =
          dualApp (resM _ h₀ (i.app V₀ (s j))) (inf_le_left : Vf ⊓ unitSec G ⁻¹ᵁ U₀ ≤ Vf) :=
        (dualApp_res _ _ _).symm
      have e2 : resM _ h₀ (i.app V₀ (s j)) = ∑ l, M l j • resM _ h₁ (i.app V (t l)) := by
        rw [← GlobalTheory.Twist.app_resM, hst, map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Scheme.Modules.Hom.app_smul, GlobalTheory.Twist.app_resM]
      rw [e1, e2, dualApp_sum, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, dualApp_res]
      congr 1
      exact (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.1 E C xE Vf _ inf_le_left hxEf hxs (M l j)).trans
        (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 K E C (algebraMap K E) x Vf hxf hxEf (M l j))
    have he' : ∀ l, u * φ (e l) = ∑ j, algebraMap K E (evAt x hxf (M l j)) * w j := by
      intro l
      show u * (u⁻¹ * y l) = _
      rw [← _root_.mul_assoc, mul_inv_cancel₀ hu, _root_.one_mul]
      simp [y, Matrix.mulVec, dotProduct]
    refine Eq.trans h1 ?_
    simp only [hD, hR, he', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have htan' : HasTan G xE (spMap (sc p u) ≫ ζ) (fun j => i.app V₀ (s j)) w :=
    GlobalTheory.T.hasTangent_of_single_affineChart C G E 2 xE _ hξ'path r V₀ _ w U₀ hU₀a hξ'U _ (inf_le_left.trans h₀) inf_le_right hxs key
  have hunit : ∀ j, 2 ≤ j → IsUnit ((2 : E) ^ j - 2) := by
    intro j hj
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h4 : 4 ≤ 2 ^ j := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have hc : ((2 ^ j - 2 : ℕ) : E) = 0 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 ^ j)]; push_cast; exact h0
    rw [Nat.cast_eq_zero] at hc
    omega
  have heq : ξ = spMap (sc p u) ≫ ζ := by
    refine GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees C G E hqs 2 2 (by norm_num) hunit xE ξ _ hξ hξ'path ?_
    intro U h h' f j hj0 hj2
    obtain rfl : j = 1 := by omega
    have hb3 : ⊤ ≤ xE ⁻¹ᵁ (V₀ ⊓ unitSec G ⁻¹ᵁ U) := by
      refine top_le_preimage_inf _ hxE0 ?_
      apply top_le_of_comp
      rw [← hξ.zero]; exact top_le_comp_preimage _ _ h
    rw [hξt U h _ inf_le_left inf_le_right hb3 f, htan' U h' _ inf_le_left inf_le_right hb3 f]
  exact ⟨b, ζ, hbx, hζ, heq⟩

end GlobalTheory.Nef

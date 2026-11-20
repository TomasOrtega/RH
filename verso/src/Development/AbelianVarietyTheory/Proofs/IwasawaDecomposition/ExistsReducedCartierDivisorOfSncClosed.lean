import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
open TopologicalSpace Opposite

namespace GlobalTheory.BoundaryDivisor

variable {X : Scheme.{0}}

section Pull

variable {Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j]

def pull (y : Y) : X.presheaf.stalk (j y) →+* Y.functionField :=
  (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (j.stalkMap y).hom

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
variable {Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j] in
omit [IsIntegral Y] in

/- English proof (translation)
The claim follows from `ConcreteCategory.bijective_of_isIso _`.
-/
theorem _root_.GlobalTheory.BoundaryDivisor.stalkMap_bijective (y : Y) : Function.Bijective (j.stalkMap y).hom :=
  ConcreteCategory.bijective_of_isIso _

end Pull

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
variable {Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j] in
/- English proof (translation)
Establish `hη : genericPoint Y ∈ j ⁻¹ᵁ V` using `((genericPoint_spec Y).mem_open_set_iff (j ⁻¹ᵁ V).isOpen).2 ⟨y, Set.mem_univ _, hy⟩`. Establish `e : ∀ (w : Y) (hw : j w ∈ V), _root_.GlobalTheory.BoundaryDivisor.pull j w (X.presheaf.germ V (j w) hw s) = Y.presheaf.germ (j ⁻¹ᵁ V) (genericPoint Y) hη (j.app V s)`. Introduce `w hw`. Express the relevant statement in the definitionally equal form `algebraMap (Y.presheaf.stalk w) Y.functionField (j.stalkMap w (X.presheaf.germ V (j w) hw s)) = _`. Rewrite using `[Scheme.Hom.germ_stalkMap_apply]`.

Simplify using `only [RingHom.algebraMap_toAlgebra]`. Conclude with `Y.presheaf.germ_stalkSpecializes_apply hw _ _`. Rewrite using `[e y hy, e z hz]`.
-/
private lemma pull_germ_eq_pull_germ (V : X.Opens) (s : Γ(X, V)) (y z : Y)
    (hy : j y ∈ V) (hz : j z ∈ V) :
    _root_.GlobalTheory.BoundaryDivisor.pull j y (X.presheaf.germ V (j y) hy s) =
      _root_.GlobalTheory.BoundaryDivisor.pull j z (X.presheaf.germ V (j z) hz s) := by
  have hη : genericPoint Y ∈ j ⁻¹ᵁ V :=
    ((genericPoint_spec Y).mem_open_set_iff (j ⁻¹ᵁ V).isOpen).2 ⟨y, Set.mem_univ _, hy⟩
  have e : ∀ (w : Y) (hw : j w ∈ V), _root_.GlobalTheory.BoundaryDivisor.pull j w (X.presheaf.germ V (j w) hw s) =
      Y.presheaf.germ (j ⁻¹ᵁ V) (genericPoint Y) hη (j.app V s) := by
    intro w hw
    change algebraMap (Y.presheaf.stalk w) Y.functionField
      (j.stalkMap w (X.presheaf.germ V (j w) hw s)) = _
    rw [Scheme.Hom.germ_stalkMap_apply]
    simp only [RingHom.algebraMap_toAlgebra]
    exact Y.presheaf.germ_stalkSpecializes_apply hw _ _
  rw [e y hy, e z hz]

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
/- English proof (translation)
Establish `key : z ∈ (Scheme.IdealSheafData.vanishingIdeal T).support ↔ z ∈ T`. Rewrite using `[← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal, SetLike.mem_coe]`. Rewrite using `[← key, Scheme.IdealSheafData.mem_support_iff_of_mem hz, hI, Scheme.mem_zeroLocus_iff, ← X.mem_basicOpen h z hz]`. Prove the components needed by the constructor for the conclusion. Introduce `H`.

Conclude with `H h (Ideal.mem_span_singleton_self h)`. Introduce `H f hf hzf`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hf`. Rewrite `hzf` using `[X.basicOpen_mul]`. Conclude with `H hzf.2`.
-/
private lemma mem_closed_iff_not_isUnit_germ (T : Closeds X) (U : X.affineOpens) (h : Γ(X, U))
    (hI : (Scheme.IdealSheafData.vanishingIdeal T).ideal U = Ideal.span {h}) (z : X)
    (hz : z ∈ (U : X.Opens)) :
    z ∈ T ↔ ¬ IsUnit (X.presheaf.germ U z hz h) := by
  have key : z ∈ (Scheme.IdealSheafData.vanishingIdeal T).support ↔ z ∈ T := by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal, SetLike.mem_coe]
  rw [← key, Scheme.IdealSheafData.mem_support_iff_of_mem hz, hI, Scheme.mem_zeroLocus_iff,
    ← X.mem_basicOpen h z hz]
  constructor
  · intro H
    exact H h (Ideal.mem_span_singleton_self h)
  · intro H f hf hzf
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hf
    rw [X.basicOpen_mul] at hzf
    exact H hzf.2

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
/- English proof (translation)
Simplify using `[Scheme.IdealSheafData.vanishingIdeal]`. Rewrite using `[PrimeSpectrum.mem_vanishingIdeal]`. Introduce `p hp`. Establish `hz : W.2.fromSpec p ∈ (W : X.Opens)`. Rewrite using `[← SetLike.mem_coe, ← W.2.range_fromSpec]`.

Conclude with `⟨p, rfl⟩`. Assume the negation of the conclusion as `hsp`. Establish `h1 : p ∈ PrimeSpectrum.basicOpen s` using `hsp`. Rewrite `h1` using `[← W.2.fromSpec_preimage_basicOpen]`. Conclude with `hs _ hz hp ((X.mem_basicOpen s _ hz).1 h1)`.
-/
private lemma mem_vanishingIdeal_of_not_isUnit_germ (T : Closeds X) (W : X.affineOpens)
    (s : Γ(X, W))
    (hs : ∀ (z : X) (hz : z ∈ (W : X.Opens)), z ∈ T → ¬ IsUnit (X.presheaf.germ W z hz s)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal T).ideal W := by
  simp [Scheme.IdealSheafData.vanishingIdeal]
  rw [PrimeSpectrum.mem_vanishingIdeal]
  intro p hp
  have hz : W.2.fromSpec p ∈ (W : X.Opens) := by
    rw [← SetLike.mem_coe, ← W.2.range_fromSpec]
    exact ⟨p, rfl⟩
  by_contra hsp
  have h1 : p ∈ PrimeSpectrum.basicOpen s := hsp
  rw [← W.2.fromSpec_preimage_basicOpen] at h1
  exact hs _ hz hp ((X.mem_basicOpen s _ hz).1 h1)

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
/- English proof (translation)
Take `⟨f, hfV, hxf⟩` from `U.2.exists_basicOpen_le (V := V) ⟨x, hxV⟩ hx`. Establish `hWV : ((X.affineBasicOpen f : X.affineOpens) : X.Opens) ≤ V` using `hfV`. Establish `hxW : x ∈ ((X.affineBasicOpen f : X.affineOpens) : X.Opens)` using `hxf`. Establish `hmem : X.presheaf.map (homOfLE hWV).op s ∈ (Scheme.IdealSheafData.vanishingIdeal T).ideal (X.affineBasicOpen f)`. Apply `mem_vanishingIdeal_of_not_isUnit_germ` to reduce the goal to its premises.

Introduce `z hz hzT hu`. Apply `hs z (hWV hz) hzT` to reduce the goal to its premises. Rewrite using `[← X.presheaf.germ_res_apply (homOfLE hWV) z hz s]`. Conclude with `hu`. Rewrite `hmem` using `[← Scheme.IdealSheafData.map_ideal_basicOpen, hI, Ideal.map_span, Set.image_singleton]`.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hmem`. Use `⟨X.presheaf.germ _ x hxW c, ?_⟩` and prove the remaining obligations. Rewrite using `[← X.presheaf.germ_res_apply (homOfLE hWV) x hxW s, ← hc]`. Use `(map_mul (ConcreteCategory.hom (X.presheaf.germ _ x hxW)) c _).trans ?_` and prove the remaining obligations. Use `congr 1`.

Conclude with `X.presheaf.germ_res_apply _ x hxW h`.
-/
private lemma exists_germ_eq_mul_of_not_isUnit_on_closed (T : Closeds X) (U : X.affineOpens) (h : Γ(X, U))
    (hI : (Scheme.IdealSheafData.vanishingIdeal T).ideal U = Ideal.span {h}) (x : X)
    (hx : x ∈ (U : X.Opens)) (V : X.Opens) (hxV : x ∈ V) (s : Γ(X, V))
    (hs : ∀ (z : X) (hz : z ∈ V), z ∈ T → ¬ IsUnit (X.presheaf.germ V z hz s)) :
    ∃ c, X.presheaf.germ V x hxV s = c * X.presheaf.germ U x hx h := by
  obtain ⟨f, hfV, hxf⟩ := U.2.exists_basicOpen_le (V := V) ⟨x, hxV⟩ hx
  have hWV : ((X.affineBasicOpen f : X.affineOpens) : X.Opens) ≤ V := hfV
  have hxW : x ∈ ((X.affineBasicOpen f : X.affineOpens) : X.Opens) := hxf
  have hmem : X.presheaf.map (homOfLE hWV).op s ∈
      (Scheme.IdealSheafData.vanishingIdeal T).ideal (X.affineBasicOpen f) := by
    apply mem_vanishingIdeal_of_not_isUnit_germ
    intro z hz hzT hu
    apply hs z (hWV hz) hzT
    rw [← X.presheaf.germ_res_apply (homOfLE hWV) z hz s]
    exact hu
  rw [← Scheme.IdealSheafData.map_ideal_basicOpen, hI, Ideal.map_span, Set.image_singleton] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨X.presheaf.germ _ x hxW c, ?_⟩
  rw [← X.presheaf.germ_res_apply (homOfLE hWV) x hxW s, ← hc]
  refine (map_mul (ConcreteCategory.hom (X.presheaf.germ _ x hxW)) c _).trans ?_
  congr 1
  exact X.presheaf.germ_res_apply _ x hxW h

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in
/- English proof (translation)
Take `⟨V₁, hx₁, s, rfl⟩` from `X.presheaf.germ_exist a`. Take `⟨V₂, hx₂, t, rfl⟩` from `X.presheaf.germ_exist b`. Establish `hx₂U : x ∈ V₂ ⊓ (U : X.Opens)` using `⟨hx₂, hx⟩`. Establish `key : X.presheaf.germ V₁ x hx₁ (s ^ n) = X.presheaf.germ (V₂ ⊓ (U : X.Opens)) x hx₂U (X.presheaf.map (homOfLE (inf_le_left : V₂ ⊓ (U : X.Opens) ≤ V₂)).op t * X.presheaf.map (homOfLE (inf_le_right : V₂ ⊓ (U : X.Opens) ≤ U)).op h)`. Rewrite using `[map_pow, map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, hab]`.

Take `⟨W, hxW, i₁, i₂, hW⟩` from `X.presheaf.germ_eq x hx₁ hx₂U _ _ key`. Establish `hvan : ∀ (z : X) (hz : z ∈ W), z ∈ T → ¬ IsUnit (X.presheaf.germ W z hz (X.presheaf.map i₁.op s))`. Introduce `z hz hzT hu`. Establish `hzU : z ∈ (U : X.Opens)` using `(i₂.le hz).2`. Apply `(mem_closed_iff_not_isUnit_germ T U h hI z hzU).1 hzT` to reduce the goal to its premises.

Establish `h1 : IsUnit (X.presheaf.germ W z hz (X.presheaf.map i₁.op (s ^ n)))`. Rewrite using `[map_pow, map_pow]`. Conclude with `hu.pow n`. Rewrite `h1` using `[hW, map_mul, map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]`. Conclude with `isUnit_of_mul_isUnit_right h1`.

Take `⟨c, hc⟩` from `exists_germ_eq_mul_of_not_isUnit_on_closed T U h hI x hx W hxW (X.presheaf.map i₁.op s) hvan`. Conclude with `⟨c, by rw [← hc, X.presheaf.germ_res_apply]⟩`.
-/
private lemma exists_eq_mul_of_pow_eq_mul_germ (T : Closeds X) (U : X.affineOpens) (h : Γ(X, U))
    (hI : (Scheme.IdealSheafData.vanishingIdeal T).ideal U = Ideal.span {h}) (x : X)
    (hx : x ∈ (U : X.Opens)) (a b : X.presheaf.stalk x) (n : ℕ)
    (hab : a ^ n = b * X.presheaf.germ U x hx h) :
    ∃ c, a = c * X.presheaf.germ U x hx h := by
  obtain ⟨V₁, hx₁, s, rfl⟩ := X.presheaf.germ_exist a
  obtain ⟨V₂, hx₂, t, rfl⟩ := X.presheaf.germ_exist b
  have hx₂U : x ∈ V₂ ⊓ (U : X.Opens) := ⟨hx₂, hx⟩
  have key : X.presheaf.germ V₁ x hx₁ (s ^ n) = X.presheaf.germ (V₂ ⊓ (U : X.Opens)) x hx₂U
      (X.presheaf.map (homOfLE (inf_le_left : V₂ ⊓ (U : X.Opens) ≤ V₂)).op t *
        X.presheaf.map (homOfLE (inf_le_right : V₂ ⊓ (U : X.Opens) ≤ U)).op h) := by
    rw [map_pow, map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, hab]
  obtain ⟨W, hxW, i₁, i₂, hW⟩ := X.presheaf.germ_eq x hx₁ hx₂U _ _ key
  have hvan : ∀ (z : X) (hz : z ∈ W), z ∈ T →
      ¬ IsUnit (X.presheaf.germ W z hz (X.presheaf.map i₁.op s)) := by
    intro z hz hzT hu
    have hzU : z ∈ (U : X.Opens) := (i₂.le hz).2
    apply (mem_closed_iff_not_isUnit_germ T U h hI z hzU).1 hzT
    have h1 : IsUnit (X.presheaf.germ W z hz (X.presheaf.map i₁.op (s ^ n))) := by
      rw [map_pow, map_pow]
      exact hu.pow n
    rw [hW, map_mul, map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply,
      X.presheaf.germ_res_apply, X.presheaf.germ_res_apply] at h1
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨c, hc⟩ := exists_germ_eq_mul_of_not_isUnit_on_closed T U h hI x hx W hxW
    (X.presheaf.map i₁.op s) hvan
  exact ⟨c, by rw [← hc, X.presheaf.germ_res_apply]⟩

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory in
open TopologicalSpace Opposite in
variable {X : Scheme.{0}} in

/- English proof (translation)
Introduce `X Y _ j _ T hS hη`. Establish `hS'` using `hS`. Unfold `_root_.ReciprocityTheory.AnForm.R.FinalTheorems.Snc at hS'`. Establish `hchart : ∀ y : Y, ∃ (U : X.affineOpens) (_ : j y ∈ (U : X.Opens)) (h : Γ(X, U)), (Scheme.IdealSheafData.vanishingIdeal T).ideal U = Ideal.span {h}`. Introduce `y`.

Take `⟨_, U, hU, n, f, J, _, hJ⟩` from `hS' (j y)`. Conclude with `⟨U, hU, _, hJ⟩`. Use `choose U hU h hI using hchart`. Establish `hinj : ∀ y, Function.Injective (_root_.GlobalTheory.BoundaryDivisor.pull j y)` using `fun y => (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField).comp (_root_.GlobalTheory.BoundaryDivisor.stalkMap_bijective j y).1`. Establish `hne : ∀ y, _root_.GlobalTheory.BoundaryDivisor.pull j y (X.presheaf.germ (U y) (j y) (hU y) (h y)) ≠ 0`.

Introduce `y h0`. Establish `hηU : j (genericPoint Y) ∈ (U y : X.Opens)` using `((genericPoint_spec Y).mem_open_set_iff (j ⁻¹ᵁ (U y : X.Opens)).isOpen).2 ⟨y, Set.mem_univ _, hU y⟩`. Rewrite `h0` using `[pull_germ_eq_pull_germ j _ _ y (genericPoint Y) (hU y) hηU]`. Establish `h1 : X.presheaf.germ (U y) _ hηU (h y) = 0` using `hinj _ (by rw [h0, map_zero])`. Establish `h2` using `(mem_closed_iff_not_isUnit_germ T (U y) (h y) (hI y) _ hηU).not.1 hη`.

Rewrite `h2` using `[not_not, h1]`. Conclude with `not_isUnit_zero h2`. Take `⟨g, hg⟩ : ∃ g : Y → Y.functionFieldˣ, ∀ y, (g y : Y.functionField) = _root_.GlobalTheory.BoundaryDivisor.pull j y (X.presheaf.germ (U y) (j y) (hU y) (h y))` from `⟨fun y => Units.mk0 _ (hne y), fun y => rfl⟩`. Establish `hunit : ∀ (y z : Y) (hz : j z ∈ (U y : X.Opens)), _root_.GlobalTheory.Cartier.UnitAt z ((g y : Y.functionField) / g z)`. Introduce `y z hz`.

Take `⟨c, hc⟩` from `exists_germ_eq_mul_of_not_isUnit_on_closed T (U z) (h z) (hI z) (j z) (hU z) (U y) hz (h y) (fun w hw hwT => (mem_closed_iff_not_isUnit_germ T (U y) (h y) (hI y) w hw).1 hwT)`. Take `⟨d, hd⟩` from `exists_germ_eq_mul_of_not_isUnit_on_closed T (U y) (h y) (hI y) (j z) hz (U z) (hU z) (h z) (fun w hw hwT => (mem_closed_iff_not_isUnit_germ T (U z) (h z) (hI z) w hw).1 hwT)`. Establish `gy : (g y : Y.functionField) = _root_.GlobalTheory.BoundaryDivisor.pull j z (X.presheaf.germ (U y) (j z) hz (h y))`. Rewrite using `[hg y]`. Conclude with `pull_germ_eq_pull_germ j _ _ y z (hU y) hz`.

Establish `hcz : (g y : Y.functionField) = _root_.GlobalTheory.BoundaryDivisor.pull j z c * g z`. Rewrite using `[gy, hg z, hc, map_mul]`. Establish `hdz : (g z : Y.functionField) = _root_.GlobalTheory.BoundaryDivisor.pull j z d * g y`. Rewrite using `[gy, hg z, hd, map_mul]`. Establish `hcd : _root_.GlobalTheory.BoundaryDivisor.pull j z c * _root_.GlobalTheory.BoundaryDivisor.pull j z d = 1`.

Establish `e : (_root_.GlobalTheory.BoundaryDivisor.pull j z c * _root_.GlobalTheory.BoundaryDivisor.pull j z d) * (g y : Y.functionField) = 1 * g y`. Rewrite using `[one_mul, mul_assoc, ← hdz, ← hcz]`. Conclude with `mul_right_cancel₀ (g y).ne_zero e`. Rewrite using `[hcz, mul_div_cancel_right₀ _ (g z).ne_zero]`. Unfold `_root_.GlobalTheory.Cartier.UnitAt`.

Use `⟨(j.stalkMap z).hom c, isUnit_iff_exists_inv.2 ⟨(j.stalkMap z).hom d, ?_⟩, rfl⟩` and prove the remaining obligations. Apply `IsFractionRing.injective (Y.presheaf.stalk z) Y.functionField` to reduce the goal to its premises. Rewrite using `[map_mul, map_one]`. Conclude with `hcd`. Set `F : (y : Y) → _root_.GlobalTheory.Cartier.Germ y` to `fun y => _root_.GlobalTheory.Cartier.germOf y (g y)`.

Establish `hF : F ∈ _root_.GlobalTheory.Cartier.cartierGroup Y`. Unfold `_root_.GlobalTheory.Cartier.cartierGroup`. Introduce `y`. Use `⟨j ⁻¹ᵁ (U y : X.Opens), hU y, g y, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `_root_.GlobalTheory.Cartier.germOf_eq_iff.2 (hunit y z hz)`.

Set `D : _root_.GlobalTheory.Cartier.CartierDiv Y` to `⟨F, hF⟩`. Establish `hDeq : ∀ y, D.IsEqn y (g y)` using `fun y => rfl`. Establish `hreg : ∀ y, _root_.GlobalTheory.Cartier.RegAt y (g y)`. Introduce `y`. Unfold `_root_.GlobalTheory.Cartier.RegAt`.

Conclude with `⟨_, (hg y).symm⟩`. Establish `hsupp : ∀ y, _root_.GlobalTheory.Cartier.UnitAt y (1 / (g y : Y.functionField)) ↔ IsUnit (X.presheaf.germ (U y) (j y) (hU y) (h y))`. Introduce `y`. Establish `bij` using `_root_.GlobalTheory.BoundaryDivisor.stalkMap_bijective j y`. Unfold `_root_.GlobalTheory.Cartier.UnitAt`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, -, ha⟩`. Take `⟨b, rfl⟩` from `bij.2 a`. Establish `hb : _root_.GlobalTheory.BoundaryDivisor.pull j y b = 1 / g y` using `ha`. Use `isUnit_iff_exists_inv.2 ⟨b, hinj y ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_one, hb, ← hg y, mul_one_div_cancel (g y).ne_zero]`. Introduce and unpack `⟨u, hu⟩`. Use `⟨(j.stalkMap y).hom ↑u⁻¹, u⁻¹.isUnit.map _, ?_⟩` and prove the remaining obligations. Use `show _root_.GlobalTheory.BoundaryDivisor.pull j y ↑u⁻¹ = 1 / g y`. Rewrite using `[hg y, ← hu, eq_div_iff (by rw [hu]; exact hne y), ← map_mul, Units.inv_mul, map_one]`.

Use `⟨D, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.GlobalTheory.Cartier.CartierDiv.eff_iff]`. Introduce `y g' hg'`. Establish `hu` using `((hDeq y).iff_unitAt).1 hg'`. Establish `e : (g' : Y.functionField) = ((g' : Y.functionField) / g y) * g y`.

Rewrite using `[div_mul_cancel₀ _ (g y).ne_zero]`. Rewrite using `[e]`. Conclude with `hu.regAt.mul (hreg y)`. Introduce `y show ¬ D.IsEqn y 1 ↔ j y ∈ T`. Rewrite using `[(hDeq y).iff_unitAt, Units.val_one, hsupp y, mem_closed_iff_not_isUnit_germ T (U y) (h y) (hI y) _ (hU y)]`.

Introduce `y g' hg' f n hf hfn`. Establish `hu` using `((hDeq y).iff_unitAt).1 hg'`. Establish `hr1 : _root_.GlobalTheory.Cartier.RegAt y (f ^ n / g y)`. Establish `e : f ^ n / (g y : Y.functionField) = (f ^ n / g') * ((g' : Y.functionField) / g y)`. Rewrite using `[div_mul_div_cancel₀ g'.ne_zero]`.

Rewrite using `[e]`. Conclude with `hfn.mul hu.regAt`. Establish `hr2 : _root_.GlobalTheory.Cartier.RegAt y (f / g y)`. Establish `bij` using `_root_.GlobalTheory.BoundaryDivisor.stalkMap_bijective j y`. Unfold `_root_.GlobalTheory.Cartier.RegAt at hf hr1 ⊢`.

Take `⟨a, ha⟩` from `hf`. Take `⟨b, hb⟩` from `hr1`. Take `⟨a', rfl⟩` from `bij.2 a`. Take `⟨b', rfl⟩` from `bij.2 b`. Establish `ha' : _root_.GlobalTheory.BoundaryDivisor.pull j y a' = f` using `ha`.

Establish `hb' : _root_.GlobalTheory.BoundaryDivisor.pull j y b' = f ^ n / g y` using `hb`. Establish `key : a' ^ n = b' * X.presheaf.germ (U y) (j y) (hU y) (h y)`. Apply `hinj y` to reduce the goal to its premises. Rewrite using `[map_pow, map_mul, ha', hb', ← hg y, div_mul_cancel₀ _ (g y).ne_zero]`. Take `⟨c, hc⟩` from `exists_eq_mul_of_pow_eq_mul_germ T (U y) (h y) (hI y) (j y) (hU y) a' b' n key`.

Use `⟨(j.stalkMap y).hom c, ?_⟩` and prove the remaining obligations. Use `show _root_.GlobalTheory.BoundaryDivisor.pull j y c = f / g y`. Rewrite using `[← ha', hc, map_mul, ← hg y, mul_div_cancel_right₀ _ (g y).ne_zero]`. Establish `hinv : _root_.GlobalTheory.Cartier.RegAt y ((g y : Y.functionField) / g')`. Use `((_root_.GlobalTheory.Cartier.unitAt_iff (div_ne_zero g'.ne_zero (g y).ne_zero)).1 hu).2` as an intermediate fact.

Rewrite `this` using `[inv_div]`. Then use the resulting hypothesis. Establish `e : f / (g' : Y.functionField) = f / g y * ((g y : Y.functionField) / g')`. Rewrite using `[div_mul_div_cancel₀ (g y).ne_zero]`. Rewrite using `[e]`. Conclude with `hr2.mul hinv`.
-/
theorem _root_.GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv :
    ∀ (X Y : Scheme.{0}) [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j]
      (T : TopologicalSpace.Closeds X), _root_.ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) →
      j (genericPoint Y) ∉ T → ∃ D : _root_.GlobalTheory.Cartier.CartierDiv Y, D.Eff ∧
        (∀ y, y ∈ D.supp ↔ j y ∈ T) ∧
        ∀ (y : Y) (g : Y.functionFieldˣ), D.IsEqn y g →
          ∀ (f : Y.functionField) (n : ℕ), _root_.GlobalTheory.Cartier.RegAt y f →
            _root_.GlobalTheory.Cartier.RegAt y (f ^ n / g) →
              _root_.GlobalTheory.Cartier.RegAt y (f / g) := by
  intro X Y _ j _ T hS hη
  have hS' := hS
  unfold _root_.ReciprocityTheory.AnForm.R.FinalTheorems.Snc at hS'
  have hchart : ∀ y : Y, ∃ (U : X.affineOpens) (_ : j y ∈ (U : X.Opens)) (h : Γ(X, U)),
      (Scheme.IdealSheafData.vanishingIdeal T).ideal U = Ideal.span {h} := by
    intro y
    obtain ⟨_, U, hU, n, f, J, _, hJ⟩ := hS' (j y)
    exact ⟨U, hU, _, hJ⟩
  choose U hU h hI using hchart
  have hinj : ∀ y, Function.Injective (_root_.GlobalTheory.BoundaryDivisor.pull j y) := fun y =>
    (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField).comp
      (_root_.GlobalTheory.BoundaryDivisor.stalkMap_bijective j y).1
  have hne : ∀ y, _root_.GlobalTheory.BoundaryDivisor.pull j y (X.presheaf.germ (U y) (j y) (hU y) (h y)) ≠ 0 := by
    intro y h0
    have hηU : j (genericPoint Y) ∈ (U y : X.Opens) :=
      ((genericPoint_spec Y).mem_open_set_iff (j ⁻¹ᵁ (U y : X.Opens)).isOpen).2
        ⟨y, Set.mem_univ _, hU y⟩
    rw [pull_germ_eq_pull_germ j _ _ y (genericPoint Y) (hU y) hηU] at h0
    have h1 : X.presheaf.germ (U y) _ hηU (h y) = 0 := hinj _ (by rw [h0, map_zero])
    have h2 := (mem_closed_iff_not_isUnit_germ T (U y) (h y) (hI y) _ hηU).not.1 hη
    rw [not_not, h1] at h2
    exact not_isUnit_zero h2
  obtain ⟨g, hg⟩ : ∃ g : Y → Y.functionFieldˣ, ∀ y, (g y : Y.functionField) =
      _root_.GlobalTheory.BoundaryDivisor.pull j y (X.presheaf.germ (U y) (j y) (hU y) (h y)) :=
    ⟨fun y => Units.mk0 _ (hne y), fun y => rfl⟩
  have hunit : ∀ (y z : Y) (hz : j z ∈ (U y : X.Opens)),
      _root_.GlobalTheory.Cartier.UnitAt z ((g y : Y.functionField) / g z) := by
    intro y z hz
    obtain ⟨c, hc⟩ := exists_germ_eq_mul_of_not_isUnit_on_closed T (U z) (h z) (hI z) (j z) (hU z) (U y) hz
      (h y) (fun w hw hwT => (mem_closed_iff_not_isUnit_germ T (U y) (h y) (hI y) w hw).1 hwT)
    obtain ⟨d, hd⟩ := exists_germ_eq_mul_of_not_isUnit_on_closed T (U y) (h y) (hI y) (j z) hz (U z) (hU z)
      (h z) (fun w hw hwT => (mem_closed_iff_not_isUnit_germ T (U z) (h z) (hI z) w hw).1 hwT)
    have gy : (g y : Y.functionField) =
        _root_.GlobalTheory.BoundaryDivisor.pull j z (X.presheaf.germ (U y) (j z) hz (h y)) := by
      rw [hg y]
      exact pull_germ_eq_pull_germ j _ _ y z (hU y) hz
    have hcz : (g y : Y.functionField) = _root_.GlobalTheory.BoundaryDivisor.pull j z c * g z := by
      rw [gy, hg z, hc, map_mul]
    have hdz : (g z : Y.functionField) = _root_.GlobalTheory.BoundaryDivisor.pull j z d * g y := by
      rw [gy, hg z, hd, map_mul]
    have hcd : _root_.GlobalTheory.BoundaryDivisor.pull j z c * _root_.GlobalTheory.BoundaryDivisor.pull j z d = 1 := by
      have e : (_root_.GlobalTheory.BoundaryDivisor.pull j z c * _root_.GlobalTheory.BoundaryDivisor.pull j z d) *
          (g y : Y.functionField) = 1 * g y := by
        rw [one_mul, mul_assoc, ← hdz, ← hcz]
      exact mul_right_cancel₀ (g y).ne_zero e
    rw [hcz, mul_div_cancel_right₀ _ (g z).ne_zero]
    unfold _root_.GlobalTheory.Cartier.UnitAt
    refine ⟨(j.stalkMap z).hom c, isUnit_iff_exists_inv.2 ⟨(j.stalkMap z).hom d, ?_⟩, rfl⟩
    apply IsFractionRing.injective (Y.presheaf.stalk z) Y.functionField
    rw [map_mul, map_one]
    exact hcd
  let F : (y : Y) → _root_.GlobalTheory.Cartier.Germ y := fun y => _root_.GlobalTheory.Cartier.germOf y (g y)
  have hF : F ∈ _root_.GlobalTheory.Cartier.cartierGroup Y := by
    unfold _root_.GlobalTheory.Cartier.cartierGroup
    intro y
    refine ⟨j ⁻¹ᵁ (U y : X.Opens), hU y, g y, fun z hz => ?_⟩
    exact _root_.GlobalTheory.Cartier.germOf_eq_iff.2 (hunit y z hz)
  let D : _root_.GlobalTheory.Cartier.CartierDiv Y := ⟨F, hF⟩
  have hDeq : ∀ y, D.IsEqn y (g y) := fun y => rfl
  have hreg : ∀ y, _root_.GlobalTheory.Cartier.RegAt y (g y) := by
    intro y
    unfold _root_.GlobalTheory.Cartier.RegAt
    exact ⟨_, (hg y).symm⟩
  have hsupp : ∀ y, _root_.GlobalTheory.Cartier.UnitAt y (1 / (g y : Y.functionField)) ↔
      IsUnit (X.presheaf.germ (U y) (j y) (hU y) (h y)) := by
    intro y
    have bij := _root_.GlobalTheory.BoundaryDivisor.stalkMap_bijective j y
    unfold _root_.GlobalTheory.Cartier.UnitAt
    constructor
    · rintro ⟨a, -, ha⟩
      obtain ⟨b, rfl⟩ := bij.2 a
      have hb : _root_.GlobalTheory.BoundaryDivisor.pull j y b = 1 / g y := ha
      refine isUnit_iff_exists_inv.2 ⟨b, hinj y ?_⟩
      rw [map_mul, map_one, hb, ← hg y, mul_one_div_cancel (g y).ne_zero]
    · rintro ⟨u, hu⟩
      refine ⟨(j.stalkMap y).hom ↑u⁻¹, u⁻¹.isUnit.map _, ?_⟩
      show _root_.GlobalTheory.BoundaryDivisor.pull j y ↑u⁻¹ = 1 / g y
      rw [hg y, ← hu, eq_div_iff (by rw [hu]; exact hne y), ← map_mul, Units.inv_mul, map_one]
  refine ⟨D, ?_, ?_, ?_⟩
  · rw [_root_.GlobalTheory.Cartier.CartierDiv.eff_iff]
    intro y g' hg'
    have hu := ((hDeq y).iff_unitAt).1 hg'
    have e : (g' : Y.functionField) = ((g' : Y.functionField) / g y) * g y := by
      rw [div_mul_cancel₀ _ (g y).ne_zero]
    rw [e]
    exact hu.regAt.mul (hreg y)
  · intro y
    show ¬ D.IsEqn y 1 ↔ j y ∈ T
    rw [(hDeq y).iff_unitAt, Units.val_one, hsupp y,
      mem_closed_iff_not_isUnit_germ T (U y) (h y) (hI y) _ (hU y)]
  · intro y g' hg' f n hf hfn
    have hu := ((hDeq y).iff_unitAt).1 hg'
    have hr1 : _root_.GlobalTheory.Cartier.RegAt y (f ^ n / g y) := by
      have e : f ^ n / (g y : Y.functionField) =
          (f ^ n / g') * ((g' : Y.functionField) / g y) := by
        rw [div_mul_div_cancel₀ g'.ne_zero]
      rw [e]
      exact hfn.mul hu.regAt
    have hr2 : _root_.GlobalTheory.Cartier.RegAt y (f / g y) := by
      have bij := _root_.GlobalTheory.BoundaryDivisor.stalkMap_bijective j y
      unfold _root_.GlobalTheory.Cartier.RegAt at hf hr1 ⊢
      obtain ⟨a, ha⟩ := hf
      obtain ⟨b, hb⟩ := hr1
      obtain ⟨a', rfl⟩ := bij.2 a
      obtain ⟨b', rfl⟩ := bij.2 b
      have ha' : _root_.GlobalTheory.BoundaryDivisor.pull j y a' = f := ha
      have hb' : _root_.GlobalTheory.BoundaryDivisor.pull j y b' = f ^ n / g y := hb
      have key : a' ^ n = b' * X.presheaf.germ (U y) (j y) (hU y) (h y) := by
        apply hinj y
        rw [map_pow, map_mul, ha', hb', ← hg y, div_mul_cancel₀ _ (g y).ne_zero]
      obtain ⟨c, hc⟩ := exists_eq_mul_of_pow_eq_mul_germ T (U y) (h y) (hI y) (j y) (hU y) a' b' n key
      refine ⟨(j.stalkMap y).hom c, ?_⟩
      show _root_.GlobalTheory.BoundaryDivisor.pull j y c = f / g y
      rw [← ha', hc, map_mul, ← hg y, mul_div_cancel_right₀ _ (g y).ne_zero]
    have hinv : _root_.GlobalTheory.Cartier.RegAt y ((g y : Y.functionField) / g') := by
      have := ((_root_.GlobalTheory.Cartier.unitAt_iff
        (div_ne_zero g'.ne_zero (g y).ne_zero)).1 hu).2
      rwa [inv_div] at this
    have e : f / (g' : Y.functionField) = f / g y * ((g y : Y.functionField) / g') := by
      rw [div_mul_div_cancel₀ (g y).ne_zero]
    rw [e]
    exact hr2.mul hinv

end GlobalTheory.BoundaryDivisor

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductAffineOpenClosureLegsEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecAppLETopEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSBaseChangeLocal

/- English proof (translation)
Introduce `x _`. Establish `hs : x ⤳ IsLocalRing.closedPoint S` using `(PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)`. Conclude with `(hs.map g₀.base.hom.continuous).mem_open V.isOpen hV`.
-/
theorem top_le_of_mem {S : Type} [CommRing S] [IsLocalRing S] {Y : Scheme.{0}} (g₀ : Sp S ⟶ Y) (V : Y.Opens)
    (hV : g₀.base (IsLocalRing.closedPoint S) ∈ V) : ⊤ ≤ g₀ ⁻¹ᵁ V := by
  intro x _
  have hs : x ⤳ IsLocalRing.closedPoint S :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)
  exact (hs.map g₀.base.hom.continuous).mem_open V.isOpen hV

/- English proof (translation)
Simplify using `only [valR, dif_pos h, map_one]`.
-/
theorem valR_one_of_le {A : Type} [CommRing A] {Y : Scheme.{0}} (x : Sp A ⟶ Y) (O : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) : valR x O 1 = 1 := by
  simp only [valR, dif_pos h, map_one]

/- English proof (translation)
Introduce `Z Z' X X' p p' φ g hpb U U' hU'U W₀ hW₀ O hO S _ _ g₀ hg₀ Δ hadd hmul hres hφ hp' f`. Use `set m := IsLocalRing.closedPoint S`. Establish `hz : g₀.base m ∈ O` using `hg₀ (Set.mem_univ m)`. Establish `hzW : φ.base (g₀.base m) ∈ W₀` using `(hO hz).1`. Take `⟨O₀, hO₀a, hzO₀, hO₀W⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens) hzW`.

Take `⟨hA, hcl⟩` from `GlobalTheory.T.fibreProduct_affineOpen_closure_legs_eq_top Z Z' X X' p p' φ g hpb U U' hU'U ⟨O₀, hO₀a⟩ (hO₀W.trans hW₀)`. Use `set A := φ ⁻¹ᵁ O₀ ⊓ p' ⁻¹ᵁ U'.1 with hAdef`. Establish `hzA : g₀.base m ∈ A` using `⟨hzO₀, (hO hz).2⟩`. Take `⟨h, hhle, hzD⟩` from `hA.exists_basicOpen_le (V := A ⊓ O) ⟨g₀.base m, hzA, hz⟩ hzA`. Use `set D := Z'.basicOpen h`.

Establish `hDA : D ≤ A` using `hhle.trans inf_le_left`. Establish `hDO : D ≤ O` using `hhle.trans inf_le_right`. Establish `htop : ⊤ ≤ g₀ ⁻¹ᵁ D` using `top_le_of_mem g₀ D hzD`. Set `δ : Γ(Z', D) →+ S` to `AddMonoidHom.mk' (Δ D) (hadd D hDO htop)`. Establish `hδ : ∀ a, δ a = Δ D a` using `fun _ => rfl`.

Establish `h1 : Δ D 1 = 0`. Establish `e` using `hmul D hDO htop 1 1`. Rewrite `e` using `[_root_.mul_one, valR_one_of_le g₀ D htop, _root_.one_mul]`. Establish `: Δ D 1 + Δ D 1 - Δ D 1 = Δ D 1 - Δ D 1` using `by rw [← e]`. Simplify using `using this`.

Establish `hgen : ∀ a : Γ(Z', A), Δ D (resG Z' hDA a) = 0`. Introduce `a`. Establish `ha : a ∈ Subring.closure (Set.range (φ.appLE O₀ A inf_le_left).hom ∪ Set.range (p'.appLE U'.1 A inf_le_right).hom)` using `by rw [hcl]; trivial`. Proceed by induction on `ha using Subring.closure_induction with`. Consider the case `mem x hx`.

Break down `hx with ⟨f₀, rfl⟩ | ⟨r, rfl⟩` into its components or cases. Rewrite using `[GlobalTheory.CechKSSmul.resG_appLE']`. Conclude with `hφ O₀ D _ hO₀W hDO htop f₀`. Rewrite using `[GlobalTheory.CechKSSmul.resG_appLE']`. Conclude with `hp' D _ hDO htop r`.

Consider the case `zero => rw [map_zero, ← hδ, map_zero]`. Consider the case `one => rw [map_one, h1]`. Consider the case `add x y _ _ hx hy => rw [map_add, hadd D hDO htop, hx, hy, add_zero]`. Consider the case `neg x _ hx => rw [map_neg, ← hδ, map_neg, hδ, hx, neg_zero]`. Consider the case `mul x y _ _ hx hy => rw [map_mul, hmul D hDO htop, hx, hy, mul_zero, mul_zero, add_zero]`.

Establish `hall : ∀ b : Γ(Z', D), Δ D b = 0`. Introduce `b`. Take `⟨u, r, hu, hb⟩` from `GlobalTheory.LogKSLoc.exists_frac ⟨A, hA⟩ ⟨D, hA.basicOpen h⟩ hDA h rfl b`. Establish `e` using `hmul D hDO htop b (resG Z' hDA u)`. Establish `e2 : Δ D (b * resG Z' hDA u) = 0`.

Establish `: b * resG Z' hDA u = resG Z' hDA r` using `hb`. Rewrite using `[this, hgen]`. Rewrite `e` using `[e2, hgen, mul_zero, zero_add]`. Establish `hunit : IsUnit (valR g₀ D (resG Z' hDA u))`. Take `⟨w, hw⟩` from `hu`.

Use `IsUnit.of_mul_eq_one (valR g₀ D (w⁻¹ : (Γ(Z', D))ˣ)) ?_` and prove the remaining obligations. Rewrite using `[← hw, ← GlobalTheory.CechKSSmul.valR_mul_of_le g₀ D htop, Units.mul_inv, valR_one_of_le g₀ D htop]`. Conclude with `(hunit.mul_right_eq_zero).mp e.symm`. Rewrite using `[← hres O D hDO le_rfl htop f]`. Conclude with `hall _`.
-/
theorem eq_zero_of_kills_both : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens), U'.1 ≤ g ⁻¹ᵁ U.1 → ∀ (W₀ : Z.Opens), W₀ ≤ p ⁻¹ᵁ U.1 → ∀ (O : Z'.Opens), O ≤ φ ⁻¹ᵁ W₀ ⊓ p' ⁻¹ᵁ U'.1 → ∀ (S : Type) [CommRing S] [IsLocalRing S] (g₀ : Sp S ⟶ Z'), ⊤ ≤ g₀ ⁻¹ᵁ O → ∀ (Δ : ∀ O' : Z'.Opens, Γ(Z', O') → S), (∀ O' : Z'.Opens, O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f f', Δ O' (f + f') = Δ O' f + Δ O' f') → (∀ O' : Z'.Opens, O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f f', Δ O' (f * f') = valR g₀ O' f * Δ O' f' + valR g₀ O' f' * Δ O' f) → (∀ (O₁ O₂ : Z'.Opens) (h : O₂ ≤ O₁), O₁ ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O₂ → ∀ f, Δ O₂ (resG Z' h f) = Δ O₁ f) → (∀ (O₀ : Z.Opens) (O' : Z'.Opens) (h : O' ≤ φ ⁻¹ᵁ O₀), O₀ ≤ W₀ → O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f₀, Δ O' ((φ.appLE O₀ O' h).hom f₀) = 0) → (∀ (O' : Z'.Opens) (h : O' ≤ p' ⁻¹ᵁ U'.1), O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ r, Δ O' ((p'.appLE U'.1 O' h).hom r) = 0) → ∀ f, Δ O f = 0 := by
  intro Z Z' X X' p p' φ g hpb U U' hU'U W₀ hW₀ O hO S _ _ g₀ hg₀ Δ hadd hmul hres hφ hp' f
  set m := IsLocalRing.closedPoint S
  have hz : g₀.base m ∈ O := hg₀ (Set.mem_univ m)
  have hzW : φ.base (g₀.base m) ∈ W₀ := (hO hz).1
  obtain ⟨O₀, hO₀a, hzO₀, hO₀W⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens) hzW
  obtain ⟨hA, hcl⟩ := GlobalTheory.T.fibreProduct_affineOpen_closure_legs_eq_top Z Z' X X' p p' φ g hpb U U' hU'U ⟨O₀, hO₀a⟩ (hO₀W.trans hW₀)
  set A := φ ⁻¹ᵁ O₀ ⊓ p' ⁻¹ᵁ U'.1 with hAdef
  have hzA : g₀.base m ∈ A := ⟨hzO₀, (hO hz).2⟩
  obtain ⟨h, hhle, hzD⟩ := hA.exists_basicOpen_le (V := A ⊓ O) ⟨g₀.base m, hzA, hz⟩ hzA
  set D := Z'.basicOpen h
  have hDA : D ≤ A := hhle.trans inf_le_left
  have hDO : D ≤ O := hhle.trans inf_le_right
  have htop : ⊤ ≤ g₀ ⁻¹ᵁ D := top_le_of_mem g₀ D hzD
  let δ : Γ(Z', D) →+ S := AddMonoidHom.mk' (Δ D) (hadd D hDO htop)
  have hδ : ∀ a, δ a = Δ D a := fun _ => rfl
  have h1 : Δ D 1 = 0 := by
    have e := hmul D hDO htop 1 1
    rw [_root_.mul_one, valR_one_of_le g₀ D htop, _root_.one_mul] at e
    have : Δ D 1 + Δ D 1 - Δ D 1 = Δ D 1 - Δ D 1 := by rw [← e]
    simpa using this
  have hgen : ∀ a : Γ(Z', A), Δ D (resG Z' hDA a) = 0 := by
    intro a
    have ha : a ∈ Subring.closure (Set.range (φ.appLE O₀ A inf_le_left).hom ∪
        Set.range (p'.appLE U'.1 A inf_le_right).hom) := by rw [hcl]; trivial
    induction ha using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨f₀, rfl⟩ | ⟨r, rfl⟩
      · rw [GlobalTheory.CechKSSmul.resG_appLE']
        exact hφ O₀ D _ hO₀W hDO htop f₀
      · rw [GlobalTheory.CechKSSmul.resG_appLE']
        exact hp' D _ hDO htop r
    | zero => rw [map_zero, ← hδ, map_zero]
    | one => rw [map_one, h1]
    | add x y _ _ hx hy => rw [map_add, hadd D hDO htop, hx, hy, add_zero]
    | neg x _ hx => rw [map_neg, ← hδ, map_neg, hδ, hx, neg_zero]
    | mul x y _ _ hx hy => rw [map_mul, hmul D hDO htop, hx, hy, mul_zero, mul_zero, add_zero]
  have hall : ∀ b : Γ(Z', D), Δ D b = 0 := by
    intro b
    obtain ⟨u, r, hu, hb⟩ := GlobalTheory.LogKSLoc.exists_frac ⟨A, hA⟩ ⟨D, hA.basicOpen h⟩ hDA h rfl b
    have e := hmul D hDO htop b (resG Z' hDA u)
    have e2 : Δ D (b * resG Z' hDA u) = 0 := by
      have : b * resG Z' hDA u = resG Z' hDA r := hb
      rw [this, hgen]
    rw [e2, hgen, mul_zero, zero_add] at e
    have hunit : IsUnit (valR g₀ D (resG Z' hDA u)) := by
      obtain ⟨w, hw⟩ := hu
      refine IsUnit.of_mul_eq_one (valR g₀ D (w⁻¹ : (Γ(Z', D))ˣ)) ?_
      rw [← hw, ← GlobalTheory.CechKSSmul.valR_mul_of_le g₀ D htop, Units.mul_inv, valR_one_of_le g₀ D htop]
    exact (hunit.mul_right_eq_zero).mp e.symm
  rw [← hres O D hDO le_rfl htop f]
  exact hall _

end GlobalTheory.KSBaseChangeLocal

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantValuationLeCommonBoundMulMonomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantNeZeroUniformisedMemberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteValuationCentredCompleteNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.DivInt

variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

/- English proof (translation)
Use `haveI := 𝔪.cn.2.2.2`. Take `⟨u, hu⟩` from `𝔪.psi mu`. Take `⟨r, hr, -, hm, -⟩` from `(PsiCoordLocal.main V 𝔪.D 𝔪.cn.2.1 (𝔪.e₈ mu)).1`. Take `⟨v, hv⟩` from `PsiCoordLocal.exists_unit_of_coord hr hu`. Establish `: (u : V) * t mu ∈ maximalIdeal V` using `hv ▸ Ideal.mul_mem_left _ _ (hm (𝔪.e₈.map_ne_zero_iff.2 h))`.

Conclude with `(Ideal.unit_mul_mem_iff_mem _ u.isUnit).1 this`.
-/
theorem t_mem (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {mu : X} (h : mu ≠ 0) : t mu ∈ maximalIdeal V := by
  haveI := 𝔪.cn.2.2.2
  obtain ⟨u, hu⟩ := 𝔪.psi mu
  obtain ⟨r, hr, -, hm, -⟩ := (PsiCoordLocal.main V 𝔪.D 𝔪.cn.2.1 (𝔪.e₈ mu)).1
  obtain ⟨v, hv⟩ := PsiCoordLocal.exists_unit_of_coord hr hu
  have : (u : V) * t mu ∈ maximalIdeal V := hv ▸ Ideal.mul_mem_left _ _ (hm (𝔪.e₈.map_ne_zero_iff.2 h))
  exact (Ideal.unit_mul_mem_iff_mem _ u.isUnit).1 this

/- English proof (translation)
Establish `sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁` using `fun w => by`. Establish `: X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁)` using `⟨w, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Use `set yC : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyC`. Establish `hC : yC (closedPoint V) ⤳ z₁` using `sp _`.

Use `set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy`. Use `set ξ := y (closedPoint (FractionRing V)) with hξ`. Establish `hyξ : ∀ w, y w ⤳ ξ` using `RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)`. Establish `hξz : ξ ⤳ z₁` using `sp _`. Establish `hr : X₁.S.th b / X₁.S.th a ∈ X₁.M.O z₁` using `ha.2 b`.

Establish `hrξ : X₁.S.th b / X₁.S.th a ∈ X₁.M.O ξ` using `RatModel.O_le_of_specializes hξz hr`. Establish `haξ : X₁.S.th a ∈ X₁.M.O ξ` using `𝔪.reg _ (X₁.S.th_mem a)`. Use `⟨RatModel.valLoc yC z₁ hC ⟨_, hr⟩, ?_⟩` and prove the remaining obligations. Establish `e1 : X₁.S.th b = X₁.S.th b / X₁.S.th a * X₁.S.th a` using `(div_mul_cancel₀ _ ha.1).symm`. Establish `e2 : X₁.M.val y (X₁.S.th b / X₁.S.th a) = algebraMap V (FractionRing V) (RatModel.valLoc yC z₁ hC ⟨_, hr⟩)` using `RatModel.val_spMap_comp (algebraMap V (FractionRing V)) yC hC ⟨_, hr⟩`.

Rewrite using `[𝔪.yK_eq, 𝔪.yK_eq]`. Use `show X₁.M.val y (X₁.S.th b) = _ * X₁.M.val y (X₁.S.th a)`. Rewrite using `[← e2, ← RatModel.val_mul hyξ hrξ haξ, ← e1]`.
-/
theorem ratio (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {a : X₁.S.Gam} (ha : X₁.M.Div X₁.S.th a z₁) (b : X₁.S.Gam) :
    ∃ v : V, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ = algebraMap V (FractionRing V) v * 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ := by
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set yC : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyC
  have hC : yC (closedPoint V) ⤳ z₁ := sp _
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hξz : ξ ⤳ z₁ := sp _
  have hr : X₁.S.th b / X₁.S.th a ∈ X₁.M.O z₁ := ha.2 b
  have hrξ : X₁.S.th b / X₁.S.th a ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz hr
  have haξ : X₁.S.th a ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem a)
  refine ⟨RatModel.valLoc yC z₁ hC ⟨_, hr⟩, ?_⟩
  have e1 : X₁.S.th b = X₁.S.th b / X₁.S.th a * X₁.S.th a := (div_mul_cancel₀ _ ha.1).symm
  have e2 : X₁.M.val y (X₁.S.th b / X₁.S.th a) = algebraMap V (FractionRing V) (RatModel.valLoc yC z₁ hC ⟨_, hr⟩) :=
    RatModel.val_spMap_comp (algebraMap V (FractionRing V)) yC hC ⟨_, hr⟩
  rw [𝔪.yK_eq, 𝔪.yK_eq]
  show X₁.M.val y (X₁.S.th b) = _ * X₁.M.val y (X₁.S.th a)
  rw [← e2, ← RatModel.val_mul hyξ hrξ haξ, ← e1]

/- English proof (translation)
Introduce `I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 a ha`. Establish `ha' : X₁.M.Div X₁.S.th a z₁` using `ha`. Take `⟨b₀, hb₀⟩` from `GlobalTheory.T.exists_thetaConstant_ne_zero_uniformisedMember I X₁ z₁ act V ev X t δ 𝔪`. Establish `hane : 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ≠ 0`. Introduce `h0`.

Take `⟨v, hv⟩` from `ratio 𝔪 ha' b₀`. Rewrite `hv` using `[h0, mul_zero]`. Conclude with `hb₀ hv`. Take `⟨ν, hν1, hνm⟩` from `GlobalTheory.T.exists_discreteValuation_centred_completeNormal V 𝔪.cn`. Establish `hmax : ∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)` using `fun b => by`.

Take `⟨v, hv⟩` from `ratio 𝔪 ha' b`. Rewrite using `[hv, map_mul]`. Conclude with `mul_le_of_le_one_left' (hν1 v)`. Take `⟨w, hw, hle⟩` from `GlobalTheory.T.thetaConstant_valuation_le_common_bound_mul_monomial I X₁ z₁ act V ev X t δ 𝔪 ν hν1 hνm _ hmax a`. Establish `h0 : ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≠ 0` using `pow_ne_zero _ ((Valuation.ne_zero_iff ν).2 hane)`.

Establish `h1 : 1 ≤ ν (algebraMap V (FractionRing V) (t w))`. Use `mul_le_mul_of_nonneg_left hle (zero_le' : (0 : WithZero (Multiplicative ℤ)) ≤ (ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2))⁻¹)` as an intermediate fact. Rewrite `this` using `[← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul]`. Then use the resulting hypothesis. Distinguish the cases in `hw0 : w = 0`. Conclude with `hw0 ▸ hw`.

Conclude with `absurd h1 (not_le.2 (hνm _ (t_mem 𝔪 hw0)))`.
-/
theorem label_zero_of_mem_supI : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → 𝔪.YY a 0 := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 a ha
  have ha' : X₁.M.Div X₁.S.th a z₁ := ha
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.exists_thetaConstant_ne_zero_uniformisedMember I X₁ z₁ act V ev X t δ 𝔪
  have hane : 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := ratio 𝔪 ha' b₀
    rw [h0, mul_zero] at hv
    exact hb₀ hv
  obtain ⟨ν, hν1, hνm⟩ := GlobalTheory.T.exists_discreteValuation_centred_completeNormal V 𝔪.cn
  have hmax : ∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) := fun b => by
    obtain ⟨v, hv⟩ := ratio 𝔪 ha' b
    rw [hv, map_mul]
    exact mul_le_of_le_one_left' (hν1 v)
  obtain ⟨w, hw, hle⟩ := GlobalTheory.T.thetaConstant_valuation_le_common_bound_mul_monomial I X₁ z₁ act V ev X t δ 𝔪 ν hν1 hνm _ hmax a
  have h0 : ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≠ 0 :=
    pow_ne_zero _ ((Valuation.ne_zero_iff ν).2 hane)
  have h1 : 1 ≤ ν (algebraMap V (FractionRing V) (t w)) := by
    have := mul_le_mul_of_nonneg_left hle
      (zero_le' : (0 : WithZero (Multiplicative ℤ)) ≤ (ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2))⁻¹)
    rwa [← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul] at this
  by_cases hw0 : w = 0
  · exact hw0 ▸ hw
  · exact absurd h1 (not_le.2 (hνm _ (t_mem 𝔪 hw0)))

end GlobalTheory.GSep.DivInt

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemClassSumsValuesOfFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSumsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.GSep.ExactSums

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw⟩ v`. Conclude with `⟨w v, by rw [hw]; rfl⟩`. Introduce `h choose w hw using h`. Conclude with `⟨w, funext fun v => by rw [hw v]; rfl⟩`.
-/
theorem congMod_pi_iff {X : Type} [AddCommGroup X] {s : ℕ} (N : ℕ) (a b : Fin s → X) :
    CongMod N a b ↔ ∀ v, CongMod N (a v) (b v) := by
  constructor
  · rintro ⟨w, hw⟩ v
    exact ⟨w v, by rw [hw]; rfl⟩
  · intro h
    choose w hw using h
    exact ⟨w, funext fun v => by rw [hw v]; rfl⟩

/- English proof (translation)
Take `⟨l, hl⟩ : ∃ l : X → S.Gam, ∀ mu, YY (l mu) mu` from `⟨fun mu => (h2 mu).choose, fun mu => (h2 mu).choose_spec⟩`. Establish `sub : ∀ a a' mu, YY a mu → YY a' mu → a - a' ∈ H`. Introduce `a a' mu ha ha'`. Take `⟨b, hb⟩` from `h2 (-mu)`. Establish `e1` using `h4 _ _ _ _ ha hb`.

Establish `e2` using `h4 _ _ _ _ ha' hb`. Rewrite `e1`, `e2` using `[add_neg_cancel]`. Use `H.sub_mem ((hH _).2 e1) ((hH _).2 e2)` as an intermediate fact. Simplify using `using this`. Establish `D1 : ∀ τ ∈ S.perp H, ∀ a mu, YY a mu → eStd S.g _ τ a = eStd S.g _ τ (l mu)`.

Introduce `τ hτ a mu ha`. Establish `h0 : eStd S.g _ τ (a - l mu) = 0` using `hτ _ (sub a (l mu) mu ha (hl mu))`. Establish `e : a = (a - l mu) + l mu` using `(sub_add_cancel a (l mu)).symm`. Use `conv_lhs => rw [e]`. Rewrite using `[eStd_add_right, h0, zero_add]`.

Use `⟨l, hl, D1, fun mu κ => ⟨fun h => ?_, fun h τ hτ => ?_⟩⟩` and prove the remaining obligations. Establish `hb : l mu - l κ ∈ H`. Rewrite using `[← TestBasis.perp_perp S H]`. Introduce `τ hτ`. Establish `e : eStd S.g _ τ (l mu) = eStd S.g _ τ (l mu - l κ) + eStd S.g _ τ (l κ)`.

Rewrite using `[← eStd_add_right, sub_add_cancel]`. Establish `h0 : eStd S.g _ τ (l mu - l κ) = 0` using `by rw [h τ hτ] at e; simpa using e.symm`. Rewrite using `[eStd_swap, h0, neg_zero]`. Establish `e1` using `h4 _ _ _ _ (hl κ) ((hH _).1 hb)`. Rewrite `e1` using `[add_sub_cancel, add_zero]`.

Take `⟨w, hw⟩` from `(h3 _ _ _ (hl mu)).1 e1`. Conclude with `⟨-w, by rw [hw, smul_neg, add_neg_cancel_right]⟩`. Conclude with `(D1 τ hτ (l κ) mu ((h3 _ _ _ (hl κ)).2 h)).symm`.
-/
theorem labels {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (H : AddSubgroup S.Gam)
    {X : Type} [AddCommGroup X] (YY : S.Gam → X → Prop)
    (h1 : ∀ a, ∃ mu, YY a mu) (h2 : ∀ mu, ∃ a, YY a mu)
    (h3 : ∀ a mu mu', YY a mu → (YY a mu' ↔ CongMod (S.r * S.N) mu' mu))
    (h4 : ∀ a a' mu mu', YY a mu → YY a' mu' → YY (a + a') (mu + mu'))
    (hH : ∀ a, a ∈ H ↔ YY a 0) :
    ∃ l : X → S.Gam, (∀ mu, YY (l mu) mu) ∧
      (∀ τ ∈ S.perp H, ∀ a mu, YY a mu → eStd S.g _ τ a = eStd S.g _ τ (l mu)) ∧
      ∀ mu κ, (∀ τ ∈ S.perp H, eStd S.g _ τ (l mu) = eStd S.g _ τ (l κ)) ↔ CongMod (S.r * S.N) mu κ := by
  obtain ⟨l, hl⟩ : ∃ l : X → S.Gam, ∀ mu, YY (l mu) mu := ⟨fun mu => (h2 mu).choose, fun mu => (h2 mu).choose_spec⟩
  have sub : ∀ a a' mu, YY a mu → YY a' mu → a - a' ∈ H := by
    intro a a' mu ha ha'
    obtain ⟨b, hb⟩ := h2 (-mu)
    have e1 := h4 _ _ _ _ ha hb
    have e2 := h4 _ _ _ _ ha' hb
    rw [add_neg_cancel] at e1 e2
    have := H.sub_mem ((hH _).2 e1) ((hH _).2 e2)
    simpa using this
  have D1 : ∀ τ ∈ S.perp H, ∀ a mu, YY a mu → eStd S.g _ τ a = eStd S.g _ τ (l mu) := by
    intro τ hτ a mu ha
    have h0 : eStd S.g _ τ (a - l mu) = 0 := hτ _ (sub a (l mu) mu ha (hl mu))
    have e : a = (a - l mu) + l mu := (sub_add_cancel a (l mu)).symm
    conv_lhs => rw [e]
    rw [eStd_add_right, h0, zero_add]
  refine ⟨l, hl, D1, fun mu κ => ⟨fun h => ?_, fun h τ hτ => ?_⟩⟩
  · have hb : l mu - l κ ∈ H := by
      rw [← TestBasis.perp_perp S H]
      intro τ hτ
      have e : eStd S.g _ τ (l mu) = eStd S.g _ τ (l mu - l κ) + eStd S.g _ τ (l κ) := by
        rw [← eStd_add_right, sub_add_cancel]
      have h0 : eStd S.g _ τ (l mu - l κ) = 0 := by rw [h τ hτ] at e; simpa using e.symm
      rw [eStd_swap, h0, neg_zero]
    have e1 := h4 _ _ _ _ (hl κ) ((hH _).1 hb)
    rw [add_sub_cancel, add_zero] at e1
    obtain ⟨w, hw⟩ := (h3 _ _ _ (hl mu)).1 e1
    exact ⟨-w, by rw [hw, smul_neg, add_neg_cancel_right]⟩
  · exact (D1 τ hτ (l κ) mu ((h3 _ _ _ (hl κ)).2 h)).symm

open Classical GlobalTheory.Poinc.Sep.ExactSums in

/- English proof (translation)
Introduce `O _ bar q s W X₁ z₁ act x₀ Φ lab hG`. Take `⟨hdiv, hlab, hmem⟩` from `hG`. Take `⟨sg, eps, hlink⟩` from `GlobalTheory.T.thetaConstants_translate_eq_twisted_sums O X₁ z₁ act x₀ hdiv`. Introduce `y κ c`. Take `⟨𝔪, hT⟩` from `hmem y`.

Use `haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)⟩`. Use `haveI : IsDomain X₁.o₁ := X₁.ar.ded.toIsDomain`. Take `⟨yy1, yy2, yy3, yy4⟩` from `GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level O X₁ z₁ act (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪`. Establish `hH` using `GlobalTheory.T.mem_dividingLabels_iff_class_zero O X₁ z₁ act x₀ hdiv (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪`. Take `⟨l, -, hlY, hlC⟩` from `labels X₁.S (X₁.S.HH X₁.M z₁) 𝔪.YY yy1 yy2 yy3 yy4 hH`.

Set `φ : X₁.o₁ →+* X₁.M.Z.presheaf.stalk z₁` to `(X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))`. Establish `hsh : ∀ b : X₁.M.O z₁, X₁.M.stalkHom z₁ ((X₁.M.stalkEquiv z₁).symm b) = b` using `fun b => by`. Rewrite using `[← RatModel.coe_stalkEquiv (M := X₁.M), RingEquiv.apply_symm_apply]`. Establish `hφ : ∀ a, X₁.M.stalkHom z₁ (φ a) = algebraMap X₁.o₁ X₁.Ω₁ a` using `fun a => hsh _`. Set `zt` to `φ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))`.

Establish `hzt : X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))` using `hφ _`. Establish `hunitV : IsUnit (((X₁.S.r * X₁.S.N : ℕ) : Φ.V y))`. Use `X₁.S.unit.map ((Φ.ev y).comp φ)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hω : IsPrimitiveRoot (Φ.ev y zt) (X₁.S.r * X₁.S.N)`.

Establish `h0 : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N)` using `X₁.S.prim.pow (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) 2) (sq _)`. Conclude with `isPrimitiveRoot_map' ((Φ.ev y).comp φ) hunitV.ne_zero h0`. Set `TT` to `X₁.S.TT X₁.M z₁`. Establish `hmemO : ∀ τ : TT, algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ ∈ X₁.M.O z₁` using `fun τ => by rw [mul_div_assoc]; exact mul_mem (Subalgebra.algebraMap_mem _ _) (hdiv.2 _)`. Set `hτ : TT → X₁.M.Z.presheaf.stalk z₁` to `fun τ => (X₁.M.stalkEquiv z₁).symm ⟨_, hmemO τ⟩`.

Establish `hhτ : ∀ τ : TT, X₁.M.stalkHom z₁ (hτ τ) = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀` using `fun τ => hsh _`. Establish `hcard : IsUnit ((Fintype.card TT : ℕ) : X₁.o₁)`. Establish `h1 : Fintype.card TT ∣ Fintype.card X₁.S.Gam`. Rewrite using `[← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]`. Conclude with `AddSubgroup.card_addSubgroup_dvd_card _`.

Establish `h2 : IsUnit ((Fintype.card X₁.S.Gam : ℕ) : X₁.o₁)`. Rewrite using `[Fintype.card_fun, ZMod.card, Nat.cast_pow]`. Conclude with `X₁.S.unit.pow _`. Conclude with `isUnit_of_dvd_unit (Nat.cast_dvd_cast h1) h2`. Take `⟨u, hu⟩` from `hcard.map φ`.

Set `d` to `((u⁻¹ : (X₁.M.Z.presheaf.stalk z₁)ˣ) : X₁.M.Z.presheaf.stalk z₁)`. Establish `hd : Φ.ev y d * (Fintype.card TT : Φ.V y) = 1`. Rewrite using `[← map_natCast (Φ.ev y), ← map_mul, ← map_natCast φ, ← hu, Units.inv_mul, map_one]`. Set `w : (Fin s → Φ.X y) → TT → ZMod (X₁.S.r * X₁.S.N)` to `fun mu τ => (sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) (l mu)`. Establish `hw : ∀ mu τ τ', w mu (τ + τ') = w mu τ + w mu τ'` using `fun mu τ τ' => by`.

Simplify using `only [w, AddSubgroup.coe_add, eStd_add_left, smul_add]`. Establish `hsg : ∀ a b : ZMod (X₁.S.r * X₁.S.N), (sg : ℤ) • a = (sg : ℤ) • b → a = b` using `fun a b h => by`. Use `congrArg (fun t => (sg : ℤ) • t) h` as an intermediate fact. Apply the tactic sequence `have e : ((sg : ℤ) * sg) = 1 := by rcases Int.units_eq_one_or sg with h | h <;> simp [h]`. Simplify `this` using `only [smul_smul, e, one_smul]`.

Establish `hwκ : ∀ mu, (∀ τ, w mu τ = w κ τ) ↔ ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu v) (κ v)` using `fun mu => by`. Rewrite using `[← congMod_pi_iff, ← hlC mu κ]`. Conclude with `⟨fun h τ hτ' => hsg _ _ (h ⟨τ, hτ'⟩), fun h τ => by simp only [w, h τ τ.2]⟩`. Establish `hlab' : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁` using `fun c => by`. Rewrite using `[← SetLike.mem_coe, ← hlab]`.

Conclude with `Set.mem_range_self c`. Establish `hsum : ∀ τ : TT, SumI (maximalIdeal (Φ.V y)) (fun mu => Φ.ev y zt ^ (w mu τ).val * Φ.term y mu c) (Φ.ev y (hτ τ))` using `fun τ => hlink (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪 Φ.Q lab hlab' (Φ.term y) hT c τ τ.2 zt (hτ τ) hzt (hhτ τ) (fun mu => w mu τ) (fun a mu hY => by simp only [w, hlY τ τ.2 a mu hY])`. Set `f : (Fin s → Φ.X y) → Φ.V y` to `fun mu => if ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu v) (κ v) then Φ.term y mu c else 0`. Establish `hf` using `sumI_fourier (maximalIdeal (Φ.V y)) hω (Φ.ev y d) hd w hw κ (fun mu => Φ.term y mu c) (fun τ => Φ.ev y (hτ τ)) hsum f (fun mu h => if_pos ((hwκ mu).1 h)) (fun mu h => if_neg fun h' => h ((hwκ mu).2 h'))`. Use `⟨d * ∑ τ : TT, zt ^ (-(w κ τ)).val * hτ τ, isClassSum_of_sumI Φ y _ κ c (RingHom.id _) _ f (fun mu h => if_pos h) (fun mu h => if_neg h) ?_⟩` and prove the remaining obligations.

Simplify `hf` using `only [map_mul, map_sum, map_pow]`.
-/
theorem exact_of_isGeo : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : O → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (Φ : VPre bar q W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam), GlobalTheory.GSep.IsGeo X₁ z₁ act x₀ Φ lab → Φ.Exact (X₁.S.r * X₁.S.N) := by
  intro O _ bar q s W X₁ z₁ act x₀ Φ lab hG
  obtain ⟨hdiv, hlab, hmem⟩ := hG
  obtain ⟨sg, eps, hlink⟩ := GlobalTheory.T.thetaConstants_translate_eq_twisted_sums O X₁ z₁ act x₀ hdiv
  intro y κ c
  obtain ⟨𝔪, hT⟩ := hmem y
  haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)⟩
  haveI : IsDomain X₁.o₁ := X₁.ar.ded.toIsDomain
  obtain ⟨yy1, yy2, yy3, yy4⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level O X₁ z₁ act (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪
  have hH := GlobalTheory.T.mem_dividingLabels_iff_class_zero O X₁ z₁ act x₀ hdiv (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪
  obtain ⟨l, -, hlY, hlC⟩ := labels X₁.S (X₁.S.HH X₁.M z₁) 𝔪.YY yy1 yy2 yy3 yy4 hH

  let φ : X₁.o₁ →+* X₁.M.Z.presheaf.stalk z₁ :=
    (X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))
  have hsh : ∀ b : X₁.M.O z₁, X₁.M.stalkHom z₁ ((X₁.M.stalkEquiv z₁).symm b) = b := fun b => by
    rw [← RatModel.coe_stalkEquiv (M := X₁.M), RingEquiv.apply_symm_apply]
  have hφ : ∀ a, X₁.M.stalkHom z₁ (φ a) = algebraMap X₁.o₁ X₁.Ω₁ a := fun a => hsh _

  let zt := φ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))
  have hzt : X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) := hφ _
  have hunitV : IsUnit (((X₁.S.r * X₁.S.N : ℕ) : Φ.V y)) := by
    have := X₁.S.unit.map ((Φ.ev y).comp φ)
    rwa [map_natCast] at this
  have hω : IsPrimitiveRoot (Φ.ev y zt) (X₁.S.r * X₁.S.N) := by
    have h0 : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
      X₁.S.prim.pow (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) 2) (sq _)
    exact isPrimitiveRoot_map' ((Φ.ev y).comp φ) hunitV.ne_zero h0

  let TT := X₁.S.TT X₁.M z₁
  have hmemO : ∀ τ : TT, algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ ∈ X₁.M.O z₁ :=
    fun τ => by rw [mul_div_assoc]; exact mul_mem (Subalgebra.algebraMap_mem _ _) (hdiv.2 _)
  let hτ : TT → X₁.M.Z.presheaf.stalk z₁ := fun τ => (X₁.M.stalkEquiv z₁).symm ⟨_, hmemO τ⟩
  have hhτ : ∀ τ : TT, X₁.M.stalkHom z₁ (hτ τ) =
      algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ := fun τ => hsh _

  have hcard : IsUnit ((Fintype.card TT : ℕ) : X₁.o₁) := by
    have h1 : Fintype.card TT ∣ Fintype.card X₁.S.Gam := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact AddSubgroup.card_addSubgroup_dvd_card _
    have h2 : IsUnit ((Fintype.card X₁.S.Gam : ℕ) : X₁.o₁) := by
      rw [Fintype.card_fun, ZMod.card, Nat.cast_pow]; exact X₁.S.unit.pow _
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast h1) h2
  obtain ⟨u, hu⟩ := hcard.map φ
  let d := ((u⁻¹ : (X₁.M.Z.presheaf.stalk z₁)ˣ) : X₁.M.Z.presheaf.stalk z₁)
  have hd : Φ.ev y d * (Fintype.card TT : Φ.V y) = 1 := by
    rw [← map_natCast (Φ.ev y), ← map_mul, ← map_natCast φ, ← hu, Units.inv_mul, map_one]

  let w : (Fin s → Φ.X y) → TT → ZMod (X₁.S.r * X₁.S.N) := fun mu τ => (sg : ℤ) • eStd X₁.S.g _ (τ : X₁.S.Gam) (l mu)
  have hw : ∀ mu τ τ', w mu (τ + τ') = w mu τ + w mu τ' := fun mu τ τ' => by
    simp only [w, AddSubgroup.coe_add, eStd_add_left, smul_add]
  have hsg : ∀ a b : ZMod (X₁.S.r * X₁.S.N), (sg : ℤ) • a = (sg : ℤ) • b → a = b := fun a b h => by
    have := congrArg (fun t => (sg : ℤ) • t) h
    have e : ((sg : ℤ) * sg) = 1 := by rcases Int.units_eq_one_or sg with h | h <;> simp [h]
    simpa only [smul_smul, e, one_smul] using this
  have hwκ : ∀ mu, (∀ τ, w mu τ = w κ τ) ↔ ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu v) (κ v) := fun mu => by
    rw [← congMod_pi_iff, ← hlC mu κ]
    exact ⟨fun h τ hτ' => hsg _ _ (h ⟨τ, hτ'⟩), fun h τ => by simp only [w, h τ τ.2]⟩
  have hlab' : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁ := fun c => by
    rw [← SetLike.mem_coe, ← hlab]; exact Set.mem_range_self c
  have hsum : ∀ τ : TT, SumI (maximalIdeal (Φ.V y)) (fun mu => Φ.ev y zt ^ (w mu τ).val * Φ.term y mu c) (Φ.ev y (hτ τ)) :=
    fun τ => hlink (Φ.V y) (Φ.ev y) (Fin s → Φ.X y) _ _ 𝔪 Φ.Q lab hlab' (Φ.term y) hT c τ τ.2 zt (hτ τ) hzt
      (hhτ τ) (fun mu => w mu τ) (fun a mu hY => by simp only [w, hlY τ τ.2 a mu hY])
  let f : (Fin s → Φ.X y) → Φ.V y := fun mu => if ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu v) (κ v) then Φ.term y mu c else 0
  have hf := sumI_fourier (maximalIdeal (Φ.V y)) hω (Φ.ev y d) hd w hw κ (fun mu => Φ.term y mu c) (fun τ => Φ.ev y (hτ τ))
    hsum f (fun mu h => if_pos ((hwκ mu).1 h)) (fun mu h => if_neg fun h' => h ((hwκ mu).2 h'))
  refine ⟨d * ∑ τ : TT, zt ^ (-(w κ τ)).val * hτ τ, isClassSum_of_sumI Φ y _ κ c (RingHom.id _) _ f
    (fun mu h => if_pos h) (fun mu h => if_neg h) ?_⟩
  simpa only [map_mul, map_sum, map_pow] using hf

end GlobalTheory.GSep.ExactSums

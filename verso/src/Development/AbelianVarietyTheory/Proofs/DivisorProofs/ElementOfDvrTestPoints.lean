import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStatementHolds
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegralCoeffZeroMulOfAevalInv

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory

/- English proof (translation)
Establish `hp0 : p ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Establish `hpC : ‖(p : ℂ_[p])‖ < 1`. Establish `h3 : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p])` using `by simp`. Rewrite using `[h3, norm_algebraMap', Padic.norm_p]`. Establish `: (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`.

Conclude with `inv_lt_one_of_one_lt₀ this`. Set `N : V' → ℝ` to `fun y => ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO y)‖`. Establish `hNmul : ∀ y z, N (y * z) = N y * N z` using `fun y z => by`. Simplify using `only [N, map_mul, norm_mul]`. Establish `hN0 : ∀ y, 0 ≤ N y` using `fun y => norm_nonneg _`.

Establish `hOC : ∀ z : ℂ_[p], z ∈ 𝓞_ℂ_[p] → ‖z‖ ≤ 1`. Introduce `z hz`. Establish `h : z ∈ 𝓞_ℂ_[p] ↔ ‖z‖ ≤ 1`. Rewrite using `[PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]`. Conclude with `(Valued.toNormedField.norm_le_one_iff).symm`.

Conclude with `h.1 hz`. Establish `hN1 : ∀ y, N y ≤ 1` using `fun y => hOC _ (kO y).2`. Establish `hNpos : ∀ y, y ≠ 0 → 0 < N y` using `fun y hy => by`. Apply `norm_pos_iff.2` to reduce the goal to its premises. Introduce `h0`.

Conclude with `hy (hkO (Subtype.val_injective (by simpa using h0)))`. Establish `hNone : N 1 = 1` using `by simp only [N, map_one, norm_one]`. Establish `hNu : ∀ w : V'ˣ, N w = 1` using `fun w => by`. Establish `h1 : N (w : V') * N ((w⁻¹ : V'ˣ) : V') = 1`. Rewrite using `[← hNmul, Units.mul_inv, hNone]`.

Use `hN1 (w : V')` as an intermediate fact. Use `hN1 ((w⁻¹ : V'ˣ) : V')` as an intermediate fact. Use polynomial arithmetic with `[hN0 (w : V'), hN0 ((w⁻¹ : V'ˣ) : V')]`. Establish `hNpow : ∀ y (m : ℕ), N (y ^ m) = N y ^ m` using `fun y m => by`. Simplify using `only [N, map_pow, norm_pow]`.

Establish `hNp : N (p : V') < 1`. Establish `: N (p : V') = ‖(p : ℂ_[p])‖` using `by simp only [N, map_natCast]`. Rewrite using `[this]`. Conclude with `hpC`. Take `⟨ϖ', hϖ'⟩` from `IsDiscreteValuationRing.exists_irreducible V'`.

Establish `hNϖ : N ϖ' < 1`. Establish `hp0' : (p : V') ≠ 0`. Introduce `h`. Establish `: (kO (p : V') : ℂ_[p]) = 0` using `by rw [h, map_zero]; rfl`. Rewrite `this` using `[map_natCast]`.

Conclude with `hp0 (by exact_mod_cast this)`. Take `⟨m, w, hw⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0' hϖ'`. Establish `hm : m ≠ 0`. Introduce and unpack `rfl`. Rewrite `hw` using `[pow_zero, _root_.mul_one]`.

Rewrite `hpT` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hpT (hw ▸ w.isUnit)`. Establish `hNpm : N (p : V') = N ϖ' ^ m`. Rewrite using `[hw, hNmul, hNu, _root_.one_mul, hNpow]`. Assume the negation of the conclusion as `hge`.

Establish `h1 : N ϖ' = 1` using `le_antisymm (hN1 _) (not_lt.1 hge)`. Rewrite `hNp` using `[hNpm, h1, one_pow]`. Conclude with `lt_irrefl _ hNp`. Break down `ValuationRing.dvd_total b a with h | ⟨d, hd⟩` into its components or cases. Conclude with `h`.

Distinguish the cases in `hdu : IsUnit d`. Take `⟨w, rfl⟩` from `hdu`. Conclude with `⟨((w⁻¹ : V'ˣ) : V'), by rw [hd, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩`. It suffices to derive a contradiction. Establish `hdm : d ∈ IsLocalRing.maximalIdeal V'` using `(IsLocalRing.mem_maximalIdeal _).2 hdu`.

Rewrite `hdm` using `[hϖ'.maximalIdeal_eq, Ideal.mem_span_singleton']`. Take `⟨d', rfl⟩` from `hdm`. Establish `hNd : N (d' * ϖ') < 1`. Rewrite using `[hNmul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hb0` using `hNpos _ hb`. Establish `h2 : N b = N a * N (d' * ϖ')` using `by rw [hd, hNmul]`. Establish `hle' : N a ≤ N b` using `hle`. Establish `h4` using `mul_le_mul_of_nonneg_right hle' (hN0 (d' * ϖ'))`. Establish `h5` using `mul_lt_mul_of_pos_left hNd hb0`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dvd_of_norm_le_of_padicComplexInt (p : ℕ) [Fact p.Prime] (V' : Type) [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (kO : V' →+* 𝓞_ℂ_[p]) (hkO : Function.Injective kO)
    (hpT : (p : V') ∈ IsLocalRing.maximalIdeal V') (a b : V') (hb : b ≠ 0)
    (hle : ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a)‖ ≤ ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO b)‖) : b ∣ a := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpC : ‖(p : ℂ_[p])‖ < 1 := by
    have h3 : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [h3, norm_algebraMap', Padic.norm_p]
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact inv_lt_one_of_one_lt₀ this
  let N : V' → ℝ := fun y => ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO y)‖
  have hNmul : ∀ y z, N (y * z) = N y * N z := fun y z => by
    simp only [N, map_mul, norm_mul]
  have hN0 : ∀ y, 0 ≤ N y := fun y => norm_nonneg _
  have hOC : ∀ z : ℂ_[p], z ∈ 𝓞_ℂ_[p] → ‖z‖ ≤ 1 := by
    intro z hz
    have h : z ∈ 𝓞_ℂ_[p] ↔ ‖z‖ ≤ 1 := by
      rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
      exact (Valued.toNormedField.norm_le_one_iff).symm
    exact h.1 hz
  have hN1 : ∀ y, N y ≤ 1 := fun y => hOC _ (kO y).2
  have hNpos : ∀ y, y ≠ 0 → 0 < N y := fun y hy => by
    apply norm_pos_iff.2
    intro h0
    exact hy (hkO (Subtype.val_injective (by simpa using h0)))
  have hNone : N 1 = 1 := by simp only [N, map_one, norm_one]
  have hNu : ∀ w : V'ˣ, N w = 1 := fun w => by
    have h1 : N (w : V') * N ((w⁻¹ : V'ˣ) : V') = 1 := by
      rw [← hNmul, Units.mul_inv, hNone]
    have := hN1 (w : V'); have := hN1 ((w⁻¹ : V'ˣ) : V')
    nlinarith [hN0 (w : V'), hN0 ((w⁻¹ : V'ˣ) : V')]
  have hNpow : ∀ y (m : ℕ), N (y ^ m) = N y ^ m := fun y m => by
    simp only [N, map_pow, norm_pow]
  have hNp : N (p : V') < 1 := by
    have : N (p : V') = ‖(p : ℂ_[p])‖ := by simp only [N, map_natCast]
    rw [this]; exact hpC
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V'
  have hNϖ : N ϖ' < 1 := by
    have hp0' : (p : V') ≠ 0 := by
      intro h
      have : (kO (p : V') : ℂ_[p]) = 0 := by rw [h, map_zero]; rfl
      rw [map_natCast] at this
      exact hp0 (by exact_mod_cast this)
    obtain ⟨m, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0' hϖ'
    have hm : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, _root_.mul_one] at hw
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hpT
      exact hpT (hw ▸ w.isUnit)
    have hNpm : N (p : V') = N ϖ' ^ m := by
      rw [hw, hNmul, hNu, _root_.one_mul, hNpow]
    by_contra hge
    have h1 : N ϖ' = 1 := le_antisymm (hN1 _) (not_lt.1 hge)
    rw [hNpm, h1, one_pow] at hNp
    exact lt_irrefl _ hNp
  rcases ValuationRing.dvd_total b a with h | ⟨d, hd⟩
  · exact h
  · by_cases hdu : IsUnit d
    · obtain ⟨w, rfl⟩ := hdu
      exact ⟨((w⁻¹ : V'ˣ) : V'), by rw [hd, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
    · exfalso
      have hdm : d ∈ IsLocalRing.maximalIdeal V' := (IsLocalRing.mem_maximalIdeal _).2 hdu
      rw [hϖ'.maximalIdeal_eq, Ideal.mem_span_singleton'] at hdm
      obtain ⟨d', rfl⟩ := hdm
      have hNd : N (d' * ϖ') < 1 := by
        rw [hNmul]
        calc N d' * N ϖ' ≤ 1 * N ϖ' := mul_le_mul_of_nonneg_right (hN1 _) (hN0 _)
          _ < 1 := by rw [_root_.one_mul]; exact hNϖ
      have hb0 := hNpos _ hb
      have h2 : N b = N a * N (d' * ϖ') := by rw [hd, hNmul]
      have hle' : N a ≤ N b := hle
      have h4 := mul_le_mul_of_nonneg_right hle' (hN0 (d' * ϖ'))
      have h5 := mul_lt_mul_of_pos_left hNd hb0
      linarith

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ V _ p _ hp A _ _ _ _ _ hinj e he x hx`. Establish `hp0 : p ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Establish `hfin : Finite (IsLocalRing.ResidueField V)` using `(GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hp0 hp).2`. Establish `hpV : ((p : V)) ∈ IsLocalRing.maximalIdeal V`. Rewrite using `[ValuationSubring.valuation_lt_one_iff]`.

Rewrite `hp` using `[ValuationSubring.mem_nonunits_iff]`. Simplify using `using hp`. Establish `hpV0 : ((p : V)) ≠ 0`. Introduce `h`. Establish `: ((p : V) : F) = 0` using `by rw [h]; rfl`.

Conclude with `hp0 (by exact_mod_cast this)`. Set `O'` to `AdicCompletion (IsLocalRing.maximalIdeal V) V`. Establish `hinj0 : Function.Injective (algebraMap V O')` using `GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V`. Use `haveI : CharZero O' := charZero_of_injective_algebraMap hinj0`. Use `haveI : IsLocalHom (algebraMap V O') := inferInstance`.

Establish `hfinO' : Finite (IsLocalRing.ResidueField O')` using `Finite.of_surjective _ (AdicCompletion.residueField_map_bijective V).2`. Set `L` to `Localization.Away (p : A)`. Establish `hpA0 : (p : A) ≠ 0`. Introduce `h`. Apply `hpV0` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_natCast, h, map_zero]`. Set `Ω` to `FractionRing A`. Establish `hu : IsUnit (algebraMap A Ω (p : A))` using `IsUnit.mk0 _ (fun h => hpA0 (IsFractionRing.injective A Ω (by rw [h, map_zero])))`. Set `j : L →+* Ω` to `IsLocalization.Away.lift (p : A) hu`.

Establish `hj : ∀ a, j (algebraMap A L a) = algebraMap A Ω a` using `fun a => IsLocalization.lift_eq _ a`. Establish `hjinj : Function.Injective j`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj (p : A) y`.

Establish `h1 : algebraMap A Ω a = 0` using `by rw [← hj, ← ha, map_mul, hy, zero_mul]`. Establish `h2 : a = 0` using `IsFractionRing.injective A Ω (by rw [h1, map_zero])`. Establish `h3 : IsUnit (algebraMap A L (p : A) ^ n)` using `(IsLocalization.Away.algebraMap_isUnit (p : A)).pow n`. Rewrite `ha` using `[h2, map_zero]`. Conclude with `h3.mul_left_eq_zero.1 ha`.

Take `⟨s, hs1, hsint⟩` from `GlobalTheory.isIntegral_mul_of_bounded_at_points V O' hinj0 (GlobalTheory.exists_integral_point_of_complete_case (fun O B _ _ _ _ _ _ _ _ _ _ M hM hsp e he => GlobalTheory.exists_integral_point_through O B M hM hsp e he) V O' hinj0) A Ω hinj e he (j x) (fun V' _ _ _ _ _ φ hφ hφe …`. Take `⟨-, hloc', hcpl, hch, hfin'⟩` from `GlobalTheory.dvr_finite_over_complete_dvr O' V'`. Set `T : CDVR` to `{ V := V' }`. Establish `hT : T.FinRes` using `hfin' hfinO'`. Take `⟨q, hq, k, kO, hk⟩` from `GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hT`.

Establish `hpT : (p : V') ∈ IsLocalRing.maximalIdeal V'`. Establish `h1 : (p : V') = algebraMap O' V' (algebraMap V O' (p : V))`. Rewrite using `[map_natCast, map_natCast]`. Rewrite using `[h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu'`.

Rewrite `hpV` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hpV (isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ hu'))`. Take `rfl` from `GlobalTheory.FlatModel.eq_of_mem_maximalIdeal_of_padicComplexInt T p q hpT kO`. Establish `hkO : Function.Injective kO` using `fun a b hab => by`. Apply `IsFractionRing.injective T.V T.Fr` to reduce the goal to its premises.

Apply `k.injective` to reduce the goal to its premises. Rewrite using `[← hk, ← hk, hab]`. Set `g : A →+* ℂ_[p]` to `(algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (kO.comp φ)`. Establish `hgu : IsUnit (g (p : A))`. Rewrite using `[map_natCast]`.

Conclude with `IsUnit.mk0 _ (by exact_mod_cast hp0)`. Set `ψ : L →+* ℂ_[p]` to `IsLocalization.Away.lift (p : A) hgu`. Establish `hψ : ψ.comp (algebraMap A L) = g` using `IsLocalization.Away.lift_comp (p : A) hgu`. Establish `hxle : ‖ψ x‖ ≤ 1` using `hx T kO φ hT hkO hφe ψ hψ`. Establish `hxb : x * algebraMap A L b = algebraMap A L a`.

Apply `hjinj` to reduce the goal to its premises. Rewrite using `[map_mul, hj, hj, hab]`. Establish `hgab : ψ x * g b = g a`. Rewrite using `[← hψ, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, hxb]`. Use `GlobalTheory.dvd_of_norm_le_of_padicComplexInt p V' kO hkO hpT (φ a) (φ b) hb ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `‖g a‖ ≤ ‖g b‖`. Rewrite using `[← hgab, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) hxle`. Use the proof step `)`. Take `⟨c, hc⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 hsint`.

Establish `hsc : algebraMap A L s * x = algebraMap A L c`. Apply `hjinj` to reduce the goal to its premises. Rewrite using `[map_mul, hj, hj, hc]`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Establish `hs1' : s - 1 ∈ Ideal.span {algebraMap V A ϖ}`.

Rewrite `hs1` using `[hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Conclude with `hs1`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 hs1'`. Establish `hcop : IsCoprime s (algebraMap V A ϖ)` using `⟨1, -t, by linear_combination (-1 : A) * ht⟩`. Take `⟨k, u, hpu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hpV0 hϖ`.

Take `⟨n, a0, ha0⟩` from `IsLocalization.Away.surj (p : A) x`. Establish `hpA : ((p : A)) ^ n = algebraMap V A ((u ^ n : Vˣ) : V) * algebraMap V A ϖ ^ (k * n)`. Rewrite using `[← map_natCast (algebraMap V A), hpu, ← map_pow, ← map_pow, ← map_mul, mul_pow, ← pow_mul, Units.val_pow_eq_pow_val]`. Establish `hcopU : IsCoprime s (algebraMap V A ((u ^ n : Vˣ) : V))`. Take `⟨w, hw⟩` from `((u ^ n).isUnit.map (algebraMap V A))`.

Conclude with `⟨0, ((w⁻¹ : Aˣ) : A), by rw [← hw]; simp⟩`. Establish `hcopP : IsCoprime s ((p : A) ^ n)`. Rewrite using `[hpA]`. Conclude with `hcopU.mul_right (hcop.pow_right)`. Take `⟨α, β, hαβ⟩` from `hcopP`.

Use `⟨α * c + β * a0, ?_⟩` and prove the remaining obligations. Establish `hαβ' : algebraMap A L α * algebraMap A L s + algebraMap A L β * algebraMap A L (p : A) ^ n = 1`. Rewrite using `[← map_pow, ← map_mul, ← map_mul, ← map_add, hαβ, map_one]`. Rewrite using `[map_add, map_mul, map_mul]`. Take the linear combination `(-(algebraMap A L α)) * hsc + (-(algebraMap A L β)) * ha0 + x * hαβ'`.
-/
theorem mem_range_of_norm_le_one_at_points_away : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra V A] [Algebra.FiniteType V A], Function.Injective (algebraMap V A) → ∀ e : A, e ≠ 0 → ∀ x : Localization.Away (p : A), (∀ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (φ : A →+* T.V), T.FinRes → Function.Injective kO → φ e ≠ 0 → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p], ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (kO.comp φ) → ‖ψ x‖ ≤ 1) → ∃ a : A, algebraMap A (Localization.Away (p : A)) a = x := by
  intro F _ _ V _ p _ hp A _ _ _ _ _ hinj e he x hx
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hfin : Finite (IsLocalRing.ResidueField V) :=
    (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hp0 hp).2
  have hpV : ((p : V)) ∈ IsLocalRing.maximalIdeal V := by
    rw [ValuationSubring.valuation_lt_one_iff]
    rw [ValuationSubring.mem_nonunits_iff] at hp
    simpa using hp
  have hpV0 : ((p : V)) ≠ 0 := by
    intro h
    have : ((p : V) : F) = 0 := by rw [h]; rfl
    exact hp0 (by exact_mod_cast this)
  let O' := AdicCompletion (IsLocalRing.maximalIdeal V) V
  have hinj0 : Function.Injective (algebraMap V O') := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V
  haveI : CharZero O' := charZero_of_injective_algebraMap hinj0
  haveI : IsLocalHom (algebraMap V O') := inferInstance
  have hfinO' : Finite (IsLocalRing.ResidueField O') :=
    Finite.of_surjective _ (AdicCompletion.residueField_map_bijective V).2
  let L := Localization.Away (p : A)
  have hpA0 : (p : A) ≠ 0 := by
    intro h
    apply hpV0
    apply hinj
    rw [map_natCast, h, map_zero]
  let Ω := FractionRing A
  have hu : IsUnit (algebraMap A Ω (p : A)) :=
    IsUnit.mk0 _ (fun h => hpA0 (IsFractionRing.injective A Ω (by rw [h, map_zero])))
  let j : L →+* Ω := IsLocalization.Away.lift (p : A) hu
  have hj : ∀ a, j (algebraMap A L a) = algebraMap A Ω a := fun a => IsLocalization.lift_eq _ a
  have hjinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (p : A) y
    have h1 : algebraMap A Ω a = 0 := by rw [← hj, ← ha, map_mul, hy, zero_mul]
    have h2 : a = 0 := IsFractionRing.injective A Ω (by rw [h1, map_zero])
    have h3 : IsUnit (algebraMap A L (p : A) ^ n) := (IsLocalization.Away.algebraMap_isUnit (p : A)).pow n
    rw [h2, map_zero] at ha
    exact h3.mul_left_eq_zero.1 ha
  obtain ⟨s, hs1, hsint⟩ := GlobalTheory.isIntegral_mul_of_bounded_at_points V O' hinj0
    (GlobalTheory.exists_integral_point_of_complete_case
      (fun O B _ _ _ _ _ _ _ _ _ _ M hM hsp e he => GlobalTheory.exists_integral_point_through O B M hM hsp e he)
      V O' hinj0)
    A Ω hinj e he (j x) (fun V' _ _ _ _ _ φ hφ hφe a b hab hb => by
      obtain ⟨-, hloc', hcpl, hch, hfin'⟩ := GlobalTheory.dvr_finite_over_complete_dvr O' V'
      let T : CDVR := { V := V' }
      have hT : T.FinRes := hfin' hfinO'
      obtain ⟨q, hq, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hT
      have hpT : (p : V') ∈ IsLocalRing.maximalIdeal V' := by
        have h1 : (p : V') = algebraMap O' V' (algebraMap V O' (p : V)) := by
          rw [map_natCast, map_natCast]
        rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu'
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hpV
        exact hpV (isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ hu'))
      obtain rfl := GlobalTheory.FlatModel.eq_of_mem_maximalIdeal_of_padicComplexInt T p q hpT kO
      have hkO : Function.Injective kO := fun a b hab => by
        apply IsFractionRing.injective T.V T.Fr
        apply k.injective
        rw [← hk, ← hk, hab]
      let g : A →+* ℂ_[p] := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (kO.comp φ)
      have hgu : IsUnit (g (p : A)) := by
        rw [map_natCast]
        exact IsUnit.mk0 _ (by exact_mod_cast hp0)
      let ψ : L →+* ℂ_[p] := IsLocalization.Away.lift (p : A) hgu
      have hψ : ψ.comp (algebraMap A L) = g := IsLocalization.Away.lift_comp (p : A) hgu
      have hxle : ‖ψ x‖ ≤ 1 := hx T kO φ hT hkO hφe ψ hψ
      have hxb : x * algebraMap A L b = algebraMap A L a := by
        apply hjinj
        rw [map_mul, hj, hj, hab]
      have hgab : ψ x * g b = g a := by
        rw [← hψ, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, hxb]
      refine GlobalTheory.dvd_of_norm_le_of_padicComplexInt p V' kO hkO hpT (φ a) (φ b) hb ?_
      change ‖g a‖ ≤ ‖g b‖
      rw [← hgab, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hxle
      )
  obtain ⟨c, hc⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 hsint
  have hsc : algebraMap A L s * x = algebraMap A L c := by
    apply hjinj
    rw [map_mul, hj, hj, hc]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hs1' : s - 1 ∈ Ideal.span {algebraMap V A ϖ} := by
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hs1
    exact hs1
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hs1'
  have hcop : IsCoprime s (algebraMap V A ϖ) := ⟨1, -t, by linear_combination (-1 : A) * ht⟩
  obtain ⟨k, u, hpu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hpV0 hϖ
  obtain ⟨n, a0, ha0⟩ := IsLocalization.Away.surj (p : A) x
  have hpA : ((p : A)) ^ n = algebraMap V A ((u ^ n : Vˣ) : V) * algebraMap V A ϖ ^ (k * n) := by
    rw [← map_natCast (algebraMap V A), hpu, ← map_pow, ← map_pow, ← map_mul, mul_pow, ← pow_mul,
      Units.val_pow_eq_pow_val]
  have hcopU : IsCoprime s (algebraMap V A ((u ^ n : Vˣ) : V)) := by
    obtain ⟨w, hw⟩ := ((u ^ n).isUnit.map (algebraMap V A))
    exact ⟨0, ((w⁻¹ : Aˣ) : A), by rw [← hw]; simp⟩
  have hcopP : IsCoprime s ((p : A) ^ n) := by
    rw [hpA]
    exact hcopU.mul_right (hcop.pow_right)
  obtain ⟨α, β, hαβ⟩ := hcopP
  refine ⟨α * c + β * a0, ?_⟩
  have hαβ' : algebraMap A L α * algebraMap A L s + algebraMap A L β * algebraMap A L (p : A) ^ n = 1 := by
    rw [← map_pow, ← map_mul, ← map_mul, ← map_add, hαβ, map_one]
  rw [map_add, map_mul, map_mul]
  linear_combination (-(algebraMap A L α)) * hsc + (-(algebraMap A L β)) * ha0 + x * hαβ'

end GlobalTheory

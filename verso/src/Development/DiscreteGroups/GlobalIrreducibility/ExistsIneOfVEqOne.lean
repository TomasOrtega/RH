import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import GroundTheory.LocalFields.PrincipalUnitsModule
import GroundTheory.LocalFields.PadicLogHom
import GroundTheory.LocalFields.LocalFourierHaar
import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Art

variable {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A w'}

/- English proof (translation)
Establish `e1` using `DiscreteGroups.sglob.DzIso.val_lt_iff y`. Establish `e2` using `DiscreteGroups.sglob.DzIso.val_le_iff y`. Rewrite `e1` using `[Valued.toNormedField.norm_lt_one_iff]`. Rewrite `e2` using `[Valued.toNormedField.norm_le_one_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `le_antisymm (e2.1 h.le) (not_lt.1 fun hl => (e1.2 hl).ne h)`. Introduce `h`. Conclude with `le_antisymm (e2.2 h.le) (not_lt.1 fun hl => (e1.1 hl).ne h)`.
-/
theorem val_eq_one_iff (y : w'.adicCompletion E') :
    valuation (w'.adicCompletion E') y = 1 ↔ Valued.v y = 1 := by
  have e1 := DiscreteGroups.sglob.DzIso.val_lt_iff y
  have e2 := DiscreteGroups.sglob.DzIso.val_le_iff y
  rw [Valued.toNormedField.norm_lt_one_iff] at e1
  rw [Valued.toNormedField.norm_le_one_iff] at e2
  constructor
  · intro h
    exact le_antisymm (e2.1 h.le) (not_lt.1 fun hl => (e1.2 hl).ne h)
  · intro h
    exact le_antisymm (e2.2 h.le) (not_lt.1 fun hl => (e1.1 hl).ne h)

/- English proof (translation)
Take `⟨σ, hσ⟩` from `ha'.surj u`. Establish `h1` using `ha'.ord_eq σ`. Rewrite `h1` using `[hσ, GlobalTheory.SmGL.SphCompletion.ord_completion, hu]`. Establish `h2 : deg σ = 0` using `by simpa using h1`. Conclude with `⟨⟨σ, deg_eq_zero_iff.1 h2⟩, by rw [← hσ]; rfl⟩`.
-/
theorem exists_ine_of_v_eq_one {a' : Weil h' →* (w'.adicCompletion E')ˣ} (ha' : IsLocalArtin h' a')
    (u : (w'.adicCompletion E')ˣ) (hu : Valued.v (u : w'.adicCompletion E') = 1) :
    ∃ t : Ine (F := E') A, a' (ineIncl h' t) = u := by
  obtain ⟨σ, hσ⟩ := ha'.surj u
  have h1 := ha'.ord_eq σ
  rw [hσ, GlobalTheory.SmGL.SphCompletion.ord_completion, hu] at h1
  have h2 : deg σ = 0 := by simpa using h1
  exact ⟨⟨σ, deg_eq_zero_iff.1 h2⟩, by rw [← hσ]; rfl⟩

end Art

set_option linter.unusedVariables false in
/- English proof (translation)
Introduce `z`. Take `⟨x, hx⟩` from `hr z`. Establish `hnm : x ∉ w'.asIdeal` using `fun hm => z.ne_zero (by rw [← hx, ← RingHom.mem_ker, hk]; exact hm)`. Establish `hv : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = 1`. Establish `e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E')` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')`.

Rewrite using `[e]`. Conclude with `(HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w') (K := E')).2 hnm`. Establish `h0 : algebraMap E' (w'.adicCompletion E') (x : E') ≠ 0` using `fun h0 => by`. Rewrite `hv` using `[h0, map_zero]`. Conclude with `zero_ne_one hv`.

Take `⟨t, ht⟩` from `exists_ine_of_v_eq_one ha' (Units.mk0 _ h0) (by simpa using hv)`. Use `⟨t, x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[ht, Units.val_mk0, sub_self, map_zero]`. Conclude with `zero_lt_one`.
-/
theorem exists_ine_of_res {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (n : ℕ)
    (hn : 0 < n) (hN : normV w' = g ^ n) (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (K : Type) [Field K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red) (hk : RingHom.ker red = w'.asIdeal) :
    ∀ z : Kˣ, ∃ (t : Ine (F := E') A) (x : 𝓞 E'), red x = z ∧
      Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  intro z
  obtain ⟨x, hx⟩ := hr z
  have hnm : x ∉ w'.asIdeal := fun hm => z.ne_zero (by rw [← hx, ← RingHom.mem_ker, hk]; exact hm)
  have hv : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = 1 := by
    have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
    rw [e]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w') (K := E')).2 hnm
  have h0 : algebraMap E' (w'.adicCompletion E') (x : E') ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv; exact zero_ne_one hv
  obtain ⟨t, ht⟩ := exists_ine_of_v_eq_one ha' (Units.mk0 _ h0) (by simpa using hv)
  refine ⟨t, x, hx, ?_⟩
  rw [ht, Units.val_mk0, sub_self, map_zero]
  exact zero_lt_one

/- English proof (translation)
Take `⟨χ, -, hχ⟩` from `ha'.factor η hη`. Establish `hgp : g.Prime` using `Fact.out`. Establish `hvF : ∀ e : E', Valued.v (algebraMap E' (w'.adicCompletion E') e) = w'.valuation E' e` using `fun e => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' e`. Establish `hpow : ∀ u : (w'.adicCompletion E')ˣ, Valued.v (u : w'.adicCompletion E') = 1 → χ u ^ (g ^ n - 1) = 1`. Introduce `u hu`.

Take `⟨t, ht⟩` from `exists_ine_of_v_eq_one ha' u hu`. Rewrite using `[← ht, ← MonoidHom.comp_apply, ← hχ]`. Conclude with `hηN t`. Establish `hgw : ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal`. Establish `: Finite (𝓞 E' ⧸ w'.asIdeal)` using `w'.asIdeal.finiteQuotientOfFreeOfNeBot w'.ne_bot`.

Set `` to `Fintype.ofFinite (𝓞 E' ⧸ w'.asIdeal)`. Establish `hc : ((Fintype.card (𝓞 E' ⧸ w'.asIdeal) : ℕ) : 𝓞 E' ⧸ w'.asIdeal) = 0` using `Nat.cast_card_eq_zero _`. Rewrite `hc` using `[← Nat.card_eq_fintype_card, show Nat.card (𝓞 E' ⧸ w'.asIdeal) = g ^ n from hN, Nat.cast_pow]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `(pow_eq_zero_iff hn.ne').1 hc`.

Establish `hgv : Valued.v ((g : ℕ) : w'.adicCompletion E') < 1`. Establish `h1` using `(w'.valuation_lt_one_iff_mem (K := E') ((g : ℕ) : 𝓞 E')).2 hgw`. Establish `h2` using `hvF ((g : ℕ) : E')`. Rewrite `h2` using `[map_natCast]`. Rewrite using `[h2]`.

Simplify using `using h1`. Establish `: CharP 𝓀[w'.adicCompletion E'] g`. Rewrite using `[CharP.charP_iff_prime_eq_zero hgp, ← map_natCast (IsLocalRing.residue 𝒪[w'.adicCompletion E']) g, GlobalTheory.StepData.residue_eq_zero_iff_lt]`. Establish `e : (((g : ℕ) : 𝒪[w'.adicCompletion E']) : w'.adicCompletion E') = ((g : ℕ) : w'.adicCompletion E')`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `(DiscreteGroups.sglob.DzIso.val_lt_iff _).2 (Valued.toNormedField.norm_lt_one_iff.2 hgv)`. Establish `hmU : IsUnit (((g ^ n - 1 : ℕ) : ℤ_[g]))`. Rewrite using `[← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast]`. Establish `: Fact (1 < g)` using `⟨hgp.one_lt⟩`.

Establish `h1 : 1 ≤ g ^ n` using `Nat.one_le_pow _ _ hgp.pos`. Rewrite using `[Nat.cast_sub h1, Nat.cast_pow, ZMod.natCast_self, zero_pow hn.ne', Nat.cast_one, zero_sub, neg_eq_zero]`. Conclude with `one_ne_zero`. Establish `hU1 : ∀ u : (w'.adicCompletion E')ˣ, valuation (w'.adicCompletion E') ((u : w'.adicCompletion E') - 1) < 1 → χ u = 1`. Introduce `u hu`.

Establish `hmem : u ∈ GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1` using `(GroundTheory.LocalField.mem_unitFiltrationUnits_iff_valBall le_rfl).2 (GroundTheory.LocalField.mem_valBall_one_iff.2 hu)`. Set `U : Additive (GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1)` to `Additive.ofMul ⟨u, hmem⟩`. Set `y` to `((hmU.unit⁻¹ : ℤ_[g]ˣ) : ℤ_[g]) • U`. Establish `hy : (((g ^ n - 1 : ℕ) : ℤ_[g])) • y = U`. Rewrite using `[smul_smul, IsUnit.mul_val_inv, one_smul]`.

Rewrite `hy` using `[GroundTheory.LocalField.natCast_smul g (g ^ n - 1) y]`. Establish `hy' : ((Additive.toMul y : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) : (w'.adicCompletion E')ˣ) ^ (g ^ n - 1) = u`. Use `congrArg (fun z : Additive (GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) => ((Additive.toMul z : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) : (w'.adicCompletion E')ˣ)) hy` as an intermediate fact. Simplify `this` using `[U]`. Establish `hy0 : ((Additive.toMul y : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) : (w'.adicCompletion E')ˣ) ∈ GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 0` using `GroundTheory.LocalField.unitFiltrationUnits_antitone (Nat.zero_le 1) (Additive.toMul y).2`.

Establish `hyv` using `(val_eq_one_iff _).1 (GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff.1 hy0)`. Rewrite using `[← hy', map_pow]`. Conclude with `hpow _ hyv`. Establish `hcong : ∀ u1 u2 : (w'.adicCompletion E')ˣ, Valued.v (u1 : w'.adicCompletion E') = 1 → Valued.v ((u1 : w'.adicCompletion E') - u2) < 1 → χ u1 = χ u2`. Introduce `u1 u2 h1 h2`.

Establish `hinv : Valued.v (((u1⁻¹ : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') = 1`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]`. Establish `: χ (u1⁻¹ * u2) = 1` using `hU1 _ (by`. Rewrite using `[DiscreteGroups.sglob.DzIso.val_lt_iff, Valued.toNormedField.norm_lt_one_iff]`. Establish `e : (((u1⁻¹ * u2 : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') - 1 = ((u1⁻¹ : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') * ((u2 : w'.adicCompletion E') - u1)`.

Rewrite using `[Units.val_mul, mul_sub, Units.inv_mul]`. Rewrite using `[e, map_mul, hinv, one_mul, Valuation.map_sub_swap]`. Conclude with `h2)`. Rewrite `this` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `this`.

Establish `hv1 : ∀ x : 𝓞 E', red x ≠ 0 → Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = 1`. Introduce `x hx`. Establish `hnm : x ∉ w'.asIdeal` using `fun hm => hx (by rw [← RingHom.mem_ker, hk]; exact hm)`. Rewrite using `[hvF]`. Conclude with `(HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w') (K := E')).2 hnm`.

Use `choose xz hxz using hr`. Establish `hne : ∀ z : Kˣ, algebraMap E' (w'.adicCompletion E') (xz z : E') ≠ 0` using `fun z h0 => by`. Use `hv1 (xz z) (by rw [hxz]; exact z.ne_zero)` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `zero_ne_one this`.

Set `Uz : Kˣ → (w'.adicCompletion E')ˣ` to `fun z => Units.mk0 _ (hne z)`. Establish `hUv : ∀ z : Kˣ, Valued.v ((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1` using `fun z => hv1 (xz z) (by rw [hxz]; exact z.ne_zero)`. Establish `hUc : ∀ (z : Kˣ) (x : 𝓞 E'), red x = z → Valued.v (((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1`. Introduce `z x hx`. Establish `hm : xz z - x ∈ w'.asIdeal` using `by rw [← hk, RingHom.mem_ker, map_sub, hxz, hx, sub_self]`.

Use `(w'.valuation_lt_one_iff_mem (K := E') (xz z - x)).2 hm` as an intermediate fact. Use `show Valued.v (algebraMap E' (w'.adicCompletion E') (xz z : E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1`. Rewrite using `[← map_sub, hvF]`. Conclude with `this`. Set `ξ : Kˣ →* ℂˣ` to `{ toFun := fun z => χ (Uz z) map_one' := by`.

Establish `h` using `hUc 1 1 (by rw [map_one, Units.val_one])`. Rewrite `h` using `[show algebraMap E' (w'.adicCompletion E') ((1 : 𝓞 E') : E') = (((1 : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') by simp]`. Use `show χ (Uz 1) = 1`. Rewrite using `[hcong _ 1 (hUv 1) h, map_one]`. Use the proof step `map_mul' := fun z1 z2 => by show χ (Uz (z1 * z2)) = χ (Uz z1) * χ (Uz z2)`.

Rewrite using `[← map_mul]`. Use `hcong _ _ (hUv _) ?_` and prove the remaining obligations. Establish `h` using `hUc (z1 * z2) (xz z1 * xz z2) (by rw [map_mul, hxz, hxz, Units.val_mul])`. Establish `e : (((Uz z1 * Uz z2 : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') = algebraMap E' (w'.adicCompletion E') ((xz z1 * xz z2 : 𝓞 E') : E')`. Simplify using `[Uz]`.

Rewrite using `[e]`. Conclude with `h }`. Use `⟨ξ, fun t x z hxz' hv => ?_⟩` and prove the remaining obligations. Use `show χ (Uz z) = η (ineIncl h' t)`. Rewrite using `[hχ, MonoidHom.comp_apply]`.

Use `hcong _ _ (hUv z) ?_` and prove the remaining obligations. Establish `h1` using `hUc z x hxz'`. Establish `e : ((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') - (a' (ineIncl h' t) : w'.adicCompletion E') = (((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) - ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' ( …`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 hv)`.
-/
theorem exists_resChar {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (n : ℕ)
    (hn : 0 < n) (hN : normV w' = g ^ n) (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (K : Type) [Field K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red) (hk : RingHom.ker red = w'.asIdeal)
    (η : Weil h' →* ℂˣ) (hη : IsSmooth η) (hηN : ∀ t : Ine (F := E') A, η (ineIncl h' t) ^ (g ^ n - 1) = 1) :
    ∃ ξ : Kˣ →* ℂˣ, ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
      Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        ξ z = η (ineIncl h' t) := by
  obtain ⟨χ, -, hχ⟩ := ha'.factor η hη
  have hgp : g.Prime := Fact.out
  have hvF : ∀ e : E', Valued.v (algebraMap E' (w'.adicCompletion E') e) = w'.valuation E' e :=
    fun e => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' e

  have hpow : ∀ u : (w'.adicCompletion E')ˣ, Valued.v (u : w'.adicCompletion E') = 1 → χ u ^ (g ^ n - 1) = 1 := by
    intro u hu
    obtain ⟨t, ht⟩ := exists_ine_of_v_eq_one ha' u hu
    rw [← ht, ← MonoidHom.comp_apply, ← hχ]
    exact hηN t

  have hgw : ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal := by
    have : Finite (𝓞 E' ⧸ w'.asIdeal) := w'.asIdeal.finiteQuotientOfFreeOfNeBot w'.ne_bot
    let := Fintype.ofFinite (𝓞 E' ⧸ w'.asIdeal)
    have hc : ((Fintype.card (𝓞 E' ⧸ w'.asIdeal) : ℕ) : 𝓞 E' ⧸ w'.asIdeal) = 0 := Nat.cast_card_eq_zero _
    rw [← Nat.card_eq_fintype_card, show Nat.card (𝓞 E' ⧸ w'.asIdeal) = g ^ n from hN, Nat.cast_pow] at hc
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (pow_eq_zero_iff hn.ne').1 hc
  have hgv : Valued.v ((g : ℕ) : w'.adicCompletion E') < 1 := by
    have h1 := (w'.valuation_lt_one_iff_mem (K := E') ((g : ℕ) : 𝓞 E')).2 hgw
    have h2 := hvF ((g : ℕ) : E')
    rw [map_natCast] at h2
    rw [h2]
    simpa using h1
  have : CharP 𝓀[w'.adicCompletion E'] g := by
    rw [CharP.charP_iff_prime_eq_zero hgp, ← map_natCast (IsLocalRing.residue 𝒪[w'.adicCompletion E']) g,
      GlobalTheory.StepData.residue_eq_zero_iff_lt]
    have e : (((g : ℕ) : 𝒪[w'.adicCompletion E']) : w'.adicCompletion E') = ((g : ℕ) : w'.adicCompletion E') := by
      simp
    rw [e]
    exact (DiscreteGroups.sglob.DzIso.val_lt_iff _).2 (Valued.toNormedField.norm_lt_one_iff.2 hgv)

  have hmU : IsUnit (((g ^ n - 1 : ℕ) : ℤ_[g])) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast]
    have : Fact (1 < g) := ⟨hgp.one_lt⟩
    have h1 : 1 ≤ g ^ n := Nat.one_le_pow _ _ hgp.pos
    rw [Nat.cast_sub h1, Nat.cast_pow, ZMod.natCast_self, zero_pow hn.ne', Nat.cast_one, zero_sub, neg_eq_zero]
    exact one_ne_zero
  have hU1 : ∀ u : (w'.adicCompletion E')ˣ,
      valuation (w'.adicCompletion E') ((u : w'.adicCompletion E') - 1) < 1 → χ u = 1 := by
    intro u hu
    have hmem : u ∈ GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1 :=
      (GroundTheory.LocalField.mem_unitFiltrationUnits_iff_valBall le_rfl).2 (GroundTheory.LocalField.mem_valBall_one_iff.2 hu)
    let U : Additive (GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) := Additive.ofMul ⟨u, hmem⟩
    let y := ((hmU.unit⁻¹ : ℤ_[g]ˣ) : ℤ_[g]) • U
    have hy : (((g ^ n - 1 : ℕ) : ℤ_[g])) • y = U := by
      rw [smul_smul, IsUnit.mul_val_inv, one_smul]
    rw [GroundTheory.LocalField.natCast_smul g (g ^ n - 1) y] at hy
    have hy' : ((Additive.toMul y : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) :
        (w'.adicCompletion E')ˣ) ^ (g ^ n - 1) = u := by
      have := congrArg (fun z : Additive (GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) =>
        ((Additive.toMul z : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) :
          (w'.adicCompletion E')ˣ)) hy
      simpa [U] using this
    have hy0 : ((Additive.toMul y : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) :
        (w'.adicCompletion E')ˣ) ∈ GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 0 :=
      GroundTheory.LocalField.unitFiltrationUnits_antitone (Nat.zero_le 1) (Additive.toMul y).2
    have hyv := (val_eq_one_iff _).1 (GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff.1 hy0)
    rw [← hy', map_pow]
    exact hpow _ hyv

  have hcong : ∀ u1 u2 : (w'.adicCompletion E')ˣ, Valued.v (u1 : w'.adicCompletion E') = 1 →
      Valued.v ((u1 : w'.adicCompletion E') - u2) < 1 → χ u1 = χ u2 := by
    intro u1 u2 h1 h2
    have hinv : Valued.v (((u1⁻¹ : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]
    have : χ (u1⁻¹ * u2) = 1 := hU1 _ (by
      rw [DiscreteGroups.sglob.DzIso.val_lt_iff, Valued.toNormedField.norm_lt_one_iff]
      have e : (((u1⁻¹ * u2 : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') - 1 =
          ((u1⁻¹ : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') * ((u2 : w'.adicCompletion E') - u1) := by
        rw [Units.val_mul, mul_sub, Units.inv_mul]
      rw [e, map_mul, hinv, one_mul, Valuation.map_sub_swap]
      exact h2)
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this
  have hv1 : ∀ x : 𝓞 E', red x ≠ 0 → Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = 1 := by
    intro x hx
    have hnm : x ∉ w'.asIdeal := fun hm => hx (by rw [← RingHom.mem_ker, hk]; exact hm)
    rw [hvF]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w') (K := E')).2 hnm
  choose xz hxz using hr
  have hne : ∀ z : Kˣ, algebraMap E' (w'.adicCompletion E') (xz z : E') ≠ 0 := fun z h0 => by
    have := hv1 (xz z) (by rw [hxz]; exact z.ne_zero)
    rw [h0, map_zero] at this
    exact zero_ne_one this
  let Uz : Kˣ → (w'.adicCompletion E')ˣ := fun z => Units.mk0 _ (hne z)
  have hUv : ∀ z : Kˣ, Valued.v ((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1 :=
    fun z => hv1 (xz z) (by rw [hxz]; exact z.ne_zero)
  have hUc : ∀ (z : Kˣ) (x : 𝓞 E'), red x = z →
      Valued.v (((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') -
        algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
    intro z x hx
    have hm : xz z - x ∈ w'.asIdeal := by rw [← hk, RingHom.mem_ker, map_sub, hxz, hx, sub_self]
    have := (w'.valuation_lt_one_iff_mem (K := E') (xz z - x)).2 hm
    show Valued.v (algebraMap E' (w'.adicCompletion E') (xz z : E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1
    rw [← map_sub, hvF]
    exact this
  let ξ : Kˣ →* ℂˣ :=
    { toFun := fun z => χ (Uz z)
      map_one' := by
        have h := hUc 1 1 (by rw [map_one, Units.val_one])
        rw [show algebraMap E' (w'.adicCompletion E') ((1 : 𝓞 E') : E') = (((1 : (w'.adicCompletion E')ˣ)) :
          w'.adicCompletion E') by simp] at h
        show χ (Uz 1) = 1
        rw [hcong _ 1 (hUv 1) h, map_one]
      map_mul' := fun z1 z2 => by
        show χ (Uz (z1 * z2)) = χ (Uz z1) * χ (Uz z2)
        rw [← map_mul]
        refine hcong _ _ (hUv _) ?_
        have h := hUc (z1 * z2) (xz z1 * xz z2) (by rw [map_mul, hxz, hxz, Units.val_mul])
        have e : (((Uz z1 * Uz z2 : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') =
            algebraMap E' (w'.adicCompletion E') ((xz z1 * xz z2 : 𝓞 E') : E') := by
          simp [Uz]
        rw [e]
        exact h }
  refine ⟨ξ, fun t x z hxz' hv => ?_⟩
  show χ (Uz z) = η (ineIncl h' t)
  rw [hχ, MonoidHom.comp_apply]
  refine hcong _ _ (hUv z) ?_
  have h1 := hUc z x hxz'
  have e : ((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') - (a' (ineIncl h' t) : w'.adicCompletion E') =
      (((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) -
        ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) := by
    ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 hv)

end DiscreteGroups.sglob.DzType

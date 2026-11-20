import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnit

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Neutral.B1
  GlobalTheory.HeckeGal

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Tame

variable {M Ω : Type} [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 M)}

/- English proof (translation)
Establish `: Finite (𝓞 M ⧸ v.asIdeal)` using `v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot`. Set `` to `Fintype.ofFinite (𝓞 M ⧸ v.asIdeal)`. Establish `hc : ((Fintype.card (𝓞 M ⧸ v.asIdeal) : ℕ) : 𝓞 M ⧸ v.asIdeal) = 0` using `Nat.cast_card_eq_zero _`. Rewrite `hc` using `[← Nat.card_eq_fintype_card]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`.

Conclude with `hc`.
-/
theorem normV_mem (v : HeightOneSpectrum (𝓞 M)) : ((normV v : ℕ) : 𝓞 M) ∈ v.asIdeal := by
  have : Finite (𝓞 M ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let := Fintype.ofFinite (𝓞 M ⧸ v.asIdeal)
  have hc : ((Fintype.card (𝓞 M ⧸ v.asIdeal) : ℕ) : 𝓞 M ⧸ v.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card] at hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact hc

omit [IsAlgClosure M Ω] in

/- English proof (translation)
Establish `hq : 1 < normV v` using `one_lt_normV v`. Establish `hζi : IsIntegral ℤ ζ` using `IsIntegral.of_pow (n := normV v - 1) (by omega) (by rw [hζ]; exact isIntegral_one)`. Establish `hζA : A.valuation ζ ≤ 1` using `(A.valuation_le_one_iff _).2 (ReciprocityTheory.Gal.mem_of_isIntegral_int A hζi)`. Establish `hζ1 : ζ ^ normV v = ζ`. Establish `: normV v = (normV v - 1) + 1` using `by omega`.

Rewrite using `[this, pow_succ, hζ, one_mul]`. Establish `hpow : ∀ (y : Ω), y ^ normV v = y → ∀ k : ℕ, y ^ (normV v ^ k) = y`. Introduce `y hy k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih => rw [pow_succ, pow_mul, ih, hy]`. Establish `hsζ : ((s : G M Ω) ζ) ^ (normV v - 1) = 1` using `by rw [← map_pow, hζ, map_one]`. Establish `hsζ1 : ((s : G M Ω) ζ) ^ normV v = (s : G M Ω) ζ`. Establish `: normV v = (normV v - 1) + 1` using `by omega`. Rewrite using `[this, pow_succ, hsζ, one_mul]`.

Take `⟨a, b, hab⟩` from `s.2`. Establish `hc` using `hab.2 ζ hζA`. Rewrite `hc` using `[hpow _ hsζ1, hpow _ hζ1]`. Establish `hsA : A.valuation ((s : G M Ω) ζ) ≤ 1`. Rewrite using `[A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hab.1, ← A.valuation_le_one_iff]`.

Conclude with `hζA`. Establish `hval1 : A.valuation ζ = 1`. Use `le_antisymm hζA (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Use `pow_lt_one₀ zero_le hlt (show normV v - 1 ≠ 0 by omega)` as an intermediate fact. Rewrite `this` using `[← map_pow, hζ, map_one]`.

Conclude with `lt_irrefl _ this`. Establish `hqA : A.valuation ((normV v : ℕ) : Ω) < 1`. Use `(h ((normV v : ℕ) : 𝓞 M)).2 (normV_mem v)` as an intermediate fact. Simplify using `using this`. Establish `hd : ¬ A.valuation (aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X]))) < 1`.

Establish `e : aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X])) = (((normV v - 1 : ℕ) : Ω)) * ζ ^ (normV v - 1 - 1)`. Simplify using `[derivative_X_pow]`. Rewrite using `[e, map_mul, map_pow, hval1, one_pow, mul_one]`. Establish `e2 : (((normV v - 1 : ℕ) : Ω)) = -1 + ((normV v : ℕ) : Ω)`. Rewrite using `[Nat.cast_sub hq.le]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h' : A.valuation ((normV v : ℕ) : Ω) < A.valuation (-1 : Ω)`. Rewrite using `[Valuation.map_neg, map_one]`. Conclude with `hqA`. Rewrite using `[e2, Valuation.map_add_eq_of_lt_left _ h', Valuation.map_neg, map_one]`.

Conclude with `lt_irrefl _`. Conclude with `(GlobalTheory.eq_of_root_congr_of_deriv_unit A (X ^ (normV v - 1) - 1) ζ ((s : G M Ω) ζ) hζA hsA (by simp [hζ]) (by simp [hsζ]) hd (by rw [Valuation.map_sub_swap]; exact hc)).symm`.
-/
theorem weil_fix_root (h : IsPlaceOver A v) (s : Weil h) (ζ : Ω) (hζ : ζ ^ (normV v - 1) = 1) :
    (s : G M Ω) ζ = ζ := by
  have hq : 1 < normV v := one_lt_normV v
  have hζi : IsIntegral ℤ ζ := IsIntegral.of_pow (n := normV v - 1) (by omega) (by rw [hζ]; exact isIntegral_one)
  have hζA : A.valuation ζ ≤ 1 := (A.valuation_le_one_iff _).2 (ReciprocityTheory.Gal.mem_of_isIntegral_int A hζi)
  have hζ1 : ζ ^ normV v = ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  have hpow : ∀ (y : Ω), y ^ normV v = y → ∀ k : ℕ, y ^ (normV v ^ k) = y := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, hy]
  have hsζ : ((s : G M Ω) ζ) ^ (normV v - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hsζ1 : ((s : G M Ω) ζ) ^ normV v = (s : G M Ω) ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hsζ, one_mul]
  obtain ⟨a, b, hab⟩ := s.2
  have hc := hab.2 ζ hζA
  rw [hpow _ hsζ1, hpow _ hζ1] at hc
  have hsA : A.valuation ((s : G M Ω) ζ) ≤ 1 := by
    rw [A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hab.1, ← A.valuation_le_one_iff]
    exact hζA
  have hval1 : A.valuation ζ = 1 := by
    refine le_antisymm hζA (not_lt.1 fun hlt => ?_)
    have := pow_lt_one₀ zero_le hlt (show normV v - 1 ≠ 0 by omega)
    rw [← map_pow, hζ, map_one] at this
    exact lt_irrefl _ this
  have hqA : A.valuation ((normV v : ℕ) : Ω) < 1 := by
    have := (h ((normV v : ℕ) : 𝓞 M)).2 (normV_mem v)
    simpa using this
  have hd : ¬ A.valuation (aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X]))) < 1 := by
    have e : aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X])) =
        (((normV v - 1 : ℕ) : Ω)) * ζ ^ (normV v - 1 - 1) := by
      simp [derivative_X_pow]
    rw [e, map_mul, map_pow, hval1, one_pow, mul_one]
    have e2 : (((normV v - 1 : ℕ) : Ω)) = -1 + ((normV v : ℕ) : Ω) := by
      rw [Nat.cast_sub hq.le]; ring
    have h' : A.valuation ((normV v : ℕ) : Ω) < A.valuation (-1 : Ω) := by
      rw [Valuation.map_neg, map_one]; exact hqA
    rw [e2, Valuation.map_add_eq_of_lt_left _ h', Valuation.map_neg, map_one]
    exact lt_irrefl _
  exact (GlobalTheory.eq_of_root_congr_of_deriv_unit A (X ^ (normV v - 1) - 1) ζ ((s : G M Ω) ζ) hζA hsA
    (by simp [hζ]) (by simp [hsζ]) hd (by rw [Valuation.map_sub_swap]; exact hc)).symm

end Tame

/- English proof (translation)
Introduce `hA hC M Ω _ _ _ _ _ _ g _ A v h hg1 hg2 a ha π hπ t x hx`. Establish `hq : 1 < normV v` using `one_lt_normV v`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap M Ω).injective`. Establish `: NeZero (normV v - 1)` using `⟨by omega⟩`. Establish `hg0 : ((g : ℕ) : Ω) ≠ 0` using `by exact_mod_cast (Fact.out : g.Prime).ne_zero`.

Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[zero_pow (by omega)]`. Conclude with `hg0 hπ.symm`. Set `f : Weil h →* rootsOfUnity (normV v - 1) Ω` to `{ toFun := fun s => ⟨Units.mk0 ((s : G M Ω) π / π) (div_ne_zero ((_root_.map_ne_zero _).2 hπ0) hπ0), by`.

Rewrite using `[mem_rootsOfUnity]`. Use `ext`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]`. Rewrite using `[div_pow, ← map_pow, hπ, map_natCast, div_self hg0]⟩`. Use the proof step `map_one' := by`.

Use `ext`. Simplify using `[div_self hπ0]`. Use the proof step `map_mul' := fun s s' => by`. Use `ext`. Simplify using `only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, Subgroup.coe_mul, AlgEquiv.mul_apply]`.

Establish `hr : (((s' : G M Ω) π / π)) ^ (normV v - 1) = 1`. Rewrite using `[div_pow, ← map_pow, hπ, map_natCast, div_self hg0]`. Establish `hfix` using `weil_fix_root h s _ hr`. Establish `e : (s : G M Ω) ((s' : G M Ω) π) = (s : G M Ω) (((s' : G M Ω) π / π) * π)`. Rewrite using `[div_mul_cancel₀ _ hπ0]`.

Rewrite using `[e, map_mul, hfix]`. Clear denominators, using `}` for the nonvanishing conditions. Establish `hf : ∀ s s' : Weil h, f s = f s' → (s : G M Ω) π = (s' : G M Ω) π` using `fun s s' hss => by`. Use `congrArg (fun z : rootsOfUnity (normV v - 1) Ω => ((z : Ωˣ) : Ω)) hss` as an intermediate fact. Simplify using `only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0] at this`.

Conclude with `(div_left_inj' hπ0).1 this`. Set `d` to `Nat.card (rootsOfUnity (normV v - 1) Ω)`. Establish `hd : 0 < d` using `Nat.card_pos`. Establish `: NeZero d` using `⟨hd.ne'⟩`. Set `e : rootsOfUnity (normV v - 1) Ω ≃* rootsOfUnity d ℂ` to `mulEquivOfCyclicCardEq (Complex.card_rootsOfUnity d).symm`.

Set `η : Weil h →* ℂˣ` to `(rootsOfUnity d ℂ).subtype.comp (e.toMonoidHom.comp f)`. Establish `hη : ∀ s s' : Weil h, η s = η s' → (s : G M Ω) π = (s' : G M Ω) π` using `fun s s' hss => hf s s' (e.injective (Subtype.ext hss))`. Establish `hπi : IsIntegral M π` using `Algebra.IsIntegral.isIntegral π`. Establish `: FiniteDimensional M (IntermediateField.adjoin M ({π} : Set Ω))` using `IntermediateField.adjoin.finiteDimensional hπi`. Establish `hηs : IsSmooth η`.

Set `H1 : Subgroup (Ine (F` to `M) A) := (IntermediateField.adjoin M ({π} : Set Ω)).fixingSubgroup.comap (Ine (F := M) A).subtype`. Establish `hH1 : IsOpen (H1 : Set (Ine (F` using `M) A)) := (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val`. Establish `hle : H1 ≤ (η.comp (ineIncl h)).ker` using `fun σ hσ => by`. Establish `hσπ : (σ : G M Ω) π = π` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ π (IntermediateField.mem_adjoin_simple_self _ _)`. Establish `h1 : f (ineIncl h σ) = 1`.

Use `ext`. Simplify using `[f, hσπ, div_self hπ0]`. Use `show η (ineIncl h σ) = 1`. Simplify using `[η, h1]`. Conclude with `Subgroup.isOpen_mono hle hH1`.

Take `⟨χ, -, hχ⟩` from `ha.factor η hηs`. Take `⟨art, hart⟩` from `hA M Ω`. Establish `hπ' : π ^ (normV v - 1) = algebraMap M Ω (((g : ℕ) : 𝓞 M) : M)` using `by rw [hπ]; simp`. Take `⟨σ, hσI, hσab, hσπ⟩` from `GlobalTheory.TameRecip.exists_ine_of_unit hA M Ω art hart v A h ((g : ℕ) : 𝓞 M) hg1 hg2 π hπ' (a (ineIncl h t)) x (GlobalTheory.ArtinInertia.isUnitAt_artin_ine h a ha t) hx`. Set `σ' : Ine (F` to `M) A := ⟨σ, hσI⟩`.

Establish `e1 : art (localIdele M v (a (ineIncl h σ'))) = art (localIdele M v (a (ineIncl h t)))`. Rewrite using `[ha.glob art hart, ha.glob art hart]`. Conclude with `hσab.trans (ha.glob art hart (ineIncl h t))`. Establish `e2 : a (ineIncl h σ') = a (ineIncl h t)` using `GlobalTheory.T.globalArtin_localIdele_injective hC M Ω art hart v e1`. Establish `e3 : η (ineIncl h σ') = η (ineIncl h t)`.

Rewrite using `[hχ, MonoidHom.comp_apply, MonoidHom.comp_apply, e2]`. Establish `e4` using `hη _ _ e3`. Establish `e5 : (t : G M Ω) π = σ π` using `e4.symm`. Rewrite using `[e5]`. Conclude with `hσπ`.
-/
theorem lTameRec : LTameRec := by
  intro hA hC M Ω _ _ _ _ _ _ g _ A v h hg1 hg2 a ha π hπ t x hx
  classical
  have hq : 1 < normV v := one_lt_normV v
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap M Ω).injective
  have : NeZero (normV v - 1) := ⟨by omega⟩
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hπ
    exact hg0 hπ.symm

  let f : Weil h →* rootsOfUnity (normV v - 1) Ω :=
    { toFun := fun s => ⟨Units.mk0 ((s : G M Ω) π / π) (div_ne_zero ((_root_.map_ne_zero _).2 hπ0) hπ0), by
          rw [mem_rootsOfUnity]
          ext
          simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
          rw [div_pow, ← map_pow, hπ, map_natCast, div_self hg0]⟩
      map_one' := by
        ext
        simp [div_self hπ0]
      map_mul' := fun s s' => by
        ext
        simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, Subgroup.coe_mul, AlgEquiv.mul_apply]
        have hr : (((s' : G M Ω) π / π)) ^ (normV v - 1) = 1 := by
          rw [div_pow, ← map_pow, hπ, map_natCast, div_self hg0]
        have hfix := weil_fix_root h s _ hr
        have e : (s : G M Ω) ((s' : G M Ω) π) = (s : G M Ω) (((s' : G M Ω) π / π) * π) := by
          rw [div_mul_cancel₀ _ hπ0]
        rw [e, map_mul, hfix]
        field_simp }
  have hf : ∀ s s' : Weil h, f s = f s' → (s : G M Ω) π = (s' : G M Ω) π := fun s s' hss => by
    have := congrArg (fun z : rootsOfUnity (normV v - 1) Ω => ((z : Ωˣ) : Ω)) hss
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0] at this
    exact (div_left_inj' hπ0).1 this
  let d := Nat.card (rootsOfUnity (normV v - 1) Ω)
  have hd : 0 < d := Nat.card_pos
  have : NeZero d := ⟨hd.ne'⟩
  let e : rootsOfUnity (normV v - 1) Ω ≃* rootsOfUnity d ℂ :=
    mulEquivOfCyclicCardEq (Complex.card_rootsOfUnity d).symm
  let η : Weil h →* ℂˣ := (rootsOfUnity d ℂ).subtype.comp (e.toMonoidHom.comp f)
  have hη : ∀ s s' : Weil h, η s = η s' → (s : G M Ω) π = (s' : G M Ω) π := fun s s' hss =>
    hf s s' (e.injective (Subtype.ext hss))

  have hπi : IsIntegral M π := Algebra.IsIntegral.isIntegral π
  have : FiniteDimensional M (IntermediateField.adjoin M ({π} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional hπi
  have hηs : IsSmooth η := by
    let H1 : Subgroup (Ine (F := M) A) :=
      (IntermediateField.adjoin M ({π} : Set Ω)).fixingSubgroup.comap (Ine (F := M) A).subtype
    have hH1 : IsOpen (H1 : Set (Ine (F := M) A)) :=
      (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val
    have hle : H1 ≤ (η.comp (ineIncl h)).ker := fun σ hσ => by
      have hσπ : (σ : G M Ω) π = π :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ π (IntermediateField.mem_adjoin_simple_self _ _)
      have h1 : f (ineIncl h σ) = 1 := by
        ext
        simp [f, hσπ, div_self hπ0]
      show η (ineIncl h σ) = 1
      simp [η, h1]
    exact Subgroup.isOpen_mono hle hH1
  obtain ⟨χ, -, hχ⟩ := ha.factor η hηs

  obtain ⟨art, hart⟩ := hA M Ω
  have hπ' : π ^ (normV v - 1) = algebraMap M Ω (((g : ℕ) : 𝓞 M) : M) := by rw [hπ]; simp
  obtain ⟨σ, hσI, hσab, hσπ⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hA M Ω art hart v A h ((g : ℕ) : 𝓞 M) hg1 hg2 π
    hπ' (a (ineIncl h t)) x (GlobalTheory.ArtinInertia.isUnitAt_artin_ine h a ha t) hx
  let σ' : Ine (F := M) A := ⟨σ, hσI⟩
  have e1 : art (localIdele M v (a (ineIncl h σ'))) = art (localIdele M v (a (ineIncl h t))) := by
    rw [ha.glob art hart, ha.glob art hart]
    exact hσab.trans (ha.glob art hart (ineIncl h t))
  have e2 : a (ineIncl h σ') = a (ineIncl h t) := GlobalTheory.T.globalArtin_localIdele_injective hC M Ω art hart v e1
  have e3 : η (ineIncl h σ') = η (ineIncl h t) := by
    rw [hχ, MonoidHom.comp_apply, MonoidHom.comp_apply, e2]
  have e4 := hη _ _ e3
  have e5 : (t : G M Ω) π = σ π := e4.symm
  rw [e5]
  exact hσπ

end DiscreteGroups.sglob.DzType

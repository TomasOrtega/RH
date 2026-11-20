import Formalism.SatakeDualWeyl.StatementE
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.UG.P

open Formalism.UG

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Introduce `h0`. Substitute `h0` using the available equality. Unfold `IsUnifV at h`. Apply the tactic sequence `first | simp at h | done`.
-/
theorem satake_unif_ne_zero {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ϖ ≠ 0 := by
  intro h0
  subst h0
  unfold IsUnifV at h
  first | simp at h | done

/- English proof (translation)
Consider the cases of `x using WithZero.recZeroCoe with`. Consider the case `zero => exact WithZero.zero_le _`. Consider the case `coe a`. Establish `h1 : a < 1` using `by exact_mod_cast hx`. Establish `h2 : a ≤ Multiplicative.ofAdd (-1 : ℤ)`.

Express the relevant statement in the definitionally equal form `Multiplicative.toAdd a ≤ -1`. Establish `h3 : Multiplicative.toAdd a < 0` using `h1`. Use linear arithmetic over natural numbers and integers. Conclude with `WithZero.coe_le_coe.mpr h2`.
-/
theorem satake_lt_one_le {x : WithZero (Multiplicative ℤ)} (hx : x < 1) :
    x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  cases x using WithZero.recZeroCoe with
  | zero => exact WithZero.zero_le _
  | coe a =>
    have h1 : a < 1 := by exact_mod_cast hx
    have h2 : a ≤ Multiplicative.ofAdd (-1 : ℤ) := by
      change Multiplicative.toAdd a ≤ -1
      have h3 : Multiplicative.toAdd a < 0 := h1
      omega
    exact WithZero.coe_le_coe.mpr h2

/- English proof (translation)
Unfold `Ov`. Use `first`. Consider the case `exact Iff.rfl`. Consider the case `exact mem_adicCompletionIntegers`. Consider the case `simp [mem_adicCompletionIntegers]`.
-/
private theorem mem_Ov_iff' (x : v.adicCompletion F) : x ∈ Ov F v ↔ Valued.v x ≤ 1 := by
  unfold Ov
  first
    | exact Iff.rfl
    | exact mem_adicCompletionIntegers
    | simp [mem_adicCompletionIntegers]

/- English proof (translation)
Unfold `IsUnifV at h`. Introduce `hm`. Establish `hm' : Valued.v ϖ⁻¹ ≤ 1` using `(mem_Ov_iff' v _).mp hm`. Rewrite `hm'` using `[map_inv₀, h]`. Establish `h4 : ((Multiplicative.ofAdd (-1 : ℤ))⁻¹ : Multiplicative ℤ) ≤ 1`.

Rewrite using `[← WithZero.coe_le_coe, WithZero.coe_inv]`. Apply the tactic sequence `first | exact_mod_cast hm' | simpa using hm'`. Establish `h5 : Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : ℤ))⁻¹) ≤ Multiplicative.toAdd (1 : Multiplicative ℤ)` using `h4`. Simplify using `at h5`.
-/
theorem satake_unif_inv_not_mem {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ϖ⁻¹ ∉ Ov F v := by
  unfold IsUnifV at h
  intro hm
  have hm' : Valued.v ϖ⁻¹ ≤ 1 := (mem_Ov_iff' v _).mp hm
  rw [map_inv₀, h] at hm'
  have h4 : ((Multiplicative.ofAdd (-1 : ℤ))⁻¹ : Multiplicative ℤ) ≤ 1 := by
    rw [← WithZero.coe_le_coe, WithZero.coe_inv]
    first | exact_mod_cast hm' | simpa using hm'
  have h5 : Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : ℤ))⁻¹) ≤ Multiplicative.toAdd (1 : Multiplicative ℤ) := h4
  simp at h5

/- English proof (translation)
Establish `h0` using `satake_unif_ne_zero v h`. Rewrite using `[Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Establish `hz : Valued.v ((z : Ov F v) : v.adicCompletion F) ≤ 1` using `z.2`.

Use `show Valued.v ((z : v.adicCompletion F) * ϖ) < 1`. Rewrite using `[Valuation.map_mul, h]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_mul, ← WithZero.coe_one, WithZero.coe_lt_coe]`. Use `show (-1 : ℤ) < 0`.

Use linear arithmetic over natural numbers and integers. Introduce `hy`. Establish `hle` using `satake_lt_one_le hy`. Establish `hm : (y : v.adicCompletion F) * ϖ⁻¹ ∈ Ov F v` using `by show Valued.v ((y : v.adicCompletion F) * ϖ⁻¹) ≤ 1`. Rewrite using `[Valuation.map_mul, Valuation.map_inv, h]`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨⟨_, hm⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (y : v.adicCompletion F) * ϖ⁻¹ * ϖ = y`. Clear the denominators using the available nonvanishing facts.
-/
theorem satake_mem_span_iff {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (h : IsUnifV F v ϖ)
    (y : Ov F v) : y ∈ Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)} ↔ Valued.v (y : v.adicCompletion F) < 1 := by
  have h0 := satake_unif_ne_zero v h
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : Valued.v ((z : Ov F v) : v.adicCompletion F) ≤ 1 := z.2
    show Valued.v ((z : v.adicCompletion F) * ϖ) < 1
    rw [Valuation.map_mul, h]
    calc Valued.v (z : v.adicCompletion F) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ < 1 := by
          rw [one_mul, ← WithZero.coe_one, WithZero.coe_lt_coe]
          show (-1 : ℤ) < 0
          omega
  · intro hy
    have hle := satake_lt_one_le hy
    have hm : (y : v.adicCompletion F) * ϖ⁻¹ ∈ Ov F v := by
      show Valued.v ((y : v.adicCompletion F) * ϖ⁻¹) ≤ 1
      rw [Valuation.map_mul, Valuation.map_inv, h]
      calc Valued.v (y : v.adicCompletion F) * (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))⁻¹
          ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) *
              (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))⁻¹ :=
            by gcongr
        _ = 1 := mul_inv_cancel₀ WithZero.coe_ne_zero
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    show (y : v.adicCompletion F) * ϖ⁻¹ * ϖ = y
    field_simp

def satakeIota : 𝓞 F →+* Ov F v := algebraMap (𝓞 F) (v.adicCompletionIntegers F)

/- English proof (translation)
Apply the tactic sequence `first | rfl | simp [satakeIota] | (unfold satakeIota Ov; done)`.
-/
theorem satakeIota_coe (r : 𝓞 F) :
    ((satakeIota v r : Ov F v) : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) r := by first | rfl | simp [satakeIota] | (unfold satakeIota Ov; done)

/- English proof (translation)
Use `set I := Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)}`. Set `φ : 𝓞 F →+* Ov F v ⧸ I` to `(Ideal.Quotient.mk I).comp (satakeIota v)`. Establish `hker : ∀ r ∈ v.asIdeal, φ r = 0`. Introduce `r hr`. Simplify using `only [φ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]`.

Rewrite using `[satake_mem_span_iff v hϖ h]`. Unfold `satakeIota`. Rewrite using `[algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := F) (v := v), valuation_of_algebraMap]`. Conclude with `(intValuation_lt_one_iff_mem v r).2 hr`. Use `v.isMaximal` as an intermediate fact.

Set `_` to `Ideal.Quotient.field v.asIdeal`. Set `ψ` to `Ideal.Quotient.lift v.asIdeal φ hker`. Establish `hne : I ≠ ⊤`. Introduce `htop`. Establish `h1 : (1 : Ov F v) ∈ I` using `htop ▸ Submodule.mem_top`.

Rewrite `h1` using `[satake_mem_span_iff v hϖ h]`. Simplify using `at h1`. Establish `: Nontrivial (Ov F v ⧸ I)` using `Ideal.Quotient.nontrivial_iff.2 hne`. Establish `hinj : Function.Injective ψ` using `RingHom.injective ψ`. Establish `hsurj : Function.Surjective ψ`.

Introduce `y`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨r, hr⟩` from `glint_exists_approx v x`. Use `⟨Ideal.Quotient.mk _ r, ?_⟩` and prove the remaining obligations. Use `show φ r = _`.

Simplify using `only [φ, RingHom.comp_apply]`. Rewrite using `[Ideal.Quotient.eq, satake_mem_span_iff v hϖ h]`. Establish `e : ((satakeIota v r - x : Ov F v) : v.adicCompletion F) = -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r)`. Rewrite using `[AddSubgroupClass.coe_sub, satakeIota_coe, neg_sub]`. Rewrite using `[e, Valuation.map_neg]`.

Conclude with `hr`. Rewrite using `[← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)]`. Unfold `qV`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem satake_card_res {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (h : IsUnifV F v ϖ) :
    Nat.card (Ov F v ⧸ Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)}) = qV F v := by
  set I := Ideal.span {(⟨ϖ, hϖ⟩ : Ov F v)}
  let φ : 𝓞 F →+* Ov F v ⧸ I := (Ideal.Quotient.mk I).comp (satakeIota v)
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    rw [satake_mem_span_iff v hϖ h]
    unfold satakeIota
    rw [algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := F) (v := v),
      valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem v r).2 hr
  have := v.isMaximal
  let _ := Ideal.Quotient.field v.asIdeal
  let ψ := Ideal.Quotient.lift v.asIdeal φ hker
  have hne : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : Ov F v) ∈ I := htop ▸ Submodule.mem_top
    rw [satake_mem_span_iff v hϖ h] at h1
    simp at h1
  have : Nontrivial (Ov F v ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hne
  have hinj : Function.Injective ψ := RingHom.injective ψ
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    show φ r = _
    simp only [φ, RingHom.comp_apply]
    rw [Ideal.Quotient.eq, satake_mem_span_iff v hϖ h]
    have e : ((satakeIota v r - x : Ov F v) : v.adicCompletion F) =
        -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, satakeIota_coe, neg_sub]
    rw [e, Valuation.map_neg]
    exact hr
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩)]
  unfold qV
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Unfold `ordV IsUnifV at *`. Establish `h0 : Valued.v ϖ ≠ 0` using `by rw [h]; exact WithZero.coe_ne_zero`. Rewrite using `[dif_neg h0]`. Establish `e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Rewrite using `[WithZero.coe_unzero, h]`.

Rewrite using `[WithZero.coe_injective e]`. Simplify using the standard rewrite rules.
-/
theorem satake_ordV_unif {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ordV F v ϖ = 1 := by
  unfold ordV IsUnifV at *
  have h0 : Valued.v ϖ ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  rw [dif_neg h0]
  have e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_unzero, h]
  rw [WithZero.coe_injective e]
  simp

/- English proof (translation)
Unfold `ordV`. Establish `h0 : Valued.v (1 : v.adicCompletion F) ≠ 0` using `by simp`. Rewrite using `[dif_neg h0]`. Establish `e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Rewrite using `[WithZero.coe_unzero, map_one, WithZero.coe_one]`.

Rewrite using `[WithZero.coe_injective e]`. Simplify using the standard rewrite rules.
-/
theorem satake_ordV_one : ordV F v 1 = 0 := by
  unfold ordV
  have h0 : Valued.v (1 : v.adicCompletion F) ≠ 0 := by simp
  rw [dif_neg h0]
  have e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [WithZero.coe_injective e]
  simp

/- English proof (translation)
Unfold `qV`. Establish `h1 : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `h2 : Ideal.absNorm v.asIdeal ≠ 1`.

Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`. Conclude with `v.isPrime.ne_top`. Use linear arithmetic over natural numbers and integers.
-/
theorem satake_two_le_qV : 2 ≤ qV F v := by
  unfold qV
  have h1 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h2 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

end Formalism.UG.P

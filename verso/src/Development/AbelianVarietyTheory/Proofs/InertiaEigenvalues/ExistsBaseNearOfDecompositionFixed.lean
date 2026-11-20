import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraMapSubEqSumConjugatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlacesOfSamePrimeBelowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrtApproxIntegralStatement

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise

namespace GlobalTheory

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h z hz r hr`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Establish `hint : ∀ x : Ω, IsIntegral ℤ x → A.valuation x ≤ 1` using `fun x hx => (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A hx)`. Establish `halg : ∀ x : Ω, IsAlgebraic ℤ x` using `fun x => by`. Establish `: IsIntegral ℚ x` using `isIntegral_trans (R := ℚ) (A := E) x (Algebra.IsIntegral.isIntegral x)`.

Conclude with `(IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr this.isAlgebraic`. Take `⟨b, hb0, hbz⟩` from `(halg z).exists_integral_multiple`. Take `⟨b', hb'0, hb'r⟩` from `(halg r⁻¹).exists_integral_multiple`. Use `set m : ℕ := Ideal.absNorm w.asIdeal with hm`. Establish `hm0 : m ≠ 0`.

Rewrite using `[hm, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `w.ne_bot`. Establish `hmA : A.valuation (m : Ω) < 1`. Establish `h1` using `(h ((m : ℕ) : 𝓞 E)).mpr (Ideal.absNorm_mem w.asIdeal)`. Simplify using `using h1`.

Establish `hbv : A.valuation (b : Ω) ≠ 0` using `by simpa using hb0`. Establish `hrv : A.valuation r ≠ 0` using `by simpa using hr`. Establish `hb'v : A.valuation (b' : Ω) ≤ A.valuation r`. Establish `h1` using `hint _ hb'r`. Rewrite `h1` using `[zsmul_eq_mul, Valuation.map_mul, map_inv₀]`.

Use `mul_le_mul_left h1 (A.valuation r)` as an intermediate fact. Rewrite `this` using `[mul_assoc, inv_mul_cancel₀ hrv, mul_one, one_mul]`. Then use the resulting hypothesis. Use `set c : ℕ := b'.natAbs * b.natAbs * m with hc`. Establish `hc0 : c ≠ 0`. Rewrite using `[hc]`.

Conclude with `mul_ne_zero (mul_ne_zero (Int.natAbs_ne_zero.mpr hb'0) (Int.natAbs_ne_zero.mpr hb0)) hm0`. Establish `hnat : ∀ n : ℤ, A.valuation ((n.natAbs : ℕ) : Ω) = A.valuation (n : Ω)`. Introduce `n`. Break down `Int.natAbs_eq n with e | e` into its components or cases. Use `conv_rhs => rw [e]`.

Simplify using the standard rewrite rules. Use `conv_rhs => rw [e]`. Simplify using the standard rewrite rules. Establish `hcv : A.valuation (c : Ω) < A.valuation r * A.valuation (b : Ω)`. Rewrite using `[hc, Nat.cast_mul, Nat.cast_mul, Valuation.map_mul, Valuation.map_mul, hnat, hnat]`.

Establish `h1 : A.valuation (b' : Ω) * A.valuation (b : Ω) ≤ A.valuation r * A.valuation (b : Ω)` using `mul_le_mul_left hb'v _`. Establish `hpos : 0 < A.valuation (b' : Ω) * A.valuation (b : Ω)`. Rewrite using `[zero_lt_iff, ← Valuation.map_mul]`. Simplify using `using ⟨hb'0, hb0⟩`. Combine the equalities or inequalities in the displayed calculation.

Establish `hbz' : IsIntegral ℤ ((b : Ω) * z)` using `by rwa [zsmul_eq_mul] at hbz`. Establish `key : ∀ x u : Ω, A.valuation x ≤ A.valuation (c : Ω) → IsIntegral ℤ ((b : Ω) * u) → A.valuation (x * u) < A.valuation r`. Introduce `x u hx hu`. Use `lt_of_mul_lt_mul_right' (a := A.valuation (b : Ω)) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Valuation.map_mul, Valuation.map_mul, mul_assoc, mul_comm (A.valuation u)]`. Use `_ ≤ A.valuation (c : Ω) * 1 := mul_le_mul' hx (hint _ hu)`. Use `_ < A.valuation r * A.valuation (b : Ω) := by rw [mul_one]; exact hcv`. Use `set K := IntermediateField.adjoin E ({z} : Set Ω) with hK`. Use `haveI : FiniteDimensional E K := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)`.

Establish `hzK : z ∈ K` using `IntermediateField.mem_adjoin_simple_self E z`. Establish `hfix : ∀ σ : G E Ω, σ z = z → ∀ x ∈ K, σ x = x`. Introduce `σ hσ x hx`. Establish `e1 : ((σ : Ω →ₐ[E] Ω).comp K.val) = K.val` using `IntermediateField.adjoin_algHom_ext E (fun y hy => by`. Rewrite `hy` using `[Set.mem_singleton_iff]`.

Substitute `hy` using the available equality. Simplify using `using hσ)`. Simplify using `using congrArg (fun φ : K →ₐ[E] Ω => φ ⟨x, hx⟩) e1`. Establish `hsame : ∀ σ : G E Ω, (∀ x ∈ K, IsIntegral ℤ x → (A.valuation (σ x) < 1 ↔ A.valuation x < 1)) → σ z = z`. Introduce `σ hall`.

Take `⟨ρ, hρK, hρ⟩` from `GlobalTheory.T.exists_conj_valuationSubring_of_same_below E Ω K A (σ⁻¹ • A) (fun x hx hxi => by`. Rewrite using `[smul_valuation_lt_one_iff, inv_inv]`. Conclude with `(hall x hx hxi).symm)`. Establish `hD : σ * ρ ∈ Dec (F` using `E) A := by`. Rewrite using `[mem_Dec, mul_smul, hρ, smul_inv_smul]`.

Use `hz _ hD` as an intermediate fact. Rewrite `this` using `[AlgEquiv.mul_apply, hρK z hzK]`. Conclude with `this`. Take `⟨t, htK, htint, ht1, htσ⟩` from `GlobalTheory.T.exists_integral_near_one_small_off_decomposition E Ω K A c hc0`. Take `⟨e, s, hs, he⟩` from `GlobalTheory.T.exists_algebraMap_sub_eq_sum_conjugates' E Ω (t * z)`.

Use `⟨e, ?_⟩` and prove the remaining obligations. Establish `hyz : A.valuation (t * z - z) < A.valuation r`. Establish `: t * z - z = (t - 1) * z` using `by ring`. Rewrite using `[this]`. Conclude with `key _ _ ht1 hbz'`.

Establish `hsum : ∀ x ∈ s, A.valuation x < A.valuation r`. Introduce `x hx`. Take `⟨hxy, σ, rfl⟩` from `hs x hx`. Establish `hσz : σ z ≠ z`. Introduce `hσz`.

Apply `hxy` to reduce the goal to its premises. Rewrite using `[map_mul, hfix σ hσz t htK, hσz]`. Establish `hex : ∃ x ∈ K, IsIntegral ℤ x ∧ ¬(A.valuation (σ x) < 1 ↔ A.valuation x < 1)`. Assume the negation of the conclusion as `hne`. Conclude with `hσz (hsame σ (fun x hx hxi => by`.

Assume the negation of the conclusion as `hn`. Conclude with `hne ⟨x, hx, hxi, hn⟩))`. Rewrite using `[map_mul]`. Use `key _ _ (htσ σ hex) ?_` and prove the remaining obligations. Establish `: (b : Ω) * σ z = σ ((b : Ω) * z)` using `by simp`.

Rewrite using `[this]`. Conclude with `hbz'.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)`. Establish `e2 : algebraMap E Ω e - z = (∑ x ∈ s, x) + (t * z - z)` using `by rw [← he]; ring`. Rewrite using `[e2]`. Conclude with `Valuation.map_add_lt _ (Valuation.map_sum_lt _ hrv hsum) hyz`.
-/
theorem exists_base_near_of_dec_fixed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (z : Ω), (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r := by
  intro E Ω _ _ _ _ _ A w h z hz r hr
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hint : ∀ x : Ω, IsIntegral ℤ x → A.valuation x ≤ 1 := fun x hx =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A hx)
  have halg : ∀ x : Ω, IsAlgebraic ℤ x := fun x => by
    have : IsIntegral ℚ x := isIntegral_trans (R := ℚ) (A := E) x (Algebra.IsIntegral.isIntegral x)
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr this.isAlgebraic

  obtain ⟨b, hb0, hbz⟩ := (halg z).exists_integral_multiple

  obtain ⟨b', hb'0, hb'r⟩ := (halg r⁻¹).exists_integral_multiple

  set m : ℕ := Ideal.absNorm w.asIdeal with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hmA : A.valuation (m : Ω) < 1 := by
    have h1 := (h ((m : ℕ) : 𝓞 E)).mpr (Ideal.absNorm_mem w.asIdeal)
    simpa using h1
  have hbv : A.valuation (b : Ω) ≠ 0 := by simpa using hb0
  have hrv : A.valuation r ≠ 0 := by simpa using hr
  have hb'v : A.valuation (b' : Ω) ≤ A.valuation r := by
    have h1 := hint _ hb'r
    rw [zsmul_eq_mul, Valuation.map_mul, map_inv₀] at h1
    have := mul_le_mul_left h1 (A.valuation r)
    rwa [mul_assoc, inv_mul_cancel₀ hrv, mul_one, one_mul] at this
  set c : ℕ := b'.natAbs * b.natAbs * m with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact mul_ne_zero (mul_ne_zero (Int.natAbs_ne_zero.mpr hb'0) (Int.natAbs_ne_zero.mpr hb0)) hm0
  have hnat : ∀ n : ℤ, A.valuation ((n.natAbs : ℕ) : Ω) = A.valuation (n : Ω) := by
    intro n
    rcases Int.natAbs_eq n with e | e
    · conv_rhs => rw [e]
      simp
    · conv_rhs => rw [e]
      simp

  have hcv : A.valuation (c : Ω) < A.valuation r * A.valuation (b : Ω) := by
    rw [hc, Nat.cast_mul, Nat.cast_mul, Valuation.map_mul, Valuation.map_mul, hnat, hnat]
    have h1 : A.valuation (b' : Ω) * A.valuation (b : Ω) ≤ A.valuation r * A.valuation (b : Ω) :=
      mul_le_mul_left hb'v _
    have hpos : 0 < A.valuation (b' : Ω) * A.valuation (b : Ω) := by
      rw [zero_lt_iff, ← Valuation.map_mul]; simpa using ⟨hb'0, hb0⟩
    calc A.valuation (b' : Ω) * A.valuation (b : Ω) * A.valuation (m : Ω)
        < A.valuation (b' : Ω) * A.valuation (b : Ω) * 1 := mul_lt_mul_of_pos_left hmA hpos
      _ ≤ A.valuation r * A.valuation (b : Ω) := by rw [mul_one]; exact h1
  have hbz' : IsIntegral ℤ ((b : Ω) * z) := by rwa [zsmul_eq_mul] at hbz
  have key : ∀ x u : Ω, A.valuation x ≤ A.valuation (c : Ω) → IsIntegral ℤ ((b : Ω) * u) →
      A.valuation (x * u) < A.valuation r := by
    intro x u hx hu
    refine lt_of_mul_lt_mul_right' (a := A.valuation (b : Ω)) ?_
    calc A.valuation (x * u) * A.valuation (b : Ω) = A.valuation x * A.valuation ((b : Ω) * u) := by
          rw [Valuation.map_mul, Valuation.map_mul, mul_assoc, mul_comm (A.valuation u)]
      _ ≤ A.valuation (c : Ω) * 1 := mul_le_mul' hx (hint _ hu)
      _ < A.valuation r * A.valuation (b : Ω) := by rw [mul_one]; exact hcv
  set K := IntermediateField.adjoin E ({z} : Set Ω) with hK
  haveI : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  have hzK : z ∈ K := IntermediateField.mem_adjoin_simple_self E z
  have hfix : ∀ σ : G E Ω, σ z = z → ∀ x ∈ K, σ x = x := by
    intro σ hσ x hx
    have e1 : ((σ : Ω →ₐ[E] Ω).comp K.val) = K.val :=
      IntermediateField.adjoin_algHom_ext E (fun y hy => by
        rw [Set.mem_singleton_iff] at hy; subst hy; simpa using hσ)
    simpa using congrArg (fun φ : K →ₐ[E] Ω => φ ⟨x, hx⟩) e1
  have hsame : ∀ σ : G E Ω, (∀ x ∈ K, IsIntegral ℤ x → (A.valuation (σ x) < 1 ↔ A.valuation x < 1)) →
      σ z = z := by
    intro σ hall
    obtain ⟨ρ, hρK, hρ⟩ := GlobalTheory.T.exists_conj_valuationSubring_of_same_below E Ω K A (σ⁻¹ • A) (fun x hx hxi => by
      rw [smul_valuation_lt_one_iff, inv_inv]; exact (hall x hx hxi).symm)
    have hD : σ * ρ ∈ Dec (F := E) A := by
      rw [mem_Dec, mul_smul, hρ, smul_inv_smul]
    have := hz _ hD
    rw [AlgEquiv.mul_apply, hρK z hzK] at this
    exact this
  obtain ⟨t, htK, htint, ht1, htσ⟩ := GlobalTheory.T.exists_integral_near_one_small_off_decomposition E Ω K A c hc0
  obtain ⟨e, s, hs, he⟩ := GlobalTheory.T.exists_algebraMap_sub_eq_sum_conjugates' E Ω (t * z)
  refine ⟨e, ?_⟩
  have hyz : A.valuation (t * z - z) < A.valuation r := by
    have : t * z - z = (t - 1) * z := by ring
    rw [this]; exact key _ _ ht1 hbz'
  have hsum : ∀ x ∈ s, A.valuation x < A.valuation r := by
    intro x hx
    obtain ⟨hxy, σ, rfl⟩ := hs x hx
    have hσz : σ z ≠ z := by
      intro hσz
      apply hxy
      rw [map_mul, hfix σ hσz t htK, hσz]
    have hex : ∃ x ∈ K, IsIntegral ℤ x ∧ ¬(A.valuation (σ x) < 1 ↔ A.valuation x < 1) := by
      by_contra hne
      exact hσz (hsame σ (fun x hx hxi => by
        by_contra hn
        exact hne ⟨x, hx, hxi, hn⟩))
    rw [map_mul]
    refine key _ _ (htσ σ hex) ?_
    have : (b : Ω) * σ z = σ ((b : Ω) * z) := by simp
    rw [this]
    exact hbz'.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)
  have e2 : algebraMap E Ω e - z = (∑ x ∈ s, x) + (t * z - z) := by rw [← he]; ring
  rw [e2]
  exact Valuation.map_add_lt _ (Valuation.map_sum_lt _ hrv hsum) hyz

end GlobalTheory

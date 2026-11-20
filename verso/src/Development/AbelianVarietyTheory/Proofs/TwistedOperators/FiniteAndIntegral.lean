import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

set_option autoImplicit false

noncomputable section

open IsDedekindDomain IsLocalRing Formalism.L2.Pj

namespace GlobalTheory.CompleteValExt

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Conclude with `⟨fun _ => by simp [vV], fun _ => ⟨0, map_zero _⟩⟩`. Establish `h1` using `WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero`. Rewrite `h1` using `[WithZero.log_one]`.

Establish `h2 : 0 ≤ vV V x ↔ valV V x ≤ 1`. Rewrite using `[← h1]`. Unfold `vV`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h2]`.

Use `⟨?_, fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) h⟩` and prove the remaining obligations. Introduce and unpack `⟨a, rfl⟩`. Conclude with `HeightOneSpectrum.valuation_le_one _ a`.
-/
theorem exists_algebraMap_eq_iff (x : K) : (∃ a : V, algebraMap V K a = x) ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => by simp [vV], fun _ => ⟨0, map_zero _⟩⟩
  have h1 := WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero
  rw [WithZero.log_one] at h1
  have h2 : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
    rw [← h1]
    unfold vV
    omega
  rw [h2]
  refine ⟨?_, fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) h⟩
  rintro ⟨a, rfl⟩
  exact HeightOneSpectrum.valuation_le_one _ a

variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]

/- English proof (translation)
Establish `hint : ∀ a : V, ∃ v : W, algebraMap W L v = i (algebraMap V K a)` using `fun a => (exists_algebraMap_eq_iff _).2 (by`. Rewrite using `[hi]; exact mul_nonneg (by positivity) ((exists_algebraMap_eq_iff _).1 ⟨a, rfl⟩))`. Use `choose g0 hg0 using hint`. Establish `hinj` using `IsFractionRing.injective W L`. Set `g : V →+* W` to `{ toFun := g0 map_one' := hinj (by simp [hg0]) map_mul' := fun a b => hinj (by simp [hg0]) map_zero' := hinj (by simp [hg0]) map_add' := fun a b => hinj (by simp [hg0]) }`.

Establish `hg : ∀ a, algebraMap W L (g a) = i (algebraMap V K a)` using `hg0`. Use `letI : Algebra V W := g.toAlgebra`. Use `letI : Algebra K L := i.toAlgebra`. Use `letI : Algebra V L := (i.comp (algebraMap V K)).toAlgebra`. Establish `: IsScalarTower V W L` using `IsScalarTower.of_algebraMap_eq fun a => (hg a).symm`.

Establish `: IsScalarTower V K L` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hgi : Function.Injective (algebraMap V W)` using `fun a b hab => by`. Apply `IsFractionRing.injective V K` to reduce the goal to its premises. Apply `i.injective` to reduce the goal to its premises. Rewrite using `[← hg, ← hg]`.

Conclude with `congrArg _ hab`. Establish `: FaithfulSMul V W` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hgi`. Establish `hle : (maximalIdeal V).map (algebraMap V W) ≤ maximalIdeal W`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`.

Rewrite using `[Ideal.mem_comap, mem_maximalIdeal]`. Introduce `hu`. Take `⟨b, hb⟩` from `hu.exists_right_inv`. Establish `hb' : i (algebraMap V K a) * algebraMap W L b = 1`. Rewrite using `[← hg, ← map_mul, ← map_one (algebraMap W L)]`.

Conclude with `congrArg _ hb`. Establish `h0 : algebraMap V K a ≠ 0` using `fun h => by`. Rewrite `hb'` using `[h, map_zero, zero_mul]`. Conclude with `zero_ne_one hb'`. Establish `h1 : algebraMap W L b = i (algebraMap V K a)⁻¹`.

Rewrite using `[map_inv₀]`. Conclude with `eq_inv_of_mul_eq_one_right hb'`. Establish `h2` using `(exists_algebraMap_eq_iff (V := W) _).1 ⟨b, h1⟩`. Rewrite `h2` using `[hi]`. Take `⟨c, hc⟩` from `(exists_algebraMap_eq_iff (V := V) _).2 (nonneg_of_mul_nonneg_right h2 (by exact_mod_cast hr))`.

Use `(mem_maximalIdeal a).1 ha (IsUnit.of_mul_eq_one c (IsFractionRing.injective V K ?_))` and prove the remaining obligations. Rewrite using `[map_mul, hc, map_one, mul_inv_cancel₀ h0]`. Establish `hne : (maximalIdeal V).map (algebraMap V W) ≠ ⊥`. Rewrite using `[Ne, Ideal.map_eq_bot_iff_of_injective hgi]`. Conclude with `IsDiscreteValuationRing.not_a_field V`.

Establish `htop : (maximalIdeal V).map (algebraMap V W) ≠ ⊤` using `ne_top_of_le_ne_top (maximalIdeal.isMaximal W).ne_top hle`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Establish `: Finite (W ⧸ maximalIdeal W)` using `h'`. Establish `: Module.Finite V W` using `GlobalTheory.finite_of_forall_prime_mem hϖ.ne_zero (fun P hP h0 => by`. Rewrite using `[eq_maximalIdeal (hP.isMaximal h0)]`.

Conclude with `hϖ.not_isUnit) hne htop`. Use `⟨Module.Finite.of_isLocalization V W (nonZeroDivisors V), fun b => ?_⟩` and prove the remaining obligations. Conclude with `(Algebra.IsIntegral.isIntegral (R := V) b).algebraMap (B := L)`.
-/
theorem finite_and_integral_of_scale [IsAdicComplete (maximalIdeal V) V] (i : K →+* L) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV W (i z) = (r : ℤ) * vV V z) (h' : Finite (ResidueField W)) :
    i.Finite ∧ ∀ b : W, (i.comp (algebraMap V K)).IsIntegralElem (algebraMap W L b) := by
  have hint : ∀ a : V, ∃ v : W, algebraMap W L v = i (algebraMap V K a) := fun a =>
    (exists_algebraMap_eq_iff _).2 (by
      rw [hi]; exact mul_nonneg (by positivity) ((exists_algebraMap_eq_iff _).1 ⟨a, rfl⟩))
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective W L
  let g : V →+* W :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap W L (g a) = i (algebraMap V K a) := hg0
  letI : Algebra V W := g.toAlgebra
  letI : Algebra K L := i.toAlgebra
  letI : Algebra V L := (i.comp (algebraMap V K)).toAlgebra
  have : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hgi : Function.Injective (algebraMap V W) := fun a b hab => by
    apply IsFractionRing.injective V K
    apply i.injective
    rw [← hg, ← hg]
    exact congrArg _ hab
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hgi
  have hle : (maximalIdeal V).map (algebraMap V W) ≤ maximalIdeal W := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : i (algebraMap V K a) * algebraMap W L b = 1 := by
      rw [← hg, ← map_mul, ← map_one (algebraMap W L)]
      exact congrArg _ hb
    have h0 : algebraMap V K a ≠ 0 := fun h => by
      rw [h, map_zero, zero_mul] at hb'
      exact zero_ne_one hb'
    have h1 : algebraMap W L b = i (algebraMap V K a)⁻¹ := by
      rw [map_inv₀]
      exact eq_inv_of_mul_eq_one_right hb'
    have h2 := (exists_algebraMap_eq_iff (V := W) _).1 ⟨b, h1⟩
    rw [hi] at h2
    obtain ⟨c, hc⟩ := (exists_algebraMap_eq_iff (V := V) _).2
      (nonneg_of_mul_nonneg_right h2 (by exact_mod_cast hr))
    refine (mem_maximalIdeal a).1 ha (IsUnit.of_mul_eq_one c (IsFractionRing.injective V K ?_))
    rw [map_mul, hc, map_one, mul_inv_cancel₀ h0]
  have hne : (maximalIdeal V).map (algebraMap V W) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hgi]
    exact IsDiscreteValuationRing.not_a_field V
  have htop : (maximalIdeal V).map (algebraMap V W) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal W).ne_top hle
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have : Finite (W ⧸ maximalIdeal W) := h'
  have : Module.Finite V W := GlobalTheory.finite_of_forall_prime_mem hϖ.ne_zero (fun P hP h0 => by
    rw [eq_maximalIdeal (hP.isMaximal h0)]
    exact hϖ.not_isUnit) hne htop
  refine ⟨Module.Finite.of_isLocalization V W (nonZeroDivisors V), fun b => ?_⟩
  exact (Algebra.IsIntegral.isIntegral (R := V) b).algebraMap (B := L)

/- English proof (translation)
Introduce `T T' i _ hr hi h'` and use `finite_and_integral_of_scale (V := T.V) (W := T'.V) i hr hi h'`.
-/
theorem finite_and_integral : ∀ (T T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r →
    (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → T'.FinRes →
    i.Finite ∧ ∀ b : T'.V, (i.comp (algebraMap T.V T.Fr)).IsIntegralElem (algebraMap T'.V T'.Fr b) :=
  fun T T' i _ hr hi h' => finite_and_integral_of_scale (V := T.V) (W := T'.V) i hr hi h'

end GlobalTheory.CompleteValExt

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

noncomputable section

open GlobalTheory.EtC

namespace GlobalTheory.LocInField

variable {K : Type} [Field K]

def locAt (R : Subring K) (𝔪 : Ideal R) [𝔪.IsPrime] : Subring K where
  carrier := {x | ∃ a s : R, s ∉ 𝔪 ∧ x * s = a}
  zero_mem' := ⟨0, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  one_mem' := ⟨1, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, t, ht, hy⟩
    refine ⟨a * t + b * s, s * t, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs ht, ?_⟩
    push_cast; rw [← hx, ← hy]; ring
  mul_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, t, ht, hy⟩
    refine ⟨a * b, s * t, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs ht, ?_⟩
    push_cast; rw [← hx, ← hy]; ring
  neg_mem' := by
    rintro x ⟨a, s, hs, hx⟩
    refine ⟨-a, s, hs, ?_⟩
    push_cast; rw [← hx]; ring

/- English proof (translation)
Introduce `x hx` and use `⟨⟨x, hx⟩, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩`.
-/
theorem le_locAt (R : Subring K) (𝔪 : Ideal R) [𝔪.IsPrime] : R ≤ locAt R 𝔪 := fun x hx =>
  ⟨⟨x, hx⟩, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩

/- English proof (translation)
Introduce `k K _ _ _ φ R 𝔪 hφ hmax hres hden hic`. Use `haveI : 𝔪.IsPrime := hmax.isPrime`. Establish `hRT` using `le_locAt R 𝔪`. Use `letI : Algebra R (locAt R 𝔪) := (Subring.inclusion hRT).toAlgebra`. Use `haveI : IsScalarTower R (locAt R 𝔪) K := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Establish `hunit : ∀ s : R, s ∉ 𝔪 → IsUnit (algebraMap R (locAt R 𝔪) s)`. Introduce `s hs`. Establish `hs0 : (s : K) ≠ 0` using `fun h => hs (by rw [show s = 0 from Subtype.ext h]; exact zero_mem _)`. Use `isUnit_iff_exists_inv.2 ⟨⟨(s : K)⁻¹, 1, s, hs, by simp [hs0]⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(s : K) * (s : K)⁻¹ = 1`.

Conclude with `mul_inv_cancel₀ hs0`. Use `haveI hloc : IsLocalization 𝔪.primeCompl (locAt R 𝔪) := { map_units := fun s => hunit s s.2 surj := fun t => by`. Take `⟨a, s, hs, h⟩` from `t.2`. Conclude with `⟨(a, ⟨s, hs⟩), Subtype.ext h⟩`. Use `exists_of_eq := fun {x y} h => by`.

Establish `h'` using `congrArg Subtype.val h`. Establish `hxy : x = y` using `Subtype.ext h'`. Conclude with `⟨1, by rw [hxy]⟩ }`. Use `haveI : IsLocalRing (locAt R 𝔪) := IsLocalization.AtPrime.isLocalRing (locAt R 𝔪) 𝔪`. Use `⟨locAt R 𝔪, fun x hx => hRT (hφ hx), ⟨inferInstance, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `p hp hdeg`. Establish `hdeg' : (p.map (algebraMap (locAt R 𝔪) K)).degree ≠ 0`. Rewrite using `[hp.degree_map, Polynomial.degree_eq_natDegree hp.ne_zero]`. Conclude with `hdeg.ne'` after adjusting the coercions. Take `⟨y, hy⟩` from `IsAlgClosed.exists_root _ hdeg'`.

Establish `hyT : IsIntegral (locAt R 𝔪) y` using `⟨p, hp, by rw [← Polynomial.eval_map]; exact hy⟩`. Take `⟨m, hm⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization 𝔪.primeCompl y hyT`. Establish `hmR : m • y ∈ R` using `hic _ hm`. Establish `hmy : m • y = y * ((m : R) : K)`. Rewrite using `[Submonoid.smul_def, Algebra.smul_def, mul_comm]`.

Both sides reduce to the same expression. Establish `hyT' : y ∈ locAt R 𝔪` using `⟨⟨m • y, hmR⟩, m, m.2, hmy.symm⟩`. Use `⟨⟨y, hyT'⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap (locAt R 𝔪) K (p.eval ⟨y, hyT'⟩) = 0`. Rewrite using `[← Polynomial.eval₂_at_apply (algebraMap (locAt R 𝔪) K), ← Polynomial.eval_map]`.

Conclude with `hy`. Introduce `t`. Take `⟨a, s, hs, hts⟩` from `t.2`. Take `⟨c, hc, hac⟩` from `hres a`. Take `⟨e, he, hse⟩` from `hres s`.

Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Apply `hs` to reduce the goal to its premises. Establish `h0 : s - ⟨φ 0, he⟩ = s`. Rewrite using `[sub_eq_self]; exact Subtype.ext (by simp)`.

Rewrite `hse` using `[h0]`. Then use the resulting hypothesis. Establish `hg : φ (c / e) ∈ R` using `hφ ⟨c / e, rfl⟩`. Establish `hge : φ (c / e) * φ e = φ c` using `by rw [← map_mul, div_mul_cancel₀ c he0]`. Use `⟨c / e, hRT hg, ?_⟩` and prove the remaining obligations. Establish `hb : (a - ⟨φ c, hc⟩) - ⟨φ (c / e), hg⟩ * (s - ⟨φ e, he⟩) ∈ 𝔪` using `sub_mem hac (Ideal.mul_mem_left _ _ hse)`.

Establish `key : (t - ⟨φ (c / e), hRT hg⟩) * algebraMap R (locAt R 𝔪) s = algebraMap R (locAt R 𝔪) ((a - ⟨φ c, hc⟩) - ⟨φ (c / e), hg⟩ * (s - ⟨φ e, he⟩))`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((t : K) - φ (c / e)) * (s : K) = ((a : K) - φ c) - φ (c / e) * ((s : K) - φ e)`. Take the linear combination `hts - hge`. Establish `hb'` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff (locAt R 𝔪) 𝔪 _).2 hb`.

Rewrite `hb'` using `[← key]`. Conclude with `(Ideal.IsPrime.mem_or_mem inferInstance hb').resolve_right fun h => (IsLocalRing.mem_maximalIdeal _).1 h (hunit s hs)`. Use `haveI : FaithfulSMul (locAt R 𝔪) K := inferInstance`. Use `IsFractionRing.of_field _ K fun z => ?_` and prove the remaining obligations. Take `⟨d, hd, hdz⟩` from `hden z`.

Establish `hd0 : (d : K) ≠ 0` using `fun h => hd (Subtype.ext h)`. Use `⟨⟨(d : K) * z, hRT hdz⟩, ⟨d, hRT d.2⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z = (d : K) * z / d`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_local_subring : ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] (φ : k →+* K) (R : Subring K) (𝔪 : Ideal R),
    φ.range ≤ R → 𝔪.IsMaximal → (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) →
    (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) → (∀ x : K, IsIntegral R x → x ∈ R) →
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  intro k K _ _ _ φ R 𝔪 hφ hmax hres hden hic
  haveI : 𝔪.IsPrime := hmax.isPrime
  have hRT := le_locAt R 𝔪
  letI : Algebra R (locAt R 𝔪) := (Subring.inclusion hRT).toAlgebra
  haveI : IsScalarTower R (locAt R 𝔪) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hunit : ∀ s : R, s ∉ 𝔪 → IsUnit (algebraMap R (locAt R 𝔪) s) := by
    intro s hs
    have hs0 : (s : K) ≠ 0 := fun h => hs (by rw [show s = 0 from Subtype.ext h]; exact zero_mem _)
    refine isUnit_iff_exists_inv.2 ⟨⟨(s : K)⁻¹, 1, s, hs, by simp [hs0]⟩, Subtype.ext ?_⟩
    change (s : K) * (s : K)⁻¹ = 1
    exact mul_inv_cancel₀ hs0
  haveI hloc : IsLocalization 𝔪.primeCompl (locAt R 𝔪) :=
    { map_units := fun s => hunit s s.2
      surj := fun t => by
        obtain ⟨a, s, hs, h⟩ := t.2
        exact ⟨(a, ⟨s, hs⟩), Subtype.ext h⟩
      exists_of_eq := fun {x y} h => by
        have h' := congrArg Subtype.val h
        have hxy : x = y := Subtype.ext h'
        exact ⟨1, by rw [hxy]⟩ }
  haveI : IsLocalRing (locAt R 𝔪) := IsLocalization.AtPrime.isLocalRing (locAt R 𝔪) 𝔪
  refine ⟨locAt R 𝔪, fun x hx => hRT (hφ hx), ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · intro p hp hdeg
    have hdeg' : (p.map (algebraMap (locAt R 𝔪) K)).degree ≠ 0 := by
      rw [hp.degree_map, Polynomial.degree_eq_natDegree hp.ne_zero]
      exact_mod_cast hdeg.ne'
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg'
    have hyT : IsIntegral (locAt R 𝔪) y := ⟨p, hp, by rw [← Polynomial.eval_map]; exact hy⟩
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization 𝔪.primeCompl y hyT
    have hmR : m • y ∈ R := hic _ hm
    have hmy : m • y = y * ((m : R) : K) := by
      rw [Submonoid.smul_def, Algebra.smul_def, mul_comm]; rfl
    have hyT' : y ∈ locAt R 𝔪 := ⟨⟨m • y, hmR⟩, m, m.2, hmy.symm⟩
    refine ⟨⟨y, hyT'⟩, Subtype.ext ?_⟩
    change algebraMap (locAt R 𝔪) K (p.eval ⟨y, hyT'⟩) = 0
    rw [← Polynomial.eval₂_at_apply (algebraMap (locAt R 𝔪) K), ← Polynomial.eval_map]
    exact hy
  · intro t
    obtain ⟨a, s, hs, hts⟩ := t.2
    obtain ⟨c, hc, hac⟩ := hres a
    obtain ⟨e, he, hse⟩ := hres s
    have he0 : e ≠ 0 := by
      rintro rfl
      apply hs
      have h0 : s - ⟨φ 0, he⟩ = s := by
        rw [sub_eq_self]; exact Subtype.ext (by simp)
      rwa [h0] at hse
    have hg : φ (c / e) ∈ R := hφ ⟨c / e, rfl⟩
    have hge : φ (c / e) * φ e = φ c := by rw [← map_mul, div_mul_cancel₀ c he0]
    refine ⟨c / e, hRT hg, ?_⟩
    have hb : (a - ⟨φ c, hc⟩) - ⟨φ (c / e), hg⟩ * (s - ⟨φ e, he⟩) ∈ 𝔪 :=
      sub_mem hac (Ideal.mul_mem_left _ _ hse)
    have key : (t - ⟨φ (c / e), hRT hg⟩) * algebraMap R (locAt R 𝔪) s =
        algebraMap R (locAt R 𝔪) ((a - ⟨φ c, hc⟩) - ⟨φ (c / e), hg⟩ * (s - ⟨φ e, he⟩)) := by
      apply Subtype.ext
      change ((t : K) - φ (c / e)) * (s : K) = ((a : K) - φ c) - φ (c / e) * ((s : K) - φ e)
      linear_combination hts - hge
    have hb' := (IsLocalization.AtPrime.to_map_mem_maximal_iff (locAt R 𝔪) 𝔪 _).2 hb
    rw [← key] at hb'
    exact (Ideal.IsPrime.mem_or_mem inferInstance hb').resolve_right
      fun h => (IsLocalRing.mem_maximalIdeal _).1 h (hunit s hs)
  · haveI : FaithfulSMul (locAt R 𝔪) K := inferInstance
    refine IsFractionRing.of_field _ K fun z => ?_
    obtain ⟨d, hd, hdz⟩ := hden z
    have hd0 : (d : K) ≠ 0 := fun h => hd (Subtype.ext h)
    refine ⟨⟨(d : K) * z, hRT hdz⟩, ⟨d, hRT d.2⟩, ?_⟩
    change z = (d : K) * z / d
    field_simp

end GlobalTheory.LocInField

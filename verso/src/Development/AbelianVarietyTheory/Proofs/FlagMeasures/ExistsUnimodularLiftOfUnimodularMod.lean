import Mathlib

open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Use `haveI : Fintype {p : Ideal R // p ∣ J} := UniqueFactorizationMonoid.fintypeSubtypeDvd J hJ`. Set `ι` to `{p : Ideal R // p.IsMaximal ∧ J ≤ p}`. Use `haveI : Finite ι := Finite.of_injective (fun p : ι => (⟨p.1, Ideal.dvd_iff_le.2 p.2.2⟩ : {p : Ideal R // p ∣ J})) (fun a b hab => Subtype.ext (Subtype.mk.inj hab))`. Establish `hc : Pairwise fun i j : ι => IsCoprime i.1 j.1`. Introduce `i j hij`.

Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Conclude with `Ideal.IsMaximal.coprime_of_ne i.2.1 j.2.1 (fun e => hij (Subtype.ext e))`. Take `⟨s, hs⟩` from `Ideal.pi_quotient_surjective (I := fun i : ι => i.1) hc (fun i => Ideal.Quotient.mk i.1 (if x ∈ i.1 then 1 else 0))`. Use `⟨s, fun p hp hJp hmem => ?_⟩` and prove the remaining obligations. Establish `h1` using `Ideal.Quotient.eq.1 (hs ⟨p, hp, hJp⟩)`.

Distinguish the cases in `hx : x ∈ p`. Simplify using `only [hx, if_true] at h1`. Establish `h2 : n * s ∈ p` using `by simpa using p.sub_mem hmem hx`. Establish `h3 : n ∈ p`. Use `p.sub_mem h2 (p.mul_mem_left n h1)` as an intermediate fact.

Establish `e : n * s - n * (s - 1) = n` using `by ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Conclude with `h p hp hJp h3 hx`. Simplify using `only [hx, if_false, sub_zero] at h1`. Apply `hx` to reduce the goal to its premises.

Simplify using `using p.sub_mem hmem (p.mul_mem_left n h1)`.
-/
theorem exists_add_mul_notMem_of_maximal_ge {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J : Ideal R) (hJ : J ≠ 0) (n x : R)
    (h : ∀ p : Ideal R, p.IsMaximal → J ≤ p → n ∈ p → x ∉ p) :
    ∃ s : R, ∀ p : Ideal R, p.IsMaximal → J ≤ p → x + n * s ∉ p := by
  classical
  haveI : Fintype {p : Ideal R // p ∣ J} := UniqueFactorizationMonoid.fintypeSubtypeDvd J hJ
  let ι := {p : Ideal R // p.IsMaximal ∧ J ≤ p}
  haveI : Finite ι := Finite.of_injective
    (fun p : ι => (⟨p.1, Ideal.dvd_iff_le.2 p.2.2⟩ : {p : Ideal R // p ∣ J}))
    (fun a b hab => Subtype.ext (Subtype.mk.inj hab))
  have hc : Pairwise fun i j : ι => IsCoprime i.1 j.1 := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne i.2.1 j.2.1 (fun e => hij (Subtype.ext e))
  obtain ⟨s, hs⟩ := Ideal.pi_quotient_surjective (I := fun i : ι => i.1) hc
    (fun i => Ideal.Quotient.mk i.1 (if x ∈ i.1 then 1 else 0))
  refine ⟨s, fun p hp hJp hmem => ?_⟩
  have h1 := Ideal.Quotient.eq.1 (hs ⟨p, hp, hJp⟩)
  by_cases hx : x ∈ p
  · simp only [hx, if_true] at h1
    have h2 : n * s ∈ p := by simpa using p.sub_mem hmem hx
    have h3 : n ∈ p := by
      have := p.sub_mem h2 (p.mul_mem_left n h1)
      have e : n * s - n * (s - 1) = n := by ring
      rwa [e] at this
    exact h p hp hJp h3 hx
  · simp only [hx, if_false, sub_zero] at h1
    apply hx
    simpa using p.sub_mem hmem (p.mul_mem_left n h1)

/- English proof (translation)
Introduce `F _ _ b hb n x₀ y₀ hn hy₀ H`. Establish `hnF : (n : F) ≠ 0`. Introduce `e`. Conclude with `hn (RingOfIntegers.ext e)`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht, hy⟩ : ∃ t : F, t ∈ b ∧ y₀ + (n : F) * t ≠ 0 := by`.

Distinguish the cases in `h0 : y₀ = 0`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht, ht0⟩ : ∃ t : F, t ∈ b ∧ t ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hb (FractionalIdeal.eq_zero_iff.2 hcon)`.

Conclude with `⟨t, ht, by rw [h0, zero_add]; exact mul_ne_zero hnF ht0⟩`. Conclude with `⟨0, b.zero_mem, by simpa using h0⟩`. Use `set y := y₀ + (n : F) * t with hydef`. Establish `hyb : y ∈ b`. Establish `h1 : n • t ∈ (b : Submodule (𝓞 F) F)` using `Submodule.smul_mem _ n ht`.

Conclude with `Submodule.add_mem (b : Submodule (𝓞 F) F) hy₀ h1`. Establish `hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y * b⁻¹ ≤ 1`. Rewrite using `[← mul_inv_cancel₀ hb]`. Conclude with `mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 hyb) _`. Take `⟨J, hJ⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle`.

Establish `hJb : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y`. Rewrite using `[hJ, mul_assoc, inv_mul_cancel₀ hb, mul_one]`. Establish `hJ0 : J ≠ 0`. Introduce and unpack `rfl`. Apply `hy` to reduce the goal to its premises.

Rewrite using `[← FractionalIdeal.spanSingleton_eq_zero_iff (S := nonZeroDivisors (𝓞 F)), ← hJb]`. Simplify using the standard rewrite rules. Establish `key : ∀ p : Ideal (𝓞 F), y ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b ↔ J ≤ p`. Introduce `p`. Rewrite using `[← FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.coeIdeal_le_coeIdeal F]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `mul_le_mul_left h b⁻¹` as an intermediate fact. Rewrite `this` using `[mul_assoc, mul_inv_cancel₀ hb, mul_one, ← hJ]`. Then use the resulting hypothesis. Introduce `h`.

Rewrite using `[← hJb]`. Conclude with `mul_le_mul_left h b`. Take `⟨s, hs⟩` from `exists_add_mul_notMem_of_maximal_ge J hJ0 n x₀ (by`. Introduce `p hp hJp hnp hx`. Use `H p hp hnp ⟨hx, ?_⟩` and prove the remaining obligations.

Establish `h1` using `(key p).2 hJp`. Establish `h2 : (n : F) * t ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b` using `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hnp) ht`. Establish `h3` using `Submodule.sub_mem (((p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b : FractionalIdeal _ F) : Submodule (𝓞 F) F) h1 h2`. Establish `e : y - (n : F) * t = y₀` using `by rw [hydef]; ring`. Rewrite `h3` using `[e]`.

Conclude with `h3)`. Conclude with `⟨s, t, ht, fun p hp h => hs p hp ((key p).1 h.2) h.1⟩`.
-/
theorem exists_unimodular_lift_of_unimodular_mod :
    ∀ (F : Type) [Field F] [NumberField F] (b : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), b ≠ 0 → ∀ (n x₀ : 𝓞 F) (y₀ : F), n ≠ 0 → y₀ ∈ b → (∀ p : Ideal (𝓞 F), p.IsMaximal → n ∈ p → ¬ (x₀ ∈ p ∧ y₀ ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b)) → ∃ (s : 𝓞 F) (t : F), t ∈ b ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → ¬ (x₀ + n * s ∈ p ∧ y₀ + (n : F) * t ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b) := by
  intro F _ _ b hb n x₀ y₀ hn hy₀ H
  have hnF : (n : F) ≠ 0 := by
    intro e
    exact hn (RingOfIntegers.ext e)
  obtain ⟨t, ht, hy⟩ : ∃ t : F, t ∈ b ∧ y₀ + (n : F) * t ≠ 0 := by
    by_cases h0 : y₀ = 0
    · obtain ⟨t, ht, ht0⟩ : ∃ t : F, t ∈ b ∧ t ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hb (FractionalIdeal.eq_zero_iff.2 hcon)
      exact ⟨t, ht, by rw [h0, zero_add]; exact mul_ne_zero hnF ht0⟩
    · exact ⟨0, b.zero_mem, by simpa using h0⟩
  set y := y₀ + (n : F) * t with hydef
  have hyb : y ∈ b := by
    have h1 : n • t ∈ (b : Submodule (𝓞 F) F) := Submodule.smul_mem _ n ht
    exact Submodule.add_mem (b : Submodule (𝓞 F) F) hy₀ h1
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y * b⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hb]
    exact mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 hyb) _
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJb : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b
      = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y := by
    rw [hJ, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  have hJ0 : J ≠ 0 := by
    rintro rfl
    apply hy
    rw [← FractionalIdeal.spanSingleton_eq_zero_iff (S := nonZeroDivisors (𝓞 F)), ← hJb]
    simp
  have key : ∀ p : Ideal (𝓞 F),
      y ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b ↔ J ≤ p := by
    intro p
    rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.coeIdeal_le_coeIdeal F]
    constructor
    · intro h
      have := mul_le_mul_left h b⁻¹
      rwa [mul_assoc, mul_inv_cancel₀ hb, mul_one, ← hJ] at this
    · intro h
      rw [← hJb]
      exact mul_le_mul_left h b
  obtain ⟨s, hs⟩ := exists_add_mul_notMem_of_maximal_ge J hJ0 n x₀ (by
    intro p hp hJp hnp hx
    refine H p hp hnp ⟨hx, ?_⟩
    have h1 := (key p).2 hJp
    have h2 : (n : F) * t ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b :=
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hnp) ht
    have h3 := Submodule.sub_mem
      (((p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b : FractionalIdeal _ F) : Submodule (𝓞 F) F) h1 h2
    have e : y - (n : F) * t = y₀ := by rw [hydef]; ring
    rw [e] at h3
    exact h3)
  exact ⟨s, t, ht, fun p hp h => hs p hp ((key p).1 h.2) h.1⟩

end GlobalTheory

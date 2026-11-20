import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralHalf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

namespace GlobalTheory.Mem.Col2.SplitPrime

/- English proof (translation)
Establish `hnot : ¬ (a ∈ P ∧ a' ∈ P)`. Introduce and unpack `⟨h1, h2⟩`. Establish `h3 : (t : A) ∈ P` using `ht ▸ P.add_mem h1 h2`. Take `⟨u, v, huv⟩` from `hc`. Establish `h4 : (u : A) * p + (v : A) * t = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → A) huv`.

Conclude with `hP.ne_top ((Ideal.eq_top_iff_one P).2 (h4 ▸ P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h3)))`. Establish `h5 : a * a' ∈ P` using `hm ▸ P.mul_mem_right _ hp`. Break down `hP.mem_or_mem h5 with h | h` into its components or cases. Conclude with `Or.inl ⟨h, fun h' => hnot ⟨h, h'⟩⟩`. Conclude with `Or.inr ⟨h, fun h' => hnot ⟨h', h⟩⟩`.
-/
theorem mem_xor {A : Type*} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (p t m : ℤ) (hp : (p : A) ∈ P) (a a' : A)
    (hm : a * a' = (p : A) * m) (ht : a + a' = t) (hc : IsCoprime p t) :
    (a ∈ P ∧ a' ∉ P) ∨ (a' ∈ P ∧ a ∉ P) := by
  have hnot : ¬ (a ∈ P ∧ a' ∈ P) := by
    rintro ⟨h1, h2⟩
    have h3 : (t : A) ∈ P := ht ▸ P.add_mem h1 h2
    obtain ⟨u, v, huv⟩ := hc
    have h4 : (u : A) * p + (v : A) * t = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) huv
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (h4 ▸ P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h3)))
  have h5 : a * a' ∈ P := hm ▸ P.mul_mem_right _ hp
  rcases hP.mem_or_mem h5 with h | h
  · exact Or.inl ⟨h, fun h' => hnot ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => hnot ⟨h', h⟩⟩

/- English proof (translation)
Establish `hpr : (Ideal.span {(p : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)`. Take `⟨Q, -, hQ, hQc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥ (by`. Rewrite using `[Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]`. Conclude with `bot_le)`. Establish `hmem : (p : 𝓞 K) ∈ Q`.

Establish `: (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K))` using `hQc ▸ Ideal.mem_span_singleton_self _`. Simplify using `using this`. Use `⟨⟨Q, hQ, ?_⟩, hmem⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `(Nat.cast_ne_zero.2 hp.ne_zero) ((Ideal.mem_bot).1 hmem)`.
-/
theorem exists_over (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal := by
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥ (by
    rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]
    exact bot_le)
  have hmem : (p : 𝓞 K) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQc ▸ Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) ((Ideal.mem_bot).1 hmem)

/- English proof (translation)
Use `set θ : H.K := ⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ with hθ`. Establish `hsq : θ ^ 2 = -(H.d : H.K)` using `Subtype.ext (by simpa [hθ] using H.sqrtMinusD_sq)`. Establish `hcj : HostK.conjK H θ = -θ` using `Subtype.ext (by simpa [hθ, HostK.coe_conjK] using H.conj_sqrtMinusD)`. Distinguish the cases in `h2 : p = 2`. Substitute `h2` using the available equality.

Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 8 * m := by`. Use `H.hyp.2.2.2.1` as an intermediate fact. Conclude with `⟨(H.d + 1) / 8, by omega⟩`. Establish `hm' : (H.d : H.K) + 1 = 8 * m` using `by exact_mod_cast hm`. Use `⟨(1 + θ) / 2, 1, m, HostK.isIntegral_half H, ?_, ?_, isCoprime_one_right⟩` and prove the remaining obligations.

Rewrite using `[map_div₀, map_add, map_one, hcj, map_ofNat]`. Use `push_cast`. Take the linear combination `(-1 / 4 : H.K) * hsq + (1 / 4 : H.K) * hm'`. Rewrite using `[map_div₀, map_add, map_one, hcj, map_ofNat]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hj : jacobiSym (-(H.d : ℤ)) p = 1` using `hs.resolve_left h2 haveI : Fact p.Prime := ⟨hp⟩`. Rewrite `hj` using `[← jacobiSym.legendreSym.to_jacobiSym]`. Establish `hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0`. Introduce `h`.

Rewrite `hj` using `[(legendreSym.eq_zero_iff p _).2 h]`. Conclude with `zero_ne_one hj`. Take `⟨s, hs'⟩` from `(legendreSym.eq_one_iff p hne).1 hj`. Take `⟨r, rfl⟩` from `ZMod.intCast_surjective s`. Establish `hr : ¬ (p : ℤ) ∣ r`.

Introduce `h`. Rewrite `hne` using `[hs', (ZMod.intCast_zmod_eq_zero_iff_dvd r p).2 h]`. Conclude with `hne (mul_zero _)`. Establish `hdiv : (p : ℤ) ∣ r * r + H.d`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Move the coercions through the operations in `at hs' ⊢`. Take the linear combination `-hs'`. Take `⟨m, hm⟩` from `hdiv`. Establish `hm' : (r : H.K) * r + H.d = (p : H.K) * m` using `by exact_mod_cast congrArg (Int.cast : ℤ → H.K) hm`. Establish `hθi : IsIntegral ℤ θ`.

Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Rewrite using `[hsq]`. Conclude with `(isIntegral_natCast H.d).neg`. Establish `hpi : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Use `⟨r + θ, 2 * r, m, (isIntegral_intCast r).add hθi, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_intCast, hcj]`. Take the linear combination `hm' - hsq`. Rewrite using `[map_add, map_intCast, hcj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `(hpi.coprime_iff_not_dvd).2 fun h => ?_` and prove the remaining obligations. Break down `hpi.dvd_or_dvd h with h | h` into its components or cases. Establish `h' : p ∣ 2` using `by exact_mod_cast h`. Conclude with `h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')`. Conclude with `hr h`.
-/
theorem exists_elt {R : Ranks} (H : Host R) (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) :
    ∃ (a : H.K) (t m : ℤ), IsIntegral ℤ a ∧ a * HostK.conjK H a = (p : H.K) * m ∧ a + HostK.conjK H a = t ∧
      IsCoprime (p : ℤ) t := by
  set θ : H.K := ⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ with hθ
  have hsq : θ ^ 2 = -(H.d : H.K) := Subtype.ext (by simpa [hθ] using H.sqrtMinusD_sq)
  have hcj : HostK.conjK H θ = -θ := Subtype.ext (by simpa [hθ, HostK.coe_conjK] using H.conj_sqrtMinusD)
  by_cases h2 : p = 2
  · subst h2
    obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 8 * m := by
      have := H.hyp.2.2.2.1
      exact ⟨(H.d + 1) / 8, by omega⟩
    have hm' : (H.d : H.K) + 1 = 8 * m := by exact_mod_cast hm
    refine ⟨(1 + θ) / 2, 1, m, HostK.isIntegral_half H, ?_, ?_, isCoprime_one_right⟩
    · rw [map_div₀, map_add, map_one, hcj, map_ofNat]
      push_cast
      linear_combination (-1 / 4 : H.K) * hsq + (1 / 4 : H.K) * hm'
    · rw [map_div₀, map_add, map_one, hcj, map_ofNat]
      push_cast
      ring
  · have hj : jacobiSym (-(H.d : ℤ)) p = 1 := hs.resolve_left h2
    haveI : Fact p.Prime := ⟨hp⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
    have hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      intro h
      rw [(legendreSym.eq_zero_iff p _).2 h] at hj
      exact zero_ne_one hj
    obtain ⟨s, hs'⟩ := (legendreSym.eq_one_iff p hne).1 hj
    obtain ⟨r, rfl⟩ := ZMod.intCast_surjective s
    have hr : ¬ (p : ℤ) ∣ r := by
      intro h
      rw [hs', (ZMod.intCast_zmod_eq_zero_iff_dvd r p).2 h] at hne
      exact hne (mul_zero _)
    have hdiv : (p : ℤ) ∣ r * r + H.d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast at hs' ⊢
      linear_combination -hs'
    obtain ⟨m, hm⟩ := hdiv
    have hm' : (r : H.K) * r + H.d = (p : H.K) * m := by exact_mod_cast congrArg (Int.cast : ℤ → H.K) hm
    have hθi : IsIntegral ℤ θ := by
      refine IsIntegral.of_pow two_pos ?_
      rw [hsq]
      exact (isIntegral_natCast H.d).neg
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    refine ⟨r + θ, 2 * r, m, (isIntegral_intCast r).add hθi, ?_, ?_, ?_⟩
    · rw [map_add, map_intCast, hcj]
      linear_combination hm' - hsq
    · rw [map_add, map_intCast, hcj]
      push_cast
      ring
    · refine (hpi.coprime_iff_not_dvd).2 fun h => ?_
      rcases hpi.dvd_or_dvd h with h | h
      · have h' : p ∣ 2 := by exact_mod_cast h
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
      · exact hr h

/- English proof (translation)
Take `⟨a, t, m, hai, hm, ht, hc⟩` from `exists_elt H p hp hs`. Establish `hai' : IsIntegral ℤ (HostK.conjK H a)`. Establish `: HostK.conjK H a = t - a` using `by linear_combination ht`. Rewrite using `[this]`. Conclude with `(isIntegral_intCast t).sub hai`.

Take `⟨𝔭, h𝔭⟩` from `exists_over H.K p hp`. Set `x : 𝓞 H.K` to `⟨a, hai⟩`. Set `y : 𝓞 H.K` to `⟨HostK.conjK H a, hai'⟩`. Establish `hx : (x : H.K) = a` using `rfl`. Establish `hy : (y : H.K) = HostK.conjK H a` using `rfl`.

Establish `h1 : x * y = ((p : ℤ) : 𝓞 H.K) * m`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify `hm` using `[hx, hy]`. Establish `h2 : x + y = t`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Simplify `ht` using `[hx, hy]`. Break down `mem_xor 𝔭.asIdeal 𝔭.isPrime p t m (by exact_mod_cast h𝔭) x y h1 h2 hc with h | h` into its components or cases. Conclude with `⟨𝔭, x, y, h𝔭, h.1, h.2, rfl⟩`. Conclude with `⟨𝔭, y, x, h𝔭, h.1, h.2, by rw [hx, hy, HostK.conjK_conjK]⟩`.
-/
theorem exists_prime_not_conj (R : Ranks) (H : Host R) (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) :
    ∃ (𝔭 : HeightOneSpectrum (𝓞 H.K)) (α β : 𝓞 H.K), (p : 𝓞 H.K) ∈ 𝔭.asIdeal ∧ α ∈ 𝔭.asIdeal ∧ β ∉ 𝔭.asIdeal ∧
      (β : H.K) = HostK.conjK H α := by
  obtain ⟨a, t, m, hai, hm, ht, hc⟩ := exists_elt H p hp hs
  have hai' : IsIntegral ℤ (HostK.conjK H a) := by
    have : HostK.conjK H a = t - a := by linear_combination ht
    rw [this]
    exact (isIntegral_intCast t).sub hai
  obtain ⟨𝔭, h𝔭⟩ := exists_over H.K p hp
  let x : 𝓞 H.K := ⟨a, hai⟩
  let y : 𝓞 H.K := ⟨HostK.conjK H a, hai'⟩
  have hx : (x : H.K) = a := rfl
  have hy : (y : H.K) = HostK.conjK H a := rfl
  have h1 : x * y = ((p : ℤ) : 𝓞 H.K) * m := by
    apply RingOfIntegers.ext
    simpa [hx, hy] using hm
  have h2 : x + y = t := by
    apply RingOfIntegers.ext
    simpa [hx, hy] using ht
  rcases mem_xor 𝔭.asIdeal 𝔭.isPrime p t m (by exact_mod_cast h𝔭) x y h1 h2 hc with h | h
  · exact ⟨𝔭, x, y, h𝔭, h.1, h.2, rfl⟩
  · exact ⟨𝔭, y, x, h𝔭, h.1, h.2, by rw [hx, hy, HostK.conjK_conjK]⟩

end GlobalTheory.Mem.Col2.SplitPrime

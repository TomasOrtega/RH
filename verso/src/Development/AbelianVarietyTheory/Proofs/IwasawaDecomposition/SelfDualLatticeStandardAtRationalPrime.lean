import Mathlib
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ σ n _ _ p 𝔭 α β L t hσ hN hp hp𝔭 hα hβ hβα hL ht h1 h2`. Establish `hint : ∀ x ∈ (algebraMap (𝓞 K) K).range, σ x ∈ (algebraMap (𝓞 K) K).range`. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `: IsIntegral ℤ (σ (algebraMap (𝓞 K) K x))` using `(RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom`. Conclude with `⟨⟨_, this⟩, rfl⟩`.

Take `⟨t', ht'⟩` from `hint (t : K) ⟨t, rfl⟩`. Establish `ht'' : (t' : K) = σ t` using `ht'`. Establish `h1' : ∀ x ∈ L, ∀ j, (t' : K) * x j ∈ (algebraMap (𝓞 K) K).range`. Introduce `x hx j`. Use `(hL x).1 hx _ (h2 j)` as an intermediate fact.

Rewrite `this` using `[Finset.sum_eq_single j (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)]`. Rewrite using `[ht'', mul_comm]`. Simplify `this` using `only [Pi.single_eq_same]`. Establish `h2' : ∀ j, (Pi.single j (t' : K) : n → K) ∈ L`. Introduce `j`.

Rewrite using `[hL]`. Introduce `y hy`. Rewrite using `[Finset.sum_eq_single j (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)]`. Rewrite using `[Pi.single_eq_same, ht'', ← map_mul]`. Conclude with `hint _ (h1 y hy j)`.

Use `set a : 𝓞 K := β * t + α * t' with ha`. Establish `haK : (a : K) = β * t + α * t'` using `by simp [ha]`. Establish `ha𝔭 : a ∉ 𝔭.asIdeal`. Introduce `h`. Establish `h' : β * t ∈ 𝔭.asIdeal`.

Use `𝔭.asIdeal.sub_mem h (𝔭.asIdeal.mul_mem_right t' hα)` as an intermediate fact. Simplify `this` using `[ha]`. Break down `𝔭.isPrime.mem_or_mem h' with h | h` into its components or cases. Conclude with `hβ h`. Conclude with `ht h`.

Establish `hσa : σ a = a`. Rewrite using `[haK, map_add, map_mul, map_mul, hβα, ht'', hσ, hσ]`. Expand and normalize the polynomial expressions, which then agree. Establish `ha1 : ∀ x ∈ L, ∀ j, (a : K) * x j ∈ (algebraMap (𝓞 K) K).range`. Introduce `x hx j`.

Establish `: (a : K) * x j = β * (t * x j) + α * (t' * x j)` using `by rw [haK]; ring`. Rewrite using `[this]`. Conclude with `add_mem (mul_mem ⟨β, rfl⟩ (h1 x hx j)) (mul_mem ⟨α, rfl⟩ (h1' x hx j))`. Establish `ha2 : ∀ j, (Pi.single j (a : K) : n → K) ∈ L`. Introduce `j`.

Establish `: (Pi.single j (a : K) : n → K) = β • (Pi.single j (t : K) : n → K) + α • (Pi.single j (t' : K) : n → K)`. Use extensionality with `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[haK, Algebra.smul_def]`.

Simplify using `[Pi.single_eq_of_ne h]`. Rewrite using `[this]`. Conclude with `add_mem (L.smul_mem _ (h2 j)) (L.smul_mem _ (h2' j))`. Take `⟨m, hm⟩` from `hN a`. Rewrite `hm` using `[hσa]`.

Establish `hmO : a * a = (m : 𝓞 K)`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Simplify using `using hm`. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : ℤ, ((m.natAbs : ℕ) : ℤ) = e * m := by`. Break down `Int.natAbs_eq m with h | h` into its components or cases.

Conclude with `⟨1, by omega⟩`. Conclude with `⟨-1, by omega⟩`. Establish `hs : ((m.natAbs : ℕ) : K) = (e : K) * (a * a)`. Rewrite using `[hm]`. Use `congrArg (Int.cast : ℤ → K) he` as an intermediate fact.

Rewrite `this` using `[Int.cast_natCast, Int.cast_mul]`. Then use the resulting hypothesis. Use `⟨m.natAbs, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.coprime_comm, hp.coprime_iff_not_dvd]`. Introduce `h`. Take `⟨c, hc⟩` from `Int.natCast_dvd.2 h`.

Establish `: a * a ∈ 𝔭.asIdeal`. Rewrite using `[hmO, hc]`. Use `push_cast`. Conclude with `𝔭.asIdeal.mul_mem_right _ hp𝔭`. Apply the tactic sequence `rcases 𝔭.isPrime.mem_or_mem this with h | h <;> exact ha𝔭 h`.

Introduce `x hx i`. Establish `: ((m.natAbs : ℕ) : K) * x i = (e : K) * a * (a * x i)` using `by rw [hs]; ring`. Rewrite using `[this]`. Conclude with `mul_mem (mul_mem (intCast_mem _ e) ⟨a, rfl⟩) (ha1 x hx i)`. Introduce `v hv choose w hw using hv`.

Establish `: ((m.natAbs : ℕ) : K) • v = ∑ j, ((e : 𝓞 K) * w j * a) • (Pi.single j (a : K) : n → K)`. Use extensionality with `i`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single i (by intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]) (by simp)]`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, hs, ← hw i, Algebra.smul_def (_ : 𝓞 K), smul_eq_mul]`. Simplify using `only [map_mul, map_intCast]`.

Express the relevant statement in the definitionally equal form `_ = (e : K) * _ * (a : K) * (a : K)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `L.sum_mem fun j _ => L.smul_mem _ (ha2 j)`.
-/
theorem selfDual_standard_at_rational_prime : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (p : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K) (L : Submodule (𝓞 K) (n → K)) (t : 𝓞 K), (∀ x, σ (σ x) = x) → (∀ x : 𝓞 K, ∃ m : ℤ, (x : K) * σ x = m) → p.Prime → (p : 𝓞 K) ∈ 𝔭.asIdeal → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∑ i, x i * σ (y i) ∈ (algebraMap (𝓞 K) K).range) → t ∉ 𝔭.asIdeal → (∀ x ∈ L, ∀ i, (t : K) * x i ∈ (algebraMap (𝓞 K) K).range) → (∀ j, (Pi.single j (t : K) : n → K) ∈ L) → ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, ∀ i, (s : K) * x i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ v : n → K, (∀ i, v i ∈ (algebraMap (𝓞 K) K).range) → (s : K) • v ∈ L := by
  intro K _ _ σ n _ _ p 𝔭 α β L t hσ hN hp hp𝔭 hα hβ hβα hL ht h1 h2
  have hint : ∀ x ∈ (algebraMap (𝓞 K) K).range, σ x ∈ (algebraMap (𝓞 K) K).range := by
    rintro _ ⟨x, rfl⟩
    have : IsIntegral ℤ (σ (algebraMap (𝓞 K) K x)) :=
      (RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom
    exact ⟨⟨_, this⟩, rfl⟩
  obtain ⟨t', ht'⟩ := hint (t : K) ⟨t, rfl⟩
  have ht'' : (t' : K) = σ t := ht'
  have h1' : ∀ x ∈ L, ∀ j, (t' : K) * x j ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx j
    have := (hL x).1 hx _ (h2 j)
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)] at this
    rw [ht'', mul_comm]
    simpa only [Pi.single_eq_same] using this
  have h2' : ∀ j, (Pi.single j (t' : K) : n → K) ∈ L := by
    intro j
    rw [hL]
    intro y hy
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)]
    rw [Pi.single_eq_same, ht'', ← map_mul]
    exact hint _ (h1 y hy j)
  set a : 𝓞 K := β * t + α * t' with ha
  have haK : (a : K) = β * t + α * t' := by simp [ha]
  have ha𝔭 : a ∉ 𝔭.asIdeal := by
    intro h
    have h' : β * t ∈ 𝔭.asIdeal := by
      have := 𝔭.asIdeal.sub_mem h (𝔭.asIdeal.mul_mem_right t' hα)
      simpa [ha] using this
    rcases 𝔭.isPrime.mem_or_mem h' with h | h
    · exact hβ h
    · exact ht h
  have hσa : σ a = a := by
    rw [haK, map_add, map_mul, map_mul, hβα, ht'', hσ, hσ]
    ring
  have ha1 : ∀ x ∈ L, ∀ j, (a : K) * x j ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx j
    have : (a : K) * x j = β * (t * x j) + α * (t' * x j) := by rw [haK]; ring
    rw [this]
    exact add_mem (mul_mem ⟨β, rfl⟩ (h1 x hx j)) (mul_mem ⟨α, rfl⟩ (h1' x hx j))
  have ha2 : ∀ j, (Pi.single j (a : K) : n → K) ∈ L := by
    intro j
    have : (Pi.single j (a : K) : n → K)
        = β • (Pi.single j (t : K) : n → K) + α • (Pi.single j (t' : K) : n → K) := by
      ext i
      by_cases h : i = j
      · subst h
        simp [haK, Algebra.smul_def]
      · simp [Pi.single_eq_of_ne h]
    rw [this]
    exact add_mem (L.smul_mem _ (h2 j)) (L.smul_mem _ (h2' j))
  obtain ⟨m, hm⟩ := hN a
  rw [hσa] at hm
  have hmO : a * a = (m : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    simpa using hm
  obtain ⟨e, he⟩ : ∃ e : ℤ, ((m.natAbs : ℕ) : ℤ) = e * m := by
    rcases Int.natAbs_eq m with h | h
    · exact ⟨1, by omega⟩
    · exact ⟨-1, by omega⟩
  have hs : ((m.natAbs : ℕ) : K) = (e : K) * (a * a) := by
    rw [hm]
    have := congrArg (Int.cast : ℤ → K) he
    rwa [Int.cast_natCast, Int.cast_mul] at this
  refine ⟨m.natAbs, ?_, ?_, ?_⟩
  · rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    obtain ⟨c, hc⟩ := Int.natCast_dvd.2 h
    have : a * a ∈ 𝔭.asIdeal := by
      rw [hmO, hc]
      push_cast
      exact 𝔭.asIdeal.mul_mem_right _ hp𝔭
    rcases 𝔭.isPrime.mem_or_mem this with h | h <;> exact ha𝔭 h
  · intro x hx i
    have : ((m.natAbs : ℕ) : K) * x i = (e : K) * a * (a * x i) := by rw [hs]; ring
    rw [this]
    exact mul_mem (mul_mem (intCast_mem _ e) ⟨a, rfl⟩) (ha1 x hx i)
  · intro v hv
    choose w hw using hv
    have : ((m.natAbs : ℕ) : K) • v
        = ∑ j, ((e : 𝓞 K) * w j * a) • (Pi.single j (a : K) : n → K) := by
      ext i
      rw [Finset.sum_apply, Finset.sum_eq_single i
        (by intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]) (by simp)]
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, hs, ← hw i, Algebra.smul_def (_ : 𝓞 K),
        smul_eq_mul]
      simp only [map_mul, map_intCast]
      change _ = (e : K) * _ * (a : K) * (a : K)
      ring
    rw [this]
    exact L.sum_mem fun j _ => L.smul_mem _ (ha2 j)

end GlobalTheory

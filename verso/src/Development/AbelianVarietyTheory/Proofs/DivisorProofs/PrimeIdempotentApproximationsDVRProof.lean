import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

open GlobalTheory.IsoTriv

namespace GlobalTheory.IsoTriv.PrimeIdempotent

/- English proof (translation)
Use `set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef`. Distinguish the cases in `ha : a = 0`. Rewrite using `[ha]`. Conclude with `Ideal.zero_mem _`. Establish `hspan : Ideal.span {a} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Take `⟨J, hJ, hfac⟩` from `Ideal.eq_prime_pow_mul_coprime hspan w`. Generalize the expression as in `Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = i at hfac`. Distinguish the cases in `hi : n ≤ i`. Establish `h1 : a ∈ w ^ i * J` using `hfac ▸ Ideal.mem_span_singleton_self a`.

Conclude with `Ideal.pow_le_pow_right hi (Ideal.mul_le_inf h1).1`. It suffices to derive a contradiction. Establish `hJw : ¬ J ≤ w` using `fun h => hw.ne_top (by rw [← hJ, sup_eq_left.mpr h])`. Take `⟨s, hsJ, hsw⟩` from `Set.not_subset.mp hJw`. Establish `hb1 : b ∈ w ^ (i + 1)` using `Ideal.pow_le_pow_right (by omega) hbn`.

Establish `h2 : b * s ∈ Ideal.span {a} * w`. Rewrite using `[hfac, mul_right_comm, ← pow_succ]`. Conclude with `Ideal.mul_mem_mul hb1 hsJ`. Take `⟨m, hm, hm'⟩` from `Ideal.mem_span_singleton_mul.mp h2`. Apply `hsw` to reduce the goal to its premises.

Establish `h3 : φ s = z * φ m`. Apply `mul_left_cancel₀ hb` to reduce the goal to its premises. Rewrite using `[← map_mul, ← hm', map_mul, hz, mul_assoc]`. Express the relevant statement in the definitionally equal form `φ s ∈ IsLocalRing.maximalIdeal V`. Rewrite using `[h3]`.

Conclude with `Ideal.mul_mem_left _ _ hm`.
-/
theorem mem_pow_of_map_dvd {R V : Type} [CommRing R] [IsDedekindDomain R] [CommRing V]
    [IsDomain V] [IsDiscreteValuationRing V] (φ : R →+* V) (b a : R) (hb : φ b ≠ 0) (n : ℕ)
    (hw : (Ideal.comap φ (IsLocalRing.maximalIdeal V)).IsMaximal)
    (hbn : b ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n) (z : V) (hz : φ a = φ b * z) :
    a ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n := by
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  by_cases ha : a = 0
  · rw [ha]; exact Ideal.zero_mem _
  have hspan : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = i
    at hfac
  by_cases hi : n ≤ i
  · have h1 : a ∈ w ^ i * J := hfac ▸ Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_pow_right hi (Ideal.mul_le_inf h1).1
  exfalso
  have hJw : ¬ J ≤ w := fun h => hw.ne_top (by rw [← hJ, sup_eq_left.mpr h])
  obtain ⟨s, hsJ, hsw⟩ := Set.not_subset.mp hJw
  have hb1 : b ∈ w ^ (i + 1) := Ideal.pow_le_pow_right (by omega) hbn
  have h2 : b * s ∈ Ideal.span {a} * w := by
    rw [hfac, mul_right_comm, ← pow_succ]
    exact Ideal.mul_mem_mul hb1 hsJ
  obtain ⟨m, hm, hm'⟩ := Ideal.mem_span_singleton_mul.mp h2
  apply hsw
  have h3 : φ s = z * φ m := by
    apply mul_left_cancel₀ hb
    rw [← map_mul, ← hm', map_mul, hz, mul_assoc]
  change φ s ∈ IsLocalRing.maximalIdeal V
  rw [h3]
  exact Ideal.mul_mem_left _ _ hm

/- English proof (translation)
Introduce `R V _ _ _ _ _ φ q hq hu`. Use `set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef`. Establish `hq0 : q ≠ 0` using `fun h => hq (by rw [h, map_zero])`. Establish `hqw : q ∈ w` using `(IsLocalRing.mem_maximalIdeal _).mpr hu`. Establish `hwp : w.IsPrime` using `Ideal.comap_isPrime φ _`.

Establish `hw0 : w ≠ ⊥` using `fun h => hq0 (by rw [h] at hqw; exact hqw)`. Establish `hw : w.IsMaximal` using `hwp.isMaximal hw0`. Establish `hspan : Ideal.span {q} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Take `⟨J, hJ, hfac⟩` from `Ideal.eq_prime_pow_mul_coprime hspan w`.

Generalize the expression as in `Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {q})) = e at hfac`. Establish `hpow : ∀ M : ℕ, Ideal.span {q ^ M} = w ^ (e * M) * J ^ M` using `fun M => by`. Rewrite using `[← Ideal.span_singleton_pow, hfac, mul_pow, pow_mul]`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Establish `key : ∀ N : ℕ, ∃ y ∈ J ^ N, ∃ z, φ y = 1 + φ q ^ N * z`.

Introduce `N`. Take `⟨k, hk⟩` from `IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero N hq) hϖ`. Establish `hco : w ^ k ⊔ J ^ N = ⊤` using `Ideal.pow_sup_pow_eq_top hJ`. Take `⟨x, hx, y, hy, hxy⟩` from `Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hco)`. Establish `h1 : φ x ∈ Ideal.span {φ q ^ N}`.

Establish `h2 : φ x ∈ (Ideal.map φ w) ^ k`. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem φ hx`. Establish `h3 : φ x ∈ IsLocalRing.maximalIdeal V ^ k` using `Ideal.pow_right_mono Ideal.map_comap_le k h2`. Rewrite `h3` using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]`.

Rewrite using `[Ideal.span_singleton_eq_span_singleton.mpr hk]` and apply the resulting hypothesis. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.mp h1`. Use `⟨y, hy, -c, ?_⟩` and prove the remaining obligations. Establish `h4 : φ x + φ y = 1` using `by rw [← map_add, hxy, map_one]`. Rewrite using `[← h4, hc]`.

Expand and normalize the polynomial expressions, which then agree. Use `choose ε hεJ hε using key`. Use `⟨ε, fun N => ⟨hε N, fun M hM a ⟨z, hz⟩ => ?_⟩⟩` and prove the remaining obligations. Establish `hqM : q ^ M ∈ w ^ (e * M)`. Establish `h1 : q ^ M ∈ w ^ (e * M) * J ^ M` using `hpow M ▸ Ideal.mem_span_singleton_self _`.

Conclude with `(Ideal.mul_le_inf h1).1`. Establish `ha : a ∈ w ^ (e * M)` using `mem_pow_of_map_dvd φ (q ^ M) a (by rw [map_pow]; exact pow_ne_zero M hq) _ hw hqM z (by rw [map_pow]; exact hz)`. Rewrite using `[hpow M, mul_comm (ε N)]`. Conclude with `Ideal.mul_mem_mul ha (Ideal.pow_le_pow_right hM (hεJ N))`.
-/
theorem epsSt : EpsSt := by
  intro R V _ _ _ _ _ φ q hq hu
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  have hq0 : q ≠ 0 := fun h => hq (by rw [h, map_zero])
  have hqw : q ∈ w := (IsLocalRing.mem_maximalIdeal _).mpr hu
  have hwp : w.IsPrime := Ideal.comap_isPrime φ _
  have hw0 : w ≠ ⊥ := fun h => hq0 (by rw [h] at hqw; exact hqw)
  have hw : w.IsMaximal := hwp.isMaximal hw0
  have hspan : Ideal.span {q} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {q})) = e
    at hfac
  have hpow : ∀ M : ℕ, Ideal.span {q ^ M} = w ^ (e * M) * J ^ M := fun M => by
    rw [← Ideal.span_singleton_pow, hfac, mul_pow, pow_mul]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ N : ℕ, ∃ y ∈ J ^ N, ∃ z, φ y = 1 + φ q ^ N * z := by
    intro N
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero N hq) hϖ
    have hco : w ^ k ⊔ J ^ N = ⊤ := Ideal.pow_sup_pow_eq_top hJ
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hco)
    have h1 : φ x ∈ Ideal.span {φ q ^ N} := by
      have h2 : φ x ∈ (Ideal.map φ w) ^ k := by
        rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem φ hx
      have h3 : φ x ∈ IsLocalRing.maximalIdeal V ^ k :=
        Ideal.pow_right_mono Ideal.map_comap_le k h2
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h3
      rwa [Ideal.span_singleton_eq_span_singleton.mpr hk]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h1
    refine ⟨y, hy, -c, ?_⟩
    have h4 : φ x + φ y = 1 := by rw [← map_add, hxy, map_one]
    rw [← h4, hc]; ring
  choose ε hεJ hε using key
  refine ⟨ε, fun N => ⟨hε N, fun M hM a ⟨z, hz⟩ => ?_⟩⟩
  have hqM : q ^ M ∈ w ^ (e * M) := by
    have h1 : q ^ M ∈ w ^ (e * M) * J ^ M := hpow M ▸ Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf h1).1
  have ha : a ∈ w ^ (e * M) :=
    mem_pow_of_map_dvd φ (q ^ M) a (by rw [map_pow]; exact pow_ne_zero M hq) _ hw hqM z
      (by rw [map_pow]; exact hz)
  rw [hpow M, mul_comm (ε N)]
  exact Ideal.mul_mem_mul ha (Ideal.pow_le_pow_right hM (hεJ N))

end GlobalTheory.IsoTriv.PrimeIdempotent

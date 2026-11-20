import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

namespace GlobalTheory.BSP.StrictIndep

variable {S A : Type} [CommRing S] [CommRing A]

/- English proof (translation)
Rewrite using `[← Ideal.span_union, Set.singleton_union]`.
-/
theorem span_sup_span_eq_pair (x y : S) :
    Ideal.span {x} ⊔ Ideal.span {y} = Ideal.span ({x, y} : Set S) := by
  rw [← Ideal.span_union, Set.singleton_union]

/- English proof (translation)
Rewrite using `[Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, span_sup_span_eq_pair]`.
-/
theorem map_span_pair (s : S →+* A) (x y : S) :
    (Ideal.span {x} ⊔ Ideal.span {y}).map s = Ideal.span ({s x, s y} : Set A) := by
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    span_sup_span_eq_pair]

/- English proof (translation)
Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_decomp (s : S →+* A) {ι : Type} (b : ι → A) (T : Finset ι) (u v : ι → S) (P Q : S) :
    ∑ i ∈ T, s (u i * P + v i * Q) * b i
      = s P * ∑ i ∈ T, s (u i) * b i + s Q * ∑ i ∈ T, s (v i) * b i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_add, map_mul]
  ring

/- English proof (translation)
Introduce `i hi`. Establish `key` using `h3 (Finsupp.onFinset T (fun j => if j ∈ T then c j else 0) (by intro j hj; by_contra hn; simp [hn] at hj)) (by`. Rewrite using `[map_span_pair, Finsupp.onFinset_sum _ (by intro j; simp)]`. Use `h using 1` and compare the differences between its conclusion and the goal. Conclude with `Finset.sum_congr rfl (fun j hj => by simp [hj])) i`.

Rewrite `key` using `[span_sup_span_eq_pair]`. Simplify `key` using `[hi]`.
-/
theorem indep_finset (s : S →+* A) (p q : S) {ι : Type} (b : ι → A)
    (h3 : ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q})
    (T : Finset ι) (c : ι → S) (h : ∑ i ∈ T, s (c i) * b i ∈ Ideal.span ({s p, s q} : Set A)) :
    ∀ i ∈ T, c i ∈ Ideal.span ({p, q} : Set S) := by
  classical
  intro i hi
  have key := h3 (Finsupp.onFinset T (fun j => if j ∈ T then c j else 0)
    (by intro j hj; by_contra hn; simp [hn] at hj)) (by
      rw [map_span_pair, Finsupp.onFinset_sum _ (by intro j; simp)]
      convert h using 1
      exact Finset.sum_congr rfl (fun j hj => by simp [hj])) i
  rw [span_sup_span_eq_pair] at key
  simpa [hi] using key

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x h`. Simplify using `using h`. Consider the case `succ n ih`.

Introduce `x h`. Apply `h2` to reduce the goal to its premises. Apply `ih` to reduce the goal to its premises. Rewrite `h` using `[pow_succ, mul_assoc]`. Conclude with `h`.
-/
theorem dvd_of_dvd_pow_mul (s : S →+* A) (p q : S)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x) :
    ∀ (n : ℕ) (x : A), s p ∣ s q ^ n * x → s p ∣ x := by
  intro n
  induction n with
  | zero => intro x h; simpa using h
  | succ n ih =>
    intro x h
    apply h2
    apply ih
    rw [pow_succ, mul_assoc] at h
    exact h

/- English proof (translation)
Establish `base : ∀ x : A, s q ^ n ∣ s p * x → s q ^ n ∣ x`. Introduce and unpack `x ⟨y, hy⟩`. Take `⟨t, ht⟩` from `dvd_of_dvd_pow_mul s p q h2 n y ⟨x, by rw [← hy]⟩`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `h0 : s p * (x - s q ^ n * t) = 0`.

Rewrite using `[mul_sub, hy, ht]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.1 (h1 _ h0)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => intro x h`. Simplify using `using h`. Consider the case `succ m ih`. Introduce `x h`. Apply `base` to reduce the goal to its premises.

Apply `ih` to reduce the goal to its premises. Rewrite `h` using `[pow_succ, mul_assoc]`. Conclude with `h`.
-/
theorem pow_dvd_of_dvd_pow_mul (s : S →+* A) (p q : S)
    (h1 : ∀ x : A, s p * x = 0 → x = 0)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x) (n : ℕ) :
    ∀ (m : ℕ) (x : A), s q ^ n ∣ s p ^ m * x → s q ^ n ∣ x := by
  have base : ∀ x : A, s q ^ n ∣ s p * x → s q ^ n ∣ x := by
    rintro x ⟨y, hy⟩
    obtain ⟨t, ht⟩ := dvd_of_dvd_pow_mul s p q h2 n y ⟨x, by rw [← hy]⟩
    refine ⟨t, ?_⟩
    have h0 : s p * (x - s q ^ n * t) = 0 := by
      rw [mul_sub, hy, ht]; ring
    exact sub_eq_zero.1 (h1 _ h0)
  intro m
  induction m with
  | zero => intro x h; simpa using h
  | succ m ih =>
    intro x h
    apply base
    apply ih
    rw [pow_succ, mul_assoc] at h
    exact h

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `T c _ i _`. Conclude with `Ideal.mem_span_pair.2 ⟨0, c i, by simp⟩`.

Consider the case `succ n ih`. Introduce `T c h`. Take `⟨x, y, hxy⟩` from `Ideal.mem_span_pair.1 h`. Establish `hT : ∀ i ∈ T, c i ∈ Ideal.span ({p, q ^ n} : Set S)` using `ih T c (Ideal.mem_span_pair.2 ⟨x, y * s q, by rw [← hxy]; ring⟩)`. Establish `hex : ∀ i, ∃ u v : S, i ∈ T → u * p + v * q ^ n = c i`.

Introduce `i`. Distinguish the cases in `hi : i ∈ T`. Take `⟨u, v, huv⟩` from `Ideal.mem_span_pair.1 (hT i hi)`. Conclude with `⟨u, v, fun _ => huv⟩`. Conclude with `⟨0, 0, fun h => absurd h hi⟩`.

Use `choose u v huv using hex`. Establish `hsum : ∑ i ∈ T, s (c i) * b i = s p * ∑ i ∈ T, s (u i) * b i + s q ^ n * ∑ i ∈ T, s (v i) * b i`. Rewrite using `[← map_pow, ← sum_decomp]`. Conclude with `Finset.sum_congr rfl fun i hi => by rw [huv i hi]`. Use `set U := ∑ i ∈ T, s (u i) * b i`.

Use `set V := ∑ i ∈ T, s (v i) * b i`. Establish `hd : s p ∣ s q ^ n * (V - y * s q)` using `⟨x - U, by linear_combination -hxy - hsum⟩`. Take `⟨t, ht⟩` from `dvd_of_dvd_pow_mul s p q h2 n _ hd`. Establish `hV : V ∈ Ideal.span ({s p, s q} : Set A)` using `Ideal.mem_span_pair.2 ⟨t, y, by linear_combination -ht⟩`. Introduce `i hi`.

Take `⟨α, β, hαβ⟩` from `Ideal.mem_span_pair.1 (indep_finset s p q b h3 T v hV i hi)`. Use `Ideal.mem_span_pair.2 ⟨u i + α * q ^ n, β, ?_⟩` and prove the remaining obligations. Rewrite using `[← huv i hi, ← hαβ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem step_one (s : S →+* A) (p q : S) {ι : Type} (b : ι → A)
    (h1 : ∀ x : A, s p * x = 0 → x = 0)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x)
    (h3 : ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q}) :
    ∀ (n : ℕ) (T : Finset ι) (c : ι → S),
      ∑ i ∈ T, s (c i) * b i ∈ Ideal.span ({s p, s q ^ n} : Set A) →
      ∀ i ∈ T, c i ∈ Ideal.span ({p, q ^ n} : Set S) := by
  intro n
  induction n with
  | zero =>
    intro T c _ i _
    exact Ideal.mem_span_pair.2 ⟨0, c i, by simp⟩
  | succ n ih =>
    intro T c h
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 h
    have hT : ∀ i ∈ T, c i ∈ Ideal.span ({p, q ^ n} : Set S) :=
      ih T c (Ideal.mem_span_pair.2 ⟨x, y * s q, by rw [← hxy]; ring⟩)
    have hex : ∀ i, ∃ u v : S, i ∈ T → u * p + v * q ^ n = c i := by
      intro i
      by_cases hi : i ∈ T
      · obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hT i hi)
        exact ⟨u, v, fun _ => huv⟩
      · exact ⟨0, 0, fun h => absurd h hi⟩
    choose u v huv using hex
    have hsum : ∑ i ∈ T, s (c i) * b i
        = s p * ∑ i ∈ T, s (u i) * b i + s q ^ n * ∑ i ∈ T, s (v i) * b i := by
      rw [← map_pow, ← sum_decomp]
      exact Finset.sum_congr rfl fun i hi => by rw [huv i hi]
    set U := ∑ i ∈ T, s (u i) * b i
    set V := ∑ i ∈ T, s (v i) * b i
    have hd : s p ∣ s q ^ n * (V - y * s q) :=
      ⟨x - U, by linear_combination -hxy - hsum⟩
    obtain ⟨t, ht⟩ := dvd_of_dvd_pow_mul s p q h2 n _ hd
    have hV : V ∈ Ideal.span ({s p, s q} : Set A) :=
      Ideal.mem_span_pair.2 ⟨t, y, by linear_combination -ht⟩
    intro i hi
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 (indep_finset s p q b h3 T v hV i hi)
    refine Ideal.mem_span_pair.2 ⟨u i + α * q ^ n, β, ?_⟩
    rw [← huv i hi, ← hαβ]
    ring

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `T c _ i _`. Conclude with `Ideal.mem_span_pair.2 ⟨c i, 0, by simp⟩`.

Consider the case `succ m ih`. Introduce `T c h`. Take `⟨x, y, hxy⟩` from `Ideal.mem_span_pair.1 h`. Establish `hT : ∀ i ∈ T, c i ∈ Ideal.span ({p ^ m, q ^ n} : Set S)` using `ih T c (Ideal.mem_span_pair.2 ⟨x * s p, y, by rw [← hxy]; ring⟩)`. Establish `hex : ∀ i, ∃ u v : S, i ∈ T → u * p ^ m + v * q ^ n = c i`.

Introduce `i`. Distinguish the cases in `hi : i ∈ T`. Take `⟨u, v, huv⟩` from `Ideal.mem_span_pair.1 (hT i hi)`. Conclude with `⟨u, v, fun _ => huv⟩`. Conclude with `⟨0, 0, fun h => absurd h hi⟩`.

Use `choose u v huv using hex`. Establish `hsum : ∑ i ∈ T, s (c i) * b i = s p ^ m * ∑ i ∈ T, s (u i) * b i + s q ^ n * ∑ i ∈ T, s (v i) * b i`. Rewrite using `[← map_pow, ← map_pow, ← sum_decomp]`. Conclude with `Finset.sum_congr rfl fun i hi => by rw [huv i hi]`. Use `set U := ∑ i ∈ T, s (u i) * b i`.

Use `set V := ∑ i ∈ T, s (v i) * b i`. Establish `hd : s q ^ n ∣ s p ^ m * (U - x * s p)` using `⟨y - V, by linear_combination -hxy - hsum⟩`. Take `⟨w, hw⟩` from `pow_dvd_of_dvd_pow_mul s p q h1 h2 n m _ hd`. Establish `hU : U ∈ Ideal.span ({s p, s q ^ n} : Set A)` using `Ideal.mem_span_pair.2 ⟨x, w, by linear_combination -hw⟩`. Introduce `i hi`.

Take `⟨α, β, hαβ⟩` from `Ideal.mem_span_pair.1 (step_one s p q b h1 h2 h3 n T u hU i hi)`. Use `Ideal.mem_span_pair.2 ⟨α, β * p ^ m + v i, ?_⟩` and prove the remaining obligations. Rewrite using `[← huv i hi, ← hαβ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem step_three (s : S →+* A) (p q : S) {ι : Type} (b : ι → A)
    (h1 : ∀ x : A, s p * x = 0 → x = 0)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x)
    (h3 : ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q}) (n : ℕ) :
    ∀ (m : ℕ) (T : Finset ι) (c : ι → S),
      ∑ i ∈ T, s (c i) * b i ∈ Ideal.span ({s p ^ m, s q ^ n} : Set A) →
      ∀ i ∈ T, c i ∈ Ideal.span ({p ^ m, q ^ n} : Set S) := by
  intro m
  induction m with
  | zero =>
    intro T c _ i _
    exact Ideal.mem_span_pair.2 ⟨c i, 0, by simp⟩
  | succ m ih =>
    intro T c h
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 h
    have hT : ∀ i ∈ T, c i ∈ Ideal.span ({p ^ m, q ^ n} : Set S) :=
      ih T c (Ideal.mem_span_pair.2 ⟨x * s p, y, by rw [← hxy]; ring⟩)
    have hex : ∀ i, ∃ u v : S, i ∈ T → u * p ^ m + v * q ^ n = c i := by
      intro i
      by_cases hi : i ∈ T
      · obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hT i hi)
        exact ⟨u, v, fun _ => huv⟩
      · exact ⟨0, 0, fun h => absurd h hi⟩
    choose u v huv using hex
    have hsum : ∑ i ∈ T, s (c i) * b i
        = s p ^ m * ∑ i ∈ T, s (u i) * b i + s q ^ n * ∑ i ∈ T, s (v i) * b i := by
      rw [← map_pow, ← map_pow, ← sum_decomp]
      exact Finset.sum_congr rfl fun i hi => by rw [huv i hi]
    set U := ∑ i ∈ T, s (u i) * b i
    set V := ∑ i ∈ T, s (v i) * b i
    have hd : s q ^ n ∣ s p ^ m * (U - x * s p) :=
      ⟨y - V, by linear_combination -hxy - hsum⟩
    obtain ⟨w, hw⟩ := pow_dvd_of_dvd_pow_mul s p q h1 h2 n m _ hd
    have hU : U ∈ Ideal.span ({s p, s q ^ n} : Set A) :=
      Ideal.mem_span_pair.2 ⟨x, w, by linear_combination -hw⟩
    intro i hi
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 (step_one s p q b h1 h2 h3 n T u hU i hi)
    refine Ideal.mem_span_pair.2 ⟨α, β * p ^ m + v i, ?_⟩
    rw [← huv i hi, ← hαβ]
    ring

end GlobalTheory.BSP.StrictIndep

namespace GlobalTheory.BSP

open GlobalTheory.BSP.StrictIndep in

/- English proof (translation)
Introduce `S A _ _ s p q ι b h1 h2 h3 n`. Use `⟨n + n, fun a ha i => ?_⟩` and prove the remaining obligations. Establish `hle : (Ideal.span {p} ⊔ Ideal.span {q}) ^ (n + n) ≤ Ideal.span {p ^ n} ⊔ Ideal.span {q ^ n}`. Use `Ideal.sup_pow_add_le_pow_sup_pow.trans ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_pow, Ideal.span_singleton_pow]`.

Establish `ha' : a.sum (fun i y => s y * b i) ∈ Ideal.span ({s p ^ n, s q ^ n} : Set A)`. Use `Ideal.map_mono (f := s) hle ha` as an intermediate fact. Rewrite `this` using `[map_span_pair, map_pow, map_pow]`. Then use the resulting hypothesis. Distinguish the cases in `hi : i ∈ a.support`. Establish `hc` using `step_three s p q b h1 h2 h3 n n a.support (fun j => a j) ha' i hi`.

Rewrite `hc` using `[← span_sup_span_eq_pair, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]`. Establish `hle2 : Ideal.span {p} ^ n ⊔ Ideal.span {q} ^ n ≤ (Ideal.span {p} ⊔ Ideal.span {q}) ^ n` using `sup_le (Ideal.pow_right_mono le_sup_left n) (Ideal.pow_right_mono le_sup_right n)`. Conclude with `hle2 hc`. Rewrite using `[Finsupp.notMem_support_iff.1 hi]`. Conclude with `Ideal.zero_mem _`.
-/
theorem strict_indep_pow : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (p q : S)
    (ι : Type) (b : ι → A), (∀ x : A, s p * x = 0 → x = 0) →
    (∀ x : A, s p ∣ s q * x → s p ∣ x) →
    (∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q}) →
    ∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈
      ((Ideal.span {p} ⊔ Ideal.span {q}) ^ m).map s →
      ∀ i, a i ∈ (Ideal.span {p} ⊔ Ideal.span {q}) ^ n := by
  intro S A _ _ s p q ι b h1 h2 h3 n
  refine ⟨n + n, fun a ha i => ?_⟩
  have hle : (Ideal.span {p} ⊔ Ideal.span {q}) ^ (n + n) ≤ Ideal.span {p ^ n} ⊔ Ideal.span {q ^ n} := by
    refine Ideal.sup_pow_add_le_pow_sup_pow.trans ?_
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
  have ha' : a.sum (fun i y => s y * b i) ∈ Ideal.span ({s p ^ n, s q ^ n} : Set A) := by
    have := Ideal.map_mono (f := s) hle ha
    rwa [map_span_pair, map_pow, map_pow] at this
  by_cases hi : i ∈ a.support
  · have hc := step_three s p q b h1 h2 h3 n n a.support (fun j => a j) ha' i hi
    rw [← span_sup_span_eq_pair, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow] at hc
    have hle2 : Ideal.span {p} ^ n ⊔ Ideal.span {q} ^ n ≤ (Ideal.span {p} ⊔ Ideal.span {q}) ^ n :=
      sup_le (Ideal.pow_right_mono le_sup_left n) (Ideal.pow_right_mono le_sup_right n)
    exact hle2 hc
  · rw [Finsupp.notMem_support_iff.1 hi]
    exact Ideal.zero_mem _

end GlobalTheory.BSP

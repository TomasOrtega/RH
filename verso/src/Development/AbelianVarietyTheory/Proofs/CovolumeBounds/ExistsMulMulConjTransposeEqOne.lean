import Mathlib

open Module

namespace GlobalTheory.FiniteOrders

section Field

variable {K : Type*} [Field K] [StarRing K]

/- English proof (translation)
Take `⟨a, ha⟩` from `hs`. Establish `hd : a - star a ≠ 0` using `sub_ne_zero.2 ha.symm`. Establish `hd' : star a - a ≠ 0` using `sub_ne_zero.2 ha`. Rewrite using `[sq, ← Nat.card_prod]`. Use `symm`.

Use `Nat.card_congr (Equiv.ofBijective (fun p : selfAdjoint K × selfAdjoint K => (p.1 : K) + p.2 * a) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce and unpack `⟨x, y⟩ ⟨x', y'⟩ h`. Simplify using `only at h`. Establish `h2` using `congrArg star h`. Simplify using `only [star_add, star_mul', selfAdjoint.star_val_eq] at h2`.

Establish `hy : ((y : K) - y') * (a - star a) = 0` using `by linear_combination h - h2`. Establish `hy' : (y : K) = y'` using `sub_eq_zero.1 ((mul_eq_zero.1 hy).resolve_right hd)`. Establish `hx : (x : K) = x'` using `by rw [hy'] at h; exact add_right_cancel h`. Conclude with `Prod.ext (Subtype.ext hx) (Subtype.ext hy')`. Introduce `z`.

Establish `hy : star ((z - star z) / (a - star a)) = (z - star z) / (a - star a)`. Rewrite using `[star_div₀, star_sub, star_sub, star_star, star_star]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨(⟨z - (z - star z) / (a - star a) * a, ?_⟩, ⟨(z - star z) / (a - star a), hy⟩), by simp⟩` and prove the remaining obligations.

Rewrite using `[selfAdjoint.mem_iff, star_sub, star_mul', hy]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_eq_card_selfAdjoint_sq (hs : ∃ a : K, star a ≠ a) :
    Nat.card K = Nat.card (selfAdjoint K) ^ 2 := by
  obtain ⟨a, ha⟩ := hs
  have hd : a - star a ≠ 0 := sub_ne_zero.2 ha.symm
  have hd' : star a - a ≠ 0 := sub_ne_zero.2 ha
  rw [sq, ← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : selfAdjoint K × selfAdjoint K => (p.1 : K) + p.2 * a) ⟨?_, ?_⟩)
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only at h
    have h2 := congrArg star h
    simp only [star_add, star_mul', selfAdjoint.star_val_eq] at h2
    have hy : ((y : K) - y') * (a - star a) = 0 := by linear_combination h - h2
    have hy' : (y : K) = y' := sub_eq_zero.1 ((mul_eq_zero.1 hy).resolve_right hd)
    have hx : (x : K) = x' := by rw [hy'] at h; exact add_right_cancel h
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy')
  · intro z
    have hy : star ((z - star z) / (a - star a)) = (z - star z) / (a - star a) := by
      rw [star_div₀, star_sub, star_sub, star_star, star_star]
      field_simp
      ring
    refine ⟨(⟨z - (z - star z) / (a - star a) * a, ?_⟩, ⟨(z - star z) / (a - star a), hy⟩), by simp⟩
    rw [selfAdjoint.mem_iff, star_sub, star_mul', hy]
    field_simp
    ring

/- English proof (translation)
Establish `key : ∃ a : K, a + u * star a ≠ 0`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨a, ha⟩` from `hs`. Establish `h1` using `hne 1`.

Establish `h2` using `hne a`. Rewrite `h1` using `[star_one]`. Conclude with `ha (by linear_combination (star a) * h1 - h2)`. Take `⟨a, ha⟩` from `key`. Use `⟨_, ha, ?_⟩` and prove the remaining obligations.

Rewrite using `[star_add, star_mul', star_star]`. Take the linear combination `a * hu`.
-/
theorem exists_mul_star_eq_of_norm_eq_one (hs : ∃ a : K, star a ≠ a) {u : K}
    (hu : u * star u = 1) : ∃ z : K, z ≠ 0 ∧ u * star z = z := by
  have key : ∃ a : K, a + u * star a ≠ 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨a, ha⟩ := hs
    have h1 := hne 1
    have h2 := hne a
    rw [star_one] at h1
    exact ha (by linear_combination (star a) * h1 - h2)
  obtain ⟨a, ha⟩ := key
  refine ⟨_, ha, ?_⟩
  rw [star_add, star_mul', star_star]
  linear_combination a * hu

private def normHom (K : Type*) [Field K] [StarRing K] : Kˣ →* Kˣ :=
  MonoidHom.mk' (fun z => z * star z) (by
    intro a b; rw [star_mul']; exact mul_mul_mul_comm _ _ _ _)

private def quotHom (K : Type*) [Field K] [StarRing K] : Kˣ →* Kˣ :=
  MonoidHom.mk' (fun z => z / star z) (by
    intro a b; rw [star_mul']; exact mul_div_mul_comm _ _ _ _)

/- English proof (translation)
Rewrite using `[MonoidHom.mem_ker, Units.ext_iff]`. Simplify using `[normHom]`.
-/
private theorem mem_ker_normHom (z : Kˣ) : z ∈ (normHom K).ker ↔ (z : K) * star (z : K) = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]; simp [normHom]

/- English proof (translation)
Rewrite using `[MonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `z / star z = 1 ↔ _`. Rewrite using `[div_eq_one, Units.ext_iff, Units.coe_star, eq_comm]`.
-/
private theorem mem_ker_quotHom (z : Kˣ) : z ∈ (quotHom K).ker ↔ star (z : K) = z := by
  rw [MonoidHom.mem_ker]
  change z / star z = 1 ↔ _
  rw [div_eq_one, Units.ext_iff, Units.coe_star, eq_comm]

/- English proof (translation)
Use extensionality with `u`. Rewrite using `[mem_ker_normHom]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Establish `h1 : (z : K) ≠ 0` using `z.ne_zero`.

Establish `h2 : star (z : K) ≠ 0` using `star_ne_zero.2 h1`. Simplify using `only [quotHom, MonoidHom.mk'_apply, Units.val_div_eq_div_val, Units.coe_star, star_div₀, star_star]`. Clear the denominators using the available nonvanishing facts. Introduce `hu`. Take `⟨z, hz, h⟩` from `exists_mul_star_eq_of_norm_eq_one hs hu`.

Use `⟨Units.mk0 z hz, Units.ext ?_⟩` and prove the remaining obligations. Establish `h2 : star z ≠ 0` using `star_ne_zero.2 hz`. Simplify using `only [quotHom, MonoidHom.mk'_apply, Units.val_div_eq_div_val, Units.coe_star, Units.val_mk0]`. Rewrite using `[div_eq_iff h2, h]`.
-/
private theorem range_quotHom (hs : ∃ a : K, star a ≠ a) :
    (quotHom K).range = (normHom K).ker := by
  ext u
  rw [mem_ker_normHom]
  constructor
  · rintro ⟨z, rfl⟩
    have h1 : (z : K) ≠ 0 := z.ne_zero
    have h2 : star (z : K) ≠ 0 := star_ne_zero.2 h1
    simp only [quotHom, MonoidHom.mk'_apply, Units.val_div_eq_div_val, Units.coe_star, star_div₀,
      star_star]
    field_simp
  · intro hu
    obtain ⟨z, hz, h⟩ := exists_mul_star_eq_of_norm_eq_one hs hu
    refine ⟨Units.mk0 z hz, Units.ext ?_⟩
    have h2 : star z ≠ 0 := star_ne_zero.2 hz
    simp only [quotHom, MonoidHom.mk'_apply, Units.val_div_eq_div_val, Units.coe_star,
      Units.val_mk0]
    rw [div_eq_iff h2, h]

/- English proof (translation)
Rewrite using `[← Subgroup.index_ker, Subgroup.card_mul_index]`.
-/
private theorem card_ker_mul_card_range {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

/- English proof (translation)
Apply `Subgroup.eq_of_le_of_card_ge` to reduce the goal to its premises. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[mem_ker_quotHom]`. Simplify using `[normHom, mul_comm]`. Establish `h1` using `card_ker_mul_card_range (normHom K)`.

Establish `h2` using `card_ker_mul_card_range (quotHom K)`. Rewrite `h2` using `[range_quotHom hs, ← h1, mul_comm]`. Conclude with `(Nat.eq_of_mul_eq_mul_left Nat.card_pos h2).le`.
-/
private theorem range_normHom [Finite K] (hs : ∃ a : K, star a ≠ a) :
    (normHom K).range = (quotHom K).ker := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨z, rfl⟩
    rw [mem_ker_quotHom]
    simp [normHom, mul_comm]
  · have h1 := card_ker_mul_card_range (normHom K)
    have h2 := card_ker_mul_card_range (quotHom K)
    rw [range_quotHom hs, ← h1, mul_comm] at h2
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h2).le

/- English proof (translation)
Distinguish the cases in `h0 : c = 0`. Conclude with `⟨0, by simp [h0]⟩`. Establish `: Units.mk0 c h0 ∈ (normHom K).range`. Rewrite using `[range_normHom hs, mem_ker_quotHom]`. Conclude with `hc`.

Take `⟨t, ht⟩` from `this`. Conclude with `⟨t, by simpa [normHom] using congrArg Units.val ht⟩`.
-/
theorem exists_mul_star_eq [Finite K] (hs : ∃ a : K, star a ≠ a) {c : K} (hc : star c = c) :
    ∃ t : K, t * star t = c := by
  by_cases h0 : c = 0
  · exact ⟨0, by simp [h0]⟩
  have : Units.mk0 c h0 ∈ (normHom K).range := by
    rw [range_normHom hs, mem_ker_quotHom]; exact hc
  obtain ⟨t, ht⟩ := this
  exact ⟨t, by simpa [normHom] using congrArg Units.val ht⟩

/- English proof (translation)
Rewrite `hq` using `[card_eq_card_selfAdjoint_sq hs]`. Conclude with `(Nat.pow_left_injective two_ne_zero hq)`.
-/
theorem card_selfAdjoint {q : ℕ} (hq : Nat.card K = q ^ 2) (hs : ∃ a : K, star a ≠ a) :
    Nat.card (selfAdjoint K) = q := by
  rw [card_eq_card_selfAdjoint_sq hs] at hq
  exact (Nat.pow_left_injective two_ne_zero hq)

/- English proof (translation)
Establish `: 1 < Nat.card K` using `Finite.one_lt_card`. Rewrite `this` using `[hq]`. Assume the negation of the conclusion as `h`. Establish `: q ≤ 1` using `by omega`. Apply the tactic sequence `interval_cases q <;> omega`.
-/
theorem two_le_of_card_eq_sq {K : Type*} [Field K] [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2) :
    2 ≤ q := by
  have : 1 < Nat.card K := Finite.one_lt_card
  rw [hq] at this
  by_contra h
  have : q ≤ 1 := by omega
  interval_cases q <;> omega

/- English proof (translation)
Establish `h2` using `card_ker_mul_card_range (quotHom K)`. Rewrite `h2` using `[range_quotHom hs, Nat.card_units, hq]`. Establish `e1 : Nat.card (quotHom K).ker = q - 1`. Rewrite using `[← card_selfAdjoint hq hs, ← Nat.card_units]`. Use `Nat.card_congr (Equiv.ofBijective (fun z => Units.mk0 (⟨((z : Kˣ) : K), (mem_ker_quotHom _).1 z.2⟩ : selfAdjoint K) (fun h => (z : Kˣ).ne_zero (congrArg Subtype.val h))) ⟨?_, ?_⟩)` and prove the remaining obligations.

Introduce `z w h`. Conclude with `Subtype.ext (Units.ext (congrArg (fun t : (selfAdjoint K)ˣ => ((t : selfAdjoint K) : K)) h))`. Introduce `t`. Use `⟨⟨Units.mk0 ((t : selfAdjoint K) : K) (fun h => t.ne_zero (Subtype.ext h)), (mem_ker_quotHom _).2 (t : selfAdjoint K).2⟩, Units.ext (Subtype.ext rfl)⟩` and prove the remaining obligations. Establish `e2 : Nat.card (normHom K).ker = Nat.card {u : K // u * star u = 1}`.

Use `Nat.card_congr (Equiv.ofBijective (fun z => ⟨((z : Kˣ) : K), (mem_ker_normHom _).1 z.2⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `z w h`. Conclude with `Subtype.ext (Units.ext (congrArg Subtype.val h))`. Introduce and unpack `⟨u, hu⟩`. Conclude with `⟨⟨Units.mk0 u (left_ne_zero_of_mul_eq_one hu), (mem_ker_normHom _).2 hu⟩, rfl⟩`.

Rewrite `h2` using `[e1, e2]`. Establish `hq2` using `two_le_of_card_eq_sq hq`. Establish `h3 : q ^ 2 - 1 = (q - 1) * (q + 1)`. Take `⟨k, rfl⟩ : ∃ k, q = k + 1` from `⟨q - 1, by omega⟩`. Apply `Nat.sub_eq_of_eq_add` to reduce the goal to its premises.

Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[h3]`. Conclude with `Nat.eq_of_mul_eq_mul_left (by omega) h2`.
-/
theorem card_norm_eq_one [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2) (hs : ∃ a : K, star a ≠ a) :
    Nat.card {u : K // u * star u = 1} = q + 1 := by
  have h2 := card_ker_mul_card_range (quotHom K)
  rw [range_quotHom hs, Nat.card_units, hq] at h2
  have e1 : Nat.card (quotHom K).ker = q - 1 := by
    rw [← card_selfAdjoint hq hs, ← Nat.card_units]
    refine Nat.card_congr (Equiv.ofBijective (fun z => Units.mk0
      (⟨((z : Kˣ) : K), (mem_ker_quotHom _).1 z.2⟩ : selfAdjoint K)
      (fun h => (z : Kˣ).ne_zero (congrArg Subtype.val h))) ⟨?_, ?_⟩)
    · intro z w h
      exact Subtype.ext (Units.ext (congrArg (fun t : (selfAdjoint K)ˣ => ((t : selfAdjoint K) : K)) h))
    · intro t
      refine ⟨⟨Units.mk0 ((t : selfAdjoint K) : K) (fun h => t.ne_zero (Subtype.ext h)),
        (mem_ker_quotHom _).2 (t : selfAdjoint K).2⟩, Units.ext (Subtype.ext rfl)⟩
  have e2 : Nat.card (normHom K).ker = Nat.card {u : K // u * star u = 1} := by
    refine Nat.card_congr (Equiv.ofBijective (fun z => ⟨((z : Kˣ) : K), (mem_ker_normHom _).1 z.2⟩)
      ⟨?_, ?_⟩)
    · intro z w h
      exact Subtype.ext (Units.ext (congrArg Subtype.val h))
    · rintro ⟨u, hu⟩
      exact ⟨⟨Units.mk0 u (left_ne_zero_of_mul_eq_one hu), (mem_ker_normHom _).2 hu⟩, rfl⟩
  rw [e1, e2] at h2
  have hq2 := two_le_of_card_eq_sq hq
  have h3 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    apply Nat.sub_eq_of_eq_add
    simp only [Nat.add_sub_cancel]; ring
  rw [h3] at h2
  exact Nat.eq_of_mul_eq_mul_left (by omega) h2

end Field

section Sphere

variable {K : Type*} [Field K] [StarRing K]

noncomputable def sphereCard (K : Type*) [Field K] [StarRing K] (n : ℕ) (c : K) : ℕ :=
  Nat.card {x : Fin n → K // ∑ i, x i * star (x i) = c}

/- English proof (translation)
Unfold `sphereCard`. Rewrite using `[← Nat.card_sigma]`. Use `symm`. Use `Nat.card_congr (Equiv.ofBijective (fun p : (Σ t : K, {x : Fin n → K // ∑ i, x i * star (x i) = c - t * star t}) => (⟨Fin.cons p.1 p.2.1, by` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succ]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[p.2.2]`. Use the proof step `ring⟩ :`. Use the proof step `{x : Fin (n + 1) → K // ∑ i, x i * star (x i) = c})) ⟨?_, ?_⟩)`. Introduce and unpack `⟨t, x, hx⟩ ⟨t', x', hx'⟩ h`.

Establish `h' : (Fin.cons t x : Fin (n + 1) → K) = Fin.cons t' x'` using `congrArg Subtype.val h`. Take `⟨rfl, rfl⟩` from `Fin.cons_injective2.eq_iff.1 h'`. Both sides reduce to the same expression. Introduce and unpack `⟨x, hx⟩`. Use `⟨⟨x 0, Fin.tail x, ?_⟩, Subtype.ext (Fin.cons_self_tail x)⟩` and prove the remaining obligations.

Rewrite `hx` using `[Fin.sum_univ_succ]`. Rewrite using `[← hx]`. Simplify using `[Fin.tail]`.
-/
theorem sphereCard_succ [Fintype K] (n : ℕ) (c : K) :
    sphereCard K (n + 1) c = ∑ t : K, sphereCard K n (c - t * star t) := by
  unfold sphereCard
  rw [← Nat.card_sigma]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : (Σ t : K, {x : Fin n → K // ∑ i, x i * star (x i) = c - t * star t}) =>
      (⟨Fin.cons p.1 p.2.1, by
        rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; rw [p.2.2]; ring⟩ :
        {x : Fin (n + 1) → K // ∑ i, x i * star (x i) = c})) ⟨?_, ?_⟩)
  · rintro ⟨t, x, hx⟩ ⟨t', x', hx'⟩ h
    have h' : (Fin.cons t x : Fin (n + 1) → K) = Fin.cons t' x' := congrArg Subtype.val h
    obtain ⟨rfl, rfl⟩ := Fin.cons_injective2.eq_iff.1 h'
    rfl
  · rintro ⟨x, hx⟩
    refine ⟨⟨x 0, Fin.tail x, ?_⟩, Subtype.ext (Fin.cons_self_tail x)⟩
    rw [Fin.sum_univ_succ] at hx
    rw [← hx]; simp [Fin.tail]

/- English proof (translation)
Take `⟨t, rfl⟩` from `exists_mul_star_eq hs hc`. Establish `ht : t ≠ 0` using `left_ne_zero_of_mul h0`. Use `symm`. Use `Nat.card_congr (Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => Equiv.mulLeft₀ t ht) fun x => ?_)` and prove the remaining obligations. Establish `: ∑ i, (t * x i) * star (t * x i) = (t * star t) * ∑ i, x i * star (x i)`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul']`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `_ ↔ ∑ i, (t * x i) * star (t * x i) = _`.

Rewrite using `[this, mul_eq_left₀ h0]`.
-/
theorem sphereCard_eq_one [Finite K] (hs : ∃ a : K, star a ≠ a) (n : ℕ) {c : K}
    (hc : star c = c) (h0 : c ≠ 0) : sphereCard K n c = sphereCard K n 1 := by
  obtain ⟨t, rfl⟩ := exists_mul_star_eq hs hc
  have ht : t ≠ 0 := left_ne_zero_of_mul h0
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.piCongrRight fun _ => Equiv.mulLeft₀ t ht) fun x => ?_)
  have : ∑ i, (t * x i) * star (t * x i) = (t * star t) * ∑ i, x i * star (x i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul']; ring
  change _ ↔ ∑ i, (t * x i) * star (t * x i) = _
  rw [this, mul_eq_left₀ h0]

/- English proof (translation)
Use `Fintype.ofFinite K` as an intermediate fact. Establish `hcard : (Fintype.card K : ℤ) = q ^ 2`. Rewrite using `[← Nat.card_eq_fintype_card, hq]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `step : ∀ (n : ℕ) (c : K), star c = c → (sphereCard K (n + 1) c : ℤ) = q ^ 2 * sphereCard K n 1 + (Nat.card {u : K // u * star u = c} : ℤ) * (sphereCard K n 0 - sphereCard K n 1)`. Introduce `n c hc`. Rewrite using `[sphereCard_succ]`. Use `push_cast`. Establish `: ∀ t : K, (sphereCard K n (c - t * star t) : ℤ) = sphereCard K n 1 + if t * star t = c then (sphereCard K n 0 - sphereCard K n 1 : ℤ) else 0`.

Introduce `t`. Use `split_ifs with h`. Simplify using `[h]`. Rewrite using `[sphereCard_eq_one hs n (by simp [hc, mul_comm]) (sub_ne_zero.2 (Ne.symm h)), add_zero]`. Simplify using `only [this]`.

Rewrite using `[Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Proceed by induction on `n with`. Consider the case `zero`. Prove the components needed by the constructor for the conclusion. Establish `: IsEmpty {x : Fin 0 → K // ∑ i, x i * star (x i) = 1}` using `⟨fun x => by simpa using x.2⟩`.

Simplify using `[sphereCard]`. Establish `: Unique {x : Fin 0 → K // ∑ i, x i * star (x i) = 0}` using `uniqueOfSubsingleton ⟨0, by simp⟩`. Simplify using `only [sphereCard, Nat.card_unique]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Take `⟨h1, h0⟩` from `ih`. Establish `c0 : Nat.card {u : K // u * star u = 0} = 1`. Establish `: Unique {u : K // u * star u = 0}` using `⟨⟨⟨0, by simp⟩⟩, fun u => Subtype.ext (by simpa using u.2)⟩`. Conclude with `Nat.card_unique`. Rewrite using `[step n 1 (star_one K), step n 0 (star_zero K), card_norm_eq_one hq hs, c0]`.

Use `push_cast`. Prove the components needed by the constructor for the conclusion. Take the linear combination `(q ^ 2 - q - 1) * h1 + (q + 1) * h0`. Take the linear combination `(q ^ 2 - 1) * h1 + h0`.
-/
theorem sphereCard_formula [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2)
    (hs : ∃ a : K, star a ≠ a) (n : ℕ) :
    (q : ℤ) * sphereCard K n 1 = q ^ n * (q ^ n - (-1) ^ n) ∧
    (q : ℤ) * sphereCard K n 0 = q ^ (2 * n) + (-1) ^ n * (q - 1) * q ^ n := by
  classical
  have := Fintype.ofFinite K
  have hcard : (Fintype.card K : ℤ) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hq]; push_cast; rfl
  have step : ∀ (n : ℕ) (c : K), star c = c → (sphereCard K (n + 1) c : ℤ) =
      q ^ 2 * sphereCard K n 1 + (Nat.card {u : K // u * star u = c} : ℤ) *
        (sphereCard K n 0 - sphereCard K n 1) := by
    intro n c hc
    rw [sphereCard_succ]
    push_cast
    have : ∀ t : K, (sphereCard K n (c - t * star t) : ℤ) = sphereCard K n 1 +
        if t * star t = c then (sphereCard K n 0 - sphereCard K n 1 : ℤ) else 0 := by
      intro t
      split_ifs with h
      · simp [h]
      · rw [sphereCard_eq_one hs n (by simp [hc, mul_comm]) (sub_ne_zero.2 (Ne.symm h)), add_zero]
    simp only [this]
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, hcard, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  induction n with
  | zero =>
    constructor
    · have : IsEmpty {x : Fin 0 → K // ∑ i, x i * star (x i) = 1} := ⟨fun x => by simpa using x.2⟩
      simp [sphereCard]
    · have : Unique {x : Fin 0 → K // ∑ i, x i * star (x i) = 0} :=
        uniqueOfSubsingleton ⟨0, by simp⟩
      simp only [sphereCard, Nat.card_unique]
      simp
  | succ n ih =>
    obtain ⟨h1, h0⟩ := ih
    have c0 : Nat.card {u : K // u * star u = 0} = 1 := by
      have : Unique {u : K // u * star u = 0} :=
        ⟨⟨⟨0, by simp⟩⟩, fun u => Subtype.ext (by simpa using u.2)⟩
      exact Nat.card_unique
    rw [step n 1 (star_one K), step n 0 (star_zero K), card_norm_eq_one hq hs, c0]
    push_cast
    constructor
    · linear_combination (q ^ 2 - q - 1) * h1 + (q + 1) * h0
    · linear_combination (q ^ 2 - 1) * h1 + h0

/- English proof (translation)
Establish `h` using `(sphereCard_formula hq hs (n + 1)).1`. Establish `hq2` using `two_le_of_card_eq_sq hq`. Establish `: (q : ℤ) ≠ 0` using `by positivity`. Apply `mul_left_cancel₀ this` to reduce the goal to its premises. Rewrite using `[h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sphereCard_succ_one [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2)
    (hs : ∃ a : K, star a ≠ a) (n : ℕ) :
    (sphereCard K (n + 1) 1 : ℤ) = q ^ n * (q ^ (n + 1) - (-1) ^ (n + 1)) := by
  have h := (sphereCard_formula hq hs (n + 1)).1
  have hq2 := two_le_of_card_eq_sq hq
  have : (q : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ this
  rw [h]; ring

end Sphere

section Frames

variable {K : Type*} [Field K] [StarRing K]

def IsOrthonormal {V : Type*} [AddCommGroup V] [Module K V] (h : V →ₗ[K] V →ₗ⋆[K] K)
    {ι : Type*} [DecidableEq ι] (s : ι → V) : Prop :=
  ∀ i j, h (s i) (s j) = if i = j then 1 else 0

section

variable {V : Type*} [AddCommGroup V] [Module K V] {h : V →ₗ[K] V →ₗ⋆[K] K}

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `t g hg i hi`. Use `congrArg (fun v => h v (s i)) hg` as an intermediate fact. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hs _ i, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hi, if_true, map_zero, LinearMap.zero_apply] at this`. Conclude with `this`.
-/
theorem IsOrthonormal.linearIndependent {ι : Type*} [DecidableEq ι] {s : ι → V}
    (hs : IsOrthonormal h s) : LinearIndependent K s := by
  rw [linearIndependent_iff']
  intro t g hg i hi
  have := congrArg (fun v => h v (s i)) hg
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hs _ i, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hi, if_true, map_zero,
    LinearMap.zero_apply] at this
  exact this

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]`. Simplify using `only [map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hb _ _, smul_eq_mul, mul_ite, mul_one, mul_zero, starRingEnd_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[mul_comm]`.
-/
theorem IsOrthonormal.apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Basis ι K V}
    (hb : IsOrthonormal h b) (x y : V) : h x y = ∑ i, b.repr x i * star (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    hb _ _, smul_eq_mul, mul_ite, mul_one, mul_zero, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

/- English proof (translation)
Establish `key : ∃ v, h v v ≠ 0`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `htr : ∀ b : K, b + star b = 0`. Introduce `b`.

Establish `h1` using `hne ((b / h x y) • x + y)`. Simplify using `only [map_add, map_smul, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, hne, smul_eq_mul, starRingEnd_apply, hh x y, mul_zero, zero_add, add_zero, ← star_mul', div_mul_cancel₀ _ hxy] at h1`. Take the linear combination `h1`. Take `⟨a, ha⟩` from `hs`. Establish `h1` using `htr 1`.

Rewrite `h1` using `[star_one]`. Conclude with `ha (by linear_combination htr a - a * h1)`. Take `⟨v, hv⟩` from `key`. Take `⟨t, ht⟩` from `exists_mul_star_eq hs (c := (h v v)⁻¹) (by rw [star_inv₀, ← hh])`. Use `⟨t • v, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]`. Use `mul_inv_cancel₀ hv` as an intermediate fact. Take the linear combination `(h v v) * ht + this`.
-/
theorem exists_apply_self_eq_one [Finite K] (hs : ∃ a : K, star a ≠ a)
    (hh : ∀ x y, h y x = star (h x y)) {x y : V} (hxy : h x y ≠ 0) : ∃ v, h v v = 1 := by
  have key : ∃ v, h v v ≠ 0 := by
    by_contra hne
    push Not at hne
    have htr : ∀ b : K, b + star b = 0 := by
      intro b
      have h1 := hne ((b / h x y) • x + y)
      simp only [map_add, map_smul, LinearMap.map_smulₛₗ, LinearMap.add_apply,
        LinearMap.smul_apply, hne, smul_eq_mul, starRingEnd_apply, hh x y, mul_zero, zero_add,
        add_zero, ← star_mul', div_mul_cancel₀ _ hxy] at h1
      linear_combination h1
    obtain ⟨a, ha⟩ := hs
    have h1 := htr 1
    rw [star_one] at h1
    exact ha (by linear_combination htr a - a * h1)
  obtain ⟨v, hv⟩ := key
  obtain ⟨t, ht⟩ := exists_mul_star_eq hs (c := (h v v)⁻¹) (by rw [star_inv₀, ← hh])
  refine ⟨t • v, ?_⟩
  simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  have := mul_inv_cancel₀ hv
  linear_combination (h v v) * ht + this

private abbrev perp (h : V →ₗ[K] V →ₗ⋆[K] K) (v : V) : Submodule K V := LinearMap.ker (h.flip v)

private abbrev res (h : V →ₗ[K] V →ₗ⋆[K] K) (v : V) : perp h v →ₗ[K] perp h v →ₗ⋆[K] K :=
  h.domRestrict₁₂ (perp h v) (perp h v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] private theorem res_apply (v : V) (x y : perp h v) : res h v x y = h x y := rfl

/- English proof (translation)
Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (h.flip v)`. Establish `h2 : LinearMap.range (h.flip v) = ⊤`. Rewrite using `[LinearMap.range_eq_top]`. Introduce `c`. Conclude with `⟨c • v, by simp [hv]⟩`.

Rewrite `h1` using `[h2, finrank_top, finrank_self, hn]`. Express the relevant statement in the definitionally equal form `finrank K (LinearMap.ker (h.flip v)) = n`. Use linear arithmetic over natural numbers and integers.
-/
private theorem finrank_perp [FiniteDimensional K V] {v : V} (hv : h v v = 1) {n : ℕ}
    (hn : finrank K V = n + 1) : finrank K (perp h v) = n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (h.flip v)
  have h2 : LinearMap.range (h.flip v) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • v, by simp [hv]⟩
  rw [h2, finrank_top, finrank_self, hn] at h1
  change finrank K (LinearMap.ker (h.flip v)) = n
  omega

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `hnd` to reduce the goal to its premises. Introduce `y`. Establish `h1` using `hx ⟨y - h y v • v, by simp [hv]⟩`. Establish `h2 : h x v = 0` using `x.2`.

Simplify `h1` using `[LinearMap.map_smulₛₗ, h2]`.
-/
private theorem res_nondeg (hh : ∀ x y, h y x = star (h x y))
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {v : V} (hv : h v v = 1) (x : perp h v)
    (hx : ∀ y, res h v x y = 0) : x = 0 := by
  apply Subtype.ext
  apply hnd
  intro y
  have h1 := hx ⟨y - h y v • v, by simp [hv]⟩
  have h2 : h x v = 0 := x.2
  simpa [LinearMap.map_smulₛₗ, h2] using h1

/- English proof (translation)
Establish `h0 : ∀ i, h (s i) v = 0` using `fun i => (s i).2`. Introduce `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Simplify using `[hv]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`.

Rewrite using `[hh, h0, star_zero, if_neg (Fin.succ_ne_zero j).symm]`. Simplify using `[h0]`. Simplify using `using hs i j`.
-/
private theorem isOrthonormal_cons (hh : ∀ x y, h y x = star (h x y)) {v : V} (hv : h v v = 1)
    {n : ℕ} {s : Fin n → perp h v} (hs : IsOrthonormal (res h v) s) :
    IsOrthonormal h (Fin.cons v fun i => (s i : V) : Fin (n + 1) → V) := by
  have h0 : ∀ i, h (s i) v = 0 := fun i => (s i).2
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [hv]
  · simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hh, h0, star_zero, if_neg (Fin.succ_ne_zero j).symm]
  · simp [h0]
  · simpa using hs i j

/- English proof (translation)
Use `symm`. Use `Nat.card_congr (Equiv.ofBijective (fun p => ⟨_, isOrthonormal_cons hh p.1.2 p.2.2⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce and unpack `⟨⟨v, hv⟩, s, hs⟩ ⟨⟨v', hv'⟩, s', hs'⟩ e`. Establish `e' : (Fin.cons v fun i => (s i : V) : Fin (n + 1) → V) = Fin.cons v' fun i => (s' i : V)` using `congrArg Subtype.val e`. Take `⟨rfl, e2⟩` from `Fin.cons_injective2.eq_iff.1 e'`.

Take `rfl : s = s'` from `funext fun i => Subtype.ext (congrFun e2 i)`. Both sides reduce to the same expression. Introduce and unpack `⟨s, hs⟩`. Use `⟨⟨⟨s 0, by simpa using hs 0 0⟩, fun i => ⟨s i.succ, ?_⟩, fun i j => ?_⟩, Subtype.ext (Fin.cons_self_tail s)⟩` and prove the remaining obligations. Simplify using `using hs i.succ 0`.

Simplify using `using hs i.succ j.succ`.
-/
private theorem card_frames_succ [Finite V] (hh : ∀ x y, h y x = star (h x y)) (n : ℕ) :
    Nat.card {s : Fin (n + 1) → V // IsOrthonormal h s} =
      Nat.card (Σ v : {v : V // h v v = 1},
        {s : Fin n → perp h v // IsOrthonormal (res h v) s}) := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p => ⟨_, isOrthonormal_cons hh p.1.2 p.2.2⟩)
    ⟨?_, ?_⟩)
  · rintro ⟨⟨v, hv⟩, s, hs⟩ ⟨⟨v', hv'⟩, s', hs'⟩ e
    have e' : (Fin.cons v fun i => (s i : V) : Fin (n + 1) → V) =
      Fin.cons v' fun i => (s' i : V) := congrArg Subtype.val e
    obtain ⟨rfl, e2⟩ := Fin.cons_injective2.eq_iff.1 e'
    obtain rfl : s = s' := funext fun i => Subtype.ext (congrFun e2 i)
    rfl
  · rintro ⟨s, hs⟩
    refine ⟨⟨⟨s 0, by simpa using hs 0 0⟩, fun i => ⟨s i.succ, ?_⟩, fun i j => ?_⟩,
      Subtype.ext (Fin.cons_self_tail s)⟩
    · simpa using hs i.succ 0
    · simpa using hs i.succ j.succ

end

universe u

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro V _ _ _ h _ _ _`. Conclude with `⟨0, fun i => i.elim0⟩`. Consider the case `succ n ih`. Introduce `V _ _ _ h hh hnd hn`.

Establish `: Nontrivial V` using `Module.nontrivial_of_finrank_eq_succ hn`. Take `⟨x, hx⟩` from `exists_ne (0 : V)`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Conclude with `hx (hnd x hne)`. Take `⟨v, hv⟩` from `exists_apply_self_eq_one hs hh hy`. Take `⟨s, hs⟩` from `ih (perp h v) (res h v) (fun x y => hh x y) (res_nondeg hh hnd hv) (finrank_perp hv hn)`. Conclude with `⟨_, isOrthonormal_cons hh hv hs⟩`.
-/
private theorem exists_frame [Finite K] (hs : ∃ a : K, star a ≠ a) (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V →ₗ[K] V →ₗ⋆[K] K), (∀ x y, h y x = star (h x y)) →
      (∀ x, (∀ y, h x y = 0) → x = 0) → finrank K V = n →
      ∃ s : Fin n → V, IsOrthonormal h s := by
  induction n with
  | zero => intro V _ _ _ h _ _ _; exact ⟨0, fun i => i.elim0⟩
  | succ n ih =>
    intro V _ _ _ h hh hnd hn
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hn
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hx (hnd x hne)
    obtain ⟨v, hv⟩ := exists_apply_self_eq_one hs hh hy
    obtain ⟨s, hs⟩ := ih (perp h v) (res h v) (fun x y => hh x y) (res_nondeg hh hnd hv)
      (finrank_perp hv hn)
    exact ⟨_, isOrthonormal_cons hh hv hs⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_frame hs _ V h hh hnd rfl`. Set `e : ι ≃ Fin (finrank K V)` to `Fintype.equivFinOfCardEq hι`. Establish `hs' : IsOrthonormal h (s ∘ e)` using `fun i j => by`. Simplify using `using hs (e i) (e j)`. Use `⟨basisOfLinearIndependentOfCardEqFinrank' _ hs'.linearIndependent hι, ?_⟩` and prove the remaining obligations.

Simplify using `using hs'`.
-/
theorem exists_orthonormal_basis [Finite K] (hs : ∃ a : K, star a ≠ a)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {h : V →ₗ[K] V →ₗ⋆[K] K} (hh : ∀ x y, h y x = star (h x y))
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = finrank K V) : ∃ b : Basis ι K V, IsOrthonormal h b := by
  obtain ⟨s, hs⟩ := exists_frame hs _ V h hh hnd rfl
  let e : ι ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq hι
  have hs' : IsOrthonormal h (s ∘ e) := fun i j => by
    simpa using hs (e i) (e j)
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' _ hs'.linearIndependent hι, ?_⟩
  simpa using hs'

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_orthonormal_basis hs hh hnd (ι := Fin (n + 1)) (by simp [hn])`. Rewrite using `[← sphereCard_succ_one hq hs, sphereCard]`. Use `congr 1`. Use `Nat.card_congr (Equiv.subtypeEquiv b.equivFun.toEquiv fun x => ?_)` and prove the remaining obligations. Rewrite using `[hb.apply_eq_sum]`.

Both sides reduce to the same expression.
-/
theorem card_apply_self_eq_one [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2)
    (hs : ∃ a : K, star a ≠ a) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {h : V →ₗ[K] V →ₗ⋆[K] K} (hh : ∀ x y, h y x = star (h x y))
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {n : ℕ} (hn : finrank K V = n + 1) :
    (Nat.card {v : V // h v v = 1} : ℤ) = q ^ n * (q ^ (n + 1) - (-1) ^ (n + 1)) := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis hs hh hnd (ι := Fin (n + 1)) (by simp [hn])
  rw [← sphereCard_succ_one hq hs, sphereCard]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv b.equivFun.toEquiv fun x => ?_)
  rw [hb.apply_eq_sum]
  rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `V _ _ _ h _ _ _`. Establish `: Unique {s : Fin 0 → V // IsOrthonormal h s}` using `uniqueOfSubsingleton ⟨0, fun i => i.elim0⟩`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `V _ _ _ h hh hnd hn`. Establish `: Finite V` using `Module.finite_of_finite K`. Use `Fintype.ofFinite {v : V // h v v = 1}` as an intermediate fact. Rewrite using `[card_frames_succ hh, Nat.card_sigma, Finset.prod_range_succ, ← card_apply_self_eq_one hq hs hh hnd hn]`.

Use `push_cast`. Rewrite using `[Finset.sum_congr rfl fun (v : {v : V // h v v = 1}) _ => ih (perp h v) (res h v) (fun x y => hh x y) (res_nondeg hh hnd v.2) (finrank_perp v.2 hn)]`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, mul_comm]`.
-/
private theorem card_frames [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2)
    (hs : ∃ a : K, star a ≠ a) (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V →ₗ[K] V →ₗ⋆[K] K), (∀ x y, h y x = star (h x y)) →
      (∀ x, (∀ y, h x y = 0) → x = 0) → finrank K V = n →
      (Nat.card {s : Fin n → V // IsOrthonormal h s} : ℤ) =
        ∏ i ∈ Finset.range n, (q : ℤ) ^ i * (q ^ (i + 1) - (-1) ^ (i + 1)) := by
  induction n with
  | zero =>
    intro V _ _ _ h _ _ _
    have : Unique {s : Fin 0 → V // IsOrthonormal h s} :=
      uniqueOfSubsingleton ⟨0, fun i => i.elim0⟩
    simp
  | succ n ih =>
    intro V _ _ _ h hh hnd hn
    classical
    have : Finite V := Module.finite_of_finite K
    have := Fintype.ofFinite {v : V // h v v = 1}
    rw [card_frames_succ hh, Nat.card_sigma, Finset.prod_range_succ,
      ← card_apply_self_eq_one hq hs hh hnd hn]
    push_cast
    rw [Finset.sum_congr rfl fun (v : {v : V // h v v = 1}) _ => ih (perp h v) (res h v)
      (fun x y => hh x y) (res_nondeg hh hnd v.2) (finrank_perp v.2 hn)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, mul_comm]

end Frames

section Groups

variable {K : Type*} [Field K] [StarRing K]

private def gramForm {ι : Type*} [Fintype ι] (H : Matrix ι ι K) :
    (ι → K) →ₗ[K] (ι → K) →ₗ⋆[K] K :=
  LinearMap.mk₂'ₛₗ (RingHom.id K) (starRingEnd K) (fun x y => x ⬝ᵥ H.mulVec (star y))
    (fun x x' y => add_dotProduct _ _ _)
    (fun c x y => by simp [smul_dotProduct])
    (fun x y y' => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun c x y => by simp [Matrix.mulVec_smul, dotProduct_smul, starRingEnd_apply])

/- English proof (translation)
Simplify using `[gramForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`.
-/
private theorem gramForm_apply {ι : Type*} [Fintype ι] (H : Matrix ι ι K) (x y : ι → K) :
    gramForm H x y = ∑ i, ∑ j, x i * H i j * star (y j) := by
  simp [gramForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Rewrite using `[gramForm_apply, gramForm_apply, Finset.sum_comm]`. Simplify using `only [star_sum, star_mul', star_star, hH.apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem gramForm_herm {ι : Type*} [Fintype ι] {H : Matrix ι ι K} (hH : H.IsHermitian)
    (x y : ι → K) : gramForm H y x = star (gramForm H x y) := by
  rw [gramForm_apply, gramForm_apply, Finset.sum_comm]
  simp only [star_sum, star_mul', star_star, hH.apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Apply `Matrix.eq_zero_of_vecMul_eq_zero hH` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Use `hx (Pi.single j 1)` as an intermediate fact. Simplify `this` using `[gramForm_apply, Pi.single_apply, apply_ite, Matrix.vecMul, dotProduct]`.
-/
private theorem gramForm_nondeg {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι K}
    (hH : H.det ≠ 0) (x : ι → K) (hx : ∀ y, gramForm H x y = 0) : x = 0 := by
  apply Matrix.eq_zero_of_vecMul_eq_zero hH
  funext j
  have := hx (Pi.single j 1)
  simpa [gramForm_apply, Pi.single_apply, apply_ite, Matrix.vecMul, dotProduct] using this

/- English proof (translation)
Rewrite using `[← Matrix.ext_iff]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[gramForm_apply, Finset.sum_comm, Matrix.one_apply]`. Simplify using `[Matrix.mul_apply, Finset.sum_mul]`.
-/
private theorem isOrthonormal_gramForm_iff {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (H : Matrix ι ι K) (P : Matrix κ ι K) :
    IsOrthonormal (gramForm H) (fun i => P i) ↔ P * H * P.conjTranspose = 1 := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [gramForm_apply, Finset.sum_comm, Matrix.one_apply]
  simp [Matrix.mul_apply, Finset.sum_mul]

/- English proof (translation)
Rewrite using `[← card_frames hq hs (Fintype.card ι) (ι → K) (gramForm 1) (gramForm_herm Matrix.isHermitian_one) (gramForm_nondeg (by simp)) (by simp)]`. Use `congr 1`. Set `e` to `Fintype.equivFin ι`. Use `Nat.card_congr (Equiv.subtypeEquiv (Matrix.of.symm.trans (Equiv.arrowCongr e (Equiv.refl _))) fun A => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]`.

Use `isOrthonormal_gramForm_iff (1 : Matrix ι ι K) A` as an intermediate fact. Rewrite `this` using `[Matrix.mul_one]`. Rewrite using `[← this]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`.

Use `h (e.symm i) (e.symm j)` as an intermediate fact. Simplify using `only [EmbeddingLike.apply_eq_iff_eq] at this`. Conclude with `this`. Introduce `h i j`. Use `h (e i) (e j)` as an intermediate fact.

Simplify using `only [EmbeddingLike.apply_eq_iff_eq, Equiv.trans_apply, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.symm_apply_apply, Equiv.coe_refl, id] at this`. Conclude with `this`.
-/
theorem card_unitaryGroup_int [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2)
    (hs : ∃ a : K, star a ≠ a) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (Nat.card (Matrix.unitaryGroup ι K) : ℤ) =
      ∏ i ∈ Finset.range (Fintype.card ι), (q : ℤ) ^ i * (q ^ (i + 1) - (-1) ^ (i + 1)) := by
  rw [← card_frames hq hs (Fintype.card ι) (ι → K) (gramForm 1)
    (gramForm_herm Matrix.isHermitian_one) (gramForm_nondeg (by simp)) (by simp)]
  congr 1
  let e := Fintype.equivFin ι
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Matrix.of.symm.trans (Equiv.arrowCongr e (Equiv.refl _))) fun A => ?_)
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have := isOrthonormal_gramForm_iff (1 : Matrix ι ι K) A
  rw [Matrix.mul_one] at this
  rw [← this]
  constructor
  · intro h i j
    have := h (e.symm i) (e.symm j)
    simp only [EmbeddingLike.apply_eq_iff_eq] at this
    exact this
  · intro h i j
    have := h (e i) (e j)
    simp only [EmbeddingLike.apply_eq_iff_eq, Equiv.trans_apply, Equiv.arrowCongr_apply,
      Function.comp_apply, Equiv.symm_apply_apply, Equiv.coe_refl, id] at this
    exact this

/- English proof (translation)
Set `d : Matrix.unitaryGroup ι K →* unitary K` to `{ toFun := fun A => ⟨A.1.det, Matrix.det_of_mem_unitary A.2⟩ map_one' := Subtype.ext (by simp) map_mul' := fun A B => Subtype.ext (by simp) }`. Establish `hd : d.range = ⊤`. Rewrite using `[MonoidHom.range_eq_top]`. Introduce `u`. Take `⟨i⟩` from `‹Nonempty ι›`.

Use `⟨⟨Matrix.diagonal (Function.update 1 i (u : K)), ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Express the relevant statement in the definitionally equal form `(Matrix.diagonal (Function.update 1 i (u : K))).det = u`. Rewrite using `[Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]`.

Simplify using the standard rewrite rules. Rewrite using `[← card_ker_mul_card_range d, hd, Subgroup.card_top, ← card_norm_eq_one hq hs]`. Use `congr 1`. Use `Nat.card_congr (Equiv.ofBijective (fun A => ⟨⟨A.1, A.2.1⟩, Subtype.ext A.2.2⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `A B h`.

Conclude with `Subtype.ext (congrArg (fun x : d.ker => x.1.1) h)`. Introduce and unpack `⟨⟨A, hA⟩, h⟩`. Conclude with `⟨⟨A, hA, congrArg Subtype.val h⟩, rfl⟩`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun u => by`. Rewrite using `[Unitary.mem_iff, mul_comm (star u), and_self])`.
-/
theorem card_specialUnitaryGroup_mul [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2)
    (hs : ∃ a : K, star a ≠ a) (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Nat.card (Matrix.specialUnitaryGroup ι K) * (q + 1) = Nat.card (Matrix.unitaryGroup ι K) := by
  let d : Matrix.unitaryGroup ι K →* unitary K :=
    { toFun := fun A => ⟨A.1.det, Matrix.det_of_mem_unitary A.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun A B => Subtype.ext (by simp) }
  have hd : d.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro u
    obtain ⟨i⟩ := ‹Nonempty ι›
    refine ⟨⟨Matrix.diagonal (Function.update 1 i (u : K)), ?_⟩, Subtype.ext ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    · change (Matrix.diagonal (Function.update 1 i (u : K))).det = u
      rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
      simp
  rw [← card_ker_mul_card_range d, hd, Subgroup.card_top, ← card_norm_eq_one hq hs]
  congr 1
  · refine Nat.card_congr (Equiv.ofBijective (fun A => ⟨⟨A.1, A.2.1⟩, Subtype.ext A.2.2⟩) ⟨?_, ?_⟩)
    · intro A B h
      exact Subtype.ext (congrArg (fun x : d.ker => x.1.1) h)
    · rintro ⟨⟨A, hA⟩, h⟩
      exact ⟨⟨A, hA, congrArg Subtype.val h⟩, rfl⟩
  · exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      rw [Unitary.mem_iff, mul_comm (star u), and_self])

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1 + 1)]`. Establish `: (n + 1 + 1) ^ 2 - 1 = ((n + 1) ^ 2 - 1) + (n + 1) + (n + 1 + 1)`.

Establish `h1 : (n + 1 + 1) ^ 2 = (n + 1) ^ 2 + (n + 1) + (n + 1 + 1)` using `by ring`. Establish `h2 : 1 ≤ (n + 1) ^ 2` using `Nat.one_le_pow _ _ (by omega)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, pow_add q (_ + (n + 1)) (n + 1 + 1), pow_add q (_ - 1) (n + 1)]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem prod_eq (q ε : ℚ) (hq : q ≠ 0) (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), q ^ i * (q ^ (i + 1) - ε ^ (i + 1)) =
      (q ^ ((n + 1) ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 (n + 1), (1 - ε ^ i * (q ^ i)⁻¹)) * (q - ε) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1 + 1)]
    have : (n + 1 + 1) ^ 2 - 1 = ((n + 1) ^ 2 - 1) + (n + 1) + (n + 1 + 1) := by
      have h1 : (n + 1 + 1) ^ 2 = (n + 1) ^ 2 + (n + 1) + (n + 1 + 1) := by ring
      have h2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    rw [this, pow_add q (_ + (n + 1)) (n + 1 + 1), pow_add q (_ - 1) (n + 1)]
    field_simp

/- English proof (translation)
Establish `: Nonempty ι` using `Fintype.card_pos_iff.1 (by omega)`. Take `⟨n, rfl⟩ : ∃ n, r = n + 1` from `⟨r - 1, by omega⟩`. Establish `hq2` using `two_le_of_card_eq_sq hq`. Establish `h1` using `card_unitaryGroup_int hq hs ι`. Rewrite `h1` using `[← card_specialUnitaryGroup_mul hq hs ι, hr]`.

Establish `h2` using `congrArg (Int.cast : ℤ → ℚ) h1`. Move the coercions through the operations in `at h2`. Rewrite `h2` using `[prod_eq _ _ (by positivity), sub_neg_eq_add]`. Conclude with `mul_right_cancel₀ (by positivity) h2`.
-/
theorem card_specialUnitaryGroup [Finite K] {q : ℕ} (hq : Nat.card K = q ^ 2)
    (hs : ∃ a : K, star a ≠ a) (ι : Type*) [Fintype ι] [DecidableEq ι] {r : ℕ}
    (hr : Fintype.card ι = r) (h0 : 1 ≤ r) :
    (Nat.card (Matrix.specialUnitaryGroup ι K) : ℚ) =
      (q : ℚ) ^ (r ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 r, (1 - (-1) ^ i * ((q : ℚ) ^ i)⁻¹) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hq2 := two_le_of_card_eq_sq hq
  have h1 := card_unitaryGroup_int hq hs ι
  rw [← card_specialUnitaryGroup_mul hq hs ι, hr] at h1
  have h2 := congrArg (Int.cast : ℤ → ℚ) h1
  push_cast at h2
  rw [prod_eq _ _ (by positivity), sub_neg_eq_add] at h2
  exact mul_right_cancel₀ (by positivity) h2

section Abstract

variable {V : Type*} [AddCommGroup V] [Module K V] {h : V →ₗ[K] V →ₗ⋆[K] K}

end Abstract

end Groups

section Linear

variable {F : Type*} [Field F] [Finite F]

/- English proof (translation)
Establish `hd : (Matrix.GeneralLinearGroup.det : GL ι F →* Fˣ).range = ⊤`. Rewrite using `[MonoidHom.range_eq_top]`. Introduce `u`. Take `⟨i⟩` from `‹Nonempty ι›`. Establish `: (Matrix.diagonal (Function.update 1 i (u : F))).det = u`.

Rewrite using `[Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]`. Simplify using the standard rewrite rules. Conclude with `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (this.trans_ne u.ne_zero), Units.ext this⟩`. Rewrite using `[← card_ker_mul_card_range (Matrix.GeneralLinearGroup.det : GL ι F →* Fˣ), hd, Subgroup.card_top, Nat.card_units]`. Use `congr 1`.

Use `Nat.card_congr (Equiv.ofBijective (fun A => ⟨Matrix.SpecialLinearGroup.toGL A, Units.ext A.2⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `A B h`. Conclude with `Subtype.ext (congrArg (fun x : (Matrix.GeneralLinearGroup.det : GL ι F →* Fˣ).ker => (x.1 : Matrix ι ι F)) h)`. Introduce and unpack `⟨A, h⟩`. Conclude with `⟨⟨A, congrArg Units.val h⟩, Subtype.ext (Units.ext rfl)⟩`.
-/
theorem card_specialLinearGroup_mul (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Nat.card (Matrix.SpecialLinearGroup ι F) * (Nat.card F - 1) = Nat.card (GL ι F) := by
  have hd : (Matrix.GeneralLinearGroup.det : GL ι F →* Fˣ).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro u
    obtain ⟨i⟩ := ‹Nonempty ι›
    have : (Matrix.diagonal (Function.update 1 i (u : F))).det = u := by
      rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
      simp
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (this.trans_ne u.ne_zero), Units.ext this⟩
  rw [← card_ker_mul_card_range (Matrix.GeneralLinearGroup.det : GL ι F →* Fˣ), hd,
    Subgroup.card_top, Nat.card_units]
  congr 1
  refine Nat.card_congr (Equiv.ofBijective
    (fun A => ⟨Matrix.SpecialLinearGroup.toGL A, Units.ext A.2⟩) ⟨?_, ?_⟩)
  · intro A B h
    exact Subtype.ext (congrArg
      (fun x : (Matrix.GeneralLinearGroup.det : GL ι F →* Fˣ).ker => (x.1 : Matrix ι ι F)) h)
  · rintro ⟨A, h⟩
    exact ⟨⟨A, congrArg Units.val h⟩, Subtype.ext (Units.ext rfl)⟩

/- English proof (translation)
Rewrite using `[Finset.prod_mul_distrib, ← Finset.prod_range_reflect (fun i => q ^ (i + 1) - 1 ^ (i + 1)), ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Use `Finset.mem_range.1 hi` as an intermediate fact. Rewrite using `[mul_sub, ← pow_add, one_pow, mul_one]`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem prod_GL (q : ℚ) (n : ℕ) :
    ∏ i ∈ Finset.range n, (q ^ n - q ^ i) =
      ∏ i ∈ Finset.range n, q ^ i * (q ^ (i + 1) - 1 ^ (i + 1)) := by
  rw [Finset.prod_mul_distrib, ← Finset.prod_range_reflect (fun i => q ^ (i + 1) - 1 ^ (i + 1)),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  rw [mul_sub, ← pow_add, one_pow, mul_one]
  congr 2
  omega

/- English proof (translation)
Use `Fintype.ofFinite F` as an intermediate fact. Establish `: Nonempty ι` using `Fintype.card_pos_iff.1 (by omega)`. Establish `hq2 : 1 < q` using `hq ▸ Finite.one_lt_card`. Establish `e : Nat.card (GL ι F) = Nat.card (GL (Fin r) F)` using `Nat.card_congr (Units.mapEquiv (Matrix.reindexAlgEquiv F F (Fintype.equivFinOfCardEq hr)).toMulEquiv).toEquiv`. Establish `h1` using `card_specialLinearGroup_mul (F := F) ι`.

Rewrite `h1` using `[e, Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hq, Fin.prod_univ_eq_prod_range (fun i => q ^ r - q ^ i)]`. Establish `h2` using `congrArg (Nat.cast : ℕ → ℚ) h1`. Rewrite `h2` using `[Nat.cast_mul, Nat.cast_sub hq2.le, Nat.cast_prod, Finset.prod_congr rfl fun i hi => Nat.cast_sub (Nat.pow_le_pow_right (by omega) (Finset.mem_range.1 hi).le)]`. Move the coercions through the operations in `at h2`. Take `⟨n, rfl⟩ : ∃ n, r = n + 1` from `⟨r - 1, by omega⟩`.

Rewrite `h2` using `[prod_GL, prod_eq _ _ (by positivity)]`. Simplify using `only [one_pow, one_mul] at h2`. Use `mul_right_cancel₀ (sub_ne_zero.2 ?_) h2` and prove the remaining obligations. Conclude with `hq2.ne'` after adjusting the coercions.
-/
theorem card_specialLinearGroup {q : ℕ} (hq : Nat.card F = q)
    (ι : Type*) [Fintype ι] [DecidableEq ι] {r : ℕ} (hr : Fintype.card ι = r) (h0 : 1 ≤ r) :
    (Nat.card (Matrix.SpecialLinearGroup ι F) : ℚ) =
      (q : ℚ) ^ (r ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 r, (1 - ((q : ℚ) ^ i)⁻¹) := by
  have := Fintype.ofFinite F
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hq2 : 1 < q := hq ▸ Finite.one_lt_card
  have e : Nat.card (GL ι F) = Nat.card (GL (Fin r) F) :=
    Nat.card_congr (Units.mapEquiv
      (Matrix.reindexAlgEquiv F F (Fintype.equivFinOfCardEq hr)).toMulEquiv).toEquiv
  have h1 := card_specialLinearGroup_mul (F := F) ι
  rw [e, Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hq,
    Fin.prod_univ_eq_prod_range (fun i => q ^ r - q ^ i)] at h1
  have h2 := congrArg (Nat.cast : ℕ → ℚ) h1
  rw [Nat.cast_mul, Nat.cast_sub hq2.le, Nat.cast_prod, Finset.prod_congr rfl fun i hi =>
    Nat.cast_sub (Nat.pow_le_pow_right (by omega) (Finset.mem_range.1 hi).le)] at h2
  push_cast at h2
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [prod_GL, prod_eq _ _ (by positivity)] at h2
  simp only [one_pow, one_mul] at h2
  refine mul_right_cancel₀ (sub_ne_zero.2 ?_) h2
  exact_mod_cast hq2.ne'

end Linear

section Frobenius

@[reducible] noncomputable def frobeniusStarRing (F K : Type*) [Field F] [Fintype F] [Field K]
    [Algebra F K] (h2 : finrank F K = 2) : StarRing K :=
  haveI : FiniteDimensional F K := Module.finite_of_finrank_pos (by omega)
  haveI : Finite K := Module.finite_of_finite F
  { star := FiniteField.frobeniusAlgEquivOfAlgebraic F K
    star_involutive := fun x => by
      have h := pow_orderOf_eq_one (FiniteField.frobeniusAlgEquivOfAlgebraic F K)
      rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, h2] at h
      exact DFunLike.congr_fun h x
    star_mul := fun x y => by rw [map_mul, mul_comm]
    star_add := fun x y => map_add _ x y }

end Frobenius

end GlobalTheory.FiniteOrders

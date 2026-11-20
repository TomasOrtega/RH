import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ i j : ℕ, i < j → a ^ i = a ^ j → ∃ M : ℕ, 0 < M ∧ a ^ M * a ^ M = a ^ M`. Introduce `i j hij h`. Take `⟨p, rfl⟩ : ∃ p, j = i + (p + 1)` from `⟨j - i - 1, by omega⟩`. Establish `step : ∀ n, a ^ (i + n + (p + 1)) = a ^ (i + n)`. Introduce `n`.

Rewrite using `[show i + n + (p + 1) = n + (i + (p + 1)) by ring, pow_add, ← h, ← pow_add, show n + i = i + n by ring]`. Establish `rep : ∀ k n, a ^ (i + n + k * (p + 1)) = a ^ (i + n)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro n`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `n`. Rewrite using `[show i + n + (k + 1) * (p + 1) = i + (n + k * (p + 1)) + (p + 1) by ring, step, ← add_assoc, ih]`. Use `⟨(i + 1) * (p + 1), by positivity, ?_⟩` and prove the remaining obligations.

Rewrite using `[← pow_add]`. Establish `hr` using `rep (i + 1) (i * p + p + 1)`. Rewrite `hr` using `[show i + (i * p + p + 1) + (i + 1) * (p + 1) = (i + 1) * (p + 1) + (i + 1) * (p + 1) by ring, show i + (i * p + p + 1) = (i + 1) * (p + 1) by ring]`. Then use the resulting hypothesis. Take `⟨i, j, hij, h⟩` from `Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)`. Break down `lt_or_gt_of_ne hij with hlt | hlt` into its components or cases.

Conclude with `key i j hlt h`. Conclude with `key j i hlt h.symm`.
-/
private lemma exists_pos_pow_mul_pow_eq_pow_of_finite {S : Type} [Monoid S] [Finite S] (a : S) :
    ∃ M : ℕ, 0 < M ∧ a ^ M * a ^ M = a ^ M := by
  have key : ∀ i j : ℕ, i < j → a ^ i = a ^ j → ∃ M : ℕ, 0 < M ∧ a ^ M * a ^ M = a ^ M := by
    intro i j hij h
    obtain ⟨p, rfl⟩ : ∃ p, j = i + (p + 1) := ⟨j - i - 1, by omega⟩
    have step : ∀ n, a ^ (i + n + (p + 1)) = a ^ (i + n) := by
      intro n
      rw [show i + n + (p + 1) = n + (i + (p + 1)) by ring, pow_add, ← h, ← pow_add,
        show n + i = i + n by ring]
    have rep : ∀ k n, a ^ (i + n + k * (p + 1)) = a ^ (i + n) := by
      intro k
      induction k with
      | zero => intro n; simp
      | succ k ih =>
        intro n
        rw [show i + n + (k + 1) * (p + 1) = i + (n + k * (p + 1)) + (p + 1) by ring, step,
          ← add_assoc, ih]
    refine ⟨(i + 1) * (p + 1), by positivity, ?_⟩
    rw [← pow_add]
    have hr := rep (i + 1) (i * p + p + 1)
    rwa [show i + (i * p + p + 1) + (i + 1) * (p + 1) = (i + 1) * (p + 1) + (i + 1) * (p + 1) by ring,
      show i + (i * p + p + 1) = (i + 1) * (p + 1) by ring] at hr
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt h
  · exact key j i hlt h.symm

/- English proof (translation)
Establish `hyu : IsUnit y` using `⟨⟨y, c y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩`. Take `⟨M, hM0, hM⟩` from `exists_pos_pow_mul_pow_eq_pow_of_finite ((1 + y) * c (1 + y))`. Take `⟨e, he⟩ : ∃ e, e = ((1 + y) * c (1 + y)) ^ M` from `⟨_, rfl⟩`. Rewrite `hM` using `[← he]`. Establish `hce : c e = e`.

Rewrite using `[he, map_pow, map_mul, hc, mul_comm]`. Establish `h1 : y * c (1 + y) = 1 + y`. Rewrite using `[map_add, map_one]`. Take the linear combination `hy`. Use `⟨e * (1 + y) + (1 - e) * (ω + y * c ω), ?_, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hx`. Take `⟨m, hm, hxm⟩` from `exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)`. Establish `hp` using `hm.isPrime`. Establish `hnot : y * (ω - c ω) ∉ m` using `fun h => hm.ne_top (Ideal.eq_top_of_isUnit_mem m h (hyu.mul hω))`. Establish `hid : ω * (1 + y) - (ω + y * c ω) = y * (ω - c ω)` using `by ring`.

Establish `hex : e ∈ m → 1 + y ∈ m`. Introduce `h`. Rewrite `h` using `[he]`. Break down `hp.mem_or_mem (hp.mem_of_pow_mem M h) with h' | h'` into its components or cases. Conclude with `h'`.

Rewrite using `[← h1]`. Conclude with `m.mul_mem_left y h'`. Distinguish the cases in `hem : e ∈ m`. Establish `hx1 : 1 + y ∈ m` using `hex hem`. Establish `h2 : (1 - e) * (ω + y * c ω) ∈ m`.

Establish `hr : (1 - e) * (ω + y * c ω) = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - e * (1 + y)` using `by ring`. Rewrite using `[hr]`. Conclude with `m.sub_mem hxm (m.mul_mem_right _ hem)`. Establish `h1e : 1 - e ∉ m`. Introduce `h`.

Apply `hm.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `hs` using `m.add_mem hem h`. Rewrite `hs` using `[add_sub_cancel]`. Then use the resulting hypothesis. Establish `hxω : ω + y * c ω ∈ m` using `(hp.mem_or_mem h2).resolve_left h1e`.

Apply `hnot` to reduce the goal to its premises. Rewrite using `[← hid]`. Conclude with `m.sub_mem (m.mul_mem_left ω hx1) hxω`. Establish `hee : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, hM, sub_self]`. Establish `h1e : 1 - e ∈ m`.

Use `(hp.mem_or_mem ?_).resolve_left hem` and prove the remaining obligations. Rewrite using `[hee]`. Conclude with `m.zero_mem`. Establish `h2 : e * (1 + y) ∈ m`. Establish `hr : e * (1 + y) = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - (1 - e) * (ω + y * c ω)` using `by ring`.

Rewrite using `[hr]`. Conclude with `m.sub_mem hxm (m.mul_mem_right _ h1e)`. Establish `hx1 : 1 + y ∈ m` using `(hp.mem_or_mem h2).resolve_left hem`. Apply `hem` to reduce the goal to its premises. Rewrite using `[he]`.

Conclude with `Ideal.pow_mem_of_mem m (m.mul_mem_right _ hx1) M hM0`. Simplify using `only [map_add, map_mul, map_sub, map_one, hc, hce]`. Take the linear combination `(-(e + (1 - e) * ω)) * hy`.
-/
theorem finite_involution_hilbert90 {S : Type} [CommRing S] [Finite S] (c : S →+* S)
    (hc : ∀ x, c (c x) = x) (ω : S) (hω : IsUnit (ω - c ω)) (y : S) (hy : y * c y = 1) :
    ∃ x : S, IsUnit x ∧ x = y * c x := by
  have hyu : IsUnit y := ⟨⟨y, c y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  obtain ⟨M, hM0, hM⟩ := exists_pos_pow_mul_pow_eq_pow_of_finite ((1 + y) * c (1 + y))
  obtain ⟨e, he⟩ : ∃ e, e = ((1 + y) * c (1 + y)) ^ M := ⟨_, rfl⟩
  rw [← he] at hM
  have hce : c e = e := by
    rw [he, map_pow, map_mul, hc, mul_comm]
  have h1 : y * c (1 + y) = 1 + y := by
    rw [map_add, map_one]; linear_combination hy
  refine ⟨e * (1 + y) + (1 - e) * (ω + y * c ω), ?_, ?_⟩
  · by_contra hx
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)
    have hp := hm.isPrime
    have hnot : y * (ω - c ω) ∉ m := fun h => hm.ne_top (Ideal.eq_top_of_isUnit_mem m h (hyu.mul hω))
    have hid : ω * (1 + y) - (ω + y * c ω) = y * (ω - c ω) := by ring
    have hex : e ∈ m → 1 + y ∈ m := by
      intro h
      rw [he] at h
      rcases hp.mem_or_mem (hp.mem_of_pow_mem M h) with h' | h'
      · exact h'
      · rw [← h1]; exact m.mul_mem_left y h'
    by_cases hem : e ∈ m
    · have hx1 : 1 + y ∈ m := hex hem
      have h2 : (1 - e) * (ω + y * c ω) ∈ m := by
        have hr : (1 - e) * (ω + y * c ω)
            = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - e * (1 + y) := by ring
        rw [hr]; exact m.sub_mem hxm (m.mul_mem_right _ hem)
      have h1e : 1 - e ∉ m := by
        intro h
        apply hm.ne_top
        rw [Ideal.eq_top_iff_one]
        have hs := m.add_mem hem h
        rwa [add_sub_cancel] at hs
      have hxω : ω + y * c ω ∈ m := (hp.mem_or_mem h2).resolve_left h1e
      apply hnot
      rw [← hid]
      exact m.sub_mem (m.mul_mem_left ω hx1) hxω
    · have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hM, sub_self]
      have h1e : 1 - e ∈ m := by
        refine (hp.mem_or_mem ?_).resolve_left hem
        rw [hee]; exact m.zero_mem
      have h2 : e * (1 + y) ∈ m := by
        have hr : e * (1 + y)
            = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - (1 - e) * (ω + y * c ω) := by ring
        rw [hr]; exact m.sub_mem hxm (m.mul_mem_right _ h1e)
      have hx1 : 1 + y ∈ m := (hp.mem_or_mem h2).resolve_left hem
      apply hem
      rw [he]
      exact Ideal.pow_mem_of_mem m (m.mul_mem_right _ hx1) M hM0
  · simp only [map_add, map_mul, map_sub, map_one, hc, hce]
    linear_combination (-(e + (1 - e) * ω)) * hy

/- English proof (translation)
Introduce `S _ _ c hc hω u hcu hu`. Take `⟨ω, hω⟩` from `hω`. Set `cu : Sˣ →* Sˣ` to `Units.map (c : S →* S)`. Establish `hcuv : ∀ x : Sˣ, ((cu x : Sˣ) : S) = c x` using `fun x => rfl`. Establish `hcc : ∀ x : Sˣ, cu (cu x) = x` using `fun x => Units.ext (by rw [hcuv, hcuv, hc])`.

Set `N : Sˣ →* Sˣ` to `MonoidHom.id Sˣ * cu`. Set `ψ : Sˣ →* Sˣ` to `MonoidHom.id Sˣ / cu`. Establish `hN : ∀ x, N x = x * cu x` using `fun x => rfl`. Establish `hψ : ∀ x, ψ x = x / cu x` using `fun x => MonoidHom.div_apply _ _ x`. Establish `hker : N.ker ≤ ψ.range`.

Introduce `y hy`. Rewrite `hy` using `[MonoidHom.mem_ker, hN]`. Establish `hy' : (y : S) * c y = 1`. Use `congrArg Units.val hy` as an intermediate fact. Rewrite `this` using `[Units.val_mul, hcuv, Units.val_one]`. Then use the resulting hypothesis.

Take `⟨x, hxu, hx⟩` from `finite_involution_hilbert90 c hc ω hω y hy'`. Use `⟨hxu.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[hψ, div_eq_iff_eq_mul]`. Conclude with `Units.ext (by rw [Units.val_mul, hcuv, IsUnit.unit_spec]; exact hx)`. Establish `hrange : N.range ≤ ψ.ker`.

Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[MonoidHom.mem_ker, hψ, div_eq_one, hN, map_mul, hcc, mul_comm]`. Establish `hcard : Nat.card ψ.ker ≤ Nat.card N.range`. Establish `e1` using `N.ker.card_mul_index`. Establish `e2` using `ψ.ker.card_mul_index`.

Rewrite `e1`, `e2` using `[Subgroup.index_ker]`. Establish `hle : Nat.card N.ker ≤ Nat.card ψ.range` using `Subgroup.card_le_of_le hker`. Establish `hpos : 0 < Nat.card ψ.range` using `Nat.card_pos`. Establish `h3 : Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card N.range * Nat.card ψ.range`. Rewrite using `[e2, ← e1, mul_comm (Nat.card N.range)]`.

Conclude with `Nat.mul_le_mul_right _ hle`. Conclude with `Nat.le_of_mul_le_mul_right h3 hpos`. Establish `heq : N.range = ψ.ker` using `Subgroup.eq_of_le_of_card_ge hrange hcard`. Establish `hmem : hu.unit ∈ ψ.ker`. Rewrite using `[MonoidHom.mem_ker, hψ, div_eq_one]`.

Conclude with `Units.ext (by rw [hcuv, IsUnit.unit_spec, hcu])`. Rewrite `hmem` using `[← heq]`. Take `⟨x, hx⟩` from `hmem`. Use `⟨x, ?_⟩` and prove the remaining obligations. Use `congrArg Units.val hx` as an intermediate fact.

Rewrite `this` using `[hN, Units.val_mul, hcuv, IsUnit.unit_spec]`. Then use the resulting hypothesis.
-/
theorem finite_involution_fixed_unit_isNorm :
    ∀ (S : Type) [CommRing S] [Finite S] (c : S →+* S), (∀ x, c (c x) = x) →
      (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  intro S _ _ c hc hω u hcu hu
  obtain ⟨ω, hω⟩ := hω
  let cu : Sˣ →* Sˣ := Units.map (c : S →* S)
  have hcuv : ∀ x : Sˣ, ((cu x : Sˣ) : S) = c x := fun x => rfl
  have hcc : ∀ x : Sˣ, cu (cu x) = x := fun x => Units.ext (by rw [hcuv, hcuv, hc])
  let N : Sˣ →* Sˣ := MonoidHom.id Sˣ * cu
  let ψ : Sˣ →* Sˣ := MonoidHom.id Sˣ / cu
  have hN : ∀ x, N x = x * cu x := fun x => rfl
  have hψ : ∀ x, ψ x = x / cu x := fun x => MonoidHom.div_apply _ _ x
  have hker : N.ker ≤ ψ.range := by
    intro y hy
    rw [MonoidHom.mem_ker, hN] at hy
    have hy' : (y : S) * c y = 1 := by
      have := congrArg Units.val hy
      rwa [Units.val_mul, hcuv, Units.val_one] at this
    obtain ⟨x, hxu, hx⟩ := finite_involution_hilbert90 c hc ω hω y hy'
    refine ⟨hxu.unit, ?_⟩
    rw [hψ, div_eq_iff_eq_mul]
    exact Units.ext (by rw [Units.val_mul, hcuv, IsUnit.unit_spec]; exact hx)
  have hrange : N.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, hψ, div_eq_one, hN, map_mul, hcc, mul_comm]
  have hcard : Nat.card ψ.ker ≤ Nat.card N.range := by
    have e1 := N.ker.card_mul_index
    have e2 := ψ.ker.card_mul_index
    rw [Subgroup.index_ker] at e1 e2
    have hle : Nat.card N.ker ≤ Nat.card ψ.range := Subgroup.card_le_of_le hker
    have hpos : 0 < Nat.card ψ.range := Nat.card_pos
    have h3 : Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card N.range * Nat.card ψ.range := by
      rw [e2, ← e1, mul_comm (Nat.card N.range)]
      exact Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have heq : N.range = ψ.ker := Subgroup.eq_of_le_of_card_ge hrange hcard
  have hmem : hu.unit ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hψ, div_eq_one]
    exact Units.ext (by rw [hcuv, IsUnit.unit_spec, hcu])
  rw [← heq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  have := congrArg Units.val hx
  rwa [hN, Units.val_mul, hcuv, IsUnit.unit_spec] at this

end GlobalTheory

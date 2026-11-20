import Mathlib
open Finset

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨0, by simp⟩`. Consider the case `insert χ' S hχ' ih`. Take `⟨c, hc⟩` from `ih`. Distinguish the cases in `h0 : χ' = χ₀`.

Use `⟨c, fun χ hχ hne => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hχ with rfl | h` into its components or cases. Conclude with `absurd h0 hne`. Conclude with `hc χ h hne`. Take `⟨d, hd⟩` from `DFunLike.ne_iff.1 h0`.

Establish `key : ∀ χ ∈ insert χ' S, χ ≠ χ₀ → ({n : ℕ | χ (c + n * d) = χ₀ (c + n * d)} : Set ℕ).Subsingleton`. Introduce `χ hχ hne n hn m hm`. Simplify using `only [Set.mem_setOf_eq, map_add, map_mul, map_natCast] at hn hm`. Establish `hsub : ((n : k) - m) * (χ d - χ₀ d) = 0` using `by linear_combination hn - hm`. Break down `mul_eq_zero.1 hsub with h | h` into its components or cases.

Conclude with `sub_eq_zero.1 h` after adjusting the coercions. Establish `hb : χ d = χ₀ d` using `sub_eq_zero.1 h`. Break down `Finset.mem_insert.1 hχ with rfl | h'` into its components or cases. Conclude with `absurd hb hd`. Conclude with `absurd (by rw [hb] at hn; linear_combination hn) (hc χ h' hne)`.

Establish `hfin : (⋃ χ ∈ (insert χ' S).filter (· ≠ χ₀), ({n : ℕ | χ (c + n * d) = χ₀ (c + n * d)} : Set ℕ)).Finite`. Use `Set.Finite.biUnion (Finset.finite_toSet _) fun χ hχ => ?_` and prove the remaining obligations. Rewrite `hχ` using `[Finset.mem_coe, Finset.mem_filter]`. Conclude with `(key χ hχ.1 hχ.2).finite`. Take `⟨n, hn⟩` from `hfin.exists_notMem`.

Use `⟨c + n * d, fun χ hχ hne heq => hn ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨χ, Finset.mem_filter.2 ⟨hχ, hne⟩, heq⟩`.
-/
theorem ringHom_sep_charZero (k : Type) [Field k] [CharZero k] (C : Type) [CommRing C]
    (S : Finset (C →+* k)) (χ₀ : C →+* k) : ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert χ' S hχ' ih =>
    obtain ⟨c, hc⟩ := ih
    by_cases h0 : χ' = χ₀
    · refine ⟨c, fun χ hχ hne => ?_⟩
      rcases Finset.mem_insert.1 hχ with rfl | h
      · exact absurd h0 hne
      · exact hc χ h hne
    obtain ⟨d, hd⟩ := DFunLike.ne_iff.1 h0
    have key : ∀ χ ∈ insert χ' S, χ ≠ χ₀ →
        ({n : ℕ | χ (c + n * d) = χ₀ (c + n * d)} : Set ℕ).Subsingleton := by
      intro χ hχ hne n hn m hm
      simp only [Set.mem_setOf_eq, map_add, map_mul, map_natCast] at hn hm
      have hsub : ((n : k) - m) * (χ d - χ₀ d) = 0 := by linear_combination hn - hm
      rcases mul_eq_zero.1 hsub with h | h
      · exact_mod_cast sub_eq_zero.1 h
      · have hb : χ d = χ₀ d := sub_eq_zero.1 h
        rcases Finset.mem_insert.1 hχ with rfl | h'
        · exact absurd hb hd
        · exact absurd (by rw [hb] at hn; linear_combination hn) (hc χ h' hne)
    have hfin : (⋃ χ ∈ (insert χ' S).filter (· ≠ χ₀),
        ({n : ℕ | χ (c + n * d) = χ₀ (c + n * d)} : Set ℕ)).Finite := by
      refine Set.Finite.biUnion (Finset.finite_toSet _) fun χ hχ => ?_
      rw [Finset.mem_coe, Finset.mem_filter] at hχ
      exact (key χ hχ.1 hχ.2).finite
    obtain ⟨n, hn⟩ := hfin.exists_notMem
    refine ⟨c + n * d, fun χ hχ hne heq => hn ?_⟩
    simp only [Set.mem_iUnion]
    exact ⟨χ, Finset.mem_filter.2 ⟨hχ, hne⟩, heq⟩

/- English proof (translation)
Use `haveI := Fintype.ofFinite ψ.range`. Set `f : Fin (Nat.card ψ.range + 1) → ψ.range` to `fun i => ⟨ψ a ^ (i : ℕ), ⟨a ^ (i : ℕ), by simp⟩⟩`. Take `⟨i, j, hij, hf⟩` from `Fintype.exists_ne_map_eq_of_card_lt f (by`. Rewrite using `[Fintype.card_fin, ← Nat.card_eq_fintype_card]`. Use the proof step `omega)`.

Establish `hf' : ψ a ^ (i : ℕ) = ψ a ^ (j : ℕ)` using `congrArg Subtype.val hf`. Establish `hpos : ∀ (u v : ℕ), u < v → v ≤ Nat.card ψ.range → ψ a ^ u = ψ a ^ v → ψ a ^ m = 1`. Introduce `u v huv hv he`. Establish `h1 : ψ a ^ (v - u) = 1`. Establish `: ψ a ^ u * (ψ a ^ (v - u) - 1) = 0`.

Rewrite using `[mul_sub, ← pow_add, Nat.add_sub_cancel' huv.le, mul_one, he, sub_self]`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `absurd (pow_eq_zero_iff'.1 h).1 ha`. Conclude with `sub_eq_zero.1 h`. Establish `hd : v - u ∣ m` using `(Nat.dvd_factorial (by omega) (by omega)).trans hm`.

Take `⟨t, rfl⟩` from `hd`. Rewrite using `[pow_mul, h1, one_pow]`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Break down `lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h` into its components or cases.

Conclude with `hpos i j h (by omega) hf'`. Conclude with `hpos j i h (by omega) hf'.symm`.
-/
theorem ringHom_pow_eq_one_of_finite_range {k : Type} [Field k] {C : Type} [CommRing C]
    (ψ : C →+* k) [Finite ψ.range] (a : C) (ha : ψ a ≠ 0) (m : ℕ)
    (hm : (Nat.card ψ.range).factorial ∣ m) : ψ a ^ m = 1 := by
  classical
  haveI := Fintype.ofFinite ψ.range
  let f : Fin (Nat.card ψ.range + 1) → ψ.range := fun i => ⟨ψ a ^ (i : ℕ), ⟨a ^ (i : ℕ), by simp⟩⟩
  obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
  have hf' : ψ a ^ (i : ℕ) = ψ a ^ (j : ℕ) := congrArg Subtype.val hf
  have hpos : ∀ (u v : ℕ), u < v → v ≤ Nat.card ψ.range → ψ a ^ u = ψ a ^ v → ψ a ^ m = 1 := by
    intro u v huv hv he
    have h1 : ψ a ^ (v - u) = 1 := by
      have : ψ a ^ u * (ψ a ^ (v - u) - 1) = 0 := by
        rw [mul_sub, ← pow_add, Nat.add_sub_cancel' huv.le, mul_one, he, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (pow_eq_zero_iff'.1 h).1 ha
      · exact sub_eq_zero.1 h
    have hd : v - u ∣ m := (Nat.dvd_factorial (by omega) (by omega)).trans hm
    obtain ⟨t, rfl⟩ := hd
    rw [pow_mul, h1, one_pow]
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact hpos i j h (by omega) hf'
  · exact hpos j i h (by omega) hf'.symm

/- English proof (translation)
Take `⟨u, hu⟩` from `IsCyclic.exists_generator (α := (χ₀.range)ˣ)`. Take `⟨g, hg⟩` from `((u : χ₀.range)).2`. Use `⟨g, ?_, fun b hb => ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`. Conclude with `fun h => u.ne_zero (Subtype.ext h)`.

Use `set y : χ₀.range := ⟨χ₀ b, ⟨b, rfl⟩⟩`. Establish `hy0 : y ≠ 0` using `fun h => hb (congrArg Subtype.val h)`. Establish `hyu : IsUnit y`. Establish `hpow` using `ringHom_pow_eq_one_of_finite_range χ₀ b hb _ dvd_rfl`. Conclude with `⟨Units.ofPowEqOne y (Nat.card χ₀.range).factorial (Subtype.ext (by simpa [y] using hpow)) (Nat.factorial_ne_zero _), rfl⟩`.

Take `⟨n, hn⟩` from `(mem_powers_iff_mem_zpowers.2 (hu hyu.unit) : hyu.unit ∈ Submonoid.powers u)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h1 : ((u ^ n : (χ₀.range)ˣ) : χ₀.range) = y`. Rewrite using `[show u ^ n = hyu.unit from hn]`. Both sides reduce to the same expression.

Establish `h2 : ((u : χ₀.range) : k) ^ n = χ₀ b`. Use `congrArg Subtype.val h1` as an intermediate fact. Simplify `this` using `[y]`. Rewrite using `[hg]`. Conclude with `h2.symm`.
-/
theorem ringHom_exists_generator_of_finite_range {k : Type} [Field k] {C : Type} [CommRing C]
    (χ₀ : C →+* k) [Finite χ₀.range] :
    ∃ g : C, χ₀ g ≠ 0 ∧ ∀ b, χ₀ b ≠ 0 → ∃ n : ℕ, χ₀ b = χ₀ g ^ n := by
  classical
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (χ₀.range)ˣ)
  obtain ⟨g, hg⟩ := ((u : χ₀.range)).2
  refine ⟨g, ?_, fun b hb => ?_⟩
  · rw [hg]
    exact fun h => u.ne_zero (Subtype.ext h)
  · set y : χ₀.range := ⟨χ₀ b, ⟨b, rfl⟩⟩
    have hy0 : y ≠ 0 := fun h => hb (congrArg Subtype.val h)
    have hyu : IsUnit y := by
      have hpow := ringHom_pow_eq_one_of_finite_range χ₀ b hb _ dvd_rfl
      exact ⟨Units.ofPowEqOne y (Nat.card χ₀.range).factorial
        (Subtype.ext (by simpa [y] using hpow)) (Nat.factorial_ne_zero _), rfl⟩
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.2 (hu hyu.unit) : hyu.unit ∈ Submonoid.powers u)
    refine ⟨n, ?_⟩
    have h1 : ((u ^ n : (χ₀.range)ˣ) : χ₀.range) = y := by
      rw [show u ^ n = hyu.unit from hn]; rfl
    have h2 : ((u : χ₀.range) : k) ^ n = χ₀ b := by
      have := congrArg Subtype.val h1
      simpa [y] using this
    rw [hg]
    exact h2.symm

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Set `M : ℕ` to `∏ ψ ∈ insert χ₀ S, (Nat.card ψ.range).factorial`. Establish `hM0 : M ≠ 0` using `Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _`. Establish `hpow : ∀ ψ ∈ insert χ₀ S, ∀ a, ψ a ≠ 0 → ψ a ^ M = 1` using `fun ψ hψ a ha => by haveI := hfin ψ`. Conclude with `ringHom_pow_eq_one_of_finite_range ψ a ha M (Finset.dvd_prod_of_mem _ hψ)`. Establish `hpow' : ∀ ψ ∈ insert χ₀ S, ∀ a, ψ (a ^ M) = if ψ a = 0 then 0 else 1`.

Introduce `ψ hψ a`. Rewrite using `[map_pow]`. Use `split_ifs with h`. Rewrite using `[h, zero_pow hM0]`. Conclude with `hpow ψ hψ a h`.

Use `haveI := hfin χ₀`. Take `⟨g, hg0, hgen⟩` from `ringHom_exists_generator_of_finite_range χ₀`. Establish `hsep : ∀ χ ∈ S, χ ≠ χ₀ → χ g = χ₀ g → ∃ a, χ a = 0 ∧ χ₀ a ≠ 0`. Introduce `χ hχ hne hgeq`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hχ' : χ ∈ insert χ₀ S` using `Finset.mem_insert_of_mem hχ`. Establish `hk : ∀ b, χ₀ b = 0 → χ b = 0`. Introduce `b hb`. Assume the negation of the conclusion as `hb'`.

Establish `h1` using `hcon (1 - b ^ M) (by rw [map_sub, map_one, map_pow, hpow χ hχ' b hb', sub_self])`. Rewrite `h1` using `[map_sub, map_one, map_pow, hb, zero_pow hM0, sub_zero]`. Conclude with `one_ne_zero h1`. Apply `hne` to reduce the goal to its premises. Use extensionality with `b`.

Distinguish the cases in `hb : χ₀ b = 0`. Rewrite using `[hb, hk b hb]`. Take `⟨n, hn⟩` from `hgen b hb`. Establish `h3 : χ (b - g ^ n) = 0` using `hk _ (by rw [map_sub, map_pow, hn, sub_self])`. Rewrite `h3` using `[map_sub, map_pow, sub_eq_zero, hgeq, ← hn]`.

Conclude with `h3`. Set `V` to `S.filter (fun χ => χ ≠ χ₀ ∧ χ g = χ₀ g)`. Establish `hV : ∀ χ ∈ V, ∃ a, χ a = 0 ∧ χ₀ a ≠ 0` using `fun χ hχ => by`. Take `⟨h1, h2, h3⟩` from `(Finset.mem_filter.1 hχ)`. Conclude with `hsep χ h1 h2 h3`.

Use `choose! a ha using hV`. Set `A : C` to `∏ χ ∈ V, a χ`. Establish `hA0 : χ₀ A ≠ 0`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 fun χ hχ => (ha χ hχ).2`.

Establish `hAV : ∀ χ ∈ V, χ A = 0` using `fun χ hχ => by`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_eq_zero hχ (ha χ hχ).1`. Use `⟨g * A ^ M, fun χ hχ hne => ?_⟩` and prove the remaining obligations. Establish `hχ' : χ ∈ insert χ₀ S` using `Finset.mem_insert_of_mem hχ`.

Rewrite using `[map_mul, map_mul, hpow' χ₀ (Finset.mem_insert_self _ _), if_neg hA0, mul_one, hpow' χ hχ']`. Distinguish the cases in `hgeq : χ g = χ₀ g`. Rewrite using `[if_pos (hAV χ (Finset.mem_filter.2 ⟨hχ, hne, hgeq⟩)), mul_zero]`. Conclude with `fun h => hg0 h.symm`. Use `split_ifs`.

Rewrite using `[mul_zero]`. Conclude with `fun h => hg0 h.symm`. Rewrite using `[mul_one]` and apply the resulting hypothesis.
-/
theorem ringHom_sep_of_finite_range (k : Type) [Field k] (C : Type) [CommRing C]
    (hfin : ∀ ψ : C →+* k, Finite ψ.range) (S : Finset (C →+* k)) (χ₀ : C →+* k) :
    ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  classical
  let M : ℕ := ∏ ψ ∈ insert χ₀ S, (Nat.card ψ.range).factorial
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hpow : ∀ ψ ∈ insert χ₀ S, ∀ a, ψ a ≠ 0 → ψ a ^ M = 1 := fun ψ hψ a ha => by
    haveI := hfin ψ
    exact ringHom_pow_eq_one_of_finite_range ψ a ha M (Finset.dvd_prod_of_mem _ hψ)
  have hpow' : ∀ ψ ∈ insert χ₀ S, ∀ a, ψ (a ^ M) = if ψ a = 0 then 0 else 1 := by
    intro ψ hψ a
    rw [map_pow]
    split_ifs with h
    · rw [h, zero_pow hM0]
    · exact hpow ψ hψ a h
  haveI := hfin χ₀
  obtain ⟨g, hg0, hgen⟩ := ringHom_exists_generator_of_finite_range χ₀
  have hsep : ∀ χ ∈ S, χ ≠ χ₀ → χ g = χ₀ g → ∃ a, χ a = 0 ∧ χ₀ a ≠ 0 := by
    intro χ hχ hne hgeq
    by_contra hcon
    push_neg at hcon
    have hχ' : χ ∈ insert χ₀ S := Finset.mem_insert_of_mem hχ
    have hk : ∀ b, χ₀ b = 0 → χ b = 0 := by
      intro b hb
      by_contra hb'
      have h1 := hcon (1 - b ^ M) (by rw [map_sub, map_one, map_pow, hpow χ hχ' b hb', sub_self])
      rw [map_sub, map_one, map_pow, hb, zero_pow hM0, sub_zero] at h1
      exact one_ne_zero h1
    apply hne
    ext b
    by_cases hb : χ₀ b = 0
    · rw [hb, hk b hb]
    · obtain ⟨n, hn⟩ := hgen b hb
      have h3 : χ (b - g ^ n) = 0 := hk _ (by rw [map_sub, map_pow, hn, sub_self])
      rw [map_sub, map_pow, sub_eq_zero, hgeq, ← hn] at h3
      exact h3
  let V := S.filter (fun χ => χ ≠ χ₀ ∧ χ g = χ₀ g)
  have hV : ∀ χ ∈ V, ∃ a, χ a = 0 ∧ χ₀ a ≠ 0 := fun χ hχ => by
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.1 hχ)
    exact hsep χ h1 h2 h3
  choose! a ha using hV
  let A : C := ∏ χ ∈ V, a χ
  have hA0 : χ₀ A ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun χ hχ => (ha χ hχ).2
  have hAV : ∀ χ ∈ V, χ A = 0 := fun χ hχ => by
    rw [map_prod]
    exact Finset.prod_eq_zero hχ (ha χ hχ).1
  refine ⟨g * A ^ M, fun χ hχ hne => ?_⟩
  have hχ' : χ ∈ insert χ₀ S := Finset.mem_insert_of_mem hχ
  rw [map_mul, map_mul, hpow' χ₀ (Finset.mem_insert_self _ _), if_neg hA0, mul_one,
    hpow' χ hχ']
  by_cases hgeq : χ g = χ₀ g
  · rw [if_pos (hAV χ (Finset.mem_filter.2 ⟨hχ, hne, hgeq⟩)), mul_zero]
    exact fun h => hg0 h.symm
  · split_ifs
    · rw [mul_zero]; exact fun h => hg0 h.symm
    · rwa [mul_one]

/- English proof (translation)
Use `haveI : Module.Finite ℤ ψ.range := Module.Finite.of_surjective (ψ.rangeRestrict.toAddMonoidHom.toIntLinearMap) ψ.rangeRestrict_surjective`. Use `haveI : AddGroup.FG ψ.range := Module.Finite.iff_addGroup_fg.1 inferInstance`. Use `AddCommGroup.finite_of_fg_torsion _ fun x => ?_` and prove the remaining obligations. Use `(isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨p, Nat.pos_of_ne_zero hp0, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[nsmul_eq_mul, CharP.cast_eq_zero]`.
-/
theorem ringHom_finite_range_of_charP {k : Type} [Field k] {C : Type} [CommRing C]
    [Module.Finite ℤ C] (p : ℕ) [hp : CharP k p] (hp0 : p ≠ 0) (ψ : C →+* k) :
    Finite ψ.range := by
  haveI : Module.Finite ℤ ψ.range :=
    Module.Finite.of_surjective (ψ.rangeRestrict.toAddMonoidHom.toIntLinearMap)
      ψ.rangeRestrict_surjective
  haveI : AddGroup.FG ψ.range := Module.Finite.iff_addGroup_fg.1 inferInstance
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  refine (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨p, Nat.pos_of_ne_zero hp0, ?_⟩
  apply Subtype.ext
  simp [nsmul_eq_mul, CharP.cast_eq_zero]

/- English proof (translation)
Introduce `k _ C _ _ S χ₀`. Take `⟨p, hp⟩` from `CharP.exists k`. Break down `CharP.char_is_prime_or_zero k p with hpp | rfl` into its components or cases. Conclude with `ringHom_sep_of_finite_range k C (fun ψ => ringHom_finite_range_of_charP p hpp.ne_zero ψ) S χ₀`. Use `haveI := CharP.charP_to_charZero k`.

Conclude with `ringHom_sep_charZero k C S χ₀`.
-/
theorem ringHom_exists_sep_of_moduleFinite_int : ∀ (k : Type) [Field k] (C : Type) [CommRing C]
    [Module.Finite ℤ C] (S : Finset (C →+* k)) (χ₀ : C →+* k),
    ∃ c : C, ∀ χ ∈ S, χ ≠ χ₀ → χ c ≠ χ₀ c := by
  intro k _ C _ _ S χ₀
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · exact ringHom_sep_of_finite_range k C
      (fun ψ => ringHom_finite_range_of_charP p hpp.ne_zero ψ) S χ₀
  · haveI := CharP.charP_to_charZero k
    exact ringHom_sep_charZero k C S χ₀

end GlobalTheory

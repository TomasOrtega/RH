import Mathlib

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Use `choose! n w hw hcw using hc`. Use `set S := Finset.univ.filter (fun i => c i ≠ 0) with hS`. Establish `hSne : S.Nonempty`.

Take `⟨i, hi⟩` from `hne`. Conclude with `⟨i, by simp [hS, hi]⟩`. Take `⟨i0, hi0S, hmin⟩` from `S.exists_min_image (fun i => i.val + e * n i) hSne`. Establish `hi0 : c i0 ≠ 0` using `(Finset.mem_filter.1 hi0S).2`. Establish `hdvd : ∀ i ∈ Finset.univ.erase i0, ϖ ^ (i0.val + e * n i0 + 1) ∣ c i`.

Introduce `i hi`. Establish `hii0 : i ≠ i0` using `Finset.ne_of_mem_erase hi`. Distinguish the cases in `hci : c i = 0`. Rewrite using `[hci]`. Conclude with `dvd_zero _`.

Establish `hiS : i ∈ S` using `Finset.mem_filter.2 ⟨Finset.mem_univ _, hci⟩`. Establish `hle : i0.val + e * n i0 ≤ i.val + e * n i` using `hmin i hiS`. Establish `hne' : i.val + e * n i ≠ i0.val + e * n i0`. Introduce `heq`. Apply `hii0` to reduce the goal to its premises.

Apply `Fin.ext` to reduce the goal to its premises. Establish `h1 : (i.val + e * n i) % e = i.val`. Rewrite using `[Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]`. Establish `h2 : (i0.val + e * n i0) % e = i0.val`. Rewrite using `[Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i0.isLt]`.

Rewrite using `[← h1, ← h2, heq]`. Rewrite using `[hcw i hci]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _`. Take `⟨X, hX⟩` from `Finset.dvd_sum hdvd`. Rewrite `hsum` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hX, hcw i0 hi0]`.

Establish `h0 : ϖ ^ (i0.val + e * n i0) * (w i0 + ϖ * X) = 0` using `by rw [← hsum]; ring`. Establish `h1 : w i0 + ϖ * X = 0` using `(mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hϖ.ne_zero)`. Establish `h2 : ϖ ∣ w i0` using `⟨-X, by linear_combination h1⟩`. Conclude with `hϖ.not_isUnit (isUnit_of_dvd_unit h2 (hw i0 hi0))`.
-/
theorem eq_zero_of_sum_eq_zero_of_unit_mul_pow {R : Type*} [CommRing R] [IsDomain R] {ϖ : R}
    (hϖ : Irreducible ϖ) {e : ℕ} (c : Fin e → R)
    (hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : R), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n))
    (hsum : ∑ i, c i = 0) : ∀ i, c i = 0 := by
  classical
  by_contra hne
  push_neg at hne
  choose! n w hw hcw using hc
  set S := Finset.univ.filter (fun i => c i ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [hS, hi]⟩
  obtain ⟨i0, hi0S, hmin⟩ := S.exists_min_image (fun i => i.val + e * n i) hSne
  have hi0 : c i0 ≠ 0 := (Finset.mem_filter.1 hi0S).2
  have hdvd : ∀ i ∈ Finset.univ.erase i0, ϖ ^ (i0.val + e * n i0 + 1) ∣ c i := by
    intro i hi
    have hii0 : i ≠ i0 := Finset.ne_of_mem_erase hi
    by_cases hci : c i = 0
    · rw [hci]; exact dvd_zero _
    · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hci⟩
      have hle : i0.val + e * n i0 ≤ i.val + e * n i := hmin i hiS
      have hne' : i.val + e * n i ≠ i0.val + e * n i0 := by
        intro heq
        apply hii0
        apply Fin.ext
        have h1 : (i.val + e * n i) % e = i.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
        have h2 : (i0.val + e * n i0) % e = i0.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i0.isLt]
        rw [← h1, ← h2, heq]
      rw [hcw i hci]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  obtain ⟨X, hX⟩ := Finset.dvd_sum hdvd
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hX, hcw i0 hi0] at hsum
  have h0 : ϖ ^ (i0.val + e * n i0) * (w i0 + ϖ * X) = 0 := by rw [← hsum]; ring
  have h1 : w i0 + ϖ * X = 0 :=
    (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hϖ.ne_zero)
  have h2 : ϖ ∣ w i0 := ⟨-X, by linear_combination h1⟩
  exact hϖ.not_isUnit (isUnit_of_dvd_unit h2 (hw i0 hi0))

/- English proof (translation)
Introduce `F _ T' T'' h1 h2 h hdom s hspan π hπ`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible T''`. Establish `hπ0 : Subring.inclusion h π ≠ 0`. Introduce `h0`. Apply `hπ.ne_zero` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg Subtype.val h0` as an intermediate fact. Simplify using `using this`. Take `⟨e, he⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hπ0 hϖ`. Use `⟨ϖ, hϖ, e, ?_, ?_, he⟩` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos e with rfl | hpos` into its components or cases. It suffices to derive a contradiction. Rewrite `he` using `[pow_zero]`. Establish `hu : IsUnit (Subring.inclusion h π)` using `he.isUnit_iff.2 isUnit_one`. Take `⟨y, hy⟩` from `hu.exists_right_inv`.

Take `⟨z, hzT', hz⟩` from `hdom (π : F) π.2 ⟨(y : F), y.2, by simpa using congrArg Subtype.val hy⟩`. Conclude with `hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨⟨z, hzT'⟩, Subtype.ext hz⟩)`. Conclude with `hpos`. Use `choose d hdT hd0 hdspan using fun i : Fin e => hspan ((ϖ ^ (i : ℕ) : T'') : F) (ϖ ^ (i : ℕ)).2`. Use `set D : F := ∏ i, d i with hDdef`.

Establish `hDT : D ∈ T'` using `Subring.prod_mem _ (fun i _ => hdT i)`. Establish `hD0 : D ≠ 0` using `Finset.prod_ne_zero_iff.2 (fun i _ => hd0 i)`. Set `f : Fin e → F` to `fun i => D * ((ϖ ^ (i : ℕ) : T'') : F)`. Establish `hfspan : ∀ i, f i ∈ Submodule.span T' (s : Set F)`. Introduce `i`.

Establish `hmem : (∏ j ∈ Finset.univ.erase i, d j) ∈ T'` using `Subring.prod_mem _ (fun j _ => hdT j)`. Use `Submodule.smul_mem (Submodule.span T' (s : Set F)) (⟨∏ j ∈ Finset.univ.erase i, d j, hmem⟩ : T') (hdspan i)` as an intermediate fact. Rewrite `this` using `[Subring.smul_def]`. Establish `heq : f i = (∏ j ∈ Finset.univ.erase i, d j) * (d i * ((ϖ ^ (i : ℕ) : T'') : F))`. Simplify using `only [f, hDdef]`.

Rewrite using `[← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `this`. Establish `hli : LinearIndependent T' f`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Take `⟨v, hv⟩` from `he.symm`. Set `c : Fin e → T''` to `fun i => Subring.inclusion h (g i * ⟨D, hDT⟩) * ϖ ^ (i : ℕ)`. Establish `hcsum : ∑ i, c i = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `hcs : ((∑ i, c i : T'') : F) = ∑ i, g i • f i`. Simplify using `[c, f, Subring.smul_def, mul_assoc]`. Rewrite using `[hcs, hg]`. Both sides reduce to the same expression.

Establish `hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : T''), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n)`. Introduce `i hci`. Establish `ha : g i * ⟨D, hDT⟩ ≠ 0`. Introduce `h0`. Apply `hci` to reduce the goal to its premises.

Simplify using `only [c, h0, map_zero, zero_mul]`. Take `⟨m, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ`. Use `⟨m, Subring.inclusion h (u : T') * (v : T'') ^ m, (u.isUnit.map (Subring.inclusion h)).mul (v.isUnit.pow m), ?_⟩` and prove the remaining obligations. Simplify using `only [c]`. Rewrite using `[hu, map_mul, map_pow, ← hv]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc0` using `eq_zero_of_sum_eq_zero_of_unit_mul_pow hϖ c hc hcsum`. Introduce `i`. Use `hc0 i` as an intermediate fact. Simplify using `only [c, mul_eq_zero, pow_eq_zero_iff', hϖ.ne_zero, false_and, or_false] at this`.

Establish `h3 : g i * ⟨D, hDT⟩ = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg Subtype.val this` as an intermediate fact. Simplify using `using this`. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases.

Conclude with `h4`. Conclude with `absurd (congrArg Subtype.val h4) hD0`. Set `f' : Fin e → Submodule.span T' (s : Set F)` to `fun i => ⟨f i, hfspan i⟩`. Establish `hli' : LinearIndependent T' f'` using `LinearIndependent.of_comp (Submodule.span T' (s : Set F)).subtype hli`. Establish `hcard` using `hli'.cardinal_le_rank.trans (rank_span_finset_le s)`.

Simplify using `using hcard`.
-/
theorem ramification_le_card_of_span :
    ∀ (F : Type) [Field F] (T' T'' : Subring F), IsDiscreteValuationRing T' →
      IsDiscreteValuationRing T'' → ∀ (h : T' ≤ T''),
      (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) → ∀ (s : Finset F),
      (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) →
      ∀ π : T', Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ ∃ e : ℕ, 1 ≤ e ∧ e ≤ s.card ∧
        Associated (Subring.inclusion h π) (ϖ ^ e) := by
  intro F _ T' T'' h1 h2 h hdom s hspan π hπ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T''
  have hπ0 : Subring.inclusion h π ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h0
    simpa using this
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hϖ
  refine ⟨ϖ, hϖ, e, ?_, ?_, he⟩
  · rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exfalso
      rw [pow_zero] at he
      have hu : IsUnit (Subring.inclusion h π) := he.isUnit_iff.2 isUnit_one
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      obtain ⟨z, hzT', hz⟩ := hdom (π : F) π.2
        ⟨(y : F), y.2, by simpa using congrArg Subtype.val hy⟩
      exact hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨⟨z, hzT'⟩, Subtype.ext hz⟩)
    · exact hpos
  ·
    choose d hdT hd0 hdspan using
      fun i : Fin e => hspan ((ϖ ^ (i : ℕ) : T'') : F) (ϖ ^ (i : ℕ)).2
    set D : F := ∏ i, d i with hDdef
    have hDT : D ∈ T' := Subring.prod_mem _ (fun i _ => hdT i)
    have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hd0 i)
    let f : Fin e → F := fun i => D * ((ϖ ^ (i : ℕ) : T'') : F)
    have hfspan : ∀ i, f i ∈ Submodule.span T' (s : Set F) := by
      intro i
      have hmem : (∏ j ∈ Finset.univ.erase i, d j) ∈ T' :=
        Subring.prod_mem _ (fun j _ => hdT j)
      have := Submodule.smul_mem (Submodule.span T' (s : Set F))
        (⟨∏ j ∈ Finset.univ.erase i, d j, hmem⟩ : T') (hdspan i)
      rw [Subring.smul_def] at this
      have heq : f i = (∏ j ∈ Finset.univ.erase i, d j) * (d i * ((ϖ ^ (i : ℕ) : T'') : F)) := by
        simp only [f, hDdef]
        rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
        ring
      rw [heq]
      exact this
    have hli : LinearIndependent T' f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      obtain ⟨v, hv⟩ := he.symm
      let c : Fin e → T'' := fun i =>
        Subring.inclusion h (g i * ⟨D, hDT⟩) * ϖ ^ (i : ℕ)
      have hcsum : ∑ i, c i = 0 := by
        apply Subtype.ext
        have hcs : ((∑ i, c i : T'') : F) = ∑ i, g i • f i := by
          simp [c, f, Subring.smul_def, mul_assoc]
        rw [hcs, hg]
        rfl
      have hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : T''), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n) := by
        intro i hci
        have ha : g i * ⟨D, hDT⟩ ≠ 0 := by
          intro h0; apply hci; simp only [c, h0, map_zero, zero_mul]
        obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
        refine ⟨m, Subring.inclusion h (u : T') * (v : T'') ^ m,
          (u.isUnit.map (Subring.inclusion h)).mul (v.isUnit.pow m), ?_⟩
        simp only [c]
        rw [hu, map_mul, map_pow, ← hv]
        ring
      have hc0 := eq_zero_of_sum_eq_zero_of_unit_mul_pow hϖ c hc hcsum
      intro i
      have := hc0 i
      simp only [c, mul_eq_zero, pow_eq_zero_iff', hϖ.ne_zero, false_and, or_false] at this
      have h3 : g i * ⟨D, hDT⟩ = 0 := by
        apply Subtype.ext
        have := congrArg Subtype.val this
        simpa using this
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h4
      · exact absurd (congrArg Subtype.val h4) hD0
    let f' : Fin e → Submodule.span T' (s : Set F) := fun i => ⟨f i, hfspan i⟩
    have hli' : LinearIndependent T' f' :=
      LinearIndependent.of_comp (Submodule.span T' (s : Set F)).subtype hli
    have hcard := hli'.cardinal_le_rank.trans (rank_span_finset_le s)
    simpa using hcard

end GlobalTheory

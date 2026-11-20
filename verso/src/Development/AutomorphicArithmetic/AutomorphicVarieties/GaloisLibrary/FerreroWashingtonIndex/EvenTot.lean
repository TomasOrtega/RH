import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ToZModPowOneEqZeroIff

open UpperTheory.V.FW

/- English proof (translation)
Apply `Nat.totient_even` to reduce the goal to its premises. Unfold `ee`. Use `split_ifs with h`. Substitute `h` using the available equality. Evaluate the numerical expressions.

Use `hl.out.two_le` as an intermediate fact. Rewrite using `[pow_one]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem even_tot (l : ℕ) [hl : Fact l.Prime] : Even (Nat.totient (l ^ ee l)) := by
  apply Nat.totient_even
  unfold ee
  split_ifs with h
  · subst h; norm_num
  · have := hl.out.two_le
    rw [pow_one]; omega

/- English proof (translation)
The claim follows from `Nat.totient_pos.2 (pow_pos hl.out.pos _)`.
-/
private theorem pos_tot (l : ℕ) [hl : Fact l.Prime] : 0 < Nat.totient (l ^ ee l) :=
  Nat.totient_pos.2 (pow_pos hl.out.pos _)

/- English proof (translation)
Introduce `h`. Establish `h1 : (r : ℤ_[l]) = -(r : ℤ_[l])`. Use `congrArg Units.val h` as an intermediate fact. Simplify using `using this`. Conclude with `r.ne_zero (self_eq_neg.1 h1)`.
-/
private theorem neg_ne (l : ℕ) [Fact l.Prime] (r : ℤ_[l]ˣ) : r ≠ -r := by
  intro h
  have h1 : (r : ℤ_[l]) = -(r : ℤ_[l]) := by
    have := congrArg Units.val h
    simpa using this
  exact r.ne_zero (self_eq_neg.1 h1)

/- English proof (translation)
Introduce `l _`. Establish `hev` using `even_tot l`. Establish `hpos` using `pos_tot l`. Use `haveI : NeZero (Nat.totient (l ^ ee l)) := ⟨hpos.ne'⟩`. Establish `hfin : (WW l : Set ℤ_[l]ˣ).Finite`.

Establish `: Finite (rootsOfUnity (Nat.totient (l ^ ee l)) ℤ_[l])` using `inferInstance`. Conclude with `Set.finite_coe_iff.1 this`. Establish `hm1 : (-1 : ℤ_[l]ˣ) ∈ WW l`. Unfold `WW`. Rewrite using `[mem_rootsOfUnity]`.

Conclude with `hev.neg_one_pow`. Establish `hneg : ∀ w ∈ WW l, -w ∈ WW l` using `fun w hw => by`. Use `(WW l).mul_mem hm1 hw` as an intermediate fact. Simplify using `using this`. Use `letI : LinearOrder ℤ_[l]ˣ := linearOrderOfSTO WellOrderingRel`.

Set `R : Finset ℤ_[l]ˣ` to `hfin.toFinset.filter fun r => r < -r`. Establish `hR : ∀ r, r ∈ R ↔ r ∈ WW l ∧ r < -r` using `fun r => by simp [R]`. Establish `h4 : ∀ r ∈ R, -r ∉ R` using `fun r hr hr' => by`. Establish `h1` using `((hR _).1 hr).2`. Establish `h2` using `((hR _).1 hr').2`.

Rewrite `h2` using `[neg_neg]`. Conclude with `lt_asymm h1 h2`. Establish `h5 : ∀ w ∈ WW l, w ∈ R ∨ -w ∈ R` using `fun w hw => by`. Break down `lt_or_gt_of_ne (neg_ne l w) with h | h` into its components or cases. Conclude with `Or.inl ((hR _).2 ⟨hw, h⟩)`.

Conclude with `Or.inr ((hR _).2 ⟨hneg w hw, by rwa [neg_neg]⟩)`. Use `⟨R, ?_, fun r hr => ((hR r).1 hr).1, ?_, h4, h5, hm1, ?_⟩` and prove the remaining obligations. Break down `h5 1 (WW l).one_mem with h | h` into its components or cases. Conclude with `⟨_, h⟩`. Conclude with `⟨_, h⟩`.

Introduce `r hr r' hr' hne a b hab`. Assume the negation of the conclusion as `ha`. Establish `e1 : (r : ℤ_[l]) ^ Nat.totient (l ^ ee l) = 1` using `(mem_rootsOfUnity' _ _).1 ((hR _).1 hr).1`. Establish `e2 : (r' : ℤ_[l]) ^ Nat.totient (l ^ ee l) = 1` using `(mem_rootsOfUnity' _ _).1 ((hR _).1 hr').1`. Establish `e3` using `congrArg (· ^ Nat.totient (l ^ ee l)) hab`.

Simplify using `only [mul_pow, e1, e2, mul_one] at e3`. Establish `e4 : a ^ Nat.totient (l ^ ee l) = b ^ Nat.totient (l ^ ee l)` using `by exact_mod_cast e3`. Establish `ha' : (a : ℤ_[l]) ≠ 0` using `by exact_mod_cast ha`. Break down `(pow_eq_pow_iff_of_ne_zero hpos.ne').1 e4 with h | ⟨h, -⟩` into its components or cases. Substitute `h` using the available equality.

Conclude with `hne (Units.ext (mul_left_cancel₀ ha' hab))`. Establish `hb : (b : ℤ_[l]) = -(a : ℤ_[l])` using `by rw [h]; simp`. Rewrite `hab` using `[hb, neg_mul, ← mul_neg]`. Establish `: r = -r'` using `Units.ext (by simpa using mul_left_cancel₀ ha' hab)`. Conclude with `h4 r' hr' (this ▸ hr)`.

Introduce `n hn w hw h1`. Establish `hle : ee l ≤ n`. Apply the tactic sequence `unfold ee; split_ifs <;> omega`. Establish `h2 : PadicInt.toZModPow n (w : ℤ_[l]) = 1`. Use `congrArg Units.val h1` as an intermediate fact.

Simplify `this` using `[redU]`. Establish `h3 : PadicInt.toZModPow (ee l) (w : ℤ_[l]) = 1`. Rewrite using `[← PadicInt.zmod_cast_comp_toZModPow (ee l) n hle, RingHom.comp_apply, h2, map_one]`. Establish `h4 : ((redU l (ee l)).comp (WW l).subtype) ⟨w, hw⟩ = ((redU l (ee l)).comp (WW l).subtype) 1`. Rewrite using `[map_one]`.

Apply `Units.ext` to reduce the goal to its premises. Simplify `h3` using `[redU]`. Conclude with `congrArg Subtype.val ((teich l).1 h4)`.
-/
theorem UpperTheory.V.FW.reps :
    ∀ (l : ℕ) [Fact l.Prime], ∃ R : Finset ℤ_[l]ˣ, R.Nonempty ∧ (∀ r ∈ R, r ∈ WW l) ∧ (∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → ∀ a b : ℤ, (a : ℤ_[l]) * r = (b : ℤ_[l]) * r' → a = 0) ∧ (∀ r ∈ R, -r ∉ R) ∧ (∀ w ∈ WW l, w ∈ R ∨ -w ∈ R) ∧ (-1 : ℤ_[l]ˣ) ∈ WW l ∧ ∀ n, 2 ≤ n → ∀ w ∈ WW l, redU l n w = 1 → w = 1 := by
  intro l _
  classical
  have hev := even_tot l
  have hpos := pos_tot l
  haveI : NeZero (Nat.totient (l ^ ee l)) := ⟨hpos.ne'⟩
  have hfin : (WW l : Set ℤ_[l]ˣ).Finite := by
    have : Finite (rootsOfUnity (Nat.totient (l ^ ee l)) ℤ_[l]) := inferInstance
    exact Set.finite_coe_iff.1 this
  have hm1 : (-1 : ℤ_[l]ˣ) ∈ WW l := by
    unfold WW
    rw [mem_rootsOfUnity]
    exact hev.neg_one_pow
  have hneg : ∀ w ∈ WW l, -w ∈ WW l := fun w hw => by
    have := (WW l).mul_mem hm1 hw
    simpa using this
  letI : LinearOrder ℤ_[l]ˣ := linearOrderOfSTO WellOrderingRel
  let R : Finset ℤ_[l]ˣ := hfin.toFinset.filter fun r => r < -r
  have hR : ∀ r, r ∈ R ↔ r ∈ WW l ∧ r < -r := fun r => by simp [R]
  have h4 : ∀ r ∈ R, -r ∉ R := fun r hr hr' => by
    have h1 := ((hR _).1 hr).2
    have h2 := ((hR _).1 hr').2
    rw [neg_neg] at h2
    exact lt_asymm h1 h2
  have h5 : ∀ w ∈ WW l, w ∈ R ∨ -w ∈ R := fun w hw => by
    rcases lt_or_gt_of_ne (neg_ne l w) with h | h
    · exact Or.inl ((hR _).2 ⟨hw, h⟩)
    · exact Or.inr ((hR _).2 ⟨hneg w hw, by rwa [neg_neg]⟩)
  refine ⟨R, ?_, fun r hr => ((hR r).1 hr).1, ?_, h4, h5, hm1, ?_⟩
  · rcases h5 1 (WW l).one_mem with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  · intro r hr r' hr' hne a b hab
    by_contra ha
    have e1 : (r : ℤ_[l]) ^ Nat.totient (l ^ ee l) = 1 :=
      (mem_rootsOfUnity' _ _).1 ((hR _).1 hr).1
    have e2 : (r' : ℤ_[l]) ^ Nat.totient (l ^ ee l) = 1 :=
      (mem_rootsOfUnity' _ _).1 ((hR _).1 hr').1
    have e3 := congrArg (· ^ Nat.totient (l ^ ee l)) hab
    simp only [mul_pow, e1, e2, mul_one] at e3
    have e4 : a ^ Nat.totient (l ^ ee l) = b ^ Nat.totient (l ^ ee l) := by exact_mod_cast e3
    have ha' : (a : ℤ_[l]) ≠ 0 := by exact_mod_cast ha
    rcases (pow_eq_pow_iff_of_ne_zero hpos.ne').1 e4 with h | ⟨h, -⟩
    · subst h
      exact hne (Units.ext (mul_left_cancel₀ ha' hab))
    · have hb : (b : ℤ_[l]) = -(a : ℤ_[l]) := by rw [h]; simp
      rw [hb, neg_mul, ← mul_neg] at hab
      have : r = -r' := Units.ext (by simpa using mul_left_cancel₀ ha' hab)
      exact h4 r' hr' (this ▸ hr)
  · intro n hn w hw h1
    have hle : ee l ≤ n := by
      unfold ee; split_ifs <;> omega
    have h2 : PadicInt.toZModPow n (w : ℤ_[l]) = 1 := by
      have := congrArg Units.val h1
      simpa [redU] using this
    have h3 : PadicInt.toZModPow (ee l) (w : ℤ_[l]) = 1 := by
      rw [← PadicInt.zmod_cast_comp_toZModPow (ee l) n hle, RingHom.comp_apply, h2, map_one]
    have h4 : ((redU l (ee l)).comp (WW l).subtype) ⟨w, hw⟩ = ((redU l (ee l)).comp (WW l).subtype) 1 := by
      rw [map_one]
      apply Units.ext
      simpa [redU] using h3
    exact congrArg Subtype.val ((teich l).1 h4)

import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Establish `hinj : Set.InjOn (fun i => (c + i * b) % q) (Finset.range q : Set ℕ)`. Introduce `i hi j hj h`. Establish `h1 : c + i * b ≡ c + j * b [MOD q]` using `h`. Establish `h2 : i * b ≡ j * b [MOD q]` using `Nat.ModEq.add_left_cancel' c h1`. Establish `hc : Nat.gcd q b = 1` using `(Nat.coprime_of_lt_prime hb0 hb hq)`.

Establish `h3 : i ≡ j [MOD q]` using `Nat.ModEq.cancel_right_of_coprime hc h2`. Conclude with `Nat.ModEq.eq_of_lt_of_lt h3 (by simpa using hi) (by simpa using hj)`. Establish `him : (Finset.range q).image (fun i => (c + i * b) % q) = Finset.range q`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `Finset.mem_range.2 (Nat.mod_lt _ hq.pos)`. Rewrite using `[Finset.card_image_of_injOn hinj]`. Use `Finset.sum_image (f := fun x : ℕ => x) hinj` as an intermediate fact. Rewrite `this` using `[him]`.

Conclude with `this.symm`.
-/
private theorem modSum (q b c : ℕ) (hq : q.Prime) (hb0 : b ≠ 0) (hb : b < q) :
    ∑ i ∈ Finset.range q, (c + i * b) % q = ∑ i ∈ Finset.range q, i := by
  have hinj : Set.InjOn (fun i => (c + i * b) % q) (Finset.range q : Set ℕ) := by
    intro i hi j hj h
    have h1 : c + i * b ≡ c + j * b [MOD q] := h
    have h2 : i * b ≡ j * b [MOD q] := Nat.ModEq.add_left_cancel' c h1
    have hc : Nat.gcd q b = 1 := (Nat.coprime_of_lt_prime hb0 hb hq)
    have h3 : i ≡ j [MOD q] := Nat.ModEq.cancel_right_of_coprime hc h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 (by simpa using hi) (by simpa using hj)
  have him : (Finset.range q).image (fun i => (c + i * b) % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (Nat.mod_lt _ hq.pos)
    · rw [Finset.card_image_of_injOn hinj]
  have := Finset.sum_image (f := fun x : ℕ => x) hinj
  rw [him] at this
  exact this.symm

/- English proof (translation)
Establish `key : ∀ c : ℕ, q * ∑ i ∈ Finset.range q, (c + i * b) / q + ∑ i ∈ Finset.range q, i = q * c + ∑ i ∈ Finset.range q, i * b`. Introduce `c`. Rewrite using `[← modSum q b c hq hb0 hb, Finset.mul_sum, ← Finset.sum_add_distrib]`. Simplify using `only [Nat.div_add_mod]`. Rewrite using `[Finset.sum_add_distrib]`.

Simplify using the standard rewrite rules. Establish `h1` using `key c`. Establish `h2` using `key 0`. Simplify using `only [zero_add, mul_zero] at h2`. Apply `Nat.eq_of_mul_eq_mul_left hq.pos` to reduce the goal to its premises.

Rewrite using `[mul_add]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem divSum (q b c : ℕ) (hq : q.Prime) (hb0 : b ≠ 0) (hb : b < q) :
    ∑ i ∈ Finset.range q, (c + i * b) / q = c + ∑ i ∈ Finset.range q, (i * b) / q := by
  have key : ∀ c : ℕ, q * ∑ i ∈ Finset.range q, (c + i * b) / q + ∑ i ∈ Finset.range q, i
      = q * c + ∑ i ∈ Finset.range q, i * b := by
    intro c
    rw [← modSum q b c hq hb0 hb, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [Nat.div_add_mod]
    rw [Finset.sum_add_distrib]
    simp
  have h1 := key c
  have h2 := key 0
  simp only [zero_add, mul_zero] at h2
  apply Nat.eq_of_mul_eq_mul_left hq.pos
  rw [mul_add]
  omega

/- English proof (translation)
Break down `eq_or_ne b 0 with rfl | hb0` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[← divSum q b _ hq hb0 hb]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm q M, ← Nat.div_div_eq_div_mul]`.

Use `congr 1`. Rewrite using `[show (a + i * M) * b = a * b + i * b * M by ring, Nat.add_mul_div_right _ _ hM]`.
-/
private theorem divSum' (M q b a : ℕ) (hM : 0 < M) (hq : q.Prime) (hb : b < q) :
    ∑ i ∈ Finset.range q, (a + i * M) * b / (q * M) = a * b / M + ∑ i ∈ Finset.range q, (i * b) / q := by
  rcases eq_or_ne b 0 with rfl | hb0
  · simp
  rw [← divSum q b _ hq hb0 hb]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm q M, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [show (a + i * M) * b = a * b + i * b * M by ring, Nat.add_mul_div_right _ _ hM]

/- English proof (translation)
Establish `hM : 0 < M` using `by omega`. Use `symm`. Use `Finset.sum_nbij' (fun i => a + i * M) (fun n => n / M) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi`. Simplify using `only [Finset.mem_range, Finset.mem_filter] at hi ⊢`.

Use `⟨by nlinarith, by simp [Nat.mod_eq_of_lt ha]⟩` and prove the remaining obligations. Introduce `n hn`. Simplify using `only [Finset.mem_range, Finset.mem_filter] at hn ⊢`. Conclude with `(Nat.div_lt_iff_lt_mul hM).2 hn.1`. Introduce `i _`.

Rewrite using `[Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt ha, zero_add]`. Introduce `n hn`. Simplify using `only [Finset.mem_range, Finset.mem_filter] at hn ⊢`. Rewrite using `[← hn.2, mul_comm]`. Conclude with `Nat.mod_add_div n M`.

Introduce `i _`. Both sides reduce to the same expression.
-/
private theorem classSum (M q a : ℕ) (ha : a < M) (g : ℕ → ℕ) :
    ∑ n ∈ (Finset.range (q * M)).filter (fun n => n % M = a), g n = ∑ i ∈ Finset.range q, g (a + i * M) := by
  have hM : 0 < M := by omega
  symm
  refine Finset.sum_nbij' (fun i => a + i * M) (fun n => n / M) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_filter] at hi ⊢
    refine ⟨by nlinarith, by simp [Nat.mod_eq_of_lt ha]⟩
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_filter] at hn ⊢
    exact (Nat.div_lt_iff_lt_mul hM).2 hn.1
  · intro i _
    rw [Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt ha, zero_add]
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_filter] at hn ⊢
    rw [← hn.2, mul_comm]
    exact Nat.mod_add_div n M
  · intro i _
    rfl

/- English proof (translation)
Rewrite using `[← classSum M q _ (ZMod.val_lt _) g]`. Use `set s : (ZMod M)ˣ := u⁻¹ * t with hs`. Establish `hst : (q : ZMod M) * s = t`. Rewrite using `[← hu, hs, ← Units.val_mul, mul_inv_cancel_left]`. Establish `hmod : ∀ n : ℕ, n % M = (t : ZMod M).val ↔ (n : ZMod M) = t`.

Introduce `n`. Rewrite using `[← ZMod.val_natCast]`. Conclude with `(ZMod.val_injective M).eq_iff`. Establish `hmem : q * (s : ZMod M).val ∈ (Finset.range (q * M)).filter (fun n => n % M = (t : ZMod M).val)`. Simplify using `only [Finset.mem_range, Finset.mem_filter]`.

Use `⟨Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hq.pos, ?_⟩` and prove the remaining obligations. Rewrite using `[hmod]`. Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val, hst]`. Rewrite using `[← Finset.sum_erase_add _ _ hmem]`.

Use `congr 1`. Use `Finset.sum_bij (fun t' _ => (t' : ZMod (q * M)).val) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `t' ht'`. Simplify using `only [Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at ht' ⊢`. Use `⟨?_, ZMod.val_lt _, ?_⟩` and prove the remaining obligations.

Introduce `h`. Establish `hc` using `ZMod.val_coe_unit_coprime t'`. Rewrite `hc` using `[h]`. Conclude with `hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hc) (Dvd.intro _ rfl))`. Rewrite using `[hmod, ← ht', ZMod.unitsMap_val, ZMod.natCast_val]`.

Introduce `x _ y _ h`. Conclude with `Units.ext (ZMod.val_injective _ h)`. Introduce `n hn`. Simplify using `only [Finset.mem_range, Finset.mem_filter, Finset.mem_erase] at hn`. Take `⟨h1, h2, h3⟩` from `hn`.

Rewrite `h3` using `[hmod]`. Establish `hcM : n.Coprime M`. Rewrite using `[← ZMod.isUnit_iff_coprime, h3]`. Conclude with `t.isUnit`. Establish `hcq : n.Coprime q`.

Rewrite using `[Nat.coprime_comm, hq.coprime_iff_not_dvd]`. Introduce and unpack `⟨k, rfl⟩`. Apply `h1` to reduce the goal to its premises. Use `congr 1`. Establish `hk : k < M` using `Nat.lt_of_mul_lt_mul_left h2`.

Establish `: (k : ZMod M) = s`. Apply `u.isUnit.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[hu, hst, ← h3]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[← this, ZMod.val_natCast, Nat.mod_eq_of_lt hk]`. Establish `hv : ((ZMod.unitOfCoprime n (Nat.Coprime.mul_right hcq hcM) : (ZMod (q * M))ˣ) : ZMod (q * M)).val = n`. Rewrite using `[ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt h2]`. Use `⟨ZMod.unitOfCoprime n (Nat.Coprime.mul_right hcq hcM), ?_, hv⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[ZMod.unitsMap_val, ← ZMod.natCast_val, hv, h3]`. Introduce `_ _`. Both sides reduce to the same expression.
-/
private theorem unitSum (M q : ℕ) [NeZero M] [NeZero (q * M)] (hq : q.Prime) (u : (ZMod M)ˣ) (hu : (u : ZMod M) = q)
    (t : (ZMod M)ˣ) (g : ℕ → ℕ) :
    ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t),
      g (t' : ZMod (q * M)).val + g (q * ((u⁻¹ * t : (ZMod M)ˣ) : ZMod M).val)
      = ∑ i ∈ Finset.range q, g ((t : ZMod M).val + i * M) := by
  rw [← classSum M q _ (ZMod.val_lt _) g]
  set s : (ZMod M)ˣ := u⁻¹ * t with hs
  have hst : (q : ZMod M) * s = t := by
    rw [← hu, hs, ← Units.val_mul, mul_inv_cancel_left]
  have hmod : ∀ n : ℕ, n % M = (t : ZMod M).val ↔ (n : ZMod M) = t := by
    intro n
    rw [← ZMod.val_natCast]
    exact (ZMod.val_injective M).eq_iff
  have hmem : q * (s : ZMod M).val ∈ (Finset.range (q * M)).filter (fun n => n % M = (t : ZMod M).val) := by
    simp only [Finset.mem_range, Finset.mem_filter]
    refine ⟨Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hq.pos, ?_⟩
    rw [hmod]
    push_cast
    rw [ZMod.natCast_zmod_val, hst]
  rw [← Finset.sum_erase_add _ _ hmem]
  congr 1
  refine Finset.sum_bij (fun t' _ => (t' : ZMod (q * M)).val) ?_ ?_ ?_ ?_
  · intro t' ht'
    simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at ht' ⊢
    refine ⟨?_, ZMod.val_lt _, ?_⟩
    · intro h
      have hc := ZMod.val_coe_unit_coprime t'
      rw [h] at hc
      exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hc) (Dvd.intro _ rfl))
    · rw [hmod, ← ht', ZMod.unitsMap_val, ZMod.natCast_val]
  · intro x _ y _ h
    exact Units.ext (ZMod.val_injective _ h)
  · intro n hn
    simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_erase] at hn
    obtain ⟨h1, h2, h3⟩ := hn
    rw [hmod] at h3
    have hcM : n.Coprime M := by
      rw [← ZMod.isUnit_iff_coprime, h3]
      exact t.isUnit
    have hcq : n.Coprime q := by
      rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
      rintro ⟨k, rfl⟩
      apply h1
      congr 1
      have hk : k < M := Nat.lt_of_mul_lt_mul_left h2
      have : (k : ZMod M) = s := by
        apply u.isUnit.mul_left_cancel
        rw [hu, hst, ← h3]
        push_cast
        rfl
      rw [← this, ZMod.val_natCast, Nat.mod_eq_of_lt hk]
    have hv : ((ZMod.unitOfCoprime n (Nat.Coprime.mul_right hcq hcM) : (ZMod (q * M))ˣ) : ZMod (q * M)).val = n := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt h2]
    refine ⟨ZMod.unitOfCoprime n (Nat.Coprime.mul_right hcq hcM), ?_, hv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Units.ext
    rw [ZMod.unitsMap_val, ← ZMod.natCast_val, hv, h3]
  · intro _ _
    rfl

/- English proof (translation)
Establish `h` using `unitSum M q hq u hu t (fun n => n * b / (q * M))`. Rewrite `h` using `[divSum' M q b _ (Nat.pos_of_ne_zero (NeZero.ne M)) hq hb, mul_assoc, Nat.mul_div_mul_left _ _ hq.pos]`. Rewrite using `[← Nat.cast_sum, ← Nat.cast_add, h, Nat.cast_add]`.
-/
private theorem halfSum (M q b : ℕ) [NeZero M] [NeZero (q * M)] (hq : q.Prime) (hb : b < q) (u : (ZMod M)ˣ)
    (hu : (u : ZMod M) = q) (t : (ZMod M)ˣ) :
    ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t),
      (((t' : ZMod (q * M)).val * b / (q * M) : ℕ) : ℤ) + ((((u⁻¹ * t : (ZMod M)ˣ) : ZMod M).val * b / M : ℕ) : ℤ)
      = (((t : ZMod M).val * b / M : ℕ) : ℤ) + ((∑ i ∈ Finset.range q, (i * b) / q : ℕ) : ℤ) := by
  have h := unitSum M q hq u hu t (fun n => n * b / (q * M))
  rw [divSum' M q b _ (Nat.pos_of_ne_zero (NeZero.ne M)) hq hb, mul_assoc, Nat.mul_div_mul_left _ _ hq.pos] at h
  rw [← Nat.cast_sum, ← Nat.cast_add, h, Nat.cast_add]

/- English proof (translation)
Introduce `M q b _ _ hq hb u hu t`. Establish `h1` using `halfSum M q b hq hb u hu t`. Establish `h2` using `halfSum M q b hq hb u hu (-t)`. Establish `hneg : ∀ x : (ZMod (q * M))ˣ, ZMod.unitsMap (Dvd.intro_left q rfl) (-x) = -ZMod.unitsMap (Dvd.intro_left q rfl) x`. Introduce `x`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_neg, ZMod.unitsMap_val, ZMod.unitsMap_val, Units.val_neg, ZMod.cast_neg (Dvd.intro_left q rfl)]`. Establish `h3 : ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t), (((-(t' : ZMod (q * M))).val * b / (q * M) : ℕ) : ℤ) = ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = -t), (((t' : ZMod (q * …`. Use `Finset.sum_equiv (Equiv.neg _) ?_ ?_` and prove the remaining obligations. Introduce `x`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.neg_apply, hneg, neg_inj]`. Introduce `x _`. Simplify using `only [Equiv.neg_apply, Units.val_neg]`. Rewrite `h2` using `[mul_neg, Units.val_neg, Units.val_neg]`. Simplify using `only [th]`.

Rewrite using `[Finset.sum_sub_distrib, h3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.ML.thDist :
    ∀ (M q b : ℕ) [NeZero M] [NeZero (q * M)], q.Prime → b < q → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ t : (ZMod M)ˣ,
    ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t), th (q * M) b t' = th M b t - th M b (u⁻¹ * t : (ZMod M)ˣ) := by
  intro M q b _ _ hq hb u hu t
  have h1 := halfSum M q b hq hb u hu t
  have h2 := halfSum M q b hq hb u hu (-t)
  have hneg : ∀ x : (ZMod (q * M))ˣ, ZMod.unitsMap (Dvd.intro_left q rfl) (-x) = -ZMod.unitsMap (Dvd.intro_left q rfl) x := by
    intro x
    apply Units.ext
    rw [Units.val_neg, ZMod.unitsMap_val, ZMod.unitsMap_val, Units.val_neg, ZMod.cast_neg (Dvd.intro_left q rfl)]
  have h3 : ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = t),
      (((-(t' : ZMod (q * M))).val * b / (q * M) : ℕ) : ℤ) =
      ∑ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (Dvd.intro_left q rfl) t' = -t),
      (((t' : ZMod (q * M)).val * b / (q * M) : ℕ) : ℤ) := by
    refine Finset.sum_equiv (Equiv.neg _) ?_ ?_
    · intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.neg_apply, hneg, neg_inj]
    · intro x _
      simp only [Equiv.neg_apply, Units.val_neg]
  rw [mul_neg, Units.val_neg, Units.val_neg] at h2
  simp only [th]
  rw [Finset.sum_sub_distrib, h3]
  linarith

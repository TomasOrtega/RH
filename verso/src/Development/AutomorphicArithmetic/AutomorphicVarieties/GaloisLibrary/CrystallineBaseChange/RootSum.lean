import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

open UpperTheory.V.Af

namespace UpperTheory.V.Br

/- English proof (translation)
Proceed by induction on `B using Multiset.induction_on with`. Consider the case `empty`. Use `⟨{0}, by simp, fun C hC => ?_⟩` and prove the remaining obligations. Simplify using `using hC`. Consider the case `cons b B ih`.

Take `⟨T, hT, hm⟩` from `ih`. Use `⟨((Polynomial.nthRoots f b).toFinset ×ˢ T).image fun x => x.1 ::ₘ x.2, ?_, fun C hC => ?_⟩` and prove the remaining obligations. Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.card_product, Multiset.card_cons, pow_succ']`. Conclude with `Nat.mul_le_mul (((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots f b)).trans h2) hT`.

Take `⟨a, ha, hab, hr⟩` from `(Multiset.map_eq_cons _ _ _ _).2 hC`. Use `Finset.mem_image.2 ⟨(a, C.erase a), Finset.mem_product.2 ⟨?_, hm _ hr⟩, Multiset.cons_erase ha⟩` and prove the remaining obligations. Conclude with `Multiset.mem_toFinset.2 ((Polynomial.mem_nthRoots h1).2 hab)`.
-/
private theorem roots_finset (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) (B : Multiset ℂ) :
    ∃ T : Finset (Multiset ℂ), T.card ≤ 2 ^ B.card ∧ ∀ C : Multiset ℂ, C.map (· ^ f) = B → C ∈ T := by
  classical
  induction B using Multiset.induction_on with
  | empty =>
    refine ⟨{0}, by simp, fun C hC => ?_⟩
    simpa using hC
  | cons b B ih =>
    obtain ⟨T, hT, hm⟩ := ih
    refine ⟨((Polynomial.nthRoots f b).toFinset ×ˢ T).image fun x => x.1 ::ₘ x.2, ?_, fun C hC => ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Multiset.card_cons, pow_succ']
      exact Nat.mul_le_mul (((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots f b)).trans h2) hT
    · obtain ⟨a, ha, hab, hr⟩ := (Multiset.map_eq_cons _ _ _ _).2 hC
      refine Finset.mem_image.2 ⟨(a, C.erase a), Finset.mem_product.2 ⟨?_, hm _ hr⟩, Multiset.cons_erase ha⟩
      exact Multiset.mem_toFinset.2 ((Polynomial.mem_nthRoots h1).2 hab)

/- English proof (translation)
Take `⟨T, hT, hm⟩` from `roots_finset f h1 h2 B`. Set `g : {C : Multiset ℂ // C.map (· ^ f) = B} → T` to `fun C => ⟨C.1, hm _ C.2⟩`. Establish `hg : Function.Injective g` using `fun x y h => Subtype.ext (congrArg Subtype.val h :)`. Use `⟨Finite.of_injective g hg, (Nat.card_le_card_of_injective g hg).trans ?_⟩` and prove the remaining obligations. Simplify using `using hT`.
-/
private theorem roots_card (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) (B : Multiset ℂ) :
    Finite {C : Multiset ℂ // C.map (· ^ f) = B} ∧ Nat.card {C : Multiset ℂ // C.map (· ^ f) = B} ≤ 2 ^ B.card := by
  obtain ⟨T, hT, hm⟩ := roots_finset f h1 h2 B
  let g : {C : Multiset ℂ // C.map (· ^ f) = B} → T := fun C => ⟨C.1, hm _ C.2⟩
  have hg : Function.Injective g := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  refine ⟨Finite.of_injective g hg, (Nat.card_le_card_of_injective g hg).trans ?_⟩
  simpa using hT

/- English proof (translation)
Use `haveI := D.fin`. Use `haveI := Fintype.ofFinite D.S`. Use `haveI : ∀ s, Finite {C : Multiset ℂ // C.map (· ^ f) = D.β s} := fun s => (roots_card f h1 h2 _).1`. Set `e` to `Equiv.subtypeProdEquivSigmaSubtype fun (s : D.S) (C : Multiset ℂ) => C.map (· ^ f) = D.β s`. Use `⟨Finite.of_equiv _ e.symm, ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.card_congr e, Nat.card_sigma]`. Use `(Finset.sum_le_card_nsmul _ _ (2 ^ n) fun s _ => ?_).trans ?_` and prove the remaining obligations. Use `(roots_card f h1 h2 (D.β s)).2` as an intermediate fact. Rewrite `this` using `[D.card]`. Then use the resulting hypothesis. Simplify using `[mul_comm]`.
-/
private theorem pairs_card {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) :
    Finite {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ∧
      Nat.card {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ≤ 2 ^ n * Nat.card D.S := by
  haveI := D.fin
  haveI := Fintype.ofFinite D.S
  haveI : ∀ s, Finite {C : Multiset ℂ // C.map (· ^ f) = D.β s} := fun s => (roots_card f h1 h2 _).1
  let e := Equiv.subtypeProdEquivSigmaSubtype fun (s : D.S) (C : Multiset ℂ) => C.map (· ^ f) = D.β s
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_sigma]
  refine (Finset.sum_le_card_nsmul _ _ (2 ^ n) fun s _ => ?_).trans ?_
  · have := (roots_card f h1 h2 (D.β s)).2
    rwa [D.card] at this
  · simp [mul_comm]

/- English proof (translation)
Use `haveI := (pairs_card D f h1 h2).1`. Take `⟨e, he⟩` from `D.conj σ`. Set `g : {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} → {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1}` to `fun x => ⟨(e x.1.1, x.1.2.map σ), by show (x.1.2.map σ).map (· ^ f) = D.β (e x.1.1)`. Rewrite using `[he, ← x.2, Multiset.map_map, Multiset.map_map]`. Conclude with `Multiset.map_congr rfl fun b _ => by simp⟩`.

Establish `hg : Function.Injective g` using `fun x y h => by`. Establish `h'` using `congrArg Subtype.val h`. Simplify using `only [g, Prod.mk.injEq] at h'`. Conclude with `Subtype.ext (Prod.ext (e.injective h'.1) (Multiset.map_injective σ.injective h'.2))`. Conclude with `⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hg), fun _ => rfl⟩`.
-/
private theorem pairs_conj {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2)
    (σ : ℂ ≃+* ℂ) :
    ∃ e : {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ≃ {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1},
      ∀ x, (e x).1.2 = x.1.2.map σ := by
  haveI := (pairs_card D f h1 h2).1
  obtain ⟨e, he⟩ := D.conj σ
  let g : {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} → {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} :=
    fun x => ⟨(e x.1.1, x.1.2.map σ), by
      show (x.1.2.map σ).map (· ^ f) = D.β (e x.1.1)
      rw [he, ← x.2, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun b _ => by simp⟩
  have hg : Function.Injective g := fun x y h => by
    have h' := congrArg Subtype.val h
    simp only [g, Prod.mk.injEq] at h'
    exact Subtype.ext (Prod.ext (e.injective h'.1) (Multiset.map_injective σ.injective h'.2))
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hg), fun _ => rfl⟩

/- English proof (translation)
Use `IsIntegral.of_pow (n := f) h1 ?_` and prove the remaining obligations. Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[mul_pow, Nat.cast_pow, ← zpow_natCast, ← zpow_natCast (p : ℂ), ← zpow_mul, ← zpow_mul, mul_comm a]`.
-/
private theorem int_root (p f : ℕ) (h1 : 1 ≤ f) (a : ℤ) (b : ℂ) (h : IsIntegral ℤ (((p ^ f : ℕ) : ℂ) ^ a * b ^ f)) :
    IsIntegral ℤ ((p : ℂ) ^ a * b) := by
  refine IsIntegral.of_pow (n := f) h1 ?_
  convert h using 1
  rw [mul_pow, Nat.cast_pow, ← zpow_natCast, ← zpow_natCast (p : ℂ), ← zpow_mul, ← zpow_mul, mul_comm a]

end UpperTheory.V.Br

open UpperTheory.V.Br in
/- English proof (translation)
Introduce `n p hp m wt I _ q f hf D`. Use `haveI : ∀ i, Finite {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} := fun i => (pairs_card (D i) (f i) (hf i).1 (hf i).2.1).1`. Establish `hmem : ∀ i (x : {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1}), ∀ b ∈ x.1.2, b ^ f i ∈ (D i).β x.1.1` using `fun i x b hb => by`. Rewrite using `[← x.2]`. Conclude with `Multiset.mem_map_of_mem _ hb`.

Use `⟨⟨Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool, inferInstance, fun x => x.2.1.1.2, ?_, ?_, ?_, ?_, ?_⟩, ?_, id, Function.injective_id, fun _ => rfl⟩` and prove the remaining obligations. Introduce and unpack `⟨i, x, t⟩`. Use `(D i).card x.1.1` as an intermediate fact. Rewrite `this` using `[← x.2, Multiset.card_map]`. Conclude with `this`.

Introduce `σ choose e he using fun i => pairs_conj (D i) (f i) (hf i).1 (hf i).2.1 σ`. Conclude with `⟨Equiv.sigmaCongrRight fun i => (e i).prodCongr (Equiv.refl _), fun x => he x.1 x.2.1⟩`. Introduce and unpack `⟨i, x, t⟩ b hb`. Establish `h` using `(D i).pure _ _ (hmem i x b hb)`. Establish `hp0 : (0 : ℝ) ≤ p` using `Nat.cast_nonneg p`.

Establish `hq : ((q i : ℕ) : ℝ) = (p : ℝ) ^ f i` using `by rw [(hf i).2.2, Nat.cast_pow]`. Rewrite `h` using `[norm_pow, hq, ← Real.rpow_natCast (p : ℝ), ← Real.rpow_mul hp0, mul_comm, Real.rpow_mul hp0, Real.rpow_natCast]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hp0 _) (by have := (hf i).1; omega)).1 h`. Introduce and unpack `a ha ⟨i, x, t⟩ b hb`. Establish `h` using `(D i).int a ha _ _ (hmem i x b hb)`.

Use `int_root p (f i) (hf i).1 a b ?_` and prove the remaining obligations. Rewrite using `[← (hf i).2.2]`. Conclude with `h`. Introduce and unpack `a ha ⟨i, x, t⟩ b hb`. Establish `h` using `(D i).intInv a ha _ _ (hmem i x b hb)`.

Use `int_root p (f i) (hf i).1 a b⁻¹ ?_` and prove the remaining obligations. Rewrite using `[← (hf i).2.2, inv_pow]`. Conclude with `h`. Use `show Nat.card (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) ≤ _`. Rewrite using `[Nat.card_sigma, Finset.mul_sum]`.

Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]`. Use `(pairs_card (D i) (f i) (hf i).1 (hf i).2.1).2` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Br.rootSum :
    UpperTheory.V.Br.RootSum := by
  intro n p hp m wt I _ q f hf D
  haveI : ∀ i, Finite {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} :=
    fun i => (pairs_card (D i) (f i) (hf i).1 (hf i).2.1).1
  have hmem : ∀ i (x : {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1}), ∀ b ∈ x.1.2,
      b ^ f i ∈ (D i).β x.1.1 := fun i x b hb => by
    rw [← x.2]
    exact Multiset.mem_map_of_mem _ hb
  refine ⟨⟨Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool, inferInstance,
    fun x => x.2.1.1.2, ?_, ?_, ?_, ?_, ?_⟩, ?_, id, Function.injective_id, fun _ => rfl⟩
  · rintro ⟨i, x, t⟩
    have := (D i).card x.1.1
    rw [← x.2, Multiset.card_map] at this
    exact this
  · intro σ
    choose e he using fun i => pairs_conj (D i) (f i) (hf i).1 (hf i).2.1 σ
    exact ⟨Equiv.sigmaCongrRight fun i => (e i).prodCongr (Equiv.refl _), fun x => he x.1 x.2.1⟩
  · rintro ⟨i, x, t⟩ b hb
    have h := (D i).pure _ _ (hmem i x b hb)
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hq : ((q i : ℕ) : ℝ) = (p : ℝ) ^ f i := by rw [(hf i).2.2, Nat.cast_pow]
    rw [norm_pow, hq, ← Real.rpow_natCast (p : ℝ), ← Real.rpow_mul hp0, mul_comm, Real.rpow_mul hp0, Real.rpow_natCast] at h
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hp0 _) (by have := (hf i).1; omega)).1 h
  · rintro a ha ⟨i, x, t⟩ b hb
    have h := (D i).int a ha _ _ (hmem i x b hb)
    refine int_root p (f i) (hf i).1 a b ?_
    rw [← (hf i).2.2]
    exact h
  · rintro a ha ⟨i, x, t⟩ b hb
    have h := (D i).intInv a ha _ _ (hmem i x b hb)
    refine int_root p (f i) (hf i).1 a b⁻¹ ?_
    rw [← (hf i).2.2, inv_pow]
    exact h
  · show Nat.card (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) ≤ _
    rw [Nat.card_sigma, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    have := (pairs_card (D i) (f i) (hf i).1 (hf i).2.1).2
    calc _ ≤ 2 ^ n * Nat.card (D i).S * 2 := Nat.mul_le_mul_right _ this
      _ = _ := by ring

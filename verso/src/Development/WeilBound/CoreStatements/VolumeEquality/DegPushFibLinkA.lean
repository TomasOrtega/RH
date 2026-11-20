import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs

noncomputable section

namespace SheetDecomposition

open GlobalTheory.CompanionTheory.Ar

section

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, hk, rfl⟩` from `hx`.

Use `⟨Pi.single k 1, fun m hm => ?_, ?_⟩` and prove the remaining obligations. Establish `: m ≠ k` using `by rintro rfl; exact absurd hk (not_lt.2 hm)`. Simplify using `[this]`. Simplify using `[Pi.single_apply]`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨B, hB, rfl⟩` from `hx`. Take `⟨C, hC, rfl⟩` from `hy`. Conclude with `⟨B + C, fun m hm => by simp [hB m hm, hC m hm], by simp [add_smul, Finset.sum_add_distrib]⟩`. Consider the case `smul a x _ hx`.

Take `⟨B, hB, rfl⟩` from `hx`. Conclude with `⟨a • B, fun m hm => by simp [hB m hm], by simp [Finset.smul_sum, mul_smul]⟩`. Introduce and unpack `⟨B, hB, rfl⟩`. Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (m : ℕ) < n`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, h, rfl⟩)`. Simplify using `[hB m (not_lt.1 h)]`.
-/
theorem mem_flagStep_iff (f : Fin r → V) (n : ℕ) (x : V) :
    x ∈ flagStep Ω f n ↔ ∃ B : Fin r → Ω, (∀ m : Fin r, n ≤ (m : ℕ) → B m = 0) ∧ x = ∑ m, B m • f m := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨Pi.single k 1, fun m hm => ?_, ?_⟩
      · have : m ≠ k := by rintro rfl; exact absurd hk (not_lt.2 hm)
        simp [this]
      · simp [Pi.single_apply]
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨B, hB, rfl⟩ := hx
      obtain ⟨C, hC, rfl⟩ := hy
      exact ⟨B + C, fun m hm => by simp [hB m hm, hC m hm], by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul a x _ hx =>
      obtain ⟨B, hB, rfl⟩ := hx
      exact ⟨a • B, fun m hm => by simp [hB m hm], by simp [Finset.smul_sum, mul_smul]⟩
  · rintro ⟨B, hB, rfl⟩
    refine Submodule.sum_mem _ fun m _ => ?_
    by_cases h : (m : ℕ) < n
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, h, rfl⟩)
    · simp [hB m (not_lt.1 h)]

/- English proof (translation)
Take `⟨B, hB, e⟩` from `(mem_flagStep_iff f n _).1 h`. Use `Fintype.linearIndependent_iff.1 hf (a - B) (by simp [sub_smul, Finset.sum_sub_distrib, e]) m` as an intermediate fact. Simplify `this` using `[hB m hm]`.
-/
theorem coeff_zero_of_mem {f : Fin r → V} (hf : LinearIndependent Ω f) {n : ℕ} {a : Fin r → Ω}
    (h : ∑ m, a m • f m ∈ flagStep Ω f n) (m : Fin r) (hm : n ≤ (m : ℕ)) : a m = 0 := by
  obtain ⟨B, hB, e⟩ := (mem_flagStep_iff f n _).1 h
  have := Fintype.linearIndependent_iff.1 hf (a - B) (by simp [sub_smul, Finset.sum_sub_distrib, e]) m
  simpa [hB m hm] using this

/- English proof (translation)
Use `coeff_zero_of_mem hf (a := Pi.single m t) (n := m) (by simpa [Pi.single_apply] using h) m le_rfl` as an intermediate fact. Simplify using `using this`.
-/
theorem smul_mem_flagStep {f : Fin r → V} (hf : LinearIndependent Ω f) {m : Fin r} {t : Ω}
    (h : t • f m ∈ flagStep Ω f m) : t = 0 := by
  classical
  have := coeff_zero_of_mem hf (a := Pi.single m t) (n := m) (by simpa [Pi.single_apply] using h) m le_rfl
  simpa using this

/- English proof (translation)
Use `(mem_flagStep_iff f m _).2 ⟨B - Pi.single m (B m), fun m' hm' => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `e : m' = m`. Simplify using `[e]`. Establish `: (m' : ℕ) ≠ m` using `fun h => e (Fin.ext h)`. Simplify using `[e, hB m' (by omega)]`.

Simplify using `[sub_smul, Finset.sum_sub_distrib, Pi.single_apply]`.
-/
theorem sum_sub_mem (f : Fin r → V) (m : Fin r) {B : Fin r → Ω} (hB : ∀ m' : Fin r, (m : ℕ) + 1 ≤ (m' : ℕ) → B m' = 0) :
    ∑ m', B m' • f m' - B m • f m ∈ flagStep Ω f m := by
  classical
  refine (mem_flagStep_iff f m _).2 ⟨B - Pi.single m (B m), fun m' hm' => ?_, ?_⟩
  · by_cases e : m' = m
    · simp [e]
    · have : (m' : ℕ) ≠ m := fun h => e (Fin.ext h)
      simp [e, hB m' (by omega)]
  · simp [sub_smul, Finset.sum_sub_distrib, Pi.single_apply]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨m, Nat.lt_succ_self _, rfl⟩`.
-/
theorem self_mem_flagStep (f : Fin r → V) (m : Fin r) : f m ∈ flagStep Ω f (m + 1) :=
  Submodule.subset_span ⟨m, Nat.lt_succ_self _, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)`.
-/
theorem flagStep_mono (f : Fin r → V) {n n' : ℕ} (h : n ≤ n') : flagStep Ω f n ≤ flagStep Ω f n' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

/- English proof (translation)
Take `⟨B, hB, rfl⟩` from `(mem_flagStep_iff f _ _).1 hx`. Conclude with `⟨B m, sum_sub_mem f m hB⟩`.
-/
theorem exists_lead (f : Fin r → V) (m : Fin r) {x : V} (hx : x ∈ flagStep Ω f (m + 1)) :
    ∃ t : Ω, x - t • f m ∈ flagStep Ω f m := by
  obtain ⟨B, hB, rfl⟩ := (mem_flagStep_iff f _ _).1 hx
  exact ⟨B m, sum_sub_mem f m hB⟩

/- English proof (translation)
Use `⟨?_, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Establish `: (1 : Ω) • bb m ∈ flagStep Ω bb m` using `by simpa [hf] using ht`. Conclude with `one_ne_zero (smul_mem_flagStep hb this)`. Introduce and unpack `t' ⟨e, he, h⟩`.

Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 he`. Establish `e1 : ∑ l, a l • bb l = ∑ l, (a l : Ω) • bb l` using `rfl`. Rewrite `h` using `[e1]`. Establish `h1 : ∑ l, (a l : Ω) • bb l ∈ flagStep Ω bb (m + 1)`. Rewrite using `[hf]`.

Use `Submodule.add_mem _ (flagStep_mono b₀ (Nat.le_succ _) h) (Submodule.smul_mem _ t' (self_mem_flagStep (Ω := Ω) b₀ m))` as an intermediate fact. Simplify using `using this`. Establish `h2` using `sum_sub_mem bb m (B := fun l => (a l : Ω)) (coeff_zero_of_mem hb h1)`. Rewrite `h2` using `[hf]`. Establish `h3 : (t' - a m * t) • b₀ m ∈ flagStep Ω b₀ m`.

Use `Submodule.sub_mem _ (Submodule.add_mem _ h2 (Submodule.smul_mem _ (a m : Ω) ht)) h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [sub_smul, smul_sub, mul_smul]`. Normalize the expressions using the abelian group laws. Establish `h4` using `smul_mem_flagStep h₀ h3`.

Conclude with `Submodule.mem_span_singleton.2 ⟨a m, by show (a m : Ω) * t = t'`. Take the linear combination `-h4⟩`. Introduce and unpack `_ rfl`. Conclude with `Submodule.subset_span ⟨bb m, Submodule.subset_span ⟨m, rfl⟩, ht⟩`.
-/
theorem gr_span {b₀ bb : Fin r → V} (h₀ : LinearIndependent Ω b₀) (hb : LinearIndependent Ω bb)
    (hf : ∀ n, flagStep Ω bb n = flagStep Ω b₀ n) (R : Subring Ω) (m : Fin r) {t : Ω}
    (ht : bb m - t • b₀ m ∈ flagStep Ω b₀ m) :
    t ≠ 0 ∧ Submodule.span R {t' : Ω | ∃ e ∈ Submodule.span R (Set.range bb), e - t' • b₀ m ∈ flagStep Ω b₀ m} =
      Submodule.span R {t} := by
  refine ⟨?_, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
  · rintro rfl
    have : (1 : Ω) • bb m ∈ flagStep Ω bb m := by simpa [hf] using ht
    exact one_ne_zero (smul_mem_flagStep hb this)
  · rintro t' ⟨e, he, h⟩
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he
    have e1 : ∑ l, a l • bb l = ∑ l, (a l : Ω) • bb l := rfl
    rw [e1] at h
    have h1 : ∑ l, (a l : Ω) • bb l ∈ flagStep Ω bb (m + 1) := by
      rw [hf]
      have := Submodule.add_mem _ (flagStep_mono b₀ (Nat.le_succ _) h)
        (Submodule.smul_mem _ t' (self_mem_flagStep (Ω := Ω) b₀ m))
      simpa using this
    have h2 := sum_sub_mem bb m (B := fun l => (a l : Ω)) (coeff_zero_of_mem hb h1)
    rw [hf] at h2
    have h3 : (t' - a m * t) • b₀ m ∈ flagStep Ω b₀ m := by
      have := Submodule.sub_mem _ (Submodule.add_mem _ h2 (Submodule.smul_mem _ (a m : Ω) ht)) h
      convert this using 1
      simp only [sub_smul, smul_sub, mul_smul]
      abel
    have h4 := smul_mem_flagStep h₀ h3
    exact Submodule.mem_span_singleton.2 ⟨a m, by
      show (a m : Ω) * t = t'
      linear_combination -h4⟩
  · rintro _ rfl
    exact Submodule.subset_span ⟨bb m, Submodule.subset_span ⟨m, rfl⟩, ht⟩

end

section

variable {Ω₃ : Type} [Field Ω₃] (O : ValuationSubring Ω₃)

/- English proof (translation)
Establish `e : (H * G : Matrix (Fin n) (Fin n) Ω₃) = fun a => ∑ l, H a l • G l`. Use function extensionality and compare the values at `a b`. Simplify using `[Matrix.mul_apply]`. Establish `h` using `(Matrix.detRowAlternating (R := Ω₃) (n := Fin n)).toMultilinearMap.map_sum (fun a l => H a l • G l)`. Establish `h' : (H * G).det = (Matrix.detRowAlternating (R` using `Ω₃) (n := Fin n)).toMultilinearMap (fun a => ∑ l, H a l • G l) := by`.

Rewrite using `[e]`. Both sides reduce to the same expression. Rewrite using `[h', h]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ]`.

Both sides reduce to the same expression.
-/
theorem det_mul_rows {n r : ℕ} (H : Matrix (Fin n) (Fin r) Ω₃) (G : Matrix (Fin r) (Fin n) Ω₃) :
    (H * G).det = ∑ I : Fin n → Fin r, (∏ a, H a (I a)) * (Matrix.of fun a b => G (I a) b).det := by
  have e : (H * G : Matrix (Fin n) (Fin n) Ω₃) = fun a => ∑ l, H a l • G l := by
    funext a b
    simp [Matrix.mul_apply]
  have h := (Matrix.detRowAlternating (R := Ω₃) (n := Fin n)).toMultilinearMap.map_sum (fun a l => H a l • G l)
  have h' : (H * G).det = (Matrix.detRowAlternating (R := Ω₃) (n := Fin n)).toMultilinearMap (fun a => ∑ l, H a l • G l) := by
    rw [e]; rfl
  rw [h', h]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

/- English proof (translation)
Use `le_antisymm (Finset.sup_le fun I _ => (O.valuation_le_one_iff _).2 ?_) ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_apply']`. Conclude with `sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ => hG _ _)`. Establish `e` using `det_mul_rows H G`. Rewrite `e` using `[h, Matrix.det_one]`.

Rewrite using `[← O.valuation.map_one, e]`. Use `Valuation.map_sum_le _ fun I _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `(mul_le_of_le_one_left' ((O.valuation_le_one_iff _).2 (prod_mem fun a _ => hH _ _))).trans ?_` and prove the remaining obligations. Conclude with `Finset.le_sup (f := fun I : Fin n → Fin r => O.valuation (Matrix.of fun a b => G (I a) b).det) (Finset.mem_univ I)`.
-/
theorem sup_minor_eq_one {n r : ℕ} (H : Matrix (Fin n) (Fin r) Ω₃) (G : Matrix (Fin r) (Fin n) Ω₃) (hH : ∀ a l, H a l ∈ O)
    (hG : ∀ l b, G l b ∈ O) (h : H * G = 1) :
    (Finset.univ.sup fun I : Fin n → Fin r => O.valuation (Matrix.of fun a b => G (I a) b).det) = 1 := by
  refine le_antisymm (Finset.sup_le fun I _ => (O.valuation_le_one_iff _).2 ?_) ?_
  · rw [Matrix.det_apply']
    exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ => hG _ _)
  · have e := det_mul_rows H G
    rw [h, Matrix.det_one] at e
    rw [← O.valuation.map_one, e]
    refine Valuation.map_sum_le _ fun I _ => ?_
    rw [map_mul]
    refine (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).2 (prod_mem fun a _ => hH _ _))).trans ?_
    exact Finset.le_sup (f := fun I : Fin n → Fin r => O.valuation (Matrix.of fun a b => G (I a) b).det) (Finset.mem_univ I)

/- English proof (translation)
The claim follows from `Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => γ * x) (fun _ _ h => mul_le_mul_right h γ) (by rw [show (⊥ : O.ValueGroup) = 0 from le_antisymm bot_le zero_le']; exact mul_zero γ)`.
-/
theorem mul_sup {ι : Type} [Fintype ι] (γ : O.ValueGroup) (f : ι → O.ValueGroup) :
    γ * Finset.univ.sup f = Finset.univ.sup fun I => γ * f I :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => γ * x) (fun _ _ h => mul_le_mul_right h γ)
    (by rw [show (⊥ : O.ValueGroup) = 0 from le_antisymm bot_le zero_le']; exact mul_zero γ)

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hS x hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `(Valuation.map_add _ _ _).trans (max_le hx hy)`.

Consider the case `smul a x _ hx => show O.valuation (i ((a : Ω) * x)) ≤ γ`. Rewrite using `[map_mul, map_mul]`. Conclude with `(mul_le_of_le_one_left' ((O.valuation_le_one_iff _).2 (hR _ a.2))).trans hx`.
-/
theorem val_le_of_mem_span {Ω : Type} [Field Ω] (i : Ω →+* Ω₃) (R : Subring Ω) (hR : ∀ a ∈ R, i a ∈ O) {S : Set Ω}
    {γ : O.ValueGroup} (hS : ∀ s ∈ S, O.valuation (i s) ≤ γ) {x : Ω} (hx : x ∈ Submodule.span R S) :
    O.valuation (i x) ≤ γ := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    show O.valuation (i ((a : Ω) * x)) ≤ γ
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).2 (hR _ a.2))).trans hx

/- English proof (translation)
The claim follows from `le_antisymm (val_le_of_mem_span O i R hR (S := {y}) (by rintro _ rfl; rfl) (h ▸ Submodule.mem_span_singleton_self x)) (val_le_of_mem_span O i R hR (S := {x}) (by rintro _ rfl; rfl) (h ▸ Submodule.mem_span_singleton_self y))`.
-/
theorem val_eq_of_span_eq {Ω : Type} [Field Ω] (i : Ω →+* Ω₃) (R : Subring Ω) (hR : ∀ a ∈ R, i a ∈ O) {x y : Ω}
    (h : Submodule.span R {x} = Submodule.span R {y}) : O.valuation (i x) = O.valuation (i y) :=
  le_antisymm (val_le_of_mem_span O i R hR (S := {y}) (by rintro _ rfl; rfl) (h ▸ Submodule.mem_span_singleton_self x))
    (val_le_of_mem_span O i R hR (S := {x}) (by rintro _ rfl; rfl) (h ▸ Submodule.mem_span_singleton_self y))

/- English proof (translation)
Use `Finset.prod_bij (fun a _ => Fin.castLE m.2 a) (fun a _ => ?_) (fun a _ b _ h => Fin.castLE_injective _ h) (fun b hb => ⟨⟨b, ?_⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl` and prove the remaining obligations. Conclude with `Finset.mem_Iic.2 (Fin.le_def.2 (Nat.lt_succ_iff.1 a.2))`. Conclude with `Nat.lt_succ_iff.2 (Fin.le_def.1 (Finset.mem_Iic.1 hb))`.
-/
theorem prod_castLE {M : Type} [CommMonoid M] {r : ℕ} (m : Fin r) (f : Fin r → M) :
    ∏ a : Fin (m + 1), f (Fin.castLE m.2 a) = ∏ m' ∈ Finset.Iic m, f m' := by
  refine Finset.prod_bij (fun a _ => Fin.castLE m.2 a) (fun a _ => ?_) (fun a _ b _ h => Fin.castLE_injective _ h)
    (fun b hb => ⟨⟨b, ?_⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl
  · exact Finset.mem_Iic.2 (Fin.le_def.2 (Nat.lt_succ_iff.1 a.2))
  · exact Nat.lt_succ_iff.2 (Fin.le_def.1 (Finset.mem_Iic.1 hb))

/- English proof (translation)
Establish `e : (Matrix.of fun a b : Fin (m + 1) => (u * B) (I a) (Fin.castLE m.2 b)) = (Matrix.of fun a b : Fin (m + 1) => u (I a) (Fin.castLE m.2 b)) * Matrix.of fun a b : Fin (m + 1) => B (Fin.castLE m.2 a) (Fin.castLE m.2 b)`. Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Use `symm`. Use `Finset.sum_of_injOn (Fin.castLE m.2) (fun _ _ _ _ h => Fin.castLE_injective _ h) (by simp) (fun l _ hl => ?_) fun _ _ => rfl` and prove the remaining obligations.

Rewrite using `[hB, mul_zero]`. Assume the negation of the conclusion as `h`. Use `hl ⟨⟨l, ?_⟩, by simp, rfl⟩` and prove the remaining obligations. Use `b.2` as an intermediate fact. Simplify using `only [Fin.val_castLE] at h`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e, Matrix.det_mul, mul_comm, Matrix.det_of_isUpperTriangular, ← prod_castLE m fun m' => B m' m']`. Both sides reduce to the same expression. Introduce `a b h`. Conclude with `hB _ _ h`.
-/
theorem minor_mul {r : ℕ} (u B : Matrix (Fin r) (Fin r) Ω₃) (hB : ∀ m' m : Fin r, (m : ℕ) + 1 ≤ m' → B m' m = 0) (m : Fin r)
    (I : Fin (m + 1) → Fin r) :
    (Matrix.of fun a b : Fin (m + 1) => (u * B) (I a) (Fin.castLE m.2 b)).det =
      (∏ m' ∈ Finset.Iic m, B m' m') * (Matrix.of fun a b : Fin (m + 1) => u (I a) (Fin.castLE m.2 b)).det := by
  have e : (Matrix.of fun a b : Fin (m + 1) => (u * B) (I a) (Fin.castLE m.2 b)) =
      (Matrix.of fun a b : Fin (m + 1) => u (I a) (Fin.castLE m.2 b)) *
        Matrix.of fun a b : Fin (m + 1) => B (Fin.castLE m.2 a) (Fin.castLE m.2 b) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.of_apply]
    symm
    refine Finset.sum_of_injOn (Fin.castLE m.2) (fun _ _ _ _ h => Fin.castLE_injective _ h) (by simp) (fun l _ hl => ?_)
      fun _ _ => rfl
    rw [hB, mul_zero]
    by_contra h
    refine hl ⟨⟨l, ?_⟩, by simp, rfl⟩
    have := b.2
    simp only [Fin.val_castLE] at h
    omega
  rw [e, Matrix.det_mul, mul_comm, Matrix.det_of_isUpperTriangular, ← prod_castLE m fun m' => B m' m']
  · rfl
  · intro a b h
    exact hB _ _ h

end

end SheetDecomposition

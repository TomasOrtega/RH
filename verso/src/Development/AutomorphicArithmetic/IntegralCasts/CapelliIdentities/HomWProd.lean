import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qi22.wsum.{v} :
    {ι : Type v} → (ι → ℤ) → (ι →₀ ℕ) → ℤ :=
    fun {ι : Type v} (w : ι → ℤ) (n : ι →₀ ℕ) ↦ n.sum fun (x : ι) (k : ℕ) ↦ (↑k : ℤ) * w x

noncomputable def UpperTheory.Reformulated.B.Qi22.HomW.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → (ι → ℤ) → ℤ → MvPowerSeries ι K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (w : ι → ℤ) (c : ℤ) (f : MvPowerSeries ι K) ↦
      ∀ (n : ι →₀ ℕ), (MvPowerSeries.coeff n : MvPowerSeries ι K → K) f ≠ (0 : K) → UpperTheory.Reformulated.B.Qi22.wsum w n = c

/- English proof (translation)
Unfold `UpperTheory.Reformulated.B.Qi22.wsum`. Apply `Finsupp.sum_add_index'` to reduce the goal to its premises. Introduce `x`. Simplify using the standard rewrite rules. Introduce `x p q`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem UpperTheory.Reformulated.B.Qi22.wsum_add {ι : Type*} (w : ι → ℤ) (a b : ι →₀ ℕ) :
    UpperTheory.Reformulated.B.Qi22.wsum w (a + b) = UpperTheory.Reformulated.B.Qi22.wsum w a + UpperTheory.Reformulated.B.Qi22.wsum w b := by
  unfold UpperTheory.Reformulated.B.Qi22.wsum
  apply Finsupp.sum_add_index'
  · intro x; simp
  · intro x p q; push_cast; ring

/- English proof (translation)
Introduce `n hn`. Establish `h0 : n = 0`. Assume the negation of the conclusion as `h`. Conclude with `hn (by rw [MvPowerSeries.coeff_one, if_neg h])`. Substitute `h0` using the available equality.

Simplify using `[UpperTheory.Reformulated.B.Qi22.wsum]`.
-/
private theorem UpperTheory.Reformulated.B.Qi22.homW_one {K : Type*} [NormedField K] {ι : Type*} (w : ι → ℤ) :
    UpperTheory.Reformulated.B.Qi22.HomW w 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n hn
  have h0 : n = 0 := by
    by_contra h
    exact hn (by rw [MvPowerSeries.coeff_one, if_neg h])
  subst h0
  simp [UpperTheory.Reformulated.B.Qi22.wsum]

/- English proof (translation)
Introduce `n hn`. Rewrite `hn` using `[MvPowerSeries.coeff_mul]`. Take `⟨p, hp, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hn`. Establish `hsum : p.1 + p.2 = n` using `by simpa using hp`. Rewrite using `[← hsum, UpperTheory.Reformulated.B.Qi22.wsum_add, hf p.1 (left_ne_zero_of_mul hne), hg p.2 (right_ne_zero_of_mul hne)]`.
-/
private theorem UpperTheory.Reformulated.B.Qi22.homW_mul {K : Type*} [NormedField K] {ι : Type*} {w : ι → ℤ}
    {c d : ℤ} {f g : MvPowerSeries ι K} (hf : UpperTheory.Reformulated.B.Qi22.HomW w c f)
    (hg : UpperTheory.Reformulated.B.Qi22.HomW w d g) : UpperTheory.Reformulated.B.Qi22.HomW w (c + d) (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hsum : p.1 + p.2 = n := by simpa using hp
  rw [← hsum, UpperTheory.Reformulated.B.Qi22.wsum_add, hf p.1 (left_ne_zero_of_mul hne),
    hg p.2 (right_ne_zero_of_mul hne)]

/- English proof (translation)
Introduce `K inst ι w α s c F`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `_`. Simplify using `using UpperTheory.Reformulated.B.Qi22.homW_one (K := K) w`.

Consider the case `insert a s ha ih`. Introduce `h`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `UpperTheory.Reformulated.B.Qi22.homW_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem UpperTheory.Reformulated.B.Qi22.homW_prod.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} {w : ι → ℤ} {α : Type w} (s : Finset α) (c : α → ℤ)
      (F : α → MvPowerSeries ι K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi22.HomW w (c i) (F i)) → UpperTheory.Reformulated.B.Qi22.HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by
  intro K inst ι w α s c F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using UpperTheory.Reformulated.B.Qi22.homW_one (K := K) w
  | insert a s ha ih =>
    intro h
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact UpperTheory.Reformulated.B.Qi22.homW_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

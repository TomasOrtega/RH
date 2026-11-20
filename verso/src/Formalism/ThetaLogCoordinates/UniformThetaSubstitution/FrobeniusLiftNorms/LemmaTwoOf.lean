import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

namespace LemTwo

section Slice

variable {K : Type} [Field K]

def sl (G : MvPowerSeries (Fin 2) K) (m : ℕ) : PowerSeries K :=
  PowerSeries.mk fun i => MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 m) G

def ext3 (e : Fin 2 →₀ ℕ) (m : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.embDomain Fin.castSuccEmb e + Finsupp.single 2 m

/- English proof (translation)
Rewrite using `[MvPowerSeries.rename_eq_subst, in3]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
theorem include_three_eq_rename (g : MvPowerSeries (Fin 2) K) :
    in3 g = MvPowerSeries.rename (Fin.castSuccEmb (n := 2)) g := by
  rw [MvPowerSeries.rename_eq_subst, in3]
  congr 1
  funext i
  fin_cases i <;> rfl

/- English proof (translation)
Rewrite using `[Finsupp.embDomain_notin_range]`. Introduce and unpack `⟨i, hi⟩`. Establish `h1` using `congrArg Fin.val hi`. Establish `h2` using `i.isLt`. Simplify using `at h1`.

Use linear arithmetic over natural numbers and integers.
-/
theorem embDomain_two (e : Fin 2 →₀ ℕ) : Finsupp.embDomain Fin.castSuccEmb e (2 : Fin 3) = 0 := by
  rw [Finsupp.embDomain_notin_range]
  rintro ⟨i, hi⟩
  have h1 := congrArg Fin.val hi
  have h2 := i.isLt
  simp at h1
  omega

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_rename, Finset.sum_eq_single_of_mem u]`. Simplify using the standard rewrite rules. Introduce `b hb hne`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises.

Simplify using `only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hb`. Conclude with `Finsupp.mapDomain_injective hf hb`.
-/
private theorem coeff_rename_map_lemma {σ τ : Type} (f : σ → τ) [Filter.TendstoCofinite f]
    (hf : Function.Injective f) (g : MvPowerSeries σ K) (u : σ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.mapDomain f u) (MvPowerSeries.rename f g) = MvPowerSeries.coeff u g := by
  classical
  rw [MvPowerSeries.coeff_rename, Finset.sum_eq_single_of_mem u]
  · simp
  · intro b hb hne
    exfalso
    apply hne
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hb
    exact Finsupp.mapDomain_injective hf hb

/- English proof (translation)
Rewrite using `[include_three_eq_rename]`. Distinguish the cases in `h : j = m`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, MvPowerSeries.X_pow_eq, ext3, MvPowerSeries.coeff_add_mul_monomial, mul_one, Finsupp.embDomain_eq_mapDomain]`. Conclude with `coeff_rename_map_lemma _ (Fin.castSuccEmb (n := 2)).injective g e`.

Rewrite using `[if_neg h, MvPowerSeries.coeff_mul]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce and unpack `⟨a, b⟩ hab`. Use `replace hab : a + b = ext3 e m := by simpa using hab`. Rewrite using `[MvPowerSeries.coeff_X_pow]`.

Use `split_ifs with hb`. Rewrite using `[mul_one]`. Apply `MvPowerSeries.coeff_rename_eq_zero` to reduce the goal to its premises. Introduce and unpack `⟨u, hu⟩`. Simplify using `only at hb hu`.

Establish `h2` using `congrArg (fun d : Fin 3 →₀ ℕ => d 2) hab`. Simplify using `only [Finsupp.add_apply, hb, ext3] at h2`. Rewrite `h2` using `[← hu, Finsupp.mapDomain_notin_range, embDomain_two]`. Simplify using `at h2`. Use linear arithmetic over natural numbers and integers.

Introduce and unpack `⟨i, hi⟩`. Establish `h1` using `congrArg Fin.val hi`. Establish `h3` using `i.isLt`. Simplify using `at h1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[mul_zero]`.
-/
theorem coeff_include_three_mul (g : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m j : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (in3 g * MvPowerSeries.X 2 ^ j) =
      if j = m then MvPowerSeries.coeff e g else 0 := by
  classical
  rw [include_three_eq_rename]
  by_cases h : j = m
  · subst h
    rw [if_pos rfl, MvPowerSeries.X_pow_eq, ext3, MvPowerSeries.coeff_add_mul_monomial, mul_one,
      Finsupp.embDomain_eq_mapDomain]
    exact coeff_rename_map_lemma _ (Fin.castSuccEmb (n := 2)).injective g e
  · rw [if_neg h, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    replace hab : a + b = ext3 e m := by simpa using hab
    rw [MvPowerSeries.coeff_X_pow]
    split_ifs with hb
    · rw [mul_one]
      apply MvPowerSeries.coeff_rename_eq_zero
      rintro ⟨u, hu⟩
      simp only at hb hu
      have h2 := congrArg (fun d : Fin 3 →₀ ℕ => d 2) hab
      simp only [Finsupp.add_apply, hb, ext3] at h2
      rw [← hu, Finsupp.mapDomain_notin_range, embDomain_two] at h2
      · simp at h2
        omega
      · rintro ⟨i, hi⟩
        have h1 := congrArg Fin.val hi
        have h3 := i.isLt
        simp at h1
        omega
    · rw [mul_zero]

/- English proof (translation)
Rewrite using `[include_three_eq_rename, MvPowerSeries.constantCoeff_rename, hg]`.
-/
theorem constantCoeff_law_first_two_of_three {g : MvPowerSeries (Fin 2) K} (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (in3 g) = 0 := by
  rw [include_three_eq_rename, MvPowerSeries.constantCoeff_rename, hg]

/- English proof (translation)
Rewrite using `[include_three_eq_rename, include_three_eq_rename, map_pow]`.
-/
theorem include_three_pow (g : MvPowerSeries (Fin 2) K) (k : ℕ) : in3 g ^ k = in3 (g ^ k) := by
  rw [include_three_eq_rename, include_three_eq_rename, map_pow]

/- English proof (translation)
Rewrite using `[include_three_eq_rename, MvPowerSeries.rename_X]`. Both sides reduce to the same expression.
-/
theorem include_three_X (i : Fin 2) :
    in3 (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = MvPowerSeries.X (Fin.castSucc i) := by
  rw [include_three_eq_rename, MvPowerSeries.rename_X]
  rfl

/- English proof (translation)
Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp`.
-/
theorem fin_two_vector_eq_matrixVecCons (d : Fin 2 →₀ ℕ) : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
  ext i
  fin_cases i <;> simp

/- English proof (translation)
The claim follows from `MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hk) (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hf))`.
-/
theorem coeff_pow_high {ι : Type} {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0)
    {e : ι →₀ ℕ} {k : ℕ} (hk : e.degree < k) : MvPowerSeries.coeff e (f ^ k) = 0 :=
  MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hk)
    (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hf))

/- English proof (translation)
Establish `ha : MvPowerSeries.HasSubst ![in3 f, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)]` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s`. Conclude with `constantCoeff_law_first_two_of_three hf`. Use the proof step `simp)`. Establish `hb : PowerSeries.HasSubst f` using `PowerSeries.HasSubst.of_constantCoeff_zero hf`. Rewrite using `[MvPowerSeries.coeff_subst ha, PowerSeries.coeff_subst hb]`.

Establish `hterm : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff (ext3 e m) (d.prod fun s k => (![in3 f, MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) K) s ^ k) = if d 1 = m then MvPowerSeries.coeff e (f ^ d 0) else 0`. Introduce `d`. Rewrite using `[Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]`. Rewrite using `[include_three_pow, coeff_include_three_mul]`.

Repeatedly rewrite using `[hterm]`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := (Finset.range (e.degree + 1)).image (fun i => Finsupp.single (0 : Fin 2) i + Finsupp.single 1 m)), finsum_eq_sum_of_support_subset _ (s := Finset.range (e.degree + 1))]`. Rewrite using `[Finset.sum_image]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Simplify using `[sl]`. Introduce `x _ y _ hxy`. Use `congrArg (fun d : Fin 2 →₀ ℕ => d 0) hxy` as an intermediate fact. Simplify using `using this`. Introduce `i hi`.

Rewrite `hi` using `[Function.mem_support]`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `hc`. Conclude with `hi (by rw [coeff_pow_high hf (by omega), smul_zero])`. Introduce `d hd`.

Rewrite `hd` using `[Function.mem_support]`. Use `split_ifs at hd with h1`. Simplify using `only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]`. Use `⟨d 0, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Conclude with `hd (by rw [coeff_pow_high hf (by omega), smul_zero])`. Rewrite using `[← h1]`. Conclude with `(fin_two_vector_eq_matrixVecCons d).symm`. Conclude with `absurd (smul_zero _) hd`.
-/
theorem coeff_subst_slice {f : MvPowerSeries (Fin 2) K} (hf : MvPowerSeries.constantCoeff f = 0)
    (G : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (MvPowerSeries.subst ![in3 f, MvPowerSeries.X 2] G) =
      MvPowerSeries.coeff e (PowerSeries.subst f (sl G m)) := by
  classical
  have ha : MvPowerSeries.HasSubst ![in3 f, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
      fin_cases s
      · exact constantCoeff_law_first_two_of_three hf
      · simp)
  have hb : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  rw [MvPowerSeries.coeff_subst ha, PowerSeries.coeff_subst hb]
  have hterm : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff (ext3 e m)
      (d.prod fun s k => (![in3 f, MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) K) s ^ k) =
        if d 1 = m then MvPowerSeries.coeff e (f ^ d 0) else 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [include_three_pow, coeff_include_three_mul]
  simp_rw [hterm]
  rw [finsum_eq_sum_of_support_subset _
      (s := (Finset.range (e.degree + 1)).image (fun i => Finsupp.single (0 : Fin 2) i + Finsupp.single 1 m)),
    finsum_eq_sum_of_support_subset _ (s := Finset.range (e.degree + 1))]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i _
      simp [sl]
    · intro x _ y _ hxy
      have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) hxy
      simpa using this
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact hi (by rw [coeff_pow_high hf (by omega), smul_zero])
  · intro d hd
    rw [Function.mem_support] at hd
    split_ifs at hd with h1
    · simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      refine ⟨d 0, ?_, ?_⟩
      · by_contra hc
        exact hd (by rw [coeff_pow_high hf (by omega), smul_zero])
      · rw [← h1]
        exact (fin_two_vector_eq_matrixVecCons d).symm
    · exact absurd (smul_zero _) hd

/- English proof (translation)
Establish `h0` using `coeff_subst_slice (f := (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (MvPowerSeries.constantCoeff_X 0) G e m`. Establish `h1` using `coeff_subst_slice (f := (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) (MvPowerSeries.constantCoeff_X 1) G e m`. Rewrite `h0`, `h1` using `[include_three_X]`. Rewrite using `[d1, map_sub, map_sub, coeff_subst_slice hF, cob, map_sub, map_sub, at1, at1]`. Rewrite using `[← h0, ← h1]`.

Both sides reduce to the same expression.
-/
theorem coeff_partial_coboundary {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (G : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (m : ℕ) :
    MvPowerSeries.coeff (ext3 e m) (d1 F G) = MvPowerSeries.coeff e (cob F (sl G m)) := by
  have h0 := coeff_subst_slice (f := (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
    (MvPowerSeries.constantCoeff_X 0) G e m
  have h1 := coeff_subst_slice (f := (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K))
    (MvPowerSeries.constantCoeff_X 1) G e m
  rw [include_three_X] at h0 h1
  rw [d1, map_sub, map_sub, coeff_subst_slice hF, cob, map_sub, map_sub, at1, at1]
  rw [← h0, ← h1]
  rfl

end Slice

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Introduce `n`. Rewrite using `[MvPowerSeries.coeff_mul]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun q _ => by rw [norm_mul]; exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _))`.
-/
theorem integral_mul {ι : Type} {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun q _ => by rw [norm_mul]; exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _))

end Norm

section Top

variable {K : Type} [Field K]

end Top

section Additive

variable {K : Type} [Field K]

/- English proof (translation)
Unfold `cob at1`. Rewrite using `[PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero hF), PowerSeries.subst_add (PowerSeries.HasSubst.X 0), PowerSeries.subst_add (PowerSeries.HasSubst.X 1)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cob_add {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f g : PowerSeries K) : cob F (f + g) = cob F f + cob F g := by
  unfold cob at1
  rw [PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero hF),
    PowerSeries.subst_add (PowerSeries.HasSubst.X 0), PowerSeries.subst_add (PowerSeries.HasSubst.X 1)]
  ring

/- English proof (translation)
Rewrite using `[lgF, PowerSeries.coeff_mk, Finset.sum_range_succ, Finset.sum_range_one]`. Establish `h4 : 4 ≤ p ^ 2` using `by nlinarith`. Establish `hne : (1 : ℕ) ≠ (p ^ 2) ^ 1` using `by rw [pow_one]; omega`. Rewrite using `[if_neg hne, if_pos (by rw [pow_zero]), pow_zero, inv_one, add_zero]`.
-/
theorem coeff_one_lgF {p : ℕ} (hp : 2 ≤ p) : PowerSeries.coeff 1 (lgF K p) = 1 := by
  rw [lgF, PowerSeries.coeff_mk, Finset.sum_range_succ, Finset.sum_range_one]
  have h4 : 4 ≤ p ^ 2 := by nlinarith
  have hne : (1 : ℕ) ≠ (p ^ 2) ^ 1 := by rw [pow_one]; omega
  rw [if_neg hne, if_pos (by rw [pow_zero]), pow_zero, inv_one, add_zero]

/- English proof (translation)
Rewrite using `[MvPowerSeries.rename_eq_subst, swap2]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
theorem swap_two_eq_rename (H : MvPowerSeries (Fin 2) K) :
    swap2 H = MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1).toEmbedding H := by
  rw [MvPowerSeries.rename_eq_subst, swap2]
  congr 1
  funext i
  fin_cases i <;> rfl

/- English proof (translation)
Rewrite using `[swap_two_eq_rename]`. Establish `hu : Finsupp.mapDomain (⇑(Equiv.swap (0 : Fin 2) 1).toEmbedding) (Finsupp.single 0 k + Finsupp.single 1 i) = Finsupp.single 0 i + Finsupp.single 1 k`. Rewrite using `[Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single]`. Simplify using `only [Equiv.coe_toEmbedding, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Conclude with `add_comm _ _`.

Rewrite using `[← hu, coeff_rename_map_lemma _ (Equiv.swap (0 : Fin 2) 1).toEmbedding.injective]`.
-/
theorem coeff_swap2 (H : MvPowerSeries (Fin 2) K) (i k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) (swap2 H) =
      MvPowerSeries.coeff (Finsupp.single 0 k + Finsupp.single 1 i) H := by
  rw [swap_two_eq_rename]
  have hu : Finsupp.mapDomain (⇑(Equiv.swap (0 : Fin 2) 1).toEmbedding)
      (Finsupp.single 0 k + Finsupp.single 1 i) = Finsupp.single 0 i + Finsupp.single 1 k := by
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact add_comm _ _
  rw [← hu, coeff_rename_map_lemma _ (Equiv.swap (0 : Fin 2) 1).toEmbedding.injective]

def asm (R : ℕ → PowerSeries K) : MvPowerSeries (Fin 2) K :=
  fun n => PowerSeries.coeff (n 0) (R (n 1))

/- English proof (translation)
Introduce `h`. Establish `e1 : p * (p ^ 2) ^ i = p ^ (2 * i + 1)` using `by ring`. Establish `e2 : (p ^ 2) ^ j = p ^ (2 * j)` using `by ring`. Rewrite `h` using `[e1, e2]`. Use `Nat.pow_right_injective hp h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem pow_parity {p : ℕ} (hp : 2 ≤ p) (i j : ℕ) : p * (p ^ 2) ^ i ≠ (p ^ 2) ^ j := by
  intro h
  have e1 : p * (p ^ 2) ^ i = p ^ (2 * i + 1) := by ring
  have e2 : (p ^ 2) ^ j = p ^ (2 * j) := by ring
  rw [e1, e2] at h
  have := Nat.pow_right_injective hp h
  omega

/- English proof (translation)
Rewrite using `[lgF, PowerSeries.coeff_mk]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[if_neg (pow_parity hp i j)]`.
-/
theorem coeff_lgF_odd {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    PowerSeries.coeff (p * (p ^ 2) ^ i) (lgF K p) = 0 := by
  rw [lgF, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (pow_parity hp i j)]

/- English proof (translation)
Rewrite using `[g0F, PowerSeries.coeff_mk]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[if_neg (fun h => pow_parity hp j i h.symm)]`.
-/
theorem coeff_g0F_even {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    PowerSeries.coeff ((p ^ 2) ^ i) (g0F K p) = 0 := by
  rw [g0F, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (fun h => pow_parity hp j i h.symm)]

end Additive

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max x (-y)).trans (max_le hx (by rwa [norm_neg]))`.
-/
theorem norm_sub_le_one {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max x (-y)).trans (max_le hx (by rwa [norm_neg]))

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hxpos : 0 < ‖x‖` using `norm_pos_iff.2 hx`. Establish `hp1 : ((p : ℝ))⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < p))`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one hxpos hp1`. Take `⟨i, hi, hle⟩` from `h N`.

Establish `hpos : (0 : ℝ) < (p : ℝ) ^ i` using `by positivity`. Rewrite `hle` using `[norm_mul, norm_inv, norm_pow, hnp, inv_pow, inv_inv]`. Establish `h1 : ‖x‖ ≤ ((p : ℝ)⁻¹) ^ i`. Rewrite using `[inv_pow]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : ((p : ℝ)⁻¹) ^ i ≤ ((p : ℝ)⁻¹) ^ N` using `pow_le_pow_of_le_one (by positivity) hp1.le hi`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_zero_of_div {p : ℕ} (hp : 2 ≤ p) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {x : K}
    (h : ∀ N : ℕ, ∃ i, N ≤ i ∧ ‖((p : K) ^ i)⁻¹ * x‖ ≤ 1) : x = 0 := by
  by_contra hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hp1 : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < p))
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hxpos hp1
  obtain ⟨i, hi, hle⟩ := h N
  have hpos : (0 : ℝ) < (p : ℝ) ^ i := by positivity
  rw [norm_mul, norm_inv, norm_pow, hnp, inv_pow, inv_inv] at hle
  have h1 : ‖x‖ ≤ ((p : ℝ)⁻¹) ^ i := by
    rw [inv_pow]
    calc ‖x‖ = ((p : ℝ) ^ i)⁻¹ * ((p : ℝ) ^ i * ‖x‖) := by field_simp
      _ ≤ ((p : ℝ) ^ i)⁻¹ * 1 := by gcongr
      _ = ((p : ℝ) ^ i)⁻¹ := mul_one _
  have h2 : ((p : ℝ)⁻¹) ^ i ≤ ((p : ℝ)⁻¹) ^ N := pow_le_pow_of_le_one (by positivity) hp1.le hi
  linarith

end Norm

end LemTwo

open LemTwo in

/- English proof (translation)
Introduce `K _ _ _ _ p σ hU F hF H hH hd hd'`. Take `⟨hp, -, hnp, -, -⟩` from `id hU`. Establish `hp2 : 2 ≤ p` using `hp.two_le`. Take `⟨hF0, -, -⟩` from `id hF`. Establish `np : ∀ k : ℕ, ‖((p : K) ^ k)⁻¹‖ = (p : ℝ) ^ k`.

Introduce `k`. Rewrite using `[norm_inv, norm_pow, hnp, inv_pow, inv_inv]`. Establish `zero_of_bdd : ∀ (c : K) (M : ℝ), (∀ N : ℕ, ∃ k, N ≤ k ∧ ‖c * ((p : K) ^ k)⁻¹‖ ≤ M) → c = 0`. Introduce `c M h`. Assume the negation of the conclusion as `hc`.

Establish `hcpos : 0 < ‖c‖` using `norm_pos_iff.2 hc`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (by omega : 1 < p)`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (M / ‖c‖) hp1`. Take `⟨k, hk, hle⟩` from `h n`. Rewrite `hle` using `[norm_mul, np]`.

Establish `hpk : (p : ℝ) ^ n ≤ (p : ℝ) ^ k` using `pow_le_pow_right₀ hp1.le hk`. Establish `h3 : M / ‖c‖ < (p : ℝ) ^ k` using `lt_of_lt_of_le hn hpk`. Rewrite `h3` using `[div_lt_iff₀ hcpos]`. Combine the linear relations using `[mul_comm ‖c‖ ((p : ℝ) ^ k)]`. Establish `ultra : ∀ {a b : K} {M : ℝ}, ‖a - b‖ ≤ 1 → ‖b‖ ≤ M → 1 ≤ M → ‖a‖ ≤ M`.

Introduce `a b M h hb hM`. Combine the equalities or inequalities in the displayed calculation. Establish `hpp : 2 ≤ p ^ 2` using `by nlinarith`. Establish `lg_pow : ∀ k : ℕ, PowerSeries.coeff ((p ^ 2) ^ k) (lgF K p) = ((p : K) ^ k)⁻¹`. Introduce `k`.

Rewrite using `[lgF, PowerSeries.coeff_mk, Finset.sum_eq_single k]`. Rewrite using `[if_pos rfl]`. Introduce `j _ hj`. Rewrite using `[if_neg]`. Introduce `h`.

Conclude with `hj (Nat.pow_right_injective hpp h).symm`. Introduce `hk`. It suffices to derive a contradiction. Apply `hk` to reduce the goal to its premises. Rewrite using `[Finset.mem_range]`.

Establish `: k < (p ^ 2) ^ k` using `Nat.lt_pow_self (by omega)`. Use linear arithmetic over natural numbers and integers. Establish `g0_pow : ∀ k : ℕ, PowerSeries.coeff (p * (p ^ 2) ^ k) (g0F K p) = ((p : K) ^ (k + 1))⁻¹`. Introduce `k`. Rewrite using `[g0F, PowerSeries.coeff_mk, Finset.sum_eq_single k]`.

Rewrite using `[if_pos rfl]`. Introduce `j _ hj`. Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hj (Nat.pow_right_injective hpp (Nat.eq_of_mul_eq_mul_left (by omega) h)).symm`.

Introduce `hk`. It suffices to derive a contradiction. Apply `hk` to reduce the goal to its premises. Rewrite using `[Finset.mem_range]`. Establish `: k < (p ^ 2) ^ k` using `Nat.lt_pow_self (by omega)`.

Establish `: (p ^ 2) ^ k ≤ p * (p ^ 2) ^ k` using `Nat.le_mul_of_pos_left _ (by omega)`. Use linear arithmetic over natural numbers and integers. Establish `lg_zero : ∀ m : ℕ, (∀ l, m ≠ (p ^ 2) ^ l) → PowerSeries.coeff m (lgF K p) = 0`. Introduce `m hm`. Rewrite using `[lgF, PowerSeries.coeff_mk]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[if_neg (hm j)]`. Establish `g01 : PowerSeries.coeff 1 (g0F K p) = 0`. Use `LemTwo.coeff_g0F_even (K := K) hp2 0` as an intermediate fact.

Rewrite `this` using `[pow_zero]`. Then use the resulting hypothesis. Establish `lg1 : PowerSeries.coeff 1 (lgF K p) = 1` using `LemTwo.coeff_one_lgF hp2`. Establish `hH2 : DivAB (swap2 H)`. Introduce `n hn`. Rewrite using `[LemTwo.fin_two_vector_eq_matrixVecCons n, LemTwo.coeff_swap2]`.

Apply `hH` to reduce the goal to its premises. Break down `hn with h | h` into its components or cases. Use `right`. Simplify using `[h]`. Use `left`.

Simplify using `[h]`. Establish `cobInt : ∀ G : MvPowerSeries (Fin 2) K, Integral (d1 F G) → ∀ m, Integral (cob F (sl G m))`. Introduce `G hG m e`. Rewrite using `[← LemTwo.coeff_partial_coboundary hF0 G e m]`. Conclude with `hG _`.

Establish `c0 : ∀ G : MvPowerSeries (Fin 2) K, DivAB G → ∀ m, PowerSeries.constantCoeff (sl G m) = 0`. Introduce `G hG m`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, sl, PowerSeries.coeff_mk]`. Apply `hG` to reduce the goal to its premises. Use `left`.

Simplify using the standard rewrite rules. Use `choose α β R hα hR hsl using fun m => h1 K p σ hU F hF (sl H m) (c0 H hH m) (cobInt H hd m)`. Use `choose α' β' R' hα' hR' hsl' using fun m => h1 K p σ hU F hF (sl (swap2 H) m) (c0 _ hH2 m) (cobInt _ hd' m)`. Establish `cH : ∀ i m, MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 m) H = α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p) + PowerSeries.coeff i (R m)`. Introduce `i m`.

Establish `h3` using `congrArg (PowerSeries.coeff i) (hsl m)`. Rewrite `h3` using `[sl, PowerSeries.coeff_mk]`. Rewrite using `[h3, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]`. Establish `cH' : ∀ i m, MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 m) H = α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p) + PowerSeries.coeff m (R' i)`. Introduce `i m`.

Establish `h3` using `congrArg (PowerSeries.coeff m) (hsl' i)`. Rewrite `h3` using `[sl, PowerSeries.coeff_mk, LemTwo.coeff_swap2]`. Rewrite using `[h3, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]`. Establish `star : ∀ i m, ‖(α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p)) - (α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p))‖ ≤ 1`. Introduce `i m`.

Establish `e : (α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p)) - (α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p)) = PowerSeries.coeff m (R' i) - PowerSeries.coeff i (R m)`. Establish `e1` using `cH i m`. Establish `e2` using `cH' i m`. Take the linear combination `e2 - e1`. Rewrite using `[e]`.

Conclude with `LemTwo.norm_sub_le_one (hR' i m) (hR m i)`. Establish `hA : ∀ k, β' (p * (p ^ 2) ^ k) = 0`. Introduce `k`. Apply `zero_of_bdd _ ((p : ℝ) ^ (k + 1))` to reduce the goal to its premises. Introduce `N`.

Use `⟨N, le_rfl, ?_⟩` and prove the remaining obligations. Establish `s` using `star (p * (p ^ 2) ^ k) ((p ^ 2) ^ N)`. Rewrite `s` using `[g0_pow k, LemTwo.coeff_lgF_odd hp2 k, LemTwo.coeff_g0F_even hp2 N, lg_pow N]`. Simplify using `only [mul_zero, add_zero, zero_add] at s`. Use `ultra (b := α ((p ^ 2) ^ N) * ((p : K) ^ (k + 1))⁻¹) ?_ ?_ (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ p)))` and prove the remaining obligations.

Rewrite using `[norm_sub_rev]`. Conclude with `s`. Rewrite using `[norm_mul, np]`. Conclude with `mul_le_of_le_one_left (by positivity) (hα _)`. Establish `hB : ∀ m, α m = 0`.

Introduce `m`. Apply `zero_of_bdd _ (max 1 ‖PowerSeries.coeff m (g0F K p)‖)` to reduce the goal to its premises. Introduce `N`. Use `⟨N + 1, by omega, ?_⟩` and prove the remaining obligations. Establish `s` using `star (p * (p ^ 2) ^ N) m`.

Rewrite `s` using `[g0_pow N, LemTwo.coeff_lgF_odd hp2 N, hA N]`. Simplify using `only [mul_zero, add_zero, zero_mul] at s`. Use `ultra (b := α' (p * (p ^ 2) ^ N) * PowerSeries.coeff m (g0F K p)) s ?_ (le_max_left _ _)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (hα' _)).trans (le_max_right _ _)`.

Establish `hC : ∀ m, (∀ l, m ≠ (p ^ 2) ^ l) → β m = 0`. Introduce `m hm`. Apply `zero_of_bdd _ (max 1 ‖PowerSeries.coeff m (g0F K p)‖)` to reduce the goal to its premises. Introduce `N`. Use `⟨N, le_rfl, ?_⟩` and prove the remaining obligations.

Establish `s` using `star ((p ^ 2) ^ N) m`. Rewrite `s` using `[LemTwo.coeff_g0F_even hp2 N, lg_pow N, lg_zero m hm, hB m]`. Simplify using `only [mul_zero, zero_mul, add_zero, zero_add] at s`. Use `ultra (b := α' ((p ^ 2) ^ N) * PowerSeries.coeff m (g0F K p)) s ?_ (le_max_left _ _)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (hα' _)).trans (le_max_right _ _)`. Establish `hD : ∀ l, β ((p ^ 2) ^ l) = β 1 * ((p : K) ^ l)⁻¹`. Introduce `l`. Rewrite using `[← sub_eq_zero]`. Apply `zero_of_bdd _ ((p : ℝ) ^ l)` to reduce the goal to its premises.

Introduce `N`. Use `⟨N, le_rfl, ?_⟩` and prove the remaining obligations. Establish `s1` using `star ((p ^ 2) ^ N) ((p ^ 2) ^ l)`. Establish `s2` using `star ((p ^ 2) ^ N) 1`. Rewrite `s1` using `[LemTwo.coeff_g0F_even hp2 N, lg_pow N, LemTwo.coeff_g0F_even hp2 l, lg_pow l, hB]`.

Rewrite `s2` using `[LemTwo.coeff_g0F_even hp2 N, lg_pow N, g01, lg1, hB]`. Simplify using `only [mul_zero, zero_mul, add_zero, zero_add, mul_one] at s1 s2`. Establish `e : (β ((p ^ 2) ^ l) - β 1 * ((p : K) ^ l)⁻¹) * ((p : K) ^ N)⁻¹ = (β ((p ^ 2) ^ l) * ((p : K) ^ N)⁻¹ - β' ((p ^ 2) ^ N) * ((p : K) ^ l)⁻¹) - ((p : K) ^ l)⁻¹ * (β 1 * ((p : K) ^ N)⁻¹ - β' ((p ^ 2) ^ N))` using `by ring`. Rewrite using `[e]`. Establish `usub : ∀ a b : K, ‖a - b‖ ≤ max ‖a‖ ‖b‖` using `fun a b => by`.

Rewrite using `[sub_eq_add_neg]`. Establish `h4` using `IsUltrametricDist.norm_add_le_max a (-b)`. Rewrite `h4` using `[norm_neg]`. Then use the resulting hypothesis. Use `(usub _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `s1.trans (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ p)))`.

Rewrite using `[norm_mul, np]`. Conclude with `mul_le_of_le_one_right (by positivity) s2`. Use `⟨β 1, H - MvPowerSeries.C (β 1) * (at1 0 (lgF K p) * at1 1 (lgF K p)), ?_, by ring⟩` and prove the remaining obligations. Introduce `n`. Rewrite using `[LemTwo.fin_two_vector_eq_matrixVecCons n]`.

Use `set i := n 0`. Use `set m := n 1`. Rewrite using `[map_sub, MvPowerSeries.coeff_C_mul, at1, at1, PowerSeries.coeff_subst_X_zero_subst_mul_X_one, cH, hB m]`. Establish `ev0 : (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) m : Fin 2 →₀ ℕ) 0 = i` using `by simp`. Establish `ev1 : (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) m : Fin 2 →₀ ℕ) 1 = m` using `by simp`.

Rewrite using `[ev0, ev1]`. Establish `key : β m * PowerSeries.coeff i (lgF K p) - β 1 * (PowerSeries.coeff i (lgF K p) * PowerSeries.coeff m (lgF K p)) = 0`. Distinguish the cases in `hm : ∃ l, m = (p ^ 2) ^ l`. Take `⟨l, hl⟩` from `hm`. Rewrite using `[hl, hD l, lg_pow l]`.

Expand and normalize the polynomial expressions, which then agree. Use `push_neg at hm`. Rewrite using `[hC m hm, lg_zero m hm]`. Expand and normalize the polynomial expressions, which then agree. Establish `e : 0 * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p) + PowerSeries.coeff i (R m) - β 1 * (PowerSeries.coeff i (lgF K p) * PowerSeries.coeff m (lgF K p)) = PowerSeries.coeff i (R m) + (β m * PowerSeries.coeff i (lgF K p) - β 1 * (PowerSeries.coeff i (lgF K p …` using `by ring`.

Rewrite using `[e, key, add_zero]`. Conclude with `hR m i`.
-/
theorem LemmaTwo_of (h1 : LemmaOne) (hL : LawSymm) : LemmaTwo := by
  intro K _ _ _ _ p σ hU F hF H hH hd hd'
  obtain ⟨hp, -, hnp, -, -⟩ := id hU
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨hF0, -, -⟩ := id hF
  have np : ∀ k : ℕ, ‖((p : K) ^ k)⁻¹‖ = (p : ℝ) ^ k := by
    intro k
    rw [norm_inv, norm_pow, hnp, inv_pow, inv_inv]
  have zero_of_bdd : ∀ (c : K) (M : ℝ), (∀ N : ℕ, ∃ k, N ≤ k ∧ ‖c * ((p : K) ^ k)⁻¹‖ ≤ M) → c = 0 := by
    intro c M h
    by_contra hc
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / ‖c‖) hp1
    obtain ⟨k, hk, hle⟩ := h n
    rw [norm_mul, np] at hle
    have hpk : (p : ℝ) ^ n ≤ (p : ℝ) ^ k := pow_le_pow_right₀ hp1.le hk
    have h3 : M / ‖c‖ < (p : ℝ) ^ k := lt_of_lt_of_le hn hpk
    rw [div_lt_iff₀ hcpos] at h3
    linarith [mul_comm ‖c‖ ((p : ℝ) ^ k)]
  have ultra : ∀ {a b : K} {M : ℝ}, ‖a - b‖ ≤ 1 → ‖b‖ ≤ M → 1 ≤ M → ‖a‖ ≤ M := by
    intro a b M h hb hM
    calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ max ‖a - b‖ ‖b‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ M := max_le (h.trans hM) hb
  have hpp : 2 ≤ p ^ 2 := by nlinarith
  have lg_pow : ∀ k : ℕ, PowerSeries.coeff ((p ^ 2) ^ k) (lgF K p) = ((p : K) ^ k)⁻¹ := by
    intro k
    rw [lgF, PowerSeries.coeff_mk, Finset.sum_eq_single k]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Nat.pow_right_injective hpp h).symm
    · intro hk
      exfalso
      apply hk
      rw [Finset.mem_range]
      have : k < (p ^ 2) ^ k := Nat.lt_pow_self (by omega)
      omega
  have g0_pow : ∀ k : ℕ, PowerSeries.coeff (p * (p ^ 2) ^ k) (g0F K p) = ((p : K) ^ (k + 1))⁻¹ := by
    intro k
    rw [g0F, PowerSeries.coeff_mk, Finset.sum_eq_single k]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Nat.pow_right_injective hpp (Nat.eq_of_mul_eq_mul_left (by omega) h)).symm
    · intro hk
      exfalso
      apply hk
      rw [Finset.mem_range]
      have : k < (p ^ 2) ^ k := Nat.lt_pow_self (by omega)
      have : (p ^ 2) ^ k ≤ p * (p ^ 2) ^ k := Nat.le_mul_of_pos_left _ (by omega)
      omega
  have lg_zero : ∀ m : ℕ, (∀ l, m ≠ (p ^ 2) ^ l) → PowerSeries.coeff m (lgF K p) = 0 := by
    intro m hm
    rw [lgF, PowerSeries.coeff_mk]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (hm j)]
  have g01 : PowerSeries.coeff 1 (g0F K p) = 0 := by
    have := LemTwo.coeff_g0F_even (K := K) hp2 0
    rwa [pow_zero] at this
  have lg1 : PowerSeries.coeff 1 (lgF K p) = 1 := LemTwo.coeff_one_lgF hp2
  have hH2 : DivAB (swap2 H) := by
    intro n hn
    rw [LemTwo.fin_two_vector_eq_matrixVecCons n, LemTwo.coeff_swap2]
    apply hH
    rcases hn with h | h
    · right
      simp [h]
    · left
      simp [h]
  have cobInt : ∀ G : MvPowerSeries (Fin 2) K, Integral (d1 F G) → ∀ m, Integral (cob F (sl G m)) := by
    intro G hG m e
    rw [← LemTwo.coeff_partial_coboundary hF0 G e m]
    exact hG _
  have c0 : ∀ G : MvPowerSeries (Fin 2) K, DivAB G → ∀ m, PowerSeries.constantCoeff (sl G m) = 0 := by
    intro G hG m
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, sl, PowerSeries.coeff_mk]
    apply hG
    left
    simp
  choose α β R hα hR hsl using fun m => h1 K p σ hU F hF (sl H m) (c0 H hH m) (cobInt H hd m)
  choose α' β' R' hα' hR' hsl' using fun m =>
    h1 K p σ hU F hF (sl (swap2 H) m) (c0 _ hH2 m) (cobInt _ hd' m)
  have cH : ∀ i m, MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 m) H =
      α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p) +
        PowerSeries.coeff i (R m) := by
    intro i m
    have h3 := congrArg (PowerSeries.coeff i) (hsl m)
    rw [sl, PowerSeries.coeff_mk] at h3
    rw [h3, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  have cH' : ∀ i m, MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 m) H =
      α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p) +
        PowerSeries.coeff m (R' i) := by
    intro i m
    have h3 := congrArg (PowerSeries.coeff m) (hsl' i)
    rw [sl, PowerSeries.coeff_mk, LemTwo.coeff_swap2] at h3
    rw [h3, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  have star : ∀ i m, ‖(α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p)) -
      (α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p))‖ ≤ 1 := by
    intro i m
    have e : (α m * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p)) -
        (α' i * PowerSeries.coeff m (g0F K p) + β' i * PowerSeries.coeff m (lgF K p)) =
        PowerSeries.coeff m (R' i) - PowerSeries.coeff i (R m) := by
      have e1 := cH i m
      have e2 := cH' i m
      linear_combination e2 - e1
    rw [e]
    exact LemTwo.norm_sub_le_one (hR' i m) (hR m i)
  have hA : ∀ k, β' (p * (p ^ 2) ^ k) = 0 := by
    intro k
    apply zero_of_bdd _ ((p : ℝ) ^ (k + 1))
    intro N
    refine ⟨N, le_rfl, ?_⟩
    have s := star (p * (p ^ 2) ^ k) ((p ^ 2) ^ N)
    rw [g0_pow k, LemTwo.coeff_lgF_odd hp2 k, LemTwo.coeff_g0F_even hp2 N, lg_pow N] at s
    simp only [mul_zero, add_zero, zero_add] at s
    refine ultra (b := α ((p ^ 2) ^ N) * ((p : K) ^ (k + 1))⁻¹) ?_ ?_
      (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ p)))
    · rw [norm_sub_rev]
      exact s
    · rw [norm_mul, np]
      exact mul_le_of_le_one_left (by positivity) (hα _)
  have hB : ∀ m, α m = 0 := by
    intro m
    apply zero_of_bdd _ (max 1 ‖PowerSeries.coeff m (g0F K p)‖)
    intro N
    refine ⟨N + 1, by omega, ?_⟩
    have s := star (p * (p ^ 2) ^ N) m
    rw [g0_pow N, LemTwo.coeff_lgF_odd hp2 N, hA N] at s
    simp only [mul_zero, add_zero, zero_mul] at s
    refine ultra (b := α' (p * (p ^ 2) ^ N) * PowerSeries.coeff m (g0F K p)) s ?_ (le_max_left _ _)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hα' _)).trans (le_max_right _ _)
  have hC : ∀ m, (∀ l, m ≠ (p ^ 2) ^ l) → β m = 0 := by
    intro m hm
    apply zero_of_bdd _ (max 1 ‖PowerSeries.coeff m (g0F K p)‖)
    intro N
    refine ⟨N, le_rfl, ?_⟩
    have s := star ((p ^ 2) ^ N) m
    rw [LemTwo.coeff_g0F_even hp2 N, lg_pow N, lg_zero m hm, hB m] at s
    simp only [mul_zero, zero_mul, add_zero, zero_add] at s
    refine ultra (b := α' ((p ^ 2) ^ N) * PowerSeries.coeff m (g0F K p)) s ?_ (le_max_left _ _)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hα' _)).trans (le_max_right _ _)
  have hD : ∀ l, β ((p ^ 2) ^ l) = β 1 * ((p : K) ^ l)⁻¹ := by
    intro l
    rw [← sub_eq_zero]
    apply zero_of_bdd _ ((p : ℝ) ^ l)
    intro N
    refine ⟨N, le_rfl, ?_⟩
    have s1 := star ((p ^ 2) ^ N) ((p ^ 2) ^ l)
    have s2 := star ((p ^ 2) ^ N) 1
    rw [LemTwo.coeff_g0F_even hp2 N, lg_pow N, LemTwo.coeff_g0F_even hp2 l, lg_pow l, hB] at s1
    rw [LemTwo.coeff_g0F_even hp2 N, lg_pow N, g01, lg1, hB] at s2
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one] at s1 s2
    have e : (β ((p ^ 2) ^ l) - β 1 * ((p : K) ^ l)⁻¹) * ((p : K) ^ N)⁻¹ =
        (β ((p ^ 2) ^ l) * ((p : K) ^ N)⁻¹ - β' ((p ^ 2) ^ N) * ((p : K) ^ l)⁻¹) -
          ((p : K) ^ l)⁻¹ * (β 1 * ((p : K) ^ N)⁻¹ - β' ((p ^ 2) ^ N)) := by ring
    rw [e]
    have usub : ∀ a b : K, ‖a - b‖ ≤ max ‖a‖ ‖b‖ := fun a b => by
      rw [sub_eq_add_neg]
      have h4 := IsUltrametricDist.norm_add_le_max a (-b)
      rwa [norm_neg] at h4
    refine (usub _ _).trans (max_le ?_ ?_)
    · exact s1.trans (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ p)))
    · rw [norm_mul, np]
      exact mul_le_of_le_one_right (by positivity) s2
  refine ⟨β 1, H - MvPowerSeries.C (β 1) * (at1 0 (lgF K p) * at1 1 (lgF K p)), ?_, by ring⟩
  intro n
  rw [LemTwo.fin_two_vector_eq_matrixVecCons n]
  set i := n 0
  set m := n 1
  rw [map_sub, MvPowerSeries.coeff_C_mul, at1, at1, PowerSeries.coeff_subst_X_zero_subst_mul_X_one, cH,
    hB m]
  have ev0 : (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) m : Fin 2 →₀ ℕ) 0 = i := by simp
  have ev1 : (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) m : Fin 2 →₀ ℕ) 1 = m := by simp
  rw [ev0, ev1]
  have key : β m * PowerSeries.coeff i (lgF K p) -
      β 1 * (PowerSeries.coeff i (lgF K p) * PowerSeries.coeff m (lgF K p)) = 0 := by
    by_cases hm : ∃ l, m = (p ^ 2) ^ l
    · obtain ⟨l, hl⟩ := hm
      rw [hl, hD l, lg_pow l]
      ring
    · push_neg at hm
      rw [hC m hm, lg_zero m hm]
      ring
  have e : 0 * PowerSeries.coeff i (g0F K p) + β m * PowerSeries.coeff i (lgF K p) + PowerSeries.coeff i (R m) -
      β 1 * (PowerSeries.coeff i (lgF K p) * PowerSeries.coeff m (lgF K p)) =
      PowerSeries.coeff i (R m) + (β m * PowerSeries.coeff i (lgF K p) -
        β 1 * (PowerSeries.coeff i (lgF K p) * PowerSeries.coeff m (lgF K p))) := by ring
  rw [e, key, add_zero]
  exact hR m i

end Formalism.InvariantFactorPaths.G7

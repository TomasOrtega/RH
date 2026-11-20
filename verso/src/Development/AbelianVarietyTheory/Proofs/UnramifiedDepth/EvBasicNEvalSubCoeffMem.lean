import Mathlib
import ReciprocityTheory.DualLattices.FormalChartAtZero

noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

section

variable {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : Type} [CommRing S] [Algebra R₀ S]

/- English proof (translation)
Unfold `tEval`. Use `Finset.sum_bij' (fun e _ => fun i => (e i : ℕ)) (fun e he => fun i => ⟨e i, Finset.mem_range.mp (Fintype.mem_piFinset.mp he i)⟩) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `e _`. Conclude with `Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (e i).isLt`. Introduce `e _`.

Conclude with `Finset.mem_univ _`. Introduce `e _`. Both sides reduce to the same expression. Introduce `e _`. Both sides reduce to the same expression.

Introduce `e _`. Both sides reduce to the same expression.
-/
lemma evBasic_tEval_eq_sum (N : ℕ) (f : MvPowerSeries ι R₀) (a : ι → S) :
    tEval N f a = ∑ e ∈ Fintype.piFinset (fun _ : ι => Finset.range N),
      algebraMap R₀ S (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) f) *
        ∏ i, a i ^ e i := by
  unfold tEval
  refine Finset.sum_bij' (fun e _ => fun i => (e i : ℕ))
    (fun e he => fun i => ⟨e i, Finset.mem_range.mp (Fintype.mem_piFinset.mp he i)⟩) ?_ ?_ ?_ ?_ ?_
  · intro e _
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (e i).isLt
  · intro e _
    exact Finset.mem_univ _
  · intro e _
    rfl
  · intro e _
    rfl
  · intro e _
    rfl

/- English proof (translation)
Rewrite using `[evBasic_tEval_eq_sum, evBasic_tEval_eq_sum]`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `e he`. Rewrite `he`, the goal using `[Fintype.mem_piFinset]`. Conclude with `fun i => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp (he i)) hN)`.

Introduce `e _ hne`. Rewrite `hne` using `[Fintype.mem_piFinset]`. Use `push Not at hne`. Take `⟨i, hi⟩` from `hne`. Rewrite `hi` using `[Finset.mem_range, not_lt]`.

Establish `hz : ∏ j, a j ^ e j = 0` using `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← Nat.sub_add_cancel hi, pow_add, ha i, mul_zero])`. Rewrite using `[hz, mul_zero]`.
-/
lemma evBasic_tEval_of_le {N N' : ℕ} (hN : N ≤ N') (f : MvPowerSeries ι R₀) (a : ι → S)
    (ha : ∀ i, a i ^ N = 0) : tEval N f a = tEval N' f a := by
  rw [evBasic_tEval_eq_sum, evBasic_tEval_eq_sum]
  apply Finset.sum_subset
  · intro e he
    rw [Fintype.mem_piFinset] at he ⊢
    exact fun i => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp (he i)) hN)
  · intro e _ hne
    rw [Fintype.mem_piFinset] at hne
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    rw [Finset.mem_range, not_lt] at hi
    have hz : ∏ j, a j ^ e j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← Nat.sub_add_cancel hi, pow_add, ha i, mul_zero])
    rw [hz, mul_zero]

/- English proof (translation)
Break down `le_total N N' with h | h` into its components or cases. Conclude with `evBasic_tEval_of_le h f a ha`. Conclude with `(evBasic_tEval_of_le h f a ha').symm`.
-/
lemma evBasic_tEval_indep {N N' : ℕ} (f : MvPowerSeries ι R₀) (a : ι → S)
    (ha : ∀ i, a i ^ N = 0) (ha' : ∀ i, a i ^ N' = 0) : tEval N f a = tEval N' f a := by
  rcases le_total N N' with h | h
  · exact evBasic_tEval_of_le h f a ha
  · exact (evBasic_tEval_of_le h f a ha').symm

/- English proof (translation)
Unfold `nEval`. Use `split_ifs with h`. Conclude with `evBasic_tEval_indep f a (Nat.find_spec h) ha`. Conclude with `absurd ⟨N, ha⟩ h`.
-/
lemma evBasic_nEval_eq_tEval (f : MvPowerSeries ι R₀) (a : ι → S) (N : ℕ)
    (ha : ∀ i, a i ^ N = 0) : nEval f a = tEval N f a := by
  classical
  unfold nEval
  split_ifs with h
  · exact evBasic_tEval_indep f a (Nat.find_spec h) ha
  · exact absurd ⟨N, ha⟩ h

omit [DecidableEq ι] in

/- English proof (translation)
Establish `ha' : ∀ i, ∃ m : ℕ, a i ^ m = 0` using `ha`. Use `choose n hn using ha'`. Use `⟨(∑ i, n i) + 1, Nat.succ_pos _, fun i => pow_eq_zero_of_le ?_ (hn i)⟩` and prove the remaining obligations. Conclude with `(Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)).trans (Nat.le_succ _)`.
-/
lemma evBasic_exists_pow (a : ι → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, a i ^ N = 0 := by
  have ha' : ∀ i, ∃ m : ℕ, a i ^ m = 0 := ha
  choose n hn using ha'
  refine ⟨(∑ i, n i) + 1, Nat.succ_pos _, fun i => pow_eq_zero_of_le ?_ (hn i)⟩
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)).trans (Nat.le_succ _)

/- English proof (translation)
Unfold `tEval`. Simplify using `only [map_sum, map_mul, map_prod, map_pow, AlgHom.commutes]`.
-/
lemma evBasic_map_tEval {S' : Type} [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (N : ℕ)
    (f : MvPowerSeries ι R₀) (a : ι → S) :
    φ (tEval N f a) = tEval N f (fun i => φ (a i)) := by
  unfold tEval
  simp only [map_sum, map_mul, map_prod, map_pow, AlgHom.commutes]

/- English proof (translation)
Take `⟨N, -, hN⟩` from `evBasic_exists_pow a ha`. Establish `hN' : ∀ i, φ (a i) ^ N = 0` using `fun i => by rw [← map_pow, hN i, map_zero]`. Rewrite using `[evBasic_nEval_eq_tEval f a N hN, evBasic_nEval_eq_tEval f _ N hN', evBasic_map_tEval]`.
-/
lemma evBasic_map_nEval {S' : Type} [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S')
    (f : MvPowerSeries ι R₀) (a : ι → S) (ha : ∀ i, IsNilpotent (a i)) :
    φ (nEval f a) = nEval f (fun i => φ (a i)) := by
  obtain ⟨N, -, hN⟩ := evBasic_exists_pow a ha
  have hN' : ∀ i, φ (a i) ^ N = 0 := fun i => by rw [← map_pow, hN i, map_zero]
  rw [evBasic_nEval_eq_tEval f a N hN, evBasic_nEval_eq_tEval f _ N hN', evBasic_map_tEval]

/- English proof (translation)
Take `⟨N, hNpos, hN⟩` from `evBasic_exists_pow a ha`. Rewrite using `[evBasic_nEval_eq_tEval f a N hN, evBasic_tEval_eq_sum]`. Establish `h0 : (0 : ι → ℕ) ∈ Fintype.piFinset (fun _ : ι => Finset.range N)` using `Fintype.mem_piFinset.mpr fun _ => Finset.mem_range.mpr hNpos`. Rewrite using `[← Finset.add_sum_erase _ _ h0]`. Establish `hc : algebraMap R₀ S (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (0 : ι → ℕ)) f) * ∏ i, a i ^ (0 : ι → ℕ) i = algebraMap R₀ S (MvPowerSeries.coeff 0 f)`.

Establish `hz : Finsupp.equivFunOnFinite.symm (0 : ι → ℕ) = 0`. Use extensionality with `i`. Both sides reduce to the same expression. Simplify using `[hz]`. Rewrite using `[hc, add_sub_cancel_left]`.

Use `Ideal.sum_mem _ fun e he => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, e i ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `Finset.ne_of_mem_erase he (funext hcon)`.

Use `Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self i) : a i ∈ Ideal.span (Set.range a)) _ (Nat.pos_of_ne_zero hi))`.
-/
lemma evBasic_nEval_sub_coeff_mem (f : MvPowerSeries ι R₀) (a : ι → S)
    (ha : ∀ i, IsNilpotent (a i)) :
    nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a) := by
  obtain ⟨N, hNpos, hN⟩ := evBasic_exists_pow a ha
  rw [evBasic_nEval_eq_tEval f a N hN, evBasic_tEval_eq_sum]
  have h0 : (0 : ι → ℕ) ∈ Fintype.piFinset (fun _ : ι => Finset.range N) :=
    Fintype.mem_piFinset.mpr fun _ => Finset.mem_range.mpr hNpos
  rw [← Finset.add_sum_erase _ _ h0]
  have hc : algebraMap R₀ S (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (0 : ι → ℕ)) f) *
      ∏ i, a i ^ (0 : ι → ℕ) i = algebraMap R₀ S (MvPowerSeries.coeff 0 f) := by
    have hz : Finsupp.equivFunOnFinite.symm (0 : ι → ℕ) = 0 := by
      ext i
      rfl
    simp [hz]
  rw [hc, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun e he => ?_
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact Finset.ne_of_mem_erase he (funext hcon)
  refine Ideal.mul_mem_left _ _ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _
    (Ideal.subset_span (Set.mem_range_self i) : a i ∈ Ideal.span (Set.range a)) _ (Nat.pos_of_ne_zero hi))

end

/- English proof (translation)
Introduce `R₀ _ ι _ _ f S _ _ a`. Conclude with `⟨fun N hN => evBasic_nEval_eq_tEval f a N hN, fun ha => ⟨fun S' _ _ φ => evBasic_map_nEval φ f a ha, evBasic_nEval_sub_coeff_mem f a ha⟩⟩`.
-/
theorem nEval_basic :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) := by
  intro R₀ _ ι _ _ f S _ _ a
  exact ⟨fun N hN => evBasic_nEval_eq_tEval f a N hN,
    fun ha => ⟨fun S' _ _ φ => evBasic_map_nEval φ f a ha, evBasic_nEval_sub_coeff_mem f a ha⟩⟩

end GlobalTheory

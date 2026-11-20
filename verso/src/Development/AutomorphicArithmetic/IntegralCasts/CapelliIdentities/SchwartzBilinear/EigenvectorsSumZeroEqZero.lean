import Mathlib

namespace UpperTheory.Reformulated.B.P6.r14a

/- English proof (translation)
Introduce `s`. Proceed by induction on `s using Finset.strongInduction with`. Consider the case `H s ih`. Introduce `v hv hsum a ha`. Distinguish the cases in `hall : ∀ b ∈ s, b = a`.

Establish `h1 : ∑ i ∈ s, v i = v a`. Apply `Finset.sum_eq_single_of_mem a ha` to reduce the goal to its premises. Introduce `b hb hba`. Conclude with `absurd (hall b hb) hba`. Rewrite using `[← h1]`.

Conclude with `hsum`. Use `push_neg at hall`. Take `⟨b, hb, hba⟩` from `hall`. Establish `hfb : f b ≠ f a` using `fun h => hba (hf h)`. Take `⟨k, hk⟩ : ∃ k, f b k ≠ f a k` from `Function.ne_iff.mp hfb`.

Establish `hw_eig : ∀ i ∈ s.erase a, ∀ k', T k' ((f i k - f a k) • v i) = f i k' • ((f i k - f a k) • v i)`. Introduce `i hi k'`. Rewrite using `[map_smul, hv i (Finset.mem_of_mem_erase hi) k', smul_comm]`. Establish `h2 : ∑ i ∈ s, (f i k - f a k) • v i = 0`. Establish `h3 : ∑ i ∈ s, (f i k - f a k) • v i = T k (∑ i ∈ s, v i) - f a k • ∑ i ∈ s, v i`.

Rewrite using `[map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[hv i hi k, sub_smul]`. Rewrite using `[h3, hsum, map_zero, smul_zero, sub_zero]`.

Establish `hw_sum : ∑ i ∈ s.erase a, (f i k - f a k) • v i = 0`. Establish `h4` using `Finset.sum_erase_add s (fun i => (f i k - f a k) • v i) ha`. Simplify using `only [sub_self, zero_smul, add_zero] at h4`. Rewrite using `[h4]`. Conclude with `h2`.

Establish `hw0` using `ih (s.erase a) (Finset.erase_ssubset ha) (fun i => (f i k - f a k) • v i) hw_eig hw_sum`. Establish `hz : ∀ i ∈ s, f i k ≠ f a k → v i = 0`. Introduce `i hi hne`. Establish `hia : i ≠ a` using `fun h => hne (by rw [h])`. Establish `h5 : (f i k - f a k) • v i = 0` using `hw0 i (Finset.mem_erase.mpr ⟨hia, hi⟩)`.

Break down `smul_eq_zero.mp h5 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h) hne`. Conclude with `h`. Establish `hts : s.filter (fun i => f i k = f a k) ⊂ s`. Rewrite using `[Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]`.

Conclude with `⟨b, hb, fun h => hk (Finset.mem_filter.mp h).2⟩`. Establish `hsum_t : ∑ i ∈ s.filter (fun i => f i k = f a k), v i = 0`. Rewrite using `[Finset.sum_filter_of_ne]`. Conclude with `hsum`. Introduce `i hi hvi`.

Assume the negation of the conclusion as `hne`. Conclude with `hvi (hz i hi hne)`. Conclude with `ih _ hts v (fun i hi k' => hv i (Finset.filter_subset _ _ hi) k') hsum_t a (Finset.mem_filter.mpr ⟨ha, rfl⟩)`.
-/
theorem eigenvectors_sum_zero_eq_zero {ι κ A : Type} [DecidableEq ι] [AddCommGroup A] [Module ℂ A]
    (T : κ → Module.End ℂ A) (f : ι → κ → ℂ) (hf : Function.Injective f) :
    ∀ (s : Finset ι) (v : ι → A), (∀ i ∈ s, ∀ k, T k (v i) = f i k • v i) →
      ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0 := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro v hv hsum a ha
    by_cases hall : ∀ b ∈ s, b = a
    · have h1 : ∑ i ∈ s, v i = v a := by
        apply Finset.sum_eq_single_of_mem a ha
        intro b hb hba
        exact absurd (hall b hb) hba
      rw [← h1]
      exact hsum
    · push_neg at hall
      obtain ⟨b, hb, hba⟩ := hall
      have hfb : f b ≠ f a := fun h => hba (hf h)
      obtain ⟨k, hk⟩ : ∃ k, f b k ≠ f a k := Function.ne_iff.mp hfb
      have hw_eig : ∀ i ∈ s.erase a, ∀ k', T k' ((f i k - f a k) • v i)
          = f i k' • ((f i k - f a k) • v i) := by
        intro i hi k'
        rw [map_smul, hv i (Finset.mem_of_mem_erase hi) k', smul_comm]
      have h2 : ∑ i ∈ s, (f i k - f a k) • v i = 0 := by
        have h3 : ∑ i ∈ s, (f i k - f a k) • v i
            = T k (∑ i ∈ s, v i) - f a k • ∑ i ∈ s, v i := by
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hv i hi k, sub_smul]
        rw [h3, hsum, map_zero, smul_zero, sub_zero]
      have hw_sum : ∑ i ∈ s.erase a, (f i k - f a k) • v i = 0 := by
        have h4 := Finset.sum_erase_add s (fun i => (f i k - f a k) • v i) ha
        simp only [sub_self, zero_smul, add_zero] at h4
        rw [h4]
        exact h2
      have hw0 := ih (s.erase a) (Finset.erase_ssubset ha)
        (fun i => (f i k - f a k) • v i) hw_eig hw_sum
      have hz : ∀ i ∈ s, f i k ≠ f a k → v i = 0 := by
        intro i hi hne
        have hia : i ≠ a := fun h => hne (by rw [h])
        have h5 : (f i k - f a k) • v i = 0 := hw0 i (Finset.mem_erase.mpr ⟨hia, hi⟩)
        rcases smul_eq_zero.mp h5 with h | h
        · exact absurd (sub_eq_zero.mp h) hne
        · exact h
      have hts : s.filter (fun i => f i k = f a k) ⊂ s := by
        rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
        exact ⟨b, hb, fun h => hk (Finset.mem_filter.mp h).2⟩
      have hsum_t : ∑ i ∈ s.filter (fun i => f i k = f a k), v i = 0 := by
        rw [Finset.sum_filter_of_ne]
        · exact hsum
        · intro i hi hvi
          by_contra hne
          exact hvi (hz i hi hne)
      exact ih _ hts v (fun i hi k' => hv i (Finset.filter_subset _ _ hi) k') hsum_t a
        (Finset.mem_filter.mpr ⟨ha, rfl⟩)

/- English proof (translation)
Introduce `ι κ A _ _ _ T f hf s v hv hsum`. Conclude with `eigenvectors_sum_zero_eq_zero T f hf s v hv hsum`.
-/
theorem GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec :
    ∀ {ι κ A : Type} [DecidableEq ι] [inst : AddCommGroup A] [inst_1 : _root_.Module ℂ A] (T : κ → Module.End ℂ A) (f : ι → κ → ℂ), Function.Injective f → ∀ (s : Finset ι) (v : ι → A), (∀ i ∈ s, ∀ (k : κ), DFunLike.coe (T k) (v i) = f i k • v i) → ∑ i ∈ s, v i = OfNat.ofNat (nat_lit 0) → ∀ i ∈ s, v i = OfNat.ofNat (nat_lit 0) := by
  intro ι κ A _ _ _ T f hf s v hv hsum
  exact eigenvectors_sum_zero_eq_zero T f hf s v hv hsum

end UpperTheory.Reformulated.B.P6.r14a

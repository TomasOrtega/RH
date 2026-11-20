import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatSpan

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B]

/- English proof (translation)
Establish `hc : (((i + j).choose i : ℕ) : ℚ) * ((i + j).factorial : ℚ)⁻¹ = ((i.factorial : ℚ))⁻¹ * ((j.factorial : ℚ))⁻¹`. Establish `h` using `Nat.add_choose_mul_factorial_mul_factorial i j`. Rewrite `h` using `[← Nat.choose_symm_add]`. Establish `h' : (((i + j).choose i : ℕ) : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ) = ((i + j).factorial : ℚ)` using `by exact_mod_cast h`. Establish `hi : (i.factorial : ℚ) ≠ 0` using `by exact_mod_cast i.factorial_ne_zero`.

Establish `hj : (j.factorial : ℚ) ≠ 0` using `by exact_mod_cast j.factorial_ne_zero`. Rewrite using `[← h']`. Establish `hcne : (((i + j).choose i : ℕ) : ℚ) ≠ 0`. Conclude with `(Nat.choose_pos (Nat.le_add_right i j)).ne'` after adjusting the coercions. Clear the denominators using the available nonvanishing facts.

Unfold `Lat.dpE`. Rewrite using `[smul_mul_smul_comm, ← pow_add, ← hc, ← smul_smul, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul ℚ]`.
-/
theorem dpE_mul (f : W →+* B) (ξ : W) (l M i j : ℕ) :
    Lat.dpE f ξ l M i * Lat.dpE f ξ l M j =
      ((i + j).choose i : B) * Lat.dpE f ξ l M (i + j) := by
  have hc : (((i + j).choose i : ℕ) : ℚ) * ((i + j).factorial : ℚ)⁻¹ =
      ((i.factorial : ℚ))⁻¹ * ((j.factorial : ℚ))⁻¹ := by
    have h := Nat.add_choose_mul_factorial_mul_factorial i j
    rw [← Nat.choose_symm_add] at h
    have h' : (((i + j).choose i : ℕ) : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ) =
        ((i + j).factorial : ℚ) := by exact_mod_cast h
    have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    rw [← h']
    have hcne : (((i + j).choose i : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_right i j)).ne'
    field_simp
  unfold Lat.dpE
  rw [smul_mul_smul_comm, ← pow_add, ← hc, ← smul_smul, ← nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul ℚ]

/- English proof (translation)
Use `letI : Algebra W B := f.toAlgebra`. Establish `hsm : ∀ (w : W) (b : B), w • b = f w * b` using `fun w b => Algebra.smul_def w b`. Establish `h0 : Lat.dpE f ξ l M 0 = 1` using `by simp [Lat.dpE]`. Establish `hgen : ∀ i, Lat.dpE f ξ l M i ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M))` using `fun i => Submodule.subset_span ⟨i, rfl⟩`. Establish `hW : ∀ w : W, f w ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M))`.

Introduce `w`. Establish `h` using `Submodule.smul_mem _ w (hgen 0)`. Rewrite `h` using `[hsm, h0, mul_one]`. Then use the resulting hypothesis. Establish `hnat : ∀ (n : ℕ) (y : B), y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) → (n : B) * y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M))`. Introduce `n y hy`.

Establish `h` using `Submodule.smul_mem _ (n : W) hy`. Rewrite `h` using `[hsm, map_natCast]`. Then use the resulting hypothesis. Establish `hmul : ∀ a b : B, a ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) → b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) → a * b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M))`. Introduce `a b ha hb`. Proceed by induction on `ha using Submodule.span_induction with`.

Consider the case `mem a ha`. Take `⟨i, rfl⟩` from `ha`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem b hb`. Take `⟨j, rfl⟩` from `hb`.

Rewrite using `[dpE_mul]`. Conclude with `hnat _ _ (hgen _)`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [mul_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul w y _ hy => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ w hy`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [add_mul]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul w y _ hy => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ w hy`. Unfold `Lat.sub at hx`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem y hy`.

Break down `hy with ⟨w, rfl⟩ | ⟨i, rfl⟩` into its components or cases. Conclude with `hW w`. Conclude with `hgen i`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `one => rw [← h0]`.

Conclude with `hgen 0`. Consider the case `add y z _ _ hy hz => exact Submodule.add_mem _ hy hz`. Consider the case `neg y _ hy => exact Submodule.neg_mem _ hy`. Consider the case `mul y z _ _ hy hz => exact hmul y z hy hz`.
-/
theorem mem_span_of_mem_sub (f : W →+* B) (ξ : W) (l M : ℕ) (x : B) (hx : x ∈ Lat.sub f ξ l M) :
    letI : Algebra W B := f.toAlgebra
    x ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
  letI : Algebra W B := f.toAlgebra
  have hsm : ∀ (w : W) (b : B), w • b = f w * b := fun w b => Algebra.smul_def w b
  have h0 : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]
  have hgen : ∀ i, Lat.dpE f ξ l M i ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) :=
    fun i => Submodule.subset_span ⟨i, rfl⟩
  have hW : ∀ w : W, f w ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro w
    have h := Submodule.smul_mem _ w (hgen 0)
    rwa [hsm, h0, mul_one] at h
  have hnat : ∀ (n : ℕ) (y : B), y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      (n : B) * y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro n y hy
    have h := Submodule.smul_mem _ (n : W) hy
    rwa [hsm, map_natCast] at h
  have hmul : ∀ a b : B, a ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      a * b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨j, rfl⟩ := hb
        rw [dpE_mul]
        exact hnat _ _ (hgen _)
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
      | smul w y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ w hy
    | zero => simp
    | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
    | smul w y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ w hy
  unfold Lat.sub at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · exact hW w
    · exact hgen i
  | zero => exact Submodule.zero_mem _
  | one => rw [← h0]; exact hgen 0
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | neg y _ hy => exact Submodule.neg_mem _ hy
  | mul y z _ _ hy hz => exact hmul y z hy hz

/- English proof (translation)
Introduce `W B _ _ _ f ξ l M x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `letI : Algebra W B := f.toAlgebra`. Establish `hsm : ∀ (w : W) (b : B), w • b = f w * b` using `fun w b => Algebra.smul_def w b`.

Take `⟨c, rfl⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_of_mem_sub f ξ l M x hx)`. Use `⟨c.support.sup id + 1, fun i => c i, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => f (c i) * Lat.dpE f ξ l M i), Finsupp.sum]`. Establish `hsub : c.support ⊆ Finset.range (c.support.sup id + 1)`. Introduce `i hi`.

Conclude with `Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))`. Rewrite using `[Finset.sum_congr rfl (fun i _ => hsm (c i) (Lat.dpE f ξ l M i))]`. Use `Finset.sum_subset hsub fun i _ hi => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.notMem_support_iff.1 hi, map_zero, zero_mul]`. Introduce and unpack `⟨n, c, rfl⟩`.

Use `Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ ?_` and prove the remaining obligations. Conclude with `Subring.subset_closure (Or.inl ⟨c i, rfl⟩)`. Conclude with `Subring.subset_closure (Or.inr ⟨i, rfl⟩)`.
-/
theorem mem_sub_iff : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (x : B), x ∈ Lat.sub f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), x = ∑ i, f (c i) * Lat.dpE f ξ l M i := by
  intro W B _ _ _ f ξ l M x
  constructor
  · intro hx
    letI : Algebra W B := f.toAlgebra
    have hsm : ∀ (w : W) (b : B), w • b = f w * b := fun w b => Algebra.smul_def w b
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_of_mem_sub f ξ l M x hx)
    refine ⟨c.support.sup id + 1, fun i => c i, ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => f (c i) * Lat.dpE f ξ l M i), Finsupp.sum]
    have hsub : c.support ⊆ Finset.range (c.support.sup id + 1) := by
      intro i hi
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
    rw [Finset.sum_congr rfl (fun i _ => hsm (c i) (Lat.dpE f ξ l M i))]
    refine Finset.sum_subset hsub fun i _ hi => ?_
    rw [Finsupp.notMem_support_iff.1 hi, map_zero, zero_mul]
  · rintro ⟨n, c, rfl⟩
    refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ ?_
    · exact Subring.subset_closure (Or.inl ⟨c i, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.LatSpan

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.BlockGS

/- English proof (translation)
Take `⟨l, hl, rfl⟩` from `(Finsupp.mem_span_image_iff_linearCombination ℂ).1 hv`. Use `⟨l, fun y hy => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hy (hl (Finsupp.mem_support_iff.2 h))`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype]`.

Simplify using the standard rewrite rules.
-/
theorem exists_coeff_of_mem_span {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    (g : ι → V) (s : Set ι) (v : V) (hv : v ∈ Submodule.span ℂ (g '' s)) :
    ∃ c : ι → ℂ, (∀ y, y ∉ s → c y = 0) ∧ v = ∑ y, c y • g y := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hv
  refine ⟨l, fun y hy => ?_, ?_⟩
  · by_contra h
    exact hy (hl (Finsupp.mem_support_iff.2 h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    simp

/- English proof (translation)
Set `_ : LocallyFiniteOrderBot ι` to `LocallyFiniteOrderBot.ofIic ι (fun x => Finset.univ.filter (· ≤ x)) (by simp)`. Establish `: WellFoundedLT ι` using `Finite.to_wellFoundedLT`. Establish `hs : ∀ x, Submodule.span ℂ (InnerProductSpace.gramSchmidtNormed ℂ f '' Set.Iic x) = Submodule.span ℂ (f '' Set.Iic x)` using `fun x => by`. Rewrite using `[InnerProductSpace.span_gramSchmidtNormed, InnerProductSpace.span_gramSchmidt_Iic]`. Establish `h1 : ∀ x, ∃ c : ι → ℂ, (∀ y, y ∉ Set.Iic x → c y = 0) ∧ f x = ∑ y, c y • InnerProductSpace.gramSchmidtNormed ℂ f y` using `fun x => exists_coeff_of_mem_span _ _ _ (by`.

Rewrite using `[hs]`. Conclude with `Submodule.subset_span ⟨x, le_refl x, rfl⟩)`. Establish `h2 : ∀ x, ∃ c : ι → ℂ, (∀ y, y ∉ Set.Iic x → c y = 0) ∧ InnerProductSpace.gramSchmidtNormed ℂ f x = ∑ y, c y • f y` using `fun x => exists_coeff_of_mem_span _ _ _ (by`. Rewrite using `[← hs]`. Conclude with `Submodule.subset_span ⟨x, le_refl x, rfl⟩)`.

Use `choose P hP hP' using h1`. Use `choose Q hQ hQ' using h2`. Conclude with `⟨_, fun y x => P x y, fun y x => Q x y, InnerProductSpace.gramSchmidtNormed_orthonormal hf, fun y x h => ⟨hP x y (not_le.2 h), hQ x y (not_le.2 h)⟩, hP', hQ'⟩`.
-/
theorem exists_orthonormal_triangular {ι V : Type} [Fintype ι] [LinearOrder ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f : ι → V) (hf : LinearIndependent ℂ f) :
    ∃ (g : ι → V) (P Q : ι → ι → ℂ), Orthonormal ℂ g ∧ (∀ y x, x < y → P y x = 0 ∧ Q y x = 0) ∧
      (∀ x, f x = ∑ y, P y x • g y) ∧ ∀ x, g x = ∑ y, Q y x • f y := by
  classical
  let _ : LocallyFiniteOrderBot ι := LocallyFiniteOrderBot.ofIic ι (fun x => Finset.univ.filter (· ≤ x)) (by simp)
  have : WellFoundedLT ι := Finite.to_wellFoundedLT
  have hs : ∀ x, Submodule.span ℂ (InnerProductSpace.gramSchmidtNormed ℂ f '' Set.Iic x)
      = Submodule.span ℂ (f '' Set.Iic x) := fun x => by
    rw [InnerProductSpace.span_gramSchmidtNormed, InnerProductSpace.span_gramSchmidt_Iic]
  have h1 : ∀ x, ∃ c : ι → ℂ, (∀ y, y ∉ Set.Iic x → c y = 0) ∧
      f x = ∑ y, c y • InnerProductSpace.gramSchmidtNormed ℂ f y := fun x =>
    exists_coeff_of_mem_span _ _ _ (by
      rw [hs]; exact Submodule.subset_span ⟨x, le_refl x, rfl⟩)
  have h2 : ∀ x, ∃ c : ι → ℂ, (∀ y, y ∉ Set.Iic x → c y = 0) ∧
      InnerProductSpace.gramSchmidtNormed ℂ f x = ∑ y, c y • f y := fun x =>
    exists_coeff_of_mem_span _ _ _ (by
      rw [← hs]; exact Submodule.subset_span ⟨x, le_refl x, rfl⟩)
  choose P hP hP' using h1
  choose Q hQ hQ' using h2
  exact ⟨_, fun y x => P x y, fun y x => Q x y, InnerProductSpace.gramSchmidtNormed_orthonormal hf,
    fun y x h => ⟨hP x y (not_le.2 h), hQ x y (not_le.2 h)⟩, hP', hQ'⟩

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce and unpack `c hc ⟨i, u⟩`. Establish `hr : ∀ r, ∑ x : (Σ i, Fin (j i)), c x * A x.1 r x.2 = 0` using `fun r => by`. Use `congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) hc` as an intermediate fact. Simplify using `using this`.

Establish `h : ∑ x : (Σ i, Fin (j i)), c x * (C i * A x.1) u x.2 = 0`. Simplify using `only [Matrix.mul_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun r _ => ?_` and prove the remaining obligations. Use `congrArg (fun z => C i u r * z) (hr r)` as an intermediate fact.

Simplify using `only [Finset.mul_sum, mul_zero] at this`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun x _ => by ring`. Rewrite `h` using `[Fintype.sum_sigma, Finset.sum_eq_single i]`. Simplify `h` using `[h1, Matrix.one_apply]`.

Introduce `k _ hk`. Simplify using `[h0 i k hk.symm]`. Simplify using the standard rewrite rules.
-/
theorem linearIndependent_columns (n a : ℕ) (j : Fin a → ℕ)
    (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ)
    (h1 : ∀ i, C i * A i = 1) (h0 : ∀ i k, i ≠ k → C i * A k = 0) :
    LinearIndependent ℂ (fun x : (Σ i, Fin (j i)) =>
      (WithLp.toLp 2 (fun r => A x.1 r x.2) : EuclideanSpace ℂ (Fin n))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  rintro c hc ⟨i, u⟩
  have hr : ∀ r, ∑ x : (Σ i, Fin (j i)), c x * A x.1 r x.2 = 0 := fun r => by
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) hc
    simpa using this
  have h : ∑ x : (Σ i, Fin (j i)), c x * (C i * A x.1) u x.2 = 0 := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun r _ => ?_
    have := congrArg (fun z => C i u r * z) (hr r)
    simp only [Finset.mul_sum, mul_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [Fintype.sum_sigma, Finset.sum_eq_single i] at h
  · simpa [h1, Matrix.one_apply] using h
  · intro k _ hk
    simp [h0 i k hk.symm]
  · simp

/- English proof (translation)
Introduce `n a j A C h1 h0`. Set `_ : LinearOrder (Σ i, Fin (j i))` to `inferInstanceAs (LinearOrder (Σₗ i, Fin (j i)))`. Take `⟨g, P, Q, hg, htri, hf, hg'⟩` from `exists_orthonormal_triangular _ (linearIndependent_columns n a j A C h1 h0)`. Set `B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ` to `fun i => Matrix.of fun r u => g ⟨i, u⟩ r`. Set `p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ` to `fun k i => Matrix.of fun v u => P ⟨k, v⟩ ⟨i, u⟩`.

Set `q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ` to `fun k i => Matrix.of fun v u => Q ⟨k, v⟩ ⟨i, u⟩`. Establish `hBB : ∀ i k u v, ((B i)ᴴ * B k) u v = inner ℂ (g ⟨i, u⟩) (g ⟨k, v⟩)`. Introduce `i k u v`. Simplify using `[B, Matrix.mul_apply, PiLp.inner_apply, mul_comm]`. Establish `e1 : ∀ i, (B i)ᴴ * B i = 1`.

Introduce `i`. Use extensionality with `u v`. Rewrite using `[hBB, orthonormal_iff_ite.1 hg, Matrix.one_apply]`. Simplify using the standard rewrite rules. Establish `e2 : ∀ i k, i ≠ k → (B i)ᴴ * B k = 0`.

Introduce `i k h`. Use extensionality with `u v`. Rewrite using `[hBB, orthonormal_iff_ite.1 hg]`. Simplify using `[h]`. Establish `e3 : ∀ k i, i < k → p k i = 0 ∧ q k i = 0`.

Introduce `k i h`. Apply the tactic sequence `constructor <;> ext v u`. Conclude with `(htri _ _ (Sigma.Lex.left _ _ h)).1`. Conclude with `(htri _ _ (Sigma.Lex.left _ _ h)).2`. Establish `e4 : ∀ i, A i = ∑ k, B k * p k i`.

Introduce `i`. Use extensionality with `r u`. Use `congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) (hf ⟨i, u⟩)` as an intermediate fact. Simplify using `only [Matrix.sum_apply, Matrix.mul_apply, B, p, Matrix.of_apply]`. Simplify `this` using `[Fintype.sum_sigma, mul_comm]`.

Establish `e5 : ∀ i, B i = ∑ k, A k * q k i`. Introduce `i`. Use extensionality with `r u`. Use `congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) (hg' ⟨i, u⟩)` as an intermediate fact. Simplify using `only [Matrix.sum_apply, Matrix.mul_apply, B, q, Matrix.of_apply]`.

Simplify `this` using `[Fintype.sum_sigma, mul_comm]`. Use `⟨B, p, q, e1, e2, e3, e4, e5, fun i => ?_⟩` and prove the remaining obligations. Establish `hp : ∀ k, (B i)ᴴ * A k = p i k`. Introduce `k`. Rewrite using `[e4 k, Matrix.mul_sum, Finset.sum_eq_single i]`.

Rewrite using `[← Matrix.mul_assoc, e1, Matrix.one_mul]`. Introduce `l _ hl`. Rewrite using `[← Matrix.mul_assoc, e2 i l hl.symm, Matrix.zero_mul]`. Simplify using the standard rewrite rules. Establish `h : (B i)ᴴ * (∑ k, A k * q k i) = 1` using `by rw [← e5, e1]`.

Rewrite `h` using `[Matrix.mul_sum, Finset.sum_eq_single i]`. Rewrite using `[← h, ← Matrix.mul_assoc, hp]`. Introduce `l _ hl`. Rewrite using `[← Matrix.mul_assoc, hp]`. Break down `lt_or_gt_of_ne hl with hl | hl` into its components or cases.

Rewrite using `[(e3 i l hl).1, Matrix.zero_mul]`. Rewrite using `[(e3 l i hl).2, Matrix.mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem block_gramSchmidt : ∀ (n a : ℕ) (j : Fin a → ℕ) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ), (∀ i, C i * A i = 1) → (∀ i k, i ≠ k → C i * A k = 0) → ∃ (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ), (∀ i, (B i)ᴴ * B i = 1) ∧ (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) ∧ (∀ k i, i < k → p k i = 0 ∧ q k i = 0) ∧ (∀ i, A i = ∑ k, B k * p k i) ∧ (∀ i, B i = ∑ k, A k * q k i) ∧ ∀ i, p i i * q i i = 1 := by
  classical
  intro n a j A C h1 h0
  let _ : LinearOrder (Σ i, Fin (j i)) := inferInstanceAs (LinearOrder (Σₗ i, Fin (j i)))
  obtain ⟨g, P, Q, hg, htri, hf, hg'⟩ :=
    exists_orthonormal_triangular _ (linearIndependent_columns n a j A C h1 h0)
  let B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ := fun i => Matrix.of fun r u => g ⟨i, u⟩ r
  let p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ := fun k i => Matrix.of fun v u => P ⟨k, v⟩ ⟨i, u⟩
  let q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ := fun k i => Matrix.of fun v u => Q ⟨k, v⟩ ⟨i, u⟩
  have hBB : ∀ i k u v, ((B i)ᴴ * B k) u v = inner ℂ (g ⟨i, u⟩) (g ⟨k, v⟩) := by
    intro i k u v
    simp [B, Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  have e1 : ∀ i, (B i)ᴴ * B i = 1 := by
    intro i
    ext u v
    rw [hBB, orthonormal_iff_ite.1 hg, Matrix.one_apply]
    simp
  have e2 : ∀ i k, i ≠ k → (B i)ᴴ * B k = 0 := by
    intro i k h
    ext u v
    rw [hBB, orthonormal_iff_ite.1 hg]
    simp [h]
  have e3 : ∀ k i, i < k → p k i = 0 ∧ q k i = 0 := by
    intro k i h
    constructor <;> ext v u
    · exact (htri _ _ (Sigma.Lex.left _ _ h)).1
    · exact (htri _ _ (Sigma.Lex.left _ _ h)).2
  have e4 : ∀ i, A i = ∑ k, B k * p k i := by
    intro i
    ext r u
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) (hf ⟨i, u⟩)
    simp only [Matrix.sum_apply, Matrix.mul_apply, B, p, Matrix.of_apply]
    simpa [Fintype.sum_sigma, mul_comm] using this
  have e5 : ∀ i, B i = ∑ k, A k * q k i := by
    intro i
    ext r u
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) (hg' ⟨i, u⟩)
    simp only [Matrix.sum_apply, Matrix.mul_apply, B, q, Matrix.of_apply]
    simpa [Fintype.sum_sigma, mul_comm] using this
  refine ⟨B, p, q, e1, e2, e3, e4, e5, fun i => ?_⟩
  have hp : ∀ k, (B i)ᴴ * A k = p i k := by
    intro k
    rw [e4 k, Matrix.mul_sum, Finset.sum_eq_single i]
    · rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
    · intro l _ hl
      rw [← Matrix.mul_assoc, e2 i l hl.symm, Matrix.zero_mul]
    · simp
  have h : (B i)ᴴ * (∑ k, A k * q k i) = 1 := by rw [← e5, e1]
  rw [Matrix.mul_sum, Finset.sum_eq_single i] at h
  · rw [← h, ← Matrix.mul_assoc, hp]
  · intro l _ hl
    rw [← Matrix.mul_assoc, hp]
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [(e3 i l hl).1, Matrix.zero_mul]
    · rw [(e3 l i hl).2, Matrix.mul_zero]
  · simp

end GlobalTheory.LeviIso.BlockGS

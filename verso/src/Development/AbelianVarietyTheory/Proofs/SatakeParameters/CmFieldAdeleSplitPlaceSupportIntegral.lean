import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `TensorProduct.equivFinsuppOfBasisLeft_symm_apply b (TensorProduct.equivFinsuppOfBasisLeft b z)`. Rewrite `h` using `[LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]`. Conclude with `⟨_, _, h⟩`.
-/
theorem tensor_exists_decomp {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (z : M ⊗[K] N) :
    ∃ a c : N, z = b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c := by
  have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b
    (TensorProduct.equivFinsuppOfBasisLeft b z)
  rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
  exact ⟨_, _, h⟩

/- English proof (translation)
Establish `h'` using `congrArg (TensorProduct.equivFinsuppOfBasisLeft b) h`. Establish `h0` using `DFunLike.congr_fun h' 0`. Establish `h1` using `DFunLike.congr_fun h' 1`. Simplify using `[map_add, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at h0 h1`. Conclude with `⟨h0, h1⟩`.
-/
theorem tensor_decomp_eq_zero {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (a c : N)
    (h : b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c = 0) : a = 0 ∧ c = 0 := by
  have h' := congrArg (TensorProduct.equivFinsuppOfBasisLeft b) h
  have h0 := DFunLike.congr_fun h' 0
  have h1 := DFunLike.congr_fun h' 1
  simp [map_add, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at h0 h1
  exact ⟨h0, h1⟩

/- English proof (translation)
Introduce `L _ _ _ s e he hc z hz hp hq`. Establish `hne : (e : L) ≠ IsCMField.complexConj L (e : L)`. Introduce `h`. Rewrite `hc` using `[← h, he]`. Conclude with `lt_irrefl _ hc`.

Establish `hli : LinearIndependent (maximalRealSubfield L) ![(1 : L), (e : L)]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `a t h`. Establish `h'` using `congrArg (IsCMField.complexConj L) h`. Simplify using `only [Algebra.smul_def, map_add, map_mul, AlgEquiv.commutes, map_one, map_zero] at h h'`.

Establish `hd : algebraMap (maximalRealSubfield L) L t * ((e : L) - IsCMField.complexConj L (e : L)) = 0`. Take the linear combination `h - h'`. Establish `ht : t = 0`. Break down `mul_eq_zero.1 hd with h0 | h0` into its components or cases. Simplify using `using h0`.

Conclude with `absurd (sub_eq_zero.1 h0) hne`. Substitute `ht` using the available equality. Simplify using `using h`. Establish `hcard : Fintype.card (Fin 2) = Module.finrank (maximalRealSubfield L) L`. Rewrite using `[Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L]`.

Simplify using the standard rewrite rules. Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hb0 : b 0 = 1` using `by simp [b]`. Establish `hb1 : b 1 = (e : L)` using `by simp [b]`. Take `⟨A, B, hAB⟩` from `tensor_exists_decomp b z`.

Rewrite `hAB` using `[hb0, hb1]`. Establish `hoff : ∀ w, w ≠ s.v → A w = 0 ∧ B w = 0`. Introduce `w hw`. Establish `h` using `hz w hw`. Rewrite `h` using `[hAB]`.

Apply `tensor_decomp_eq_zero b` to reduce the goal to its premises. Rewrite using `[hb0, hb1]`. Simplify using `[ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at h`. Conclude with `h`. Establish `h1 : s.proj z = A s.v + s.i (e : L) * B s.v`.

Rewrite using `[hAB]`. Simplify using `[ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]`. Both sides reduce to the same expression. Establish `h2 : s.proj (ReciprocityTheory.Aut.conjAL L z) = A s.v + s.i (IsCMField.complexConj L (e : L)) * B s.v`. Rewrite using `[hAB]`.

Simplify using `[ReciprocityTheory.Aut.SplitPlace.proj, ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression. Establish `hu : Valued.v (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) = 1`. Rewrite using `[Valuation.map_sub_eq_of_lt_left _ (by rw [he]; exact hc), he]`. Establish `hBv : Valued.v (B s.v) ≤ 1`.

Establish `hm : (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) * B s.v = s.proj z - s.proj (ReciprocityTheory.Aut.conjAL L z)`. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv` using `congrArg Valued.v hm`. Rewrite `hv` using `[map_mul, hu, one_mul]`.

Rewrite using `[hv]`. Conclude with `Valuation.map_sub_le _ hp hq`. Establish `hAv : Valued.v (A s.v) ≤ 1`. Establish `hm : A s.v = s.proj z - s.i (e : L) * B s.v` using `by rw [h1]; ring`. Rewrite using `[hm]`.

Use `Valuation.map_sub_le _ hp ?_` and prove the remaining obligations. Rewrite using `[map_mul, he, one_mul]`. Conclude with `hBv`. Establish `hAi : ∀ w, A w ∈ w.adicCompletionIntegers (maximalRealSubfield L)`. Introduce `w`.

Break down `eq_or_ne w s.v with rfl | hw` into its components or cases. Conclude with `hAv`. Rewrite using `[(hoff w hw).1]`. Conclude with `zero_mem _`. Establish `hBi : ∀ w, B w ∈ w.adicCompletionIntegers (maximalRealSubfield L)`.

Introduce `w`. Break down `eq_or_ne w s.v with rfl | hw` into its components or cases. Conclude with `hBv`. Rewrite using `[(hoff w hw).2]`. Conclude with `zero_mem _`.

Establish `hsplit : ((e : L) ⊗ₜ[maximalRealSubfield L] B : ReciprocityTheory.Aut.AL L) = ((e : L) ⊗ₜ[maximalRealSubfield L] (1 : ReciprocityTheory.Aut.AFplus L)) * ((1 : L) ⊗ₜ[maximalRealSubfield L] B)`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[hAB, hsplit]`. Use `Subring.add_mem _ (Subring.subset_closure (Or.inr ⟨A, hAi, rfl⟩)) (Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨e, rfl⟩)) (Subring.subset_closure (Or.inr ⟨B, hBi, rfl⟩)))` and prove the remaining obligations.
-/
theorem mem_ALint_of_supported_at_split : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (e : 𝓞 L), Valued.v (s.i (e : L)) = 1 → Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 → ∀ z : ReciprocityTheory.Aut.AL L, (∀ w, w ≠ s.v → ReciprocityTheory.Aut.compAt L w z = 0) → Valued.v (s.proj z) ≤ 1 → Valued.v (s.proj (ReciprocityTheory.Aut.conjAL L z)) ≤ 1 → z ∈ ReciprocityTheory.Aut.ALint L := by
  intro L _ _ _ s e he hc z hz hp hq
  have hne : (e : L) ≠ IsCMField.complexConj L (e : L) := by
    intro h
    rw [← h, he] at hc
    exact lt_irrefl _ hc
  have hli : LinearIndependent (maximalRealSubfield L) ![(1 : L), (e : L)] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    have h' := congrArg (IsCMField.complexConj L) h
    simp only [Algebra.smul_def, map_add, map_mul, AlgEquiv.commutes, map_one, map_zero] at h h'
    have hd : algebraMap (maximalRealSubfield L) L t * ((e : L) - IsCMField.complexConj L (e : L)) = 0 := by
      linear_combination h - h'
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hd with h0 | h0
      · simpa using h0
      · exact absurd (sub_eq_zero.1 h0) hne
    subst ht
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank (maximalRealSubfield L) L := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L]; simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = (e : L) := by simp [b]
  obtain ⟨A, B, hAB⟩ := tensor_exists_decomp b z
  rw [hb0, hb1] at hAB
  have hoff : ∀ w, w ≠ s.v → A w = 0 ∧ B w = 0 := by
    intro w hw
    have h := hz w hw
    rw [hAB] at h
    apply tensor_decomp_eq_zero b
    rw [hb0, hb1]
    simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at h
    exact h
  have h1 : s.proj z = A s.v + s.i (e : L) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]
    rfl
  have h2 : s.proj (ReciprocityTheory.Aut.conjAL L z) =
      A s.v + s.i (IsCMField.complexConj L (e : L)) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  have hu : Valued.v (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_left _ (by rw [he]; exact hc), he]
  have hBv : Valued.v (B s.v) ≤ 1 := by
    have hm : (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) * B s.v =
        s.proj z - s.proj (ReciprocityTheory.Aut.conjAL L z) := by
      rw [h1, h2]; ring
    have hv := congrArg Valued.v hm
    rw [map_mul, hu, one_mul] at hv
    rw [hv]
    exact Valuation.map_sub_le _ hp hq
  have hAv : Valued.v (A s.v) ≤ 1 := by
    have hm : A s.v = s.proj z - s.i (e : L) * B s.v := by rw [h1]; ring
    rw [hm]
    refine Valuation.map_sub_le _ hp ?_
    rw [map_mul, he, one_mul]
    exact hBv
  have hAi : ∀ w, A w ∈ w.adicCompletionIntegers (maximalRealSubfield L) := by
    intro w
    rcases eq_or_ne w s.v with rfl | hw
    · exact hAv
    · rw [(hoff w hw).1]; exact zero_mem _
  have hBi : ∀ w, B w ∈ w.adicCompletionIntegers (maximalRealSubfield L) := by
    intro w
    rcases eq_or_ne w s.v with rfl | hw
    · exact hBv
    · rw [(hoff w hw).2]; exact zero_mem _
  have hsplit : ((e : L) ⊗ₜ[maximalRealSubfield L] B : ReciprocityTheory.Aut.AL L) =
      ((e : L) ⊗ₜ[maximalRealSubfield L] (1 : ReciprocityTheory.Aut.AFplus L)) *
        ((1 : L) ⊗ₜ[maximalRealSubfield L] B) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [hAB, hsplit]
  refine Subring.add_mem _ (Subring.subset_closure (Or.inr ⟨A, hAi, rfl⟩))
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨e, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨B, hBi, rfl⟩)))

end GlobalTheory

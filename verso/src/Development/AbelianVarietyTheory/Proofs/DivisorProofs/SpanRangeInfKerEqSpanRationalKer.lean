import Mathlib

open Module

namespace GlobalTheory

/- English proof (translation)
Establish `hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → K)`. Use extensionality with `l`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [hx]`. Rewrite using `[map_sum]`.

Simplify using `only [LinearMap.map_smulₛₗ]`.
-/
theorem semilinear_pi_eq_sum_single {K : Type} [Field K] (σ : K →+* ℂ) {W : Type} [AddCommGroup W]
    [Module ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ k, σ (x k) • j (Pi.single k 1) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [LinearMap.map_smulₛₗ]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `w ⟨hw, hw0⟩`. Establish `hle : Submodule.span ℂ (Set.range j) ≤ Submodule.span ℂ (Set.range fun k => j (Pi.single k 1))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[semilinear_pi_eq_sum_single σ j x]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hw)`. Establish `h0 : f (∑ k, c k • j (Pi.single k 1)) = 0` using `hw0`. Establish `h1 : ∑ l, (∑ k, σ (M l k) * c k) • j' (Pi.single l 1) = 0`.

Rewrite using `[← h0, map_sum]`. Simplify using `only [map_smul, hf, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[semilinear_pi_eq_sum_single σ j' (M.mulVec _), Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Simplify using the standard rewrite rules. Establish `h2 : ∀ l, ∑ k, σ (M l k) * c k = 0` using `Fintype.linearIndependent_iff.1 hli _ h1`. Use `letI : Algebra K ℂ := σ.toAlgebra`.

Set `b` to `Basis.ofVectorSpace K ℂ`. Set `s` to `Finset.univ.biUnion fun k => (b.repr (c k)).support`. Establish `hc : ∀ k, c k = ∑ i ∈ s, σ (b.repr (c k) i) * b i`. Introduce `k`. Establish `h3` using `b.linearCombination_repr (c k)`.

Rewrite `h3` using `[Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (s := s) (Finset.subset_biUnion_of_mem (fun k => (b.repr (c k)).support) (Finset.mem_univ k)) _ (by simp)]`. Conclude with `h3.symm`. Establish `hw' : ∑ k, c k • j (Pi.single k 1) = ∑ i ∈ s, b i • j (fun k => b.repr (c k) i)`. Establish `h5 : ∀ i, b i • j (fun k => b.repr (c k) i) = ∑ k, b i • σ (b.repr (c k) i) • j (Pi.single k 1)` using `fun i => by`. Rewrite using `[semilinear_pi_eq_sum_single σ j (fun k => b.repr (c k) i), Finset.smul_sum]`.

Rewrite using `[Finset.sum_congr rfl fun i _ => h5 i, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [hc k, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`.

Rewrite using `[hw']`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)` and prove the remaining obligations. Use extensionality with `l`. Establish `h4 : b.repr (∑ k, M l k • c k) i = 0`. Establish `: ∑ k, M l k • c k = 0` using `h2 l`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite `h4` using `[map_sum, Finsupp.finset_sum_apply]`. Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h4`. Conclude with `h4`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `⟨Submodule.subset_span ⟨x, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hx' : M.mulVec x = 0` using `hx`. Express the relevant statement in the definitionally equal form `f (j x) = 0`.

Rewrite using `[hf, hx', map_zero]`.
-/
theorem span_range_inf_ker_eq_span_rational_ker {K : Type} [Field K] (σ : K →+* ℂ) {W E : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E] {n d : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (j' : (Fin d → K) →ₛₗ[σ] E) (f : W →ₗ[ℂ] E)
    (M : Matrix (Fin d) (Fin n) K)
    (hli : LinearIndependent ℂ (fun l => j' (Pi.single l 1)))
    (hf : ∀ x, f (j x) = j' (M.mulVec x)) :
    Submodule.span ℂ (Set.range j) ⊓ LinearMap.ker f
      = Submodule.span ℂ (j '' {x | M.mulVec x = 0}) := by
  classical
  apply le_antisymm
  · rintro w ⟨hw, hw0⟩
    have hle : Submodule.span ℂ (Set.range j)
        ≤ Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [semilinear_pi_eq_sum_single σ j x]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hw)
    have h0 : f (∑ k, c k • j (Pi.single k 1)) = 0 := hw0
    have h1 : ∑ l, (∑ k, σ (M l k) * c k) • j' (Pi.single l 1) = 0 := by
      rw [← h0, map_sum]
      simp only [map_smul, hf, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [semilinear_pi_eq_sum_single σ j' (M.mulVec _), Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, mul_comm]
      simp
    have h2 : ∀ l, ∑ k, σ (M l k) * c k = 0 := Fintype.linearIndependent_iff.1 hli _ h1
    letI : Algebra K ℂ := σ.toAlgebra
    let b := Basis.ofVectorSpace K ℂ
    let s := Finset.univ.biUnion fun k => (b.repr (c k)).support
    have hc : ∀ k, c k = ∑ i ∈ s, σ (b.repr (c k) i) * b i := by
      intro k
      have h3 := b.linearCombination_repr (c k)
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (s := s)
          (Finset.subset_biUnion_of_mem (fun k => (b.repr (c k)).support) (Finset.mem_univ k))
          _ (by simp)] at h3
      exact h3.symm
    have hw' : ∑ k, c k • j (Pi.single k 1) = ∑ i ∈ s, b i • j (fun k => b.repr (c k) i) := by
      have h5 : ∀ i, b i • j (fun k => b.repr (c k) i)
          = ∑ k, b i • σ (b.repr (c k) i) • j (Pi.single k 1) := fun i => by
        rw [semilinear_pi_eq_sum_single σ j (fun k => b.repr (c k) i), Finset.smul_sum]
      rw [Finset.sum_congr rfl fun i _ => h5 i, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [hc k, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm]
    rw [hw']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    ext l
    have h4 : b.repr (∑ k, M l k • c k) i = 0 := by
      have : ∑ k, M l k • c k = 0 := h2 l
      rw [this]; simp
    rw [map_sum, Finsupp.finset_sum_apply] at h4
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h4
    exact h4
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Submodule.subset_span ⟨x, rfl⟩, ?_⟩
    have hx' : M.mulVec x = 0 := hx
    change f (j x) = 0
    rw [hf, hx', map_zero]

end GlobalTheory

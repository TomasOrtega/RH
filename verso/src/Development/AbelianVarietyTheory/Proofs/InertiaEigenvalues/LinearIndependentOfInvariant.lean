import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Per

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. It suffices to establish `H : ∀ n : ℕ, ∀ c : ι → E, (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ n → ∑ i, c i • v i = 0 → ∀ i, c i = 0 by`. Conclude with `fun c hc => H _ c le_rfl hc`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `c hcard _ i`. Assume the negation of the conclusion as `h`. Establish `hpos : 0 < (Finset.univ.filter (fun i => c i ≠ 0)).card` using `Finset.card_pos.mpr ⟨i, by simp [h]⟩`. Use linear arithmetic over natural numbers and integers.

Consider the case `succ n ih`. Introduce `c hcard hsum`. Assume the negation of the conclusion as `hne`. Take `⟨i0, hi0⟩` from `not_forall.mp hne`. Take `⟨c', hc'⟩ : ∃ c' : ι → E, c' = fun i => (c i0)⁻¹ * c i` from `⟨_, rfl⟩`.

Establish `hc'sum : ∑ i, c' i • v i = 0`. Simplify using `only [hc', mul_smul, ← Finset.smul_sum, hsum, smul_zero]`. Establish `hc'i0 : c' i0 = 1`. Rewrite using `[hc']`. Conclude with `inv_mul_cancel₀ hi0`.

Establish `hsupp : Finset.univ.filter (fun i => c' i ≠ 0) = Finset.univ.filter (fun i => c i ≠ 0)`. Use extensionality with `i`. Simplify using `[hc', hi0]`. Establish `hfix : ∀ g i, σ g (c' i) = c' i`. Introduce `g`.

Take `⟨d, hd⟩ : ∃ d : ι → E, d = fun i => σ g (c' i) - c' i` from `⟨_, rfl⟩`. Establish `h1 : ∑ i, σ g (c' i) • v i = 0`. Establish `h2` using `congrArg (ρ g) hc'sum`. Rewrite `h2` using `[map_sum, map_zero]`. Simplify `h2` using `[hρ, hv]`.

Establish `hdsum : ∑ i, d i • v i = 0`. Simplify using `only [hd, sub_smul, Finset.sum_sub_distrib, h1, hc'sum, sub_zero]`. Establish `hsub : Finset.univ.filter (fun i => d i ≠ 0) ⊆ (Finset.univ.filter (fun i => c' i ≠ 0)).erase i0`. Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hi ⊢`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hi` to reduce the goal to its premises. Simplify using `[hd, hc'i0]`. Introduce `h0`.

Apply `hi` to reduce the goal to its premises. Simplify using `[hd, h0]`. Establish `hmem : i0 ∈ Finset.univ.filter (fun i => c' i ≠ 0)` using `by simp [hc'i0]`. Establish `hdcard : (Finset.univ.filter (fun i => d i ≠ 0)).card ≤ n`. Establish `h3` using `Finset.card_le_card hsub`.

Rewrite `h3` using `[Finset.card_erase_of_mem hmem, hsupp]`. Use linear arithmetic over natural numbers and integers. Introduce `i`. Establish `h5` using `ih d hdcard hdsum i`. Rewrite `h5` using `[hd]`.

Conclude with `sub_eq_zero.mp h5`. Establish `h4` using `hind c' hfix hc'sum i0`. Rewrite `h4` using `[hc'i0]`. Conclude with `one_ne_zero h4`.
-/
theorem linearIndependent_of_invariant (G E M ι : Type) [Field E] [AddCommGroup M] [Module E M]
    [Fintype ι] (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : ι → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : ι → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0) :
    LinearIndependent E v := by
  classical
  rw [Fintype.linearIndependent_iff]

  suffices H : ∀ n : ℕ, ∀ c : ι → E,
      (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ n → ∑ i, c i • v i = 0 → ∀ i, c i = 0 by
    exact fun c hc => H _ c le_rfl hc
  intro n
  induction n with
  | zero =>
    intro c hcard _ i
    by_contra h
    have hpos : 0 < (Finset.univ.filter (fun i => c i ≠ 0)).card :=
      Finset.card_pos.mpr ⟨i, by simp [h]⟩
    omega
  | succ n ih =>
    intro c hcard hsum
    by_contra hne
    obtain ⟨i0, hi0⟩ := not_forall.mp hne

    obtain ⟨c', hc'⟩ : ∃ c' : ι → E, c' = fun i => (c i0)⁻¹ * c i := ⟨_, rfl⟩
    have hc'sum : ∑ i, c' i • v i = 0 := by
      simp only [hc', mul_smul, ← Finset.smul_sum, hsum, smul_zero]
    have hc'i0 : c' i0 = 1 := by
      rw [hc']
      exact inv_mul_cancel₀ hi0
    have hsupp : Finset.univ.filter (fun i => c' i ≠ 0) = Finset.univ.filter (fun i => c i ≠ 0) := by
      ext i
      simp [hc', hi0]

    have hfix : ∀ g i, σ g (c' i) = c' i := by
      intro g
      obtain ⟨d, hd⟩ : ∃ d : ι → E, d = fun i => σ g (c' i) - c' i := ⟨_, rfl⟩
      have h1 : ∑ i, σ g (c' i) • v i = 0 := by
        have h2 := congrArg (ρ g) hc'sum
        rw [map_sum, map_zero] at h2
        simpa [hρ, hv] using h2
      have hdsum : ∑ i, d i • v i = 0 := by
        simp only [hd, sub_smul, Finset.sum_sub_distrib, h1, hc'sum, sub_zero]
      have hsub : Finset.univ.filter (fun i => d i ≠ 0) ⊆
          (Finset.univ.filter (fun i => c' i ≠ 0)).erase i0 := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hi ⊢
        refine ⟨?_, ?_⟩
        · rintro rfl
          apply hi
          simp [hd, hc'i0]
        · intro h0
          apply hi
          simp [hd, h0]
      have hmem : i0 ∈ Finset.univ.filter (fun i => c' i ≠ 0) := by simp [hc'i0]
      have hdcard : (Finset.univ.filter (fun i => d i ≠ 0)).card ≤ n := by
        have h3 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hmem, hsupp] at h3
        omega
      intro i
      have h5 := ih d hdcard hdsum i
      rw [hd] at h5
      exact sub_eq_zero.mp h5
    have h4 := hind c' hfix hc'sum i0
    rw [hc'i0] at h4
    exact one_ne_zero h4

end GlobalTheory.Per

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOpCommLiB
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Finset

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hx' : x ∉ Subalgebra.toSubmodule S` using `hx`. Take `⟨f, hf1, hf2⟩` from `Submodule.exists_le_ker_of_notMem hx'`. Conclude with `hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))`.
-/
theorem mem_subalgebra_of_dual {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (x : A)
    (h : ∀ f : A →ₗ[ℂ] ℂ, (∀ z ∈ S, f z = 0) → f x = 0) : x ∈ S := by
  by_contra hx
  have hx' : x ∉ Subalgebra.toSubmodule S := hx
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem hx'
  exact hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))

/- English proof (translation)
Take `⟨Rm, hR⟩` from `_root_.GlobalTheory.qdet_top_three_orders A n E`. Distinguish the cases in `hn : 2 ≤ n`. Use `swap`. Establish `hn' : n = 0 ∨ n = 1` using `by omega`. Break down `hn' with rfl | rfl` into its components or cases.

Simplify using `[Formalism.REAL.Cas]`. Establish `h0` using `hcap 0`. Rewrite `h0` using `[hR]`. Establish `h1 : E 0 0 ∈ S`. Simplify `h0` using `[Finset.filter_singleton]`.

Establish `: Formalism.REAL.Cas E = E 0 0 * E 0 0` using `by simp [Formalism.REAL.Cas]`. Rewrite using `[this]`. Conclude with `Subalgebra.mul_mem _ h1 h1`. Use `set ρ : Fin n → ℂ := fun l => ((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) with hρ`. Establish `hρ0 : ∑ l, ρ l = 0`.

Establish `h1 : ∑ l, ρ l = ∑ l, ρ (Fin.rev l)` using `(Equiv.sum_comp Fin.revPerm ρ).symm`. Establish `h2 : ∑ l, ρ (Fin.rev l) = - ∑ l, ρ l`. Rewrite using `[← sum_neg_distrib]`. Use `sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `l.2` as an intermediate fact.

Simplify using `only [hρ, Fin.val_rev]`. Rewrite using `[Nat.cast_sub (by omega)]; push_cast; ring`. Take the linear combination `(h1.trans h2) / 2`. Establish `core` using `fun (f : A →ₗ[ℂ] ℂ) (hf : ∀ z ∈ S, f z = 0) => scalar_core n hn ρ (fun _ => 0) (fun i => f (E i i)) (fun i j => f (E i i * E j j - E j i * E i j)) (fun d => f (Rm d)) (f 1) (((n : ℂ) - 1) / 2) (fun Y => by`. Establish `h1` using `hf _ (hcap Y)`.

Rewrite `h1` using `[hR]`. Establish `e : f 1 = 0` using `hf 1 (Subalgebra.one_mem _)`. Simplify using `only [map_add, map_sum, map_smul, smul_eq_mul, add_sub_assoc] at h1`. Simplify using `only [e, mul_zero] at h1 ⊢`. Conclude with `h1)`.

Establish `hT : ∑ i, E i i ∈ S`. Use `mem_subalgebra_of_dual S _ fun f hf => ?_` and prove the remaining obligations. Establish `e : f 1 = 0` using `hf 1 (Subalgebra.one_mem _)`. Use `(core f hf).1` as an intermediate fact. Rewrite `this` using `[hρ0, e]`.

Simplify using `only [map_sum]`. Take the linear combination `this`. Establish `hW : (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j) - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i ∈ S`. Use `mem_subalgebra_of_dual S _ fun f hf => ?_` and prove the remaining obligations. Establish `e : f 1 = 0` using `hf 1 (Subalgebra.one_mem _)`.

Establish `h2` using `(core f hf).2`. Rewrite `h2` using `[e]`. Simplify using `only [sum_erase_eq_sub (mem_univ _), hρ0] at h2`. Simplify using `only [map_sub f, map_sum, map_smul, smul_eq_mul]`. Establish `h5 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) * f (E i i) = - (2 * ∑ i, (0 - ρ i) * f (E i i))`.

Rewrite using `[mul_sum, ← sum_neg_distrib]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [hρ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h5]`.

Simplify using `only [map_sub f] at h2`. Take the linear combination `h2`. Establish `h3` using `sq_sub_cas E hE`. Establish `: Formalism.REAL.Cas E = (∑ i, E i i) * (∑ i, E i i) - ((2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j) - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i)`. Rewrite using `[← h3]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hT hT) hW`.
-/
theorem cas_mem_of_qdet_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (n : ℕ)
    (E : Fin n → Fin n → A) (hE : Formalism.REAL.GlRel E)
    (hcap : ∀ Y : ℂ, Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) ∈ S) : Formalism.REAL.Cas E ∈ S := by
  obtain ⟨Rm, hR⟩ := _root_.GlobalTheory.qdet_top_three_orders A n E
  by_cases hn : 2 ≤ n
  swap
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simp [Formalism.REAL.Cas]
    · have h0 := hcap 0
      rw [hR] at h0
      have h1 : E 0 0 ∈ S := by
        simpa [Finset.filter_singleton] using h0
      have : Formalism.REAL.Cas E = E 0 0 * E 0 0 := by simp [Formalism.REAL.Cas]
      rw [this]
      exact Subalgebra.mul_mem _ h1 h1
  set ρ : Fin n → ℂ := fun l => ((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) with hρ
  have hρ0 : ∑ l, ρ l = 0 := by
    have h1 : ∑ l, ρ l = ∑ l, ρ (Fin.rev l) := (Equiv.sum_comp Fin.revPerm ρ).symm
    have h2 : ∑ l, ρ (Fin.rev l) = - ∑ l, ρ l := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      have := l.2
      simp only [hρ, Fin.val_rev]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linear_combination (h1.trans h2) / 2
  have core := fun (f : A →ₗ[ℂ] ℂ) (hf : ∀ z ∈ S, f z = 0) =>
    scalar_core n hn ρ (fun _ => 0) (fun i => f (E i i))
      (fun i j => f (E i i * E j j - E j i * E i j)) (fun d => f (Rm d)) (f 1)
      (((n : ℂ) - 1) / 2)
      (fun Y => by
        have h1 := hf _ (hcap Y)
        rw [hR] at h1
        have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
        simp only [map_add, map_sum, map_smul, smul_eq_mul, add_sub_assoc] at h1
        simp only [e, mul_zero] at h1 ⊢
        exact h1)
  have hT : ∑ i, E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have := (core f hf).1
    rw [hρ0, e] at this
    simp only [map_sum]
    linear_combination this
  have hW : (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have h2 := (core f hf).2
    rw [e] at h2
    simp only [sum_erase_eq_sub (mem_univ _), hρ0] at h2
    simp only [map_sub f, map_sum, map_smul, smul_eq_mul]
    have h5 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) * f (E i i)
        = - (2 * ∑ i, (0 - ρ i) * f (E i i)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [hρ]; ring
    rw [h5]
    simp only [map_sub f] at h2
    linear_combination h2
  have h3 := sq_sub_cas E hE
  have : Formalism.REAL.Cas E = (∑ i, E i i) * (∑ i, E i i)
      - ((2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i) := by
    rw [← h3]; abel
  rw [this]
  exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hT hT) hW

/- English proof (translation)
Introduce `F _ _ _ n τ`. Establish `hcap : ∀ Y : ℂ, cap (a` using `n) τ Y ∈ Zalg F n := fun Y => Algebra.subset_adjoin (show cap (a := n) τ Y ∈ {z | ∃ τ u, z = cap τ u} from ⟨τ, Y, rfl⟩)`. Conclude with `cas_mem_of_qdet_mem (Zalg F n) n (Eop τ) (glRel_Eop τ) hcap`.
-/
theorem cas_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  intro F _ _ _ n τ
  have hcap : ∀ Y : ℂ, cap (a := n) τ Y ∈ Zalg F n := fun Y =>
    Algebra.subset_adjoin (show cap (a := n) τ Y ∈ {z | ∃ τ u, z = cap τ u} from ⟨τ, Y, rfl⟩)
  exact cas_mem_of_qdet_mem (Zalg F n) n (Eop τ) (glRel_Eop τ) hcap

end GlobalTheory.CompanionTheory.Inh.CapelliCasimir

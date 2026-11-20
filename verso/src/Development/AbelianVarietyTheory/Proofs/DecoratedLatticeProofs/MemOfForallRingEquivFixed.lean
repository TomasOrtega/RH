import Mathlib
import Formalism.PadicSubsetSums.StableGradedCounts.FixedByAutomorphismInField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivAddOne

open Polynomial

namespace GlobalTheory.FixedRoots

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one`. Consider the case `exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one`. Consider the case `(apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one ..)`.
-/
theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental k c) :
    ∃ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) ∧ σ c = c + 1 := by
  first
  | exact @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | (apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one ..)

/- English proof (translation)
Distinguish the cases in `hc : Transcendental k c`. It suffices to derive a contradiction. Take `⟨σ, hσk, hσc⟩` from `exists_ringEquiv_add_one k c hc`. Use `hfix σ hσk` as an intermediate fact. Rewrite `this` using `[hσc]`.

Simplify using `at this`. Establish `hcA : IsAlgebraic k c` using `by simpa [Transcendental] using hc`. Establish `hzA : c ∈ algebraicClosure k Ω` using `(mem_algebraicClosure_iff).2 hcA`. Establish `: IsGalois k (algebraicClosure k Ω)` using `inferInstance`. Take `⟨r, hr⟩` from `(InfiniteGalois.mem_range_algebraMap_iff_fixed (k := k) (K := algebraicClosure k Ω) ⟨c, hzA⟩).2 (by`.

Introduce `σ₀`. Take `⟨σ, hσ⟩` from `Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending σ₀`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hσ]`. Conclude with `hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩))`.

Establish `: ((r : k) : Ω) = c` using `congrArg Subtype.val hr`. Rewrite using `[← this]`. Conclude with `r.2`.
-/
theorem mem_of_forall_ringEquiv_fixed {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (k : Subfield Ω) (c : Ω) (hfix : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → σ c = c) : c ∈ k := by
  by_cases hc : Transcendental k c
  · exfalso
    obtain ⟨σ, hσk, hσc⟩ := exists_ringEquiv_add_one k c hc
    have := hfix σ hσk
    rw [hσc] at this
    simp at this
  · have hcA : IsAlgebraic k c := by simpa [Transcendental] using hc
    have hzA : c ∈ algebraicClosure k Ω := (mem_algebraicClosure_iff).2 hcA
    have : IsGalois k (algebraicClosure k Ω) := inferInstance
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := k) (K := algebraicClosure k Ω) ⟨c, hzA⟩).2 (by
        intro σ₀
        obtain ⟨σ, hσ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending σ₀
        apply Subtype.ext
        rw [← hσ]
        exact hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩))
    have : ((r : k) : Ω) = c := congrArg Subtype.val hr
    rw [← this]
    exact r.2

/- English proof (translation)
Apply `mem_of_forall_ringEquiv_fixed k` to reduce the goal to its premises. Introduce `σ hσ`. Establish `hmap : S.map σ.toEquiv.toEmbedding = S`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `y hy`.

Take `⟨x, hx, rfl⟩` from `Finset.mem_map.1 hy`. Conclude with `hS σ hσ x hx`. Simplify using the standard rewrite rules. Establish `hP : (∏ x ∈ S, (X - C x)).map (σ : Ω →+* Ω) = ∏ x ∈ S, (X - C x)`. Rewrite using `[Polynomial.map_prod]`.

Use `conv_rhs => rw [← hmap]`. Rewrite using `[Finset.prod_map]`. Simplify using the standard rewrite rules. Use `congrArg (fun P => Polynomial.coeff P n) hP` as an intermediate fact. Simplify `this` using `[Polynomial.coeff_map]`.
-/
theorem coeff_prod_mem {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (k : Subfield Ω)
    (S : Finset Ω) (hS : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → ∀ x ∈ S, σ x ∈ S) (n : ℕ) :
    (∏ x ∈ S, (X - C x)).coeff n ∈ k := by
  apply mem_of_forall_ringEquiv_fixed k
  intro σ hσ
  have hmap : S.map σ.toEquiv.toEmbedding = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
      exact hS σ hσ x hx
    · simp
  have hP : (∏ x ∈ S, (X - C x)).map (σ : Ω →+* Ω) = ∏ x ∈ S, (X - C x) := by
    rw [Polynomial.map_prod]
    conv_rhs => rw [← hmap]
    rw [Finset.prod_map]
    simp
  have := congrArg (fun P => Polynomial.coeff P n) hP
  simpa [Polynomial.coeff_map] using this

/- English proof (translation)
Introduce `_ _ _ _ k S hS n` and use `coeff_prod_mem k S hS n`.
-/
theorem main : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (k : Subfield Ω) (S : Finset Ω),
    (∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → ∀ x ∈ S, σ x ∈ S) → ∀ n,
      (∏ x ∈ S, (X - C x)).coeff n ∈ k :=
  fun _ _ _ _ k S hS n => coeff_prod_mem k S hS n

end GlobalTheory.FixedRoots

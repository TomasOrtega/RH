import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIntegral
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.LatticeQuotBound

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem`. Consider the case `exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem`. Consider the case `(apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem ..)`.
-/
theorem exists_pow_smul_mem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (hT : IsLatticeIn T)
    (ϖ : O) (hϖ : Irreducible ϖ) (v : V) : ∃ m : ℕ, ϖ ^ m • v ∈ T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerMultiple.exists_pow_smul_mem ..)

/- English proof (translation)
Introduce `O _ _ _ V _ _ _ _ _ _ X _ _ T hT hTo ϖ hϖ c hc`. Establish `hopen : ∀ m : ℕ, IsOpen {q : V ⧸ T | ϖ ^ m • q = 0}`. Introduce `m`. Establish `h : IsOpen ((Submodule.Quotient.mk : V → V ⧸ T) ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0})`. Rewrite using `[isOpen_iff_forall_mem_open]`.

Introduce `v hv`. Use `⟨(fun t => v + t) '' (T : Set V), ?_, isOpenMap_add_left v _ hTo, ⟨0, T.zero_mem, add_zero v⟩⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq] at hv ⊢`. Rewrite using `[Submodule.Quotient.mk_add, smul_add, hv, zero_add, (Submodule.Quotient.mk_eq_zero T).2 ht, smul_zero]`.

Conclude with `isOpen_coinduced.mpr h`. Establish `hcover : ∀ x, ∃ m : ℕ, x ∈ c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0}`. Introduce `x`. Take `⟨v, hv⟩` from `Submodule.Quotient.mk_surjective T (c x)`. Take `⟨m, hm⟩` from `exists_pow_smul_mem T hT ϖ hϖ v`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq]`. Rewrite using `[← hv, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero T).2 hm]`. Establish `hmono : Monotone (fun m : ℕ => c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0})`. Introduce `a b hab x hx`.

Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢`. Rewrite using `[← Nat.add_sub_cancel' hab, pow_add, mul_comm, mul_smul, hx, smul_zero]`. Take `⟨m, hm⟩` from `isCompact_univ.elim_directed_cover _ (fun m => (hopen m).preimage hc) (fun x _ => Set.mem_iUnion.2 (hcover x)) hmono.directed_le`. Conclude with `⟨m, fun x => hm (Set.mem_univ x)⟩`.
-/
theorem pow_smul_eq_zero_of_compact : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V] {X : Type} [TopologicalSpace X] [CompactSpace X] (T : Submodule O V), IsLatticeIn T → IsOpen (T : Set V) → ∀ ϖ : O, Irreducible ϖ → ∀ c : X → V ⧸ T, Continuous c → ∃ r : ℕ, ∀ x, ϖ ^ r • c x = 0 := by
  intro O _ _ _ V _ _ _ _ _ _ X _ _ T hT hTo ϖ hϖ c hc
  have hopen : ∀ m : ℕ, IsOpen {q : V ⧸ T | ϖ ^ m • q = 0} := by
    intro m
    have h : IsOpen ((Submodule.Quotient.mk : V → V ⧸ T) ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0}) := by
      rw [isOpen_iff_forall_mem_open]
      intro v hv
      refine ⟨(fun t => v + t) '' (T : Set V), ?_, isOpenMap_add_left v _ hTo,
        ⟨0, T.zero_mem, add_zero v⟩⟩
      rintro _ ⟨t, ht, rfl⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv ⊢
      rw [Submodule.Quotient.mk_add, smul_add, hv, zero_add,
        (Submodule.Quotient.mk_eq_zero T).2 ht, smul_zero]
    exact isOpen_coinduced.mpr h
  have hcover : ∀ x, ∃ m : ℕ, x ∈ c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0} := by
    intro x
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective T (c x)
    obtain ⟨m, hm⟩ := exists_pow_smul_mem T hT ϖ hϖ v
    refine ⟨m, ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hv, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero T).2 hm]
  have hmono : Monotone (fun m : ℕ => c ⁻¹' {q : V ⧸ T | ϖ ^ m • q = 0}) := by
    intro a b hab x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    rw [← Nat.add_sub_cancel' hab, pow_add, mul_comm, mul_smul, hx, smul_zero]
  obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover _ (fun m => (hopen m).preimage hc)
    (fun x _ => Set.mem_iUnion.2 (hcover x)) hmono.directed_le
  exact ⟨m, fun x => hm (Set.mem_univ x)⟩

end GlobalTheory.LatticeQuotBound

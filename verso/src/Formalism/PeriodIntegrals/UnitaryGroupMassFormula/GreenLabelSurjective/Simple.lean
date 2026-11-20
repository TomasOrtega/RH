import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent

open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

namespace PI.GreenLabelSurjWork

variable {G : Type} [Group G] [Fintype G]

def repHomLin (A B : Rep ℂ G) : (A ⟶ B) ≃ₗ[ℂ] A.ρ.IntertwiningMap B.ρ :=
  { Rep.homEquiv with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/- English proof (translation)
Use `haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩`. Rewrite using `[FDRep.simple_iff_end_is_rank_one]`. Rewrite using `[← (FDRep.forget₂HomLinearEquiv _ _).finrank_eq, (repHomLin _ _).finrank_eq]`. Conclude with `Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := σ)`.
-/
theorem simple_of_irr {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [σ.IsIrreducible] : Simple (FDRep.of σ) := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  rw [FDRep.simple_iff_end_is_rank_one]
  rw [← (FDRep.forget₂HomLinearEquiv _ _).finrank_eq, (repHomLin _ _).finrank_eq]
  exact Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := σ)

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Apply `CategoryTheory.id_nonzero V` to reduce the goal to its premises. Use `first`. Consider the case `(ext x; exact Subsingleton.elim _ _)`.

Consider the case `(apply Action.Hom.ext; ext x; exact Subsingleton.elim _ _)`. Consider the case `(ext; exact Subsingleton.elim _ _)`.
-/
theorem nontrivial_of_simple (V : FDRep ℂ G) (h : Simple V) : Nontrivial V := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  apply CategoryTheory.id_nonzero V
  first
    | (ext x; exact Subsingleton.elim _ _)
    | (apply Action.Hom.ext; ext x; exact Subsingleton.elim _ _)
    | (ext; exact Subsingleton.elim _ _)

/- English proof (translation)
Establish `hex : ∃ n, ∃ A : Subrepresentation ρ, A.toSubmodule ≠ ⊥ ∧ Module.finrank ℂ A.toSubmodule = n` using `⟨_, ⊤, show (⊤ : Submodule ℂ V) ≠ ⊥ from top_ne_bot, rfl⟩`. Take `⟨A, hA0, hAn⟩` from `Nat.find_spec hex`. Establish `hirr : (A.toRepresentation).IsIrreducible`. Use `{ exists_pair_ne := ⟨⊥, ⊤, fun h => hA0 ?_⟩, eq_bot_or_eq_top := fun U => ?_ }` and prove the remaining obligations. Establish `h1` using `congrArg Subrepresentation.toSubmodule h`.

Rewrite using `[Submodule.eq_bot_iff]`. Introduce `x hx`. Establish `h2 : (⟨x, hx⟩ : A.toSubmodule) ∈ (⊥ : Subrepresentation A.toRepresentation).toSubmodule`. Rewrite using `[h1]`. Conclude with `Submodule.mem_top`.

Establish `h3 : (⟨x, hx⟩ : A.toSubmodule) = 0` using `(Submodule.mem_bot ℂ).mp h2`. Conclude with `congrArg Subtype.val h3`. Distinguish the cases in `hU : U.toSubmodule = ⊥`. Use `left`. Conclude with `Subrepresentation.toSubmodule_injective hU`.

Use `right`. Set `U' : Subrepresentation ρ` to `⟨U.toSubmodule.map A.toSubmodule.subtype, by`. Introduce `g v hv`. Take `⟨u, hu, rfl⟩` from `Submodule.mem_map.mp hv`. Conclude with `Submodule.mem_map.mpr ⟨A.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩⟩`.

Establish `hfr : Module.finrank ℂ U'.toSubmodule = Module.finrank ℂ U.toSubmodule` using `Submodule.finrank_map_subtype_eq _ _`. Establish `hU0 : U'.toSubmodule ≠ ⊥`. Introduce `h`. Establish `: Module.finrank ℂ U'.toSubmodule = 0` using `by rw [h]; exact finrank_bot ℂ V`. Rewrite `this` using `[hfr, Submodule.finrank_eq_zero]`.

Conclude with `hU this`. Establish `hmin` using `Nat.find_min' hex ⟨U', hU0, rfl⟩`. Establish `hle : Module.finrank ℂ U.toSubmodule ≤ Module.finrank ℂ A.toSubmodule` using `Submodule.finrank_le _`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Conclude with `Submodule.eq_top_of_finrank_eq (by omega)`.

Use `⟨FDRep.of A.toRepresentation, simple_of_irr _, A.toSubmodule.subtype, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Use extensionality with `v`. Both sides reduce to the same expression. Introduce `h`.

Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hA0`. Conclude with `hv0 (congrArg (fun φ : A.toSubmodule →ₗ[ℂ] V => φ ⟨v, hv⟩) h)`.
-/
theorem exists_simple_constituent {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ G V) : ∃ τ : FDRep ℂ G, Simple τ ∧ IsConstituent τ ρ := by
  classical
  have hex : ∃ n, ∃ A : Subrepresentation ρ, A.toSubmodule ≠ ⊥ ∧
      Module.finrank ℂ A.toSubmodule = n :=
    ⟨_, ⊤, show (⊤ : Submodule ℂ V) ≠ ⊥ from top_ne_bot, rfl⟩
  obtain ⟨A, hA0, hAn⟩ := Nat.find_spec hex
  have hirr : (A.toRepresentation).IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hA0 ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
    · have h1 := congrArg Subrepresentation.toSubmodule h
      rw [Submodule.eq_bot_iff]
      intro x hx
      have h2 : (⟨x, hx⟩ : A.toSubmodule) ∈ (⊥ : Subrepresentation A.toRepresentation).toSubmodule := by
        rw [h1]; exact Submodule.mem_top
      have h3 : (⟨x, hx⟩ : A.toSubmodule) = 0 := (Submodule.mem_bot ℂ).mp h2
      exact congrArg Subtype.val h3
    · by_cases hU : U.toSubmodule = ⊥
      · left
        exact Subrepresentation.toSubmodule_injective hU
      · right
        let U' : Subrepresentation ρ :=
          ⟨U.toSubmodule.map A.toSubmodule.subtype, by
            intro g v hv
            obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
            exact Submodule.mem_map.mpr ⟨A.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩⟩
        have hfr : Module.finrank ℂ U'.toSubmodule = Module.finrank ℂ U.toSubmodule :=
          Submodule.finrank_map_subtype_eq _ _
        have hU0 : U'.toSubmodule ≠ ⊥ := by
          intro h
          have : Module.finrank ℂ U'.toSubmodule = 0 := by rw [h]; exact finrank_bot ℂ V
          rw [hfr, Submodule.finrank_eq_zero] at this
          exact hU this
        have hmin := Nat.find_min' hex ⟨U', hU0, rfl⟩
        have hle : Module.finrank ℂ U.toSubmodule ≤ Module.finrank ℂ A.toSubmodule :=
          Submodule.finrank_le _
        apply Subrepresentation.toSubmodule_injective
        exact Submodule.eq_top_of_finrank_eq (by omega)
  refine ⟨FDRep.of A.toRepresentation, simple_of_irr _, A.toSubmodule.subtype, ?_, ?_⟩
  · intro g
    ext v
    rfl
  · intro h
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0
    exact hv0 (congrArg (fun φ : A.toSubmodule →ₗ[ℂ] V => φ ⟨v, hv⟩) h)

end PI.GreenLabelSurjWork

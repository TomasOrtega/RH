import Mathlib
import Formalism.UnipotentAdelicQuotients.CuspEllipticValues
import Development.AbelianVarietyTheory.BlockTheory.IrreducibleCharacters.CuspidalCharacters
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps

namespace GlobalTheory.CuspCharCompare

open CuspElliptic GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
open scoped MonoidAlgebra

section Group

variable {G : Type} [Group G]

/- English proof (translation)
Establish `hE : Nontrivial (Module.End R M)` using `Module.nontrivial_of_finrank_eq_succ h`. Establish `hM : Nontrivial M`. Assume the negation of the conclusion as `hM`. Rewrite `hM` using `[not_nontrivial_iff_subsingleton]`. Conclude with `not_subsingleton (Module.End R M) inferInstance`.

Establish `: Nontrivial (Submodule R M)` using `(Submodule.nontrivial_iff R).2 hM`. Use `{ eq_bot_or_eq_top := fun U => ?_ }` and prove the remaining obligations. Take `⟨U', hU⟩` from `exists_isCompl U`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) one_ne_zero).1 h (U.subtype ∘ₗ U.projectionOnto U' hU)`. Distinguish the cases in `h0 : c = 0`.

Use `left`. Rewrite using `[Submodule.eq_bot_iff]`. Introduce `x hx`. Use `LinearMap.congr_fun hc x` as an intermediate fact. Rewrite `this` using `[h0, zero_smul]`.

Establish `h2 : (U.subtype ∘ₗ U.projectionOnto U' hU) x = x`. Simplify using `using congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨x, hx⟩)`. Rewrite using `[← h2, ← this]`. Both sides reduce to the same expression. Use `right`.

Rewrite using `[Submodule.eq_top_iff']`. Introduce `x`. Use `LinearMap.congr_fun hc (c⁻¹ • x)` as an intermediate fact. Establish `h2 : (c • (1 : Module.End R M)) (c⁻¹ • x) = x`. Simplify using `[smul_smul, h0]`.

Rewrite using `[← h2, this]`. Conclude with `Subtype.property _`.
-/
theorem isSimpleModule_of_finrank_end {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module R M]
    [Module ℂ M] [IsScalarTower ℂ R M] [SMulCommClass R ℂ M] [IsSemisimpleModule R M]
    (h : Module.finrank ℂ (Module.End R M) = 1) : IsSimpleModule R M := by
  have hE : Nontrivial (Module.End R M) := Module.nontrivial_of_finrank_eq_succ h
  have hM : Nontrivial M := by
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    exact not_subsingleton (Module.End R M) inferInstance
  have : Nontrivial (Submodule R M) := (Submodule.nontrivial_iff R).2 hM
  refine { eq_bot_or_eq_top := fun U => ?_ }
  obtain ⟨U', hU⟩ := exists_isCompl U
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) one_ne_zero).1 h
    (U.subtype ∘ₗ U.projectionOnto U' hU)
  by_cases h0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := LinearMap.congr_fun hc x
    rw [h0, zero_smul] at this
    have h2 : (U.subtype ∘ₗ U.projectionOnto U' hU) x = x := by
      simpa using congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨x, hx⟩)
    rw [← h2, ← this]; rfl
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have := LinearMap.congr_fun hc (c⁻¹ • x)
    have h2 : (c • (1 : Module.End R M)) (c⁻¹ • x) = x := by
      simp [smul_smul, h0]
    rw [← h2, this]
    exact Subtype.property _

variable [Fintype G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end Group

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

end GlobalTheory.CuspCharCompare

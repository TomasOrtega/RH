import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.LsCmp

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem cmpq_bijective (R : Type) [CommRing R] (C : Type 1) [Category.{0} C]
    (A : C ⥤ CommAlgCat.{0} R) (l n i : ℕ) : Function.Bijective ((cmpq A l n).f i) := by
  have hmk := cmpq_mk A l n i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hmk] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    have hy : ∀ s : ComposableArrows C i, ∃ a : ↑(A.obj (s.obj (Fin.last i))),
        a * algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n) = y s := by
      intro s
      have h1 : ((qM A l n).pullC i y) s = 0 := by
        rw [hq]
        rfl
      have h2 : Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) (y s) = 0 :=
        congrArg Subtype.val h1
      exact Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h2)
    choose a ha using hy
    rw [CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]
    refine ⟨a, ?_⟩
    funext s
    show ((l : R) ^ n) • a s = y s
    rw [Algebra.smul_def, mul_comm]
    exact ha s
  · intro g
    have hx : ∀ s : ComposableArrows C i, ∃ x : ↑(A.obj (s.obj (Fin.last i))),
        Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) x =
          Subtype.val (g s) := fun s => Ideal.Quotient.mk_surjective _
    choose x hx using hx
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [hmk]
    funext s
    apply Subtype.ext
    exact hx s

end GlobalTheory.CompanionTheory.LsCmp

end

import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.LsCmp

/- English proof (translation)
Establish `hmk` using `cmpq_mk A l n i`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `q hq`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Rewrite `hq` using `[hmk]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Establish `hy : ∀ s : ComposableArrows C i, ∃ a : ↑(A.obj (s.obj (Fin.last i))), a * algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n) = y s`. Introduce `s`. Establish `h1 : ((qM A l n).pullC i y) s = 0`.

Rewrite using `[hq]`. Both sides reduce to the same expression. Establish `h2 : Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) (y s) = 0` using `congrArg Subtype.val h1`. Conclude with `Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h2)`. Use `choose a ha using hy`.

Rewrite using `[CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]`. Use `⟨a, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Use `show ((l : R) ^ n) • a s = y s`. Rewrite using `[Algebra.smul_def, mul_comm]`.

Conclude with `ha s`. Introduce `g`. Establish `hx : ∀ s : ComposableArrows C i, ∃ x : ↑(A.obj (s.obj (Fin.last i))), Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) x = Subtype.val (g s)` using `fun s => Ideal.Quotient.mk_surjective _`. Use `choose x hx using hx`. Use `⟨Submodule.Quotient.mk x, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmk]`. Use function extensionality and compare the values at `s`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hx s`.
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

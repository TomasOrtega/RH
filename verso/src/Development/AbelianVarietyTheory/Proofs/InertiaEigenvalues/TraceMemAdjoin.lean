import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CentralIdem

/- English proof (translation)
Use `haveI : NeZero n := ⟨hn⟩`. Rewrite using `[Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]`. Apply `Subalgebra.multiset_sum_mem` to reduce the goal to its premises. Introduce `μ hμ`. Establish `hr : T.charpoly.IsRoot μ` using `Polynomial.isRoot_of_mem_roots hμ`.

Establish `he : T.HasEigenvalue μ` using `(Module.End.hasEigenvalue_iff_isRoot_charpoly T μ).2 hr`. Take `⟨v, hv⟩` from `he.exists_hasEigenvector`. Establish `h1` using `hv.pow_apply (n + 1)`. Rewrite `h1` using `[hT, hv.apply_eq_smul]`. Establish `h2 : μ = μ ^ (n + 1)` using `smul_left_injective ℂ hv.2 h1`.

Distinguish the cases in `h0 : μ = 0`. Rewrite using `[h0]`. Conclude with `Subalgebra.zero_mem _`. Establish `h3 : μ ^ n = 1`. Rewrite `h2` using `[pow_succ]`.

Conclude with `mul_right_cancel₀ h0 (by rw [one_mul]; exact h2.symm)`. Take `⟨i, -, hi⟩` from `hζ.eq_pow_of_pow_eq_one h3`. Rewrite using `[← hi]`. Conclude with `Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _`.
-/
theorem trace_mem_adjoin {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hT : T ^ (n + 1) = T) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    LinearMap.trace ℂ V T ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  haveI : NeZero n := ⟨hn⟩
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  apply Subalgebra.multiset_sum_mem
  intro μ hμ
  have hr : T.charpoly.IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
  have he : T.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly T μ).2 hr
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  have h1 := hv.pow_apply (n + 1)
  rw [hT, hv.apply_eq_smul] at h1
  have h2 : μ = μ ^ (n + 1) := smul_left_injective ℂ hv.2 h1
  by_cases h0 : μ = 0
  · rw [h0]; exact Subalgebra.zero_mem _
  · have h3 : μ ^ n = 1 := by
      rw [pow_succ] at h2
      exact mul_right_cancel₀ h0 (by rw [one_mul]; exact h2.symm)
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h3
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _

/- English proof (translation)
Use `haveI := Fintype.ofFinite Γ`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis Γ ℂ), Matrix.trace]`. Establish `: ∀ g : Γ, (LinearMap.toMatrix (MonoidAlgebra.basis Γ ℂ) (MonoidAlgebra.basis Γ ℂ) (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x)).diag g = x.coeff 1`. Introduce `g`. Rewrite using `[Matrix.diag, LinearMap.toMatrix_apply]`.

Establish `hb : MonoidAlgebra.basis Γ ℂ g = MonoidAlgebra.single g 1` using `by simp`. Rewrite using `[hb]`. Express the relevant statement in the definitionally equal form `(x * MonoidAlgebra.single g (1 : ℂ)).coeff g = _`. Rewrite using `[MonoidAlgebra.coeff_mul_single_apply]`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_congr rfl fun g _ => this g]`. Simplify using the standard rewrite rules.
-/
theorem trace_lmul {Γ : Type} [Group Γ] [Finite Γ] (x : MonoidAlgebra ℂ Γ) :
    LinearMap.trace ℂ _ (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x) = (Nat.card Γ : ℂ) * x.coeff 1 := by
  classical
  haveI := Fintype.ofFinite Γ
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis Γ ℂ), Matrix.trace]
  have : ∀ g : Γ, (LinearMap.toMatrix (MonoidAlgebra.basis Γ ℂ) (MonoidAlgebra.basis Γ ℂ)
      (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x)).diag g = x.coeff 1 := by
    intro g
    rw [Matrix.diag, LinearMap.toMatrix_apply]
    have hb : MonoidAlgebra.basis Γ ℂ g = MonoidAlgebra.single g 1 := by simp
    rw [hb]
    change (x * MonoidAlgebra.single g (1 : ℂ)).coeff g = _
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp
  rw [Finset.sum_congr rfl fun g _ => this g]
  simp

/- English proof (translation)
Introduce `Γ _ _ e he hc ζ hζ h`. Use `haveI : Module.Finite ℂ (MonoidAlgebra ℂ Γ) := Module.Finite.of_basis (MonoidAlgebra.basis Γ ℂ)`. Use `set x : MonoidAlgebra ℂ Γ := MonoidAlgebra.single h⁻¹ (1 : ℂ) * e with hx`. Establish `hcm : Commute (MonoidAlgebra.single h⁻¹ (1 : ℂ)) e` using `(hc _).symm`. Establish `hid : IsIdempotentElem e` using `he`.

Establish `hp : x ^ (Nat.card Γ + 1) = x`. Rewrite using `[hx, hcm.mul_pow, hid.pow_succ_eq, MonoidAlgebra.single_pow, one_pow, pow_succ, pow_card_eq_one', one_mul]`. Establish `hT` using `trace_mem_adjoin (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x) (n := Nat.card Γ) Nat.card_pos.ne' (by rw [← map_pow, hp]) hζ`. Rewrite `hT` using `[trace_lmul, hx, MonoidAlgebra.coeff_single_mul_apply]`. Simplify using `using hT`.
-/
theorem centralIdemCoeff : CentralIdemCoeff := by
  intro Γ _ _ e he hc ζ hζ h
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ Γ) := Module.Finite.of_basis (MonoidAlgebra.basis Γ ℂ)
  set x : MonoidAlgebra ℂ Γ := MonoidAlgebra.single h⁻¹ (1 : ℂ) * e with hx
  have hcm : Commute (MonoidAlgebra.single h⁻¹ (1 : ℂ)) e := (hc _).symm
  have hid : IsIdempotentElem e := he
  have hp : x ^ (Nat.card Γ + 1) = x := by
    rw [hx, hcm.mul_pow, hid.pow_succ_eq, MonoidAlgebra.single_pow, one_pow, pow_succ,
      pow_card_eq_one', one_mul]
  have hT := trace_mem_adjoin (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x) (n := Nat.card Γ)
    Nat.card_pos.ne' (by rw [← map_pow, hp]) hζ
  rw [trace_lmul, hx, MonoidAlgebra.coeff_single_mul_apply] at hT
  simpa using hT

end GlobalTheory.CentralIdem

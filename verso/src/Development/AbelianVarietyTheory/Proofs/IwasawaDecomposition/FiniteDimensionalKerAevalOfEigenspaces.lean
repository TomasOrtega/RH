import Mathlib

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `hn : p.natDegree using Nat.strong_induction_on generalizing p with`. Consider the case `_ n ih`. Distinguish the cases in `h0 : p.degree = 0`. Establish `hu : IsUnit p` using `Polynomial.isUnit_iff_degree_eq_zero.mpr h0`. Establish `hu' : IsUnit (Polynomial.aeval T p)` using `hu.map _`.

Establish `hk : LinearMap.ker (Polynomial.aeval T p) = ⊥` using `LinearMap.ker_eq_bot.mpr ((Module.End.isUnit_iff _).mp hu').1`. Rewrite using `[hk]`. Use `infer_instance`. Take `⟨a, ha⟩` from `IsAlgClosed.exists_root p h0`. Take `⟨q, hq⟩` from `Polynomial.dvd_iff_isRoot.mpr ha`.

Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hq`. Conclude with `hp hq`. Establish `hdeg : q.natDegree < n`.

Rewrite using `[← hn, hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq0, Polynomial.natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Establish `ihq` using `ih _ hdeg q hq0 rfl`. Establish `hfg : (LinearMap.ker (Polynomial.aeval T p)).FG`. Apply `Submodule.fg_of_fg_map_of_fg_inf_ker (Polynomial.aeval T q)` to reduce the goal to its premises.

Establish `hle : (LinearMap.ker (Polynomial.aeval T p)).map (Polynomial.aeval T q) ≤ T.eigenspace a`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Establish `hx' : Polynomial.aeval T p x = 0` using `hx`. Rewrite `hx'` using `[hq, map_mul, Module.End.mul_apply]`.

Simplify using `only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply] at hx'`. Conclude with `sub_eq_zero.mp hx'`. Use `haveI := hT a`. Conclude with `(Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le hle)`. Conclude with `(Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le (inf_le_right : _ ≤ LinearMap.ker (Polynomial.aeval T q)))`.

Conclude with `(Module.Finite.iff_fg).mpr hfg`.
-/
theorem finiteDimensional_ker_aeval_of_eigenspaces
    (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (hT : ∀ lam : ℂ, FiniteDimensional ℂ (T.eigenspace lam)) (p : Polynomial ℂ) (hp : p ≠ 0) :
    FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  by_cases h0 : p.degree = 0
  · have hu : IsUnit p := Polynomial.isUnit_iff_degree_eq_zero.mpr h0
    have hu' : IsUnit (Polynomial.aeval T p) := hu.map _
    have hk : LinearMap.ker (Polynomial.aeval T p) = ⊥ :=
      LinearMap.ker_eq_bot.mpr ((Module.End.isUnit_iff _).mp hu').1
    rw [hk]
    infer_instance
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p h0
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr ha
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hq
      exact hp hq
    have hdeg : q.natDegree < n := by
      rw [← hn, hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq0,
        Polynomial.natDegree_X_sub_C]
      omega
    have ihq := ih _ hdeg q hq0 rfl
    have hfg : (LinearMap.ker (Polynomial.aeval T p)).FG := by
      apply Submodule.fg_of_fg_map_of_fg_inf_ker (Polynomial.aeval T q)
      · have hle : (LinearMap.ker (Polynomial.aeval T p)).map (Polynomial.aeval T q)
            ≤ T.eigenspace a := by
          rintro _ ⟨x, hx, rfl⟩
          rw [Module.End.mem_eigenspace_iff]
          have hx' : Polynomial.aeval T p x = 0 := hx
          rw [hq, map_mul, Module.End.mul_apply] at hx'
          simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
            Module.algebraMap_end_apply] at hx'
          exact sub_eq_zero.mp hx'
        haveI := hT a
        exact (Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le hle)
      · exact (Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le
          (inf_le_right : _ ≤ LinearMap.ker (Polynomial.aeval T q)))
    exact (Module.Finite.iff_fg).mpr hfg

end GlobalTheory

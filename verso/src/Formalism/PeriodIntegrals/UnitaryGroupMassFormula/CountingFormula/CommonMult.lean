import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EichESymmApply
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalTheoryWindows

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Take `⟨s, hs⟩` from `hP`. Use `⟨Set.range (fun r : s → Fin N.natAbs => ∑ g : s, ((r g : ℕ) : ℤ) • (g : M)), Set.finite_range _, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[← hs]`. Take `⟨f, -, hf⟩` from `Submodule.mem_span_finset.1 hx`.

Use `⟨∑ g ∈ s, (f g / N) • g, ?_, ∑ g ∈ s, (f g % N) • g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hs]`. Conclude with `Submodule.sum_mem _ fun g hg => Submodule.smul_mem _ _ (Submodule.subset_span hg)`. Use `⟨fun g => ⟨(f g % N).toNat, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `Int.emod_nonneg (f g) hN`.

Establish `h2` using `Int.emod_lt (f g) hN`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Finset.sum_coe_sort s]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Int.toNat_of_nonneg (Int.emod_nonneg _ hN)]`.

Rewrite using `[← hf, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← add_smul, Int.mul_ediv_add_emod]`.
-/
theorem gen_red {M : Type*} [AddCommGroup M] (P : Submodule ℤ M) (hP : P.FG) (N : ℤ) (hN : N ≠ 0) :
    ∃ Rs : Set M, Rs.Finite ∧ ∀ x ∈ P, ∃ q ∈ P, ∃ ρ ∈ Rs, x = N • q + ρ := by
  obtain ⟨s, hs⟩ := hP
  refine ⟨Set.range (fun r : s → Fin N.natAbs => ∑ g : s, ((r g : ℕ) : ℤ) • (g : M)), Set.finite_range _, ?_⟩
  intro x hx
  rw [← hs] at hx
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hx
  refine ⟨∑ g ∈ s, (f g / N) • g, ?_, ∑ g ∈ s, (f g % N) • g, ?_, ?_⟩
  · rw [← hs]
    exact Submodule.sum_mem _ fun g hg => Submodule.smul_mem _ _ (Submodule.subset_span hg)
  · refine ⟨fun g => ⟨(f g % N).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_nonneg (f g) hN
      have h2 := Int.emod_lt (f g) hN
      omega
    · rw [← Finset.sum_coe_sort s]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hN)]
  · rw [← hf, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_smul, ← add_smul, Int.mul_ediv_add_emod]

/- English proof (translation)
Use `IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)` as an intermediate fact. Use `Algebra.IsAlgebraic.trans ℤ ℚ D.host.E` as an intermediate fact. Take `⟨n, hn, h⟩` from `Algebra.IsAlgebraic.exists_integral_multiples ℤ s`. Conclude with `⟨n, hn, fun k hk => ⟨⟨n • k, h k hk⟩, zsmul_eq_mul k n⟩⟩`.
-/
theorem int_mult (D : Formalism.BasicNotions.D7) (s : Finset D.host.E) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ k ∈ s, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (n : D.host.E) * k := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have := Algebra.IsAlgebraic.trans ℤ ℚ D.host.E
  obtain ⟨n, hn, h⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  exact ⟨n, hn, fun k hk => ⟨⟨n • k, h k hk⟩, zsmul_eq_mul k n⟩⟩

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult .. | (apply UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> assumption) | (intros; apply UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> assumption) | (apply @UpperTheory.Reformulated.B.Loc …`.
-/
theorem lat_mult (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ)
    (v : (VS D).V) : ∃ n : ℤ, n ≠ 0 ∧ (n : D.host.E) • v ∈ Λ := by
  first | exact UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult .. | (apply UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> assumption) | (intros; apply UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> assumption) | (apply @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> assumption) | (apply @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult D Λ hΛ v | exact @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult D Λ hΛ | exact @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult D Λ | exact @UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult D

/- English proof (translation)
Establish `hv : ∃ n : ℤ, n ≠ 0 ∧ ∀ v ∈ vs, (n : D.host.E) • v ∈ Λ`. Proceed by induction on `vs using Finset.induction_on with`. Consider the case `empty => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `insert v vs hv ih`. Take `⟨n, hn, h⟩` from `ih`.

Take `⟨m, hm, hmv⟩` from `lat_mult D hΛ v`. Use `⟨m * n, mul_ne_zero hm hn, fun w hw => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hw with rfl | hw` into its components or cases. Establish `: ((m * n : ℤ) : D.host.E) • w = (n : D.host.E) • ((m : D.host.E) • w)`. Rewrite using `[smul_smul, Int.cast_mul, mul_comm]`.

Rewrite using `[this]; exact smul_int_mem D ⟨n, by simp⟩ hmv`. Establish `: ((m * n : ℤ) : D.host.E) • w = (m : D.host.E) • ((n : D.host.E) • w)`. Rewrite using `[smul_smul, Int.cast_mul]`. Rewrite using `[this]; exact smul_int_mem D ⟨m, by simp⟩ (h w hw)`. Take `⟨n, hn, h1⟩` from `hv`.

Take `⟨m, hm, h2⟩` from `int_mult D ks`. Use `⟨n * m, mul_ne_zero hn hm, fun v hv => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Establish `: ((n * m : ℤ) : D.host.E) • v = (m : D.host.E) • ((n : D.host.E) • v)`. Rewrite using `[smul_smul, Int.cast_mul, mul_comm]`. Rewrite using `[this]; exact smul_int_mem D ⟨m, by simp⟩ (h1 v hv)`.

Take `⟨o, ho⟩` from `h2 k hk`. Use `⟨(n : 𝓞 D.host.E) * o, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ho, map_intCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem common_mult (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ)
    (vs : Finset (VS D).V) (ks : Finset D.host.E) :
    ∃ n : ℤ, n ≠ 0 ∧ (∀ v ∈ vs, (n : D.host.E) • v ∈ Λ) ∧
      ∀ k ∈ ks, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (n : D.host.E) * k := by
  have hv : ∃ n : ℤ, n ≠ 0 ∧ ∀ v ∈ vs, (n : D.host.E) • v ∈ Λ := by
    induction vs using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert v vs hv ih =>
      obtain ⟨n, hn, h⟩ := ih
      obtain ⟨m, hm, hmv⟩ := lat_mult D hΛ v
      refine ⟨m * n, mul_ne_zero hm hn, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with rfl | hw
      · have : ((m * n : ℤ) : D.host.E) • w = (n : D.host.E) • ((m : D.host.E) • w) := by
          rw [smul_smul, Int.cast_mul, mul_comm]
        rw [this]; exact smul_int_mem D ⟨n, by simp⟩ hmv
      · have : ((m * n : ℤ) : D.host.E) • w = (m : D.host.E) • ((n : D.host.E) • w) := by
          rw [smul_smul, Int.cast_mul]
        rw [this]; exact smul_int_mem D ⟨m, by simp⟩ (h w hw)
  obtain ⟨n, hn, h1⟩ := hv
  obtain ⟨m, hm, h2⟩ := int_mult D ks
  refine ⟨n * m, mul_ne_zero hn hm, fun v hv => ?_, fun k hk => ?_⟩
  · have : ((n * m : ℤ) : D.host.E) • v = (m : D.host.E) • ((n : D.host.E) • v) := by
      rw [smul_smul, Int.cast_mul, mul_comm]
    rw [this]; exact smul_int_mem D ⟨m, by simp⟩ (h1 v hv)
  · obtain ⟨o, ho⟩ := h2 k hk
    refine ⟨(n : 𝓞 D.host.E) * o, ?_⟩
    rw [map_mul, ho, map_intCast]; push_cast; ring

end PI.UnitaryGroupMassFormula.CntFormula

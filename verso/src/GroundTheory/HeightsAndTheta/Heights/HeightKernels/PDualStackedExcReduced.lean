import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcCycle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalReduced

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]

/- English proof (translation)
Introduce `x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`. Rewrite using `[mul_add]`. Use `Ideal.add_mem _ (Ideal.mem_sup_left ((stackedGraph b' a).mul_mem_left _ hy)) ?_` and prove the remaining obligations. Use `clear hx`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨s, rfl⟩` from `hx`. Rewrite using `[mul_comm (graphSecond u)]`. Conclude with `StackedExceptionalCycle.mul_mem_first b' a s u`.

Consider the case `zero => rw [mul_zero]`. Conclude with `Ideal.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `Ideal.add_mem _ hx hy`. Consider the case `smul r x _ hx => rw [smul_eq_mul, mul_left_comm]`.

Conclude with `Ideal.mul_mem_left _ r hx`.
-/
theorem mul_mem_of_mem_base [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (u : T) :
    ∀ x ∈ stackedBase b' a,
      graphSecond u * x ∈ stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u} := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [mul_add]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ((stackedGraph b' a).mul_mem_left _ hy)) ?_
  clear hx
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [mul_comm (graphSecond u)]
    exact StackedExceptionalCycle.mul_mem_first b' a s u
  | zero => rw [mul_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ r hx

/- English proof (translation)
Rewrite using `[linPrime, RingHom.mem_ker, LinPrimeExample.linPointMap_first]`. Conclude with `mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_ne_zero _)`.
-/
theorem graphFirst_not_mem {k : Type} [Field k] {n : ℕ} {α : T → k} {M : T → Fin n → k} {t : T}
    (h : α t ≠ 0) : graphFirst t ∉ linPrime α M := by
  rw [linPrime, RingHom.mem_ker, LinPrimeExample.linPointMap_first]
  exact mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_ne_zero _)

/- English proof (translation)
Rewrite using `[linPrime, RingHom.mem_ker, LinPrimeExample.linPointMap_second]`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Establish `h1` using `congrArg (MvPolynomial.eval fun o : Option (Fin (m + 1)) => o.elim (0 : k) fun j => if j = 0 then 1 else 0) h0`. Simplify `h1` using `[Finset.sum_ite_eq']`.
-/
theorem graphSecond_not_mem {k : Type} [Field k] {m : ℕ} {α : T → k} {M : T → Fin (m + 1) → k} {t : T}
    (h : M t 0 ≠ 0) : graphSecond t ∉ linPrime α M := by
  rw [linPrime, RingHom.mem_ker, LinPrimeExample.linPointMap_second]
  intro h0
  apply h
  have h1 := congrArg (MvPolynomial.eval fun o : Option (Fin (m + 1)) =>
    o.elim (0 : k) fun j => if j = 0 then 1 else 0) h0
  simpa [Finset.sum_ite_eq'] using h1

end StackedExceptionalReduced

open StackedExceptionalCycle StackedGraphHorizontal StackedExceptionalReduced in

/- English proof (translation)
Introduce `K _ _ i F F' T _ _ b b' a hi hlt hcov hab`. Take `⟨k, _, ρ, π, y₀, m, g, α, M, hd⟩` from `hC K i F F' T b b' a hi hlt hcov hab`. Establish `hbase` using `hB K i F F' T b b' a hi hlt hcov hab k ρ π y₀ m g α M hd`. Establish `hchart` using `hX K i F F' T b b' a hi hlt hcov hab k ρ π y₀ m g α M hd`. Take `⟨-, -, -, -, -, -, -, ⟨v, hv⟩, ⟨u, hu⟩, -⟩` from `hd`.

Establish `hEp : (linPrime α M).IsPrime` using `RingHom.ker_isPrime _`. Establish `hXv : graphFirst v ∉ linPrime α M` using `graphFirst_not_mem hv`. Establish `hYu : graphSecond u ∉ linPrime α M` using `graphSecond_not_mem hu`. Establish `hrel : IsRelevant (linPrime α M)`. Introduce and unpack `(⟨⟩ | ⟨⟩)`.

Conclude with `⟨v, hXv⟩`. Conclude with `⟨u, hYu⟩`. Establish `hsub : ∀ w : T, stackedGraph b' a ⊔ Ideal.span {C (a w) * graphFirst w} ≤ stackedBase b' a` using `fun w => sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (first_mem_base b' a w))`. Establish `hkey : ∀ W : Ideal (MRing (stackedBlocks T)), W.IsPrime → IsRelevant W → stackedBase b' a ≤ W → linPrime α M ≤ W`. Introduce `W hW hWr hBW e he`.

Take `⟨v', hv'⟩ : ∃ v' : T, graphFirst v' ∉ W` from `hWr (Sum.inl ())`. Take `⟨u', hu'⟩ : ∃ u' : T, graphSecond u' ∉ W` from `hWr (Sum.inr ())`. Take `⟨N, hN⟩` from `hchart v' u'`. Establish `h1 : (graphFirst v' * graphSecond u') ^ N * e ∈ W` using `hBW (hsub u' (hN e he))`. Use `(hW.mem_or_mem h1).resolve_left fun h2 => ?_` and prove the remaining obligations.

Break down `hW.mem_or_mem (hW.mem_of_pow_mem N h2) with h3 | h3` into its components or cases. Conclude with `hv' h3`. Conclude with `hu' h3`. Establish `hmin : linPrime α M ∈ (stackedBase b' a).minimalPrimes`. Use `⟨⟨hEp, hbase⟩, fun Q hQ hQE => hkey Q hQ.1 (fun κ => ?_) hQ.2⟩` and prove the remaining obligations.

Take `⟨j, hj⟩` from `hrel κ`. Conclude with `⟨j, fun h => hj (hQE h)⟩`. Use `⟨linPrime α M, ⟨hmin, hrel⟩, fun W hW => ?_, ?_⟩` and prove the remaining obligations. Establish `hEW` using `hkey W hW.1.1.1 hW.2 hW.1.1.2`. Conclude with `le_antisymm (hW.1.2 ⟨hEp, hbase⟩ hEW) hEW`.

Take `⟨N, hN⟩` from `hchart v u`. Establish `hs : (graphFirst v * graphSecond u) ^ N ∉ linPrime α M` using `fun h => (hEp.mem_or_mem (hEp.mem_of_pow_mem N h)).elim hXv hYu`. Rewrite using `[← multAt_eq_of_mul_mem (hsub u) hYu (mul_mem_of_mem_base b' a u), multAt_eq_of_mul_mem ((hsub u).trans hbase) hs hN]`. Use `hEp` as an intermediate fact. Conclude with `ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self _`.
-/
theorem DualStackedExcReduced.proof (hC : DualStackedExcCoords.Statement) (hB : DualStackedExcBase.Statement)
    (hX : DualStackedExcChart.Statement) : DualStackedExcReduced.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab
  obtain ⟨k, _, ρ, π, y₀, m, g, α, M, hd⟩ := hC K i F F' T b b' a hi hlt hcov hab
  have hbase := hB K i F F' T b b' a hi hlt hcov hab k ρ π y₀ m g α M hd
  have hchart := hX K i F F' T b b' a hi hlt hcov hab k ρ π y₀ m g α M hd
  obtain ⟨-, -, -, -, -, -, -, ⟨v, hv⟩, ⟨u, hu⟩, -⟩ := hd
  have hEp : (linPrime α M).IsPrime := RingHom.ker_isPrime _
  have hXv : graphFirst v ∉ linPrime α M := graphFirst_not_mem hv
  have hYu : graphSecond u ∉ linPrime α M := graphSecond_not_mem hu
  have hrel : IsRelevant (linPrime α M) := by
    rintro (⟨⟩ | ⟨⟩)
    · exact ⟨v, hXv⟩
    · exact ⟨u, hYu⟩
  have hsub : ∀ w : T, stackedGraph b' a ⊔ Ideal.span {C (a w) * graphFirst w} ≤ stackedBase b' a :=
    fun w => sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (first_mem_base b' a w))

  have hkey : ∀ W : Ideal (MRing (stackedBlocks T)), W.IsPrime → IsRelevant W → stackedBase b' a ≤ W →
      linPrime α M ≤ W := by
    intro W hW hWr hBW e he
    obtain ⟨v', hv'⟩ : ∃ v' : T, graphFirst v' ∉ W := hWr (Sum.inl ())
    obtain ⟨u', hu'⟩ : ∃ u' : T, graphSecond u' ∉ W := hWr (Sum.inr ())
    obtain ⟨N, hN⟩ := hchart v' u'
    have h1 : (graphFirst v' * graphSecond u') ^ N * e ∈ W := hBW (hsub u' (hN e he))
    refine (hW.mem_or_mem h1).resolve_left fun h2 => ?_
    rcases hW.mem_or_mem (hW.mem_of_pow_mem N h2) with h3 | h3
    · exact hv' h3
    · exact hu' h3
  have hmin : linPrime α M ∈ (stackedBase b' a).minimalPrimes := by
    refine ⟨⟨hEp, hbase⟩, fun Q hQ hQE => hkey Q hQ.1 (fun κ => ?_) hQ.2⟩
    obtain ⟨j, hj⟩ := hrel κ
    exact ⟨j, fun h => hj (hQE h)⟩
  refine ⟨linPrime α M, ⟨hmin, hrel⟩, fun W hW => ?_, ?_⟩
  · have hEW := hkey W hW.1.1.1 hW.2 hW.1.1.2
    exact le_antisymm (hW.1.2 ⟨hEp, hbase⟩ hEW) hEW
  · obtain ⟨N, hN⟩ := hchart v u
    have hs : (graphFirst v * graphSecond u) ^ N ∉ linPrime α M := fun h =>
      (hEp.mem_or_mem (hEp.mem_of_pow_mem N h)).elim hXv hYu
    rw [← multAt_eq_of_mul_mem (hsub u) hYu (mul_mem_of_mem_base b' a u),
      multAt_eq_of_mul_mem ((hsub u).trans hbase) hs hN]
    have := hEp
    exact ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self _

end

end GroundTheory.Heights₂.Heights

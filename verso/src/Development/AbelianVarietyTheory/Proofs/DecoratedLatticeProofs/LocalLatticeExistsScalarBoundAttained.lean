import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ _ _ n _ L hL hn`. Take `⟨s, hs⟩` from `hL.fg`. Establish `hex : ∃ x ∈ s, ∃ j, x j ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hbot : L = ⊥`. Rewrite using `[← hs, Submodule.span_eq_bot]`. Introduce `x hx`. Use function extensionality and compare the values at `j`. Conclude with `hcon x hx j`.

Establish `htop` using `hL.span_eq_top`. Rewrite `htop` using `[hbot]`. Simplify using `only [Submodule.bot_coe, Submodule.span_zero_singleton] at htop`. Take `⟨j⟩` from `hn`. Establish `h1 : (Pi.single j (1 : k) : n → k) ∈ (⊤ : Submodule k (n → k))` using `Submodule.mem_top`.

Rewrite `h1` using `[← htop, Submodule.mem_bot]`. Use `congrFun h1 j` as an intermediate fact. Simplify using `at this`. Take `⟨x0, hx0, j0, hx0j⟩` from `hex`. Establish `hne : (s ×ˢ (Finset.univ : Finset n)).Nonempty` using `⟨(x0, j0), by simp [hx0]⟩`.

Take `⟨p, hp, hmax⟩` from `Finset.exists_max_image (s ×ˢ (Finset.univ : Finset n)) (fun q : (n → k) × n => valuation k (q.1 q.2)) hne`. Establish `hc : p.1 p.2 ≠ 0`. Introduce `h0`. Use `hmax (x0, j0) (by simp [hx0])` as an intermediate fact. Simplify using `only [h0, map_zero] at this`.

Establish `h' : valuation k (x0 j0) = 0` using `le_antisymm this zero_le'`. Conclude with `hx0j ((Valuation.zero_iff _).mp h')`. Use `⟨p.1 p.2, hc, ?_, p.1, ?_, p.2, rfl⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[← hs]`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Introduce `j`. Use `show valuation k ((p.1 p.2)⁻¹ * y j) ≤ 1`. Establish `hle` using `hmax (y, j) (by simpa using hy)`.

Simplify using `only at hle`. Establish `hvc : valuation k (p.1 p.2) ≠ 0` using `by simpa using hc`. Rewrite using `[map_mul, map_inv₀]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `zero => intro j`.

Simplify using the standard rewrite rules. Consider the case `add y z _ _ hy hz`. Introduce `j`. Simplify `add_mem (hy j) (hz j)` using `[mul_add]`. Consider the case `smul a y _ hy`.

Introduce `j`. Use `mul_mem a.2 (hy j)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Pi.smul_apply, Subring.smul_def, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hs]`. Conclude with `Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_product.mp hp).1)`.
-/
theorem lattice_exists_scalar_bound_attained : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (L : Submodule 𝒪[k] (n → k)), L.IsLattice k → Nonempty n → ∃ c : k, c ≠ 0 ∧ (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ x ∈ L, ∃ j, x j = c := by
  intro k _ _ _ _ n _ L hL hn
  obtain ⟨s, hs⟩ := hL.fg

  have hex : ∃ x ∈ s, ∃ j, x j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : L = ⊥ := by
      rw [← hs, Submodule.span_eq_bot]
      intro x hx
      funext j
      exact hcon x hx j
    have htop := hL.span_eq_top
    rw [hbot] at htop
    simp only [Submodule.bot_coe, Submodule.span_zero_singleton] at htop
    obtain ⟨j⟩ := hn
    have h1 : (Pi.single j (1 : k) : n → k) ∈ (⊤ : Submodule k (n → k)) := Submodule.mem_top
    rw [← htop, Submodule.mem_bot] at h1
    have := congrFun h1 j
    simp at this
  obtain ⟨x0, hx0, j0, hx0j⟩ := hex
  have hne : (s ×ˢ (Finset.univ : Finset n)).Nonempty := ⟨(x0, j0), by simp [hx0]⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (s ×ˢ (Finset.univ : Finset n))
    (fun q : (n → k) × n => valuation k (q.1 q.2)) hne
  have hc : p.1 p.2 ≠ 0 := by
    intro h0
    have := hmax (x0, j0) (by simp [hx0])
    simp only [h0, map_zero] at this
    have h' : valuation k (x0 j0) = 0 := le_antisymm this zero_le'
    exact hx0j ((Valuation.zero_iff _).mp h')
  refine ⟨p.1 p.2, hc, ?_, p.1, ?_, p.2, rfl⟩
  · intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      intro j
      show valuation k ((p.1 p.2)⁻¹ * y j) ≤ 1
      have hle := hmax (y, j) (by simpa using hy)
      simp only at hle
      have hvc : valuation k (p.1 p.2) ≠ 0 := by simpa using hc
      rw [map_mul, map_inv₀]
      calc (valuation k (p.1 p.2))⁻¹ * valuation k (y j)
          ≤ (valuation k (p.1 p.2))⁻¹ * valuation k (p.1 p.2) := by gcongr
        _ = 1 := inv_mul_cancel₀ hvc
    | zero => intro j; simp
    | add y z _ _ hy hz =>
      intro j
      simpa [mul_add] using add_mem (hy j) (hz j)
    | smul a y _ hy =>
      intro j
      have := mul_mem a.2 (hy j)
      convert this using 1
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      ring
  · rw [← hs]
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_product.mp hp).1)

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrigVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.AdicSum

open Classical in

/- English proof (translation)
Rewrite using `[← Finset.sum_sdiff_sub_sum_sdiff (s₁ := T) (s₂ := S)]`. Conclude with `J.sub_mem (J.sum_mem fun α hα => hT α (Finset.mem_sdiff.1 hα).2) (J.sum_mem fun α hα => hS α (Finset.mem_sdiff.1 hα).2)`.
-/
theorem sum_sub_sum_mem {R : Type} [CommRing R] (J : Ideal R) {X : Type} (v : X → R)
    (S T : Finset X) (hS : ∀ α ∉ S, v α ∈ J) (hT : ∀ α ∉ T, v α ∈ J) :
    ∑ α ∈ S, v α - ∑ α ∈ T, v α ∈ J := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff (s₁ := T) (s₂ := S)]
  exact J.sub_mem (J.sum_mem fun α hα => hT α (Finset.mem_sdiff.1 hα).2)
    (J.sum_mem fun α hα => hS α (Finset.mem_sdiff.1 hα).2)

/- English proof (translation)
Introduce `R _ _ _ hR X v hfin`. Establish `hC : IsAdicComplete (maximalIdeal R) R` using `hR.1.2.2.2`. Establish `hfin' : ∀ n : ℕ, {α | v α ∉ maximalIdeal R ^ n}.Finite` using `fun n => (hfin n).subset fun α (hα : v α ∉ maximalIdeal R ^ n) (h : v α ∈ maximalIdeal R ^ (n + 1)) => hα (Ideal.pow_le_pow_right (Nat.le_succ n) h)`. Set `F : ℕ → Finset X` to `fun n => (hfin' n).toFinset`. Establish `hF : ∀ n, ∀ α ∉ F n, v α ∈ maximalIdeal R ^ n`.

Introduce `n α hα`. Assume the negation of the conclusion as `h`. Conclude with `hα ((hfin' n).mem_toFinset.2 h)`. Set `f : ℕ → R` to `fun n => ∑ α ∈ F n, v α`. Establish `hsm : ∀ n : ℕ, maximalIdeal R ^ n • (⊤ : Submodule R R) = maximalIdeal R ^ n` using `fun n => by`.

Rewrite using `[smul_eq_mul, Ideal.mul_top]`. Take `⟨L, hL⟩` from `(hC.toIsPrecomplete).prec (f := f) (by`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, hsm]`. Conclude with `sum_sub_sum_mem (maximalIdeal R ^ m) v (F m) (F n) (hF m) fun α hα => Ideal.pow_le_pow_right hmn (hF n α hα))`.

Use `⟨L, fun e S hS => ?_⟩` and prove the remaining obligations. Establish `h1 : f (e + 1) - L ∈ maximalIdeal R ^ (e + 1)`. Use `hL (e + 1)` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, hsm]`. Then use the resulting hypothesis. Establish `h2` using `sum_sub_sum_mem (maximalIdeal R ^ (e + 1)) v (F (e + 1)) S (hF (e + 1)) hS`.

Establish `: L - ∑ α ∈ S, v α = (f (e + 1) - ∑ α ∈ S, v α) - (f (e + 1) - L)` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ h2 h1`.
-/
theorem exists_adic_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (X : Type) (v : X → R), (∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite) →
    ∃ s : R, ∀ (e : ℕ) (S : Finset X), (∀ α ∉ S, v α ∈ maximalIdeal R ^ (e + 1)) →
      s - ∑ α ∈ S, v α ∈ maximalIdeal R ^ (e + 1) := by
  intro R _ _ _ hR X v hfin
  have hC : IsAdicComplete (maximalIdeal R) R := hR.1.2.2.2
  have hfin' : ∀ n : ℕ, {α | v α ∉ maximalIdeal R ^ n}.Finite := fun n =>
    (hfin n).subset fun α (hα : v α ∉ maximalIdeal R ^ n) (h : v α ∈ maximalIdeal R ^ (n + 1)) =>
      hα (Ideal.pow_le_pow_right (Nat.le_succ n) h)
  let F : ℕ → Finset X := fun n => (hfin' n).toFinset
  have hF : ∀ n, ∀ α ∉ F n, v α ∈ maximalIdeal R ^ n := by
    intro n α hα
    by_contra h
    exact hα ((hfin' n).mem_toFinset.2 h)
  let f : ℕ → R := fun n => ∑ α ∈ F n, v α
  have hsm : ∀ n : ℕ, maximalIdeal R ^ n • (⊤ : Submodule R R) = maximalIdeal R ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := (hC.toIsPrecomplete).prec (f := f) (by
    intro m n hmn
    rw [SModEq.sub_mem, hsm]
    exact sum_sub_sum_mem (maximalIdeal R ^ m) v (F m) (F n) (hF m)
      fun α hα => Ideal.pow_le_pow_right hmn (hF n α hα))
  refine ⟨L, fun e S hS => ?_⟩
  have h1 : f (e + 1) - L ∈ maximalIdeal R ^ (e + 1) := by
    have := hL (e + 1)
    rwa [SModEq.sub_mem, hsm] at this
  have h2 := sum_sub_sum_mem (maximalIdeal R ^ (e + 1)) v (F (e + 1)) S (hF (e + 1)) hS
  have : L - ∑ α ∈ S, v α = (f (e + 1) - ∑ α ∈ S, v α) - (f (e + 1) - L) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 h1

end GlobalTheory.Mum.AdicSum

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoeNeZeroOfNotMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts)

/- English proof (translation)
Introduce `S _ K ι _ Ω _ _ y k₀ hmod j hj k`. Use `set x := IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) with hx`. Use `set A := chartRingOver S x (fun _ => j) with hA`. Set `D : Set A` to `{d | ∃ b, y ⟨k, b⟩ ≠ 0 ∧ ∀ a, (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b⟩) ∈ A}`. Establish `hI : (Submodule.span A D : Ideal A) = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨q, hq, hIq⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hqp : q.IsPrime` using `hq.isPrime`. Establish `hsame : modelPts S y = modelPts S x` using `hmod.2`. Establish `hmem : locIn A q ∈ modelPts S x` using `⟨fun _ => j, fun _ => hj, q, hqp, rfl⟩`.

Rewrite `hmem` using `[← hsame]`. Take `⟨c, hc, p, hp, hEq⟩` from `hmem`. Establish `hr : ∀ a, y ⟨k, a⟩ / y ⟨k, c k⟩ ∈ locIn A q`. Introduce `a`. Rewrite using `[hEq]`.

Conclude with `(mem_locIn_chart_iff y c p).mpr ⟨⟨_, Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩⟩, 1, Ideal.one_notMem p, by simp⟩`. Use `choose nn dd hdd hnd using fun a => (mem_locIn_chart_iff x (fun _ => j) q).mp (hr a)`. Establish `hdq : (∏ a, dd a) ∉ q`. Rewrite using `[Ideal.IsPrime.prod_mem_iff]`. Introduce and unpack `⟨a, -, ha⟩`.

Conclude with `hdd a ha`. Apply `hdq` to reduce the goal to its premises. Apply `hIq` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨c k, hc k, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[hnd a]`. Establish `hda : (dd a : Ω) ≠ 0` using `coe_ne_zero_of_notMem x (fun _ => j) q (hdd a)`. Establish `e : ((∏ a', dd a' : A) : Ω) * ((nn a : Ω) / dd a) = (nn a : Ω) * ∏ a' ∈ Finset.univ.erase a, (dd a' : Ω)`. Rewrite using `[SubmonoidClass.coe_finsetProd, ← Finset.mul_prod_erase Finset.univ (fun a' => (dd a' : Ω)) (Finset.mem_univ a)]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `Subalgebra.mul_mem _ (nn a).2 (Subalgebra.prod_mem _ fun i _ => (dd i).2)`. Establish `key : ∀ t ∈ (Submodule.span A D : Ideal A), ∃ w : ι k → Ω, (∀ a b, y ⟨k, a⟩ * w b ∈ A) ∧ ∑ b, y ⟨k, b⟩ * w b = (t : Ω)`. Introduce `t ht`. Proceed by induction on `ht using Submodule.span_induction with`.

Consider the case `mem d hd`. Take `⟨b, hb, hdb⟩` from `hd`. Use `⟨Pi.single b ((d : Ω) / y ⟨k, b⟩), fun a b' => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : b' = b`. Substitute `h` using the available equality.

Simplify using `only [Pi.single_eq_same]`. Establish `e : y ⟨k, a⟩ * ((d : Ω) / y ⟨k, b'⟩) = (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b'⟩)` using `by ring`. Rewrite using `[e]`. Conclude with `hdb a`. Simplify using `only [Pi.single_eq_of_ne h, mul_zero]`.

Conclude with `Subalgebra.zero_mem _`. Simplify using `only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Clear the denominators using the available nonvanishing facts. Consider the case `zero => exact ⟨0, fun _ _ => by simp, by simp⟩`. Consider the case `add s t _ _ hs ht`.

Take `⟨w, hw, hws⟩` from `hs`. Take `⟨w', hw', hwt⟩` from `ht`. Use `⟨w + w', fun a b => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply, mul_add]`. Conclude with `Subalgebra.add_mem _ (hw a b) (hw' a b)`.

Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hws, hwt]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul r t _ ht`. Take `⟨w, hw, hwt⟩` from `ht`.

Use `⟨fun b => (r : Ω) * w b, fun a b => ?_, ?_⟩` and prove the remaining obligations. Establish `e : y ⟨k, a⟩ * ((r : Ω) * w b) = (r : Ω) * (y ⟨k, a⟩ * w b)` using `by ring`. Rewrite using `[e]`. Conclude with `Subalgebra.mul_mem _ r.2 (hw a b)`. Rewrite using `[smul_eq_mul, Subalgebra.coe_mul, ← hwt, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun b _ => by ring`. Take `⟨w, hw, hsum⟩` from `key 1 (by rw [hI]; exact Submodule.mem_top)`. Conclude with `⟨w, hw, by rw [hsum]; simp⟩`.
-/
theorem BlockGenOfModel.proof : BlockGenOfModel.Statement := by
  classical
  intro S _ K ι _ Ω _ _ y k₀ hmod j hj k
  set x := IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) with hx
  set A := chartRingOver S x (fun _ => j) with hA

  let D : Set A := {d | ∃ b, y ⟨k, b⟩ ≠ 0 ∧ ∀ a, (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b⟩) ∈ A}
  have hI : (Submodule.span A D : Ideal A) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal _ hne
    have hqp : q.IsPrime := hq.isPrime
    have hsame : modelPts S y = modelPts S x := hmod.2
    have hmem : locIn A q ∈ modelPts S x := ⟨fun _ => j, fun _ => hj, q, hqp, rfl⟩
    rw [← hsame] at hmem
    obtain ⟨c, hc, p, hp, hEq⟩ := hmem
    have hr : ∀ a, y ⟨k, a⟩ / y ⟨k, c k⟩ ∈ locIn A q := by
      intro a
      rw [hEq]
      exact (mem_locIn_chart_iff y c p).mpr
        ⟨⟨_, Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩⟩, 1, Ideal.one_notMem p, by simp⟩
    choose nn dd hdd hnd using fun a => (mem_locIn_chart_iff x (fun _ => j) q).mp (hr a)
    have hdq : (∏ a, dd a) ∉ q := by
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨a, -, ha⟩
      exact hdd a ha
    apply hdq
    apply hIq
    apply Submodule.subset_span
    refine ⟨c k, hc k, fun a => ?_⟩
    rw [hnd a]
    have hda : (dd a : Ω) ≠ 0 := coe_ne_zero_of_notMem x (fun _ => j) q (hdd a)
    have e : ((∏ a', dd a' : A) : Ω) * ((nn a : Ω) / dd a) =
        (nn a : Ω) * ∏ a' ∈ Finset.univ.erase a, (dd a' : Ω) := by
      rw [SubmonoidClass.coe_finsetProd, ← Finset.mul_prod_erase Finset.univ (fun a' => (dd a' : Ω))
        (Finset.mem_univ a)]
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _ (nn a).2 (Subalgebra.prod_mem _ fun i _ => (dd i).2)

  have key : ∀ t ∈ (Submodule.span A D : Ideal A), ∃ w : ι k → Ω,
      (∀ a b, y ⟨k, a⟩ * w b ∈ A) ∧ ∑ b, y ⟨k, b⟩ * w b = (t : Ω) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨b, hb, hdb⟩ := hd
      refine ⟨Pi.single b ((d : Ω) / y ⟨k, b⟩), fun a b' => ?_, ?_⟩
      · by_cases h : b' = b
        · subst h
          simp only [Pi.single_eq_same]
          have e : y ⟨k, a⟩ * ((d : Ω) / y ⟨k, b'⟩) = (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b'⟩) := by ring
          rw [e]
          exact hdb a
        · simp only [Pi.single_eq_of_ne h, mul_zero]
          exact Subalgebra.zero_mem _
      · simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        field_simp
    | zero => exact ⟨0, fun _ _ => by simp, by simp⟩
    | add s t _ _ hs ht =>
      obtain ⟨w, hw, hws⟩ := hs
      obtain ⟨w', hw', hwt⟩ := ht
      refine ⟨w + w', fun a b => ?_, ?_⟩
      · rw [Pi.add_apply, mul_add]
        exact Subalgebra.add_mem _ (hw a b) (hw' a b)
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hws, hwt]
        push_cast
        ring
    | smul r t _ ht =>
      obtain ⟨w, hw, hwt⟩ := ht
      refine ⟨fun b => (r : Ω) * w b, fun a b => ?_, ?_⟩
      · have e : y ⟨k, a⟩ * ((r : Ω) * w b) = (r : Ω) * (y ⟨k, a⟩ * w b) := by ring
        rw [e]
        exact Subalgebra.mul_mem _ r.2 (hw a b)
      · rw [smul_eq_mul, Subalgebra.coe_mul, ← hwt, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
  obtain ⟨w, hw, hsum⟩ := key 1 (by rw [hI]; exact Submodule.mem_top)
  exact ⟨w, hw, by rw [hsum]; simp⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

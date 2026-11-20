import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularLocalDomain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularQuotientIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing Ideal

/- English proof (translation)
Introduce `S _ _ h`. Proceed by induction on `h generalizing S with`. Consider the case `zero`. Introduce `x _ _`. Establish `hr : Set.range x = ∅` using `Set.range_eq_empty x`.

Rewrite using `[hr, Ideal.span_empty]`. Conclude with `IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot S).symm`. Consider the case `succ h ih`. Introduce `x hxm hind`. Establish `hx02 : x 0 ∉ maximalIdeal S ^ 2`.

Introduce `hc`. Establish `h1` using `hind (Pi.single 0 1) (by simpa [Pi.single_apply] using hc) 0`. Simplify using `at h1`. Establish `hne : span {x 0} ≠ ⊤` using `ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top ((span_singleton_le_iff_mem _).mpr (hxm 0))`. Establish `: Nontrivial (S ⧸ span {x 0})` using `Ideal.Quotient.nontrivial_iff.mpr hne`.

Establish `: IsLocalRing (S ⧸ span {x 0})` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`. Use `(GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient (hxm 0) hx02).1` as an intermediate fact. Use `set f := Ideal.Quotient.mk (span {x 0}) with hf`. Establish `hmax : (maximalIdeal S).map f = maximalIdeal (S ⧸ span {x 0})` using `map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective`. Set `y : Fin h → S ⧸ span {x 0}` to `fun i ↦ f (x i.succ)`.

Establish `hy : ∀ i, y i ∈ maximalIdeal (S ⧸ span {x 0})` using `fun i ↦ hmax ▸ Ideal.mem_map_of_mem f (hxm i.succ)`. Establish `hyind : ∀ b : Fin h → S ⧸ span {x 0}, ∑ i, b i * y i ∈ maximalIdeal (S ⧸ span {x 0}) ^ 2 → ∀ i, b i ∈ maximalIdeal (S ⧸ span {x 0})`. Introduce `b hb i`. Use `choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (I := span {x 0}) (b i)`. Establish `hsum : ∑ i, b i * y i = f (∑ i, a i * x i.succ)`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ ↦ by simp only [map_mul, ← ha i, hf, y]`. Rewrite `hb` using `[hsum, ← hmax, ← Ideal.map_pow, hf, Ideal.mem_quotient_iff_mem_sup]`. Take `⟨z, hz, w, hw, hzw⟩` from `Submodule.mem_sup.mp hb`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hw`.

Establish `h2` using `hind (Fin.cons (-c) a) (by`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Establish `: -c * x 0 + ∑ i, a i * x i.succ = z` using `by rw [← hzw]; ring`. Rewrite using `[this]`.

Conclude with `hz) i.succ`. Simplify using `only [Fin.cons_succ] at h2`. Rewrite using `[← ha i, ← hmax]`. Conclude with `Ideal.mem_map_of_mem _ h2`. Establish `hreg` using `ih (S ⧸ span {x 0}) y hy hyind`.

Use `set J : Ideal S := span (Set.range (fun i : Fin h ↦ x i.succ)) with hJ`. Establish `hspan : span (Set.range y) = J.map f`. Rewrite using `[hJ, Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hsup : span {x 0} ⊔ J = span (Set.range x)`.

Rewrite using `[hJ, ← Ideal.span_union]`. Use `congr 1`. Use extensionality with `s`. Simplify using `[Fin.exists_fin_succ, eq_comm]`. Conclude with `IsRegularLocalRing.of_ringEquiv (((Ideal.quotEquivOfEq hspan).trans (DoubleQuot.quotQuotEquivQuotSup (span {x 0}) J)).trans (Ideal.quotEquivOfEq hsup))`.
-/
theorem RegularQuotientIndependent.proof : RegularQuotientIndependent.Statement := by
  intro S _ _ h
  induction h generalizing S with
  | zero =>
    intro x _ _
    have hr : Set.range x = ∅ := Set.range_eq_empty x
    rw [hr, Ideal.span_empty]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot S).symm
  | succ h ih =>
    intro x hxm hind
    have hx02 : x 0 ∉ maximalIdeal S ^ 2 := by
      intro hc
      have h1 := hind (Pi.single 0 1) (by simpa [Pi.single_apply] using hc) 0
      simp at h1
    have hne : span {x 0} ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top
      ((span_singleton_le_iff_mem _).mpr (hxm 0))
    have : Nontrivial (S ⧸ span {x 0}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x 0}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have := (GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient (hxm 0) hx02).1
    set f := Ideal.Quotient.mk (span {x 0}) with hf
    have hmax : (maximalIdeal S).map f = maximalIdeal (S ⧸ span {x 0}) :=
      map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective
    let y : Fin h → S ⧸ span {x 0} := fun i ↦ f (x i.succ)
    have hy : ∀ i, y i ∈ maximalIdeal (S ⧸ span {x 0}) := fun i ↦
      hmax ▸ Ideal.mem_map_of_mem f (hxm i.succ)
    have hyind : ∀ b : Fin h → S ⧸ span {x 0}, ∑ i, b i * y i ∈ maximalIdeal (S ⧸ span {x 0}) ^ 2 →
        ∀ i, b i ∈ maximalIdeal (S ⧸ span {x 0}) := by
      intro b hb i
      choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (I := span {x 0}) (b i)
      have hsum : ∑ i, b i * y i = f (∑ i, a i * x i.succ) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by simp only [map_mul, ← ha i, hf, y]
      rw [hsum, ← hmax, ← Ideal.map_pow, hf, Ideal.mem_quotient_iff_mem_sup] at hb
      obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
      have h2 := hind (Fin.cons (-c) a) (by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have : -c * x 0 + ∑ i, a i * x i.succ = z := by rw [← hzw]; ring
        rw [this]; exact hz) i.succ
      simp only [Fin.cons_succ] at h2
      rw [← ha i, ← hmax]
      exact Ideal.mem_map_of_mem _ h2
    have hreg := ih (S ⧸ span {x 0}) y hy hyind
    set J : Ideal S := span (Set.range (fun i : Fin h ↦ x i.succ)) with hJ
    have hspan : span (Set.range y) = J.map f := by
      rw [hJ, Ideal.map_span, ← Set.range_comp]
      rfl
    have hsup : span {x 0} ⊔ J = span (Set.range x) := by
      rw [hJ, ← Ideal.span_union]
      congr 1
      ext s
      simp [Fin.exists_fin_succ, eq_comm]
    exact IsRegularLocalRing.of_ringEquiv (((Ideal.quotEquivOfEq hspan).trans
      (DoubleQuot.quotQuotEquivQuotSup (span {x 0}) J)).trans (Ideal.quotEquivOfEq hsup))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

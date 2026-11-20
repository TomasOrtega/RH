import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelProjectionLocallyInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.NormalModelGraph
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelProper
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveProperClosedFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology IndefiniteRowSideFullHecke.ComplexSets

/- English proof (translation)
Introduce `n J M w hJ hdim hw`. Use `choose a b hbJ hab using M.birational`. Use `set B : MvPolynomial (Fin n) ℂ := ∏ i, b i with hB`. Establish `hBJ : B ∉ J` using `fun h => by`. Use `hJ` as an intermediate fact.

Take `⟨i, -, hi⟩` from `Ideal.IsPrime.prod_mem_iff.1 h`. Conclude with `hbJ i hi`. Use `set S : Set (Fin n → ℂ) := ComplexSets.zeroSet J ∩ ComplexSets.zeroSet (Ideal.span {B}) with hS`. Establish `hSfin : S.Finite` using `CurveProperClosedFinite.proof n J _ hJ hdim (fun h => hBJ (h (Ideal.subset_span rfl)))`. Use `choose P hPm hP using M.integral`.

Use `set F : Set (Fin n ⊕ Fin M.m → ℂ) := {z | z ∈ zeroSetIn M.ideal ∧ firstCoords z ∈ S} with hF`. Establish `hFfin : F.Finite`. Establish `hT : (⋃ x ∈ S, ({x} : Set (Fin n → ℂ)) ×ˢ Set.pi Set.univ (fun i => {y : ℂ | ((P i).map (eval x)).IsRoot y})).Finite` using `hSfin.biUnion fun x _ => (Set.finite_singleton x).prod (Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map (eval x)).ne_zero)`. Use `(hT.image fun p => Sum.elim p.1 p.2).subset ?_` and prove the remaining obligations. Introduce `z hz`.

Use `⟨(firstCoords z, fun i => z (Sum.inr i)), ?_, ?_⟩` and prove the remaining obligations. Use `Set.mem_biUnion hz.2 ⟨rfl, fun i _ => ?_⟩` and prove the remaining obligations. Conclude with `isRoot_map_eval_of_mem_zeroSetIn hz.1 i (P i) (hP i)`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `rcases s with j | i <;> rfl`.

Use `⟨(F \ {w})ᶜ, (hFfin.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl), ?_⟩` and prove the remaining obligations. Establish `hnear : ∀ z ∈ zeroSetIn M.ideal ∩ (F \ {w})ᶜ, (∃ i, eval (firstCoords z) (b i) = 0) → z = w`. Introduce and unpack `z ⟨hz, hzU⟩ ⟨i, hi⟩`. Establish `hxJ : firstCoords z ∈ ComplexSets.zeroSet J` using `fun q hq => by`. Rewrite `hq` using `[← M.comap_eq, Ideal.mem_comap]`.

Establish `h` using `hz _ hq`. Rewrite `h` using `[eval_rename]`. Conclude with `h`. Establish `hxB : firstCoords z ∈ ComplexSets.zeroSet (Ideal.span {B})` using `fun q hq => by`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton.1 hq`.

Rewrite using `[eval_mul, hB, map_prod, Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]`. Assume the negation of the conclusion as `hne`. Conclude with `hzU ⟨⟨hz, hxJ, hxB⟩, hne⟩`. Introduce `z hz z' hz' hzz`. Distinguish the cases in `hbz : ∀ i, eval (firstCoords z) (b i) ≠ 0`.

Establish `hbz' : ∀ i, eval (firstCoords z') (b i) ≠ 0` using `hzz ▸ hbz`. Rewrite using `[M.eq_graph_of_mem_zeroSetIn a b hab z hz.1 hbz, M.eq_graph_of_mem_zeroSetIn a b hab z' hz'.1 hbz', hzz]`. Simplify using `only [not_forall, not_not] at hbz`. Establish `hbz' : ∃ i, eval (firstCoords z') (b i) = 0` using `hzz ▸ hbz`. Rewrite using `[hnear z hz hbz, hnear z' hz' hbz']`.
-/
theorem NormalModelProjectionLocallyInjective.proof : NormalModelProjectionLocallyInjective.Statement := by
  intro n J M w hJ hdim hw
  choose a b hbJ hab using M.birational
  set B : MvPolynomial (Fin n) ℂ := ∏ i, b i with hB
  have hBJ : B ∉ J := fun h => by
    have := hJ
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hbJ i hi

  set S : Set (Fin n → ℂ) := ComplexSets.zeroSet J ∩ ComplexSets.zeroSet (Ideal.span {B}) with hS
  have hSfin : S.Finite := CurveProperClosedFinite.proof n J _ hJ hdim
    (fun h => hBJ (h (Ideal.subset_span rfl)))

  choose P hPm hP using M.integral
  set F : Set (Fin n ⊕ Fin M.m → ℂ) := {z | z ∈ zeroSetIn M.ideal ∧ firstCoords z ∈ S} with hF
  have hFfin : F.Finite := by
    have hT : (⋃ x ∈ S, ({x} : Set (Fin n → ℂ)) ×ˢ
        Set.pi Set.univ (fun i => {y : ℂ | ((P i).map (eval x)).IsRoot y})).Finite :=
      hSfin.biUnion fun x _ => (Set.finite_singleton x).prod
        (Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot ((hPm i).map (eval x)).ne_zero)
    refine (hT.image fun p => Sum.elim p.1 p.2).subset ?_
    intro z hz
    refine ⟨(firstCoords z, fun i => z (Sum.inr i)), ?_, ?_⟩
    · refine Set.mem_biUnion hz.2 ⟨rfl, fun i _ => ?_⟩
      exact isRoot_map_eval_of_mem_zeroSetIn hz.1 i (P i) (hP i)
    · funext s
      rcases s with j | i <;> rfl
  refine ⟨(F \ {w})ᶜ, (hFfin.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds
    (fun h => h.2 rfl), ?_⟩

  have hnear : ∀ z ∈ zeroSetIn M.ideal ∩ (F \ {w})ᶜ, (∃ i, eval (firstCoords z) (b i) = 0) → z = w := by
    rintro z ⟨hz, hzU⟩ ⟨i, hi⟩
    have hxJ : firstCoords z ∈ ComplexSets.zeroSet J := fun q hq => by
      rw [← M.comap_eq, Ideal.mem_comap] at hq
      have h := hz _ hq
      rw [eval_rename] at h
      exact h
    have hxB : firstCoords z ∈ ComplexSets.zeroSet (Ideal.span {B}) := fun q hq => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hq
      rw [eval_mul, hB, map_prod, Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
    by_contra hne
    exact hzU ⟨⟨hz, hxJ, hxB⟩, hne⟩
  intro z hz z' hz' hzz
  by_cases hbz : ∀ i, eval (firstCoords z) (b i) ≠ 0
  · have hbz' : ∀ i, eval (firstCoords z') (b i) ≠ 0 := hzz ▸ hbz
    rw [M.eq_graph_of_mem_zeroSetIn a b hab z hz.1 hbz, M.eq_graph_of_mem_zeroSetIn a b hab z' hz'.1 hbz', hzz]
  · simp only [not_forall, not_not] at hbz
    have hbz' : ∃ i, eval (firstCoords z') (b i) = 0 := hzz ▸ hbz
    rw [hnear z hz hbz, hnear z' hz' hbz']

end GroundTheory.Heights₂.Heights

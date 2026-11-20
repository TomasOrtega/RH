import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.BdBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
open UpperTheory.V.Lit.Geo NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

/- English proof (translation)
Introduce `E _ _ _ a Ξ q α`. Take `⟨T, B, hB, hT⟩` from `bdBasis E a Ξ q`. Establish `hq` using `(qhtFacts E a).1`. Establish `hr : ∀ g, qht (E` using `E) (a := a) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = qht g := fun g => by`. Take `⟨t, ht⟩` from `(retrFacts E a).1 g`.

Establish `h` using `(qhtFacts E a).2.1 1 t g`. Rewrite `h` using `[map_one, one_mul]`. Rewrite using `[ht, h]`. Establish `hs : ∀ (C : _ → ℝ), ∀ X ∈ T, C X ≤ ∑ X ∈ T, |C X|` using `fun C X hX => (le_abs_self _).trans (Finset.single_le_sum (f := fun X => |C X|) (fun _ _ => abs_nonneg _) hX)`. Use `⟨fun ⟨N, h⟩ => ?_, fun h N => ?_⟩` and prove the remaining obligations.

Use `choose C hC using h`. Establish `h0 : 0 ≤ ∑ X ∈ T, |C X|` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Use `⟨N, B * ∑ X ∈ T, |C X|, mul_nonneg hB h0, fun g => ?_⟩` and prove the remaining obligations. Establish `q0 : 0 < qht g` using `one_pos.trans_le (hq g)`. Rewrite using `[mul_assoc]`.

Use `hT α g _ (by positivity) fun X hX => (hC X _).trans ?_` and prove the remaining obligations. Rewrite using `[hr]`. Conclude with `mul_le_mul_of_nonneg_right (hs C X hX) (by positivity)`. Use `choose C hC using fun X => h X N`. Establish `h0 : 0 ≤ ∑ X ∈ T, |C X|` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`.

Use `⟨B * ∑ X ∈ T, |C X|, mul_nonneg hB h0, fun g => ?_⟩` and prove the remaining obligations. Establish `q0 : 0 < qht g` using `one_pos.trans_le (hq g)`. Rewrite using `[mul_div_assoc]`. Use `hT α g _ (by positivity) fun X hX => ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀ (by positivity), ← hr g]`.

Conclude with `(hC X _).trans (hs C X hX)`.
-/
theorem UpperTheory.V.Lit.Geo.bdGrowth :
    BdGrowth := by
  intro E _ _ _ a Ξ q α
  obtain ⟨T, B, hB, hT⟩ := bdBasis E a Ξ q
  have hq := (qhtFacts E a).1
  have hr : ∀ g, qht (E := E) (a := a)
      (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = qht g := fun g => by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    have h := (qhtFacts E a).2.1 1 t g
    rw [map_one, one_mul] at h
    rw [ht, h]
  have hs : ∀ (C : _ → ℝ), ∀ X ∈ T, C X ≤ ∑ X ∈ T, |C X| := fun C X hX =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun X => |C X|) (fun _ _ => abs_nonneg _) hX)
  refine ⟨fun ⟨N, h⟩ => ?_, fun h N => ?_⟩
  · choose C hC using h
    have h0 : 0 ≤ ∑ X ∈ T, |C X| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨N, B * ∑ X ∈ T, |C X|, mul_nonneg hB h0, fun g => ?_⟩
    have q0 : 0 < qht g := one_pos.trans_le (hq g)
    rw [mul_assoc]
    refine hT α g _ (by positivity) fun X hX => (hC X _).trans ?_
    rw [hr]
    exact mul_le_mul_of_nonneg_right (hs C X hX) (by positivity)
  · choose C hC using fun X => h X N
    have h0 : 0 ≤ ∑ X ∈ T, |C X| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨B * ∑ X ∈ T, |C X|, mul_nonneg hB h0, fun g => ?_⟩
    have q0 : 0 < qht g := one_pos.trans_le (hq g)
    rw [mul_div_assoc]
    refine hT α g _ (by positivity) fun X hX => ?_
    rw [le_div_iff₀ (by positivity), ← hr g]
    exact (hC X _).trans (hs C X hX)

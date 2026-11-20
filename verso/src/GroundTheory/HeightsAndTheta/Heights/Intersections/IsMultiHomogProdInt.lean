import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverChart
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GenericPointsAvoidBadLocus

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K] in

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `m hm k`. Rewrite `hm` using `[Finset.prod_empty, MvPolynomial.support_one, Finset.mem_singleton]`. Substitute `hm` using the available equality.

Simplify using the standard rewrite rules. Consider the case `insert b s hb ih`. Rewrite using `[Finset.prod_insert hb, Finset.sum_insert hb]`. Introduce `m hm k`. Take `⟨m1, hm1, m2, hm2, rfl⟩` from `Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)`.

Establish `h1` using `h b (Finset.mem_insert_self b s) m1 hm1 k`. Establish `h2` using `ih (fun b' hb' => h b' (Finset.mem_insert_of_mem hb')) m2 hm2 k`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, h1, h2]`.
-/
theorem isMultiHomog_prod_int {β : Type*} (s : Finset β) (f : β → MRing ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m hm k
    rw [Finset.prod_empty, MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    intro m hm k
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    have h1 := h b (Finset.mem_insert_self b s) m1 hm1 k
    have h2 := ih (fun b' hb' => h b' (Finset.mem_insert_of_mem hb')) m2 hm2 k
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, h1, h2]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

/- English proof (translation)
Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨q, rfl⟩`. Establish `hq : G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ = (G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) / (G.x' ⟨q.1.1, j q.1⟩ / G.x' ⟨q.1.1, i q.1⟩)` using `(div_div_div_cancel_right₀ (hi q.1) _ _).symm`. Use `show G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ ∈ _`. Rewrite using `[hq]`.

Conclude with `div_mem (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩) (IntermediateField.subset_adjoin _ _ ⟨⟨q.1, j q.1⟩, rfl⟩)`.
-/
theorem adjoin_chart_le {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
    (G : GenFibre v P') (i j : ∀ k : FibreBlock κ, ι' k.1) (hi : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) :
    IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) ≤
      IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨q, rfl⟩
  have hq : G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ =
      (G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) / (G.x' ⟨q.1.1, j q.1⟩ / G.x' ⟨q.1.1, i q.1⟩) :=
    (div_div_div_cancel_right₀ (hi q.1) _ _).symm
  show G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩ ∈ _
  rw [hq]
  exact div_mem (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩)
    (IntermediateField.subset_adjoin _ _ ⟨⟨q.1, j q.1⟩, rfl⟩)

end GenericPointsAvoidBadLocus

open GenericPointsAvoidBadLocus in

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' n G i hv hP' hZ hi`. Set `C` to `{j : ∀ k : FibreBlock κ, ι' k.1 // ∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0}`. Use `choose D a hD hDZ hpts using fun j : C => hChart K ι K' ι' κ v P' n G j.1 hv hP' hZ j.2`. Establish `hprime : (imageZ v P').IsPrime` using `hZ.2.1.1`. Use `⟨∏ j, D j, ∑ j, a j, isMultiHomog_prod_int _ _ _ fun j _ => hD j, fun hmem => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨j, -, hj⟩` from `Ideal.IsPrime.prod_mem_iff.mp hmem`. Conclude with `hDZ j hj`. Introduce `z hz hDz`. Establish `hDj : ∀ j : C, eval z (map (Int.castRingHom ℂ) (D j)) ≠ 0`. Introduce `j h0`.

Apply `hDz` to reduce the goal to its premises. Rewrite using `[map_prod, map_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ j) h0`. Set `i0 : C` to `⟨i, hi⟩`. Establish `hEq : ∀ j : C, ptsOverChart P' κ v i z = ptsOverChart P' κ v j.1 z`.

Introduce `j`. Establish `hci : (ptsOverChart P' κ v i z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩))` using `(hpts i0 z hz (hDj i0)).2.1`. Take `⟨hfin, hcj, -⟩` from `hpts j z hz (hDj j)`. Establish `hsub : ptsOverChart P' κ v i z ⊆ ptsOverChart P' κ v j.1 z`. Introduce and unpack `O ⟨z', hz', rfl, hw, hc⟩`.

Conclude with `⟨z', hz', rfl, hw, fun k => (hpts i0 z hz (hDj i0)).2.2 z' hz' hw hc ⟨k, j.1 k⟩ (j.2 k)⟩`. Use `Set.eq_of_subset_of_ncard_le hsub (le_of_eq ?_) hfin` and prove the remaining obligations. Rewrite using `[hcj, hci, le_antisymm (adjoin_chart_le G i j.1 hi) (adjoin_chart_le G j.1 i j.2)]`. Establish `hall : ptsOverPt P' v z = ptsOverChart P' κ v i z`. Use extensionality with `O`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z', hz', rfl, hw⟩ choose ℓ hℓ using fun k : FibreBlock κ => hz'.1 k.1`. Establish `hgen : ∀ k : FibreBlock κ, G.x' ⟨k.1, ℓ k⟩ ≠ 0`. Introduce `k h0`. Apply `hℓ k` to reduce the goal to its premises.

Establish `hmem : (X ⟨k.1, ℓ k⟩ : MRing ι') ∈ P'`. Rewrite using `[← G.genericFibre_ker_target, RingHom.mem_ker]`. Simplify using `using h0`. Simplify using `using hz'.2 _ hmem`. Rewrite using `[hEq ⟨ℓ, hgen⟩]`.

Conclude with `⟨z', hz', rfl, hw, hℓ⟩`. Introduce and unpack `⟨z', hz', rfl, hw, -⟩`. Conclude with `⟨z', hz', rfl, hw⟩`. Rewrite using `[hall]`. Conclude with `(hpts i0 z hz (hDj i0)).2.1`.
-/
theorem GenericPointsAvoidBadLocus.proof (hChart : GenericPointsInAffineChart.Statement) : GenericPointsAvoidBadLocus.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G i hv hP' hZ hi
  classical
  let C := {j : ∀ k : FibreBlock κ, ι' k.1 // ∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0}
  choose D a hD hDZ hpts using fun j : C => hChart K ι K' ι' κ v P' n G j.1 hv hP' hZ j.2
  have hprime : (imageZ v P').IsPrime := hZ.2.1.1
  refine ⟨∏ j, D j, ∑ j, a j, isMultiHomog_prod_int _ _ _ fun j _ => hD j, fun hmem => ?_, ?_⟩
  · obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hDZ j hj
  intro z hz hDz
  have hDj : ∀ j : C, eval z (map (Int.castRingHom ℂ) (D j)) ≠ 0 := by
    intro j h0
    apply hDz
    rw [map_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) h0
  let i0 : C := ⟨i, hi⟩
  have hEq : ∀ j : C, ptsOverChart P' κ v i z = ptsOverChart P' κ v j.1 z := by
    intro j
    have hci : (ptsOverChart P' κ v i z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩)) :=
      (hpts i0 z hz (hDj i0)).2.1
    obtain ⟨hfin, hcj, -⟩ := hpts j z hz (hDj j)
    have hsub : ptsOverChart P' κ v i z ⊆ ptsOverChart P' κ v j.1 z := by
      rintro O ⟨z', hz', rfl, hw, hc⟩
      exact ⟨z', hz', rfl, hw, fun k => (hpts i0 z hz (hDj i0)).2.2 z' hz' hw hc ⟨k, j.1 k⟩ (j.2 k)⟩
    refine Set.eq_of_subset_of_ncard_le hsub (le_of_eq ?_) hfin
    rw [hcj, hci, le_antisymm (adjoin_chart_le G i j.1 hi) (adjoin_chart_le G j.1 i j.2)]
  have hall : ptsOverPt P' v z = ptsOverChart P' κ v i z := by
    ext O
    constructor
    · rintro ⟨z', hz', rfl, hw⟩
      choose ℓ hℓ using fun k : FibreBlock κ => hz'.1 k.1
      have hgen : ∀ k : FibreBlock κ, G.x' ⟨k.1, ℓ k⟩ ≠ 0 := by
        intro k h0
        apply hℓ k
        have hmem : (X ⟨k.1, ℓ k⟩ : MRing ι') ∈ P' := by
          rw [← G.genericFibre_ker_target, RingHom.mem_ker]
          simpa using h0
        simpa using hz'.2 _ hmem
      rw [hEq ⟨ℓ, hgen⟩]
      exact ⟨z', hz', rfl, hw, hℓ⟩
    · rintro ⟨z', hz', rfl, hw, -⟩
      exact ⟨z', hz', rfl, hw⟩
  rw [hall]
  exact (hpts i0 z hz (hDj i0)).2.1

end GroundTheory.Heights₂.Heights.Inter

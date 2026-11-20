import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation
import Formalism.FrobeniusOrbits.HostCorollaries

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.GlobalTheoryTheory

/- English proof (translation)
Conclude with `⟨Formalism.FrobeniusOrbits.hostOrbits, Formalism.FrobeniusOrbits.hostOrbitsPlaces, Formalism.FrobeniusOrbits.hostOrbitsFin.2.2.1, Formalism.FrobeniusOrbits.hostOrders⟩`.
-/
theorem orbits_and_orders_hold : LocalQuadraticParts.HostOrbitConditions := by
  exact ⟨Formalism.FrobeniusOrbits.hostOrbits, Formalism.FrobeniusOrbits.hostOrbitsPlaces, Formalism.FrobeniusOrbits.hostOrbitsFin.2.2.1, Formalism.FrobeniusOrbits.hostOrders⟩

/- English proof (translation)
Conclude with `Formalism.FrobeniusOrbits.Final.host_places.2.2.1`.
-/
theorem lemma_on_tops_holds : LocalQuadraticParts.TopsChoiceLemma := by
  exact Formalism.FrobeniusOrbits.Final.host_places.2.2.1

/- English proof (translation)
Rewrite using `[← Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices.ordH_eq]`. Use `congr 1`. Unfold `LocalQuadraticParts.hclP hOf`. Establish `hc2 : l.Coprime 2` using `(Nat.coprime_primes hl Nat.prime_two).2 h2`. Establish `hc : l.Coprime (2 ^ (e + 2))` using `Nat.Coprime.pow_right _ hc2`.

Rewrite using `[dif_pos hc, dif_pos hc2]`.
-/
theorem ord_hclP (e l : ℕ) (hl : l.Prime) (h2 : l ≠ 2) :
    orderOf (LocalQuadraticParts.hclP e l) = ordH (hOf e l) := by
  rw [← Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices.ordH_eq]
  congr 1
  unfold LocalQuadraticParts.hclP hOf
  have hc2 : l.Coprime 2 := (Nat.coprime_primes hl Nat.prime_two).2 h2
  have hc : l.Coprime (2 ^ (e + 2)) := Nat.Coprime.pow_right _ hc2
  rw [dif_pos hc, dif_pos hc2]

/- English proof (translation)
Take `⟨-, h2, h3, h4⟩` from `h`. Establish `hc : ((2 ^ D.R.e : ℕ) : ℝ) = (2 : ℝ) ^ D.R.e` using `by norm_num`. Use `⟨fun J l hJ hl hl2 ho => ?_, fun J S hJ hS => ?_, fun J Y S hJ hY hS => ?_⟩` and prove the remaining obligations. Establish `h5` using `h2 J (by exact_mod_cast hJ) l hl hl2 (by rw [← ord_hclP _ l hl hl2]; exact_mod_cast ho)`. Rewrite `h5` using `[hc]`.

Conclude with `h5`. Establish `h5` using `h3 J (by exact_mod_cast hJ) S (fun l hlS => ⟨(hS l hlS).1, (hS l hlS).2.1, by`. Rewrite using `[← ord_hclP _ l (hS l hlS).1 (hS l hlS).2.1]`. Conclude with `(hS l hlS).2.2⟩)` after adjusting the coercions. Rewrite `h5` using `[hc]`.

Conclude with `h5`. Establish `hsub : S ⊆ (Finset.range (⌊Y⌋₊ + 1)).filter (fun l => l.Prime ∧ l ≠ 2 ∧ (ordH (hOf D.R.e l) : ℝ) ≤ J)`. Introduce `l hlS`. Take `⟨hl, hl2, hlY, ho⟩` from `hS l hlS`. Rewrite using `[Finset.mem_filter, Finset.mem_range]`.

Use `⟨Nat.lt_succ_of_le (Nat.le_floor hlY), hl, hl2, ?_⟩` and prove the remaining obligations. Rewrite using `[← ord_hclP _ l hl hl2]`. Conclude with `ho` after adjusting the coercions. Establish `h5` using `h4 J (by exact_mod_cast hJ) Y`. Rewrite `h5` using `[hc]`.

Use `le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun l _ _ => ?_) h5` and prove the remaining obligations. Conclude with `div_nonneg (Real.log_natCast_nonneg l) (Nat.cast_nonneg l)`.
-/
theorem dyadic_order_consequences (D : D7) (C : ℝ) (h : UnusedSlot33.Conclusion4 D C) : LocalQuadraticParts.OrderConsequences D C := by
  obtain ⟨-, h2, h3, h4⟩ := h
  have hc : ((2 ^ D.R.e : ℕ) : ℝ) = (2 : ℝ) ^ D.R.e := by norm_num
  refine ⟨fun J l hJ hl hl2 ho => ?_, fun J S hJ hS => ?_, fun J Y S hJ hY hS => ?_⟩
  · have h5 := h2 J (by exact_mod_cast hJ) l hl hl2 (by rw [← ord_hclP _ l hl hl2]; exact_mod_cast ho)
    rw [hc] at h5
    exact h5
  · have h5 := h3 J (by exact_mod_cast hJ) S (fun l hlS => ⟨(hS l hlS).1, (hS l hlS).2.1, by
      rw [← ord_hclP _ l (hS l hlS).1 (hS l hlS).2.1]; exact_mod_cast (hS l hlS).2.2⟩)
    rw [hc] at h5
    exact h5
  · have hsub : S ⊆ (Finset.range (⌊Y⌋₊ + 1)).filter
        (fun l => l.Prime ∧ l ≠ 2 ∧ (ordH (hOf D.R.e l) : ℝ) ≤ J) := by
      intro l hlS
      obtain ⟨hl, hl2, hlY, ho⟩ := hS l hlS
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le (Nat.le_floor hlY), hl, hl2, ?_⟩
      rw [← ord_hclP _ l hl hl2]
      exact_mod_cast ho
    have h5 := h4 J (by exact_mod_cast hJ) Y
    rw [hc] at h5
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun l _ _ => ?_) h5
    exact div_nonneg (Real.log_natCast_nonneg l) (Nat.cast_nonneg l)

/- English proof (translation)
Conclude with `⟨C, fun x i => dyadic_order_consequences _ C (h x i)⟩`.
-/
theorem family_dyadic_order_consequences {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ)
    (h : ∀ x (i : Fm.Ix x), UnusedSlot33.Conclusion4 (Fm.D x i) C) : LocalQuadraticParts.SmallOrderPrimeBoundsFamily Fm := by
  exact ⟨C, fun x i => dyadic_order_consequences _ C (h x i)⟩

/- English proof (translation)
Take `⟨x0, hx0⟩` from `h`. Use `⟨x0, fun x hx hx1 i => ⟨⟨Fm.nprimeDef x hx1 i, Fm.nuDef x hx1 i, fun p hp => Fm.drop_iff x hx1 i p hp, fun w => Fm.fills x hx1 i w⟩, hx0 x hx i⟩⟩` and prove the remaining obligations.
-/
theorem full_rank_family_of_eventually_nuFull {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).NuFull) : LocalQuadraticParts.FullRankFamily Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx hx1 i => ⟨⟨Fm.nprimeDef x hx1 i, Fm.nuDef x hx1 i, fun p hp => Fm.drop_iff x hx1 i p hp,
    fun w => Fm.fills x hx1 i w⟩, hx0 x hx i⟩⟩

end Formalism.MainNotions.J

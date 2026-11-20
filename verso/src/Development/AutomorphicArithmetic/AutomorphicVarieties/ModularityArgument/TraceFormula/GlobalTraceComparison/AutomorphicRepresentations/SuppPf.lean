import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

/- English proof (translation)
Introduce `hB hZ hK hP hKer E _ _ _ n ι _ s m R hR x y hxy`. Take `⟨hac, hmul, -, -, hone, -, hldth, hthth, hthmul, hrat, -, hthc⟩` from `hB E n s.pos`. Establish `hl1 : ldet (1 : H E n 0) = 0`. Establish `h` using `hac 0`. Rewrite `h` using `[hone]`. Then use the resulting hypothesis.

Establish `hlinv : ∀ z : H E n 0, ldet z⁻¹ = -ldet z`. Introduce `z`. Establish `h` using `hmul z z⁻¹`. Rewrite `h` using `[mul_inv_cancel, hl1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hf : Continuous fun w : H E n 0 => m.G x (th w)` using `by show Continuous fun w : H E n 0 => ∑ i, inner ℂ (s.k₁ x i) (m.Uπ (s.k₂ (th w) i))`. Use `continuous_finset_sum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `continuous_const.inner (m.Uπ.continuous.comp (((s.vecs.cont i).2).comp hthc))`. Establish `hinv : Inv fun w : H E n 0 => m.G x (th w)`. Introduce `γ w`.

Establish `h` using `(hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th w)`. Use `show Gk s.k₁ s.k₂ m.Uπ x (th ((γ : H E n 0) * w)) = Gk s.k₁ s.k₂ m.Uπ x (th w)`. Rewrite using `[hthmul]`. Unfold `Gk`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[show s.k₂ (th (γ : H E n 0) * th w) = s.k₂ (th w) from h]`. Take `⟨δ, hδ⟩ : ∃ δ, δ = (|ldet x + ldet y| - R) / 2` from `⟨_, rfl⟩`. Establish `hδ0 : 0 < δ` using `by rw [hδ]; linarith`. Establish `key` using `hZ E n s.D (fun w => m.G x (th w)) (Set.Ioo (-ldet y - δ) (-ldet y + δ)) hf hinv isOpen_Ioo ?_ (th y) ?_`. Simplify `key` using `only [hthth]`.

Introduce `v hv`. Use `((hKer E n ι s m v x).2).trans ?_` and prove the remaining obligations. Establish `hPv` using `hP E n s.D s.π (-ldet y - δ) (-ldet y + δ) v (hv.mono fun w h h' => h fun hI => h' (Set.Ioo_subset_Icc_self hI))`. Apply `integral_eq_zero_of_ae` to reduce the goal to its premises. Use `filter_upwards [hPv] with w hw`.

Distinguish the cases in `hI : ldet w ∈ Set.Icc (-ldet y - δ) (-ldet y + δ)`. Establish `hk : kerH m.φ x w = 0`. Unfold `kerH`. Use `finsum_eq_zero_of_forall_eq_zero fun γ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `h1` using `hR _ hne`. Rewrite `h1` using `[hmul, hmul, hlinv, (hrat γ).1]`. Take `⟨a1, a2⟩` from `abs_le.mp h1`. Take `⟨b1, b2⟩` from `hI`. Apply the tactic sequence `rcases abs_cases (ldet x + ldet y) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hδ <;> linarith`.

Simplify using `[hk]`. Simplify using `[hw hI]`. Rewrite using `[hldth]`. Conclude with `⟨by linarith, by linarith⟩`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.supp_pf :
    Basic → Zero → KInv → PSupp → Ker → Supp := by
  intro hB hZ hK hP hKer E _ _ _ n ι _ s m R hR x y hxy
  obtain ⟨hac, hmul, -, -, hone, -, hldth, hthth, hthmul, hrat, -, hthc⟩ := hB E n s.pos
  have hl1 : ldet (1 : H E n 0) = 0 := by
    have h := hac 0
    rwa [hone] at h
  have hlinv : ∀ z : H E n 0, ldet z⁻¹ = -ldet z := by
    intro z
    have h := hmul z z⁻¹
    rw [mul_inv_cancel, hl1] at h
    linarith
  have hf : Continuous fun w : H E n 0 => m.G x (th w) := by
    show Continuous fun w : H E n 0 => ∑ i, inner ℂ (s.k₁ x i) (m.Uπ (s.k₂ (th w) i))
    refine continuous_finset_sum _ fun i _ => ?_
    exact continuous_const.inner (m.Uπ.continuous.comp (((s.vecs.cont i).2).comp hthc))
  have hinv : Inv fun w : H E n 0 => m.G x (th w) := by
    intro γ w
    have h := (hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th w)
    show Gk s.k₁ s.k₂ m.Uπ x (th ((γ : H E n 0) * w)) = Gk s.k₁ s.k₂ m.Uπ x (th w)
    rw [hthmul]
    unfold Gk
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show s.k₂ (th (γ : H E n 0) * th w) = s.k₂ (th w) from h]
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (|ldet x + ldet y| - R) / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have key := hZ E n s.D (fun w => m.G x (th w)) (Set.Ioo (-ldet y - δ) (-ldet y + δ)) hf hinv isOpen_Ioo ?_ (th y) ?_
  · simpa only [hthth] using key
  · intro v hv
    refine ((hKer E n ι s m v x).2).trans ?_
    have hPv := hP E n s.D s.π (-ldet y - δ) (-ldet y + δ) v
      (hv.mono fun w h h' => h fun hI => h' (Set.Ioo_subset_Icc_self hI))
    apply integral_eq_zero_of_ae
    filter_upwards [hPv] with w hw
    by_cases hI : ldet w ∈ Set.Icc (-ldet y - δ) (-ldet y + δ)
    · have hk : kerH m.φ x w = 0 := by
        unfold kerH
        refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
        by_contra hne
        have h1 := hR _ hne
        rw [hmul, hmul, hlinv, (hrat γ).1] at h1
        obtain ⟨a1, a2⟩ := abs_le.mp h1
        obtain ⟨b1, b2⟩ := hI
        rcases abs_cases (ldet x + ldet y) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hδ <;> linarith
      simp [hk]
    · simp [hw hI]
  · rw [hldth]
    exact ⟨by linarith, by linarith⟩

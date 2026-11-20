import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

/- English proof (translation)
Introduce `P L hTT hL X hX b hb`. Establish `hLaw : (MA.DQ P).Laws P.TT` using `Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT`. Establish `hS` using `Formalism.FourierDecayAlt.P.MAx3.H.hyp_model hL hLaw`. Establish `hV` using `Formalism.FourierDecayAlt.P.MAx3.K.hypV_model hL hLaw`. Establish `gen : ∀ b' ∈ Submonoid.closure (MA.bddSet P L), ∀ X' ∈ MA.hatSet P L, b' * X' ∈ Submodule.span ℂ (bddHat P L)` using `fun b' hb' X' hX' => Submodule.subset_span ⟨b', hb', X', hX', rfl⟩`.

Establish `mA : ∀ y, L.Ahat y ∈ MA.hatSet P L` using `fun y => Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))`. Establish `mR : ∀ y, L.R0 y ∈ MA.hatSet P L` using `fun y => Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))`. Establish `mAv : ∀ y, L.Ahatv y ∈ MA.hatSet P L` using `fun y => Or.inl (Or.inr ⟨y, rfl⟩)`. Establish `mRv : ∀ y, L.R0v y ∈ MA.hatSet P L` using `fun y => Or.inr ⟨y, rfl⟩`. Establish `sumA : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) → (ts.map fun x => x.1 • (x.2.1 * L.Ahat x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L)`.

Introduce `ts hts`. Use `list_sum_mem fun u hu => ?_` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `List.mem_map.1 hu`. Conclude with `Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mA _))`. Establish `sumAv : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) → (ts.map fun x => x.1 • (x.2.1 * L.Ahatv x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L)`.

Introduce `ts hts`. Use `list_sum_mem fun u hu => ?_` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `List.mem_map.1 hu`. Conclude with `Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mAv _))`. Break down `hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)` into its components or cases.

Take `⟨t, ht⟩` from `hS.ahat b hb`. Rewrite using `[ht y]`. Conclude with `gen _ hb _ (mA _)`. Take `⟨t, ts, hts, he⟩` from `hS.r0 b hb y`. Rewrite using `[he]`.

Conclude with `Submodule.add_mem _ (gen _ hb _ (mR _)) (sumA ts hts)`. Take `⟨t, ht⟩` from `hV.ahatv b hb`. Rewrite using `[ht y]`. Conclude with `gen _ hb _ (mAv _)`. Take `⟨t, ts, hts, he⟩` from `hV.r0v b hb y`.

Rewrite using `[he]`. Conclude with `Submodule.add_mem _ (gen _ hb _ (mRv _)) (sumAv ts hts)`.
-/
theorem hat_bounded_decay_holds : JDHatBdd := by
  intro P L hTT hL X hX b hb
  have hLaw : (MA.DQ P).Laws P.TT := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT
  have hS := Formalism.FourierDecayAlt.P.MAx3.H.hyp_model hL hLaw
  have hV := Formalism.FourierDecayAlt.P.MAx3.K.hypV_model hL hLaw
  have gen : ∀ b' ∈ Submonoid.closure (MA.bddSet P L), ∀ X' ∈ MA.hatSet P L,
      b' * X' ∈ Submodule.span ℂ (bddHat P L) := fun b' hb' X' hX' =>
    Submodule.subset_span ⟨b', hb', X', hX', rfl⟩
  have mA : ∀ y, L.Ahat y ∈ MA.hatSet P L := fun y => Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
  have mR : ∀ y, L.R0 y ∈ MA.hatSet P L := fun y => Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))
  have mAv : ∀ y, L.Ahatv y ∈ MA.hatSet P L := fun y => Or.inl (Or.inr ⟨y, rfl⟩)
  have mRv : ∀ y, L.R0v y ∈ MA.hatSet P L := fun y => Or.inr ⟨y, rfl⟩
  have sumA : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahat x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L) := by
    intro ts hts
    refine list_sum_mem fun u hu => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mA _))
  have sumAv : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahatv x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L) := by
    intro ts hts
    refine list_sum_mem fun u hu => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mAv _))
  rcases hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
  · obtain ⟨t, ht⟩ := hS.ahat b hb
    rw [ht y]; exact gen _ hb _ (mA _)
  · obtain ⟨t, ts, hts, he⟩ := hS.r0 b hb y
    rw [he]; exact Submodule.add_mem _ (gen _ hb _ (mR _)) (sumA ts hts)
  · obtain ⟨t, ht⟩ := hV.ahatv b hb
    rw [ht y]; exact gen _ hb _ (mAv _)
  · obtain ⟨t, ts, hts, he⟩ := hV.r0v b hb y
    rw [he]; exact Submodule.add_mem _ (gen _ hb _ (mRv _)) (sumAv ts hts)

end

end Formalism.FourierDecayAlt.P.CutMP

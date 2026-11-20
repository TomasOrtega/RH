import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulIdempotentHalfAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdCardAdicCompletionIntegersQuotDvdPowFinrankStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulHalfOrthogonalIdempotentSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIdempotentChartPlacesInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.HalfCosetCount

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D S T ΛS ΛT hS hT e P he k hk`. Take `⟨⟨es, hes, rfl⟩, hec⟩` from `he`. Use `set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ`. Use `set c := cA D (∑ Q ∈ P, es Q) with hcdef`. Establish `hc : c = ∑ Q ∈ P, cA D (es Q)` using `map_sum _ _ _`.

Establish `hes_orth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → es Q * es Q' = 0` using `fun Q hQ Q' hQ' hne => (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne (HeightOneSpectrum.ext (Ideal.ext fun x => by`. Distinguish the cases in `hx : x = 0`. Rewrite using `[hx]`. Conclude with `iff_of_true (zero_mem _) (zero_mem _)`. Rewrite using `[(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]))`.

Establish `hidem : ∀ Q ∈ P, cA D (es Q) * cA D (es Q) = cA D (es Q)` using `fun Q hQ => by`. Rewrite using `[← map_mul, (hes Q hQ).1.1]`. Establish `horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → cA D (es Q) * cA D (es Q') = 0` using `fun Q hQ Q' hQ' hne => by`. Rewrite using `[← map_mul, hes_orth Q hQ Q' hQ' hne, map_zero]`. Establish `hstab : ∀ Q ∈ P, ∀ u ∈ Λ, cA D (es Q) • u ∈ Λ` using `fun Q hQ u hu => GlobalTheory.PlaceModelSum.idem_smul_latO (hidem Q hQ) hu`.

Establish `hch : ∀ Q : ↥P, ∃ w : HeightOneSpectrum (𝓞 D.host.F), ∃ π : AE D →+* Fv D.host.F w, GlobalTheory.SplitHecke.Chart (cA D (es Q)) w π` using `fun Q => GlobalTheory.SplitChart.exists_chart _ (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1)`. Use `choose v π hπ using hch`. Establish `hvinj : Function.Injective v` using `GlobalTheory.T.conjugate_idempotent_chart_places_injective _ P es (fun Q hQ => hes Q hQ) rfl hec v fun Q => ⟨π Q, hπ Q⟩`. Establish `hcount : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T c) = (∏ Q : ↥P, Nat.card ((v Q).adicCompletionIntegers D.host.F ⧸ Ideal.span {(k : (v Q).adicCompletionIntegers D.host.F)})) ^ (S.rank * T.rank …`. Rewrite using `[hc, GlobalTheory.T.relIndex_nsmul_half_orthogonal_idempotent_sum S T Λ P (fun Q => cA D (es Q)) hidem horth hstab k, ← Finset.prod_pow, ← Finset.prod_attach P]`.

Use `Finset.prod_congr rfl fun Q _ => ?_` and prove the remaining obligations. Conclude with `GlobalTheory.T.relIndex_nsmul_idempotentHalf_at_splitPlace S T ΛS ΛT hS.1 hT.1 _ (v Q) (π Q) (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1) (hπ Q) k hk`. Establish `hdvd : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T c) ∣ k ^ (D.R.f * S.rank * T.rank)`. Establish `h1` using `GlobalTheory.T.prod_card_adicCompletionIntegers_quot_dvd_pow_finrank D.host.F (Finset.univ.image v) k hk`. Rewrite `h1` using `[Finset.prod_image fun x _ y _ h => hvinj h, Formalism.MainNotions.J.finrank_F_eq]`.

Rewrite using `[hcount, mul_assoc, pow_mul k D.R.f]`. Conclude with `pow_dvd_pow_of_dvd h1 _`. Use `set M := Λ ⊓ GlobalTheory.PlaceModel.half S T c with hM`. Use `set Y := Λ.comap (nsmulAddMonoidHom k) ⊓ GlobalTheory.PlaceModel.half S T c with hY`. Establish `hinj : Function.Injective (nsmulAddMonoidHom k : WO S T →+ WO S T)` using `fun x y h => nsmul_cancel_mx hk h`.

Establish `hu : IsUnit (k : AE D)`. Rewrite using `[← map_natCast (algebraMap D.host.F (AE D))]`. Conclude with `(isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk.ne')).map _`. Establish `hYM : Y.map (nsmulAddMonoidHom k) = M`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨hy1, hy2⟩` from `AddSubgroup.mem_inf.1 hy`. Conclude with `AddSubgroup.mem_inf.2 ⟨hy1, (GlobalTheory.PlaceModel.half S T c).nsmul_mem hy2 k⟩`. Introduce `hx`.

Take `⟨hx1, hx2⟩` from `AddSubgroup.mem_inf.1 hx`. Establish `key : k • ((↑hu.unit⁻¹ : AE D) • x) = x`. Rewrite using `[← Nat.cast_smul_eq_nsmul (AE D), smul_smul, IsUnit.mul_val_inv, one_smul]`. Use `⟨(↑hu.unit⁻¹ : AE D) • x, AddSubgroup.mem_inf.2 ⟨?_, ?_⟩, key⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.mem_comap]`.

Express the relevant statement in the definitionally equal form `k • _ ∈ Λ`. Rewrite using `[key]`. Conclude with `hx1`. Use `(GlobalTheory.PlaceModel.mem_half S T).2 ?_` and prove the remaining obligations. Establish `hx3 : c • x = x` using `(GlobalTheory.PlaceModel.mem_half S T).1 hx2`.

Rewrite using `[smul_comm c (↑hu.unit⁻¹ : AE D) x, hx3]`. Establish `hMY : M.relIndex Y = (M.map (nsmulAddMonoidHom k)).relIndex M`. Rewrite using `[← AddSubgroup.relIndex_map_map_of_injective (f := (nsmulAddMonoidHom k : WO S T →+ WO S T)) M Y hinj, hYM]`. Establish `hne : (M.addSubgroupOf Y).index ≠ 0`. Express the relevant statement in the definitionally equal form `M.relIndex Y ≠ 0`.

Rewrite using `[hMY]`. Conclude with `fun h => (pow_pos hk _).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))`. Use `haveI : Finite (↥Y ⧸ M.addSubgroupOf Y) := AddSubgroup.index_ne_zero_iff_finite.1 hne`. Take `⟨R, hRc, hRY, hRu⟩` from `GlobalTheory.SplitLinear.exists_reps M Y`. Use `⟨R, fun y hy => ?_, fun y hy1 hy2 => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `AddSubgroup.mem_inf.1 (hRY y hy)`. Conclude with `⟨(GlobalTheory.PlaceModel.isHalf_iff S T).2 h2, h1⟩`. Establish `hyY : y ∈ Y` using `AddSubgroup.mem_inf.2 ⟨hy2, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1⟩`. Take `⟨r, ⟨hr, hyr⟩, huniq⟩` from `hRu y hyY`. Use `⟨r, ⟨hr, (AddSubgroup.mem_inf.1 hyr).1⟩, fun r' hr' => huniq r' ⟨hr'.1, AddSubgroup.mem_inf.2 ⟨hr'.2, ?_⟩⟩⟩` and prove the remaining obligations.

Conclude with `sub_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1) (AddSubgroup.mem_inf.1 (hRY r' hr'.1)).2`. Rewrite using `[hRc, hMY]`. Conclude with `hdvd`.
-/
theorem halfCoset_reps_card : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃! r, r ∈ R ∧ y - r ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ R.card ∣ k ^ (D.R.f * S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT e P he k hk
  classical
  obtain ⟨⟨es, hes, rfl⟩, hec⟩ := he
  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ
  set c := cA D (∑ Q ∈ P, es Q) with hcdef
  have hc : c = ∑ Q ∈ P, cA D (es Q) := map_sum _ _ _
  have hes_orth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → es Q * es Q' = 0 := fun Q hQ Q' hQ' hne =>
    (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne
      (HeightOneSpectrum.ext (Ideal.ext fun x => by
        by_cases hx : x = 0
        · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
        · rw [(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]))
  have hidem : ∀ Q ∈ P, cA D (es Q) * cA D (es Q) = cA D (es Q) := fun Q hQ => by
    rw [← map_mul, (hes Q hQ).1.1]
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → cA D (es Q) * cA D (es Q') = 0 := fun Q hQ Q' hQ' hne => by
    rw [← map_mul, hes_orth Q hQ Q' hQ' hne, map_zero]
  have hstab : ∀ Q ∈ P, ∀ u ∈ Λ, cA D (es Q) • u ∈ Λ := fun Q hQ u hu =>
    GlobalTheory.PlaceModelSum.idem_smul_latO (hidem Q hQ) hu
  have hch : ∀ Q : ↥P, ∃ w : HeightOneSpectrum (𝓞 D.host.F), ∃ π : AE D →+* Fv D.host.F w,
      GlobalTheory.SplitHecke.Chart (cA D (es Q)) w π := fun Q =>
    GlobalTheory.SplitChart.exists_chart _ (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1)
  choose v π hπ using hch
  have hvinj : Function.Injective v :=
    GlobalTheory.T.conjugate_idempotent_chart_places_injective _ P es (fun Q hQ => hes Q hQ) rfl hec v fun Q => ⟨π Q, hπ Q⟩

  have hcount : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex
      (Λ ⊓ GlobalTheory.PlaceModel.half S T c) =
      (∏ Q : ↥P, Nat.card ((v Q).adicCompletionIntegers D.host.F ⧸
        Ideal.span {(k : (v Q).adicCompletionIntegers D.host.F)})) ^ (S.rank * T.rank) := by
    rw [hc, GlobalTheory.T.relIndex_nsmul_half_orthogonal_idempotent_sum S T Λ P (fun Q => cA D (es Q)) hidem horth hstab k, ← Finset.prod_pow,
      ← Finset.prod_attach P]
    refine Finset.prod_congr rfl fun Q _ => ?_
    exact GlobalTheory.T.relIndex_nsmul_idempotentHalf_at_splitPlace S T ΛS ΛT hS.1 hT.1 _ (v Q) (π Q) (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1) (hπ Q) k hk
  have hdvd : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex
      (Λ ⊓ GlobalTheory.PlaceModel.half S T c) ∣ k ^ (D.R.f * S.rank * T.rank) := by
    have h1 := GlobalTheory.T.prod_card_adicCompletionIntegers_quot_dvd_pow_finrank D.host.F (Finset.univ.image v) k hk
    rw [Finset.prod_image fun x _ y _ h => hvinj h, Formalism.MainNotions.J.finrank_F_eq] at h1
    rw [hcount, mul_assoc, pow_mul k D.R.f]
    exact pow_dvd_pow_of_dvd h1 _

  set M := Λ ⊓ GlobalTheory.PlaceModel.half S T c with hM
  set Y := Λ.comap (nsmulAddMonoidHom k) ⊓ GlobalTheory.PlaceModel.half S T c with hY
  have hinj : Function.Injective (nsmulAddMonoidHom k : WO S T →+ WO S T) := fun x y h => nsmul_cancel_mx hk h
  have hu : IsUnit (k : AE D) := by
    rw [← map_natCast (algebraMap D.host.F (AE D))]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk.ne')).map _
  have hYM : Y.map (nsmulAddMonoidHom k) = M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hy1, hy2⟩ := AddSubgroup.mem_inf.1 hy
      exact AddSubgroup.mem_inf.2 ⟨hy1, (GlobalTheory.PlaceModel.half S T c).nsmul_mem hy2 k⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.1 hx
      have key : k • ((↑hu.unit⁻¹ : AE D) • x) = x := by
        rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, IsUnit.mul_val_inv, one_smul]
      refine ⟨(↑hu.unit⁻¹ : AE D) • x, AddSubgroup.mem_inf.2 ⟨?_, ?_⟩, key⟩
      · rw [AddSubgroup.mem_comap]
        change k • _ ∈ Λ
        rw [key]; exact hx1
      · refine (GlobalTheory.PlaceModel.mem_half S T).2 ?_
        have hx3 : c • x = x := (GlobalTheory.PlaceModel.mem_half S T).1 hx2
        rw [smul_comm c (↑hu.unit⁻¹ : AE D) x, hx3]
  have hMY : M.relIndex Y = (M.map (nsmulAddMonoidHom k)).relIndex M := by
    rw [← AddSubgroup.relIndex_map_map_of_injective (f := (nsmulAddMonoidHom k : WO S T →+ WO S T)) M Y hinj, hYM]
  have hne : (M.addSubgroupOf Y).index ≠ 0 := by
    change M.relIndex Y ≠ 0
    rw [hMY]
    exact fun h => (pow_pos hk _).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  haveI : Finite (↥Y ⧸ M.addSubgroupOf Y) := AddSubgroup.index_ne_zero_iff_finite.1 hne
  obtain ⟨R, hRc, hRY, hRu⟩ := GlobalTheory.SplitLinear.exists_reps M Y
  refine ⟨R, fun y hy => ?_, fun y hy1 hy2 => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 (hRY y hy)
    exact ⟨(GlobalTheory.PlaceModel.isHalf_iff S T).2 h2, h1⟩
  · have hyY : y ∈ Y := AddSubgroup.mem_inf.2 ⟨hy2, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1⟩
    obtain ⟨r, ⟨hr, hyr⟩, huniq⟩ := hRu y hyY
    refine ⟨r, ⟨hr, (AddSubgroup.mem_inf.1 hyr).1⟩, fun r' hr' => huniq r' ⟨hr'.1, AddSubgroup.mem_inf.2 ⟨hr'.2, ?_⟩⟩⟩
    exact sub_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1) (AddSubgroup.mem_inf.1 (hRY r' hr'.1)).2
  · rw [hRc, hMY]
    exact hdvd

end GlobalTheory.HalfCosetCount

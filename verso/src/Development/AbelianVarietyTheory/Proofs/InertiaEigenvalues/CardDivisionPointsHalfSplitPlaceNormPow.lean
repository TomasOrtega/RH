import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsIotaAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsComplMapEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PtStringAllOfHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceIdempotentEqCompletionEmbeddingOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDivisionPointsSplitPlaceLocalMatricesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLocalMatrixDivisionPointQuotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceModelIndicatorEqMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.DivPtLocal

open GlobalTheory.AdelicU in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem mem_latO_true_iff_at : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D) (u : WO S T), algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin q 1)) • u = u → (u ∈ latO S T LS LT (fun _ => True) ↔ u ∈ latO S T LS LT (fun v => v = q)) := by
  intro D S T LS LT q u hu
  set e0 := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin q 1)) with he0
  constructor
  · intro h
    let Ψ : WO S T →+ WO S T := AddMonoidHom.mk' (fun x => e0 • x)
      fun x y => Matrix.ext fun i j => mul_add e0 (x i j) (y i j)
    have main : latO S T LS LT (fun _ => True) ≤ (latO S T LS LT (fun v => v = q)).comap Ψ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
      refine AddSubgroup.subset_closure ⟨GlobalTheory.AdelicU.singleFin q 1 * α, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, ?_⟩
      · rw [map_mul]
        by_cases hv : v = q
        · subst hv
          rw [evalV_singleFin_self]
          simpa using hα v
        · rw [evalV_singleFin_ne hv, zero_mul]
          exact zero_mem _
      · rw [map_mul, evalV_singleFin_ne hv, zero_mul]
      · ext i j
        simp only [Ψ, AddMonoidHom.mk'_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, he0,
          Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        rw [Algebra.algebraMap_self, RingHom.id_apply]
        exact Prod.ext (mul_zero (0 : Ainf D.host.F)) rfl
    have := main h
    rw [AddSubgroup.mem_comap] at this
    exact hu ▸ this
  · intro h
    refine AddSubgroup.closure_mono ?_ h
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun _ h' => absurd trivial h', rest⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem isSplit_of_isIdemAt : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) := by
  intro D P e he
  rw [GlobalTheory.PtString.isSplit_iff_conj, Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  intro h
  exact GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt he (IsDedekindDomain.HeightOneSpectrum.ext h)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem natCard_DQ_eq_locQ : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) e N) = Nat.card (GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank) := by
  intro D S T ΛS ΛT hS hT P e he N hN
  have hs := isSplit_of_isIdemAt D P e he
  obtain ⟨ι, hι⟩ := GlobalTheory.DivPtLocal.exists_isIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) hs
  have he1 := GlobalTheory.T.splitPlace_idempotent_eq_completionEmbedding_one D P e he ι hι
  have h3 := hι.2.2.2.1
  have key : ∀ u : WO S T, e • u = u → (u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun v => v = P.under (𝓞 D.host.F))) := by
    intro u hu
    refine mem_latO_true_iff_at D S T _ _ _ u ?_
    rw [← hu, smul_smul, he1, h3]
  have hd : GlobalTheory.DivPtFourier.divPts (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) e N =
      GlobalTheory.DivPtFourier.divPts (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun v => v = P.under (𝓞 D.host.F)) e N := by
    ext y
    rw [GlobalTheory.DivPtFourier.mem_divPts, GlobalTheory.DivPtFourier.mem_divPts]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (key _ (by rw [smul_comm, h1])).1 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (key _ (by rw [smul_comm, h1])).2 h2⟩
  have hh : (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e =
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun v => v = P.under (𝓞 D.host.F)) ⊓ GlobalTheory.PlaceModel.half S T e := by
    ext y
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(key _ ((GlobalTheory.PlaceModel.mem_half S T).1 h2)).1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(key _ ((GlobalTheory.PlaceModel.mem_half S T).1 h2)).2 h1, h2⟩
  unfold GlobalTheory.DivPtFourier.DQ
  rw [hd, hh]
  subst he1
  exact GlobalTheory.T.card_divisionPoints_splitPlace_local_matrices D S T ΛS ΛT hS hT P hs ι hι N hN

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem natCard_DQ : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) e N) = Ideal.absNorm (P.maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) ^ (S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT P e he N hN
  have hI : (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  rw [natCard_DQ_eq_locQ D S T ΛS ΛT hS hT P e he N hN, GlobalTheory.T.card_localMatrixDivisionPointQuotient D.host.E P N T.rank S.rank hN, mul_comm T.rank,
    ← GlobalTheory.LocalDifferentProduct.card_quot_map P hI, Ideal.map_span, Set.image_singleton, map_natCast]

end GlobalTheory.DivPtLocal

import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScPsiExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.PeriodIntegrals.ScPsiExists
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScGapBig
import Formalism.PeriodIntegrals.ScGapBig
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScMuExists
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.PeriodIntegrals.ScMuExists
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScRefExists
import Formalism.PeriodIntegrals.ScRefExists
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScXuExists
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScPiFrame
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScPiBuild
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Formalism.PeriodIntegrals.ScPiExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeHW
import Formalism.SharpRestriction.CuspSpanNormBounds.HCFiniteKMultiplicityGapped
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MExistsCut
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasWCore
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasInfXfer
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.BesselNVGapPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ScWlocExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HCReprodM
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SplitPrimeCounts.LsSetresSplit
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SplitPrimeCounts.LsSetresInt

namespace Formalism.L2.SG.Closed.ScPsi

/- English proof (translation)
Introduce `A`. Take `⟨p, h1, h2, h3⟩` from `h A.I`. Conclude with `⟨⟨p, h1, h2, h3⟩⟩`.
-/
theorem chkScPsiExists (h : PI.ScPsiExists.Target) (D : Formalism.BasicNotions.D7) :
    Formalism.L2.SG.SplitPrimeNormLemmas.PsiExists D := by
  intro A
  obtain ⟨p, h1, h2, h3⟩ := h A.I
  exact ⟨⟨p, h1, h2, h3⟩⟩

end Formalism.L2.SG.Closed.ScPsi

namespace Formalism.L2.SG.Closed.ScGap

/- English proof (translation)
Introduce `hm hG τ`. Take `⟨hn, hgap⟩` from `hG`. Establish `h2` using `D.R.two_le_m`. Establish `hr : D.R.r = 2 * D.R.rS + D.R.k + 1`. Simplify using `only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]`.

Use linear arithmetic over natural numbers and integers. Use `show PI.ScGapBig.GapBig D.R.k D.R.rS (fun j => ((D.hc τ).b (Fin.cast hm.symm j) : ℝ))`. Use `h D.R.k D.R.rS _ (by show 1801 ≤ 2 * D.R.rS + D.R.k + 1; omega) ?_` and prove the remaining obligations. Introduce `j hj`. Establish `hg` using `hgap τ (Fin.cast hm.symm j) (by simp; omega)`.

Establish `hr' : ((PI.ScGapBig.rk48 D.R.k D.R.rS : ℕ) : ℝ) = ((D.R.r : ℕ) : ℝ)`. Rewrite using `[hr]`. Both sides reduce to the same expression. Rewrite using `[hr']`. Establish `e1 : (⟨(Fin.cast hm.symm j).1 + 1, by simp; omega⟩ : Fin D.R.m) = Fin.cast hm.symm ⟨j.1 + 1, hj⟩` using `rfl`.

Rewrite `hg` using `[e1]`. Establish `: ((16 * (D.R.r : ℚ) ^ 19 : ℚ) : ℝ) ≤ (((D.hc τ).b (Fin.cast hm.symm ⟨j.1 + 1, hj⟩) - (D.hc τ).b (Fin.cast hm.symm j) : ℚ) : ℝ)`. Conclude with `hg` after adjusting the coercions. Move the coercions through the operations in `at this`. Simplify using `using this`.
-/
theorem chkScGapBig (h : PI.ScGapBig.ScGapBig) (D : Formalism.BasicNotions.D7) :
    Formalism.L2.SG.SplitPrimeNormLemmas.GapBigOfGapHyp D := by
  intro hm hG τ
  obtain ⟨hn, hgap⟩ := hG
  have h2 := D.R.two_le_m
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
    simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]; omega
  show PI.ScGapBig.GapBig D.R.k D.R.rS (fun j => ((D.hc τ).b (Fin.cast hm.symm j) : ℝ))
  refine h D.R.k D.R.rS _ (by show 1801 ≤ 2 * D.R.rS + D.R.k + 1; omega) ?_
  intro j hj
  have hg := hgap τ (Fin.cast hm.symm j) (by simp; omega)
  have hr' : ((PI.ScGapBig.rk48 D.R.k D.R.rS : ℕ) : ℝ) = ((D.R.r : ℕ) : ℝ) := by
    rw [hr]; rfl
  rw [hr']
  have e1 : (⟨(Fin.cast hm.symm j).1 + 1, by simp; omega⟩ : Fin D.R.m) = Fin.cast hm.symm ⟨j.1 + 1, hj⟩ := rfl
  rw [e1] at hg
  have : ((16 * (D.R.r : ℚ) ^ 19 : ℚ) : ℝ) ≤
      (((D.hc τ).b (Fin.cast hm.symm ⟨j.1 + 1, hj⟩) - (D.hc τ).b (Fin.cast hm.symm j) : ℚ) : ℝ) := by
    exact_mod_cast hg
  push_cast at this
  simpa using this

end Formalism.L2.SG.Closed.ScGap

namespace Formalism.L2.SG.Closed.ScMu

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ChkScMu

/- English proof (translation)
Use `conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply, A.J_eq, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_crdA {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    A.ιE (Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply,
    A.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

/- English proof (translation)
Rewrite using `[← hform_crdA, RingEquiv.symm_apply_apply]`.
-/
theorem hform_eq {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w) =
      A.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdA, RingEquiv.symm_apply_apply]

/- English proof (translation)
Introduce `A L`. Establish `key : ∀ u, ∃ muN muH nuQ : Measure A.I.Ginf, IsHaarOnSet A.I (Ninf A.I (eC A L) (zC A L u)) muN ∧ IsHaarOnSet A.I (Hset A.I (Set.range (eC A L) ∪ Set.range (fC A L) ∪ {zC A L u})) muH ∧ IsQuotMeasS A.I (((muN.prod muH).map (fun p => p.1 * p.2))) nuQ`. Introduce `u`. Use `h A.I D.R.rS (eC A L) (fC A L) (zC A L u) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a b`.

Simplify using `only [eC, hform_eq, L.ee, map_zero]`. Introduce `a b`. Simplify using `only [fC, hform_eq, L.ff, map_zero]`. Apply the tactic sequence `intro a b; simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp`. Introduce `a`.

Simplify using `only [eC, fC, zC, hform_eq, (L.zu_orth u a).1, (L.zu_orth u a).2, map_zero, and_self]`. Simplify using `only [zC, hform_eq, L.zu_norm]`. Introduce `h0`. Establish `h1` using `congrArg A.ιE h0`. Simplify using `only [RingEquiv.apply_symm_apply, map_zero, neg_eq_zero, Nat.cast_eq_zero] at h1`.

Establish `h2` using `D.T_mod_g u 0`. Rewrite `h2` using `[h1]`. Simplify using `at h2`. Use `choose muN muH nuQ hN hH hQ using key`. Conclude with `⟨⟨muN, muH, hN, hH, nuQ, hQ⟩⟩`.
-/
theorem chkScMuExists (h : PI.ScMuExists.Target) (D : D7) : MuExists D := by
  intro A L
  have key : ∀ u, ∃ muN muH nuQ : Measure A.I.Ginf,
      IsHaarOnSet A.I (Ninf A.I (eC A L) (zC A L u)) muN ∧
      IsHaarOnSet A.I (Hset A.I (Set.range (eC A L) ∪ Set.range (fC A L) ∪ {zC A L u})) muH ∧
      IsQuotMeasS A.I (((muN.prod muH).map (fun p => p.1 * p.2))) nuQ := by
    intro u
    refine h A.I D.R.rS (eC A L) (fC A L) (zC A L u) ?_ ?_ ?_ ?_ ?_
    · intro a b; simp only [eC, hform_eq, L.ee, map_zero]
    · intro a b; simp only [fC, hform_eq, L.ff, map_zero]
    · intro a b; simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp
    · intro a; simp only [eC, fC, zC, hform_eq, (L.zu_orth u a).1, (L.zu_orth u a).2, map_zero, and_self]
    · simp only [zC, hform_eq, L.zu_norm]
      intro h0
      have h1 := congrArg A.ιE h0
      simp only [RingEquiv.apply_symm_apply, map_zero, neg_eq_zero, Nat.cast_eq_zero] at h1
      have h2 := D.T_mod_g u 0
      rw [h1] at h2
      simp at h2
  choose muN muH nuQ hN hH hQ using key
  exact ⟨⟨muN, muH, hN, hH, nuQ, hQ⟩⟩

end ChkScMu
end

end Formalism.L2.SG.Closed.ScMu

namespace Formalism.L2.SG.Closed.ScRef

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ChkScRef

/- English proof (translation)
Use `conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply, A.J_eq, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_crdA {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    A.ιE (Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply,
    A.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

/- English proof (translation)
Rewrite using `[← hform_crdA, RingEquiv.symm_apply_apply]`.
-/
theorem hform_eq {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w) =
      A.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdA, RingEquiv.symm_apply_apply]

def SplitAtG (D : D7) : Prop :=
  ∀ (A : UnitaryGroupInstance D) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 A.I.F)), ((gD D : ℕ) : 𝓞 A.I.F) ∈ v.asIdeal →
    Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 A.I.E) //
      w.asIdeal.comap (algebraMap (𝓞 A.I.F) (𝓞 A.I.E)) = v.asIdeal} = 2

def IntAtG (D : D7) : Prop :=
  ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (a : Fin D.R.rS),
    InAt A.I (gD D) 1 (incl A.I (eC A L a)) ∧ InAt A.I (gD D) 1 (incl A.I (fC A L a))

/- English proof (translation)
Introduce `A L`. Establish `hn : A.I.n = 2 * D.R.rS + D.R.k + 1` using `A.n_eq.trans (Formalism.MainNotions.S.dimS_eq D.R).symm`. Establish `hg : 1 ≤ gD D` using `Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos`. Apply the tactic sequence `obtain ⟨P⟩ := h A.I (gD D) D.R.rS D.R.k (eC A L) (fC A L) hg (hs A) hn (fun a b => by simp only [eC, hform_eq, L.ee, map_zero]) (fun a b => by simp only [fC, hform_eq, L.ff, map_zero]) (fun a b => by simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp) (hi A L)`. Conclude with `⟨{ e0 := P.e0 f0 := P.f0 z0 := P.z0 bw := P.bw bwd := P.bwd ew := P.ew vectorsInLattice := P.vectorsInLattice basisApprox := P.basisApprox gramIntegral := P.gramIntegral formsAtZero := P.formsAtZero weightVectorsIntegral := P.weightVectorsIntegral ew_idem := P.ew_idem ew_orth := …`.
-/
theorem chkScRefExists (h : PI.ScRefExists.Target) (D : D7) (hs : SplitAtG D) (hi : IntAtG D) :
    RefExists D := by
  intro A L
  have hn : A.I.n = 2 * D.R.rS + D.R.k + 1 := A.n_eq.trans (Formalism.MainNotions.S.dimS_eq D.R).symm
  have hg : 1 ≤ gD D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨P⟩ := h A.I (gD D) D.R.rS D.R.k (eC A L) (fC A L) hg (hs A) hn
    (fun a b => by simp only [eC, hform_eq, L.ee, map_zero])
    (fun a b => by simp only [fC, hform_eq, L.ff, map_zero])
    (fun a b => by simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp)
    (hi A L)
  exact ⟨{ e0 := P.e0
           f0 := P.f0
           z0 := P.z0
           bw := P.bw
           bwd := P.bwd
           ew := P.ew
           vectorsInLattice := P.vectorsInLattice
           basisApprox := P.basisApprox
           gramIntegral := P.gramIntegral
           formsAtZero := P.formsAtZero
           weightVectorsIntegral := P.weightVectorsIntegral
           ew_idem := P.ew_idem
           ew_orth := P.ew_orth
           ew_int := P.ew_int
           ew_full := P.ew_full
           bw_w := P.bw_w
           bwd_w := P.bwd_w
           bw_dual := P.bw_dual
           latticeSpan := P.latticeSpan }⟩

end ChkScRef
end

end Formalism.L2.SG.Closed.ScRef

namespace Formalism.L2.SG.Closed.ScXu

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ChkScXu

/- English proof (translation)
Use `conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply, A.J_eq, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_crdA {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    A.ιE (Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply,
    A.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

/- English proof (translation)
Rewrite using `[← hform_crdA, RingEquiv.symm_apply_apply]`.
-/
theorem hform_eq {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w) =
      A.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdA, RingEquiv.symm_apply_apply]

def SplitAtG (D : D7) : Prop :=
  ∀ (A : UnitaryGroupInstance D) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 A.I.F)), ((gD D : ℕ) : 𝓞 A.I.F) ∈ v.asIdeal →
    Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 A.I.E) //
      w.asIdeal.comap (algebraMap (𝓞 A.I.F) (𝓞 A.I.E)) = v.asIdeal} = 2

def IntAtGZ (D : D7) : Prop :=
  ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D),
    (∀ a : Fin D.R.rS, InAt A.I (gD D) 1 (incl A.I (eC A L a)) ∧ InAt A.I (gD D) 1 (incl A.I (fC A L a))) ∧
    ∀ u, InAt A.I (gD D) 1 (incl A.I (zC A L u))

/- English proof (translation)
Introduce `A L Rf`. Establish `hn : A.I.n = 2 * D.R.rS + D.R.k + 1` using `A.n_eq.trans (Formalism.MainNotions.S.dimS_eq D.R).symm`. Establish `hg : 1 ≤ gD D` using `Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos`. Set `P : PI.ScRefExists.RefData A.I (gD D) D.R.rS D.R.k (eC A L) (fC A L)` to `{ e0 := Rf.e0 f0 := Rf.f0 z0 := Rf.z0 bw := Rf.bw bwd := Rf.bwd ew := Rf.ew vectorsInLattice := Rf.vectorsInLattice basisApprox := Rf.basisApprox gramIntegral := Rf.gramIntegral formsAtZero := Rf.formsAtZero weightVectorsIntegral := Rf.weightVectorsIntegral ew_idem := Rf.ew_idem …`. Establish `key : ∀ u, ∃ x : A.I.Gf, (∀ a, A.I.fmat x *ᵥ incl A.I (eC A L a) = incl A.I (eC A L a) ∧ A.I.fmat x *ᵥ incl A.I (fC A L a) = incl A.I (fC A L a)) ∧ InAt A.I (gD D) (gD D) (A.I.fmat x⁻¹ *ᵥ incl A.I (zC A L u) - Rf.z0) ∧ OneOff A.I (gD D) x ∧ x ∈ A.I.Kset`.

Introduce `u`. Establish `hT : (D.mem u).A.T ≡ 1 [MOD gD D]` using `D.T_modEq_of_dvd u (dvd_trans (dvd_pow_self _ two_ne_zero) D.gg_dvd_modT)`. Apply the tactic sequence `exact h A.I (gD D) D.R.rS D.R.k (eC A L) (fC A L) (zC A L u) P hg (hs A) hn (fun a b => by simp only [eC, hform_eq, L.ee, map_zero]) (fun a b => by simp only [fC, hform_eq, L.ff, map_zero]) (fun a b => by simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp) (fun a => by simp o …`. Use `choose xu hfix hz hone hK using key`. Conclude with `⟨{ xu := xu xu_fix := fun u a => hfix u a xu_z := hz xu_one := hone xu_K := hK }⟩`.
-/
theorem chkScXuExists (h : PI.ScXuExists.Target) (D : D7) (hs : SplitAtG D) (hi : IntAtGZ D) :
    XuExists D := by
  intro A L Rf
  have hn : A.I.n = 2 * D.R.rS + D.R.k + 1 := A.n_eq.trans (Formalism.MainNotions.S.dimS_eq D.R).symm
  have hg : 1 ≤ gD D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  let P : PI.ScRefExists.RefData A.I (gD D) D.R.rS D.R.k (eC A L) (fC A L) :=
    { e0 := Rf.e0
      f0 := Rf.f0
      z0 := Rf.z0
      bw := Rf.bw
      bwd := Rf.bwd
      ew := Rf.ew
      vectorsInLattice := Rf.vectorsInLattice
      basisApprox := Rf.basisApprox
      gramIntegral := Rf.gramIntegral
      formsAtZero := Rf.formsAtZero
      weightVectorsIntegral := Rf.weightVectorsIntegral
      ew_idem := Rf.ew_idem
      ew_orth := Rf.ew_orth
      ew_int := Rf.ew_int
      ew_full := Rf.ew_full
      bw_w := Rf.bw_w
      bwd_w := Rf.bwd_w
      bw_dual := Rf.bw_dual
      latticeSpan := Rf.latticeSpan }
  have key : ∀ u, ∃ x : A.I.Gf, (∀ a, A.I.fmat x *ᵥ incl A.I (eC A L a) = incl A.I (eC A L a) ∧
      A.I.fmat x *ᵥ incl A.I (fC A L a) = incl A.I (fC A L a)) ∧
      InAt A.I (gD D) (gD D) (A.I.fmat x⁻¹ *ᵥ incl A.I (zC A L u) - Rf.z0) ∧ OneOff A.I (gD D) x ∧
      x ∈ A.I.Kset := by
    intro u
    have hT : (D.mem u).A.T ≡ 1 [MOD gD D] :=
      D.T_modEq_of_dvd u (dvd_trans (dvd_pow_self _ two_ne_zero) D.gg_dvd_modT)
    exact h A.I (gD D) D.R.rS D.R.k (eC A L) (fC A L) (zC A L u) P hg (hs A) hn
      (fun a b => by simp only [eC, hform_eq, L.ee, map_zero])
      (fun a b => by simp only [fC, hform_eq, L.ff, map_zero])
      (fun a b => by simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp)
      (fun a => by simp only [eC, fC, zC, hform_eq, (L.zu_orth u a).1, (L.zu_orth u a).2, map_zero, and_self])
      ⟨(D.mem u).A.T, hT, by simp only [zC, hform_eq, L.zu_norm, map_neg, map_natCast]⟩
      (hi A L).1 ((hi A L).2 u)
  choose xu hfix hz hone hK using key
  exact ⟨{ xu := xu
           xu_fix := fun u a => hfix u a
           xu_z := hz
           xu_one := hone
           xu_K := hK }⟩

end ChkScXu
end

end Formalism.L2.SG.Closed.ScXu

namespace Formalism.L2.SG.Closed.ScPi

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ChkScPi

/- English proof (translation)
Use `conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply, A.J_eq, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_crdA {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    A.ιE (Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply,
    A.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

/- English proof (translation)
Rewrite using `[← hform_crdA, RingEquiv.symm_apply_apply]`.
-/
theorem hform_eq {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w) =
      A.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdA, RingEquiv.symm_apply_apply]

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b`. Simplify using `only [eC, hform_eq, L.ee, map_zero]`. Introduce `a b`. Simplify using `only [fC, hform_eq, L.ff, map_zero]`.

Apply the tactic sequence `intro a b; simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp`. Introduce `a`. Simplify using `only [eC, fC, zC, hform_eq, (L.zu_orth u a).1, (L.zu_orth u a).2, map_zero, and_self]`.
-/
theorem isFrame {D : D7} (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (u : D.what₂.Word) :
    PI.ScPiExists.IsFrame A.I (eC A L) (fC A L) (zC A L u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b; simp only [eC, hform_eq, L.ee, map_zero]
  · intro a b; simp only [fC, hform_eq, L.ff, map_zero]
  · intro a b; simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp
  · intro a; simp only [eC, fC, zC, hform_eq, (L.zu_orth u a).1, (L.zu_orth u a).2, map_zero, and_self]

/- English proof (translation)
Simplify using `only [zC, hform_eq, L.zu_norm, map_neg, map_natCast]`.
-/
theorem zz_eq {D : D7} (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (u : D.what₂.Word) :
    Formalism.UG.hform (starRingEnd A.I.E) A.I.J (zC A L u) (zC A L u) = -(((D.mem u).A.T : ℕ) : A.I.E) := by
  simp only [zC, hform_eq, L.zu_norm, map_neg, map_natCast]

/- English proof (translation)
Establish `h2` using `D.T_mod_g u 0`. Break down `Nat.eq_zero_or_pos (D.mem u).A.T with h | h` into its components or cases. Rewrite `h2` using `[h]`. Simplify using `at h2`. Conclude with `h`.
-/
theorem T_pos {D : D7} (u : D.what₂.Word) : 0 < (D.mem u).A.T := by
  have h2 := D.T_mod_g u 0
  rcases Nat.eq_zero_or_pos (D.mem u).A.T with h | h
  · rw [h] at h2; simp at h2
  · exact h

/- English proof (translation)
Establish `key : ∀ a : ℕ, ∀ i j : Fin k, j.1 = i.1 + a + 1 → g j < g i`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero => intro i j h; exact hs i j (by omega)`. Consider the case `succ a ih`.

Introduce `i j h`. Establish `hm : i.1 + a + 1 < k` using `by omega`. Conclude with `lt_trans (hs ⟨i.1 + a + 1, hm⟩ j (by simp; omega)) (ih i ⟨i.1 + a + 1, hm⟩ rfl)`. Introduce `i j hij`. Conclude with `key (j.1 - i.1 - 1) i j (by have : i.1 < j.1 := hij; omega)`.
-/
theorem strictAnti_fin {k : ℕ} (g : Fin k → ℝ) (hs : ∀ (i j : Fin k), j.1 = i.1 + 1 → g j < g i) :
    StrictAnti g := by
  have key : ∀ a : ℕ, ∀ i j : Fin k, j.1 = i.1 + a + 1 → g j < g i := by
    intro a
    induction a with
    | zero => intro i j h; exact hs i j (by omega)
    | succ a ih =>
      intro i j h
      have hm : i.1 + a + 1 < k := by omega
      exact lt_trans (hs ⟨i.1 + a + 1, hm⟩ j (by simp; omega)) (ih i ⟨i.1 + a + 1, hm⟩ rfl)
  intro i j hij
  exact key (j.1 - i.1 - 1) i j (by have : i.1 < j.1 := hij; omega)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `strictAnti_fin` to reduce the goal to its premises. Introduce `i j hj`. Establish `hi : i.1 < D.R.k - 1` using `by omega`. Establish `h1` using `P.u_gt_v ⟨i.1, hi⟩`.

Establish `h2` using `P.v_gt_u ⟨i.1, hi⟩`. Establish `hj' : j = ⟨i.1 + 1, by omega⟩` using `Fin.ext hj`. Establish `e1 : P.u ⟨i.1 + 1, by omega⟩ < P.u i` using `lt_trans h2 h1`. Rewrite using `[hj']`. Conclude with `e1` after adjusting the coercions.

Introduce `a`. Take `⟨z, hz⟩` from `P.u_half a`. Take `⟨j, hj⟩` from `D.R.k_even`. Use `⟨z - j + 1, ?_⟩` and prove the remaining obligations. Use `show ((P.u a : ℚ) : ℝ) - _ = _`.

Rewrite using `[hz]`. Establish `hk : (D.R.k : ℝ) = j + j` using `by exact_mod_cast hj`. Rewrite using `[hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hcParam (D : D7) (P : HCParam D.R) : PI.UpqRep.IsHCParam (fun i => ((P.u i : ℚ) : ℝ)) := by
  refine ⟨?_, ?_⟩
  · apply strictAnti_fin
    intro i j hj
    have hi : i.1 < D.R.k - 1 := by omega
    have h1 := P.u_gt_v ⟨i.1, hi⟩
    have h2 := P.v_gt_u ⟨i.1, hi⟩
    have hj' : j = ⟨i.1 + 1, by omega⟩ := Fin.ext hj
    have e1 : P.u ⟨i.1 + 1, by omega⟩ < P.u i := lt_trans h2 h1
    rw [hj']
    exact_mod_cast e1
  · intro a
    obtain ⟨z, hz⟩ := P.u_half a
    obtain ⟨j, hj⟩ := D.R.k_even
    refine ⟨z - j + 1, ?_⟩
    show ((P.u a : ℚ) : ℝ) - _ = _
    rw [hz]
    have hk : (D.R.k : ℝ) = j + j := by exact_mod_cast hj
    rw [hk]
    push_cast
    ring

/- English proof (translation)
Introduce `A L`. Establish `hW' : PI.ScPiExists.WeylHyp` using `fun k u hu => hW k u hu`. Establish `hn : A.I.n = 2 * D.R.rS + D.R.k + 1` using `A.n_eq.trans (Formalism.MainNotions.S.dimS_eq D.R).symm`. Establish `heps : ∀ v (i : Fin A.I.n), A.I.ε v i = if i.val < D.R.k - 1 then true else decide ((i.val - (D.R.k - 1)) % 2 = 0)`. Introduce `v i`.

Rewrite using `[A.eps_eq v i]`. Simplify using `only [epsS, Fin.val_cast]`. Establish `key : ∀ u, Nonempty (PI.ScPiExists.PiData A.I D.R.k (eC A L) (fC A L) (zC A L u) (fun v i => (((D.hcW u (A.pl v)).u i : ℚ) : ℝ)))`. Introduce `u`. Use `hB hW' A.I D.R.rS D.R.k (eC A L) (fC A L) (zC A L u) _ hn (isFrame A L u) ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[zz_eq]`. Introduce `h0`. Establish `h1 : (((D.mem u).A.T : ℕ) : A.I.E) = 0` using `neg_eq_zero.mp h0`. Rewrite `h1` using `[Nat.cast_eq_zero]`. Conclude with `(Nat.pos_iff_ne_zero.mp (T_pos u)) h1`.

Introduce `v`. Conclude with `hcParam D (D.hcW u (A.pl v))`. Conclude with `hF A.I D.R.rS D.R.k (eC A L) (fC A L) (zC A L u) hn (isFrame A L u) ⟨(D.mem u).A.T, T_pos u, zz_eq A L u⟩ heps`. Set `P` to `fun u => Classical.choice (key u)`. Conclude with `⟨{ Vpi := fun u => (P u).Vpi vN := fun u => (P u).vN vI := fun u => (P u).vI vF := fun u => (P u).vF piU := fun u => (P u).piU piU_rep := fun u => (P u).piU_rep Vloc := fun u => (P u).Vloc lN := fun u => (P u).lN lI := fun u => (P u).lI lF := fun u => (P u).lF piLoc := fun u => ( …`.
-/
theorem chkScPiExists (hW : Formalism.MainNotions.DiscreteSeriesWeylDimension.HighestWeightExists) (hF : PI.ScPiExists.Frame)
    (hB : PI.ScPiExists.Build) (D : D7) : PiExists D := by
  intro A L
  have hW' : PI.ScPiExists.WeylHyp := fun k u hu => hW k u hu
  have hn : A.I.n = 2 * D.R.rS + D.R.k + 1 := A.n_eq.trans (Formalism.MainNotions.S.dimS_eq D.R).symm
  have heps : ∀ v (i : Fin A.I.n), A.I.ε v i =
      if i.val < D.R.k - 1 then true else decide ((i.val - (D.R.k - 1)) % 2 = 0) := by
    intro v i
    rw [A.eps_eq v i]
    simp only [epsS, Fin.val_cast]
  have key : ∀ u, Nonempty (PI.ScPiExists.PiData A.I D.R.k (eC A L) (fC A L) (zC A L u)
      (fun v i => (((D.hcW u (A.pl v)).u i : ℚ) : ℝ))) := by
    intro u
    refine hB hW' A.I D.R.rS D.R.k (eC A L) (fC A L) (zC A L u) _ hn (isFrame A L u) ?_ ?_ ?_
    · rw [zz_eq]
      intro h0
      have h1 : (((D.mem u).A.T : ℕ) : A.I.E) = 0 := neg_eq_zero.mp h0
      rw [Nat.cast_eq_zero] at h1
      exact (Nat.pos_iff_ne_zero.mp (T_pos u)) h1
    · intro v; exact hcParam D (D.hcW u (A.pl v))
    · exact hF A.I D.R.rS D.R.k (eC A L) (fC A L) (zC A L u) hn (isFrame A L u)
        ⟨(D.mem u).A.T, T_pos u, zz_eq A L u⟩ heps
  let P := fun u => Classical.choice (key u)
  exact ⟨{ Vpi := fun u => (P u).Vpi
           vN := fun u => (P u).vN
           vI := fun u => (P u).vI
           vF := fun u => (P u).vF
           piU := fun u => (P u).piU
           piU_rep := fun u => (P u).piU_rep
           Vloc := fun u => (P u).Vloc
           lN := fun u => (P u).lN
           lI := fun u => (P u).lI
           lF := fun u => (P u).lF
           piLoc := fun u => (P u).piLoc
           piLoc_type := fun u => (P u).piLoc_type
           wfr := fun u => (P u).wfr
           wfr_on := fun u => (P u).wfr_on
           wfr_perp := fun u => (P u).wfr_perp
           tensU := fun u => (P u).tensU
           tensU_inner := fun u => (P u).tensU_inner
           tensU_span := fun u => (P u).tensU_span
           tensU_equiv := fun u => (P u).tensU_equiv }⟩

end ChkScPi
end

end Formalism.L2.SG.Closed.ScPi

namespace Formalism.L2.SG.Closed

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas

/- English proof (translation)
The claim follows from `ScPsi.chkScPsiExists sc_psi_exists D`.
-/
theorem PsiExists_holds (D : D7) : PsiExists D := ScPsi.chkScPsiExists sc_psi_exists D

/- English proof (translation)
The claim follows from `ScGap.chkScGapBig scGapBig D`.
-/
theorem GapBigOfGapHyp_holds (D : D7) : GapBigOfGapHyp D := ScGap.chkScGapBig scGapBig D

/- English proof (translation)
The claim follows from `ScMu.ChkScMu.chkScMuExists PI.sc_mu_exists D`.
-/
theorem MuExists_holds (D : D7) : MuExists D := ScMu.ChkScMu.chkScMuExists PI.sc_mu_exists D

/- English proof (translation)
The claim follows from `ScRef.ChkScRef.chkScRefExists sc_reference_exists D (Formalism.L2.SG.SplitPrimeNormLemmas.SplitG.splitAtG_holds D) (fun A L a => (Formalism.L2.SG.SplitPrimeNormLemmas.IntG.intAtGZ_holds D A L).1 a)`.
-/
theorem RefExists_holds (D : D7) : RefExists D :=
  ScRef.ChkScRef.chkScRefExists sc_reference_exists D (Formalism.L2.SG.SplitPrimeNormLemmas.SplitG.splitAtG_holds D)
    (fun A L a => (Formalism.L2.SG.SplitPrimeNormLemmas.IntG.intAtGZ_holds D A L).1 a)

/- English proof (translation)
The claim follows from `ScXu.ChkScXu.chkScXuExists sc_xu_exists D (Formalism.L2.SG.SplitPrimeNormLemmas.SplitG.splitAtG_holds D) (Formalism.L2.SG.SplitPrimeNormLemmas.IntG.intAtGZ_holds D)`.
-/
theorem XuExists_holds (D : D7) : XuExists D :=
  ScXu.ChkScXu.chkScXuExists sc_xu_exists D (Formalism.L2.SG.SplitPrimeNormLemmas.SplitG.splitAtG_holds D)
    (Formalism.L2.SG.SplitPrimeNormLemmas.IntG.intAtGZ_holds D)

variable [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.HighestWeightExists] in
/- English proof (translation)
The claim follows from `ScPi.ChkScPi.chkScPiExists Formalism.MainNotions.BridgeHW.highest_weight_exists_bis sc_pi_frame sc_pi_construction D`.
-/
theorem PiExists_holds (D : D7) : PiExists D :=
  ScPi.ChkScPi.chkScPiExists Formalism.MainNotions.BridgeHW.highest_weight_exists_bis sc_pi_frame sc_pi_construction D

variable [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExistsG] in
/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.automorphic_bundle_exists Formalism.MainNotions.BridgeDS3.discrete_series_exists_gapped D`.
-/
theorem BunExists_holds (D : D7) : BunExists D :=
  Formalism.L2.SG.Pf.automorphic_bundle_exists Formalism.MainNotions.BridgeDS3.discrete_series_exists_gapped D

/- English proof (translation)
The claim follows from `Formalism.L2.SG.InstExistsPf.instExists D`.
-/
theorem InstExists_holds (D : D7) : InstExists D := Formalism.L2.SG.InstExistsPf.instExists D

/- English proof (translation)
The claim follows from `Fact.out`.
-/
theorem CoefWeightedLoc_holds [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] : CoefWeightedLoc := Fact.out

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.latExists_of hPC D`.
-/
theorem LatExists_of_primesInClasses (hPC : Formalism.L2.SG.Pf.LatEx.PrimesInClasses) (D : D7) : LatExists D :=
  Formalism.L2.SG.Pf.latExists_of hPC D

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.mExists_of_cuts D weil_measure_compat infinite_measure_transfer`.
-/
theorem MExists_holds (D : D7) : MExists D :=
  Formalism.L2.SG.Pf.mExists_of_cuts D weil_measure_compat infinite_measure_transfer

variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] in
/- English proof (translation)
The claim follows from `Formalism.L2.SG.BesselDiscreteSeries.besselNVGap`.
-/
theorem BesselNVGap_holds : BesselNVGap := Formalism.L2.SG.BesselDiscreteSeries.besselNVGap

/- English proof (translation)
The claim follows from `scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm`.
-/
theorem WlocExists_holds : WlocExists := scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm

end Formalism.L2.SG.Closed

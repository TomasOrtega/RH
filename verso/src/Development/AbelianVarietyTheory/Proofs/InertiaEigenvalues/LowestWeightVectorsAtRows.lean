import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefMapNormEquivariantBasisOfPre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeights
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexCoefficientMapCoreFieldPropertiesStatement

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open GlobalTheory.AdTh.RecPair GlobalTheory.AdTh.VecFock
open scoped ComplexOrder
namespace GlobalTheory.AdTh.PhaseMapFree

/- English proof (translation)
Establish `hW` using `hP.ωP i t`. Establish `hr : Odd D.R.r`. Use `D.R.m_add_three_le_k` as an intermediate fact. Take `⟨a, ha⟩` from `D.R.k_even`. Take `⟨b, hb⟩` from `D.R.m_even`.

Conclude with `⟨a + b - 1, by simp only [Ranks.r]; omega⟩`. Establish `rV : (Vc D i).rank = D.R.r + D.R.t` using `D.sp.V_rank _ (Nat.le_add_left _ _) i.2`. Establish `rW : (Wc D i).rank = D.R.r` using `D.sp.W_rank _ (Nat.le_add_left _ _) i.2`. Establish `hev : Even (Vc D i).rank` using `rV ▸ hr.add_odd D.R.t_odd`. Establish `hη : GlobalTheory.WeilParts.IsEtaTilde D R.eta` using `GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr))`.

Use `⟨hW, hM.inf, hV.1, hev, D.sp.V_sig _, D.sp.W_sig _, exp_mu hL i t, fun τ => ?_, fun v ε hv => ?_, ⟨_, hη⟩⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `exp_mu hL i t τ`. Take `⟨s, hs⟩` from `hr`. Use `⟨a - s - 1, ?_⟩` and prove the remaining obligations. Establish `h3` using `GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hη.2.2.2 τ))`.

Establish `e : ((a - s - 1 : ℤ) : ℚ) + ((Wc D i).rank : ℚ) / 2 = (a : ℚ) + -(1 / 2)`. Rewrite using `[rW, hs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `h3`. Take `⟨-, e, ⟨⟨es, hes, -⟩, -⟩, -⟩` from `hP.vP i t`. Establish `key` using `fun P (hP : P.under (𝓞 D.host.F) = v) => (GlobalTheory.levCh_unramified_places D T0 R.toLevCh A.μ0 hL t).2.2.2 P fun PP hPP => by`. Rewrite using `[hP]`. Conclude with `under_ne (hes PP (Finset.mem_union.2 hPP)) hv`.

Establish `u1` using `GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 fun P hP => (key P hP).2 i`. Establish `u2` using `GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.xi t) v ε hv.1 fun P hP => (key P hP).1`. Establish `u3` using `GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P`. Establish `u4 : GlobalTheory.WeilParts.UnramAt ε (R.toLevCh.mu t ((i : ℕ) + 1))` using `fun x a b c => by show R.mu0 ((i : ℕ) + 1) x * R.xi t x = 1`. Rewrite using `[u1 x a b c, u2 x a b c, one_mul]`.

Use `⟨u4, fun x a b c => ?_⟩` and prove the remaining obligations. Use `show R.toLevCh.mu t ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1`. Rewrite using `[u4 x a b c, u3 x a b c, inv_one, one_mul]`.
-/
theorem isPair_of_clauses (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0)
    (hM : R.IsModels) (hP : R.IsThP) (i : Fin D.R.m) (t : T0) (hV : VStd D i) :
    IsPair R.ψ R.θ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t) := by
  have hW := hP.ωP i t
  have hr : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ hr.add_odd D.R.t_odd
  have hη : GlobalTheory.WeilParts.IsEtaTilde D R.eta :=
    GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr))
  refine ⟨hW, hM.inf, hV.1, hev, D.sp.V_sig _, D.sp.W_sig _, exp_mu hL i t, fun τ => ?_, fun v ε hv => ?_, ⟨_, hη⟩⟩
  · obtain ⟨a, ha⟩ := exp_mu hL i t τ
    obtain ⟨s, hs⟩ := hr
    refine ⟨a - s - 1, ?_⟩
    have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hη.2.2.2 τ))
    have e : ((a - s - 1 : ℤ) : ℚ) + ((Wc D i).rank : ℚ) / 2 = (a : ℚ) + -(1 / 2) := by
      rw [rW, hs]; push_cast; ring
    rw [e]
    exact h3
  · obtain ⟨-, e, ⟨⟨es, hes, -⟩, -⟩, -⟩ := hP.vP i t
    have key := fun P (hP : P.under (𝓞 D.host.F) = v) =>
      (GlobalTheory.levCh_unramified_places D T0 R.toLevCh A.μ0 hL t).2.2.2 P fun PP hPP => by
        rw [hP]
        exact under_ne (hes PP (Finset.mem_union.2 hPP)) hv
    have u1 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 fun P hP => (key P hP).2 i
    have u2 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.xi t) v ε hv.1 fun P hP => (key P hP).1
    have u3 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P
    have u4 : GlobalTheory.WeilParts.UnramAt ε (R.toLevCh.mu t ((i : ℕ) + 1)) := fun x a b c => by
      show R.mu0 ((i : ℕ) + 1) x * R.xi t x = 1
      rw [u1 x a b c, u2 x a b c, one_mul]
    refine ⟨u4, fun x a b c => ?_⟩
    show R.toLevCh.mu t ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1
    rw [u4 x a b c, u3 x a b c, inv_one, one_mul]

/- English proof (translation)
Establish `hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t)`. Use `hP.pt_theta i t 1` as an intermediate fact. Unfold `RealDat.ptP pureTensorO at this`. Rewrite `this` using `[pureTensorL_one]`. Then use the resulting hypothesis. Use `⟨hθ, GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hP.vP i t) hθ, isCartanInv_cart _, fun τ => ?_, fun τ => isONBasis_onb _ τ _ (hM.order i τ)⟩` and prove the remaining obligations.

Establish `: gramAt D (Vc D i) τ = 1`. Unfold `gramAt`. Rewrite using `[hV.1]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Rewrite using `[this]`.

Conclude with `⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩`.
-/
theorem vec_fock_of_clauses (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.IsThP)
    (i : Fin D.R.m) (t : T0) (hV : VStd D i) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧
    (∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t)) ∧
    (∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ)) ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧
    ∀ τ, IsONBasis (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) (onb (R.MW i (sg0 D A)) τ) ((Wc D i).sig (tauE D τ)).1 := by
  have hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [pureTensorL_one] at this
  refine ⟨hθ, GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hP.vP i t) hθ,
    isCartanInv_cart _, fun τ => ?_, fun τ => isONBasis_onb _ τ _ (hM.order i τ)⟩
  have : gramAt D (Vc D i) τ = 1 := by
    unfold gramAt
    rw [hV.1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

/- English proof (translation)
The claim follows from `GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i)) (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)) ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hP.vP i A.μ0)`.
-/
theorem thetaVector_ne_zero_of_clauses (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0)
    (hP : R.IsThP) (i : Fin D.R.m) : R.vP i A.μ0 ≠ 0 :=
  GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hP.vP i A.μ0)

end GlobalTheory.AdTh.PhaseMapFree

namespace GlobalTheory.AdTh.PhaseMapFree
open GlobalTheory.AdTh.PhaseMap

end GlobalTheory.AdTh.PhaseMapFree

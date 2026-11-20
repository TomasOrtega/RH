import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMapsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivCoefNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow

noncomputable section

set_option maxHeartbeats 1600000

namespace GlobalTheory.Tow.LatHalf

variable {D : D7}

/- English proof (translation)
Take `⟨⟨es, hes, rfl⟩, -⟩` from `he`. Rewrite using `[map_sum, Finset.sum_mul, map_sum]`. Use `sum_mem fun PP hPP => ?_` and prove the remaining obligations. Use `GlobalTheory.ConjHalfInt.toEAf_mul_mem (GlobalTheory.IdemSupport.Comparison₂.conj ((hes PP hPP).2 : GlobalTheory.IdemSupport.Comparison₂ PP (es PP))) ?_ ha` and prove the remaining obligations. Conclude with `GlobalTheory.HalfCompare.primeToAA_of_not_mem ((GlobalTheory.StdFrames.natCast_mem_cP PP _).not.2 (hP PP hPP))`.
-/
theorem toEAf_cA_mul_mem {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((GlobalTheory.Tow.badN D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {a : D.host.E} (ha : a ∈ D.host.AA) :
    toEAf D (cA D e * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  refine GlobalTheory.ConjHalfInt.toEAf_mul_mem (GlobalTheory.IdemSupport.Comparison₂.conj ((hes PP hPP).2 : GlobalTheory.IdemSupport.Comparison₂ PP (es PP))) ?_ ha
  exact GlobalTheory.HalfCompare.primeToAA_of_not_mem ((GlobalTheory.StdFrames.natCast_mem_cP PP _).not.2 (hP PP hPP))

/- English proof (translation)
Establish `hx' : cA D e • x = x` using `Matrix.ext hx`. Rewrite using `[← hx']`. Use `GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapO E.V E.W E.βV E.βW (cA D e • u))) ?_ ?_ ?_ ?_ hl` and prove the remaining obligations. Introduce `α hα M hM`. Establish `hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)`.

Proceed by induction on `hM using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨a, ha, s, hs, t, ht, rfl⟩` from `hw`. Unfold `frMapO`. Rewrite using `[GlobalTheory.ConjHalfInt.map_gen, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc (E.βW⁻¹).val, Matrix.mul_assoc]`.

Conclude with `GlobalTheory.ConjHalfInt.isIntM_smul (mul_mem (toEAf_cA_mul_mem he hP ha) hα') (GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int E.frW ht) (GlobalTheory.ConjHalfInt.pair_row_int E.sdV E.frV hs))`. Consider the case `zero`. Rewrite using `[GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]`. Conclude with `fun _ _ => zero_mem _`. Consider the case `add M N _ _ hM hN`.

Rewrite using `[GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.ConjHalfInt.frMapO_add]`. Conclude with `fun i j => add_mem (hM i j) (hN i j)`. Consider the case `neg M _ hM`. Rewrite using `[GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]`. Conclude with `fun i j => neg_mem (hM i j)`.

Rewrite using `[smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]`. Conclude with `fun _ _ => zero_mem _`. Introduce `u v hu hv`. Rewrite using `[smul_add, GlobalTheory.ConjHalfInt.frMapO_add]`. Conclude with `fun i j => add_mem (hu i j) (hv i j)`.

Introduce `u hu`. Rewrite using `[smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]`. Conclude with `fun i j => neg_mem (hu i j)`.
-/
theorem isIntM_of_mem (E : ExpSet D) {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((GlobalTheory.Tow.badN D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {x : WO E.V E.W} (hx : IsHalf (cA D e) x)
    (hl : x ∈ lat E) : IsIntM (frMapO E.V E.W E.βV E.βW x) := by
  have hx' : cA D e • x = x := Matrix.ext hx
  rw [← hx']
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapO E.V E.W E.βV E.βW (cA D e • u))) ?_ ?_ ?_ ?_ hl
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      unfold frMapO
      rw [GlobalTheory.ConjHalfInt.map_gen, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc (E.βW⁻¹).val, Matrix.mul_assoc]
      exact GlobalTheory.ConjHalfInt.isIntM_smul (mul_mem (toEAf_cA_mul_mem he hP ha) hα')
        (GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int E.frW ht)
          (GlobalTheory.ConjHalfInt.pair_row_int E.sdV E.frV hs))
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.ConjHalfInt.frMapO_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.ConjHalfInt.frMapO_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]
    exact fun i j => neg_mem (hu i j)

open GlobalTheory.ExportSeries.Model in

/- English proof (translation)
Establish `e : x.map (toEAf D) = E.βW.val * frMapO E.V E.W E.βV E.βW x * (E.βV⁻¹).val`. Unfold `frMapO`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Use `int_mul (int_mul (gram_frame_int E.V E.sdV E.frV).2 (int_ct h)) (gram_frame_int E.W E.sdW E.frW).1` as an intermediate fact. Rewrite using `[GlobalTheory.PlaceVec.frMapAdj_eq]`.

Express the relevant statement in the definitionally equal form `IsIntM (_ * ct (x.map (toEAf D)) * _)`. Rewrite using `[e, ct_mul, ct_mul]`. Simplify `this` using `only [Matrix.mul_assoc]`.
-/
theorem isIntM_adj (E : ExpSet D) {x : WO E.V E.W} (h : IsIntM (frMapO E.V E.W E.βV E.βW x)) :
    IsIntM (frMapAdj E.V E.W E.βV E.βW x) := by
  have e : x.map (toEAf D) = E.βW.val * frMapO E.V E.W E.βV E.βW x * (E.βV⁻¹).val := by
    unfold frMapO
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  have := int_mul (int_mul (gram_frame_int E.V E.sdV E.frV).2 (int_ct h)) (gram_frame_int E.W E.sdW E.frW).1
  rw [GlobalTheory.PlaceVec.frMapAdj_eq]
  change IsIntM (_ * ct (x.map (toEAf D)) * _)
  rw [e, ct_mul, ct_mul]
  simpa only [Matrix.mul_assoc] using this

end GlobalTheory.Tow.LatHalf

end

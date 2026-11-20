import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceCut

/- English proof (translation)
Establish `i0 : infPart D e = 0` using `(GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) h).1`. Establish `a1 : GlobalTheory.RowRep.piAt w e = 1` using `(GlobalTheory.StdFrames.cpt_of_isIdemAt h).1`. Establish `a2 : ∀ u, u ≠ w → GlobalTheory.RowRep.piAt u e = 0` using `(GlobalTheory.StdFrames.cpt_of_isIdemAt h).2`. Establish `b1 : GlobalTheory.RowRep.piAt w' e' = 1` using `(GlobalTheory.StdFrames.cpt_of_isIdemAt h').1`. Establish `b2 : ∀ u, u ≠ w' → GlobalTheory.RowRep.piAt u e' = 0` using `(GlobalTheory.StdFrames.cpt_of_isIdemAt h').2`.

Establish `i1 : infPart D (e * e') = 0` using `((infPart D).map_mul e e').trans ((congrArg (· * infPart D e') i0).trans (zero_mul _))`. Use `⟨fun hw => ae_ext (i1.trans i0.symm) fun u => ?_, fun hw => ae_ext (i1.trans (infPart D).map_zero.symm) fun u => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `GlobalTheory.RowRep.piAt u (e * e') = GlobalTheory.RowRep.piAt u e`. Rewrite using `[RingHom.map_mul]`. Distinguish the cases in `hu : u = w`.

Substitute `hu` using the available equality. Substitute `hw` using the available equality. Rewrite using `[b1, mul_one]`. Rewrite using `[a2 u hu, zero_mul]`. Express the relevant statement in the definitionally equal form `GlobalTheory.RowRep.piAt u (e * e') = GlobalTheory.RowRep.piAt u 0`.

Rewrite using `[RingHom.map_mul, RingHom.map_zero]`. Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality. Rewrite using `[b2 u hw, mul_zero]`. Rewrite using `[a2 u hu, zero_mul]`.
-/
theorem idem_mul {D : D7} {e e' : AE D} {w w' : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') : (w = w' → e * e' = e) ∧ (w ≠ w' → e * e' = 0) := by
  have i0 : infPart D e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) h).1
  have a1 : GlobalTheory.RowRep.piAt w e = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h).1
  have a2 : ∀ u, u ≠ w → GlobalTheory.RowRep.piAt u e = 0 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h).2
  have b1 : GlobalTheory.RowRep.piAt w' e' = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h').1
  have b2 : ∀ u, u ≠ w' → GlobalTheory.RowRep.piAt u e' = 0 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h').2
  have i1 : infPart D (e * e') = 0 :=
    ((infPart D).map_mul e e').trans ((congrArg (· * infPart D e') i0).trans (zero_mul _))
  refine ⟨fun hw => ae_ext (i1.trans i0.symm) fun u => ?_, fun hw => ae_ext (i1.trans (infPart D).map_zero.symm) fun u => ?_⟩
  · change GlobalTheory.RowRep.piAt u (e * e') = GlobalTheory.RowRep.piAt u e
    rw [RingHom.map_mul]
    by_cases hu : u = w
    · subst hu; subst hw; rw [b1, mul_one]
    · rw [a2 u hu, zero_mul]
  · change GlobalTheory.RowRep.piAt u (e * e') = GlobalTheory.RowRep.piAt u 0
    rw [RingHom.map_mul, RingHom.map_zero]
    by_cases hu : u = w
    · subst hu; rw [b2 u hw, mul_zero]
    · rw [a2 u hu, zero_mul]

/- English proof (translation)
Establish `k : ∀ i ∈ P, a i * ∑ j ∈ P, a j = a i` using `fun i hi => by`. Rewrite using `[Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => h2 i hi j hj (Ne.symm hji)) (fun h => absurd hi h), h1 i hi]`. Introduce `i hi j hj`. Rewrite using `[← k i hi, ← k j hj, map_mul, mul_mul_mul_comm, h0, mul_zero]`.
-/
theorem mul_conj_zero {R ι : Type} [CommRing R] (c : R →+* R) (P : Finset ι) (a : ι → R)
    (h1 : ∀ i ∈ P, a i * a i = a i) (h2 : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → a i * a j = 0)
    (h0 : (∑ i ∈ P, a i) * c (∑ i ∈ P, a i) = 0) : ∀ i ∈ P, ∀ j ∈ P, a i * c (a j) = 0 := by
  have k : ∀ i ∈ P, a i * ∑ j ∈ P, a j = a i := fun i hi => by
    rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => h2 i hi j hj (Ne.symm hji)) (fun h => absurd hi h), h1 i hi]
  intro i hi j hj
  rw [← k i hi, ← k j hj, map_mul, mul_mul_mul_comm, h0, mul_zero]

/- English proof (translation)
Take the linear combination `h1 + h2 + 2 * h3`.
-/
theorem add_mul_self_eq_of_orthogonal_idempotents {R : Type} [CommRing R] {a b : R} (h1 : a * a = a) (h2 : b * b = b) (h3 : a * b = 0) :
    (a + b) * (a + b) = a + b := by linear_combination h1 + h2 + 2 * h3

/- English proof (translation)
Take the linear combination `h1 + h2 + h3 + h4`.
-/
theorem add_mul_add_eq_zero_of_pairwise_products_zero {R : Type} [CommRing R] {a b a' b' : R} (h1 : a * a' = 0) (h2 : b * b' = 0) (h3 : a * b' = 0)
    (h4 : a' * b = 0) : (a + b) * (a' + b') = 0 := by linear_combination h1 + h2 + h3 + h4

/- English proof (translation)
Establish `hb : f b = 0`. Use `congrArg f h0` as an intermediate fact. Rewrite `this` using `[map_mul, h1, one_mul, map_zero]`. Then use the resulting hypothesis. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, h1, hb]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_cut {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} {a b : R} (h1 : f a = 1) (h0 : a * b = 0)
    (M : Matrix (Fin n) (Fin n) R) :
    ((a + b) • M + (1 - (a + b)) • (1 : Matrix (Fin n) (Fin n) R)).map f = M.map f := by
  have hb : f b = 0 := by
    have := congrArg f h0
    rwa [map_mul, h1, one_mul, map_zero] at this
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, h1, hb]
  ring

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D V P es hes h0 r hr`. Establish `h1 : ∀ w ∈ P, es w * es w = es w` using `fun w hw => (idem_mul (hes w hw) (hes w hw)).1 rfl`. Establish `h2 : ∀ w ∈ P, ∀ w' ∈ P, w ≠ w' → es w * es w' = 0` using `fun w hw w' hw' => (idem_mul (hes w hw) (hes w' hw')).2`. Establish `h3` using `mul_conj_zero (cA D) P es h1 h2 h0`. Set `E : P → AE D` to `fun w => es w.1 + cA D (es w.1)`.

Establish `hEE : ∀ w, E w * E w = E w` using `fun w => add_mul_self_eq_of_orthogonal_idempotents (h1 _ w.2) (by rw [← RingHom.map_mul, h1 _ w.2]) (h3 _ w.2 _ w.2)`. Establish `hEc : ∀ w, cA D (E w) = E w` using `fun w => by show cA D (es w.1 + cA D (es w.1)) = es w.1 + cA D (es w.1)`. Rewrite using `[RingHom.map_add, cA_cA, add_comm]`. Establish `hEo : ∀ w w', w ≠ w' → E w * E w' = 0` using `fun w w' hww => by`. Use `h2 _ w.2 _ w'.2 fun h => hww (Subtype.ext h)` as an intermediate fact.

Conclude with `add_mul_add_eq_zero_of_pairwise_products_zero this (by rw [← RingHom.map_mul, this, RingHom.map_zero]) (h3 _ w.2 _ w'.2) (h3 _ w'.2 _ w.2)`. Use `choose h hh using fun w => GlobalTheory.SplitCut.cut_exists V r (E w) (hEE w) (hEc w)`. Use `⟨h, fun w i j => ?_, fun w => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hh w]`. Apply the tactic sequence `exact GlobalTheory.SplitCut.idempotent_mul_cut_sub_one_entry _ (hEE w) _ i j`.

Rewrite using `[hh w]`. Establish `a1 : GlobalTheory.RowRep.piAt w.1 (es w.1) = 1` using `(GlobalTheory.StdFrames.cpt_of_isIdemAt (hes _ w.2)).1`. Conclude with `map_cut (GlobalTheory.RowRep.piAt w.1) a1 (h3 _ w.2 _ w.2) _`. Apply `GlobalTheory.SplitCut.mt_injective` to reduce the goal to its premises. Establish `hsum : (Finset.univ.toList.map E).sum = (∑ w ∈ P, es w) + cA D (∑ w ∈ P, es w)`.

Rewrite using `[Finset.sum_map_toList, map_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_coe_sort P fun w => es w + cA D (es w)`. Rewrite using `[GlobalTheory.SplitCut.mt_list_prod V h E (mt V r) hh hEo _ (Finset.nodup_toList _), hsum]`. Use `GlobalTheory.SplitCut.exists_widePullback_of_iteratedLine _ _ fun i j => ?_` and prove the remaining obligations. Rewrite using `[sub_mul, one_mul, hr i j, sub_self]`.
-/
theorem exists_prod_pieces : ∀ {D : D7} (V : HSp D) (P : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ w ∈ P, Formalism.L2.NTheta.IsIdemAt (es w) w) → (∑ w ∈ P, es w) * cA D (∑ w ∈ P, es w) = 0 → ∀ r : GA D V, SuppAt (∑ w ∈ P, es w) V r → ∃ h : P → GA D V, (∀ w, SuppAt (es w.1) V (h w)) ∧ (∀ w, (mt V (h w)).map (GlobalTheory.RowRep.piAt w.1) = (mt V r).map (GlobalTheory.RowRep.piAt w.1)) ∧ r = (Finset.univ.toList.map h).prod := by
  intro D V P es hes h0 r hr
  have h1 : ∀ w ∈ P, es w * es w = es w := fun w hw => (idem_mul (hes w hw) (hes w hw)).1 rfl
  have h2 : ∀ w ∈ P, ∀ w' ∈ P, w ≠ w' → es w * es w' = 0 := fun w hw w' hw' => (idem_mul (hes w hw) (hes w' hw')).2
  have h3 := mul_conj_zero (cA D) P es h1 h2 h0
  let E : P → AE D := fun w => es w.1 + cA D (es w.1)
  have hEE : ∀ w, E w * E w = E w := fun w =>
    add_mul_self_eq_of_orthogonal_idempotents (h1 _ w.2) (by rw [← RingHom.map_mul, h1 _ w.2]) (h3 _ w.2 _ w.2)
  have hEc : ∀ w, cA D (E w) = E w := fun w => by
    show cA D (es w.1 + cA D (es w.1)) = es w.1 + cA D (es w.1)
    rw [RingHom.map_add, cA_cA, add_comm]
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    have := h2 _ w.2 _ w'.2 fun h => hww (Subtype.ext h)
    exact add_mul_add_eq_zero_of_pairwise_products_zero this (by rw [← RingHom.map_mul, this, RingHom.map_zero]) (h3 _ w.2 _ w'.2) (h3 _ w'.2 _ w.2)
  choose h hh using fun w => GlobalTheory.SplitCut.cut_exists V r (E w) (hEE w) (hEc w)
  refine ⟨h, fun w i j => ?_, fun w => ?_, ?_⟩
  · rw [hh w]
    exact GlobalTheory.SplitCut.idempotent_mul_cut_sub_one_entry _ (hEE w) _ i j
  · rw [hh w]
    have a1 : GlobalTheory.RowRep.piAt w.1 (es w.1) = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes _ w.2)).1
    exact map_cut (GlobalTheory.RowRep.piAt w.1) a1 (h3 _ w.2 _ w.2) _
  · apply GlobalTheory.SplitCut.mt_injective
    have hsum : (Finset.univ.toList.map E).sum = (∑ w ∈ P, es w) + cA D (∑ w ∈ P, es w) := by
      rw [Finset.sum_map_toList, map_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_coe_sort P fun w => es w + cA D (es w)
    rw [GlobalTheory.SplitCut.mt_list_prod V h E (mt V r) hh hEo _ (Finset.nodup_toList _), hsum]
    refine GlobalTheory.SplitCut.exists_widePullback_of_iteratedLine _ _ fun i j => ?_
    rw [sub_mul, one_mul, hr i j, sub_self]

end GlobalTheory.PlaceCut

end

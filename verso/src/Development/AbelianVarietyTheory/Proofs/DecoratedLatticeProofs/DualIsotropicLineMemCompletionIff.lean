import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLatticeDualZIdealMul
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorDisjointSupportSmulAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DualLine

variable {D : D7}

/- English proof (translation)
Proceed by induction on `ha using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨α, -, hα, b, -, rfl⟩` from `hx`. Conclude with `GlobalTheory.FinPl.LatMem.tmul_mem_idAt (fun w hw => hα w hw) b`. Consider the case `zero => exact zero_mem _`.

Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `neg x _ hx => exact neg_mem hx`.
-/
theorem idV_le_idAt {𝔞 : FI D} {v : Pl D} {a : AE D} (ha : a ∈ idV 𝔞 v) : a ∈ idAt D (· = v) := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, hα, b, -, rfl⟩ := hx
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt (fun w hw => hα w hw) b
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

/- English proof (translation)
Rewrite `h`, the goal using `[GlobalTheory.FinPl.Model.mem_idAt_iff]`. Rewrite `h`, the goal using `[← Algebra.smul_def]`. Use `conv_rhs => rw [← h]`. Rewrite using `[GlobalTheory.HeisDisj.cA_smul]`.
-/
theorem cA_mem_idAt {v : Pl D} {a : AE D} (h : a ∈ idAt D (· = v)) : cA D a ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

/- English proof (translation)
Proceed by induction on `hc using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨α, hαi, hα, a, ha, rfl⟩` from `hx`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Take `⟨o', ho'⟩` from `GlobalTheory.FinPl.LatMem.star_int o`.

Use `AddSubgroup.subset_closure ⟨α, hαi, hα, (o' : D.host.E), (FractionalIdeal.mem_one_iff _).2 ⟨o', rfl⟩, ?_⟩` and prove the remaining obligations. Use `show pairA D.host.F 0 α ⊗ₜ[D.host.F] star ((o : D.host.E)) = _`. Rewrite using `[ho']`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `neg_mem hx`.
-/
theorem cA_mem_idV_one {v : Pl D} {c : AE D} (hc : c ∈ idV (1 : FI D) v) : cA D c ∈ idV (1 : FI D) v := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨o', ho'⟩ := GlobalTheory.FinPl.LatMem.star_int o
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, (o' : D.host.E), (FractionalIdeal.mem_one_iff _).2 ⟨o', rfl⟩, ?_⟩
    show pairA D.host.F 0 α ⊗ₜ[D.host.F] star ((o : D.host.E)) = _
    rw [ho']
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

/- English proof (translation)
Proceed by induction on `hc using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨α, hαi, hα, a, ha, rfl⟩` from `hx`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Use `AddSubgroup.subset_closure ⟨α, hαi, fun w hw => hα w hw, 1, rfl, o • s, L.smul_mem o hs, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `l`. Use `show (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] s l) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Pi.smul_apply, Algebra.smul_def]`. Consider the case `zero`. Establish `: (fun a => (0 : AE D) * incA D (s a)) = 0` using `funext fun a => zero_mul _`.

Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `: (fun a => (x + y) * incA D (s a)) = (fun a => x * incA D (s a)) + fun a => y * incA D (s a)`. Use function extensionality and compare the values at `fun a => add_mul _ _ _`.

Rewrite using `[this]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx`. Establish `: (fun a => (-x) * incA D (s a)) = -fun a => x * incA D (s a)` using `funext fun a => neg_mul _ _`. Rewrite using `[this]`.

Conclude with `neg_mem hx`.
-/
theorem mul_incA_mem {S : HSp D} {L : Lat S} {v : Pl D} {c : AE D} (hc : c ∈ idV (1 : FI D) v)
    {s : Fin S.rank → D.host.E} (hs : s ∈ L) : (fun a => c * incA D (s a)) ∈ latV S L (· = v) := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    refine AddSubgroup.subset_closure ⟨α, hαi, fun w hw => hα w hw, 1, rfl, o • s, L.smul_mem o hs, ?_⟩
    funext l
    show (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] s l) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Pi.smul_apply, Algebra.smul_def]
  | zero =>
    have : (fun a => (0 : AE D) * incA D (s a)) = 0 := funext fun a => zero_mul _
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun a => (x + y) * incA D (s a)) = (fun a => x * incA D (s a)) + fun a => y * incA D (s a) :=
      funext fun a => add_mul _ _ _
    rw [this]; exact add_mem hx hy
  | neg x _ hx =>
    have : (fun a => (-x) * incA D (s a)) = -fun a => x * incA D (s a) := funext fun a => neg_mul _ _
    rw [this]; exact neg_mem hx

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

variable {D : D7}

def hA (S : HSp D) (w y : Fin S.rank → AE D) : AE D := ∑ a, ∑ b, cA D (y a) * gA S a b * w b

/- English proof (translation)
Simplify using `only [hA, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hA_add_left (S : HSp D) (w w' y : Fin S.rank → AE D) : hA S (w + w') y = hA S w y + hA S w' y := by
  simp only [hA, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hA, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]`.
-/
theorem hA_neg_left (S : HSp D) (w y : Fin S.rank → AE D) : hA S (-w) y = -hA S w y := by
  simp only [hA, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/- English proof (translation)
Simplify using `only [hA, Pi.zero_apply, mul_zero, Finset.sum_const_zero]`.
-/
theorem hA_zero_left (S : HSp D) (y : Fin S.rank → AE D) : hA S 0 y = 0 := by
  simp only [hA, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/- English proof (translation)
Simplify using `only [hA, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hA_add_right (S : HSp D) (w y y' : Fin S.rank → AE D) : hA S w (y + y') = hA S w y + hA S w y' := by
  simp only [hA, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hA, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]`.
-/
theorem hA_neg_right (S : HSp D) (w y : Fin S.rank → AE D) : hA S w (-y) = -hA S w y := by
  simp only [hA, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

/- English proof (translation)
Simplify using `only [hA, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]`.
-/
theorem hA_zero_right (S : HSp D) (w : Fin S.rank → AE D) : hA S w 0 = 0 := by
  simp only [hA, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy'`. Take `⟨β, hβi, hβ, c, hc, x', hx', rfl⟩` from `hy'`. Rewrite `hc` using `[Set.mem_singleton_iff]`. Substitute `hc` using the available equality.

Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw'`. Take `⟨α, hαi, hα, c, hc, x, hx, rfl⟩` from `hw'`. Rewrite `hc` using `[Set.mem_singleton_iff]`. Substitute `hc` using the available equality.

Take `⟨b, hb⟩` from `(hL.2 x).1 hx x' hx'`. Establish `hp : pairA D.host.F 0 β * pairA D.host.F 0 α = pairA D.host.F 0 (β * α)` using `Prod.ext (zero_mul _) rfl`. Establish `e : hA S (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) = pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (b : D.host.E)`. Rewrite using `[hb, TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show (pairA D.host.F 0 β ⊗ₜ[D.host.F] star (1 * x' a)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram a k) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x k)) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp, one_mul, one_mul]`. Rewrite using `[e]`.

Conclude with `AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi, fun w hw => by rw [map_mul, hβ w hw, zero_mul], (b : D.host.E), (FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩, rfl⟩`. Consider the case `zero => rw [hA_zero_left]`. Conclude with `zero_mem _`. Consider the case `add w w' _ _ h h' => rw [hA_add_left]`. Conclude with `add_mem h h'`.

Consider the case `neg w _ h => rw [hA_neg_left]`. Conclude with `neg_mem h`. Consider the case `zero => rw [hA_zero_right]`. Conclude with `zero_mem _`. Consider the case `add y y' _ _ h h' => rw [hA_add_right]`.

Conclude with `add_mem h h'`. Consider the case `neg y _ h => rw [hA_neg_right]`. Conclude with `neg_mem h`.
-/
theorem hA_mem {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) {v : Pl D} {w y : Fin S.rank → AE D}
    (hw : w ∈ latV S L (· = v)) (hy : y ∈ latV S L (· = v)) : hA S w y ∈ idV (1 : FI D) v := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    obtain ⟨β, hβi, hβ, c, hc, x', hx', rfl⟩ := hy'
    rw [Set.mem_singleton_iff] at hc
    subst hc
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨α, hαi, hα, c, hc, x, hx, rfl⟩ := hw'
      rw [Set.mem_singleton_iff] at hc
      subst hc
      obtain ⟨b, hb⟩ := (hL.2 x).1 hx x' hx'
      have hp : pairA D.host.F 0 β * pairA D.host.F 0 α = pairA D.host.F 0 (β * α) := Prod.ext (zero_mul _) rfl
      have e : hA S (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
          pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (b : D.host.E) := by
        rw [hb, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        show (pairA D.host.F 0 β ⊗ₜ[D.host.F] star (1 * x' a)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram a k) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x k)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp, one_mul, one_mul]
      rw [e]
      exact AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi,
        fun w hw => by rw [map_mul, hβ w hw, zero_mul], (b : D.host.E), (FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩, rfl⟩
    | zero => rw [hA_zero_left]; exact zero_mem _
    | add w w' _ _ h h' => rw [hA_add_left]; exact add_mem h h'
    | neg w _ h => rw [hA_neg_left]; exact neg_mem h
  | zero => rw [hA_zero_right]; exact zero_mem _
  | add y y' _ _ h h' => rw [hA_add_right]; exact add_mem h h'
  | neg y _ h => rw [hA_neg_right]; exact neg_mem h

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

variable {D : D7}

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c e => show c ⊗ₜ[D.host.F] star (star e) = _`. Rewrite using `[star_star]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem cA_cA' (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c e => show c ⊗ₜ[D.host.F] star (star e) = _; rw [star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
The claim follows from `congrArg (incA D) (GlobalTheory.LatVac.gram_star S a b)`.
-/
theorem cA_gA (S : HSp D) (a b : Fin S.rank) : cA D (gA S a b) = incA D (S.gram b a) :=
  congrArg (incA D) (GlobalTheory.LatVac.gram_star S a b)

/- English proof (translation)
Take `⟨m, s, s', hs, hs', hdual⟩` from `GlobalTheory.FinPl.LatMem.exists_dualBasis S hL`. Use `set ι : AE D := pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) with hι`. Use `set w : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 * s' i l) with hwdef`. Establish `hw : ∀ i, w i ∈ latV S L (· = v)` using `fun i => AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' _ _, GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _, 1, rfl, s' i, hs' i, rfl⟩`. Establish `hcw : ∀ i l, cA D (w i l) = ι * incA D (star (s' i l))` using `fun i l => by show pairA D.host.F 0 _ ⊗ₜ[D.host.F] star (1 * s' i l) = (pairA D.host.F 0 _ ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] star (s' i l))`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, one_mul]`. Establish `hyeq : y = ∑ i, fun a => cA D (hA S (w i) y) * incA D (s i a)`. Use function extensionality and compare the values at `a`. Rewrite using `[Finset.sum_apply]`. Establish `e1 : y a = ∑ a', y a' * ι * incA D (∑ i, s i a * ∑ k, star (s' i k) * S.gram k a')`.

Simplify using `only [hdual]`. Rewrite using `[Finset.sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, mul_zero]) (fun h => absurd (Finset.mem_univ a) h), if_pos rfl, map_one, mul_one]`. Conclude with `(GlobalTheory.FinPl.LatMem.mul_indP (hyAt a)).symm`. Rewrite using `[e1]`. Simplify using `only [hA, map_sum, map_mul, cA_cA', cA_gA, hcw, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hyeq]`. Conclude with `sum_mem fun i _ => mul_incA_mem (cA_mem_idV_one (h _ (hw i))) (hs i)`.
-/
theorem mem_of_hA {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) {v : Pl D} {y : Fin S.rank → AE D}
    (hyAt : ∀ a, y a ∈ idAt D (· = v)) (h : ∀ w ∈ latV S L (· = v), hA S w y ∈ idV (1 : FI D) v) :
    y ∈ latV S L (· = v) := by
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hL
  set ι : AE D := pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) with hι
  set w : Fin m → Fin S.rank → AE D := fun i l =>
    pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 * s' i l) with hwdef
  have hw : ∀ i, w i ∈ latV S L (· = v) := fun i => AddSubgroup.subset_closure
    ⟨_, GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' _ _, GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _, 1, rfl, s' i, hs' i, rfl⟩
  have hcw : ∀ i l, cA D (w i l) = ι * incA D (star (s' i l)) := fun i l => by
    show pairA D.host.F 0 _ ⊗ₜ[D.host.F] star (1 * s' i l) = (pairA D.host.F 0 _ ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] star (s' i l))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, one_mul]
  have hyeq : y = ∑ i, fun a => cA D (hA S (w i) y) * incA D (s i a) := by
    funext a
    rw [Finset.sum_apply]
    have e1 : y a = ∑ a', y a' * ι * incA D (∑ i, s i a * ∑ k, star (s' i k) * S.gram k a') := by
      simp only [hdual]
      rw [Finset.sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, mul_zero])
        (fun h => absurd (Finset.mem_univ a) h), if_pos rfl, map_one, mul_one]
      exact (GlobalTheory.FinPl.LatMem.mul_indP (hyAt a)).symm
    rw [e1]
    simp only [hA, map_sum, map_mul, cA_cA', cA_gA, hcw, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hyeq]
  exact sum_mem fun i _ => mul_incA_mem (cA_mem_idV_one (h _ (hw i))) (hs i)

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

/- English proof (translation)
Introduce `D ψ hψ S S₀ ρ d L L₀ 𝔟 v hL hM i hb t ht`. Establish `I2` using `(GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v).2.1 (𝔟 i) 1 hb one_ne_zero (cA D t) (cA_mem_idAt ht)`. Rewrite `I2` using `[one_mul]`. Establish `hH : ∀ w, hA S w (colMul d.jY i t) = cA D t * (d.pX *ᵥ w) i`. Introduce `w`.

Rewrite using `[d.pX_eq]`. Simplify using `only [hA, colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, map_mul, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `show cA D t * cA D (d.jY a i) * gA S a b * w b = cA D t * (cA D (d.jY a i) * gA S a b * w b)`.

Expand and normalize the polynomial expressions, which then agree. Establish `hPX : ∀ a, (d.pX *ᵥ colMul d.jX i a) i = a`. Introduce `a`. Establish `h1` using `congrFun (congrFun d.pX_jX i) i`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.one_apply_eq]`.

Simplify using `only [Matrix.mulVec, dotProduct, colMul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring`. Use `_ = a := by rw [h1, mul_one]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Use `I2.1 fun a ha => ?_` and prove the remaining obligations. Establish `hx` using `(hM.2 i a (idV_le_idAt ha)).2 ha`. Establish `h2` using `hA_mem hL hx hy`. Rewrite `h2` using `[hH, hPX]`. Then use the resulting hypothesis.

Introduce `hc`. Establish `hall` using `I2.2 hc`. Use `mem_of_hA hL (fun k => Ideal.mul_mem_right _ _ ht) fun w hw => ?_` and prove the remaining obligations. Rewrite using `[hH]`. Establish `hwAt` using `GlobalTheory.FinPlLoc.latV_idAt hw`.

Establish `heAt : (d.pX *ᵥ w) i ∈ idAt D (· = v)` using `by show ∑ b, d.pX i b * w b ∈ idAt D (· = v)`. Use `exact`. Use the proof step `Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ (d.pX i b) (hwAt b)`. Conclude with `hall _ ((hM.2 i _ heAt).1 (((hM.1 w).1 hw).1 i))`.
-/
theorem dualLine_mem_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D), IsSelfDualC S L → MonoId d L L₀ 𝔟 v → ∀ i : Fin ρ, 𝔟 i ≠ 0 →
      ∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latV S L (· = v) ↔ cA D t ∈ idV (𝔟 i)⁻¹ v := by
  intro D ψ hψ S S₀ ρ d L L₀ 𝔟 v hL hM i hb t ht
  have I2 := (GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v).2.1 (𝔟 i) 1 hb one_ne_zero (cA D t) (cA_mem_idAt ht)
  rw [one_mul] at I2
  have hH : ∀ w, hA S w (colMul d.jY i t) = cA D t * (d.pX *ᵥ w) i := by
    intro w
    rw [d.pX_eq]
    simp only [hA, colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    show cA D t * cA D (d.jY a i) * gA S a b * w b = cA D t * (cA D (d.jY a i) * gA S a b * w b)
    ring
  have hPX : ∀ a, (d.pX *ᵥ colMul d.jX i a) i = a := by
    intro a
    have h1 := congrFun (congrFun d.pX_jX i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simp only [Matrix.mulVec, dotProduct, colMul]
    calc ∑ k, d.pX i k * (a * d.jX k i) = a * ∑ k, d.pX i k * d.jX k i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = a := by rw [h1, mul_one]
  constructor
  · intro hy
    refine I2.1 fun a ha => ?_
    have hx := (hM.2 i a (idV_le_idAt ha)).2 ha
    have h2 := hA_mem hL hx hy
    rwa [hH, hPX] at h2
  · intro hc
    have hall := I2.2 hc
    refine mem_of_hA hL (fun k => Ideal.mul_mem_right _ _ ht) fun w hw => ?_
    rw [hH]
    have hwAt := GlobalTheory.FinPlLoc.latV_idAt hw
    have heAt : (d.pX *ᵥ w) i ∈ idAt D (· = v) := by
      show ∑ b, d.pX i b * w b ∈ idAt D (· = v)
      exact
      Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ (d.pX i b) (hwAt b)
    exact hall _ ((hM.2 i _ heAt).1 (((hM.1 w).1 hw).1 i))

end GlobalTheory.DualLine

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.SelfDualCompl

open GlobalTheory.FinPlLoc

variable {D : D7}

/- English proof (translation)
Use `show Algebra.TensorProduct.map (AlgHom.id _ _) _ (a ⊗ₜ[D.host.F] e) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.
-/
theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) _ (a ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

def hA (S : HSp D) (y s : Fin S.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j

/- English proof (translation)
Assemble the required witnesses or components as `⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩`.
-/
theorem intAt_zero (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩`.
-/
theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩`.
-/
theorem intAt_neg {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩

/- English proof (translation)
Simplify using `[hA]`.
-/
theorem hA_zero_left (S : HSp D) (s : Fin S.rank → AE D) : hA S 0 s = 0 := by
  simp [hA]

/- English proof (translation)
Simplify using `[hA, mul_add, Finset.sum_add_distrib]`.
-/
theorem hA_add_left (S : HSp D) (y y' s : Fin S.rank → AE D) : hA S (y + y') s = hA S y s + hA S y' s := by
  simp [hA, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hA, Finset.sum_neg_distrib]`.
-/
theorem hA_neg_left (S : HSp D) (y s : Fin S.rank → AE D) : hA S (-y) s = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

/- English proof (translation)
Simplify using `[hA]`.
-/
theorem hA_zero_right (S : HSp D) (y : Fin S.rank → AE D) : hA S y 0 = 0 := by
  simp [hA]

/- English proof (translation)
Simplify using `[hA, add_mul, Finset.sum_add_distrib]`.
-/
theorem hA_add_right (S : HSp D) (y s s' : Fin S.rank → AE D) : hA S y (s + s') = hA S y s + hA S y s' := by
  simp [hA, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hA, Finset.sum_neg_distrib]`.
-/
theorem hA_neg_right (S : HSp D) (y s : Fin S.rank → AE D) : hA S y (-s) = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

/- English proof (translation)
Simplify using `only [hA, cA_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum, pairA_mul]`.
-/
theorem hA_gen (S : HSp D) (α β : Af D.host.F) (x x' : Fin S.rank → D.host.E) :
    hA S (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x j)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (∑ i, ∑ j, star (x' i) * HSpace.gram S i j * x j) := by
  simp only [hA, cA_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum,
    pairA_mul]

/- English proof (translation)
Proceed by induction on `hs using AddSubgroup.closure_induction with`. Consider the case `mem s hs`. Take `⟨β, hβi, hβ, a, ha, x', hx', rfl⟩` from `hs`. Rewrite `ha` using `[Set.mem_singleton_iff]`. Substitute `ha` using the available equality.

Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hαi, hα, a, ha, x, hx, rfl⟩` from `hy`. Rewrite `ha` using `[Set.mem_singleton_iff]`. Substitute `ha` using the available equality.

Rewrite using `[hA_gen]`. Take `⟨c, hc⟩` from `(hS.2 x).1 hx x' hx'`. Rewrite using `[← hc]`. Use `⟨pair_mem_idAt P _ (fun v hv => by rw [map_mul, hα v hv, mul_zero]) _, ?_⟩` and prove the remaining obligations. Rewrite using `[finPart_pair]`.

Conclude with `AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi, c, rfl⟩`. Consider the case `zero => rw [hA_zero_left]`. Conclude with `intAt_zero P`. Consider the case `add y y' _ _ h h' => rw [hA_add_left]`. Conclude with `intAt_add h h'`.

Consider the case `neg y _ h => rw [hA_neg_left]`. Conclude with `intAt_neg h`. Consider the case `zero => rw [hA_zero_right]`. Conclude with `intAt_zero P`. Consider the case `add s s' _ _ h h' => rw [hA_add_right]`.

Conclude with `intAt_add h h'`. Consider the case `neg s _ h => rw [hA_neg_right]`. Conclude with `intAt_neg h`.
-/
theorem hA_mem {S : HSp D} {LS : Lat S} (hS : IsSelfDualC S LS) {P : Pl D → Prop} {y s : Fin S.rank → AE D}
    (hy : y ∈ latV S LS P) (hs : s ∈ latV S LS P) : hA S y s ∈ intAt D P := by
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨β, hβi, hβ, a, ha, x', hx', rfl⟩ := hs
    rw [Set.mem_singleton_iff] at ha
    subst ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [hA_gen]
      obtain ⟨c, hc⟩ := (hS.2 x).1 hx x' hx'
      rw [← hc]
      refine ⟨pair_mem_idAt P _ (fun v hv => by rw [map_mul, hα v hv, mul_zero]) _, ?_⟩
      rw [finPart_pair]
      exact AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi, c, rfl⟩
    | zero => rw [hA_zero_left]; exact intAt_zero P
    | add y y' _ _ h h' => rw [hA_add_left]; exact intAt_add h h'
    | neg y _ h => rw [hA_neg_left]; exact intAt_neg h
  | zero => rw [hA_zero_right]; exact intAt_zero P
  | add s s' _ _ h h' => rw [hA_add_right]; exact intAt_add h h'
  | neg s _ h => rw [hA_neg_right]; exact intAt_neg h

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, o, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨ePl D P * a, GlobalTheory.FinPl.LatMem.intAf_mul' (ePl_int P) ha, fun w hw => by rw [map_mul, evalV_ePl, if_neg hw, zero_mul], 1, rfl, o • s, LS.smul_mem o hs, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, idem, finIn_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, pairA_mul, mul_one, one_mul]`. Use `congr 1`. Consider the case `zero => rw [map_zero, mul_zero, zero_smul]`. Conclude with `zero_mem _`. Consider the case `add z z' _ _ h h' => rw [map_add, mul_add, add_smul]`.

Conclude with `add_mem h h'`. Consider the case `neg z _ h => rw [map_neg, mul_neg, neg_smul]`. Conclude with `neg_mem h`.
-/
theorem wachExpansion_smul_compatible {S : HSp D} {LS : Lat S} (P : Pl D → Prop) {s : Fin S.rank → D.host.E} (hs : s ∈ LS)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (idem D P * finIn D z) • (fun l => incA D (s l)) ∈ latV S LS P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨ePl D P * a, GlobalTheory.FinPl.LatMem.intAf_mul' (ePl_int P) ha,
      fun w hw => by rw [map_mul, evalV_ePl, if_neg hw, zero_mul], 1, rfl, o • s, LS.smul_mem o hs, ?_⟩
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, idem, finIn_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, pairA_mul,
      mul_one, one_mul]
    congr 1
  | zero => rw [map_zero, mul_zero, zero_smul]; exact zero_mem _
  | add z z' _ _ h h' => rw [map_add, mul_add, add_smul]; exact add_mem h h'
  | neg z _ h => rw [map_neg, mul_neg, neg_smul]; exact neg_mem h

/- English proof (translation)
Establish `h1 : idem D P * c = c` using `(mem_idAt_iff P c).1 hc.1`. Establish `h2 : c = finIn D (finPart D c)` using `eq_finIn (infPart_of_idAt hc.1)`. Use `wachExpansion_smul_compatible P hs hc.2` as an intermediate fact. Rewrite `this` using `[← h2, h1]`. Then use the resulting hypothesis.
-/
theorem smul_mem {S : HSp D} {LS : Lat S} {P : Pl D → Prop} {c : AE D} (hc : c ∈ intAt D P) {s : Fin S.rank → D.host.E}
    (hs : s ∈ LS) : c • (fun l => incA D (s l)) ∈ latV S LS P := by
  have h1 : idem D P * c = c := (mem_idAt_iff P c).1 hc.1
  have h2 : c = finIn D (finPart D c) := eq_finIn (infPart_of_idAt hc.1)
  have := wachExpansion_smul_compatible P hs hc.2
  rwa [← h2, h1] at this

/- English proof (translation)
Rewrite using `[cA_tmul, idem, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, mul_one]`.
-/
theorem cA_test (P : Pl D → Prop) (e : D.host.E) :
    cA D (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * e)) = idem D P * incA D (star e) := by
  rw [cA_tmul, idem, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, mul_one]

/- English proof (translation)
Introduce `D S LS hS P y hy`. Use `⟨fun h s hs => hA_mem hS h hs, fun h => ?_⟩` and prove the remaining obligations. Take `⟨m, s, s', hs, hs', hdual⟩` from `GlobalTheory.FinPl.LatMem.exists_dualBasis S hS`. Set `t : Fin m → Fin S.rank → AE D` to `fun i l => pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * s' i l)`. Establish `ht : ∀ i, t i ∈ latV S LS P` using `fun i => AddSubgroup.subset_closure ⟨ePl D P, ePl_int P, fun w hw => by rw [evalV_ePl, if_neg hw], 1, rfl, s' i, hs' i, rfl⟩`.

Establish `hyeq : y = ∑ i, hA S y (t i) • (fun a => incA D (s i a))`. Use function extensionality and compare the values at `a`. Establish `hya : y a = idem D P * y a` using `((mem_idAt_iff P (y a)).1 (hy a)).symm`. Establish `hsum : ∀ j, idem D P * y j * incA D (if a = j then 1 else 0) = if a = j then idem D P * y j else 0`. Introduce `j`.

Apply the tactic sequence `split_ifs <;> simp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_congr rfl fun j _ => hsum j, Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]`. Conclude with `hya`. Use `_ = ∑ j, idem D P * y j * incA D (∑ i, s i a * ∑ k, star (s' i k) * HSpace.gram S k j) := by`.

Simplify using `only [hdual]`. Use `_ = _ := by`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hA, t, cA_test, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hyeq]`. Conclude with `sum_mem fun i _ => smul_mem (h (t i) (ht i)) (hs i)`.
-/
theorem selfDual_latV : ∀ (D : D7) (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ (P : Pl D → Prop)
    (y : Fin S.rank → AE D), (∀ r, y r ∈ idAt D P) →
    (y ∈ latV S LS P ↔ ∀ s ∈ latV S LS P, (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j) ∈ intAt D P) := by
  intro D S LS hS P y hy
  refine ⟨fun h s hs => hA_mem hS h hs, fun h => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hS
  let t : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * s' i l)
  have ht : ∀ i, t i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨ePl D P, ePl_int P, fun w hw => by rw [evalV_ePl, if_neg hw], 1, rfl, s' i, hs' i, rfl⟩
  have hyeq : y = ∑ i, hA S y (t i) • (fun a => incA D (s i a)) := by
    funext a
    have hya : y a = idem D P * y a := ((mem_idAt_iff P (y a)).1 (hy a)).symm
    have hsum : ∀ j, idem D P * y j * incA D (if a = j then 1 else 0) = if a = j then idem D P * y j else 0 := by
      intro j
      split_ifs <;> simp
    calc y a = ∑ j, idem D P * y j * incA D (if a = j then 1 else 0) := by
          rw [Finset.sum_congr rfl fun j _ => hsum j, Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]
          exact hya
      _ = ∑ j, idem D P * y j * incA D (∑ i, s i a * ∑ k, star (s' i k) * HSpace.gram S k j) := by
          simp only [hdual]
      _ = _ := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hA, t, cA_test, map_sum, map_mul, Finset.mul_sum,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  rw [hyeq]
  exact sum_mem fun i _ => smul_mem (h (t i) (ht i)) (hs i)

end GlobalTheory.FinPl.SelfDualCompl

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumFixedByLevelPairAtSelfDualPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QProd

open GlobalTheory.FinPl in
/- English proof (translation)
Rewrite using `[(GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.2.1]`. Simplify using `only [not_not]`.
-/
theorem at_eq' {D : D7} (V : HSp D) (P : Pl D → Prop) : grpAt V P = GfC V ⊓ grpOff V (fun p => ¬ P p) := by
  rw [(GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.2.1]
  simp only [not_not]

open GlobalTheory.FinPl in
/- English proof (translation)
The claim follows from `(GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.1 P P' h`.
-/
theorem at_le_off' {D : D7} (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' :=
  (GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.1 P P' h

open GlobalTheory.FinPl in

/- English proof (translation)
Unfold `grpOff at h ⊢`. Rewrite `h`, the goal using `[GlobalTheory.FinPlLoc.mem_congGrp]`. Introduce `a b`. Use `h a b` as an intermediate fact. Unfold `idOff at this ⊢`.

Rewrite `this`, the goal using `[Submodule.mem_iInf]`. Introduce `u`. Conclude with `this ⟨u.1, hR u.1 u.2⟩`.
-/
theorem off_mono {D : D7} {V : HSp D} {R R' : Pl D → Prop} (hR : ∀ p, R' p → R p) {g : GA D V} (h : g ∈ grpOff V R) :
    g ∈ grpOff V R' := by
  unfold grpOff at h ⊢
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at h ⊢
  intro a b
  have := h a b
  unfold idOff at this ⊢
  rw [Submodule.mem_iInf] at this ⊢
  intro u
  exact this ⟨u.1, hR u.1 u.2⟩

open GlobalTheory.FinPl in

/- English proof (translation)
Unfold `grpOff`. Rewrite using `[GlobalTheory.FinPlLoc.mem_congGrp]`. Introduce `a b`. Unfold `idOff`. Rewrite using `[Submodule.mem_iInf]`.

Introduce `u`. Establish `hu` using `h u.1 u.2`. Unfold `grpOff at hu`. Rewrite `hu` using `[GlobalTheory.FinPlLoc.mem_congGrp]`. Use `hu a b` as an intermediate fact.

Unfold `idOff at this`. Rewrite `this` using `[Submodule.mem_iInf]`. Conclude with `this ⟨u.1, rfl⟩`.
-/
theorem off_of_each {D : D7} {V : HSp D} {R : Pl D → Prop} {g : GA D V} (h : ∀ p, R p → g ∈ grpOff V (· = p)) :
    g ∈ grpOff V R := by
  unfold grpOff
  rw [GlobalTheory.FinPlLoc.mem_congGrp]
  intro a b
  unfold idOff
  rw [Submodule.mem_iInf]
  intro u
  have hu := h u.1 u.2
  unfold grpOff at hu
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at hu
  have := hu a b
  unfold idOff at this
  rw [Submodule.mem_iInf] at this
  exact this ⟨u.1, rfl⟩

/- English proof (translation)
Introduce `D c v t w F hF j σ h`. Establish `hd : ∀ i, j + 1 + (2 * σ + 2) = (F.Q i).s + 1` using `fun i => by have := (F.Q i).hs; omega`. Establish `key` using `fun i => GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V (j + 1)) ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) ((F.Q i).FY (j + 1) (2 * σ + 2) (hd i)) ((F.Q i).gl (j + 1) (2 * σ + 2) (hd i)) ((F.Q i).gl_loc (j + 1) (2 * σ + 2) (hd i))`. Set `gl` to `fun i => (F.Q i).gl (j + 1) (2 * σ + 2) (hd i)`. Establish `hoff : ∀ i i', i ≠ i' → ∀ g, gl i' g ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v)`.

Introduce `i i' hne g`. Establish `hr : gl i' g ∈ (gl i').range` using `⟨g, rfl⟩`. Rewrite `hr` using `[(key i').2.1]`. Conclude with `at_le_off' _ (fun p hp hq => hne (hF.inj (hq.symm.trans hp))) hr`. Establish `hcomm : Pairwise fun i i' => ∀ x y, Commute (gl i x) (gl i' y)`.

Introduce `i i' hne x y`. Conclude with `(key i).2.2.2.1 x _ (hoff i i' hne y)`. Establish `hmem : ∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, gl i (y i) ∈ H) → MonoidHom.noncommPiCoprod gl hcomm y ∈ H`. Introduce `H y hy`. Conclude with `Submonoid.noncommProd_mem H.toSubmonoid Finset.univ _ (fun _ _ _ _ h => hcomm h _ _) (fun i _ => hy i)`.

Establish `hat : ∀ i g, gl i g ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q)`. Introduce `i g`. Establish `hr : gl i g ∈ (gl i).range` using `⟨g, rfl⟩`. Rewrite `hr` using `[(key i).2.1]`. Rewrite `hr`, the goal using `[at_eq']`.

Use `⟨hr.1, off_mono (fun p hp hq => hp ((hF.places p).2 ⟨i, hq.symm⟩)) hr.2⟩` and prove the remaining obligations. Use `⟨MonoidHom.noncommPiCoprod gl hcomm, hmem, fun y => hmem _ y fun i => hat i (y i), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Use `choose y hy _ using fun i => (key i).2.2.1 x`. Use `set P := MonoidHom.noncommPiCoprod gl hcomm`.

Establish `hsplit : ∀ i, P y = P (Function.update y i 1) * gl i (y i)`. Introduce `i`. Establish `hy' : y = Function.update y i 1 * Pi.mulSingle i (y i)`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk]`. Use `conv_lhs => rw [hy']`. Rewrite using `[map_mul, MonoidHom.noncommPiCoprod_mulSingle]`.

Establish `hrest : ∀ i, P (Function.update y i 1) ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v)`. Introduce `i`. Use `hmem _ _ fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hk]`. Conclude with `hoff i k (Ne.symm hk) _`. Establish `hz_i : ∀ i, x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v)`. Introduce `i`.

Rewrite using `[hsplit i, _root_.mul_inv_rev, ← mul_assoc]`. Conclude with `Subgroup.mul_mem _ (hy i) (Subgroup.inv_mem _ (hrest i))`. Establish `hzQ : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q)` using `Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hmem _ y fun i => hat i (y i)))`. Rewrite `hzQ` using `[at_eq']`. Establish `hall : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (fun _ => ¬ False)`.

Use `off_of_each fun p _ => ?_` and prove the remaining obligations. Distinguish the cases in `hp : p ∈ w.Q`. Take `⟨i, rfl⟩` from `(hF.places p).1 hp`. Conclude with `hz_i i`. Conclude with `off_mono (fun p' hp' => hp'.symm ▸ hp) hzQ.2`.

Establish `hz1 : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (fun _ => False)`. Rewrite using `[at_eq']`. Conclude with `⟨hzQ.1, hall⟩`. Use `GlobalTheory.VacFixP.eq_one_of_grpAt (fun _ h => h) hz1` as an intermediate fact. Conclude with `⟨y, mul_inv_eq_one.1 this, hy⟩`.
-/
theorem prod_local : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ P : (∀ i, GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k) →* GA D (c.V (j + 1)), (∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i) ∈ H) → P y ∈ H) ∧ (∀ y, P y ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), ∃ y, x = P y ∧ ∀ i, x * ((F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
  intro D c v t w F hF j σ h
  have hd : ∀ i, j + 1 + (2 * σ + 2) = (F.Q i).s + 1 := fun i => by have := (F.Q i).hs; omega
  have key := fun i => GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V (j + 1)) ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2))
    ((F.Q i).FY (j + 1) (2 * σ + 2) (hd i)) ((F.Q i).gl (j + 1) (2 * σ + 2) (hd i)) ((F.Q i).gl_loc (j + 1) (2 * σ + 2) (hd i))
  let gl := fun i => (F.Q i).gl (j + 1) (2 * σ + 2) (hd i)
  have hoff : ∀ i i', i ≠ i' → ∀ g, gl i' g ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i i' hne g
    have hr : gl i' g ∈ (gl i').range := ⟨g, rfl⟩
    rw [(key i').2.1] at hr
    exact at_le_off' _ (fun p hp hq => hne (hF.inj (hq.symm.trans hp))) hr
  have hcomm : Pairwise fun i i' => ∀ x y, Commute (gl i x) (gl i' y) := by
    intro i i' hne x y
    exact (key i).2.2.2.1 x _ (hoff i i' hne y)
  have hmem : ∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, gl i (y i) ∈ H) →
      MonoidHom.noncommPiCoprod gl hcomm y ∈ H := by
    intro H y hy
    exact Submonoid.noncommProd_mem H.toSubmonoid Finset.univ _ (fun _ _ _ _ h => hcomm h _ _) (fun i _ => hy i)
  have hat : ∀ i g, gl i g ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q) := by
    intro i g
    have hr : gl i g ∈ (gl i).range := ⟨g, rfl⟩
    rw [(key i).2.1] at hr
    rw [at_eq'] at hr ⊢
    refine ⟨hr.1, off_mono (fun p hp hq => hp ((hF.places p).2 ⟨i, hq.symm⟩)) hr.2⟩
  refine ⟨MonoidHom.noncommPiCoprod gl hcomm, hmem, fun y => hmem _ y fun i => hat i (y i), ?_⟩
  intro x hx
  choose y hy _ using fun i => (key i).2.2.1 x
  set P := MonoidHom.noncommPiCoprod gl hcomm
  have hsplit : ∀ i, P y = P (Function.update y i 1) * gl i (y i) := by
    intro i
    have hy' : y = Function.update y i 1 * Pi.mulSingle i (y i) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    conv_lhs => rw [hy']
    rw [map_mul, MonoidHom.noncommPiCoprod_mulSingle]
  have hrest : ∀ i, P (Function.update y i 1) ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i
    refine hmem _ _ fun k => ?_
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk]
      exact hoff i k (Ne.symm hk) _
  have hz_i : ∀ i, x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i
    rw [hsplit i, _root_.mul_inv_rev, ← mul_assoc]
    exact Subgroup.mul_mem _ (hy i) (Subgroup.inv_mem _ (hrest i))
  have hzQ : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q) :=
    Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hmem _ y fun i => hat i (y i)))
  rw [at_eq'] at hzQ
  have hall : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (fun _ => ¬ False) := by
    refine off_of_each fun p _ => ?_
    by_cases hp : p ∈ w.Q
    · obtain ⟨i, rfl⟩ := (hF.places p).1 hp
      exact hz_i i
    · exact off_mono (fun p' hp' => hp'.symm ▸ hp) hzQ.2
  have hz1 : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (fun _ => False) := by
    rw [at_eq']
    exact ⟨hzQ.1, hall⟩
  have := GlobalTheory.VacFixP.eq_one_of_grpAt (fun _ h => h) hz1
  exact ⟨y, mul_inv_eq_one.1 this, hy⟩

end GlobalTheory.QProd
end

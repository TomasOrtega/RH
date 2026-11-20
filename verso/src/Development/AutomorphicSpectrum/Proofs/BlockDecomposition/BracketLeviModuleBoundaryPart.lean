import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionPreservesSupportDegree
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionCommutesWithTotalBoundary
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionIsGlRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BracketWedgeFormula

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.LeviQ

open CompanionTheory.D.LK (Pos)
open CompanionTheory.RgExh.U (adC)

variable {n : ℕ}

/- English proof (translation)
Unfold `CompanionTheory.D.LK.key`. Establish `h1` using `p.1.1.2`. Establish `h2` using `p.1.2.2`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem key_lt' (p : Pos n) : CompanionTheory.D.LK.key p < (n + 1) * (n + 1) := by
  unfold CompanionTheory.D.LK.key
  have h1 := p.1.1.2
  have h2 := p.1.2.2
  nlinarith

/- English proof (translation)
Take `⟨a, i⟩` from `i`. Take `⟨b, j⟩` from `j`. Establish `hi` using `key_lt' i`. Establish `hj` using `key_lt' j`. Apply the tactic sequence `cases a <;> cases b <;> simp only [keyL, Bool.false_eq_true, if_false, if_true, zero_add] at h`.

Rewrite using `[CompanionTheory.D.LK.Car.key_inj (Nat.add_left_cancel h)]`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Rewrite using `[CompanionTheory.D.LK.Car.key_inj h]`.
-/
theorem keyL_inj {i j : Lt n} (h : keyL i = keyL j) : i = j := by
  obtain ⟨a, i⟩ := i
  obtain ⟨b, j⟩ := j
  have hi := key_lt' i
  have hj := key_lt' j
  cases a <;> cases b <;> simp only [keyL, Bool.false_eq_true, if_false, if_true, zero_add] at h
  · rw [CompanionTheory.D.LK.Car.key_inj (Nat.add_left_cancel h)]
  · omega
  · omega
  · rw [CompanionTheory.D.LK.Car.key_inj h]

def tw (i j : Lt n) : ℂ := if keyL j < keyL i then -1 else 1

/- English proof (translation)
Simplify using `[tw]`.
-/
theorem tw_self (i : Lt n) : tw i i = 1 := by simp [tw]

/- English proof (translation)
Apply the tactic sequence `unfold tw; split_ifs <;> simp`.
-/
theorem tw_mul_self (i j : Lt n) : tw i j * tw i j = 1 := by
  unfold tw; split_ifs <;> simp

/- English proof (translation)
Establish `hk : keyL i ≠ keyL j` using `fun e => h (keyL_inj e)`. Unfold `tw`. Break down `lt_or_gt_of_ne hk with h1 | h1` into its components or cases. Simplify using `[h1, h1.not_gt]`. Simplify using `[h1, h1.not_gt]`.
-/
theorem tw_swap {i j : Lt n} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : keyL i ≠ keyL j := fun e => h (keyL_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

/- English proof (translation)
Unfold `sgL`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem sg_mul_self (i : Lt n) (A : Finset (Lt n)) : sgL i A * sgL i A = 1 := by
  unfold sgL
  rw [← mul_pow]; simp

/- English proof (translation)
Unfold `sgL tw`. Rewrite using `[Finset.filter_insert]`. Use `split_ifs with hk`. Rewrite using `[Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules.
-/
theorem sg_insert (i : Lt n) {j : Lt n} {A : Finset (Lt n)} (h : j ∉ A) :
    sgL i (insert j A) = tw i j * sgL i A := by
  unfold sgL tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

/- English proof (translation)
Establish `h1` using `sg_insert i (Finset.notMem_erase j A)`. Rewrite `h1` using `[Finset.insert_erase h]`. Rewrite using `[h1, ← mul_assoc, tw_mul_self, one_mul]`.
-/
theorem sg_erase (i : Lt n) {j : Lt n} {A : Finset (Lt n)} (h : j ∈ A) :
    sgL i (A.erase j) = tw i j * sgL i A := by
  have h1 := sg_insert i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem annq_apply (i : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    annq i x A = if i ∈ A then 0 else sgL i A • x (insert i A) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem creq_apply (i : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    creq i x A = if i ∈ A then sgL i A • x (A.erase i) else 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftq_apply (T : Module.End ℂ V) (x : Cq n V) (A : Finset (Lt n)) :
    liftq n T x A = T (x A) := rfl

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply, annq_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Establish `hji : j ≠ i` using `fun e => hij e.symm`. Distinguish the cases in `hi : i ∈ A`. Simplify using `[hi]`. Distinguish the cases in `hj : j ∈ A`. Simplify using `[hj]`.

Simplify using `only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]`. Rewrite using `[sg_insert j hi, sg_insert i hj, tw_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]`. Establish `: sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0` using `by ring`. Rewrite using `[this, zero_smul]`.
-/
theorem annq_annq (i j : Lt n) : (annq i * annq j + annq j * annq i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    annq_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert j hi, sg_insert i hj, tw_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply, creq_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Establish `hji : j ≠ i` using `fun e => hij e.symm`. Distinguish the cases in `hi : i ∈ A`. Use `swap`. Simplify using `[hi]`. Distinguish the cases in `hj : j ∈ A`.

Use `swap`. Simplify using `[hj]`. Simplify using `only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]`. Rewrite using `[sg_erase j hi, sg_erase i hj, tw_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul, ← add_smul]`. Establish `: sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0` using `by ring`.

Rewrite using `[this, zero_smul]`.
-/
theorem creq_creq (i j : Lt n) : (creq i * creq j + creq j * creq i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    creq_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]
  rw [sg_erase j hi, sg_erase i hj, tw_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, annq_apply, creq_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Distinguish the cases in `hi : i ∈ A`.

Simplify using `[hi, sg_erase i hi, tw_self, smul_smul, sg_mul_self, Finset.insert_erase hi]`. Simplify using `[hi, sg_insert i hi, tw_self, smul_smul, sg_mul_self, Finset.erase_insert hi]`. Establish `hji : j ≠ i` using `fun e => hij e.symm`. Rewrite using `[if_neg hij, LinearMap.zero_apply, Pi.zero_apply]`. Distinguish the cases in `hi : i ∈ A`.

Simplify using `[hi, hij]`. Distinguish the cases in `hj : j ∈ A`. Use `swap`. Simplify using `[hj, hji]`. Simplify using `only [hi, hj, Finset.mem_insert, Finset.mem_erase, or_true, and_false, if_true, if_false]`.

Rewrite using `[sg_insert j hi, sg_erase i hj, tw_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul, ← add_smul]`. Establish `: sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0` using `by ring`. Rewrite using `[this, zero_smul]`.
-/
theorem annq_creq (i j : Lt n) :
    (annq i * creq j + creq j * annq i : Module.End ℂ (Cq n V)) = if i = j then 1 else 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, annq_apply, creq_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ A
    · simp [hi, sg_erase i hi, tw_self, smul_smul, sg_mul_self, Finset.insert_erase hi]
    · simp [hi, sg_insert i hi, tw_self, smul_smul, sg_mul_self, Finset.erase_insert hi]
  have hji : j ≠ i := fun e => hij e.symm
  rw [if_neg hij, LinearMap.zero_apply, Pi.zero_apply]
  by_cases hi : i ∈ A
  · simp [hi, hij]
  by_cases hj : j ∈ A
  swap
  · simp [hj, hji]
  simp only [hi, hj, Finset.mem_insert, Finset.mem_erase, or_true, and_false, if_true, if_false]
  rw [sg_insert j hi, sg_erase i hj, tw_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul,
    ← add_smul]
  have : sgL i A * (-tw i j * sgL j A) + sgL j A * (tw i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `[liftq_apply, LinearMap.sum_apply, Finset.sum_apply]`.
-/
theorem liftq_sum_smul {κ : Type*} [Fintype κ] (d : κ → ℂ) (T : κ → Module.End ℂ V) :
    (liftq n (∑ k, d k • T k) : Module.End ℂ (Cq n V)) = ∑ k, d k • (liftq n (T k) : Module.End ℂ (Cq n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp [liftq_apply, LinearMap.sum_apply, Finset.sum_apply]

open GlobalTheory.CompanionTheory.RealMult.TorC (br Dm br_mul br_add_left br_add_right br_smul_right br_sum_right br_anti dm_a dm_c bracket_wedge_formula
  br_lift_dm)

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `only [br, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, LinearMap.zero_apply, Pi.zero_apply, annq_apply, liftq_apply]`. Apply the tactic sequence `by_cases hi : i ∈ A <;> simp [hi]`.
-/
theorem br_lift_annq (T : Module.End ℂ V) (i : Lt n) :
    br (liftq n T : Module.End ℂ (Cq n V)) (annq i) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [br, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, LinearMap.zero_apply, Pi.zero_apply,
    annq_apply, liftq_apply]
  by_cases hi : i ∈ A <;> simp [hi]

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `only [br, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, LinearMap.zero_apply, Pi.zero_apply, creq_apply, liftq_apply]`. Apply the tactic sequence `by_cases hi : i ∈ A <;> simp [hi]`.
-/
theorem br_lift_creq (T : Module.End ℂ V) (i : Lt n) :
    br (liftq n T : Module.End ℂ (Cq n V)) (creq i) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [br, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, LinearMap.zero_apply, Pi.zero_apply,
    creq_apply, liftq_apply]
  by_cases hi : i ∈ A <;> simp [hi]

/- English proof (translation)
Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `[br, liftq_apply]`.
-/
theorem br_lift_lift (T S : Module.End ℂ V) :
    br (liftq n T : Module.End ℂ (Cq n V)) (liftq n S) = liftq n (br T S) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp [br, liftq_apply]

def Mt (s : Bool) (p q : Fin n) (l m : Lt n) : ℂ := if m.1 = (s == l.1) then adC p q l.2 m.2 else 0

def Sq (l1 l2 l3 : Lt n) : ℂ :=
  if l3.1 = (l1.1 == l2.1) then GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc l1.2 l2.2 l3.2 else 0

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single (s == l.1)]`. Simplify using `[Mt]`. Introduce `b _ hb`. Conclude with `Finset.sum_eq_zero fun k _ => by simp [Mt, hb]`. Simplify using the standard rewrite rules.
-/
theorem sum_Mt {M : Type*} [AddCommMonoid M] [Module ℂ M] (s : Bool) (p q : Fin n) (l : Lt n) (f : Lt n → M) :
    ∑ m, Mt s p q l m • f m = ∑ k : Pos n, adC p q l.2 k • f ((s == l.1), k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (s == l.1)]
  · simp [Mt]
  · intro b _ hb
    exact Finset.sum_eq_zero fun k _ => by simp [Mt, hb]
  · simp

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single (l1.1 == l2.1)]`. Simplify using `[Sq]`. Introduce `b _ hb`. Conclude with `Finset.sum_eq_zero fun k _ => by simp [Sq, hb]`. Simplify using the standard rewrite rules.
-/
theorem sum_Sq {M : Type*} [AddCommMonoid M] [Module ℂ M] (l1 l2 : Lt n) (f : Lt n → M) :
    ∑ m, Sq l1 l2 m • f m = ∑ k : Pos n, GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc l1.2 l2.2 k • f ((l1.1 == l2.1), k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (l1.1 == l2.1)]
  · simp [Sq]
  · intro b _ hb
    exact Finset.sum_eq_zero fun k _ => by simp [Sq, hb]
  · simp

/- English proof (translation)
Unfold `adLq Dm`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[sum_Mt]`.
-/
theorem adLq_eq (s : Bool) (p q : Fin n) :
    (adLq s p q : Module.End ℂ (Cq n V)) = Dm annq creq (Mt s p q) := by
  unfold adLq Dm
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
  rw [sum_Mt]

def cubicBoundaryPart (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module.End ℂ (Cq n V) :=
  ∑ l1 : Lt n, ∑ l2 : Lt n, ∑ l3 : Lt n, Sq l1 l2 l3 • (creq l3 * annq l2 * annq l1)

def moduleBoundaryPart (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cq n V) :=
  ∑ l : Lt n, (liftq n (Tl E1 E2 l) : Module.End ℂ (Cq n V)) * annq l

/- English proof (translation)
Unfold `bdq moduleBoundaryPart cubicBoundaryPart`. Use `congr 1`. Simplify using `only [sum_Sq]`. Simplify using `only [Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2`. Simplify using `[GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc, h]`. Simplify using `[GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc, h]`.
-/
theorem bdq_eq (E1 E2 : Fin n → Fin n → Module.End ℂ V) : bdq E1 E2 = moduleBoundaryPart E1 E2 + cubicBoundaryPart n V := by
  unfold bdq moduleBoundaryPart cubicBoundaryPart
  congr 1
  simp only [sum_Sq]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  by_cases h : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2
  · simp [GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc, h]
  · simp [GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc, h]

section Ops

variable (E1 E2 : Fin n → Fin n → Module.End ℂ V)

/- English proof (translation)
The claim follows from `annq_annq i j`.
-/
theorem aa (i j : Lt n) : (annq i * annq j + annq j * annq i : Module.End ℂ (Cq n V)) = 0 := annq_annq i j
/- English proof (translation)
The claim follows from `creq_creq i j`.
-/
theorem cc (i j : Lt n) : (creq i * creq j + creq j * creq i : Module.End ℂ (Cq n V)) = 0 := creq_creq i j
/- English proof (translation)
The claim follows from `annq_creq i j`.
-/
theorem ac (i j : Lt n) : (annq i * creq j + creq j * annq i : Module.End ℂ (Cq n V)) = if i = j then 1 else 0 :=
  annq_creq i j

/- English proof (translation)
Rewrite using `[lFq, adLq_eq]`.
-/
theorem lFq_eq (s : Bool) (p q : Fin n) :
    lFq E1 E2 s p q = liftq n (Ts E1 E2 s p q) + Dm annq creq (Mt s p q) := by
  rw [lFq, adLq_eq]

/- English proof (translation)
Rewrite using `[lFq_eq, br_add_left, br_lift_annq, zero_add, dm_a aa ac]`.
-/
theorem br_L_ann (s : Bool) (p q : Fin n) (m : Lt n) :
    br (lFq E1 E2 s p q) (annq m) = -∑ i, Mt s p q i m • annq i := by
  rw [lFq_eq, br_add_left, br_lift_annq, zero_add, dm_a aa ac]

/- English proof (translation)
Rewrite using `[br_anti, br_lift_dm (fun i => br_lift_annq T i) (fun i => br_lift_creq T i), neg_zero]`.
-/
theorem br_dm_lift (A : Lt n → Lt n → ℂ) (T : Module.End ℂ V) :
    br (Dm annq creq A) (liftq n T : Module.End ℂ (Cq n V)) = 0 := by
  rw [br_anti, br_lift_dm (fun i => br_lift_annq T i) (fun i => br_lift_creq T i), neg_zero]

/- English proof (translation)
Rewrite using `[lFq_eq, br_add_left, br_lift_lift, br_dm_lift, add_zero]`.
-/
theorem br_L_lift (s : Bool) (p q : Fin n) (T : Module.End ℂ V) :
    br (lFq E1 E2 s p q) (liftq n T) = liftq n (br (Ts E1 E2 s p q) T) := by
  rw [lFq_eq, br_add_left, br_lift_lift, br_dm_lift, add_zero]

/- English proof (translation)
Establish `hsub : ∀ S T : Module.End ℂ V, (liftq n (S - T) : Module.End ℂ (Cq n V)) = liftq n S - liftq n T` using `fun S T => by`. Use `LinearMap.ext fun x => funext fun A => ?_` and prove the remaining obligations. Simplify using `[liftq_apply]`. Unfold `moduleBoundaryPart`. Simplify using `only [br_sum_right, br_mul, br_L_lift, br_L_ann, hsub, liftq_sum_smul, sub_mul, Finset.sum_mul, mul_neg, Finset.mul_sum, mul_smul_comm, smul_mul_assoc, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]`.

Rewrite using `[sub_eq_add_neg]`. Use `congr 2`. Conclude with `Finset.sum_comm`.
-/
theorem bracket_levi_moduleBoundaryPart (s : Bool) (p q : Fin n) :
    br (lFq E1 E2 s p q) (moduleBoundaryPart E1 E2) =
      ∑ l : Lt n, (liftq n (br (Ts E1 E2 s p q) (Tl E1 E2 l) - ∑ m, Mt s p q l m • Tl E1 E2 m) :
        Module.End ℂ (Cq n V)) * annq l := by
  have hsub : ∀ S T : Module.End ℂ V, (liftq n (S - T) : Module.End ℂ (Cq n V)) = liftq n S - liftq n T := fun S T => by
    refine LinearMap.ext fun x => funext fun A => ?_
    simp [liftq_apply]
  unfold moduleBoundaryPart
  simp only [br_sum_right, br_mul, br_L_lift, br_L_ann, hsub, liftq_sum_smul, sub_mul, Finset.sum_mul, mul_neg,
    Finset.mul_sum, mul_smul_comm, smul_mul_assoc, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]
  congr 2
  exact Finset.sum_comm

/- English proof (translation)
Rewrite using `[lFq_eq, br_add_left]`. Establish `h0 : br (liftq n (Ts E1 E2 s p q) : Module.End ℂ (Cq n V)) (cubicBoundaryPart n V) = 0`. Simplify using `only [cubicBoundaryPart, br_sum_right, br_smul_right, br_mul, br_lift_annq, br_lift_creq, zero_mul, mul_zero, add_zero, smul_zero, Finset.sum_const_zero]`. Rewrite using `[h0, zero_add]`. Unfold `cubicBoundaryPart`.

Establish `hW` using `fun l1 l2 l3 => bracket_wedge_formula (R := Module.End ℂ (Cq n V)) (ι := Lt n) (a := annq) (c := creq) aa cc ac (Mt s p q) l1 l2 l3`. Simplify using `only [br_sum_right, br_smul_right, hW]`. Conclude with `GlobalTheory.CompanionTheory.RealMult.TorC.reindex (R := Module.End ℂ (Cq n V)) (fun i j k => creq k * annq j * annq i) Sq (Mt s p q)`.
-/
theorem bracket_levi_cubicBoundaryPart (s : Bool) (p q : Fin n) :
    br (lFq E1 E2 s p q) (cubicBoundaryPart n V) =
      ∑ l1 : Lt n, ∑ l2 : Lt n, ∑ l3 : Lt n,
        ((∑ m, Sq l1 l2 m * Mt s p q m l3) - (∑ m, Sq l1 m l3 * Mt s p q l2 m) - ∑ m, Sq m l2 l3 * Mt s p q l1 m) •
          (creq l3 * annq l2 * annq l1) := by
  rw [lFq_eq, br_add_left]
  have h0 : br (liftq n (Ts E1 E2 s p q) : Module.End ℂ (Cq n V)) (cubicBoundaryPart n V) = 0 := by
    simp only [cubicBoundaryPart, br_sum_right, br_smul_right, br_mul, br_lift_annq, br_lift_creq, zero_mul, mul_zero, add_zero,
      smul_zero, Finset.sum_const_zero]
  rw [h0, zero_add]
  unfold cubicBoundaryPart
  have hW := fun l1 l2 l3 => bracket_wedge_formula (R := Module.End ℂ (Cq n V)) (ι := Lt n) (a := annq) (c := creq) aa cc ac (Mt s p q) l1 l2 l3
  simp only [br_sum_right, br_smul_right, hW]
  exact GlobalTheory.CompanionTheory.RealMult.TorC.reindex (R := Module.End ℂ (Cq n V)) (fun i j k => creq k * annq j * annq i) Sq (Mt s p q)

end Ops

/- English proof (translation)
Take `⟨a, i⟩` from `l1`. Take `⟨b, j⟩` from `l2`. Take `⟨c, k⟩` from `l3`. Establish `e1 : ∑ m, Sq (a, i) (b, j) m * Mt s p q m (c, k) = ∑ m : Pos n, GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc i j m * Mt s p q ((a == b), m) (c, k)`. Simplify `sum_Sq (a, i) (b, j) (fun m => Mt s p q m (c, k))` using `only [smul_eq_mul]`.

Establish `e2 : ∑ m, Sq (a, i) m (c, k) * Mt s p q (b, j) m = ∑ m : Pos n, adC p q j m * Sq (a, i) ((s == b), m) (c, k)`. Simplify `sum_Mt s p q (b, j) (fun m => Sq (a, i) m (c, k))` using `only [smul_eq_mul, mul_comm]`. Establish `e3 : ∑ m, Sq m (b, j) (c, k) * Mt s p q (a, i) m = ∑ m : Pos n, adC p q i m * Sq ((s == a), m) (b, j) (c, k)`. Simplify `sum_Mt s p q (a, i) (fun m => Sq m (b, j) (c, k))` using `only [smul_eq_mul, mul_comm]`. Rewrite using `[e1, e2, e3]`.

Establish `hD` using `GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.Dc_eq_zero (p := p) (q := q) hm hpq (a := i) (b := j) h1 h2 k`. Unfold `GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.Dc at hD`. Distinguish the cases in `hc : c = (s == (a == b))`. Establish `i1 : c = (s == (a == b))` using `hc`. Apply the tactic sequence `have i2 : c = (a == (s == b)) := by rw [hc]; cases s <;> cases a <;> cases b <;> rfl`.

Apply the tactic sequence `have i3 : c = ((s == a) == b) := by rw [hc]; cases s <;> cases a <;> cases b <;> rfl`. Simplify using `only [Mt, Sq, i1.symm, i2.symm, i3.symm, if_true]`. Simplify using `only [mul_comm (adC p q j _), mul_comm (adC p q i _)]`. Conclude with `hD`. Apply the tactic sequence `have i2 : ¬c = (a == (s == b)) := fun e => hc (by rw [e]; cases s <;> cases a <;> cases b <;> rfl)`.

Apply the tactic sequence `have i3 : ¬c = ((s == a) == b) := fun e => hc (by rw [e]; cases s <;> cases a <;> cases b <;> rfl)`. Simplify using `[Mt, Sq, hc, i2, i3]`.
-/
theorem coef_zero {lev : Fin n → ℕ} (hm : Monotone lev) {s : Bool} {p q : Fin n} (hpq : lev p = lev q) {l1 l2 : Lt n}
    (h1 : inUL lev l1) (h2 : inUL lev l2) (l3 : Lt n) :
    (∑ m, Sq l1 l2 m * Mt s p q m l3) - (∑ m, Sq l1 m l3 * Mt s p q l2 m) - ∑ m, Sq m l2 l3 * Mt s p q l1 m = 0 := by
  obtain ⟨a, i⟩ := l1
  obtain ⟨b, j⟩ := l2
  obtain ⟨c, k⟩ := l3
  have e1 : ∑ m, Sq (a, i) (b, j) m * Mt s p q m (c, k) =
      ∑ m : Pos n, GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.tc i j m * Mt s p q ((a == b), m) (c, k) := by
    simpa only [smul_eq_mul] using sum_Sq (a, i) (b, j) (fun m => Mt s p q m (c, k))
  have e2 : ∑ m, Sq (a, i) m (c, k) * Mt s p q (b, j) m =
      ∑ m : Pos n, adC p q j m * Sq (a, i) ((s == b), m) (c, k) := by
    simpa only [smul_eq_mul, mul_comm] using sum_Mt s p q (b, j) (fun m => Sq (a, i) m (c, k))
  have e3 : ∑ m, Sq m (b, j) (c, k) * Mt s p q (a, i) m =
      ∑ m : Pos n, adC p q i m * Sq ((s == a), m) (b, j) (c, k) := by
    simpa only [smul_eq_mul, mul_comm] using sum_Mt s p q (a, i) (fun m => Sq m (b, j) (c, k))
  rw [e1, e2, e3]
  have hD := GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.Dc_eq_zero (p := p) (q := q) hm hpq (a := i) (b := j) h1 h2 k
  unfold GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.Dc at hD
  by_cases hc : c = (s == (a == b))
  · have i1 : c = (s == (a == b)) := hc
    have i2 : c = (a == (s == b)) := by rw [hc]; cases s <;> cases a <;> cases b <;> rfl
    have i3 : c = ((s == a) == b) := by rw [hc]; cases s <;> cases a <;> cases b <;> rfl
    simp only [Mt, Sq, i1.symm, i2.symm, i3.symm, if_true]
    simp only [mul_comm (adC p q j _), mul_comm (adC p q i _)]
    exact hD
  · have i2 : ¬c = (a == (s == b)) := fun e => hc (by rw [e]; cases s <;> cases a <;> cases b <;> rfl)
    have i3 : ¬c = ((s == a) == b) := fun e => hc (by rw [e]; cases s <;> cases a <;> cases b <;> rfl)
    simp [Mt, Sq, hc, i2, i3]

section Abs

variable {R ι : Type*} [Ring R] [Algebra ℂ R] [Fintype ι] [DecidableEq ι] {a c : ι → R}

open GlobalTheory.CompanionTheory.RealMult.TorC (swap3)

/- English proof (translation)
Establish `h1 : ∑ m, ∑ l, B m l • ((∑ x, A l x • c x) * a m) = ∑ m, ∑ x, (∑ l, B m l * A l x) • (c x * a m)` using `sum_congr rfl fun m _ => by`. Simplify using `only [sum_mul, smul_mul_assoc, smul_sum, smul_smul, sum_smul]`. Conclude with `sum_comm`. Establish `h2 : ∑ m, ∑ l, B m l • (c l * ∑ i, A i m • a i) = ∑ i, ∑ l, (∑ m, A i m * B m l) • (c l * a i)`. Simplify using `only [mul_sum, mul_smul_comm, smul_sum, smul_smul, sum_smul]`.

Rewrite using `[swap3 (fun m l i => (B m l * A i m) • (c l * a i))]`. Conclude with `sum_congr rfl fun i _ => sum_congr rfl fun l _ => sum_congr rfl fun m _ => by rw [mul_comm]`. Establish `h3 : br (Dm a c A) (Dm a c B) = (∑ m, ∑ l, B m l • ((∑ x, A l x • c x) * a m)) - ∑ m, ∑ l, B m l • (c l * ∑ i, A i m • a i)` using `by conv_lhs => rw [Dm.eq_1 a c B]`. Simplify using `only [br_sum_right, br_smul_right, br_mul, dm_a haa hac, dm_c hcc hac, mul_neg, smul_add, smul_neg, sum_add_distrib, sum_neg_distrib, sub_eq_add_neg]`. Rewrite using `[h3, h1, h2]`.

Simplify using `only [sub_smul, sum_sub_distrib]`.
-/
theorem br_dm_gen (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A B : ι → ι → ℂ) :
    br (Dm a c A) (Dm a c B) =
      ∑ i, ∑ l, ((∑ m, B i m * A m l) - ∑ m, A i m * B m l) • (c l * a i) := by
  have h1 : ∑ m, ∑ l, B m l • ((∑ x, A l x • c x) * a m) = ∑ m, ∑ x, (∑ l, B m l * A l x) • (c x * a m) :=
    sum_congr rfl fun m _ => by
      simp only [sum_mul, smul_mul_assoc, smul_sum, smul_smul, sum_smul]; exact sum_comm
  have h2 : ∑ m, ∑ l, B m l • (c l * ∑ i, A i m • a i) = ∑ i, ∑ l, (∑ m, A i m * B m l) • (c l * a i) := by
    simp only [mul_sum, mul_smul_comm, smul_sum, smul_smul, sum_smul]
    rw [swap3 (fun m l i => (B m l * A i m) • (c l * a i))]
    exact sum_congr rfl fun i _ => sum_congr rfl fun l _ => sum_congr rfl fun m _ => by rw [mul_comm]
  have h3 : br (Dm a c A) (Dm a c B) =
      (∑ m, ∑ l, B m l • ((∑ x, A l x • c x) * a m)) - ∑ m, ∑ l, B m l • (c l * ∑ i, A i m • a i) := by
    conv_lhs => rw [Dm.eq_1 a c B]
    simp only [br_sum_right, br_smul_right, br_mul, dm_a haa hac, dm_c hcc hac, mul_neg, smul_add, smul_neg,
      sum_add_distrib, sum_neg_distrib, sub_eq_add_neg]
  rw [h3, h1, h2]
  simp only [sub_smul, sum_sub_distrib]

end Abs

def eps (s : Bool) : ℂ := if s then 1 else -1

/- English proof (translation)
Apply the tactic sequence `cases s <;> cases t <;> simp [eps]`.
-/
theorem eps_mul (s t : Bool) : eps s * eps t = eps (s == t) := by
  cases s <;> cases t <;> simp [eps]

section Rel

variable {E1 E2 : Fin n → Fin n → Module.End ℂ V}

/- English proof (translation)
Apply the tactic sequence `cases s <;> simp [Ts, eps, sub_eq_add_neg]`.
-/
theorem Ts_eq (s : Bool) (p q : Fin n) : Ts E1 E2 s p q = E1 p q + eps s • E2 p q := by
  cases s <;> simp [Ts, eps, sub_eq_add_neg]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `g1` using `h1 p q r v`. Establish `g2` using `h2 p q r v`. Establish `c1 : E1 p q * E2 r v = E2 r v * E1 p q` using `h3 p q r v`. Establish `c2 : E1 r v * E2 p q = E2 p q * E1 r v` using `h3 r v p q`.

Establish `e : br (E1 p q + eps s • E2 p q) (E1 r v + eps t • E2 r v) = (E1 p q * E1 r v - E1 r v * E1 p q) + (eps s * eps t) • (E2 p q * E2 r v - E2 r v * E2 p q)`. Simplify using `only [br, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul, c1, c2]`. Use `module`. Rewrite using `[Ts_eq, Ts_eq, e, g1, g2, eps_mul]`. Simplify using `only [Ts_eq]`.

Apply the tactic sequence `split_ifs <;> module`.
-/
theorem ts_rel (h : PairRel E1 E2) (s t : Bool) (p q r v : Fin n) :
    br (Ts E1 E2 s p q) (Ts E1 E2 t r v) =
      (if q = r then Ts E1 E2 (s == t) p v else 0) - (if v = p then Ts E1 E2 (s == t) r q else 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  have g1 := h1 p q r v
  have g2 := h2 p q r v
  have c1 : E1 p q * E2 r v = E2 r v * E1 p q := h3 p q r v
  have c2 : E1 r v * E2 p q = E2 p q * E1 r v := h3 r v p q
  have e : br (E1 p q + eps s • E2 p q) (E1 r v + eps t • E2 r v) =
      (E1 p q * E1 r v - E1 r v * E1 p q) + (eps s * eps t) • (E2 p q * E2 r v - E2 r v * E2 p q) := by
    simp only [br, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul, c1, c2]
    module
  rw [Ts_eq, Ts_eq, e, g1, g2, eps_mul]
  simp only [Ts_eq]
  split_ifs <;> module

/- English proof (translation)
Take `⟨u, i⟩` from `l`. Establish `hi : lev i.1.1 < lev i.1.2` using `hl`. Rewrite using `[sum_Mt]`. Establish `hX : ∀ k : Pos n, Tl E1 E2 ((s == u), k) = Ts E1 E2 (s == u) k.1.1 k.1.2` using `fun _ => rfl`. Simplify using `only [hX]`.

Use `set X := Ts E1 E2 (s == u) with hXd`. Establish `h1 : ∑ k : Pos n, (if q = i.1.1 ∧ k.1.1 = p ∧ k.1.2 = i.1.2 then (1 : ℂ) else 0) • X k.1.1 k.1.2 = if q = i.1.1 then X p i.1.2 else 0`. Distinguish the cases in `h : q = i.1.1`. Establish `hlt : p < i.1.2` using `GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.lt_of_lev hm (by rw [hpq, h]; exact hi)`. Simplify using `only [h, true_and, if_true]`.

Conclude with `GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.sum_ind hlt fun k => X k.1.1 k.1.2`. Simplify using `[h]`. Establish `h2 : ∑ k : Pos n, (if i.1.2 = p ∧ k.1.1 = i.1.1 ∧ k.1.2 = q then (1 : ℂ) else 0) • X k.1.1 k.1.2 = if i.1.2 = p then X i.1.1 q else 0`. Distinguish the cases in `h : i.1.2 = p`. Establish `hlt : i.1.1 < q` using `GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.lt_of_lev hm (by rw [← hpq, ← h]; exact hi)`.

Simplify using `only [h, true_and, if_true]`. Conclude with `GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.sum_ind hlt fun k => X k.1.1 k.1.2`. Simplify using `[h]`. Simplify using `only [GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.adC_eq, sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[h1, h2]`.

Use `ts_rel hP s u p q i.1.1 i.1.2` as an intermediate fact. Use `show br (Ts E1 E2 s p q) (Ts E1 E2 u i.1.1 i.1.2) - _ = 0`. Rewrite using `[this, sub_eq_zero]`.
-/
theorem lin_q (hP : PairRel E1 E2) {lev : Fin n → ℕ} (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q)
    (s : Bool) {l : Lt n} (hl : inUL lev l) :
    br (Ts E1 E2 s p q) (Tl E1 E2 l) - ∑ m, Mt s p q l m • Tl E1 E2 m = 0 := by
  obtain ⟨u, i⟩ := l
  have hi : lev i.1.1 < lev i.1.2 := hl
  rw [sum_Mt]
  have hX : ∀ k : Pos n, Tl E1 E2 ((s == u), k) = Ts E1 E2 (s == u) k.1.1 k.1.2 := fun _ => rfl
  simp only [hX]
  set X := Ts E1 E2 (s == u) with hXd
  have h1 : ∑ k : Pos n, (if q = i.1.1 ∧ k.1.1 = p ∧ k.1.2 = i.1.2 then (1 : ℂ) else 0) • X k.1.1 k.1.2 =
      if q = i.1.1 then X p i.1.2 else 0 := by
    by_cases h : q = i.1.1
    · have hlt : p < i.1.2 := GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.lt_of_lev hm (by rw [hpq, h]; exact hi)
      simp only [h, true_and, if_true]
      exact GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.sum_ind hlt fun k => X k.1.1 k.1.2
    · simp [h]
  have h2 : ∑ k : Pos n, (if i.1.2 = p ∧ k.1.1 = i.1.1 ∧ k.1.2 = q then (1 : ℂ) else 0) • X k.1.1 k.1.2 =
      if i.1.2 = p then X i.1.1 q else 0 := by
    by_cases h : i.1.2 = p
    · have hlt : i.1.1 < q := GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.lt_of_lev hm (by rw [← hpq, ← h]; exact hi)
      simp only [h, true_and, if_true]
      exact GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.sum_ind hlt fun k => X k.1.1 k.1.2
    · simp [h]
  simp only [GlobalTheory.CompanionTheory.RgCOBlock.LeviBd.adC_eq, sub_smul, Finset.sum_sub_distrib]
  rw [h1, h2]
  have := ts_rel hP s u p q i.1.1 i.1.2
  show br (Ts E1 E2 s p q) (Ts E1 E2 u i.1.1 i.1.2) - _ = 0
  rw [this, sub_eq_zero]

/- English proof (translation)
Rewrite `h` using `[annq_apply]`. Distinguish the cases in `hi : i ∈ A`. Simplify using `[hi] at h`. Use `⟨hi, fun h0 => h ?_⟩` and prove the remaining obligations. Simplify using `[hi, h0]`.
-/
theorem annq_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : annq i x A ≠ 0) : i ∉ A ∧ x (insert i A) ≠ 0 := by
  rw [annq_apply] at h
  by_cases hi : i ∈ A
  · simp [hi] at h
  · refine ⟨hi, fun h0 => h ?_⟩
    simp [hi, h0]

/- English proof (translation)
Use function extensionality and compare the values at `A`. Assume the negation of the conclusion as `h`. Conclude with `hi (hx _ (annq_ne h).2 i (mem_insert_self _ _))`.
-/
theorem annq_eq_zero {P : Lt n → Prop} {x : Cq n V} (hx : SuppQ P x) {i : Lt n} (hi : ¬P i) : annq i x = 0 := by
  funext A
  by_contra h
  exact hi (hx _ (annq_ne h).2 i (mem_insert_self _ _))

/- English proof (translation)
Introduce `A h j hj`. Conclude with `hx _ (annq_ne h).2 j (mem_insert_of_mem hj)`.
-/
theorem annq_supp {P : Lt n → Prop} {x : Cq n V} (hx : SuppQ P x) (i : Lt n) : SuppQ P (annq i x) := by
  intro A h j hj
  exact hx _ (annq_ne h).2 j (mem_insert_of_mem hj)

/- English proof (translation)
Establish `h1 : br (lFq E1 E2 s p q) (moduleBoundaryPart E1 E2) x = 0`. Rewrite using `[bracket_levi_moduleBoundaryPart, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : inUL lev l`. Rewrite using `[lin_q hP hm hpq s hl]`.

Use `funext fun A => ?_` and prove the remaining obligations. Simplify using `[liftq_apply]`. Rewrite using `[Module.End.mul_apply, annq_eq_zero hx hl, map_zero]`. Establish `h2 : br (lFq E1 E2 s p q) (cubicBoundaryPart n V) x = 0`. Rewrite using `[bracket_levi_cubicBoundaryPart]`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply]`. Use `Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Distinguish the cases in `ha : inUL lev a`. Distinguish the cases in `hb : inUL lev b`. Rewrite using `[coef_zero hm hpq ha hb, zero_smul]`.

Simplify using `only [Module.End.mul_apply]`. Rewrite using `[annq_eq_zero (annq_supp hx a) hb, map_zero, smul_zero]`. Simplify using `only [Module.End.mul_apply]`. Rewrite using `[annq_eq_zero hx ha, map_zero, map_zero, smul_zero]`. Rewrite using `[bdq_eq]`.

Simplify using `only [br, LinearMap.sub_apply, Module.End.mul_apply] at h1 h2`. Simplify using `only [LinearMap.add_apply, map_add]`. Rewrite using `[sub_eq_zero.1 h1, sub_eq_zero.1 h2]`.
-/
theorem lFq_bd (hP : PairRel E1 E2) {lev : Fin n → ℕ} (hm : Monotone lev) {x : Cq n V} (hx : SuppQ (inUL lev) x)
    (s : Bool) {p q : Fin n} (hpq : lev p = lev q) :
    lFq E1 E2 s p q (bdq E1 E2 x) = bdq E1 E2 (lFq E1 E2 s p q x) := by
  have h1 : br (lFq E1 E2 s p q) (moduleBoundaryPart E1 E2) x = 0 := by
    rw [bracket_levi_moduleBoundaryPart, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : inUL lev l
    · rw [lin_q hP hm hpq s hl]
      refine funext fun A => ?_
      simp [liftq_apply]
    · rw [Module.End.mul_apply, annq_eq_zero hx hl, map_zero]
  have h2 : br (lFq E1 E2 s p q) (cubicBoundaryPart n V) x = 0 := by
    rw [bracket_levi_cubicBoundaryPart]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun m _ => ?_
    by_cases ha : inUL lev a
    · by_cases hb : inUL lev b
      · rw [coef_zero hm hpq ha hb, zero_smul]
      · simp only [Module.End.mul_apply]
        rw [annq_eq_zero (annq_supp hx a) hb, map_zero, smul_zero]
    · simp only [Module.End.mul_apply]
      rw [annq_eq_zero hx ha, map_zero, map_zero, smul_zero]
  rw [bdq_eq]
  simp only [br, LinearMap.sub_apply, Module.End.mul_apply] at h1 h2
  simp only [LinearMap.add_apply, map_add]
  rw [sub_eq_zero.1 h1, sub_eq_zero.1 h2]

/- English proof (translation)
Take `⟨u, i⟩` from `i`. Take `⟨w, l⟩` from `l`. Establish `e1 : ∑ m, Mt t r v (u, i) m * Mt s p q m (w, l) = ∑ k : Pos n, adC r v i k * Mt s p q ((t == u), k) (w, l)`. Simplify `sum_Mt t r v (u, i) (fun m => Mt s p q m (w, l))` using `only [smul_eq_mul]`. Establish `e2 : ∑ m, Mt s p q (u, i) m * Mt t r v m (w, l) = ∑ k : Pos n, adC p q i k * Mt t r v ((s == u), k) (w, l)`.

Simplify `sum_Mt s p q (u, i) (fun m => Mt t r v m (w, l))` using `only [smul_eq_mul]`. Rewrite using `[e1, e2]`. Establish `hM` using `GlobalTheory.CompanionTheory.RgCOBlock.LetterGl.mat_id hm hpq hrv (i := i) hi l`. Rewrite `hM` using `[Finset.sum_sub_distrib]`. Distinguish the cases in `hc : w = ((s == t) == u)`.

Apply the tactic sequence `have i1 : w = (s == (t == u)) := by rw [hc]; cases s <;> cases t <;> cases u <;> rfl`. Apply the tactic sequence `have i2 : w = (t == (s == u)) := by rw [hc]; cases s <;> cases t <;> cases u <;> rfl`. Simplify using `only [Mt, i1.symm, i2.symm, hc.symm, if_true]`. Conclude with `hM`. Apply the tactic sequence `have i1 : ¬w = (s == (t == u)) := fun e => hc (by rw [e]; cases s <;> cases t <;> cases u <;> rfl)`.

Apply the tactic sequence `have i2 : ¬w = (t == (s == u)) := fun e => hc (by rw [e]; cases s <;> cases t <;> cases u <;> rfl)`. Simplify using `[Mt, hc, i1, i2]`.
-/
theorem mt_id {lev : Fin n → ℕ} (hm : Monotone lev) {s t : Bool} {p q r v : Fin n} (hpq : lev p = lev q)
    (hrv : lev r = lev v) {i : Lt n} (hi : inUL lev i) (l : Lt n) :
    (∑ m, Mt t r v i m * Mt s p q m l) - ∑ m, Mt s p q i m * Mt t r v m l =
      (if q = r then Mt (s == t) p v i l else 0) - (if v = p then Mt (s == t) r q i l else 0) := by
  obtain ⟨u, i⟩ := i
  obtain ⟨w, l⟩ := l
  have e1 : ∑ m, Mt t r v (u, i) m * Mt s p q m (w, l) = ∑ k : Pos n, adC r v i k * Mt s p q ((t == u), k) (w, l) := by
    simpa only [smul_eq_mul] using sum_Mt t r v (u, i) (fun m => Mt s p q m (w, l))
  have e2 : ∑ m, Mt s p q (u, i) m * Mt t r v m (w, l) = ∑ k : Pos n, adC p q i k * Mt t r v ((s == u), k) (w, l) := by
    simpa only [smul_eq_mul] using sum_Mt s p q (u, i) (fun m => Mt t r v m (w, l))
  rw [e1, e2]
  have hM := GlobalTheory.CompanionTheory.RgCOBlock.LetterGl.mat_id hm hpq hrv (i := i) hi l
  rw [Finset.sum_sub_distrib] at hM
  by_cases hc : w = ((s == t) == u)
  · have i1 : w = (s == (t == u)) := by rw [hc]; cases s <;> cases t <;> cases u <;> rfl
    have i2 : w = (t == (s == u)) := by rw [hc]; cases s <;> cases t <;> cases u <;> rfl
    simp only [Mt, i1.symm, i2.symm, hc.symm, if_true]
    exact hM
  · have i1 : ¬w = (s == (t == u)) := fun e => hc (by rw [e]; cases s <;> cases t <;> cases u <;> rfl)
    have i2 : ¬w = (t == (s == u)) := fun e => hc (by rw [e]; cases s <;> cases t <;> cases u <;> rfl)
    simp [Mt, hc, i1, i2]

/- English proof (translation)
Simplify using `[Dm, LinearMap.sum_apply, Module.End.mul_apply]`.
-/
theorem dm_apply (A : Lt n → Lt n → ℂ) (x : Cq n V) :
    (Dm annq creq A : Module.End ℂ (Cq n V)) x = ∑ i, ∑ l, A i l • creq l (annq i x) := by
  simp [Dm, LinearMap.sum_apply, Module.End.mul_apply]

/- English proof (translation)
Rewrite using `[br_dm_gen (R := Module.End ℂ (Cq n V)) aa cc ac]`. Establish `t1 : ∀ i l : Lt n, ((∑ m, Mt t r v i m * Mt s p q m l) - ∑ m, Mt s p q i m * Mt t r v m l) • creq l (annq i x) = ((if q = r then Mt (s == t) p v i l else 0) - (if v = p then Mt (s == t) r q i l else 0)) • creq l (annq i x)`. Introduce `i l`. Distinguish the cases in `hi : inUL lev i`. Rewrite using `[mt_id hm hpq hrv hi]`.

Rewrite using `[annq_eq_zero hx hi, map_zero, smul_zero, smul_zero]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]`. Simplify using `only [t1]`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Use `congr 1`.

Use `split_ifs`. Rewrite using `[dm_apply]`. Simplify using the standard rewrite rules. Use `split_ifs`. Rewrite using `[dm_apply]`.

Simplify using the standard rewrite rules.
-/
theorem dm_comm_apply {lev : Fin n → ℕ} (hm : Monotone lev) {x : Cq n V} (hx : SuppQ (inUL lev) x)
    {s t : Bool} {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v) :
    br (Dm annq creq (Mt s p q)) (Dm annq creq (Mt t r v) : Module.End ℂ (Cq n V)) x =
      (if q = r then Dm annq creq (Mt (s == t) p v) x else 0) -
        (if v = p then (Dm annq creq (Mt (s == t) r q) : Module.End ℂ (Cq n V)) x else 0) := by
  rw [br_dm_gen (R := Module.End ℂ (Cq n V)) aa cc ac]
  have t1 : ∀ i l : Lt n,
      ((∑ m, Mt t r v i m * Mt s p q m l) - ∑ m, Mt s p q i m * Mt t r v m l) • creq l (annq i x) =
      ((if q = r then Mt (s == t) p v i l else 0) - (if v = p then Mt (s == t) r q i l else 0)) • creq l (annq i x) := by
    intro i l
    by_cases hi : inUL lev i
    · rw [mt_id hm hpq hrv hi]
    · rw [annq_eq_zero hx hi, map_zero, smul_zero, smul_zero]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  simp only [t1]
  simp only [sub_smul, Finset.sum_sub_distrib]
  congr 1
  · split_ifs
    · rw [dm_apply]
    · simp
  · split_ifs
    · rw [dm_apply]
    · simp

/- English proof (translation)
Establish `hb : br (lFq E1 E2 s p q) (lFq E1 E2 t r v) = liftq n (br (Ts E1 E2 s p q) (Ts E1 E2 t r v)) + br (Dm annq creq (Mt s p q)) (Dm annq creq (Mt t r v))`. Rewrite using `[lFq_eq E1 E2 t r v, br_add_right, br_L_lift, lFq_eq E1 E2 s p q, br_add_left, br_lift_dm (fun i => br_lift_annq _ i) (fun i => br_lift_creq _ i), zero_add]`. Establish `h` using `LinearMap.congr_fun hb x`. Rewrite `h` using `[LinearMap.add_apply, dm_comm_apply hm hx hpq hrv, ts_rel hP]`. Establish `hsub : ∀ S T : Module.End ℂ V, (liftq n (S - T) : Module.End ℂ (Cq n V)) x = liftq n S x - liftq n T x` using `fun S T => by`.

Use function extensionality and compare the values at `A`. Simplify using `[liftq_apply]`. Rewrite `h` using `[hsub]`. Simplify using `only [br, LinearMap.sub_apply, Module.End.mul_apply] at h`. Rewrite using `[h]`.

Simplify using `only [lFq_eq, LinearMap.add_apply]`. Establish `h0 : (liftq n (0 : Module.End ℂ V) : Module.End ℂ (Cq n V)) x = 0`. Use function extensionality and compare the values at `A`. Simplify using `[liftq_apply]`. Apply the tactic sequence `split_ifs <;> (try simp only [h0]) <;> abel`.
-/
theorem lFq_rel (hP : PairRel E1 E2) {lev : Fin n → ℕ} (hm : Monotone lev) {x : Cq n V} (hx : SuppQ (inUL lev) x)
    (s t : Bool) {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v) :
    lFq E1 E2 s p q (lFq E1 E2 t r v x) - lFq E1 E2 t r v (lFq E1 E2 s p q x) =
      (if q = r then lFq E1 E2 (s == t) p v x else 0) - (if v = p then lFq E1 E2 (s == t) r q x else 0) := by
  have hb : br (lFq E1 E2 s p q) (lFq E1 E2 t r v) =
      liftq n (br (Ts E1 E2 s p q) (Ts E1 E2 t r v)) + br (Dm annq creq (Mt s p q)) (Dm annq creq (Mt t r v)) := by
    rw [lFq_eq E1 E2 t r v, br_add_right, br_L_lift, lFq_eq E1 E2 s p q, br_add_left,
      br_lift_dm (fun i => br_lift_annq _ i) (fun i => br_lift_creq _ i), zero_add]
  have h := LinearMap.congr_fun hb x
  rw [LinearMap.add_apply, dm_comm_apply hm hx hpq hrv, ts_rel hP] at h
  have hsub : ∀ S T : Module.End ℂ V, (liftq n (S - T) : Module.End ℂ (Cq n V)) x = liftq n S x - liftq n T x :=
    fun S T => by
      funext A
      simp [liftq_apply]
  rw [hsub] at h
  simp only [br, LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [h]
  simp only [lFq_eq, LinearMap.add_apply]
  have h0 : (liftq n (0 : Module.End ℂ V) : Module.End ℂ (Cq n V)) x = 0 := by
    funext A
    simp [liftq_apply]
  split_ifs <;> (try simp only [h0]) <;> abel

/- English proof (translation)
Establish `e : (creq k * annq i : Module.End ℂ (Cq n V)) x A = if k ∈ A then sgL k A • (if i ∈ A.erase k then (0 : V) else sgL i (A.erase k) • x (insert i (A.erase k))) else 0` using `rfl`. Rewrite `h` using `[e]`. Distinguish the cases in `hk : k ∈ A`. Distinguish the cases in `hi : i ∈ A.erase k`. Simplify using `[hk, hi] at h`.

Use `⟨hk, hi, fun h0 => h ?_⟩` and prove the remaining obligations. Simplify using `[hk, hi, h0]`. Simplify using `[hk] at h`.
-/
theorem cre_ann_ne (i k : Lt n) (x : Cq n V) (A : Finset (Lt n))
    (h : (creq k * annq i : Module.End ℂ (Cq n V)) x A ≠ 0) :
    k ∈ A ∧ i ∉ A.erase k ∧ x (insert i (A.erase k)) ≠ 0 := by
  have e : (creq k * annq i : Module.End ℂ (Cq n V)) x A =
      if k ∈ A then sgL k A • (if i ∈ A.erase k then (0 : V) else
        sgL i (A.erase k) • x (insert i (A.erase k))) else 0 := rfl
  rw [e] at h
  by_cases hk : k ∈ A
  · by_cases hi : i ∈ A.erase k
    · simp [hk, hi] at h
    · refine ⟨hk, hi, fun h0 => h ?_⟩
      simp [hk, hi, h0]
  · simp [hk] at h

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨h0, h1⟩` from `hc`. Apply `h` to reduce the goal to its premises. Establish `hs : adLq s p q x A = 0`.

Unfold `adLq`. Simplify using `only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply]`. Use `Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hz : adC p q i k = 0`. Simplify using `[hz]`.

Rewrite using `[h1 t i k hz, smul_zero]`. Establish `e : lFq E1 E2 s p q x A = Ts E1 E2 s p q (x A) + adLq s p q x A` using `rfl`. Rewrite using `[e, hs, h0, map_zero, add_zero]`.
-/
theorem lFq_ne (s : Bool) (p q : Fin n) (x : Cq n V) (A : Finset (Lt n)) (h : lFq E1 E2 s p q x A ≠ 0) :
    x A ≠ 0 ∨ ∃ (t : Bool) (i k : Pos n), adC p q i k ≠ 0 ∧
      (creq ((s == t), k) * annq (t, i) : Module.End ℂ (Cq n V)) x A ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨h0, h1⟩ := hc
  apply h
  have hs : adLq s p q x A = 0 := by
    unfold adLq
    simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply]
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases hz : adC p q i k = 0
    · simp [hz]
    · rw [h1 t i k hz, smul_zero]
  have e : lFq E1 E2 s p q x A = Ts E1 E2 s p q (x A) + adLq s p q x A := rfl
  rw [e, hs, h0, map_zero, add_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `A hA m hm`. Break down `lFq_ne s p q x A hA with h | ⟨t, i, k, hc, h⟩` into its components or cases. Conclude with `hx A h m hm`. Take `⟨-, -, h3⟩` from `cre_ann_ne (t, i) ((s == t), k) x A h`.

Distinguish the cases in `hmk : m = ((s == t), k)`. Substitute `hmk` using the available equality. Conclude with `GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.inU_of_adC hpq hc (hx _ h3 (t, i) (Finset.mem_insert_self _ _))`. Conclude with `hx _ h3 m (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hmk, hm⟩))`. Introduce `j hj A hA`.

Break down `lFq_ne s p q x A hA with h | ⟨t, i, k, -, h⟩` into its components or cases. Conclude with `hj A h`. Take `⟨h1, h2, h3⟩` from `cre_ann_ne (t, i) ((s == t), k) x A h`. Establish `hc` using `hj _ h3`. Rewrite `hc` using `[Finset.card_insert_of_notMem h2, Finset.card_erase_of_mem h1]`.

Establish `hpos : 0 < A.card` using `Finset.card_pos.2 ⟨_, h1⟩`. Use linear arithmetic over natural numbers and integers.
-/
theorem lFq_supp_deg {lev : Fin n → ℕ} {x : Cq n V} (hx : SuppQ (inUL lev) x) (s : Bool) {p q : Fin n}
    (hpq : lev p = lev q) :
    SuppQ (inUL lev) (lFq E1 E2 s p q x) ∧ ∀ j, DegQ j x → DegQ j (lFq E1 E2 s p q x) := by
  constructor
  · intro A hA m hm
    rcases lFq_ne s p q x A hA with h | ⟨t, i, k, hc, h⟩
    · exact hx A h m hm
    · obtain ⟨-, -, h3⟩ := cre_ann_ne (t, i) ((s == t), k) x A h
      by_cases hmk : m = ((s == t), k)
      · subst hmk
        exact GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp.inU_of_adC hpq hc (hx _ h3 (t, i) (Finset.mem_insert_self _ _))
      · exact hx _ h3 m (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hmk, hm⟩))
  · intro j hj A hA
    rcases lFq_ne s p q x A hA with h | ⟨t, i, k, -, h⟩
    · exact hj A h
    · obtain ⟨h1, h2, h3⟩ := cre_ann_ne (t, i) ((s == t), k) x A h
      have hc := hj _ h3
      rw [Finset.card_insert_of_notMem h2, Finset.card_erase_of_mem h1] at hc
      have hpos : 0 < A.card := Finset.card_pos.2 ⟨_, h1⟩
      omega

end Rel

end GlobalTheory.CompanionTheory.PairMult.LeviQ

namespace GlobalTheory.CompanionTheory.PairMult

open GlobalTheory.CompanionTheory.PairMult.LeviQ

/- English proof (translation)
Introduce `n lev V _ _ E1 E2 hm hP x hx`. Use `⟨fun s p q hpq => ?_, fun p q r v hpq hrv => ?_⟩` and prove the remaining obligations. Take `⟨a, b⟩` from `lFq_supp_deg (E1 := E1) (E2 := E2) hx s hpq`. Conclude with `⟨a, b, lFq_bd hP hm hx s hpq⟩`. Establish `R` using `fun s t => lFq_rel hP hm hx s t hpq hrv`.

Establish `tt` using `R true true`. Establish `tf` using `R true false`. Establish `ft` using `R false true`. Establish `ff` using `R false false`. Simplify using `only [beq_self_eq_true, Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false, beq_iff_eq] at tt tf ft ff`.

Simplify using `only [c1, c2, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, map_smul, map_add, map_sub]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `split_ifs at tt tf ft ff ⊢ <;>`. Take the linear combination `(norm := module) (1 / 4 : ℂ) • tt + (1 / 4 : ℂ) • tf + (1 / 4 : ℂ) • ft + (1 / 4 : ℂ) • ff`. Apply the tactic sequence `split_ifs at tt tf ft ff ⊢ <;>`.

Take the linear combination `(norm := module) (1 / 4 : ℂ) • tt - (1 / 4 : ℂ) • tf - (1 / 4 : ℂ) • ft + (1 / 4 : ℂ) • ff`. Apply the tactic sequence `split_ifs at tt tf ft ff <;>`. Take the linear combination `(norm := module) (1 / 4 : ℂ) • tt - (1 / 4 : ℂ) • tf + (1 / 4 : ℂ) • ft - (1 / 4 : ℂ) • ff`.
-/
theorem leviRel : LeviRel := by
  intro n lev V _ _ E1 E2 hm hP x hx
  refine ⟨fun s p q hpq => ?_, fun p q r v hpq hrv => ?_⟩
  · obtain ⟨a, b⟩ := lFq_supp_deg (E1 := E1) (E2 := E2) hx s hpq
    exact ⟨a, b, lFq_bd hP hm hx s hpq⟩
  · have R := fun s t => lFq_rel hP hm hx s t hpq hrv
    have tt := R true true
    have tf := R true false
    have ft := R false true
    have ff := R false false
    simp only [beq_self_eq_true, Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false,
      beq_iff_eq] at tt tf ft ff
    simp only [c1, c2, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, map_smul, map_add, map_sub]
    refine ⟨?_, ?_, ?_⟩
    · split_ifs at tt tf ft ff ⊢ <;>
        linear_combination (norm := module) (1 / 4 : ℂ) • tt + (1 / 4 : ℂ) • tf + (1 / 4 : ℂ) • ft + (1 / 4 : ℂ) • ff
    · split_ifs at tt tf ft ff ⊢ <;>
        linear_combination (norm := module) (1 / 4 : ℂ) • tt - (1 / 4 : ℂ) • tf - (1 / 4 : ℂ) • ft + (1 / 4 : ℂ) • ff
    · split_ifs at tt tf ft ff <;>
        linear_combination (norm := module) (1 / 4 : ℂ) • tt - (1 / 4 : ℂ) • tf + (1 / 4 : ℂ) • ft - (1 / 4 : ℂ) • ff

end GlobalTheory.CompanionTheory.PairMult

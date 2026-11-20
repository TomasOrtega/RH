import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichRhoAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfJqSmoothOfNnMaj

noncomputable section

open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

variable {k r : ℕ}

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

def ep (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

/- English proof (translation)
Unfold `Hpk sg ep`. Distinguish the cases in `h1 : i.val < r ∨ r + k < i.val`. Rewrite using `[if_pos h1]`. Break down `h1 with h1 | h1` into its components or cases. Distinguish the cases in `hj : i.val + j.val = 2 * r + k`.

Rewrite using `[if_pos ⟨h1, hj⟩, if_pos (Fin.ext (by simp; omega)), if_neg (by omega)]`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by rw [Fin.ext_iff]; simp; omega)]`. Distinguish the cases in `hj : i.val + j.val = 2 * r + k`. Rewrite using `[if_neg (by omega), if_pos ⟨by omega, hj⟩, if_pos (Fin.ext (by simp; omega)), if_neg (by omega)]`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by rw [Fin.ext_iff]; simp; omega)]`.

Rewrite using `[if_neg h1]`. Simplify using `only [not_or, not_lt] at h1`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos ⟨h1.1, h1.2, rfl⟩, if_pos rfl]`.

Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (by tauto), if_neg hj]`.
-/
lemma hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sg k r i then ep k r i else 0 := by
  unfold Hpk sg ep
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    rcases h1 with h1 | h1
    · by_cases hj : i.val + j.val = 2 * r + k
      · rw [if_pos ⟨h1, hj⟩, if_pos (Fin.ext (by simp; omega)), if_neg (by omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by rw [Fin.ext_iff]; simp; omega)]
    · by_cases hj : i.val + j.val = 2 * r + k
      · rw [if_neg (by omega), if_pos ⟨by omega, hj⟩, if_pos (Fin.ext (by simp; omega)), if_neg (by omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by rw [Fin.ext_iff]; simp; omega)]
  · rw [if_neg h1]
    simp only [not_or, not_lt] at h1
    by_cases hj : j = i
    · subst hj
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1.1, h1.2, rfl⟩, if_pos rfl]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by tauto), if_neg hj]

/- English proof (translation)
Unfold `sg`. Distinguish the cases in `h1 : i.val < r ∨ r + k < i.val`. Rewrite using `[if_pos h1, if_pos (by simp; omega)]; ext; simp; omega`. Rewrite using `[if_neg h1, if_neg h1]`.
-/
lemma sg_sg (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  unfold sg
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1, if_pos (by simp; omega)]; ext; simp; omega
  · rw [if_neg h1, if_neg h1]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Rewrite using `[sg_sg]`. Introduce and unpack `rfl`. Rewrite using `[sg_sg]`.
-/
lemma sg_eq_iff (i j : Fin (2 * r + k + 1)) : j = sg k r i ↔ i = sg k r j := by
  constructor
  · rintro rfl; rw [sg_sg]
  · rintro rfl; rw [sg_sg]

/- English proof (translation)
Unfold `ep sg`. Distinguish the cases in `h1 : i.val < r ∨ r + k < i.val`. Rewrite using `[if_pos h1]; simp only; rw [if_neg (by omega), if_neg (by omega)]`. Rewrite using `[if_neg h1]`.
-/
lemma ep_sg (i : Fin (2 * r + k + 1)) : ep k r (sg k r i) = ep k r i := by
  unfold ep sg
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]; simp only; rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h1]

/- English proof (translation)
Apply the tactic sequence `unfold ep; split_ifs <;> simp`.
-/
lemma norm_ep (i : Fin (2 * r + k + 1)) : ‖ep k r i‖ = 1 := by
  unfold ep; split_ifs <;> simp

/- English proof (translation)
The claim follows from `(hpkFacts k r).2.1`.
-/
lemma hsq : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Establish `h : yᴴ * Hpk k r * y = Hpk k r` using `hy`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma inv_eq {y : Mat k r} (hy : y ∈ GV k r) : y⁻¹ = Hpk k r * yᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h : yᴴ * Hpk k r * y = Hpk k r := hy
  calc Hpk k r * yᴴ * Hpk k r * y = Hpk k r * (yᴴ * Hpk k r * y) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hsq]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `only [hpk_apply, ite_mul, zero_mul, Matrix.conjTranspose_apply]`. Rewrite using `[Finset.sum_ite_eq' Finset.univ (sg k r i)]`. Simplify using the standard rewrite rules.
-/
lemma hy_apply (y : Mat k r) (i l : Fin (2 * r + k + 1)) :
    (Hpk k r * yᴴ) i l = ep k r i * star (y l (sg k r i)) := by
  rw [Matrix.mul_apply]
  simp only [hpk_apply, ite_mul, zero_mul, Matrix.conjTranspose_apply]
  rw [Finset.sum_ite_eq' Finset.univ (sg k r i)]
  simp

/- English proof (translation)
Rewrite using `[inv_eq hy, Matrix.mul_apply]`. Simplify using `only [hy_apply, hpk_apply]`. Establish `: ∀ l : Fin (2 * r + k + 1), (ep k r i * star (y l (sg k r i)) * if j = sg k r l then ep k r l else 0) = if sg k r j = l then ep k r i * star (y l (sg k r i)) * ep k r l else 0`. Introduce `l`. Distinguish the cases in `h : sg k r j = l`.

Rewrite using `[if_pos h, if_pos ((sg_eq_iff l j).2 h.symm)]`. Rewrite using `[if_neg h, if_neg (fun h' => h ((sg_eq_iff l j).1 h').symm), mul_zero]`. Simplify using `only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true, ep_sg]`.
-/
lemma inv_apply {y : Mat k r} (hy : y ∈ GV k r) (i j : Fin (2 * r + k + 1)) :
    y⁻¹ i j = ep k r i * star (y (sg k r j) (sg k r i)) * ep k r j := by
  rw [inv_eq hy, Matrix.mul_apply]
  simp only [hy_apply, hpk_apply]
  have : ∀ l : Fin (2 * r + k + 1), (ep k r i * star (y l (sg k r i)) *
      if j = sg k r l then ep k r l else 0) =
      if sg k r j = l then ep k r i * star (y l (sg k r i)) * ep k r l else 0 := by
    intro l
    by_cases h : sg k r j = l
    · rw [if_pos h, if_pos ((sg_eq_iff l j).2 h.symm)]
    · rw [if_neg h, if_neg (fun h' => h ((sg_eq_iff l j).1 h').symm), mul_zero]
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true, ep_sg]

/- English proof (translation)
Rewrite using `[inv_apply hy, norm_mul, norm_mul, norm_ep, norm_ep, norm_star]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_inv_apply {y : Mat k r} (hy : y ∈ GV k r) (i j : Fin (2 * r + k + 1)) :
    ‖y⁻¹ i j‖ = ‖y (sg k r j) (sg k r i)‖ := by
  rw [inv_apply hy, norm_mul, norm_mul, norm_ep, norm_ep, norm_star]; ring

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.unipotent_radical_closed k r`.
-/
lemma closedN : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (Nset k r) := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r

/- English proof (translation)
The claim follows from `hn.1`.
-/
lemma n_mem_G {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ GV k r := hn.1

/- English proof (translation)
The claim follows from `closedN.inv_mem n hn`.
-/
lemma n_inv_mem {n : Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Nset k r := closedN.inv_mem n hn

/- English proof (translation)
The claim follows from `hn.2.1 a i h`.
-/
lemma n_colE {n : Mat k r} (hn : n ∈ Nset k r) (a : Fin r) (i : Fin (2 * r + k + 1)) (h : a.val ≤ i.val) :
    n i (eI k r a) = if i = eI k r a then 1 else 0 := hn.2.1 a i h

/- English proof (translation)
The claim follows from `hn.2.2 i j hj1 hj2 hi`.
-/
lemma n_colM {n : Mat k r} (hn : n ∈ Nset k r) (i j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val)
    (hj2 : j.val ≤ r + k) (hi : r ≤ i.val) : n i j = if i = j then 1 else 0 := hn.2.2 i j hj1 hj2 hi

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma eI_val (a : Fin r) : (eI k r a).val = a.val := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma esI_val (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := rfl

/- English proof (translation)
Distinguish the cases in `hl' : l.val < r`. Use `n_colE hn ⟨l.val, hl'⟩ i (by simp; omega)` as an intermediate fact. Establish `e : eI k r ⟨l.val, hl'⟩ = l` using `Fin.ext rfl`. Rewrite `this` using `[e]`. Rewrite using `[this, if_neg (by rintro rfl; omega)]`.

Rewrite using `[n_colM hn i l (by omega) hl (by omega), if_neg (by rintro rfl; omega)]`.
-/
lemma n_rowEs {n : Mat k r} (hn : n ∈ Nset k r) (i l : Fin (2 * r + k + 1)) (hi : r + k < i.val)
    (hl : l.val ≤ r + k) : n i l = 0 := by
  by_cases hl' : l.val < r
  · have := n_colE hn ⟨l.val, hl'⟩ i (by simp; omega)
    have e : eI k r ⟨l.val, hl'⟩ = l := Fin.ext rfl
    rw [e] at this
    rw [this, if_neg (by rintro rfl; omega)]
  · rw [n_colM hn i l (by omega) hl (by omega), if_neg (by rintro rfl; omega)]

/- English proof (translation)
Distinguish the cases in `hl' : l.val < r`. Use `n_colE hn ⟨l.val, hl'⟩ i (by simp; omega)` as an intermediate fact. Establish `e : eI k r ⟨l.val, hl'⟩ = l` using `Fin.ext rfl`. Rewrite `this` using `[e]`. Rewrite using `[this]`.

Conclude with `n_colM hn i l (by omega) hl hi1`.
-/
lemma n_rowM {n : Mat k r} (hn : n ∈ Nset k r) (i l : Fin (2 * r + k + 1)) (hi1 : r ≤ i.val)
    (hl : l.val ≤ r + k) : n i l = if i = l then 1 else 0 := by
  by_cases hl' : l.val < r
  · have := n_colE hn ⟨l.val, hl'⟩ i (by simp; omega)
    have e : eI k r ⟨l.val, hl'⟩ = l := Fin.ext rfl
    rw [e] at this
    rw [this]
  · exact n_colM hn i l (by omega) hl hi1

/- English proof (translation)
Rewrite using `[n_colE hn b l (by have := b.isLt; omega), if_neg (by intro h; have := congrArg Fin.val h; simp [eI] at this; omega)]`.
-/
lemma n_colE_zero {n : Mat k r} (hn : n ∈ Nset k r) (l : Fin (2 * r + k + 1)) (b : Fin r) (hl : r ≤ l.val) :
    n l (eI k r b) = 0 := by
  rw [n_colE hn b l (by have := b.isLt; omega),
    if_neg (by intro h; have := congrArg Fin.val h; simp [eI] at this; omega)]

/- English proof (translation)
Introduce `a b h` and use `Fin.ext (by simpa [eI] using congrArg Fin.val h)`.
-/
lemma eI_inj : Function.Injective (eI k r) := fun a b h => Fin.ext (by simpa [eI] using congrArg Fin.val h)

/- English proof (translation)
Introduce `a b h` and use `by have := congrArg Fin.val h; simp [esI] at this; exact Fin.ext (by omega)`.
-/
lemma esI_inj : Function.Injective (esI k r) := fun a b h => by
  have := congrArg Fin.val h; simp [esI] at this; exact Fin.ext (by omega)

/- English proof (translation)
Rewrite using `[← Finset.sum_image (s := Finset.univ) (g := eI k r) (fun a _ b _ hab => eI_inj hab)]`. Use `(Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => h l ?_)).symm` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `hl (Finset.mem_image.2 ⟨⟨l.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)`.
-/
lemma sum_E {M : Type*} [AddCommMonoid M] (f : Fin (2 * r + k + 1) → M)
    (h : ∀ l : Fin (2 * r + k + 1), r ≤ l.val → f l = 0) : ∑ l, f l = ∑ b : Fin r, f (eI k r b) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := eI k r) (fun a _ b _ hab => eI_inj hab)]
  refine (Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => h l ?_)).symm
  by_contra hc
  exact hl (Finset.mem_image.2 ⟨⟨l.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/- English proof (translation)
Rewrite using `[← Finset.sum_image (s := Finset.univ) (g := esI k r) (fun a _ b _ hab => esI_inj hab)]`. Use `(Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => h l ?_)).symm` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `hl (Finset.mem_image.2 ⟨⟨2 * r + k - l.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp [esI]; omega)⟩)`.
-/
lemma sum_Es {M : Type*} [AddCommMonoid M] (f : Fin (2 * r + k + 1) → M)
    (h : ∀ l : Fin (2 * r + k + 1), l.val ≤ r + k → f l = 0) : ∑ l, f l = ∑ a : Fin r, f (esI k r a) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := esI k r) (fun a _ b _ hab => esI_inj hab)]
  refine (Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => h l ?_)).symm
  by_contra hc
  exact hl (Finset.mem_image.2 ⟨⟨2 * r + k - l.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp [esI]; omega)⟩)

/- English proof (translation)
Apply the tactic sequence `have h1 : ∀ l : Fin (2 * r + k + 1), f l = (if l.val ≤ r + k then f l else 0) + (if l.val ≤ r + k then 0 else f l) := by intro l; split_ifs <;> simp`. Rewrite using `[Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib, sum_Es (fun l => if l.val ≤ r + k then 0 else f l) (fun l hl => if_pos hl)]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg (by simp [esI]; omega)]`.
-/
lemma sum_split_Es {M : Type*} [AddCommMonoid M] (f : Fin (2 * r + k + 1) → M) :
    ∑ l, f l = ∑ l, (if l.val ≤ r + k then f l else 0) + ∑ a : Fin r, f (esI k r a) := by
  have h1 : ∀ l : Fin (2 * r + k + 1), f l = (if l.val ≤ r + k then f l else 0) +
      (if l.val ≤ r + k then 0 else f l) := by intro l; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_add_distrib,
    sum_Es (fun l => if l.val ≤ r + k then 0 else f l) (fun l hl => if_pos hl)]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [if_neg (by simp [esI]; omega)]

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

variable {k r : ℕ}

def Zm (y : Mat k r) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => y (esI k r a) (eI k r b)

def Lm (n : Mat k r) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a c => n⁻¹ (esI k r a) (esI k r c)

def Um (n : Mat k r) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun b c => n (eI k r b) (eI k r c)

def cE (y : Mat k r) : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := Matrix.of fun i b => y i (eI k r b)

/- English proof (translation)
Use extensionality with `i b`. Simplify using `only [cE, Um, Matrix.of_apply, Matrix.mul_apply]`. Rewrite using `[sum_E (fun l => (∑ j, n⁻¹ i j * g j l) * n' l (eI k r b)) (fun l hl => by rw [n_colE_zero hn' l b hl, mul_zero])]`.
-/
lemma cE_mul {n n' : Mat k r} (_hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (g : Mat k r) :
    cE (n⁻¹ * g * n') = n⁻¹ * cE g * Um n' := by
  ext i b
  simp only [cE, Um, Matrix.of_apply, Matrix.mul_apply]
  rw [sum_E (fun l => (∑ j, n⁻¹ i j * g j l) * n' l (eI k r b))
    (fun l hl => by rw [n_colE_zero hn' l b hl, mul_zero])]

/- English proof (translation)
Establish `h` using `cE_mul hn hn' g`. Use extensionality with `a b`. Establish `h2 : (n⁻¹ * g * n') (esI k r a) (eI k r b) = (n⁻¹ * cE g * Um n') (esI k r a) b`. Rewrite using `[← h]`. Both sides reduce to the same expression.

Use `show (n⁻¹ * g * n') (esI k r a) (eI k r b) = (Lm n * Zm g * Um n') a b`. Rewrite using `[h2, Matrix.mul_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`.

Rewrite using `[sum_Es (M := ℂ) (fun l => n⁻¹ (esI k r a) l * cE g l b') (fun l hl => by rw [n_rowEs (n_inv_mem hn) _ l (by simp [esI]; omega) hl, zero_mul])]`. Both sides reduce to the same expression.
-/
lemma Zm_mul {n n' : Mat k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (g : Mat k r) :
    Zm (n⁻¹ * g * n') = Lm n * Zm g * Um n' := by
  have h := cE_mul hn hn' g
  ext a b
  have h2 : (n⁻¹ * g * n') (esI k r a) (eI k r b) = (n⁻¹ * cE g * Um n') (esI k r a) b := by
    rw [← h]; rfl
  show (n⁻¹ * g * n') (esI k r a) (eI k r b) = (Lm n * Zm g * Um n') a b
  rw [h2, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b' _ => ?_
  congr 1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [sum_Es (M := ℂ) (fun l => n⁻¹ (esI k r a) l * cE g l b')
    (fun l hl => by rw [n_rowEs (n_inv_mem hn) _ l (by simp [esI]; omega) hl, zero_mul])]
  rfl

/- English proof (translation)
Simplify using `only [Um, Matrix.of_apply]`. Rewrite using `[n_colE hn c (eI k r b) (by simp [eI]; omega), if_neg (by intro h'; have := congrArg Fin.val h'; simp [eI] at this; omega)]`.
-/
lemma Um_lower {n : Mat k r} (hn : n ∈ Nset k r) (b c : Fin r) (h : c < b) : Um n b c = 0 := by
  simp only [Um, Matrix.of_apply]
  rw [n_colE hn c (eI k r b) (by simp [eI]; omega), if_neg (by intro h'; have := congrArg Fin.val h'; simp [eI] at this; omega)]

/- English proof (translation)
Simplify using `only [Um, Matrix.of_apply]`. Rewrite using `[n_colE hn b (eI k r b) le_rfl, if_pos rfl]`.
-/
lemma Um_diag {n : Mat k r} (hn : n ∈ Nset k r) (b : Fin r) : Um n b b = 1 := by
  simp only [Um, Matrix.of_apply]
  rw [n_colE hn b (eI k r b) le_rfl, if_pos rfl]

/- English proof (translation)
Unfold `sg; rw [if_pos (by right; simp [esI]; omega)]; ext; simp [esI, eI]; omega`.
-/
lemma sg_esI (a : Fin r) : sg k r (esI k r a) = eI k r a := by
  unfold sg; rw [if_pos (by right; simp [esI]; omega)]; ext; simp [esI, eI]; omega

/- English proof (translation)
Unfold `sg; rw [if_pos (by left; simp [eI])]; ext; simp [esI, eI]`.
-/
lemma sg_eI (a : Fin r) : sg k r (eI k r a) = esI k r a := by
  unfold sg; rw [if_pos (by left; simp [eI])]; ext; simp [esI, eI]

/- English proof (translation)
Unfold `ep; rw [if_neg (by simp [esI]; omega)]`.
-/
lemma ep_esI (a : Fin r) : ep k r (esI k r a) = 1 := by
  unfold ep; rw [if_neg (by simp [esI]; omega)]

/- English proof (translation)
Unfold `ep; rw [if_neg (by simp [eI]; omega)]`.
-/
lemma ep_eI (a : Fin r) : ep k r (eI k r a) = 1 := by
  unfold ep; rw [if_neg (by simp [eI]; omega)]

/- English proof (translation)
Simplify using `only [Lm, Matrix.of_apply]`. Rewrite using `[inv_apply (n_mem_G hn), sg_esI, sg_esI, ep_esI, ep_esI, one_mul, mul_one]`.
-/
lemma Lm_apply {n : Mat k r} (hn : n ∈ Nset k r) (a c : Fin r) :
    Lm n a c = star (n (eI k r c) (eI k r a)) := by
  simp only [Lm, Matrix.of_apply]
  rw [inv_apply (n_mem_G hn), sg_esI, sg_esI, ep_esI, ep_esI, one_mul, mul_one]

/- English proof (translation)
Rewrite using `[Lm_apply hn, n_colE hn a (eI k r c) (by simp [eI]; omega), if_neg (by intro h'; have := congrArg Fin.val h'; simp [eI] at this; omega)]`. Simplify using the standard rewrite rules.
-/
lemma Lm_upper {n : Mat k r} (hn : n ∈ Nset k r) (a c : Fin r) (h : a < c) : Lm n a c = 0 := by
  rw [Lm_apply hn, n_colE hn a (eI k r c) (by simp [eI]; omega),
    if_neg (by intro h'; have := congrArg Fin.val h'; simp [eI] at this; omega)]
  simp

/- English proof (translation)
Rewrite using `[Lm_apply hn, n_colE hn a (eI k r a) le_rfl, if_pos rfl]`. Simplify using the standard rewrite rules.
-/
lemma Lm_diag {n : Mat k r} (hn : n ∈ Nset k r) (a : Fin r) : Lm n a a = 1 := by
  rw [Lm_apply hn, n_colE hn a (eI k r a) le_rfl, if_pos rfl]; simp

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular (fun i j h => Um_lower hn i j h)]`. Simplify using `[Um_diag hn]`.
-/
lemma det_Um {n : Mat k r} (hn : n ∈ Nset k r) : (Um n).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j h => Um_lower hn i j h)]
  simp [Um_diag hn]

/- English proof (translation)
Rewrite using `[Matrix.det_of_isLowerTriangular _ (fun i j h => Lm_upper hn i j h)]`. Simplify using `[Lm_diag hn]`.
-/
lemma det_Lm {n : Mat k r} (hn : n ∈ Nset k r) : (Lm n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (fun i j h => Lm_upper hn i j h)]
  simp [Lm_diag hn]

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Matrix

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU

variable {r : ℕ}

def rs (b a : Fin r) : Fin (b.val + 1) → Fin r := fun i => if h : i.val < b.val then ⟨i.val, by omega⟩ else a

def cs (b : Fin r) : Fin (b.val + 1) → Fin r := fun i => ⟨i.val, by omega⟩

def mn (Y : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) : ℂ := (Y.submatrix (rs b a) (cs b)).det

def ld (Y : Matrix (Fin r) (Fin r) ℂ) (b : Fin r) : ℂ := mn Y b b

def ell (Y : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b ≤ a then mn Y a b / ld Y b else 0

def IsLU (L : Matrix (Fin r) (Fin r) ℂ) : Prop := (∀ i j : Fin r, i < j → L i j = 0) ∧ ∀ i, L i i = 1

def IsUU (U : Matrix (Fin r) (Fin r) ℂ) : Prop := (∀ i j : Fin r, j < i → U i j = 0) ∧ ∀ i, U i i = 1

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [rs, cs]`. Use `split_ifs with h`. Both sides reduce to the same expression. Use `ext`.

Simplify using the standard rewrite rules. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma rs_self (b : Fin r) : rs b b = cs b := by
  funext i
  simp only [rs, cs]
  split_ifs with h
  · rfl
  · ext; simp; have := i.isLt; omega

/- English proof (translation)
Introduce `i j h` and use `by have := congrArg Fin.val h; simp [cs] at this; exact Fin.ext this`.
-/
lemma cs_inj (b : Fin r) : Function.Injective (cs b) := fun i j h => by
  have := congrArg Fin.val h; simp [cs] at this; exact Fin.ext this

/- English proof (translation)
Rewrite using `[← Finset.sum_image (s := Finset.univ) (g := cs b) (fun i _ j _ hij => cs_inj b hij)]`. Use `(Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => h l ?_)).symm` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `hl (Finset.mem_image.2 ⟨⟨l.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)`.
-/
lemma sum_cs (b : Fin r) (f : Fin r → ℂ) (h : ∀ l : Fin r, b.val < l.val → f l = 0) :
    ∑ l, f l = ∑ i : Fin (b.val + 1), f (cs b i) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := cs b) (fun i _ j _ hij => cs_inj b hij)]
  refine (Finset.sum_subset (Finset.subset_univ _) (fun l _ hl => h l ?_)).symm
  by_contra hc
  exact hl (Finset.mem_image.2 ⟨⟨l.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/- English proof (translation)
Unfold `mn`. Establish `e : (Y * U).submatrix (rs b a) (cs b) = Y.submatrix (rs b a) (cs b) * U.submatrix (cs b) (cs b)`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Rewrite using `[sum_cs b (fun l => Y (rs b a i) l * U l (cs b j)) (fun l hl => by`.

Rewrite using `[hU.1 l (cs b j) (by rw [Fin.lt_def]; simp only [cs]; omega), mul_zero])]`. Establish `hdet : (U.submatrix (cs b) (cs b)).det = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular (fun i j h => by`. Simplify using `only [Matrix.submatrix_apply]`. Conclude with `hU.1 _ _ (by rw [Fin.lt_def] at h ⊢; simpa [cs] using h))]`.

Simplify using `[hU.2]`. Rewrite using `[e, Matrix.det_mul, hdet, mul_one]`.
-/
lemma mn_mul_upper (Y U : Matrix (Fin r) (Fin r) ℂ) (hU : IsUU U) (a b : Fin r) :
    mn (Y * U) a b = mn Y a b := by
  unfold mn
  have e : (Y * U).submatrix (rs b a) (cs b) =
      Y.submatrix (rs b a) (cs b) * U.submatrix (cs b) (cs b) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [sum_cs b (fun l => Y (rs b a i) l * U l (cs b j))
      (fun l hl => by
        rw [hU.1 l (cs b j) (by rw [Fin.lt_def]; simp only [cs]; omega), mul_zero])]
  have hdet : (U.submatrix (cs b) (cs b)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j h => by
      simp only [Matrix.submatrix_apply]
      exact hU.1 _ _ (by rw [Fin.lt_def] at h ⊢; simpa [cs] using h))]
    simp [hU.2]
  rw [e, Matrix.det_mul, hdet, mul_one]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp)`. Consider the case `insert t s ht ih`.

Rewrite using `[Finset.sum_insert ht, Finset.sum_insert ht, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih]`.
-/
lemma det_updateRow_fsum {n ι : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (i : n)
    (s : Finset ι) (c : ι → ℂ) (v : ι → n → ℂ) :
    (M.updateRow i (∑ t ∈ s, c t • v t)).det = ∑ t ∈ s, c t * (M.updateRow i (v t)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp)
  | insert t s ht ih =>
    rw [Finset.sum_insert ht, Finset.sum_insert ht, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih]

/- English proof (translation)
Establish `h1 : ∀ t : Fin r, f t = (if t.val < b then f t else 0) + (if b ≤ t.val then f t else 0)`. Introduce `t`. Distinguish the cases in `h : t.val < b`. Rewrite using `[if_pos h, if_neg (by omega), add_zero]`. Rewrite using `[if_neg h, if_pos (by omega), zero_add]`.

Rewrite using `[Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[← Finset.sum_image (s := Finset.univ) (g := Fin.castLE hb) (fun i _ j _ hij => Fin.castLE_injective hb hij)]`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE hb)))]`. Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations.

Take `⟨l, -, rfl⟩` from `Finset.mem_image.1 ht`. Rewrite using `[if_pos (by simp)]`. Introduce `t _ ht`. Rewrite using `[if_neg]`. Introduce `h`.

Conclude with `ht (Finset.mem_image.2 ⟨⟨t.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)`.
-/
lemma split_lt (b : ℕ) (hb : b ≤ r) (f : Fin r → ℂ) :
    ∑ t, f t = ∑ l : Fin b, f (Fin.castLE hb l) + ∑ t, if b ≤ t.val then f t else 0 := by
  have h1 : ∀ t : Fin r, f t = (if t.val < b then f t else 0) + (if b ≤ t.val then f t else 0) := by
    intro t; by_cases h : t.val < b
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_image (s := Finset.univ) (g := Fin.castLE hb)
    (fun i _ j _ hij => Fin.castLE_injective hb hij)]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE hb)))]
  · refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 ht
    rw [if_pos (by simp)]
  · intro t _ ht
    rw [if_neg]
    intro h
    exact ht (Finset.mem_image.2 ⟨⟨t.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/- English proof (translation)
Use `set S := rs b a`. Use `set C := cs b`. Set `Λ : Matrix (Fin (b.val + 1)) (Fin (b.val + 1)) ℂ` to `Matrix.of fun i j => if j.val < b.val then L (S i) (C j) else (if i = Fin.last b.val then 1 else 0)`. Set `Y0 : Matrix (Fin (b.val + 1)) (Fin (b.val + 1)) ℂ` to `Y.submatrix C C`. Set `c : Fin r → ℂ` to `fun t => if b ≤ t then L a t else 0`.

Set `v : Fin r → Fin (b.val + 1) → ℂ` to `fun t j => Y t (C j)`. Set `Yh` to `Y0.updateRow (Fin.last b.val) (∑ t, c t • v t)`. Establish `hb : b.val ≤ r` using `b.isLt.le`. Establish `key : (L * Y).submatrix S C = Λ * Yh`. Use extensionality with `i j`.

Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Rewrite using `[split_lt b.val hb, Fin.sum_univ_castSucc]`. Establish `hYc : ∀ l : Fin b.val, Yh (Fin.castSucc l) j = Y (Fin.castLE hb l) (C j)`. Introduce `l`. Simplify using `only [Yh, Y0]`.

Rewrite using `[Matrix.updateRow_ne (Fin.castSucc_lt_last l).ne]`. Simplify using `only [Matrix.submatrix_apply]`. Use `congr 1`. Establish `hΛc : ∀ l : Fin b.val, Λ i (Fin.castSucc l) = L (S i) (Fin.castLE hb l)`. Introduce `l`.

Simplify using `only [Λ, Matrix.of_apply, Fin.val_castSucc, l.isLt, if_true]`. Use `congr 1`. Simplify using `only [hYc, hΛc]`. Use `congr 1`. Establish `hYl : Yh (Fin.last b.val) j = ∑ t, c t * Y t (C j)`.

Simplify using `only [Yh, Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v]`. Rewrite using `[hYl]`. Distinguish the cases in `hi : i = Fin.last b.val`. Substitute `hi` using the available equality. Establish `hS : S (Fin.last b.val) = a`.

Simplify using `only [S, rs, Fin.val_last, lt_irrefl, dite_false]`. Simplify using `only [Λ, Matrix.of_apply, Fin.val_last, lt_irrefl, if_false, if_true, one_mul, hS, c]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : b.val ≤ t.val`. Establish `h2 : b ≤ t` using `Fin.le_def.2 h1`.

Rewrite using `[if_pos h1, if_pos h2]`. Establish `h2 : ¬ b ≤ t` using `fun h => h1 (Fin.le_def.1 h)`. Rewrite using `[if_neg h1, if_neg h2, zero_mul]`. Establish `hilt : i.val < b.val`. Use `i.isLt` as an intermediate fact.

Break down `Nat.lt_succ_iff_lt_or_eq.1 this with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (Fin.ext h) hi`. Simplify using `only [Λ, Matrix.of_apply, Fin.val_last, lt_irrefl, if_false, hi, zero_mul]`. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations.

Use `split_ifs with h1`. Establish `hS : S i = ⟨i.val, by omega⟩` using `by simp only [S, rs, hilt, dite_true]`. Rewrite using `[hS, hL.1 _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]`. Both sides reduce to the same expression. Establish `hΛ : Λ.det = 1`.

Rewrite using `[Matrix.det_of_isLowerTriangular _ (fun i j h => by`. Establish `h' : i < j` using `OrderDual.toDual_lt_toDual.1 h`. Rewrite `h'` using `[Fin.lt_def]`. Simplify using `only [Λ, Matrix.of_apply]`. Use `split_ifs with hj hi`.

Establish `hilt : i.val < b.val` using `by omega`. Establish `hS : S i = ⟨i.val, by omega⟩` using `by simp only [S, rs, hilt, dite_true]`. Rewrite using `[hS]`. Conclude with `hL.1 _ _ (by rw [Fin.lt_def]; simp [C, cs]; omega)`. It suffices to derive a contradiction.

Rewrite `h'` using `[hi]`. Simplify using `at h'`. Use `j.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use the proof step `rfl)]`.

Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Λ, Matrix.of_apply]`. Use `split_ifs with hi hi'`. Establish `hS : S i = ⟨i.val, by omega⟩` using `by simp only [S, rs, hi, dite_true]`. Rewrite using `[hS]`.

Conclude with `hL.2 _`. Both sides reduce to the same expression. Use the proof step `exfalso; exact hi' (Fin.ext (by simp; have := i.isLt; omega))`. Establish `hrow : ∀ t : Fin r, Y0.updateRow (Fin.last b.val) (v t) = Y.submatrix (rs b t) C`. Introduce `t`.

Use extensionality with `i j`. Distinguish the cases in `hi : i = Fin.last b.val`. Substitute `hi` using the available equality. Simplify using `only [Matrix.updateRow_self, v, Matrix.submatrix_apply, rs, Fin.val_last, lt_irrefl, dite_false]`. Rewrite using `[Matrix.updateRow_ne hi]`.

Establish `hilt : i.val < b.val`. Use `i.isLt` as an intermediate fact. Break down `Nat.lt_succ_iff_lt_or_eq.1 this with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (Fin.ext h) hi`.

Simplify using `only [Y0, Matrix.submatrix_apply, rs, hilt, dite_true, C, cs]`. Unfold `mn`. Rewrite using `[key, Matrix.det_mul, hΛ, one_mul]`. Simplify using `only [Yh]`. Rewrite using `[det_updateRow_fsum]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[hrow t]`. Distinguish the cases in `h : b ≤ t`. Simplify using `only [c, if_pos h]`. Both sides reduce to the same expression.

Simplify using `only [c, if_neg h, zero_mul]`.
-/
lemma mn_lower_mul (L Y : Matrix (Fin r) (Fin r) ℂ) (hL : IsLU L) (a b : Fin r) :
    mn (L * Y) a b = ∑ t, if b ≤ t then L a t * mn Y t b else 0 := by
  classical
  set S := rs b a
  set C := cs b
  let Λ : Matrix (Fin (b.val + 1)) (Fin (b.val + 1)) ℂ := Matrix.of fun i j =>
    if j.val < b.val then L (S i) (C j) else (if i = Fin.last b.val then 1 else 0)
  let Y0 : Matrix (Fin (b.val + 1)) (Fin (b.val + 1)) ℂ := Y.submatrix C C
  let c : Fin r → ℂ := fun t => if b ≤ t then L a t else 0
  let v : Fin r → Fin (b.val + 1) → ℂ := fun t j => Y t (C j)
  let Yh := Y0.updateRow (Fin.last b.val) (∑ t, c t • v t)
  have hb : b.val ≤ r := b.isLt.le
  have key : (L * Y).submatrix S C = Λ * Yh := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [split_lt b.val hb, Fin.sum_univ_castSucc]
    have hYc : ∀ l : Fin b.val, Yh (Fin.castSucc l) j = Y (Fin.castLE hb l) (C j) := by
      intro l
      simp only [Yh, Y0]
      rw [Matrix.updateRow_ne (Fin.castSucc_lt_last l).ne]
      simp only [Matrix.submatrix_apply]
      congr 1
    have hΛc : ∀ l : Fin b.val, Λ i (Fin.castSucc l) = L (S i) (Fin.castLE hb l) := by
      intro l
      simp only [Λ, Matrix.of_apply, Fin.val_castSucc, l.isLt, if_true]
      congr 1
    simp only [hYc, hΛc]
    congr 1
    have hYl : Yh (Fin.last b.val) j = ∑ t, c t * Y t (C j) := by
      simp only [Yh, Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v]
    rw [hYl]
    by_cases hi : i = Fin.last b.val
    · subst hi
      have hS : S (Fin.last b.val) = a := by
        simp only [S, rs, Fin.val_last, lt_irrefl, dite_false]
      simp only [Λ, Matrix.of_apply, Fin.val_last, lt_irrefl, if_false, if_true, one_mul, hS, c]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h1 : b.val ≤ t.val
      · have h2 : b ≤ t := Fin.le_def.2 h1
        rw [if_pos h1, if_pos h2]
      · have h2 : ¬ b ≤ t := fun h => h1 (Fin.le_def.1 h)
        rw [if_neg h1, if_neg h2, zero_mul]
    · have hilt : i.val < b.val := by
        have := i.isLt
        rcases Nat.lt_succ_iff_lt_or_eq.1 this with h | h
        · exact h
        · exact absurd (Fin.ext h) hi
      simp only [Λ, Matrix.of_apply, Fin.val_last, lt_irrefl, if_false, hi, zero_mul]
      refine Finset.sum_eq_zero fun t _ => ?_
      split_ifs with h1
      · have hS : S i = ⟨i.val, by omega⟩ := by simp only [S, rs, hilt, dite_true]
        rw [hS, hL.1 _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]
      · rfl
  have hΛ : Λ.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ (fun i j h => by
      have h' : i < j := OrderDual.toDual_lt_toDual.1 h
      rw [Fin.lt_def] at h'
      simp only [Λ, Matrix.of_apply]
      split_ifs with hj hi
      · have hilt : i.val < b.val := by omega
        have hS : S i = ⟨i.val, by omega⟩ := by simp only [S, rs, hilt, dite_true]
        rw [hS]
        exact hL.1 _ _ (by rw [Fin.lt_def]; simp [C, cs]; omega)
      · exfalso; rw [hi] at h'; simp at h'; have := j.isLt; omega
      · rfl)]
    refine Finset.prod_eq_one fun i _ => ?_
    simp only [Λ, Matrix.of_apply]
    split_ifs with hi hi'
    · have hS : S i = ⟨i.val, by omega⟩ := by simp only [S, rs, hi, dite_true]
      rw [hS]; exact hL.2 _
    · rfl
    · exfalso; exact hi' (Fin.ext (by simp; have := i.isLt; omega))
  have hrow : ∀ t : Fin r, Y0.updateRow (Fin.last b.val) (v t) = Y.submatrix (rs b t) C := by
    intro t
    ext i j
    by_cases hi : i = Fin.last b.val
    · subst hi
      simp only [Matrix.updateRow_self, v, Matrix.submatrix_apply, rs, Fin.val_last, lt_irrefl, dite_false]
    · rw [Matrix.updateRow_ne hi]
      have hilt : i.val < b.val := by
        have := i.isLt
        rcases Nat.lt_succ_iff_lt_or_eq.1 this with h | h
        · exact h
        · exact absurd (Fin.ext h) hi
      simp only [Y0, Matrix.submatrix_apply, rs, hilt, dite_true, C, cs]
  unfold mn
  rw [key, Matrix.det_mul, hΛ, one_mul]
  simp only [Yh]
  rw [det_updateRow_fsum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hrow t]
  by_cases h : b ≤ t
  · simp only [c, if_pos h]; rfl
  · simp only [c, if_neg h, zero_mul]

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU

open Matrix

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU

variable {r : ℕ}

/- English proof (translation)
Unfold `ld`. Rewrite using `[mn_mul_upper _ _ hU, mn_lower_mul _ _ hL]`. Rewrite using `[Finset.sum_eq_single b]`. Rewrite using `[if_pos le_rfl, hL.2, one_mul]`. Introduce `t _ htb split_ifs with h`.

Rewrite using `[hL.1 b t (lt_of_le_of_ne h (Ne.symm htb)), zero_mul]`. Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`.
-/
lemma ld_LYU (L Y U : Matrix (Fin r) (Fin r) ℂ) (hL : IsLU L) (hU : IsUU U) (b : Fin r) :
    ld (L * Y * U) b = ld Y b := by
  unfold ld
  rw [mn_mul_upper _ _ hU, mn_lower_mul _ _ hL]
  rw [Finset.sum_eq_single b]
  · rw [if_pos le_rfl, hL.2, one_mul]
  · intro t _ htb
    split_ifs with h
    · rw [hL.1 b t (lt_of_le_of_ne h (Ne.symm htb)), zero_mul]
    · rfl
  · intro h; exact absurd (Finset.mem_univ b) h

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [ell, Matrix.of_apply, Matrix.mul_apply]`. Rewrite using `[ld_LYU L Y U hL hU, mn_mul_upper _ _ hU, mn_lower_mul _ _ hL]`. Distinguish the cases in `hba : b ≤ a`. Rewrite using `[if_pos hba, Finset.sum_div]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite using `[if_neg hba]`.

Use `symm`. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[hL.1 a t (lt_of_lt_of_le (not_le.1 hba) h), zero_mul]`. Rewrite using `[mul_zero]`.
-/
lemma ell_LYU (L Y U : Matrix (Fin r) (Fin r) ℂ) (hL : IsLU L) (hU : IsUU U) :
    ell (L * Y * U) = L * ell Y := by
  ext a b
  simp only [ell, Matrix.of_apply, Matrix.mul_apply]
  rw [ld_LYU L Y U hL hU, mn_mul_upper _ _ hU, mn_lower_mul _ _ hL]
  by_cases hba : b ≤ a
  · rw [if_pos hba, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with h
    · ring
    · simp
  · rw [if_neg hba]
    symm
    refine Finset.sum_eq_zero fun t _ => ?_
    split_ifs with h
    · rw [hL.1 a t (lt_of_lt_of_le (not_le.1 hba) h), zero_mul]
    · rw [mul_zero]

/- English proof (translation)
Use `⟨fun i j h => ?_, fun i => ?_⟩` and prove the remaining obligations. Simplify using `[ell, not_le.2 h]`. Simplify using `only [ell, Matrix.of_apply, le_refl, if_true]`. Conclude with `div_self (hY i)`.
-/
lemma ell_isLU (Y : Matrix (Fin r) (Fin r) ℂ) (hY : ∀ b, ld Y b ≠ 0) : IsLU (ell Y) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp [ell, not_le.2 h]
  · simp only [ell, Matrix.of_apply, le_refl, if_true]
    exact div_self (hY i)

/- English proof (translation)
Rewrite using `[Matrix.det_of_isLowerTriangular _ (fun i j h => hL.1 i j (OrderDual.toDual_lt_toDual.1 h))]`. Simplify using `[hL.2]`.
-/
lemma det_isLU {L : Matrix (Fin r) (Fin r) ℂ} (hL : IsLU L) : L.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (fun i j h => hL.1 i j (OrderDual.toDual_lt_toDual.1 h))]
  simp [hL.2]

/- English proof (translation)
Rewrite using `[ell_LYU L Y U hL hU, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (by rw [det_isLU (ell_isLU Y hY)]; exact isUnit_one), Matrix.mul_one]`.
-/
lemma solve_L (L Y U : Matrix (Fin r) (Fin r) ℂ) (hL : IsLU L) (hU : IsUU U) (hY : ∀ b, ld Y b ≠ 0) :
    L = ell (L * Y * U) * (ell Y)⁻¹ := by
  rw [ell_LYU L Y U hL hU, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (by rw [det_isLU (ell_isLU Y hY)]; exact isUnit_one), Matrix.mul_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j h => hU.1 j i h, fun i => hU.2 i⟩`.
-/
lemma transpose_upper_unitriangular {U : Matrix (Fin r) (Fin r) ℂ} (hU : IsUU U) : IsLU Uᵀ := ⟨fun i j h => hU.1 j i h, fun i => hU.2 i⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j h => hL.1 j i h, fun i => hL.2 i⟩`.
-/
lemma transpose_lower_unitriangular {L : Matrix (Fin r) (Fin r) ℂ} (hL : IsLU L) : IsUU Lᵀ := ⟨fun i j h => hL.1 j i h, fun i => hL.2 i⟩

/- English proof (translation)
Unfold `ld mn`. Rewrite using `[rs_self]`. Rewrite using `[show Yᵀ.submatrix (cs b) (cs b) = (Y.submatrix (cs b) (cs b))ᵀ from rfl, Matrix.det_transpose]`.
-/
lemma T_smul_mem_dual_lattice (Y : Matrix (Fin r) (Fin r) ℂ) (b : Fin r) : ld Yᵀ b = ld Y b := by
  unfold ld mn
  rw [rs_self]
  rw [show Yᵀ.submatrix (cs b) (cs b) = (Y.submatrix (cs b) (cs b))ᵀ from rfl, Matrix.det_transpose]

/- English proof (translation)
Use `Formalism.FourierDecayAlt.P.Ux5.det_norm_le A (m := B) hA` as an intermediate fact. Simplify using `using this`.
-/
lemma norm_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (B : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ B) :
    ‖A.det‖ ≤ (n.factorial : ℝ) * B ^ n := by
  have := Formalism.FourierDecayAlt.P.Ux5.det_norm_le A (m := B) hA
  simpa using this

/- English proof (translation)
Unfold `mn`. Establish `h` using `norm_det_le (Y.submatrix (rs b a) (cs b)) B (fun i j => hY _ _)`. Use `h.trans (mul_le_mul ?_ (pow_le_pow_right₀ hB b.isLt) (by positivity) (by positivity))` and prove the remaining obligations. Conclude with `Nat.factorial_le b.isLt` after adjusting the coercions.
-/
lemma norm_mn_le (Y : Matrix (Fin r) (Fin r) ℂ) (B : ℝ) (hB : 1 ≤ B) (hY : ∀ i j, ‖Y i j‖ ≤ B) (a b : Fin r) :
    ‖mn Y a b‖ ≤ (r.factorial : ℝ) * B ^ r := by
  unfold mn
  have h := norm_det_le (Y.submatrix (rs b a) (cs b)) B (fun i j => hY _ _)
  refine h.trans (mul_le_mul ?_ (pow_le_pow_right₀ hB b.isLt) (by positivity) (by positivity))
  exact_mod_cast Nat.factorial_le b.isLt

/- English proof (translation)
Simplify using `only [ell, Matrix.of_apply]`. Use `split_ifs`. Rewrite using `[norm_div]`. Conclude with `div_le_div₀ (by positivity) (norm_mn_le Y B hB hY a b) hδ (hld b)`. Simplify using the standard rewrite rules.

Check the signs of the components of the expression.
-/
lemma norm_ell_le (Y : Matrix (Fin r) (Fin r) ℂ) (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 < δ)
    (hY : ∀ i j, ‖Y i j‖ ≤ B) (hld : ∀ b, δ ≤ ‖ld Y b‖) (a b : Fin r) :
    ‖ell Y a b‖ ≤ (r.factorial : ℝ) * B ^ r / δ := by
  simp only [ell, Matrix.of_apply]
  split_ifs
  · rw [norm_div]
    exact div_le_div₀ (by positivity) (norm_mn_le Y B hB hY a b) hδ (hld b)
  · simp; positivity

/- English proof (translation)
Rewrite using `[Matrix.adjugate_apply]`. Apply `norm_det_le` to reduce the goal to its premises. Introduce `i' j'`. Distinguish the cases in `h : i' = j`. Substitute `h` using the available equality.

Rewrite using `[Matrix.updateRow_self]`. Simplify using `only [Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp <;> linarith`. Rewrite using `[Matrix.updateRow_ne h]`. Conclude with `hA _ _`.
-/
lemma norm_adj_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (B : ℝ) (hB : 1 ≤ B) (hA : ∀ i j, ‖A i j‖ ≤ B)
    (i j : Fin n) : ‖A.adjugate i j‖ ≤ (n.factorial : ℝ) * B ^ n := by
  rw [Matrix.adjugate_apply]
  apply norm_det_le
  intro i' j'
  by_cases h : i' = j
  · subst h
    rw [Matrix.updateRow_self]
    simp only [Pi.single_apply]
    split_ifs <;> simp <;> linarith
  · rw [Matrix.updateRow_ne h]; exact hA _ _

/- English proof (translation)
Establish `hd : A.det ≠ 0` using `fun h => by rw [h, norm_zero] at hdet; linarith`. Establish `h1` using `norm_adj_le A B hB hA i j`. Establish `h2` using `inv_anti₀ hδ hdet`. Rewrite using `[Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul, norm_mul, norm_inv, div_eq_mul_inv]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma norm_inv_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 < δ)
    (hA : ∀ i j, ‖A i j‖ ≤ B) (hdet : δ ≤ ‖A.det‖) (i j : Fin n) :
    ‖A⁻¹ i j‖ ≤ (n.factorial : ℝ) * B ^ n / δ := by
  have hd : A.det ≠ 0 := fun h => by rw [h, norm_zero] at hdet; linarith
  have h1 := norm_adj_le A B hB hA i j
  have h2 := inv_anti₀ hδ hdet
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul, norm_mul, norm_inv, div_eq_mul_inv]
  calc ‖A.det‖⁻¹ * ‖A.adjugate i j‖ = ‖A.adjugate i j‖ * ‖A.det‖⁻¹ := mul_comm _ _
    _ ≤ ((n.factorial : ℝ) * B ^ n) * δ⁻¹ := mul_le_mul h1 h2 (by positivity) (by positivity)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `: ∀ l ∈ Finset.univ, ‖A i l * B' l j‖ ≤ a * b` using `fun l _ => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hA i l) (hB l j) (norm_nonneg _) ha`.

Use `(Finset.sum_le_card_nsmul _ _ _ this).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
lemma norm_mul_entry {m n p : Type*} [Fintype n] (A : Matrix m n ℂ) (B' : Matrix n p ℂ) (a b : ℝ)
    (ha : 0 ≤ a) (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B' i j‖ ≤ b) (i : m) (j : p) :
    ‖(A * B') i j‖ ≤ (Fintype.card n : ℝ) * (a * b) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ Finset.univ, ‖A i l * B' l j‖ ≤ a * b := fun l _ => by
    rw [norm_mul]; exact mul_le_mul (hA i l) (hB l j) (norm_nonneg _) ha
  refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
  simp

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU

open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `Real.sqrt_nonneg _`.
-/
lemma gN_nonneg (y : Mat k r) : 0 ≤ gN y := Real.sqrt_nonneg _

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.Ux6.entry_le_gN y i j`.
-/
lemma ent_le (y : Mat k r) (i j : Fin (2 * r + k + 1)) : ‖y i j‖ ≤ gN y := Formalism.FourierDecayAlt.P.Ux6.entry_le_gN y i j

/- English proof (translation)
Unfold `gN`. Rewrite using `[Real.sqrt_le_left (by positivity)]`. Establish `: ∀ i j, Complex.normSq (y i j) ≤ B ^ 2` using `fun i j => by`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (h i j) 2`.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma gN_le_of_ent (y : Mat k r) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i j, ‖y i j‖ ≤ B) :
    gN y ≤ ((2 * r + k + 1 : ℕ) : ℝ) * B := by
  unfold gN
  rw [Real.sqrt_le_left (by positivity)]
  have : ∀ i j, Complex.normSq (y i j) ≤ B ^ 2 := fun i j => by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  calc ∑ i, ∑ j, Complex.normSq (y i j) ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), B ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => this i j
    _ = (((2 * r + k + 1 : ℕ) : ℝ) * B) ^ 2 := by simp [Finset.sum_const, Finset.card_univ]; ring

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (n_mem_G hn)) hg) (n_mem_G hn')`.
-/
lemma x_mem {g n n' : Mat k r} (hg : g ∈ GV k r) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    n⁻¹ * g * n' ∈ GV k r :=
  Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (n_mem_G hn)) hg) (n_mem_G hn')

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (x_mem hg hn hn')`.
-/
lemma one_le_X {g n n' : Mat k r} (hg : g ∈ GV k r) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    1 ≤ gN (n⁻¹ * g * n') := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (x_mem hg hn hn')

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j h => Lm_upper hn i j h, Lm_diag hn⟩`.
-/
lemma isLU_Lm {n : Mat k r} (hn : n ∈ Nset k r) : IsLU (Lm n) := ⟨fun i j h => Lm_upper hn i j h, Lm_diag hn⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j h => Um_lower hn i j h, Um_diag hn⟩`.
-/
lemma isUU_Um {n : Mat k r} (hn : n ∈ Nset k r) : IsUU (Um n) := ⟨fun i j h => Um_lower hn i j h, Um_diag hn⟩

/- English proof (translation)
The claim follows from `ent_le y _ _`.
-/
lemma Zm_ent (y : Mat k r) (a b : Fin r) : ‖Zm y a b‖ ≤ gN y := ent_le y _ _

def lowerFactorEntryConstant (r : ℕ) (Γ δ : ℝ) : ℝ := 1 + (r.factorial : ℝ) * Γ ^ r / δ

def cL (r : ℕ) (Γ δ : ℝ) : ℝ := (r : ℝ) * (((r.factorial : ℝ) / δ) * ((r.factorial : ℝ) * lowerFactorEntryConstant r Γ δ ^ r))

/- English proof (translation)
Unfold `lowerFactorEntryConstant; have : 0 ≤ (r.factorial : ℝ) * Γ ^ r / δ := by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma lower_factor_constant_ge_one (r : ℕ) {Γ δ : ℝ} (hΓ : 1 ≤ Γ) (hδ : 0 < δ) : 1 ≤ lowerFactorEntryConstant r Γ δ := by
  unfold lowerFactorEntryConstant; have : 0 ≤ (r.factorial : ℝ) * Γ ^ r / δ := by positivity
  linarith

/- English proof (translation)
Unfold `cL`. Use `lower_factor_constant_ge_one r hΓ hδ` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma cL_nonneg (r : ℕ) {Γ δ : ℝ} (hΓ : 1 ≤ Γ) (hδ : 0 < δ) : 0 ≤ cL r Γ δ := by
  unfold cL; have := lower_factor_constant_ge_one r hΓ hδ; positivity

/- English proof (translation)
Establish `hne : ∀ b, ld Y b ≠ 0` using `fun b h => by have := hld b; rw [h, norm_zero] at this; linarith`. Establish `h` using `norm_inv_le (ell Y) (lowerFactorEntryConstant r Γ δ) 1 (lower_factor_constant_ge_one r hΓ hδ) one_pos (fun i j => (norm_ell_le Y Γ δ hΓ hδ hY hld i j).trans (by unfold lowerFactorEntryConstant; linarith)) (by rw [det_isLU (ell_isLU Y hne), norm_one]) a b`. Simplify using `using h`.
-/
lemma ellinv_bd (Y : Matrix (Fin r) (Fin r) ℂ) {Γ δ : ℝ} (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hY : ∀ a b, ‖Y a b‖ ≤ Γ)
    (hld : ∀ b, δ ≤ ‖ld Y b‖) (a b : Fin r) :
    ‖(ell Y)⁻¹ a b‖ ≤ (r.factorial : ℝ) * lowerFactorEntryConstant r Γ δ ^ r := by
  have hne : ∀ b, ld Y b ≠ 0 := fun b h => by have := hld b; rw [h, norm_zero] at this; linarith
  have h := norm_inv_le (ell Y) (lowerFactorEntryConstant r Γ δ) 1 (lower_factor_constant_ge_one r hΓ hδ) one_pos
    (fun i j => (norm_ell_le Y Γ δ hΓ hδ hY hld i j).trans (by unfold lowerFactorEntryConstant; linarith))
    (by rw [det_isLU (ell_isLU Y hne), norm_one]) a b
  simpa using h

/- English proof (translation)
Establish `hne : ∀ b, ld Y b ≠ 0` using `fun b h => by have := hld b; rw [h, norm_zero] at this; linarith`. Rewrite using `[solve_L L Y U hL hU hne]`. Establish `h1 : ∀ i j, ‖ell (L * Y * U) i j‖ ≤ (r.factorial : ℝ) * X ^ r / δ` using `fun i j => norm_ell_le _ X δ hX hδ hZ (fun b => by rw [ld_LYU L Y U hL hU]; exact hld b) i j`. Establish `h2` using `ellinv_bd Y hΓ hδ hY hld`. Apply the tactic sequence `refine (norm_mul_entry _ _ _ _ (by positivity) h1 h2 a b).trans (le_of_eq ?_)`.

Simplify using `only [Fintype.card_fin, cL]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma L_bd (L Y U : Matrix (Fin r) (Fin r) ℂ) (hL : IsLU L) (hU : IsUU U) {Γ δ X : ℝ} (hΓ : 1 ≤ Γ)
    (hδ : 0 < δ) (hX : 1 ≤ X) (hY : ∀ a b, ‖Y a b‖ ≤ Γ) (hld : ∀ b, δ ≤ ‖ld Y b‖)
    (hZ : ∀ a b, ‖(L * Y * U) a b‖ ≤ X) (a b : Fin r) : ‖L a b‖ ≤ cL r Γ δ * X ^ r := by
  have hne : ∀ b, ld Y b ≠ 0 := fun b h => by have := hld b; rw [h, norm_zero] at this; linarith
  rw [solve_L L Y U hL hU hne]
  have h1 : ∀ i j, ‖ell (L * Y * U) i j‖ ≤ (r.factorial : ℝ) * X ^ r / δ := fun i j =>
    norm_ell_le _ X δ hX hδ hZ (fun b => by rw [ld_LYU L Y U hL hU]; exact hld b) i j
  have h2 := ellinv_bd Y hΓ hδ hY hld
  refine (norm_mul_entry _ _ _ _ (by positivity) h1 h2 a b).trans (le_of_eq ?_)
  simp only [Fintype.card_fin, cL]
  ring

/- English proof (translation)
Establish `e : (L * Y * U)ᵀ = Uᵀ * Yᵀ * Lᵀ` using `by simp [Matrix.transpose_mul, Matrix.mul_assoc]`. Use `L_bd Uᵀ Yᵀ Lᵀ (transpose_upper_unitriangular hU) (transpose_lower_unitriangular hL) hΓ hδ hX (fun a b => hY b a) (fun b => by rw [T_smul_mem_dual_lattice]; exact hld b) (fun a b => by rw [← e]; exact hZ b a) b a` as an intermediate fact. Simplify using `using this`.
-/
lemma U_bd (L Y U : Matrix (Fin r) (Fin r) ℂ) (hL : IsLU L) (hU : IsUU U) {Γ δ X : ℝ} (hΓ : 1 ≤ Γ)
    (hδ : 0 < δ) (hX : 1 ≤ X) (hY : ∀ a b, ‖Y a b‖ ≤ Γ) (hld : ∀ b, δ ≤ ‖ld Y b‖)
    (hZ : ∀ a b, ‖(L * Y * U) a b‖ ≤ X) (a b : Fin r) : ‖U a b‖ ≤ cL r Γ δ * X ^ r := by
  have e : (L * Y * U)ᵀ = Uᵀ * Yᵀ * Lᵀ := by simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have := L_bd Uᵀ Yᵀ Lᵀ (transpose_upper_unitriangular hU) (transpose_lower_unitriangular hL) hΓ hδ hX (fun a b => hY b a)
    (fun b => by rw [T_smul_mem_dual_lattice]; exact hld b) (fun a b => by rw [← e]; exact hZ b a) b a
  simpa using this

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU

variable {k r : ℕ}

def cZi (r : ℕ) (δ : ℝ) : ℝ := (r.factorial : ℝ) / δ
def c5 (r : ℕ) (Γ δ : ℝ) : ℝ := (r : ℝ) * (((r : ℝ) * (Γ * cL r Γ δ)) * cZi r δ)
def c8 (r : ℕ) (δ : ℝ) : ℝ := (r : ℝ) * cZi r δ
def cPg (r : ℕ) (Γ δ : ℝ) : ℝ := (r : ℝ) * (Γ * (cZi r δ * Γ ^ r))
def c9 (r : ℕ) (Γ δ : ℝ) : ℝ := (r : ℝ) * (c8 r δ * cL r Γ δ)
def c10 (r : ℕ) (Γ δ : ℝ) : ℝ := (r : ℝ) * (cPg r Γ δ * c5 r Γ δ) + c8 r δ
def c11 (r : ℕ) (Γ δ : ℝ) : ℝ := 1 + c5 r Γ δ + c10 r Γ δ
def c13 (k r : ℕ) (Γ δ : ℝ) : ℝ :=
  c9 r Γ δ + ((2 * r + k + 1 : ℕ) : ℝ) * (c11 r Γ δ * cPg r Γ δ) + c11 r Γ δ

section
variable {Γ δ : ℝ} (hΓ : 1 ≤ Γ) (hδ : 0 < δ)
include hΓ hδ

/- English proof (translation)
Unfold `cZi`. Check the signs of the components of the expression.
-/
lemma cZi_nn : 0 ≤ cZi r δ := by unfold cZi; positivity
/- English proof (translation)
Unfold `c5`. Use `cL_nonneg r hΓ hδ` as an intermediate fact. Use `cZi_nn (r := r) hΓ hδ` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma orbit_constant_five_nonneg : 0 ≤ c5 r Γ δ := by
  unfold c5; have := cL_nonneg r hΓ hδ; have := cZi_nn (r := r) hΓ hδ; positivity
/- English proof (translation)
Unfold `c8`. Use `cZi_nn (r := r) hΓ hδ` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma orbit_constant_eight_nonneg : 0 ≤ c8 r δ := by unfold c8; have := cZi_nn (r := r) hΓ hδ; positivity
/- English proof (translation)
Unfold `cPg; have := cZi_nn (r := r) hΓ hδ; have : 0 ≤ Γ := by linarith`. Check the signs of the components of the expression.
-/
lemma cPg_nn : 0 ≤ cPg r Γ δ := by
  unfold cPg; have := cZi_nn (r := r) hΓ hδ; have : 0 ≤ Γ := by linarith
  positivity
/- English proof (translation)
Unfold `c9`. Use `cL_nonneg r hΓ hδ` as an intermediate fact. Use `orbit_constant_eight_nonneg (r := r) hΓ hδ` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma orbit_constant_nine_nonneg : 0 ≤ c9 r Γ δ := by
  unfold c9; have := cL_nonneg r hΓ hδ; have := orbit_constant_eight_nonneg (r := r) hΓ hδ; positivity
/- English proof (translation)
Unfold `c10`. Use `orbit_constant_five_nonneg (r := r) hΓ hδ` as an intermediate fact. Use `orbit_constant_eight_nonneg (r := r) hΓ hδ` as an intermediate fact. Use `cPg_nn (r := r) hΓ hδ` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma orbit_constant_ten_nonneg : 0 ≤ c10 r Γ δ := by
  unfold c10; have := orbit_constant_five_nonneg (r := r) hΓ hδ; have := orbit_constant_eight_nonneg (r := r) hΓ hδ
  have := cPg_nn (r := r) hΓ hδ; positivity
/- English proof (translation)
Unfold `c11`. Use `orbit_constant_five_nonneg (r := r) hΓ hδ` as an intermediate fact. Use `orbit_constant_ten_nonneg (r := r) hΓ hδ` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma orbit_constant_eleven_ge_one : 1 ≤ c11 r Γ δ := by
  unfold c11; have := orbit_constant_five_nonneg (r := r) hΓ hδ; have := orbit_constant_ten_nonneg (r := r) hΓ hδ; linarith
/- English proof (translation)
Unfold `c13`. Use `orbit_constant_nine_nonneg (r := r) hΓ hδ` as an intermediate fact. Use `orbit_constant_eleven_ge_one (r := r) hΓ hδ` as an intermediate fact. Use `cPg_nn (r := r) hΓ hδ` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma orbit_constant_thirteen_nonneg : 0 ≤ c13 k r Γ δ := by
  unfold c13; have := orbit_constant_nine_nonneg (r := r) hΓ hδ; have := orbit_constant_eleven_ge_one (r := r) hΓ hδ
  have := cPg_nn (r := r) hΓ hδ; positivity
end

/- English proof (translation)
The claim follows from `pow_le_pow_right₀ hX h`.
-/
lemma pow_mono {X : ℝ} (hX : 1 ≤ X) {a b : ℕ} (h : a ≤ b) : X ^ a ≤ X ^ b := pow_le_pow_right₀ hX h

section main

variable {Γ δ : ℝ} {g n n' : Mat k r}

/- English proof (translation)
The claim follows from `L_bd (Lm n) (Zm g) (Um n') (isLU_Lm hn) (isUU_Um hn') hΓ hδ (one_le_X hg hn hn') (fun a b => (Zm_ent g a b).trans hgΓ) hld (fun a b => by rw [← Zm_mul hn hn']; exact Zm_ent _ a b) a b`.
-/
lemma Lm_bd (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (a b : Fin r) :
    ‖Lm n a b‖ ≤ cL r Γ δ * gN (n⁻¹ * g * n') ^ r :=
  L_bd (Lm n) (Zm g) (Um n') (isLU_Lm hn) (isUU_Um hn') hΓ hδ (one_le_X hg hn hn')
    (fun a b => (Zm_ent g a b).trans hgΓ) hld (fun a b => by rw [← Zm_mul hn hn']; exact Zm_ent _ a b) a b

/- English proof (translation)
The claim follows from `U_bd (Lm n) (Zm g) (Um n') (isLU_Lm hn) (isUU_Um hn') hΓ hδ (one_le_X hg hn hn') (fun a b => (Zm_ent g a b).trans hgΓ) hld (fun a b => by rw [← Zm_mul hn hn']; exact Zm_ent _ a b) a b`.
-/
lemma Um_bd (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (a b : Fin r) :
    ‖Um n' a b‖ ≤ cL r Γ δ * gN (n⁻¹ * g * n') ^ r :=
  U_bd (Lm n) (Zm g) (Um n') (isLU_Lm hn) (isUU_Um hn') hΓ hδ (one_le_X hg hn hn')
    (fun a b => (Zm_ent g a b).trans hgΓ) hld (fun a b => by rw [← Zm_mul hn hn']; exact Zm_ent _ a b) a b

/- English proof (translation)
Rewrite using `[Zm_mul hn hn', Matrix.det_mul, Matrix.det_mul, det_Lm hn, det_Um hn', one_mul, mul_one]`.
-/
lemma det_Zx (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (g : Mat k r) :
    (Zm (n⁻¹ * g * n')).det = (Zm g).det := by
  rw [Zm_mul hn hn', Matrix.det_mul, Matrix.det_mul, det_Lm hn, det_Um hn', one_mul, mul_one]

/- English proof (translation)
Establish `h` using `norm_inv_le (Zm (n⁻¹ * g * n')) (gN (n⁻¹ * g * n')) δ (one_le_X hg hn hn') hδ (fun a b => Zm_ent _ a b) (by rw [det_Zx hn hn']; exact hdet) a b`. Simplify `h` using `[cZi, Fintype.card_fin, div_mul_eq_mul_div]`.
-/
lemma Zxinv_bd (hδ : 0 < δ) (hg : g ∈ GV k r) (hdet : δ ≤ ‖(Zm g).det‖)
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (a b : Fin r) :
    ‖(Zm (n⁻¹ * g * n'))⁻¹ a b‖ ≤ cZi r δ * gN (n⁻¹ * g * n') ^ r := by
  have h := norm_inv_le (Zm (n⁻¹ * g * n')) (gN (n⁻¹ * g * n')) δ (one_le_X hg hn hn') hδ
    (fun a b => Zm_ent _ a b) (by rw [det_Zx hn hn']; exact hdet) a b
  simpa [cZi, Fintype.card_fin, div_mul_eq_mul_div] using h

/- English proof (translation)
Establish `hd : IsUnit (Zm (n⁻¹ * g * n')).det`. Rewrite using `[det_Zx hn hn']`. Use `isUnit_iff_ne_zero.2 fun h => ?_` and prove the remaining obligations. Rewrite `hdet` using `[h, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Zm_mul hn hn', Matrix.mul_nonsing_inv _ hd]`.
-/
lemma Linv_eq (hδ : 0 < δ) (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    (Lm n)⁻¹ = Zm g * Um n' * (Zm (n⁻¹ * g * n'))⁻¹ := by
  have hd : IsUnit (Zm (n⁻¹ * g * n')).det := by
    rw [det_Zx hn hn']; refine isUnit_iff_ne_zero.2 fun h => ?_
    rw [h, norm_zero] at hdet; linarith
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Zm_mul hn hn', Matrix.mul_nonsing_inv _ hd]

/- English proof (translation)
Use `set X := gN (n⁻¹ * g * n')`. Rewrite using `[Linv_eq hδ hdet hn hn']`. Establish `h1 : ∀ i j, ‖(Zm g * Um n') i j‖ ≤ (r : ℝ) * (Γ * (cL r Γ δ * X ^ r))`. Introduce `i j`. Apply the tactic sequence `have := norm_mul_entry (Zm g) (Um n') Γ (cL r Γ δ * X ^ r) (by linarith) (fun a b => (Zm_ent g a b).trans hgΓ) (Um_bd hΓ hδ hg hgΓ hld hn hn') i j`.

Simplify using `using this`. Apply the tactic sequence `have h2 := norm_mul_entry (Zm g * Um n') (Zm (n⁻¹ * g * n'))⁻¹ _ _ (by have := cL_nonneg r hΓ hδ; have : 0 ≤ X := gN_nonneg _; positivity) h1 (Zxinv_bd hδ hg hdet hn hn') a b`. Use `h2.trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [Fintype.card_fin, c5]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma Linv_bd (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (a b : Fin r) :
    ‖(Lm n)⁻¹ a b‖ ≤ c5 r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r) := by
  set X := gN (n⁻¹ * g * n')
  rw [Linv_eq hδ hdet hn hn']
  have h1 : ∀ i j, ‖(Zm g * Um n') i j‖ ≤ (r : ℝ) * (Γ * (cL r Γ δ * X ^ r)) := by
    intro i j
    have := norm_mul_entry (Zm g) (Um n') Γ (cL r Γ δ * X ^ r) (by linarith)
      (fun a b => (Zm_ent g a b).trans hgΓ) (Um_bd hΓ hδ hg hgΓ hld hn hn') i j
    simpa using this
  have h2 := norm_mul_entry (Zm g * Um n') (Zm (n⁻¹ * g * n'))⁻¹ _ _
    (by have := cL_nonneg r hΓ hδ; have : 0 ≤ X := gN_nonneg _; positivity) h1
    (Zxinv_bd hδ hg hdet hn hn') a b
  refine h2.trans (le_of_eq ?_)
  simp only [Fintype.card_fin, c5]
  ring

/- English proof (translation)
Establish `hNL : (Matrix.of fun b a => n (esI k r b) (esI k r a)) * Lm n = 1`. Use extensionality with `b a`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Lm]`. Establish `hu : IsUnit n.det` using `closedN.unit n hn`. Establish `e` using `congrFun (congrFun (Matrix.mul_nonsing_inv n hu) (esI k r b)) (esI k r a)`.

Rewrite `e` using `[Matrix.mul_apply, sum_Es (M := ℂ) (fun l => n (esI k r b) l * n⁻¹ l (esI k r a)) (fun l hl => by rw [n_rowEs hn _ l (by simp [esI]; omega) hl, zero_mul])]`. Rewrite using `[e, Matrix.one_apply, Matrix.one_apply]`. Simplify using `only [(esI_inj (k := k)).eq_iff]`. Rewrite using `[Matrix.inv_eq_left_inv hNL]`. Both sides reduce to the same expression.
-/
lemma Nstar (hn : n ∈ Nset k r) (b a : Fin r) : n (esI k r b) (esI k r a) = (Lm n)⁻¹ b a := by
  have hNL : (Matrix.of fun b a => n (esI k r b) (esI k r a)) * Lm n = 1 := by
    ext b a
    simp only [Matrix.mul_apply, Matrix.of_apply, Lm]
    have hu : IsUnit n.det := closedN.unit n hn
    have e := congrFun (congrFun (Matrix.mul_nonsing_inv n hu) (esI k r b)) (esI k r a)
    rw [Matrix.mul_apply, sum_Es (M := ℂ) (fun l => n (esI k r b) l * n⁻¹ l (esI k r a))
      (fun l hl => by rw [n_rowEs hn _ l (by simp [esI]; omega) hl, zero_mul])] at e
    rw [e, Matrix.one_apply, Matrix.one_apply]
    simp only [(esI_inj (k := k)).eq_iff]
  rw [Matrix.inv_eq_left_inv hNL]
  rfl

end main

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU

variable {k r : ℕ}

def Pm (y : Mat k r) : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := cE y * (Zm y)⁻¹

/- English proof (translation)
Establish `e` using `congrFun (congrFun (Matrix.mul_nonsing_inv (Zm y) hy) a') a`. Rewrite `e` using `[Matrix.one_apply]`. Rewrite using `[← e]`. Simplify using `only [Pm, Matrix.mul_apply, cE, Zm, Matrix.of_apply]`.
-/
lemma Pm_Es (y : Mat k r) (hy : IsUnit (Zm y).det) (a' a : Fin r) :
    Pm y (esI k r a') a = if a' = a then 1 else 0 := by
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv (Zm y) hy) a') a
  rw [Matrix.one_apply] at e
  rw [← e]
  simp only [Pm, Matrix.mul_apply, cE, Zm, Matrix.of_apply]

/- English proof (translation)
The claim follows from `isUnit_iff_ne_zero.2 fun h' => by rw [h', norm_zero] at h; linarith`.
-/
lemma unit_of_det {δ : ℝ} (hδ : 0 < δ) {A : Matrix (Fin r) (Fin r) ℂ} (h : δ ≤ ‖A.det‖) : IsUnit A.det :=
  isUnit_iff_ne_zero.2 fun h' => by rw [h', norm_zero] at h; linarith

/- English proof (translation)
Establish `hU1 : Um n' * (Um n')⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (by rw [det_Um hn']; exact isUnit_one)`. Establish `hL1 : (Lm n)⁻¹ * Lm n = 1` using `Matrix.nonsing_inv_mul _ (by rw [det_Lm hn]; exact isUnit_one)`. Rewrite using `[Pm, Pm, cE_mul hn hn' g, Zm_mul hn hn' g, Matrix.mul_inv_rev, Matrix.mul_inv_rev]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hL1, Matrix.mul_one, ← Matrix.mul_assoc (Um n') _ _, hU1, Matrix.one_mul]`.
-/
lemma key {δ : ℝ} {g n n' : Mat k r} (_hδ : 0 < δ) (_hdet : δ ≤ ‖(Zm g).det‖)
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    n⁻¹ * Pm g = Pm (n⁻¹ * g * n') * Lm n := by
  have hU1 : Um n' * (Um n')⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [det_Um hn']; exact isUnit_one)
  have hL1 : (Lm n)⁻¹ * Lm n = 1 := Matrix.nonsing_inv_mul _ (by rw [det_Lm hn]; exact isUnit_one)
  rw [Pm, Pm, cE_mul hn hn' g, Zm_mul hn hn' g, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [hL1, Matrix.mul_one, ← Matrix.mul_assoc (Um n') _ _, hU1, Matrix.one_mul]

section main
variable {Γ δ : ℝ} {g n n' : Mat k r}

/- English proof (translation)
Apply the tactic sequence `have h := norm_mul_entry (cE (n⁻¹ * g * n')) (Zm (n⁻¹ * g * n'))⁻¹ _ _ (gN_nonneg _) (fun i b => by simp only [cE, Matrix.of_apply]; exact ent_le _ _ _) (Zxinv_bd hδ hg hdet hn hn') i a`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [Fintype.card_fin, c8]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma Pmx_bd (hδ : 0 < δ) (hg : g ∈ GV k r) (hdet : δ ≤ ‖(Zm g).det‖)
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (i : Fin (2 * r + k + 1)) (a : Fin r) :
    ‖Pm (n⁻¹ * g * n') i a‖ ≤ c8 r δ * gN (n⁻¹ * g * n') ^ (r + 1) := by
  have h := norm_mul_entry (cE (n⁻¹ * g * n')) (Zm (n⁻¹ * g * n'))⁻¹ _ _ (gN_nonneg _)
    (fun i b => by simp only [cE, Matrix.of_apply]; exact ent_le _ _ _) (Zxinv_bd hδ hg hdet hn hn') i a
  refine h.trans (le_of_eq ?_)
  simp only [Fintype.card_fin, c8]; ring

/- English proof (translation)
Establish `hinv : ∀ a b, ‖(Zm g)⁻¹ a b‖ ≤ cZi r δ * Γ ^ r` using `fun a b => by`. Use `norm_inv_le (Zm g) Γ δ hΓ hδ (fun a b => (Zm_ent g a b).trans hgΓ) hdet a b` as an intermediate fact. Simplify `this` using `[cZi, div_mul_eq_mul_div]`. Apply the tactic sequence `have h := norm_mul_entry (cE g) (Zm g)⁻¹ Γ (cZi r δ * Γ ^ r) (by linarith) (fun i b => by simp only [cE, Matrix.of_apply]; exact (ent_le g _ _).trans hgΓ) hinv i a`. Rewrite using `[Pm]`.

Simplify `h` using `[cPg]`.
-/
lemma Pmg_bd (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hgΓ : gN g ≤ Γ) (hdet : δ ≤ ‖(Zm g).det‖)
    (i : Fin (2 * r + k + 1)) (a : Fin r) : ‖Pm g i a‖ ≤ cPg r Γ δ := by
  have hinv : ∀ a b, ‖(Zm g)⁻¹ a b‖ ≤ cZi r δ * Γ ^ r := fun a b => by
    have := norm_inv_le (Zm g) Γ δ hΓ hδ (fun a b => (Zm_ent g a b).trans hgΓ) hdet a b
    simpa [cZi, div_mul_eq_mul_div] using this
  have h := norm_mul_entry (cE g) (Zm g)⁻¹ Γ (cZi r δ * Γ ^ r) (by linarith)
    (fun i b => by simp only [cE, Matrix.of_apply]; exact (ent_le g _ _).trans hgΓ) hinv i a
  rw [Pm]; simpa [cPg] using h

/- English proof (translation)
Apply the tactic sequence `have h := norm_mul_entry _ _ _ _ (by have := orbit_constant_eight_nonneg (r := r) hΓ hδ; have := gN_nonneg (n⁻¹ * g * n'); positivity) (Pmx_bd hδ hg hdet hn hn') (Lm_bd hΓ hδ hg hgΓ hld hn hn') i a`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [Fintype.card_fin, c9]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma Q_bd (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (i : Fin (2 * r + k + 1)) (a : Fin r) :
    ‖(Pm (n⁻¹ * g * n') * Lm n) i a‖ ≤ c9 r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  have h := norm_mul_entry _ _ _ _ (by have := orbit_constant_eight_nonneg (r := r) hΓ hδ; have := gN_nonneg (n⁻¹ * g * n'); positivity)
    (Pmx_bd hδ hg hdet hn hn') (Lm_bd hΓ hδ hg hgΓ hld hn hn') i a
  refine h.trans (le_of_eq ?_)
  simp only [Fintype.card_fin, c9]; ring

/- English proof (translation)
Use `set Q := Pm (n⁻¹ * g * n') * Lm n with hQ`. Use `set Rm : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := Matrix.of fun i a => n i (esI k r a)`. Establish `hu : IsUnit n.det` using `closedN.unit n hn`. Establish `hPg : Pm g = n * Q`. Rewrite using `[hQ, ← key hδ hdet hn hn', ← Matrix.mul_assoc, Matrix.mul_nonsing_inv n hu, Matrix.one_mul]`.

Establish `hx : IsUnit (Zm (n⁻¹ * g * n')).det` using `by rw [det_Zx hn hn']; exact unit_of_det hδ hdet`. Establish `hrow : ∀ c, Pm g j c = Q j c + (Rm * Lm n) j c`. Introduce `c`. Rewrite using `[hPg, Matrix.mul_apply, sum_split_Es]`. Use `congr 1`.

Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[if_pos hj2, n_rowM hn j j hj1 hj2, if_pos rfl, one_mul]`. Introduce `l _ hlj split_ifs with hl`. Rewrite using `[n_rowM hn j l hj1 hl, if_neg (Ne.symm hlj), zero_mul]`. Both sides reduce to the same expression.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Simplify using `only [Matrix.mul_apply, Rm, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun a' _ => ?_` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[hQ, Matrix.mul_apply]`. Simplify using `only [Pm_Es _ hx, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `hLL : Lm n * (Lm n)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (by rw [det_Lm hn]; exact isUnit_one)`. Establish `e1 : (Pm g * (Lm n)⁻¹) j a = (Q * (Lm n)⁻¹) j a + (Rm * Lm n * (Lm n)⁻¹) j a`. Simplify using `only [Matrix.mul_apply (M := Pm g), hrow, add_mul, Finset.sum_add_distrib]`.

Both sides reduce to the same expression. Rewrite using `[e1, hQ, Matrix.mul_assoc (Pm (n⁻¹ * g * n')) (Lm n), hLL, Matrix.mul_one, Matrix.mul_assoc Rm (Lm n), hLL, Matrix.mul_one]`. Simplify using `[Rm]`.
-/
lemma rowM_eq (hδ : 0 < δ) (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) (a : Fin r) :
    n j (esI k r a) = (Pm g * (Lm n)⁻¹) j a - Pm (n⁻¹ * g * n') j a := by
  set Q := Pm (n⁻¹ * g * n') * Lm n with hQ
  set Rm : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := Matrix.of fun i a => n i (esI k r a)
  have hu : IsUnit n.det := closedN.unit n hn
  have hPg : Pm g = n * Q := by
    rw [hQ, ← key hδ hdet hn hn', ← Matrix.mul_assoc, Matrix.mul_nonsing_inv n hu, Matrix.one_mul]
  have hx : IsUnit (Zm (n⁻¹ * g * n')).det := by rw [det_Zx hn hn']; exact unit_of_det hδ hdet
  have hrow : ∀ c, Pm g j c = Q j c + (Rm * Lm n) j c := by
    intro c
    rw [hPg, Matrix.mul_apply, sum_split_Es]
    congr 1
    · rw [Finset.sum_eq_single j]
      · rw [if_pos hj2, n_rowM hn j j hj1 hj2, if_pos rfl, one_mul]
      · intro l _ hlj
        split_ifs with hl
        · rw [n_rowM hn j l hj1 hl, if_neg (Ne.symm hlj), zero_mul]
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [Matrix.mul_apply, Rm, Matrix.of_apply]
      refine Finset.sum_congr rfl fun a' _ => ?_
      congr 1
      rw [hQ, Matrix.mul_apply]
      simp only [Pm_Es _ hx, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hLL : Lm n * (Lm n)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [det_Lm hn]; exact isUnit_one)
  have e1 : (Pm g * (Lm n)⁻¹) j a = (Q * (Lm n)⁻¹) j a + (Rm * Lm n * (Lm n)⁻¹) j a := by
    simp only [Matrix.mul_apply (M := Pm g), hrow, add_mul, Finset.sum_add_distrib]
    rfl
  rw [e1, hQ, Matrix.mul_assoc (Pm (n⁻¹ * g * n')) (Lm n), hLL, Matrix.mul_one,
    Matrix.mul_assoc Rm (Lm n), hLL, Matrix.mul_one]
  simp [Rm]

/- English proof (translation)
Use `set X := gN (n⁻¹ * g * n')`. Establish `hX : 1 ≤ X` using `one_le_X hg hn hn'`. Rewrite using `[rowM_eq hδ hdet hn hn' j hj1 hj2 a]`. Apply the tactic sequence `have h1 := norm_mul_entry (Pm g) (Lm n)⁻¹ _ _ (cPg_nn hΓ hδ) (Pmg_bd hΓ hδ hgΓ hdet) (Linv_bd hΓ hδ hg hgΓ hld hdet hn hn') j a`. Establish `h2` using `Pmx_bd hδ hg hdet hn hn' j a`.

Establish `p1 : X ^ (2 * r) ≤ X ^ (2 * r + 1)` using `pow_mono hX (by omega)`. Establish `p2 : X ^ (r + 1) ≤ X ^ (2 * r + 1)` using `pow_mono hX (by omega)`. Use `orbit_constant_five_nonneg (r := r) hΓ hδ` as an intermediate fact. Use `cPg_nn (r := r) hΓ hδ` as an intermediate fact. Use `orbit_constant_eight_nonneg (r := r) hΓ hδ` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Simplify using `using add_le_add h1 h2`. Use `_ ≤ (r : ℝ) * (cPg r Γ δ * (c5 r Γ δ * X ^ (2 * r + 1))) + c8 r δ * X ^ (2 * r + 1) := by gcongr`. Use `_ = c10 r Γ δ * X ^ (2 * r + 1) := by unfold c10; ring`.
-/
lemma rowM_bd (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) (a : Fin r) :
    ‖n j (esI k r a)‖ ≤ c10 r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  set X := gN (n⁻¹ * g * n')
  have hX : 1 ≤ X := one_le_X hg hn hn'
  rw [rowM_eq hδ hdet hn hn' j hj1 hj2 a]
  have h1 := norm_mul_entry (Pm g) (Lm n)⁻¹ _ _ (cPg_nn hΓ hδ) (Pmg_bd hΓ hδ hgΓ hdet)
    (Linv_bd hΓ hδ hg hgΓ hld hdet hn hn') j a
  have h2 := Pmx_bd hδ hg hdet hn hn' j a
  have p1 : X ^ (2 * r) ≤ X ^ (2 * r + 1) := pow_mono hX (by omega)
  have p2 : X ^ (r + 1) ≤ X ^ (2 * r + 1) := pow_mono hX (by omega)
  have := orbit_constant_five_nonneg (r := r) hΓ hδ; have := cPg_nn (r := r) hΓ hδ; have := orbit_constant_eight_nonneg (r := r) hΓ hδ
  calc ‖(Pm g * (Lm n)⁻¹) j a - Pm (n⁻¹ * g * n') j a‖
      ≤ ‖(Pm g * (Lm n)⁻¹) j a‖ + ‖Pm (n⁻¹ * g * n') j a‖ := norm_sub_le _ _
    _ ≤ (r : ℝ) * (cPg r Γ δ * (c5 r Γ δ * X ^ (2 * r))) + c8 r δ * X ^ (r + 1) := by
        simpa using add_le_add h1 h2
    _ ≤ (r : ℝ) * (cPg r Γ δ * (c5 r Γ δ * X ^ (2 * r + 1))) + c8 r δ * X ^ (2 * r + 1) := by gcongr
    _ = c10 r Γ δ * X ^ (2 * r + 1) := by unfold c10; ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨2 * r + k - m.val, by omega⟩, Fin.ext (by simp [esI]; omega)⟩`.
-/
lemma Es_of_gt (m : Fin (2 * r + k + 1)) (h : r + k < m.val) : ∃ a : Fin r, m = esI k r a :=
  ⟨⟨2 * r + k - m.val, by omega⟩, Fin.ext (by simp [esI]; omega)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨m.val, h⟩, Fin.ext rfl⟩`.
-/
lemma E_of_lt (m : Fin (2 * r + k + 1)) (h : m.val < r) : ∃ a : Fin r, m = eI k r a :=
  ⟨⟨m.val, h⟩, Fin.ext rfl⟩

/- English proof (translation)
Unfold `sg; rw [if_neg (by omega)]`.
-/
lemma sg_M (m : Fin (2 * r + k + 1)) (h1 : r ≤ m.val) (h2 : m.val ≤ r + k) : sg k r m = m := by
  unfold sg; rw [if_neg (by omega)]

/- English proof (translation)
Use `set X := gN (n⁻¹ * g * n')`. Establish `hX : 1 ≤ X` using `one_le_X hg hn hn'`. Establish `hXp : 1 ≤ X ^ (2 * r + 1)` using `one_le_pow₀ hX`. Use `orbit_constant_five_nonneg (r := r) hΓ hδ` as an intermediate fact. Use `orbit_constant_ten_nonneg (r := r) hΓ hδ` as an intermediate fact.

Establish `hc : c11 r Γ δ * X ^ (2 * r + 1) = X ^ (2 * r + 1) + c5 r Γ δ * X ^ (2 * r + 1) + c10 r Γ δ * X ^ (2 * r + 1)` using `by unfold c11; ring`. Rewrite using `[norm_inv_apply (n_mem_G hn), hc]`. Establish `hc5 : c5 r Γ δ * X ^ (2 * r) ≤ c5 r Γ δ * X ^ (2 * r + 1)` using `mul_le_mul_of_nonneg_left (pow_mono hX (by omega)) (orbit_constant_five_nonneg hΓ hδ)`. Establish `nn1 : 0 ≤ c5 r Γ δ * X ^ (2 * r + 1)` using `by positivity`. Establish `nn2 : 0 ≤ c10 r Γ δ * X ^ (2 * r + 1)` using `by positivity`.

Distinguish the cases in `hlE : l.val < r`. Take `⟨b, rfl⟩` from `E_of_lt l hlE`. Rewrite using `[sg_eI]`. Distinguish the cases in `hi : (sg k r i).val ≤ r + k`. Rewrite using `[n_rowEs hn _ _ (by simp [esI]; omega) hi, norm_zero]; positivity`.

Take `⟨a', ha'⟩` from `Es_of_gt (sg k r i) (by omega)`. Rewrite using `[ha', Nstar hn]`. Use `Linv_bd hΓ hδ hg hgΓ hld hdet hn hn' b a'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[sg_M l (by omega) hl]`.

Distinguish the cases in `hi : (sg k r i).val ≤ r + k`. Apply the tactic sequence `rw [n_rowM hn l _ (by omega) hi] split_ifs <;> simp <;> linarith`. Take `⟨a', ha'⟩` from `Es_of_gt (sg k r i) (by omega)`. Rewrite using `[ha']`. Use `rowM_bd hΓ hδ hg hgΓ hld hdet hn hn' l (by omega) hl a'` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma ninv_EM_bd (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (i l : Fin (2 * r + k + 1)) (hl : l.val ≤ r + k) :
    ‖n⁻¹ i l‖ ≤ c11 r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  set X := gN (n⁻¹ * g * n')
  have hX : 1 ≤ X := one_le_X hg hn hn'
  have hXp : 1 ≤ X ^ (2 * r + 1) := one_le_pow₀ hX
  have := orbit_constant_five_nonneg (r := r) hΓ hδ; have := orbit_constant_ten_nonneg (r := r) hΓ hδ
  have hc : c11 r Γ δ * X ^ (2 * r + 1) = X ^ (2 * r + 1) + c5 r Γ δ * X ^ (2 * r + 1) +
      c10 r Γ δ * X ^ (2 * r + 1) := by unfold c11; ring
  rw [norm_inv_apply (n_mem_G hn), hc]
  have hc5 : c5 r Γ δ * X ^ (2 * r) ≤ c5 r Γ δ * X ^ (2 * r + 1) :=
    mul_le_mul_of_nonneg_left (pow_mono hX (by omega)) (orbit_constant_five_nonneg hΓ hδ)
  have nn1 : 0 ≤ c5 r Γ δ * X ^ (2 * r + 1) := by positivity
  have nn2 : 0 ≤ c10 r Γ δ * X ^ (2 * r + 1) := by positivity
  by_cases hlE : l.val < r
  · obtain ⟨b, rfl⟩ := E_of_lt l hlE
    rw [sg_eI]
    by_cases hi : (sg k r i).val ≤ r + k
    · rw [n_rowEs hn _ _ (by simp [esI]; omega) hi, norm_zero]; positivity
    · obtain ⟨a', ha'⟩ := Es_of_gt (sg k r i) (by omega)
      rw [ha', Nstar hn]
      have := Linv_bd hΓ hδ hg hgΓ hld hdet hn hn' b a'
      linarith
  · rw [sg_M l (by omega) hl]
    by_cases hi : (sg k r i).val ≤ r + k
    · rw [n_rowM hn l _ (by omega) hi]
      split_ifs <;> simp <;> linarith
    · obtain ⟨a', ha'⟩ := Es_of_gt (sg k r i) (by omega)
      rw [ha']
      have := rowM_bd hΓ hδ hg hgΓ hld hdet hn hn' l (by omega) hl a'
      linarith

/- English proof (translation)
Use `set X := gN (n⁻¹ * g * n')`. Establish `hX : 1 ≤ X` using `one_le_X hg hn hn'`. Use `orbit_constant_nine_nonneg (r := r) hΓ hδ` as an intermediate fact. Use `orbit_constant_eleven_ge_one (r := r) hΓ hδ` as an intermediate fact. Use `cPg_nn (r := r) hΓ hδ` as an intermediate fact.

Establish `hXp : 0 ≤ X ^ (2 * r + 1)` using `by positivity`. Distinguish the cases in `hl : l.val ≤ r + k`. Establish `h` using `ninv_EM_bd hΓ hδ hg hgΓ hld hdet hn hn' i l hl`. Use `h.trans ?_` and prove the remaining obligations. Unfold `c13`.

Establish `: 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (c11 r Γ δ * cPg r Γ δ)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨a, rfl⟩` from `Es_of_gt l (by omega)`. Establish `hx : IsUnit (Zm (n⁻¹ * g * n')).det` using `by rw [det_Zx hn hn']; exact unit_of_det hδ hdet`. Establish `hk` using `congrFun (congrFun (key hδ hdet hn hn') i) a`.

Rewrite `hk` using `[Matrix.mul_apply, sum_split_Es]`. Simplify using `only [Pm_Es g (unit_of_det hδ hdet), mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hk`. Establish `e : n⁻¹ i (esI k r a) = (Pm (n⁻¹ * g * n') * Lm n) i a - ∑ l, (if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0)` using `by rw [← hk]; ring`. Rewrite using `[e]`. Establish `h1` using `Q_bd hΓ hδ hg hgΓ hld hdet hn hn' i a`.

Establish `h2 : ‖∑ l, (if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0)‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (c11 r Γ δ * X ^ (2 * r + 1) * cPg r Γ δ)`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `: ∀ l ∈ Finset.univ, ‖(if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0)‖ ≤ c11 r Γ δ * X ^ (2 * r + 1) * cPg r Γ δ`. Introduce `l _`. Use `split_ifs with hl'`.

Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (ninv_EM_bd hΓ hδ hg hgΓ hld hdet hn hn' i l hl') (Pmg_bd hΓ hδ hgΓ hdet l a) (norm_nonneg _) (by positivity)`. Simplify using the standard rewrite rules. Check the signs of the components of the expression. Use `(Finset.sum_le_card_nsmul _ _ _ this).trans ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Unfold `c13`. Establish `: 0 ≤ c11 r Γ δ * X ^ (2 * r + 1)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma ninv_bd (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (i l : Fin (2 * r + k + 1)) : ‖n⁻¹ i l‖ ≤ c13 k r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  set X := gN (n⁻¹ * g * n')
  have hX : 1 ≤ X := one_le_X hg hn hn'
  have := orbit_constant_nine_nonneg (r := r) hΓ hδ; have := orbit_constant_eleven_ge_one (r := r) hΓ hδ; have := cPg_nn (r := r) hΓ hδ
  have hXp : 0 ≤ X ^ (2 * r + 1) := by positivity
  by_cases hl : l.val ≤ r + k
  · have h := ninv_EM_bd hΓ hδ hg hgΓ hld hdet hn hn' i l hl
    refine h.trans ?_
    unfold c13
    have : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (c11 r Γ δ * cPg r Γ δ) := by positivity
    nlinarith
  · obtain ⟨a, rfl⟩ := Es_of_gt l (by omega)
    have hx : IsUnit (Zm (n⁻¹ * g * n')).det := by rw [det_Zx hn hn']; exact unit_of_det hδ hdet
    have hk := congrFun (congrFun (key hδ hdet hn hn') i) a
    rw [Matrix.mul_apply, sum_split_Es] at hk
    simp only [Pm_Es g (unit_of_det hδ hdet), mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hk
    have e : n⁻¹ i (esI k r a) = (Pm (n⁻¹ * g * n') * Lm n) i a -
        ∑ l, (if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0) := by rw [← hk]; ring
    rw [e]
    have h1 := Q_bd hΓ hδ hg hgΓ hld hdet hn hn' i a
    have h2 : ‖∑ l, (if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0)‖ ≤
        ((2 * r + k + 1 : ℕ) : ℝ) * (c11 r Γ δ * X ^ (2 * r + 1) * cPg r Γ δ) := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ l ∈ Finset.univ, ‖(if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0)‖ ≤
          c11 r Γ δ * X ^ (2 * r + 1) * cPg r Γ δ := by
        intro l _
        split_ifs with hl'
        · rw [norm_mul]
          exact mul_le_mul (ninv_EM_bd hΓ hδ hg hgΓ hld hdet hn hn' i l hl') (Pmg_bd hΓ hδ hgΓ hdet l a)
            (norm_nonneg _) (by positivity)
        · simp; positivity
      refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
      simp
    calc ‖(Pm (n⁻¹ * g * n') * Lm n) i a - ∑ l, (if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0)‖
        ≤ ‖(Pm (n⁻¹ * g * n') * Lm n) i a‖ + ‖∑ l, (if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0)‖ :=
          norm_sub_le _ _
      _ ≤ c9 r Γ δ * X ^ (2 * r + 1) + ((2 * r + k + 1 : ℕ) : ℝ) * (c11 r Γ δ * X ^ (2 * r + 1) * cPg r Γ δ) :=
          add_le_add h1 h2
      _ ≤ c13 k r Γ δ * X ^ (2 * r + 1) := by
          unfold c13
          have : 0 ≤ c11 r Γ δ * X ^ (2 * r + 1) := by positivity
          nlinarith

/- English proof (translation)
Establish `hinvG : n⁻¹ ∈ GV k r` using `n_mem_G (n_inv_mem hn)`. Establish `hnn : n = (n⁻¹)⁻¹` using `(Matrix.nonsing_inv_nonsing_inv n (closedN.unit n hn)).symm`. Establish `hX : 0 ≤ gN (n⁻¹ * g * n') ^ (2 * r + 1)` using `by have := gN_nonneg (n⁻¹ * g * n'); positivity`. Use `orbit_constant_thirteen_nonneg (k := k) (r := r) hΓ hδ` as an intermediate fact. Establish `h` using `gN_le_of_ent n (c13 k r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1)) (by positivity) (fun i j => by conv_lhs => rw [hnn]`.

Rewrite using `[norm_inv_apply hinvG]`. Conclude with `ninv_bd hΓ hδ hg hgΓ hld hdet hn hn' _ _)`. Rewrite using `[mul_assoc]`. Conclude with `h`.
-/
lemma gN_n_bd (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    gN n ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c13 k r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  have hinvG : n⁻¹ ∈ GV k r := n_mem_G (n_inv_mem hn)
  have hnn : n = (n⁻¹)⁻¹ := (Matrix.nonsing_inv_nonsing_inv n (closedN.unit n hn)).symm
  have hX : 0 ≤ gN (n⁻¹ * g * n') ^ (2 * r + 1) := by have := gN_nonneg (n⁻¹ * g * n'); positivity
  have := orbit_constant_thirteen_nonneg (k := k) (r := r) hΓ hδ
  have h := gN_le_of_ent n (c13 k r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1)) (by positivity) (fun i j => by
    conv_lhs => rw [hnn]
    rw [norm_inv_apply hinvG]
    exact ninv_bd hΓ hδ hg hgΓ hld hdet hn hn' _ _)
  rw [mul_assoc]; exact h

end main

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU

variable {k r : ℕ}

def sgE (k r : ℕ) : Equiv.Perm (Fin (2 * r + k + 1)) := Function.Involutive.toPerm (sg k r) sg_sg

/- English proof (translation)
Unfold `gN`. Use `congr 1`. Establish `h1 : ∀ i j, Complex.normSq (y⁻¹ i j) = Complex.normSq (y (sg k r j) (sg k r i))`. Introduce `i j`. Rewrite using `[Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, norm_inv_apply hy]`.

Simplify using `only [h1]`. Rewrite using `[Finset.sum_comm]`. Use `Fintype.sum_equiv (sgE k r) _ _ fun j => ?_` and prove the remaining obligations. Use `Fintype.sum_equiv (sgE k r) _ _ fun i => ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
lemma gN_inv {y : Mat k r} (hy : y ∈ GV k r) : gN y⁻¹ = gN y := by
  unfold gN
  congr 1
  have h1 : ∀ i j, Complex.normSq (y⁻¹ i j) = Complex.normSq (y (sg k r j) (sg k r i)) := by
    intro i j; rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, norm_inv_apply hy]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Fintype.sum_equiv (sgE k r) _ _ fun j => ?_
  refine Fintype.sum_equiv (sgE k r) _ _ fun i => ?_
  rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Zm, Matrix.of_apply, Matrix.conjTranspose_apply]`. Rewrite using `[inv_apply hg, sg_eI, sg_esI, ep_esI, ep_eI, one_mul, mul_one]`.
-/
lemma Zm_inv {g : Mat k r} (hg : g ∈ GV k r) : Zm g⁻¹ = (Zm g)ᴴ := by
  ext a b
  simp only [Zm, Matrix.of_apply, Matrix.conjTranspose_apply]
  rw [inv_apply hg, sg_eI, sg_esI, ep_esI, ep_eI, one_mul, mul_one]

/- English proof (translation)
Unfold `ld mn`. Rewrite using `[rs_self]`. Rewrite using `[show Yᴴ.submatrix (cs b) (cs b) = (Y.submatrix (cs b) (cs b))ᴴ from rfl, Matrix.det_conjTranspose, norm_star]`.
-/
lemma ld_conjT (Y : Matrix (Fin r) (Fin r) ℂ) (b : Fin r) : ‖ld Yᴴ b‖ = ‖ld Y b‖ := by
  unfold ld mn
  rw [rs_self]
  rw [show Yᴴ.submatrix (cs b) (cs b) = (Y.submatrix (cs b) (cs b))ᴴ from rfl, Matrix.det_conjTranspose,
    norm_star]

/- English proof (translation)
Rewrite using `[Matrix.det_conjTranspose, norm_star]`.
-/
lemma det_conjT (Y : Matrix (Fin r) (Fin r) ℂ) : ‖Yᴴ.det‖ = ‖Y.det‖ := by
  rw [Matrix.det_conjTranspose, norm_star]

/- English proof (translation)
Rewrite using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]`.
-/
lemma xinv_eq {g n n' : Mat k r} (_hn : n ∈ Nset k r) (_hn' : n' ∈ Nset k r) :
    (n⁻¹ * g * n')⁻¹ = n'⁻¹ * g⁻¹ * (n⁻¹)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]

/- English proof (translation)
Use `⟨gN_n_bd hΓ hδ hg hgΓ hld hdet hn hn', ?_⟩` and prove the remaining obligations. Establish `hgi : g⁻¹ ∈ GV k r` using `Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg`. Establish `h` using `gN_n_bd (g := g⁻¹) (n := n') (n' := n) hΓ hδ hgi (by rw [gN_inv hg]; exact hgΓ) (fun b => by rw [Zm_inv hg, ld_conjT]; exact hld b) (by rw [Zm_inv hg, det_conjT]; exact hdet) hn' hn`. Establish `hnn : (n⁻¹)⁻¹ = n` using `Matrix.nonsing_inv_nonsing_inv n (closedN.unit n hn)`. Establish `e : n'⁻¹ * g⁻¹ * n = (n⁻¹ * g * n')⁻¹` using `by rw [xinv_eq hn hn', hnn]`.

Rewrite `h` using `[e, gN_inv (x_mem hg hn hn')]`. Conclude with `h`.
-/
lemma both_bd {Γ δ : ℝ} {g n n' : Mat k r} (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ)
    (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖) (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    gN n ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c13 k r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) ∧
    gN n' ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c13 k r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  refine ⟨gN_n_bd hΓ hδ hg hgΓ hld hdet hn hn', ?_⟩
  have hgi : g⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg
  have h := gN_n_bd (g := g⁻¹) (n := n') (n' := n) hΓ hδ hgi (by rw [gN_inv hg]; exact hgΓ)
    (fun b => by rw [Zm_inv hg, ld_conjT]; exact hld b) (by rw [Zm_inv hg, det_conjT]; exact hdet) hn' hn
  have hnn : (n⁻¹)⁻¹ = n := Matrix.nonsing_inv_nonsing_inv n (closedN.unit n hn)
  have e : n'⁻¹ * g⁻¹ * n = (n⁻¹ * g * n')⁻¹ := by rw [xinv_eq hn hn', hnn]
  rw [e, gN_inv (x_mem hg hn hn')] at h
  exact h

/- English proof (translation)
Simplify using `[bvec, dotProduct, Pi.single_apply]`.
-/
lemma dot_bvec (e : Fin (2 * r + k + 1)) (v : Fin (2 * r + k + 1) → ℂ) : star (bvec e) ⬝ᵥ v = v e := by
  simp [bvec, dotProduct, Pi.single_apply]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
lemma hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (e : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) e = ep k r e * v (sg k r e) := by
  simp only [Matrix.mulVec, dotProduct, hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/- English proof (translation)
Unfold `bvec`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
lemma mulVec_bvec (g : Mat k r) (e : Fin (2 * r + k + 1)) : g *ᵥ bvec e = fun i => g i e := by
  unfold bvec; ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Simplify using `only [Zhat, fvec, dif_pos ha, dif_pos hb, herm]`. Rewrite using `[dot_bvec, hpk_mulVec, mulVec_bvec, sg_eI, ep_eI, one_mul]`. Both sides reduce to the same expression.
-/
lemma zhat_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) (a b : Fin (r + 1)) (ha : a.val < r) (hb : b.val < r) :
    Zhat k r z z' g a b = Zm g ⟨a.val, ha⟩ ⟨b.val, hb⟩ := by
  simp only [Zhat, fvec, dif_pos ha, dif_pos hb, herm]
  rw [dot_bvec, hpk_mulVec, mulVec_bvec, sg_eI, ep_eI, one_mul]
  rfl

/- English proof (translation)
Unfold `ld mn Dmin`. Rewrite using `[rs_self]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply]`.

Rewrite using `[zhat_eq z z' g _ _ (by simp; omega) (by simp; omega)]`. Both sides reduce to the same expression.
-/
lemma ld_eq_Dmin (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) (b : Fin r) :
    ld (Zm g) b = Dmin k r z z' g ⟨b.val + 1, by omega⟩ := by
  unfold ld mn Dmin
  rw [rs_self]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply]
  rw [zhat_eq z z' g _ _ (by simp; omega) (by simp; omega)]
  rfl

/- English proof (translation)
Unfold `Dmin`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply]`. Rewrite using `[zhat_eq z z' g _ _ (by simp) (by simp)]`.

Both sides reduce to the same expression.
-/
lemma det_eq_Dmin (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    (Zm g).det = Dmin k r z z' g ⟨r, by omega⟩ := by
  unfold Dmin
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply]
  rw [zhat_eq z z' g _ _ (by simp) (by simp)]
  rfl

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU

variable {k r : ℕ}

/- English proof (translation)
Unfold `gN`. Conclude with `Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))`.
-/
lemma continuous_gN : Continuous (fun g : Mat k r => gN g) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun c => ?_` and prove the remaining obligations. Use `show Continuous fun g : Mat k r => g (esI k r a) (eI k r c)`. Conclude with `(continuous_apply _).comp (continuous_apply _)`.
-/
lemma continuous_Zm : Continuous (fun g : Mat k r => Zm g) := by
  refine continuous_pi fun a => continuous_pi fun c => ?_
  show Continuous fun g : Mat k r => g (esI k r a) (eI k r c)
  exact (continuous_apply _).comp (continuous_apply _)

/- English proof (translation)
Unfold `ld mn`. Conclude with `(continuous_Zm.matrix_submatrix _ _).matrix_det`.
-/
lemma continuous_ld (b : Fin r) : Continuous (fun g : Mat k r => ld (Zm g) b) := by
  unfold ld mn
  exact (continuous_Zm.matrix_submatrix _ _).matrix_det

/- English proof (translation)
The claim follows from `continuous_Zm.matrix_det`.
-/
lemma continuous_detZ : Continuous (fun g : Mat k r => (Zm g).det) := continuous_Zm.matrix_det

/- English proof (translation)
Take `⟨M, hM⟩` from `(hK.image_of_continuousOn continuous_gN.continuousOn).bddAbove`. Establish `hΓ : 1 ≤ max 1 M` using `le_max_left _ _`. Establish `hDne : ∀ g ∈ K, ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0` using `fun g hg => (hKO hg).2.1`. Choose the witnesses or unpack the hypotheses as in `⟨δ1, hδ1, hδ1K⟩ : ∃ δ1 : ℝ, 0 < δ1 ∧ ∀ g ∈ K, ∀ b : Fin r, δ1 ≤ ‖ld (Zm g) b‖ := by`. Establish `hS : IsCompact (K ×ˢ (Set.univ : Set (Fin r)))` using `hK.prod isCompact_univ`.

Establish `hf : Continuous (fun p : Mat k r × Fin r => ‖ld (Zm p.1) p.2‖)` using `continuous_prod_of_discrete_right.2 fun b => (continuous_ld b).norm`. Distinguish the cases in `hne : (K ×ˢ (Set.univ : Set (Fin r))).Nonempty`. Take `⟨p0, hp0, hmin⟩` from `hS.exists_isMinOn hne hf.continuousOn`. Use `⟨‖ld (Zm p0.1) p0.2‖, ?_, fun g hg b => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_pos_iff, ld_eq_Dmin z z']`.

Conclude with `hDne p0.1 hp0.1 _ (by show p0.2.val + 1 ≤ r; have := p0.2.isLt; omega)`. Establish `hgb : (g, b) ∈ K ×ˢ (Set.univ : Set (Fin r))` using `⟨hg, Set.mem_univ _⟩`. Conclude with `isMinOn_iff.mp hmin (g, b) hgb`. Use `⟨1, one_pos, fun g hg b => absurd ⟨(g, b), hg, Set.mem_univ _⟩ hne⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨δ2, hδ2, hδ2K⟩ : ∃ δ2 : ℝ, 0 < δ2 ∧ ∀ g ∈ K, δ2 ≤ ‖(Zm g).det‖ := by`.

Distinguish the cases in `hne : K.Nonempty`. Take `⟨g0, hg0, hmin⟩` from `hK.exists_isMinOn hne continuous_detZ.norm.continuousOn`. Use `⟨‖(Zm g0).det‖, ?_, fun g hg => isMinOn_iff.mp hmin g hg⟩` and prove the remaining obligations. Rewrite using `[norm_pos_iff, det_eq_Dmin z z']`. Conclude with `hDne g0 hg0 _ (by show r ≤ r; exact le_rfl)`.

Conclude with `⟨1, one_pos, fun g hg => absurd ⟨g, hg⟩ hne⟩`. Establish `hδ : 0 < min δ1 δ2` using `lt_min hδ1 hδ2`. Use `⟨((2 * r + k + 1 : ℕ) : ℝ) * c13 k r (max 1 M) (min δ1 δ2), by have := orbit_constant_thirteen_nonneg (k := k) (r := r) hΓ hδ; positivity, ?_⟩` and prove the remaining obligations. Introduce `g hg n hn n' hn'`. Establish `hgM : gN g ≤ max 1 M` using `(hM (Set.mem_image_of_mem _ hg)).trans (le_max_right _ _)`.

Conclude with `both_bd hΓ hδ (hKO hg).1 hgM (fun b => (min_le_left _ _).trans (hδ1K g hg b)) ((min_le_right _ _).trans (hδ2K g hg)) hn hn'`.
-/
theorem orbit (z z' : Fin (2 * r + k + 1) → ℂ) (K : Set (Mat k r)) (hK : IsCompact K)
    (hKO : K ⊆ Om k r z z') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      gN n ≤ C * gN (n⁻¹ * g * n') ^ (2 * r + 1) ∧ gN n' ≤ C * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn continuous_gN.continuousOn).bddAbove
  have hΓ : 1 ≤ max 1 M := le_max_left _ _
  have hDne : ∀ g ∈ K, ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0 := fun g hg => (hKO hg).2.1

  obtain ⟨δ1, hδ1, hδ1K⟩ : ∃ δ1 : ℝ, 0 < δ1 ∧ ∀ g ∈ K, ∀ b : Fin r, δ1 ≤ ‖ld (Zm g) b‖ := by
    have hS : IsCompact (K ×ˢ (Set.univ : Set (Fin r))) := hK.prod isCompact_univ
    have hf : Continuous (fun p : Mat k r × Fin r => ‖ld (Zm p.1) p.2‖) :=
      continuous_prod_of_discrete_right.2 fun b => (continuous_ld b).norm
    by_cases hne : (K ×ˢ (Set.univ : Set (Fin r))).Nonempty
    · obtain ⟨p0, hp0, hmin⟩ := hS.exists_isMinOn hne hf.continuousOn
      refine ⟨‖ld (Zm p0.1) p0.2‖, ?_, fun g hg b => ?_⟩
      · rw [norm_pos_iff, ld_eq_Dmin z z']
        exact hDne p0.1 hp0.1 _ (by show p0.2.val + 1 ≤ r; have := p0.2.isLt; omega)
      · have hgb : (g, b) ∈ K ×ˢ (Set.univ : Set (Fin r)) := ⟨hg, Set.mem_univ _⟩
        exact isMinOn_iff.mp hmin (g, b) hgb
    · refine ⟨1, one_pos, fun g hg b => absurd ⟨(g, b), hg, Set.mem_univ _⟩ hne⟩
  obtain ⟨δ2, hδ2, hδ2K⟩ : ∃ δ2 : ℝ, 0 < δ2 ∧ ∀ g ∈ K, δ2 ≤ ‖(Zm g).det‖ := by
    by_cases hne : K.Nonempty
    · obtain ⟨g0, hg0, hmin⟩ := hK.exists_isMinOn hne continuous_detZ.norm.continuousOn
      refine ⟨‖(Zm g0).det‖, ?_, fun g hg => isMinOn_iff.mp hmin g hg⟩
      rw [norm_pos_iff, det_eq_Dmin z z']
      exact hDne g0 hg0 _ (by show r ≤ r; exact le_rfl)
    · exact ⟨1, one_pos, fun g hg => absurd ⟨g, hg⟩ hne⟩
  have hδ : 0 < min δ1 δ2 := lt_min hδ1 hδ2
  refine ⟨((2 * r + k + 1 : ℕ) : ℝ) * c13 k r (max 1 M) (min δ1 δ2),
    by have := orbit_constant_thirteen_nonneg (k := k) (r := r) hΓ hδ; positivity, ?_⟩
  intro g hg n hn n' hn'
  have hgM : gN g ≤ max 1 M := (hM (Set.mem_image_of_mem _ hg)).trans (le_max_right _ _)
  exact both_bd hΓ hδ (hKO hg).1 hgM
    (fun b => (min_le_left _ _).trans (hδ1K g hg b)) ((min_le_right _ _).trans (hδ2K g hg)) hn hn'

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb

open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x6

section pointwise

variable {k r' : ℕ}

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec]`. Use `congr 1`. Apply `vext` to reduce the goal to its premises. Rewrite using `[lev_mulVec_F]`. Rewrite using `[lev_mulVec_res, dual_base_vector_restriction_zero, Matrix.mulVec_zero]`.

Rewrite using `[lev_mulVec_L]`.
-/
lemma col_L (x : HPar k r') (n' : Mat k r') :
    (heis0 k r' x * ιLev k 1 r' n') *ᵥ es0 k r' = heis0 k r' x *ᵥ es0 k r' := by
  rw [← Matrix.mulVec_mulVec]
  congr 1
  apply vext
  · rw [lev_mulVec_F]
  · rw [lev_mulVec_res, dual_base_vector_restriction_zero, Matrix.mulVec_zero]
  · rw [lev_mulVec_L]

/- English proof (translation)
Rewrite using `[ent (heis0 k r' x * ιLev k 1 r' n') p (iL k r'), ← col_L x n']`. Both sides reduce to the same expression.
-/
lemma entry_L (x : HPar k r') (n' : Mat k r') (p : Fin (2 * (1 + r') + k + 1)) :
    (heis0 k r' x * ιLev k 1 r' n') p (iL k r') = (heis0 k r' x *ᵥ es0 k r') p := by
  rw [ent (heis0 k r' x * ιLev k 1 r' n') p (iL k r'), ← col_L x n']
  rfl

/- English proof (translation)
Rewrite using `[heis_L, dual_base_vector_last]`.
-/
lemma hcol_L (x : HPar k r') : (heis0 k r' x *ᵥ es0 k r') (iL k r') = 1 := by
  rw [heis_L, dual_base_vector_last]

/- English proof (translation)
Rewrite using `[heis_F, dual_base_vector_first_eq_zero, dual_base_vector_restriction_zero, dual_base_vector_last, herm_zero_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hcol_F (x : HPar k r') : (heis0 k r' x *ᵥ es0 k r') (iF k r') = hb k r' x.1 x.2 := by
  rw [heis_F, dual_base_vector_first_eq_zero, dual_base_vector_restriction_zero, dual_base_vector_last, herm_zero_left]
  ring

/- English proof (translation)
Rewrite using `[heis_res, dual_base_vector_restriction_zero, dual_base_vector_last, one_smul, zero_add]`.
-/
lemma hcol_res (x : HPar k r') : res (heis0 k r' x *ᵥ es0 k r') = x.1 := by
  rw [heis_res, dual_base_vector_restriction_zero, dual_base_vector_last, one_smul, zero_add]

/- English proof (translation)
Rewrite using `[ent (heis0 k r' x * ιLev k 1 r' n') (lv k r' i) (lv k r' j), ← Matrix.mulVec_mulVec]`. Establish `h1` using `congrFun (heis_res x (ιLev k 1 r' n' *ᵥ bvec (lv k r' j))) i`. Simplify using `only [res] at h1`. Rewrite using `[h1, Pi.add_apply, Pi.smul_apply, lev_mulVec_L]`. Establish `h3 : bvec (lv k r' j) (iL k r') = 0` using `Pi.single_eq_of_ne (lv_ne_iL j).symm _`.

Rewrite using `[h3, zero_smul, add_zero]`. Establish `h2' : res (ιLev k 1 r' n' *ᵥ bvec (lv k r' j)) = n' *ᵥ bvec j`. Rewrite using `[lev_mulVec_res, bvec_lv, lift_res]`. Rewrite using `[h2', ← ent]`.
-/
lemma entry_mm (x : HPar k r') (n' : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    (heis0 k r' x * ιLev k 1 r' n') (lv k r' i) (lv k r' j) = n' i j := by
  rw [ent (heis0 k r' x * ιLev k 1 r' n') (lv k r' i) (lv k r' j), ← Matrix.mulVec_mulVec]
  have h1 := congrFun (heis_res x (ιLev k 1 r' n' *ᵥ bvec (lv k r' j))) i
  simp only [res] at h1
  rw [h1, Pi.add_apply, Pi.smul_apply, lev_mulVec_L]
  have h3 : bvec (lv k r' j) (iL k r') = 0 := Pi.single_eq_of_ne (lv_ne_iL j).symm _
  rw [h3, zero_smul, add_zero]
  have h2' : res (ιLev k 1 r' n' *ᵥ bvec (lv k r' j)) = n' *ᵥ bvec j := by
    rw [lev_mulVec_res, bvec_lv, lift_res]
  rw [h2', ← ent]

/- English proof (translation)
Establish `hinj : Function.Injective (lv k r')` using `fun a b h => (lv_inj a b).1 h`. Establish `: ∑ j : Fin (2 * r' + k + 1), f (lv k r' j) = ∑ p ∈ Finset.univ.map ⟨lv k r', hinj⟩, f p`. Rewrite using `[Finset.sum_map]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hf p)`.
-/
lemma sum_lv_le (f : Fin (2 * (1 + r') + k + 1) → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∑ j : Fin (2 * r' + k + 1), f (lv k r' j) ≤ ∑ p, f p := by
  have hinj : Function.Injective (lv k r') := fun a b h => (lv_inj a b).1 h
  have : ∑ j : Fin (2 * r' + k + 1), f (lv k r' j) =
      ∑ p ∈ Finset.univ.map ⟨lv k r', hinj⟩, f p := by
    rw [Finset.sum_map]; rfl
  rw [this]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hf p)

/- English proof (translation)
Unfold `gN`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [entry_mm]`. Use `_ ≤ ∑ i, ∑ q, Complex.normSq ((heis0 k r' x * ιLev k 1 r' n') (lv k r' i) q) := by`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Conclude with `sum_lv_le (fun q => Complex.normSq ((heis0 k r' x * ιLev k 1 r' n') (lv k r' i) q)) (fun q => Complex.normSq_nonneg _)`. Use `_ ≤ ∑ p, ∑ q, Complex.normSq ((heis0 k r' x * ιLev k 1 r' n') p q) := sum_lv_le (fun p => ∑ q, Complex.normSq ((heis0 k r' x * ιLev k 1 r' n') p q)) (fun p => Finset.sum_nonneg (fun q _ => Complex.normSq_nonneg _))`.
-/
lemma gN_mid_le (x : HPar k r') (n' : Mat k r') : gN n' ≤ gN (heis0 k r' x * ιLev k 1 r' n') := by
  unfold gN
  apply Real.sqrt_le_sqrt
  calc ∑ i, ∑ j, Complex.normSq (n' i j)
      = ∑ i, ∑ j, Complex.normSq ((heis0 k r' x * ιLev k 1 r' n') (lv k r' i) (lv k r' j)) := by
        simp only [entry_mm]
    _ ≤ ∑ i, ∑ q, Complex.normSq ((heis0 k r' x * ιLev k 1 r' n') (lv k r' i) q) := by
        apply Finset.sum_le_sum; intro i _
        exact sum_lv_le (fun q => Complex.normSq ((heis0 k r' x * ιLev k 1 r' n') (lv k r' i) q))
          (fun q => Complex.normSq_nonneg _)
    _ ≤ ∑ p, ∑ q, Complex.normSq ((heis0 k r' x * ιLev k 1 r' n') p q) :=
        sum_lv_le (fun p => ∑ q, Complex.normSq ((heis0 k r' x * ιLev k 1 r' n') p q))
          (fun p => Finset.sum_nonneg (fun q _ => Complex.normSq_nonneg _))

/- English proof (translation)
Simplify using `[hb]`.
-/
lemma hb_im (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : (hb k r' y s).im = s := by
  simp [hb]

/- English proof (translation)
Establish `e1 : ‖(heis0 k r' x * ιLev k 1 r' n') (iL k r') (iL k r')‖ = 1`. Rewrite using `[entry_L, hcol_L, norm_one]`. Establish `h1 : (1 : ℝ) ≤ gN (heis0 k r' x * ιLev k 1 r' n')`. Use `Formalism.FourierDecayAlt.P.Ux6.entry_le_gN (heis0 k r' x * ιLev k 1 r' n') (iL k r') (iL k r')` as an intermediate fact. Rewrite `this` using `[e1]`. Then use the resulting hypothesis.

Establish `h0 : 0 ≤ gN (heis0 k r' x * ιLev k 1 r' n')` using `le_trans zero_le_one h1`. Establish `h2 : ‖x.1‖ ≤ gN (heis0 k r' x * ιLev k 1 r' n')`. Use `(pi_norm_le_iff_of_nonneg h0).2 fun i => ?_` and prove the remaining obligations. Use `Formalism.FourierDecayAlt.P.Ux6.entry_le_gN (heis0 k r' x * ιLev k 1 r' n') (lv k r' i) (iL k r')` as an intermediate fact. Establish `e : (heis0 k r' x * ιLev k 1 r' n') (lv k r' i) (iL k r') = x.1 i`.

Rewrite using `[entry_L]`. Establish `e` using `congrFun (hcol_res x) i`. Simplify using `only [res] at e`. Conclude with `e`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Establish `h3 : ‖x.2‖ ≤ gN (heis0 k r' x * ιLev k 1 r' n')`. Use `Formalism.FourierDecayAlt.P.Ux6.entry_le_gN (heis0 k r' x * ιLev k 1 r' n') (iF k r') (iL k r')` as an intermediate fact. Rewrite `this` using `[entry_L, hcol_F]`. Use `le_trans ?_ this` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hx : ‖x‖ = max ‖x.1‖ ‖x.2‖` using `Prod.norm_def x`. Rewrite using `[hx]`. Use `max_le h2 h3` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma gN_heis_le (x : HPar k r') (n' : Mat k r') :
    1 + ‖x‖ ≤ 2 * gN (heis0 k r' x * ιLev k 1 r' n') := by
  have e1 : ‖(heis0 k r' x * ιLev k 1 r' n') (iL k r') (iL k r')‖ = 1 := by
    rw [entry_L, hcol_L, norm_one]
  have h1 : (1 : ℝ) ≤ gN (heis0 k r' x * ιLev k 1 r' n') := by
    have := Formalism.FourierDecayAlt.P.Ux6.entry_le_gN (heis0 k r' x * ιLev k 1 r' n') (iL k r') (iL k r')
    rwa [e1] at this
  have h0 : 0 ≤ gN (heis0 k r' x * ιLev k 1 r' n') := le_trans zero_le_one h1
  have h2 : ‖x.1‖ ≤ gN (heis0 k r' x * ιLev k 1 r' n') := by
    refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
    have := Formalism.FourierDecayAlt.P.Ux6.entry_le_gN (heis0 k r' x * ιLev k 1 r' n') (lv k r' i) (iL k r')
    have e : (heis0 k r' x * ιLev k 1 r' n') (lv k r' i) (iL k r') = x.1 i := by
      rw [entry_L]
      have e := congrFun (hcol_res x) i
      simp only [res] at e
      exact e
    rwa [e] at this
  have h3 : ‖x.2‖ ≤ gN (heis0 k r' x * ιLev k 1 r' n') := by
    have := Formalism.FourierDecayAlt.P.Ux6.entry_le_gN (heis0 k r' x * ιLev k 1 r' n') (iF k r') (iL k r')
    rw [entry_L, hcol_F] at this
    refine le_trans ?_ this
    calc ‖x.2‖ = |(hb k r' x.1 x.2).im| := by rw [hb_im, Real.norm_eq_abs]
      _ ≤ ‖hb k r' x.1 x.2‖ := Complex.abs_im_le_norm _
  have hx : ‖x‖ = max ‖x.1‖ ‖x.2‖ := Prod.norm_def x
  rw [hx]
  have := max_le h2 h3
  linarith

/- English proof (translation)
Establish `hX : 0 < X` using `lt_of_lt_of_le hA hXA`. Establish `e : -a = -(θ * a) + -((1 - θ) * a)` using `by ring`. Rewrite using `[e, Real.rpow_add hX]`. Apply `mul_le_mul` to reduce the goal to its premises. Conclude with `Real.rpow_le_rpow_of_nonpos hA hXA (by nlinarith)`.

Conclude with `Real.rpow_le_rpow_of_nonpos hB hXB (by nlinarith)`. Conclude with `Real.rpow_nonneg hX.le _`. Conclude with `Real.rpow_nonneg hA.le _`.
-/
lemma rpow_split {X A B a θ : ℝ} (hA : 0 < A) (hB : 0 < B) (hXA : A ≤ X) (hXB : B ≤ X) (ha : 0 ≤ a)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : X ^ (-a) ≤ A ^ (-(θ * a)) * B ^ (-((1 - θ) * a)) := by
  have hX : 0 < X := lt_of_lt_of_le hA hXA
  have e : -a = -(θ * a) + -((1 - θ) * a) := by ring
  rw [e, Real.rpow_add hX]
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_nonpos hA hXA (by nlinarith)
  · exact Real.rpow_le_rpow_of_nonpos hB hXB (by nlinarith)
  · exact Real.rpow_nonneg hX.le _
  · exact Real.rpow_nonneg hA.le _

/- English proof (translation)
Simplify using `[HPar, Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma finrank_hpar (k r' : ℕ) : Module.finrank ℝ (HPar k r') = 2 * (2 * r' + k + 1) + 1 := by
  simp [HPar, Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex]
  ring

instance haar_hpar (k r' : ℕ) : (volume : Measure (HPar k r')).IsAddHaarMeasure := by
  have : (volume : Measure (Fin (2 * r' + k + 1) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.prod.instIsAddHaarMeasure _ _

/- English proof (translation)
Establish `hc0 : 0 < c` using `lt_of_le_of_lt (Nat.cast_nonneg _) hc`. Establish `e : ∀ x : HPar k r', ((1 + ‖x‖) / 2) ^ (-c) = (2 : ℝ) ^ c * (1 + ‖x‖) ^ (-c)`. Introduce `x`. Establish `hu : 0 ≤ 1 + ‖x‖` using `by positivity`. Rewrite using `[Real.div_rpow hu (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul, mul_comm]`.

Repeatedly rewrite using `[e]`. Repeatedly rewrite using `[ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) c)]`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_` and prove the remaining obligations. Apply `finite_integral_one_add_norm` to reduce the goal to its premises.

Rewrite using `[finrank_hpar]`. Conclude with `hc`.
-/
lemma lint_heis_fin (k r' : ℕ) {c : ℝ} (hc : ((2 * (2 * r' + k + 1) + 1 : ℕ) : ℝ) < c) :
    ∫⁻ x : HPar k r', ENNReal.ofReal (((1 + ‖x‖) / 2) ^ (-c)) < ⊤ := by
  have hc0 : 0 < c := lt_of_le_of_lt (Nat.cast_nonneg _) hc
  have e : ∀ x : HPar k r', ((1 + ‖x‖) / 2) ^ (-c) = (2 : ℝ) ^ c * (1 + ‖x‖) ^ (-c) := by
    intro x
    have hu : 0 ≤ 1 + ‖x‖ := by positivity
    rw [Real.div_rpow hu (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  simp_rw [e]
  simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) c)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  apply finite_integral_one_add_norm
  rw [finrank_hpar]
  exact hc

end pointwise

section main

/- English proof (translation)
Establish `: IsFiniteMeasureOnCompacts μ` using `⟨fun K hK => h.finite_compact K hK⟩`. Use `infer_instance`.
-/
lemma sigmaFinite_haar {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

/- English proof (translation)
Unfold `gN`. Use `fun_prop`.
-/
lemma gN_cont (k r : ℕ) : Continuous (fun x : Mt k r => gN (Matrix.of x : Mat k r)) := by
  unfold gN
  fun_prop

/- English proof (translation)
Apply `Continuous.measurable` to reduce the goal to its premises. Apply `continuous_pi` to reduce the goal to its premises. Introduce `p`. Apply `continuous_pi` to reduce the goal to its premises. Introduce `q`.

Use `show Continuous fun x : Mt k r' => ιLev k 1 r' (Matrix.of x) p q`. Unfold `ιLev`. Distinguish the cases in `hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1`. Simplify using `only [dif_pos hp]`. Distinguish the cases in `hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1`.

Simplify using `only [dif_pos hq]`. Conclude with `(continuous_apply _).comp (continuous_apply _)`. Simplify using `only [dif_neg hq]`. Conclude with `continuous_const`. Simplify using `only [dif_neg hp]`.

Conclude with `continuous_const`.
-/
lemma levM_meas (k r' : ℕ) : Measurable (levM k r') := by
  apply Continuous.measurable
  apply continuous_pi; intro p
  apply continuous_pi; intro q
  show Continuous fun x : Mt k r' => ιLev k 1 r' (Matrix.of x) p q
  unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [dif_pos hp]
    by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
    · simp only [dif_pos hq]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [dif_neg hq]; exact continuous_const
  · simp only [dif_neg hp]; exact continuous_const

/- English proof (translation)
Establish `hN : Nset k 0 = {1}` using `unipotent_haar_base_case k`. Establish `hc : μ ((({1} : Set (Mat k 0))ᶜ : Set (Mat k 0)) : Set (Mt k 0)) = 0`. Use `hμ.conc` as an intermediate fact. Rewrite `this` using `[hN]`. Conclude with `this`.

Establish `hae : ∀ᵐ x ∂μ, ENNReal.ofReal (gN (Matrix.of x : Mat k 0) ^ (-a)) = ENNReal.ofReal (gN (1 : Mat k 0) ^ (-a))`. Rewrite using `[ae_iff]`. Use `measure_mono_null ?_ hc` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Set.mem_ofPred_eq] at hx`.

Introduce `h1`. Apply `hx` to reduce the goal to its premises. Establish `: (Matrix.of x : Mat k 0) = 1` using `h1`. Rewrite using `[this]`. Rewrite using `[lintegral_congr_ae hae, lintegral_const]`.

Use `ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_` and prove the remaining obligations. Establish `h1 : μ ((({1} : Set (Mat k 0))) : Set (Mt k 0)) < ⊤` using `hμ.finite_compact _ isCompact_singleton`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma base (k : ℕ) (μ : Measure (Mt k 0)) (hμ : IsHaarOn (Nset k 0) μ) (a : ℝ) :
    ∫⁻ x, ENNReal.ofReal (gN (Matrix.of x : Mat k 0) ^ (-a)) ∂μ < ⊤ := by
  have hN : Nset k 0 = {1} := unipotent_haar_base_case k
  have hc : μ ((({1} : Set (Mat k 0))ᶜ : Set (Mat k 0)) : Set (Mt k 0)) = 0 := by
    have := hμ.conc; rw [hN] at this; exact this
  have hae : ∀ᵐ x ∂μ, ENNReal.ofReal (gN (Matrix.of x : Mat k 0) ^ (-a)) =
      ENNReal.ofReal (gN (1 : Mat k 0) ^ (-a)) := by
    rw [ae_iff]
    refine measure_mono_null ?_ hc
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    intro h1
    apply hx
    have : (Matrix.of x : Mat k 0) = 1 := h1
    rw [this]
  rw [lintegral_congr_ae hae, lintegral_const]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have h1 : μ ((({1} : Set (Mat k 0))) : Set (Mt k 0)) < ⊤ :=
    hμ.finite_compact _ isCompact_singleton
  calc μ Set.univ ≤ μ ((({1} : Set (Mat k 0))) : Set (Mt k 0)) +
        μ ((({1} : Set (Mat k 0))ᶜ : Set (Mat k 0)) : Set (Mt k 0)) := measure_univ_le_add_compl _
    _ < ⊤ := by rw [hc, add_zero]; exact h1

/- English proof (translation)
Use `revert μ a`. Proceed by induction on `r with`. Consider the case `zero => intro μ hμ a _`. Conclude with `base k μ hμ a`. Consider the case `succ r' ih`.

Rewrite using `[Nat.add_comm r' 1]`. Introduce `μ hμ a ha`. Establish `ha' : ((1 + r' : ℕ) : ℝ) * (4 * ((1 + r' : ℕ) : ℝ) + 2 * (k : ℝ) - 1) < a`. Break down `ha with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Move the coercions through the operations in `at ha'`. Establish `hr0 : (0 : ℝ) ≤ r'` using `Nat.cast_nonneg _`. Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg _`. Establish `ha0 : 0 < a` using `by nlinarith`.

Take `⟨μ', hμ'⟩` from `unipotent_haar_exists k r'`. Use `sigmaFinite_haar hμ'` as an intermediate fact. Take `⟨c, hc⟩` from `haar_measure_unique_up_to_scalar k (1 + r') (Nset k (1 + r')) _ μ (unipotent_radical_closed k (1 + r')) (unipotent_haar_recursion k r' μ' hμ') hμ.conc hμ.left hμ.finite_compact`. Establish `hf : Measurable (fun x : Mt k (1 + r') => ENNReal.ofReal (gN (Matrix.of x : Mat k (1 + r')) ^ (-a)))` using `ENNReal.measurable_ofReal.comp ((gN_cont k (1 + r')).measurable.pow_const _)`. Establish `hM : Measurable (mulM : Mt k (1 + r') × Mt k (1 + r') → Mt k (1 + r'))` using `Formalism.FourierDecayAlt.P.B2x1.mulM_cont.measurable`.

Rewrite using `[hc, lintegral_smul_measure]`. Rewrite using `[ENNReal.smul_def, smul_eq_mul]`. Use `ENNReal.mul_lt_top ENNReal.coe_lt_top ?_` and prove the remaining obligations. Rewrite using `[lintegral_map hf hM, Formalism.FourierDecayAlt.P.B2x5.μHeis_eq, Measure.map_prod_map _ _ (Formalism.FourierDecayAlt.P.B2x5.measurable_heisT k r') (levM_meas k r'), lintegral_map (f := fun p : Mt k (1 + r') × Mt k (1 + r') => ENNReal.ofReal (gN (Matrix.of (mulM p) : Mat k (1 + r' …`. Use `set θ : ℝ := 1 / (1 + (r' : ℝ)) with hθ`.

Establish `h1r : (0 : ℝ) < 1 + r'` using `by linarith`. Establish `hθ0 : 0 ≤ θ` using `by rw [hθ]; positivity`. Establish `hθ1 : θ ≤ 1` using `by rw [hθ, div_le_one h1r]; linarith`. Establish `hae : ∀ᵐ q ∂((volume : Measure (HPar k r')).prod μ'), Matrix.of q.2 ∈ Nset k r'`. Rewrite using `[ae_iff]`.

Use `measure_mono_null (t := (Set.univ : Set (HPar k r')) ×ˢ ((Nset k r')ᶜ : Set (Mt k r'))) ?_ ?_` and prove the remaining obligations. Introduce `q hq`. Conclude with `⟨trivial, hq⟩`. Rewrite using `[Measure.prod_prod, hμ'.conc, mul_zero]`. Establish `key : ∀ᵐ q ∂((volume : Measure (HPar k r')).prod μ'), ENNReal.ofReal (gN (Matrix.of (mulM (Prod.map (Formalism.FourierDecayAlt.P.B2x5.heisT k r') (levM k r') q)) : Mat k (1 + r')) ^ (-a)) ≤ ENNReal.ofReal (((1 + ‖q.1‖) / 2) ^ (-(θ * a))) * ENNReal.ofReal (gN (Matrix.of q.2 : Mat …` using `by filter_upwards [hae] with q hq`.

Establish `e : ENNReal.ofReal (gN (Matrix.of (mulM (Prod.map (Formalism.FourierDecayAlt.P.B2x5.heisT k r') (levM k r') q)) : Mat k (1 + r')) ^ (-a)) = ENNReal.ofReal (gN (heis0 k r' q.1 * ιLev k 1 r' (Matrix.of q.2)) ^ (-a))` using `rfl`. Rewrite using `[e, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hB : 1 ≤ gN (Matrix.of q.2 : Mat k r')` using `Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hq.1`. Apply `rpow_split (by positivity) (by linarith) _ (le_trans' (gN_mid_le q.1 _) le_rfl) ha0.le hθ0 hθ1` to reduce the goal to its premises.

Use `gN_heis_le q.1 (Matrix.of q.2 : Mat k r')` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hF1 : Measurable (fun x : HPar k r' => ENNReal.ofReal (((1 + ‖x‖) / 2) ^ (-(θ * a))))`. Apply `ENNReal.measurable_ofReal.comp` to reduce the goal to its premises. Conclude with `((measurable_const.add measurable_norm).div_const _).pow_const _`.

Establish `hF2 : Measurable (fun x : Mt k r' => ENNReal.ofReal (gN (Matrix.of x : Mat k r') ^ (-((1 - θ) * a))))` using `ENNReal.measurable_ofReal.comp ((gN_cont k r').measurable.pow_const _)`. Combine the equalities or inequalities in the displayed calculation. Use `ENNReal.mul_lt_top (lint_heis_fin k r' ?_) (ih μ' hμ' _ ?_)` and prove the remaining obligations. Use `push_cast`. Rewrite using `[hθ, one_div, inv_mul_eq_div, lt_div_iff₀ h1r]`.

Use the polynomial consequences of the given equalities and inequalities. Break down `Nat.eq_zero_or_pos r' with h0 | hpos` into its components or cases. Conclude with `Or.inl h0`. Use `right`. Establish `e1 : (1 - θ) * a = (r' : ℝ) * (a / (1 + r'))`.

Rewrite using `[hθ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Establish `hrpos : (0 : ℝ) < r'` using `by exact_mod_cast hpos`.

Apply `mul_lt_mul_of_pos_left _ hrpos` to reduce the goal to its premises. Rewrite using `[lt_div_iff₀ h1r]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lint_gN_fin (k r : ℕ) (μ : Measure (Mt k r)) (hμ : IsHaarOn (Nset k r) μ) (a : ℝ)
    (ha : r = 0 ∨ (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) < a) :
    ∫⁻ x, ENNReal.ofReal (gN (Matrix.of x : Mat k r) ^ (-a)) ∂μ < ⊤ := by
  revert μ a
  induction r with
  | zero => intro μ hμ a _; exact base k μ hμ a
  | succ r' ih =>
    rw [Nat.add_comm r' 1]
    intro μ hμ a ha
    have ha' : ((1 + r' : ℕ) : ℝ) * (4 * ((1 + r' : ℕ) : ℝ) + 2 * (k : ℝ) - 1) < a := by
      rcases ha with h | h
      · omega
      · exact h
    push_cast at ha'
    have hr0 : (0 : ℝ) ≤ r' := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have ha0 : 0 < a := by nlinarith
    obtain ⟨μ', hμ'⟩ := unipotent_haar_exists k r'
    have := sigmaFinite_haar hμ'
    obtain ⟨c, hc⟩ := haar_measure_unique_up_to_scalar k (1 + r') (Nset k (1 + r')) _ μ (unipotent_radical_closed k (1 + r'))
      (unipotent_haar_recursion k r' μ' hμ') hμ.conc hμ.left hμ.finite_compact
    have hf : Measurable (fun x : Mt k (1 + r') => ENNReal.ofReal (gN (Matrix.of x : Mat k (1 + r')) ^ (-a))) :=
      ENNReal.measurable_ofReal.comp ((gN_cont k (1 + r')).measurable.pow_const _)
    have hM : Measurable (mulM : Mt k (1 + r') × Mt k (1 + r') → Mt k (1 + r')) :=
      Formalism.FourierDecayAlt.P.B2x1.mulM_cont.measurable
    rw [hc, lintegral_smul_measure]
    rw [ENNReal.smul_def, smul_eq_mul]
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
    rw [lintegral_map hf hM, Formalism.FourierDecayAlt.P.B2x5.μHeis_eq,
      Measure.map_prod_map _ _ (Formalism.FourierDecayAlt.P.B2x5.measurable_heisT k r') (levM_meas k r'),
      lintegral_map (f := fun p : Mt k (1 + r') × Mt k (1 + r') =>
        ENNReal.ofReal (gN (Matrix.of (mulM p) : Mat k (1 + r')) ^ (-a))) (hf.comp hM)
        ((Formalism.FourierDecayAlt.P.B2x5.measurable_heisT k r').prodMap (levM_meas k r'))]
    set θ : ℝ := 1 / (1 + (r' : ℝ)) with hθ
    have h1r : (0 : ℝ) < 1 + r' := by linarith
    have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one h1r]; linarith
    have hae : ∀ᵐ q ∂((volume : Measure (HPar k r')).prod μ'), Matrix.of q.2 ∈ Nset k r' := by
      rw [ae_iff]
      refine measure_mono_null (t := (Set.univ : Set (HPar k r')) ×ˢ ((Nset k r')ᶜ : Set (Mt k r'))) ?_ ?_
      · intro q hq; exact ⟨trivial, hq⟩
      · rw [Measure.prod_prod, hμ'.conc, mul_zero]
    have key : ∀ᵐ q ∂((volume : Measure (HPar k r')).prod μ'),
        ENNReal.ofReal (gN (Matrix.of (mulM (Prod.map (Formalism.FourierDecayAlt.P.B2x5.heisT k r') (levM k r') q)) :
          Mat k (1 + r')) ^ (-a)) ≤
        ENNReal.ofReal (((1 + ‖q.1‖) / 2) ^ (-(θ * a))) *
          ENNReal.ofReal (gN (Matrix.of q.2 : Mat k r') ^ (-((1 - θ) * a))) := by
      filter_upwards [hae] with q hq
      have e : ENNReal.ofReal (gN (Matrix.of (mulM (Prod.map (Formalism.FourierDecayAlt.P.B2x5.heisT k r') (levM k r') q)) :
          Mat k (1 + r')) ^ (-a)) =
          ENNReal.ofReal (gN (heis0 k r' q.1 * ιLev k 1 r' (Matrix.of q.2)) ^ (-a)) := rfl
      rw [e, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      apply ENNReal.ofReal_le_ofReal
      have hB : 1 ≤ gN (Matrix.of q.2 : Mat k r') := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hq.1
      apply rpow_split (by positivity) (by linarith) _ (le_trans' (gN_mid_le q.1 _) le_rfl) ha0.le hθ0 hθ1
      have := gN_heis_le q.1 (Matrix.of q.2 : Mat k r')
      linarith
    have hF1 : Measurable (fun x : HPar k r' => ENNReal.ofReal (((1 + ‖x‖) / 2) ^ (-(θ * a)))) := by
      apply ENNReal.measurable_ofReal.comp
      exact ((measurable_const.add measurable_norm).div_const _).pow_const _
    have hF2 : Measurable (fun x : Mt k r' => ENNReal.ofReal (gN (Matrix.of x : Mat k r') ^ (-((1 - θ) * a)))) :=
      ENNReal.measurable_ofReal.comp ((gN_cont k r').measurable.pow_const _)
    calc _ ≤ ∫⁻ q, ENNReal.ofReal (((1 + ‖q.1‖) / 2) ^ (-(θ * a))) *
          ENNReal.ofReal (gN (Matrix.of q.2 : Mat k r') ^ (-((1 - θ) * a))) ∂((volume : Measure (HPar k r')).prod μ') :=
          lintegral_mono_ae key
      _ = (∫⁻ x : HPar k r', ENNReal.ofReal (((1 + ‖x‖) / 2) ^ (-(θ * a)))) *
          ∫⁻ x, ENNReal.ofReal (gN (Matrix.of x : Mat k r') ^ (-((1 - θ) * a))) ∂μ' :=
          lintegral_prod_mul hF1.aemeasurable hF2.aemeasurable
      _ < ⊤ := by
        refine ENNReal.mul_lt_top (lint_heis_fin k r' ?_) (ih μ' hμ' _ ?_)
        · push_cast
          rw [hθ, one_div, inv_mul_eq_div, lt_div_iff₀ h1r]
          nlinarith
        · rcases Nat.eq_zero_or_pos r' with h0 | hpos
          · exact Or.inl h0
          · right
            have e1 : (1 - θ) * a = (r' : ℝ) * (a / (1 + r')) := by
              rw [hθ]; field_simp; ring
            rw [e1]
            have hrpos : (0 : ℝ) < r' := by exact_mod_cast hpos
            apply mul_lt_mul_of_pos_left _ hrpos
            rw [lt_div_iff₀ h1r]
            nlinarith

end main

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt

open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.WeakDominationMajorants

variable {k r : ℕ}

/- English proof (translation)
Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Use `⟨gN (1 : Mat k 0), Orb.gN_nonneg _, fun g _ n hn n' hn' => ?_⟩` and prove the remaining obligations. Establish `hN` using `Formalism.FourierDecayAlt.P.unipotent_haar_base_case k`. Rewrite `hn`, `hn'` using `[hN]`. Rewrite using `[Set.mem_singleton_iff.1 hn, Set.mem_singleton_iff.1 hn']`.

Simplify using the standard rewrite rules. Take `⟨C, hC, h⟩` from `Orb.orbit z z' K hK hKO`. Use `⟨C, hC, fun g hg n hn n' hn' => ?_⟩` and prove the remaining obligations. Establish `hX` using `Orb.one_le_X (hKO hg).1 hn hn'`. Establish `hp : gN (n⁻¹ * g * n') ^ (2 * r + 1) ≤ gN (n⁻¹ * g * n') ^ (3 * r)` using `pow_le_pow_right₀ hX (by omega)`.

Take `⟨h1, h2⟩` from `h g hg n hn n' hn'`. Conclude with `⟨h1.trans (mul_le_mul_of_nonneg_left hp hC), h2.trans (mul_le_mul_of_nonneg_left hp hC)⟩`.
-/
lemma orbit3 (z z' : Fin (2 * r + k + 1) → ℂ) (K : Set (Mat k r)) (hK : IsCompact K)
    (hKO : K ⊆ Om k r z z') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      gN n ≤ C * gN (n⁻¹ * g * n') ^ (3 * r) ∧ gN n' ≤ C * gN (n⁻¹ * g * n') ^ (3 * r) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨gN (1 : Mat k 0), Orb.gN_nonneg _, fun g _ n hn n' hn' => ?_⟩
    have hN := Formalism.FourierDecayAlt.P.unipotent_haar_base_case k
    rw [hN] at hn hn'
    rw [Set.mem_singleton_iff.1 hn, Set.mem_singleton_iff.1 hn']
    simp
  · obtain ⟨C, hC, h⟩ := Orb.orbit z z' K hK hKO
    refine ⟨C, hC, fun g hg n hn n' hn' => ?_⟩
    have hX := Orb.one_le_X (hKO hg).1 hn hn'
    have hp : gN (n⁻¹ * g * n') ^ (2 * r + 1) ≤ gN (n⁻¹ * g * n') ^ (3 * r) :=
      pow_le_pow_right₀ hX (by omega)
    obtain ⟨h1, h2⟩ := h g hg n hn n' hn'
    exact ⟨h1.trans (mul_le_mul_of_nonneg_left hp hC), h2.trans (mul_le_mul_of_nonneg_left hp hC)⟩

/- English proof (translation)
Establish `hc` using `Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT`. Take `⟨M, hM⟩` from `(hc.image_of_continuousOn Orb.continuous_gN.continuousOn).bddAbove`. Conclude with `⟨max 1 M, le_max_left _ _, fun h hh => (hM (Set.mem_image_of_mem _ hh)).trans (le_max_right _ _)⟩`.
-/
lemma uw_bound (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ h ∈ UWset k r z, gN h ≤ c := by
  have hc := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT
  obtain ⟨M, hM⟩ := (hc.image_of_continuousOn Orb.continuous_gN.continuousOn).bddAbove
  exact ⟨max 1 M, le_max_left _ _, fun h hh => (hM (Set.mem_image_of_mem _ hh)).trans (le_max_right _ _)⟩

/- English proof (translation)
The claim follows from `(Matrix.norm_le_iff (Orb.gN_nonneg M)).2 fun i j => Orb.ent_le M i j`.
-/
lemma sup_le_gN (M : Mat k r) : ‖M‖ ≤ gN M :=
  (Matrix.norm_le_iff (Orb.gN_nonneg M)).2 fun i j => Orb.ent_le M i j

/- English proof (translation)
Use `Orb.gN_le_of_ent X 1 zero_le_one (fun i j => hX.2 i j)` as an intermediate fact. Simplify using `using this`.
-/
lemma gN_unit {X : Mat k r} (hX : unitLie k r X) : gN X ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
  have := Orb.gN_le_of_ent X 1 zero_le_one (fun i j => hX.2 i j)
  simpa using this

/- English proof (translation)
Use `(sup_le_gN _).trans ?_` and prove the remaining obligations. Establish `h1` using `Formalism.FourierDecayAlt.P.B6.gN_mul_le (s⁻¹ * X) s`. Establish `h2` using `Formalism.FourierDecayAlt.P.B6.gN_mul_le s⁻¹ X`. Rewrite `h2` using `[Orb.gN_inv hs]`. Establish `h3` using `gN_unit hX`.

Establish `hs0` using `Orb.gN_nonneg s`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma ad_bd {s X : Mat k r} (hs : s ∈ GV k r) (hX : unitLie k r X) :
    ‖s⁻¹ * X * s‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * gN s ^ 2 := by
  refine (sup_le_gN _).trans ?_
  have h1 := Formalism.FourierDecayAlt.P.B6.gN_mul_le (s⁻¹ * X) s
  have h2 := Formalism.FourierDecayAlt.P.B6.gN_mul_le s⁻¹ X
  rw [Orb.gN_inv hs] at h2
  have h3 := gN_unit hX
  have hs0 := Orb.gN_nonneg s
  calc gN (s⁻¹ * X * s) ≤ gN (s⁻¹ * X) * gN s := h1
    _ ≤ (gN s * gN X) * gN s := mul_le_mul_of_nonneg_right h2 hs0
    _ ≤ (gN s * ((2 * r + k + 1 : ℕ) : ℝ)) * gN s := by gcongr
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * gN s ^ 2 := by ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons x l ih`. Rewrite using `[List.prod_cons, List.length_cons, pow_succ, mul_comm (c ^ l.length)]`. Establish `hx` using `h x List.mem_cons_self`.

Establish `ih'` using `ih fun y hy => h y (List.mem_cons_of_mem _ hy)`. Establish `hl : 0 ≤ l.prod` using `List.prod_nonneg fun y hy => (h y (List.mem_cons_of_mem _ hy)).1`. Conclude with `mul_le_mul hx.2 ih' hl (hx.1.trans hx.2)`.
-/
lemma list_prod_le (l : List ℝ) (c : ℝ) (h : ∀ x ∈ l, 0 ≤ x ∧ x ≤ c) : l.prod ≤ c ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons, List.length_cons, pow_succ, mul_comm (c ^ l.length)]
    have hx := h x List.mem_cons_self
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hl : 0 ≤ l.prod := List.prod_nonneg fun y hy => (h y (List.mem_cons_of_mem _ hy)).1
    exact mul_le_mul hx.2 ih' hl (hx.1.trans hx.2)

/- English proof (translation)
Establish `h' : G / C4 ≤ X ^ e` using `by rw [div_le_iff₀ hC4]; linarith [mul_comm C4 (X ^ e)]`. Use `Real.rpow_le_rpow_of_nonpos (div_pos hG hC4) h' (by linarith : -β ≤ 0)` as an intermediate fact. Rewrite `this` using `[Real.div_rpow hG.le hC4.le, Real.rpow_neg hC4.le, div_inv_eq_mul]`. Combine the linear relations using `[mul_comm (G ^ (-β)) (C4 ^ β)]`.
-/
lemma rp_bd (X C4 G β : ℝ) (e : ℕ) (hC4 : 0 < C4) (hG : 0 < G) (h : G ≤ C4 * X ^ e) (hβ : 0 ≤ β) :
    (X ^ e) ^ (-β) ≤ C4 ^ β * G ^ (-β) := by
  have h' : G / C4 ≤ X ^ e := by rw [div_le_iff₀ hC4]; linarith [mul_comm C4 (X ^ e)]
  have := Real.rpow_le_rpow_of_nonpos (div_pos hG hC4) h' (by linarith : -β ≤ 0)
  rw [Real.div_rpow hG.le hC4.le, Real.rpow_neg hC4.le, div_inv_eq_mul] at this
  linarith [mul_comm (G ^ (-β)) (C4 ^ β)]

/- English proof (translation)
Establish `hXpos : 0 < X` using `by linarith`. Establish `hXA : 0 ≤ X ^ (-A)` using `Real.rpow_nonneg hXpos.le _`. Establish `hb1` using `rp_bd X C4 G1 β (3 * r) (by linarith) (by linarith) h1 hβ`. Establish `hb2` using `rp_bd X C4 G2 β (3 * r) (by linarith) (by linarith) h2 hβ`. Establish `hn1 : 0 ≤ (X ^ (3 * r)) ^ (-β)` using `Real.rpow_nonneg (by positivity) _`.

Establish `hn2 : 0 ≤ C4 ^ β * G1 ^ (-β)`. Use `Real.rpow_nonneg (show (0:ℝ) ≤ C4 by linarith) β` as an intermediate fact. Use `Real.rpow_nonneg (show (0:ℝ) ≤ G1 by linarith) (-β); positivity` as an intermediate fact. Establish `hΛm : 0 ≤ Λ1 ^ m` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_pow, ← pow_mul, mul_assoc, ← Real.rpow_natCast X (6 * r * m), ← Real.rpow_add hXpos]`. Use `congr 2`. Rewrite using `[hA1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ Λ1 ^ m * X ^ (-(6 * (r : ℝ) * β)) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) hΛm`. Use `_ = Λ1 ^ m * ((X ^ (3 * r)) ^ (-β) * (X ^ (3 * r)) ^ (-β)) := by`. Use `congr 1`. Rewrite using `[← Real.rpow_natCast X (3 * r), ← Real.rpow_mul hXpos.le, ← Real.rpow_add hXpos]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ Λ1 ^ m * ((C4 ^ β * G1 ^ (-β)) * (C4 ^ β * G2 ^ (-β))) := by gcongr`. Use `_ = Λ1 ^ m * (C4 ^ β) ^ 2 * (G1 ^ (-β) * G2 ^ (-β)) := by ring`.
-/
lemma real_step (X G1 G2 C4 Λ1 A A1 β P : ℝ) (m r : ℕ) (hX : 1 ≤ X) (hC4 : 1 ≤ C4) (hG1 : 1 ≤ G1)
    (hG2 : 1 ≤ G2) (h1 : G1 ≤ C4 * X ^ (3 * r)) (h2 : G2 ≤ C4 * X ^ (3 * r)) (hβ : 0 ≤ β)
    (hβA : 6 * (r : ℝ) * β ≤ A1) (hA1 : A1 = A - 6 * (r : ℝ) * (m : ℝ)) (hΛ : 1 ≤ Λ1)
    (hP : P ≤ (Λ1 * X ^ (6 * r)) ^ m) :
    P * X ^ (-A) ≤ Λ1 ^ m * (C4 ^ β) ^ 2 * (G1 ^ (-β) * G2 ^ (-β)) := by
  have hXpos : 0 < X := by linarith
  have hXA : 0 ≤ X ^ (-A) := Real.rpow_nonneg hXpos.le _
  have hb1 := rp_bd X C4 G1 β (3 * r) (by linarith) (by linarith) h1 hβ
  have hb2 := rp_bd X C4 G2 β (3 * r) (by linarith) (by linarith) h2 hβ
  have hn1 : 0 ≤ (X ^ (3 * r)) ^ (-β) := Real.rpow_nonneg (by positivity) _
  have hn2 : 0 ≤ C4 ^ β * G1 ^ (-β) := by
    have := Real.rpow_nonneg (show (0:ℝ) ≤ C4 by linarith) β
    have := Real.rpow_nonneg (show (0:ℝ) ≤ G1 by linarith) (-β); positivity
  have hΛm : 0 ≤ Λ1 ^ m := by positivity
  calc P * X ^ (-A) ≤ (Λ1 * X ^ (6 * r)) ^ m * X ^ (-A) := mul_le_mul_of_nonneg_right hP hXA
    _ = Λ1 ^ m * X ^ (-A1) := by
        rw [mul_pow, ← pow_mul, mul_assoc, ← Real.rpow_natCast X (6 * r * m), ← Real.rpow_add hXpos]
        congr 2
        rw [hA1]; push_cast; ring
    _ ≤ Λ1 ^ m * X ^ (-(6 * (r : ℝ) * β)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) hΛm
    _ = Λ1 ^ m * ((X ^ (3 * r)) ^ (-β) * (X ^ (3 * r)) ^ (-β)) := by
        congr 1
        rw [← Real.rpow_natCast X (3 * r), ← Real.rpow_mul hXpos.le, ← Real.rpow_add hXpos]
        congr 1; push_cast; ring
    _ ≤ Λ1 ^ m * ((C4 ^ β * G1 ^ (-β)) * (C4 ^ β * G2 ^ (-β))) := by
        gcongr
    _ = Λ1 ^ m * (C4 ^ β) ^ 2 * (G1 ^ (-β) * G2 ^ (-β)) := by ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨calc μ Set.univ ≤ μ U + μ Uᶜ := measure_univ_le_add_compl U _ = μ U := by rw [h.conc, add_zero] _ < ⊤ := h.finite_compact U hU⟩`.
-/
lemma haar_finite {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) (hU : IsCompact U) :
    IsFiniteMeasure μ :=
  ⟨calc μ Set.univ ≤ μ U + μ Uᶜ := measure_univ_le_add_compl U
      _ = μ U := by rw [h.conc, add_zero]
      _ < ⊤ := h.finite_compact U hU⟩

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm

open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.WeakDominationMajorants

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ D A m hThr K hK hKO`. Take `⟨C3, hC3, horb⟩` from `orbit3 D.z D.z' K hK hKO`. Take `⟨cW, hcW, hW⟩` from `uw_bound D.z D.z_mem D.T_pos`. Take `⟨cW', hcW', hW'⟩` from `uw_bound D.z' D.z'_mem D.T'_pos`. Establish `hc : 1 ≤ max cW cW'` using `le_trans hcW (le_max_left _ _)`.

Establish `hC4 : 1 ≤ max 1 (C3 * max cW cW' ^ (6 * r))` using `le_max_left _ _`. Use `set c := max cW cW' with hc_def`. Use `set C4 := max 1 (C3 * c ^ (6 * r)) with hC4_def`. Use `set NN : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hNN`. Establish `hNN1 : 1 ≤ NN` using `by rw [hNN]; exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)`.

Use `set Λ1 := max 1 (NN * c ^ 2 * C4 ^ 2) with hΛ1_def`. Establish `hΛ1 : 1 ≤ Λ1` using `le_max_left _ _`. Use `set A1 := A - 6 * (r : ℝ) * (m : ℝ) with hA1_def`. Establish `hThr' : 9 * ((r : ℝ) + 1) * NN ^ 2 < A1`. Establish `h9 : (0 : ℝ) < 9 * ((r : ℝ) + 1)` using `by positivity`.

Use `(lt_div_iff₀ h9).1 hThr` as an intermediate fact. Rewrite using `[hNN]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA1pos : 0 < A1` using `lt_of_le_of_lt (by positivity) hThr'`. Use `set β := A1 / (6 * (r : ℝ) + 1) with hβ_def`.

Establish `hβ0 : 0 ≤ β` using `div_nonneg hA1pos.le (by positivity)`. Establish `hβA : 6 * (r : ℝ) * β ≤ A1`. Rewrite using `[hβ_def, mul_div_assoc']`. Rewrite using `[div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hthr : r = 0 ∨ (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) < β`. Break down `Nat.eq_zero_or_pos r with h | h` into its components or cases. Conclude with `Or.inl h`. Use `right`. Rewrite using `[hβ_def, lt_div_iff₀ (by positivity)]`.

Establish `hr : (1 : ℝ) ≤ r` using `by exact_mod_cast h`. Establish `hk : (0 : ℝ) ≤ k` using `by positivity`. Establish `hNNe : NN = 2 * (r : ℝ) + k + 1` using `by rw [hNN]; push_cast; ring`. Rewrite `hThr'` using `[hNNe]`. Use polynomial arithmetic with `[mul_nonneg (by linarith : (0:ℝ) ≤ r) hk, mul_nonneg hk hk, mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ r) hk) hk, mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ r) (by linarith : (0:ℝ) ≤ r)) hk]`.

Use `set f : Mt k r → ℝ := fun x => gN (Matrix.of x : Mat k r) ^ (-β) with hf_def`. Use `⟨fun p => Λ1 ^ m * (C4 ^ β) ^ 2 * (f p.1.2 * f p.2.2), ?_, ?_⟩` and prove the remaining obligations. Establish `: SigmaFinite D.μN` using `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN`. Establish `: IsFiniteMeasure D.μW` using `haar_finite D.haarW (Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z D.z_mem D.T_pos)`. Establish `: IsFiniteMeasure D.μW'` using `haar_finite D.haarW' (Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z' D.z'_mem D.T'_pos)`.

Establish `hfi : Integrable f D.μN`. Use `⟨((NInt.gN_cont k r).measurable.pow_const (-β)).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (Orb.gN_nonneg _) _)]`. Conclude with `NInt.lint_gN_fin k r D.μN D.haarN β hthr`. Establish `h1 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * f q.2) (D.μW.prod D.μN)` using `(integrable_const (1 : ℝ)).mul_prod hfi`.

Establish `h2 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * f q.2) (D.μW'.prod D.μN)` using `(integrable_const (1 : ℝ)).mul_prod hfi`. Establish `h3` using `(h1.mul_prod h2).const_mul (Λ1 ^ m * (C4 ^ β) ^ 2)`. Use `h3.congr (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Simplify using `only [one_mul]`. Introduce `u v hu hv hl g hg filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp`.

Establish `hh : Matrix.of p.1.1 ∈ GV k r` using `hp.1.1`. Establish `hn : Matrix.of p.1.2 ∈ Nset k r` using `hp.2.1`. Establish `hh' : Matrix.of p.2.1 ∈ GV k r` using `hp.2.2.1.1`. Establish `hn' : Matrix.of p.2.2 ∈ Nset k r` using `hp.2.2.2`. Establish `hgG : g ∈ GV k r` using `(hKO hg).1`.

Establish `hx : sgs p g ∈ GV k r`. Simplify using `only [sgs]`. Conclude with `Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv h …`. Use `set X := gN (sgs p g) with hX_def`. Establish `hX1 : 1 ≤ X` using `Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx`.

Establish `hY : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 = Matrix.of p.1.1 * sgs p g * (Matrix.of p.2.1)⁻¹`. Establish `hs : sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1`. Simplify using `only [sgs, Matrix.mul_assoc]`. Rewrite using `[hs, Matrix.mul_assoc (Matrix.of p.1.1)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit hh), Matrix.mul_nonsing_inv_cancel_right _ _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit hh')]`. Establish `hgh : gN (Matrix.of p.1.1) ≤ c` using `(hW _ hp.1).trans (le_max_left _ _)`.

Establish `hgh' : gN (Matrix.of p.2.1) ≤ c` using `(hW' _ hp.2.2.1).trans (le_max_right _ _)`. Establish `hYb : gN ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) ≤ c ^ 2 * X`. Rewrite using `[hY]`. Establish `e1` using `Formalism.FourierDecayAlt.P.B6.gN_mul_le (Matrix.of p.1.1 * sgs p g) (Matrix.of p.2.1)⁻¹`. Establish `e2` using `Formalism.FourierDecayAlt.P.B6.gN_mul_le (Matrix.of p.1.1) (sgs p g)`.

Rewrite `e1` using `[Orb.gN_inv hh']`. Use `Orb.gN_nonneg (sgs p g)` as an intermediate fact. Use `Orb.gN_nonneg (Matrix.of p.1.1)` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `e3 : gN (Matrix.of p.1.1 * sgs p g) ≤ c * X` using `e2.trans (mul_le_mul_of_nonneg_right hgh (Orb.gN_nonneg _))`.

Conclude with `mul_le_mul e3 hgh' (Orb.gN_nonneg _) (by positivity)`. Use `_ = c ^ 2 * X := by ring`. Establish `hYX : gN ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) ^ (3 * r) ≤ c ^ (6 * r) * X ^ (3 * r)`. Combine the equalities or inequalities in the displayed calculation. Take `⟨hb1, hb2⟩` from `horb g hg _ hn _ hn'`.

Establish `hXr : 0 ≤ X ^ (3 * r)` using `by positivity`. Establish `hG1 : gN (Matrix.of p.1.2) ≤ C4 * X ^ (3 * r)`. Use `hb1.trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hG2 : gN (Matrix.of p.2.2) ≤ C4 * X ^ (3 * r)`.

Use `hb2.trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hlet : ∀ s h : Mat k r, s = Matrix.of p.1.2 * Matrix.of p.1.1 ∨ s = Matrix.of p.2.2 * Matrix.of p.2.1 → s ∈ GV k r → ∀ Y : Mat k r, unitLie k r Y → ‖s⁻¹ * Y * s‖ ≤ Λ1 * X ^ (6 * r)`. Introduce `s _ hs hsG Y hYu`. Establish `hsb : gN s ≤ C4 * X ^ (3 * r) * c`.

Break down `hs with rfl | rfl` into its components or cases. Conclude with `(Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul hG1 hgh (Orb.gN_nonneg _) (by positivity))`. Conclude with `(Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul hG2 hgh' (Orb.gN_nonneg _) (by positivity))`. Use `(ad_bd hsG hYu).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hΛX : 1 ≤ Λ1 * X ^ (6 * r)` using `one_le_mul_of_one_le_of_one_le hΛ1 (one_le_pow₀ hX1)`. Establish `hPu : (u.map fun Y => ‖AdL p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ u.length`. Use `list_prod_le (u.map fun Y => ‖AdL p Y‖) (Λ1 * X ^ (6 * r)) (by` as an intermediate fact. Introduce `y hy`. Take `⟨Y, hYu, rfl⟩` from `List.mem_map.1 hy`.

Conclude with `⟨norm_nonneg _, hlet _ (Matrix.of p.1.1) (Or.inl rfl) (Formalism.FourierDecayAlt.P.JFxDs2.sL_mem hp) Y (hu Y hYu)⟩)`. Simplify using `using this`. Establish `hPv : (v.map fun Y => ‖AdR p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ v.length`. Use `list_prod_le (v.map fun Y => ‖AdR p Y‖) (Λ1 * X ^ (6 * r)) (by` as an intermediate fact. Introduce `y hy`.

Take `⟨Y, hYv, rfl⟩` from `List.mem_map.1 hy`. Conclude with `⟨norm_nonneg _, hlet _ (Matrix.of p.2.1) (Or.inr rfl) (Formalism.FourierDecayAlt.P.JFxDs2.sR_mem hp) Y (hv Y hYv)⟩)`. Simplify using `using this`. Establish `hP : (u.map fun Y => ‖AdL p Y‖).prod * (v.map fun Y => ‖AdR p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ m`. Establish `hu0 : 0 ≤ (u.map fun Y => ‖AdL p Y‖).prod` using `List.prod_nonneg fun y hy => by`.

Take `⟨Y, _, rfl⟩` from `List.mem_map.1 hy`. Conclude with `norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Take `⟨Y, _, rfl⟩` from `List.mem_map.1 hy; exact norm_nonneg _) (by positivity)`. Use `_ = (Λ1 * X ^ (6 * r)) ^ (u.length + v.length) := by rw [pow_add]`.

Use `_ ≤ (Λ1 * X ^ (6 * r)) ^ m := pow_le_pow_right₀ hΛX hl`. Conclude with `real_step X (gN (Matrix.of p.1.2)) (gN (Matrix.of p.2.2)) C4 Λ1 A A1 β _ m r hX1 hC4 (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (Orb.n_mem_G hn)) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (Orb.n_mem_G hn')) hG1 hG2 hβ0 hβA hA1_def hΛ1 hP`.
-/
theorem nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj := by
  intro k r Wp Wq _ _ _ _ D A m hThr K hK hKO
  obtain ⟨C3, hC3, horb⟩ := orbit3 D.z D.z' K hK hKO
  obtain ⟨cW, hcW, hW⟩ := uw_bound D.z D.z_mem D.T_pos
  obtain ⟨cW', hcW', hW'⟩ := uw_bound D.z' D.z'_mem D.T'_pos

  have hc : 1 ≤ max cW cW' := le_trans hcW (le_max_left _ _)
  have hC4 : 1 ≤ max 1 (C3 * max cW cW' ^ (6 * r)) := le_max_left _ _
  set c := max cW cW' with hc_def
  set C4 := max 1 (C3 * c ^ (6 * r)) with hC4_def
  set NN : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hNN
  have hNN1 : 1 ≤ NN := by rw [hNN]; exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  set Λ1 := max 1 (NN * c ^ 2 * C4 ^ 2) with hΛ1_def
  have hΛ1 : 1 ≤ Λ1 := le_max_left _ _
  set A1 := A - 6 * (r : ℝ) * (m : ℝ) with hA1_def

  have hThr' : 9 * ((r : ℝ) + 1) * NN ^ 2 < A1 := by
    have h9 : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    have := (lt_div_iff₀ h9).1 hThr
    rw [hNN]; linarith
  have hA1pos : 0 < A1 := lt_of_le_of_lt (by positivity) hThr'
  set β := A1 / (6 * (r : ℝ) + 1) with hβ_def
  have hβ0 : 0 ≤ β := div_nonneg hA1pos.le (by positivity)
  have hβA : 6 * (r : ℝ) * β ≤ A1 := by
    rw [hβ_def, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hthr : r = 0 ∨ (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) < β := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact Or.inl h
    · right
      rw [hβ_def, lt_div_iff₀ (by positivity)]
      have hr : (1 : ℝ) ≤ r := by exact_mod_cast h
      have hk : (0 : ℝ) ≤ k := by positivity
      have hNNe : NN = 2 * (r : ℝ) + k + 1 := by rw [hNN]; push_cast; ring
      rw [hNNe] at hThr'
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r) hk, mul_nonneg hk hk, mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ r) hk) hk,
        mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ r) (by linarith : (0:ℝ) ≤ r)) hk]

  set f : Mt k r → ℝ := fun x => gN (Matrix.of x : Mat k r) ^ (-β) with hf_def
  refine ⟨fun p => Λ1 ^ m * (C4 ^ β) ^ 2 * (f p.1.2 * f p.2.2), ?_, ?_⟩
  ·
    have : SigmaFinite D.μN := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
    have : IsFiniteMeasure D.μW := haar_finite D.haarW (Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z D.z_mem D.T_pos)
    have : IsFiniteMeasure D.μW' :=
      haar_finite D.haarW' (Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z' D.z'_mem D.T'_pos)
    have hfi : Integrable f D.μN := by
      refine ⟨((NInt.gN_cont k r).measurable.pow_const (-β)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (Orb.gN_nonneg _) _)]
      exact NInt.lint_gN_fin k r D.μN D.haarN β hthr
    have h1 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * f q.2) (D.μW.prod D.μN) :=
      (integrable_const (1 : ℝ)).mul_prod hfi
    have h2 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * f q.2) (D.μW'.prod D.μN) :=
      (integrable_const (1 : ℝ)).mul_prod hfi
    have h3 := (h1.mul_prod h2).const_mul (Λ1 ^ m * (C4 ^ β) ^ 2)
    refine h3.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [one_mul]
  · intro u v hu hv hl g hg
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp

    have hh : Matrix.of p.1.1 ∈ GV k r := hp.1.1
    have hn : Matrix.of p.1.2 ∈ Nset k r := hp.2.1
    have hh' : Matrix.of p.2.1 ∈ GV k r := hp.2.2.1.1
    have hn' : Matrix.of p.2.2 ∈ Nset k r := hp.2.2.2
    have hgG : g ∈ GV k r := (hKO hg).1
    have hx : sgs p g ∈ GV k r := by
      simp only [sgs]
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
        (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hh) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (Orb.n_mem_G hn))) hgG) (Orb.n_mem_G hn')) hh'
    set X := gN (sgs p g) with hX_def
    have hX1 : 1 ≤ X := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx

    have hY : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 = Matrix.of p.1.1 * sgs p g * (Matrix.of p.2.1)⁻¹ := by
      have hs : sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
        simp only [sgs, Matrix.mul_assoc]
      rw [hs, Matrix.mul_assoc (Matrix.of p.1.1)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit hh),
        Matrix.mul_nonsing_inv_cancel_right _ _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit hh')]
    have hgh : gN (Matrix.of p.1.1) ≤ c := (hW _ hp.1).trans (le_max_left _ _)
    have hgh' : gN (Matrix.of p.2.1) ≤ c := (hW' _ hp.2.2.1).trans (le_max_right _ _)
    have hYb : gN ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) ≤ c ^ 2 * X := by
      rw [hY]
      have e1 := Formalism.FourierDecayAlt.P.B6.gN_mul_le (Matrix.of p.1.1 * sgs p g) (Matrix.of p.2.1)⁻¹
      have e2 := Formalism.FourierDecayAlt.P.B6.gN_mul_le (Matrix.of p.1.1) (sgs p g)
      rw [Orb.gN_inv hh'] at e1
      have := Orb.gN_nonneg (sgs p g); have := Orb.gN_nonneg (Matrix.of p.1.1)
      calc _ ≤ gN (Matrix.of p.1.1 * sgs p g) * gN (Matrix.of p.2.1) := e1
        _ ≤ (c * X) * c := by
            have e3 : gN (Matrix.of p.1.1 * sgs p g) ≤ c * X :=
              e2.trans (mul_le_mul_of_nonneg_right hgh (Orb.gN_nonneg _))
            exact mul_le_mul e3 hgh' (Orb.gN_nonneg _) (by positivity)
        _ = c ^ 2 * X := by ring
    have hYX : gN ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) ^ (3 * r) ≤ c ^ (6 * r) * X ^ (3 * r) := by
      calc _ ≤ (c ^ 2 * X) ^ (3 * r) := pow_le_pow_left₀ (Orb.gN_nonneg _) hYb _
        _ = c ^ (6 * r) * X ^ (3 * r) := by rw [mul_pow, ← pow_mul]; ring_nf
    obtain ⟨hb1, hb2⟩ := horb g hg _ hn _ hn'
    have hXr : 0 ≤ X ^ (3 * r) := by positivity
    have hG1 : gN (Matrix.of p.1.2) ≤ C4 * X ^ (3 * r) := by
      refine hb1.trans ?_
      calc C3 * _ ≤ C3 * (c ^ (6 * r) * X ^ (3 * r)) := mul_le_mul_of_nonneg_left hYX hC3
        _ = (C3 * c ^ (6 * r)) * X ^ (3 * r) := by ring
        _ ≤ C4 * X ^ (3 * r) := mul_le_mul_of_nonneg_right (le_max_right _ _) hXr
    have hG2 : gN (Matrix.of p.2.2) ≤ C4 * X ^ (3 * r) := by
      refine hb2.trans ?_
      calc C3 * _ ≤ C3 * (c ^ (6 * r) * X ^ (3 * r)) := mul_le_mul_of_nonneg_left hYX hC3
        _ = (C3 * c ^ (6 * r)) * X ^ (3 * r) := by ring
        _ ≤ C4 * X ^ (3 * r) := mul_le_mul_of_nonneg_right (le_max_right _ _) hXr

    have hlet : ∀ s h : Mat k r, s = Matrix.of p.1.2 * Matrix.of p.1.1 ∨ s = Matrix.of p.2.2 * Matrix.of p.2.1 →
        s ∈ GV k r → ∀ Y : Mat k r, unitLie k r Y → ‖s⁻¹ * Y * s‖ ≤ Λ1 * X ^ (6 * r) := by
      intro s _ hs hsG Y hYu
      have hsb : gN s ≤ C4 * X ^ (3 * r) * c := by
        rcases hs with rfl | rfl
        · exact (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul hG1 hgh (Orb.gN_nonneg _) (by positivity))
        · exact (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul hG2 hgh' (Orb.gN_nonneg _) (by positivity))
      refine (ad_bd hsG hYu).trans ?_
      calc NN * gN s ^ 2 ≤ NN * (C4 * X ^ (3 * r) * c) ^ 2 := by
            gcongr; exact Orb.gN_nonneg _
        _ = (NN * c ^ 2 * C4 ^ 2) * X ^ (6 * r) := by ring_nf
        _ ≤ Λ1 * X ^ (6 * r) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hΛX : 1 ≤ Λ1 * X ^ (6 * r) := one_le_mul_of_one_le_of_one_le hΛ1 (one_le_pow₀ hX1)
    have hPu : (u.map fun Y => ‖AdL p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ u.length := by
      have := list_prod_le (u.map fun Y => ‖AdL p Y‖) (Λ1 * X ^ (6 * r)) (by
        intro y hy
        obtain ⟨Y, hYu, rfl⟩ := List.mem_map.1 hy
        exact ⟨norm_nonneg _, hlet _ (Matrix.of p.1.1) (Or.inl rfl) (Formalism.FourierDecayAlt.P.JFxDs2.sL_mem hp) Y (hu Y hYu)⟩)
      simpa using this
    have hPv : (v.map fun Y => ‖AdR p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ v.length := by
      have := list_prod_le (v.map fun Y => ‖AdR p Y‖) (Λ1 * X ^ (6 * r)) (by
        intro y hy
        obtain ⟨Y, hYv, rfl⟩ := List.mem_map.1 hy
        exact ⟨norm_nonneg _, hlet _ (Matrix.of p.2.1) (Or.inr rfl) (Formalism.FourierDecayAlt.P.JFxDs2.sR_mem hp) Y (hv Y hYv)⟩)
      simpa using this
    have hP : (u.map fun Y => ‖AdL p Y‖).prod * (v.map fun Y => ‖AdR p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ m := by
      have hu0 : 0 ≤ (u.map fun Y => ‖AdL p Y‖).prod := List.prod_nonneg fun y hy => by
        obtain ⟨Y, _, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _
      calc _ ≤ (Λ1 * X ^ (6 * r)) ^ u.length * (Λ1 * X ^ (6 * r)) ^ v.length :=
            mul_le_mul hPu hPv (List.prod_nonneg fun y hy => by
              obtain ⟨Y, _, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _) (by positivity)
        _ = (Λ1 * X ^ (6 * r)) ^ (u.length + v.length) := by rw [pow_add]
        _ ≤ (Λ1 * X ^ (6 * r)) ^ m := pow_le_pow_right₀ hΛX hl
    exact real_step X (gN (Matrix.of p.1.2)) (gN (Matrix.of p.2.2)) C4 Λ1 A A1 β _ m r hX1 hC4
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (Orb.n_mem_G hn)) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (Orb.n_mem_G hn')) hG1 hG2 hβ0 hβA
      hA1_def hΛ1 hP

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.nnMaj`.
-/
theorem Formalism.FourierDecayAlt.P.WeakDominationMajorants.unipotent_majorant : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.nnMaj

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.jf_jDom_of_nnMaj Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.nnMaj`.
-/
theorem Formalism.FourierDecayAlt.P.bessel_integral_domain : Formalism.FourierDecayAlt.JF.JDom :=
  Formalism.FourierDecayAlt.P.jf_jDom_of_nnMaj Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.nnMaj

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.jf_jConv_of_nnMaj Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.nnMaj`.
-/
theorem Formalism.FourierDecayAlt.P.bessel_integral_converges : Formalism.FourierDecayAlt.JF.JConv :=
  Formalism.FourierDecayAlt.P.jf_jConv_of_nnMaj Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.nnMaj

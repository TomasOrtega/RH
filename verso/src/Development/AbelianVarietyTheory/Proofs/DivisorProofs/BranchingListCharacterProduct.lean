import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare.Shift

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

/- English proof (translation)
Establish `h1 : lam.detShift = lam.w (Fin.last n)`. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos (Nat.succ_pos n)]`. Both sides reduce to the same expression. Establish `h2` using `lam.anti (Fin.le_last a)`.

Unfold `DomWeight.natW`. Rewrite using `[h1]`. Use linear arithmetic over natural numbers and integers.
-/
theorem natW_top (lam : DomWeight (n + 1)) (a : Fin (n + 1)) :
    (lam.natW a : ℤ) = lam.w a - lam.w (Fin.last n) := by
  have h1 : lam.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dif_pos (Nat.succ_pos n)]
    rfl
  have h2 := lam.anti (Fin.le_last a)
  unfold DomWeight.natW
  rw [h1]
  omega

/- English proof (translation)
Unfold `lamZ`. Use `split_ifs with h`. Conclude with `natW_top lam a`. Establish `: a = Fin.last n` using `Fin.ext (by have := a.2; simp; omega)`. Simplify using `[this]`.
-/
theorem lamZ_lamN (lam : DomWeight (n + 1)) (a : Fin (n + 1)) :
    lamZ (lamN lam) a = lam.w a - lam.w (Fin.last n) := by
  unfold lamZ
  split_ifs with h
  · exact natW_top lam a
  · have : a = Fin.last n := Fin.ext (by have := a.2; simp; omega)
    simp [this]

/- English proof (translation)
The claim follows from `natW_top lam _`.
-/
theorem lamN_cast (lam : DomWeight (n + 1)) (i : Fin n) :
    (lamN lam i : ℤ) = lam.w i.castSucc - lam.w (Fin.last n) := natW_top lam _

/- English proof (translation)
Rewrite using `[← lamZ_lamN]`. Unfold `nuNext lamZ`. Simplify using `only [Fin.val_succ]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem nuNext_cast (lam : DomWeight (n + 1)) (i : Fin n) :
    (nuNext (lamN lam) i : ℤ) = lam.w i.succ - lam.w (Fin.last n) := by
  rw [← lamZ_lamN]
  unfold nuNext lamZ
  simp only [Fin.val_succ]
  split_ifs <;> rfl

/- English proof (translation)
Establish `hi` using `i.2`. Establish `h0 : 0 < n` using `by omega`. Establish `h1 : sg.detShift = lam.w (Fin.last n)`. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos h0]`.

Conclude with `hE _ (by simp only; omega)`. Establish `h2 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i` using `sg.anti (by rw [Fin.le_def]; simp only; omega)`. Rewrite `h2` using `[hE ⟨n - 1, by omega⟩ (by simp only; omega)]`. Unfold `DomWeight.natW`. Rewrite using `[h1]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem natW_low (hE : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg) (i : Fin n) :
    (sg.natW i : ℤ) = sg.w i - lam.w (Fin.last n) := by
  have hi := i.2
  have h0 : 0 < n := by omega
  have h1 : sg.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dif_pos h0]
    exact hE _ (by simp only; omega)
  have h2 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i := sg.anti (by rw [Fin.le_def]; simp only; omega)
  rw [hE ⟨n - 1, by omega⟩ (by simp only; omega)] at h2
  unfold DomWeight.natW
  rw [h1]
  omega

/- English proof (translation)
Unfold `Formalism.BranchingDeterminantCap.d0 GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.dZero`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [lamZ_lamN, natW_low hE]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem d0_eq (hE : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg) :
    Formalism.BranchingDeterminantCap.d0 (lamZ (lamN lam)) (fun i => (sg.natW i : ℤ)) = GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.dZero lam sg := by
  unfold Formalism.BranchingDeterminantCap.d0 GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.dZero
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [lamZ_lamN, natW_low hE]
  ring

/- English proof (translation)
Unfold `initMinor incl`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using the standard rewrite rules.
-/
theorem rename_initMinor (K : Type) [Field K] {s : ℕ} (I : Fin s → Fin (n + 1)) (hs : s ≤ n) :
    incl K n (initMinor K I hs) = initMinor K I (hs.trans (Nat.le_succ n)) := by
  unfold initMinor incl
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp

end GlobalTheory.BrCompare.Shift

open GlobalTheory.BrCompare.Shift in

/- English proof (translation)
Introduce `n lam sg hI hE`. Establish `hb : ∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s`. Introduce `s`. Establish `h1` using `lamN_cast lam s`. Establish `h2` using `natW_low hE s`.

Establish `h3 : Formalism.L2.Col.Br.bBr rfl lam sg s = lam.w s.castSucc - sg.w s` using `rfl`. Rewrite using `[h3]`. Use linear arithmetic over natural numbers and integers. Establish `ha : ∀ s, (Formalism.L2.Col.Br.aBr rfl lam sg s).toNat = sg.natW s - nuNext (lamN lam) s`. Introduce `s`.

Establish `h1` using `nuNext_cast lam s`. Establish `h2` using `natW_low hE s`. Establish `h3 : Formalism.L2.Col.Br.aBr rfl lam sg s = sg.w s - lam.w s.succ` using `rfl`. Rewrite using `[h3]`. Use linear arithmetic over natural numbers and integers.

Use `⟨?_, ?_, ?_, hb, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `hI i` as an intermediate fact. Simplify using `only [lamZ_lamN, natW_low hE]`. Use linear arithmetic over natural numbers and integers.

Introduce `u hu`. Simplify using `only [bmList, List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_erase, rset, d0_eq hE, Finset.mem_Icc] at hu`. Simplify using `only [lamZ_lamN, natW_low hE] at hu`. Take `⟨i, -, v, ⟨h1, h2, h3⟩, rfl⟩` from `hu`. Simplify using `only [zList, List.mem_flatten, List.mem_ofFn]`.

Use `⟨_, ⟨i, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [List.mem_map, Finset.mem_toList, Finset.mem_erase, GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.rangeSet, Finset.mem_Icc]`. Conclude with `⟨v + lam.w (Fin.last n), ⟨by omega, by omega, by omega⟩, by ring⟩`. Unfold `zList Formalism.L2.Col.Br.cBr`. Rewrite using `[List.map_flatten, List.prod_flatten, List.map_map, List.map_ofFn, List.prod_ofFn]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_def, List.map_map, Finset.prod_map_toList]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Unfold `bmChi`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `h1` using `lamN_cast lam j`. Establish `h2` using `natW_low hE j`. Establish `h3` using `hI j`. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Introduce `K _`. Unfold `Formalism.L2.Col.Br.xiBr xiB`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_pow, rename_initMinor, rename_initMinor, ha, hb]`.

Use `congr 2`.
-/
theorem GlobalTheory.BrCompare.shifted_branching_list_character : ∀ (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → Formalism.BranchingDeterminantCap.Interlace (lamZ (lamN lam)) (fun i => (sg.natW i : ℤ)) ∧ (∀ u ∈ bmList (lamN lam) sg.natW, u ∈ zList lam sg) ∧ ((zList lam sg).map (bmChi (lamN lam) fun s => ((lamN lam s - sg.natW s : ℕ) : ℤ))).prod = Formalism.L2.Col.Br.cBr rfl lam sg ∧ (∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s) ∧ ∀ (K : Type) [Field K], Formalism.L2.Col.Br.xiBr K rfl lam sg = incl K n (xiB K (lamN lam) sg.natW) := by
  intro n lam sg hI hE
  have hb : ∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s := by
    intro s
    have h1 := lamN_cast lam s
    have h2 := natW_low hE s
    have h3 : Formalism.L2.Col.Br.bBr rfl lam sg s = lam.w s.castSucc - sg.w s := rfl
    rw [h3]
    omega
  have ha : ∀ s, (Formalism.L2.Col.Br.aBr rfl lam sg s).toNat = sg.natW s - nuNext (lamN lam) s := by
    intro s
    have h1 := nuNext_cast lam s
    have h2 := natW_low hE s
    have h3 : Formalism.L2.Col.Br.aBr rfl lam sg s = sg.w s - lam.w s.succ := rfl
    rw [h3]
    omega
  refine ⟨?_, ?_, ?_, hb, ?_⟩
  · intro i
    have := hI i
    simp only [lamZ_lamN, natW_low hE]
    omega
  · intro u hu
    simp only [bmList, List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_erase, rset, d0_eq hE,
      Finset.mem_Icc] at hu
    simp only [lamZ_lamN, natW_low hE] at hu
    obtain ⟨i, -, v, ⟨h1, h2, h3⟩, rfl⟩ := hu
    simp only [zList, List.mem_flatten, List.mem_ofFn]
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_erase, GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.rangeSet, Finset.mem_Icc]
    exact ⟨v + lam.w (Fin.last n), ⟨by omega, by omega, by omega⟩, by ring⟩
  · unfold zList Formalism.L2.Col.Br.cBr
    rw [List.map_flatten, List.prod_flatten, List.map_map, List.map_ofFn, List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_def, List.map_map, Finset.prod_map_toList]
    refine Finset.prod_congr rfl fun v _ => ?_
    unfold bmChi
    refine Finset.prod_congr rfl fun j _ => ?_
    have h1 := lamN_cast lam j
    have h2 := natW_low hE j
    have h3 := hI j
    simp only
    omega
  · intro K _
    unfold Formalism.L2.Col.Br.xiBr xiB
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_pow, rename_initMinor, rename_initMinor, ha, hb]
    congr 2

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.Tope

noncomputable section

namespace GlobalTheory.CompanionTheory.RealCountG.DomA

variable {n : ℕ}

def phw (w : Fin n → ℤ) : (Fin n → ℤ) →+ ℤ where
  toFun μ := ∑ a, w a * μ a
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phw_apply (w μ : Fin n → ℤ) : phw w μ = ∑ a, w a * μ a := rfl

/- English proof (translation)
Set `D : (Fin n → ℤ) → Lex (ℤ × Lex (Fin n → ℤ))` to `fun μ => toLex (φ μ, toLex μ)`. Establish `hD : Function.Injective D`. Introduce `x y h`. Use `congrArg (fun z => ofLex (ofLex z).2) h` as an intermediate fact. Simplify `this` using `[D]`.

Establish `hadd : ∀ x y, D (x + y) = D x + D y`. Introduce `x y`. Use `show toLex (φ (x + y), toLex (x + y)) = toLex (φ x, toLex x) + toLex (φ y, toLex y)`. Rewrite using `[map_add]`. Both sides reduce to the same expression.

Establish `hmono : ∀ x y, D x ≤ D y → φ x ≤ φ y`. Introduce `x y h`. Break down `Prod.Lex.toLex_le_toLex.1 h with h | h` into its components or cases. Use `exacts [h.le, h.1.le]`. Establish `hf' : f.coeff.support.Nonempty` using `by simpa [Finsupp.support_nonempty_iff] using hf`.

Establish `hg' : g.coeff.support.Nonempty` using `by simpa [Finsupp.support_nonempty_iff] using hg`. Take `⟨a, ha, hamax⟩` from `Finset.exists_max_image f.coeff.support D hf'`. Take `⟨b, hb, hbmax⟩` from `Finset.exists_max_image g.coeff.support D hg'`. Establish `hc : (f * g).coeff (a + b) = f.coeff a * g.coeff b`. Rewrite using `[AddMonoidAlgebra.coeff_mul]`.

Simplify using `only [Finsupp.sum]`. Rewrite using `[Finset.sum_eq_single a]`. Rewrite using `[Finset.sum_eq_single b]`. Rewrite using `[if_pos rfl]`. Introduce `y _ hne`.

Rewrite using `[if_neg]`. Introduce `he`. Conclude with `hne (add_left_cancel he)`. Introduce `h`. Rewrite using `[Finsupp.notMem_support_iff.1 h]`.

Simplify using the standard rewrite rules. Introduce `x hx hne`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `y hy`. Rewrite using `[if_neg]`.

Introduce `he`. Establish `h1 : D x < D a` using `lt_of_le_of_ne (hamax x hx) (hD.ne hne)`. Establish `h2 : D y ≤ D b` using `hbmax y hy`. Establish `h3 : D (x + y) < D (a + b)`. Rewrite using `[hadd, hadd]`.

Conclude with `add_lt_add_of_lt_of_le h1 h2`. Conclude with `h3.ne (congrArg D he)`. Introduce `h`. Rewrite using `[Finsupp.notMem_support_iff.1 h]`. Simplify using the standard rewrite rules.

Use `⟨a, b, Finsupp.mem_support_iff.1 ha, Finsupp.mem_support_iff.1 hb, ?_, fun x hx => hmono _ _ (hamax x (Finsupp.mem_support_iff.2 hx)), fun y hy => hmono _ _ (hbmax y (Finsupp.mem_support_iff.2 hy))⟩` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `mul_ne_zero (Finsupp.mem_support_iff.1 ha) (Finsupp.mem_support_iff.1 hb)`.
-/
theorem exists_top_add (φ : (Fin n → ℤ) →+ ℤ) (f g : LP n) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ a b, f.coeff a ≠ 0 ∧ g.coeff b ≠ 0 ∧ (f * g).coeff (a + b) ≠ 0 ∧
      (∀ x, f.coeff x ≠ 0 → φ x ≤ φ a) ∧ (∀ y, g.coeff y ≠ 0 → φ y ≤ φ b) := by
  classical
  let D : (Fin n → ℤ) → Lex (ℤ × Lex (Fin n → ℤ)) := fun μ => toLex (φ μ, toLex μ)
  have hD : Function.Injective D := by
    intro x y h
    have := congrArg (fun z => ofLex (ofLex z).2) h
    simpa [D] using this
  have hadd : ∀ x y, D (x + y) = D x + D y := by
    intro x y
    show toLex (φ (x + y), toLex (x + y)) = toLex (φ x, toLex x) + toLex (φ y, toLex y)
    rw [map_add]; rfl
  have hmono : ∀ x y, D x ≤ D y → φ x ≤ φ y := by
    intro x y h
    rcases Prod.Lex.toLex_le_toLex.1 h with h | h
    exacts [h.le, h.1.le]
  have hf' : f.coeff.support.Nonempty := by simpa [Finsupp.support_nonempty_iff] using hf
  have hg' : g.coeff.support.Nonempty := by simpa [Finsupp.support_nonempty_iff] using hg
  obtain ⟨a, ha, hamax⟩ := Finset.exists_max_image f.coeff.support D hf'
  obtain ⟨b, hb, hbmax⟩ := Finset.exists_max_image g.coeff.support D hg'
  have hc : (f * g).coeff (a + b) = f.coeff a * g.coeff b := by
    rw [AddMonoidAlgebra.coeff_mul]
    simp only [Finsupp.sum]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · rw [if_pos rfl]
      · intro y _ hne
        rw [if_neg]
        intro he
        exact hne (add_left_cancel he)
      · intro h
        rw [Finsupp.notMem_support_iff.1 h]
        simp
    · intro x hx hne
      apply Finset.sum_eq_zero
      intro y hy
      rw [if_neg]
      intro he
      have h1 : D x < D a := lt_of_le_of_ne (hamax x hx) (hD.ne hne)
      have h2 : D y ≤ D b := hbmax y hy
      have h3 : D (x + y) < D (a + b) := by
        rw [hadd, hadd]; exact add_lt_add_of_lt_of_le h1 h2
      exact h3.ne (congrArg D he)
    · intro h
      rw [Finsupp.notMem_support_iff.1 h]
      simp
  refine ⟨a, b, Finsupp.mem_support_iff.1 ha, Finsupp.mem_support_iff.1 hb, ?_,
    fun x hx => hmono _ _ (hamax x (Finsupp.mem_support_iff.2 hx)),
    fun y hy => hmono _ _ (hbmax y (Finsupp.mem_support_iff.2 hy))⟩
  rw [hc]
  exact mul_ne_zero (Finsupp.mem_support_iff.1 ha) (Finsupp.mem_support_iff.1 hb)

def Bd (φ : (Fin n → ℤ) →+ ℤ) (f : LP n) (B : ℤ) : Prop := ∀ ν, f.coeff ν ≠ 0 → φ ν ≤ B

/- English proof (translation)
Introduce `ν hν` and use `(h ν hν).trans hBC`.
-/
theorem Bd.mono {φ : (Fin n → ℤ) →+ ℤ} {f : LP n} {B C : ℤ} (h : Bd φ f B) (hBC : B ≤ C) : Bd φ f C :=
  fun ν hν => (h ν hν).trans hBC

/- English proof (translation)
Introduce `ν hν`. Rewrite `hν` using `[AddMonoidAlgebra.coeff_mul, Finsupp.sum]`. Take `⟨x, hx, hx'⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hν`. Rewrite `hx'` using `[Finsupp.sum]`. Take `⟨y, hy, hy'⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hx'`.

Distinguish the cases in `he : x + y = ν`. Rewrite using `[← he, map_add]`. Conclude with `add_le_add (hf x (Finsupp.mem_support_iff.1 hx)) (hg y (Finsupp.mem_support_iff.1 hy))`. Conclude with `absurd (if_neg he) hy'`.
-/
theorem Bd.mul {φ : (Fin n → ℤ) →+ ℤ} {f g : LP n} {B C : ℤ} (hf : Bd φ f B) (hg : Bd φ g C) :
    Bd φ (f * g) (B + C) := by
  classical
  intro ν hν
  rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum] at hν
  obtain ⟨x, hx, hx'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hν
  rw [Finsupp.sum] at hx'
  obtain ⟨y, hy, hy'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx'
  by_cases he : x + y = ν
  · rw [← he, map_add]
    exact add_le_add (hf x (Finsupp.mem_support_iff.1 hx)) (hg y (Finsupp.mem_support_iff.1 hy))
  · exact absurd (if_neg he) hy'

/- English proof (translation)
Introduce `ν hν`. Rewrite `hν` using `[AddMonoidAlgebra.coeff_add, Finsupp.add_apply]`. Distinguish the cases in `h : f.coeff ν = 0`. Rewrite `hν` using `[h, zero_add]`. Conclude with `hg ν hν`.

Conclude with `hf ν h`.
-/
theorem Bd.add {φ : (Fin n → ℤ) →+ ℤ} {f g : LP n} {B : ℤ} (hf : Bd φ f B) (hg : Bd φ g B) :
    Bd φ (f + g) B := by
  intro ν hν
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hν
  by_cases h : f.coeff ν = 0
  · rw [h, zero_add] at hν; exact hg ν hν
  · exact hf ν h

/- English proof (translation)
Introduce `ν hν`. Rewrite `hν` using `[AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `hf ν (right_ne_zero_of_mul hν)`.
-/
theorem Bd.smul {φ : (Fin n → ℤ) →+ ℤ} {f : LP n} {B : ℤ} (c : ℂ) (hf : Bd φ f B) : Bd φ (c • f) B := by
  intro ν hν
  rw [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at hν
  exact hf ν (right_ne_zero_of_mul hν)

/- English proof (translation)
Introduce `ν hν`. Rewrite `hν` using `[AddMonoidAlgebra.coeff_single, Finsupp.single_apply]`. Distinguish the cases in `h : m = ν`. Rewrite using `[h]`. Conclude with `absurd (if_neg h) hν`.
-/
theorem bd_single (φ : (Fin n → ℤ) →+ ℤ) (m : Fin n → ℤ) (r : ℂ) :
    Bd φ (AddMonoidAlgebra.single m r) (φ m) := by
  classical
  intro ν hν
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at hν
  by_cases h : m = ν
  · rw [h]
  · exact absurd (if_neg h) hν

/- English proof (translation)
Introduce `ν hν`. Rewrite `hν` using `[AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]`. Take `⟨i, hi, hi'⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hν`. Conclude with `h i hi ν hi'`.
-/
theorem Bd.sum {ι : Type*} {φ : (Fin n → ℤ) →+ ℤ} (s : Finset ι) (F : ι → LP n) {B : ℤ}
    (h : ∀ i ∈ s, Bd φ (F i) B) : Bd φ (∑ i ∈ s, F i) B := by
  intro ν hν
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply] at hν
  obtain ⟨i, hi, hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hν
  exact h i hi ν hi'

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.prod_empty, Finset.sum_empty, AddMonoidAlgebra.one_def]`. Simplify using `using bd_single φ 0 (1 : ℂ)`. Consider the case `insert i s hi ih`.

Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi]`. Conclude with `(h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem Bd.prod {ι : Type*} {φ : (Fin n → ℤ) →+ ℤ} (s : Finset ι) (F : ι → LP n) (B : ι → ℤ)
    (h : ∀ i ∈ s, Bd φ (F i) (B i)) : Bd φ (∏ i ∈ s, F i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, AddMonoidAlgebra.one_def]
    simpa using bd_single φ 0 (1 : ℂ)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end GlobalTheory.CompanionTheory.RealCountG.DomA

namespace GlobalTheory.CompanionTheory.RealCountG.DomA

variable {n : ℕ}

/- English proof (translation)
Unfold `altL`. Use `Bd.sum _ _ fun σ _ => ?_` and prove the remaining obligations. Use `Bd.smul _ ((bd_single _ _ _).mono ?_)` and prove the remaining obligations. Simplify using `only [phw_apply]`. Conclude with `Monovary.sum_mul_comp_perm_le_sum_mul (Antitone.monovary hw hm)`.
-/
theorem bd_altL (w m : Fin n → ℤ) (hw : Antitone w) (hm : Antitone m) :
    Bd (phw w) (altL m) (phw w m) := by
  unfold altL
  refine Bd.sum _ _ fun σ _ => ?_
  refine Bd.smul _ ((bd_single _ _ _).mono ?_)
  simp only [phw_apply]
  exact Monovary.sum_mul_comp_perm_le_sum_mul (Antitone.monovary hw hm)

/- English proof (translation)
Simplify using `[phw_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem phw_single_sub (w : Fin n → ℤ) (a b : Fin n) :
    phw w (Pi.single a 1 - Pi.single b 1) = w a - w b := by
  classical
  simp [phw_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Unfold `pPL`. Use `Bd.prod _ _ _ fun a _ => Bd.prod _ _ _ fun b _ => ?_` and prove the remaining obligations. Use `Bd.add ?_ ?_` and prove the remaining obligations. Rewrite using `[AddMonoidAlgebra.one_def]`. Conclude with `(bd_single _ _ _).mono (by simp)`.

Conclude with `(bd_single _ _ _).mono (by rw [phw_single_sub]; exact le_max_right _ _)`.
-/
theorem bd_pPL (w : Fin n → ℤ) :
    Bd (phw w) (pPL n) (∑ a, ∑ b, max 0 (w a - w b)) := by
  unfold pPL
  refine Bd.prod _ _ _ fun a _ => Bd.prod _ _ _ fun b _ => ?_
  refine Bd.add ?_ ?_
  · rw [AddMonoidAlgebra.one_def]
    exact (bd_single _ _ _).mono (by simp)
  · exact (bd_single _ _ _).mono (by rw [phw_single_sub]; exact le_max_right _ _)

/- English proof (translation)
Introduce `i j hij`. Simplify using `only [delZ]`. Establish `: (i : ℕ) ≤ j` using `hij`. Conclude with `Nat.sub_le_sub_left this _` after adjusting the coercions.
-/
theorem delZ_antitone : Antitone (delZ n) := by
  intro i j hij
  simp only [delZ]
  have : (i : ℕ) ≤ j := hij
  exact_mod_cast Nat.sub_le_sub_left this _

/- English proof (translation)
Introduce `i j h`. Simplify using `only [delZ, Nat.cast_inj] at h`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Use `ext`.

Use linear arithmetic over natural numbers and integers.
-/
theorem delZ_injective : Function.Injective (delZ n) := by
  intro i j h
  simp only [delZ, Nat.cast_inj] at h
  have hi := i.isLt
  have hj := j.isLt
  ext; omega

/- English proof (translation)
Unfold `altL`. Rewrite using `[AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]`. Simplify using the standard rewrite rules. Introduce `σ _ hσ`. Rewrite using `[AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg, smul_zero]`.

Introduce `he`. Apply `hσ` to reduce the goal to its premises. Use extensionality with `i`. Use `congrFun he i` as an intermediate fact. Conclude with `congrArg Fin.val (delZ_injective this)`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem coeff_altL_delZ : (altL (delZ n)).coeff (delZ n) = 1 := by
  classical
  unfold altL
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp
  · intro σ _ hσ
    rw [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      if_neg, smul_zero]
    intro he
    apply hσ
    ext i
    have := congrFun he i
    exact congrArg Fin.val (delZ_injective this)
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use `set φ := phw w`. Establish `hA1 : (altL (delZ n)).coeff (delZ n) ≠ 0` using `by rw [coeff_altL_delZ]; exact one_ne_zero`. Establish `hA1ne : altL (delZ n) ≠ 0`. Introduce `h0`. Rewrite `hA1` using `[h0]`.

Conclude with `hA1 rfl`. Establish `hp : p ≠ 0`. Introduce `h0`. Rewrite `hμ` using `[h0]`. Conclude with `hμ rfl`.

Take `⟨a, b, _, _, hab, hamax, hbmax⟩` from `exists_top_add φ p (altL (delZ n)) hp hA1ne`. Establish `hpA : p * altL (delZ n) ≠ 0`. Introduce `h0`. Rewrite `hab` using `[h0]`. Conclude with `hab rfl`.

Take `⟨c, d, _, _, hcd, hcmax, hdmax⟩` from `exists_top_add φ _ _ hpA hA1ne`. Establish `hR : (pPL n * altL (lam + delZ n) ^ 2).coeff (c + d) ≠ 0`. Rewrite using `[← h, sq, ← mul_assoc]`. Conclude with `hcd`. Establish `hB : Bd φ (pPL n * altL (lam + delZ n) ^ 2) ((∑ a, ∑ b, max 0 (w a - w b)) + (φ (lam + delZ n) + φ (lam + delZ n)))`.

Rewrite using `[sq]`. Conclude with `(bd_pPL w).mul ((bd_altL w _ hw (hlam.add delZ_antitone)).mul (bd_altL w _ hw (hlam.add delZ_antitone)))`. Establish `e1` using `hB _ hR`. Establish `e2` using `hamax μ hμ`. Establish `e3` using `hcmax _ hab`.

Establish `e4` using `hbmax _ hA1`. Establish `e5` using `hdmax _ hA1`. Rewrite `e1`, `e3` using `[map_add]`. Rewrite `e1` using `[map_add]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem phw_le (w : Fin n → ℤ) (hw : Antitone w) (lam : Fin n → ℤ) (hlam : Antitone lam) (p : LP n)
    (h : p * altL (delZ n) ^ 2 = pPL n * altL (lam + delZ n) ^ 2) (μ : Fin n → ℤ) (hμ : p.coeff μ ≠ 0) :
    phw w μ ≤ (∑ a, ∑ b, max 0 (w a - w b)) + 2 * phw w lam := by
  set φ := phw w
  have hA1 : (altL (delZ n)).coeff (delZ n) ≠ 0 := by rw [coeff_altL_delZ]; exact one_ne_zero
  have hA1ne : altL (delZ n) ≠ 0 := by
    intro h0; rw [h0] at hA1; exact hA1 rfl
  have hp : p ≠ 0 := by
    intro h0; rw [h0] at hμ; exact hμ rfl
  obtain ⟨a, b, _, _, hab, hamax, hbmax⟩ := exists_top_add φ p (altL (delZ n)) hp hA1ne
  have hpA : p * altL (delZ n) ≠ 0 := by
    intro h0; rw [h0] at hab; exact hab rfl
  obtain ⟨c, d, _, _, hcd, hcmax, hdmax⟩ := exists_top_add φ _ _ hpA hA1ne
  have hR : (pPL n * altL (lam + delZ n) ^ 2).coeff (c + d) ≠ 0 := by
    rw [← h, sq, ← mul_assoc]; exact hcd
  have hB : Bd φ (pPL n * altL (lam + delZ n) ^ 2)
      ((∑ a, ∑ b, max 0 (w a - w b)) + (φ (lam + delZ n) + φ (lam + delZ n))) := by
    rw [sq]
    exact (bd_pPL w).mul ((bd_altL w _ hw (hlam.add delZ_antitone)).mul
      (bd_altL w _ hw (hlam.add delZ_antitone)))
  have e1 := hB _ hR
  have e2 := hamax μ hμ
  have e3 := hcmax _ hab
  have e4 := hbmax _ hA1
  have e5 := hdmax _ hA1
  rw [map_add] at e1 e3
  rw [map_add] at e1
  linarith

end GlobalTheory.CompanionTheory.RealCountG.DomA

namespace GlobalTheory.CompanionTheory.RealCountG.DomA

variable {n : ℕ}

def wk (k : ℕ) : Fin n → ℤ := fun a => if (a : ℕ) < k then 1 else 0

/- English proof (translation)
Introduce `i j hij`. Establish `: (i : ℕ) ≤ j` using `hij`. Simplify using `only [wk]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem wk_antitone (k : ℕ) : Antitone (wk (n := n) k) := by
  intro i j hij
  have : (i : ℕ) ≤ j := hij
  simp only [wk]
  split_ifs <;> omega

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ, ih.1, ih.2]`. Distinguish the cases in `hN : N < k`.

Rewrite using `[if_pos hN, min_eq_left hN.le, min_eq_left (Nat.succ_le_of_lt hN)]`. Use `push_cast`. Apply the tactic sequence `constructor <;> ring`. Rewrite `hN` using `[if_neg hN] push_neg`. Rewrite using `[min_eq_right hN, min_eq_right (by omega)]`.

Simplify using the standard rewrite rules.
-/
theorem range_sums (k N : ℕ) :
    ∑ i ∈ range N, (if i < k then (1 : ℤ) else 0) = ((min N k : ℕ) : ℤ) ∧
      ∑ i ∈ range N, (if i < k then (1 : ℤ) else 0) * (1 + 2 * (i : ℤ)) = ((min N k : ℕ) : ℤ) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih.1, ih.2]
    by_cases hN : N < k
    · rw [if_pos hN, min_eq_left hN.le, min_eq_left (Nat.succ_le_of_lt hN)]
      push_cast
      constructor <;> ring
    · rw [if_neg hN]
      push_neg at hN
      rw [min_eq_right hN, min_eq_right (by omega)]
      simp

/- English proof (translation)
Establish `h1 : ∀ a b : Fin n, max 0 (wk k a - wk k b) = wk k a * (1 - wk k b)`. Apply the tactic sequence `intro a b; simp only [wk]; split_ifs <;> norm_num`. Establish `h2 : ∀ a : Fin n, wk k a * ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)) = (n : ℤ) * wk k a - wk k a * (1 + 2 * ((a : ℕ) : ℤ))`. Introduce `a`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[h1, h2]`. Rewrite using `[← Finset.sum_mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]`. Establish `hU : ∑ a : Fin n, wk k a = ((min n k : ℕ) : ℤ)`. Rewrite using `[← (range_sums k n).1]`. Conclude with `Fin.sum_univ_eq_sum_range (fun i => if i < k then (1 : ℤ) else 0) n`.

Establish `hV : ∑ a : Fin n, wk k a * (1 + 2 * ((a : ℕ) : ℤ)) = ((min n k : ℕ) : ℤ) ^ 2`. Rewrite using `[← (range_sums k n).2]`. Conclude with `Fin.sum_univ_eq_sum_range (fun i => (if i < k then (1 : ℤ) else 0) * (1 + 2 * (i : ℤ))) n`. Rewrite using `[hU, hV]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_max_eq (k : ℕ) :
    ∑ a : Fin n, ∑ b : Fin n, max 0 (wk k a - wk k b) = ∑ a : Fin n, wk k a * ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)) := by
  have h1 : ∀ a b : Fin n, max 0 (wk k a - wk k b) = wk k a * (1 - wk k b) := by
    intro a b; simp only [wk]; split_ifs <;> norm_num
  have h2 : ∀ a : Fin n, wk k a * ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)) =
      (n : ℤ) * wk k a - wk k a * (1 + 2 * ((a : ℕ) : ℤ)) := by
    intro a; ring
  simp_rw [h1, h2]
  rw [← Finset.sum_mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hU : ∑ a : Fin n, wk k a = ((min n k : ℕ) : ℤ) := by
    rw [← (range_sums k n).1]
    exact Fin.sum_univ_eq_sum_range (fun i => if i < k then (1 : ℤ) else 0) n
  have hV : ∑ a : Fin n, wk k a * (1 + 2 * ((a : ℕ) : ℤ)) = ((min n k : ℕ) : ℤ) ^ 2 := by
    rw [← (range_sums k n).2]
    exact Fin.sum_univ_eq_sum_range (fun i => (if i < k then (1 : ℤ) else 0) * (1 + 2 * (i : ℤ))) n
  rw [hU, hV]
  simp
  ring

end GlobalTheory.CompanionTheory.RealCountG.DomA

namespace GlobalTheory.CompanionTheory.RealCountG.DomA

/- English proof (translation)
Introduce `n lam hlam p h μ hμ`. Establish `hpart : ∀ k : ℕ, ∑ a, wk k a * μ a ≤ ∑ a, wk k a * (2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)))`. Introduce `k`. Use `phw_le (wk k) (wk_antitone k) lam hlam p h μ hμ` as an intermediate fact. Rewrite `this` using `[sum_max_eq, phw_apply, phw_apply]`.

Establish `e : ∑ a : Fin n, wk k a * (2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ))) = ∑ a : Fin n, wk k a * ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)) + 2 * ∑ a : Fin n, wk k a * lam a`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfilt : ∀ (k : ℕ) (x : Fin n → ℤ), ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), (x a : ℝ) = ((∑ a, wk k a * x a : ℤ) : ℝ)`.

Introduce `k x`. Rewrite using `[Finset.sum_filter]`. Use `push_cast`. Apply the tactic sequence `exact Finset.sum_congr rfl fun a _ => by simp only [wk]; split_ifs <;> simp`. Establish `hm0 : ∀ a, m0 lam a = ((2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)) : ℤ) : ℝ)`.

Introduce `a`. Simplify using `only [m0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hw1 : ∀ a : Fin n, wk n a = 1` using `fun a => if_pos a.isLt`.

Establish `htot : ∑ a : Fin n, ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)) = 0`. Use `sum_max_eq (n := n) n` as an intermediate fact. Simplify using `only [hw1, sub_self, max_self, Finset.sum_const_zero, one_mul] at this`. Conclude with `this.symm`. Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations.

Establish `e1` using `hfilt k μ`. Establish `e2` using `hfilt k (fun a => 2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)))`. Simplify using `only [wtR, hm0]`. Rewrite using `[e1, e2]`. Conclude with `hpart k` after adjusting the coercions.

Establish `hup` using `hpart n`. Simplify using `only [hw1, one_mul] at hup`. Establish `hlow` using `phw_le (fun _ => (-1 : ℤ)) antitone_const lam hlam p h μ hμ`. Rewrite `hlow` using `[phw_apply, phw_apply]`. Simplify using `only [sub_self, max_self, Finset.sum_const_zero, neg_one_mul, Finset.sum_neg_distrib, zero_add] at hlow`.

Establish `hsum : ∑ a, (2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ))) = 2 * ∑ a, lam a`. Rewrite using `[Finset.sum_add_distrib, htot, Finset.mul_sum, add_zero]`. Establish `heq : ∑ a, μ a = ∑ a, (2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)))` using `le_antisymm hup (by rw [hsum]; linarith)`. Simplify using `only [wtR, hm0]`. Conclude with `heq` after adjusting the coercions.
-/
theorem domLE_of_mul_eq : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ p : LP n,
    p * altL (delZ n) ^ 2 = pPL n * altL (lam + delZ n) ^ 2 →
    ∀ μ, p.coeff μ ≠ 0 → DomLE (wtR μ) (m0 lam) := by
  intro n lam hlam p h μ hμ
  have hpart : ∀ k : ℕ, ∑ a, wk k a * μ a ≤
      ∑ a, wk k a * (2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ))) := by
    intro k
    have := phw_le (wk k) (wk_antitone k) lam hlam p h μ hμ
    rw [sum_max_eq, phw_apply, phw_apply] at this
    have e : ∑ a : Fin n, wk k a * (2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ))) =
        ∑ a : Fin n, wk k a * ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)) + 2 * ∑ a : Fin n, wk k a * lam a := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    linarith
  have hfilt : ∀ (k : ℕ) (x : Fin n → ℤ),
      ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), (x a : ℝ) = ((∑ a, wk k a * x a : ℤ) : ℝ) := by
    intro k x
    rw [Finset.sum_filter]
    push_cast
    exact Finset.sum_congr rfl fun a _ => by simp only [wk]; split_ifs <;> simp
  have hm0 : ∀ a, m0 lam a = ((2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)) : ℤ) : ℝ) := by
    intro a; simp only [m0]; push_cast; ring
  have hw1 : ∀ a : Fin n, wk n a = 1 := fun a => if_pos a.isLt
  have htot : ∑ a : Fin n, ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)) = 0 := by
    have := sum_max_eq (n := n) n
    simp only [hw1, sub_self, max_self, Finset.sum_const_zero, one_mul] at this
    exact this.symm
  refine ⟨fun k => ?_, ?_⟩
  · have e1 := hfilt k μ
    have e2 := hfilt k (fun a => 2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ)))
    simp only [wtR, hm0]
    rw [e1, e2]
    exact_mod_cast hpart k
  · have hup := hpart n
    simp only [hw1, one_mul] at hup
    have hlow := phw_le (fun _ => (-1 : ℤ)) antitone_const lam hlam p h μ hμ
    rw [phw_apply, phw_apply] at hlow
    simp only [sub_self, max_self, Finset.sum_const_zero, neg_one_mul, Finset.sum_neg_distrib, zero_add] at hlow
    have hsum : ∑ a, (2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ))) = 2 * ∑ a, lam a := by
      rw [Finset.sum_add_distrib, htot, Finset.mul_sum, add_zero]
    have heq : ∑ a, μ a = ∑ a, (2 * lam a + ((n : ℤ) - 1 - 2 * ((a : ℕ) : ℤ))) :=
      le_antisymm hup (by rw [hsum]; linarith)
    simp only [wtR, hm0]
    exact_mod_cast heq

end GlobalTheory.CompanionTheory.RealCountG.DomA

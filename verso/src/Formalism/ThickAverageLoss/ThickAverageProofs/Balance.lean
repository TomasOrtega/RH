import Formalism.ThickAverageLoss.PartnersToFactorsAt

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.D5

open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter

namespace Bal

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (translation)
Use `revert e`. Evaluate the decidable proposition.
-/
lemma zmod_two_ne_zero_iff_eq_one (e : ZMod 2) : ¬ e = 0 ↔ e = 1 := by
  revert e
  decide

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma prod_add_fst_fst (x y : E0 × H) : (x + y).1.1 = x.1.1 + y.1.1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma topPl_fst_fst_eq_zero (t : H) : (topPl t).1.1 = 0 := rfl

/- English proof (translation)
Use `show (g + topPl t).1.1 = 0 ↔ g.1.1 = 0`. Rewrite using `[prod_add_fst_fst, topPl_fst_fst_eq_zero, add_zero]`.
-/
lemma inPhi_add_topPl (g : E0 × H) (t : H) : InPhi (g + topPl t) ↔ InPhi g := by
  show (g + topPl t).1.1 = 0 ↔ g.1.1 = 0
  rw [prod_add_fst_fst, topPl_fst_fst_eq_zero, add_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma cconj_fst_fst_eq_one : (cconj : E0 × H).1.1 = 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma prod_sub_fst_fst (x y : E0 × H) : (x - y).1.1 = x.1.1 - y.1.1 := rfl

/- English proof (translation)
Use `Finset.sum_nbij' (fun g => cconj + g + topPl t) (fun ρ => ρ - cconj - topPl t) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `g hg`. Establish `hg' : ¬ InPhi (g + topPl t)` using `(Finset.mem_filter.mp hg).2`. Establish `h1 : ¬ g.1.1 = 0` using `fun h => hg' ((inPhi_add_topPl g t).mpr h)`. Use `show cconj + g + topPl t ∈ PhiSet (H := H)`.

Rewrite using `[PhiSet, Finset.mem_filter]`. Use `⟨Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use `show (cconj + g + topPl t).1.1 = 0`. Rewrite using `[prod_add_fst_fst, prod_add_fst_fst, cconj_fst_fst_eq_one, topPl_fst_fst_eq_zero]`. Use `revert h1`.

Generalize the expression as in `g.1.1 = e`. Use `revert e`. Evaluate the decidable proposition. Introduce `ρ hρ`. Rewrite `hρ` using `[PhiSet, Finset.mem_filter]`.

Establish `h1 : ρ.1.1 = 0` using `hρ.2`. Use `show ρ - cconj - topPl t ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t))`. Rewrite using `[Finset.mem_filter]`. Use `⟨Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Rewrite using `[inPhi_add_topPl]`.

Use `show ¬ (ρ - cconj - topPl t).1.1 = 0`. Rewrite using `[prod_sub_fst_fst, prod_sub_fst_fst, cconj_fst_fst_eq_one, topPl_fst_fst_eq_zero]`. Use `revert h1`. Generalize the expression as in `ρ.1.1 = e`. Use `revert e`.

Evaluate the decidable proposition. Introduce `g _ show cconj + g + topPl t - cconj - topPl t = g`. Normalize the expressions using the abelian group laws. Introduce `ρ _ show cconj + (ρ - cconj - topPl t) + topPl t = ρ`. Normalize the expressions using the abelian group laws.

Introduce `g _`. Both sides reduce to the same expression.
-/
lemma sum_S_rho {β : Type*} [AddCommMonoid β] (t : H) (F : E0 × H → β) :
    ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), F (cconj + g + topPl t)
      = ∑ ρ ∈ PhiSet (H := H), F ρ := by
  refine Finset.sum_nbij' (fun g => cconj + g + topPl t) (fun ρ => ρ - cconj - topPl t) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    have hg' : ¬ InPhi (g + topPl t) := (Finset.mem_filter.mp hg).2
    have h1 : ¬ g.1.1 = 0 := fun h => hg' ((inPhi_add_topPl g t).mpr h)
    show cconj + g + topPl t ∈ PhiSet (H := H)
    rw [PhiSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show (cconj + g + topPl t).1.1 = 0
    rw [prod_add_fst_fst, prod_add_fst_fst, cconj_fst_fst_eq_one, topPl_fst_fst_eq_zero]
    revert h1
    generalize g.1.1 = e
    revert e
    decide
  · intro ρ hρ
    rw [PhiSet, Finset.mem_filter] at hρ
    have h1 : ρ.1.1 = 0 := hρ.2
    show ρ - cconj - topPl t ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t))
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [inPhi_add_topPl]
    show ¬ (ρ - cconj - topPl t).1.1 = 0
    rw [prod_sub_fst_fst, prod_sub_fst_fst, cconj_fst_fst_eq_one, topPl_fst_fst_eq_zero]
    revert h1
    generalize ρ.1.1 = e
    revert e
    decide
  · intro g _
    show cconj + g + topPl t - cconj - topPl t = g
    abel
  · intro ρ _
    show cconj + (ρ - cconj - topPl t) + topPl t = ρ
    abel
  · intro g _
    rfl

/- English proof (translation)
Rewrite using `[Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]`. Conclude with `sum_S_rho t (fun _ => (1 : ℕ))`.
-/
lemma card_S (t : H) :
    (univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t))).card = (PhiSet (H := H)).card := by
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
  exact sum_S_rho t (fun _ => (1 : ℕ))

/- English proof (translation)
Establish `h1 : (univ.filter (fun g : E0 × H => InPhi g)).card + (univ.filter (fun g : E0 × H => ¬ InPhi g)).card = Fintype.card (E0 × H)`. Rewrite using `[Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, ← Finset.card_univ, Finset.card_eq_sum_ones]`. Conclude with `Finset.sum_filter_add_sum_filter_not _ _ _`. Establish `h2 : (univ.filter (fun g : E0 × H => ¬ InPhi g)).card = (PhiSet (H` using `H)).card := by`. Rewrite using `[← card_S (H := H) 0]`.

Use `congr 1`. Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `g _`. Rewrite using `[inPhi_add_topPl]`. Establish `h3 : univ.filter (fun g : E0 × H => InPhi g) = PhiSet (H` using `H) := PhiSet.eq_1.symm`.

Rewrite using `[← h1, h2, h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma card_G_eq : (Fintype.card (E0 × H) : ℂ) = 2 * ((PhiSet (H := H)).card : ℂ) := by
  have h1 : (univ.filter (fun g : E0 × H => InPhi g)).card
      + (univ.filter (fun g : E0 × H => ¬ InPhi g)).card = Fintype.card (E0 × H) := by
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, ← Finset.card_univ, Finset.card_eq_sum_ones]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have h2 : (univ.filter (fun g : E0 × H => ¬ InPhi g)).card = (PhiSet (H := H)).card := by
    rw [← card_S (H := H) 0]
    congr 1
    apply Finset.filter_congr
    intro g _
    rw [inPhi_add_topPl]
  have h3 : univ.filter (fun g : E0 × H => InPhi g) = PhiSet (H := H) := PhiSet.eq_1.symm
  rw [← h1, h2, h3]
  push_cast
  ring

/- English proof (translation)
Establish `hmem : (0 : E0 × H) ∈ PhiSet (H` using `H) := by`. Rewrite using `[PhiSet, Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, rfl⟩`. Conclude with `Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨_, hmem⟩).ne'`.
-/
lemma phiSet_card_ne_zero : ((PhiSet (H := H)).card : ℂ) ≠ 0 := by
  have hmem : (0 : E0 × H) ∈ PhiSet (H := H) := by
    rw [PhiSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  exact Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨_, hmem⟩).ne'

/- English proof (translation)
Rewrite using `[Hs.7, Hs.7]`. Establish `h : (-g).1.1 = g.1.1` using `by show -g.1.1 = g.1.1`. Generalize the expression as in `g.1.1 = e`. Use `revert e`. Evaluate the decidable proposition.

Rewrite using `[h]`.
-/
lemma chC_neg (Hs : CycHost H) (g : E0 × H) : Hs.chC (-g) = Hs.chC g := by
  rw [Hs.7, Hs.7]
  have h : (-g).1.1 = g.1.1 := by
    show -g.1.1 = g.1.1
    generalize g.1.1 = e
    revert e
    decide
  rw [h]

/- English proof (translation)
Use `AddChar.ext _ _ (fun g => ?_)` and prove the remaining obligations. Rewrite using `[AddChar.mul_apply, AddChar.zero_apply, Hs.7, sgn2]`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
lemma chC_mul_self (Hs : CycHost H) : Hs.chC * Hs.chC = 0 := by
  refine AddChar.ext _ _ (fun g => ?_)
  rw [AddChar.mul_apply, AddChar.zero_apply, Hs.7, sgn2]
  split_ifs <;> norm_num

/- English proof (translation)
Rewrite using `[← AddChar.mul_apply, chC_mul_self, AddChar.zero_apply]`.
-/
lemma chC_sq (Hs : CycHost H) (g : E0 × H) : Hs.chC g * Hs.chC g = 1 := by
  rw [← AddChar.mul_apply, chC_mul_self, AddChar.zero_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `AddChar.ext _ _ (fun g => ?_)` and prove the remaining obligations. Establish `h1 : ψ g * Hs.chC g = 1`. Rewrite using `[← AddChar.mul_apply, h, AddChar.zero_apply]`.

Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `rfl`. Conclude with `chC_mul_self Hs`.
-/
lemma mul_chC_eq_zero_iff (Hs : CycHost H) (ψ : AddChar (E0 × H) ℂ) : ψ * Hs.chC = 0 ↔ ψ = Hs.chC := by
  constructor
  · intro h
    refine AddChar.ext _ _ (fun g => ?_)
    have h1 : ψ g * Hs.chC g = 1 := by
      rw [← AddChar.mul_apply, h, AddChar.zero_apply]
    calc ψ g = ψ g * (Hs.chC g * Hs.chC g) := by rw [chC_sq, mul_one]
      _ = (ψ g * Hs.chC g) * Hs.chC g := by ring
      _ = Hs.chC g := by rw [h1, one_mul]
  · rintro rfl
    exact chC_mul_self Hs

/- English proof (translation)
Introduce `h`. Establish `h1 : Hs.chC cconj = 1` using `by rw [h, AddChar.zero_apply]`. Establish `hne : ¬ (1 : ZMod 2) = 0` using `by decide`. Rewrite `h1` using `[Hs.7, cconj_fst_fst_eq_one, sgn2, if_neg hne]`. Evaluate the numerical expressions using `at h1`.
-/
lemma chC_ne_zero (Hs : CycHost H) : Hs.chC ≠ 0 := by
  intro h
  have h1 : Hs.chC cconj = 1 := by rw [h, AddChar.zero_apply]
  have hne : ¬ (1 : ZMod 2) = 0 := by decide
  rw [Hs.7, cconj_fst_fst_eq_one, sgn2, if_neg hne] at h1
  norm_num at h1

/- English proof (translation)
The claim follows from `Equiv.sum_comp (Equiv.neg (E0 × H)) F`.
-/
lemma sum_neg_eq (F : E0 × H → ℂ) : ∑ g : E0 × H, F (-g) = ∑ g, F g := Equiv.sum_comp (Equiv.neg (E0 × H)) F

/- English proof (translation)
Distinguish the cases in `h : g.1.1 = 0`. Establish `hp : InPhi (g + topPl t)` using `(inPhi_add_topPl g t).mpr h`. Rewrite using `[if_neg (not_not.mpr hp), Hs.7, h, sgn2, if_pos rfl]`. Evaluate the numerical expressions. Apply the tactic sequence `try ring`.

Establish `hp : ¬ InPhi (g + topPl t)` using `fun h' => h ((inPhi_add_topPl g t).mp h')`. Rewrite using `[if_pos hp, Hs.7, sgn2, if_neg h]`. Evaluate the numerical expressions. Apply the tactic sequence `try ring`.
-/
private lemma ite_not_inPhi_eq_mul_one_sub_chC_div_two (Hs : CycHost H) (t : H) (g : E0 × H) (x : ℂ) :
    (if ¬ InPhi (g + topPl t) then x else 0) = x * ((1 - Hs.chC g) / 2) := by
  by_cases h : g.1.1 = 0
  · have hp : InPhi (g + topPl t) := (inPhi_add_topPl g t).mpr h
    rw [if_neg (not_not.mpr hp), Hs.7, h, sgn2, if_pos rfl]
    norm_num
    try ring
  · have hp : ¬ InPhi (g + topPl t) := fun h' => h ((inPhi_add_topPl g t).mp h')
    rw [if_pos hp, Hs.7, sgn2, if_neg h]
    norm_num
    try ring

/- English proof (translation)
Establish `e1 : ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ψ (-g) = ∑ g : E0 × H, ψ (-g) * ((1 - Hs.chC g) / 2)`. Rewrite using `[Finset.sum_filter]`. Conclude with `Finset.sum_congr rfl (fun g _ => ite_not_inPhi_eq_mul_one_sub_chC_div_two Hs t g (ψ (-g)))`. Establish `hs0 : ∑ g : E0 × H, ψ (-g) = 0` using `(sum_neg_eq (fun g => ψ g)).trans (AddChar.sum_eq_zero_iff_ne_zero.mpr hψ)`. Establish `hs1 : ∑ g : E0 × H, ψ (-g) * Hs.chC g = ∑ g : E0 × H, (ψ * Hs.chC) g`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsplit : ∑ g : E0 × H, ψ (-g) * ((1 - Hs.chC g) / 2) = (∑ g : E0 × H, ψ (-g) - ∑ g : E0 × H, ψ (-g) * Hs.chC g) / 2`. Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_div]`. Conclude with `Finset.sum_congr rfl (fun g _ => by ring)`. Rewrite using `[e1, hsplit, hs0, hs1]`.

Distinguish the cases in `h : ψ = Hs.chC`. Establish `h' : ψ * Hs.chC = 0` using `(mul_chC_eq_zero_iff Hs ψ).mpr h`. Rewrite using `[h', if_pos h]`. Simplify using `only [AddChar.zero_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]`. Rewrite using `[card_G_eq]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h' : ¬ ψ * Hs.chC = 0` using `fun h'' => h ((mul_chC_eq_zero_iff Hs ψ).mp h'')`. Rewrite using `[AddChar.sum_eq_zero_iff_ne_zero.mpr h', if_neg h]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_S_char (Hs : CycHost H) (t : H) (ψ : AddChar (E0 × H) ℂ) (hψ : ψ ≠ 0) :
    ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ψ (-g)
      = if ψ = Hs.chC then -((PhiSet (H := H)).card : ℂ) else 0 := by
  have e1 : ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ψ (-g)
      = ∑ g : E0 × H, ψ (-g) * ((1 - Hs.chC g) / 2) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun g _ => ite_not_inPhi_eq_mul_one_sub_chC_div_two Hs t g (ψ (-g)))
  have hs0 : ∑ g : E0 × H, ψ (-g) = 0 :=
    (sum_neg_eq (fun g => ψ g)).trans (AddChar.sum_eq_zero_iff_ne_zero.mpr hψ)
  have hs1 : ∑ g : E0 × H, ψ (-g) * Hs.chC g = ∑ g : E0 × H, (ψ * Hs.chC) g := by
    calc ∑ g : E0 × H, ψ (-g) * Hs.chC g = ∑ g : E0 × H, (ψ * Hs.chC) (-g) :=
          Finset.sum_congr rfl (fun g _ => by rw [AddChar.mul_apply, chC_neg])
      _ = ∑ g : E0 × H, (ψ * Hs.chC) g := sum_neg_eq (fun g => (ψ * Hs.chC) g)
  have hsplit : ∑ g : E0 × H, ψ (-g) * ((1 - Hs.chC g) / 2)
      = (∑ g : E0 × H, ψ (-g) - ∑ g : E0 × H, ψ (-g) * Hs.chC g) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl (fun g _ => by ring)
  rw [e1, hsplit, hs0, hs1]
  by_cases h : ψ = Hs.chC
  · have h' : ψ * Hs.chC = 0 := (mul_chC_eq_zero_iff Hs ψ).mpr h
    rw [h', if_pos h]
    simp only [AddChar.zero_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [card_G_eq]
    ring
  · have h' : ¬ ψ * Hs.chC = 0 := fun h'' => h ((mul_chC_eq_zero_iff Hs ψ).mp h'')
    rw [AddChar.sum_eq_zero_iff_ne_zero.mpr h', if_neg h]
    ring

/- English proof (translation)
Rewrite using `[mul_sub, mul_one, div_div, mul_div_assoc', mul_div_mul_left _ _ hw]`.
-/
lemma term_real (a w : ℝ) (hw : w ≠ 0) (n : ℕ) : a / n - w = w * (a / w / n - 1) := by
  rw [mul_sub, mul_one, div_div, mul_div_assoc', mul_div_mul_left _ _ hw]

/- English proof (translation)
Establish `hw0 : w ≠ 0` using `hw.ne'`. Establish `hterm : ∀ n : ℕ, ((a / n - w : ℝ) : ℂ) = (w : ℂ) * ((a / w / n - 1 : ℝ) : ℂ)`. Introduce `n`. Rewrite using `[term_real a w hw0 n, Complex.ofReal_mul]`. Establish `hwaR : w * (a / w) = a`.

Rewrite using `[mul_div_assoc', mul_comm, mul_div_assoc, div_self hw0, mul_one]`. Distinguish the cases in `hψ : ψ = 0`. Substitute `hψ` using the available equality. Establish `key : w * Formalism.Gz (a / w) + (a * Real.log a - a * Real.log w - (1 + Real.eulerMascheroniConstant) * a) = w * Formalism.Sz (a / w)`. Rewrite using `[Formalism.Gz, Real.log_div ha.ne' hw0]`.

Take the linear combination `(-(Real.log a - Real.log w) + (1 + Real.eulerMascheroniConstant)) * hwaR`. Establish `hL : ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv 0 n * ((a / n - w : ℝ) : ℂ) = ((w * Formalism.Sz (a / w) : ℝ) : ℂ)`. Rewrite using `[Formalism.Sz, Finset.mul_sum, Complex.ofReal_sum]`. Use `Finset.sum_congr rfl (fun n _ => ?_)` and prove the remaining obligations. Rewrite using `[Hs.2 n, hterm n, Complex.ofReal_mul, Complex.ofReal_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hL, GC, if_pos rfl, if_pos rfl, ← key, Complex.ofReal_add, Complex.ofReal_mul]`. Establish `hS : ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((a / n - w : ℝ) : ℂ) = (w : ℂ) * ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((a / w / n - 1 : ℝ) : ℂ)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun n _ => ?_)` and prove the remaining obligations.

Rewrite using `[hterm n]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwa : (w : ℂ) * ((a / w : ℝ) : ℂ) = (a : ℂ)`. Rewrite using `[← Complex.ofReal_mul, hwaR]`. Rewrite using `[hS, if_neg hψ, GC, if_neg hψ]`.

Take the linear combination `(-(Hs.ell ψ)) * hwa`.
-/
lemma askC_eq (Hs : CycHost H) (ψ : AddChar (E0 × H) ℂ) (a w : ℝ) (ha : 0 < a) (hw : 0 < w) :
    ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((a / n - w : ℝ) : ℂ)
      = (w : ℂ) * GC Hs ψ (a / w) + (if ψ = 0 then
          ((a * Real.log a - a * Real.log w - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
          else -(a : ℂ) * Hs.ell ψ) := by
  have hw0 : w ≠ 0 := hw.ne'
  have hterm : ∀ n : ℕ, ((a / n - w : ℝ) : ℂ) = (w : ℂ) * ((a / w / n - 1 : ℝ) : ℂ) := by
    intro n
    rw [term_real a w hw0 n, Complex.ofReal_mul]
  have hwaR : w * (a / w) = a := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hw0, mul_one]
  by_cases hψ : ψ = 0
  · subst hψ
    have key : w * Formalism.Gz (a / w) + (a * Real.log a - a * Real.log w - (1 + Real.eulerMascheroniConstant) * a)
        = w * Formalism.Sz (a / w) := by
      rw [Formalism.Gz, Real.log_div ha.ne' hw0]
      linear_combination (-(Real.log a - Real.log w) + (1 + Real.eulerMascheroniConstant)) * hwaR
    have hL : ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv 0 n * ((a / n - w : ℝ) : ℂ)
        = ((w * Formalism.Sz (a / w) : ℝ) : ℂ) := by
      rw [Formalism.Sz, Finset.mul_sum, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Hs.2 n, hterm n, Complex.ofReal_mul, Complex.ofReal_mul]
      ring
    rw [hL, GC, if_pos rfl, if_pos rfl, ← key, Complex.ofReal_add, Complex.ofReal_mul]
  · have hS : ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((a / n - w : ℝ) : ℂ)
        = (w : ℂ) * ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((a / w / n - 1 : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [hterm n]
      ring
    have hwa : (w : ℂ) * ((a / w : ℝ) : ℂ) = (a : ℂ) := by
      rw [← Complex.ofReal_mul, hwaR]
    rw [hS, if_neg hψ, GC, if_neg hψ]
    linear_combination (-(Hs.ell ψ)) * hwa

end

end Bal

open Bal in
/- English proof (translation)
Introduce `Hs a t w ha hw`. Establish `hf0` using `phiSet_card_ne_zero (H := H)`. Establish `hfr : ((PhiSet (H` using `H)).card : ℝ) ≠ 0 := by exact_mod_cast hf0`. Establish `hG` using `card_G_eq (H := H)`. Establish `hask : askTop Hs a t w = ((1 / ((PhiSet (H` using `H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ∑ ψ : AddChar (E0 × H) ℂ, (ψ (-g) * ((w (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w (cconj + g + topPl t)) + ψ (-g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (cconj + g + topPl t)) - (1 + …`.

Unfold `askTop vonMangoldtClassSum`. Rewrite using `[Finset.mul_sum, Complex.re_sum]`. Use `Finset.sum_congr rfl (fun g _ => ?_)` and prove the remaining obligations. Establish `e1 : (∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ∑ n ∈ Icc 1 ⌊a / w (cconj + g + topPl t)⌋₊, (Λ n : ℂ) * Hs.cv ψ n * ((a / n - w (cconj + g + topPl t) : ℝ) : ℂ)) = ∑ ψ : AddChar (E0 × H) ℂ, (ψ (-g) * ((w (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w (cconj + g + topPl t)) + ψ (-g) * ( …` using `Finset.sum_congr rfl (fun ψ _ => by rw [askC_eq Hs ψ a _ ha (hw _)]; ring)`. Rewrite using `[e1, hG]`.

Rewrite using `[show (1 / ((PhiSet (H := H)).card : ℂ)) = ((2 : ℝ) : ℂ) * (1 / (2 * ((PhiSet (H := H)).card : ℂ))) by push_cast; field_simp, mul_assoc, Complex.re_ofReal_mul]`. Establish `hsplit : ∀ g : E0 × H, (∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (cconj + g + topPl t)) - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * Hs.ell ψ)) = ((a * Real.log a - a * Real.log (w (cconj + g + topPl t)) - (1 + Rea …`. Introduce `g`. Rewrite using `[← Finset.add_sum_erase _ _ (mem_univ (0 : AddChar (E0 × H) ℂ)), if_pos rfl, AddChar.zero_apply, one_mul]`. Use `congr 1`.

Use `Finset.sum_congr rfl (fun ψ hψ => ?_)` and prove the remaining obligations. Rewrite using `[if_neg (Finset.ne_of_mem_erase hψ)]`. Establish `hcol : (∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ∑ ψ ∈ univ.erase (0 : AddChar (E0 × H) ℂ), ψ (-g) * (-(a : ℂ) * Hs.ell ψ)) = ((PhiSet (H` using `H)).card : ℂ) * ((a : ℂ) * Hs.ell Hs.chC) := by`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_congr rfl (fun ψ hψ => by`.

Rewrite using `[← Finset.sum_mul, sum_S_char Hs t ψ (Finset.ne_of_mem_erase hψ)])]`. Simplify using `only [ite_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq', if_pos (Finset.mem_erase.2 ⟨chC_ne_zero Hs, mem_univ _⟩)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hreal : (∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ((a * Real.log a - a * Real.log (w (cconj + g + topPl t)) - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)) = ((((PhiSet (H` using `H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a) - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ) := by`.

Rewrite using `[← Complex.ofReal_sum]`. Use `congr 1`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, card_S, ← Finset.mul_sum, sum_S_rho t (fun ρ => Real.log (w ρ))]`. Simplify using `only [nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hY : ((1 / ((PhiSet (H` using `H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (cconj + g + topPl t)) - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * Hs.ell ψ)).re = ledTop Hs a …`. Rewrite using `[Finset.sum_congr rfl (fun g _ => hsplit g), Finset.sum_add_distrib, hreal, hcol]`. Establish `e2 : (1 / ((PhiSet (H` using `H)).card : ℂ)) * (((((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a) - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ) + ((PhiSet (H := H)).card : ℂ) * ((a : ℂ) * Hs.ell Hs.chC)) = (((((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 …`. Rewrite using `[Complex.ofReal_div, Complex.ofReal_natCast]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]`. Unfold `ledTop`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hask, Finset.sum_congr rfl (fun g _ => Finset.sum_add_distrib), Finset.sum_add_distrib, mul_add, Complex.add_re, hY]`.

Unfold `balTop`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem character_sum_balance {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] : Balance (H := H) := by
  intro Hs a t w ha hw
  have hf0 := phiSet_card_ne_zero (H := H)
  have hfr : ((PhiSet (H := H)).card : ℝ) ≠ 0 := by exact_mod_cast hf0
  have hG := card_G_eq (H := H)

  have hask : askTop Hs a t w = ((1 / ((PhiSet (H := H)).card : ℂ)) *
      ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ∑ ψ : AddChar (E0 × H) ℂ,
        (ψ (-g) * ((w (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w (cconj + g + topPl t))
          + ψ (-g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * Hs.ell ψ))).re := by
    unfold askTop vonMangoldtClassSum
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    have e1 : (∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ∑ n ∈ Icc 1 ⌊a / w (cconj + g + topPl t)⌋₊,
          (Λ n : ℂ) * Hs.cv ψ n * ((a / n - w (cconj + g + topPl t) : ℝ) : ℂ))
        = ∑ ψ : AddChar (E0 × H) ℂ,
        (ψ (-g) * ((w (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w (cconj + g + topPl t))
          + ψ (-g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * Hs.ell ψ)) :=
      Finset.sum_congr rfl (fun ψ _ => by rw [askC_eq Hs ψ a _ ha (hw _)]; ring)
    rw [e1, hG]
    rw [show (1 / ((PhiSet (H := H)).card : ℂ)) = ((2 : ℝ) : ℂ) * (1 / (2 * ((PhiSet (H := H)).card : ℂ))) by
      push_cast; field_simp, mul_assoc, Complex.re_ofReal_mul]

  have hsplit : ∀ g : E0 × H, (∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * (if ψ = 0 then
        ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * Hs.ell ψ))
      = ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
        + ∑ ψ ∈ univ.erase (0 : AddChar (E0 × H) ℂ), ψ (-g) * (-(a : ℂ) * Hs.ell ψ) := by
    intro g
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : AddChar (E0 × H) ℂ)), if_pos rfl, AddChar.zero_apply, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun ψ hψ => ?_)
    rw [if_neg (Finset.ne_of_mem_erase hψ)]
  have hcol : (∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)),
        ∑ ψ ∈ univ.erase (0 : AddChar (E0 × H) ℂ), ψ (-g) * (-(a : ℂ) * Hs.ell ψ))
      = ((PhiSet (H := H)).card : ℂ) * ((a : ℂ) * Hs.ell Hs.chC) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun ψ hψ => by
      rw [← Finset.sum_mul, sum_S_char Hs t ψ (Finset.ne_of_mem_erase hψ)])]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_erase.2 ⟨chC_ne_zero Hs, mem_univ _⟩)]
    ring
  have hreal : (∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)),
        ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
          - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ))
      = ((((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a)
          - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, card_S,
      ← Finset.mul_sum, sum_S_rho t (fun ρ => Real.log (w ρ))]
    simp only [nsmul_eq_mul]
    ring
  have hY : ((1 / ((PhiSet (H := H)).card : ℂ)) *
      ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ∑ ψ : AddChar (E0 × H) ℂ,
        ψ (-g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (cconj + g + topPl t))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * Hs.ell ψ)).re
      = ledTop Hs a w := by
    rw [Finset.sum_congr rfl (fun g _ => hsplit g), Finset.sum_add_distrib, hreal, hcol]
    have e2 : (1 / ((PhiSet (H := H)).card : ℂ)) *
        (((((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a)
          - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ)
          + ((PhiSet (H := H)).card : ℂ) * ((a : ℂ) * Hs.ell Hs.chC))
        = (((((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a)
          - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ)) / ((PhiSet (H := H)).card : ℝ) : ℝ) : ℂ)
          + (a : ℂ) * Hs.ell Hs.chC := by
      rw [Complex.ofReal_div, Complex.ofReal_natCast]
      field_simp
    rw [e2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
    unfold ledTop
    field_simp
    ring
  rw [hask, Finset.sum_congr rfl (fun g _ => Finset.sum_add_distrib), Finset.sum_add_distrib, mul_add,
    Complex.add_re, hY]
  unfold balTop
  ring

end Formalism.D5

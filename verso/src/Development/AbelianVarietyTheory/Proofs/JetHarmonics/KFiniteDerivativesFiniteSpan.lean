import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.UnitBoxWords

open PI.UpqRep GlobalTheory.DerivedAction

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}

def lieSubspace (k r : ℕ) : Submodule ℝ (Mx k r) where
  carrier := {X | InLieHpk k r X}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_setOf_eq, InLieHpk] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp [InLieHpk]
  smul_mem' := fun c X hX => by
    simp only [Set.mem_setOf_eq, InLieHpk] at *
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

/- English proof (translation)
Take `⟨P, hP⟩` from `(lieSubspace k r).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)`. Set `n` to `Fin (2 * r + k + 1)`. Set `E : (n × n) ⊕ (n × n) → Mx k r` to `Sum.elim (fun p => Matrix.single p.1 p.2 1) (fun p => Matrix.single p.1 p.2 Complex.I)`. Use `⟨(n × n) ⊕ (n × n), inferInstance, fun j => (P (E j)).1, fun j => (P (E j)).2, fun Y hY => ?_⟩` and prove the remaining obligations. Set `c : (n × n) ⊕ (n × n) → ℝ` to `Sum.elim (fun p => (Y p.1 p.2).re) (fun p => (Y p.1 p.2).im)`.

Use `⟨c, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(p | p)`. Conclude with `(Complex.abs_re_le_norm _).trans (hY.2 _ _)`. Conclude with `(Complex.abs_im_le_norm _).trans (hY.2 _ _)`. Establish `h1 : Y = ∑ j, c j • E j`.

Rewrite using `[Fintype.sum_sum_type, ← Finset.sum_add_distrib, Fintype.sum_prod_type]`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single Y]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [c, E, Sum.elim_inl, Sum.elim_inr, Matrix.smul_single, ← Matrix.single_add]`. Use `congr 1`.

Simplify using `[Complex.real_smul]`. Establish `hYL : Y ∈ lieSubspace k r` using `hY.1`. Establish `h2 : (P Y).1 = Y`. Use `LinearMap.congr_fun hP ⟨Y, hYL⟩` as an intermediate fact. Conclude with `congrArg Subtype.val this`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_box_generators (k r : ℕ) : ∃ (J : Type) (_ : Fintype J) (Z : J → Mx k r),
    (∀ j, InLieHpk k r (Z j)) ∧ ∀ Y, B.unitLie k r Y → ∃ c : J → ℝ, (∀ j, |c j| ≤ 1) ∧ Y = ∑ j, c j • Z j := by
  obtain ⟨P, hP⟩ := (lieSubspace k r).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let n := Fin (2 * r + k + 1)
  let E : (n × n) ⊕ (n × n) → Mx k r :=
    Sum.elim (fun p => Matrix.single p.1 p.2 1) (fun p => Matrix.single p.1 p.2 Complex.I)
  refine ⟨(n × n) ⊕ (n × n), inferInstance, fun j => (P (E j)).1, fun j => (P (E j)).2, fun Y hY => ?_⟩
  let c : (n × n) ⊕ (n × n) → ℝ := Sum.elim (fun p => (Y p.1 p.2).re) (fun p => (Y p.1 p.2).im)
  refine ⟨c, ?_, ?_⟩
  · rintro (p | p)
    · exact (Complex.abs_re_le_norm _).trans (hY.2 _ _)
    · exact (Complex.abs_im_le_norm _).trans (hY.2 _ _)
  · have h1 : Y = ∑ j, c j • E j := by
      rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib, Fintype.sum_prod_type]
      conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [c, E, Sum.elim_inl, Sum.elim_inr, Matrix.smul_single, ← Matrix.single_add]
      congr 1
      simp [Complex.real_smul]
    have hYL : Y ∈ lieSubspace k r := hY.1
    have h2 : (P Y).1 = Y := by
      have := LinearMap.congr_fun hP ⟨Y, hYL⟩
      exact congrArg Subtype.val this
    calc Y = (P Y).1 := h2.symm
      _ = (P (∑ j, c j • E j)).1 := by rw [← h1]
      _ = _ := by simp [map_sum]

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_lin hv`. Establish `hm : (∑ j, c j • Z j) ∈ lieSubspace k r` using `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hZ j)`. Rewrite using `[(hL _ hm).1, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, (hL _ (hZ j)).1, Complex.coe_smul]`.
-/
theorem dsig_sum_letter {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    {J : Type} [Fintype J] {Z : J → Mx k r} (hZ : ∀ j, InLieHpk k r (Z j)) (c : J → ℝ) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ (∑ j, c j • Z j) v = ∑ j, (c j : ℂ) • dsig (k := k) (r := r) σ (Z j) v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  have hm : (∑ j, c j • Z j) ∈ lieSubspace k r :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hZ j)
  rw [(hL _ hm).1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, (hL _ (hZ j)).1, Complex.coe_smul]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [dsig_zero]`. Consider the case `insert a s ha ih`. Establish `h1 : c a • v a ∈ R.smSub` using `R.smSub.smul_mem _ (hv a)`. Establish `h2 : ∑ i ∈ s, c i • v i ∈ R.smSub` using `R.smSub.sum_mem fun i _ => R.smSub.smul_mem _ (hv i)`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, dsig_add hX h1 h2, dsig_smul hX _ (hv a), ih]`.
-/
theorem dsig_sum_vec (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    {v : ι → R.H} (hv : ∀ i, v i ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • dsig (k := k) (r := r) R.σ X (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dsig_zero]
  | insert a s ha ih =>
    have h1 : c a • v a ∈ R.smSub := R.smSub.smul_mem _ (hv a)
    have h2 : ∑ i ∈ s, c i • v i ∈ R.smSub := R.smSub.sum_mem fun i _ => R.smSub.smul_mem _ (hv i)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dsig_add hX h1 h2, dsig_smul hX _ (hv a), ih]

/- English proof (translation)
Take `⟨J, _, Z, hZ, hbox⟩` from `exists_box_generators k r`. Establish `h0 : InLieHpk k r (0 : Mx k r)` using `(lieSubspace k r).zero_mem`. Proceed by induction on `m with`. Consider the case `zero`. Use `⟨Unit, inferInstance, fun _ => x, fun _ => hx, fun a _ hl => ⟨fun _ => 1, by simp, ?_⟩⟩` and prove the remaining obligations.

Take `rfl : a = []` from `List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)`. Simplify using `[dsigW]`. Consider the case `succ m ih`. Take `⟨ι, _, xs, hxs, h⟩` from `ih`. Use `⟨Unit ⊕ (J × ι), inferInstance, Sum.elim (fun _ => x) (fun p => dsig (k := k) (r := r) R.σ (Z p.1) (xs p.2)), ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `(p | p)`. Conclude with `hx`. Conclude with `(dsig_TK hK R hR (hZ p.1) _ (hxs p.2)).2`. Introduce `a ha hl`. Consider the cases of `a with`.

Consider the case `nil`. Use `⟨Sum.elim (fun _ => 1) (fun _ => 0), ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rintro (p | p) <;> simp`. Simplify using `[dsigW, Fintype.sum_sum_type]`. Consider the case `cons Y a`.

Establish `hY` using `ha Y (by simp)`. Take `⟨co, hco, e⟩` from `h a (fun Y hY => ha Y (by simp [hY])) (by simpa using hl)`. Take `⟨c, hc, eY⟩` from `hbox Y hY`. Establish `hsm : ∀ i, xs i ∈ R.sm` using `fun i => (dsig_TK hK R hR h0 _ (hxs i)).1`. Use `⟨Sum.elim (fun _ => 0) (fun p => co p.2 * c p.1), ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `(p | p)`. Simplify using the standard rewrite rules. Simplify using `only [Sum.elim_inr, abs_mul]`. Conclude with `mul_le_one₀ (hco _) (abs_nonneg _) (hc _)`. Establish `hYL : InLieHpk k r Y` using `hY.1 show dsig (k := k) (r := r) R.σ Y (dsigW (k := k) (r := r) R.σ a x) = _`.

Rewrite using `[e, dsig_sum_vec R hYL _ _ hsm, Fintype.sum_sum_type, Fintype.sum_prod_type_right]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero, zero_add]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[eY, dsig_sum_letter hZ c (hsm i), Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul, Complex.ofReal_mul]`.
-/
theorem box_words_fintype (hK : PI.KFinSmooth) (R : Rep k r) (hR : R.IsDS ε mu) {x : R.H} (hx : x ∈ R.TK) (m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (xs : ι → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r),
      (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : ι → ℝ, (∀ i, |co i| ≤ 1) ∧
        dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i := by
  obtain ⟨J, _, Z, hZ, hbox⟩ := exists_box_generators k r
  have h0 : InLieHpk k r (0 : Mx k r) := (lieSubspace k r).zero_mem
  induction m with
  | zero =>
    refine ⟨Unit, inferInstance, fun _ => x, fun _ => hx, fun a _ hl => ⟨fun _ => 1, by simp, ?_⟩⟩
    obtain rfl : a = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)
    simp [dsigW]
  | succ m ih =>
    obtain ⟨ι, _, xs, hxs, h⟩ := ih
    refine ⟨Unit ⊕ (J × ι), inferInstance,
      Sum.elim (fun _ => x) (fun p => dsig (k := k) (r := r) R.σ (Z p.1) (xs p.2)), ?_, ?_⟩
    · rintro (p | p)
      · exact hx
      · exact (dsig_TK hK R hR (hZ p.1) _ (hxs p.2)).2
    · intro a ha hl
      cases a with
      | nil =>
        refine ⟨Sum.elim (fun _ => 1) (fun _ => 0), ?_, ?_⟩
        · rintro (p | p) <;> simp
        · simp [dsigW, Fintype.sum_sum_type]
      | cons Y a =>
        have hY := ha Y (by simp)
        obtain ⟨co, hco, e⟩ := h a (fun Y hY => ha Y (by simp [hY])) (by simpa using hl)
        obtain ⟨c, hc, eY⟩ := hbox Y hY
        have hsm : ∀ i, xs i ∈ R.sm := fun i => (dsig_TK hK R hR h0 _ (hxs i)).1
        refine ⟨Sum.elim (fun _ => 0) (fun p => co p.2 * c p.1), ?_, ?_⟩
        · rintro (p | p)
          · simp
          · simp only [Sum.elim_inr, abs_mul]
            exact mul_le_one₀ (hco _) (abs_nonneg _) (hc _)
        · have hYL : InLieHpk k r Y := hY.1
          show dsig (k := k) (r := r) R.σ Y (dsigW (k := k) (r := r) R.σ a x) = _
          rw [e, dsig_sum_vec R hYL _ _ hsm, Fintype.sum_sum_type, Fintype.sum_prod_type_right]
          simp only [Sum.elim_inl, Sum.elim_inr, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero, zero_add]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [eY, dsig_sum_letter hZ c (hsm i), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul, Complex.ofReal_mul]

/- English proof (translation)
Introduce `hK k r ε mu R hR x hx m`. Take `⟨ι, _, xs, hxs, h⟩` from `box_words_fintype hK R hR hx m`. Set `e` to `(Fintype.equivFin ι).symm`. Use `⟨_, xs ∘ e, fun i => hxs _, fun a ha hl => ?_⟩` and prove the remaining obligations. Take `⟨co, hco, h'⟩` from `h a ha hl`.

Use `⟨co ∘ e, fun i => hco _, ?_⟩` and prove the remaining obligations. Rewrite using `[h', ← e.sum_comp]`. Both sides reduce to the same expression.
-/
theorem box_words : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ x ∈ R.TK, ∀ m : ℕ, ∃ (M : ℕ) (xs : Fin M → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : Fin M → ℝ, (∀ i, |co i| ≤ 1) ∧ PI.UpqRep.dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i := by
  intro hK k r ε mu R hR x hx m
  obtain ⟨ι, _, xs, hxs, h⟩ := box_words_fintype hK R hR hx m
  let e := (Fintype.equivFin ι).symm
  refine ⟨_, xs ∘ e, fun i => hxs _, fun a ha hl => ?_⟩
  obtain ⟨co, hco, h'⟩ := h a ha hl
  refine ⟨co ∘ e, fun i => hco _, ?_⟩
  rw [h', ← e.sum_comp]
  rfl

end GlobalTheory.UnitBoxWords

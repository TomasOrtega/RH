import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

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
Take `⟨q, hq⟩` from `Submodule.exists_isCompl (lieSubspace k r)`. Take `⟨E, hE⟩ : ∃ E : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool → Mx k r, ∀ x, E x = Matrix.of fun a b => if a = x.1 ∧ b = x.2.1 then (if x.2.2 then Complex.I else 1) else 0` from `⟨_, fun _ => rfl⟩`. Use `⟨Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool, inferInstance, fun x => ((Submodule.linearProjOfIsCompl (lieSubspace k r) q hq (E x) : lieSubspace k r) : Mx k r), fun x => (Submodule.linearProjOfIsCompl (lieSubspace k r) q hq (E x)).2, ?_⟩` and prove the remaining obligations. Introduce `Y hY`. Take `⟨c, hc⟩ : ∃ c : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool → ℝ, ∀ x, c x = if x.2.2 then (Y x.1 x.2.1).im else (Y x.1 x.2.1).re` from `⟨_, fun _ => rfl⟩`.

Use `⟨c, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨i, j, β⟩`. Establish `h1 : ‖Y i j‖ ≤ 1` using `hY.2 i j`. Rewrite using `[hc]`. Consider the cases of `β`.

Conclude with `(Complex.abs_re_le_norm _).trans h1`. Conclude with `(Complex.abs_im_le_norm _).trans h1`. Establish `hYmem : Y ∈ lieSubspace k r` using `hY.1`. Establish `hdecomp : Y = ∑ x, c x • E x`. Use extensionality with `a b`.

Simplify using `only [Matrix.sum_apply, Matrix.smul_apply]`. Establish `hpair : ((a, b, true) : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) ≠ (a, b, false)`. Simplify using the standard rewrite rules. Rewrite using `[← Finset.sum_subset (Finset.subset_univ {(a, b, true), (a, b, false)})]`. Rewrite using `[Finset.sum_pair hpair, hE, hE, hc, hc]`.

Simplify using `only [Matrix.of_apply, and_self, if_true, Complex.real_smul, mul_one]`. Simplify using `only [Bool.false_eq_true, if_false, ite_true]`. Take the linear combination `(-1 : ℂ) * Complex.re_add_im (Y a b)`. Introduce and unpack `⟨i, j, β⟩ _ hx`. Rewrite using `[hE]`.

Simplify using `only [Matrix.of_apply]`. Establish `hne : ¬ (a = i ∧ b = j)`. Introduce and unpack `⟨rfl, rfl⟩`. Apply `hx` to reduce the goal to its premises. Apply the tactic sequence `cases β <;> simp`.

Rewrite using `[if_neg hne, smul_zero]`. Establish `hPY : ((Submodule.linearProjOfIsCompl (lieSubspace k r) q hq Y : lieSubspace k r) : Mx k r) = Y` using `congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hq ⟨Y, hYmem⟩)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum, Submodule.coe_sum]`. Simplify using `only [map_smul, Submodule.coe_smul]`.
-/
theorem exists_box_generators (k r : ℕ) : ∃ (J : Type) (_ : Fintype J) (Z : J → Mx k r),
    (∀ j, InLieHpk k r (Z j)) ∧ ∀ Y, B.unitLie k r Y → ∃ c : J → ℝ, (∀ j, |c j| ≤ 1) ∧ Y = ∑ j, c j • Z j := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (lieSubspace k r)
  obtain ⟨E, hE⟩ : ∃ E : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool → Mx k r, ∀ x,
      E x = Matrix.of fun a b => if a = x.1 ∧ b = x.2.1 then (if x.2.2 then Complex.I else 1) else 0 :=
    ⟨_, fun _ => rfl⟩
  refine ⟨Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool, inferInstance,
    fun x => ((Submodule.linearProjOfIsCompl (lieSubspace k r) q hq (E x) : lieSubspace k r) : Mx k r),
    fun x => (Submodule.linearProjOfIsCompl (lieSubspace k r) q hq (E x)).2, ?_⟩
  intro Y hY
  obtain ⟨c, hc⟩ : ∃ c : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool → ℝ, ∀ x,
      c x = if x.2.2 then (Y x.1 x.2.1).im else (Y x.1 x.2.1).re := ⟨_, fun _ => rfl⟩
  refine ⟨c, ?_, ?_⟩
  · rintro ⟨i, j, β⟩
    have h1 : ‖Y i j‖ ≤ 1 := hY.2 i j
    rw [hc]
    cases β
    · exact (Complex.abs_re_le_norm _).trans h1
    · exact (Complex.abs_im_le_norm _).trans h1
  · have hYmem : Y ∈ lieSubspace k r := hY.1
    have hdecomp : Y = ∑ x, c x • E x := by
      ext a b
      simp only [Matrix.sum_apply, Matrix.smul_apply]
      have hpair : ((a, b, true) : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) ≠ (a, b, false) := by
        simp
      rw [← Finset.sum_subset (Finset.subset_univ {(a, b, true), (a, b, false)})]
      · rw [Finset.sum_pair hpair, hE, hE, hc, hc]
        simp only [Matrix.of_apply, and_self, if_true, Complex.real_smul, mul_one]
        simp only [Bool.false_eq_true, if_false, ite_true]
        linear_combination (-1 : ℂ) * Complex.re_add_im (Y a b)
      · rintro ⟨i, j, β⟩ _ hx
        rw [hE]
        simp only [Matrix.of_apply]
        have hne : ¬ (a = i ∧ b = j) := by
          rintro ⟨rfl, rfl⟩
          apply hx
          cases β <;> simp
        rw [if_neg hne, smul_zero]
    have hPY : ((Submodule.linearProjOfIsCompl (lieSubspace k r) q hq Y : lieSubspace k r) : Mx k r) = Y :=
      congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hq ⟨Y, hYmem⟩)
    calc Y = ((Submodule.linearProjOfIsCompl (lieSubspace k r) q hq Y : lieSubspace k r) : Mx k r) := hPY.symm
      _ = ((Submodule.linearProjOfIsCompl (lieSubspace k r) q hq (∑ x, c x • E x) : lieSubspace k r) :
            Mx k r) := by rw [← hdecomp]
      _ = ∑ x, c x • ((Submodule.linearProjOfIsCompl (lieSubspace k r) q hq (E x) : lieSubspace k r) :
            Mx k r) := by
          rw [map_sum, Submodule.coe_sum]
          simp only [map_smul, Submodule.coe_smul]

/- English proof (translation)
Take `⟨Lm, hL⟩` from `Gp91.GlobalTheory.DerivedAction.exists_lin hv`. Establish `hsum : InLieHpk k r (∑ j, c j • Z j)` using `Submodule.sum_mem (lieSubspace k r) (fun j _ => Submodule.smul_mem (lieSubspace k r) (c j) (hZ j))`. Rewrite using `[(hL _ hsum).1, map_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`.

Rewrite using `[map_smul, (hL _ (hZ j)).1]`. Conclude with `RCLike.real_smul_eq_coe_smul (K := ℂ) (c j) (Lm (Z j))`.
-/
theorem dsig_sum_letter {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    {J : Type} [Fintype J] {Z : J → Mx k r} (hZ : ∀ j, InLieHpk k r (Z j)) (c : J → ℝ) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ (∑ j, c j • Z j) v = ∑ j, (c j : ℂ) • dsig (k := k) (r := r) σ (Z j) v := by
  obtain ⟨Lm, hL⟩ := Gp91.GlobalTheory.DerivedAction.exists_lin hv
  have hsum : InLieHpk k r (∑ j, c j • Z j) :=
    Submodule.sum_mem (lieSubspace k r) (fun j _ => Submodule.smul_mem (lieSubspace k r) (c j) (hZ j))
  rw [(hL _ hsum).1, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, (hL _ (hZ j)).1]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (c j) (Lm (Z j))

/- English proof (translation)
Establish `hd : ∀ i, HasDerivAt (fun t : ℝ => (R.σ (NormedSpace.exp ((t : ℂ) • X))) (v i)) (dsig (k` using `k) (r := r) R.σ X (v i)) 0 := fun i => Gp91.GlobalTheory.DerivedAction.hasDerivAt_dsig hX (hv i)`. Establish `hsum : HasDerivAt (fun t : ℝ => ∑ i ∈ s, c i • (R.σ (NormedSpace.exp ((t : ℂ) • X))) (v i)) (∑ i ∈ s, c i • dsig (k` using `k) (r := r) R.σ X (v i)) 0 := by`. Establish `h` using `HasDerivAt.sum (u := s) (fun i _ => (hd i).const_smul (c i))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `t`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Establish `heq : (fun t : ℝ => (R.σ (NormedSpace.exp ((t : ℂ) • X))) (∑ i ∈ s, c i • v i)) = fun t : ℝ => ∑ i ∈ s, c i • (R.σ (NormedSpace.exp ((t : ℂ) • X))) (v i)`. Use function extensionality and compare the values at `t`. Simplify using `only [map_sum, map_smul]`. Use `show deriv (fun t : ℝ => (R.σ (NormedSpace.exp ((t : ℂ) • X))) (∑ i ∈ s, c i • v i)) 0 = _`.

Rewrite using `[heq, hsum.deriv]`.
-/
theorem dsig_sum_vec (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    {v : ι → R.H} (hv : ∀ i, v i ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • dsig (k := k) (r := r) R.σ X (v i) := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => (R.σ (NormedSpace.exp ((t : ℂ) • X))) (v i))
      (dsig (k := k) (r := r) R.σ X (v i)) 0 :=
    fun i => Gp91.GlobalTheory.DerivedAction.hasDerivAt_dsig hX (hv i)
  have hsum : HasDerivAt (fun t : ℝ => ∑ i ∈ s, c i • (R.σ (NormedSpace.exp ((t : ℂ) • X))) (v i))
      (∑ i ∈ s, c i • dsig (k := k) (r := r) R.σ X (v i)) 0 := by
    have h := HasDerivAt.sum (u := s) (fun i _ => (hd i).const_smul (c i))
    convert h using 1
    ext t
    simp only [Finset.sum_apply, Pi.smul_apply]
  have heq : (fun t : ℝ => (R.σ (NormedSpace.exp ((t : ℂ) • X))) (∑ i ∈ s, c i • v i)) =
      fun t : ℝ => ∑ i ∈ s, c i • (R.σ (NormedSpace.exp ((t : ℂ) • X))) (v i) := by
    funext t
    simp only [map_sum, map_smul]
  show deriv (fun t : ℝ => (R.σ (NormedSpace.exp ((t : ℂ) • X))) (∑ i ∈ s, c i • v i)) 0 = _
  rw [heq, hsum.deriv]

/- English proof (translation)
Take `⟨J, hJ, Z, hZ, hgen⟩` from `Gp91.GlobalTheory.UnitBoxWords.exists_box_generators k r`. Establish `h0 : InLieHpk k r 0` using `(lieSubspace k r).zero_mem`. Establish `hW0 : ∀ v : R.H, dsigW (k` using `k) (r := r) R.σ [] v = v := fun v => rfl`. Establish `hWc : ∀ (X : Mx k r) (a : List (Mx k r)) (v : R.H), dsigW (k` using `k) (r := r) R.σ (X :: a) v = dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ a v) := fun X a v => rfl`. Proceed by induction on `m with`.

Consider the case `zero`. Use `⟨Unit, inferInstance, fun _ => x, fun _ => hx, ?_⟩` and prove the remaining obligations. Introduce `a _ ha`. Establish `hnil : a = []` using `List.eq_nil_of_length_eq_zero (by omega)`. Substitute `hnil` using the available equality.

Use `⟨fun _ => 1, fun _ => by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[hW0]`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Take `⟨ι, hι, xs, hxs, hrep⟩` from `ih`.

Establish `hxsm : ∀ i, xs i ∈ R.sm` using `fun i => (Gp91.GlobalTheory.DerivedAction.dsig_TK hK R hR h0 (xs i) (hxs i)).1`. Use `⟨ι ⊕ (J × ι), inferInstance, Sum.elim xs (fun p => dsig (k := k) (r := r) R.σ (Z p.1) (xs p.2)), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | ⟨j, i⟩)`. Conclude with `hxs i`. Conclude with `(Gp91.GlobalTheory.DerivedAction.dsig_TK hK R hR (hZ j) (xs i) (hxs i)).2`.

Introduce `a ha hlen`. Break down `Nat.lt_or_ge a.length (m + 1) with hlt | hge` into its components or cases. Take `⟨co, hco, heq⟩` from `hrep a ha (by omega)`. Use `⟨Sum.elim co (fun _ => 0), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | p)`.

Conclude with `hco i`. Simplify using the standard rewrite rules. Rewrite using `[heq, Fintype.sum_sum_type]`. Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨Y, a', rfl⟩ : ∃ Y a', a = Y :: a' := by`.

Consider the cases of `a with`. Consider the case `nil => simp at hge`. Consider the case `cons Y a' => exact ⟨Y, a', rfl⟩`. Establish `hY : B.unitLie k r Y` using `ha Y List.mem_cons_self`. Establish `ha' : ∀ Y' ∈ a', B.unitLie k r Y'` using `fun Y' h => ha Y' (List.mem_cons_of_mem _ h)`.

Take `⟨co, hco, heq⟩` from `hrep a' ha' (by simp at hlen; omega)`. Take `⟨cg, hcg, hYeq⟩` from `hgen Y hY`. Use `⟨Sum.elim (fun _ => 0) (fun p => cg p.1 * co p.2), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | ⟨j, i⟩)`. Simplify using the standard rewrite rules.

Simplify using `only [Sum.elim_inr]`. Rewrite using `[abs_mul]`. Conclude with `mul_le_one₀ (hcg j) (abs_nonneg _) (hco i)`. Establish `hvTK : dsigW (k` using `k) (r := r) R.σ a' x ∈ R.TK := by`. Rewrite using `[heq]`.

Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hxs i))`. Establish `hvsm` using `(Gp91.GlobalTheory.DerivedAction.dsig_TK hK R hR h0 _ hvTK).1`. Rewrite using `[hWc, hYeq, Gp91.GlobalTheory.UnitBoxWords.dsig_sum_letter hZ cg hvsm, heq]`. Rewrite using `[Fintype.sum_sum_type, Fintype.sum_prod_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero, zero_add]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[Gp91.GlobalTheory.UnitBoxWords.dsig_sum_vec R (hZ j) Finset.univ (fun i => (co i : ℂ)) hxsm, Finset.smul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[smul_smul, Complex.ofReal_mul]`.
-/
theorem box_words_fintype (hK : PI.KFinSmooth) (R : Rep k r) (hR : R.IsDG ε mu) {x : R.H} (hx : x ∈ R.TK) (m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (xs : ι → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r),
      (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : ι → ℝ, (∀ i, |co i| ≤ 1) ∧
        dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i := by
  obtain ⟨J, hJ, Z, hZ, hgen⟩ := Gp91.GlobalTheory.UnitBoxWords.exists_box_generators k r
  have h0 : InLieHpk k r 0 := (lieSubspace k r).zero_mem
  have hW0 : ∀ v : R.H, dsigW (k := k) (r := r) R.σ [] v = v := fun v => rfl
  have hWc : ∀ (X : Mx k r) (a : List (Mx k r)) (v : R.H), dsigW (k := k) (r := r) R.σ (X :: a) v =
      dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ a v) := fun X a v => rfl
  induction m with
  | zero =>
    refine ⟨Unit, inferInstance, fun _ => x, fun _ => hx, ?_⟩
    intro a _ ha
    have hnil : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    rw [hW0]
    simp
  | succ m ih =>
    obtain ⟨ι, hι, xs, hxs, hrep⟩ := ih
    have hxsm : ∀ i, xs i ∈ R.sm := fun i => (Gp91.GlobalTheory.DerivedAction.dsig_TK hK R hR h0 (xs i) (hxs i)).1
    refine ⟨ι ⊕ (J × ι), inferInstance,
      Sum.elim xs (fun p => dsig (k := k) (r := r) R.σ (Z p.1) (xs p.2)), ?_, ?_⟩
    · rintro (i | ⟨j, i⟩)
      · exact hxs i
      · exact (Gp91.GlobalTheory.DerivedAction.dsig_TK hK R hR (hZ j) (xs i) (hxs i)).2
    · intro a ha hlen
      rcases Nat.lt_or_ge a.length (m + 1) with hlt | hge
      · obtain ⟨co, hco, heq⟩ := hrep a ha (by omega)
        refine ⟨Sum.elim co (fun _ => 0), ?_, ?_⟩
        · rintro (i | p)
          · exact hco i
          · simp
        · rw [heq, Fintype.sum_sum_type]
          simp
      · obtain ⟨Y, a', rfl⟩ : ∃ Y a', a = Y :: a' := by
          cases a with
          | nil => simp at hge
          | cons Y a' => exact ⟨Y, a', rfl⟩
        have hY : B.unitLie k r Y := ha Y List.mem_cons_self
        have ha' : ∀ Y' ∈ a', B.unitLie k r Y' := fun Y' h => ha Y' (List.mem_cons_of_mem _ h)
        obtain ⟨co, hco, heq⟩ := hrep a' ha' (by simp at hlen; omega)
        obtain ⟨cg, hcg, hYeq⟩ := hgen Y hY
        refine ⟨Sum.elim (fun _ => 0) (fun p => cg p.1 * co p.2), ?_, ?_⟩
        · rintro (i | ⟨j, i⟩)
          · simp
          · simp only [Sum.elim_inr]
            rw [abs_mul]
            exact mul_le_one₀ (hcg j) (abs_nonneg _) (hco i)
        · have hvTK : dsigW (k := k) (r := r) R.σ a' x ∈ R.TK := by
            rw [heq]
            exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hxs i))
          have hvsm := (Gp91.GlobalTheory.DerivedAction.dsig_TK hK R hR h0 _ hvTK).1
          rw [hWc, hYeq, Gp91.GlobalTheory.UnitBoxWords.dsig_sum_letter hZ cg hvsm, heq]
          rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
          simp only [Sum.elim_inl, Sum.elim_inr, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero,
            zero_add]
          apply Finset.sum_congr rfl
          intro j _
          rw [Gp91.GlobalTheory.UnitBoxWords.dsig_sum_vec R (hZ j) Finset.univ (fun i => (co i : ℂ)) hxsm,
            Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [smul_smul, Complex.ofReal_mul]

/- English proof (translation)
Introduce `hK k r ε mu R hR x hx m`. Take `⟨ι, hι, xs, hxs, hrep⟩` from `Gp91.GlobalTheory.UnitBoxWords.box_words_fintype hK R hR hx m`. Use `⟨Fintype.card ι, fun i => xs ((Fintype.equivFin ι).symm i), fun i => hxs _, ?_⟩` and prove the remaining obligations. Introduce `a ha hlen`. Take `⟨co, hco, heq⟩` from `hrep a ha hlen`.

Use `⟨fun i => co ((Fintype.equivFin ι).symm i), fun i => hco _, ?_⟩` and prove the remaining obligations. Rewrite using `[heq]`. Conclude with `(Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (co i : ℂ) • xs i)).symm`.
-/
theorem box_words : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ x ∈ R.TK, ∀ m : ℕ, ∃ (M : ℕ) (xs : Fin M → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : Fin M → ℝ, (∀ i, |co i| ≤ 1) ∧ PI.UpqRep.dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i := by
  intro hK k r ε mu R hR x hx m
  obtain ⟨ι, hι, xs, hxs, hrep⟩ := Gp91.GlobalTheory.UnitBoxWords.box_words_fintype hK R hR hx m
  refine ⟨Fintype.card ι, fun i => xs ((Fintype.equivFin ι).symm i), fun i => hxs _, ?_⟩
  intro a ha hlen
  obtain ⟨co, hco, heq⟩ := hrep a ha hlen
  refine ⟨fun i => co ((Fintype.equivFin ι).symm i), fun i => hco _, ?_⟩
  rw [heq]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (co i : ℂ) • xs i)).symm

end GlobalTheory.UnitBoxWords

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

namespace GlobalTheory.FibreProj.DetPol

open Classical in

/- English proof (translation)
Unfold `pol`. Use `Finset.sum_involution (fun S _ => if i ∈ S then S.erase i else insert i S) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_` and prove the remaining obligations. Introduce `S _`. Establish `hpt : ∀ T : Finset ι, (i ∈ T ↔ i ∉ S) → (∀ j, j ≠ i → (j ∈ T ↔ j ∈ S)) → (fun j => if j ∈ T then (-1 : ℤ) else 0) = Function.update (fun j => if j ∈ S then (-1 : ℤ) else 0) i (if i ∈ T then -1 else 0)`. Introduce `T _ hT`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hj]`.

Distinguish the cases in `hS : j ∈ S`. Simplify using `[hS, (hT j hj).2 hS]`. Establish `: j ∉ T` using `fun h' => hS ((hT j hj).1 h')`. Simplify using `[hS, this]`. Distinguish the cases in `hS : i ∈ S`.

Simplify using `only [hS, if_true]`. Rewrite using `[hpt (S.erase i) (by simp [hS]) (fun j hj => by simp [hj]), h]`. Establish `hc` using `Finset.card_erase_add_one hS`. Rewrite using `[← hc, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hS, if_false]`. Rewrite using `[hpt (insert i S) (by simp [hS]) (fun j hj => by simp [hj]), h]`. Rewrite using `[Finset.card_insert_of_notMem hS, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Introduce `S _ _ heq`.

Distinguish the cases in `hS : i ∈ S`. Simplify using `only [hS, if_true] at heq`. Establish `hn` using `Finset.notMem_erase i S`. Rewrite `hn` using `[heq]`. Conclude with `hn hS`.

Simplify using `only [hS, if_false] at heq`. Establish `hm` using `Finset.mem_insert_self i S`. Rewrite `hm` using `[heq]`. Conclude with `hS hm`. Introduce `S _`.

Distinguish the cases in `hS : i ∈ S`. Simplify using `[hS, Finset.insert_erase hS]`. Simplify using `[hS, Finset.erase_insert hS]`.
-/
theorem pol_eq_zero_of_indep {ι : Type} [Fintype ι] (φ : (ι → ℤ) → ℝ) (i : ι)
    (h : ∀ n v, φ (Function.update n i v) = φ n) : pol φ = 0 := by
  unfold pol
  refine Finset.sum_involution (fun S _ => if i ∈ S then S.erase i else insert i S) ?_ ?_
    (fun _ _ => Finset.mem_univ _) ?_
  · intro S _
    have hpt : ∀ T : Finset ι, (i ∈ T ↔ i ∉ S) → (∀ j, j ≠ i → (j ∈ T ↔ j ∈ S)) →
        (fun j => if j ∈ T then (-1 : ℤ) else 0) =
          Function.update (fun j => if j ∈ S then (-1 : ℤ) else 0) i (if i ∈ T then -1 else 0) := by
      intro T _ hT
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]
        by_cases hS : j ∈ S
        · simp [hS, (hT j hj).2 hS]
        · have : j ∉ T := fun h' => hS ((hT j hj).1 h')
          simp [hS, this]
    by_cases hS : i ∈ S
    · simp only [hS, if_true]
      rw [hpt (S.erase i) (by simp [hS]) (fun j hj => by simp [hj]), h]
      have hc := Finset.card_erase_add_one hS
      rw [← hc, pow_succ]
      ring
    · simp only [hS, if_false]
      rw [hpt (insert i S) (by simp [hS]) (fun j hj => by simp [hj]), h]
      rw [Finset.card_insert_of_notMem hS, pow_succ]
      ring
  · intro S _ _ heq
    by_cases hS : i ∈ S
    · simp only [hS, if_true] at heq
      have hn := Finset.notMem_erase i S
      rw [heq] at hn
      exact hn hS
    · simp only [hS, if_false] at heq
      have hm := Finset.mem_insert_self i S
      rw [heq] at hm
      exact hS hm
  · intro S _
    by_cases hS : i ∈ S
    · simp [hS, Finset.insert_erase hS]
    · simp [hS, Finset.erase_insert hS]

variable (α β : Type) [Fintype α] [Fintype β]

def DepOn (T : Finset β) (g : (α ⊕ β → ℤ) → ℂ) : Prop :=
  ∀ n n' : α ⊕ β → ℤ, (∀ a, n (Sum.inl a) = n' (Sum.inl a)) →
    (∀ b ∈ T, n (Sum.inr b) = n' (Sum.inr b)) → g n = g n'

def lowDeg (k : ℕ) : Submodule ℂ ((α ⊕ β → ℤ) → ℂ) :=
  Submodule.span ℂ {g | ∃ T : Finset β, T.card ≤ k ∧ DepOn α β T g}

variable {α β}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨T, hT, hg⟩`.
-/
theorem mem_lowDeg_of_depOn {k : ℕ} (T : Finset β) (hT : T.card ≤ k) (g : (α ⊕ β → ℤ) → ℂ)
    (hg : DepOn α β T g) : g ∈ lowDeg α β k :=
  Submodule.subset_span ⟨T, hT, hg⟩

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨T, hT, hg⟩ => ⟨T, hT.trans h, hg⟩`.
-/
theorem lowDeg_mono {k l : ℕ} (h : k ≤ l) : lowDeg α β k ≤ lowDeg α β l :=
  Submodule.span_mono fun _ ⟨T, hT, hg⟩ => ⟨T, hT.trans h, hg⟩

/- English proof (translation)
Establish `gen : ∀ f, (∃ T : Finset β, T.card ≤ k ∧ DepOn α β T f) → ∀ g, g ∈ lowDeg α β l → f * g ∈ lowDeg α β (k + l)`. Introduce `f ⟨T, hT, hfT⟩ g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg'`. Take `⟨T', hT', hgT⟩` from `hg'`.

Use `mem_lowDeg_of_depOn (T ∪ T') ((Finset.card_union_le _ _).trans (by omega)) _ ?_` and prove the remaining obligations. Introduce `n n' ha hb`. Simplify using `only [Pi.mul_apply]`. Rewrite using `[hfT n n' ha (fun b hb' => hb b (Finset.mem_union_left _ hb')), hgT n n' ha (fun b hb' => hb b (Finset.mem_union_right _ hb'))]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c hx`. Proceed by induction on `hf using Submodule.span_induction with`.

Consider the case `mem f hf' => exact gen f hf' g hg`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [smul_mul_assoc]`.

Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem mul_mem_lowDeg {k l : ℕ} {f g : (α ⊕ β → ℤ) → ℂ} (hf : f ∈ lowDeg α β k)
    (hg : g ∈ lowDeg α β l) : f * g ∈ lowDeg α β (k + l) := by
  classical
  have gen : ∀ f, (∃ T : Finset β, T.card ≤ k ∧ DepOn α β T f) → ∀ g, g ∈ lowDeg α β l →
      f * g ∈ lowDeg α β (k + l) := by
    intro f ⟨T, hT, hfT⟩ g hg
    induction hg using Submodule.span_induction with
    | mem g hg' =>
      obtain ⟨T', hT', hgT⟩ := hg'
      refine mem_lowDeg_of_depOn (T ∪ T') ((Finset.card_union_le _ _).trans (by omega)) _ ?_
      intro n n' ha hb
      simp only [Pi.mul_apply]
      rw [hfT n n' ha (fun b hb' => hb b (Finset.mem_union_left _ hb')),
        hgT n n' ha (fun b hb' => hb b (Finset.mem_union_right _ hb'))]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  induction hf using Submodule.span_induction with
  | mem f hf' => exact gen f hf' g hg
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty, Finset.sum_empty]`. Conclude with `mem_lowDeg_of_depOn ∅ le_rfl _ fun _ _ _ _ => rfl`. Consider the case `insert i s hi ih`.

Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi]`. Conclude with `mul_mem_lowDeg (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))`.
-/
theorem prod_mem_lowDeg {ι : Type} (s : Finset ι) (f : ι → (α ⊕ β → ℤ) → ℂ) (k : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ lowDeg α β (k i)) : ∏ i ∈ s, f i ∈ lowDeg α β (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact mem_lowDeg_of_depOn ∅ le_rfl _ fun _ _ _ _ => rfl
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_lowDeg (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg'`. Take `⟨T, hT, hgT⟩` from `hg'`. Introduce `L`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, b ∉ T := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use `Finset.card_le_card (fun b _ => hc b : (Finset.univ : Finset β) ⊆ T)` as an intermediate fact. Rewrite `this` using `[Finset.card_univ]`. Use linear arithmetic over natural numbers and integers.

Use `pol_eq_zero_of_indep _ (Sum.inr b) fun n v => ?_` and prove the remaining obligations. Use `congr 1`. Use `hgT _ _ (fun a => by simp) fun b' hb' => ?_` and prove the remaining obligations. Establish `: b' ≠ b` using `fun h => hb (h ▸ hb')`. Simplify using `[Function.update_apply, this]`.

Consider the case `zero => intro L`. Simplify using `[pol]`. Consider the case `add x y _ _ hx hy`. Introduce `L`. Establish `h1` using `hx L`.

Establish `h2` using `hy L`. Simplify using `only [pol] at h1 h2 ⊢`. Simplify using `only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]`. Consider the case `smul c x _ hx`. Introduce `L`.

Use `hx (L ∘ₗ LinearMap.mulLeft ℝ c)` as an intermediate fact. Simplify `this` using `[smul_eq_mul]`.
-/
theorem pol_eq_zero_of_mem_lowDeg {k : ℕ} (hk : k < Fintype.card β) {g : (α ⊕ β → ℤ) → ℂ}
    (hg : g ∈ lowDeg α β k) : ∀ L : ℂ →ₗ[ℝ] ℝ, pol (fun n => L (g n)) = 0 := by
  classical
  induction hg using Submodule.span_induction with
  | mem g hg' =>
    obtain ⟨T, hT, hgT⟩ := hg'
    intro L
    obtain ⟨b, hb⟩ : ∃ b, b ∉ T := by
      by_contra hc
      push_neg at hc
      have := Finset.card_le_card (fun b _ => hc b : (Finset.univ : Finset β) ⊆ T)
      rw [Finset.card_univ] at this
      omega
    refine pol_eq_zero_of_indep _ (Sum.inr b) fun n v => ?_
    congr 1
    refine hgT _ _ (fun a => by simp) fun b' hb' => ?_
    have : b' ≠ b := fun h => hb (h ▸ hb')
    simp [Function.update_apply, this]
  | zero => intro L; simp [pol]
  | add x y _ _ hx hy =>
    intro L
    have h1 := hx L
    have h2 := hy L
    simp only [pol] at h1 h2 ⊢
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]
  | smul c x _ hx =>
    intro L
    have := hx (L ∘ₗ LinearMap.mulLeft ℝ c)
    simpa [smul_eq_mul] using this

end GlobalTheory.FibreProj.DetPol

namespace GlobalTheory.FibreProj.DetPol

/- English proof (translation)
Rewrite using `[Matrix.det_fromBlocks_one₂₂, Matrix.neg_mul, sub_neg_eq_add]`. Use `congr 2`. Simplify using `only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem det_add_perturb_eq {D d : ℕ} {β : Type} [Fintype β] (A : Matrix (Fin D) (Fin D) ℂ)
    (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ) (K : β → Matrix (Fin d) (Fin d) ℂ)
    (c : β → ℂ) :
    Matrix.det (A + ∑ b, c b • (P * K b * Q)) =
      Matrix.det (Matrix.fromBlocks A (-(P * ∑ b, c b • K b)) Q 1) := by
  rw [Matrix.det_fromBlocks_one₂₂, Matrix.neg_mul, sub_neg_eq_add]
  congr 2
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Introduce `D d α β _ _ hd H P Q K`. Set `M : (α ⊕ β → ℤ) → Matrix (Fin D ⊕ Fin d) (Fin D ⊕ Fin d) ℂ` to `fun n => Matrix.fromBlocks (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a) (-(P * ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • K b)) Q 1`. Establish `hfun : (fun n : α ⊕ β → ℤ => (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a + ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re) = fun n => Complex.reLm ((M n).det)`. Use function extensionality and compare the values at `n`. Rewrite using `[det_add_perturb_eq]`.

Both sides reduce to the same expression. Rewrite using `[hfun]`. Use `pol_eq_zero_of_mem_lowDeg hd ?_ Complex.reLm` and prove the remaining obligations. Apply the tactic sequence `have hentry : ∀ r c : Fin D ⊕ Fin d, (fun n => M n r c) ∈ lowDeg α β (Sum.elim (fun _ => 0) (fun _ => 1) c) := by`. Introduce `r c`.

Break down `c with j | j` into its components or cases. Use `mem_lowDeg_of_depOn ∅ (by simp) _ fun n n' ha _ => ?_` and prove the remaining obligations. Break down `r with r | r` into its components or cases. Simplify using `[M, ha]`. Simplify using `[M]`.

Break down `r with r | r` into its components or cases. Establish `: (fun n => M n (Sum.inl r) (Sum.inr j)) = ∑ b, (-(P * K b) r j) • (fun n : α ⊕ β → ℤ => ((n (Sum.inr b) : ℝ) : ℂ))`. Use function extensionality and compare the values at `n`. Simplify using `[M, Matrix.mul_sum, Matrix.sum_apply, Matrix.mul_smul, Finset.sum_apply, mul_comm]`. Rewrite using `[this]`.

Use `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `mem_lowDeg_of_depOn {b} (by simp) _ fun n n' _ hb => ?_` and prove the remaining obligations. Simplify using `[hb b (Finset.mem_singleton_self b)]`. Conclude with `lowDeg_mono (Nat.zero_le 1) (mem_lowDeg_of_depOn ∅ (by simp) _ fun n n' _ _ => by simp [M])`. Establish `hdet : (fun n => (M n).det) = ∑ σ : Equiv.Perm (Fin D ⊕ Fin d), Equiv.Perm.sign σ • ∏ i, (fun n => M n (σ i) i)`.

Use function extensionality and compare the values at `n`. Simplify using `[Matrix.det_apply, Finset.sum_apply, Finset.prod_apply]`. Rewrite using `[show (fun n => (M n).det) = _ from hdet]`. Use `Submodule.sum_mem _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`.

Use `zsmul_mem ?_ _` and prove the remaining obligations. Apply the tactic sequence `have := prod_mem_lowDeg Finset.univ (fun i => fun n => M n (σ i) i) (fun i => Sum.elim (fun _ => 0) (fun _ => 1) i) (fun i _ => hentry (σ i) i)`. Simplify `this` using `[Fintype.sum_sum_type]`.
-/
theorem pol_det_perturb_eq_zero : ∀ (D d : ℕ) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β →
    ∀ (H : α → Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ)
      (K : β → Matrix (Fin d) (Fin d) ℂ),
    pol (fun n : α ⊕ β → ℤ => (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a +
      ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re) = 0 := by
  intro D d α β _ _ hd H P Q K
  classical
  let M : (α ⊕ β → ℤ) → Matrix (Fin D ⊕ Fin d) (Fin D ⊕ Fin d) ℂ := fun n =>
    Matrix.fromBlocks (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a)
      (-(P * ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • K b)) Q 1
  have hfun : (fun n : α ⊕ β → ℤ => (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a +
      ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re) =
      fun n => Complex.reLm ((M n).det) := by
    funext n
    rw [det_add_perturb_eq]
    rfl
  rw [hfun]
  refine pol_eq_zero_of_mem_lowDeg hd ?_ Complex.reLm
  have hentry : ∀ r c : Fin D ⊕ Fin d,
      (fun n => M n r c) ∈ lowDeg α β (Sum.elim (fun _ => 0) (fun _ => 1) c) := by
    intro r c
    rcases c with j | j
    · refine mem_lowDeg_of_depOn ∅ (by simp) _ fun n n' ha _ => ?_
      rcases r with r | r
      · simp [M, ha]
      · simp [M]
    · rcases r with r | r
      · have : (fun n => M n (Sum.inl r) (Sum.inr j)) =
            ∑ b, (-(P * K b) r j) • (fun n : α ⊕ β → ℤ => ((n (Sum.inr b) : ℝ) : ℂ)) := by
          funext n
          simp [M, Matrix.mul_sum, Matrix.sum_apply, Matrix.mul_smul, Finset.sum_apply, mul_comm]
        rw [this]
        refine Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
        refine mem_lowDeg_of_depOn {b} (by simp) _ fun n n' _ hb => ?_
        simp [hb b (Finset.mem_singleton_self b)]
      · exact lowDeg_mono (Nat.zero_le 1)
          (mem_lowDeg_of_depOn ∅ (by simp) _ fun n n' _ _ => by simp [M])
  have hdet : (fun n => (M n).det) =
      ∑ σ : Equiv.Perm (Fin D ⊕ Fin d), Equiv.Perm.sign σ • ∏ i, (fun n => M n (σ i) i) := by
    funext n
    simp [Matrix.det_apply, Finset.sum_apply, Finset.prod_apply]
  rw [show (fun n => (M n).det) = _ from hdet]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  have := prod_mem_lowDeg Finset.univ (fun i => fun n => M n (σ i) i)
    (fun i => Sum.elim (fun _ => 0) (fun _ => 1) i) (fun i _ => hentry (σ i) i)
  simpa [Fintype.sum_sum_type] using this

end GlobalTheory.FibreProj.DetPol

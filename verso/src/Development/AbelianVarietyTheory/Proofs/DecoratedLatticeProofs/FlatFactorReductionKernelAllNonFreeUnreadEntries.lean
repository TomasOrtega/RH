import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRead
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelReductionExtendEvaluatedIntegrated
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearMapKillingPartialEvalIntegralKernelTransla

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.FlatFactor.LowStage

section Shear
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

variable {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

end Shear

section Transv
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def tv (i j : Fin c) (h : i ≠ j) (a : k) : GL (Fin c) k :=
  ⟨transvection i j a, transvection i j (-a),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

end Transv

section PiLocalization₂
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)

open Classical in

def evStage (i : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  (evAll n n' c ρ).filter fun e => ∀ q, e.2 = Sum.inr q → q.val ≤ i

variable {n n' c ρ}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

end PiLocalization₂

open MeasureTheory ValuativeRel Matrix in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.FlatFactor.evC`. Simplify using `only [Finset.mem_filter_univ]`.
-/
private theorem mem_evC_iff (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ _root_.GlobalTheory.FlatFactor.evC n n' c ρ ↔
      (∃ i : Fin (c + 1), e.2 = Sum.inr i ∧ (i : ℕ) < ρ ∧ ¬_root_.GlobalTheory.RootEx.Free (ρ + 1) e) ∨
        ∃ l : Fin c, e.1 = Sum.inr l ∧ ρ ≤ (l : ℕ) ∧ ∀ i : Fin (c + 1), e.2 = Sum.inr i → (i : ℕ) = ρ := by
  unfold _root_.GlobalTheory.FlatFactor.evC
  simp only [Finset.mem_filter_univ]

open MeasureTheory ValuativeRel Matrix in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.FlatFactor.evAll`. Simplify using `only [Finset.mem_filter_univ]`.
-/
private theorem mem_evAll_iff (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ ↔
      ¬_root_.GlobalTheory.RootEx.Free (ρ + 1) e ∧ ¬_root_.GlobalTheory.FlatFactor.IsRead n n' c ρ e := by
  unfold _root_.GlobalTheory.FlatFactor.evAll
  simp only [Finset.mem_filter_univ]

open MeasureTheory ValuativeRel Matrix in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
/- English proof (translation)
Introduce `e hC`. Rewrite `hC` using `[mem_evC_iff]`. Rewrite using `[mem_evAll_iff]`. Apply the tactic sequence `obtain ⟨r | r, q | q⟩ := e <;>`. Apply the tactic sequence `simp [_root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.FlatFactor.IsRead] at hC ⊢ <;> omega`.
-/
private theorem evC_subset_evAll :
    _root_.GlobalTheory.FlatFactor.evC n n' c ρ ⊆ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ := by
  intro e hC
  rw [mem_evC_iff] at hC
  rw [mem_evAll_iff]
  obtain ⟨r | r, q | q⟩ := e <;>
    simp [_root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.FlatFactor.IsRead] at hC ⊢ <;> omega

open MeasureTheory ValuativeRel Matrix in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.FlatFactor.itB`. Simplify using `only [Finset.mem_filter_univ]`.
-/
private theorem mem_itB_iff (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ _root_.GlobalTheory.FlatFactor.itB n n' c ρ ↔
      _root_.GlobalTheory.RootEx.Free (ρ + 1) e ∧ ∀ i : Fin (c + 1), e.2 = Sum.inr i → ρ ≤ (i : ℕ) := by
  unfold _root_.GlobalTheory.FlatFactor.itB
  simp only [Finset.mem_filter_univ]

open MeasureTheory ValuativeRel Matrix in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
/- English proof (translation)
Use `Finset.disjoint_left.mpr fun e h1 h2 => ?_` and prove the remaining obligations. Rewrite `h1` using `[mem_evAll_iff]`. Rewrite `h2` using `[mem_itB_iff]`. Conclude with `h1.1 h2.1`.
-/
private theorem disjoint_evAll_itB :
    Disjoint (_root_.GlobalTheory.FlatFactor.evAll n n' c ρ) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) := by
  refine Finset.disjoint_left.mpr fun e h1 h2 => ?_
  rw [mem_evAll_iff] at h1
  rw [mem_itB_iff] at h2
  exact h1.1 h2.1

open MeasureTheory ValuativeRel Matrix in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
/- English proof (translation)
Rewrite `he` using `[mem_evAll_iff]`. Rewrite `hC` using `[mem_evC_iff]`. Apply the tactic sequence `obtain ⟨r | r, q | q⟩ := e <;>`. Apply the tactic sequence `simp [_root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.FlatFactor.IsRead] at he hC ⊢ <;> omega`.
-/
private theorem exists_inr_lt_le_of_mem_evAll_notMem_evC
    {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} (he : e ∈ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ)
    (hC : e ∉ _root_.GlobalTheory.FlatFactor.evC n n' c ρ) :
    ∃ (L : Fin c) (I : Fin (c + 1)), e = (Sum.inr L, Sum.inr I) ∧ ρ < (I : ℕ) ∧ (I : ℕ) ≤ L := by
  rw [mem_evAll_iff] at he
  rw [mem_evC_iff] at hC
  obtain ⟨r | r, q | q⟩ := e <;>
    simp [_root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.FlatFactor.IsRead] at he hC ⊢ <;> omega

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
/- English proof (translation)
Simplify using `only [_root_.GlobalTheory.RootEx.embA, _root_.GlobalTheory.FlatFactor.LowStage.tv]`. Use extensionality with `r s`. Apply the tactic sequence `rcases r with r | r <;> rcases s with s | s <;>`. Simplify using `[Matrix.transvection, Matrix.one_apply, Matrix.single_apply]`.
-/
private theorem embA_tv_eq_one_add_single (i j : Fin c) (h : i ≠ j) (a : k) :
    ((_root_.GlobalTheory.RootEx.embA n (_root_.GlobalTheory.FlatFactor.LowStage.tv i j h a) : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = 1 + single (Sum.inr i) (Sum.inr j) a := by
  simp only [_root_.GlobalTheory.RootEx.embA, _root_.GlobalTheory.FlatFactor.LowStage.tv]
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Take `⟨hlc, hcs⟩` from `hΘ`. Set `φ : Matrix m m' k ≃ₜ Matrix m m' k` to `{ toFun := fun t => (A : Matrix m m k) * t invFun := fun t => ((A⁻¹ : GL m k) : Matrix m m k) * t left_inv := fun t => by`. Simplify using `only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Use `right_inv := fun t => by`. Simplify using `only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`.

Use `continuous_toFun := continuous_const.matrix_mul continuous_id`. Use `continuous_invFun := continuous_const.matrix_mul continuous_id }`. Conclude with `⟨hlc.comp_continuous φ.continuous, hcs.comp_homeomorph φ⟩`.
-/
private theorem comp_left_mul_mem_SB {m m' : Type} [Fintype m] [DecidableEq m]
    [Fintype m'] (A : GL m k) {Θ : Matrix m m' k → ℂ} (hΘ : Θ ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix m m' k)) :
    (fun t => Θ ((A : Matrix m m k) * t)) ∈ _root_.GlobalTheory.SplitWeil.SB (Matrix m m' k) := by
  obtain ⟨hlc, hcs⟩ := hΘ
  let φ : Matrix m m' k ≃ₜ Matrix m m' k :=
    { toFun := fun t => (A : Matrix m m k) * t
      invFun := fun t => ((A⁻¹ : GL m k) : Matrix m m k) * t
      left_inv := fun t => by
        simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      right_inv := fun t => by
        simp only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }
  exact ⟨hlc.comp_continuous φ.continuous, hcs.comp_homeomorph φ⟩

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable [MeasurableSpace k] [BorelSpace k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
/- English proof (translation)
Use `haveI := _root_.GlobalTheory.SplitWeil.secondCountable k`. Use `haveI : T2Space k := (_root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2`. Use `set it := _root_.GlobalTheory.FlatFactor.itB n n' c ρ`. Use `set β := _root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) with hβdef`. Establish `key : ∀ t, _root_.GlobalTheory.FlatFactor.red ν ev it β ((Θ' - Θ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t = 0`.

Introduce `t`. Use `set X := _root_.GlobalTheory.FlatFactor.fill ev it β t with hXdef`. Establish `hX : ∀ a r q, X a r q = if h : (r, q) ∈ it then a ⟨(r, q), h⟩ else if (r, q) ∈ ev then β r q else t r q` using `fun _ _ _ => rfl`. Establish `hXc : Continuous X` using `_root_.GlobalTheory.FlatFactor.continuous_fill ev it β t`. Set `f : ↥it → (↥it → k) → k` to `fun p a => if p.1.1 = Sum.inr i₀ then s * X a (Sum.inr j) p.1.2 else 0`.

Set `rk : ↥it → ℕ` to `fun p => Sum.elim (fun _ => 0) (fun r : Fin c => c - (r : ℕ)) p.1.1`. Establish `hfm : ∀ p, Measurable (f p)`. Introduce `p`. Distinguish the cases in `hp : p.1.1 = Sum.inr i₀`. Simplify using `only [f, hp, if_true]`.

Conclude with `(continuous_const.mul ((continuous_apply _).comp ((continuous_apply _).comp hXc))).measurable`. Simplify using `only [f, hp, if_false]`. Conclude with `measurable_const`. Establish `hfd : ∀ (p : ↥it) (x y : ↥it → k), (∀ q, rk q < rk p → x q = y q) → f p x = f p y`. Introduce `p x y hxy`.

Distinguish the cases in `hp : p.1.1 = Sum.inr i₀`. Simplify using `only [f, hp, if_true, hX] split_ifs with h1 h2`. Use `congr 1`. Apply `hxy` to reduce the goal to its premises. Simplify using `only [rk, hp, Sum.elim_inr]`.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Both sides reduce to the same expression. Simplify using `only [f, hp, if_false]`. Establish `hmp` using `_root_.GlobalTheory.SgLoc.TriShift.measurePreserving_triangular ν rk f hfm hfd`.

Establish `hshear : ∀ a, X (fun p => a p + f p a) = (1 + single (Sum.inr i₀) (Sum.inr j) s : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * X a`. Introduce `a`. Use extensionality with `r q`. Rewrite using `[_root_.Matrix.add_mul, _root_.Matrix.one_mul, _root_.Matrix.add_apply]`. Distinguish the cases in `hr : r = Sum.inr i₀`.

Substitute `hr` using the available equality. Rewrite using `[single_mul_apply_same, hX, hX]`. Distinguish the cases in `hit : (Sum.inr i₀, q) ∈ it`. Simplify using `only [hit, dite_true, f, if_true]`. Simplify using `only [hit, dite_false]`.

Establish `hz : X a (Sum.inr j) q = 0`. Rewrite `hit` using `[mem_itB_iff]`. Establish `hnit : (Sum.inr j, q) ∉ it`. Rewrite using `[mem_itB_iff]`. Apply the tactic sequence `rcases q with q | q <;> simp [_root_.GlobalTheory.RootEx.Free] at hit ⊢ <;> omega`.

Establish `hev : (Sum.inr j, q) ∈ ev`. Apply `hcov` to reduce the goal to its premises. Rewrite using `[mem_evAll_iff]`. Apply the tactic sequence `rcases q with q | q <;> simp [_root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.FlatFactor.IsRead] at hit ⊢ <;> omega`. Introduce `q' hq'`.

Simplify using `only at hq'`. Substitute `hq'` using the available equality. Simplify using `[_root_.GlobalTheory.RootEx.Free] at hit`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hX, dif_neg hnit, if_pos hev]`.

Break down `q with q | q` into its components or cases. Simplify using `[hβdef, _root_.GlobalTheory.RootEx.basePt]`. Simplify using `[_root_.GlobalTheory.RootEx.Free] at hit`. Apply the tactic sequence `simp [hβdef, _root_.GlobalTheory.RootEx.basePt] <;> omega`. Rewrite using `[hz, mul_zero, add_zero]`.

Apply the tactic sequence `rw [single_mul_apply_of_ne (h := hr), add_zero, hX, hX] split_ifs with h1 <;> simp [f, hr]`. Establish `hI : ∀ Φ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), Integrable (fun a => (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a)) (Measure.pi fun _ => ν)`. Introduce `Φ`. Take `⟨hlc, hcs⟩` from `Φ.2`. Conclude with `(hlc.continuous.comp hXc).integrable_of_hasCompactSupport (_root_.GlobalTheory.FlatFactor.hasCompactSupport_comp_fill ev it β t _ hcs)`.

Establish `hcomp : ∫ a, (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X (fun p => a p + f p a)) ∂(Measure.pi fun _ => ν) = ∫ a, (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a) ∂(Measure.pi fun _ => ν)`. Establish `hg' : AEStronglyMeasurable (fun a => (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a)) (Measure.map (fun a p => a p + f p a) (Measure.pi fun _ => ν))`. Rewrite using `[hmp.map_eq]`. Conclude with `(hI Θ).aestronglyMeasurable`. Combine the equalities or inequalities in the displayed calculation.

Express the relevant statement in the definitionally equal form `∫ a, ((Θ' - Θ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a) ∂(Measure.pi fun _ => ν) = 0`. Simplify using `only [Submodule.coe_sub, Pi.sub_apply]`. Rewrite using `[integral_sub (hI Θ') (hI Θ), sub_eq_zero]`. Simplify using `only [hΘ', ← hshear]`. Conclude with `hcomp`.

Establish `h` using `hker (Θ' - Θ) key`. Rewrite `h` using `[map_sub, sub_eq_zero]`. Conclude with `h`.
-/
private theorem killsKernel_rowShear_invariant_lemma_10 (ν : Measure k) [ν.IsAddHaarMeasure]
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (l : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (ev : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (i₀ j : Fin c) (hρ : ρ ≤ (i₀ : ℕ))
    (hij : (i₀ : ℕ) < j)
    (hcov : ∀ e ∈ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ,
      (∀ q : Fin (c + 1), e.2 = Sum.inr q → (q : ℕ) ≤ i₀) → e ∈ ev)
    (hker : _root_.GlobalTheory.FlatFactor.KerRed ν ev (_root_.GlobalTheory.FlatFactor.itB n n' c ρ)
      (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l)
    (s : k) (Θ Θ' : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΘ' : ∀ t, (Θ' : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t =
      (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) ((1 + single (Sum.inr i₀) (Sum.inr j) s : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t)) :
    l Θ' = l Θ := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  haveI : T2Space k := (_root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  set it := _root_.GlobalTheory.FlatFactor.itB n n' c ρ
  set β := _root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) with hβdef
  have key : ∀ t, _root_.GlobalTheory.FlatFactor.red ν ev it β
      ((Θ' - Θ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
        Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t = 0 := by
    intro t
    set X := _root_.GlobalTheory.FlatFactor.fill ev it β t with hXdef
    have hX : ∀ a r q, X a r q = if h : (r, q) ∈ it then a ⟨(r, q), h⟩ else if (r, q) ∈ ev then β r q else t r q :=
      fun _ _ _ => rfl
    have hXc : Continuous X := _root_.GlobalTheory.FlatFactor.continuous_fill ev it β t
    let f : ↥it → (↥it → k) → k := fun p a =>
      if p.1.1 = Sum.inr i₀ then s * X a (Sum.inr j) p.1.2 else 0
    let rk : ↥it → ℕ := fun p => Sum.elim (fun _ => 0) (fun r : Fin c => c - (r : ℕ)) p.1.1
    have hfm : ∀ p, Measurable (f p) := by
      intro p
      by_cases hp : p.1.1 = Sum.inr i₀
      · simp only [f, hp, if_true]
        exact (continuous_const.mul ((continuous_apply _).comp
          ((continuous_apply _).comp hXc))).measurable
      · simp only [f, hp, if_false]
        exact measurable_const
    have hfd : ∀ (p : ↥it) (x y : ↥it → k), (∀ q, rk q < rk p → x q = y q) → f p x = f p y := by
      intro p x y hxy
      by_cases hp : p.1.1 = Sum.inr i₀
      · simp only [f, hp, if_true, hX]
        split_ifs with h1 h2
        · congr 1
          apply hxy
          simp only [rk, hp, Sum.elim_inr]
          omega
        · rfl
        · rfl
      · simp only [f, hp, if_false]
    have hmp := _root_.GlobalTheory.SgLoc.TriShift.measurePreserving_triangular ν rk f hfm hfd
    have hshear : ∀ a, X (fun p => a p + f p a) = (1 + single (Sum.inr i₀) (Sum.inr j) s : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * X a := by
      intro a
      ext r q
      rw [_root_.Matrix.add_mul, _root_.Matrix.one_mul, _root_.Matrix.add_apply]
      by_cases hr : r = Sum.inr i₀
      · subst hr
        rw [single_mul_apply_same, hX, hX]
        by_cases hit : (Sum.inr i₀, q) ∈ it
        · simp only [hit, dite_true, f, if_true]
        · simp only [hit, dite_false]
          have hz : X a (Sum.inr j) q = 0 := by
            rw [mem_itB_iff] at hit
            have hnit : (Sum.inr j, q) ∉ it := by
              rw [mem_itB_iff]
              rcases q with q | q <;> simp [_root_.GlobalTheory.RootEx.Free] at hit ⊢ <;> omega
            have hev : (Sum.inr j, q) ∈ ev := by
              apply hcov
              · rw [mem_evAll_iff]
                rcases q with q | q <;> simp [_root_.GlobalTheory.RootEx.Free, _root_.GlobalTheory.FlatFactor.IsRead] at hit ⊢ <;> omega
              · intro q' hq'
                simp only at hq'
                subst hq'
                simp [_root_.GlobalTheory.RootEx.Free] at hit
                omega
            rw [hX, dif_neg hnit, if_pos hev]
            rcases q with q | q
            · simp [hβdef, _root_.GlobalTheory.RootEx.basePt]
            · simp [_root_.GlobalTheory.RootEx.Free] at hit
              simp [hβdef, _root_.GlobalTheory.RootEx.basePt] <;> omega
          rw [hz, mul_zero, add_zero]
      · rw [single_mul_apply_of_ne (h := hr), add_zero, hX, hX]
        split_ifs with h1 <;> simp [f, hr]
    have hI : ∀ Φ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
        Integrable (fun a => (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a))
          (Measure.pi fun _ => ν) := by
      intro Φ
      obtain ⟨hlc, hcs⟩ := Φ.2
      exact (hlc.continuous.comp hXc).integrable_of_hasCompactSupport
        (_root_.GlobalTheory.FlatFactor.hasCompactSupport_comp_fill ev it β t _ hcs)
    have hcomp : ∫ a, (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X (fun p => a p + f p a))
          ∂(Measure.pi fun _ => ν) =
        ∫ a, (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a) ∂(Measure.pi fun _ => ν) := by
      have hg' : AEStronglyMeasurable (fun a => (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a))
          (Measure.map (fun a p => a p + f p a) (Measure.pi fun _ => ν)) := by
        rw [hmp.map_eq]
        exact (hI Θ).aestronglyMeasurable
      calc _ = ∫ y, (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X y)
            ∂(Measure.map (fun a p => a p + f p a) (Measure.pi fun _ => ν)) :=
              (integral_map hmp.measurable.aemeasurable hg').symm
        _ = _ := by rw [hmp.map_eq]
    change ∫ a, ((Θ' - Θ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
      Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (X a) ∂(Measure.pi fun _ => ν) = 0
    simp only [Submodule.coe_sub, Pi.sub_apply]
    rw [integral_sub (hI Θ') (hI Θ), sub_eq_zero]
    simp only [hΘ', ← hshear]
    exact hcomp
  have h := hker (Θ' - Θ) key
  rw [map_sub, sub_eq_zero] at h
  exact h

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ : ℕ} in
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] in
/- English proof (translation)
Use `set i₀ : Fin c := ⟨(I : ℕ) - 1, by omega⟩ with hi₀`. Establish `hi₀v : (i₀ : ℕ) = (I : ℕ) - 1` using `rfl`. Establish `hi₀L : i₀ ≠ L`. Introduce `h`. Rewrite `h` using `[Fin.ext_iff, hi₀v]`.

Use linear arithmetic over natural numbers and integers. Establish `hsucc : i₀.succ = I`. Use `ext`. Rewrite using `[Fin.val_succ, hi₀v]`. Use linear arithmetic over natural numbers and integers.

Use `set u := _root_.GlobalTheory.FlatFactor.LowStage.tv i₀ L hi₀L b with hu`. Establish `hg : ((_root_.GlobalTheory.RootEx.embA n u : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = 1 + single (Sum.inr i₀) (Sum.inr L) b` using `embA_tv_eq_one_add_single _ _ _ _`. Establish `hginv : (((_root_.GlobalTheory.RootEx.embA n u)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = 1 + single (Sum.inr i₀) (Sum.inr L) (-b)`. Rewrite using `[← map_inv, show u⁻¹ = _root_.GlobalTheory.FlatFactor.LowStage.tv i₀ L hi₀L (-b) from Units.ext rfl]`. Conclude with `embA_tv_eq_one_add_single _ _ _ _`.

Establish `hmem : _root_.GlobalTheory.RootEx.embA n u ∈ _root_.GlobalTheory.RootEx.N k n c (ρ + 1)`. Rewrite using `[_root_.GlobalTheory.RootEx.Model.mem_N_iff]`. Introduce `r s hrs`. Rewrite using `[hg, _root_.Matrix.add_apply, Matrix.single_apply, if_neg, add_zero]`. Introduce and unpack `⟨rfl, rfl⟩`.

Simplify using `[_root_.GlobalTheory.RootEx.lev] at hrs`. Use linear arithmetic over natural numbers and integers. Establish `hblock : ∀ i j : Fin c, (i : ℕ) < ρ → ρ ≤ (j : ℕ) → (u : Matrix (Fin c) (Fin c) k) i j = 0`. Introduce `i j hi hj`. Establish `hne : i ≠ j`.

Introduce `h`. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Establish `hne' : i ≠ i₀`. Introduce `h`.

Rewrite `h` using `[Fin.ext_iff, hi₀v]`. Use linear arithmetic over natural numbers and integers. Simplify using `[hu, _root_.GlobalTheory.FlatFactor.LowStage.tv, Matrix.transvection, Matrix.one_apply, hne, Matrix.single_apply, hne', Ne.symm hne']`. Take `⟨Θu, hΘu⟩ : ∃ Θu : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ t, (Θu : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t = (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) ((((_root_.GlobalTheory.RootEx.embA n u)⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n …` from `⟨⟨_, comp_left_mul_mem_SB _ Θ.2⟩, fun _ => rfl⟩`. Use `set β := _root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) (Sum.inr L) (Sum.inr I) with hβ`.

Establish `hchar : ∀ t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k, _root_.GlobalTheory.RootEx.ch (((_root_.GlobalTheory.RootEx.embA n u : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) - _root_.GlobalTheory.RootEx.ch t = b * t (Sum.inr L) (Sum.inr I)`. Introduce `t`. Rewrite using `[hg, _root_.Matrix.add_mul, _root_.Matrix.one_mul]`. Simplify using `only [_root_.GlobalTheory.RootEx.ch, _root_.Matrix.add_apply, Finset.sum_add_distrib, add_sub_cancel_left]`. Rewrite using `[Fintype.sum_eq_single i₀, single_mul_apply_same, hsucc]`.

Introduce `i hi`. Conclude with `single_mul_apply_of_ne (h := by simpa using hi) ..`. Establish `hI' : (I : ℕ) = (i₀ : ℕ) + 1`. Rewrite using `[hi₀v]`. Use linear arithmetic over natural numbers and integers.

Establish `hlt : (i₀ : ℕ) < L` using `by omega`. Establish `hβv : β = if (L : ℕ) = (i₀ : ℕ) + 1 then 1 else 0`. Rewrite using `[hβ]`. Simplify using `[_root_.GlobalTheory.RootEx.basePt, hI']`. Establish `hsum : _root_.GlobalTheory.RootEx.simpleSum (_root_.GlobalTheory.RootEx.embA n u) = b * β`.

Unfold `_root_.GlobalTheory.RootEx.simpleSum`. Rewrite using `[hg, hβv, Fintype.sum_eq_single i₀, Fintype.sum_eq_single L]`. Apply the tactic sequence `by_cases h : (L : ℕ) = (i₀ : ℕ) + 1 <;>`. Apply the tactic sequence `simp [h, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff] <;> omega`. Introduce `j hj`.

Apply the tactic sequence `by_cases h : (j : ℕ) = (i₀ : ℕ) + 1 <;>`. Apply the tactic sequence `simp [h, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hj] <;> omega`. Introduce `i hi`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`.

Apply the tactic sequence `by_cases h : (j : ℕ) = (i : ℕ) + 1 <;>`. Apply the tactic sequence `simp [h, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hi] <;> omega`. Establish `hTw'` using `hTw u hmem hblock Θ Θu ((ψ (b * β) : ℂ) • Θ') hΘu (by`. Introduce `t`. Rewrite using `[Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hΘ', hchar, ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, show b * β + b * (t (Sum.inr L) (Sum.inr I) - β) = b * t (Sum.inr L) (Sum.inr I) by ring])`.

Establish `hinv : l Θu = l Θ` using `killsKernel_rowShear_invariant_lemma_10 ν l ev i₀ L (by omega) (by omega) (fun e he hcol => hcov e he fun q hq => by have := hcol q hq; omega) hker (-b) Θ Θu (fun t => by rw [hΘu, hginv])`. Rewrite `hTw'` using `[hinv, map_smul, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, hsum, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one, one_smul]`. Conclude with `hTw'.symm`.
-/
private theorem twist_invariant_of_lowerEntry_lemma_4 (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] {M : Type} [AddCommGroup M] [Module ℂ M]
    (l : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hTw : _root_.GlobalTheory.FlatFactor.TwLaw ρ ψ l)
    (ev : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (L : Fin c) (I : Fin (c + 1))
    (hρI : ρ < (I : ℕ)) (hIL : (I : ℕ) ≤ L)
    (hcov : ∀ e ∈ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ,
      (∀ q : Fin (c + 1), e.2 = Sum.inr q → (q : ℕ) < I) → e ∈ ev)
    (hker : _root_.GlobalTheory.FlatFactor.KerRed ν ev (_root_.GlobalTheory.FlatFactor.itB n n' c ρ)
      (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l)
    (b : k) (Θ Θ' : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΘ' : ∀ t, (Θ' : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t =
      (ψ (b * (t (Sum.inr L) (Sum.inr I) -
        _root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) (Sum.inr L) (Sum.inr I))) : ℂ) *
        (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t) :
    l Θ' = l Θ := by
  set i₀ : Fin c := ⟨(I : ℕ) - 1, by omega⟩ with hi₀
  have hi₀v : (i₀ : ℕ) = (I : ℕ) - 1 := rfl
  have hi₀L : i₀ ≠ L := by
    intro h
    rw [Fin.ext_iff, hi₀v] at h
    omega
  have hsucc : i₀.succ = I := by
    ext
    rw [Fin.val_succ, hi₀v]
    omega
  set u := _root_.GlobalTheory.FlatFactor.LowStage.tv i₀ L hi₀L b with hu
  have hg : ((_root_.GlobalTheory.RootEx.embA n u : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = 1 + single (Sum.inr i₀) (Sum.inr L) b :=
    embA_tv_eq_one_add_single _ _ _ _
  have hginv : (((_root_.GlobalTheory.RootEx.embA n u)⁻¹ : GL (n ⊕ Fin c) k) :
      Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = 1 + single (Sum.inr i₀) (Sum.inr L) (-b) := by
    rw [← map_inv, show u⁻¹ = _root_.GlobalTheory.FlatFactor.LowStage.tv i₀ L hi₀L (-b) from Units.ext rfl]
    exact embA_tv_eq_one_add_single _ _ _ _
  have hmem : _root_.GlobalTheory.RootEx.embA n u ∈ _root_.GlobalTheory.RootEx.N k n c (ρ + 1) := by
    rw [_root_.GlobalTheory.RootEx.Model.mem_N_iff]
    intro r s hrs
    rw [hg, _root_.Matrix.add_apply, Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    simp [_root_.GlobalTheory.RootEx.lev] at hrs
    omega
  have hblock : ∀ i j : Fin c, (i : ℕ) < ρ → ρ ≤ (j : ℕ) →
      (u : Matrix (Fin c) (Fin c) k) i j = 0 := by
    intro i j hi hj
    have hne : i ≠ j := by
      intro h
      subst h
      omega
    have hne' : i ≠ i₀ := by
      intro h
      rw [Fin.ext_iff, hi₀v] at h
      omega
    simp [hu, _root_.GlobalTheory.FlatFactor.LowStage.tv, Matrix.transvection, Matrix.one_apply, hne,
      Matrix.single_apply, hne', Ne.symm hne']
  obtain ⟨Θu, hΘu⟩ : ∃ Θu : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      ∀ t, (Θu : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) t =
        (Θ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
          ((((_root_.GlobalTheory.RootEx.embA n u)⁻¹ : GL (n ⊕ Fin c) k) :
            Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) :=
    ⟨⟨_, comp_left_mul_mem_SB _ Θ.2⟩, fun _ => rfl⟩
  set β := _root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) (Sum.inr L) (Sum.inr I) with hβ
  have hchar : ∀ t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k,
      _root_.GlobalTheory.RootEx.ch (((_root_.GlobalTheory.RootEx.embA n u : GL (n ⊕ Fin c) k) :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * t) - _root_.GlobalTheory.RootEx.ch t =
        b * t (Sum.inr L) (Sum.inr I) := by
    intro t
    rw [hg, _root_.Matrix.add_mul, _root_.Matrix.one_mul]
    simp only [_root_.GlobalTheory.RootEx.ch, _root_.Matrix.add_apply, Finset.sum_add_distrib,
      add_sub_cancel_left]
    rw [Fintype.sum_eq_single i₀, single_mul_apply_same, hsucc]
    intro i hi
    exact single_mul_apply_of_ne (h := by simpa using hi) ..
  have hI' : (I : ℕ) = (i₀ : ℕ) + 1 := by
    rw [hi₀v]
    omega
  have hlt : (i₀ : ℕ) < L := by omega
  have hβv : β = if (L : ℕ) = (i₀ : ℕ) + 1 then 1 else 0 := by
    rw [hβ]
    simp [_root_.GlobalTheory.RootEx.basePt, hI']
  have hsum : _root_.GlobalTheory.RootEx.simpleSum (_root_.GlobalTheory.RootEx.embA n u) = b * β := by
    unfold _root_.GlobalTheory.RootEx.simpleSum
    rw [hg, hβv, Fintype.sum_eq_single i₀, Fintype.sum_eq_single L]
    · by_cases h : (L : ℕ) = (i₀ : ℕ) + 1 <;>
        simp [h, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff] <;> omega
    · intro j hj
      by_cases h : (j : ℕ) = (i₀ : ℕ) + 1 <;>
        simp [h, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hj] <;> omega
    · intro i hi
      apply Finset.sum_eq_zero
      intro j _
      by_cases h : (j : ℕ) = (i : ℕ) + 1 <;>
        simp [h, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hi] <;> omega
  have hTw' := hTw u hmem hblock Θ Θu ((ψ (b * β) : ℂ) • Θ') hΘu (by
    intro t
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hΘ', hchar, ← mul_assoc, ← Circle.coe_mul,
      ← AddChar.map_add_eq_mul,
      show b * β + b * (t (Sum.inr L) (Sum.inr I) - β) = b * t (Sum.inr L) (Sum.inr I) by ring])
  have hinv : l Θu = l Θ :=
    killsKernel_rowShear_invariant_lemma_10 ν l ev i₀ L (by omega) (by omega)
      (fun e he hcol => hcov e he fun q hq => by have := hcol q hq; omega) hker (-b) Θ Θu
      (fun t => by rw [hΘu, hginv])
  rw [hinv, map_smul, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, hsum, neg_add_cancel,
    AddChar.map_zero_eq_one, Circle.coe_one, one_smul] at hTw'
  exact hTw'.symm

open MeasureTheory ValuativeRel Matrix in

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ψ ν hψ hψ1 hν n n' _ _ _ _ c ρ M _ _ l _ hTw hC`. Use `haveI := hν`. Establish `hstage_sub : ∀ j, _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j ⊆ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ` using `fun j => Finset.filter_subset _ _`. Establish `hmem_stage : ∀ (j : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))), e ∈ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j ↔ e ∈ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ ∧ ∀ q : Fin (c + 1), e.2 = Sum.inr q → (q : ℕ) ≤ j` using `fun j e => Finset.mem_filter`. Establish `hsub : ∀ j, _root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j ⊆ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ` using `fun j => Finset.union_subset evC_subset_evAll (hstage_sub j)`.

Establish `hdisj : ∀ j, Disjoint (_root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ)` using `fun j => disjoint_evAll_itB.mono_left (hsub j)`. Establish `hstep : ∀ j, _root_.GlobalTheory.FlatFactor.KerRed ν (_root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`.

Use `_root_.GlobalTheory.FlatFactor.KerRedStep.kerRed_extend k ψ ν hψ hψ1 hν _ _ M l _ _ _ _ _ Finset.subset_union_left Finset.Subset.rfl (hdisj 0) hC ?_ (fun e h1 h2 => absurd h1 h2)` and prove the remaining obligations. Introduce `e he heC`. It suffices to derive a contradiction. Break down `Finset.mem_union.1 he with h | h` into its components or cases. Conclude with `heC h`.

Take `⟨L, I, rfl, hρI, hIL⟩` from `exists_inr_lt_le_of_mem_evAll_notMem_evC (hstage_sub 0 h) heC`. Use `((hmem_stage 0 _).1 h).2 I rfl` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Consider the case `succ j ih`. Use `_root_.GlobalTheory.FlatFactor.KerRedStep.kerRed_extend k ψ ν hψ hψ1 hν _ _ M l _ _ _ _ _ ?_ Finset.Subset.rfl (hdisj (j + 1)) ih ?_ (fun e h1 h2 => absurd h1 h2)` and prove the remaining obligations.

Use `Finset.union_subset_union Finset.Subset.rfl fun e he => (hmem_stage _ e).2 ⟨((hmem_stage _ e).1 he).1, fun q hq => ?_⟩` and prove the remaining obligations. Use `((hmem_stage _ e).1 he).2 q hq` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `e he hne`. Establish `heC : e ∉ _root_.GlobalTheory.FlatFactor.evC n n' c ρ` using `fun h => hne (Finset.mem_union_left _ h)`.

Establish `hest : e ∈ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ (j + 1)`. Break down `Finset.mem_union.1 he with h | h` into its components or cases. Conclude with `absurd h heC`. Conclude with `h`. Take `⟨L, I, rfl, hρI, hIL⟩` from `exists_inr_lt_le_of_mem_evAll_notMem_evC (hstage_sub _ hest) heC`.

Establish `hI1 : (I : ℕ) ≤ j + 1` using `((hmem_stage _ _).1 hest).2 I rfl`. Establish `hI2 : ¬ (I : ℕ) ≤ j` using `fun h => hne (Finset.mem_union_right _ ((hmem_stage _ _).2 ⟨hstage_sub _ hest, fun q hq => by`. Establish `hqI` using `Sum.inr_injective hq`. Substitute `hqI` using the available equality. Conclude with `h⟩))`.

Introduce `b Θ Θ' hΘ'`. Conclude with `twist_invariant_of_lowerEntry_lemma_4 ψ ν l hTw _ L I hρI hIL (fun e' he' hcol => Finset.mem_union_right _ ((hmem_stage _ _).2 ⟨he', fun q hq => by`. Use `hcol q hq` as an intermediate fact. Use the proof step `omega⟩)) ih b Θ Θ' hΘ'`. Establish `hall : _root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ c = _root_.GlobalTheory.FlatFactor.evAll n n' c ρ`.

Apply `Finset.Subset.antisymm (hsub c)` to reduce the goal to its premises. Introduce `e he`. Conclude with `Finset.mem_union_right _ ((hmem_stage _ _).2 ⟨he, fun q _ => Nat.lt_succ_iff.1 q.2⟩)`. Rewrite using `[← hall]`. Conclude with `hstep c`.
-/
theorem _root_.GlobalTheory.FlatFactor.LowStage.kerRed_evAll : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (l : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → _root_.GlobalTheory.FlatFactor.TwLaw ρ ψ l → _root_.GlobalTheory.FlatFactor.KerRed ν (_root_.GlobalTheory.FlatFactor.evC n n' c ρ) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l → _root_.GlobalTheory.FlatFactor.KerRed ν (_root_.GlobalTheory.FlatFactor.evAll n n' c ρ) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν n n' _ _ _ _ c ρ M _ _ l _ hTw hC
  haveI := hν
  have hstage_sub : ∀ j, _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j ⊆
      _root_.GlobalTheory.FlatFactor.evAll n n' c ρ := fun j => Finset.filter_subset _ _
  have hmem_stage : ∀ (j : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))),
      e ∈ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j ↔
        e ∈ _root_.GlobalTheory.FlatFactor.evAll n n' c ρ ∧
          ∀ q : Fin (c + 1), e.2 = Sum.inr q → (q : ℕ) ≤ j := fun j e => Finset.mem_filter
  have hsub : ∀ j, _root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j ⊆
      _root_.GlobalTheory.FlatFactor.evAll n n' c ρ :=
    fun j => Finset.union_subset evC_subset_evAll (hstage_sub j)
  have hdisj : ∀ j, Disjoint (_root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪
      _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) :=
    fun j => disjoint_evAll_itB.mono_left (hsub j)
  have hstep : ∀ j, _root_.GlobalTheory.FlatFactor.KerRed ν
      (_root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ j)
      (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l := by
    intro j
    induction j with
    | zero =>
      refine _root_.GlobalTheory.FlatFactor.KerRedStep.kerRed_extend k ψ ν hψ hψ1 hν _ _ M l _ _ _ _ _
        Finset.subset_union_left Finset.Subset.rfl (hdisj 0) hC ?_ (fun e h1 h2 => absurd h1 h2)
      intro e he heC
      exfalso
      rcases Finset.mem_union.1 he with h | h
      · exact heC h
      obtain ⟨L, I, rfl, hρI, hIL⟩ := exists_inr_lt_le_of_mem_evAll_notMem_evC (hstage_sub 0 h) heC
      have := ((hmem_stage 0 _).1 h).2 I rfl
      omega
    | succ j ih =>
      refine _root_.GlobalTheory.FlatFactor.KerRedStep.kerRed_extend k ψ ν hψ hψ1 hν _ _ M l _ _ _ _ _ ?_
        Finset.Subset.rfl (hdisj (j + 1)) ih ?_ (fun e h1 h2 => absurd h1 h2)
      · refine Finset.union_subset_union Finset.Subset.rfl fun e he => (hmem_stage _ e).2
          ⟨((hmem_stage _ e).1 he).1, fun q hq => ?_⟩
        have := ((hmem_stage _ e).1 he).2 q hq
        omega
      intro e he hne
      have heC : e ∉ _root_.GlobalTheory.FlatFactor.evC n n' c ρ := fun h => hne (Finset.mem_union_left _ h)
      have hest : e ∈ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ (j + 1) := by
        rcases Finset.mem_union.1 he with h | h
        · exact absurd h heC
        · exact h
      obtain ⟨L, I, rfl, hρI, hIL⟩ := exists_inr_lt_le_of_mem_evAll_notMem_evC (hstage_sub _ hest) heC
      have hI1 : (I : ℕ) ≤ j + 1 := ((hmem_stage _ _).1 hest).2 I rfl
      have hI2 : ¬ (I : ℕ) ≤ j := fun h => hne (Finset.mem_union_right _ ((hmem_stage _ _).2
        ⟨hstage_sub _ hest, fun q hq => by
          have hqI := Sum.inr_injective hq
          subst hqI
          exact h⟩))
      intro b Θ Θ' hΘ'
      exact twist_invariant_of_lowerEntry_lemma_4 ψ ν l hTw _ L I hρI hIL
        (fun e' he' hcol => Finset.mem_union_right _ ((hmem_stage _ _).2 ⟨he', fun q hq => by
          have := hcol q hq
          omega⟩)) ih b Θ Θ' hΘ'
  have hall : _root_.GlobalTheory.FlatFactor.evC n n' c ρ ∪ _root_.GlobalTheory.FlatFactor.LowStage.evStage n n' c ρ c =
      _root_.GlobalTheory.FlatFactor.evAll n n' c ρ := by
    apply Finset.Subset.antisymm (hsub c)
    intro e he
    exact Finset.mem_union_right _ ((hmem_stage _ _).2 ⟨he, fun q _ => Nat.lt_succ_iff.1 q.2⟩)
  rw [← hall]
  exact hstep c

end GlobalTheory.FlatFactor.LowStage

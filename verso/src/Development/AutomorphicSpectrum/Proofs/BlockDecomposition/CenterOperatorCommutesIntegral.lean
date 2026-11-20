import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace Topology
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ZOpAvg

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isOpen_invertible_matrices (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne.preimage (Continuous.matrix_det continuous_id)

def Sm (U : ℝ → Mat n → V) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)

section Gen

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem fderiv_slice {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {t : ℝ} {x : E} (hx : x ∈ S) :
    HasFDerivAt (U t) ((fderiv ℝ (Function.uncurry U) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  have hd : DifferentiableAt ℝ (Function.uncurry U) (t, x) :=
    (hU.contDiffAt ((isOpen_univ.prod hS).mem_nhds ⟨Set.mem_univ _, hx⟩)).differentiableAt (by simp)
  have hi : HasFDerivAt (fun y : E => (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    hasFDerivAt_prodMk_right t x
  exact hd.hasFDerivAt.comp x hi

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules.
-/
theorem gen_sm {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {c : E → E} (hc : ContDiff ℝ ∞ c) :
    ContDiffOn ℝ ∞ (Function.uncurry fun t x => fderiv ℝ (U t) x (c x)) (Set.univ ×ˢ S) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × E => ((0 : ℝ), c p.2)) :=
    contDiff_const.prodMk (hc.comp contDiff_snd)
  have h0 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry U)) (Set.univ ×ˢ S) :=
    ContDiffOn.fderiv_of_isOpen hU (isOpen_univ.prod hS) (by simp)
  have h2 := h0.clm_apply h1.contDiffOn
  refine h2.congr ?_
  rintro ⟨t, x⟩ ⟨-, hx⟩
  simp [Function.uncurry, (fderiv_slice hS hU hx).fderiv]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem int_real {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {φ : ℝ → W} (hφ : Continuous φ) : Integrable (fun t => g t • φ t) := by
  refine Continuous.integrable_of_hasCompactSupport (hg.smul hφ) ?_
  exact hgc.smul_right

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem gen_avg [ProperSpace E] [CompleteSpace W] {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {x : E} (hx : x ∈ S) (v : E) :
    fderiv ℝ (fun x' => ∫ t, g t • U t x') x v = ∫ t, g t • fderiv ℝ (U t) x v := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hS.mem_nhds hx)
  have hSo : IsOpen ((Set.univ : Set ℝ) ×ˢ S) := isOpen_univ.prod hS
  have hcU : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ S) := hU.continuousOn
  have hsl : ∀ y ∈ S, Continuous (fun t => U t y) := fun y hy =>
    hcU.comp_continuous (f := fun t : ℝ => (t, y)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hy⟩)
  have hDc : ContinuousOn (fun p : ℝ × E => fderiv ℝ (U p.1) p.2) (Set.univ ×ˢ S) := by
    have h0 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry U)) (Set.univ ×ˢ S) :=
      ContDiffOn.fderiv_of_isOpen hU hSo (by simp)
    have h1 : ContinuousOn (fun p : ℝ × E =>
        (fderiv ℝ (Function.uncurry U) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) (Set.univ ×ˢ S) :=
      h0.continuousOn.clm_comp continuousOn_const
    refine h1.congr ?_
    rintro ⟨t, y⟩ ⟨-, hy⟩
    exact (fderiv_slice hS hU hy).fderiv
  obtain ⟨T, hT⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hK : IsCompact (Metric.closedBall (0 : ℝ) T ×ˢ Metric.closedBall x r) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hDc.mono (Set.prod_mono (Set.subset_univ _) hball))
  have hdiff : ∀ (t : ℝ) (y : E), y ∈ S → HasFDerivAt (U t) (fderiv ℝ (U t) y) y := fun t y hy =>
    (fderiv_slice hS hU hy).differentiableAt.hasFDerivAt
  have hcD : Continuous (fun t => fderiv ℝ (U t) x) :=
    hDc.comp_continuous (f := fun t : ℝ => (t, x)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hx⟩)
  have hIntD := int_real hg hgc hcD
  have key : HasFDerivAt (fun x' => ∫ t, g t • U t x') (∫ t, g t • fderiv ℝ (U t) x) x := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.closedBall x r)
      (F := fun x' t => g t • U t x') (F' := fun x' t => g t • fderiv ℝ (U t) x')
      (bound := fun t => |g t| * C) (Metric.closedBall_mem_nhds x hr) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hS.mem_nhds hx] with y hy
      exact (int_real hg hgc (hsl y hy)).aestronglyMeasurable
    · exact int_real hg hgc (hsl x hx)
    · exact hIntD.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t y hy => ?_
      by_cases ht : t ∈ tsupport g
      · have := hC (t, y) ⟨hT ht, hy⟩
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      · have hz : g t = 0 := image_eq_zero_of_notMem_tsupport ht
        simp [hz]
    · have : Continuous (fun t => |g t| * C) := (continuous_abs.comp hg).mul continuous_const
      refine Continuous.integrable_of_hasCompactSupport this ?_
      exact (hgc.comp_left (g := fun a : ℝ => |a|) (by simp)).mul_right
    · refine Filter.Eventually.of_forall fun t y hy => ?_
      exact (hdiff t y (hball hy)).const_smul (g t)
  rw [key.fderiv, ContinuousLinearMap.integral_apply hIntD]
  rfl

end Gen

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem contDiff_mulRight (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) := by
  have : (fun y : Mat n => y * X) = ((LinearMap.mulRight ℝ X : Mat n →ₗ[ℝ] Mat n).toContinuousLinearMap : Mat n → Mat n) := by
    funext y; simp
  rw [this]
  exact ContinuousLinearMap.contDiff _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sm_Rd (X : Mat n) {U : ℝ → Mat n → V} (hU : Sm U) : Sm (fun t => Rd X (U t)) :=
  gen_sm (isOpen_invertible_matrices n) hU (contDiff_mulRight X)

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem cont_slice {U : ℝ → Mat n → V} (hU : Sm U) {x : Mat n} (hx : x ∈ GLs n) :
    Continuous (fun t => U t x) := by
  have h : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ GLs n) := hU.continuousOn
  exact h.comp_continuous (f := fun t : ℝ => (t, x)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hx⟩)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem bump_support {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) |T|) ?_
  intro t ht
  refine hg.2.2 t (lt_of_le_of_lt (le_abs_self T) ?_)
  simpa [Metric.mem_closedBall, Real.dist_eq] using ht

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem int_sm {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : Sm U) (hg : IsBump g T) {x : Mat n} (hx : x ∈ GLs n) :
    Integrable (fun t => (g t : ℂ) • U t x) := by
  simpa only [Complex.coe_smul] using int_real hg.1.continuous (bump_support hg) (cont_slice hU hx)

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem rd_avg [CompleteSpace V] (X : Mat n) {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : Sm U) (hg : IsBump g T)
    {x : Mat n} (hx : x ∈ GLs n) :
    Rd X (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • Rd X (U t) x := by
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ _
  simp only [Complex.coe_smul]
  exact gen_avg (isOpen_invertible_matrices n) hU hg.1.continuous (bump_support hg) hx (x * X)

def Good (L : (Mat n → V) → (Mat n → V)) : Prop :=
  (∀ U : ℝ → Mat n → V, Sm U → Sm (fun t => L (U t))) ∧
  (∀ F F' : Mat n → V, (∀ y ∈ GLs n, F y = F' y) → ∀ x ∈ GLs n, L F x = L F' x) ∧
  ∀ (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ), Sm U → IsBump g T → ∀ x ∈ GLs n,
    L (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • L (U t) x

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem good_id : Good (n := n) (V := V) (fun f => f) :=
  ⟨fun _ h => h, fun _ _ h => h, fun _ _ _ _ _ _ _ => rfl⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem good_zero : Good (n := n) (V := V) (fun _ => 0) := by
  refine ⟨fun U _ => ?_, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp⟩
  exact (contDiffOn_const (c := (0 : V))).congr (fun _ _ => rfl)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem good_comp {L₁ L₂ : (Mat n → V) → (Mat n → V)} (h₁ : Good L₁) (h₂ : Good L₂) :
    Good (fun f => L₁ (L₂ f)) := by
  refine ⟨fun U hU => h₁.1 _ (h₂.1 U hU), fun F F' h => h₁.2.1 _ _ (h₂.2.1 F F' h), ?_⟩
  intro U g T hU hg x hx
  show L₁ (L₂ _) x = ∫ t, (g t : ℂ) • L₁ (L₂ (U t)) x
  rw [h₁.2.1 _ (fun x' => ∫ t, (g t : ℂ) • L₂ (U t) x') (h₂.2.2 U g T hU hg) x hx]
  exact h₁.2.2 _ g T (h₂.1 U hU) hg x hx

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem good_add {L₁ L₂ : (Mat n → V) → (Mat n → V)} (h₁ : Good L₁) (h₂ : Good L₂) :
    Good (fun f => L₁ f + L₂ f) := by
  refine ⟨fun U hU => ?_, fun F F' h x hx => ?_, ?_⟩
  · exact ((h₁.1 U hU).add (h₂.1 U hU)).congr (fun _ _ => rfl)
  · simp only [Pi.add_apply, h₁.2.1 F F' h x hx, h₂.2.1 F F' h x hx]
  · intro U g T hU hg x hx
    simp only [Pi.add_apply, smul_add]
    rw [integral_add (int_sm (h₁.1 U hU) hg hx) (int_sm (h₂.1 U hU) hg hx),
      h₁.2.2 U g T hU hg x hx, h₂.2.2 U g T hU hg x hx]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem good_smul (c : ℂ) {L : (Mat n → V) → (Mat n → V)} (h : Good L) : Good (fun f => c • L f) := by
  refine ⟨fun U hU => ?_, fun F F' e x hx => ?_, ?_⟩
  · exact ((h.1 U hU).const_smul c).congr (fun _ _ => rfl)
  · simp only [Pi.smul_apply, h.2.1 F F' e x hx]
  · intro U g T hU hg x hx
    simp only [Pi.smul_apply]
    rw [h.2.2 U g T hU hg x hx, ← integral_smul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => smul_comm _ _ _)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem good_sum {ι : Type} (s : Finset ι) {L : ι → (Mat n → V) → (Mat n → V)} (h : ∀ i, Good (L i)) :
    Good (fun f => ∑ i ∈ s, L i f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact good_add (h a) ih

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem good_Rd [CompleteSpace V] (X : Mat n) : Good (n := n) (V := V) (Rd X) := by
  refine ⟨fun U hU => sm_Rd X hU, fun F F' h x hx => ?_, fun U g T hU hg x hx => rd_avg X hU hg hx⟩
  have he : F =ᶠ[𝓝 x] F' := Filter.eventuallyEq_of_mem ((isOpen_invertible_matrices n).mem_nhds hx) h
  show fderiv ℝ F x (x * X) = fderiv ℝ F' x (x * X)
  rw [he.fderiv_eq]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem good_Eu [CompleteSpace V] (s : Bool) (a b : Fin n) : Good (n := n) (V := V) (Eu s a b) :=
  good_smul _ (good_add (good_Rd _) (good_smul _ (good_Rd _)))

/- English proof (translation)
Proceed by induction. Treat this case separately. Consider separately whether the proposition holds or fails. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.

Treat this case separately. A detailed English derivation is pending.
-/
theorem good_Epow [CompleteSpace V] (s : Bool) (m : ℕ) (a b : Fin n) : Good (n := n) (V := V) (Epow s m a b) := by
  induction m generalizing a b with
  | zero =>
    by_cases h : a = b
    · simpa [Epow, h] using good_id
    · simpa [Epow, h] using good_zero
  | succ m ih =>
    exact good_sum Finset.univ fun c => good_comp (good_Eu s a c) (ih c b)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem good_gel [CompleteSpace V] (s : Bool) (m : ℕ) : Good (n := n) (V := V) (gel s m) :=
  good_sum Finset.univ fun a => good_Epow s m a a

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem good_zOp [CompleteSpace V] (w : List (Bool × ℕ)) : Good (n := n) (V := V) (zOp w) := by
  induction w with
  | nil => exact good_id
  | cons p w ih =>
    show Good (fun f => gel p.1 p.2 (zOp w f))
    exact good_comp (good_gel p.1 p.2) ih

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem zOp_avg : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (U : ℝ → Mat n → V)
    (g : ℝ → ℝ) (T : ℝ) (w : List (Bool × ℕ)), ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) → IsBump g T →
    ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • zOp w (U t) x :=
  fun _ _ _ _ _ U g T w hU hg x hx => (good_zOp w).2.2 U g T hU hg x hx

end GlobalTheory.CompanionTheory.WaveMult.ZOpAvg

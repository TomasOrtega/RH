import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.IteratedDerivOrbit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.InKRealSmul

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def brIdxSum (v : Fin n → ℝ) : ℝ := ∑ i : Fin n, ((i : ℕ) : ℝ) * v i

/- English proof (translation)
Unfold `brIdxSum`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem brIdxSum_sub (u v : Fin n → ℝ) : brIdxSum (u - v) = brIdxSum u - brIdxSum v := by
  unfold brIdxSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.sub_apply]
  ring

/- English proof (translation)
Unfold `brIdxSum`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem brIdxSum_add (u v : Fin n → ℝ) : brIdxSum (u + v) = brIdxSum u + brIdxSum v := by
  unfold brIdxSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply]
  ring

/- English proof (translation)
Simplify using `[brIdxSum, Formalism.REAL.root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem brIdxSum_root (a b : Fin n) : brIdxSum (Formalism.REAL.root a b) = (a : ℕ) - (b : ℕ) := by
  simp [brIdxSum, Formalism.REAL.root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Establish `hsmul : ∀ (r : ℝ) (v : Fin n → ℝ), brIdxSum (r • v) = r * brIdxSum v`. Introduce `r v`. Unfold `brIdxSum`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Fin n → ℝ), brIdxSum (∑ x ∈ s, f x) = ∑ x ∈ s, brIdxSum (f x)`. Introduce `ι s f`. Unfold `brIdxSum`.

Simplify using `only [Finset.sum_apply, Finset.mul_sum]`. Conclude with `Finset.sum_comm`. Rewrite using `[hsum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hsum]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hsmul, brIdxSum_root]`.
-/
theorem brIdxSum_cdom_sum (ε : Fin n → Bool) (c : Fin n → Fin n → ℕ)
    (_hc : ∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) :
    brIdxSum (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) = ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) := by
  have hsmul : ∀ (r : ℝ) (v : Fin n → ℝ), brIdxSum (r • v) = r * brIdxSum v := by
    intro r v
    unfold brIdxSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Fin n → ℝ),
      brIdxSum (∑ x ∈ s, f x) = ∑ x ∈ s, brIdxSum (f x) := by
    intro ι s f
    unfold brIdxSum
    simp only [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hsum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hsmul, brIdxSum_root]

/- English proof (translation)
Distinguish the cases in `h0 : c a b = 0`. Simplify using `[h0]`. Establish `h1 : (a : ℕ) < (b : ℕ)` using `(hc a b h0).1`. Establish `h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast h1`. Apply `mul_nonpos_of_nonneg_of_nonpos (by positivity)` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem br_cdom_term_nonpos (ε : Fin n → Bool) (c : Fin n → Fin n → ℕ)
    (hc : ∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) (a b : Fin n) :
    (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) ≤ 0 := by
  by_cases h0 : c a b = 0
  · simp [h0]
  · have h1 : (a : ℕ) < (b : ℕ) := (hc a b h0).1
    have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h1
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    linarith

/- English proof (translation)
Unfold `Formalism.MainNotions.S.CDom at h`. Take `⟨c, hc, hΛ⟩` from `h`. Rewrite using `[hΛ, brIdxSum_cdom_sum ε c hc]`. Conclude with `Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => br_cdom_term_nonpos ε c hc a b`.
-/
theorem brIdxSum_nonpos_of_cdom {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h : Formalism.MainNotions.S.CDom ε μ Λ) :
    brIdxSum (Λ - μ) ≤ 0 := by
  unfold Formalism.MainNotions.S.CDom at h
  obtain ⟨c, hc, hΛ⟩ := h
  rw [hΛ, brIdxSum_cdom_sum ε c hc]
  exact Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => br_cdom_term_nonpos ε c hc a b

/- English proof (translation)
Introduce `h`. Establish `h1` using `brIdxSum_nonpos_of_cdom h`. Establish `hr : root a b = Formalism.REAL.root a b` using `rfl`. Rewrite `h1` using `[brIdxSum_sub, brIdxSum_add, hr, brIdxSum_root]`. Establish `h2 : (a : ℕ) < (b : ℕ)` using `hab`.

Establish `h3 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_cdom_add_root (ε : Fin n → Bool) (Λ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ Formalism.MainNotions.S.CDom ε (Λ + root a b) Λ := by
  intro h
  have h1 := brIdxSum_nonpos_of_cdom h
  have hr : root a b = Formalism.REAL.root a b := rfl
  rw [brIdxSum_sub, brIdxSum_add, hr, brIdxSum_root] at h1
  have h2 : (a : ℕ) < (b : ℕ) := hab
  have h3 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h2
  linarith

/- English proof (translation)
Establish `hA` using `brIdxSum_nonpos_of_cdom h₂`. Unfold `Formalism.MainNotions.S.CDom at h₁`. Take `⟨c, hc, hΛ⟩` from `h₁`. Establish `hB : brIdxSum (Λ - μ) = ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ)`. Rewrite using `[hΛ, brIdxSum_cdom_sum ε c hc]`.

Establish `hneg : brIdxSum (μ - Λ) = - brIdxSum (Λ - μ)`. Rewrite using `[brIdxSum_sub, brIdxSum_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum0 : ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) = 0`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => br_cdom_term_nonpos ε c hc a b`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hterm : ∀ a b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) = 0`. Introduce `a b`. Establish `h0` using `(Finset.sum_eq_zero_iff_of_nonpos (fun a _ => Finset.sum_nonpos fun b _ => br_cdom_term_nonpos ε c hc a b)).1 hsum0 a (Finset.mem_univ _)`.

Conclude with `(Finset.sum_eq_zero_iff_of_nonpos (fun b _ => br_cdom_term_nonpos ε c hc a b)).1 h0 b (Finset.mem_univ _)`. Establish `hc0 : ∀ a b, c a b = 0`. Introduce `a b`. Assume the negation of the conclusion as `hne`. Establish `h1 : (a : ℕ) < (b : ℕ)` using `(hc a b hne).1`.

Establish `hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast h1`. Establish `hpos : (0 : ℝ) < c a b` using `by exact_mod_cast Nat.pos_of_ne_zero hne`. Establish `h3` using `hterm a b`. Establish `h4 : (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) < 0` using `mul_neg_of_pos_of_neg hpos (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h5 : Λ - μ = 0`. Rewrite using `[hΛ]`. Simplify using `[hc0]`. Conclude with `(sub_eq_zero.mp h5).symm`.
-/
theorem cdom_antisymm (ε : Fin n → Bool) {μ Λ : Fin n → ℝ} (h₁ : Formalism.MainNotions.S.CDom ε μ Λ)
    (h₂ : Formalism.MainNotions.S.CDom ε Λ μ) : μ = Λ := by
  have hA := brIdxSum_nonpos_of_cdom h₂
  unfold Formalism.MainNotions.S.CDom at h₁
  obtain ⟨c, hc, hΛ⟩ := h₁
  have hB : brIdxSum (Λ - μ) = ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) := by
    rw [hΛ, brIdxSum_cdom_sum ε c hc]
  have hneg : brIdxSum (μ - Λ) = - brIdxSum (Λ - μ) := by
    rw [brIdxSum_sub, brIdxSum_sub]
    ring
  have hsum0 : ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) = 0 := by
    apply le_antisymm
    · exact Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => br_cdom_term_nonpos ε c hc a b
    · linarith
  have hterm : ∀ a b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) = 0 := by
    intro a b
    have h0 := (Finset.sum_eq_zero_iff_of_nonpos (fun a _ => Finset.sum_nonpos fun b _ =>
      br_cdom_term_nonpos ε c hc a b)).1 hsum0 a (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => br_cdom_term_nonpos ε c hc a b)).1 h0 b
      (Finset.mem_univ _)
  have hc0 : ∀ a b, c a b = 0 := by
    intro a b
    by_contra hne
    have h1 : (a : ℕ) < (b : ℕ) := (hc a b hne).1
    have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h1
    have hpos : (0 : ℝ) < c a b := by exact_mod_cast Nat.pos_of_ne_zero hne
    have h3 := hterm a b
    have h4 : (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) < 0 :=
      mul_neg_of_pos_of_neg hpos (by linarith)
    linarith
  have h5 : Λ - μ = 0 := by
    rw [hΛ]
    simp [hc0]
  exact (sub_eq_zero.mp h5).symm

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

/- English proof (translation)
Establish `hG : Xᴴ * Jm ε + Jm ε * X = 0` using `hX.1`. Establish `hXJ : X * Jm ε = Jm ε * X` using `hX.2`. Establish `hJJ : Jm ε * Jm ε = 1`. Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hXH : Xᴴ = -X`. Establish `h1 : Xᴴ * Jm ε = -(X * Jm ε)`.

Rewrite using `[hXJ]`. Conclude with `eq_neg_of_add_eq_zero_left hG`. Combine the equalities or inequalities in the displayed calculation. Establish `hexpK : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε`. Introduce `t`.

Establish `hYH : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X)`. Rewrite using `[Matrix.conjTranspose_smul, hXH, smul_neg]`. Use `congr 2`. Simplify using `[Complex.conj_ofReal]`. Establish `hcomm : Commute ((t : ℂ) • X) (-((t : ℂ) • X))` using `(Commute.refl _).neg_right`.

Establish `hYJ : Commute ((t : ℂ) • X) (Jm ε)` using `by show (t : ℂ) • X * Jm ε = Jm ε * ((t : ℂ) • X)`. Rewrite using `[smul_mul_assoc, mul_smul_comm, hXJ]`. Simplify using `only [Kset, Set.mem_setOf_eq]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hYH, ← Matrix.exp_add_of_commute _ _ hcomm, add_neg_cancel, NormedSpace.exp_zero]`.

Establish `hU : IsUnit (Jm ε)` using `⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩`. Establish `hJi : (Jm ε)⁻¹ = Jm ε` using `Matrix.inv_eq_left_inv hJJ`. Establish `hc` using `Matrix.exp_conj (Jm ε) ((t : ℂ) • X) hU`. Establish `hc' : NormedSpace.exp (Jm ε * ((t : ℂ) • X) * (Jm ε)⁻¹) = NormedSpace.exp ((t : ℂ) • X)`. Rewrite using `[hJi, ← hYJ.eq, mul_assoc, hJJ, mul_one]`.

Rewrite `hc` using `[hc', hJi]`. Combine the equalities or inequalities in the displayed calculation. Use `haveI := hS`. Establish `hWc : IsClosed ((LinearMap.range (D.subtype.comp S.subtype) : Submodule ℂ H) : Set H)` using `Submodule.closed_of_finiteDimensional _`. Establish `hmem : ∀ t : ℝ, σ (NormedSpace.exp ((t : ℂ) • X)) (v : H) ∈ LinearMap.range (D.subtype.comp S.subtype)`.

Introduce `t`. Take `⟨w, hw, hwv⟩` from `hK _ (hexpK t) v hv`. Conclude with `LinearMap.mem_range.mpr ⟨⟨w, hw⟩, hwv⟩`. Establish `hd` using `hD.deriv X hX.1 v`. Establish `hlim : ((actM E X v : D) : H) ∈ LinearMap.range (D.subtype.comp S.subtype)` using `hWc.mem_of_tendsto hd.tendsto_slope_zero (Filter.Eventually.of_forall fun t => Submodule.smul_of_tower_mem _ t⁻¹ (Submodule.sub_mem _ (hmem _) (hmem _)))`.

Take `⟨y, hy⟩` from `LinearMap.mem_range.mp hlim`. Establish `hy' : (y : D) = actM E X v` using `Subtype.ext (by simpa using hy)`. Rewrite using `[← hy']`. Conclude with `y.2`.
-/
theorem br_actM_mem_of_kStable (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (S : Submodule ℂ D)
    (hS : FiniteDimensional ℂ S) (hK : ∀ k ∈ Kset ε, ∀ v ∈ S, ∃ w ∈ S, (w : H) = σ k v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {v : D} (hv : v ∈ S) : actM E X v ∈ S := by
  classical
  have hG : Xᴴ * Jm ε + Jm ε * X = 0 := hX.1
  have hXJ : X * Jm ε = Jm ε * X := hX.2
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hXH : Xᴴ = -X := by
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
      rw [hXJ]
      exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = -X := by rw [h1, neg_mul, mul_assoc, hJJ, mul_one]
  have hexpK : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
    intro t
    have hYH : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
      rw [Matrix.conjTranspose_smul, hXH, smul_neg]
      congr 2
      simp [Complex.conj_ofReal]
    have hcomm : Commute ((t : ℂ) • X) (-((t : ℂ) • X)) := (Commute.refl _).neg_right
    have hYJ : Commute ((t : ℂ) • X) (Jm ε) := by
      show (t : ℂ) • X * Jm ε = Jm ε * ((t : ℂ) • X)
      rw [smul_mul_assoc, mul_smul_comm, hXJ]
    simp only [Kset, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hYH,
        ← Matrix.exp_add_of_commute _ _ hcomm, add_neg_cancel, NormedSpace.exp_zero]
    · have hU : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
      have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
      have hc := Matrix.exp_conj (Jm ε) ((t : ℂ) • X) hU
      have hc' : NormedSpace.exp (Jm ε * ((t : ℂ) • X) * (Jm ε)⁻¹) = NormedSpace.exp ((t : ℂ) • X) := by
        rw [hJi, ← hYJ.eq, mul_assoc, hJJ, mul_one]
      rw [hc', hJi] at hc
      calc NormedSpace.exp ((t : ℂ) • X) * Jm ε
          = Jm ε * NormedSpace.exp ((t : ℂ) • X) * Jm ε * Jm ε := by rw [← hc]
        _ = Jm ε * NormedSpace.exp ((t : ℂ) • X) := by rw [mul_assoc, hJJ, mul_one]
  haveI := hS
  have hWc : IsClosed ((LinearMap.range (D.subtype.comp S.subtype) : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : ∀ t : ℝ, σ (NormedSpace.exp ((t : ℂ) • X)) (v : H) ∈
      LinearMap.range (D.subtype.comp S.subtype) := by
    intro t
    obtain ⟨w, hw, hwv⟩ := hK _ (hexpK t) v hv
    exact LinearMap.mem_range.mpr ⟨⟨w, hw⟩, hwv⟩
  have hd := hD.deriv X hX.1 v
  have hlim : ((actM E X v : D) : H) ∈ LinearMap.range (D.subtype.comp S.subtype) :=
    hWc.mem_of_tendsto hd.tendsto_slope_zero (Filter.Eventually.of_forall fun t =>
      Submodule.smul_of_tower_mem _ t⁻¹ (Submodule.sub_mem _ (hmem _) (hmem _)))
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hlim
  have hy' : (y : D) = actM E X v := Subtype.ext (by simpa using hy)
  rw [← hy']
  exact y.2

/- English proof (translation)
Introduce `a b hab v hv`. Establish `hact : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (w : D), actM E X w = ∑ i, ∑ j, X i j • E i j w`. Introduce `X w`. Simplify using `only [actM, LinearMap.sum_apply, LinearMap.smul_apply]`. Establish `key : ∀ (c : ℂ) (p q : Fin n), (∑ i, ∑ j, (if i = p ∧ j = q then c else 0) • E i j v) = c • E p q v`.

Introduce `c p q`. Rewrite using `[Finset.sum_eq_single p, Finset.sum_eq_single q]`. Apply the tactic sequence `all_goals first`. Consider the case `(intro x _ hx; simp [hx])`. Consider the case `simp`.

Establish `hinK : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → X * Jm ε = Jm ε * X → inK ε X`. Introduce `X h1 h2`. Use `⟨?_, h2⟩` and prove the remaining obligations. Use `show Xᴴ * Jm ε + Jm ε * X = 0`. Rewrite using `[h1, neg_mul, h2, neg_add_cancel]`.

Establish `hcommJ : ∀ z : ℂ, (Matrix.of fun i j => (if i = a ∧ j = b then z else 0) + (if i = b ∧ j = a then z else 0) : Matrix (Fin n) (Fin n) ℂ) * Jm ε = Jm ε * (Matrix.of fun i j => (if i = a ∧ j = b then z else 0) + (if i = b ∧ j = a then z else 0))`. Introduce `z`. Use extensionality with `i j`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]`. Distinguish the cases in `h1 : i = a ∧ j = b`.

Take `⟨rfl, rfl⟩` from `h1`. Rewrite using `[hab]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `h2 : i = b ∧ j = a`. Take `⟨rfl, rfl⟩` from `h2`.

Rewrite using `[hab]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h1, if_neg h2]`. Expand and normalize the polynomial expressions, which then agree. Use `set X₁ : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => (if i = a ∧ j = b then (1 : ℂ) else 0) + (if i = b ∧ j = a then (-1 : ℂ) else 0) with hX₁`.

Use `set X₂ : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => (if i = a ∧ j = b then Complex.I else 0) + (if i = b ∧ j = a then Complex.I else 0) with hX₂`. Establish `hJ₁ : X₁ * Jm ε = Jm ε * X₁`. Use extensionality with `i j`. Simplify using `only [hX₁, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]`. Distinguish the cases in `h1 : i = a ∧ j = b`.

Take `⟨rfl, rfl⟩` from `h1`. Rewrite using `[hab]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `h2 : i = b ∧ j = a`. Take `⟨rfl, rfl⟩` from `h2`.

Rewrite using `[hab]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h1, if_neg h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hJ₂ : X₂ * Jm ε = Jm ε * X₂` using `hcommJ Complex.I`.

Establish `hH₁ : X₁ᴴ = -X₁`. Use extensionality with `i j`. Simplify using `only [hX₁, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.neg_apply]`. Establish `e1 : (j = a ∧ i = b) ↔ (i = b ∧ j = a)` using `and_comm`. Establish `e2 : (j = b ∧ i = a) ↔ (i = a ∧ j = b)` using `and_comm`.

Simplify using `only [e1, e2]`. Apply the tactic sequence `split_ifs <;> simp [Complex.star_def, Complex.conj_I]`. Establish `hH₂ : X₂ᴴ = -X₂`. Use extensionality with `i j`. Simplify using `only [hX₂, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.neg_apply]`.

Establish `e1 : (j = a ∧ i = b) ↔ (i = b ∧ j = a)` using `and_comm`. Establish `e2 : (j = b ∧ i = a) ↔ (i = a ∧ j = b)` using `and_comm`. Simplify using `only [e1, e2]`. Apply the tactic sequence `split_ifs <;> simp [Complex.star_def, Complex.conj_I]`. Establish `m₁` using `br_actM_mem_of_kStable hσ hD S hS hK (hinK X₁ hH₁ hJ₁) hv`.

Establish `m₂` using `br_actM_mem_of_kStable hσ hD S hS hK (hinK X₂ hH₂ hJ₂) hv`. Establish `e₁ : actM E X₁ v = E a b v + (-1 : ℂ) • E b a v`. Rewrite using `[hact, hX₁]`. Simplify using `only [Matrix.of_apply, add_smul, Finset.sum_add_distrib]`. Rewrite using `[key, key, one_smul]`.

Establish `e₂ : actM E X₂ v = Complex.I • E a b v + Complex.I • E b a v`. Rewrite using `[hact, hX₂]`. Simplify using `only [Matrix.of_apply, add_smul, Finset.sum_add_distrib]`. Rewrite using `[key, key]`. Establish `e₃ : E a b v = (1 / 2 : ℂ) • (actM E X₁ v - Complex.I • actM E X₂ v)`.

Rewrite using `[e₁, e₂, smul_add, smul_smul, smul_smul, Complex.I_mul_I]`. Use `module`. Rewrite using `[e₃]`. Conclude with `S.smul_mem _ (S.sub_mem m₁ (S.smul_mem _ m₂))`.
-/
theorem isKStableSub_of_kStable (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (S : Submodule ℂ D)
    (hS : FiniteDimensional ℂ S) (hK : ∀ k ∈ Kset ε, ∀ v ∈ S, ∃ w ∈ S, (w : H) = σ k v) :
    IsKStableSub ε E S := by
  classical
  intro a b hab v hv
  have hact : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (w : D), actM E X w = ∑ i, ∑ j, X i j • E i j w := by
    intro X w
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  have key : ∀ (c : ℂ) (p q : Fin n),
      (∑ i, ∑ j, (if i = p ∧ j = q then c else 0) • E i j v) = c • E p q v := by
    intro c p q
    rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
    all_goals first
      | (intro x _ hx; simp [hx])
      | simp
  have hinK : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → X * Jm ε = Jm ε * X → inK ε X := by
    intro X h1 h2
    refine ⟨?_, h2⟩
    show Xᴴ * Jm ε + Jm ε * X = 0
    rw [h1, neg_mul, h2, neg_add_cancel]
  have hcommJ : ∀ z : ℂ, (Matrix.of fun i j => (if i = a ∧ j = b then z else 0) +
      (if i = b ∧ j = a then z else 0) : Matrix (Fin n) (Fin n) ℂ) * Jm ε =
      Jm ε * (Matrix.of fun i j => (if i = a ∧ j = b then z else 0) +
      (if i = b ∧ j = a then z else 0)) := by
    intro z
    ext i j
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    by_cases h1 : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h1
      rw [hab]
      ring
    · by_cases h2 : i = b ∧ j = a
      · obtain ⟨rfl, rfl⟩ := h2
        rw [hab]
        ring
      · rw [if_neg h1, if_neg h2]
        ring
  set X₁ : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => (if i = a ∧ j = b then (1 : ℂ) else 0) +
      (if i = b ∧ j = a then (-1 : ℂ) else 0) with hX₁
  set X₂ : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => (if i = a ∧ j = b then Complex.I else 0) +
      (if i = b ∧ j = a then Complex.I else 0) with hX₂
  have hJ₁ : X₁ * Jm ε = Jm ε * X₁ := by
    ext i j
    simp only [hX₁, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    by_cases h1 : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h1
      rw [hab]
      ring
    · by_cases h2 : i = b ∧ j = a
      · obtain ⟨rfl, rfl⟩ := h2
        rw [hab]
        ring
      · rw [if_neg h1, if_neg h2]
        ring
  have hJ₂ : X₂ * Jm ε = Jm ε * X₂ := hcommJ Complex.I
  have hH₁ : X₁ᴴ = -X₁ := by
    ext i j
    simp only [hX₁, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.neg_apply]
    have e1 : (j = a ∧ i = b) ↔ (i = b ∧ j = a) := and_comm
    have e2 : (j = b ∧ i = a) ↔ (i = a ∧ j = b) := and_comm
    simp only [e1, e2]
    split_ifs <;> simp [Complex.star_def, Complex.conj_I]
  have hH₂ : X₂ᴴ = -X₂ := by
    ext i j
    simp only [hX₂, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.neg_apply]
    have e1 : (j = a ∧ i = b) ↔ (i = b ∧ j = a) := and_comm
    have e2 : (j = b ∧ i = a) ↔ (i = a ∧ j = b) := and_comm
    simp only [e1, e2]
    split_ifs <;> simp [Complex.star_def, Complex.conj_I]
  have m₁ := br_actM_mem_of_kStable hσ hD S hS hK (hinK X₁ hH₁ hJ₁) hv
  have m₂ := br_actM_mem_of_kStable hσ hD S hS hK (hinK X₂ hH₂ hJ₂) hv
  have e₁ : actM E X₁ v = E a b v + (-1 : ℂ) • E b a v := by
    rw [hact, hX₁]
    simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib]
    rw [key, key, one_smul]
  have e₂ : actM E X₂ v = Complex.I • E a b v + Complex.I • E b a v := by
    rw [hact, hX₂]
    simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib]
    rw [key, key]
  have e₃ : E a b v = (1 / 2 : ℂ) • (actM E X₁ v - Complex.I • actM E X₂ v) := by
    rw [e₁, e₂, smul_add, smul_smul, smul_smul, Complex.I_mul_I]
    module
  rw [e₃]
  exact S.smul_mem _ (S.sub_mem m₁ (S.smul_mem _ m₂))

end Rep

end ReciprocityTheory.ChartRestriction.DS

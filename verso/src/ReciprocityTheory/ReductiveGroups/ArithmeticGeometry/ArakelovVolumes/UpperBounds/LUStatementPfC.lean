import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}

/- English proof (translation)
Simplify using `only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]`. Establish `hp : ∀ σ : Equiv.Perm (Fin k), DifferentiableOn ℂ (fun x => ∏ i, m x (σ i) i) s`. Introduce `σ`. Proceed by induction on `(Finset.univ : Finset (Fin k)) using Finset.induction_on with`. Consider the case `empty => simp [differentiableOn_const]`.

Consider the case `insert a t ha ih`. Simplify using `only [Finset.prod_insert ha]`. Conclude with `(hm (σ a) a).mul ih`. Use `fun_prop`.
-/
theorem diffOn_det {k : ℕ} {s : Set (Frame X.Ψ r)} (m : Frame X.Ψ r → Matrix (Fin k) (Fin k) ℂ)
    (hm : ∀ i j, DifferentiableOn ℂ (fun x => m x i j) s) : DifferentiableOn ℂ (fun x => (m x).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  have hp : ∀ σ : Equiv.Perm (Fin k), DifferentiableOn ℂ (fun x => ∏ i, m x (σ i) i) s := by
    intro σ
    induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
    | empty => simp [differentiableOn_const]
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hm (σ a) a).mul ih
  fun_prop

/- English proof (translation)
Introduce `i j`. Establish `hadj : DifferentiableOn ℂ (fun x => (m x).adjugate i j) s`. Simplify using `only [Matrix.adjugate_apply]`. Use `diffOn_det (fun x => (m x).updateRow j (Pi.single i 1)) ?_` and prove the remaining obligations. Introduce `a b`.

Distinguish the cases in `h : a = j`. Simplify using `[Matrix.updateRow_apply, h, differentiableOn_const]`. Simplify `hm a b` using `[Matrix.updateRow_apply, h]`. Establish `hinv : DifferentiableOn ℂ (fun x => ((m x).det)⁻¹) s` using `(diffOn_det m hm).inv hd`. Use `(hinv.mul hadj).congr ?_` and prove the remaining obligations.

Introduce `x _`. Simplify using `[Matrix.inv_def, Ring.inverse_eq_inv']`.
-/
theorem diffOn_inv {k : ℕ} {s : Set (Frame X.Ψ r)} (m : Frame X.Ψ r → Matrix (Fin k) (Fin k) ℂ)
    (hm : ∀ i j, DifferentiableOn ℂ (fun x => m x i j) s) (hd : ∀ x ∈ s, (m x).det ≠ 0) :
    ∀ i j, DifferentiableOn ℂ (fun x => (m x)⁻¹ i j) s := by
  intro i j
  have hadj : DifferentiableOn ℂ (fun x => (m x).adjugate i j) s := by
    simp only [Matrix.adjugate_apply]
    refine diffOn_det (fun x => (m x).updateRow j (Pi.single i 1)) ?_
    intro a b
    by_cases h : a = j
    · simp [Matrix.updateRow_apply, h, differentiableOn_const]
    · simpa [Matrix.updateRow_apply, h] using hm a b
  have hinv : DifferentiableOn ℂ (fun x => ((m x).det)⁻¹) s := (diffOn_det m hm).inv hd
  refine (hinv.mul hadj).congr ?_
  intro x _
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

/- English proof (translation)
Simplify using `only [Mx, Matrix.mul_apply, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]`. Use `first`. Consider the case `fun_prop`. Consider the case `exact Differentiable.sum fun b _ => (differentiable_const _).mul ((differentiable_apply c).comp ((differentiable_apply b).comp (differentiable_apply τ)))`.
-/
theorem Mx_diff (τ : X.Ψ) (a c : Fin r) : Differentiable ℂ (fun x => Mx X x0 x τ a c) := by
  simp only [Mx, Matrix.mul_apply, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]
  first
    | fun_prop
    | exact Differentiable.sum fun b _ => (differentiable_const _).mul
        ((differentiable_apply c).comp ((differentiable_apply b).comp (differentiable_apply τ)))

/- English proof (translation)
Establish `hdet : ∀ τ (k : Fin (r + 1)), Differentiable ℂ (fun x => lminor (Mx X x0 x τ) k)`. Introduce `τ k`. Rewrite using `[← differentiableOn_univ]`. Conclude with `diffOn_det (s := Set.univ) (fun x => (Mx X x0 x τ).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))) (fun i j => (Mx_diff τ _ _).differentiableOn)`. Use `show Differentiable ℂ (fun x => ∏ τ, ∏ k : Fin (r + 1), lminor (Mx X x0 x τ) k)`.

Use `fun_prop`.
-/
theorem Delta_diff : Differentiable ℂ (DeltaF X x0) := by
  have hdet : ∀ τ (k : Fin (r + 1)), Differentiable ℂ (fun x => lminor (Mx X x0 x τ) k) := by
    intro τ k
    rw [← differentiableOn_univ]
    exact diffOn_det (s := Set.univ)
      (fun x => (Mx X x0 x τ).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
        (Fin.castLE (Nat.le_of_lt_succ k.isLt)))
      (fun i j => (Mx_diff τ _ _).differentiableOn)
  show Differentiable ℂ (fun x => ∏ τ, ∏ k : Fin (r + 1), lminor (Mx X x0 x τ) k)
  fun_prop

def cellL (X : Data E r) (x0 : Frame X.Ψ r) : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ DeltaF X x0 x ≠ 0}

/- English proof (translation)
Establish `hl : ∀ x ∈ cellL X x0, ∀ k : Fin (r + 1), lminor (Mx X x0 x τ) k ≠ 0`. Introduce `x hx k`. Establish `h1 : DeltaF X x0 x ≠ 0` using `hx.2`. Unfold `DeltaF at h1`. Conclude with `Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp h1 τ (Finset.mem_univ _)) k (Finset.mem_univ _)`.

Distinguish the cases in `h1 : (k : ℕ) < i`. Simplify using `only [Lm, Matrix.of_apply, h1, ↓reduceDIte]`. Establish `hinv : ∀ a b, DifferentiableOn ℂ (fun x => (lb (Mx X x0 x τ) i)⁻¹ a b) (cellL X x0)` using `diffOn_inv (fun x => lb (Mx X x0 x τ) i) (fun a b => (Mx_diff τ _ _).differentiableOn) (fun x hx => by rw [det_lb]; exact hl x hx _)`. Establish `hM : ∀ a b, DifferentiableOn ℂ (fun x => Mx X x0 x τ a b) (cellL X x0)` using `fun a b => (Mx_diff τ a b).differentiableOn`. Simplify using `only [wv, Matrix.vecMul, dotProduct]`.

Use `DifferentiableOn.fun_neg ?_` and prove the remaining obligations. Use `DifferentiableOn.fun_sum fun j _ => ?_` and prove the remaining obligations. Conclude with `(hM i _).mul (hinv j ⟨k, h1⟩)`. Distinguish the cases in `h2 : k = i`. Substitute `h2` using the available equality.

Simplify using `only [Lm, Matrix.of_apply, lt_irrefl, ↓reduceDIte, ↓reduceIte]`. Use `fun_prop`. Simplify using `only [Lm, Matrix.of_apply, h1, ↓reduceDIte, h2, ↓reduceIte] fun_prop`.
-/
theorem Lm_diff (τ : X.Ψ) (i k : Fin r) :
    DifferentiableOn ℂ (fun x => Lm (Mx X x0 x τ) i k) (cellL X x0) := by
  have hl : ∀ x ∈ cellL X x0, ∀ k : Fin (r + 1), lminor (Mx X x0 x τ) k ≠ 0 := by
    intro x hx k
    have h1 : DeltaF X x0 x ≠ 0 := hx.2
    unfold DeltaF at h1
    exact Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp h1 τ (Finset.mem_univ _)) k
      (Finset.mem_univ _)
  by_cases h1 : (k : ℕ) < i
  · simp only [Lm, Matrix.of_apply, h1, ↓reduceDIte]
    have hinv : ∀ a b, DifferentiableOn ℂ (fun x => (lb (Mx X x0 x τ) i)⁻¹ a b) (cellL X x0) :=
      diffOn_inv (fun x => lb (Mx X x0 x τ) i) (fun a b => (Mx_diff τ _ _).differentiableOn)
        (fun x hx => by rw [det_lb]; exact hl x hx _)
    have hM : ∀ a b, DifferentiableOn ℂ (fun x => Mx X x0 x τ a b) (cellL X x0) :=
      fun a b => (Mx_diff τ a b).differentiableOn
    simp only [wv, Matrix.vecMul, dotProduct]
    refine DifferentiableOn.fun_neg ?_
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact (hM i _).mul (hinv j ⟨k, h1⟩)
  · by_cases h2 : k = i
    · subst h2
      simp only [Lm, Matrix.of_apply, lt_irrefl, ↓reduceDIte, ↓reduceIte]
      fun_prop
    · simp only [Lm, Matrix.of_apply, h1, ↓reduceDIte, h2, ↓reduceIte]
      fun_prop

/- English proof (translation)
The claim follows from `diffOn_inv (fun x => Lm (Mx X x0 x τ)) (fun i k => Lm_diff τ i k) (fun x _ => by rw [Lm_det]; exact one_ne_zero) a c`.
-/
theorem nF_diff (τ : X.Ψ) (a c : Fin r) : DifferentiableOn ℂ (fun x => nF X x0 x τ a c) (cellL X x0) :=
  diffOn_inv (fun x => Lm (Mx X x0 x τ)) (fun i k => Lm_diff τ i k)
    (fun x _ => by rw [Lm_det]; exact one_ne_zero) a c

/- English proof (translation)
Simplify using `only [bF, Matrix.mul_apply]`. Conclude with `DifferentiableOn.fun_sum fun b _ => (Lm_diff τ a b).mul (Mx_diff τ b c).differentiableOn`.
-/
theorem bF_diff (τ : X.Ψ) (a c : Fin r) : DifferentiableOn ℂ (fun x => bF X x0 x τ a c) (cellL X x0) := by
  simp only [bF, Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun b _ => (Lm_diff τ a b).mul (Mx_diff τ b c).differentiableOn

/- English proof (translation)
Rewrite using `[differentiableOn_pi]`. Introduce `τ`. Rewrite using `[differentiableOn_pi]`. Introduce `a`. Rewrite using `[differentiableOn_pi]`.

Introduce `c`. Conclude with `bF_diff τ a c`.
-/
theorem bF_diffOn : DifferentiableOn ℂ (bF X x0) (cellL X x0) := by
  rw [differentiableOn_pi]
  intro τ
  rw [differentiableOn_pi]
  intro a
  rw [differentiableOn_pi]
  intro c
  exact bF_diff τ a c

/- English proof (translation)
Rewrite using `[differentiableOn_euclidean]`. Introduce `k`. Simplify using `only [zF, PiLp.toLp_apply]`. Conclude with `nF_diff _ _ _`.
-/
theorem zF_diffOn : DifferentiableOn ℂ (zF X x0) (cellL X x0) := by
  rw [differentiableOn_euclidean]
  intro k
  simp only [zF, PiLp.toLp_apply]
  exact nF_diff _ _ _

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

open Matrix Polynomial PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

noncomputable section

namespace GlobalTheory.CompanionTheory.DiagProperProof

variable {n : ℕ}

local notation "θ" => thetaR (starRingEnd ℂ) _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[thetaR_val, Matrix.conjTranspose_apply]`.
-/
theorem th_val (g : GL (Fin n) ℂ) : (θ g).val = ((g⁻¹ : GL (Fin n) ℂ).val)ᴴ := by
  ext i j
  simp [thetaR_val, Matrix.conjTranspose_apply]

/- English proof (translation)
Rewrite using `[← map_inv, th_val, inv_inv]`.
-/
theorem th_inv_val (g : GL (Fin n) ℂ) : ((θ g)⁻¹ : GL (Fin n) ℂ).val = (g.val)ᴴ := by
  rw [← map_inv, th_val, inv_inv]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[th_val, th_inv_val, Matrix.conjTranspose_conjTranspose]`.
-/
theorem th_th (g : GL (Fin n) ℂ) : θ (θ g) = g := by
  apply Units.ext
  rw [th_val, th_inv_val, Matrix.conjTranspose_conjTranspose]

/- English proof (translation)
Establish `h : d * (θ d)⁻¹ = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, th_inv_val, hd, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]`. Simplify using `only [Units.val_one]`. Rewrite using `[← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Complex.mul_conj', hz i]`. Conclude with `(mul_inv_eq_one.mp h).symm`.
-/
theorem th_diag {d : GL (Fin n) ℂ} {z : Fin n → ℂ} (hd : d.val = diagonal z) (hz : ∀ i, ‖z i‖ = 1) :
    θ d = d := by
  have h : d * (θ d)⁻¹ = 1 := by
    apply Units.ext
    rw [Units.val_mul, th_inv_val, hd, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp only [Units.val_one]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    simp [Complex.mul_conj', hz i]
  exact (mul_inv_eq_one.mp h).symm

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion. Establish `: (Units.val ∘ fun g : GL (Fin n) ℂ => θ g) = fun g => ((g⁻¹ : GL (Fin n) ℂ).val)ᴴ`. Use function extensionality and compare the values at `g`. Conclude with `th_val g`.

Rewrite using `[this]`. Conclude with `(Units.continuous_coe_inv).matrix_conjTranspose`. Establish `: (fun g : GL (Fin n) ℂ => ((θ g)⁻¹ : GL (Fin n) ℂ).val) = fun g => (g.val)ᴴ`. Use function extensionality and compare the values at `g`. Conclude with `th_inv_val g`.

Use `show Continuous (fun g : GL (Fin n) ℂ => ((θ g)⁻¹ : GL (Fin n) ℂ).val)`. Rewrite using `[this]`. Conclude with `Units.continuous_val.matrix_conjTranspose`.
-/
theorem continuous_th : Continuous (fun g : GL (Fin n) ℂ => θ g) := by
  rw [Units.continuous_iff]
  constructor
  · have : (Units.val ∘ fun g : GL (Fin n) ℂ => θ g) = fun g => ((g⁻¹ : GL (Fin n) ℂ).val)ᴴ := by
      funext g; exact th_val g
    rw [this]
    exact (Units.continuous_coe_inv).matrix_conjTranspose
  · have : (fun g : GL (Fin n) ℂ => ((θ g)⁻¹ : GL (Fin n) ℂ).val) = fun g => (g.val)ᴴ := by
      funext g; exact th_inv_val g
    show Continuous (fun g : GL (Fin n) ℂ => ((θ g)⁻¹ : GL (Fin n) ℂ).val)
    rw [this]
    exact Units.continuous_val.matrix_conjTranspose

/- English proof (translation)
Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add f g hf hg => simp only [map_add, hf, hg, mul_add, add_mul]`. Consider the case `monomial k a`. Simplify using `only [aeval_monomial, Units.conj_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]`.
-/
theorem aeval_conj (p : GL (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (f : ℂ[X]) :
    aeval (p.val * A * (p⁻¹ : GL (Fin n) ℂ).val) f = p.val * aeval A f * (p⁻¹ : GL (Fin n) ℂ).val := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg, mul_add, add_mul]
  | monomial k a =>
    simp only [aeval_monomial, Units.conj_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]

/- English proof (translation)
Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add f g hf hg => simp only [map_add, hf, hg, eval_add, Matrix.diagonal_add]`. Consider the case `monomial k a`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, eval_monomial]`. Simplify using `[aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, h]`.
-/
theorem aeval_diag (w : Fin n → ℂ) (f : ℂ[X]) :
    aeval (diagonal w) f = diagonal fun k => f.eval (w k) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg, eval_add, Matrix.diagonal_add]
  | monomial k a =>
    ext i j
    by_cases h : i = j
    · subst h
      simp [aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, eval_monomial]
    · simp [aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, h]

def lag (z : Fin n → ℂ) (i : Fin n) : ℂ[X] := Lagrange.basis Finset.univ (fun k => z k ^ 2) i

def tr (z : Fin n → ℂ) (i : Fin n) (y : GL (Fin n) ℂ) : ℂ :=
  trace (aeval ((y * θ y).val) (lag z i) * y.val)

/- English proof (translation)
Unfold `tr`. Establish `h1 : Continuous fun y : GL (Fin n) ℂ => (y * θ y).val` using `Units.continuous_val.comp (continuous_id.mul continuous_th)`. Conclude with `(((Polynomial.continuous_aeval (lag z i)).comp h1).mul Units.continuous_val).matrix_trace`.
-/
theorem continuous_tr (z : Fin n → ℂ) (i : Fin n) : Continuous (tr z i) := by
  unfold tr
  have h1 : Continuous fun y : GL (Fin n) ℂ => (y * θ y).val :=
    Units.continuous_val.comp (continuous_id.mul continuous_th)
  exact (((Polynomial.continuous_aeval (lag z i)).comp h1).mul Units.continuous_val).matrix_trace

/- English proof (translation)
Establish `hθd` using `th_diag hd hz`. Establish `hy2 : (p * d * θ p⁻¹) * θ (p * d * θ p⁻¹) = p * (d * d) * p⁻¹`. Simplify using `only [map_mul, th_th, hθd, map_inv]`. Use `group`. Establish `hdd : (d * d).val = diagonal fun k => z k ^ 2`.

Rewrite using `[Units.val_mul, hd, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Expand and normalize the polynomial expressions, which then agree. Establish `hL : (diagonal fun k => (lag z i).eval (z k ^ 2)) = diagonal (Pi.single i 1)`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Simplify `Lagrange.eval_basis_self (s := Finset.univ) (v := fun k => z k ^ 2) (hinj.injOn) (Finset.mem_univ k)` using `[lag]`.

Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `Lagrange.eval_basis_of_ne (s := Finset.univ) (v := fun k => z k ^ 2) (Ne.symm h) (Finset.mem_univ k)`. Establish `hA : aeval ((p * d * θ p⁻¹ * θ (p * d * θ p⁻¹)).val) (lag z i) = p.val * diagonal (Pi.single i 1) * (p⁻¹ : GL (Fin n) ℂ).val`. Rewrite using `[hy2, Units.val_mul, Units.val_mul, hdd, aeval_conj, aeval_diag, hL]`. Establish `hyv : (p * d * θ p⁻¹).val = p.val * diagonal z * (p.val)ᴴ`.

Rewrite using `[Units.val_mul, Units.val_mul, hd, th_val, inv_inv]`. Establish `hpp : (p⁻¹ : GL (Fin n) ℂ).val * p.val = 1`. Rewrite using `[← Units.val_mul]`. Simplify using the standard rewrite rules. Unfold `tr`.

Rewrite using `[hA, hyv]`. Establish `e1 : p.val * diagonal (Pi.single i 1) * (p⁻¹ : GL (Fin n) ℂ).val * (p.val * diagonal z * (p.val)ᴴ) = p.val * (diagonal (Pi.single i 1) * diagonal z * (p.val)ᴴ)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hpp]; simp only [Matrix.mul_assoc, Matrix.mul_one]`.

Rewrite using `[e1, Matrix.trace_mul_comm, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc, Matrix.trace]`. Simplify using `only [Matrix.diag_apply]`. Simplify using `only [Matrix.diagonal_mul]`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (fun h => (h (Finset.mem_univ i)).elim)]`. Simplify using `only [Pi.single_eq_same, one_mul, Matrix.mul_apply, Matrix.conjTranspose_apply]`.

Use `congr 1`. Use `push_cast`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `using Complex.conj_mul' (p.val k i)`.
-/
theorem tr_eq {d : GL (Fin n) ℂ} {z : Fin n → ℂ} (hd : d.val = diagonal z) (hz : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective fun i => z i ^ 2) (p : GL (Fin n) ℂ) (i : Fin n) :
    tr z i (p * d * θ p⁻¹) = z i * ((∑ k, ‖p.val k i‖ ^ 2 : ℝ) : ℂ) := by
  have hθd := th_diag hd hz
  have hy2 : (p * d * θ p⁻¹) * θ (p * d * θ p⁻¹) = p * (d * d) * p⁻¹ := by
    simp only [map_mul, th_th, hθd, map_inv]
    group
  have hdd : (d * d).val = diagonal fun k => z k ^ 2 := by
    rw [Units.val_mul, hd, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    ring
  have hL : (diagonal fun k => (lag z i).eval (z k ^ 2)) = diagonal (Pi.single i 1) := by
    congr 1
    funext k
    by_cases h : k = i
    · subst h
      simpa [lag] using Lagrange.eval_basis_self (s := Finset.univ) (v := fun k => z k ^ 2)
        (hinj.injOn) (Finset.mem_univ k)
    · rw [Pi.single_eq_of_ne h]
      exact Lagrange.eval_basis_of_ne (s := Finset.univ) (v := fun k => z k ^ 2) (Ne.symm h) (Finset.mem_univ k)
  have hA : aeval ((p * d * θ p⁻¹ * θ (p * d * θ p⁻¹)).val) (lag z i) =
      p.val * diagonal (Pi.single i 1) * (p⁻¹ : GL (Fin n) ℂ).val := by
    rw [hy2, Units.val_mul, Units.val_mul, hdd, aeval_conj, aeval_diag, hL]
  have hyv : (p * d * θ p⁻¹).val = p.val * diagonal z * (p.val)ᴴ := by
    rw [Units.val_mul, Units.val_mul, hd, th_val, inv_inv]
  have hpp : (p⁻¹ : GL (Fin n) ℂ).val * p.val = 1 := by
    rw [← Units.val_mul]; simp
  unfold tr
  rw [hA, hyv]
  have e1 : p.val * diagonal (Pi.single i 1) * (p⁻¹ : GL (Fin n) ℂ).val * (p.val * diagonal z * (p.val)ᴴ) =
      p.val * (diagonal (Pi.single i 1) * diagonal z * (p.val)ᴴ) := by
    calc _ = p.val * diagonal (Pi.single i 1) * ((p⁻¹ : GL (Fin n) ℂ).val * p.val) * diagonal z * (p.val)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hpp]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [e1, Matrix.trace_mul_comm, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc, Matrix.trace]
  simp only [Matrix.diag_apply]
  simp only [Matrix.diagonal_mul]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (fun h => (h (Finset.mem_univ i)).elim)]
  simp only [Pi.single_eq_same, one_mul, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simpa using Complex.conj_mul' (p.val k i)

def twy (x d : GL (Fin n) ℂ) : GL (Fin n) ℂ := x⁻¹ * d * θ x

/- English proof (translation)
Establish `hK : IsCompact {M : Matrix (Fin n) (Fin n) ℂ | ∀ i j, ‖M i j‖ ≤ R}`. Establish `: {M : Matrix (Fin n) (Fin n) ℂ | ∀ i j, ‖M i j‖ ≤ R} = Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) R`. Use extensionality with `M`. Conclude with `⟨fun h i _ j _ => by simpa using h i j, fun h i j => by simpa using h i (Set.mem_univ _) j (Set.mem_univ _)⟩`. Rewrite using `[this]`.

Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Establish `hemb` using `Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[hemb.isCompact_iff]`. Use `(hK.prod (hK.image MulOpposite.continuous_op)).of_isClosed_subset (hemb.isClosedMap _ hS) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Use `⟨fun i j => (h x hx i j).1, (x⁻¹ : GL (Fin n) ℂ).val, fun i j => (h x hx i j).2, rfl⟩` and prove the remaining obligations.
-/
theorem isCompact_of_bounded {S : Set (GL (Fin n) ℂ)} (hS : IsClosed S) (R : ℝ)
    (h : ∀ x ∈ S, ∀ i j, ‖x.val i j‖ ≤ R ∧ ‖(x⁻¹ : GL (Fin n) ℂ).val i j‖ ≤ R) : IsCompact S := by
  have hK : IsCompact {M : Matrix (Fin n) (Fin n) ℂ | ∀ i j, ‖M i j‖ ≤ R} := by
    have : {M : Matrix (Fin n) (Fin n) ℂ | ∀ i j, ‖M i j‖ ≤ R} =
        Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) R := by
      ext M
      exact ⟨fun h i _ j _ => by simpa using h i j,
        fun h i j => by simpa using h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hemb := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) ℂ)
  rw [hemb.isCompact_iff]
  refine (hK.prod (hK.image MulOpposite.continuous_op)).of_isClosed_subset (hemb.isClosedMap _ hS) ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨fun i j => (h x hx i j).1, (x⁻¹ : GL (Fin n) ℂ).val, fun i j => (h x hx i j).2, rfl⟩

/- English proof (translation)
Establish `h1 : ‖tr z i (p * d * θ p⁻¹)‖ ≤ B` using `(Finset.single_le_sum (f := fun i => ‖tr z i (p * d * θ p⁻¹)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans hB`. Rewrite `h1` using `[tr_eq hd hz hinj, norm_mul, hz, one_mul, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]`. Establish `h2 : ‖p.val k i‖ ^ 2 ≤ ∑ k, ‖p.val k i‖ ^ 2` using `Finset.single_le_sum (f := fun k => ‖p.val k i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)`. Establish `h3 : 0 ≤ B` using `(by positivity : 0 ≤ ‖p.val k i‖ ^ 2).trans (h2.trans h1)`. Use polynomial arithmetic with `[sq_nonneg (‖p.val k i‖ - 1)]`.
-/
theorem col_bound {d : GL (Fin n) ℂ} {z : Fin n → ℂ} (hd : d.val = diagonal z) (hz : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective fun i => z i ^ 2) (p : GL (Fin n) ℂ) {B : ℝ}
    (hB : ∑ i, ‖tr z i (p * d * θ p⁻¹)‖ ≤ B) (k i : Fin n) : ‖p.val k i‖ ≤ B + 1 := by
  have h1 : ‖tr z i (p * d * θ p⁻¹)‖ ≤ B :=
    (Finset.single_le_sum (f := fun i => ‖tr z i (p * d * θ p⁻¹)‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)).trans hB
  rw [tr_eq hd hz hinj, norm_mul, hz, one_mul, Complex.norm_real, Real.norm_of_nonneg
    (Finset.sum_nonneg fun _ _ => by positivity)] at h1
  have h2 : ‖p.val k i‖ ^ 2 ≤ ∑ k, ‖p.val k i‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖p.val k i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
  have h3 : 0 ≤ B := (by positivity : 0 ≤ ‖p.val k i‖ ^ 2).trans (h2.trans h1)
  nlinarith [sq_nonneg (‖p.val k i‖ - 1)]

/- English proof (translation)
Introduce `n d z hd hz hinj C hC`. Establish `hθd` using `th_diag hd hz`. Use `set S : Set (GL (Fin n) ℂ) := {x | PositivityTheory.Rg.Tf.Loc.twConj (thetaR (starRingEnd ℂ) n) x d ∈ C} with hSdef`. Establish `hcont : Continuous fun x : GL (Fin n) ℂ => PositivityTheory.Rg.Tf.Loc.twConj (thetaR (starRingEnd ℂ) n) x d`. Unfold `PositivityTheory.Rg.Tf.Loc.twConj`.

Conclude with `(continuous_inv.mul continuous_const).mul continuous_th`. Establish `hcl : IsClosed S` using `hC.isClosed.preimage hcont`. Establish `hC' : IsCompact (C ∪ (fun g : GL (Fin n) ℂ => θ g) '' C)` using `hC.union (hC.image continuous_th)`. Establish `hG : Continuous fun y : GL (Fin n) ℂ => ∑ i, ‖tr z i y‖` using `continuous_finsetSum _ fun i _ => (continuous_tr z i).norm`. Take `⟨B, hB⟩` from `hC'.exists_bound_of_continuousOn hG.continuousOn`.

Establish `hB' : ∀ y ∈ C ∪ (fun g : GL (Fin n) ℂ => θ g) '' C, ∑ i, ‖tr z i y‖ ≤ B` using `fun y hy => (le_abs_self _).trans (hB y hy)`. Use `isCompact_of_bounded hcl (B + 1) fun x hx i j => ⟨?_, ?_⟩` and prove the remaining obligations. Establish `hy : twy x d ∈ C` using `hx`. Establish `e : θ (twy x d) = (θ x⁻¹) * d * θ (θ x⁻¹)⁻¹`. Simplify using `only [twy, map_mul, map_inv, th_th, hθd, inv_inv]`.

Use `col_bound hd hz hinj (θ x⁻¹) (B := B) (by` as an intermediate fact. Rewrite using `[← e]`. Conclude with `hB' _ (Or.inr ⟨_, hy, rfl⟩)) j i`. Rewrite `this` using `[th_val, inv_inv, Matrix.conjTranspose_apply, norm_star]`. Conclude with `this`.

Establish `hy : twy x d ∈ C` using `hx`. Establish `e : twy x d = x⁻¹ * d * θ (x⁻¹)⁻¹` using `by simp [twy]`. Conclude with `col_bound hd hz hinj x⁻¹ (B := B) (by rw [← e]; exact hB' _ (Or.inl hy)) i j`.
-/
theorem diagProper : DiagProper := by
  intro n d z hd hz hinj C hC
  have hθd := th_diag hd hz
  set S : Set (GL (Fin n) ℂ) := {x | PositivityTheory.Rg.Tf.Loc.twConj (thetaR (starRingEnd ℂ) n) x d ∈ C} with hSdef
  have hcont : Continuous fun x : GL (Fin n) ℂ => PositivityTheory.Rg.Tf.Loc.twConj (thetaR (starRingEnd ℂ) n) x d := by
    unfold PositivityTheory.Rg.Tf.Loc.twConj
    exact (continuous_inv.mul continuous_const).mul continuous_th
  have hcl : IsClosed S := hC.isClosed.preimage hcont
  have hC' : IsCompact (C ∪ (fun g : GL (Fin n) ℂ => θ g) '' C) := hC.union (hC.image continuous_th)
  have hG : Continuous fun y : GL (Fin n) ℂ => ∑ i, ‖tr z i y‖ :=
    continuous_finsetSum _ fun i _ => (continuous_tr z i).norm
  obtain ⟨B, hB⟩ := hC'.exists_bound_of_continuousOn hG.continuousOn
  have hB' : ∀ y ∈ C ∪ (fun g : GL (Fin n) ℂ => θ g) '' C, ∑ i, ‖tr z i y‖ ≤ B :=
    fun y hy => (le_abs_self _).trans (hB y hy)
  refine isCompact_of_bounded hcl (B + 1) fun x hx i j => ⟨?_, ?_⟩
  ·
    have hy : twy x d ∈ C := hx
    have e : θ (twy x d) = (θ x⁻¹) * d * θ (θ x⁻¹)⁻¹ := by
      simp only [twy, map_mul, map_inv, th_th, hθd, inv_inv]
    have := col_bound hd hz hinj (θ x⁻¹) (B := B) (by
      rw [← e]; exact hB' _ (Or.inr ⟨_, hy, rfl⟩)) j i
    rw [th_val, inv_inv, Matrix.conjTranspose_apply, norm_star] at this
    exact this
  · have hy : twy x d ∈ C := hx
    have e : twy x d = x⁻¹ * d * θ (x⁻¹)⁻¹ := by simp [twy]
    exact col_bound hd hz hinj x⁻¹ (B := B) (by rw [← e]; exact hB' _ (Or.inl hy)) i j

end GlobalTheory.CompanionTheory.DiagProperProof

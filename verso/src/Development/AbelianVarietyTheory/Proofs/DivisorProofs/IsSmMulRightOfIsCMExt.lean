import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportWordMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped NNReal Matrix Topology ContDiff
open GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.UAut.RightTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Take `⟨w, τ, Z, hZ, hγ⟩` from `hγ`. Establish `hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1` using `fun x => (archEquiv J h τ x).2`. Establish `h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`. Establish `h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1`.

Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Establish `u1` using `hu (projArch σ J w a)`. Establish `u2` using `hu (projArch σ J w a)⁻¹`. Use `⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_, fun t => ?_⟩` and prove the remaining obligations. Generalize the expression as in `GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *`.

Generalize the expression as in `GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *`. Generalize the expression as in `J.map τ.1 = Q at u1 u2 hZ ⊢`. Establish `e1 : M'ᴴ * Q = Q * M` using `by conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]`. Establish `e2 : Q * M' = Mᴴ * Q` using `by conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by`. Rewrite using `[e1, e2]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]`.

Take `⟨y, e1, e2⟩` from `hγ t`. Use `⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩` and prove the remaining obligations. Use `show a⁻¹ * γ t * a = _`. Rewrite using `[e1]`. Use `GAd_ext σ J (fun u => ?_) fun v => by simp` and prove the remaining obligations.

Distinguish the cases in `e : u = w`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[projArch_embArch_ne σ J e]`. Rewrite using `[map_mul, map_mul, e2]`.

Generalize the expression as in `GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *`. Generalize the expression as in `GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *`. Establish `hM : IsUnit M` using `⟨⟨M, M', h2, h1⟩, rfl⟩`. Rewrite using `[← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem isRealLine_conj (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (a : GAd σ J) :
    IsRealLine σ J fun t => a⁻¹ * γ t * a := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1 :=
    fun x => (archEquiv J h τ x).2
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have u1 := hu (projArch σ J w a)
  have u2 := hu (projArch σ J w a)⁻¹
  refine ⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_,
    fun t => ?_⟩
  · generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    generalize J.map τ.1 = Q at u1 u2 hZ ⊢
    have e1 : M'ᴴ * Q = Q * M := by
      conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : Q * M' = Mᴴ * Q := by
      conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]
    calc (M' * Z * M)ᴴ * Q + Q * (M' * Z * M) = Mᴴ * Zᴴ * (M'ᴴ * Q) + (Q * M') * Z * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
    · show a⁻¹ * γ t * a = _
      rw [e1]
      refine GAd_ext σ J (fun u => ?_) fun v => by simp
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ J e]
    · rw [map_mul, map_mul, e2]
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
      have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
      rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.UAut.RightTranslate

open GlobalTheory.UAut.RightTranslate in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J h f a hf`. Introduce `k γ hγ g`. Establish `hc : ∀ l : List (GAd σ J), (l.map fun x => a⁻¹ * x * a).prod = a⁻¹ * l.prod * a` using `fun l => by`. Proceed by induction on `l with`. Consider the case `nil => simp`.

Consider the case `cons x l ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih]`. Simplify using `[mul_assoc]`. Establish `e : (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)) = fun t => f (g * a * (List.ofFn fun i => a⁻¹ * γ i (t i) * a).prod)` using `funext fun t => by`. Rewrite using `[show (List.ofFn fun i => a⁻¹ * γ i (t i) * a) = (List.ofFn fun i => γ i (t i)).map fun x => a⁻¹ * x * a from by`. Rewrite using `[List.map_ofFn]`.

Use the proof step `rfl, hc]`. Simplify using `[mul_assoc]`. Use `show ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)`. Rewrite using `[e]`. Conclude with `hf k (fun i t => a⁻¹ * γ i t * a) (fun i => isRealLine_conj h (hγ i) a) (g * a)`.
-/
theorem GlobalTheory.UAut.isSm_mul_right_of_isCMExt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E), IsCMExt F E σ → ∀ (f : GlobalTheory.AdelicU.GAd σ J → ℂ) (a : GlobalTheory.AdelicU.GAd σ J), GlobalTheory.UAut.IsSm σ J f → GlobalTheory.UAut.IsSm σ J (fun x => f (x * a)) := by
  intro F E _ _ _ _ _ σ n J h f a hf
  intro k γ hγ g
  have hc : ∀ l : List (GAd σ J), (l.map fun x => a⁻¹ * x * a).prod = a⁻¹ * l.prod * a := fun l => by
    induction l with
    | nil => simp
    | cons x l ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih]; simp [mul_assoc]
  have e : (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)) =
      fun t => f (g * a * (List.ofFn fun i => a⁻¹ * γ i (t i) * a).prod) := funext fun t => by
    rw [show (List.ofFn fun i => a⁻¹ * γ i (t i) * a) = (List.ofFn fun i => γ i (t i)).map fun x => a⁻¹ * x * a from by
      rw [List.map_ofFn]; rfl, hc]
    simp [mul_assoc]
  show ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)
  rw [e]
  exact hf k (fun i t => a⁻¹ * γ i t * a) (fun i => isRealLine_conj h (hγ i) a) (g * a)

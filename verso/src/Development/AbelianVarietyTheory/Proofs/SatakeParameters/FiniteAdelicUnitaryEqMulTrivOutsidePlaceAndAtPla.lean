import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.PlaceDecomp

/- English proof (translation)
Introduce `L _ _ _ n v κ`. Use `set e : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v 1 with he_def`. Establish `hsgl : GlobalTheory.InertUmax.sgl L v 1 * GlobalTheory.InertUmax.sgl L v 1 = GlobalTheory.InertUmax.sgl L v 1`. Use `RestrictedProduct.ext _ _ fun w => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `GlobalTheory.InertUmax.sgl L v 1 w * GlobalTheory.InertUmax.sgl L v 1 w = GlobalTheory.InertUmax.sgl L v 1 w`.

Break down `eq_or_ne w v with rfl | hw` into its components or cases. Simplify using `only [GlobalTheory.InertUmax.sgl_same, mul_one]`. Simplify using `only [GlobalTheory.InertUmax.sgl_ne L _ _ hw, mul_zero]`. Establish `he2 : e * e = e` using `by rw [he_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hsgl]`. Establish `hce : conjAL L e = e` using `by simp [he_def, conjAL, Algebra.TensorProduct.map_tmul]`.

Establish `hcv : compAt L v e = 1`. Rewrite using `[he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]`. Both sides reduce to the same expression. Establish `hcw : ∀ w, w ≠ v → compAt L w e = 0` using `fun w hw => by`. Rewrite using `[he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L _ _ hw, TensorProduct.tmul_zero]`.

Set `θ : AL L × AL L →+* AL L` to `{ toFun := fun q => e * q.1 + (1 - e) * q.2 map_one' := by simp only [Prod.fst_one, Prod.snd_one]; ring map_mul' := fun q q' => by`. Simplify using `only [Prod.fst_mul, Prod.snd_mul]`. Take the linear combination `(-(q.1 * q'.1 - q.1 * q'.2 - q.2 * q'.1 + q.2 * q'.2)) * he2`. Use the proof step `map_zero' := by simp`. Use the proof step `map_add' := fun q q' => by simp only [Prod.fst_add, Prod.snd_add]; ring }`.

Establish `hθ : ∀ q, θ q = e * q.1 + (1 - e) * q.2` using `fun _ => rfl`. Establish `hθc : ∀ a b, conjAL L (θ (a, b)) = θ (conjAL L a, conjAL L b)`. Introduce `a b`. Rewrite using `[hθ, hθ, map_add, map_mul, map_mul, map_sub, map_one, hce]`. Establish `hθv : ∀ q, compAt L v (θ q) = compAt L v q.1`.

Introduce `q`. Rewrite using `[hθ, map_add, map_mul, map_mul, map_sub, map_one, hcv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hθw : ∀ w, w ≠ v → ∀ q, compAt L w (θ q) = compAt L w q.2`. Introduce `w hw q`.

Rewrite using `[hθ, map_add, map_mul, map_mul, map_sub, map_one, hcw w hw]`. Expand and normalize the polynomial expressions, which then agree. Set `pr : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L × AL L)` to `fun A B i j => (A i j, B i j)`. Establish `pr_mul : ∀ A B C D, pr A B * pr C D = pr (A * C) (B * D)`. Introduce `A B C D`.

Use extensionality with `i j`. Use `show (∑ l, pr A B i l * pr C D l j).1 = ∑ l, A i l * C l j`. Rewrite using `[Prod.fst_sum]`. Both sides reduce to the same expression. Use `show (∑ l, pr A B i l * pr C D l j).2 = ∑ l, B i l * D l j`.

Rewrite using `[Prod.snd_sum]`. Both sides reduce to the same expression. Establish `pr_one : pr 1 1 = 1`. Apply the tactic sequence `ext i j <;> by_cases h : i = j <;> simp [pr, Matrix.one_apply, h]`. Set `M : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L)` to `fun A B => (pr A B).map θ`.

Establish `hM : ∀ A B i j, M A B i j = e * A i j + (1 - e) * B i j` using `fun _ _ _ _ => rfl`. Establish `M_mul : ∀ A B C D, M A B * M C D = M (A * C) (B * D)`. Introduce `A B C D`. Use `show (pr A B).map θ * (pr C D).map θ = (pr (A * C) (B * D)).map θ`. Rewrite using `[← Matrix.map_mul, pr_mul]`.

Establish `M_one : M 1 1 = 1` using `by show (pr 1 1).map θ = 1`. Rewrite using `[pr_one, Matrix.map_one _ (map_zero θ) (map_one θ)]`. Establish `M_conj : ∀ A B, conjT (conjAL L) (M A B) = M (conjT (conjAL L) A) (conjT (conjAL L) B)`. Introduce `A B`. Use extensionality with `i j`.

Use `show conjAL L (θ (A j i, B j i)) = θ (conjAL L (A j i), conjAL L (B j i))`. Conclude with `hθc _ _`. Establish `M_diag : ∀ A, M A A = A` using `by intro A; ext i j; rw [hM]; ring`. Use `set K : Matrix (Fin n) (Fin n) (AL L) := ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hK`. Establish `hKK : K * conjT (conjAL L) K = 1` using `κ.2`.

Establish `hX : M K 1 * conjT (conjAL L) (M K 1) = 1`. Rewrite using `[M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]`. Establish `hY : M 1 K * conjT (conjAL L) (M 1 K) = 1`. Rewrite using `[M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]`. Set `gX : GL (Fin n) (AL L)` to `⟨M K 1, conjT (conjAL L) (M K 1), hX, mul_eq_one_comm.mp hX⟩`.

Set `gY : GL (Fin n) (AL L)` to `⟨M 1 K, conjT (conjAL L) (M 1 K), hY, mul_eq_one_comm.mp hY⟩`. Establish `hc1 : ∀ w i j, compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j`. Apply the tactic sequence `intro w i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`. Use `⟨⟨gX, hX⟩, ⟨gY, hY⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`.

Establish `hw' : w ≠ v` using `hw`. Use extensionality with `i j`. Use `show compAt L w (θ (K i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) = _`. Rewrite using `[hθw w hw', hc1]`. Introduce `w hw`.

Establish `hw' : w = v` using `by simpa using hw`. Substitute `hw'` using the available equality. Use extensionality with `i j`. Use `show compAt L w (θ ((1 : Matrix (Fin n) (Fin n) (AL L)) i j, K i j)) = _`. Rewrite using `[hθv, hc1]`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext show K = M K 1 * M 1 K` to reduce the goal to its premises. Rewrite using `[M_mul, Matrix.mul_one, Matrix.one_mul, M_diag]`.
-/
theorem decomp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GAf L n),
    ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ g = x * y := by
  intro L _ _ _ n v κ
  classical
  set e : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v 1 with he_def
  have hsgl : GlobalTheory.InertUmax.sgl L v 1 * GlobalTheory.InertUmax.sgl L v 1 = GlobalTheory.InertUmax.sgl L v 1 := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    change GlobalTheory.InertUmax.sgl L v 1 w * GlobalTheory.InertUmax.sgl L v 1 w = GlobalTheory.InertUmax.sgl L v 1 w
    rcases eq_or_ne w v with rfl | hw
    · simp only [GlobalTheory.InertUmax.sgl_same, mul_one]
    · simp only [GlobalTheory.InertUmax.sgl_ne L _ _ hw, mul_zero]
  have he2 : e * e = e := by rw [he_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hsgl]
  have hce : conjAL L e = e := by simp [he_def, conjAL, Algebra.TensorProduct.map_tmul]
  have hcv : compAt L v e = 1 := by
    rw [he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]; rfl
  have hcw : ∀ w, w ≠ v → compAt L w e = 0 := fun w hw => by
    rw [he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L _ _ hw, TensorProduct.tmul_zero]
  let θ : AL L × AL L →+* AL L :=
    { toFun := fun q => e * q.1 + (1 - e) * q.2
      map_one' := by simp only [Prod.fst_one, Prod.snd_one]; ring
      map_mul' := fun q q' => by
        simp only [Prod.fst_mul, Prod.snd_mul]
        linear_combination (-(q.1 * q'.1 - q.1 * q'.2 - q.2 * q'.1 + q.2 * q'.2)) * he2
      map_zero' := by simp
      map_add' := fun q q' => by simp only [Prod.fst_add, Prod.snd_add]; ring }
  have hθ : ∀ q, θ q = e * q.1 + (1 - e) * q.2 := fun _ => rfl
  have hθc : ∀ a b, conjAL L (θ (a, b)) = θ (conjAL L a, conjAL L b) := by
    intro a b; rw [hθ, hθ, map_add, map_mul, map_mul, map_sub, map_one, hce]
  have hθv : ∀ q, compAt L v (θ q) = compAt L v q.1 := by
    intro q; rw [hθ, map_add, map_mul, map_mul, map_sub, map_one, hcv]; ring
  have hθw : ∀ w, w ≠ v → ∀ q, compAt L w (θ q) = compAt L w q.2 := by
    intro w hw q; rw [hθ, map_add, map_mul, map_mul, map_sub, map_one, hcw w hw]; ring
  let pr : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) →
      Matrix (Fin n) (Fin n) (AL L × AL L) :=
    fun A B i j => (A i j, B i j)
  have pr_mul : ∀ A B C D, pr A B * pr C D = pr (A * C) (B * D) := by
    intro A B C D; ext i j
    · show (∑ l, pr A B i l * pr C D l j).1 = ∑ l, A i l * C l j
      rw [Prod.fst_sum]; rfl
    · show (∑ l, pr A B i l * pr C D l j).2 = ∑ l, B i l * D l j
      rw [Prod.snd_sum]; rfl
  have pr_one : pr 1 1 = 1 := by
    ext i j <;> by_cases h : i = j <;> simp [pr, Matrix.one_apply, h]
  let M : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) →
      Matrix (Fin n) (Fin n) (AL L) :=
    fun A B => (pr A B).map θ
  have hM : ∀ A B i j, M A B i j = e * A i j + (1 - e) * B i j := fun _ _ _ _ => rfl
  have M_mul : ∀ A B C D, M A B * M C D = M (A * C) (B * D) := by
    intro A B C D; show (pr A B).map θ * (pr C D).map θ = (pr (A * C) (B * D)).map θ
    rw [← Matrix.map_mul, pr_mul]
  have M_one : M 1 1 = 1 := by
    show (pr 1 1).map θ = 1
    rw [pr_one, Matrix.map_one _ (map_zero θ) (map_one θ)]
  have M_conj : ∀ A B, conjT (conjAL L) (M A B) = M (conjT (conjAL L) A) (conjT (conjAL L) B) := by
    intro A B; ext i j
    show conjAL L (θ (A j i, B j i)) = θ (conjAL L (A j i), conjAL L (B j i))
    exact hθc _ _
  have M_diag : ∀ A, M A A = A := by intro A; ext i j; rw [hM]; ring
  set K : Matrix (Fin n) (Fin n) (AL L) := ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
    with hK
  have hKK : K * conjT (conjAL L) K = 1 := κ.2
  have hX : M K 1 * conjT (conjAL L) (M K 1) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  have hY : M 1 K * conjT (conjAL L) (M 1 K) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  let gX : GL (Fin n) (AL L) := ⟨M K 1, conjT (conjAL L) (M K 1), hX, mul_eq_one_comm.mp hX⟩
  let gY : GL (Fin n) (AL L) := ⟨M 1 K, conjT (conjAL L) (M 1 K), hY, mul_eq_one_comm.mp hY⟩
  have hc1 : ∀ w i j, compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro w i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  refine ⟨⟨gX, hX⟩, ⟨gY, hY⟩, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w ≠ v := hw
    ext i j
    show compAt L w (θ (K i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) = _
    rw [hθw w hw', hc1]
  · intro w hw
    have hw' : w = v := by simpa using hw
    subst hw'
    ext i j
    show compAt L w (θ ((1 : Matrix (Fin n) (Fin n) (AL L)) i j, K i j)) = _
    rw [hθv, hc1]
  · apply Subtype.ext; apply Units.ext
    show K = M K 1 * M 1 K
    rw [M_mul, Matrix.mul_one, Matrix.one_mul, M_diag]

end GlobalTheory.PlaceDecomp

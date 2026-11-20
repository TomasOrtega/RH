import Mathlib
open IsLocalRing

namespace GlobalTheory

open MvPolynomial

/- English proof (translation)
Introduce `K L _ _ _ _ n d f hf`. Use `set m := Module.finrank K L`. Use `set b := Module.finBasis K L`. Set `g : Fin n → MvPolynomial (Fin n × Fin m) L` to `fun i => ∑ j, X (i, j) * C (b j)`. Establish `hg : ∀ i, (g i).IsHomogeneous 1`.

Introduce `i`. Use `IsHomogeneous.sum _ _ _ (fun j _ => ?_)` and prove the remaining obligations. Simplify using `using (isHomogeneous_X L (i, j)).mul (isHomogeneous_C _ (b j))`. Set `G : MvPolynomial (Fin n × Fin m) L` to `bind₁ g f`. Establish `hG : G.IsHomogeneous d` using `by simpa [G, aeval_eq_bind₁] using hf.aeval g hg`.

Establish `hGev : ∀ y : Fin n × Fin m → K, eval (fun p => algebraMap K L (y p)) G = eval (fun i => ∑ j, algebraMap K L (y (i, j)) * b j) f`. Introduce `y`. Establish `key : ∀ (φ : MvPolynomial (Fin n) L) (x : Fin n × Fin m → L), eval x (bind₁ g φ) = eval (fun i => eval x (g i)) φ`. Introduce `φ x`. Apply the tactic sequence `induction φ using MvPolynomial.induction_on <;> simp_all`.

Rewrite using `[show G = bind₁ g f from rfl, key]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `[g]`. Both sides reduce to the same expression.

Set `M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin m) K)` to `fun i j => ∑ s ∈ G.support, monomial s (Algebra.leftMulMatrix b (coeff s G) i j)`. Establish `hM : ∀ i j, (M i j).IsHomogeneous d`. Introduce `i j`. Use `IsHomogeneous.sum _ _ _ (fun s hs => isHomogeneous_monomial _ ?_)` and prove the remaining obligations. Use `hG (mem_support_iff.mp hs)` as an intermediate fact.

Rewrite using `[Finsupp.degree_eq_weight_one]` and apply the resulting hypothesis. Use `⟨M.det, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_apply']`. Use `IsHomogeneous.sum _ _ _ (fun σ _ => ?_)` and prove the remaining obligations. Establish `hp : (∏ i, M (σ i) i).IsHomogeneous (d * m)`.

Use `IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => d) (fun i _ => hM _ _)` as an intermediate fact. Simplify `this` using `[mul_comm]`. Establish `hε : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n × Fin m) K).IsHomogeneous 0`. Rewrite using `[← map_intCast (C : K →+* MvPolynomial (Fin n × Fin m) K)]`. Conclude with `isHomogeneous_C _ _`.

Simplify using `using hε.mul hp`. Introduce `y`. Rewrite using `[RingHom.map_det, Algebra.norm_eq_matrix_det b, ← hGev]`. Use `congr 1`. Use extensionality with `i j`.

Use `show eval y (M i j) = _`. Simplify using `only [M, map_sum, eval_monomial]`. Rewrite using `[eval_eq' _ G, map_sum, Matrix.sum_apply]`. Use `Finset.sum_congr rfl (fun s _ => ?_)` and prove the remaining obligations. Establish `: coeff s G * ∏ k, (algebraMap K L (y k)) ^ (s k) = (∏ k, y k ^ s k) • coeff s G`.

Rewrite using `[Algebra.smul_def, mul_comm]`. Simplify using `[map_prod, map_pow]`. Rewrite using `[this, map_smul, Matrix.smul_apply, smul_eq_mul, mul_comm, Finsupp.prod_fintype]`. Simplify using the standard rewrite rules.
-/
theorem norm_comp_homogeneous_isHomogeneous :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n d : ℕ)
      (f : MvPolynomial (Fin n) L), f.IsHomogeneous d →
      ∃ F : MvPolynomial (Fin n × Fin (Module.finrank K L)) K,
        F.IsHomogeneous (d * Module.finrank K L) ∧
        ∀ y : Fin n × Fin (Module.finrank K L) → K, MvPolynomial.eval y F =
          Algebra.norm K (MvPolynomial.eval
            (fun i => ∑ j, algebraMap K L (y (i, j)) * Module.finBasis K L j) f) := by
  intro K L _ _ _ _ n d f hf
  classical
  set m := Module.finrank K L
  set b := Module.finBasis K L
  let g : Fin n → MvPolynomial (Fin n × Fin m) L := fun i => ∑ j, X (i, j) * C (b j)
  have hg : ∀ i, (g i).IsHomogeneous 1 := by
    intro i
    refine IsHomogeneous.sum _ _ _ (fun j _ => ?_)
    simpa using (isHomogeneous_X L (i, j)).mul (isHomogeneous_C _ (b j))
  let G : MvPolynomial (Fin n × Fin m) L := bind₁ g f
  have hG : G.IsHomogeneous d := by simpa [G, aeval_eq_bind₁] using hf.aeval g hg
  have hGev : ∀ y : Fin n × Fin m → K, eval (fun p => algebraMap K L (y p)) G =
      eval (fun i => ∑ j, algebraMap K L (y (i, j)) * b j) f := by
    intro y
    have key : ∀ (φ : MvPolynomial (Fin n) L) (x : Fin n × Fin m → L),
        eval x (bind₁ g φ) = eval (fun i => eval x (g i)) φ := by
      intro φ x
      induction φ using MvPolynomial.induction_on <;> simp_all
    rw [show G = bind₁ g f from rfl, key]
    congr 2
    funext i
    simp [g]
    rfl
  let M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin m) K) :=
    fun i j => ∑ s ∈ G.support, monomial s (Algebra.leftMulMatrix b (coeff s G) i j)
  have hM : ∀ i j, (M i j).IsHomogeneous d := by
    intro i j
    refine IsHomogeneous.sum _ _ _ (fun s hs => isHomogeneous_monomial _ ?_)
    have := hG (mem_support_iff.mp hs)
    rwa [Finsupp.degree_eq_weight_one]
  refine ⟨M.det, ?_, ?_⟩
  · rw [Matrix.det_apply']
    refine IsHomogeneous.sum _ _ _ (fun σ _ => ?_)
    have hp : (∏ i, M (σ i) i).IsHomogeneous (d * m) := by
      have := IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => d) (fun i _ => hM _ _)
      simpa [mul_comm] using this
    have hε : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n × Fin m) K).IsHomogeneous 0 := by
      rw [← map_intCast (C : K →+* MvPolynomial (Fin n × Fin m) K)]
      exact isHomogeneous_C _ _
    simpa using hε.mul hp
  · intro y
    rw [RingHom.map_det, Algebra.norm_eq_matrix_det b, ← hGev]
    congr 1
    ext i j
    show eval y (M i j) = _
    simp only [M, map_sum, eval_monomial]
    rw [eval_eq' _ G, map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have : coeff s G * ∏ k, (algebraMap K L (y k)) ^ (s k) = (∏ k, y k ^ s k) • coeff s G := by
      rw [Algebra.smul_def, mul_comm]
      simp [map_prod, map_pow]
    rw [this, map_smul, Matrix.smul_apply, smul_eq_mul, mul_comm, Finsupp.prod_fintype]
    simp

end GlobalTheory

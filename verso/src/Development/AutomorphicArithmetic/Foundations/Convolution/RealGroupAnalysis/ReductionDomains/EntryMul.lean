import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hq : ∀ z : Fin n → ℝ, (z ᵥ* M) ⬝ᵥ (z ᵥ* M) = z ⬝ᵥ z`. Introduce `z`. Establish `h2` using `congrArg (· ^ 2) (h z)`.

Simplify using `only [Reduction.euclidNorm_sq, Real.norm_eq_abs, sq_abs] at h2`. Simplify `h2` using `only [dotProduct, sq]`. Establish `hb : ∀ x z : Fin n → ℝ, (x ᵥ* M) ⬝ᵥ (z ᵥ* M) = x ⬝ᵥ z`. Introduce `x z`. Establish `h1` using `hq (x + z)`.

Rewrite `h1` using `[add_vecMul]`. Simplify using `only [add_dotProduct, dotProduct_add, hq] at h1`. Rewrite `h1` using `[dotProduct_comm (z ᵥ* M), dotProduct_comm z x]`. Combine the linear equalities and inequalities to obtain the conclusion. Use extensionality with `i j`.

Establish `h3` using `hb (Pi.single i 1) (Pi.single j 1)`. Rewrite `h3` using `[single_one_vecMul, single_one_vecMul, single_one_dotProduct]`. Rewrite using `[mul_apply, one_apply]`. Simplify using `only [transpose_apply]`. Use `Eq.trans h3 ?_` and prove the remaining obligations.

Simplify using `[Pi.single_apply]`. Introduce `h z`. Use `Reduction.euclidNorm_vecMul_unitary ?_ z` and prove the remaining obligations. Rewrite using `[mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]`. Conclude with `h`.
-/
private theorem real_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (∀ z : Fin n → ℝ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z) ↔ M * Mᵀ = 1 := by
  constructor
  · intro h
    have hq : ∀ z : Fin n → ℝ, (z ᵥ* M) ⬝ᵥ (z ᵥ* M) = z ⬝ᵥ z := by
      intro z
      have h2 := congrArg (· ^ 2) (h z)
      simp only [Reduction.euclidNorm_sq, Real.norm_eq_abs, sq_abs] at h2
      simpa only [dotProduct, sq] using h2
    have hb : ∀ x z : Fin n → ℝ, (x ᵥ* M) ⬝ᵥ (z ᵥ* M) = x ⬝ᵥ z := by
      intro x z
      have h1 := hq (x + z)
      rw [add_vecMul] at h1
      simp only [add_dotProduct, dotProduct_add, hq] at h1
      rw [dotProduct_comm (z ᵥ* M), dotProduct_comm z x] at h1
      linarith
    ext i j
    have h3 := hb (Pi.single i 1) (Pi.single j 1)
    rw [single_one_vecMul, single_one_vecMul, single_one_dotProduct] at h3
    rw [mul_apply, one_apply]
    simp only [transpose_apply]
    refine Eq.trans h3 ?_
    simp [Pi.single_apply]
  · intro h z
    refine Reduction.euclidNorm_vecMul_unitary ?_ z
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    exact h

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Both sides reduce to the same expression.
-/
private theorem entry_mul {F : Type} [Field F] [NumberField F] (k : G1 F) (w : InfinitePlace F) (i j : Fin 2) :
    ((k.1 * k.1ᵀ) i j).1 w = ∑ l, (k i l).1 w * (k j l).1 w := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  rfl

/- English proof (translation)
Rewrite using `[one_apply, one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
private theorem entry_one {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w = (1 : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  rw [one_apply, one_apply]
  split_ifs <;> rfl

/- English proof (translation)
Use `set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) with hψdef`. Establish `hψ : ∀ z, ‖ψ.toRingHom z‖ = ‖z‖` using `fun z => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero (map_zero _) z`. Set `M : Matrix (Fin 2) (Fin 2) ℝ` to `Matrix.of fun i j => ψ ((k i j).1 w)`. Establish `e : ∀ z : Fin 2 → w.Completion, (fun j => ψ.toRingHom ((z ᵥ* (Reduction.infAt w (gl k) : Matrix (Fin 2) (Fin 2) w.Completion)) j)) = (fun i => ψ.toRingHom (z i)) ᵥ* M`. Introduce `z`.

Use extensionality with `j`. Simplify using `only [vecMul, dotProduct, map_sum, map_mul]`. Both sides reduce to the same expression. Establish `key : ∀ i j, (M * Mᵀ) i j = ψ (((k.1 * k.1ᵀ) i j).1 w)`. Introduce `i j`.

Rewrite using `[entry_mul, map_sum, mul_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Establish `key1 : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = ψ (((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w)`.

Introduce `i j`. Rewrite using `[entry_one, one_apply, one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h1 : Reduction.infAt w (gl k) ∈ Reduction.archCompact w ↔ ∀ z : Fin 2 → ℝ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z`. Rewrite using `[Reduction.mem_archCompact]`.

Prove the components needed by the constructor for the conclusion. Introduce `h z`. Establish `hz : z = fun i => ψ.toRingHom (ψ.symm (z i))` using `funext fun i => (ψ.apply_symm_apply _).symm`. Rewrite using `[hz, ← e, Reduction.euclidNorm_map _ hψ, Reduction.euclidNorm_map _ hψ, h]`. Introduce `h z`.

Rewrite using `[← Reduction.euclidNorm_map _ hψ, e, h, Reduction.euclidNorm_map _ hψ]`. Rewrite using `[h1, real_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Apply `ψ.injective` to reduce the goal to its premises.

Rewrite using `[← key, ← key1, h]`. Introduce `h`. Use extensionality with `i j`. Rewrite using `[key, key1, h i j]`.
-/
private theorem place_iff {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (k : G1 F) (w : InfinitePlace F) :
    Reduction.infAt w (gl k) ∈ Reduction.archCompact w ↔
      ∀ i j, ((k.1 * k.1ᵀ) i j).1 w = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w := by
  set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) with hψdef
  have hψ : ∀ z, ‖ψ.toRingHom z‖ = ‖z‖ := fun z =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero
      (map_zero _) z
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => ψ ((k i j).1 w)
  have e : ∀ z : Fin 2 → w.Completion,
      (fun j => ψ.toRingHom ((z ᵥ* (Reduction.infAt w (gl k) : Matrix (Fin 2) (Fin 2) w.Completion)) j)) =
        (fun i => ψ.toRingHom (z i)) ᵥ* M := by
    intro z
    ext j
    simp only [vecMul, dotProduct, map_sum, map_mul]
    rfl
  have key : ∀ i j, (M * Mᵀ) i j = ψ (((k.1 * k.1ᵀ) i j).1 w) := by
    intro i j
    rw [entry_mul, map_sum, mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  have key1 : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = ψ (((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 w) := by
    intro i j
    rw [entry_one, one_apply, one_apply]
    split_ifs <;> simp
  have h1 : Reduction.infAt w (gl k) ∈ Reduction.archCompact w ↔
      ∀ z : Fin 2 → ℝ, Reduction.euclidNorm (z ᵥ* M) = Reduction.euclidNorm z := by
    rw [Reduction.mem_archCompact]
    constructor
    · intro h z
      have hz : z = fun i => ψ.toRingHom (ψ.symm (z i)) := funext fun i => (ψ.apply_symm_apply _).symm
      rw [hz, ← e, Reduction.euclidNorm_map _ hψ, Reduction.euclidNorm_map _ hψ, h]
    · intro h z
      rw [← Reduction.euclidNorm_map _ hψ, e, h, Reduction.euclidNorm_map _ hψ]
  rw [h1, real_iff]
  constructor
  · intro h i j
    apply ψ.injective
    rw [← key, ← key1, h]
  · intro h
    ext i j
    rw [key, key1, h i j]

/- English proof (translation)
Introduce `F _ _ _ k`. Simplify using `only [place_iff, InfOrth]`. Conclude with `⟨fun h w i j => congrFun (h i j) w, fun h i j => funext fun w => h w i j⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.kkInf :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ k : G1 F, InfOrth k ↔ ∀ w, Reduction.infAt w (gl k) ∈ Reduction.archCompact w := by
  intro F _ _ _ k
  simp only [place_iff, InfOrth]
  exact ⟨fun h w i j => congrFun (h i j) w, fun h i j => funext fun w => h w i j⟩

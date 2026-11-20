import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LatFill
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]`. Consider the case `tmul b x`. Rewrite using `[TensorProduct.smul_tmul']`.

Express the relevant statement in the definitionally equal form `splitProj τ (compFin F E v ((a • b) ⊗ₜ[F] x)) = evFin F v a * splitProj τ (compFin F E v (b ⊗ₜ[F] x))`. Simplify using `[compFin, mul_assoc]`.
-/
theorem piW_smul {v : Pl F} (τ : E →ₐ[F] Fv F v) (a : AF F) (z : AE F E) :
    piW τ (a • z) = evFin F v a * piW τ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]
  | tmul b x =>
    rw [TensorProduct.smul_tmul']
    change splitProj τ (compFin F E v ((a • b) ⊗ₜ[F] x)) = evFin F v a * splitProj τ (compFin F E v (b ⊗ₜ[F] x))
    simp [compFin, mul_assoc]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x`. Simplify using `[compFin]`.
-/
theorem piW_inclR {v : Pl F} (τ : E →ₐ[F] Fv F v) (x : E) : piW τ (inclR (F := F) (AF F) x) = τ x := by
  change splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x
  simp [compFin]

variable {n d : ℕ}

def fillSet (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) :
    AddSubgroup (Matrix (Fin n) (Fin d) (Fv F v)) where
  carrier := {M | ∃ γ ∈ latAtV X W v, (∀ i j, piW (t.comp σ) (γ i j) = 0) ∧ ∀ i j, piW t (γ i j) = M i j}
  zero_mem' := ⟨0, zero_mem _, fun _ _ => by simp, fun _ _ => by simp⟩
  add_mem' := by
    rintro _ _ ⟨γ, hγ, h1, h2⟩ ⟨γ', hγ', h1', h2'⟩
    exact ⟨γ + γ', add_mem hγ hγ', fun i j => by simp [h1, h1'], fun i j => by simp [h2, h2']⟩
  neg_mem' := by
    rintro _ ⟨γ, hγ, h1, h2⟩
    exact ⟨-γ, neg_mem hγ, fun i j => by simp [h1], fun i j => by simp [h2]⟩

variable {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d} {v : Pl F} {t : E →ₐ[F] Fv F v}

/- English proof (translation)
Take `⟨γ, hγ, h1, h2⟩` from `hM`. Use `⟨GlobalTheory.LatVac.liftV v a • γ, (GlobalTheory.LatVac.latAtV_at_stable X W v).2 a ha γ hγ, fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, piW_smul, h1, mul_zero]`. Rewrite using `[Matrix.smul_apply, piW_smul, h2, GlobalTheory.LatVac.evFin_liftV, Matrix.smul_apply, smul_eq_mul]`.
-/
theorem smul_mem_fillSet {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) {M : Matrix (Fin n) (Fin d) (Fv F v)}
    (hM : M ∈ fillSet σ X W v t) : a • M ∈ fillSet σ X W v t := by
  obtain ⟨γ, hγ, h1, h2⟩ := hM
  refine ⟨GlobalTheory.LatVac.liftV v a • γ, (GlobalTheory.LatVac.latAtV_at_stable X W v).2 a ha γ hγ, fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.smul_apply, piW_smul, h1, mul_zero]
  · rw [Matrix.smul_apply, piW_smul, h2, GlobalTheory.LatVac.evFin_liftV, Matrix.smul_apply, smul_eq_mul]

/- English proof (translation)
Establish `key : ∀ e ∈ intLoc F E v, ∃ γ ∈ latAtV X W v, (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧ ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j))`. Introduce `e he`. Use `intLoc_induction (p := fun e => ∃ γ ∈ latAtV X W v, (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧ ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j))) (fun a ha o => ?_) ⟨0, zero_mem _, fun _ _ => by simp, fun _ _ => b …` and prove the remaining obligations. Establish `ho : algebraMap (𝓞 E) E o = (o : E)` using `rfl`. Use `⟨GlobalTheory.LatVac.liftV v a • incM F (Matrix.vecMulVec (o • x) x'), AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, _, X.L.smul_mem o hx, x', hx', rfl⟩, fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV, Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]`. Rewrite using `[Algebra.smul_def, map_mul, ho]`. Simplify using `only [AlgHom.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV, Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]`.

Rewrite using `[Algebra.smul_def, map_mul, ho]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `y z ⟨γ, hγ, h1, h2⟩ ⟨γ', hγ', h1', h2'⟩`. Conclude with `⟨γ + γ', add_mem hγ hγ', fun i j => by simp [h1, h1', add_mul], fun i j => by simp [h2, h2', add_mul]⟩`. Introduce and unpack `y ⟨γ, hγ, h1, h2⟩`.

Conclude with `⟨-γ, neg_mem hγ, fun i j => by simp [h1], fun i j => by simp [h2]⟩`. Take `⟨γ, hγ, h1, h2⟩` from `key _ (splitIdem_mem h t)`. Conclude with `⟨γ, hγ, fun i j => by simp [h1], fun i j => by simp [h2, Matrix.vecMulVec_apply]⟩`.
-/
theorem gen_mem_fillSet (h : IsCMExt F E σ) {x : Fin n → E} (hx : x ∈ X.L) {x' : Fin d → E} (hx' : x' ∈ W.L) :
    Matrix.vecMulVec (fun i => t (x i)) (fun j => t (x' j)) ∈ fillSet σ X W v t := by
  have key : ∀ e ∈ intLoc F E v, ∃ γ ∈ latAtV X W v,
      (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧
      ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j)) := by
    intro e he
    refine intLoc_induction (p := fun e => ∃ γ ∈ latAtV X W v,
      (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧
      ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j))) (fun a ha o => ?_) ⟨0, zero_mem _, fun _ _ => by simp, fun _ _ => by simp⟩ ?_ ?_ he
    · have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
      refine ⟨GlobalTheory.LatVac.liftV v a • incM F (Matrix.vecMulVec (o • x) x'),
        AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha,
          _, X.L.smul_mem o hx, x', hx', rfl⟩, fun i j => ?_, fun i j => ?_⟩
      · simp only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV,
          Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]
        rw [Algebra.smul_def, map_mul, ho]
        simp only [AlgHom.comp_apply]
        ring
      · simp only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV,
          Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]
        rw [Algebra.smul_def, map_mul, ho]
        ring
    · rintro y z ⟨γ, hγ, h1, h2⟩ ⟨γ', hγ', h1', h2'⟩
      exact ⟨γ + γ', add_mem hγ hγ', fun i j => by simp [h1, h1', add_mul],
        fun i j => by simp [h2, h2', add_mul]⟩
    · rintro y ⟨γ, hγ, h1, h2⟩
      exact ⟨-γ, neg_mem hγ, fun i j => by simp [h1], fun i j => by simp [h2]⟩
  obtain ⟨γ, hγ, h1, h2⟩ := key _ (splitIdem_mem h t)
  exact ⟨γ, hγ, fun i j => by simp [h1], fun i j => by simp [h2, Matrix.vecMulVec_apply]⟩

/- English proof (translation)
Use `latLoc_induction (p := fun y => Matrix.vecMulVec (splitVec t y) (splitVec t y') ∈ fillSet σ X W v t) (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy` and prove the remaining obligations. Use `latLoc_induction (p := fun y' => Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t y') ∈ fillSet σ X W v t) (fun a' ha' x' hx' => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy'` and prove the remaining obligations. Establish `e : Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t fun j => a' ⊗ₜ[F] x' j) = (a * a') • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (x' j))`. Use extensionality with `i j`. Simplify using `[splitVec, Matrix.vecMulVec_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `smul_mem_fillSet (mul_mem ha ha') (gen_mem_fillSet h hx hx')`. Use `zero_mem (fillSet σ X W v t) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`.

Simplify using `[splitVec, Matrix.vecMulVec_apply]`. Use `add_mem hy hz using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `[splitVec, Matrix.vecMulVec_apply, mul_add]`. Use `neg_mem hy using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i j`. Simplify using `[splitVec, Matrix.vecMulVec_apply]`. Use `zero_mem (fillSet σ X W v t) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `[splitVec, Matrix.vecMulVec_apply]`.

Use `add_mem hy hz using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `[splitVec, Matrix.vecMulVec_apply, add_mul]`. Use `neg_mem hy using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`.

Simplify using `[splitVec, Matrix.vecMulVec_apply]`.
-/
theorem vecMulVec_mem_fillSet (h : IsCMExt F E σ) {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc F X.L v)
    {y' : Fin d → Fv F v ⊗[F] E} (hy' : y' ∈ latLoc F W.L v) :
    Matrix.vecMulVec (splitVec t y) (splitVec t y') ∈ fillSet σ X W v t := by
  refine latLoc_induction (p := fun y => Matrix.vecMulVec (splitVec t y) (splitVec t y') ∈ fillSet σ X W v t)
    (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · refine latLoc_induction (p := fun y' => Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t y') ∈
      fillSet σ X W v t) (fun a' ha' x' hx' => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy'
    · have e : Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t fun j => a' ⊗ₜ[F] x' j) =
          (a * a') • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (x' j)) := by
        ext i j; simp [splitVec, Matrix.vecMulVec_apply]; ring
      rw [e]
      exact smul_mem_fillSet (mul_mem ha ha') (gen_mem_fillSet h hx hx')
    · convert zero_mem (fillSet σ X W v t) using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply]
    · convert add_mem hy hz using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply, mul_add]
    · convert neg_mem hy using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply]
  · convert zero_mem (fillSet σ X W v t) using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply]
  · convert add_mem hy hz using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply, add_mul]
  · convert neg_mem hy using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply]

/- English proof (translation)
Use extensionality with `k l`. Simplify using `only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec_single_one, Matrix.transpose_apply, Matrix.col_apply, smul_eq_mul, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_mul_transpose_eq_sum {K : Type} [Field K] (b : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin d) (Fin d) K)
    (A : Matrix (Fin n) (Fin d) K) :
    b * A * cᵀ = ∑ i, ∑ j, A i j • Matrix.vecMulVec (b *ᵥ Pi.single i 1) (c *ᵥ Pi.single j 1) := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec_single_one,
    Matrix.transpose_apply, Matrix.col_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.LatFill

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d h X W v t b c hb hc A hA`. Establish `single_mem : ∀ {m : ℕ} (i : Fin m) (k : Fin m), (Pi.single i (1 : Fv F v) : Fin m → Fv F v) k ∈ v.adicCompletionIntegers F` using `fun i k => by`. Distinguish the cases in `e : k = i`. Substitute `e` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[e]`. Establish `hT : b.1 * A * c.1ᵀ ∈ GlobalTheory.LatFill.fillSet σ X W v t`. Rewrite using `[GlobalTheory.LatFill.mul_mul_transpose_eq_sum]`. Use `sum_mem fun i _ => sum_mem fun j _ => GlobalTheory.LatFill.smul_mem_fillSet (hA i j) ?_` and prove the remaining obligations. Take `⟨y, hy, ey⟩` from `(hb _).1 (single_mem i)`.

Take `⟨y', hy', ey'⟩` from `(hc _).1 (single_mem j)`. Rewrite using `[← ey, ← ey']`. Conclude with `GlobalTheory.LatFill.vecMulVec_mem_fillSet h hy hy'`. Take `⟨γ, hγ, h1, h2⟩` from `hT`. Use `⟨γ, hγ, Matrix.ext fun i j => h1 i j, ?_⟩` and prove the remaining obligations.

Establish `e : γ.map (piW t) = b.1 * A * c.1ᵀ` using `Matrix.ext fun i j => h2 i j`. Rewrite using `[e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.mul_one]`.
-/
theorem GlobalTheory.LatFill.exists_latAtV_coord : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∀ A : Matrix (Fin n) (Fin d) (Fv F v), (∀ i j, A i j ∈ v.adicCompletionIntegers F) →
      ∃ γ ∈ latAtV X W v, γ.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ = A := by
  intro F E _ _ _ _ _ σ n d h X W v t b c hb hc A hA
  have single_mem : ∀ {m : ℕ} (i : Fin m) (k : Fin m),
      (Pi.single i (1 : Fv F v) : Fin m → Fv F v) k ∈ v.adicCompletionIntegers F := fun i k => by
    by_cases e : k = i
    · subst e; simp
    · simp [e]
  have hT : b.1 * A * c.1ᵀ ∈ GlobalTheory.LatFill.fillSet σ X W v t := by
    rw [GlobalTheory.LatFill.mul_mul_transpose_eq_sum]
    refine sum_mem fun i _ => sum_mem fun j _ => GlobalTheory.LatFill.smul_mem_fillSet (hA i j) ?_
    obtain ⟨y, hy, ey⟩ := (hb _).1 (single_mem i)
    obtain ⟨y', hy', ey'⟩ := (hc _).1 (single_mem j)
    rw [← ey, ← ey']
    exact GlobalTheory.LatFill.vecMulVec_mem_fillSet h hy hy'
  obtain ⟨γ, hγ, h1, h2⟩ := hT
  refine ⟨γ, hγ, Matrix.ext fun i j => h1 i j, ?_⟩
  have e : γ.map (piW t) = b.1 * A * c.1ᵀ := Matrix.ext fun i j => h2 i j
  rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.mul_one]

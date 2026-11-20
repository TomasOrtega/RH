import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IrrSplitSub

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show (x.1 : Matrix (Fin n) (Fin n) (AL L)) * y.1 = (y.1 : Matrix (Fin n) (Fin n) (AL L)) * x.1`. Use extensionality with `i j`. Rewrite using `[← sub_eq_zero]`.

Apply `GlobalTheory.InertUmax.eq_zero_of_compAt L` to reduce the goal to its premises. Introduce `w`. Rewrite using `[map_sub, sub_eq_zero]`. Establish `hmx : ∀ A B : Matrix (Fin n) (Fin n) (AL L), compAt L w ((A * B) i j) = (A.map (compAt L w) * B.map (compAt L w)) i j`. Introduce `A B`.

Rewrite using `[← Matrix.map_mul]`. Both sides reduce to the same expression. Rewrite using `[hmx, hmx]`. Distinguish the cases in `hw : w = s.v`. Rewrite using `[hy w (by simp [hw]), mul_one, one_mul]`.

Rewrite using `[hx w (by simpa using hw), mul_one, one_mul]`.
-/
theorem commute_of_trivOutside (s : SplitPlace L) {x y : GAf L n} (hx : TrivOutside {s.v} x)
    (hy : TrivOutside {s.v}ᶜ y) : x * y = y * x := by
  apply Subtype.ext; apply Units.ext
  show (x.1 : Matrix (Fin n) (Fin n) (AL L)) * y.1 = (y.1 : Matrix (Fin n) (Fin n) (AL L)) * x.1
  ext i j
  rw [← sub_eq_zero]
  apply GlobalTheory.InertUmax.eq_zero_of_compAt L
  intro w
  rw [map_sub, sub_eq_zero]
  have hmx : ∀ A B : Matrix (Fin n) (Fin n) (AL L),
      compAt L w ((A * B) i j) = (A.map (compAt L w) * B.map (compAt L w)) i j := by
    intro A B; rw [← Matrix.map_mul]; rfl
  rw [hmx, hmx]
  by_cases hw : w = s.v
  · rw [hy w (by simp [hw]), mul_one, one_mul]
  · rw [hx w (by simpa using hw), mul_one, one_mul]

/- English proof (translation)
Use `⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hk.1) ha, ?_⟩` and prove the remaining obligations. Use `choose Y hY hYe using hk.2`. Set `Ym : Matrix (Fin n) (Fin n) (AL L)` to `Matrix.of Y`. Establish `hint : ∀ A B : Matrix (Fin n) (Fin n) (AL L), (∀ i j, A i j ∈ ALint L) → (∀ i j, B i j ∈ ALint L) → ∀ i j, (A * B) i j ∈ ALint L` using `fun A B hA hB i j => by`. Rewrite using `[Matrix.mul_apply]`.

Conclude with `Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)`. Establish `haI : ∀ i j, ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L` using `ha`. Establish `haiI : ∀ i j, (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L` using `Subgroup.inv_mem _ ha`. Establish `hAiA : (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1`. Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]`.

Both sides reduce to the same expression. Establish `hK : ((k.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) - 1 = (N : AL L) • Ym`. Use extensionality with `i j`. Simplify using `[Ym, hYe i j]`. Establish `hmat : (((a⁻¹ * k * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) - 1 = (N : AL L) • ((((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * Ym * ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)))`.

Establish `e : (((a⁻¹ * k * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * ((k.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))` using `rfl`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul]`. Use `_ = _ := by rw [hK, Matrix.mul_smul, Matrix.smul_mul]`.

Introduce `i j`. Use `⟨_, hint _ _ (hint _ _ haiI (fun i j => hY i j)) haI i j, ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun hmat i) j` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `this`.
-/
theorem cong_conj {N : ℕ} {a k : GAf L n} (ha : a ∈ Umax L n) (hk : NG.Cong L n N k) :
    NG.Cong L n N (a⁻¹ * k * a) := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hk.1) ha, ?_⟩
  choose Y hY hYe using hk.2
  let Ym : Matrix (Fin n) (Fin n) (AL L) := Matrix.of Y
  have hint : ∀ A B : Matrix (Fin n) (Fin n) (AL L), (∀ i j, A i j ∈ ALint L) → (∀ i j, B i j ∈ ALint L) →
      ∀ i j, (A * B) i j ∈ ALint L := fun A B hA hB i j => by
    rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)
  have haI : ∀ i j, ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := ha
  have haiI : ∀ i j, (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L :=
    Subgroup.inv_mem _ ha
  have hAiA : (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hK : ((k.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) - 1 = (N : AL L) • Ym := by
    ext i j; simp [Ym, hYe i j]
  have hmat : (((a⁻¹ * k * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) - 1 =
      (N : AL L) • ((((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * Ym *
        ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
    have e : (((a⁻¹ * k * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          ((k.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := rfl
    rw [e]
    calc _ = (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          ((k.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) -
          (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * 1 *
          ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := by rw [Matrix.mul_one, hAiA]
      _ = (((a⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          (((k.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) - 1) *
          ((a.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = _ := by rw [hK, Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  refine ⟨_, hint _ _ (hint _ _ haiI (fun i j => hY i j)) haI i j, ?_⟩
  have := congrFun (congrFun hmat i) j
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
  exact this

/- English proof (translation)
Use `set e : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L s.v 1 with he_def`. Establish `hsgl : GlobalTheory.InertUmax.sgl L s.v 1 * GlobalTheory.InertUmax.sgl L s.v 1 = GlobalTheory.InertUmax.sgl L s.v 1`. Use `RestrictedProduct.ext _ _ fun w => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `GlobalTheory.InertUmax.sgl L s.v 1 w * GlobalTheory.InertUmax.sgl L s.v 1 w = GlobalTheory.InertUmax.sgl L s.v 1 w`. Break down `eq_or_ne w s.v with rfl | hw` into its components or cases.

Simplify using `only [GlobalTheory.InertUmax.sgl_same, mul_one]`. Simplify using `only [GlobalTheory.InertUmax.sgl_ne L _ _ hw, mul_zero]`. Establish `he2 : e * e = e` using `by rw [he_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hsgl]`. Establish `hce : conjAL L e = e` using `by simp [he_def, conjAL, Algebra.TensorProduct.map_tmul]`. Establish `heI : e ∈ ALint L` using `GlobalTheory.InertUmax.one_tmul_sgl_mem L s.v 1 (one_mem _)`.

Establish `hcv : compAt L s.v e = 1`. Rewrite using `[he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]`. Both sides reduce to the same expression. Establish `hcw : ∀ w, w ≠ s.v → compAt L w e = 0` using `fun w hw => by`. Rewrite using `[he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L _ _ hw, TensorProduct.tmul_zero]`.

Set `θ : AL L × AL L →+* AL L` to `{ toFun := fun q => e * q.1 + (1 - e) * q.2 map_one' := by simp only [Prod.fst_one, Prod.snd_one]; ring map_mul' := fun q q' => by`. Simplify using `only [Prod.fst_mul, Prod.snd_mul]`. Take the linear combination `(-(q.1 * q'.1 - q.1 * q'.2 - q.2 * q'.1 + q.2 * q'.2)) * he2`. Use the proof step `map_zero' := by simp`. Use the proof step `map_add' := fun q q' => by simp only [Prod.fst_add, Prod.snd_add]; ring }`.

Establish `hθ : ∀ q, θ q = e * q.1 + (1 - e) * q.2` using `fun _ => rfl`. Establish `hθc : ∀ a b, conjAL L (θ (a, b)) = θ (conjAL L a, conjAL L b)`. Introduce `a b`. Rewrite using `[hθ, hθ, map_add, map_mul, map_mul, map_sub, map_one, hce]`. Establish `hθv : ∀ q, compAt L s.v (θ q) = compAt L s.v q.1`.

Introduce `q`. Rewrite using `[hθ, map_add, map_mul, map_mul, map_sub, map_one, hcv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hθw : ∀ w, w ≠ s.v → ∀ q, compAt L w (θ q) = compAt L w q.2`. Introduce `w hw q`.

Rewrite using `[hθ, map_add, map_mul, map_mul, map_sub, map_one, hcw w hw]`. Expand and normalize the polynomial expressions, which then agree. Set `pr : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L × AL L)` to `fun A B i j => (A i j, B i j)`. Establish `pr_mul : ∀ A B C D, pr A B * pr C D = pr (A * C) (B * D)`. Introduce `A B C D`.

Use extensionality with `i j`. Use `show (∑ l, pr A B i l * pr C D l j).1 = ∑ l, A i l * C l j`. Rewrite using `[Prod.fst_sum]`. Both sides reduce to the same expression. Use `show (∑ l, pr A B i l * pr C D l j).2 = ∑ l, B i l * D l j`.

Rewrite using `[Prod.snd_sum]`. Both sides reduce to the same expression. Establish `pr_one : pr 1 1 = 1`. Apply the tactic sequence `ext i j <;> by_cases h : i = j <;> simp [pr, Matrix.one_apply, h]`. Set `M : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L)` to `fun A B => (pr A B).map θ`.

Establish `hM : ∀ A B i j, M A B i j = e * A i j + (1 - e) * B i j` using `fun _ _ _ _ => rfl`. Establish `M_mul : ∀ A B C D, M A B * M C D = M (A * C) (B * D)`. Introduce `A B C D`. Use `show (pr A B).map θ * (pr C D).map θ = (pr (A * C) (B * D)).map θ`. Rewrite using `[← Matrix.map_mul, pr_mul]`.

Establish `M_one : M 1 1 = 1` using `by show (pr 1 1).map θ = 1`. Rewrite using `[pr_one, Matrix.map_one _ (map_zero θ) (map_one θ)]`. Establish `M_conj : ∀ A B, conjT (conjAL L) (M A B) = M (conjT (conjAL L) A) (conjT (conjAL L) B)`. Introduce `A B`. Use extensionality with `i j`.

Use `show conjAL L (θ (A j i, B j i)) = θ (conjAL L (A j i), conjAL L (B j i))`. Conclude with `hθc _ _`. Establish `M_diag : ∀ A, M A A = A` using `by intro A; ext i j; rw [hM]; ring`. Use `set K : Matrix (Fin n) (Fin n) (AL L) := ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hK`. Establish `hKK : K * conjT (conjAL L) K = 1` using `κ.2`.

Establish `hKI : ∀ i j, K i j ∈ ALint L` using `hκ.1`. Establish `h1I : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L`. Introduce `i j`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Establish `hX : M K 1 * conjT (conjAL L) (M K 1) = 1`. Rewrite using `[M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]`. Establish `hY : M 1 K * conjT (conjAL L) (M 1 K) = 1`.

Rewrite using `[M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]`. Set `gX : GL (Fin n) (AL L)` to `⟨M K 1, conjT (conjAL L) (M K 1), hX, mul_eq_one_comm.mp hX⟩`. Set `gY : GL (Fin n) (AL L)` to `⟨M 1 K, conjT (conjAL L) (M 1 K), hY, mul_eq_one_comm.mp hY⟩`. Establish `hc1 : ∀ w i j, compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j`. Apply the tactic sequence `intro w i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`.

Use `⟨⟨gX, hX⟩, ⟨gY, hY⟩, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Establish `hw' : w ≠ s.v` using `hw`. Use extensionality with `i j`. Use `show compAt L w (θ (K i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) = _`.

Rewrite using `[hθw w hw', hc1]`. Use `show M K 1 i j ∈ ALint L`. Rewrite using `[hM]`. Conclude with `add_mem (mul_mem heI (hKI i j)) (mul_mem (sub_mem (one_mem _) heI) (h1I i j))`. Take `⟨y, hy, hye⟩` from `hκ.2 i j`.

Use `⟨e * y, mul_mem heI hy, ?_⟩` and prove the remaining obligations. Use `show M K 1 i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j = _`. Rewrite using `[hM]`. Take the linear combination `e * hye`. Introduce `w hw`.

Establish `hw' : w = s.v` using `by simpa using hw`. Substitute `hw'` using the available equality. Use extensionality with `i j`. Use `show compAt L s.v (θ ((1 : Matrix (Fin n) (Fin n) (AL L)) i j, K i j)) = _`. Rewrite using `[hθv, hc1]`.

Use `show M 1 K i j ∈ ALint L`. Rewrite using `[hM]`. Conclude with `add_mem (mul_mem heI (h1I i j)) (mul_mem (sub_mem (one_mem _) heI) (hKI i j))`. Take `⟨y, hy, hye⟩` from `hκ.2 i j`. Use `⟨(1 - e) * y, mul_mem (sub_mem (one_mem _) heI) hy, ?_⟩` and prove the remaining obligations.

Use `show M 1 K i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j = _`. Rewrite using `[hM]`. Take the linear combination `(1 - e) * hye`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext show K = M K 1 * M 1 K` to reduce the goal to its premises.

Rewrite using `[M_mul, Matrix.mul_one, Matrix.one_mul, M_diag]`.
-/
theorem cong_factor (s : SplitPlace L) (N : ℕ) (κ : GAf L n) (hκ : NG.Cong L n N κ) :
    ∃ x y : GAf L n, TrivOutside {s.v} x ∧ NG.Cong L n N x ∧ TrivOutside {s.v}ᶜ y ∧ NG.Cong L n N y ∧
      κ = x * y := by
  classical
  set e : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L s.v 1 with he_def
  have hsgl : GlobalTheory.InertUmax.sgl L s.v 1 * GlobalTheory.InertUmax.sgl L s.v 1 = GlobalTheory.InertUmax.sgl L s.v 1 := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    change GlobalTheory.InertUmax.sgl L s.v 1 w * GlobalTheory.InertUmax.sgl L s.v 1 w = GlobalTheory.InertUmax.sgl L s.v 1 w
    rcases eq_or_ne w s.v with rfl | hw
    · simp only [GlobalTheory.InertUmax.sgl_same, mul_one]
    · simp only [GlobalTheory.InertUmax.sgl_ne L _ _ hw, mul_zero]
  have he2 : e * e = e := by rw [he_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hsgl]
  have hce : conjAL L e = e := by simp [he_def, conjAL, Algebra.TensorProduct.map_tmul]
  have heI : e ∈ ALint L := GlobalTheory.InertUmax.one_tmul_sgl_mem L s.v 1 (one_mem _)
  have hcv : compAt L s.v e = 1 := by
    rw [he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]; rfl
  have hcw : ∀ w, w ≠ s.v → compAt L w e = 0 := fun w hw => by
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
  have hθv : ∀ q, compAt L s.v (θ q) = compAt L s.v q.1 := by
    intro q; rw [hθ, map_add, map_mul, map_mul, map_sub, map_one, hcv]; ring
  have hθw : ∀ w, w ≠ s.v → ∀ q, compAt L w (θ q) = compAt L w q.2 := by
    intro w hw q; rw [hθ, map_add, map_mul, map_mul, map_sub, map_one, hcw w hw]; ring
  let pr : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L × AL L) :=
    fun A B i j => (A i j, B i j)
  have pr_mul : ∀ A B C D, pr A B * pr C D = pr (A * C) (B * D) := by
    intro A B C D; ext i j
    · show (∑ l, pr A B i l * pr C D l j).1 = ∑ l, A i l * C l j
      rw [Prod.fst_sum]; rfl
    · show (∑ l, pr A B i l * pr C D l j).2 = ∑ l, B i l * D l j
      rw [Prod.snd_sum]; rfl
  have pr_one : pr 1 1 = 1 := by
    ext i j <;> by_cases h : i = j <;> simp [pr, Matrix.one_apply, h]
  let M : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) :=
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
  set K : Matrix (Fin n) (Fin n) (AL L) := ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hK
  have hKK : K * conjT (conjAL L) K = 1 := κ.2
  have hKI : ∀ i j, K i j ∈ ALint L := hκ.1
  have h1I : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    intro i j; rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hX : M K 1 * conjT (conjAL L) (M K 1) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  have hY : M 1 K * conjT (conjAL L) (M 1 K) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  let gX : GL (Fin n) (AL L) := ⟨M K 1, conjT (conjAL L) (M K 1), hX, mul_eq_one_comm.mp hX⟩
  let gY : GL (Fin n) (AL L) := ⟨M 1 K, conjT (conjAL L) (M 1 K), hY, mul_eq_one_comm.mp hY⟩
  have hc1 : ∀ w i j, compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro w i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  refine ⟨⟨gX, hX⟩, ⟨gY, hY⟩, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, ?_, ⟨fun i j => ?_, fun i j => ?_⟩, ?_⟩
  · intro w hw
    have hw' : w ≠ s.v := hw
    ext i j
    show compAt L w (θ (K i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) = _
    rw [hθw w hw', hc1]
  · show M K 1 i j ∈ ALint L
    rw [hM]
    exact add_mem (mul_mem heI (hKI i j)) (mul_mem (sub_mem (one_mem _) heI) (h1I i j))
  · obtain ⟨y, hy, hye⟩ := hκ.2 i j
    refine ⟨e * y, mul_mem heI hy, ?_⟩
    show M K 1 i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j = _
    rw [hM]
    linear_combination e * hye
  · intro w hw
    have hw' : w = s.v := by simpa using hw
    subst hw'
    ext i j
    show compAt L s.v (θ ((1 : Matrix (Fin n) (Fin n) (AL L)) i j, K i j)) = _
    rw [hθv, hc1]
  · show M 1 K i j ∈ ALint L
    rw [hM]
    exact add_mem (mul_mem heI (h1I i j)) (mul_mem (sub_mem (one_mem _) heI) (hKI i j))
  · obtain ⟨y, hy, hye⟩ := hκ.2 i j
    refine ⟨(1 - e) * y, mul_mem (sub_mem (one_mem _) heI) hy, ?_⟩
    show M 1 K i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j = _
    rw [hM]
    linear_combination (1 - e) * hye
  · apply Subtype.ext; apply Units.ext
    show K = M K 1 * M 1 K
    rw [M_mul, Matrix.mul_one, Matrix.one_mul, M_diag]

end GlobalTheory.IrrSplitSub

open GlobalTheory.IrrSplitSub in

/- English proof (translation)
Introduce `L _ _ _ n π B hlin hherm hpos hinv hadm s`. Establish `rt_apply : ∀ (h : GAf L n) (f : GAf L n → ℂ) g, NG.rt L n h f g = f (g * h)` using `fun _ _ _ => rfl`. Establish `rt_mul : ∀ (a b : GAf L n) (f : GAf L n → ℂ), NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f)`. Introduce `a b f`. Use function extensionality and compare the values at `g`.

Rewrite using `[rt_apply, rt_apply, rt_apply, mul_assoc]`. Establish `rt_one : ∀ f : GAf L n → ℂ, NG.rt L n 1 f = f`. Introduce `f`. Use function extensionality and compare the values at `g`. Rewrite using `[rt_apply, mul_one]`.

Establish `rt_inv : ∀ (x : GAf L n) (f : GAf L n → ℂ), NG.rt L n x (NG.rt L n x⁻¹ f) = f`. Introduce `x f`. Rewrite using `[← rt_mul, mul_inv_cancel, rt_one]`. Establish `B0r : ∀ x, B x 0 = 0` using `fun x => by simpa using hlin x 0 0 1`. Establish `Badd : ∀ x y z, B x (y + z) = B x y + B x z` using `fun x y z => by simpa using hlin x y z 1`.

Establish `Bsmul : ∀ x (c : ℂ) z, B x (c • z) = c * B x z` using `fun x c z => by simpa [B0r] using hlin x 0 z c`. Establish `triv_one : TrivOutside {s.v} (1 : GAf L n)` using `fun w _ => by show (1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Set `Fix : (GAf L n → Prop) → Submodule ℂ (GAf L n → ℂ)` to `fun P => { carrier := {f | f ∈ π.S ∧ ∀ κ, P κ → NG.rt L n κ f = f} add_mem' := fun {a b} ha hb => ⟨π.S.add_mem ha.1 hb.1, fun κ hκ => by rw [map_add, ha.2 κ hκ, hb.2 κ hκ]⟩ zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩ smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ h …`. Establish `finFix : ∀ M, 0 < M → FiniteDimensional ℂ (Fix (NG.Cong L n M))`.

Introduce `M hM`. Establish `h` using `hadm M hM`. Establish `e : Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n M κ → NG.rt L n κ f = f} = Fix (NG.Cong L n M)` using `Submodule.span_eq (Fix (NG.Cong L n M))`. Rewrite `h` using `[e]`. Conclude with `h`.

Take `⟨f₀, hf₀S, hf₀ne⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot π.ne`. Take `⟨N, hN, hf₀N⟩` from `π.smooth f₀ hf₀S`. Set `VN` to `Fix (NG.Cong L n N)`. Use `haveI : FiniteDimensional ℂ VN := finFix N hN`. Set `W₀` to `Fix (fun y => NG.Cong L n N y ∧ TrivOutside {s.v}ᶜ y)`.

Set `Hst : Submodule ℂ (GAf L n → ℂ) → Prop` to `fun U => ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ U, NG.rt L n x f ∈ U`. Establish `W₀S : W₀ ≤ π.S` using `fun f hf => hf.1`. Establish `W₀st : Hst W₀`. Introduce `x hx f hf`. Use `⟨π.stable x f hf.1, fun y hy => ?_⟩` and prove the remaining obligations.

Rewrite using `[← rt_mul, ← commute_of_trivOutside s hx hy.2, rt_mul, hf.2 y hy]`. Set `𝒰 : Submodule ℂ (GAf L n → ℂ) → Prop` to `fun U => U ≤ W₀ ∧ Hst U ∧ U ⊓ VN ≠ ⊥`. Establish `hex : ∃ d, ∃ U, 𝒰 U ∧ Module.finrank ℂ ↥(U ⊓ VN) = d`. Use `⟨_, W₀, ⟨le_rfl, W₀st, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[Submodule.ne_bot_iff]`.

Conclude with `⟨f₀, ⟨⟨hf₀S, fun y hy => hf₀N y hy.1⟩, ⟨hf₀S, hf₀N⟩⟩, hf₀ne⟩`. Take `⟨U, hU, hUd⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ U', 𝒰 U' → Nat.find hex ≤ Module.finrank ℂ ↥(U' ⊓ VN)` using `fun U' hU' => Nat.find_min' hex ⟨U', hU', rfl⟩`. Set `X` to `U ⊓ VN`. Use `haveI : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le inf_le_right`.

Set `gen : Set (GAf L n → ℂ)` to `{g | ∃ x, TrivOutside {s.v} x ∧ ∃ f ∈ X, g = NG.rt L n x f}`. Set `Wsp` to `Submodule.span ℂ gen`. Establish `hWU : Wsp ≤ U` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨x, hx, f, hf, rfl⟩`. Conclude with `hU.2.1 x hx f hf.1)`.

Establish `hXW : X ≤ Wsp` using `fun f hf => Submodule.subset_span ⟨1, triv_one, f, hf, (rt_one f).symm⟩`. Establish `Wst : Hst Wsp`. Introduce `x hx f hf`. Establish `: Wsp ≤ Wsp.comap (NG.rt L n x)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, g, hg, rfl⟩`.

Conclude with `Submodule.subset_span ⟨x * y, GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy, g, hg, (rt_mul x y g).symm⟩)`. Conclude with `this hf`. Establish `hWS : Wsp ≤ π.S` using `hWU.trans (hU.1.trans W₀S)`. Use `⟨Wsp, hWS, ?_, Wst, ?_⟩` and prove the remaining obligations. Introduce `h`.

Conclude with `hU.2.2 (eq_bot_iff.2 (h ▸ hXW))`. Introduce `W' hW'le hW'st`. Distinguish the cases in `hV : W' ⊓ VN = ⊥`. Use `swap`. Use `right`.

Establish `h𝒰 : 𝒰 W'` using `⟨hW'le.trans (hWU.trans hU.1), hW'st, hV⟩`. Establish `hle : W' ⊓ VN ≤ X` using `inf_le_inf_right _ (hW'le.trans hWU)`. Establish `heq : W' ⊓ VN = X` using `Submodule.eq_of_le_of_finrank_le hle (by rw [hUd]; exact hmin W' h𝒰)`. Apply `le_antisymm hW'le` to reduce the goal to its premises. Apply `Submodule.span_le.2` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, hx, f, hf, rfl⟩`. Establish `hf' : f ∈ W' ⊓ VN` using `heq ▸ hf`. Conclude with `hW'st x hx f hf'.1`. Use `left`. Establish `hW'S : W' ≤ π.S` using `hW'le.trans hWS`.

Set `Bf : π.S →ₗ[ℂ] π.S →ₗ⋆[ℂ] ℂ` to `LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u v => B v u) (fun u₁ u₂ v => Badd v u₁ u₂) (fun c u v => Bsmul v c u) (fun u v₁ v₂ => by rw [hherm, Badd, map_add, ← hherm, ← hherm]) (fun c u v => by rw [hherm, Bsmul, map_mul, ← hherm]; rfl)`. Establish `hBf : ∀ u v, Bf u v = B v u` using `fun _ _ => rfl`. Establish `hBfpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re` using `fun v hv => by rw [hBf]; exact hpos v hv`. Establish `key : ∀ w' (hw' : w' ∈ π.S), w' ∈ W' → ∀ f (hf : f ∈ π.S), f ∈ X → B ⟨w', hw'⟩ ⟨f, hf⟩ = 0`. Introduce `w' hw'S hw'W' f hfS hfX`.

Take `⟨N₁, hN₁, hw'N₁⟩` from `π.smooth w' hw'S`. Set `F : Submodule ℂ π.S` to `(Fix (NG.Cong L n N₁)).comap π.S.subtype`. Use `haveI := finFix N₁ hN₁`. Use `haveI : FiniteDimensional ℂ F := by`. Set `φ : F →ₗ[ℂ] Fix (NG.Cong L n N₁)` to `LinearMap.codRestrict (Fix (NG.Cong L n N₁)) (π.S.subtype ∘ₗ F.subtype) (fun c => c.2)`.

Use `Module.Finite.of_injective φ ?_` and prove the remaining obligations. Introduce `a b h`. Establish `h'` using `congrArg Subtype.val h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `h'`. Set `E : Submodule ℂ π.S` to `F ⊓ W'.comap π.S.subtype`. Use `haveI : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left`. Establish `stabE : ∀ k : GAf L n, k ∈ Umax L n → TrivOutside {s.v} k → ∀ v ∈ E, (⟨NG.rt L n k v, π.stable k v v.2⟩ : π.S) ∈ E`. Introduce `k hkU hkT v hv`.

Use `⟨⟨π.stable k v v.2, fun κ hκ => ?_⟩, hW'st k hkT v hv.2⟩` and prove the remaining obligations. Establish `e : κ * k = k * (k⁻¹ * κ * k)` using `by group`. Use `show NG.rt L n κ (NG.rt L n k (v : GAf L n → ℂ)) = NG.rt L n k (v : GAf L n → ℂ)`. Establish `hfx : NG.rt L n (k⁻¹ * κ * k) (v : GAf L n → ℂ) = v` using `hv.1.2 _ (cong_conj hkU hκ)`. Rewrite using `[← rt_mul, e, rt_mul, hfx]`.

Take `⟨u, huE, hu⟩` from `GlobalTheory.SmoothRiesz.exists_mem_eq_on_of_finiteDimensional Bf hBfpos (Bf ⟨f, hfS⟩) E`. Establish `hfixH : ∀ k, NG.Cong L n N k → TrivOutside {s.v} k → NG.rt L n k (u : GAf L n → ℂ) = u`. Introduce `k hkC hkT`. Set `u' : π.S` to `⟨NG.rt L n k u, π.stable k u u.2⟩`. Establish `hu'E : u' ∈ E` using `stabE k hkC.1 hkT u huE`.

Establish `hsame : ∀ v ∈ E, Bf u' v = Bf u v`. Introduce `v hv`. Set `v' : π.S` to `⟨NG.rt L n k⁻¹ v, π.stable k⁻¹ v v.2⟩`. Establish `hv'E : v' ∈ E` using `stabE k⁻¹ (Subgroup.inv_mem _ hkC.1) (GlobalTheory.SatInd.CosetFin.trivOutside_inv hkT) v hv`. Establish `hkf : NG.rt L n k f = f` using `hfX.2.2 k hkC`.

Combine the equalities or inequalities in the displayed calculation. Establish `hd : u' - u = 0`. Assume the negation of the conclusion as `hne`. Establish `h1` using `hBfpos _ hne`. Establish `h2 : Bf (u' - u) (u' - u) = 0`.

Rewrite using `[show Bf (u' - u) = Bf u' - Bf u from map_sub Bf u' u, LinearMap.sub_apply, hsame _ (E.sub_mem hu'E huE), sub_self]`. Rewrite `h1` using `[h2]`. Simplify using `at h1`. Conclude with `congrArg Subtype.val (sub_eq_zero.1 hd)`. Establish `huW' : (u : GAf L n → ℂ) ∈ W'` using `huE.2`.

Establish `hfixK : ∀ κ, NG.Cong L n N κ → NG.rt L n κ (u : GAf L n → ℂ) = u`. Introduce `κ hκ`. Take `⟨x, y, hx, hxc, hy, hyc, rfl⟩` from `cong_factor s N κ hκ`. Establish `huW₀ : (u : GAf L n → ℂ) ∈ W₀` using `(hW'le.trans (hWU.trans hU.1)) huW'`. Rewrite using `[rt_mul, huW₀.2 y ⟨hyc, hy⟩, hfixH x hxc hx]`.

Establish `hu0 : u = 0`. Establish `hmem : (u : GAf L n → ℂ) ∈ W' ⊓ VN` using `⟨huW', ⟨u.2, hfixK⟩⟩`. Rewrite `hmem` using `[hV, Submodule.mem_bot]`. Conclude with `Subtype.ext hmem`. Establish `hw'E : (⟨w', hw'S⟩ : π.S) ∈ E` using `⟨⟨hw'S, fun κ hκ => hw'N₁ κ hκ⟩, hw'W'⟩`.

Use `hu _ hw'E` as an intermediate fact. Rewrite `this` using `[hBf, hBf, hu0]`. Rewrite using `[this]`. Conclude with `B0r _`. Set `Z : (w : GAf L n → ℂ) → w ∈ π.S → Submodule ℂ (GAf L n → ℂ)` to `fun w hw => { carrier := {g | ∃ hg : g ∈ π.S, B ⟨w, hw⟩ ⟨g, hg⟩ = 0} add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨π.S.add_mem ha hb, by`.

Use `Badd ⟨w, hw⟩ ⟨a, ha⟩ ⟨b, hb⟩` as an intermediate fact. Rewrite `this` using `[ha', hb', add_zero]`. Conclude with `this⟩`. Use the proof step `zero_mem' := ⟨π.S.zero_mem, B0r _⟩`. Use the proof step `smul_mem' := fun c a ⟨ha, ha'⟩ => ⟨π.S.smul_mem c ha, by`.

Use `Bsmul ⟨w, hw⟩ c ⟨a, ha⟩` as an intermediate fact. Rewrite `this` using `[ha', mul_zero]`. Conclude with `this⟩ }`. Rewrite using `[eq_bot_iff]`. Introduce `w hw`.

Rewrite using `[Submodule.mem_bot]`. Establish `hwS` using `hW'S hw`. Establish `hWZ : Wsp ≤ Z w hwS` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨x, hx, f, hf, rfl⟩`. Establish `hfS : f ∈ π.S` using `hf.2.1`.

Establish `hxw : NG.rt L n x⁻¹ w ∈ W'` using `hW'st x⁻¹ (GlobalTheory.SatInd.CosetFin.trivOutside_inv hx) w hw`. Use `⟨π.stable x f hfS, ?_⟩` and prove the remaining obligations. Rewrite using `[hinv x ⟨NG.rt L n x⁻¹ w, hW'S hxw⟩ ⟨f, hfS⟩ ⟨w, hwS⟩ _ (rt_inv x w).symm rfl]`. Conclude with `key _ _ hxw f hfS hf)`. Take `⟨_, hww⟩` from `hWZ (hW'le hw)`.

Assume the negation of the conclusion as `hne`. Use `hpos ⟨w, hwS⟩ (fun h => hne (congrArg Subtype.val h))` as an intermediate fact. Rewrite `this` using `[hww]`. Simplify using `at this`.
-/
theorem GlobalTheory.exists_irreducible_sub_trivOutside_split : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (B : π.S → π.S → ℂ), (∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z) → (∀ x y, B x y = starRingEnd ℂ (B y x)) → (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ h (x y x' y' : π.S), (x' : GAf L n → ℂ) = NG.rt L n h x → (y' : GAf L n → ℂ) = NG.rt L n h y → B x' y' = B x y) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f})) → ∀ s : SplitPlace L, ∃ W : Submodule ℂ (GAf L n → ℂ), W ≤ π.S ∧ W ≠ ⊥ ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W, NG.rt L n x f ∈ W) ∧ ∀ W' : Submodule ℂ (GAf L n → ℂ), W' ≤ W → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W', NG.rt L n x f ∈ W') → W' = ⊥ ∨ W' = W := by
  intro L _ _ _ n π B hlin hherm hpos hinv hadm s
  classical
  have rt_apply : ∀ (h : GAf L n) (f : GAf L n → ℂ) g, NG.rt L n h f g = f (g * h) := fun _ _ _ => rfl
  have rt_mul : ∀ (a b : GAf L n) (f : GAf L n → ℂ), NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f) := by
    intro a b f; funext g; rw [rt_apply, rt_apply, rt_apply, mul_assoc]
  have rt_one : ∀ f : GAf L n → ℂ, NG.rt L n 1 f = f := by
    intro f; funext g; rw [rt_apply, mul_one]
  have rt_inv : ∀ (x : GAf L n) (f : GAf L n → ℂ), NG.rt L n x (NG.rt L n x⁻¹ f) = f := by
    intro x f; rw [← rt_mul, mul_inv_cancel, rt_one]
  have B0r : ∀ x, B x 0 = 0 := fun x => by simpa using hlin x 0 0 1
  have Badd : ∀ x y z, B x (y + z) = B x y + B x z := fun x y z => by simpa using hlin x y z 1
  have Bsmul : ∀ x (c : ℂ) z, B x (c • z) = c * B x z := fun x c z => by simpa [B0r] using hlin x 0 z c
  have triv_one : TrivOutside {s.v} (1 : GAf L n) := fun w _ => by
    show (1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1
    exact Matrix.map_one _ (map_zero _) (map_one _)

  let Fix : (GAf L n → Prop) → Submodule ℂ (GAf L n → ℂ) := fun P =>
    { carrier := {f | f ∈ π.S ∧ ∀ κ, P κ → NG.rt L n κ f = f}
      add_mem' := fun {a b} ha hb => ⟨π.S.add_mem ha.1 hb.1, fun κ hκ => by rw [map_add, ha.2 κ hκ, hb.2 κ hκ]⟩
      zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩
      smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩ }
  have finFix : ∀ M, 0 < M → FiniteDimensional ℂ (Fix (NG.Cong L n M)) := by
    intro M hM
    have h := hadm M hM
    have e : Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n M κ → NG.rt L n κ f = f} =
        Fix (NG.Cong L n M) := Submodule.span_eq (Fix (NG.Cong L n M))
    rw [e] at h; exact h
  obtain ⟨f₀, hf₀S, hf₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne
  obtain ⟨N, hN, hf₀N⟩ := π.smooth f₀ hf₀S
  let VN := Fix (NG.Cong L n N)
  haveI : FiniteDimensional ℂ VN := finFix N hN
  let W₀ := Fix (fun y => NG.Cong L n N y ∧ TrivOutside {s.v}ᶜ y)
  let Hst : Submodule ℂ (GAf L n → ℂ) → Prop := fun U =>
    ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ U, NG.rt L n x f ∈ U
  have W₀S : W₀ ≤ π.S := fun f hf => hf.1
  have W₀st : Hst W₀ := by
    intro x hx f hf
    refine ⟨π.stable x f hf.1, fun y hy => ?_⟩
    rw [← rt_mul, ← commute_of_trivOutside s hx hy.2, rt_mul, hf.2 y hy]
  let 𝒰 : Submodule ℂ (GAf L n → ℂ) → Prop := fun U => U ≤ W₀ ∧ Hst U ∧ U ⊓ VN ≠ ⊥
  have hex : ∃ d, ∃ U, 𝒰 U ∧ Module.finrank ℂ ↥(U ⊓ VN) = d := by
    refine ⟨_, W₀, ⟨le_rfl, W₀st, ?_⟩, rfl⟩
    rw [Submodule.ne_bot_iff]
    exact ⟨f₀, ⟨⟨hf₀S, fun y hy => hf₀N y hy.1⟩, ⟨hf₀S, hf₀N⟩⟩, hf₀ne⟩
  obtain ⟨U, hU, hUd⟩ := Nat.find_spec hex
  have hmin : ∀ U', 𝒰 U' → Nat.find hex ≤ Module.finrank ℂ ↥(U' ⊓ VN) :=
    fun U' hU' => Nat.find_min' hex ⟨U', hU', rfl⟩
  let X := U ⊓ VN
  haveI : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le inf_le_right
  let gen : Set (GAf L n → ℂ) := {g | ∃ x, TrivOutside {s.v} x ∧ ∃ f ∈ X, g = NG.rt L n x f}
  let Wsp := Submodule.span ℂ gen
  have hWU : Wsp ≤ U := Submodule.span_le.2 (by
    rintro _ ⟨x, hx, f, hf, rfl⟩; exact hU.2.1 x hx f hf.1)
  have hXW : X ≤ Wsp := fun f hf => Submodule.subset_span ⟨1, triv_one, f, hf, (rt_one f).symm⟩
  have Wst : Hst Wsp := by
    intro x hx f hf
    have : Wsp ≤ Wsp.comap (NG.rt L n x) := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, g, hg, rfl⟩
      exact Submodule.subset_span ⟨x * y, GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy, g, hg, (rt_mul x y g).symm⟩)
    exact this hf
  have hWS : Wsp ≤ π.S := hWU.trans (hU.1.trans W₀S)
  refine ⟨Wsp, hWS, ?_, Wst, ?_⟩
  · intro h
    exact hU.2.2 (eq_bot_iff.2 (h ▸ hXW))
  intro W' hW'le hW'st
  by_cases hV : W' ⊓ VN = ⊥
  swap
  · right
    have h𝒰 : 𝒰 W' := ⟨hW'le.trans (hWU.trans hU.1), hW'st, hV⟩
    have hle : W' ⊓ VN ≤ X := inf_le_inf_right _ (hW'le.trans hWU)
    have heq : W' ⊓ VN = X := Submodule.eq_of_le_of_finrank_le hle (by rw [hUd]; exact hmin W' h𝒰)
    apply le_antisymm hW'le
    apply Submodule.span_le.2
    rintro _ ⟨x, hx, f, hf, rfl⟩
    have hf' : f ∈ W' ⊓ VN := heq ▸ hf
    exact hW'st x hx f hf'.1
  left
  have hW'S : W' ≤ π.S := hW'le.trans hWS

  let Bf : π.S →ₗ[ℂ] π.S →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u v => B v u)
    (fun u₁ u₂ v => Badd v u₁ u₂) (fun c u v => Bsmul v c u)
    (fun u v₁ v₂ => by rw [hherm, Badd, map_add, ← hherm, ← hherm])
    (fun c u v => by rw [hherm, Bsmul, map_mul, ← hherm]; rfl)
  have hBf : ∀ u v, Bf u v = B v u := fun _ _ => rfl
  have hBfpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re := fun v hv => by rw [hBf]; exact hpos v hv

  have key : ∀ w' (hw' : w' ∈ π.S), w' ∈ W' → ∀ f (hf : f ∈ π.S), f ∈ X → B ⟨w', hw'⟩ ⟨f, hf⟩ = 0 := by
    intro w' hw'S hw'W' f hfS hfX
    obtain ⟨N₁, hN₁, hw'N₁⟩ := π.smooth w' hw'S
    let F : Submodule ℂ π.S := (Fix (NG.Cong L n N₁)).comap π.S.subtype
    haveI := finFix N₁ hN₁
    haveI : FiniteDimensional ℂ F := by
      let φ : F →ₗ[ℂ] Fix (NG.Cong L n N₁) :=
        LinearMap.codRestrict (Fix (NG.Cong L n N₁)) (π.S.subtype ∘ₗ F.subtype) (fun c => c.2)
      refine Module.Finite.of_injective φ ?_
      intro a b h
      have h' := congrArg Subtype.val h
      apply Subtype.ext; apply Subtype.ext; exact h'
    let E : Submodule ℂ π.S := F ⊓ W'.comap π.S.subtype
    haveI : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
    have stabE : ∀ k : GAf L n, k ∈ Umax L n → TrivOutside {s.v} k → ∀ v ∈ E,
        (⟨NG.rt L n k v, π.stable k v v.2⟩ : π.S) ∈ E := by
      intro k hkU hkT v hv
      refine ⟨⟨π.stable k v v.2, fun κ hκ => ?_⟩, hW'st k hkT v hv.2⟩
      have e : κ * k = k * (k⁻¹ * κ * k) := by group
      show NG.rt L n κ (NG.rt L n k (v : GAf L n → ℂ)) = NG.rt L n k (v : GAf L n → ℂ)
      have hfx : NG.rt L n (k⁻¹ * κ * k) (v : GAf L n → ℂ) = v := hv.1.2 _ (cong_conj hkU hκ)
      rw [← rt_mul, e, rt_mul, hfx]
    obtain ⟨u, huE, hu⟩ := GlobalTheory.SmoothRiesz.exists_mem_eq_on_of_finiteDimensional Bf hBfpos (Bf ⟨f, hfS⟩) E
    have hfixH : ∀ k, NG.Cong L n N k → TrivOutside {s.v} k → NG.rt L n k (u : GAf L n → ℂ) = u := by
      intro k hkC hkT
      let u' : π.S := ⟨NG.rt L n k u, π.stable k u u.2⟩
      have hu'E : u' ∈ E := stabE k hkC.1 hkT u huE
      have hsame : ∀ v ∈ E, Bf u' v = Bf u v := by
        intro v hv
        let v' : π.S := ⟨NG.rt L n k⁻¹ v, π.stable k⁻¹ v v.2⟩
        have hv'E : v' ∈ E := stabE k⁻¹ (Subgroup.inv_mem _ hkC.1)
          (GlobalTheory.SatInd.CosetFin.trivOutside_inv hkT) v hv
        have hkf : NG.rt L n k f = f := hfX.2.2 k hkC
        calc Bf u' v = B v u' := rfl
          _ = B v' u := hinv k v' u v u' (rt_inv k v).symm rfl
          _ = B v' ⟨f, hfS⟩ := (hu v' hv'E).symm
          _ = B v ⟨f, hfS⟩ := (hinv k v' ⟨f, hfS⟩ v ⟨f, hfS⟩ (rt_inv k v).symm hkf.symm).symm
          _ = Bf u v := hu v hv
      have hd : u' - u = 0 := by
        by_contra hne
        have h1 := hBfpos _ hne
        have h2 : Bf (u' - u) (u' - u) = 0 := by
          rw [show Bf (u' - u) = Bf u' - Bf u from map_sub Bf u' u, LinearMap.sub_apply,
            hsame _ (E.sub_mem hu'E huE), sub_self]
        rw [h2] at h1; simp at h1
      exact congrArg Subtype.val (sub_eq_zero.1 hd)
    have huW' : (u : GAf L n → ℂ) ∈ W' := huE.2
    have hfixK : ∀ κ, NG.Cong L n N κ → NG.rt L n κ (u : GAf L n → ℂ) = u := by
      intro κ hκ
      obtain ⟨x, y, hx, hxc, hy, hyc, rfl⟩ := cong_factor s N κ hκ
      have huW₀ : (u : GAf L n → ℂ) ∈ W₀ := (hW'le.trans (hWU.trans hU.1)) huW'
      rw [rt_mul, huW₀.2 y ⟨hyc, hy⟩, hfixH x hxc hx]
    have hu0 : u = 0 := by
      have hmem : (u : GAf L n → ℂ) ∈ W' ⊓ VN := ⟨huW', ⟨u.2, hfixK⟩⟩
      rw [hV, Submodule.mem_bot] at hmem
      exact Subtype.ext hmem
    have hw'E : (⟨w', hw'S⟩ : π.S) ∈ E := ⟨⟨hw'S, fun κ hκ => hw'N₁ κ hκ⟩, hw'W'⟩
    have := hu _ hw'E
    rw [hBf, hBf, hu0] at this
    rw [this]
    exact B0r _

  let Z : (w : GAf L n → ℂ) → w ∈ π.S → Submodule ℂ (GAf L n → ℂ) := fun w hw =>
    { carrier := {g | ∃ hg : g ∈ π.S, B ⟨w, hw⟩ ⟨g, hg⟩ = 0}
      add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨π.S.add_mem ha hb, by
        have := Badd ⟨w, hw⟩ ⟨a, ha⟩ ⟨b, hb⟩; rw [ha', hb', add_zero] at this; exact this⟩
      zero_mem' := ⟨π.S.zero_mem, B0r _⟩
      smul_mem' := fun c a ⟨ha, ha'⟩ => ⟨π.S.smul_mem c ha, by
        have := Bsmul ⟨w, hw⟩ c ⟨a, ha⟩; rw [ha', mul_zero] at this; exact this⟩ }
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  have hwS := hW'S hw
  have hWZ : Wsp ≤ Z w hwS := Submodule.span_le.2 (by
    rintro _ ⟨x, hx, f, hf, rfl⟩
    have hfS : f ∈ π.S := hf.2.1
    have hxw : NG.rt L n x⁻¹ w ∈ W' := hW'st x⁻¹ (GlobalTheory.SatInd.CosetFin.trivOutside_inv hx) w hw
    refine ⟨π.stable x f hfS, ?_⟩
    rw [hinv x ⟨NG.rt L n x⁻¹ w, hW'S hxw⟩ ⟨f, hfS⟩ ⟨w, hwS⟩ _ (rt_inv x w).symm rfl]
    exact key _ _ hxw f hfS hf)
  obtain ⟨_, hww⟩ := hWZ (hW'le hw)
  by_contra hne
  have := hpos ⟨w, hwS⟩ (fun h => hne (congrArg Subtype.val h))
  rw [hww] at this; simp at this

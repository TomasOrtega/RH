import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatDoubledPairSchrodingerFunction
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilMaj

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨C0, hC0, hC0'⟩ : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ a, (1 + ‖a‖) ^ (N * n) * ‖f a‖ ≤ C0 := by`. Use `⟨(2 : ℝ) ^ (N * n, 0).1 * ((Finset.Iic (N * n, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f, by positivity, fun a => ?_⟩` and prove the remaining obligations. Establish `h` using `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N * n, 0)) (k := N * n) (n := 0) le_rfl le_rfl f a`. Simplify using `using h`. Use `⟨C0 * P ^ (N * n), by positivity, fun a b hab => ?_⟩` and prove the remaining obligations.

Establish `hP0 : 0 < P` using `by linarith`. Establish `ha : 0 < 1 + ‖a‖` using `by positivity`. Establish `hb : 0 < 1 + ‖b‖` using `by positivity`. Establish `h1 : 1 + ‖b‖ ≤ P * (1 + ‖a‖)` using `by nlinarith [norm_nonneg a]`. Establish `hcol : ∀ j, ‖fun τ i => b τ i j‖ ≤ ‖b‖` using `fun j => by`.

Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun τ => ?_` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Conclude with `(norm_le_pi_norm (b τ i) j).trans ((norm_le_pi_norm (b τ) i).trans (norm_le_pi_norm b τ))`. Establish `h2 : ((1 + ‖b‖) ^ (N * n))⁻¹ ≤ ∏ j : Fin n, ((1 + ‖fun τ i => b τ i j‖) ^ N)⁻¹`. Establish `e : ((1 + ‖b‖) ^ (N * n))⁻¹ = ∏ _j : Fin n, ((1 + ‖b‖) ^ N)⁻¹`.

Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, pow_mul]`. Rewrite using `[e]`. Use `Finset.prod_le_prod (fun _ _ => by positivity) fun j _ => ?_` and prove the remaining obligations. Establish `: 0 < 1 + ‖fun τ i => b τ i j‖` using `by positivity`. Use `inv_anti₀ (by positivity) (pow_le_pow_left₀ this.le ?_ N)` and prove the remaining obligations.

Combine the linear relations using `[hcol j]`. Establish `h3 : ‖f a‖ ≤ C0 * ((1 + ‖a‖) ^ (N * n))⁻¹`. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]`. Conclude with `hC0' a`. Establish `h4 : ((1 + ‖a‖) ^ (N * n))⁻¹ ≤ P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹`.

Rewrite using `[← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity), ← mul_pow, mul_comm (1 + ‖a‖)]`. Conclude with `pow_le_pow_left₀ hb.le h1 _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem schwartz_col_bound {T : Type} [Fintype T] {M n : ℕ} (f : SchwartzMap (T → Fin M → Fin n → ℂ) ℂ)
    (P : ℝ) (hP : 1 ≤ P) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : T → Fin M → Fin n → ℂ, ‖b‖ ≤ P * ‖a‖ →
      ‖f a‖ ≤ C * ∏ j : Fin n, ((1 + ‖fun τ i => b τ i j‖) ^ N)⁻¹ := by
  obtain ⟨C0, hC0, hC0'⟩ : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ a, (1 + ‖a‖) ^ (N * n) * ‖f a‖ ≤ C0 := by
    refine ⟨(2 : ℝ) ^ (N * n, 0).1 * ((Finset.Iic (N * n, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f,
      by positivity, fun a => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N * n, 0)) (k := N * n) (n := 0)
      le_rfl le_rfl f a
    simpa using h
  refine ⟨C0 * P ^ (N * n), by positivity, fun a b hab => ?_⟩
  have hP0 : 0 < P := by linarith
  have ha : 0 < 1 + ‖a‖ := by positivity
  have hb : 0 < 1 + ‖b‖ := by positivity
  have h1 : 1 + ‖b‖ ≤ P * (1 + ‖a‖) := by nlinarith [norm_nonneg a]
  have hcol : ∀ j, ‖fun τ i => b τ i j‖ ≤ ‖b‖ := fun j => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun τ => ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact (norm_le_pi_norm (b τ i) j).trans ((norm_le_pi_norm (b τ) i).trans (norm_le_pi_norm b τ))
  have h2 : ((1 + ‖b‖) ^ (N * n))⁻¹ ≤ ∏ j : Fin n, ((1 + ‖fun τ i => b τ i j‖) ^ N)⁻¹ := by
    have e : ((1 + ‖b‖) ^ (N * n))⁻¹ = ∏ _j : Fin n, ((1 + ‖b‖) ^ N)⁻¹ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, pow_mul]
    rw [e]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun j _ => ?_
    have : 0 < 1 + ‖fun τ i => b τ i j‖ := by positivity
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ this.le ?_ N)
    linarith [hcol j]
  have h3 : ‖f a‖ ≤ C0 * ((1 + ‖a‖) ^ (N * n))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact hC0' a
  have h4 : ((1 + ‖a‖) ^ (N * n))⁻¹ ≤ P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity), ← mul_pow, mul_comm (1 + ‖a‖)]
    exact pow_le_pow_left₀ hb.le h1 _
  calc ‖f a‖ ≤ C0 * ((1 + ‖a‖) ^ (N * n))⁻¹ := h3
    _ ≤ C0 * (P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹) := by gcongr
    _ = C0 * P ^ (N * n) * ((1 + ‖b‖) ^ (N * n))⁻¹ := by ring
    _ ≤ _ := by gcongr

variable {D : D7}

/- English proof (translation)
Establish `h : (Formalism.L2.Theta.matHom V y) * (Formalism.L2.Theta.matHom V y⁻¹) = 1`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Conclude with `congrArg Units.val h`.
-/
theorem mt_mul_inv (V : HSp D) (y : GA D V) :
    (HMul.hMul (Formalism.L2.Theta.mt V y) (Formalism.L2.Theta.mt V y⁻¹) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = 1 := by
  have h : (Formalism.L2.Theta.matHom V y) * (Formalism.L2.Theta.matHom V y⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact congrArg Units.val h

/- English proof (translation)
The claim follows from `Matrix.map_mul (f := (θ τ).comp (infPart D))`.
-/
theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = HMul.hMul (compAt θ τ x) (compAt θ τ y) :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

/- English proof (translation)
Set `B : GA D V → (D.what₂.Tau → Fin V.rank → Fin V.rank → ℂ)` to `fun y τ i k => compAt θ τ (Formalism.L2.Theta.mt V y) i k`. Establish `hB : Continuous B`. Use `continuous_pi fun τ => continuous_pi fun i => continuous_pi fun k => ?_` and prove the remaining obligations. Conclude with `((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp (GlobalTheory.RealWeil.continuous_mt V).1).matrix_elem i k`. Take `⟨R, hR⟩` from `hC₁.exists_bound_of_continuousOn hB.continuousOn`.

Use `⟨1 + V.rank * |R|, by have := abs_nonneg R; nlinarith [Nat.cast_nonneg (α := ℝ) V.rank, mul_nonneg (Nat.cast_nonneg (α := ℝ) V.rank) (abs_nonneg R)], fun y hy x => ?_⟩` and prove the remaining obligations. Use `set u : D.what₂.Tau → Fin V.rank → Fin n → ℂ := fun τ i j => compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j with hu`. Establish `hx : ∀ τ, compAt θ τ x = HMul.hMul (compAt θ τ (Formalism.L2.Theta.mt V y)) (compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n))` using `fun τ => by`. Rewrite using `[← compAt_mul', ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]`. Establish `hN : 0 ≤ (1 + V.rank * |R|) * ‖u‖` using `by positivity`.

Use `(pi_norm_le_iff_of_nonneg hN).2 fun τ => (pi_norm_le_iff_of_nonneg hN).2 fun i => (pi_norm_le_iff_of_nonneg hN).2 fun j => ?_` and prove the remaining obligations. Rewrite using `[hx τ, Matrix.mul_apply]`. Establish `hk : ∀ k, ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k * compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ ≤ |R| * ‖u‖` using `fun k => by`. Rewrite using `[norm_mul]`. Establish `e1 : ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k‖ ≤ |R|` using `((norm_le_pi_norm (B y τ i) k).trans ((norm_le_pi_norm (B y τ) i).trans (norm_le_pi_norm (B y) τ))).trans ((hR y hy).trans (le_abs_self R))`.

Establish `e2 : ‖compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ ≤ ‖u‖` using `(norm_le_pi_norm (u τ k) j).trans ((norm_le_pi_norm (u τ) k).trans (norm_le_pi_norm u τ))`. Conclude with `mul_le_mul e1 e2 (norm_nonneg _) (abs_nonneg _)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem real_compare {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
      ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin V.rank → Fin n → ℂ)‖ ≤
        P * ‖(fun τ i j => compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j :
          D.what₂.Tau → Fin V.rank → Fin n → ℂ)‖ := by
  let B : GA D V → (D.what₂.Tau → Fin V.rank → Fin V.rank → ℂ) := fun y τ i k => compAt θ τ (Formalism.L2.Theta.mt V y) i k
  have hB : Continuous B := by
    refine continuous_pi fun τ => continuous_pi fun i => continuous_pi fun k => ?_
    exact ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp (GlobalTheory.RealWeil.continuous_mt V).1).matrix_elem i k
  obtain ⟨R, hR⟩ := hC₁.exists_bound_of_continuousOn hB.continuousOn
  refine ⟨1 + V.rank * |R|, by have := abs_nonneg R; nlinarith [Nat.cast_nonneg (α := ℝ) V.rank, mul_nonneg (Nat.cast_nonneg (α := ℝ) V.rank) (abs_nonneg R)], fun y hy x => ?_⟩
  set u : D.what₂.Tau → Fin V.rank → Fin n → ℂ :=
    fun τ i j => compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j with hu
  have hx : ∀ τ, compAt θ τ x = HMul.hMul (compAt θ τ (Formalism.L2.Theta.mt V y))
      (compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n)) := fun τ => by
    rw [← compAt_mul', ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  have hN : 0 ≤ (1 + V.rank * |R|) * ‖u‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg hN).2 fun τ => (pi_norm_le_iff_of_nonneg hN).2 fun i =>
    (pi_norm_le_iff_of_nonneg hN).2 fun j => ?_
  rw [hx τ, Matrix.mul_apply]
  have hk : ∀ k, ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k * compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ ≤ |R| * ‖u‖ := fun k => by
    rw [norm_mul]
    have e1 : ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k‖ ≤ |R| :=
      ((norm_le_pi_norm (B y τ i) k).trans ((norm_le_pi_norm (B y τ) i).trans (norm_le_pi_norm (B y) τ))).trans
        ((hR y hy).trans (le_abs_self R))
    have e2 : ‖compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ ≤ ‖u‖ :=
      (norm_le_pi_norm (u τ k) j).trans ((norm_le_pi_norm (u τ) k).trans (norm_le_pi_norm u τ))
    exact mul_le_mul e1 e2 (norm_nonneg _) (abs_nonneg _)
  calc _ ≤ ∑ k, ‖compAt θ τ (Formalism.L2.Theta.mt V y) i k * compAt θ τ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin V.rank, |R| * ‖u‖ := Finset.sum_le_sum fun k _ => hk k
    _ = V.rank * |R| * ‖u‖ := by simp [Finset.sum_const, mul_assoc]
    _ ≤ _ := by nlinarith [norm_nonneg u]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Use `haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _`. Establish `hS : IsCompact (tsupport g)` using `hg.2`. Set `Φ : GA D V × (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)` to `fun p i j => ∑ k, finPart D (Formalism.L2.Theta.mt V p.1 i k) * p.2 k j`. Establish `hΦ : Continuous Φ`. Use `continuous_pi fun i => continuous_pi fun j => continuous_finset_sum _ fun k _ => ?_` and prove the remaining obligations.

Use `Continuous.mul ?_ ?_` and prove the remaining obligations. Conclude with `GlobalTheory.SchwartzSch.continuous_finPart'.comp (((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_fst).matrix_elem i k)`. Conclude with `(continuous_apply j).comp ((continuous_apply k).comp continuous_snd)`. Establish `hK` using `(hC₁.prod hS).image hΦ`. Set `col : Fin n → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)` to `fun j w => Matrix.of fun i' _ => w i' j`.

Establish `hcol : ∀ j, Continuous (col j)` using `fun j => continuous_pi fun i => continuous_pi fun _ => (continuous_apply j).comp (continuous_apply i)`. Use `⟨⋃ j, col j '' (Φ '' (C₁ ×ˢ tsupport g)), isCompact_iUnion fun j => hK.image (hcol j), fun y hy x hne j => Set.mem_iUnion.2 ⟨j, fun i j => finPart D (x i j), ⟨(y, fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)), ⟨hy, subset_tsupport _ hne⟩, …` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Establish `e : (HMul.hMul (Formalism.L2.Theta.mt V y) (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) : Mx D V.rank n) = x`. Rewrite using `[← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]`.

Establish `e2` using `congrFun (congrFun e i) j`. Rewrite `e2` using `[Matrix.mul_apply]`. Use `show ∑ k, finPart D (Formalism.L2.Theta.mt V y i k) * finPart D _ = _`. Rewrite using `[← e2, map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => ((finPart D).map_mul _ _).symm`.
-/
theorem finite_compare (V : HSp D) (n : ℕ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (C₁ : Set (GA D V)) (hC₁ : IsCompact C₁) :
    ∃ L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact L ∧
      ∀ y ∈ C₁, ∀ x : Mx D V.rank n,
        g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)) ≠ 0 →
        ∀ j, (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) ∈ L := by
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have hS : IsCompact (tsupport g) := hg.2
  let Φ : GA D V × (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun p i j => ∑ k, finPart D (Formalism.L2.Theta.mt V p.1 i k) * p.2 k j
  have hΦ : Continuous Φ := by
    refine continuous_pi fun i => continuous_pi fun j => continuous_finset_sum _ fun k _ => ?_
    refine Continuous.mul ?_ ?_
    · exact GlobalTheory.SchwartzSch.continuous_finPart'.comp
        (((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_fst).matrix_elem i k)
    · exact (continuous_apply j).comp ((continuous_apply k).comp continuous_snd)
  have hK := (hC₁.prod hS).image hΦ
  let col : Fin n → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →
      Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun j w => Matrix.of fun i' _ => w i' j
  have hcol : ∀ j, Continuous (col j) := fun j =>
    continuous_pi fun i => continuous_pi fun _ => (continuous_apply j).comp (continuous_apply i)
  refine ⟨⋃ j, col j '' (Φ '' (C₁ ×ˢ tsupport g)), isCompact_iUnion fun j => hK.image (hcol j),
    fun y hy x hne j => Set.mem_iUnion.2 ⟨j, fun i j => finPart D (x i j),
      ⟨(y, fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)),
        ⟨hy, subset_tsupport _ hne⟩, ?_⟩, rfl⟩⟩
  funext i j
  have e : (HMul.hMul (Formalism.L2.Theta.mt V y) (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) : Mx D V.rank n) = x := by
    rw [← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  have e2 := congrFun (congrFun e i) j
  rw [Matrix.mul_apply] at e2
  show ∑ k, finPart D (Formalism.L2.Theta.mt V y i k) * finPart D _ = _
  rw [← e2, map_sum]
  exact Finset.sum_congr rfl fun k _ => ((finPart D).map_mul _ _).symm

/- English proof (translation)
Introduce `D θ hθ V n f g hg C₁ hC₁ N`. Take `⟨P, hP, hPx⟩` from `real_compare hθ V n C₁ hC₁`. Take `⟨C, hC, hf⟩` from `schwartz_col_bound f P hP N`. Take `⟨L, hL, hLx⟩` from `finite_compare V n g hg C₁ hC₁`. Take `⟨G, hG⟩` from `hg.1.continuous.bounded_above_of_compact_support hg.2`.

Use `⟨C * |G|, L, hL, fun y hy x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)) = 0`. Establish `e : ∀ a : ℂ, ‖a * g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j))‖ₑ = 0` using `fun a => by`. Rewrite using `[h0, mul_zero, enorm_zero]`. Conclude with `(e _).le.trans zero_le`.

Establish `hm` using `hLx y hy x h0`. Establish `hb` using `hf _ _ (hPx y hy x)`. Establish `hterm : ∀ j : Fin n, 0 ≤ ((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j))` using `fun j => by`. Rewrite using `[Set.indicator_of_mem (hm j)]`. Check the signs of the components of the expression.

Rewrite using `[← ENNReal.ofReal_prod_of_nonneg fun j _ => hterm j, ← ENNReal.ofReal_mul (mul_nonneg hC (abs_nonneg G)), ← ofReal_norm_eq_enorm]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Simplify using `only [Set.indicator_of_mem (hm _), mul_one]`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem schwartz_translate_majorant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ) (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ), g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ∀ (C₁ : Set (GA D V)), IsCompact C₁ → ∀ N : ℕ, ∃ (C : ℝ) (L : Set (Matrix (Fin V.rank) (Fin 1) (Af D.host.F ⊗[D.host.F] D.host.E))), IsCompact L ∧ ∀ y ∈ C₁, ∀ x : Mx D V.rank n, ‖f (fun τ i j => compAt θ τ (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j) * g (fun i j => finPart D ((HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D)) i j))‖ₑ ≤ ENNReal.ofReal C * ∏ j : Fin n, ENNReal.ofReal (((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹ * Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j))) := by
  intro D θ hθ V n f g hg C₁ hC₁ N
  obtain ⟨P, hP, hPx⟩ := real_compare hθ V n C₁ hC₁
  obtain ⟨C, hC, hf⟩ := schwartz_col_bound f P hP N
  obtain ⟨L, hL, hLx⟩ := finite_compare V n g hg C₁ hC₁
  obtain ⟨G, hG⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  refine ⟨C * |G|, L, hL, fun y hy x => ?_⟩
  by_cases h0 : g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j)) = 0
  · have e : ∀ a : ℂ, ‖a * g (fun i j => finPart D ((HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) i j))‖ₑ = 0 := fun a => by
      rw [h0, mul_zero, enorm_zero]
    exact (e _).le.trans zero_le
  · have hm := hLx y hy x h0
    have hb := hf _ _ (hPx y hy x)
    have hterm : ∀ j : Fin n, 0 ≤ ((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹ *
        Set.indicator L (fun _ => (1 : ℝ)) (Matrix.of fun i' (_ : Fin 1) => finPart D (x i' j)) := fun j => by
      rw [Set.indicator_of_mem (hm j)]
      positivity
    rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => hterm j,
      ← ENNReal.ofReal_mul (mul_nonneg hC (abs_nonneg G)), ← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Set.indicator_of_mem (hm _), mul_one]
    rw [norm_mul]
    calc _ ≤ (C * ∏ j : Fin n, ((1 + ‖fun τ i => compAt θ τ (Matrix.of fun i' (_ : Fin 1) => x i' j) i 0‖) ^ N)⁻¹) * |G| :=
          mul_le_mul hb ((hG _).trans (le_abs_self G)) (norm_nonneg _)
            (mul_nonneg hC (Finset.prod_nonneg fun j _ => by positivity))
      _ = _ := by ring

end GlobalTheory.CompanionTheory.WeilMaj
end

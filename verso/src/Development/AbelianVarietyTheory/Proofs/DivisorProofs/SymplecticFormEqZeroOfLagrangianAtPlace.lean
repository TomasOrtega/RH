import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertVacIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]`. Consider the case `tmul x b`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul]`.

Simplify using `[compFin, Algebra.TensorProduct.map_tmul]`.
-/
theorem smul_eq_map_compFin (v : Pl F) (a : AE F E) :
    GlobalTheory.EmbChart.atPlace v 1 • a =
      TensorProduct.map (GlobalTheory.EmbChart.atPlace v) LinearMap.id (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]
  | tmul x b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul]
    simp [compFin, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
Rewrite using `[smul_eq_map_compFin, h, map_zero]`.
-/
theorem smul_eq_zero_of_compFin (v : Pl F) {a : AE F E} (h : compFin F E v a = 0) :
    GlobalTheory.EmbChart.atPlace v 1 • a = 0 := by
  rw [smul_eq_map_compFin, h, map_zero]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`. Consider the case `tmul x b => simp [cA, compFin, Algebra.TensorProduct.map_tmul]`.
-/
theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl F) (a : AE F E) :
    compFin F E v (cA σ a) =
      Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul x b => simp [cA, compFin, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
Establish `h1` using `h (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])`. Rewrite `h1` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `h1`.
-/
theorem self_eq_smul_of_at {n d : ℕ} (v : Pl F) {u : Matrix (Fin n) (Fin d) (AE F E)} (h : At (evFin F v) u) :
    u = GlobalTheory.EmbChart.atPlace v 1 • u := by
  have h1 := h (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

/- English proof (translation)
Simplify using `only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_eq_sum {α β : Type} [Fintype α] [Fintype β] (c : AE F E →ₐ[AF F] AE F E) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (x y : Matrix α β (AE F E)) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d m JX W v C hL ξ u u' hu hu'`. Take `⟨hat, z, rfl⟩` from `hu`. Take `⟨-, z', rfl⟩` from `hu'`. Use `set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v)`. Use `set P := Cᵀ * incM F W.J * C.map (cA σ) with hP`.

Establish `hPv : P.map (compFin F E v) = 0`. Establish `h1` using `hL.1`. Rewrite using `[hP, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]`. Use `h1 using 2` and compare the differences between its conclusion and the goal. Use `congr 1`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`. Conclude with `compFin_cA σ v (C i j)`. Establish `heP : e • P = 0`. Use extensionality with `p q`.

Rewrite using `[Matrix.smul_apply, Matrix.zero_apply]`. Apply `smul_eq_zero_of_compFin` to reduce the goal to its premises. Use `congrArg (fun M => M p q) hPv` as an intermediate fact. Simplify using `using this`. Establish `hM : z * Cᵀ * incM F W.J * ((z' * Cᵀ).map (cA σ))ᵀ = 0`.

Rewrite using `[self_eq_smul_of_at v hat]`. Establish `hmap : (z' * Cᵀ).map (cA σ) = z'.map (cA σ) * Cᵀ.map (cA σ)` using `Matrix.map_mul (f := (cA σ).toRingHom)`. Rewrite using `[hmap, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]`. Rewrite using `[Matrix.smul_mul, Matrix.smul_mul]`. Establish `: z * Cᵀ * incM F W.J * (C.map (cA σ) * (z'.map (cA σ))ᵀ) = z * P * (z'.map (cA σ))ᵀ`.

Rewrite using `[hP]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, ← Matrix.smul_mul, ← Matrix.mul_smul, heP, Matrix.mul_zero, Matrix.zero_mul]`. Rewrite using `[symp, hTens_eq_sum, hM]`. Simplify using the standard rewrite rules.
-/
theorem symp_eq_zero_of_lagAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d m : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (W : Spc F E d) (v : Pl F) (C : Matrix (Fin d) (Fin m) (AE F E)),
    GlobalTheory.InertVacLag.IsLagrAt σ W v C → ∀ (ξ : AE F E) (u u' : Matrix (Fin n) (Fin d) (AE F E)),
    u ∈ GlobalTheory.InertVacLag.lagAt v C → u' ∈ GlobalTheory.InertVacLag.lagAt v C →
    symp (cA σ) ξ (incM F JX) (incM F W.J) u u' = 0 := by
  intro F E _ _ _ _ _ σ n d m JX W v C hL ξ u u' hu hu'
  obtain ⟨hat, z, rfl⟩ := hu
  obtain ⟨-, z', rfl⟩ := hu'
  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v)
  set P := Cᵀ * incM F W.J * C.map (cA σ) with hP
  have hPv : P.map (compFin F E v) = 0 := by
    have h1 := hL.1
    rw [hP, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    convert h1 using 2
    · congr 1
    · ext i j
      simp only [Matrix.map_apply]
      exact compFin_cA σ v (C i j)
  have heP : e • P = 0 := by
    ext p q
    rw [Matrix.smul_apply, Matrix.zero_apply]
    apply smul_eq_zero_of_compFin
    have := congrArg (fun M => M p q) hPv
    simpa using this
  have hM : z * Cᵀ * incM F W.J * ((z' * Cᵀ).map (cA σ))ᵀ = 0 := by
    rw [self_eq_smul_of_at v hat]
    have hmap : (z' * Cᵀ).map (cA σ) = z'.map (cA σ) * Cᵀ.map (cA σ) :=
      Matrix.map_mul (f := (cA σ).toRingHom)
    rw [hmap, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]
    rw [Matrix.smul_mul, Matrix.smul_mul]
    have : z * Cᵀ * incM F W.J * (C.map (cA σ) * (z'.map (cA σ))ᵀ) = z * P * (z'.map (cA σ))ᵀ := by
      rw [hP]; simp only [Matrix.mul_assoc]
    rw [this, ← Matrix.smul_mul, ← Matrix.mul_smul, heP, Matrix.mul_zero, Matrix.zero_mul]
  rw [symp, hTens_eq_sum, hM]
  simp

end GlobalTheory.InertVacIso
end

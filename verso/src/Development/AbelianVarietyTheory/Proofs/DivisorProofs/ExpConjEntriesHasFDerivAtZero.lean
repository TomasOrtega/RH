import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `n ι _ A p`. Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Set `E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (ι → ℂ)` to `{ toFun := fun M x => M (p x).1 (p x).2 map_add' := by intros; rfl map_smul' := by intros; rfl }`. Set `Ec` to `LinearMap.toContinuousLinearMap E`.

Set `Ac` to `LinearMap.toContinuousLinearMap A`. Establish `hA0 : Ac 0 = 0` using `map_zero _`. Establish `hnA0 : (-Ac) 0 = 0` using `map_zero _`. Establish `h1 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) (Ac 0)`. Rewrite using `[hA0]`.

Conclude with `hasFDerivAt_exp_zero`. Establish `h1' : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) ((-Ac) 0)`. Rewrite using `[hnA0]`. Conclude with `hasFDerivAt_exp_zero`. Establish `hexpA : HasFDerivAt (fun w => NormedSpace.exp (Ac w)) ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp Ac) 0` using `h1.comp (0 : ι → ℂ) Ac.hasFDerivAt`.

Establish `hexpN : HasFDerivAt (fun w => NormedSpace.exp ((-Ac) w)) ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp (-Ac)) 0` using `h1'.comp (0 : ι → ℂ) (-Ac).hasFDerivAt`. Use `⟨⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hexpA⟩, fun s => ?_⟩` and prove the remaining obligations. Introduce `w x`. Both sides reduce to the same expression. Establish `hprod` using `(hexpN.mul' (hasFDerivAt_const s (0 : ι → ℂ))).mul' hexpA`.

Use `⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hprod⟩` and prove the remaining obligations. Introduce `w x`. Establish `hA0' : A 0 = 0` using `map_zero A`. Simplify using `only [Ec, E, Ac, hA0', NormedSpace.exp_zero, Pi.mul_apply, map_zero, neg_zero]`. Express the relevant statement in the definitionally equal form `((1 * s) * A w + (1 * 0 + (-(A w)) * s) * 1 : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2 = (s * A w - A w * s) (p x).1 (p x).2`.

Rewrite using `[one_mul, mul_zero, zero_add, mul_one, neg_mul, ← sub_eq_add_neg]`.
-/
theorem exp_conj_entries_hasFDerivAt_zero : ∀ (n : ℕ) (ι : Type) [Fintype ι] (A : (ι → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (p : ι → Fin n × Fin n), (∃ L : (ι → ℂ) →L[ℝ] (ι → ℂ), (∀ w x, L w x = A w (p x).1 (p x).2) ∧ HasFDerivAt (fun (w : ι → ℂ) (x : ι) => (NormedSpace.exp (A w) : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2) L 0) ∧ ∀ s : Matrix (Fin n) (Fin n) ℂ, ∃ L : (ι → ℂ) →L[ℝ] (ι → ℂ), (∀ w x, L w x = (s * A w - A w * s) (p x).1 (p x).2) ∧ HasFDerivAt (fun (w : ι → ℂ) (x : ι) => (NormedSpace.exp (-A w) * s * NormedSpace.exp (A w) : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2) L 0 := by
  intro n ι _ A p
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (ι → ℂ) :=
    { toFun := fun M x => M (p x).1 (p x).2
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let Ec := LinearMap.toContinuousLinearMap E
  let Ac := LinearMap.toContinuousLinearMap A
  have hA0 : Ac 0 = 0 := map_zero _
  have hnA0 : (-Ac) 0 = 0 := map_zero _
  have h1 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) (Ac 0) := by
    rw [hA0]; exact hasFDerivAt_exp_zero
  have h1' : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) ((-Ac) 0) := by
    rw [hnA0]; exact hasFDerivAt_exp_zero
  have hexpA : HasFDerivAt (fun w => NormedSpace.exp (Ac w))
      ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp Ac) 0 :=
    h1.comp (0 : ι → ℂ) Ac.hasFDerivAt
  have hexpN : HasFDerivAt (fun w => NormedSpace.exp ((-Ac) w))
      ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp (-Ac)) 0 :=
    h1'.comp (0 : ι → ℂ) (-Ac).hasFDerivAt
  refine ⟨⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hexpA⟩, fun s => ?_⟩
  · intro w x; rfl
  · have hprod := (hexpN.mul' (hasFDerivAt_const s (0 : ι → ℂ))).mul' hexpA
    refine ⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hprod⟩
    intro w x
    have hA0' : A 0 = 0 := map_zero A
    simp only [Ec, E, Ac, hA0', NormedSpace.exp_zero, Pi.mul_apply, map_zero, neg_zero]
    change ((1 * s) * A w + (1 * 0 + (-(A w)) * s) * 1 : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2 = (s * A w - A w * s) (p x).1 (p x).2
    rw [one_mul, mul_zero, zero_add, mul_one, neg_mul, ← sub_eq_add_neg]

end GlobalTheory

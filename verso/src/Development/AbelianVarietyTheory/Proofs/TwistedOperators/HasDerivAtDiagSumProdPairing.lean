import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Use `set d := Module.finrank ℝ V`. Set `e : Module.Basis (Fin d) ℝ V` to `Module.finBasis ℝ V`. Establish `hinj : Function.Injective β.flip`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `q hq`.

Conclude with `hβ q (fun x => by simpa using LinearMap.congr_fun hq x)`. Establish `hsurj : Function.Surjective β.flip` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj`. Use `choose q hq using fun i : Fin d => hsurj (e.coord i)`. Establish `hqx : ∀ x i, β x (q i) = e.repr x i`. Introduce `x i`.

Use `LinearMap.congr_fun (hq i) x` as an intermediate fact. Simplify using `using this`. Establish `hexp : ∀ x t, M t x x = ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j)`. Introduce `x t`. Use `conv_lhs => rw [← e.sum_repr x]`.

Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.mul_sum, Complex.real_smul, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Set `c : Fin d × Fin d → ℂ` to `fun p => deriv (fun t => M t (e p.1) (e p.2)) 0`.

Use `⟨d * d, fun k => q (finProdFinEquiv.symm k).1, fun k => q (finProdFinEquiv.symm k).2, fun k => c (finProdFinEquiv.symm k), fun x => ?_⟩` and prove the remaining obligations. Establish `hfun : (fun t => M t x x) = fun t => ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j)` using `funext (hexp x)`. Rewrite using `[hfun]`. Establish `hd : HasDerivAt (fun t => ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j)) (∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * c (i, j)) 0`. Apply `HasDerivAt.fun_sum` to reduce the goal to its premises.

Introduce `i _`. Apply `HasDerivAt.fun_sum` to reduce the goal to its premises. Introduce `j _`. Conclude with `((hM (e i) (e j)).hasDerivAt).const_mul _`. Use `hd using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [hqx]`. Rewrite using `[← Fintype.sum_prod_type']`. Rewrite using `[← (finProdFinEquiv (m := d) (n := d)).symm.sum_comp]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_diag_sum_prod_pairing
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hβ : ∀ q, (∀ x, β x q = 0) → q = 0)
    (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hM : ∀ x y, DifferentiableAt ℝ (fun t => M t x y) 0) :
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
      HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  classical
  set d := Module.finrank ℝ V
  let e : Module.Basis (Fin d) ℝ V := Module.finBasis ℝ V

  have hinj : Function.Injective β.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    exact hβ q (fun x => by simpa using LinearMap.congr_fun hq x)
  have hsurj : Function.Surjective β.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj
  choose q hq using fun i : Fin d => hsurj (e.coord i)
  have hqx : ∀ x i, β x (q i) = e.repr x i := by
    intro x i
    have := LinearMap.congr_fun (hq i) x
    simpa using this

  have hexp : ∀ x t, M t x x =
      ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j) := by
    intro x t
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.mul_sum,
      Complex.real_smul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  let c : Fin d × Fin d → ℂ := fun p => deriv (fun t => M t (e p.1) (e p.2)) 0
  refine ⟨d * d, fun k => q (finProdFinEquiv.symm k).1, fun k => q (finProdFinEquiv.symm k).2,
    fun k => c (finProdFinEquiv.symm k), fun x => ?_⟩
  have hfun : (fun t => M t x x) = fun t =>
      ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j) := funext (hexp x)
  rw [hfun]
  have hd : HasDerivAt (fun t => ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j))
      (∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * c (i, j)) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact ((hM (e i) (e j)).hasDerivAt).const_mul _
  convert hd using 1
  simp only [hqx]
  rw [← Fintype.sum_prod_type']
  rw [← (finProdFinEquiv (m := d) (n := d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory

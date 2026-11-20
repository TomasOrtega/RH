import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.ChartUnit

/- English proof (translation)
Use `⟨fun i => by simp [h.1 i], fun m => ?_⟩` and prove the remaining obligations. Take `⟨N, hN⟩` from `h.2 m`. Use `⟨N, fun f hf => ?_⟩` and prove the remaining obligations. Use `map_dvd φ (hN f hf)` as an intermediate fact. Simplify using `using this`.
-/
theorem isEval_comp {p : ℕ} {σ R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    {x : σ → A} {E : MvPowerSeries σ R →ₐ[R] A} (φ : A →ₐ[R] A') (h : IsEval p x E) :
    IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd φ (hN f hf)
  simpa using this

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [Algebra.smul_def, mul_comm]`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`.
-/
theorem lift_counit_eq {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] (t : A ⊗[O] A) :
    Algebra.TensorProduct.lift (AlgHom.id O A) ((Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A))
      (fun _ _ => Commute.all _ _) t = TensorProduct.rid O A (LinearMap.lTensor A (Coalgebra.counit (R := O)) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.smul_def, mul_comm]
  | add s t hs ht => simp only [map_add, hs, ht]

end GlobalTheory.ChartUnit

open GlobalTheory.ChartUnit in

/- English proof (translation)
Introduce `p O A _ _ _ _ d x ev E₂ μ hnil hcu hev hev₂ hcomul i`. Use `set ψ : A ⊗[O] A →ₐ[O] A := Algebra.TensorProduct.lift (AlgHom.id O A) ((Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A)) (fun _ _ => Commute.all _ _) with hψ`. Establish `key` using `(GlobalTheory.CEval.continuous_eval p O A (Fin d) x hnil).2 ev hev`. Set `u : Fin d ⊕ Fin d → MvPowerSeries (Fin d) O` to `Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0)`. Establish `hE' : IsEval p (fun j => ev (u j)) (ψ.comp E₂)`.

Establish `h` using `isEval_comp ψ hev₂`. Use `h using 2 with j` and compare the differences between its conclusion and the goal. Break down `j with j | j` into its components or cases. Simplify using `[u, hψ, hev.1 j]`. Simplify using `[u, hψ, hcu j]`.

Establish `hu : ∀ j, constantCoeff (u j) = 0`. Apply the tactic sequence `intro j; rcases j with j | j <;> simp [u]`. Use `key.1 (Fin d ⊕ Fin d) u (ψ.comp E₂) hu hE' (μ i)` as an intermediate fact. Use `show ev (subst u (μ i)) = x i`. Rewrite using `[this, AlgHom.comp_apply, hcomul, hψ, lift_counit_eq, Coalgebra.lTensor_counit_comul]`.

Simplify using the standard rewrite rules.
-/
theorem GlobalTheory.chart_unit : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A)}) A] {d : ℕ} (x : Fin d → A) (ev : MvPowerSeries (Fin d) O →ₐ[O] A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p x ev → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, ev (op μ (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0) i) = x i := by
  intro p O A _ _ _ _ d x ev E₂ μ hnil hcu hev hev₂ hcomul i
  set ψ : A ⊗[O] A →ₐ[O] A := Algebra.TensorProduct.lift (AlgHom.id O A)
    ((Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A)) (fun _ _ => Commute.all _ _) with hψ
  have key := (GlobalTheory.CEval.continuous_eval p O A (Fin d) x hnil).2 ev hev
  let u : Fin d ⊕ Fin d → MvPowerSeries (Fin d) O :=
    Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0)
  have hE' : IsEval p (fun j => ev (u j)) (ψ.comp E₂) := by
    have h := isEval_comp ψ hev₂
    convert h using 2 with j
    rcases j with j | j
    · simp [u, hψ, hev.1 j]
    · simp [u, hψ, hcu j]
  have hu : ∀ j, constantCoeff (u j) = 0 := by
    intro j; rcases j with j | j <;> simp [u]
  have := key.1 (Fin d ⊕ Fin d) u (ψ.comp E₂) hu hE' (μ i)
  show ev (subst u (μ i)) = x i
  rw [this, AlgHom.comp_apply, hcomul, hψ, lift_counit_eq, Coalgebra.lTensor_counit_comul]
  simp

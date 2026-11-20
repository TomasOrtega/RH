import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

/- English proof (translation)
Use `letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) := Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)`. Use `letI (i : Fin k) : TopologicalSpace (C i ⊗[F] AdeleRing (𝓞 F) F) := Formalism.BasicNotions.tensTopL (F := F) (E := C i) (AdeleRing (𝓞 F) F)`. Use `haveI := (hL F B).1`. Use `choose D hD hDu using h`. Set `p (i : Fin k) : B ⊗[F] AdeleRing (𝓞 F) F →ₐ[F] C i ⊗[F] AdeleRing (𝓞 F) F` to `Algebra.TensorProduct.map (π i) (AlgHom.id F _)`.

Set `Φ : (∀ i, C i ⊗[F] AdeleRing (𝓞 F) F) → B ⊗[F] AdeleRing (𝓞 F) F` to `fun x => ∑ i, LinearMap.rTensor (AdeleRing (𝓞 F) F) (s i) (x i)`. Establish `hΦ : Continuous Φ` using `continuous_finset_sum _ fun i _ => (continuous_rTensor (AdeleRing (𝓞 F) F) (s i)).comp (continuous_apply i)`. Establish `hp : ∀ i u, p i (sigR τ _ u) = sigR (ρ i) _ (p i u)`. Introduce `i u`. Proceed by induction on `u with`.

Consider the case `zero => simp`. Consider the case `tmul a b => simp [p, sigR, hcomm]`. Consider the case `add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]`. Establish `hm : ∀ i u (y : C i), LinearMap.rTensor (AdeleRing (𝓞 F) F) (s i) (p i u * inclE (F` using `F) _ y) = u * inclE (F := F) _ (s i y) := by`. Introduce `i u y`.

Proceed by induction on `u with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [p, inclE, hmul]`. Consider the case `add a b ha hb => rw [map_add, add_mul, map_add, add_mul, ha, hb]`. Use `⟨Φ '' Set.pi Set.univ D, (isCompact_univ_pi hD).image hΦ, fun u hu => ?_⟩` and prove the remaining obligations.

Establish `hpu : ∀ i, p i u * sigR (ρ i) _ (p i u) = 1` using `fun i => by`. Rewrite using `[← hp, ← map_mul, hu, map_one]`. Use `choose β hβ hβD using fun i => hDu i (p i u) (hpu i)`. Use `choose γ hγ using fun i => (hβ i).exists_right_inv`. Use `⟨∑ i, s i (β i), IsUnit.of_mul_eq_one (∑ i, s i (γ i)) ?_, fun i => p i u * inclE (F := F) _ (β i), fun i _ => hβD i, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Simplify using `only [← hmul, hps, hγ]`. Simplify using `using hsum 1`. Simplify using `only [Φ, hm, map_sum, Finset.mul_sum]`.
-/
theorem unitBounded_of_split (hL : TensorLattice) {F B : Type} [Field F] [NumberField F]
    [CommRing B] [Algebra F B] [Module.Finite F B] (τ : B →ₐ[F] B) {k : ℕ} (C : Fin k → Type)
    [∀ i, CommRing (C i)] [∀ i, Algebra F (C i)] (ρ : ∀ i, C i →ₐ[F] C i)
    (π : ∀ i, B →ₐ[F] C i) (s : ∀ i, C i →ₗ[F] B)
    (hsum : ∀ x, ∑ i, s i (π i x) = x)
    (hmul : ∀ i x y, s i (π i x * y) = x * s i y)
    (hps : ∀ (b : ∀ i, C i) j, π j (∑ i, s i (b i)) = b j)
    (hcomm : ∀ i x, π i (τ x) = ρ i (π i x))
    (h : ∀ i, UnitBounded F (C i) (ρ i)) : UnitBounded F B τ := by
  classical
  letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  letI (i : Fin k) : TopologicalSpace (C i ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := C i) (AdeleRing (𝓞 F) F)
  haveI := (hL F B).1
  choose D hD hDu using h
  let p (i : Fin k) : B ⊗[F] AdeleRing (𝓞 F) F →ₐ[F] C i ⊗[F] AdeleRing (𝓞 F) F :=
    Algebra.TensorProduct.map (π i) (AlgHom.id F _)
  let Φ : (∀ i, C i ⊗[F] AdeleRing (𝓞 F) F) → B ⊗[F] AdeleRing (𝓞 F) F :=
    fun x => ∑ i, LinearMap.rTensor (AdeleRing (𝓞 F) F) (s i) (x i)
  have hΦ : Continuous Φ :=
    continuous_finset_sum _ fun i _ =>
      (continuous_rTensor (AdeleRing (𝓞 F) F) (s i)).comp (continuous_apply i)
  have hp : ∀ i u, p i (sigR τ _ u) = sigR (ρ i) _ (p i u) := by
    intro i u
    induction u with
    | zero => simp
    | tmul a b => simp [p, sigR, hcomm]
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  have hm : ∀ i u (y : C i), LinearMap.rTensor (AdeleRing (𝓞 F) F) (s i)
      (p i u * inclE (F := F) _ y) = u * inclE (F := F) _ (s i y) := by
    intro i u y
    induction u with
    | zero => simp
    | tmul a b => simp [p, inclE, hmul]
    | add a b ha hb => rw [map_add, add_mul, map_add, add_mul, ha, hb]
  refine ⟨Φ '' Set.pi Set.univ D, (isCompact_univ_pi hD).image hΦ, fun u hu => ?_⟩
  have hpu : ∀ i, p i u * sigR (ρ i) _ (p i u) = 1 := fun i => by
    rw [← hp, ← map_mul, hu, map_one]
  choose β hβ hβD using fun i => hDu i (p i u) (hpu i)
  choose γ hγ using fun i => (hβ i).exists_right_inv
  refine ⟨∑ i, s i (β i), IsUnit.of_mul_eq_one (∑ i, s i (γ i)) ?_,
    fun i => p i u * inclE (F := F) _ (β i), fun i _ => hβD i, ?_⟩
  · rw [Finset.mul_sum]
    simp only [← hmul, hps, hγ]
    simpa using hsum 1
  · simp only [Φ, hm, map_sum, Finset.mul_sum]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ P _ _ _ k K _ _ ⟨e⟩ h`. Set `q (i : Fin k) : P →ₐ[F] K i` to `(Pi.evalAlgHom F K i).comp (e : P →ₐ[F] ∀ i, K i)`. Set `t (i : Fin k) : K i →ₗ[F] P` to `e.symm.toLinearMap ∘ₗ LinearMap.single F K i`. Establish `hq : ∀ i x, q i x = e x i` using `fun _ _ => rfl`. Establish `ht : ∀ i x, t i x = e.symm (Pi.single i x)` using `fun _ _ => rfl`.

Establish `h1 : ∀ x, ∑ i, t i (q i x) = x` using `fun x => by`. Simplify using `only [hq, ht, ← map_sum, Finset.univ_sum_single, AlgEquiv.symm_apply_apply]`. Establish `h2 : ∀ i x y, t i (q i x * y) = x * t i y` using `fun i x y => by`. Apply `e.injective` to reduce the goal to its premises. Simplify using `only [hq, ht, map_mul, AlgEquiv.apply_symm_apply]`.

Use extensionality with `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`.

Use `unitBounded_of_split hL (tConj P σ) (fun i => K i ⊗[F] E) (fun i => tConj (K i) σ) (fun i => Algebra.TensorProduct.map (q i) (AlgHom.id F E)) (fun i => LinearMap.rTensor E (t i)) ?_ ?_ ?_ ?_ h` and prove the remaining obligations. Introduce `x`. Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [← TensorProduct.sum_tmul, h1]`.

Consider the case `add a b ha hb => simp only [map_add, Finset.sum_add_distrib, ha, hb]`. Introduce `i x y`. Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, add_mul, ha, hb]`.

Consider the case `tmul a b`. Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `add c d hc hd => simp only [map_add, mul_add, hc, hd]`. Consider the case `tmul c d => simp [h2]`.

Introduce `b j`. Rewrite using `[map_sum, Finset.sum_eq_single j]`. Generalize the expression as in `b j = y`. Proceed by induction on `y with`. Consider the case `zero => simp`.

Consider the case `add c d hc hd => simp only [map_add, hc, hd]`. Consider the case `tmul c d => simp [hq, ht]`. Introduce `i _ hi`. Generalize the expression as in `b i = y`. Proceed by induction on `y with`.

Consider the case `zero => simp`. Consider the case `add c d hc hd => simp only [map_add, hc, hd, add_zero]`. Consider the case `tmul c d => simp [hq, ht, hi.symm]`. Simplify using the standard rewrite rules. Introduce `i x`.

Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [tConj]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem productUnitBounded (hL : TensorLattice) : ProductUnitBounded := by
  classical
  intro F E _ _ _ _ _ σ P _ _ _ k K _ _ ⟨e⟩ h
  let q (i : Fin k) : P →ₐ[F] K i := (Pi.evalAlgHom F K i).comp (e : P →ₐ[F] ∀ i, K i)
  let t (i : Fin k) : K i →ₗ[F] P := e.symm.toLinearMap ∘ₗ LinearMap.single F K i
  have hq : ∀ i x, q i x = e x i := fun _ _ => rfl
  have ht : ∀ i x, t i x = e.symm (Pi.single i x) := fun _ _ => rfl
  have h1 : ∀ x, ∑ i, t i (q i x) = x := fun x => by
    simp only [hq, ht, ← map_sum, Finset.univ_sum_single, AlgEquiv.symm_apply_apply]
  have h2 : ∀ i x y, t i (q i x * y) = x * t i y := fun i x y => by
    apply e.injective
    simp only [hq, ht, map_mul, AlgEquiv.apply_symm_apply]
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  refine unitBounded_of_split hL (tConj P σ) (fun i => K i ⊗[F] E) (fun i => tConj (K i) σ)
    (fun i => Algebra.TensorProduct.map (q i) (AlgHom.id F E))
    (fun i => LinearMap.rTensor E (t i)) ?_ ?_ ?_ ?_ h
  · intro x
    induction x with
    | zero => simp
    | tmul a b => simp [← TensorProduct.sum_tmul, h1]
    | add a b ha hb => simp only [map_add, Finset.sum_add_distrib, ha, hb]
  · intro i x y
    induction x with
    | zero => simp
    | add a b ha hb => simp only [map_add, add_mul, ha, hb]
    | tmul a b =>
      induction y with
      | zero => simp
      | add c d hc hd => simp only [map_add, mul_add, hc, hd]
      | tmul c d => simp [h2]
  · intro b j
    rw [map_sum, Finset.sum_eq_single j]
    · generalize b j = y
      induction y with
      | zero => simp
      | add c d hc hd => simp only [map_add, hc, hd]
      | tmul c d => simp [hq, ht]
    · intro i _ hi
      generalize b i = y
      induction y with
      | zero => simp
      | add c d hc hd => simp only [map_add, hc, hd, add_zero]
      | tmul c d => simp [hq, ht, hi.symm]
    · simp
  · intro i x
    induction x with
    | zero => simp
    | tmul a b => simp [tConj]
    | add a b ha hb => simp only [map_add, ha, hb]

end GlobalTheory.RegSS

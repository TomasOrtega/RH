import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open scoped SchwartzMap Matrix

open scoped RealInnerProductSpace
noncomputable section
namespace GlobalTheory.ArchUniq
open GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def leftForm {P : V → V → ℝ} (hP : IsPairing P) (b : V) : V →ₗ[ℝ] ℝ where
  toFun x := P x b
  map_add' x x' := hP.addL x x' b
  map_smul' c x := hP.smulL c x b

/- English proof (translation)
Establish `hy : y = ∑ i, C y i • C.symm (EuclideanSpace.single i 1)` using `by conv_lhs => rw [← C.symm_apply_apply y, ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (C y)]`. Simplify using `[map_sum]`. Establish `e : P y b = leftForm hP b y` using `rfl`. Rewrite using `[e]`. Use `conv_lhs => rw [hy]`.

Rewrite using `[map_sum]`. Simplify using `[leftForm, hP.smulL]`.
-/
theorem pair_expand {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) (y b : V) :
    P y b = ∑ i, C y i * P (C.symm (EuclideanSpace.single i 1)) b := by
  have hy : y = ∑ i, C y i • C.symm (EuclideanSpace.single i 1) := by
    conv_lhs => rw [← C.symm_apply_apply y, ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (C y)]
    simp [map_sum]
  have e : P y b = leftForm hP b y := rfl
  rw [e]
  conv_lhs => rw [hy]
  rw [map_sum]
  simp [leftForm, hP.smulL]

def pairCoordsL {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) :
    V × V →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) where
  toFun v := Sum.elim (fun i => C v.1 i) (fun i => -P (C.symm (EuclideanSpace.single i 1)) v.2)
  map_add' v v' := by
    funext j
    rcases j with i | i <;> simp [hP.addR]; ring
  map_smul' c v := by
    funext j
    rcases j with i | i <;> simp [hP.smulR]

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨a, b⟩ h`. Establish `ha : a = 0`. Apply `C.injective` to reduce the goal to its premises. Use extensionality with `i`.

Simplify `congrFun h (Sum.inl i)` using `[pairCoordsL]`. Establish `hb : b = 0`. Apply `hP.nondegR` to reduce the goal to its premises. Introduce `x`. Rewrite using `[pair_expand C hP]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `congrFun h (Sum.inr i)` as an intermediate fact. Simplify using `[pairCoordsL] at this`. Simplify using `[this]`. Simplify using `[ha, hb]`.
-/
theorem pairCoordsL_injective {n : ℕ} (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) {P : V → V → ℝ} (hP : IsPairing P) :
    Function.Injective (pairCoordsL C hP) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, b⟩ h
  have ha : a = 0 := by
    apply C.injective
    ext i
    simpa [pairCoordsL] using congrFun h (Sum.inl i)
  have hb : b = 0 := by
    apply hP.nondegR
    intro x
    rw [pair_expand C hP]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h (Sum.inr i)
    simp [pairCoordsL] at this
    simp [this]
  simp [ha, hb]

/- English proof (translation)
Introduce `V _ _ _ P hP n hn`. Set `C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)` to `ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_fin).symm)`. Establish `hdim : Module.finrank ℝ (V × V) = Module.finrank ℝ (Fin n ⊕ Fin n → ℝ)`. Simplify using `[Module.finrank_prod, hn]`. Set `φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)` to `LinearMap.linearEquivOfInjective (pairCoordsL C hP) (pairCoordsL_injective C hP) hdim`.

Establish `hφ : ∀ v, φ v = pairCoordsL C hP v` using `fun v => rfl`. Establish `hp : ∀ v : V × V, pPart (φ v) = C v.1`. Introduce `v`. Use extensionality with `i`. Simplify using `[hφ, pPart, pairCoordsL]`.

Establish `hq : ∀ (v : V × V) (x : EuclideanSpace ℝ (Fin n)), ⟪qPart (φ v), x⟫ = -∑ i, P (C.symm (EuclideanSpace.single i 1)) v.2 * x i`. Introduce `v x`. Simplify using `[hφ, qPart, pairCoordsL, PiLp.inner_apply, mul_comm]`. Establish `hq' : ∀ (v : V × V) (y : V), ⟪qPart (φ v), C y⟫ = -P y v.2`. Introduce `v y`.

Rewrite using `[hq, pair_expand C hP y v.2]`. Simplify using `[mul_comm]`. Establish `hCq : ∀ (v : V × V) (y : V), ⟪C y, qPart (φ v)⟫ = -P y v.2`. Introduce `v y`. Rewrite using `[real_inner_comm, hq']`.

Use `⟨C, φ, ?_, ?_⟩` and prove the remaining obligations. Introduce `v v'`. Simplify using `only [sympl, omega, hp, hCq, hq']`. Expand and normalize the polynomial expressions, which then agree. Introduce `v f`.

Use function extensionality and compare the values at `y`. Simplify using `only [schrF, rhoFun, phase, Function.comp_apply, map_add, hp, hq', hCq]`. Use `congr 1`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pairing_coords : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := by
  intro V _ _ _ P hP n hn
  let C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_fin).symm)
  have hdim : Module.finrank ℝ (V × V) = Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) := by
    simp [Module.finrank_prod, hn]
  let φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    LinearMap.linearEquivOfInjective (pairCoordsL C hP) (pairCoordsL_injective C hP) hdim
  have hφ : ∀ v, φ v = pairCoordsL C hP v := fun v => rfl
  have hp : ∀ v : V × V, pPart (φ v) = C v.1 := by
    intro v; ext i; simp [hφ, pPart, pairCoordsL]
  have hq : ∀ (v : V × V) (x : EuclideanSpace ℝ (Fin n)),
      ⟪qPart (φ v), x⟫ = -∑ i, P (C.symm (EuclideanSpace.single i 1)) v.2 * x i := by
    intro v x
    simp [hφ, qPart, pairCoordsL, PiLp.inner_apply, mul_comm]
  have hq' : ∀ (v : V × V) (y : V), ⟪qPart (φ v), C y⟫ = -P y v.2 := by
    intro v y
    rw [hq, pair_expand C hP y v.2]
    simp [mul_comm]
  have hCq : ∀ (v : V × V) (y : V), ⟪C y, qPart (φ v)⟫ = -P y v.2 := by
    intro v y
    rw [real_inner_comm, hq']
  refine ⟨C, φ, ?_, ?_⟩
  · intro v v'
    simp only [sympl, omega, hp, hCq, hq']
    ring
  · intro v f
    funext y
    simp only [schrF, rhoFun, phase, Function.comp_apply, map_add, hp, hq', hCq]
    congr 1
    congr 1
    push_cast
    ring
end GlobalTheory.ArchUniq
end

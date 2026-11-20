import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [h]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
private theorem algebraTensorModule_map_map_id_left_comm_of_comm {F L V B B' : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup B] [Module F B] [AddCommGroup B'] [Module F B']
    (c : B →ₗ[F] B') (f : V →ₗ[L] V) (u : B →ₗ[F] B) (u' : B' →ₗ[F] B')
    (h : ∀ b, c (u b) = u' (c b)) (x : V ⊗[F] B) :
    AlgebraTensorModule.map f u' (AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) c x) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) c (AlgebraTensorModule.map f u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [h]
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `F G B B' _ _ _ _ _ _ σ ψ σ' ψ' c hc hσ hψ L _ _ e hB V _ _ _ _ _ ρ hA`. Unfold `Bound at hB`. Unfold `admitted at hA ⊢`. Establish `hpow : ∀ k b, c ((ψ ^ k) b) = (ψ' ^ k) (c b)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro b`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `b`.

Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hψ]`. Set `m : V ⊗[F] B →ₗ[L] V ⊗[F] B'` to `AlgebraTensorModule.map LinearMap.id c`. Establish `hm_inj : Function.Injective m`. Establish `h1 : ⇑m = ⇑(LinearMap.lTensor V c)`. Use function extensionality and compare the values at `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [m]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Rewrite using `[h1]`.

Conclude with `Module.Flat.lTensor_preserves_injective_linearMap c hc`. Establish `hmaps : ∀ x ∈ Dinv σ ρ, m x ∈ Dinv σ' ρ`. Introduce `x hx`. Simplify using `only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢`. Introduce `g`.

Conclude with `(algebraTensorModule_map_map_id_left_comm_of_comm c (ρ g) (σ g) (σ' g) (hσ g) x).trans (congrArg m (hx g))`. Set `φ : Dinv σ ρ →ₗ[L] Dinv σ' ρ` to `m.restrict hmaps`. Establish `hφ : Function.Injective φ`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `hm_inj` to reduce the goal to its premises. Conclude with `congrArg Subtype.val hab`. Take `⟨hfin', hle⟩` from `hB V ρ`. Use `haveI : Module.Finite L (Dinv σ ρ) := Module.Finite.of_injective φ hφ`. Establish `hge : finrank L (Dinv σ ρ) ≤ finrank L (Dinv σ' ρ)` using `LinearMap.finrank_le_finrank_of_injective hφ`.

Establish `heq : finrank L (Dinv σ ρ) = finrank L (Dinv σ' ρ)` using `by omega`. Establish `hsurj : Function.Surjective φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hφ`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Introduce `q n T hT`. Unfold `AnnD at hT ⊢`.

Introduce `x hx`. Take `⟨y, hy⟩` from `hsurj ⟨x, hx⟩`. Establish `hxy : x = m y.1` using `(congrArg Subtype.val hy).symm`. Establish `key : ∀ j, (AlgebraTensorModule.map (T j) (ψ' ^ (n - j))) (m y.1) = m ((AlgebraTensorModule.map (T j) (ψ ^ (n - j))) y.1)` using `fun j => algebraTensorModule_map_map_id_left_comm_of_comm c (T j) (ψ ^ (n - j)) (ψ' ^ (n - j)) (hpow (n - j)) y.1`. Establish `h0` using `congrArg m (hT y.1 y.2)`.

Rewrite `h0` using `[map_zero, map_sum]`. Rewrite using `[hxy, ← h0]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[key j]`. Conclude with `(LinearMap.map_smul_of_tower m _ _).symm`.
-/
theorem UpperTheory.Gal.crystallineComparison.annPer_of :
    AnnPer := by
  intro F G B B' _ _ _ _ _ _ σ ψ σ' ψ' c hc hσ hψ L _ _ e hB V _ _ _ _ _ ρ hA
  unfold Bound at hB
  unfold admitted at hA ⊢
  have hpow : ∀ k b, c ((ψ ^ k) b) = (ψ' ^ k) (c b) := by
    intro k
    induction k with
    | zero => intro b; simp
    | succ k ih =>
      intro b
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hψ]
  let m : V ⊗[F] B →ₗ[L] V ⊗[F] B' := AlgebraTensorModule.map LinearMap.id c
  have hm_inj : Function.Injective m := by
    have h1 : ⇑m = ⇑(LinearMap.lTensor V c) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [m]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [h1]
    exact Module.Flat.lTensor_preserves_injective_linearMap c hc
  have hmaps : ∀ x ∈ Dinv σ ρ, m x ∈ Dinv σ' ρ := by
    intro x hx
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    exact (algebraTensorModule_map_map_id_left_comm_of_comm c (ρ g) (σ g) (σ' g) (hσ g) x).trans (congrArg m (hx g))
  let φ : Dinv σ ρ →ₗ[L] Dinv σ' ρ := m.restrict hmaps
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply hm_inj
    exact congrArg Subtype.val hab
  obtain ⟨hfin', hle⟩ := hB V ρ
  haveI : Module.Finite L (Dinv σ ρ) := Module.Finite.of_injective φ hφ
  have hge : finrank L (Dinv σ ρ) ≤ finrank L (Dinv σ' ρ) :=
    LinearMap.finrank_le_finrank_of_injective hφ
  have heq : finrank L (Dinv σ ρ) = finrank L (Dinv σ' ρ) := by omega
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hφ
  refine ⟨by omega, ?_⟩
  intro q n T hT
  unfold AnnD at hT ⊢
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hxy : x = m y.1 := (congrArg Subtype.val hy).symm
  have key : ∀ j, (AlgebraTensorModule.map (T j) (ψ' ^ (n - j))) (m y.1) =
      m ((AlgebraTensorModule.map (T j) (ψ ^ (n - j))) y.1) :=
    fun j => algebraTensorModule_map_map_id_left_comm_of_comm c (T j) (ψ ^ (n - j)) (ψ' ^ (n - j)) (hpow (n - j)) y.1
  have h0 := congrArg m (hT y.1 y.2)
  rw [map_zero, map_sum] at h0
  rw [hxy, ← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j]
  exact (LinearMap.map_smul_of_tower m _ _).symm

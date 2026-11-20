import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsBaseChangeStatement
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

/- English proof (translation)
Rewrite using `[map_smul, smul_assoc, smul_comm]`.
-/
theorem smul_smul_mapDR (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] (c : K) (x : L) (ω : DR k K) :
    (c • x) • mapDR k K L ω = x • mapDR k K L (c • ω) := by
  rw [map_smul, smul_assoc, smul_comm]

/- English proof (translation)
Introduce `k K L _ _ _ _ _ _ _ _ _`. Take `⟨hspan, hind⟩` from `GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L`. Establish `uniq : ∀ T T' : DR k L →ₗ[k] DR k K, IsTrDR k K L T → IsTrDR k K L T' → T = T'`. Introduce `T T' hT hT'`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations.

Take `⟨m, b, ω, rfl⟩` from `hspan y`. Simplify using `only [map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hT, hT']`. Set `e` to `Module.finBasis K L`. Set `n` to `Module.finrank K L`.

Set `φ : (Fin n → DR k K) →ₗ[k] DR k L` to `{ toFun := fun ω => ∑ j, e j • mapDR k K L (ω j) map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib] map_smul' := fun c a => by`. Simplify using `only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K c (a j), map_smul, algebraMap_smul, smul_comm] }`. Establish `hφ : Function.Bijective φ`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `ω hω`. Use function extensionality and compare the values at `j`. Conclude with `hind n e ω e.linearIndependent hω j`.

Introduce `y`. Take `⟨m, b, ω, rfl⟩` from `hspan y`. Use `⟨fun j => ∑ i, e.repr (b i) j • ω i, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∑ j, e j • mapDR k K L (∑ i, e.repr (b i) j • ω i) = _`. Simplify using `only [map_sum, Finset.smul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [← smul_smul_mapDR]`. Rewrite using `[← Finset.sum_smul, e.sum_repr]`. Set `ψ` to `(LinearEquiv.ofBijective φ hφ).symm`.

Set `g : (Fin n → DR k K) →ₗ[k] DR k K` to `{ toFun := fun ω => ∑ j, Algebra.trace K L (e j) • ω j map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib] map_smul' := fun c a => by`. Simplify using `only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm] }`. Establish `ex : IsTrDR k K L (g ∘ₗ ψ.toLinearMap)`.

Introduce `b ω`. Establish `hb : b • mapDR k K L ω = φ (fun j => e.repr b j • ω)`. Express the relevant statement in the definitionally equal form `_ = ∑ j, e j • mapDR k K L (e.repr b j • ω)`. Simplify using `only [← smul_smul_mapDR]`. Rewrite using `[← Finset.sum_smul, e.sum_repr]`.

Rewrite using `[LinearMap.comp_apply, hb]`. Establish `: ψ (φ (fun j => e.repr b j • ω)) = fun j => e.repr b j • ω` using `(LinearEquiv.ofBijective φ hφ).symm_apply_apply _`. Rewrite using `[LinearEquiv.coe_coe, this]`. Express the relevant statement in the definitionally equal form `∑ j, Algebra.trace K L (e j) • e.repr b j • ω = _`. Simplify using `only [smul_smul, ← Finset.sum_smul]`.

Use `congr 1`. Use `conv_rhs => rw [← e.sum_repr b]`. Simplify using `only [map_sum, map_smul, smul_eq_mul, mul_comm]`. Establish `htr : IsTrDR k K L (trDR k K L)`. Establish `h : ∃ T, IsTrDR k K L T` using `⟨_, ex⟩`.

Unfold `trDR`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`. Conclude with `⟨htr, fun T hT => uniq T _ hT htr⟩`.
-/
theorem trDR_isTrDR_unique : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L],
    IsTrDR k K L (trDR k K L) ∧ ∀ T, IsTrDR k K L T → T = trDR k K L := by
  intro k K L _ _ _ _ _ _ _ _ _
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L
  have uniq : ∀ T T' : DR k L →ₗ[k] DR k K, IsTrDR k K L T → IsTrDR k K L T' → T = T' := by
    intro T T' hT hT'
    refine LinearMap.ext fun y => ?_
    obtain ⟨m, b, ω, rfl⟩ := hspan y
    simp only [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hT, hT']
  let e := Module.finBasis K L
  let n := Module.finrank K L
  let φ : (Fin n → DR k K) →ₗ[k] DR k L :=
    { toFun := fun ω => ∑ j, e j • mapDR k K L (ω j)
      map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← algebraMap_smul K c (a j), map_smul, algebraMap_smul, smul_comm] }
  have hφ : Function.Bijective φ := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro ω hω
      funext j
      exact hind n e ω e.linearIndependent hω j
    · intro y
      obtain ⟨m, b, ω, rfl⟩ := hspan y
      refine ⟨fun j => ∑ i, e.repr (b i) j • ω i, ?_⟩
      change ∑ j, e j • mapDR k K L (∑ i, e.repr (b i) j • ω i) = _
      simp only [map_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [← smul_smul_mapDR]
      rw [← Finset.sum_smul, e.sum_repr]
  let ψ := (LinearEquiv.ofBijective φ hφ).symm
  let g : (Fin n → DR k K) →ₗ[k] DR k K :=
    { toFun := fun ω => ∑ j, Algebra.trace K L (e j) • ω j
      map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_comm] }
  have ex : IsTrDR k K L (g ∘ₗ ψ.toLinearMap) := by
    intro b ω
    have hb : b • mapDR k K L ω = φ (fun j => e.repr b j • ω) := by
      change _ = ∑ j, e j • mapDR k K L (e.repr b j • ω)
      simp only [← smul_smul_mapDR]
      rw [← Finset.sum_smul, e.sum_repr]
    rw [LinearMap.comp_apply, hb]
    have : ψ (φ (fun j => e.repr b j • ω)) = fun j => e.repr b j • ω :=
      (LinearEquiv.ofBijective φ hφ).symm_apply_apply _
    rw [LinearEquiv.coe_coe, this]
    change ∑ j, Algebra.trace K L (e j) • e.repr b j • ω = _
    simp only [smul_smul, ← Finset.sum_smul]
    congr 1
    conv_rhs => rw [← e.sum_repr b]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  have htr : IsTrDR k K L (trDR k K L) := by
    have h : ∃ T, IsTrDR k K L T := ⟨_, ex⟩
    unfold trDR
    rw [dif_pos h]
    exact h.choose_spec
  exact ⟨htr, fun T hT => uniq T _ hT htr⟩

end GlobalTheory.W1

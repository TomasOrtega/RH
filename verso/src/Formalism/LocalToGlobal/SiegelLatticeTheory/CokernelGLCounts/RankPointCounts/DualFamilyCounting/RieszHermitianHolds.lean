import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ProjectionIntoHolds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsBasisLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def SummandLoc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    ∀ X : Submodule K V, ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ Λ : Submodule (𝓞 K) V,
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      ∃ π : V →ₗ[K] V, (∀ v, π v ∈ X) ∧ (∀ x ∈ X, π x = x) ∧ ∀ y ∈ Λ, π y ∈ Λ

def RieszH : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ f : V →ₗ[K] K, ∃ x : V, ∀ y, h x y = f y

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]`.
-/
theorem coe_algebraMap_OF (t : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 K) t : 𝓞 K) : K) = algebraMap F K (t : F) := by
  change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]

/- English proof (translation)
Use `h𝔭` as an intermediate fact. Take `⟨t, ht, hty⟩` from `(LocalSpans.mem_locF 𝔭 L y).1 hy`. Take `⟨u, hu, huv⟩` from `(LocalSpans.mem_locF 𝔭 _ v).1 hv`. Establish `H` using `(mem_dual_iff.1 huv.2) _ hty`. Use `(LocalSpans.mem_locF 𝔭 _ _).2 ⟨t * u, fun hm => (h𝔭.mem_or_mem hm).elim ht hu, ?_⟩` and prove the remaining obligations.

Establish `hst : starRingEnd K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)`. Establish `e` using `coe_algebraMap_OF (K := K) t`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _ at e`. Rewrite using `[e, starRingEnd_apply]`. Conclude with `(hF _).2 ⟨_, rfl⟩`.

Rewrite `H` using `[form_ozmul_right, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hst, algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) (h y v)]`. Rewrite using `[map_mul, mul_smul, smul_comm]`. Conclude with `H`.
-/
theorem form_mem_locF_of (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) {v y : V}
    (hv : v ∈ locF 𝔭 (dualIn h X L)) (hy : y ∈ locF 𝔭 L) : h y v ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have := h𝔭
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 L y).1 hy
  obtain ⟨u, hu, huv⟩ := (LocalSpans.mem_locF 𝔭 _ v).1 hv
  have H := (mem_dual_iff.1 huv.2) _ hty
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨t * u, fun hm => (h𝔭.mem_or_mem hm).elim ht hu, ?_⟩
  have hst : starRingEnd K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) := by
    have e := coe_algebraMap_OF (K := K) t
    change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _ at e
    rw [e, starRingEnd_apply]
    exact (hF _).2 ⟨_, rfl⟩
  rw [form_ozmul_right, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, hst, algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) (h y v)] at H
  rw [map_mul, mul_smul, smul_comm]
  exact H

/- English proof (translation)
Introduce `K V _ _ _ _ _ h _ hnd f`. Set `b` to `Module.finBasis K V`. Set `Φ : (Fin (finrank K V) → K) →ₗ[K] Module.Dual K V` to `{ toFun := fun c => ∑ i, c i • h (b i) map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }`. Establish `hΦ : ∀ c, h (∑ i, star (c i) • b i) = Φ c`. Introduce `c`.

Simplify using `[Φ, map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star]`. Establish `hinj : Function.Injective Φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Establish `hx : (∑ i, star (c i) • b i) = 0`.

Apply `hnd` to reduce the goal to its premises. Introduce `y`. Rewrite using `[hΦ, hc]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `i`.

Use `Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => star (c i)) hx i` as an intermediate fact. Simplify using `using this`. Establish `hsurj : Function.Surjective Φ`. Use `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj` and prove the remaining obligations. Rewrite using `[Module.finrank_fin_fun, Subspace.dual_finrank_eq]`.

Take `⟨c, hc⟩` from `hsurj f`. Conclude with `⟨∑ i, star (c i) • b i, fun y => by rw [hΦ, hc]⟩`.
-/
theorem riesz_hermitian_holds : RieszH := by
  intro K V _ _ _ _ _ h _ hnd f
  classical
  let b := Module.finBasis K V
  let Φ : (Fin (finrank K V) → K) →ₗ[K] Module.Dual K V :=
    { toFun := fun c => ∑ i, c i • h (b i)
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  have hΦ : ∀ c, h (∑ i, star (c i) • b i) = Φ c := by
    intro c
    simp [Φ, map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star]
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hx : (∑ i, star (c i) • b i) = 0 := by
      apply hnd
      intro y
      rw [hΦ, hc]
      rfl
    funext i
    have := Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => star (c i)) hx i
    simpa using this
  have hsurj : Function.Surjective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_fin_fun, Subspace.dual_finrank_eq]
  obtain ⟨c, hc⟩ := hsurj f
  exact ⟨∑ i, star (c i) • b i, fun y => by rw [hΦ, hc]⟩

/- English proof (translation)
Establish `hu0 : (u : F) ≠ 0`. Introduce `e`. Apply `hu` to reduce the goal to its premises. Establish `: u = 0` using `RingOfIntegers.ext (by simpa using e)`. Rewrite using `[this]`.

Conclude with `𝔭.zero_mem`. Establish `hc0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) ≠ 0`. Establish `e` using `coe_algebraMap_OF (K := K) u`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) = _ at e`. Rewrite using `[e]`.

Conclude with `(map_ne_zero _).2 hu0`. Establish `h1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) • v ∈ X`. Rewrite using `[algebraMap_smul]`. Conclude with `hv`. Use `X.smul_mem (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u))⁻¹ h1` as an intermediate fact.

Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Then use the resulting hypothesis.
-/
theorem mem_of_smul_mem {X : Submodule K V} {𝔭 : Ideal (𝓞 F)} {u : 𝓞 F} (hu : u ∉ 𝔭) {v : V}
    (hv : algebraMap (𝓞 F) (𝓞 K) u • v ∈ X) : v ∈ X := by
  have hu0 : (u : F) ≠ 0 := by
    intro e
    apply hu
    have : u = 0 := RingOfIntegers.ext (by simpa using e)
    rw [this]
    exact 𝔭.zero_mem
  have hc0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) ≠ 0 := by
    have e := coe_algebraMap_OF (K := K) u
    change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) = _ at e
    rw [e]
    exact (map_ne_zero _).2 hu0
  have h1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) • v ∈ X := by
    rw [algebraMap_smul]
    exact hv
  have := X.smul_mem (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u))⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

/- English proof (translation)
Introduce `K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd X Y hc hXY L hL 𝔭 h𝔭 Λ hΛ0 hΛd hΛX v hv`. Establish `hp : 𝔭.IsPrime` using `h𝔭.isPrime`. Take `⟨π, hπX, hπid, hπΛ⟩` from `hS K F V X 𝔭 h𝔭 Λ hΛ0`. Take `⟨x, hx⟩` from `hR K V h hs hnd ((h v).comp π)`. Establish `key : ∀ y, h y x = h (π y) v`.

Introduce `y`. Rewrite using `[← hs.eq x y, hx y, LinearMap.comp_apply, hs.eq v (π y)]`. Establish `hvX : v ∈ X`. Take `⟨u, hu, huv⟩` from `(LocalSpans.mem_locF 𝔭 _ v).1 hv`. Conclude with `mem_of_smul_mem hu huv.1`.

Establish `hxΛ : x ∈ Λ`. Rewrite using `[← hΛd]`. Use `show ∀ y ∈ Λ, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)`. Introduce `y hy`. Rewrite using `[key]`.

Establish `: π y ∈ locF 𝔭 L`. Rewrite using `[← hΛX]`. Conclude with `⟨hπΛ y hy, hπX y⟩`. Conclude with `form_mem_locF_of hF hp hv this`. Use `⟨x, hxΛ, ?_⟩` and prove the remaining obligations.

Use `set w := X.projection Y hc x - v with hw`. Establish `hwX : w ∈ X` using `X.sub_mem (Submodule.projection_apply_mem hc x) hvX`. Establish `hw0 : w = 0`. Apply `hnd` to reduce the goal to its premises. Introduce `z`.

Establish `ez` using `Submodule.projection_add_projection_eq_self hc z`. Rewrite using `[← ez, map_add]`. Establish `h1 : h w (Y.projection X hc.symm z) = 0` using `hXY w hwX _ (Submodule.projection_apply_mem _ z)`. Establish `hzX : X.projection Y hc z ∈ X` using `Submodule.projection_apply_mem hc z`. Establish `ex` using `Submodule.projection_add_projection_eq_self hc x`.

Establish `e3 : h (X.projection Y hc z) (X.projection Y hc x) = h (X.projection Y hc z) x` using `by conv_rhs => rw [← ex]`. Rewrite using `[map_add, hXY _ hzX _ (Submodule.projection_apply_mem _ x), add_zero]`. Establish `h2 : h (X.projection Y hc z) w = 0`. Rewrite using `[hw, map_sub, e3, key, hπid _ hzX, sub_self]`. Rewrite using `[h1, add_zero, ← hs.eq (X.projection Y hc z) w, h2, map_zero]`.

Conclude with `sub_eq_zero.mp hw0`.
-/
theorem projOnto_of (hS : SummandLoc) (hR : RieszH) : ProjOnto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd X Y hc hXY L hL 𝔭 h𝔭 Λ hΛ0 hΛd hΛX v hv
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨π, hπX, hπid, hπΛ⟩ := hS K F V X 𝔭 h𝔭 Λ hΛ0
  obtain ⟨x, hx⟩ := hR K V h hs hnd ((h v).comp π)
  have key : ∀ y, h y x = h (π y) v := by
    intro y
    rw [← hs.eq x y, hx y, LinearMap.comp_apply, hs.eq v (π y)]
  have hvX : v ∈ X := by
    obtain ⟨u, hu, huv⟩ := (LocalSpans.mem_locF 𝔭 _ v).1 hv
    exact mem_of_smul_mem hu huv.1
  have hxΛ : x ∈ Λ := by
    rw [← hΛd]
    show ∀ y ∈ Λ, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
    intro y hy
    rw [key]
    have : π y ∈ locF 𝔭 L := by
      rw [← hΛX]
      exact ⟨hπΛ y hy, hπX y⟩
    exact form_mem_locF_of hF hp hv this
  refine ⟨x, hxΛ, ?_⟩
  set w := X.projection Y hc x - v with hw
  have hwX : w ∈ X := X.sub_mem (Submodule.projection_apply_mem hc x) hvX
  have hw0 : w = 0 := by
    apply hnd
    intro z
    have ez := Submodule.projection_add_projection_eq_self hc z
    rw [← ez, map_add]
    have h1 : h w (Y.projection X hc.symm z) = 0 := hXY w hwX _ (Submodule.projection_apply_mem _ z)
    have hzX : X.projection Y hc z ∈ X := Submodule.projection_apply_mem hc z
    have ex := Submodule.projection_add_projection_eq_self hc x
    have e3 : h (X.projection Y hc z) (X.projection Y hc x) = h (X.projection Y hc z) x := by
      conv_rhs => rw [← ex]
      rw [map_add, hXY _ hzX _ (Submodule.projection_apply_mem _ x), add_zero]
    have h2 : h (X.projection Y hc z) w = 0 := by
      rw [hw, map_sub, e3, key, hπid _ hzX, sub_self]
    rw [h1, add_zero, ← hs.eq (X.projection Y hc z) w, h2, map_zero]
  exact sub_eq_zero.mp hw0

end Formalism.L2.SG.Pf.G6

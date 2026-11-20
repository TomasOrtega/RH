import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

noncomputable section

namespace GlobalTheory.Desc.FlatInter

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩`. Consider the case `tmul m n => exact ⟨1, fun _ => m, fun _ => n, by simp⟩`. Consider the case `add x y hx hy`. Take `⟨n, u, r, rfl⟩` from `hx`.

Take `⟨m, u', r', rfl⟩` from `hy`. Conclude with `⟨n + m, Fin.append u u', Fin.append r r', by simp [Fin.sum_univ_add]⟩`.
-/
theorem exists_fin_sum {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : M ⊗[R] N) : ∃ (n : ℕ) (u : Fin n → M) (r : Fin n → N), x = ∑ i, u i ⊗ₜ[R] r i := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul m n => exact ⟨1, fun _ => m, fun _ => n, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, u, r, rfl⟩ := hx
    obtain ⟨m, u', r', rfl⟩ := hy
    exact ⟨n + m, Fin.append u u', Fin.append r r', by simp [Fin.sum_univ_add]⟩

/- English proof (translation)
Use `Fintype.ofFinite J` as an intermediate fact. Set `π : K →ₗ[R] ∀ j, K ⧸ N j` to `LinearMap.pi fun j => (N j).mkQ`. Establish `hex : Function.Exact (⨅ j, N j).subtype π`. Rewrite using `[LinearMap.exact_iff]`. Simplify using `[π, LinearMap.ker_pi]`.

Establish `hex'` using `Module.Flat.rTensor_exact R₁ hex`. Rewrite using `[← LinearMap.exact_iff.mp hex']`. Rewrite using `[LinearMap.mem_ker]`. Set `e` to `TensorProduct.piLeft R R₁ (fun j => K ⧸ N j)`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use function extensionality and compare the values at `j`. Establish `hj : LinearMap.proj j ∘ₗ e.toLinearMap ∘ₗ π.rTensor R₁ = (N j).mkQ.rTensor R₁`. Use extensionality with `x r`. Simplify using `[π, e]`.

Use `congrArg (fun f => f T) hj` as an intermediate fact. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_proj, Function.eval] at this`. Rewrite using `[this, Pi.zero_apply, ← LinearMap.mem_ker, rTensor_mkQ]`. Conclude with `hT j`.
-/
theorem mem_range_iInf {R K R₁ : Type} [CommRing R] [AddCommGroup K] [Module R K] [AddCommGroup R₁] [Module R R₁]
    [Module.Flat R R₁] {J : Type} [Finite J] (N : J → Submodule R K) (T : K ⊗[R] R₁)
    (hT : ∀ j, T ∈ LinearMap.range ((N j).subtype.rTensor R₁)) :
    T ∈ LinearMap.range ((⨅ j, N j).subtype.rTensor R₁) := by
  classical
  have := Fintype.ofFinite J
  let π : K →ₗ[R] ∀ j, K ⧸ N j := LinearMap.pi fun j => (N j).mkQ
  have hex : Function.Exact (⨅ j, N j).subtype π := by
    rw [LinearMap.exact_iff]
    simp [π, LinearMap.ker_pi]
  have hex' := Module.Flat.rTensor_exact R₁ hex
  rw [← LinearMap.exact_iff.mp hex']
  rw [LinearMap.mem_ker]
  let e := TensorProduct.piLeft R R₁ (fun j => K ⧸ N j)
  apply e.injective
  rw [map_zero]
  funext j
  have hj : LinearMap.proj j ∘ₗ e.toLinearMap ∘ₗ π.rTensor R₁ = (N j).mkQ.rTensor R₁ := by
    ext x r
    simp [π, e]
  have := congrArg (fun f => f T) hj
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_proj,
    Function.eval] at this
  rw [this, Pi.zero_apply, ← LinearMap.mem_ker, rTensor_mkQ]
  exact hT j

def tensorMap {R R₁ K L : Type} [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K]
    (θ : K →+* L) (c : R₁ →+* L) (hc : ∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a)) :
    K ⊗[R] R₁ →+ L :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun r => c r * θ u) (fun a b => by simp [add_mul]))
      (fun a b => by ext r; simp [mul_add]))
    (fun a u r => by
      simp only [AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, hc]
      ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tensorMap_tmul {R R₁ K L : Type} [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁]
    [Algebra R K] (θ : K →+* L) (c : R₁ →+* L) (hc : ∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a))
    (u : K) (r : R₁) : tensorMap θ c hc (u ⊗ₜ[R] r) = c r * θ u := rfl

end GlobalTheory.Desc.FlatInter

open GlobalTheory.Desc.FlatInter in

/- English proof (translation)
Introduce `R R₁ K L _ _ _ _ _ _ _ θ c hc hinj J _ _ N`. Set `Φ` to `tensorMap θ c hc`. Establish `hΦ : ∀ x, Φ x = 0 → x = 0`. Introduce `x hx`. Take `⟨n, u, r, rfl⟩` from `exists_fin_sum x`.

Apply `hinj n u r` to reduce the goal to its premises. Simplify `hx` using `[Φ, map_sum, tensorMap_tmul]`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, r, t, ht, rfl⟩`.

Use `Set.mem_iInter.2 fun j => ⟨n, r, t, fun i => Set.image_mono (Set.iInter_subset _ j) (ht i), rfl⟩` and prove the remaining obligations. Introduce `hv`. Establish `key : ∀ j, ∃ T ∈ LinearMap.range ((N j).subtype.rTensor R₁), Φ T = v`. Introduce `j`. Take `⟨n, r, t, ht, rfl⟩` from `Set.mem_iInter.1 hv j`.

Use `choose u hu hut using ht`. Use `⟨(N j).subtype.rTensor R₁ (∑ i, (⟨u i, hu i⟩ : N j) ⊗ₜ[R] r i), LinearMap.mem_range_self _ _, ?_⟩` and prove the remaining obligations. Simplify using `[Φ, map_sum, tensorMap_tmul, hut]`. Use `choose T hT hTv using key`. Take `⟨j₀⟩` from `‹Nonempty J›`.

Establish `heq : ∀ j, T j = T j₀` using `fun j => by`. Use `hΦ (T j - T j₀) (by rw [map_sub, hTv, hTv, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.1 this`. Take `⟨y, hy⟩` from `mem_range_iInf N (T j₀) fun j => heq j ▸ hT j`. Take `⟨n, w, s, rfl⟩` from `exists_fin_sum y`.

Use `⟨n, s, fun i => θ (w i), fun i => ⟨w i, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_iInter.2 fun j => (Submodule.mem_iInf N).1 (w i).2 j`. Rewrite using `[← hTv j₀, ← hy]`. Simplify using `[Φ, map_sum, tensorMap_tmul]`.
-/
theorem GlobalTheory.Desc.spanBy_iInter_of_flat : ∀ (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L), (∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a)) → (∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) → ∀ (J : Type) [Finite J] [Nonempty J] (N : J → Submodule R K), spanBy c (θ '' ⋂ j, (N j : Set K)) = ⋂ j, spanBy c (θ '' (N j : Set K)) := by
  intro R R₁ K L _ _ _ _ _ _ _ θ c hc hinj J _ _ N
  let Φ := tensorMap θ c hc
  have hΦ : ∀ x, Φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨n, u, r, rfl⟩ := exists_fin_sum x
    apply hinj n u r
    simpa [Φ, map_sum, tensorMap_tmul] using hx
  ext v
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    refine Set.mem_iInter.2 fun j => ⟨n, r, t, fun i => Set.image_mono (Set.iInter_subset _ j) (ht i), rfl⟩
  · intro hv
    have key : ∀ j, ∃ T ∈ LinearMap.range ((N j).subtype.rTensor R₁), Φ T = v := by
      intro j
      obtain ⟨n, r, t, ht, rfl⟩ := Set.mem_iInter.1 hv j
      choose u hu hut using ht
      refine ⟨(N j).subtype.rTensor R₁ (∑ i, (⟨u i, hu i⟩ : N j) ⊗ₜ[R] r i), LinearMap.mem_range_self _ _, ?_⟩
      simp [Φ, map_sum, tensorMap_tmul, hut]
    choose T hT hTv using key
    obtain ⟨j₀⟩ := ‹Nonempty J›
    have heq : ∀ j, T j = T j₀ := fun j => by
      have := hΦ (T j - T j₀) (by rw [map_sub, hTv, hTv, sub_self])
      exact sub_eq_zero.1 this
    obtain ⟨y, hy⟩ := mem_range_iInf N (T j₀) fun j => heq j ▸ hT j
    obtain ⟨n, w, s, rfl⟩ := exists_fin_sum y
    refine ⟨n, s, fun i => θ (w i), fun i => ⟨w i, ?_, rfl⟩, ?_⟩
    · exact Set.mem_iInter.2 fun j => (Submodule.mem_iInf N).1 (w i).2 j
    · rw [← hTv j₀, ← hy]
      simp [Φ, map_sum, tensorMap_tmul]

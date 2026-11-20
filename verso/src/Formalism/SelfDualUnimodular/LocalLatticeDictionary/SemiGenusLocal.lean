import Mathlib
import Formalism.SelfDualUnimodular.LocalLatticeDictionary.SelfDualRestr

noncomputable section

open NumberField Module

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGC

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA Formalism.L2.SG.Pf.LatDictZ.Z0.SGB

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Establish `he0 : e ≠ 0` using `by rintro rfl; simp at he`. Establish `hX0 : X ≠ 0` using `by rintro rfl; simp at hXe; exact he hXe.symm`. Set `f : (K ∙ e) →ₗ[K] V` to `(LinearMap.toSpanSingleton K V X) ∘ₗ ((LinearEquiv.coord K V e he0 : (K ∙ e) ≃ₗ[K] K) : (K ∙ e) →ₗ[K] K)`. Establish `hf : ∀ u, f u = LinearEquiv.coord K V e he0 u • X` using `fun u => rfl`. Establish `hu : ∀ u : (K ∙ e), (u : V) = LinearEquiv.coord K V e he0 u • e` using `fun u => (LinearEquiv.coord_apply_smul K V e he0 u).symm`.

Establish `hinj : Function.Injective f`. Introduce `u v huv`. Rewrite `huv` using `[hf, hf]`. Use `smul_left_injective K hX0 huv` as an intermediate fact. Conclude with `(LinearEquiv.coord K V e he0).injective this`.

Establish `hiso : ∀ u v : (K ∙ e), h (f u) (f v) = h u v`. Introduce `u v`. Rewrite using `[hf, hf, hu u, hu v]`. Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hXe]`. Take `⟨g, hg, hgf⟩` from `witt_extension_theorem K V h (fun x y => hsy.eq x y) hnd (K ∙ e) f hinj hiso`.

Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Use `hgf ⟨e, Submodule.mem_span_singleton_self e⟩` as an intermediate fact. Rewrite using `[this, hf, LinearEquiv.coord_self, one_smul]`.
-/
theorem exists_isom_vec {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hsy : h.IsSymm) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {e X : V}
    (he : h e e ≠ 0) (hXe : h X X = h e e) :
    ∃ τ : V ≃ₗ[K] V, (∀ x y, h (τ x) (τ y) = h x y) ∧ τ e = X := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hX0 : X ≠ 0 := by rintro rfl; simp at hXe; exact he hXe.symm
  let f : (K ∙ e) →ₗ[K] V := (LinearMap.toSpanSingleton K V X) ∘ₗ
    ((LinearEquiv.coord K V e he0 : (K ∙ e) ≃ₗ[K] K) : (K ∙ e) →ₗ[K] K)
  have hf : ∀ u, f u = LinearEquiv.coord K V e he0 u • X := fun u => rfl
  have hu : ∀ u : (K ∙ e), (u : V) = LinearEquiv.coord K V e he0 u • e := fun u =>
    (LinearEquiv.coord_apply_smul K V e he0 u).symm
  have hinj : Function.Injective f := by
    intro u v huv
    rw [hf, hf] at huv
    have := smul_left_injective K hX0 huv
    exact (LinearEquiv.coord K V e he0).injective this
  have hiso : ∀ u v : (K ∙ e), h (f u) (f v) = h u v := by
    intro u v
    rw [hf, hf, hu u, hu v]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hXe]
  obtain ⟨g, hg, hgf⟩ := witt_extension_theorem K V h (fun x y => hsy.eq x y) hnd (K ∙ e) f hinj hiso
  refine ⟨g, hg, ?_⟩
  have := hgf ⟨e, Submodule.mem_span_singleton_self e⟩
  rw [this, hf, LinearEquiv.coord_self, one_smul]

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `V _ _ _ hn h hsy hnd M₁ M₂ h1 h2`. Establish `hs : ∀ u v, star (h u v) = h v u` using `fun u v => hsy.eq u v`. Distinguish the cases in `hV : ∃ x₀ : V, x₀ ≠ 0`.

Use `swap`. Use `push Not at hV`. Use `⟨LinearEquiv.refl K V, fun _ _ => rfl, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hV x]`. Conclude with `⟨fun _ => M₂.zero_mem, fun _ => M₁.zero_mem⟩`.

Take `⟨x₀, hx₀⟩` from `hV`. Take `⟨e, heM, heu⟩` from `exists_unit_norm hK hp hsy hnd h1 x₀ hx₀`. Take `⟨X, hXM, hXe⟩` from `exists_norm_eq hK hp hsy hnd h2 e heu`. Establish `hXu : IsUnitIn (locRing p) (h X X)` using `hXe ▸ heu`. Establish `hX0 : h X X ≠ 0` using `hXu.1`.

Take `⟨τ, hτ, hτe⟩` from `exists_isom_vec hsy hnd heu.1 hXe`. Establish `hN1` using `selfDual_map h1 τ hτ`. Establish `hXN : X ∈ M₁.comap (τ.symm : V →ₗ[K] V).toAddMonoidHom`. Express the relevant statement in the definitionally equal form `τ.symm X ∈ M₁`. Rewrite using `[← hτe, LinearEquiv.symm_apply_apply]`.

Conclude with `heM`. Establish `hdim : finrank K (LinearMap.ker (h X)) < n`. Establish `h1'` using `LinearMap.finrank_range_add_finrank_ker (h X)`. Establish `hpos : 0 < finrank K (LinearMap.range (h X))`. Rewrite using `[Module.finrank_pos_iff_exists_ne_zero]`.

Conclude with `⟨⟨h X X, X, rfl⟩, fun h0 => hX0 (congrArg Subtype.val h0)⟩`. Use linear arithmetic over natural numbers and integers. Take `⟨g', hg', hmem'⟩` from `ih _ hdim (LinearMap.ker (h X)) rfl (restr h (LinearMap.ker (h X))) (symm_restr hsy _) (nondeg_restr hs hnd hX0) _ _ (selfDual_restr hs hN1 hXN hXu) (selfDual_restr hs h2 hXM hXu)`. Use `⟨τ.trans (extE h X hX0 g'), ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`.

Rewrite using `[LinearEquiv.trans_apply, LinearEquiv.trans_apply, extE_isom h X hX0 hs g' (fun u v => hg' u v), hτ]`. Introduce `x`. Rewrite using `[LinearEquiv.trans_apply]`. Establish `e1 : x ∈ M₁ ↔ τ x ∈ M₁.comap (τ.symm : V →ₗ[K] V).toAddMonoidHom`. Express the relevant statement in the definitionally equal form `_ ↔ τ.symm (τ x) ∈ M₁`.

Rewrite using `[LinearEquiv.symm_apply_apply]`. Rewrite using `[e1, mem_iff_split hN1 hXN hXu, mem_iff_split h2 hXM hXu, extE_apply, coef_ext, proj_ext]`. Conclude with `and_congr Iff.rfl (hmem' (proj h X hX0 (τ x)))`.
-/
theorem core {p : Ideal (𝓞 K)} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hp : p.IsMaximal) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V], finrank K V = n →
    ∀ (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → (∀ x, (∀ y, h x y = 0) → x = 0) →
    ∀ M₁ M₂ : AddSubgroup V, IsSelfDualMod (locRing p) h M₁ → IsSelfDualMod (locRing p) h M₂ →
      ∃ g : V ≃ₗ[K] V, (∀ x y, h (g x) (g y) = h x y) ∧ ∀ x, x ∈ M₁ ↔ g x ∈ M₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn h hsy hnd M₁ M₂ h1 h2
  have hs : ∀ u v, star (h u v) = h v u := fun u v => hsy.eq u v
  by_cases hV : ∃ x₀ : V, x₀ ≠ 0
  swap
  · push Not at hV
    refine ⟨LinearEquiv.refl K V, fun _ _ => rfl, fun x => ?_⟩
    rw [hV x]
    exact ⟨fun _ => M₂.zero_mem, fun _ => M₁.zero_mem⟩
  obtain ⟨x₀, hx₀⟩ := hV
  obtain ⟨e, heM, heu⟩ := exists_unit_norm hK hp hsy hnd h1 x₀ hx₀
  obtain ⟨X, hXM, hXe⟩ := exists_norm_eq hK hp hsy hnd h2 e heu
  have hXu : IsUnitIn (locRing p) (h X X) := hXe ▸ heu
  have hX0 : h X X ≠ 0 := hXu.1
  obtain ⟨τ, hτ, hτe⟩ := exists_isom_vec hsy hnd heu.1 hXe
  have hN1 := selfDual_map h1 τ hτ
  have hXN : X ∈ M₁.comap (τ.symm : V →ₗ[K] V).toAddMonoidHom := by
    change τ.symm X ∈ M₁
    rw [← hτe, LinearEquiv.symm_apply_apply]
    exact heM
  have hdim : finrank K (LinearMap.ker (h X)) < n := by
    have h1' := LinearMap.finrank_range_add_finrank_ker (h X)
    have hpos : 0 < finrank K (LinearMap.range (h X)) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨⟨h X X, X, rfl⟩, fun h0 => hX0 (congrArg Subtype.val h0)⟩
    omega
  obtain ⟨g', hg', hmem'⟩ := ih _ hdim (LinearMap.ker (h X)) rfl (restr h (LinearMap.ker (h X)))
    (symm_restr hsy _) (nondeg_restr hs hnd hX0) _ _ (selfDual_restr hs hN1 hXN hXu)
    (selfDual_restr hs h2 hXM hXu)
  refine ⟨τ.trans (extE h X hX0 g'), ?_, ?_⟩
  · intro x y
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, extE_isom h X hX0 hs g' (fun u v => hg' u v), hτ]
  · intro x
    rw [LinearEquiv.trans_apply]
    have e1 : x ∈ M₁ ↔ τ x ∈ M₁.comap (τ.symm : V →ₗ[K] V).toAddMonoidHom := by
      change _ ↔ τ.symm (τ x) ∈ M₁
      rw [LinearEquiv.symm_apply_apply]
    rw [e1, mem_iff_split hN1 hXN hXu, mem_iff_split h2 hXM hXu, extE_apply, coef_ext, proj_ext]
    exact and_congr Iff.rfl (hmem' (proj h X hX0 (τ x)))

/- English proof (translation)
Introduce `K _ _ _ V _ _ _ h hK hsy hnd p hp M₁ M₂ h1 h2`. Take `⟨g, hg, hm⟩` from `core hK hp _ V rfl h hsy hnd M₁ M₂ h1 h2`. Conclude with `⟨g, hg, hm⟩`.
-/
theorem semi_genus_local : SemiGenusLoc := by
  intro K _ _ _ V _ _ _ h hK hsy hnd p hp M₁ M₂ h1 h2
  obtain ⟨g, hg, hm⟩ := core hK hp _ V rfl h hsy hnd M₁ M₂ h1 h2
  exact ⟨g, hg, hm⟩

end Formalism.L2.SG.Pf.LatDictZ.Z0.SGC

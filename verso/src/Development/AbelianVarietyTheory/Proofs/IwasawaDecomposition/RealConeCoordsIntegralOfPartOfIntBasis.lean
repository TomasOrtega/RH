import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

/- English proof (translation)
Introduce `X _ m u hu hpb β t h`. Take `⟨n, b, hb⟩` from `hpb`. Establish `hpt : ∀ a y, (β a y : ℝ) = ∑ i, t i * (u i a y : ℝ)` using `fun a y => by`. Use `LinearMap.congr_fun₂ h a y` as an intermediate fact. Simplify `this` using `[LinearMap.sum_apply, toReal_apply]`.

Establish `hsym : ∀ a y, β a y = β y a` using `fun a y => by`. Establish `h1` using `hpt a y`. Establish `h2` using `hpt y a`. Establish `: (β a y : ℝ) = β y a`. Rewrite using `[h1, h2]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [((mem_balForms_int).1 (hu i)) a y]`. Conclude with `this` after adjusting the coercions. Set `β' : balForms (id : ℤ → ℤ) X` to `⟨β, (mem_balForms_int).2 hsym⟩`. Use `set s := b.repr β' with hs`. Establish `hexp : ∀ a y, β a y = ∑ j, s j * ((b j : LinearMap.BilinForm ℤ X) a y)` using `fun a y => by`.

Establish `h0` using `congrArg (fun γ : balForms (id : ℤ → ℤ) X => (γ : LinearMap.BilinForm ℤ X) a y) (b.sum_repr β')`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h0`. Conclude with `h0.symm`. Set `e : Fin m ⊕ Fin n → ℝ` to `Sum.elim t 0`. Set `c : Fin m ⊕ Fin n → ℝ` to `fun j => (s j : ℝ) - e j`.

Establish `hc : ∑ j, c j • toReal ((balForms (id : ℤ → ℤ) X).subtype (b j)) = 0`. Use `LinearMap.ext₂ fun a y => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, Submodule.subtype_apply, smul_eq_mul, LinearMap.zero_apply, c, sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[sub_eq_zero]`. Establish `e1 : (∑ j, (s j : ℝ) * ((b j : LinearMap.BilinForm ℤ X) a y : ℝ)) = β a y`.

Rewrite using `[hexp a y]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[e1, hpt a y, Fintype.sum_sum_type]`. Simplify using `[e, hb]`.

Introduce `i`. Use `⟨s (Sum.inl i), ?_⟩` and prove the remaining obligations. Use `sum_mul_eq_zero_of_sum_toReal (X := X) (j := (balForms (id : ℤ → ℤ) X).subtype) Subtype.val_injective (b.coord (Sum.inl i)) hc` as an intermediate fact. Simplify using `only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] at this`. Rewrite `this` using `[Finset.sum_eq_single (Sum.inl i)]`.

Simplify using `[c, e] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `j _ hj`. Simplify using `[hj]`. Simplify using the standard rewrite rules.
-/
theorem GlobalTheory.cone_coords_int_of_isPartOfBasis : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i, u i ∈ balForms (id : ℤ → ℤ) X), IsPartOfBasis (fun i => (⟨u i, hu i⟩ : balForms (id : ℤ → ℤ) X)) → ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z := by
  intro X _ m u hu hpb β t h
  obtain ⟨n, b, hb⟩ := hpb
  have hpt : ∀ a y, (β a y : ℝ) = ∑ i, t i * (u i a y : ℝ) := fun a y => by
    have := LinearMap.congr_fun₂ h a y
    simpa [LinearMap.sum_apply, toReal_apply] using this
  have hsym : ∀ a y, β a y = β y a := fun a y => by
    have h1 := hpt a y
    have h2 := hpt y a
    have : (β a y : ℝ) = β y a := by
      rw [h1, h2]
      exact Finset.sum_congr rfl fun i _ => by rw [((mem_balForms_int).1 (hu i)) a y]
    exact_mod_cast this
  let β' : balForms (id : ℤ → ℤ) X := ⟨β, (mem_balForms_int).2 hsym⟩
  set s := b.repr β' with hs
  have hexp : ∀ a y, β a y = ∑ j, s j * ((b j : LinearMap.BilinForm ℤ X) a y) := fun a y => by
    have h0 := congrArg (fun γ : balForms (id : ℤ → ℤ) X => (γ : LinearMap.BilinForm ℤ X) a y) (b.sum_repr β')
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h0
    exact h0.symm
  let e : Fin m ⊕ Fin n → ℝ := Sum.elim t 0
  let c : Fin m ⊕ Fin n → ℝ := fun j => (s j : ℝ) - e j
  have hc : ∑ j, c j • toReal ((balForms (id : ℤ → ℤ) X).subtype (b j)) = 0 := by
    refine LinearMap.ext₂ fun a y => ?_
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, Submodule.subtype_apply, smul_eq_mul,
      LinearMap.zero_apply, c, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    have e1 : (∑ j, (s j : ℝ) * ((b j : LinearMap.BilinForm ℤ X) a y : ℝ)) = β a y := by
      rw [hexp a y]; push_cast; rfl
    rw [e1, hpt a y, Fintype.sum_sum_type]
    simp [e, hb]
  intro i
  refine ⟨s (Sum.inl i), ?_⟩
  have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := (balForms (id : ℤ → ℤ) X).subtype) Subtype.val_injective
    (b.coord (Sum.inl i)) hc
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] at this
  rw [Finset.sum_eq_single (Sum.inl i)] at this
  · simp [c, e] at this
    linarith
  · intro j _ hj; simp [hj]
  · simp

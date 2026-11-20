import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationSymmetry

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.WeilDeligne UpperTheory.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ n w A h χ y hy`. Take `⟨b, rfl, hN, hρ⟩` from `hy`. Establish `key : ∀ c : Weil h, (hc : deg c = 0) → (∀ k, χ k c.1 = 1) → LocalGlobalAboveLAlt.Triv (WD.mk b) c`. Introduce `c hc hk`. Establish `hmem : (c : G E Ω) ∈ Ine A` using `deg_eq_zero_iff.1 hc`.

Establish `hρ1 : b.ρ c = 1`. Use `hρ ⟨c, hmem⟩` as an intermediate fact. Establish `hinc : ineIncl h ⟨c, hmem⟩ = c` using `rfl`. Rewrite `this` using `[hinc]`. Rewrite using `[this]`.

Simplify using `only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hk, Units.val_one, Matrix.diagonal_one, Matrix.toLin'_one]`. Both sides reduce to the same expression. Use `show (WD.mk b).charPol c = (Polynomial.X - 1) ^ (WD.mk b).lpDim`. Rewrite using `[WD.charPol_mk, WD.lpDim_mk, hρ1, LinearMap.charpoly_one, Module.finrank_fin_fun]`. Use `⟨fun s t => key _ ?_ (fun k => ?_), (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hN⟩` and prove the remaining obligations.

Rewrite using `[commutatorElement_def, deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]`. Expand and normalize the polynomial expressions, which then agree. Use `map_commutatorElement ((χ k).comp (Weil h).subtype) s t` as an intermediate fact. Conclude with `this.trans (commutatorElement_eq_one_iff_mul_comm.2 (mul_comm (((χ k).comp (Weil h).subtype) s) _))`.
-/
theorem UpperTheory.V.Z.Desc.P.typeTor :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω) (h : IsPlaceOver A w) (χ : Fin n → G E Ω →* ℂˣ) (y : WD h),
    Hi.IsTypeWD h (fun i => (χ i).comp (Ine (F := E) A).subtype) y → Z.Win.Gd y := by
  intro E Ω _ _ _ _ _ n w A h χ y hy
  obtain ⟨b, rfl, hN, hρ⟩ := hy
  have key : ∀ c : Weil h, (hc : deg c = 0) → (∀ k, χ k c.1 = 1) → LocalGlobalAboveLAlt.Triv (WD.mk b) c := by
    intro c hc hk
    have hmem : (c : G E Ω) ∈ Ine A := deg_eq_zero_iff.1 hc
    have hρ1 : b.ρ c = 1 := by
      have := hρ ⟨c, hmem⟩
      have hinc : ineIncl h ⟨c, hmem⟩ = c := rfl
      rw [hinc] at this
      rw [this]
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hk, Units.val_one,
        Matrix.diagonal_one, Matrix.toLin'_one]
      rfl
    show (WD.mk b).charPol c = (Polynomial.X - 1) ^ (WD.mk b).lpDim
    rw [WD.charPol_mk, WD.lpDim_mk, hρ1, LinearMap.charpoly_one, Module.finrank_fin_fun]
  refine ⟨fun s t => key _ ?_ (fun k => ?_), (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hN⟩
  · rw [commutatorElement_def, deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]
    ring
  · have := map_commutatorElement ((χ k).comp (Weil h).subtype) s t
    exact this.trans (commutatorElement_eq_one_iff_mul_comm.2 (mul_comm (((χ k).comp (Weil h).subtype) s) _))

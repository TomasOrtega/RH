import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace GlobalTheory.DepthZeroWildInertiaEigenvalues

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.PRep ValuativeRel in

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h rc ⟨a, ha, ε, _, H⟩ n σ _ ⟨v, hv, hfix⟩ t ht hw`. Establish `: (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible` using `Valuation.Compatible.ofValuation _`. Establish `he` using `isEquiv (valuation (w.adicCompletion E)) (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))`. Take `⟨e⟩` from `GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ`. Establish `h1 : fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) ≠ ⊥`.

Rewrite using `[Submodule.ne_bot_iff]`. Use `⟨e.toLinearEquiv.symm v, ?_, fun h0 => hv (e.toLinearEquiv.symm.map_eq_zero_iff.1 h0)⟩` and prove the remaining obligations. Establish `key : ∀ κ ∈ KOne (w.adicCompletion E) (Fin n), σ.cl.rep.ρ κ (e.toLinearEquiv.symm v) = e.toLinearEquiv.symm v`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Apply `e.toLinearEquiv.injective` to reduce the goal to its premises.

Establish `hi` using `LinearMap.congr_fun (e.isIntertwining' (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation (w.adicCompletion E)).integer) _) g)) (e.toLinearEquiv.symm v)`. Use `hi.trans ?_` and prove the remaining obligations. Establish `e3 : e.toLinearMap (e.toLinearEquiv.symm v) = v` using `e.toLinearEquiv.apply_symm_apply v`. Rewrite using `[LinearMap.comp_apply, e3, LinearEquiv.apply_symm_apply]`. Use `hfix _ fun i j => ?_` and prove the remaining obligations.

Rewrite using `[← he.lt_one_iff_lt_one]`. Establish `hg'` using `congrArg (fun x : GL (Fin n) _ => x.val i j) (MonoidHom.mem_ker.1 hg)`. Establish `hm : IsLocalRing.residue _ ((g.val - 1) i j) = 0`. Simplify using `only [Matrix.sub_apply, map_sub, sub_eq_zero]`. Use `hg'.trans ?_` and prove the remaining obligations.

Simplify using `[Matrix.one_apply, apply_ite]`. Rewrite `hm` using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]`. Use `hm using 2` and compare the differences between its conclusion and the goal. Simplify using `[Matrix.one_apply, apply_ite]`. Apply the tactic sequence `split_ifs <;> rfl`.

Introduce `κ`. Simplify using `using key κ κ.2`. Take `⟨m, b, hb, hb'⟩` from `(H.depth _).1 h1`. Establish `hd` using `H.dim (cls σ)`. Rewrite `hd`, the goal using `[← hb]`.

Rewrite `hd` using `[WD.lpDim_mk]`. Establish `hW : Formalism.MainNotions.BlochKatoReduction.IsWild A ((ineIncl h ⟨t, ht⟩ : Weil h) : G E Ω)`. Use `⟨ht, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h2` using `hw y hy`. Establish `h0 : A.valuation y ≠ 0` using `by simpa using hy`.

Establish `e2 : t y / y - 1 = (t y - y) / y` using `by field_simp`. Rewrite `h2` using `[e2, map_div₀, div_lt_one₀ (zero_lt_iff.mpr h0)]`. Conclude with `h2`. Rewrite using `[WD.inePol_of_mem_Ine _ ht, WD.charPol_mk, hb' _ hW, LinearMap.charpoly_one, hd]`.
-/
theorem main : GlobalTheory.Published.DepthZeroWild := by
  intro E Ω _ _ _ _ _ A w h rc ⟨a, ha, ε, _, H⟩ n σ _ ⟨v, hv, hfix⟩ t ht hw
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  obtain ⟨e⟩ := GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ
  have h1 : fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨e.toLinearEquiv.symm v, ?_, fun h0 => hv (e.toLinearEquiv.symm.map_eq_zero_iff.1 h0)⟩
    have key : ∀ κ ∈ KOne (w.adicCompletion E) (Fin n), σ.cl.rep.ρ κ (e.toLinearEquiv.symm v) = e.toLinearEquiv.symm v := by
      rintro _ ⟨g, hg, rfl⟩
      apply e.toLinearEquiv.injective
      have hi := LinearMap.congr_fun (e.isIntertwining' (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation (w.adicCompletion E)).integer) _) g)) (e.toLinearEquiv.symm v)
      refine hi.trans ?_
      have e3 : e.toLinearMap (e.toLinearEquiv.symm v) = v := e.toLinearEquiv.apply_symm_apply v
      rw [LinearMap.comp_apply, e3, LinearEquiv.apply_symm_apply]
      refine hfix _ fun i j => ?_
      rw [← he.lt_one_iff_lt_one]
      have hg' := congrArg (fun x : GL (Fin n) _ => x.val i j) (MonoidHom.mem_ker.1 hg)
      have hm : IsLocalRing.residue _ ((g.val - 1) i j) = 0 := by
        simp only [Matrix.sub_apply, map_sub, sub_eq_zero]
        refine hg'.trans ?_
        simp [Matrix.one_apply, apply_ite]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hm
      convert hm using 2
      simp [Matrix.one_apply, apply_ite]
      split_ifs <;> rfl
    intro κ
    simpa using key κ κ.2
  obtain ⟨m, b, hb, hb'⟩ := (H.depth _).1 h1
  have hd := H.dim (cls σ)
  rw [← hb] at hd ⊢
  rw [WD.lpDim_mk] at hd
  have hW : Formalism.MainNotions.BlochKatoReduction.IsWild A ((ineIncl h ⟨t, ht⟩ : Weil h) : G E Ω) := by
    refine ⟨ht, fun y hy => ?_⟩
    have h2 := hw y hy
    have h0 : A.valuation y ≠ 0 := by simpa using hy
    have e2 : t y / y - 1 = (t y - y) / y := by field_simp
    rw [e2, map_div₀, div_lt_one₀ (zero_lt_iff.mpr h0)] at h2
    exact h2
  rw [WD.inePol_of_mem_Ine _ ht, WD.charPol_mk, hb' _ hW, LinearMap.charpoly_one, hd]

end GlobalTheory.DepthZeroWildInertiaEigenvalues

end

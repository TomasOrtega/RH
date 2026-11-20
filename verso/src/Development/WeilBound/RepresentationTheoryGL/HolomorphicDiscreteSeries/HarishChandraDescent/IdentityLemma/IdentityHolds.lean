import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrime
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace IdentityBound

/- English proof (translation)
Establish `hp : pOf ε ≤ n` using `(Finset.card_filter_le _ _).trans (by simp)`. Establish `hq : qOf ε ≤ n` using `(Finset.card_filter_le _ _).trans (by simp)`. Establish `hp' : (pOf ε : ℝ) ≤ n` using `by exact_mod_cast hp`. Establish `hq' : (qOf ε : ℝ) ≤ n` using `by exact_mod_cast hq`. Establish `h0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`.

Establish `h1 : (0 : ℝ) ≤ pOf ε` using `Nat.cast_nonneg _`. Establish `h2 : (0 : ℝ) ≤ qOf ε` using `Nat.cast_nonneg _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem npq_le (n : ℕ) (ε : Fin n → Bool) : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ (n : ℝ) ^ 3 := by
  have hp : pOf ε ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  have hq : qOf ε ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  have hp' : (pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (0 : ℝ) ≤ pOf ε := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ qOf ε := Nat.cast_nonneg _
  calc (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ (n : ℝ) * n * n := by gcongr
    _ = (n : ℝ) ^ 3 := by ring

end IdentityBound

/- English proof (translation)
Introduce `n ε H _ _ _ ρ hρ mu h hmu hgap hh V hV hNo H' _ _ _ σ hσ`. Establish `hD` using `isDerivedOn_smE hρ`. Establish `hE : IsGlRep (smE ε ρ)` using `hD.glRep`. Establish `hU : IsInfUnitary ε (smE ε ρ)` using `isInfUnitary_of_isDerivedOn hρ hD`. Establish `h0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`.

Establish `hstd : StdGap ε mu` using `⟨hmu.1, h, hgap, by`. Use `IdentityBound.npq_le n ε` as an intermediate fact. Use the proof step `nlinarith⟩`. Establish `hc₁ : ∀ v ∈ V, casimir (smE ε ρ) v = (casVal mu : ℂ) • v` using `casimir_eq_casVal_of_no hmu.1 hE hU hV hNo`. Establish `hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = ρ k v` using `kStable_of_isKStableSub hρ hD V hV.1 hV.2.1`.

Establish `hV₁0 : V ≠ ⊥`. Take `⟨w, hw, hw0, -⟩` from `hV.2.2.2`. Introduce `hb`. Rewrite `hw` using `[hb, Submodule.mem_bot]`. Conclude with `hw0 hw`.

Establish `hσU : IsURepOn (UJset ε) σ` using `hσ.2.2.1`. Establish `hcas : CasOnSmooth ε mu σ`. Establish `h2n : 2 * (n : ℝ) < h` using `by nlinarith [pow_nonneg h0 3]`. Conclude with `(ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap n ε mu hmu h ((mir_gapAtLeast_iff ε mu h).2 hgap) h2n H' σ hσ).1`. Take `⟨V₂, hV₂, hV₂0, hVK₂, hc₂⟩` from `arb_datum hσ hcas`.

Establish `hD₂` using `isDerivedOn_smE hσU`. Take `⟨Uq, hUq⟩` from `data_unitary_equiv hstd hρ hD hV hc₁ hVK₁ hV₁0 hσU hD₂ hV₂ hc₂ hVK₂ hV₂0`. Establish `htop : closGen (smE ε σ) V₂ = ⊤` using `data_closGen_eq_top hstd hσU hD₂ hV₂ hc₂ hVK₂ hσ.2.2.2.1 hV₂0`. Set `e₂ : H' ≃ₗᵢ[ℂ] closGen (smE ε σ) V₂` to `(LinearIsometryEquiv.ofTop (p := closGen (smE ε σ) V₂) (hp := htop)).symm`. Set `j : H' →L[ℂ] H` to `(closGen (smE ε ρ) V).subtypeL.comp (Uq.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp e₂.toContinuousLinearEquiv.toContinuousLinearMap)`.

Establish `hj : ∀ x, j x = ((Uq.symm (e₂ x) : closGen (smE ε ρ) V) : H)` using `fun x => rfl`. Establish `he₂ : ∀ x, ((e₂ x : closGen (smE ε σ) V₂) : H') = x` using `fun x => by show (((LinearIsometryEquiv.ofTop (p := closGen (smE ε σ) V₂) (hp := htop)).symm x : closGen (smE ε σ) V₂) : H') = x`. Use `(LinearIsometryEquiv.ofTop (p := closGen (smE ε σ) V₂) (hp := htop)).apply_symm_apply x` as an intermediate fact. Conclude with `this`. Use `⟨j, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hj0`. Use `hσ.2.1` as an intermediate fact. Take `⟨x, hx⟩` from `exists_ne (0 : H')`. Apply `hx` to reduce the goal to its premises. Establish `h1 : j x = 0` using `by rw [hj0]; rfl`.

Rewrite `h1` using `[hj]`. Establish `h2 : Uq.symm (e₂ x) = 0` using `Subtype.ext h1`. Establish `h3 : e₂ x = 0` using `by simpa using congrArg Uq h2`. Establish `h4` using `congrArg (fun y : closGen (smE ε σ) V₂ => (y : H')) h3`. Simplify `h4` using `[he₂]`.

Introduce `g hg x set y : closGen (smE ε ρ) V := Uq.symm (e₂ x) with hy`. Establish `hmem : ρ g (y : H) ∈ closGen (smE ε ρ) V` using `closGen_stable hstd hρ hD hV hc₁ hVK₁ g hg _ y.2`. Set `y' : closGen (smE ε ρ) V` to `⟨ρ g (y : H), hmem⟩`. Establish `key` using `hUq g hg y' y rfl`. Establish `e1 : ((Uq y : closGen (smE ε σ) V₂) : H') = x`.

Rewrite using `[hy, LinearIsometryEquiv.apply_symm_apply, he₂]`. Rewrite `key` using `[e1]`. Establish `e2 : e₂ (σ g x) = Uq y'` using `Subtype.ext (by rw [he₂, key])`. Rewrite using `[hj, hj, e2, LinearIsometryEquiv.symm_apply_apply]`.
-/
theorem identity_holds : Ident := by
  intro n ε H _ _ _ ρ hρ mu h hmu hgap hh V hV hNo H' _ _ _ σ hσ
  have hD := isDerivedOn_smE hρ
  have hE : IsGlRep (smE ε ρ) := hD.glRep
  have hU : IsInfUnitary ε (smE ε ρ) := isInfUnitary_of_isDerivedOn hρ hD
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hstd : StdGap ε mu := ⟨hmu.1, h, hgap, by
    have := IdentityBound.npq_le n ε
    nlinarith⟩
  have hc₁ : ∀ v ∈ V, casimir (smE ε ρ) v = (casVal mu : ℂ) • v :=
    casimir_eq_casVal_of_no hmu.1 hE hU hV hNo
  have hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = ρ k v :=
    kStable_of_isKStableSub hρ hD V hV.1 hV.2.1
  have hV₁0 : V ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hV.2.2.2
    intro hb
    rw [hb, Submodule.mem_bot] at hw
    exact hw0 hw
  have hσU : IsURepOn (UJset ε) σ := hσ.2.2.1
  have hcas : CasOnSmooth ε mu σ := by
    have h2n : 2 * (n : ℝ) < h := by nlinarith [pow_nonneg h0 3]
    exact (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap n ε mu hmu h ((mir_gapAtLeast_iff ε mu h).2 hgap) h2n H' σ hσ).1
  obtain ⟨V₂, hV₂, hV₂0, hVK₂, hc₂⟩ := arb_datum hσ hcas
  have hD₂ := isDerivedOn_smE hσU
  obtain ⟨Uq, hUq⟩ := data_unitary_equiv hstd hρ hD hV hc₁ hVK₁ hV₁0 hσU hD₂ hV₂ hc₂ hVK₂ hV₂0
  have htop : closGen (smE ε σ) V₂ = ⊤ :=
    data_closGen_eq_top hstd hσU hD₂ hV₂ hc₂ hVK₂ hσ.2.2.2.1 hV₂0

  let e₂ : H' ≃ₗᵢ[ℂ] closGen (smE ε σ) V₂ := (LinearIsometryEquiv.ofTop (p := closGen (smE ε σ) V₂) (hp := htop)).symm
  let j : H' →L[ℂ] H := (closGen (smE ε ρ) V).subtypeL.comp (Uq.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    e₂.toContinuousLinearEquiv.toContinuousLinearMap)
  have hj : ∀ x, j x = ((Uq.symm (e₂ x) : closGen (smE ε ρ) V) : H) := fun x => rfl
  have he₂ : ∀ x, ((e₂ x : closGen (smE ε σ) V₂) : H') = x := fun x => by
    show (((LinearIsometryEquiv.ofTop (p := closGen (smE ε σ) V₂) (hp := htop)).symm x : closGen (smE ε σ) V₂) : H') = x
    have := (LinearIsometryEquiv.ofTop (p := closGen (smE ε σ) V₂) (hp := htop)).apply_symm_apply x
    exact this
  refine ⟨j, ?_, ?_⟩
  · intro hj0
    have := hσ.2.1
    obtain ⟨x, hx⟩ := exists_ne (0 : H')
    apply hx
    have h1 : j x = 0 := by rw [hj0]; rfl
    rw [hj] at h1
    have h2 : Uq.symm (e₂ x) = 0 := Subtype.ext h1
    have h3 : e₂ x = 0 := by simpa using congrArg Uq h2
    have h4 := congrArg (fun y : closGen (smE ε σ) V₂ => (y : H')) h3
    simpa [he₂] using h4
  · intro g hg x

    set y : closGen (smE ε ρ) V := Uq.symm (e₂ x) with hy
    have hmem : ρ g (y : H) ∈ closGen (smE ε ρ) V :=
      closGen_stable hstd hρ hD hV hc₁ hVK₁ g hg _ y.2
    let y' : closGen (smE ε ρ) V := ⟨ρ g (y : H), hmem⟩
    have key := hUq g hg y' y rfl
    have e1 : ((Uq y : closGen (smE ε σ) V₂) : H') = x := by
      rw [hy, LinearIsometryEquiv.apply_symm_apply, he₂]
    rw [e1] at key
    have e2 : e₂ (σ g x) = Uq y' := Subtype.ext (by rw [he₂, key])
    rw [hj, hj, e2, LinearIsometryEquiv.symm_apply_apply]

end PositivityTheory.RgHe3

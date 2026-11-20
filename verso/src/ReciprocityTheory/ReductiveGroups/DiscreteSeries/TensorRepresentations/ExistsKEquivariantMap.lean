import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.CartanKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Apply the tactic sequence `cases dual <;> simp only [shiftF, lowK, cond] <;> abel`.
-/
theorem lowWeight_shifted (dual : Bool) (ε : Fin n → Bool) (lam : Fin n → ℝ) (s : Fin n) :
    lowK ε (shiftF dual lam s) = cond dual (lowK ε lam - Pi.single s 1) (lowK ε lam + Pi.single s 1) := by
  cases dual <;> simp only [shiftF, lowK, cond] <;> abel

/- English proof (translation)
Take `⟨T'', φ, hφ, -, -⟩` from `HW.kRepPiece n ε R μ x hx hh`. Take `⟨ψ, hψ, -, -⟩` from `HW.kType_unique T' T''`. Use `⟨(Submodule.subtype _).comp (φ.toLinearEquiv.toLinearMap.comp ψ.toLinearEquiv.toLinearMap), ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h1` using `LinearMap.congr_fun h T'.w`.

Simplify using `only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.coe_subtype, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, ZeroMemClass.coe_eq_zero, LinearIsometryEquiv.map_eq_zero_iff] at h1`. Establish `h2` using `T'.w_norm`. Rewrite `h2` using `[h1, norm_zero]`. Conclude with `zero_ne_one h2`. Introduce `k v`.

Simplify using `only [LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]`. Rewrite using `[hψ, hφ]`.
-/
theorem exists_kEquivariant_map {ε : Fin n → Bool} (R : HW.KRep ε) {μ : Fin n → ℝ} (x : R.V) (hx : x ≠ 0)
    (hh : Formalism.REAL.KHighest ε R.units μ x) (T' : S7.KType ε μ) :
    ∃ f : T'.V →ₗ[ℂ] R.V, f ≠ 0 ∧ ∀ (k : S7.KG ε) (v : T'.V), f (T'.op k v) = R.op k (f v) := by
  obtain ⟨T'', φ, hφ, -, -⟩ := HW.kRepPiece n ε R μ x hx hh
  obtain ⟨ψ, hψ, -, -⟩ := HW.kType_unique T' T''
  refine ⟨(Submodule.subtype _).comp (φ.toLinearEquiv.toLinearMap.comp ψ.toLinearEquiv.toLinearMap), ?_, ?_⟩
  · intro h
    have h1 := LinearMap.congr_fun h T'.w
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, ZeroMemClass.coe_eq_zero,
      LinearIsometryEquiv.map_eq_zero_iff] at h1
    have h2 := T'.w_norm
    rw [h1, norm_zero] at h2
    exact zero_ne_one h2
  · intro k v
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rw [hψ, hφ]

/- English proof (translation)
Rewrite `hxh` using `[← HW.tensKRep_units T ρ dρ hc hd]`. Take `⟨f, hf, hfK⟩` from `exists_kEquivariant_map (HW.tensKRep T ρ dρ hc hd) x hx hxh T'`. Set `g : T'.V →ₗ[ℂ] PiLp 2 (fun _ : ι => T.V)` to `f`. Establish `hg : ∀ k v, g (T'.op k v) = HW.tensOp T ρ k (g v)` using `fun k v => hfK k v`. Use `⟨(WithLp.linearEquiv 2 ℂ (ι → T.V)).toLinearMap ∘ₗ g, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `hf` to reduce the goal to its premises. Use extensionality with `v`. Establish `h1` using `LinearMap.congr_fun h v`. Establish `h2 : g v = 0` using `by simpa using h1`.

Conclude with `h2`. Introduce `k v`. Use function extensionality and compare the values at `c`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[hg]`.

Simplify using `[HW.tensOp_apply]`.
-/
theorem tensor_unitary_rep {ε : Fin n → Bool} {Λ μ : Fin n → ℝ} (T : S7.KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : S7.KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : S7.KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → S7.KG ε, (∀ t : ℝ, S7.toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0)
    (T' : S7.KType ε μ) (x : PiLp 2 (fun _ : ι => T.V)) (hx : x ≠ 0)
    (hxh : Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) μ x) :
    ∃ ι₀ : T'.V →ₗ[ℂ] (ι → T.V), ι₀ ≠ 0 ∧
      ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) =
        fun c => ∑ d, ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) c d • T.op k (ι₀ v d) := by
  rw [← HW.tensKRep_units T ρ dρ hc hd] at hxh
  obtain ⟨f, hf, hfK⟩ := exists_kEquivariant_map (HW.tensKRep T ρ dρ hc hd) x hx hxh T'
  let g : T'.V →ₗ[ℂ] PiLp 2 (fun _ : ι => T.V) := f
  have hg : ∀ k v, g (T'.op k v) = HW.tensOp T ρ k (g v) := fun k v => hfK k v
  refine ⟨(WithLp.linearEquiv 2 ℂ (ι → T.V)).toLinearMap ∘ₗ g, ?_, ?_⟩
  · intro h
    apply hf
    ext v
    have h1 := LinearMap.congr_fun h v
    have h2 : g v = 0 := by simpa using h1
    exact h2
  · intro k v
    funext c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hg]
    simp [HW.tensOp_apply]

/- English proof (translation)
Establish `hdom` using `(HW.kTypeIntDom n ε Λ' T').2`. Consider the cases of `dual with`. Consider the case `false`. Establish `hΛ' : Λ' = Λ + HW.stdWt n s` using `hΛ`. Substitute `hΛ'` using the available equality.

Take `⟨x, hx, hxh⟩` from `(HW.pieriStd n ε Λ T).2.2 s hdom`. Conclude with `tensor_unitary_rep T (HW.stdRho ε) LinearMap.id (HW.stdRho_cont ε) (HW.stdRho_hasDeriv ε) T' x hx hxh`. Consider the case `true`. Establish `hΛ' : Λ' = Λ + HW.dualWt n s`. Rewrite using `[hΛ]`.

Simplify using `only [cond, HW.dualWt, sub_eq_add_neg]`. Substitute `hΛ'` using the available equality. Take `⟨x, hx, hxh⟩` from `(HW.pieriDual n ε Λ T).2.2 s hdom`. Rewrite `hxh` using `[← HW.dualD_units]`. Conclude with `tensor_unitary_rep T (HW.rhoDual ε) HW.dualD (HW.continuous_rhoDual ε) (HW.hasDeriv_rhoDual ε) T' x hx hxh`.
-/
theorem pieri_standard_embedding (dual : Bool) {ε : Fin n → Bool} {Λ Λ' : Fin n → ℝ} (T : S7.KType ε Λ) (T' : S7.KType ε Λ')
    (s : Fin n) (hΛ : Λ' = cond dual (Λ - Pi.single s 1) (Λ + Pi.single s 1)) :
    ∃ ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V), ι₀ ≠ 0 ∧
      ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) =
        fun c => ∑ d, (cond dual (star (S7.toMK k c d)) (S7.toMK k c d)) • T.op k (ι₀ v d) := by
  have hdom := (HW.kTypeIntDom n ε Λ' T').2
  cases dual with
  | false =>
    have hΛ' : Λ' = Λ + HW.stdWt n s := hΛ
    subst hΛ'
    obtain ⟨x, hx, hxh⟩ := (HW.pieriStd n ε Λ T).2.2 s hdom
    exact tensor_unitary_rep T (HW.stdRho ε) LinearMap.id (HW.stdRho_cont ε) (HW.stdRho_hasDeriv ε) T' x hx hxh
  | true =>
    have hΛ' : Λ' = Λ + HW.dualWt n s := by
      rw [hΛ]; simp only [cond, HW.dualWt, sub_eq_add_neg]
    subst hΛ'
    obtain ⟨x, hx, hxh⟩ := (HW.pieriDual n ε Λ T).2.2 s hdom
    rw [← HW.dualD_units] at hxh
    exact tensor_unitary_rep T (HW.rhoDual ε) HW.dualD (HW.continuous_rhoDual ε) (HW.hasDeriv_rhoDual ε) T' x hx hxh

end ReciprocityTheory.ChartRestriction.DS

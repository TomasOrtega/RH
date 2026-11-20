import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

/- English proof (translation)
Unfold `UpperTheory.V.Af.Tw.Descend`. Introduce `F Ω B _ _ _ _ _ _ _ _ art hart ψ hψc hdiag hfin`. Establish `hq` using `hart.quot`. Establish `hker : art.ker ≤ ψ.ker`. Rewrite using `[hart.ker]`.

Use `Subgroup.topologicalClosure_minimal _ ?_ ?_` and prove the remaining obligations. Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hdiag k`. Introduce `z hz`.

Unfold `infConn at hz`. Take `⟨w, _, rfl⟩` from `hz`. Conclude with `hfin _ rfl`. Conclude with `isClosed_singleton.preimage hψc`. Set `fC : C(Ideles F, Gab F Ω)` to `⟨art, hq.continuous⟩`.

Set `gC : C(Ideles F, B)` to `⟨ψ, hψc⟩`. Establish `hfact : Function.FactorsThrough gC fC`. Introduce `a b hab`. Establish `hab' : a / b ∈ art.ker`. Rewrite using `[MonoidHom.mem_ker, map_div]`.

Conclude with `div_eq_one.2 hab`. Use `hker hab'` as an intermediate fact. Rewrite `this` using `[MonoidHom.mem_ker, map_div]`. Conclude with `div_eq_one.1 this`. Establish `hQ : Topology.IsQuotientMap fC` using `hq.isQuotientMap`.

Set `κC` to `hQ.lift gC hfact`. Establish `hκ : ∀ x, κC (art x) = ψ x` using `fun x => DFunLike.congr_fun (hQ.lift_comp gC hfact) x`. Set `κ₀ : Gab F Ω →* B` to `MonoidHom.mk' κC (by`. Introduce `a b`. Take `⟨x, rfl⟩` from `hq.surjective a`.

Take `⟨y, rfl⟩` from `hq.surjective b`. Rewrite using `[← map_mul, hκ, hκ, hκ, map_mul])`. Use `⟨κ₀.comp (GlobalTheory.HeckeGal.toAb F Ω), ?_, ?_⟩` and prove the remaining obligations. Conclude with `κC.continuous.comp (by first`. Consider the case `exact QuotientGroup.continuous_mk`.

Consider the case `exact continuous_quot_mk)`. Introduce `x σ h show κC (GlobalTheory.HeckeGal.toAb F Ω σ) = ψ x`. Rewrite using `[← h, hκ]`.
-/
theorem UpperTheory.V.Af.Tw.descend :
    UpperTheory.V.Af.Tw.Descend := by
  unfold UpperTheory.V.Af.Tw.Descend
  intro F Ω B _ _ _ _ _ _ _ _ art hart ψ hψc hdiag hfin
  have hq := hart.quot
  have hker : art.ker ≤ ψ.ker := by
    rw [hart.ker]
    refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · refine sup_le ?_ ?_
      · rintro _ ⟨k, rfl⟩
        exact hdiag k
      · intro z hz
        unfold infConn at hz
        obtain ⟨w, _, rfl⟩ := hz
        exact hfin _ rfl
    · exact isClosed_singleton.preimage hψc
  let fC : C(Ideles F, Gab F Ω) := ⟨art, hq.continuous⟩
  let gC : C(Ideles F, B) := ⟨ψ, hψc⟩
  have hfact : Function.FactorsThrough gC fC := by
    intro a b hab
    have hab' : a / b ∈ art.ker := by
      rw [MonoidHom.mem_ker, map_div]
      exact div_eq_one.2 hab
    have := hker hab'
    rw [MonoidHom.mem_ker, map_div] at this
    exact div_eq_one.1 this
  have hQ : Topology.IsQuotientMap fC := hq.isQuotientMap
  let κC := hQ.lift gC hfact
  have hκ : ∀ x, κC (art x) = ψ x := fun x => DFunLike.congr_fun (hQ.lift_comp gC hfact) x
  let κ₀ : Gab F Ω →* B := MonoidHom.mk' κC (by
    intro a b
    obtain ⟨x, rfl⟩ := hq.surjective a
    obtain ⟨y, rfl⟩ := hq.surjective b
    rw [← map_mul, hκ, hκ, hκ, map_mul])
  refine ⟨κ₀.comp (GlobalTheory.HeckeGal.toAb F Ω), ?_, ?_⟩
  · exact κC.continuous.comp (by
      first
        | exact QuotientGroup.continuous_mk
        | exact continuous_quot_mk)
  · intro x σ h
    show κC (GlobalTheory.HeckeGal.toAb F Ω σ) = ψ x
    rw [← h, hκ]

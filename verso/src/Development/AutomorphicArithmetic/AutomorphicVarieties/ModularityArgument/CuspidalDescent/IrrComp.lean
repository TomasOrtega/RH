import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.LocGL UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Take `rfl : m = n` from `by simpa using hn`. Take `⟨φ₀⟩` from `GlobalTheory.LocGL.nonempty_equiv_multiProd_one σ.smooth (GlobalTheory.SmGL.stdBlocks (fun _ : Fin 1 => m) hn) (fun a i => Fin.ext (by rw [GlobalTheory.SmGL.stdBlocks_val]; obtain rfl := Subsingleton.elim a 0; simp))`. Take `⟨hd, h1⟩` from `hs`. Take `⟨hd', h2⟩` from `GlobalTheory.LocGL.isSpeh_one (cl ρ)`. Take `⟨e⟩` from `h1.unique h2`.

Take `⟨u⟩` from `GlobalTheory.CuspRep.LocUniq.isLocComp_unique P w τ ρ hτ hρ`. Set `q : τ.ρ.Equiv (locProd (N` to `fun _ : Fin 1 => m) hn w fun _ => σ) := (u.trans ((IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e)).trans φ₀`. Take `⟨-, f, f0, fm, fe⟩` from `hc`. Use `⟨τ.irred, f ∘ₗ q.toLinearMap, fun h0 => f0 (LinearMap.ext fun v => ?_), fun v => fm _, fun x v => ?_⟩` and prove the remaining obligations. Take `⟨u', rfl⟩` from `q.toLinearEquiv.surjective v`.

Conclude with `LinearMap.congr_fun h0 u'`. Conclude with `(congrArg f (LinearMap.congr_fun (q.isIntertwining' _) v)).trans (fe x _)`.
-/
private theorem irreducible_component_of_speh {E : Type} [Field E] [NumberField E] [IsCMField E] {n m : ℕ} (U : Submodule ℂ (UA E n → ℂ))
    (hn : ∑ _i : Fin 1, m = n) (P : CuspSub E n) (w : HeightOneSpectrum (𝓞 E))
    (ρ : SmIrr (GL (Fin n) (w.adicCompletion E))) (σ : SmIrr (GL (Fin m) (w.adicCompletion E)))
    (hρ : P.IsLocComp w ρ) (hs : IsSpeh (cl ρ) 1 σ.ρ)
    (hc : IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => m) hn w fun _ => σ))
    (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (hτ : P.IsLocComp w τ) :
    IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  obtain rfl : m = n := by simpa using hn
  obtain ⟨φ₀⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one σ.smooth
    (GlobalTheory.SmGL.stdBlocks (fun _ : Fin 1 => m) hn)
    (fun a i => Fin.ext (by rw [GlobalTheory.SmGL.stdBlocks_val]; obtain rfl := Subsingleton.elim a 0; simp))
  obtain ⟨hd, h1⟩ := hs
  obtain ⟨hd', h2⟩ := GlobalTheory.LocGL.isSpeh_one (cl ρ)
  obtain ⟨e⟩ := h1.unique h2
  obtain ⟨u⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique P w τ ρ hτ hρ
  let q : τ.ρ.Equiv (locProd (N := fun _ : Fin 1 => m) hn w fun _ => σ) :=
    (u.trans ((IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e)).trans φ₀
  obtain ⟨-, f, f0, fm, fe⟩ := hc
  refine ⟨τ.irred, f ∘ₗ q.toLinearMap, fun h0 => f0 (LinearMap.ext fun v => ?_), fun v => fm _, fun x v => ?_⟩
  · obtain ⟨u', rfl⟩ := q.toLinearEquiv.surjective v
    exact LinearMap.congr_fun h0 u'
  · exact (congrArg f (LinearMap.congr_fun (q.isIntertwining' _) v)).trans (fe x _)

/- English proof (translation)
Introduce `E _ _ _ n U hn P w ρ σ hρ hs hc τ hτ`. Conclude with `irreducible_component_of_speh U hn P w ρ σ hρ hs hc τ hτ`.
-/
theorem UpperTheory.V.Z.Desc.irrComp :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)) (hn : ∑ _i : Fin 1, 1 * n = n) (P : CuspSub E n)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : SmIrr (GL (Fin n) (w.adicCompletion E))) (σ : SmIrr (GL (Fin (1 * n)) (w.adicCompletion E))),
    P.IsLocComp w ρ → IsSpeh (cl ρ) 1 σ.ρ →
    IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => 1 * n) hn w fun _ => σ) →
    ∀ τ, P.IsLocComp w τ → IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  intro E _ _ _ n U hn P w ρ σ hρ hs hc τ hτ
  exact irreducible_component_of_speh U hn P w ρ σ hρ hs hc τ hτ

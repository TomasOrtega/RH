import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.Pee

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `h0 n ξ hm V _ _ π hs hi ⟨f, hf⟩`. Take `⟨W, _, _, σ, hσs, hσi, hσsph, hσq⟩` from `hC n ξ`. Take `⟨g, hg⟩` from `hS n ξ hm W σ hσs hσi hσsph hσq`. Take `⟨w, hwK, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hσsph`. Establish `hg0 : g ≠ 0` using `fun e => hw0 (hg (by rw [e, map_zero]; rfl))`.

Take `⟨e⟩` from `hU h0 n ξ hm V W π σ hi hσi f g hf hg0`. Use `fun hb => hw0 ?_` and prove the remaining obligations. Establish `hv : e.toLinearEquiv.symm w ∈ fixed π (KO k (Fin n))` using `fun h => by`. Establish `h1` using `hwK h`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢`.

Apply `e.toLinearEquiv.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply]`. Establish `h2` using `e.isIntertwining' h`. Establish `h3` using `congrArg (fun F => F (e.toLinearEquiv.symm w)) h2`. Simplify using `only [LinearMap.comp_apply] at h3`.

Use `(h3.trans ?_).trans h1` and prove the remaining obligations. Use `show σ h (e.toLinearEquiv (e.toLinearEquiv.symm w)) = σ h w`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Rewrite `hv` using `[hb]`. Establish `h5` using `congrArg e.toLinearEquiv ((Submodule.mem_bot ℂ).1 hv)`.

Rewrite `h5` using `[LinearEquiv.apply_symm_apply, map_zero]`. Then use the resulting hypothesis.
-/
theorem extremeSph_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hC : SphConst k) (hS : SphEmb k) (hU : UniqSub k) : ExtremeSph k := by
  intro h0 n ξ hm V _ _ π hs hi ⟨f, hf⟩
  obtain ⟨W, _, _, σ, hσs, hσi, hσsph, hσq⟩ := hC n ξ
  obtain ⟨g, hg⟩ := hS n ξ hm W σ hσs hσi hσsph hσq
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσsph
  have hg0 : g ≠ 0 := fun e => hw0 (hg (by rw [e, map_zero]; rfl))
  obtain ⟨e⟩ := hU h0 n ξ hm V W π σ hi hσi f g hf hg0
  refine fun hb => hw0 ?_
  have hv : e.toLinearEquiv.symm w ∈ fixed π (KO k (Fin n)) := fun h => by
    have h1 := hwK h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
    apply e.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    have h2 := e.isIntertwining' h
    have h3 := congrArg (fun F => F (e.toLinearEquiv.symm w)) h2
    simp only [LinearMap.comp_apply] at h3
    refine (h3.trans ?_).trans h1
    show σ h (e.toLinearEquiv (e.toLinearEquiv.symm w)) = σ h w
    rw [LinearEquiv.apply_symm_apply]
  rw [hb] at hv
  have h5 := congrArg e.toLinearEquiv ((Submodule.mem_bot ℂ).1 hv)
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h5

/- English proof (translation)
Introduce `E _ _ w c n N h σ P ξ hq he hm`. Take `⟨f, hf⟩` from `hE (w.adicCompletion E) n P.V P.ρ ξ P.smooth he`. Establish `hc : CharZero (w.adicCompletion E)` using `charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective`. Conclude with `hL E w c n N h σ P ξ hq (hX (w.adicCompletion E) hc n ξ hm P.V P.ρ P.smooth P.irred ⟨f, hf⟩) ⟨f, hf⟩`.
-/
theorem galois_fixed_adelic_matrices_descend (hE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ExpEmb k)
    (hX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ExtremeSph k)
    (hL : SatLink) : N3 := by
  intro E _ _ w c n N h σ P ξ hq he hm
  obtain ⟨f, hf⟩ := hE (w.adicCompletion E) n P.V P.ρ ξ P.smooth he
  have hc : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  exact hL E w c n N h σ P ξ hq (hX (w.adicCompletion E) hc n ξ hm P.V P.ρ P.smooth P.irred ⟨f, hf⟩) ⟨f, hf⟩

end PositivityTheory.Rg.BcB.N3.Pee

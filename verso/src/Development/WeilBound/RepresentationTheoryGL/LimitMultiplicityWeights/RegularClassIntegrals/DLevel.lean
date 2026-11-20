import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, -, b, hb, rfl⟩` from `hx`. Take `⟨V, hV, hVb⟩` from `GlobalTheory.Orb.exists_biinvariant hb`. Use `⟨V.comap (projFin σ J), hV.preimage (continuous_projFin σ J), fun k hk hkf g => ?_⟩` and prove the remaining obligations.

Use `show a (projInf σ J (g * k)) * b (projFin σ J (g * k)) = a (projInf σ J g) * b (projFin σ J g)`. Rewrite using `[map_mul, map_mul, mem_finPts.1 hkf, mul_one, (hVb _ hk _).2]`. Consider the case `zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨U, hU, h⟩` from `hx`.

Take `⟨V, hV, h'⟩` from `hy`. Conclude with `⟨U ⊓ V, hU.inter hV, fun k hk hkf g => by`. Simplify using `only [Pi.add_apply, h k hk.1 hkf g, h' k hk.2 hkf g]⟩`. Consider the case `smul c x _ hx`. Take `⟨U, hU, h⟩` from `hx`.

Conclude with `⟨U, hU, fun k hk hkf g => by simp only [Pi.smul_apply, h k hk hkf g]⟩`.
-/
theorem level_of_mem {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, b, hb, rfl⟩ := hx
    obtain ⟨V, hV, hVb⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨V.comap (projFin σ J), hV.preimage (continuous_projFin σ J), fun k hk hkf g => ?_⟩
    show a (projInf σ J (g * k)) * b (projFin σ J (g * k)) = a (projInf σ J g) * b (projFin σ J g)
    rw [map_mul, map_mul, mem_finPts.1 hkf, mul_one, (hVb _ hk _).2]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨V, hV, h'⟩ := hy
    exact ⟨U ⊓ V, hU.inter hV, fun k hk hkf g => by
      simp only [Pi.add_apply, h k hk.1 hkf g, h' k hk.2 hkf g]⟩
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hkf g => by simp only [Pi.smul_apply, h k hk hkf g]⟩

end MainStatements.WeightKernel.Dec.DLevel

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ n J _ f hf`. Conclude with `MainStatements.WeightKernel.Dec.DLevel.level_of_mem hf`.
-/
theorem MainStatements.WeightKernel.Dec.level : MainStatements.WeightKernel.Dec.Level := by
  intro F E _ _ _ _ _ σ _ n J _ f hf
  exact MainStatements.WeightKernel.Dec.DLevel.level_of_mem hf

end

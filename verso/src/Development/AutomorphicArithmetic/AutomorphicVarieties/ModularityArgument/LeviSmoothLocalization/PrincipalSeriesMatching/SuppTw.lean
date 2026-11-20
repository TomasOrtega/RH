import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hζ, e⟩`. Use `⟨ζ * χ⁻¹, hζ.mul hχ.inv, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← IrrGL.tw_ofChar ζ χ⁻¹ hζ hχ.inv, ← e, IrrGL.tw_tw_inv]`. Rewrite using `[inv_mul_cancel_right]`.

Introduce and unpack `⟨ξ, hξ, rfl, rfl⟩`. Conclude with `⟨hξ.mul hχ, IrrGL.tw_ofChar _ _ _ _⟩`.
-/
private theorem tw_eq_iff (y : IrrGL k) (χ ζ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (∃ hζ, y.tw χ hχ = IrrGL.ofChar ζ hζ) ↔ ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ ζ = ξ * χ := by
  constructor
  · rintro ⟨hζ, e⟩
    refine ⟨ζ * χ⁻¹, hζ.mul hχ.inv, ?_, ?_⟩
    · rw [← IrrGL.tw_ofChar ζ χ⁻¹ hζ hχ.inv, ← e, IrrGL.tw_tw_inv]
    · rw [inv_mul_cancel_right]
  · rintro ⟨ξ, hξ, rfl, rfl⟩
    exact ⟨hξ.mul hχ, IrrGL.tw_ofChar _ _ _ _⟩

/- English proof (translation)
Unfold `pol`. Rewrite using `[Multiset.map_map]`. Use `congrArg Multiset.prod (Multiset.map_congr rfl fun y _ => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Distinguish the cases in `h : ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * (χ * θ))`.

Establish `h' : ∃ ζ : kˣ →* ℂˣ, (∃ hζ, y.tw χ hχ = IrrGL.ofChar ζ hζ) ∧ IsUnram (ζ * θ)`. Take `⟨ξ, ⟨hξ, e⟩, hu⟩` from `h`. Conclude with `⟨ξ * χ, (tw_eq_iff y χ _ hχ).2 ⟨ξ, hξ, e, rfl⟩, by rwa [mul_assoc]⟩`. Rewrite using `[dif_pos h, dif_pos h']`. Take `⟨ξ, hξ, e, e'⟩` from `(tw_eq_iff y χ _ hχ).1 h'.choose_spec.1`.

Take `⟨hξ', e''⟩` from `h.choose_spec.1`. Establish `: ξ = h.choose` using `IrrGL.ofChar_inj.1 (e.symm.trans e'')`. Rewrite using `[e', this, mul_assoc]`. Establish `h' : ¬ ∃ ζ : kˣ →* ℂˣ, (∃ hζ, y.tw χ hχ = IrrGL.ofChar ζ hζ) ∧ IsUnram (ζ * θ)`. Introduce and unpack `⟨ζ, hζ, hu⟩`.

Take `⟨ξ, hξ, e, rfl⟩` from `(tw_eq_iff y χ _ hχ).1 hζ`. Conclude with `h ⟨ξ, ⟨hξ, e⟩, by rwa [← mul_assoc]⟩`. Rewrite using `[dif_neg h, dif_neg h']`.
-/
private theorem pol_tw (s : Multiset (IrrGL k)) (χ θ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    pol (s.map (·.tw χ hχ)) θ = pol s (χ * θ) := by
  unfold pol
  rw [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun y _ => ?_)
  simp only [Function.comp_apply]
  by_cases h : ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * (χ * θ))
  · have h' : ∃ ζ : kˣ →* ℂˣ, (∃ hζ, y.tw χ hχ = IrrGL.ofChar ζ hζ) ∧ IsUnram (ζ * θ) := by
      obtain ⟨ξ, ⟨hξ, e⟩, hu⟩ := h
      exact ⟨ξ * χ, (tw_eq_iff y χ _ hχ).2 ⟨ξ, hξ, e, rfl⟩, by rwa [mul_assoc]⟩
    rw [dif_pos h, dif_pos h']
    obtain ⟨ξ, hξ, e, e'⟩ := (tw_eq_iff y χ _ hχ).1 h'.choose_spec.1
    obtain ⟨hξ', e''⟩ := h.choose_spec.1
    have : ξ = h.choose := IrrGL.ofChar_inj.1 (e.symm.trans e'')
    rw [e', this, mul_assoc]
  · have h' : ¬ ∃ ζ : kˣ →* ℂˣ, (∃ hζ, y.tw χ hχ = IrrGL.ofChar ζ hζ) ∧ IsUnram (ζ * θ) := by
      rintro ⟨ζ, hζ, hu⟩
      obtain ⟨ξ, hξ, e, rfl⟩ := (tw_eq_iff y χ _ hχ).1 hζ
      exact h ⟨ξ, ⟨hξ, e⟩, by rwa [← mul_assoc]⟩
    rw [dif_neg h, dif_neg h']

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hζ, hm⟩`. Take `⟨y, hy, e⟩` from `Multiset.mem_map.1 hm`. Take `⟨ξ, hξ, rfl, e'⟩` from `(tw_eq_iff y χ ζ hχ).1 ⟨hζ, e⟩`. Conclude with `⟨ξ, ⟨hξ, hy⟩, e'⟩`.

Introduce and unpack `⟨ξ, ⟨hξ, hy⟩, rfl⟩`. Conclude with `⟨hξ.mul hχ, Multiset.mem_map.2 ⟨_, hy, IrrGL.tw_ofChar _ _ _ _⟩⟩`.
-/
private theorem chars_tw (s : Multiset (IrrGL k)) (χ ζ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    ζ ∈ chars (s.map (·.tw χ hχ)) ↔ ∃ ξ ∈ chars s, ζ = ξ * χ := by
  constructor
  · rintro ⟨hζ, hm⟩
    obtain ⟨y, hy, e⟩ := Multiset.mem_map.1 hm
    obtain ⟨ξ, hξ, rfl, e'⟩ := (tw_eq_iff y χ ζ hχ).1 ⟨hζ, e⟩
    exact ⟨ξ, ⟨hξ, hy⟩, e'⟩
  · rintro ⟨ξ, ⟨hξ, hy⟩, rfl⟩
    exact ⟨hξ.mul hχ, Multiset.mem_map.2 ⟨_, hy, IrrGL.tw_ofChar _ _ _ _⟩⟩

end Loc

section Glob

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
The claim follows from `GlobalTheory.HeckeComp.smooth_loc χ v`.
-/
private theorem smooth_loc (χ : HChar K) (v : HeightOneSpectrum (𝓞 K)) : IsSmoothChar (χ.loc v) :=
  GlobalTheory.HeckeComp.smooth_loc χ v

/- English proof (translation)
The claim follows from `h.tw (χ.loc v) (smooth_loc χ v)`.
-/
private theorem supp_twist [IsTotallyComplex K] {v : HeightOneSpectrum (𝓞 K)} {σ : SmIrr (GL (Fin n) (v.adicCompletion K))} (χ : HChar K)
    {s : Multiset (IrrGL (v.adicCompletion K))} (h : HasSupport σ.ρ s) :
    HasSupport (σ.twist (CuspSub.locDet n χ v) (CuspSub.isOpen_ker_locDet χ v)).ρ
      (s.map (·.tw (χ.loc v) (smooth_loc χ v))) :=
  h.tw (χ.loc v) (smooth_loc χ v)

end Glob

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter in
/- English proof (translation)
Introduce and unpack `K _ _ _ n _ π v χ s ⟨σ, hσ, hs⟩`. Use `⟨_, ⟨_, hσ.twist χ, supp_twist χ hs⟩, fun θ => pol_tw s _ θ _, fun ζ => chars_tw s _ ζ _, ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.map_map]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppTw :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SuppTw := by
  rintro K _ _ _ n _ π v χ s ⟨σ, hσ, hs⟩
  refine ⟨_, ⟨_, hσ.twist χ, supp_twist χ hs⟩, fun θ => pol_tw s _ θ _, fun ζ => chars_tw s _ ζ _, ?_⟩
  rw [Multiset.map_map]
  rfl

import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.Relab

/- English proof (translation)
Introduce `E _ _ _ H l c σ hσ`. Establish `hinj : Function.Injective (relab c σ)`. Introduce `τ₁ τ₂ h`. Use extensionality with `a`. Use `congrArg (fun f : E →+* ℂ => f a) h` as an intermediate fact.

Conclude with `congrArg Subtype.val (σ.injective this)`. Establish `h0 : H.rt0 ≠ 0`. Introduce `h`. Use `H.sqrt_neg_disc_sq` as an intermediate fact. Rewrite `this` using `[h]`.

Establish `hd : (H.d : ℂ) = 0` using `by linear_combination this`. Conclude with `H.d_prime.ne_zero (by exact_mod_cast hd)`. Establish `hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0` using `hσ`. Establish `hrel : ∀ τ' : E →+* ℂ, (relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0)`. Introduce `τ'`.

Establish `hE : ((H.rt : E)) ^ 2 = -(H.d : E)`. Use `congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2`. Rewrite using `[H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]`.

Establish `hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩` using `rfl`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx` into its components or cases. Use `⟨fun _ => hx, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[hval, ← hσ0]`. Conclude with `congrArg σ (Subtype.ext hx)`.

Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. It suffices to derive a contradiction. Establish `h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩`. Rewrite using `[← map_neg]`. Conclude with `congrArg σ (Subtype.ext hx)`.

Rewrite `h1` using `[← hval, h, hσ0]`. Conclude with `h0 (by linear_combination h1 / 2)`. It suffices to derive a contradiction. Conclude with `h0 (by linear_combination (h.symm.trans hx) / 2)`. Establish `hsurj` using `Finite.injective_iff_surjective.1 hinj`.

Use `⟨⟨hinj, hsurj⟩, hrel, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ`. Use extensionality with `a`. Establish `key : ∀ (ρ : E →+* ℂ) (x : E), conjEmb ρ x = ρ (IsCMField.complexConj E x)` using `fun ρ x => (IsCMField.complexEmbedding_complexConj E ρ x).symm`. Rewrite using `[key]`.

Conclude with `congrArg σ (Subtype.ext (key τ a))`. Introduce `Dw g e τ`. Take `⟨τ₀, rfl⟩` from `hsurj τ`. Establish `hcard : Nat.card {i // relab c σ (e i).1 = relab c σ τ₀} = Dw.mult τ₀`. Establish `e1 : {i // relab c σ (e i).1 = relab c σ τ₀} ≃ {i // (e i).1 = τ₀}` using `Equiv.subtypeEquivRight (fun i => hinj.eq_iff)`.

Establish `e2 : {i // (e i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀}` using `e.subtypeEquiv (fun _ => Iff.rfl)`. Establish `e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} ≃ Fin (Dw.mult τ₀)` using `Equiv.sigmaSubtype τ₀`. Rewrite using `[Nat.card_congr (e1.trans (e2.trans e3)), Nat.card_eq_fintype_card, Fintype.card_fin]`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[hcard]`.

Unfold `Datum.mult`. Rewrite using `[if_pos ((hrel τ₀).1 h)]`. Rewrite using `[hcard]`. Unfold `Datum.mult`. Rewrite using `[if_neg (fun h' => h ((hrel τ₀).2 h'))]`.
-/
theorem relab_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → Function.Bijective (relab c σ) ∧ (∀ τ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0) ∧ (∀ τ, relab c σ (conjEmb τ) = conjEmb (relab c σ τ)) ∧ ∀ (Dw : Datum H) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  intro E _ _ _ H l c σ hσ
  classical
  have hinj : Function.Injective (relab c σ) := by
    intro τ₁ τ₂ h
    ext a
    have := congrArg (fun f : E →+* ℂ => f a) h
    exact congrArg Subtype.val (σ.injective this)
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ τ' : E →+* ℂ, (relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0) := by
    intro τ'
    have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
    have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
    · refine ⟨fun _ => hx, fun _ => ?_⟩
      rw [hval, ← hσ0]
      exact congrArg σ (Subtype.ext hx)
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · exfalso
        have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
          rw [← map_neg]
          exact congrArg σ (Subtype.ext hx)
        rw [← hval, h, hσ0] at h1
        exact h0 (by linear_combination h1 / 2)
      · exfalso
        exact h0 (by linear_combination (h.symm.trans hx) / 2)
  have hsurj := Finite.injective_iff_surjective.1 hinj
  refine ⟨⟨hinj, hsurj⟩, hrel, ?_, ?_⟩
  · intro τ
    ext a
    have key : ∀ (ρ : E →+* ℂ) (x : E), conjEmb ρ x = ρ (IsCMField.complexConj E x) := fun ρ x =>
      (IsCMField.complexEmbedding_complexConj E ρ x).symm
    rw [key]
    exact congrArg σ (Subtype.ext (key τ a))
  · intro Dw g e τ
    obtain ⟨τ₀, rfl⟩ := hsurj τ
    have hcard : Nat.card {i // relab c σ (e i).1 = relab c σ τ₀} = Dw.mult τ₀ := by
      have e1 : {i // relab c σ (e i).1 = relab c σ τ₀} ≃ {i // (e i).1 = τ₀} :=
        Equiv.subtypeEquivRight (fun i => hinj.eq_iff)
      have e2 : {i // (e i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} :=
        e.subtypeEquiv (fun _ => Iff.rfl)
      have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} ≃ Fin (Dw.mult τ₀) := Equiv.sigmaSubtype τ₀
      rw [Nat.card_congr (e1.trans (e2.trans e3)), Nat.card_eq_fintype_card, Fintype.card_fin]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hcard]
      unfold Datum.mult
      rw [if_pos ((hrel τ₀).1 h)]
    · rw [hcard]
      unfold Datum.mult
      rw [if_neg (fun h' => h ((hrel τ₀).2 h'))]

end GlobalTheory.Relab

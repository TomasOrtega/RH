import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ImaginaryRootConj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LabelCount

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem emb_ext {τ τ' : E →+* ℂ} (h : ∀ a : 𝓞 E, τ (a : E) = τ' (a : E)) : τ = τ' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  simp at h2
  exact H.d_prime.ne_zero h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem rt0_ne_neg (H : Host E) : H.rt0 ≠ -H.rt0 := by
  intro h
  have h2 : (2 : ℂ) * H.rt0 = 0 := by linear_combination h
  exact rt0_ne_zero H ((mul_eq_zero.mp h2).resolve_left two_ne_zero)

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem labelEmb_injective (c : Coeff l) : Function.Injective (labelEmb (H := H) c) := by
  have val : ∀ {s t : CMType H ⊕ CMType H}, labelEmb c s = labelEmb c t → ∀ a : 𝓞 E,
      ((labelEmb c s a : c.F) : ℂ) = ((labelEmb c t a : c.F) : ℂ) := fun h a => by rw [h]
  rintro (τ | τ) (τ' | τ') h
  · refine congrArg Sum.inl (Subtype.ext (emb_ext fun a => val h a))
  · exact absurd ((HodgeCptTest.labelEmb_inl_rt c τ).symm.trans
      ((val h H.rt).trans (HodgeCptTest.labelEmb_inr_rt c τ'))) (rt0_ne_neg H)
  · exact absurd ((HodgeCptTest.labelEmb_inl_rt c τ').symm.trans
      ((val h H.rt).symm.trans (HodgeCptTest.labelEmb_inr_rt c τ))) (rt0_ne_neg H)
  · refine congrArg Sum.inr (Subtype.ext (emb_ext fun a => ?_))
    have := val h (H.bar.symm a)
    simpa [labelEmb] using this

def labelCx (H : Host E) : CMType H ⊕ CMType H → (E →+* ℂ) :=
  Sum.elim (fun τ => τ.1) (fun τ => (starRingEnd ℂ).comp τ.1)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis.

Supply the required witnesses or components. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem labelCx_bijective (H : Host E) : Function.Bijective (labelCx H) := by
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg Sum.inl (Subtype.ext h)
    · have h1 := RingHom.congr_fun h (H.rt : E)
      simp only [labelCx, Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply, τ.2, τ'.2,
        HodgeCptTest.imaginary_root_conj] at h1
      exact absurd h1 (rt0_ne_neg H)
    · have h1 := RingHom.congr_fun h (H.rt : E)
      simp only [labelCx, Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply, τ.2, τ'.2,
        HodgeCptTest.imaginary_root_conj] at h1
      exact absurd h1.symm (rt0_ne_neg H)
    · refine congrArg Sum.inr (Subtype.ext (RingHom.ext fun x => ?_))
      exact (starRingEnd ℂ).injective (RingHom.congr_fun h x)
  · intro σ
    have hsq : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    have hrt : σ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, hsq]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hrt with hp | hm
    · exact ⟨.inl ⟨σ, hp⟩, rfl⟩
    · have ht : ((starRingEnd ℂ).comp σ) (H.rt : E) = H.rt0 := by
        simp [hm, HodgeCptTest.imaginary_root_conj]
      refine ⟨.inr ⟨(starRingEnd ℂ).comp σ, ht⟩, RingHom.ext fun x => ?_⟩
      simp [labelCx]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem labels_injective_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) [Fintype (CMType H)] (Ω : Type) [Field Ω] (cst : c.F →+* Ω),
    Function.Injective (fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s)) ∧
      Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  intro E _ _ _ H l c _ Ω _ cst
  refine ⟨fun s t h => labelEmb_injective c (RingHom.ext fun a => cst.injective (RingHom.congr_fun h a)), ?_⟩
  rw [Fintype.card_of_bijective (labelCx_bijective H), NumberField.Embeddings.card]

end GlobalTheory.CompanionTheory.Ar.LabelCount

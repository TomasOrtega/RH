import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

/- English proof (translation)
Introduce `p O _ G _ _ ε hε e M _ _ ρ hρ m N hm`. Establish `key : ∀ g g' : G, Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O) = Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g' : Oˣ) : O) → ρ g m = ρ g' m`. Introduce `g g' h`. Establish `h1 : Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) (((ε g) ^ e : Oˣ) : O) = Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) (((ε g') ^ e : Oˣ) : O)`. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow, h]`.

Rewrite using `[hρ, hρ]`. Generalize the expression as in `(ε g) ^ e = u at h1 ⊢`. Generalize the expression as in `(ε g') ^ e = v at h1 ⊢`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)`. Establish `h2 : ((v⁻¹ : Oˣ) : O) - ((u⁻¹ : Oˣ) : O) = (((u⁻¹ : Oˣ) : O) * ((v⁻¹ : Oˣ) : O) * b) * (p : O) ^ N`.

Rewrite using `[mul_assoc, hb]`. Establish `hu : ((u⁻¹ : Oˣ) : O) * (u : O) = 1` using `u.inv_mul`. Establish `hv : ((v⁻¹ : Oˣ) : O) * (v : O) = 1` using `v.inv_mul`. Take the linear combination `(-((v⁻¹ : Oˣ) : O)) * hu + ((u⁻¹ : Oˣ) : O) * hv`. Use `symm`.

Rewrite using `[← sub_eq_zero, ← sub_smul, h2, mul_smul, hm, smul_zero]`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `g₀`. Take `⟨U, hU, hg, hc⟩` from `((IsLocallyConstant.iff_exists_open _).1 (hε N)) g₀`. Conclude with `⟨U, hU, hg, fun g hgU => key g g₀ (hc g hgU)⟩`.
-/
theorem isLocallyConstant_orbit_of_inv_pow_character :
    ∀ {p : ℕ} {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ),
    (∀ N : ℕ, IsLocallyConstant (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O))) →
    ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ (m : M) (N : ℕ), (p : O) ^ N • m = 0 →
    IsLocallyConstant (fun g => ρ g m) := by
  intro p O _ G _ _ ε hε e M _ _ ρ hρ m N hm
  have key : ∀ g g' : G,
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O) =
        Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g' : Oˣ) : O) → ρ g m = ρ g' m := by
    intro g g' h
    have h1 : Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) (((ε g) ^ e : Oˣ) : O) =
        Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) (((ε g') ^ e : Oˣ) : O) := by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow, h]
    rw [hρ, hρ]
    generalize (ε g) ^ e = u at h1 ⊢
    generalize (ε g') ^ e = v at h1 ⊢
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    have h2 : ((v⁻¹ : Oˣ) : O) - ((u⁻¹ : Oˣ) : O) =
        (((u⁻¹ : Oˣ) : O) * ((v⁻¹ : Oˣ) : O) * b) * (p : O) ^ N := by
      rw [mul_assoc, hb]
      have hu : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := u.inv_mul
      have hv : ((v⁻¹ : Oˣ) : O) * (v : O) = 1 := v.inv_mul
      linear_combination (-((v⁻¹ : Oˣ) : O)) * hu + ((u⁻¹ : Oˣ) : O) * hv
    symm
    rw [← sub_eq_zero, ← sub_smul, h2, mul_smul, hm, smul_zero]
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  obtain ⟨U, hU, hg, hc⟩ := ((IsLocallyConstant.iff_exists_open _).1 (hε N)) g₀
  exact ⟨U, hU, hg, fun g hgU => key g g₀ (hc g hgU)⟩

end GlobalTheory.ShapeNeg

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.BlowupIntegral

/- English proof (translation)
Rewrite using `[dense_iff_inter_open]`. Introduce and unpack `W hW ⟨x, hx⟩`. Assume the negation of the conclusion as `hc`. Take `⟨U, f, hxU, hf, hIU⟩` from `hI x`. Take `⟨t, ht, hxt⟩` from `U.2.exists_basicOpen_le (V := ⟨W, hW⟩) ⟨x, hx⟩ hxU`.

Establish `h0 : f * t = 0`. Rewrite using `[← basicOpen_eq_bot_iff, Scheme.basicOpen_mul, eq_bot_iff]`. Introduce and unpack `y ⟨hyf, hyt⟩`. Use `hc ⟨y, ht hyt, fun hy' => ?_⟩` and prove the remaining obligations. Establish `hyU : y ∈ U.1` using `Y.basicOpen_le f hyf`.

Use `(Scheme.IdealSheafData.mem_support_iff_of_mem hyU).1 hy'` as an intermediate fact. Rewrite `this` using `[Scheme.mem_zeroLocus_iff]`. Conclude with `this f (by rw [hIU]; exact Ideal.subset_span rfl) hyf`. Establish `ht0 : t = 0` using `(mul_left_mem_nonZeroDivisors_eq_zero_iff hf).1 h0`. Substitute `ht0` using the available equality.

Simplify using `at hxt`.
-/
theorem dense_compl_support_of_effCartier {Y : Scheme.{0}} [IsReduced Y] (I : Y.IdealSheafData)
    (hI : FinalTheorems.EffCartier I) : Dense ((I.support.compl : Y.Opens) : Set Y) := by
  rw [dense_iff_inter_open]
  rintro W hW ⟨x, hx⟩
  by_contra hc
  obtain ⟨U, f, hxU, hf, hIU⟩ := hI x
  obtain ⟨t, ht, hxt⟩ := U.2.exists_basicOpen_le (V := ⟨W, hW⟩) ⟨x, hx⟩ hxU
  have h0 : f * t = 0 := by
    rw [← basicOpen_eq_bot_iff, Scheme.basicOpen_mul, eq_bot_iff]
    rintro y ⟨hyf, hyt⟩
    refine hc ⟨y, ht hyt, fun hy' => ?_⟩
    have hyU : y ∈ U.1 := Y.basicOpen_le f hyf
    have := (Scheme.IdealSheafData.mem_support_iff_of_mem hyU).1 hy'
    rw [Scheme.mem_zeroLocus_iff] at this
    exact this f (by rw [hIU]; exact Ideal.subset_span rfl) hyf
  have ht0 : t = 0 := (mul_left_mem_nonZeroDivisors_eq_zero_iff hf).1 h0
  subst ht0
  simp at hxt

/- English proof (translation)
Set `V : X₁.Opens` to `Z.support.compl`. Establish `hbV : IsIso (π ∣_ V)` using `GlobalTheory.Principalise.isIso_restrict_of_blowup hb V fun _ hx => hx`. Establish `hU : (Z.comap π).support.compl = π ⁻¹ᵁ V`. Use extensionality with `y`. Conclude with `not_congr (GlobalTheory.ProjBlowup.mem_support_comap Z π y)`.

Establish `hd : Dense ((π ⁻¹ᵁ V : X₂.Opens) : Set X₂)` using `hU ▸ dense_compl_support_of_effCartier _ hb.1`. Establish `hne : Nonempty (π ⁻¹ᵁ V).toScheme` using `hd.nonempty.to_subtype`. Establish `: Nonempty V.toScheme` using `⟨(π ∣_ V) (Classical.arbitrary _)⟩`. Establish `: IsIntegral V.toScheme` using `isIntegral_of_isOpenImmersion V.ι`. Establish `: IsIntegral (π ⁻¹ᵁ V).toScheme` using `isIntegral_of_isOpenImmersion (π ∣_ V)`.

Establish `h` using `((IrreducibleSpace.isIrreducible_univ (π ⁻¹ᵁ V).toScheme).image _ (π ⁻¹ᵁ V).ι.continuous.continuousOn).closure`. Rewrite `h` using `[Set.image_univ, Scheme.Opens.range_ι, hd.closure_eq]`. Establish `: IrreducibleSpace X₂` using `(irreducibleSpace_def _).2 h`. Conclude with `isIntegral_of_irreducibleSpace_of_isReduced X₂`.
-/
theorem isIntegral_of_blowup {X₁ X₂ : Scheme.{0}} (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁) [IsIntegral X₁]
    [IsReduced X₂] [Nonempty X₂] (hb : FinalTheorems.Blowup π Z) : IsIntegral X₂ := by
  let V : X₁.Opens := Z.support.compl
  have hbV : IsIso (π ∣_ V) := GlobalTheory.Principalise.isIso_restrict_of_blowup hb V fun _ hx => hx
  have hU : (Z.comap π).support.compl = π ⁻¹ᵁ V := by
    ext y
    exact not_congr (GlobalTheory.ProjBlowup.mem_support_comap Z π y)
  have hd : Dense ((π ⁻¹ᵁ V : X₂.Opens) : Set X₂) := hU ▸ dense_compl_support_of_effCartier _ hb.1
  have hne : Nonempty (π ⁻¹ᵁ V).toScheme := hd.nonempty.to_subtype
  have : Nonempty V.toScheme := ⟨(π ∣_ V) (Classical.arbitrary _)⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsIntegral (π ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (π ∣_ V)
  have h := ((IrreducibleSpace.isIrreducible_univ (π ⁻¹ᵁ V).toScheme).image _
    (π ⁻¹ᵁ V).ι.continuous.continuousOn).closure
  rw [Set.image_univ, Scheme.Opens.range_ι, hd.closure_eq] at h
  have : IrreducibleSpace X₂ := (irreducibleSpace_def _).2 h
  exact isIntegral_of_irreducibleSpace_of_isReduced X₂

/- English proof (translation)
Introduce `k _ X₁ X₂ g Z π h₁ hb hs h₂`. Establish `: IsReduced X₂` using `GlobalTheory.isReduced_of_smooth_of_isReduced (π ≫ g)`. Conclude with `isIntegral_of_blowup Z π hb`.
-/
theorem isIntegral_of_smooth_blowup : ∀ {k : Type} [Field k] {X₁ X₂ : Scheme.{0}} (g : X₁ ⟶ Sp k)
    (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁), IsIntegral X₁ → FinalTheorems.Blowup π Z → Smooth (π ≫ g) → Nonempty X₂ →
      IsIntegral X₂ := by
  intro k _ X₁ X₂ g Z π h₁ hb hs h₂
  have : IsReduced X₂ := GlobalTheory.isReduced_of_smooth_of_isReduced (π ≫ g)
  exact isIntegral_of_blowup Z π hb

end GlobalTheory.CompanionTheory.BlowupIntegral

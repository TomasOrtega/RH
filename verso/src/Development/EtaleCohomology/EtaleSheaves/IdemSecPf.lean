import Development.EtaleCohomology.EtaleSheaves.SysFMPfSys
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.SysFMPf

namespace LateralTheory.E.IdemSecPf

/- English proof (translation)
Establish `h1 : Function.Injective (w.toNormalization.app ⊤)` using `w.toNormalization.app_injective ⊤`. Establish `h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom` using `((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1`. Introduce `a b h`. Conclude with `h1 (h2 h)`.
-/
theorem phi_injective {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Function.Injective (phi w) := by
  have h1 : Function.Injective (w.toNormalization.app ⊤) := w.toNormalization.app_injective ⊤
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1
  intro a b h
  exact h1 (h2 h)

/- English proof (translation)
Set `t : Γ(Spec (CommRingCat.of W), w.toNormalization ⁻¹ᵁ ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of W)).inv e`. Establish `ht : (w.toNormalization.app ⊤).hom.IsIntegralElem t`. Use `⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num))`. Establish `: t * t = t` using `by show (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e * (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e = _`.

Rewrite using `[← map_mul, he.eq]`. Rewrite using `[sq, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, this, sub_self]`. Take `⟨s, hs⟩` from `GlobalTheory.mem_range_toNormalization_app w ⊤ t ht`. Use `⟨s, ?_⟩` and prove the remaining obligations. Use `show (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (w.toNormalization.app ⊤ s) = e`.

Rewrite using `[hs]`. Use `show ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom e = e`. Simplify using the standard rewrite rules.
-/
theorem phi_idem {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (e : W) (he : IsIdempotentElem e) : ∃ s, phi w s = e := by
  let t : Γ(Spec (CommRingCat.of W), w.toNormalization ⁻¹ᵁ ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv e
  have ht : (w.toNormalization.app ⊤).hom.IsIntegralElem t := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num))
    · have : t * t = t := by
        show (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e * (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e = _
        rw [← map_mul, he.eq]
      rw [sq, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, this, sub_self]
  obtain ⟨s, hs⟩ := GlobalTheory.mem_range_toNormalization_app w ⊤ t ht
  refine ⟨s, ?_⟩
  show (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (w.toNormalization.app ⊤ s) = e
  rw [hs]
  show ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom e = e
  simp

/- English proof (translation)
Introduce `P _ _ W _ w`. Conclude with `⟨phi_injective w, fun e he => phi_idem w e he⟩`.
-/
theorem IdemSec_of : LateralTheory.E.SysFMPfSys.IdemSec := by
  intro P _ _ W _ w
  exact ⟨phi_injective w, fun e he => phi_idem w e he⟩

end LateralTheory.E.IdemSecPf

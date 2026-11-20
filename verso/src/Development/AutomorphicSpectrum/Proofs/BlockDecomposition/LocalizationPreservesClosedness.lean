import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.LocAic

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `hsplit : e = e * (1 - f) + e * f` using `by ring`. Rewrite using `[hsplit]`. Conclude with `Ideal.add_mem _ h1 (Ideal.mul_mem_left _ e (Ideal.mem_span_singleton_self f))`. Establish `hsplit : 1 - e = (1 - e) * f + (1 - e) * (1 - f)` using `by ring`.

Rewrite using `[hsplit]`. Conclude with `Ideal.add_mem _ h2 (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))`.
-/
theorem mem_of_compare {A : Type} [CommRing A] {e f : A}
    (h1 : e * (1 - f) ∈ Ideal.span {f}) (h2 : (1 - e) * f ∈ Ideal.span {1 - f}) :
    e ∈ Ideal.span {f} ∧ 1 - e ∈ Ideal.span {1 - f} := by
  constructor
  · have hsplit : e = e * (1 - f) + e * f := by ring
    rw [hsplit]
    exact Ideal.add_mem _ h1 (Ideal.mul_mem_left _ e (Ideal.mem_span_singleton_self f))
  · have hsplit : 1 - e = (1 - e) * f + (1 - e) * (1 - f) := by ring
    rw [hsplit]
    exact Ideal.add_mem _ h2 (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

/- English proof (translation)
Establish `hV' : ∀ f g : S, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) → ∃ e, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f}` using `hV`. Take `⟨e, he, h1, h2⟩` from `hV' f (1 - f) ⟨0, by`. Rewrite using `[pow_zero, Ideal.mem_span_pair]`. Conclude with `⟨1, 1, by ring⟩⟩`. Use `⟨1 - e, he.one_sub, mem_of_compare h2 ?_⟩` and prove the remaining obligations.

Rewrite using `[sub_sub_cancel]`. Conclude with `h1`.
-/
theorem local_of_val {S : Type} [CommRing S] (π : S) (hV : Val π) (f : S) :
    ∃ e : S, IsIdempotentElem e ∧ e ∈ Ideal.span {f} ∧ 1 - e ∈ Ideal.span {1 - f} := by
  have hV' : ∀ f g : S, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
      ∃ e, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f} := hV
  obtain ⟨e, he, h1, h2⟩ := hV' f (1 - f) ⟨0, by
    rw [pow_zero, Ideal.mem_span_pair]
    exact ⟨1, 1, by ring⟩⟩
  refine ⟨1 - e, he.one_sub, mem_of_compare h2 ?_⟩
  rw [sub_sub_cancel]
  exact h1

/- English proof (translation)
Establish `hV' : ∀ f g : S, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) → ∃ e, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f}` using `hV`. Take `⟨⟨a, s⟩, hf⟩` from `IsLocalization.surj (Submonoid.powers π) f`. Take `⟨n, hn⟩` from `(Submonoid.mem_powers_iff _ _).1 s.2`. Establish `hu : IsUnit (algebraMap S (Localization.Away π) (s : S))` using `IsLocalization.map_units (Localization.Away π) s`. Establish `hA : algebraMap S (Localization.Away π) a = f * algebraMap S (Localization.Away π) (s : S)` using `hf.symm`.

Establish `hB : algebraMap S (Localization.Away π) ((s : S) - a) = (1 - f) * algebraMap S (Localization.Away π) (s : S)`. Rewrite using `[map_sub, hA]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨e, he, h1, h2⟩` from `hV' a ((s : S) - a) ⟨n, by`. Rewrite using `[hn, Ideal.mem_span_pair]`.

Conclude with `⟨1, 1, by ring⟩⟩`. Establish `d1 : (1 - f) ∣ algebraMap S (Localization.Away π) e * f`. Establish `hd` using `map_dvd (algebraMap S (Localization.Away π)) (Ideal.mem_span_singleton.1 h1)`. Rewrite `hd` using `[hB, map_mul, hA, ← mul_assoc]`. Conclude with `hu.dvd_mul_right.1 (dvd_trans (dvd_mul_right _ _) hd)`.

Establish `d2 : f ∣ (1 - algebraMap S (Localization.Away π) e) * (1 - f)`. Establish `hd` using `map_dvd (algebraMap S (Localization.Away π)) (Ideal.mem_span_singleton.1 h2)`. Rewrite `hd` using `[map_mul, hB, map_sub, map_one, hA, ← mul_assoc]`. Conclude with `hu.dvd_mul_right.1 (dvd_trans (dvd_mul_right _ _) hd)`. Establish `hē : IsIdempotentElem (algebraMap S (Localization.Away π) e)`.

Rewrite using `[IsIdempotentElem, ← map_mul, he.eq]`. Use `⟨1 - algebraMap S (Localization.Away π) e, hē.one_sub, mem_of_compare (Ideal.mem_span_singleton.2 d2) ?_⟩` and prove the remaining obligations. Rewrite using `[sub_sub_cancel]`. Conclude with `Ideal.mem_span_singleton.2 d1`.
-/
theorem local_away_of_val {S : Type} [CommRing S] (π : S) (hV : Val π) (f : Localization.Away π) :
    ∃ e : Localization.Away π, IsIdempotentElem e ∧ e ∈ Ideal.span {f} ∧ 1 - e ∈ Ideal.span {1 - f} := by
  have hV' : ∀ f g : S, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
      ∃ e, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f} := hV
  obtain ⟨⟨a, s⟩, hf⟩ := IsLocalization.surj (Submonoid.powers π) f
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
  have hu : IsUnit (algebraMap S (Localization.Away π) (s : S)) :=
    IsLocalization.map_units (Localization.Away π) s
  have hA : algebraMap S (Localization.Away π) a = f * algebraMap S (Localization.Away π) (s : S) := hf.symm
  have hB : algebraMap S (Localization.Away π) ((s : S) - a) =
      (1 - f) * algebraMap S (Localization.Away π) (s : S) := by
    rw [map_sub, hA]
    ring
  obtain ⟨e, he, h1, h2⟩ := hV' a ((s : S) - a) ⟨n, by
    rw [hn, Ideal.mem_span_pair]
    exact ⟨1, 1, by ring⟩⟩
  have d1 : (1 - f) ∣ algebraMap S (Localization.Away π) e * f := by
    have hd := map_dvd (algebraMap S (Localization.Away π)) (Ideal.mem_span_singleton.1 h1)
    rw [hB, map_mul, hA, ← mul_assoc] at hd
    exact hu.dvd_mul_right.1 (dvd_trans (dvd_mul_right _ _) hd)
  have d2 : f ∣ (1 - algebraMap S (Localization.Away π) e) * (1 - f) := by
    have hd := map_dvd (algebraMap S (Localization.Away π)) (Ideal.mem_span_singleton.1 h2)
    rw [map_mul, hB, map_sub, map_one, hA, ← mul_assoc] at hd
    exact hu.dvd_mul_right.1 (dvd_trans (dvd_mul_right _ _) hd)
  have hē : IsIdempotentElem (algebraMap S (Localization.Away π) e) := by
    rw [IsIdempotentElem, ← map_mul, he.eq]
  refine ⟨1 - algebraMap S (Localization.Away π) e, hē.one_sub,
    mem_of_compare (Ideal.mem_span_singleton.2 d2) ?_⟩
  rw [sub_sub_cancel]
  exact Ideal.mem_span_singleton.2 d1

open Polynomial in

/- English proof (translation)
Establish `hA' : ∀ P : Polynomial S, P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x` using `hA`. Unfold `Aic`. Introduce `P hP hdeg`. Establish `hlift` using `IsLocalization.scaleRoots_commonDenom_mem_lifts (M := Submonoid.powers π) (Rₘ := Localization.Away π) P (by rw [hP.leadingCoeff]; exact ⟨1, map_one _⟩)`. Take `⟨q, hq, hqdeg, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hlift ((Polynomial.monic_scaleRoots_iff _).2 hP)`.

Take `⟨y, hy⟩` from `hA' q hqm (by rw [hqdeg, Polynomial.natDegree_scaleRoots]; exact hdeg)`. Establish `hs : IsUnit (algebraMap S (Localization.Away π) (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S))` using `IsLocalization.map_units (Localization.Away π) _`. Use `⟨↑hs.unit⁻¹ * algebraMap S (Localization.Away π) y, ?_⟩` and prove the remaining obligations. Establish `h1` using `Polynomial.scaleRoots_eval₂_mul (p := P) (RingHom.id (Localization.Away π)) (↑hs.unit⁻¹ * algebraMap S (Localization.Away π) y) (algebraMap S (Localization.Away π) (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S))`. Simplify using `only [RingHom.id_apply] at h1`.

Rewrite `h1` using `[← mul_assoc, hs.mul_val_inv, one_mul]`. Establish `h3 : Polynomial.eval₂ (RingHom.id _) (algebraMap S (Localization.Away π) y) (P.scaleRoots (algebraMap S (Localization.Away π) (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S))) = 0`. Rewrite using `[← hq, Polynomial.eval₂_map, RingHom.id_comp, Polynomial.eval₂_hom]`. Rewrite using `[show q.eval y = 0 from hy, map_zero]`. Rewrite `h1` using `[h3]`.

Conclude with `(hs.pow _).mul_right_eq_zero.1 h1.symm`.
-/
theorem aic_away {S : Type} [CommRing S] (π : S) (hA : Aic S) : Aic (Localization.Away π) := by
  have hA' : ∀ P : Polynomial S, P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x := hA
  unfold Aic
  intro P hP hdeg
  have hlift := IsLocalization.scaleRoots_commonDenom_mem_lifts (M := Submonoid.powers π)
    (Rₘ := Localization.Away π) P (by rw [hP.leadingCoeff]; exact ⟨1, map_one _⟩)
  obtain ⟨q, hq, hqdeg, hqm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift ((Polynomial.monic_scaleRoots_iff _).2 hP)
  obtain ⟨y, hy⟩ := hA' q hqm (by rw [hqdeg, Polynomial.natDegree_scaleRoots]; exact hdeg)
  have hs : IsUnit (algebraMap S (Localization.Away π)
      (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S)) :=
    IsLocalization.map_units (Localization.Away π) _
  refine ⟨↑hs.unit⁻¹ * algebraMap S (Localization.Away π) y, ?_⟩
  have h1 := Polynomial.scaleRoots_eval₂_mul (p := P) (RingHom.id (Localization.Away π))
    (↑hs.unit⁻¹ * algebraMap S (Localization.Away π) y)
    (algebraMap S (Localization.Away π) (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S))
  simp only [RingHom.id_apply] at h1
  rw [← mul_assoc, hs.mul_val_inv, one_mul] at h1
  have h3 : Polynomial.eval₂ (RingHom.id _) (algebraMap S (Localization.Away π) y)
      (P.scaleRoots (algebraMap S (Localization.Away π)
        (IsLocalization.commonDenom (Submonoid.powers π) P.support P.coeff : S))) = 0 := by
    rw [← hq, Polynomial.eval₂_map, RingHom.id_comp, Polynomial.eval₂_hom]
    rw [show q.eval y = 0 from hy, map_zero]
  rw [h3] at h1
  exact (hs.pow _).mul_right_eq_zero.1 h1.symm

/- English proof (translation)
Introduce `S _ ϖ`. Use `⟨fun hV => ⟨?_, ?_⟩, fun hA => aic_away ϖ hA⟩` and prove the remaining obligations. Unfold `Loc`. Conclude with `fun f => local_of_val ϖ hV f`. Unfold `Loc`.

Conclude with `fun f => local_away_of_val ϖ hV f`.
-/
theorem main : ∀ {S : Type} [CommRing S] (ϖ : S),
    (Val ϖ → Loc S ∧ Loc (Localization.Away ϖ)) ∧ (Aic S → Aic (Localization.Away ϖ)) := by
  intro S _ ϖ
  refine ⟨fun hV => ⟨?_, ?_⟩, fun hA => aic_away ϖ hA⟩
  · unfold Loc
    exact fun f => local_of_val ϖ hV f
  · unfold Loc
    exact fun f => local_away_of_val ϖ hV f

end GlobalTheory.CompanionTheory.LocAic

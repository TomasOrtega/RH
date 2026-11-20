import Formalism.LocalToGlobal.Divisibility.CoefModLemmas

open MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.initMinor`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using the standard rewrite rules.
-/
theorem fk_map_initMinor {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n s : ℕ} (I : Fin s → Fin r)
    (hs : s ≤ n) : map φ (Formalism.GradedWeylDivisibility.initMinor R I hs) = Formalism.GradedWeylDivisibility.initMinor S I hs := by
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.bideterminant`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl fun i _ => fk_map_initMinor φ _ _`.
-/
theorem fk_map_bidet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n k : ℕ} (sz : Fin k → ℕ)
    (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin r) :
    map φ (Formalism.GradedWeylDivisibility.bideterminant R sz hsz I) = Formalism.GradedWeylDivisibility.bideterminant S sz hsz I := by
  unfold Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => fk_map_initMinor φ _ _

/- English proof (translation)
Take `⟨k, sz, hsz, I, -, -, h⟩` from `((Formalism.GradedWeylDivisibility.sSBasis K n n ν).choose_spec.2 m).2.2`. Conclude with `⟨Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I, by rw [fk_map_bidet]; exact h⟩`.
-/
theorem ssB_int (K : Type) [Field K] {n : ℕ} (ν : Fin n → ℕ) (m : Formalism.GradedWeylDivisibility.ssIdx n n ν) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℤ, ssB K ν m = map (Int.castRingHom K) P := by
  obtain ⟨k, sz, hsz, I, -, -, h⟩ := ((Formalism.GradedWeylDivisibility.sSBasis K n n ν).choose_spec.2 m).2.2
  exact ⟨Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I, by rw [fk_map_bidet]; exact h⟩

/- English proof (translation)
Simplify using `only [Formalism.GradedWeylDivisibility.blockEmb]`. Conclude with `map_rename φ _ f`.
-/
theorem fk_map_blockEmb {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} {k n : ℕ} (τ : ι)
    (f : MvPolynomial (Fin k × Fin n) R) :
    map φ (Formalism.GradedWeylDivisibility.blockEmb R τ f) = Formalism.GradedWeylDivisibility.blockEmb S τ (map φ f) := by
  simp only [Formalism.GradedWeylDivisibility.blockEmb]
  exact map_rename φ _ f

/- English proof (translation)
Use `choose Q hQ using fun τ => ssB_int K (lam τ).natW (i τ)`. Use `⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℤ τ (Q τ), ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`. Unfold `bVVfun ten`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[fk_map_blockEmb]`. Conclude with `congrArg _ (hQ τ)`.
-/
theorem bVVfun_int (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (i : VVIdx lam) :
    ∃ P : MvPolynomial (ι × Fin n × Fin n) ℤ, bVVfun K lam i = MvPolynomial.map (Int.castRingHom K) P := by
  choose Q hQ using fun τ => ssB_int K (lam τ).natW (i τ)
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℤ τ (Q τ), ?_⟩
  rw [map_prod]
  unfold bVVfun ten
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [fk_map_blockEmb]
  exact congrArg _ (hQ τ)

end Formalism.L2.DIV

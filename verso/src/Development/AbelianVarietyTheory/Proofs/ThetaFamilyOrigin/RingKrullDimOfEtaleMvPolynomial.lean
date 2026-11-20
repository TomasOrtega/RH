import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothDim

/- English proof (translation)
Use `letI := Ideal.Quotient.field m`. Use `haveI : Module.Finite K (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ m)`. Use `haveI : Algebra.IsIntegral R (B ⧸ m) := Algebra.IsIntegral.tower_top K`. Establish `h` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (⊥ : Ideal (B ⧸ m))`. Rewrite `h` using `[IsScalarTower.algebraMap_eq R B (B ⧸ m), ← Ideal.comap_comap, Ideal.Quotient.algebraMap_eq, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Then use the resulting hypothesis.
-/
theorem isMaximal_under_of_finiteType (K R B : Type*) [Field K] [CommRing R] [CommRing B]
    [Algebra K R] [Algebra K B] [Algebra R B] [IsScalarTower K R B] [Algebra.FiniteType K B]
    (m : Ideal B) [m.IsMaximal] : (m.under R).IsMaximal := by
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ m)
  haveI : Algebra.IsIntegral R (B ⧸ m) := Algebra.IsIntegral.tower_top K
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (⊥ : Ideal (B ⧸ m))
  rwa [IsScalarTower.algebraMap_eq R B (B ⧸ m), ← Ideal.comap_comap, Ideal.Quotient.algebraMap_eq,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h

/- English proof (translation)
Establish `hR : ringKrullDim (MvPolynomial (Fin g) K) = g`. Simplify using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hR]`. Use `Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin g) K) B)) fun P Q hPQ => ?_` and prove the remaining obligations.

Use `lt_of_le_of_ne (Ideal.comap_mono hPQ.le) fun h => hPQ.ne ?_` and prove the remaining obligations. Conclude with `PrimeSpectrum.ext (Algebra.QuasiFinite.eq_of_le_of_under_eq (R := MvPolynomial (Fin g) K) _ _ hPQ.le (congrArg PrimeSpectrum.asIdeal h))`. Take `⟨m, hm⟩` from `Ideal.exists_maximal B`. Use `letI : Algebra K B := ((algebraMap (MvPolynomial (Fin g) K) B).comp (algebraMap K (MvPolynomial (Fin g) K))).toAlgebra`. Use `haveI : IsScalarTower K (MvPolynomial (Fin g) K) B := IsScalarTower.of_algebraMap_eq' rfl`.

Use `haveI : Algebra.FiniteType K B := Algebra.FiniteType.trans (S := MvPolynomial (Fin g) K) inferInstance inferInstance`. Use `haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B`. Use `haveI hp := isMaximal_under_of_finiteType K (MvPolynomial (Fin g) K) B m`. Establish `h1` using `ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K g (m.under (MvPolynomial (Fin g) K))`. Use `letI := Ideal.Quotient.field (m.under (MvPolynomial (Fin g) K))`.

Rewrite `h1` using `[ringKrullDim_eq_zero_of_field, add_zero]`. Establish `h2 : (m.under (MvPolynomial (Fin g) K)).height ≤ m.height`. Rewrite using `[Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (m.under (MvPolynomial (Fin g) K)) m]`. Conclude with `le_self_add`. Rewrite using `[← h1]`.

Conclude with `(WithBot.coe_le_coe.mpr h2).trans Ideal.height_le_ringKrullDim_of_isPrime`.
-/
theorem ringKrullDim_of_etale_mvPolynomial (K B : Type*) [Field K] [CommRing B] [Nontrivial B]
    (g : ℕ) [Algebra (MvPolynomial (Fin g) K) B] [Algebra.Etale (MvPolynomial (Fin g) K) B] :
    ringKrullDim B = g := by
  have hR : ringKrullDim (MvPolynomial (Fin g) K) = g := by
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  apply le_antisymm
  · rw [← hR]
    refine Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin g) K) B)) fun P Q hPQ => ?_
    refine lt_of_le_of_ne (Ideal.comap_mono hPQ.le) fun h => hPQ.ne ?_
    exact PrimeSpectrum.ext (Algebra.QuasiFinite.eq_of_le_of_under_eq
      (R := MvPolynomial (Fin g) K) _ _ hPQ.le (congrArg PrimeSpectrum.asIdeal h))
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    letI : Algebra K B := ((algebraMap (MvPolynomial (Fin g) K) B).comp
      (algebraMap K (MvPolynomial (Fin g) K))).toAlgebra
    haveI : IsScalarTower K (MvPolynomial (Fin g) K) B := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.FiniteType K B := Algebra.FiniteType.trans
      (S := MvPolynomial (Fin g) K) inferInstance inferInstance
    haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
    haveI hp := isMaximal_under_of_finiteType K (MvPolynomial (Fin g) K) B m
    have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K g
      (m.under (MvPolynomial (Fin g) K))
    letI := Ideal.Quotient.field (m.under (MvPolynomial (Fin g) K))
    rw [ringKrullDim_eq_zero_of_field, add_zero] at h1
    have h2 : (m.under (MvPolynomial (Fin g) K)).height ≤ m.height := by
      rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
        (m.under (MvPolynomial (Fin g) K)) m]
      exact le_self_add
    rw [← h1]
    exact (WithBot.coe_le_coe.mpr h2).trans Ideal.height_le_ringKrullDim_of_isPrime

/- English proof (translation)
Use `letI := hK.toField`. Take `⟨φ, -, hφ⟩` from `hf.exists_etale_mvPolynomial`. Use `algebraize [φ]`. Conclude with `ringKrullDim_of_etale_mvPolynomial K B g`.
-/
theorem ringKrullDim_of_isStandardSmooth {K B : Type*} [CommRing K] (hK : IsField K) [CommRing B]
    [Nontrivial B] {g : ℕ} {f : K →+* B} (hf : f.IsStandardSmoothOfRelativeDimension g) :
    ringKrullDim B = g := by
  letI := hK.toField
  obtain ⟨φ, -, hφ⟩ := hf.exists_etale_mvPolynomial
  algebraize [φ]
  exact ringKrullDim_of_etale_mvPolynomial K B g

/- English proof (translation)
Establish `key : ∀ q : Ideal A, q.IsPrime → ∃ t : A, Disjoint (Submonoid.powers t : Set A) q ∧ ringKrullDim (Localization.Away t) = d`. Introduce `q hq`. Choose the witnesses or unpack the hypotheses as in `⟨t, hts, htq⟩ : ∃ t ∈ s, t ∉ q := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hq.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hc))`. Establish `disj : Disjoint (Submonoid.powers t : Set A) (q : Set A)` using `(Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr htq`. Establish `hP` using `IsLocalization.isPrime_of_isPrime_disjoint (.powers t) (Localization.Away t) _ hq disj`. Use `⟨t, disj, h t hts ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Conclude with `hP.ne_top (Subsingleton.elim _ _)`. Apply `le_antisymm` to reduce the goal to its premises. Use `(ringKrullDim_le_iff_height_le d).mpr fun q hq => ?_` and prove the remaining obligations. Take `⟨t, disj, ht⟩` from `key q hq`.

Establish `hP` using `IsLocalization.isPrime_of_isPrime_disjoint (.powers t) (Localization.Away t) _ hq disj`. Rewrite using `[← IsLocalization.height_map_of_disjoint (S := Localization.Away t) _ q disj, ← ht]`. Conclude with `Ideal.height_le_ringKrullDim_of_isPrime`. Take `⟨m, hm⟩` from `Ideal.exists_maximal A`. Take `⟨t, -, ht⟩` from `key m hm.isPrime`.

Rewrite using `[← ht]`. Use `(ringKrullDim_le_iff_height_le _).mpr fun q hq => ?_` and prove the remaining obligations. Rewrite using `[← IsLocalization.height_under (R := A) (.powers t) q]`. Conclude with `Ideal.height_le_ringKrullDim_of_isPrime`.
-/
theorem ringKrullDim_eq_of_span_eq_top {A : Type*} [CommRing A] [Nontrivial A] (s : Set A)
    (hs : Ideal.span s = ⊤) (d : WithBot ℕ∞)
    (h : ∀ t ∈ s, Nontrivial (Localization.Away t) → ringKrullDim (Localization.Away t) = d) :
    ringKrullDim A = d := by
  have key : ∀ q : Ideal A, q.IsPrime → ∃ t : A, Disjoint (Submonoid.powers t : Set A) q ∧
      ringKrullDim (Localization.Away t) = d := by
    intro q hq
    obtain ⟨t, hts, htq⟩ : ∃ t ∈ s, t ∉ q := by
      by_contra hc
      push Not at hc
      exact hq.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hc))
    have disj : Disjoint (Submonoid.powers t : Set A) (q : Set A) :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr htq
    have hP := IsLocalization.isPrime_of_isPrime_disjoint (.powers t) (Localization.Away t) _ hq
      disj
    refine ⟨t, disj, h t hts ?_⟩
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hP.ne_top (Subsingleton.elim _ _)
  apply le_antisymm
  · refine (ringKrullDim_le_iff_height_le d).mpr fun q hq => ?_
    obtain ⟨t, disj, ht⟩ := key q hq
    have hP := IsLocalization.isPrime_of_isPrime_disjoint (.powers t) (Localization.Away t) _ hq
      disj
    rw [← IsLocalization.height_map_of_disjoint (S := Localization.Away t) _ q disj, ← ht]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    obtain ⟨t, -, ht⟩ := key m hm.isPrime
    rw [← ht]
    refine (ringKrullDim_le_iff_height_le _).mpr fun q hq => ?_
    rw [← IsLocalization.height_under (R := A) (.powers t) q]
    exact Ideal.height_le_ringKrullDim_of_isPrime

/- English proof (translation)
Introduce `K _ X p g hp U hU hne`. Use `haveI : Nonempty U := hne.to_subtype`. Establish `hK : IsField Γ(Sp K, ⊤)` using `MulEquiv.isField (Field.toIsField K) (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv`. Take `⟨s, hs, h⟩` from `HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top`. Conclude with `ringKrullDim_eq_of_span_eq_top s hs _ fun t ht _ => ringKrullDim_of_isStandardSmooth hK (h t ht)`.
-/
theorem ringKrullDim_affineOpen :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (g : ℕ),
      SmoothOfRelativeDimension g p → ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty →
        ringKrullDim Γ(X, U) = g := by
  intro K _ X p g hp U hU hne
  haveI : Nonempty U := hne.to_subtype
  have hK : IsField Γ(Sp K, ⊤) :=
    MulEquiv.isField (Field.toIsField K) (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨s, hs, h⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) p hp
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  exact ringKrullDim_eq_of_span_eq_top s hs _ fun t ht _ =>
    ringKrullDim_of_isStandardSmooth hK (h t ht)

end GlobalTheory.SmoothDim

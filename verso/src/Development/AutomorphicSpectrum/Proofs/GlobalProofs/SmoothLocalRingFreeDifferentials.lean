import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.ResKCoords

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨t, ht, htP⟩ : ∃ t ∈ s, t ∉ P := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `(‹P.IsPrime›).ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))`. Establish `hle : Submonoid.powers t ≤ P.primeCompl`.

Introduce and unpack `_ ⟨n, rfl⟩`. Conclude with `fun hm => htP (‹P.IsPrime›.mem_of_pow_mem n hm)`. Use `letI : Algebra (Localization.Away t) (Localization.AtPrime P) := IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers t) P.primeCompl hle`. Use `haveI : IsScalarTower A (Localization.Away t) (Localization.AtPrime P) := IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle`. Use `haveI : IsScalarTower K (Localization.Away t) (Localization.AtPrime P) := IsScalarTower.of_algebraMap_eq fun x => by`.

Rewrite using `[IsScalarTower.algebraMap_apply K A (Localization.Away t), ← IsScalarTower.algebraMap_apply A (Localization.Away t) (Localization.AtPrime P), ← IsScalarTower.algebraMap_apply K A (Localization.AtPrime P)]`. Use `haveI := IsLocalization.isLocalization_of_submonoid_le (Localization.Away t) (Localization.AtPrime P) (Submonoid.powers t) P.primeCompl hle`. Use `haveI : Algebra.FormallyEtale (Localization.Away t) (Localization.AtPrime P) := Algebra.FormallyEtale.of_isLocalization (P.primeCompl.map (algebraMap A (Localization.Away t)))`. Use `haveI := h t ht`. Use `haveI : Nontrivial (Localization.Away t) := (algebraMap (Localization.Away t) (Localization.AtPrime P)).domain_nontrivial`.

Use `haveI : Algebra.IsStandardSmooth K (Localization.Away t) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D`. Establish `r` using `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K) (S := Localization.Away t) D`. Set `e` to `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (Localization.Away t) (Localization.AtPrime P)`. Use `⟨.of_equiv e, .equiv e, ?_⟩` and prove the remaining obligations. Rewrite using `[← e.finrank_eq, Module.finrank_baseChange, Module.finrank, r]`.

Simplify using the standard rewrite rules.
-/
theorem kaehler_atPrime_of_away (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t))
    (P : Ideal A) [P.IsPrime] :
    Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  obtain ⟨t, ht, htP⟩ : ∃ t ∈ s, t ∉ P := by
    by_contra hc
    push_neg at hc
    exact (‹P.IsPrime›).ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have hle : Submonoid.powers t ≤ P.primeCompl := by
    rintro _ ⟨n, rfl⟩
    exact fun hm => htP (‹P.IsPrime›.mem_of_pow_mem n hm)
  letI : Algebra (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers t) P.primeCompl hle
  haveI : IsScalarTower A (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI : IsScalarTower K (Localization.Away t) (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K A (Localization.Away t),
        ← IsScalarTower.algebraMap_apply A (Localization.Away t) (Localization.AtPrime P),
        ← IsScalarTower.algebraMap_apply K A (Localization.AtPrime P)]
  haveI := IsLocalization.isLocalization_of_submonoid_le (Localization.Away t) (Localization.AtPrime P)
    (Submonoid.powers t) P.primeCompl hle
  haveI : Algebra.FormallyEtale (Localization.Away t) (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization
      (P.primeCompl.map (algebraMap A (Localization.Away t)))
  haveI := h t ht
  haveI : Nontrivial (Localization.Away t) :=
    (algebraMap (Localization.Away t) (Localization.AtPrime P)).domain_nontrivial
  haveI : Algebra.IsStandardSmooth K (Localization.Away t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  have r := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K)
    (S := Localization.Away t) D
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (Localization.Away t)
    (Localization.AtPrime P)
  refine ⟨.of_equiv e, .equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_baseChange, Module.finrank, r]
  simp

/- English proof (translation)
Use `RingHom.finitePresentation_algebraMap.1 (RingHom.finitePresentation_ofLocalizationSpanTarget (algebraMap K A) s hs fun r => ?_)` and prove the remaining obligations. Use `haveI := h r.1 r.2`. Use `haveI : Algebra.IsStandardSmooth K (Localization.Away r.1) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D`. Rewrite using `[← IsScalarTower.algebraMap_eq K A (Localization.Away r.1)]`. Conclude with `(RingHom.finitePresentation_algebraMap).2 inferInstance`.
-/
theorem finitePresentation_of_away (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t)) :
    Algebra.FinitePresentation K A := by
  refine RingHom.finitePresentation_algebraMap.1
    (RingHom.finitePresentation_ofLocalizationSpanTarget (algebraMap K A) s hs fun r => ?_)
  haveI := h r.1 r.2
  haveI : Algebra.IsStandardSmooth K (Localization.Away r.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  rw [← IsScalarTower.algebraMap_eq K A (Localization.Away r.1)]
  exact (RingHom.finitePresentation_algebraMap).2 inferInstance

/- English proof (translation)
Introduce `K _ D Y g hg U P _`. Use `letI := secAlgebra g U.1`. Take `⟨s, hs, h'⟩` from `HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) g hg ⟨⊤, isAffineOpen_top _⟩ U (fun _ _ => trivial)`. Establish `key : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t)`. Introduce `t ht`.

Establish `h2` using `(RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := D)).2 _ (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv (h' t ht)`. Rewrite using `[← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]`. Rewrite using `[IsScalarTower.algebraMap_eq K Γ(Y, U.1) (Localization.Away t)]`. Conclude with `h2`. Conclude with `⟨finitePresentation_of_away K _ D s hs key, kaehler_atPrime_of_away K _ D s hs key P⟩`.
-/
theorem finitePresentation_and_kaehler_atPrime :
    ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g →
      ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime],
      letI := secAlgebra g U.1
      Algebra.FinitePresentation K Γ(Y, U.1) ∧
        Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  intro K _ D Y g hg U P _
  letI := secAlgebra g U.1
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) g hg
    ⟨⊤, isAffineOpen_top _⟩ U (fun _ _ => trivial)
  have key : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t) := by
    intro t ht
    have h2 := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := D)).2
      _ (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv (h' t ht)
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    rw [IsScalarTower.algebraMap_eq K Γ(Y, U.1) (Localization.Away t)]
    exact h2
  exact ⟨finitePresentation_of_away K _ D s hs key, kaehler_atPrime_of_away K _ D s hs key P⟩

end GlobalTheory.CompanionTheory.ResKCoords

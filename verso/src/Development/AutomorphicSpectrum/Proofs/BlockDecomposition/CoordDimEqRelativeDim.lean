import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.CoordCard

/- English proof (translation)
Set `b` to `KaehlerDifferential.mvPolynomialBasis K (Fin m)`. Set `b'` to `(b.baseChange L).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial (Fin m) K) L)`. Establish `hr` using `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K) (S := L) n`. Establish `h1` using `b'.mk_eq_rank''`. Rewrite `h1` using `[hr]`.

Simplify using `using h1`.
-/
theorem card_eq_of_etale {K L : Type} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] {m n : ℕ}
    [Algebra (MvPolynomial (Fin m) K) L] [IsScalarTower K (MvPolynomial (Fin m) K) L]
    [Algebra.FormallyEtale (MvPolynomial (Fin m) K) L]
    [Algebra.IsStandardSmoothOfRelativeDimension n K L] : m = n := by
  let b := KaehlerDifferential.mvPolynomialBasis K (Fin m)
  let b' := (b.baseChange L).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial (Fin m) K) L)
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K) (S := L) n
  have h1 := b'.mk_eq_rank''
  rw [hr] at h1
  simpa using h1

/- English proof (translation)
Use `letI iPA : Algebra (MvPolynomial (Fin m) K) A := φ.toAlgebra`. Use `letI iKL : Algebra K L := ((algebraMap A L).comp g).toAlgebra`. Use `letI iPL : Algebra (MvPolynomial (Fin m) K) L := ((algebraMap A L).comp φ).toAlgebra`. Use `haveI : IsScalarTower (MvPolynomial (Fin m) K) A L := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower K (MvPolynomial (Fin m) K) L := IsScalarTower.of_algebraMap_eq fun r => by`.

Express the relevant statement in the definitionally equal form `algebraMap A L (g r) = algebraMap A L (φ (MvPolynomial.C r))`. Rewrite using `[hφ]`. Use `haveI : Algebra.Etale (MvPolynomial (Fin m) K) A := hE`. Use `haveI : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)`. Use `haveI : Algebra.FormallyEtale (MvPolynomial (Fin m) K) L := Algebra.FormallyEtale.comp _ A _`.

Use `haveI : Algebra.IsStandardSmoothOfRelativeDimension n K L := hf`. Conclude with `card_eq_of_etale (K := K) (L := L)`.
-/
theorem card_eq_of_away {K A L : Type} [Field K] [CommRing A] [CommRing L] [Nontrivial L] [Algebra A L] {m n : ℕ}
    (t : A) [IsLocalization.Away t L] (g : K →+* A) (φ : MvPolynomial (Fin m) K →+* A)
    (hφ : ∀ r, φ (MvPolynomial.C r) = g r) (hE : φ.Etale)
    (hf : RingHom.IsStandardSmoothOfRelativeDimension n ((algebraMap A L).comp g)) : m = n := by
  letI iPA : Algebra (MvPolynomial (Fin m) K) A := φ.toAlgebra
  letI iKL : Algebra K L := ((algebraMap A L).comp g).toAlgebra
  letI iPL : Algebra (MvPolynomial (Fin m) K) L := ((algebraMap A L).comp φ).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin m) K) A L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (MvPolynomial (Fin m) K) L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap A L (g r) = algebraMap A L (φ (MvPolynomial.C r))
      rw [hφ]
  haveI : Algebra.Etale (MvPolynomial (Fin m) K) A := hE
  haveI : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin m) K) L := Algebra.FormallyEtale.comp _ A _
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K L := hf
  exact card_eq_of_etale (K := K) (L := L)

/- English proof (translation)
Introduce `K _ X q n hn V hV m c`. Take `⟨x, hx⟩` from `hV`. Establish `hnt : Nontrivial Γ(X, V)` using `(X.presheaf.germ V x hx).hom.domain_nontrivial`. Take `⟨s, hs, h'⟩` from `HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) q hn ⟨⊤, isAffineOpen_top _⟩ ⟨V, c.affine⟩ le_top`. Take `⟨p, hp⟩` from `Ideal.exists_maximal Γ(X, V)`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by`. Assume the negation of the conclusion as `hc`. Conclude with `hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))`. Establish `: Nontrivial (Localization.Away t)`. Assume the negation of the conclusion as `hc`.

Take `⟨k, hk⟩` from `(IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1 (not_nontrivial_iff_subsingleton.1 hc)`. Conclude with `htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))`. Establish `h₁` using `h' t ht`. Set `e : K ≃+* Γ(Spec (CommRingCat.of K), ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv`. Establish `hf : RingHom.IsStandardSmoothOfRelativeDimension n ((algebraMap Γ(X, V) (Localization.Away t)).comp (strV q V))` using `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e h₁`.

Conclude with `card_eq_of_away (L := Localization.Away t) t (strV q V) (MvPolynomial.eval₂Hom (strV q V) c.t) (fun r => by simp) c.etale hf`.
-/
theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n q] {V : X.Opens}, (V : Set X).Nonempty → ∀ {m : ℕ} (c : Coord q V m), m = n := by
  intro K _ X q n hn V hV m c
  obtain ⟨x, hx⟩ := hV
  have hnt : Nontrivial Γ(X, V) := (X.presheaf.germ V x hx).hom.domain_nontrivial
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) q hn
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, c.affine⟩ le_top
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(X, V)
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1 (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  let e : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have hf : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap Γ(X, V) (Localization.Away t)).comp (strV q V)) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e h₁
  exact card_eq_of_away (L := Localization.Away t) t (strV q V) (MvPolynomial.eval₂Hom (strV q V) c.t)
    (fun r => by simp) c.etale hf

end GlobalTheory.CompanionTheory.CoordCard

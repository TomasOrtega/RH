import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterRecCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationSupercuspidalSupportMultiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTameWeilDeligneIffWildCharpolyStatement

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcDepth

/- English proof (translation)
Establish `e : (X - 1 : ℂ[X]) = X - C 1` using `by simp`. Rewrite `hd`, the goal using `[e]`. Take `⟨i, -, hi⟩` from `(dvd_prime_pow (prime_X_sub_C (1 : ℂ)) n).1 hd`. Establish `hpi` using `eq_of_monic_of_associated hp ((monic_X_sub_C (1 : ℂ)).pow i) hi`. Rewrite using `[hpi, natDegree_pow, natDegree_X_sub_C, mul_one]`.
-/
theorem eq_pow_natDegree_of_dvd {p : ℂ[X]} (hp : p.Monic) {n : ℕ} (hd : p ∣ (X - 1) ^ n) :
    p = (X - 1) ^ p.natDegree := by
  have e : (X - 1 : ℂ[X]) = X - C 1 := by simp
  rw [e] at hd ⊢
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C (1 : ℂ)) n).1 hd
  have hpi := eq_of_monic_of_associated hp ((monic_X_sub_C (1 : ℂ)).pow i) hi
  rw [hpi, natDegree_pow, natDegree_X_sub_C, mul_one]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih => simp [ih, pow_add]`.
-/
theorem prod_map_pow {α : Type*} (q : ℂ[X]) (f : α → ℕ) (s : Multiset α) :
    (s.map fun y => q ^ f y).prod = q ^ (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, pow_add]

/- English proof (translation)
Introduce `hDZC hDZI hEx hZel hGeo hBZ E Ω _ _ _ _ _ A w h rc hrc x`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Take `⟨a, ha, ε, -, hL⟩` from `id hrc`. Take `⟨m, hm⟩` from `hEx _ x`. Establish `hs : HasSupport x.rep (msupp m)` using `GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZel _ m x hm`.

Establish `hcp` using `GlobalTheory.T.central_character_rec_compatible hEx hZel hGeo hBZ E Ω A w h a ha _ rc hL x (msupp m) hs`. Establish `hdy : ∀ y ∈ msupp m, (fixed y.rep (KOne (w.adicCompletion E) (Fin y.1)) ≠ ⊥ ↔ IsTameWD (rc y))` using `fun y hy => hDZC E Ω A w h rc hrc y (hs.isCusp hy)`. Establish `htame : IsTameWD (rc x) ↔ ∀ y ∈ msupp m, IsTameWD (rc y)`. Simplify using `only [GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly E Ω A w h]`. Prove the components needed by the constructor for the conclusion.

Introduce `H y hy σ hσ`. Establish `hdvd : (rc y).charPol σ ∣ (rc x).charPol σ`. Rewrite using `[hcp σ]`. Conclude with `Multiset.dvd_prod (Multiset.mem_map_of_mem _ hy)`. Rewrite `hdvd` using `[H σ hσ]`.

Establish `e` using `eq_pow_natDegree_of_dvd ((rc y).charPol_monic σ) hdvd`. Rewrite `e` using `[WD.charPol_natDegree]`. Then use the resulting hypothesis. Introduce `H σ hσ`. Rewrite using `[hcp σ, Multiset.map_congr rfl (fun y hy => H y hy σ hσ), prod_map_pow]`. Use `congr 1`.

Rewrite using `[hL.dim x, Multiset.map_congr rfl (fun y _ => hL.dim y), hs.sum_fst, Fintype.card_fin]`. Rewrite using `[htame]`. Prove the components needed by the constructor for the conclusion. Introduce `hx y hy`. Rewrite using `[← hdy y hy]`.

Take `⟨n, xs, hxs, hcs⟩` from `hs`. Establish `H` using `GlobalTheory.SmGL.depthZeroSupport _ x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep) n (fun i => (xs i).1) (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (xs i).2.rep) hcs ((Submodule.ne_bot_iff _).1 hx)`. Rewrite `hy` using `[← hxs]`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hy`. Take `⟨v, hv, hv0⟩` from `H i`.

Conclude with `(Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩`. Introduce `H`. Conclude with `hDZI _ x (msupp m) hs fun y hy => (hdy y hy).2 (H y hy)`.
-/
theorem fixed_ne_bot_iff_isTameWD : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL →
    ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc →
      ∀ x : IrrGL (w.adicCompletion E), fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x) := by
  intro hDZC hDZI hEx hZel hGeo hBZ E Ω _ _ _ _ _ A w h rc hrc x
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨a, ha, ε, -, hL⟩ := id hrc
  obtain ⟨m, hm⟩ := hEx _ x
  have hs : HasSupport x.rep (msupp m) := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZel _ m x hm
  have hcp := GlobalTheory.T.central_character_rec_compatible hEx hZel hGeo hBZ E Ω A w h a ha _ rc hL x (msupp m) hs
  have hdy : ∀ y ∈ msupp m, (fixed y.rep (KOne (w.adicCompletion E) (Fin y.1)) ≠ ⊥ ↔ IsTameWD (rc y)) :=
    fun y hy => hDZC E Ω A w h rc hrc y (hs.isCusp hy)
  have htame : IsTameWD (rc x) ↔ ∀ y ∈ msupp m, IsTameWD (rc y) := by
    simp only [GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly E Ω A w h]
    constructor
    · intro H y hy σ hσ
      have hdvd : (rc y).charPol σ ∣ (rc x).charPol σ := by
        rw [hcp σ]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hy)
      rw [H σ hσ] at hdvd
      have e := eq_pow_natDegree_of_dvd ((rc y).charPol_monic σ) hdvd
      rwa [WD.charPol_natDegree] at e
    · intro H σ hσ
      rw [hcp σ, Multiset.map_congr rfl (fun y hy => H y hy σ hσ), prod_map_pow]
      congr 1
      rw [hL.dim x, Multiset.map_congr rfl (fun y _ => hL.dim y), hs.sum_fst, Fintype.card_fin]
  rw [htame]
  constructor
  · intro hx y hy
    rw [← hdy y hy]
    obtain ⟨n, xs, hxs, hcs⟩ := hs
    have H := GlobalTheory.SmGL.depthZeroSupport _ x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep) n (fun i => (xs i).1)
      (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (xs i).2.rep) hcs ((Submodule.ne_bot_iff _).1 hx)
    rw [← hxs] at hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨v, hv, hv0⟩ := H i
    exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  · intro H
    exact hDZI _ x (msupp m) hs fun y hy => (hdy y hy).2 (H y hy)

end GlobalTheory.LlcDepth

end

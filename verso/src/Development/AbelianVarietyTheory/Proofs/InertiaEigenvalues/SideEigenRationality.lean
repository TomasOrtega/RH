import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenvalueSystemSetFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsAfterLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationCoefFieldFiniteRangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolysStatement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusGoodSplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenUnitaryStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LargeO

def sysPol (n : ℕ) {E : Type} [Field E] [NumberField E] (c : HeightOneSpectrum (𝓞 E) → ℕ → ℂ)
    (v : HeightOneSpectrum (𝓞 E)) : ℂ[X] :=
  X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((normV v : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c v k) * X ^ (n - k)

def BigOk (D : D7) (l : ℕ) [Fact l.Prime] (Q : Finset (PlE D.host)) (Es : Set (PlE D.host → ℕ → ℂ))
    (ι : Qbar l ≃+* ℂ) (Sf : Finset ℂ) : Prop :=
  ∀ c ∈ Es, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ Sf, ι.symm z ∈ K) →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar l),
      Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l))) → IsSSRep ρ →
      (∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) →
        ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B v →
          IsFrob (F := D.host.E) B (normV v) σ →
          ((ρ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l)).charpoly.map ι.toRingHom = sysPol D.R.nV c v) →
      ∃ Pm : GL (Fin D.R.nV) (Qbar l), ∀ g s t,
        ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar l)) s t ∈ K

/- English proof (translation)
Introduce `c hc K hK` and use `h c hc K fun z hz => hK z (hs hz)`.
-/
theorem bigOk_mono {D : D7} {l : ℕ} [Fact l.Prime] {Q : Finset (PlE D.host)} {Es : Set (PlE D.host → ℕ → ℂ)}
    {ι : Qbar l ≃+* ℂ} {Sf Sf' : Finset ℂ} (h : BigOk D l Q Es ι Sf) (hs : Sf ⊆ Sf') : BigOk D l Q Es ι Sf' :=
  fun c hc K hK => h c hc K fun z hz => hK z (hs hz)

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `h`.
-/
theorem bigOk_cast {D : D7} {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (e : p = q) {Q : Finset (PlE D.host)}
    {Es : Set (PlE D.host → ℕ → ℂ)} {ι : Qbar p ≃+* ℂ} {Sf : Finset ℂ} (h : BigOk D p Q Es ι Sf) :
    BigOk D q Q Es (qCast e ι) Sf := by
  subst e; exact h

/- English proof (translation)
Set `Good : PlE D.host → Prop` to `fun v => IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q`. Set `U : Set (G D.host.E D.nd.Om)` to `{σ | ∃ v, Good v ∧ ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ}`. Establish `hU : Dense U` using `GlobalTheory.T.dense_frobenius_goodSplitPlaces D l Q (Fact.out) hch`. Set `p : (PlE D.host → ℕ → ℂ) → G D.host.E D.nd.Om → ℂ[X]` to `fun c σ => if h : σ ∈ U then sysPol D.R.nV c (Classical.choose h) else 0`. Establish `hS` using `fun c => GlobalTheory.T.exists_finite_coefficient_set_frobenius_charpolys l ι D.host.E D.nd.Om D.R.nV U (p c) hU`.

Use `choose Sc hSc using hS`. Use `⟨hE.toFinset.biUnion Sc, ?_⟩` and prove the remaining obligations. Introduce `c hc K hK ρ hcont hss hchar`. Use `hSc c K (fun z hz => hK z (Finset.mem_biUnion.2 ⟨c, hE.mem_toFinset.2 hc, hz⟩)) ρ hcont hss ?_` and prove the remaining obligations. Introduce `σ hσ`.

Simplify using `only [p, dif_pos hσ]`. Take `⟨hg, B, hB, hF⟩` from `Classical.choose_spec hσ`. Conclude with `hchar _ hg B σ hB hF`.
-/
theorem exists_bigOk (D : D7) (l : ℕ) [Fact l.Prime] (Q : Finset (PlE D.host)) (Es : Set (PlE D.host → ℕ → ℂ))
    (ι : Qbar l ≃+* ℂ) (hE : Es.Finite) (hch : GlobalTheory.RowTie.ChebSplit D.nd) : ∃ Sf, BigOk D l Q Es ι Sf := by
  classical
  let Good : PlE D.host → Prop := fun v =>
    IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q
  let U : Set (G D.host.E D.nd.Om) := {σ | ∃ v, Good v ∧ ∃ B : ValuationSubring D.nd.Om,
    IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ}
  have hU : Dense U := GlobalTheory.T.dense_frobenius_goodSplitPlaces D l Q (Fact.out) hch
  let p : (PlE D.host → ℕ → ℂ) → G D.host.E D.nd.Om → ℂ[X] := fun c σ =>
    if h : σ ∈ U then sysPol D.R.nV c (Classical.choose h) else 0
  have hS := fun c => GlobalTheory.T.exists_finite_coefficient_set_frobenius_charpolys l ι D.host.E D.nd.Om D.R.nV U (p c) hU
  choose Sc hSc using hS
  refine ⟨hE.toFinset.biUnion Sc, ?_⟩
  intro c hc K hK ρ hcont hss hchar
  refine hSc c K (fun z hz => hK z (Finset.mem_biUnion.2 ⟨c, hE.mem_toFinset.2 hc, hz⟩)) ρ hcont hss ?_
  intro σ hσ
  simp only [p, dif_pos hσ]
  obtain ⟨hg, B, hB, hF⟩ := Classical.choose_spec hσ
  exact hchar _ hg B σ hB hF

/- English proof (translation)
Introduce `D i x ρ hρ v hv B σ hB hF`. Establish `hso : SplitOut D.nd i v` using `⟨hv.1, hv.2.1, fun h => hv.2.2.1 ((D.nd.S_def i v).1 h), hv.2.2.2⟩`. Rewrite using `[hρ.2.2 v hso B σ hB hF, Polynomial.map_map]`. Establish `hcomp : (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) = iotaOC D i` using `rfl`. Rewrite using `[hcomp]`.

Unfold `heckePol sysPol`. Rewrite using `[Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Take `⟨hk1, hk2⟩` from `Finset.mem_Icc.1 hk`.

Establish `hg : GenAt D (D.nd.l i) (D.nd.Q i) v k` using `⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hk1, hk2⟩`. Simplify using `only [ptSys, if_pos hg, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_mul, map_pow, map_neg, map_one, map_natCast, Polynomial.map_neg, Polynomial.map_one, Polynomial.map_natCast]`.
-/
theorem charpoly_pt : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))),
    SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → ∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (D.nd.l i) ∧
      v ∉ placesS D (D.nd.l i) ∧ v ∉ D.nd.Q i) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ →
      ((ρ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly.map (D.naut.iotaQC i).toRingHom =
        sysPol D.R.nV (ptSys D i x) v := by
  intro D i x ρ hρ v hv B σ hB hF
  have hso : SplitOut D.nd i v := ⟨hv.1, hv.2.1, fun h => hv.2.2.1 ((D.nd.S_def i v).1 h), hv.2.2.2⟩
  rw [hρ.2.2 v hso B σ hB hF, Polynomial.map_map]
  have hcomp : (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) = iotaOC D i := rfl
  rw [hcomp]
  unfold heckePol sysPol
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  have hg : GenAt D (D.nd.l i) (D.nd.Q i) v k := ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hk1, hk2⟩
  simp only [ptSys, if_pos hg, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_mul,
    map_pow, map_neg, map_one, map_natCast, Polynomial.map_neg, Polynomial.map_one, Polynomial.map_natCast]

/- English proof (translation)
Introduce `R H what₂ N A i a ρ P hc hP`. Set `ρ' : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))` to `(MulAut.conj P⁻¹).toMonoidHom.comp ρ`. Establish `hρ' : ∀ g, ρ' g = P⁻¹ * ρ g * P` using `fun g => by`. Simplify using `[ρ', MulAut.conj_apply]`. Establish `hc' : SumRepresentations.At.ContQ N i ρ'`.

Unfold `SumRepresentations.At.ContQ at hc ⊢`. Establish `e : (fun g => ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) = fun g => ((P⁻¹ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) * ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) * ((P : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))`. Use function extensionality and compare the values at `g`. Rewrite using `[hρ']`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `(continuous_const.matrix_mul hc).matrix_mul continuous_const`. Take `⟨r, Pm, hr⟩` from `GlobalTheory.T.exists_integral_model_rep_coeffRing N A i a ρ' hc' (fun g s t => by rw [hρ']; exact hP g s t)`. Use `⟨r, P * Pm, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hr g, hρ', mul_inv_rev]`.

Use `group`.
-/
theorem model_of_conj : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
    (a : ℕ) (ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (P : GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ →
    (∀ g s t, ∃ x, A.iotaQ i x = ((P⁻¹ * ρ g * P : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) →
    ∃ (r : G H.E N.Om →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))),
      ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  intro R H what₂ N A i a ρ P hc hP
  let ρ' : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)) := (MulAut.conj P⁻¹).toMonoidHom.comp ρ
  have hρ' : ∀ g, ρ' g = P⁻¹ * ρ g * P := fun g => by
    simp [ρ', MulAut.conj_apply]
  have hc' : SumRepresentations.At.ContQ N i ρ' := by
    unfold SumRepresentations.At.ContQ at hc ⊢
    have e : (fun g => ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) =
        fun g => ((P⁻¹ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) * ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) *
          ((P : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) := by
      funext g; rw [hρ']; rfl
    rw [e]
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  obtain ⟨r, Pm, hr⟩ := GlobalTheory.T.exists_integral_model_rep_coeffRing N A i a ρ' hc' (fun g s t => by rw [hρ']; exact hP g s t)
  refine ⟨r, P * Pm, fun g => ?_⟩
  rw [hr g, hρ', mul_inv_rev]
  group

/- English proof (translation)
Introduce `hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb`. Establish `hbig : ∀ lam (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.places.resChar lam) (C.Q lam)).Finite → ∃ Sf, @BigOk D (D.what₂.places.resChar lam) ⟨D.what₂.places.resChar_prime lam⟩ (C.Q lam) (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.pla …` using `fun lam j h1 h2 hf => @exists_bigOk D _ ⟨D.what₂.places.resChar_prime lam⟩ _ _ _ hf hcheb`. Set `big : D.what₂.places.Pl → Finset ℂ` to `fun lam => (Finset.range (D.R.m + 1)).biUnion fun j => if h : 1 ≤ j ∧ j ≤ D.R.m then if hf : (EigSet (M (D.what₂.muTw lam) j h.1 h.2) (D.what₂.places.resChar lam) (C.Q lam)).Finite then Classical.choose (hbig lam j h.1 h.2 hf) else ∅ else ∅`. Use `⟨big, fun L hB => ?_⟩` and prove the remaining obligations. Take `⟨Sp, ⟨Au⟩, hss⟩` from `hB`.

Introduce `i x ρ hρ`. Use `haveI : Fact (L.X.nd.l i).Prime := L.X.nd.lPrime i`. Establish `hB' : Built A M C tp.tup big L` using `⟨Sp, ⟨Au⟩, hss⟩`. Take `⟨hfin, hpt⟩` from `GlobalTheory.T.side_eigen_unitary hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB' i x`. Establish `hj` using `L.X.nd.j_range i`.

Establish `hOk : @BigOk D (D.what₂.places.resChar (L.X.nd.w i)) ⟨D.what₂.places.resChar_prime (L.X.nd.w i)⟩ (C.Q (L.X.nd.w i)) (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) hj.1 hj.2) (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))) (A.pl.ι (L.X.nd.w i)) (big (L.X.nd.w i))`. Establish `hc` using `Classical.choose_spec (hbig (L.X.nd.w i) (L.X.nd.j i) hj.1 hj.2 hfin)`. Use `bigOk_mono hc ?_` and prove the remaining obligations. Introduce `z hz`. Use `Finset.mem_biUnion.2 ⟨L.X.nd.j i, Finset.mem_range.2 (by omega), ?_⟩` and prove the remaining obligations.

Rewrite using `[dif_pos hj, dif_pos hfin]`. Conclude with `hz`. Establish `hOk'` using `bigOk_cast (L.X.nd.w_l i) hOk`. Take `⟨K, hK, -, -⟩` from `GlobalTheory.T.localisation_coefField_finite_range (withLoc L).nd (withLoc L).naut i`. Establish `hcont` using `(GlobalTheory.T.contains_after_localization D cf jE A M C tp.tup big L hB' i).1`.

Establish `hKbig : ∀ z ∈ big (L.X.nd.w i), (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).symm z ∈ K`. Introduce `z hz`. Take `⟨y, hy⟩` from `hcont z hz`. Establish `hy' : L.Y.naut.iotaQC i (L.Y.naut.iotaQ i y) = z` using `hy`. Rewrite `hy'` using `[Au.iotaQC i]`.

Rewrite using `[← hy', RingEquiv.symm_apply_apply]`. Conclude with `(hK _).2 ⟨y, rfl⟩`. Establish `hQ : L.X.nd.Q i = C.Q (L.X.nd.w i)` using `(Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)`. Establish `hchar` using `charpoly_pt (withLoc L) i x ρ hρ`. Establish `hchar' : ∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (L.X.nd.l i) ∧ v ∉ placesS D (L.X.nd.l i) ∧ v ∉ C.Q (L.X.nd.w i)) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F` using `D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ → (show Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (L.X.nd.l i)) from (ρ σ).val).charpoly.map (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).toRingHom = sysPol D.R.nV (ptSys (withLoc L) i x) v := by`.

Introduce `v hv B σ hB hF`. Rewrite using `[← Au.iotaQC i]`. Conclude with `hchar v ⟨hv.1, hv.2.1, hv.2.2.1, hQ ▸ hv.2.2.2⟩ B σ hB hF`. Take `⟨P, hP⟩` from `hOk' _ hpt K hKbig ρ hρ.1 hρ.2.1 hchar'`. Conclude with `model_of_conj (withLoc L).nd (withLoc L).naut i _ ρ P hρ.1 (fun g s t => (hK _).1 (hP g s t))`.
-/
theorem evO_hypO : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → EvO A M C tp.tup SumRepresentations.hypO := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
  classical
  have hbig : ∀ lam (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
      (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.places.resChar lam) (C.Q lam)).Finite →
      ∃ Sf, @BigOk D (D.what₂.places.resChar lam) ⟨D.what₂.places.resChar_prime lam⟩ (C.Q lam)
        (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.places.resChar lam) (C.Q lam)) (A.pl.ι lam) Sf :=
    fun lam j h1 h2 hf => @exists_bigOk D _ ⟨D.what₂.places.resChar_prime lam⟩ _ _ _ hf hcheb
  let big : D.what₂.places.Pl → Finset ℂ := fun lam => (Finset.range (D.R.m + 1)).biUnion fun j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then
      if hf : (EigSet (M (D.what₂.muTw lam) j h.1 h.2) (D.what₂.places.resChar lam) (C.Q lam)).Finite then
        Classical.choose (hbig lam j h.1 h.2 hf) else ∅
    else ∅
  refine ⟨big, fun L hB => ?_⟩
  obtain ⟨Sp, ⟨Au⟩, hss⟩ := hB
  intro i x ρ hρ
  haveI : Fact (L.X.nd.l i).Prime := L.X.nd.lPrime i
  have hB' : Built A M C tp.tup big L := ⟨Sp, ⟨Au⟩, hss⟩
  obtain ⟨hfin, hpt⟩ := GlobalTheory.T.side_eigen_unitary hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB' i x
  have hj := L.X.nd.j_range i
  have hOk : @BigOk D (D.what₂.places.resChar (L.X.nd.w i)) ⟨D.what₂.places.resChar_prime (L.X.nd.w i)⟩
      (C.Q (L.X.nd.w i)) (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) hj.1 hj.2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))) (A.pl.ι (L.X.nd.w i)) (big (L.X.nd.w i)) := by
    have hc := Classical.choose_spec (hbig (L.X.nd.w i) (L.X.nd.j i) hj.1 hj.2 hfin)
    refine bigOk_mono hc ?_
    intro z hz
    refine Finset.mem_biUnion.2 ⟨L.X.nd.j i, Finset.mem_range.2 (by omega), ?_⟩
    rw [dif_pos hj, dif_pos hfin]
    exact hz
  have hOk' := bigOk_cast (L.X.nd.w_l i) hOk
  obtain ⟨K, hK, -, -⟩ := GlobalTheory.T.localisation_coefField_finite_range (withLoc L).nd (withLoc L).naut i
  have hcont := (GlobalTheory.T.contains_after_localization D cf jE A M C tp.tup big L hB' i).1
  have hKbig : ∀ z ∈ big (L.X.nd.w i), (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).symm z ∈ K := by
    intro z hz
    obtain ⟨y, hy⟩ := hcont z hz
    have hy' : L.Y.naut.iotaQC i (L.Y.naut.iotaQ i y) = z := hy
    rw [Au.iotaQC i] at hy'
    rw [← hy', RingEquiv.symm_apply_apply]
    exact (hK _).2 ⟨y, rfl⟩
  have hQ : L.X.nd.Q i = C.Q (L.X.nd.w i) :=
    (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
  have hchar := charpoly_pt (withLoc L) i x ρ hρ
  have hchar' : ∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (L.X.nd.l i) ∧ v ∉ placesS D (L.X.nd.l i) ∧
      v ∉ C.Q (L.X.nd.w i)) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ →
      (show Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (L.X.nd.l i)) from (ρ σ).val).charpoly.map
        (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).toRingHom = sysPol D.R.nV (ptSys (withLoc L) i x) v := by
    intro v hv B σ hB hF
    rw [← Au.iotaQC i]
    exact hchar v ⟨hv.1, hv.2.1, hv.2.2.1, hQ ▸ hv.2.2.2⟩ B σ hB hF
  obtain ⟨P, hP⟩ := hOk' _ hpt K hKbig ρ hρ.1 hρ.2.1 hchar'
  exact model_of_conj (withLoc L).nd (withLoc L).naut i _ ρ P hρ.1 (fun g s t => (hK _).1 (hP g s t))

end GlobalTheory.LargeO

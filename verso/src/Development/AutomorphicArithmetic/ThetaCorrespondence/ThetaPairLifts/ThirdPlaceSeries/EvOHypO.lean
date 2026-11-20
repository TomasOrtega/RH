import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenRationality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BuiltFiniteAndMemStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ContainsWithLocStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.LargeO
/- English proof (translation)
Introduce `hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb`. Establish `hbig : ∀ lam (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.places.resChar lam) (C.Q lam)).Finite → ∃ Sf, @BigOk D (D.what₂.places.resChar lam) ⟨D.what₂.places.resChar_prime lam⟩ (C.Q lam) (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.pla …` using `fun lam j h1 h2 hf => @exists_bigOk D _ ⟨D.what₂.places.resChar_prime lam⟩ _ _ _ hf hcheb`. Set `big : D.what₂.places.Pl → Finset ℂ` to `fun lam => (Finset.range (D.R.m + 1)).biUnion fun j => if h : 1 ≤ j ∧ j ≤ D.R.m then if hf : (EigSet (M (D.what₂.muTw lam) j h.1 h.2) (D.what₂.places.resChar lam) (C.Q lam)).Finite then Classical.choose (hbig lam j h.1 h.2 hf) else ∅ else ∅`. Use `⟨big, fun L hB => ?_⟩` and prove the remaining obligations. Take `⟨Sp, ⟨Au⟩, hss⟩` from `hB`.

Introduce `i x ρ hρ`. Use `haveI : Fact (L.X.nd.l i).Prime := L.X.nd.lPrime i`. Establish `hB' : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L` using `⟨Sp, ⟨Au⟩, hss⟩`. Take `⟨hfin, hpt⟩` from `_root_.GlobalTheory.T.side_eigen_unitary_alt hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB' i x`. Establish `hj` using `L.X.nd.j_range i`.

Establish `hOk : @BigOk D (D.what₂.places.resChar (L.X.nd.w i)) ⟨D.what₂.places.resChar_prime (L.X.nd.w i)⟩ (C.Q (L.X.nd.w i)) (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) hj.1 hj.2) (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))) (A.pl.ι (L.X.nd.w i)) (big (L.X.nd.w i))`. Establish `hc` using `Classical.choose_spec (hbig (L.X.nd.w i) (L.X.nd.j i) hj.1 hj.2 hfin)`. Use `bigOk_mono hc ?_` and prove the remaining obligations. Introduce `z hz`. Use `Finset.mem_biUnion.2 ⟨L.X.nd.j i, Finset.mem_range.2 (by omega), ?_⟩` and prove the remaining obligations.

Rewrite using `[dif_pos hj, dif_pos hfin]`. Conclude with `hz`. Establish `hOk'` using `bigOk_cast (L.X.nd.w_l i) hOk`. Take `⟨K, hK, -, -⟩` from `GlobalTheory.T.localisation_coefField_finite_range (withLoc L).nd (withLoc L).naut i`. Establish `hcont` using `(_root_.GlobalTheory.T.contains_after_localization_alt D cf jE A M C tp.tup big L hB' i).1`.

Establish `hKbig : ∀ z ∈ big (L.X.nd.w i), (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).symm z ∈ K`. Introduce `z hz`. Take `⟨y, hy⟩` from `hcont z hz`. Establish `hy' : L.Y.naut.iotaQC i (L.Y.naut.iotaQ i y) = z` using `hy`. Rewrite `hy'` using `[Au.iotaQC i]`.

Rewrite using `[← hy', RingEquiv.symm_apply_apply]`. Conclude with `(hK _).2 ⟨y, rfl⟩`. Establish `hQ : L.X.nd.Q i = C.Q (L.X.nd.w i)` using `(Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)`. Establish `hchar` using `charpoly_pt (withLoc L) i x ρ hρ`. Establish `hchar' : ∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (L.X.nd.l i) ∧ v ∉ placesS D (L.X.nd.l i) ∧ v ∉ C.Q (L.X.nd.w i)) → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F` using `D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ → (show Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (L.X.nd.l i)) from (ρ σ).val).charpoly.map (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).toRingHom = sysPol D.R.nV (ptSys (withLoc L) i x) v := by`.

Introduce `v hv B σ hB hF`. Rewrite using `[← Au.iotaQC i]`. Conclude with `hchar v ⟨hv.1, hv.2.1, hv.2.2.1, hQ ▸ hv.2.2.2⟩ B σ hB hF`. Take `⟨P, hP⟩` from `hOk' _ hpt K hKbig ρ hρ.1 hρ.2.1 hchar'`. Conclude with `model_of_conj (withLoc L).nd (withLoc L).naut i _ ρ P hρ.1 (fun g s t => (hK _).1 (hP g s t))`.
-/
theorem evO_hypO_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup SumRepresentations.hypO := by
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
  have hB' : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L := ⟨Sp, ⟨Au⟩, hss⟩
  obtain ⟨hfin, hpt⟩ := _root_.GlobalTheory.T.side_eigen_unitary_alt hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB' i x
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
  have hcont := (_root_.GlobalTheory.T.contains_after_localization_alt D cf jE A M C tp.tup big L hB' i).1
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
      v ∉ C.Q (L.X.nd.w i)) → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ →
      (show Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (L.X.nd.l i)) from (ρ σ).val).charpoly.map
        (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).toRingHom = sysPol D.R.nV (ptSys (withLoc L) i x) v := by
    intro v hv B σ hB hF
    rw [← Au.iotaQC i]
    exact hchar v ⟨hv.1, hv.2.1, hv.2.2.1, hQ ▸ hv.2.2.2⟩ B σ hB hF
  obtain ⟨P, hP⟩ := hOk' _ hpt K hKbig ρ hρ.1 hρ.2.1 hchar'
  exact model_of_conj (withLoc L).nd (withLoc L).naut i _ ρ P hρ.1 (fun g s t => (hK _).1 (hP g s t))
end GlobalTheory.LargeO
end
end

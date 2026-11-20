import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.GaloisLevelStructure.LevelQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfIsConjPl
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.AgreementAtAlmostAllSplitPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorOfMemIsotypicComponentStatement

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SphNonSplit

/- English proof (translation)
Introduce `hs'`. Establish `hu : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w = HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w'` using `HeightOneSpectrum.ext (hw.trans hw'.symm)`. Establish `hr : Module.finrank (maximalRealSubfield D.host.E) D.host.E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Break down `(GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj D.host.E) hr (IsCMField.complexConj_ne_one D.host.E) w' w).1 hu with h | h` into its components or cases. Conclude with `hs (h ▸ hs')`.

Establish `hc : (IsCMField.complexConj D.host.E).toRingEquiv = D.host.conj.toRingEquiv`. Use `RingEquiv.ext fun x => ?_` and prove the remaining obligations. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Use `show D.host.φ₀ (IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)`. Rewrite using `[IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]`.

Rewrite `h` using `[hc]`. Conclude with `hs (GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl hs' ((GlobalTheory.Mem.Chr.conjPl_main.2.1 _ _ w' w).2 h))`.
-/
theorem not_split_of_overPl (D : D7) {w w' : PlE D.host} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (hw : NG.OverPl w v) (hw' : NG.OverPl w' v) (hs : ¬ IsSplitPl D.host w) : ¬ IsSplitPl D.host w' := by
  intro hs'
  have hu : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w =
      HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w' :=
    HeightOneSpectrum.ext (hw.trans hw'.symm)
  have hr : Module.finrank (maximalRealSubfield D.host.E) D.host.E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj D.host.E) hr
      (IsCMField.complexConj_ne_one D.host.E) w' w).1 hu with h | h
  · exact hs (h ▸ hs')
  · have hc : (IsCMField.complexConj D.host.E).toRingEquiv = D.host.conj.toRingEquiv := by
      refine RingEquiv.ext fun x => ?_
      apply D.host.φ₀.injective
      show D.host.φ₀ (IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
      rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    rw [hc] at h
    exact hs (GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl hs' ((GlobalTheory.Mem.Chr.conjPl_main.2.1 _ _ w' w).2 h))

/- English proof (translation)
Take `⟨u, h | h⟩` from `GlobalTheory.TypePlaceCover.place_cover D k w hw`. Rewrite using `[h]`. Conclude with `GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u`. Conclude with `GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u) h`.
-/
theorem split_of_over_g (D : D7) (k : Fin 2) {w : PlE D.host} (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    IsSplitPl D.host w := by
  obtain ⟨u, h | h⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · rw [h]; exact GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u
  · exact GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u) h

/- English proof (translation)
Establish `hg : v ∉ gPl D`. Introduce and unpack `⟨w', hw', k, hk⟩`. Conclude with `not_split_of_overPl D hw hw' hs (split_of_over_g D k hk)`. Introduce and unpack `(h | h)`. Conclude with `hg h`.

Rewrite `h` using `[qPl_tup]`. Take `⟨-, w', hw', hr⟩` from `h`. Apply `not_split_of_overPl D hw hw' hs` to reduce the goal to its premises. Rewrite `hr` using `[tp.xi_tw]`. Assume the negation of the conclusion as `hns`.

Apply `hr` to reduce the goal to its premises. Establish `hpsi : (tp.psi w0).UnrAt w'`. Take `⟨Q, hQ⟩` from `tp.psi_gen w0`. Conclude with `(hQ.ram w').2 fun hq => hns (hQ.split w' hq)`. Distinguish the cases in `hl : D.what₂.places.resChar w0 = D.host.pde`.

Establish `hd : cf.del'.UnrAt w'` using `cf.isDel'.unr w' fun hp => hns (hsp w' (Or.inr hp))`. Introduce `x hx`. Simplify using `[Host.CharFrame.delAt, hl, hd x hx, hpsi x hx]`. Establish `hd : cf.del.UnrAt w'` using `cf.isDel.unr w' fun hp => hns (hsp w' (Or.inl hp))`. Introduce `x hx`.

Simplify using `[Host.CharFrame.delAt, hl, hd x hx, hpsi x hx]`.
-/
theorem not_mem_bad (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C)
    (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v)
    (w0 : D.what₂.places.Pl) (j : Fin D.R.m) (w : PlE D.host) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hw : NG.OverPl w v) (hs : ¬ IsSplitPl D.host w) :
    v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w0) j) := by
  have hg : v ∉ gPl D := by
    rintro ⟨w', hw', k, hk⟩
    exact not_split_of_overPl D hw hw' hs (split_of_over_g D k hk)
  rintro (h | h)
  · exact hg h
  · rw [qPl_tup] at h
    obtain ⟨-, w', hw', hr⟩ := h
    apply not_split_of_overPl D hw hw' hs
    rw [tp.xi_tw] at hr
    by_contra hns
    apply hr
    have hpsi : (tp.psi w0).UnrAt w' := by
      obtain ⟨Q, hQ⟩ := tp.psi_gen w0
      exact (hQ.ram w').2 fun hq => hns (hQ.split w' hq)
    by_cases hl : D.what₂.places.resChar w0 = D.host.pde
    · have hd : cf.del'.UnrAt w' := cf.isDel'.unr w' fun hp => hns (hsp w' (Or.inr hp))
      intro x hx
      simp [Host.CharFrame.delAt, hl, hd x hx, hpsi x hx]
    · have hd : cf.del.UnrAt w' := cf.isDel.unr w' fun hp => hns (hsp w' (Or.inl hp))
      intro x hx
      simp [Host.CharFrame.delAt, hl, hd x hx, hpsi x hx]

end GlobalTheory.SphNonSplit

namespace GlobalTheory.SphNonSplit

/- English proof (translation)
Introduce `D cf jE A low Pq S hL eig θ Bs M C tp _hCS hMI _hstar _hE hsp _hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop P w hns`. Use `set v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w with hv`. Establish `hover : NG.OverPl w v` using `rfl`. Rewrite using `[A.au.sph (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 _ w v hns hover]`. Take `⟨h1, h2⟩` from `X.nd.j_range i`.

Set `j : Fin D.R.m` to `⟨X.nd.j i - 1, by omega⟩`. Establish `hj : j.1 + 1 = X.nd.j i` using `by simp only [j]; omega`. Establish `hvB` using `not_mem_bad D cf C tp hsp (X.nd.w i) j w v hover hns`. Establish `hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j))`. Establish `key : ∀ (μ : D.what₂.Tup) (jj : ℕ) (k1 : 1 ≤ jj) (k2 : jj ≤ D.R.m), μ = D.what₂.muTw (X.nd.w i) → jj = j.1 + 1 → NG.HypOutside (M μ jj k1 k2).J (M μ jj k1 k2).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j))`.

Introduce and unpack `μ jj k1 k2 rfl rfl`. Conclude with `hMI.hyp (X.nd.w i) j`. Conclude with `key _ _ _ _ (X.nd.mu_w i) hj.symm`. Take `⟨y, hy, hy0⟩` from `(Submodule.ne_bot_iff _).1 (hne P)`. Establish `hry : (mlX M X i).real y ≠ 0` using `fun h0 => hy0 ((mlX M X i).real_inj (h0.trans (map_zero (mlX M X i).real).symm))`.

Establish `hT : (mlX M X i).real y ∈ NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ`. Rewrite using `[← (mlX M X i).real_range]`. Conclude with `LinearMap.mem_range_self _ _`. Take `⟨f, hfS, hf0, hfix⟩` from `GlobalTheory.T.fixed_vector_of_mem_isotypic_component (mlX M X i).wt.ρ (F P) {κ | κ ∈ Umax D.host.E D.R.nV ∧ TrivOutside {v} κ} (irr P) _ hy hry (by`. Introduce and unpack `κ ⟨hU, htr⟩`.

Establish `ht : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j))ᶜ κ` using `fun u hu => htr u (by rintro rfl; exact hu hvB)`. Establish `hJ : κ ∈ (mlX M X i).J` using `((hyp κ ht).1).2 hU`. Rewrite using `[hT.2 ⟨κ, hJ⟩, (hyp κ ht).2 hJ, Units.val_one, one_smul])`. Conclude with `⟨f, hfS, hf0, fun κ hU htr => hfix κ ⟨hU, htr⟩⟩`.
-/
theorem sphAU_of_not_split : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), ¬ IsSplitPl D.host w → D.nbc.sphAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _hCS hMI _hstar _hE hsp _hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop P w hns
  set v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w with hv
  have hover : NG.OverPl w v := rfl
  rw [A.au.sph (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 _ w v hns hover]
  obtain ⟨h1, h2⟩ := X.nd.j_range i
  let j : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = X.nd.j i := by simp only [j]; omega
  have hvB := not_mem_bad D cf C tp hsp (X.nd.w i) j w v hover hns
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
    have key : ∀ (μ : D.what₂.Tup) (jj : ℕ) (k1 : 1 ≤ jj) (k2 : jj ≤ D.R.m), μ = D.what₂.muTw (X.nd.w i) → jj = j.1 + 1 →
        NG.HypOutside (M μ jj k1 k2).J (M μ jj k1 k2).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
      rintro μ jj k1 k2 rfl rfl
      exact hMI.hyp (X.nd.w i) j
    exact key _ _ _ _ (X.nd.mu_w i) hj.symm
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (hne P)
  have hry : (mlX M X i).real y ≠ 0 := fun h0 =>
    hy0 ((mlX M X i).real_inj (h0.trans (map_zero (mlX M X i).real).symm))
  have hT : (mlX M X i).real y ∈ NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ := by
    rw [← (mlX M X i).real_range]; exact LinearMap.mem_range_self _ _
  obtain ⟨f, hfS, hf0, hfix⟩ := GlobalTheory.T.fixed_vector_of_mem_isotypic_component (mlX M X i).wt.ρ (F P)
    {κ | κ ∈ Umax D.host.E D.R.nV ∧ TrivOutside {v} κ} (irr P) _ hy hry (by
      rintro κ ⟨hU, htr⟩
      have ht : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j))ᶜ κ := fun u hu =>
        htr u (by rintro rfl; exact hu hvB)
      have hJ : κ ∈ (mlX M X i).J := ((hyp κ ht).1).2 hU
      rw [hT.2 ⟨κ, hJ⟩, (hyp κ ht).2 hJ, Units.val_one, one_smul])
  exact ⟨f, hfS, hf0, fun κ hU htr => hfix κ ⟨hU, htr⟩⟩

end GlobalTheory.SphNonSplit

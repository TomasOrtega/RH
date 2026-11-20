import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaDeRham
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ContinuousRankOneRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdCharIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeLAdicParameterAboveOfAlgebraicCharacterWD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleEmbeddingExtension
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ P AI ht ι art ha χ n μ h1 h2 h3 w A hA O _ _ _ Bw hB`. Use `H E Ω l P AI ht ι art ha χ n μ h1 h2 h3 w A hA O Bw hB` as an intermediate fact. Conclude with `⟨this.1, this.2.2.2⟩`.
-/
private theorem dr_of_above (H : HeckeLAdicCharacterAbove) : HeckeLAdicCharacterDeRham := by
  intro E Ω _ _ _ _ _ l _ P AI ht ι art ha χ n μ h1 h2 h3 w A hA O _ _ _ Bw hB
  have := H E Ω l P AI ht ι art ha χ n μ h1 h2 h3 w A hA O Bw hB
  exact ⟨this.1, this.2.2.2⟩

/- English proof (translation)
Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]`. Both sides reduce to the same expression.
-/
private theorem norm_hom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

/- English proof (translation)
Establish `e : w = GlobalTheory.EvExtend.placeOf τ`. Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.EvExtend.mem_placeOf, hτ]`. Establish `h1` using `norm_hom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩`. Use `((hj.valuation_lt_one_iff _).symm.trans (h x)).symm.trans ?_` and prove the remaining obligations.

Conclude with `iff_of_eq (congrArg (· < 1) h1.symm)`. Substitute `e` using the available equality. Take `⟨j, hc, hx, -⟩` from `GlobalTheory.EvExtend.exists_ext τ`. Conclude with `⟨⟨j, hc⟩, RingHom.ext hx⟩`.
-/
private theorem ex_emb {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') :
    ∃ j : Emb l w, j.1.comp (algebraMap F (w.adicCompletion F)) = τ := by
  have e : w = GlobalTheory.EvExtend.placeOf τ := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [GlobalTheory.EvExtend.mem_placeOf, hτ]
    have h1 := norm_hom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩
    refine ((hj.valuation_lt_one_iff _).symm.trans (h x)).symm.trans ?_
    exact iff_of_eq (congrArg (· < 1) h1.symm)
  subst e
  obtain ⟨j, hc, hx, -⟩ := GlobalTheory.EvExtend.exists_ext τ
  exact ⟨⟨j, hc⟩, RingHom.ext hx⟩

/- English proof (translation)
Introduce `N F Ω _ _ _ _ _ l _ A w h _ ι a ha ω hh ψ ho`. Establish `art` using `N.aut.art`. Take `⟨hc, hla⟩` from `(UpperTheory.V.Loc.ordCharIff art h ι a ha hh ψ).1.1 ⟨ω, ho⟩`. Establish `hdr` using `UpperTheory.V.Loc.laDeRham art art.heckeLAdicCharacter (dr_of_above N.aut.chA) N.aut.berger h ψ hc _ hla`. Use `⟨fun O _ _ _ Bw hj => ⟨(hdr O Bw hj).1, fun τ LL' τ' hτ => ?_, fun s => ?_⟩, fun O _ _ _ Bw hj => (hdr O Bw hj).2.1⟩` and prove the remaining obligations.

Take `⟨j, rfl⟩` from `ex_emb h Bw hj τ LL' τ' hτ`. Conclude with `(hdr O Bw hj).2.2 j`. Take `⟨ξ, hs, hξ, e⟩` from `UpperTheory.V.Loc.laWD art art.heckeLAdicCharacter (dr_of_above N.aut.chA) N.aut.chW N.aut.berger h ψ hc _ hla O Bw hj ι a ha`. Establish `hv : ((ψ (Subgroup.inclusion (Weil_le_Dec h) s) : (Qbar l)ˣ) : Qbar l) = ι.symm (ω (a s)) * algPow w (-hh) (a s : w.adicCompletion F)` using `ho.val s _ rfl (Set.mem_univ _)`. Establish `h1 : algPow w (-hh) (a s : w.adicCompletion F) * ∏ᶠ τ : Emb l w, τ.1 (a s : w.adicCompletion F) ^ hh (τ.1.comp (algebraMap F (w.adicCompletion F))) = 1` using `by haveI := finite_contEmb (l := l) w`.

Unfold `algPow`. Rewrite using `[← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]`. Use `finprod_eq_one_of_forall_eq_one fun j => ?_` and prove the remaining obligations. Rewrite using `[Pi.neg_apply, zpow_neg]`. Conclude with `inv_mul_cancel₀ (zpow_ne_zero _ ((map_ne_zero j.1).2 (a s).ne_zero))`.

Establish `h2 : (ξ s : ℂ) = ω (a s)`. Rewrite using `[hξ, hv, mul_assoc, h1, mul_one, ι.apply_symm_apply]`. Rewrite using `[e, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]`. Simplify using `[h2]`.
-/
theorem UpperTheory.V.Loc.charDR :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (ι : Qbar l ≃+* ℂ) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (ω : (w.adicCompletion F)ˣ →* ℂˣ) (hh : (F →+* Qbar l) → ℤ) (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), OrdChar ι a ω hh ψ → DRat ι h (GlobalTheory.TripleGal.rk1 ψ) (fun τ => {hh τ}) (fun s => Polynomial.X - Polynomial.C (ω (a s) : ℂ)) ∧ PotCrys A (GlobalTheory.TripleGal.rk1 ψ) := by
  intro N F Ω _ _ _ _ _ l _ A w h _ ι a ha ω hh ψ ho
  have art := N.aut.art
  obtain ⟨hc, hla⟩ := (UpperTheory.V.Loc.ordCharIff art h ι a ha hh ψ).1.1 ⟨ω, ho⟩
  have hdr := UpperTheory.V.Loc.laDeRham art art.heckeLAdicCharacter (dr_of_above N.aut.chA) N.aut.berger h ψ hc _ hla
  refine ⟨fun O _ _ _ Bw hj => ⟨(hdr O Bw hj).1, fun τ LL' τ' hτ => ?_, fun s => ?_⟩,
    fun O _ _ _ Bw hj => (hdr O Bw hj).2.1⟩
  · obtain ⟨j, rfl⟩ := ex_emb h Bw hj τ LL' τ' hτ
    exact (hdr O Bw hj).2.2 j
  · obtain ⟨ξ, hs, hξ, e⟩ := UpperTheory.V.Loc.laWD art art.heckeLAdicCharacter (dr_of_above N.aut.chA)
      N.aut.chW N.aut.berger h ψ hc _ hla O Bw hj ι a ha
    have hv : ((ψ (Subgroup.inclusion (Weil_le_Dec h) s) : (Qbar l)ˣ) : Qbar l) =
        ι.symm (ω (a s)) * algPow w (-hh) (a s : w.adicCompletion F) := ho.val s _ rfl (Set.mem_univ _)
    have h1 : algPow w (-hh) (a s : w.adicCompletion F) * ∏ᶠ τ : Emb l w, τ.1 (a s : w.adicCompletion F) ^
        hh (τ.1.comp (algebraMap F (w.adicCompletion F))) = 1 := by
      haveI := finite_contEmb (l := l) w
      unfold algPow
      rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
      refine finprod_eq_one_of_forall_eq_one fun j => ?_
      rw [Pi.neg_apply, zpow_neg]
      exact inv_mul_cancel₀ (zpow_ne_zero _ ((map_ne_zero j.1).2 (a s).ne_zero))
    have h2 : (ξ s : ℂ) = ω (a s) := by
      rw [hξ, hv, mul_assoc, h1, mul_one, ι.apply_symm_apply]
    rw [e, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp [h2]

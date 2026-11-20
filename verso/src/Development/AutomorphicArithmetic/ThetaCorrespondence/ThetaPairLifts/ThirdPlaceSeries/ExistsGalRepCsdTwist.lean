import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.OpenUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrRecOfHasSat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecTwistAbsPow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharpolyGeomFrobStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial
end GlobalTheory.HeightCounting
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial
end GlobalTheory.GalAllPlaces
end
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.CsdTwistGal
/- English proof (translation)
Introduce `hG _ _ _ _ hLL E Ω _ _ _ _ _ _ _ l _ ι a ha P hP m hm hnd f J hJ`. Establish `hτ : ∀ σ : E →+* ℂ, ι.toRingHom.comp (ι.symm.toRingHom.comp σ) = σ` using `fun σ => by`. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hint : ∀ σ : E →+* ℂ, ∀ z ∈ m σ, ∃ k : ℤ, f - z = k`.

Introduce `σ z hz`. Establish `h1` using `hJ (ι.symm.toRingHom.comp σ)`. Rewrite `h1` using `[hτ]`. Establish `h2 : f - z ∈ (m σ).map (fun z => f - z)` using `Multiset.mem_map_of_mem _ hz`. Rewrite `h2` using `[← h1]`.

Take `⟨k, -, hk⟩` from `Multiset.mem_map.1 h2`. Conclude with `⟨k, hk.symm⟩`. Establish `hfre : f = ((f.re : ℝ) : ℂ)`. Take `⟨τ0⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Take `⟨z, hz⟩ : ∃ z, z ∈ m τ0` from `Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ0).1]; omega)`.

Establish `hc` using `infChar_conj_of_isCsd E a P hP τ0 _ _ (hm τ0) (hm _)`. Establish `hz' : -z ∈ m (NumberField.ComplexEmbedding.conjugate τ0)`. Rewrite using `[hc]`. Conclude with `Multiset.mem_map_of_mem _ hz`. Take `⟨k1, hk1⟩` from `hint _ z hz`.

Take `⟨k2, hk2⟩` from `hint _ _ hz'`. Establish `e1` using `congrArg Complex.im hk1`. Establish `e2` using `congrArg Complex.im hk2`. Simplify using `only [Complex.sub_im, Complex.intCast_im, Complex.neg_im] at e1 e2`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Simplify using `only [Complex.ofReal_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set s : ℝ := ((a : ℝ) - 1) / 2 - f.re with hs`. Establish `hν` using `GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s`.

Establish `hexpo : ∀ τ, expo (GlobalTheory.HeckeGal.Model.absPow E s) τ = s` using `(GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 s hν`. Establish `hm' : ∀ τ, (P.twist (GlobalTheory.HeckeGal.Model.absPow E s)).HasInfChar τ ((m τ).map (· + (s : ℂ)))` using `fun τ => by`. Use `(hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)` as an intermediate fact. Rewrite `this` using `[hexpo]`. Then use the resulting hypothesis. Establish `hinf' : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ))` using `fun τ => CG.HasInfChar.infChar_eq (hm' τ)`.

Establish `hr : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg` using `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by`. Rewrite using `[hinf' τ]`. Use `⟨(hnd τ).map (add_left_injective _), fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.1 hz`. Take `⟨k, hk⟩` from `hint τ y hy`.

Use `⟨-k, ?_⟩` and prove the remaining obligations. Rewrite using `[hs]`. Use `push_cast`. Take the linear combination `(-1 : ℂ) * hk + hfre`. Take `⟨r, wt, HT, H⟩` from `hG E Ω l ι a ha _ _ hr (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s)`.

Establish `hHT : ∀ τ, HT τ = J τ` using `fun τ => by`. Apply `Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective` to reduce the goal to its premises. Rewrite using `[H.weights τ, hinf', hJ τ, Multiset.map_map]`. Use `Multiset.map_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Rewrite using `[hs]`. Use `push_cast`. Take the linear combination `(-1 : ℂ) * hfre`. Use `⟨r, H.cont, fun hsph => ⟨H.cont, fun PP AI T w A h O _ _ _ Bw hj => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal` using `hj.mem_placesOver h`.

Take `⟨σ, hσ, hsp⟩` from `hsph w hw`. Establish `HA` using `H.above PP AI T w A h O Bw hj`. Use `⟨HA.crys _ (hσ.twist _) (GlobalTheory.T.isSpherical_twist_absDetPow_GL E a w σ s hsp), fun τ LL' τ' hτ' => ?_⟩` and prove the remaining obligations. Rewrite using `[← hHT]`. Establish `hrc` using `_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hLL h`.

Conclude with `HA.jumps (_root_.UpperTheory.GalS.nice_of_spherical' hrc (hσ.twist _) (GlobalTheory.T.isSpherical_twist_absDetPow_GL E a w σ s hsp)) τ LL' τ' hτ'`. Introduce `w _ hl σ hσ S hS B g hB hg`. Take `⟨rc, hrc⟩ : ∃ rc, _root_.UpperTheory.Zero.LLC.IsRecT hB rc` from `⟨_, _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hLL hB⟩`. Establish `e0` using `H.aw hl hrc (hσ.twist (GlobalTheory.HeckeGal.Model.absPow E s))`. Rewrite `e0` using `[_root_.GlobalTheory.CsdTwistGal.rec_twist_absPow_alt E Ω w B hB rc hrc a σ s, GlobalTheory.WeilDeligne.WD.lpTw_add]`.

Establish `e1` using `e0.eq_unr ((GlobalTheory.WeilDeligne.WD.unr_tw _ _).2 (_root_.UpperTheory.GalS.unr_rec_of_has_sat hrc σ S hS))`. Rewrite using `[_root_.GlobalTheory.T.charpoly_inv_eq_prod_absNorm_cpow_of_isFrob E Ω l ι a r H.cont w hl B hB rc hrc σ S hS _ e1 g hg]`. Establish `e2 : ((-(s + (1 - (a : ℝ)) / 2) : ℝ) : ℂ) = f`. Rewrite using `[hfre, hs]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`.
-/
theorem exists_galRep_csd_twist_alt_alt : _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.HeckeLAdicCharacter →
  GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.BhattScholzeCrystallineLattices → _root_.UpperTheory.Zero.LLC.RecTExists →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
    ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
    ∀ (f : ℂ) (J : (E →+* Qbar l) → Multiset ℤ),
      (∀ τ, (J τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map (fun z => f - z)) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      ((∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
          P.IsLocComp w σ ∧ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w a)) → GlobalTheory.ExpFrame.CrysWith r J) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), P.IsLocComp w σ → ∀ S : Multiset ℂˣ,
          GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w →
            IsFrob (F := E) B (normV w) g →
            (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
              Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ f))).prod := by
  intro hG _ _ _ _ hLL E Ω _ _ _ _ _ _ _ l _ ι a ha P hP m hm hnd f J hJ
  have hτ : ∀ σ : E →+* ℂ, ι.toRingHom.comp (ι.symm.toRingHom.comp σ) = σ := fun σ => by
    ext x; simp
  have hint : ∀ σ : E →+* ℂ, ∀ z ∈ m σ, ∃ k : ℤ, f - z = k := by
    intro σ z hz
    have h1 := hJ (ι.symm.toRingHom.comp σ)
    rw [hτ] at h1
    have h2 : f - z ∈ (m σ).map (fun z => f - z) := Multiset.mem_map_of_mem _ hz
    rw [← h1] at h2
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.1 h2
    exact ⟨k, hk.symm⟩
  have hfre : f = ((f.re : ℝ) : ℂ) := by
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨z, hz⟩ : ∃ z, z ∈ m τ0 := Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ0).1]; omega)
    have hc := infChar_conj_of_isCsd E a P hP τ0 _ _ (hm τ0) (hm _)
    have hz' : -z ∈ m (NumberField.ComplexEmbedding.conjugate τ0) := by
      rw [hc]; exact Multiset.mem_map_of_mem _ hz
    obtain ⟨k1, hk1⟩ := hint _ z hz
    obtain ⟨k2, hk2⟩ := hint _ _ hz'
    have e1 := congrArg Complex.im hk1
    have e2 := congrArg Complex.im hk2
    simp only [Complex.sub_im, Complex.intCast_im, Complex.neg_im] at e1 e2
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]; linarith
  set s : ℝ := ((a : ℝ) - 1) / 2 - f.re with hs
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hexpo : ∀ τ, expo (GlobalTheory.HeckeGal.Model.absPow E s) τ = s :=
    (GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 s hν
  have hm' : ∀ τ, (P.twist (GlobalTheory.HeckeGal.Model.absPow E s)).HasInfChar τ ((m τ).map (· + (s : ℂ))) := fun τ => by
    have := (hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)
    rwa [hexpo] at this
  have hinf' : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ)) :=
    fun τ => CG.HasInfChar.infChar_eq (hm' τ)
  have hr : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hinf' τ]
    refine ⟨(hnd τ).map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨k, hk⟩ := hint τ y hy
    refine ⟨-k, ?_⟩
    rw [hs]; push_cast
    linear_combination (-1 : ℂ) * hk + hfre
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι a ha _ _ hr (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s)
  have hHT : ∀ τ, HT τ = J τ := fun τ => by
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights τ, hinf', hJ τ, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    rw [hs]; push_cast
    linear_combination (-1 : ℂ) * hfre
  refine ⟨r, H.cont, fun hsph => ⟨H.cont, fun PP AI T w A h O _ _ _ Bw hj => ?_⟩, ?_⟩
  · have hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := hj.mem_placesOver h
    obtain ⟨σ, hσ, hsp⟩ := hsph w hw
    have HA := H.above PP AI T w A h O Bw hj
    refine ⟨HA.crys _ (hσ.twist _) (GlobalTheory.T.isSpherical_twist_absDetPow_GL E a w σ s hsp), fun τ LL' τ' hτ' => ?_⟩
    rw [← hHT]
    have hrc := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hLL h
    exact HA.jumps (_root_.UpperTheory.GalS.nice_of_spherical' hrc (hσ.twist _) (GlobalTheory.T.isSpherical_twist_absDetPow_GL E a w σ s hsp)) τ LL' τ' hτ'
  · intro w _ hl σ hσ S hS B g hB hg
    obtain ⟨rc, hrc⟩ : ∃ rc, _root_.UpperTheory.Zero.LLC.IsRecT hB rc := ⟨_, _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hLL hB⟩
    have e0 := H.aw hl hrc (hσ.twist (GlobalTheory.HeckeGal.Model.absPow E s))
    rw [_root_.GlobalTheory.CsdTwistGal.rec_twist_absPow_alt E Ω w B hB rc hrc a σ s, GlobalTheory.WeilDeligne.WD.lpTw_add] at e0
    have e1 := e0.eq_unr ((GlobalTheory.WeilDeligne.WD.unr_tw _ _).2 (_root_.UpperTheory.GalS.unr_rec_of_has_sat hrc σ S hS))
    rw [_root_.GlobalTheory.T.charpoly_inv_eq_prod_absNorm_cpow_of_isFrob E Ω l ι a r H.cont w hl B hB rc hrc σ S hS _ e1 g hg]
    have e2 : ((-(s + (1 - (a : ℝ)) / 2) : ℝ) : ℂ) = f := by
      rw [hfre, hs]; push_cast; ring
    rw [e2]
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
end GlobalTheory.TempSatGal
end
end
end

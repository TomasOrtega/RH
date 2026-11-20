import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartFrobEigNormO
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.FrobeniusCharacterNorms
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
end GlobalTheory.FrobeniusCharacterNorms
namespace GlobalTheory.FrobeniusCharacterNorms
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
/- English proof (translation)
Introduce `D hA i x P Pa hxP hBC k R hR j hj hv`. Establish `hAut : At.TieAut D.nd D.naut` using `hA.1.1.1.2.1`. Establish `hC` using `hA.1.1.2.2.2.2.2.2.2.2.1`. Establish `hp : Pa.get k ∈ Pa` using `List.get_mem Pa k`. Establish `hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) ∪ {w | ¬ D.naut.unr (D.naut.locG (Pa.get k).π w)} ∪ {w | ¬ D.naut.unr (D.naut.locG (D.naut.muC i) w)} : Set (PlE D.host)).Finite`.

Establish `h1 : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite` using `((placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet`. Conclude with `(h1.union (Filter.eventually_cofinite.1 (D.naut.locG_unr_ae (Pa.get k).π))).union (Filter.eventually_cofinite.1 (D.naut.locG_unr_ae (D.naut.muC i)))`. Establish `hne` using `(hC _ hfin).symm ▸ Set.mem_univ (1 : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)`. Take `⟨σ, ⟨w, hw, hsp, B, hB, hσ⟩⟩ : Set.Nonempty {σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) ∪ {w | ¬ D.naut.unr (D.naut.locG (Pa.get k).π w)} ∪ {w | ¬ D.naut.unr (D.naut.locG (D.naut.muC i) w)} : Set (PlE D.h …` from `D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} := by`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`. Rewrite `hne` using `[h, closure_empty]`. Conclude with `hne`. Simplify using `only [Set.mem_union, not_or, Finset.mem_coe, Set.mem_setOf_eq, not_not] at hw`. Establish `hl` using `hw.1.1.1.1`.

Establish `hwo : SplitOut D.nd i w` using `⟨hsp, hl, hw.1.1.1.2, hw.1.1.2⟩`. Establish `huπ` using `hw.1.2`. Establish `huμ` using `hw.2`. Establish `hR` using `_root_.UpperTheory.GalS.strN' hR`. Establish `hwd` using `(hR.2.2 w hl).eq_of_unr ((D.naut.unr_tw _ _).2 huπ)`.

Establish `hU : D.naut.unr (D.naut.wdOf i R w)` using `by rw [hwd]; exact (D.naut.unr_tw _ _).2 huπ`. Establish `hF` using `D.naut.wdOf_frob i R w hl hR.1 hU B σ hB hσ`. Rewrite `hF` using `[hwd, D.naut.frobEig_tw _ _ huπ]`. Take `⟨v, hv0, hvg⟩` from `hv`. Establish `h1` using `hvg σ`.

Use `set M : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i)) := ((R σ : GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))) with hM`. Use `set c : Qbar (D.nd.l i) := iotaOQ D.nd D.naut i (chi1 D.nd i σ) with hc`. Establish `he0 : epsQ D i σ ≠ 0` using `((Units.isUnit (Formalism.MainNotions.N.Glob.epsO D.nd i σ)).map (iotaOQ D.nd D.naut i)).ne_zero`. Establish `hMv : M.mulVec v = (epsQ D i σ ^ j * c) • v`. Establish `h2` using `congrArg (fun u => (epsQ D i σ ^ j) • u) h1`.

Simplify using `only [smul_smul, inv_pow] at h2`. Rewrite `h2` using `[mul_inv_cancel₀ (pow_ne_zero _ he0), one_smul]`. Conclude with `h2`. Establish `hdet : (Matrix.scalar (Fin (Pa.get k).a) (epsQ D i σ ^ j * c) - M).det = 0`. Use `Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.sub_mulVec, hMv]`. Use extensionality with `t`. Simplify using `[Matrix.scalar_apply]`. Establish `hroot : (M.charpoly.map (D.naut.iotaQC i).toRingHom).IsRoot ((D.naut.iotaQC i).toRingHom (epsQ D i σ ^ j * c))` using `Polynomial.IsRoot.map (by rw [Polynomial.IsRoot.def, Matrix.eval_charpoly]; exact hdet)`. Rewrite `hroot` using `[hF]`.

Establish `hmem` using `(Polynomial.mem_roots (Polynomial.monic_multiset_prod_of_monic _ _ (fun a _ => Polynomial.monic_X_sub_C a)).ne_zero).2 hroot`. Rewrite `hmem` using `[Polynomial.roots_multiset_prod_X_sub_C]`. Take `⟨α, hα, hαe⟩` from `Multiset.mem_map.1 hmem`. Establish `hα1` using `(_root_.GlobalTheory.PartUnitary.frobEig_openB_and_norm_one_of_isBCV D hA.1.1.1 hA.1.2 i P Pa hBC (Pa.get k) hp w huπ α hα).1`. Establish `hq0 : 0 < normV w` using `normV_pos w`.

Establish `hq1 : (1 : ℝ) < normV w` using `GlobalTheory.LocalInv.one_lt_normV w`. Establish `hε : D.naut.iotaQC i (epsQ D i σ) = (normV w : ℂ)` using `eps_frob i hl hB hσ`. Establish `hχ` using `norm_first_character_frobenius hAut i hwo huμ hB hσ`. Establish `hn` using `congrArg norm hαe`. Simplify using `only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow, hε, norm_mul, norm_pow, Complex.norm_natCast_cpow_of_pos hq0, Complex.ofReal_re, Complex.norm_natCast] at hn`.

Rewrite `hn` using `[hc, hχ, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]`. Establish `hx` using `hα1.exp_eq (UpperTheory.GalN.one_lt_q w) hn (2 * (j : ℤ) + D.R.t - (Pa.get k).d) (by push_cast; ring)`. Establish `hz : (((Pa.get k).d : ℤ) - 1 - 2 * j : ℝ) = ((D.R.t : ℤ) - 1 : ℝ)` using `by push_cast; linarith`. Conclude with `hz` after adjusting the coercions.
-/
theorem sixth_weight_purity_alt_alt : _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' := by
  intro D hA i x P Pa hxP hBC k R hR j hj hv
  have hAut : At.TieAut D.nd D.naut := hA.1.1.1.2.1
  have hC := hA.1.1.2.2.2.2.2.2.2.2.1
  have hp : Pa.get k ∈ Pa := List.get_mem Pa k
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) ∪
      {w | ¬ D.naut.unr (D.naut.locG (Pa.get k).π w)} ∪
      {w | ¬ D.naut.unr (D.naut.locG (D.naut.muC i) w)} : Set (PlE D.host)).Finite := by
    have h1 : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite :=
      ((placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union
        (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
    exact (h1.union (Filter.eventually_cofinite.1 (D.naut.locG_unr_ae (Pa.get k).π))).union
      (Filter.eventually_cofinite.1 (D.naut.locG_unr_ae (D.naut.muC i)))
  have hne := (hC _ hfin).symm ▸ Set.mem_univ (1 : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)
  obtain ⟨σ, ⟨w, hw, hsp, B, hB, hσ⟩⟩ : Set.Nonempty {σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ (placesOver D.host.E (D.nd.l i) ∪
      ↑(D.nd.S i) ∪ ↑(D.nd.Q i) ∪ {w | ¬ D.naut.unr (D.naut.locG (Pa.get k).π w)} ∪
      {w | ¬ D.naut.unr (D.naut.locG (D.naut.muC i) w)} : Set (PlE D.host)), IsSplitPl D.host w ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hne
    exact hne
  simp only [Set.mem_union, not_or, Finset.mem_coe, Set.mem_setOf_eq, not_not] at hw
  have hl := hw.1.1.1.1
  have hwo : SplitOut D.nd i w := ⟨hsp, hl, hw.1.1.1.2, hw.1.1.2⟩
  have huπ := hw.1.2
  have huμ := hw.2
  have hR := _root_.UpperTheory.GalS.strN' hR
  have hwd := (hR.2.2 w hl).eq_of_unr ((D.naut.unr_tw _ _).2 huπ)
  have hU : D.naut.unr (D.naut.wdOf i R w) := by rw [hwd]; exact (D.naut.unr_tw _ _).2 huπ
  have hF := D.naut.wdOf_frob i R w hl hR.1 hU B σ hB hσ
  rw [hwd, D.naut.frobEig_tw _ _ huπ] at hF
  obtain ⟨v, hv0, hvg⟩ := hv
  have h1 := hvg σ
  set M : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i)) :=
    ((R σ : GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))) with hM
  set c : Qbar (D.nd.l i) := iotaOQ D.nd D.naut i (chi1 D.nd i σ) with hc
  have he0 : epsQ D i σ ≠ 0 :=
    ((Units.isUnit (Formalism.MainNotions.N.Glob.epsO D.nd i σ)).map (iotaOQ D.nd D.naut i)).ne_zero
  have hMv : M.mulVec v = (epsQ D i σ ^ j * c) • v := by
    have h2 := congrArg (fun u => (epsQ D i σ ^ j) • u) h1
    simp only [smul_smul, inv_pow] at h2
    rw [mul_inv_cancel₀ (pow_ne_zero _ he0), one_smul] at h2
    exact h2
  have hdet : (Matrix.scalar (Fin (Pa.get k).a) (epsQ D i σ ^ j * c) - M).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, hMv]
    ext t
    simp [Matrix.scalar_apply]
  have hroot : (M.charpoly.map (D.naut.iotaQC i).toRingHom).IsRoot
      ((D.naut.iotaQC i).toRingHom (epsQ D i σ ^ j * c)) :=
    Polynomial.IsRoot.map (by rw [Polynomial.IsRoot.def, Matrix.eval_charpoly]; exact hdet)
  rw [hF] at hroot
  have hmem := (Polynomial.mem_roots (Polynomial.monic_multiset_prod_of_monic _ _
    (fun a _ => Polynomial.monic_X_sub_C a)).ne_zero).2 hroot
  rw [Polynomial.roots_multiset_prod_X_sub_C] at hmem
  obtain ⟨α, hα, hαe⟩ := Multiset.mem_map.1 hmem
  have hα1 := (_root_.GlobalTheory.PartUnitary.frobEig_openB_and_norm_one_of_isBCV D hA.1.1.1 hA.1.2 i P Pa hBC (Pa.get k) hp w huπ α hα).1
  have hq0 : 0 < normV w := normV_pos w
  have hq1 : (1 : ℝ) < normV w := GlobalTheory.LocalInv.one_lt_normV w
  have hε : D.naut.iotaQC i (epsQ D i σ) = (normV w : ℂ) := eps_frob i hl hB hσ
  have hχ := norm_first_character_frobenius hAut i hwo huμ hB hσ
  have hn := congrArg norm hαe
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow, hε, norm_mul, norm_pow,
    Complex.norm_natCast_cpow_of_pos hq0, Complex.ofReal_re, Complex.norm_natCast] at hn
  rw [hc, hχ, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)] at hn
  have hx := hα1.exp_eq (UpperTheory.GalN.one_lt_q w) hn (2 * (j : ℤ) + D.R.t - (Pa.get k).d) (by push_cast; ring)
  have hz : (((Pa.get k).d : ℤ) - 1 - 2 * j : ℝ) = ((D.R.t : ℤ) - 1 : ℝ) := by push_cast; linarith
  exact_mod_cast hz
end GlobalTheory.FrobeniusCharacterNorms
end
end

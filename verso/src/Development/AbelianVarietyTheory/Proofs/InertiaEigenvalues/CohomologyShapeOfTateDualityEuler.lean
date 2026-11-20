import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import ReciprocityTheory.Hypotheses.GalCohDefs
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2Local
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteResidueFieldOfCompactIsAdicDvrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotKilledByPowUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotDivisibleByUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuotStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH0LevelRepEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCardH0H1EqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContActionTorsionLevelZModOfIsLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterIsLocallyConstantModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantOrbitOfInvPowCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPowMovesPadicRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPowNeOneOfMovesRootStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteInvariantsOfScalarNeOneTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2BoundedTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LevelRepOneLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivFractionRingQuotPiProdFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HcLCExistsPowSmulEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LevelRepFormulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionShapeOfTorsionCountsStatement

noncomputable section

namespace GlobalTheory.ShapeNeg

open Formalism.NG Formalism.RepresentationBoundsCohomology.JT ReciprocityTheory.Gal

/- English proof (translation)
Introduce `p _ K O _ _ _ _ _ _ _ G _ _ hK hO hF i ε hcyc e he M _ _ u ρ hρ`. Use `haveI := hO.ring`. Use `haveI := hO.compact`. Use `haveI : CompactSpace G := i.symm.toHomeomorph.compactSpace`. Use `haveI hres : Finite (IsLocalRing.ResidueField O) := GlobalTheory.T.finite_residueField_of_compact_isAdic_dvr hO.adic`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hpϖ : (p : O) ∈ Ideal.span {ϖ}`. Rewrite using `[← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]`. Conclude with `hO.p_mem`. Establish `hpn : ∀ n : ℕ, ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}` using `fun n => by`.

Rewrite using `[← Ideal.span_singleton_pow]`. Conclude with `Ideal.pow_mem_pow hpϖ n`. Use `set q := Nat.card (IsLocalRing.ResidueField O) with hq`. Use `set d := Module.finrank ℚ_[p] K with hd`. Use `set ε' : Formalism.GaloisCohomology.GK p K →* Oˣ := ε.comp i.symm.toMulEquiv.toMonoidHom with hε'`.

Establish `hcyc' : ∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε') g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}` using `hcyc`. Establish `hlcε : ∀ N : ℕ, IsLocallyConstant (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O))`. Introduce `N`. Establish `h` using `(GlobalTheory.T.cyclotomic_character_isLocallyConstant_mod_pow ε' hcyc' N).comp_continuous i.continuous`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `g`. Simplify using `only [Function.comp_apply, ε', MonoidHom.comp_apply]`. Use `first`. Consider the case `rfl`. Consider the case `(congr 3; exact (i.symm_apply_apply g).symm)`.

Consider the case `simp`. Establish `hMt : ∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0` using `fun m => by`. Take `⟨n, hn⟩` from `GlobalTheory.T.fractionRingQuot_killed_by_pow_uniformizer hϖ (u m)`. Conclude with `⟨n, u.injective (by rw [map_smul, hn, map_zero])⟩`. Establish `hMp : ∀ m : M, ∃ N : ℕ, (p : O) ^ N • m = 0` using `fun m => by`.

Take `⟨n, hn⟩` from `hMt m`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 (hpn n)`. Conclude with `⟨n, by rw [← hb, mul_smul, hn, smul_zero]⟩`. Establish `hdiv : ∀ m : M, ∃ m' : M, ϖ • m' = m` using `fun m => by`. Take `⟨y, hy⟩` from `GlobalTheory.T.fractionRingQuot_divisible_by_uniformizer hϖ (u m)`.

Conclude with `⟨u.symm y, u.injective (by rw [map_smul, LinearEquiv.apply_symm_apply, hy])⟩`. Establish `hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)` using `fun m => by`. Take `⟨N, hN⟩` from `hMp m`. Conclude with `GlobalTheory.T.isLocallyConstant_orbit_of_inv_pow_character' ε hlcε e ρ hρ m N hN`. Use `set ρ' : Representation O (Formalism.GaloisCohomology.GK p K) M := ρ.comp i.symm.toMulEquiv.toMonoidHom with hρ'def`.

Establish `hρ' : ∀ g m, ρ' g m = ((((ε' g) ^ e)⁻¹ : Oˣ) : O) • m` using `fun g m => hρ _ m`. Establish `hcont : ∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),`. Use `letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h`. Use the proof step `ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ') := fun n h =>`. Use the proof step `GlobalTheory.T.contAction_torsionLevelZMod_of_isLocallyConstant ρ' p n (ϖ ^ n) h (fun m _ => (hlc m).comp_continuous i.symm.continuous)`.

Take `⟨σ1, hσ1⟩` from `GlobalTheory.T.cyclotomic_character_pow_ne_one_of_moves_root hO.p_mem hO.p_ne ε' hcyc' e (GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity hK e he)`. Take `⟨σ2, hσ2⟩` from `GlobalTheory.T.cyclotomic_character_pow_ne_one_of_moves_root hO.p_mem hO.p_ne ε' hcyc' (e + 1) (GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity hK (e + 1) (Nat.succ_pos e))`. Establish `hNfin : Finite ρ.invariants`. Use `GlobalTheory.T.finite_invariants_of_scalar_ne_one_twist u ρ (i.symm σ1) ((((ε (i.symm σ1)) ^ e)⁻¹ : Oˣ) : O) ?_ (hρ _)` and prove the remaining obligations. Introduce `h1`.

Apply `hσ1` to reduce the goal to its premises. Establish `h2 : ((ε (i.symm σ1)) ^ e)⁻¹ = 1` using `Units.ext h1`. Conclude with `inv_eq_one.1 h2`. Take `⟨C, hC⟩` from `GlobalTheory.T.h2_bounded_twist hT hK hϖ hpϖ ε' hcyc' e u ρ' hρ' σ2 hσ2 hcont`. Establish `hone2` using `GlobalTheory.T.card_H2_level_rep_one_le hT hK hϖ u ρ' (hpn 1) (hcont 1 (hpn 1))`.

Establish `key : ∀ n : ℕ, 0 < n → Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧ (letI` using `GlobalTheory.ShapeNeg.levZ (M := M) p n (hpn n) Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) = Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ')) * …`. Introduce `n hn`. Use `letI := GlobalTheory.ShapeNeg.levZ (M := M) p n (hpn n)`. Take `⟨hLf, hLc⟩` from `GlobalTheory.T.finite_card_torsionLevel_fractionRingQuot hϖ u n`. Take `⟨hH1f, -⟩` from `GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK n (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ') hn (hcont n (hpn n))`.

Establish `hEu` using `hE p K hK n (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ') hn (hcont n (hpn n))`. Take `⟨t0, t1⟩` from `GlobalTheory.T.transfer_card_H0_H1_eq i ρ p n (ϖ ^ n) (hpn n)`. Establish `hH1O : Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n)))` using `Nat.finite_of_card_ne_zero (by rw [t1]; exact Nat.card_pos.ne')`. Take `⟨hXf, hX⟩` from `GlobalTheory.T.card_H1_level_rep_formula ρ ϖ n hdiv hlc hH1O`. Establish `h0c` using `GlobalTheory.T.card_H0_level_rep_eq ρ (ϖ ^ n) hNfin`.

Use `set Nq := Nat.card (ρ.invariants ⧸ LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) with hNq`. Use `haveI : Finite (ρ.invariants ⧸ LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := Finite.of_surjective _ (Submodule.mkQ_surjective _)`. Establish `hpos : 0 < Nq` using `Nat.card_pos`. Use `⟨hXf, ?_⟩` and prove the remaining obligations. Establish `e1 : Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) * Nq = (Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ')) * q ^ (n * d)) * Nq`.

Rewrite using `[← hX, t1, hEu, ← t0, h0c, hLc, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `Nat.eq_of_mul_eq_mul_right hpos e1`. Establish `htors` using `GlobalTheory.T.exists_pow_smul_eq_zero_of_mem_HcLC_of_torsion ρ ϖ hMt`. Establish `hfin1 : Finite (LinearMap.ker (ϖ • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ))`.

Establish `h1` using `(key 1 one_pos).1`. Simplify `h1` using `only [pow_one]`. Take `⟨a, F, _, _, hFf, ⟨φ⟩⟩` from `GlobalTheory.T.exists_equiv_fractionRingQuot_pi_prod_finite hϖ (Y := ReciprocityTheory.ChartRestriction.T2.HcLC ρ) (fun y => (htors y.1 y.2).imp fun n hn => Subtype.ext (by simpa using hn)) hfin1`. Use `haveI := hFf`. Use `GlobalTheory.T.torsion_shape_of_torsion_counts hϖ (ReciprocityTheory.ChartRestriction.T2.HcLC ρ) d a φ ⟨C, fun n hn => ?_⟩ ?_` and prove the remaining obligations.

Apply the tactic sequence `obtain ⟨hXf, hX⟩ := key n hn try dsimp only at hX`. Establish `hXpos : 0 < Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ))` using `Nat.card_pos`. Rewrite `hXpos`, the goal using `[hX]`. Establish `hb` using `hC n hn (hpn n)`. Apply the tactic sequence `try dsimp only at hb`.

Establish `h2pos` using `Nat.pos_of_mul_pos_right hXpos`. Prove the components needed by the constructor for the conclusion. Conclude with `Nat.le_mul_of_pos_left _ h2pos`. Conclude with `Nat.mul_le_mul_right _ hb`. Apply the tactic sequence `obtain ⟨-, hX⟩ := key 1 one_pos try dsimp only at hX hone2`.

Rewrite using `[hX]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem shapeG_of_localDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) :
    ReciprocityTheory.ChartRestriction.T2.ShapeG := by
  intro p _ K O _ _ _ _ _ _ _ G _ _ hK hO hF i ε hcyc e he M _ _ u ρ hρ
  haveI := hO.ring
  haveI := hO.compact
  haveI : CompactSpace G := i.symm.toHomeomorph.compactSpace
  haveI hres : Finite (IsLocalRing.ResidueField O) := GlobalTheory.T.finite_residueField_of_compact_isAdic_dvr hO.adic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpϖ : (p : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]; exact hO.p_mem
  have hpn : ∀ n : ℕ, ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n} := fun n => by
    rw [← Ideal.span_singleton_pow]; exact Ideal.pow_mem_pow hpϖ n
  set q := Nat.card (IsLocalRing.ResidueField O) with hq
  set d := Module.finrank ℚ_[p] K with hd
  set ε' : Formalism.GaloisCohomology.GK p K →* Oˣ := ε.comp i.symm.toMulEquiv.toMonoidHom with hε'
  have hcyc' : ∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε') g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n} := hcyc
  have hlcε : ∀ N : ℕ, IsLocallyConstant
      (fun g : G => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε g : Oˣ) : O)) := by
    intro N
    have h := (GlobalTheory.T.cyclotomic_character_isLocallyConstant_mod_pow ε' hcyc' N).comp_continuous i.continuous
    convert h using 1
    funext g
    simp only [Function.comp_apply, ε', MonoidHom.comp_apply]
    first
      | rfl
      | (congr 3; exact (i.symm_apply_apply g).symm)
      | simp
  have hMt : ∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0 := fun m => by
    obtain ⟨n, hn⟩ := GlobalTheory.T.fractionRingQuot_killed_by_pow_uniformizer hϖ (u m)
    exact ⟨n, u.injective (by rw [map_smul, hn, map_zero])⟩
  have hMp : ∀ m : M, ∃ N : ℕ, (p : O) ^ N • m = 0 := fun m => by
    obtain ⟨n, hn⟩ := hMt m
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hpn n)
    exact ⟨n, by rw [← hb, mul_smul, hn, smul_zero]⟩
  have hdiv : ∀ m : M, ∃ m' : M, ϖ • m' = m := fun m => by
    obtain ⟨y, hy⟩ := GlobalTheory.T.fractionRingQuot_divisible_by_uniformizer hϖ (u m)
    exact ⟨u.symm y, u.injective (by rw [map_smul, LinearEquiv.apply_symm_apply, hy])⟩
  have hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m) := fun m => by
    obtain ⟨N, hN⟩ := hMp m
    exact GlobalTheory.T.isLocallyConstant_orbit_of_inv_pow_character' ε hlcε e ρ hρ m N hN
  set ρ' : Representation O (Formalism.GaloisCohomology.GK p K) M := ρ.comp i.symm.toMulEquiv.toMonoidHom with hρ'def
  have hρ' : ∀ g m, ρ' g m = ((((ε' g) ^ e)⁻¹ : Oˣ) : O) • m := fun g m => hρ _ m
  have hcont : ∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ') := fun n h =>
    GlobalTheory.T.contAction_torsionLevelZMod_of_isLocallyConstant ρ' p n (ϖ ^ n) h (fun m _ => (hlc m).comp_continuous i.symm.continuous)
  obtain ⟨σ1, hσ1⟩ := GlobalTheory.T.cyclotomic_character_pow_ne_one_of_moves_root hO.p_mem hO.p_ne ε' hcyc' e (GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity hK e he)
  obtain ⟨σ2, hσ2⟩ := GlobalTheory.T.cyclotomic_character_pow_ne_one_of_moves_root hO.p_mem hO.p_ne ε' hcyc' (e + 1) (GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity hK (e + 1) (Nat.succ_pos e))
  have hNfin : Finite ρ.invariants := by
    refine GlobalTheory.T.finite_invariants_of_scalar_ne_one_twist u ρ (i.symm σ1) ((((ε (i.symm σ1)) ^ e)⁻¹ : Oˣ) : O) ?_ (hρ _)
    intro h1
    apply hσ1
    have h2 : ((ε (i.symm σ1)) ^ e)⁻¹ = 1 := Units.ext h1
    exact inv_eq_one.1 h2
  obtain ⟨C, hC⟩ := GlobalTheory.T.h2_bounded_twist hT hK hϖ hpϖ ε' hcyc' e u ρ' hρ' σ2 hσ2 hcont
  have hone2 := GlobalTheory.T.card_H2_level_rep_one_le hT hK hϖ u ρ' (hpn 1) (hcont 1 (hpn 1))
  have key : ∀ n : ℕ, 0 < n →
      Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧
      (letI := GlobalTheory.ShapeNeg.levZ (M := M) p n (hpn n)
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) =
        Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ')) * q ^ (n * d)) := by
    intro n hn
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p n (hpn n)
    obtain ⟨hLf, hLc⟩ := GlobalTheory.T.finite_card_torsionLevel_fractionRingQuot hϖ u n
    obtain ⟨hH1f, -⟩ := GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK n (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n))
      (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ') hn (hcont n (hpn n))
    have hEu := hE p K hK n (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ') hn
      (hcont n (hpn n))
    obtain ⟨t0, t1⟩ := GlobalTheory.T.transfer_card_H0_H1_eq i ρ p n (ϖ ^ n) (hpn n)
    have hH1O : Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) :=
      Nat.finite_of_card_ne_zero (by rw [t1]; exact Nat.card_pos.ne')
    obtain ⟨hXf, hX⟩ := GlobalTheory.T.card_H1_level_rep_formula ρ ϖ n hdiv hlc hH1O
    have h0c := GlobalTheory.T.card_H0_level_rep_eq ρ (ϖ ^ n) hNfin
    set Nq := Nat.card (ρ.invariants ⧸
      LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) with hNq
    haveI : Finite (ρ.invariants ⧸
        LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) :=
      Finite.of_surjective _ (Submodule.mkQ_surjective _)
    have hpos : 0 < Nq := Nat.card_pos
    refine ⟨hXf, ?_⟩
    have e1 : Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) * Nq =
        (Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n (hpn n) ρ')) * q ^ (n * d)) * Nq := by
      rw [← hX, t1, hEu, ← t0, h0c, hLc, ← pow_mul]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos e1
  have htors := GlobalTheory.T.exists_pow_smul_eq_zero_of_mem_HcLC_of_torsion ρ ϖ hMt
  have hfin1 : Finite (LinearMap.ker (ϖ • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) := by
    have h1 := (key 1 one_pos).1
    simpa only [pow_one] using h1
  obtain ⟨a, F, _, _, hFf, ⟨φ⟩⟩ := GlobalTheory.T.exists_equiv_fractionRingQuot_pi_prod_finite hϖ (Y := ReciprocityTheory.ChartRestriction.T2.HcLC ρ)
    (fun y => (htors y.1 y.2).imp fun n hn => Subtype.ext (by simpa using hn)) hfin1
  haveI := hFf
  refine GlobalTheory.T.torsion_shape_of_torsion_counts hϖ (ReciprocityTheory.ChartRestriction.T2.HcLC ρ) d a φ ⟨C, fun n hn => ?_⟩ ?_
  · obtain ⟨hXf, hX⟩ := key n hn
    try dsimp only at hX
    have hXpos : 0 < Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) :=
      Nat.card_pos
    rw [hX] at hXpos ⊢
    have hb := hC n hn (hpn n)
    try dsimp only at hb
    have h2pos := Nat.pos_of_mul_pos_right hXpos
    constructor
    · exact Nat.le_mul_of_pos_left _ h2pos
    · exact Nat.mul_le_mul_right _ hb
  · obtain ⟨-, hX⟩ := key 1 one_pos
    try dsimp only at hX hone2
    rw [hX]
    calc _ ≤ q * q ^ (1 * d) := Nat.mul_le_mul_right _ hone2
      _ = q ^ (d + 1) := by ring

end GlobalTheory.ShapeNeg

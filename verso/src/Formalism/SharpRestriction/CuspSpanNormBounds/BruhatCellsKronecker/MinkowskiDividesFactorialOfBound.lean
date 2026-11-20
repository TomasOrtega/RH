import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliaryNormPrimes
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
The claim follows from `Formalism.MainNotions.LatticeGluingRadicals.hadamard_section`.
-/
theorem lattice_count_fourth_admissible : VanishingOnXAndXPlusMass.ArchimedeanSignatureMatching := Formalism.MainNotions.LatticeGluingRadicals.hadamard_section
/- English proof (translation)
The claim follows from `Formalism.MainNotions.LatticeGluingRadicals.lemma_one_section D`.
-/
theorem lattice_count_fifth_admissible (D : D7) : VanishingOnXAndXPlusMass.adm5 D := Formalism.MainNotions.LatticeGluingRadicals.lemma_one_section D
/- English proof (translation)
The claim follows from `Formalism.MainNotions.LatticeGluingRadicals.radical_second_section D`.
-/
theorem lattice_count_sixth_admissible (D : D7) : VanishingOnXAndXPlusMass.adm6 D := Formalism.MainNotions.LatticeGluingRadicals.radical_second_section D
/- English proof (translation)
The claim follows from `lattice_count_fifth_admissible D u _`.
-/
theorem first_word_lemma_admissible (D : D7) (u u' : D.what₂.Word) : VanishingOnXAndXPlus.adm11 D u u' := lattice_count_fifth_admissible D u _
/- English proof (translation)
The claim follows from `Formalism.MainNotions.LatticeGluingRadicals.lattice_lemma_two_section D u _`.
-/
theorem second_word_lemma_admissible (D : D7) (u u' : D.what₂.Word) : VanishingOnXAndXPlus.adm12 D u u' := Formalism.MainNotions.LatticeGluingRadicals.lattice_lemma_two_section D u _
/- English proof (translation)
The claim follows from `lattice_count_sixth_admissible D u _`.
-/
theorem approximation_admissible_words (D : D7) (u u' : D.what₂.Word) : VanishingOnXAndXPlus.adm13 D u u' := lattice_count_sixth_admissible D u _
/- English proof (translation)
The claim follows from `Formalism.MainNotions.LatticeGluingRadicals.theorem_A_section D u _`.
-/
theorem word_theorem_a_admissible (D : D7) (u u' : D.what₂.Word) : VanishingOnXAndXPlus.adm14 D u u' := Formalism.MainNotions.LatticeGluingRadicals.theorem_A_section D u _
/- English proof (translation)
The claim follows from `Formalism.MainNotions.LatticeGluingRadicals.theorem_B_section D u _`.
-/
theorem word_theorem_b_admissible (D : D7) (u u' : D.what₂.Word) : VanishingOnXAndXPlus.adm15 D u u' := Formalism.MainNotions.LatticeGluingRadicals.theorem_B_section D u _

section FamAdm
variable {eps : ℝ} (Fm : FamP eps)
/- English proof (translation)
Introduce `x i` and use `lattice_count_fifth_admissible _`.
-/
theorem lattice_count_fifth_family : VanishingOnXAndXPlusMass.FamilyFifthHypothesis Fm := fun x i => lattice_count_fifth_admissible _
/- English proof (translation)
Introduce `x i` and use `lattice_count_sixth_admissible _`.
-/
theorem lattice_count_family_admissible : VanishingOnXAndXPlusMass.FamilySixthHypothesis Fm := fun x i => lattice_count_sixth_admissible _
/- English proof (translation)
Introduce `x i u u'` and use `first_word_lemma_admissible _ u u'`.
-/
theorem family_first_word_lemma : VanishingOnXAndXPlus.FamilyWeylAndVandermonde Fm := fun x i u u' => first_word_lemma_admissible _ u u'
/- English proof (translation)
Introduce `x i u u'` and use `second_word_lemma_admissible _ u u'`.
-/
theorem family_second_lemma_admissible : VanishingOnXAndXPlus.FamilyTwelfthHypothesis Fm := fun x i u u' => second_word_lemma_admissible _ u u'
/- English proof (translation)
Introduce `x i u u'` and use `approximation_admissible_words _ u u'`.
-/
theorem family_approximation_admissible : VanishingOnXAndXPlus.FamilyThirteenthHypothesis Fm := fun x i u u' => approximation_admissible_words _ u u'
/- English proof (translation)
Introduce `x i u u'` and use `word_theorem_a_admissible _ u u'`.
-/
theorem family_word_theorem_a : VanishingOnXAndXPlus.FamilyFourteenthHypothesis Fm := fun x i u u' => word_theorem_a_admissible _ u u'
/- English proof (translation)
Introduce `x i u u'` and use `word_theorem_b_admissible _ u u'`.
-/
theorem family_word_theorem_b : VanishingOnXAndXPlus.FamilyFifteenthHypothesis Fm := fun x i u u' => word_theorem_b_admissible _ u u'
end FamAdm

/- English proof (translation)
Take `⟨hfin, hle⟩` from `Formalism.HermitianLatticeCounting.P.ideal_count_statement D.host.E P D.R.k j hj hr`. Establish `hset : {N : Submodule (𝓞 D.host.E) P | N.toAddSubgroup.index = j} = {Q : Submodule (𝓞 D.host.E) P | Nat.card (P ⧸ Q) = j}` using `rfl`. Rewrite `hfin`, `hle` using `[hset]`. Establish `: Finite {Q : Submodule (𝓞 D.host.E) P // Nat.card (P ⧸ Q) = j}` using `hfin`. Establish `hc : (ENat.card {Q : Submodule (𝓞 D.host.E) P // Nat.card (P ⧸ Q) = j} : ℕ∞) = ((Nat.card {Q : Submodule (𝓞 D.host.E) P // Nat.card (P ⧸ Q) = j} : ℕ) : ℕ∞)` using `(ENat.card_eq_coe_natCard _)`.

Rewrite using `[hc]`. Establish `hn : Nat.card {Q : Submodule (𝓞 D.host.E) P // Nat.card (P ⧸ Q) = j} = {Q : Submodule (𝓞 D.host.E) P | Nat.card (P ⧸ Q) = j}.ncard` using `(Nat.card_coe_set_eq _)`. Rewrite using `[hn]`. Establish `hE : ((finrank ℚ D.host.E : ℕ) : ℝ) = 2 * (D.R.f : ℝ)`. Rewrite using `[Formalism.MainNotions.StandardLattice.finrank_host D]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hle` using `[hE]`. Establish `h2 : ((({Q : Submodule (𝓞 D.host.E) P | Nat.card (P ⧸ Q) = j}.ncard : ℕ) : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (({Q : Submodule (𝓞 D.host.E) P | Nat.card (P ⧸ Q) = j}.ncard : ℕ) : ℝ)`. Rewrite using `[ENNReal.ofReal_natCast]`.

Both sides reduce to the same expression. Rewrite using `[h2]`. Conclude with `ENNReal.ofReal_le_ofReal hle`.
-/
theorem sublattice_count_polynomial_bound (D : D7) (P : Type) [AddCommGroup P] [Module (𝓞 D.host.E) P] [Module.Projective (𝓞 D.host.E) P]
    [Module.Finite (𝓞 D.host.E) P] (hr : finrank (𝓞 D.host.E) P ≤ D.R.k) (j : ℕ) (hj : 1 ≤ j) :
    ((ENat.card {Q : Submodule (𝓞 D.host.E) P // Nat.card (P ⧸ Q) = j} : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((j : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f)) := by
  obtain ⟨hfin, hle⟩ := Formalism.HermitianLatticeCounting.P.ideal_count_statement D.host.E P D.R.k j hj hr
  have hset : {N : Submodule (𝓞 D.host.E) P | N.toAddSubgroup.index = j} =
      {Q : Submodule (𝓞 D.host.E) P | Nat.card (P ⧸ Q) = j} := rfl
  rw [hset] at hfin hle
  have : Finite {Q : Submodule (𝓞 D.host.E) P // Nat.card (P ⧸ Q) = j} := hfin
  have hc : (ENat.card {Q : Submodule (𝓞 D.host.E) P // Nat.card (P ⧸ Q) = j} : ℕ∞) =
      ((Nat.card {Q : Submodule (𝓞 D.host.E) P // Nat.card (P ⧸ Q) = j} : ℕ) : ℕ∞) :=
    (ENat.card_eq_coe_natCard _)
  rw [hc]
  have hn : Nat.card {Q : Submodule (𝓞 D.host.E) P // Nat.card (P ⧸ Q) = j} =
      {Q : Submodule (𝓞 D.host.E) P | Nat.card (P ⧸ Q) = j}.ncard := (Nat.card_coe_set_eq _)
  rw [hn]
  have hE : ((finrank ℚ D.host.E : ℕ) : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [Formalism.MainNotions.StandardLattice.finrank_host D]; push_cast; ring
  rw [hE] at hle
  have h2 : ((({Q : Submodule (𝓞 D.host.E) P | Nat.card (P ⧸ Q) = j}.ncard : ℕ) : ℕ∞) : ℝ≥0∞) =
      ENNReal.ofReal (({Q : Submodule (𝓞 D.host.E) P | Nat.card (P ⧸ Q) = j}.ncard : ℕ) : ℝ) := by
    rw [ENNReal.ofReal_natCast]; rfl
  rw [h2]
  exact ENNReal.ofReal_le_ofReal hle

/- English proof (translation)
Take `⟨s, hse, hsp⟩` from `hs`. Establish `hA1 : (1 : ℝ) ≤ (Nat.card A : ℝ)` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'`. Establish `hH1 : (1 : ℝ) ≤ H` using `le_trans hA1 hH`. Establish `hrange : Set.range (fun i : Fin s.card => ((s.equivFin.symm i : s) : A)) = (s : Set A)`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `(s.equivFin.symm i).2`. Introduce `hx; exact ⟨s.equivFin ⟨x, hx⟩, by simp⟩`. Establish `hv : Submodule.span R (Set.range (fun i : Fin s.card => ((s.equivFin.symm i : s) : A))) = ⊤`.

Rewrite using `[hrange]`. Conclude with `hsp`. Establish `key : ((Nat.card A : ℕ) : ℝ) ^ s.card ≤ H ^ (C * e)`. Combine the equalities or inequalities in the displayed calculation. Apply `Real.rpow_le_rpow_of_exponent_le hH1` to reduce the goal to its premises.

Establish `h1 : ((s.card : ℕ) : ℝ) ≤ (e : ℝ)` using `by exact_mod_cast hse`. Establish `h2 : (0 : ℝ) ≤ (e : ℝ)` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Prove the components needed by the constructor for the conclusion. Establish `h` using `Formalism.HermitianLatticeCounting.P.submodule_automorphism_count.1 R A s.card _ hv`.

Conclude with `le_trans (by exact_mod_cast h) key`. Establish `h` using `Formalism.HermitianLatticeCounting.P.submodule_automorphism_count.2 R A s.card _ hv`. Conclude with `le_trans (by exact_mod_cast h) key`.
-/
theorem submodule_automorphism_count_bound (R : Type) [CommRing R] [IsDedekindDomain R] (A : Type) [AddCommGroup A] [Module R A] [Finite A] (e : ℕ)
    (hs : ∃ s : Finset A, s.card ≤ e ∧ Submodule.span R (s : Set A) = ⊤) (H C : ℝ) (hC : 1 ≤ C)
    (hH : (Nat.card A : ℝ) ≤ H) :
    (Nat.card (Submodule R A) : ℝ) ≤ H ^ (C * e) ∧ (Nat.card (A ≃ₗ[R] A) : ℝ) ≤ H ^ (C * e) := by
  obtain ⟨s, hse, hsp⟩ := hs
  have hA1 : (1 : ℝ) ≤ (Nat.card A : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hH1 : (1 : ℝ) ≤ H := le_trans hA1 hH
  have hrange : Set.range (fun i : Fin s.card => ((s.equivFin.symm i : s) : A)) = (s : Set A) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact (s.equivFin.symm i).2
    · intro hx; exact ⟨s.equivFin ⟨x, hx⟩, by simp⟩
  have hv : Submodule.span R (Set.range (fun i : Fin s.card => ((s.equivFin.symm i : s) : A))) = ⊤ := by
    rw [hrange]; exact hsp
  have key : ((Nat.card A : ℕ) : ℝ) ^ s.card ≤ H ^ (C * e) := by
    calc ((Nat.card A : ℕ) : ℝ) ^ s.card ≤ H ^ s.card := pow_le_pow_left₀ (by positivity) hH _
      _ = H ^ ((s.card : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ H ^ (C * e) := by
        apply Real.rpow_le_rpow_of_exponent_le hH1
        have h1 : ((s.card : ℕ) : ℝ) ≤ (e : ℝ) := by exact_mod_cast hse
        have h2 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
        nlinarith
  constructor
  · have h := Formalism.HermitianLatticeCounting.P.submodule_automorphism_count.1 R A s.card _ hv
    exact le_trans (by exact_mod_cast h) key
  · have h := Formalism.HermitianLatticeCounting.P.submodule_automorphism_count.2 R A s.card _ hv
    exact le_trans (by exact_mod_cast h) key

/- English proof (translation)
Unfold `Formalism.MainNotions.VanishingOnXAndXPlusMass.Conclusion5 Formalism.MainNotions.S.UnitaryVolumeMass.SubmoduleIndexCount`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `P _ _ _ _ hr j hj`. Conclude with `sublattice_count_polynomial_bound D P hr j hj`. Introduce `A _ _ _ e hs hH`.

Conclude with `submodule_automorphism_count_bound _ A e hs _ C hC hH`.
-/
theorem lattice_count_bound (D : D7) (large₂ : SizeData₂ D) (CH C : ℝ) (hC : 1 ≤ C) : VanishingOnXAndXPlusMass.Conclusion5 D large₂ CH C := by
  unfold Formalism.MainNotions.VanishingOnXAndXPlusMass.Conclusion5 Formalism.MainNotions.S.UnitaryVolumeMass.SubmoduleIndexCount
  refine ⟨?_, ?_⟩
  · intro P _ _ _ _ hr j hj
    exact sublattice_count_polynomial_bound D P hr j hj
  · intro A _ _ _ e hs hH
    exact submodule_automorphism_count_bound _ A e hs _ C hC hH

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun CH => ⟨0, fun x _ i => lattice_count_bound _ _ CH 1 le_rfl⟩⟩`.
-/
theorem family_lattice_count_bound {eps : ℝ} (Fm : FamP eps) : VanishingOnXAndXPlusMass.SlopeLossFamily Fm :=
  ⟨1, fun CH => ⟨0, fun x _ i => lattice_count_bound _ _ CH 1 le_rfl⟩⟩

/- English proof (translation)
Establish `hb : (fun i : Fin j => Pi.single i (1 : K)) = ⇑(Pi.basisFun K (Fin j))` using `funext fun i => by simp`. Use `⟨fun i => Pi.single i (1 : K), ?_, ?_, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[hb]`. Conclude with `(Pi.basisFun K (Fin j)).linearIndependent`. Rewrite using `[hb]`.

Conclude with `(Pi.basisFun K (Fin j)).span_eq`. Introduce `i i'`. Simplify using `only [Cnt.stdH, LinearMap.mk₂'ₛₗ_apply]`. Rewrite using `[Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (fun hi => absurd (Finset.mem_univ i) hi)]`. Simplify using `[Pi.single_apply]`.
-/
theorem cnt_stdLat_isOrtho (K : Type) [Field K] [NumberField K] [StarRing K] (j : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (Cnt.stdH K j) (Cnt.stdLat K j) j := by
  have hb : (fun i : Fin j => Pi.single i (1 : K)) = ⇑(Pi.basisFun K (Fin j)) := funext fun i => by simp
  refine ⟨fun i => Pi.single i (1 : K), ?_, ?_, rfl, ?_⟩
  · rw [hb]
    exact (Pi.basisFun K (Fin j)).linearIndependent
  · rw [hb]
    exact (Pi.basisFun K (Fin j)).span_eq
  · intro i i'
    simp only [Cnt.stdH, LinearMap.mk₂'ₛₗ_apply]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp [Pi.single_apply]

/- English proof (translation)
The claim follows from `Formalism.MainNotions.StandardLattice.mass_ortho D.host.E D.sp.cm.cmUnram j _ _ _ (cnt_stdLat_isOrtho D.host.E j)`.
-/
theorem massS_eq (D : D7) (j : ℕ) :
    massS D j = Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm D.host.E j) (Formalism.MainNotions.StandardLattice.stdLat D.host.E j) :=
  Formalism.MainNotions.StandardLattice.mass_ortho D.host.E D.sp.cm.cmUnram j _ _ _ (cnt_stdLat_isOrtho D.host.E j)

/- English proof (translation)
Rewrite using `[massS_eq]`. Conclude with `Formalism.MainNotions.StandardLattice.massI_pos D j`.
-/
theorem massS_pos (D : D7) (j : ℕ) : 0 < massS D j := by
  rw [massS_eq]; exact Formalism.MainNotions.StandardLattice.massI_pos D j

/- English proof (translation)
Establish `hsym : ∀ n : ℕ, (Cnt.stdH D.host.E n).IsSymm` using `fun n => by first`. Consider the case `exact fun x y => by`. Simplify using `[Cnt.stdH, LinearMap.mk₂'ₛₗ_apply, starRingEnd_apply, star_sum, map_sum, star_mul, star_star]`. Consider the case `exact ⟨fun x y => by`. Simplify using `[Cnt.stdH, LinearMap.mk₂'ₛₗ_apply, starRingEnd_apply, star_sum, map_sum, star_mul, star_star]⟩`.

Establish `hr` using `h1 j hj (Fin j → D.host.E) (Fin (j - 1) → D.host.E) (Cnt.stdH D.host.E j) (Cnt.stdH D.host.E (j - 1)) (Cnt.stdLat D.host.E j) (Cnt.stdLat D.host.E (j - 1)) (hsym j) (hsym (j - 1)) (cnt_stdLat_isOrtho D.host.E j) (cnt_stdLat_isOrtho D.host.E (j - 1))`. Establish `hpos : 0 < Formalism.HermitianLatticesTheory.mass (Cnt.stdH D.host.E (j - 1)) (Cnt.stdLat D.host.E (j - 1))` using `massS_pos D (j - 1)`. Rewrite `hr` using `[div_eq_iff hpos.ne']`. Conclude with `hr`.
-/
theorem massS_ratio (D : D7) (h1 : UnitaryVolumeMass.stMassRatio D) (j : ℕ) (hj : 3 ≤ j) :
    massS D j = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j * massS D (j - 1) := by
  have hsym : ∀ n : ℕ, (Cnt.stdH D.host.E n).IsSymm := fun n => by
    first
      | exact fun x y => by
          simp [Cnt.stdH, LinearMap.mk₂'ₛₗ_apply, starRingEnd_apply, star_sum, map_sum, star_mul, star_star]
      | exact ⟨fun x y => by
          simp [Cnt.stdH, LinearMap.mk₂'ₛₗ_apply, starRingEnd_apply, star_sum, map_sum, star_mul, star_star]⟩
  have hr := h1 j hj (Fin j → D.host.E) (Fin (j - 1) → D.host.E) (Cnt.stdH D.host.E j) (Cnt.stdH D.host.E (j - 1))
    (Cnt.stdLat D.host.E j) (Cnt.stdLat D.host.E (j - 1)) (hsym j) (hsym (j - 1))
    (cnt_stdLat_isOrtho D.host.E j) (cnt_stdLat_isOrtho D.host.E (j - 1))
  have hpos : 0 < Formalism.HermitianLatticesTheory.mass (Cnt.stdH D.host.E (j - 1)) (Cnt.stdLat D.host.E (j - 1)) := massS_pos D (j - 1)
  rw [div_eq_iff hpos.ne'] at hr
  exact hr

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.massRatioRightSide Formalism.HermitianLatticeCounting.LatticeSumBounds.mJ`. Rewrite using `[Formalism.MainNotions.StandardLattice.fDeg_host, Formalism.MainNotions.StandardLattice.vInv_host, div_eq_mul_inv]`.
-/
theorem ratio_eq_mJ (D : D7) (j : ℕ) :
    Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j =
      Formalism.HermitianLatticeCounting.LatticeSumBounds.mJ D.R.f D.host.v (fun i => Formalism.HermitianLatticesTheory.lValEta D.host.E i) j := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide Formalism.HermitianLatticeCounting.LatticeSumBounds.mJ
  rw [Formalism.MainNotions.StandardLattice.fDeg_host, Formalism.MainNotions.StandardLattice.vInv_host, div_eq_mul_inv]

/- English proof (translation)
Establish `hpos` using `Formalism.MainNotions.StandardLattice.lVal_pos D j (by omega)`. Establish `hb : |Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E j)| ≤ (D.R.f : ℝ) * Real.log (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j)` using `Formalism.MainNotions.StandardLattice.massIdentity_holds D j (by omega)`. Establish `hz : 1 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j` using `Formalism.HermitianLatticeCounting.P.one_le_zetaSeries j (by omega)`. Establish `hz0 : 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j` using `by linarith`. Establish `e : (D.R.f : ℝ) * Real.log (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) = Real.log (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j ^ D.R.f)`.

Rewrite using `[Real.log_pow]`. Rewrite `hb` using `[e, abs_le]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← Real.log_le_log_iff (inv_pos.2 (pow_pos hz0 _)) hpos, Real.log_inv]`. Conclude with `hb.1`.

Rewrite using `[← Real.log_le_log_iff hpos (pow_pos hz0 _)]`. Conclude with `hb.2`.
-/
theorem lVal_bounds (D : D7) (j : ℕ) (hj : 3 ≤ j) :
    ((Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ^ D.R.f)⁻¹ ≤ Formalism.HermitianLatticesTheory.lValEta D.host.E j ∧
      Formalism.HermitianLatticesTheory.lValEta D.host.E j ≤ (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ^ D.R.f := by
  have hpos := Formalism.MainNotions.StandardLattice.lVal_pos D j (by omega)
  have hb : |Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E j)| ≤ (D.R.f : ℝ) * Real.log (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) :=
    Formalism.MainNotions.StandardLattice.massIdentity_holds D j (by omega)
  have hz : 1 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j := Formalism.HermitianLatticeCounting.P.one_le_zetaSeries j (by omega)
  have hz0 : 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j := by linarith
  have e : (D.R.f : ℝ) * Real.log (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) = Real.log (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j ^ D.R.f) := by
    rw [Real.log_pow]
  rw [e, abs_le] at hb
  constructor
  · rw [← Real.log_le_log_iff (inv_pos.2 (pow_pos hz0 _)) hpos, Real.log_inv]; exact hb.1
  · rw [← Real.log_le_log_iff hpos (pow_pos hz0 _)]; exact hb.2

/- English proof (translation)
Establish `hk : s + 2 ≤ D.R.k` using `by omega`. Unfold `XiS Xi`. Rewrite using `[if_pos ⟨hs, hsk⟩]`. Establish `hR : ∀ j, 3 ≤ j → 0 < Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j`. Introduce `j hj`.

Establish `h` using `massS_ratio D h1 j hj`. Establish `h2` using `massS_pos D j`. Establish `h3` using `massS_pos D (j - 1)`. Rewrite `h2` using `[h]`. Conclude with `(pos_iff_pos_of_mul_pos h2).2 h3`.

Establish `hid` using `Formalism.HermitianLatticeCounting.P.massRatioIdentity (massS D) (fun j => if 3 ≤ j then Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j else 1) D.R.k s (fun j => by`. Distinguish the cases in `hj : 3 ≤ j`. Simplify using `only [if_pos hj]`. Conclude with `hR j hj`. Simplify using `only [if_neg hj]`.

Conclude with `one_pos)`. Use the proof step `(massS_pos D 2)`. Use the proof step `(fun j hj => by simp only [if_pos hj]; exact massS_ratio D h1 j hj) hs hk`. Rewrite using `[hid]`. Establish `e1 : ∏ j ∈ Finset.Ioc 2 s, (if 3 ≤ j then Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j else 1) = ∏ j ∈ Finset.Ioc 2 s, Formalism.HermitianLatticeCounting.LatticeSumBounds.mJ D.R.f D.host.v (fun i => Formalism.HermitianLatticesTheory.lValEta D.host.E i) j` using `Finset.prod_congr rfl fun j hj => by`.

Establish `: 3 ≤ j` using `(Finset.mem_Ioc.1 hj).1`. Rewrite using `[if_pos this, ratio_eq_mJ]`. Establish `e2 : ∏ j ∈ Finset.Ioc (D.R.k - s) D.R.k, (if 3 ≤ j then Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j else 1) = ∏ j ∈ Finset.Ioc (D.R.k - s) D.R.k, Formalism.HermitianLatticeCounting.LatticeSumBounds.mJ D.R.f D.host.v (fun i => Formalism.HermitianLatticesTheory. …` using `Finset.prod_congr rfl fun j hj => by`. Establish `: 3 ≤ j` using `by have := (Finset.mem_Ioc.1 hj).1; omega`. Rewrite using `[if_pos this, ratio_eq_mJ]`.

Rewrite using `[e1, e2]`. Conclude with `Formalism.HermitianLatticeCounting.P.massRatioBound D.R.f D.R.k s D.host.v (massS D 2) _ hv (massS_pos D 2).le hs hk (fun j hj => lVal_bounds D j hj)`.
-/
theorem xi_explicit (D : D7) (u : D.what₂.Word) (h1 : UnitaryVolumeMass.stMassRatio D) (hv : 1 ≤ D.host.v)
    (s : ℕ) (hs : 2 ≤ s) (hsk : s ≤ D.R.k - 2) (HH C : ℝ) :
    XiS D u HH C s ≤ massS D 2 * (2 * D.host.v) ^ D.R.f * Real.exp (0.72 * D.R.f) * 17 ^ D.R.f *
      Real.sqrt (D.R.k / (2 * Real.pi)) ^ D.R.f * Real.pi ^ ((s - 2) * (D.R.k - s - 2) * D.R.f) *
      (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) := by
  have hk : s + 2 ≤ D.R.k := by omega
  unfold XiS Xi
  rw [if_pos ⟨hs, hsk⟩]
  have hR : ∀ j, 3 ≤ j → 0 < Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j := by
    intro j hj
    have h := massS_ratio D h1 j hj
    have h2 := massS_pos D j
    have h3 := massS_pos D (j - 1)
    rw [h] at h2
    exact (pos_iff_pos_of_mul_pos h2).2 h3
  have hid := Formalism.HermitianLatticeCounting.P.massRatioIdentity (massS D)
    (fun j => if 3 ≤ j then Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j else 1) D.R.k s
    (fun j => by
      by_cases hj : 3 ≤ j
      · simp only [if_pos hj]; exact hR j hj
      · simp only [if_neg hj]; exact one_pos)
    (massS_pos D 2)
    (fun j hj => by simp only [if_pos hj]; exact massS_ratio D h1 j hj) hs hk
  rw [hid]
  have e1 : ∏ j ∈ Finset.Ioc 2 s, (if 3 ≤ j then Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j else 1) =
      ∏ j ∈ Finset.Ioc 2 s, Formalism.HermitianLatticeCounting.LatticeSumBounds.mJ D.R.f D.host.v (fun i => Formalism.HermitianLatticesTheory.lValEta D.host.E i) j :=
    Finset.prod_congr rfl fun j hj => by
      have : 3 ≤ j := (Finset.mem_Ioc.1 hj).1
      rw [if_pos this, ratio_eq_mJ]
  have e2 : ∏ j ∈ Finset.Ioc (D.R.k - s) D.R.k, (if 3 ≤ j then Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j else 1) =
      ∏ j ∈ Finset.Ioc (D.R.k - s) D.R.k,
        Formalism.HermitianLatticeCounting.LatticeSumBounds.mJ D.R.f D.host.v (fun i => Formalism.HermitianLatticesTheory.lValEta D.host.E i) j :=
    Finset.prod_congr rfl fun j hj => by
      have : 3 ≤ j := by have := (Finset.mem_Ioc.1 hj).1; omega
      rw [if_pos this, ratio_eq_mJ]
  rw [e1, e2]
  exact Formalism.HermitianLatticeCounting.P.massRatioBound D.R.f D.R.k s D.host.v (massS D 2) _ hv (massS_pos D 2).le hs hk
    (fun j hj => lVal_bounds D j hj)

/- English proof (translation)
Establish `hx : (0 : ℝ) < large₂.sc.x` using `by linarith [large₂.sc.one_lt_alt]`. Establish `hL : (0 : ℝ) < large₂.sc.L`. Unfold `Formalism.BasicNotions.Scale.L`. Conclude with `Real.rpow_pos_of_pos hx _`. Unfold `Formalism.BasicNotions.Scale.b`.

Combine the linear relations using `[Real.add_one_le_exp large₂.sc.L]`.
-/
theorem one_le_scb {D : D7} (large₂ : SizeData₂ D) : 1 ≤ large₂.sc.b := by
  have hx : (0 : ℝ) < large₂.sc.x := by linarith [large₂.sc.one_lt_alt]
  have hL : (0 : ℝ) < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_pos_of_pos hx _
  unfold Formalism.BasicNotions.Scale.b
  linarith [Real.add_one_le_exp large₂.sc.L]

/- English proof (translation)
Establish `hpi1 : (1 : ℝ) ≤ Real.pi` using `by linarith [Real.pi_gt_three]`. Establish `hkR : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hkn : k ≤ s * k` using `by nlinarith`. Establish `ha : (s - 2) * (k - s - 2) ≤ s * k` using `Nat.mul_le_mul (Nat.sub_le s 2) ((Nat.sub_le _ _).trans (Nat.sub_le _ _))`. Establish `hexp : Real.exp 0.72 ≤ 3`.

Establish `h2 : Real.exp 0.72 ≤ Real.exp 1` using `Real.exp_le_exp.mpr (by norm_num)`. Combine the linear relations using `[Real.exp_one_lt_d9]`. Establish `hsq : Real.sqrt (k / (2 * Real.pi)) ≤ ((s * k : ℕ) : ℝ)`. Establish `h1 : (k : ℝ) / (2 * Real.pi) ≤ (k : ℝ) ^ 2` using `(div_le_self (by positivity) (by linarith)).trans (by nlinarith)`. Establish `h3 : ((k : ℕ) : ℝ) ≤ ((s * k : ℕ) : ℝ)` using `by exact_mod_cast hkn`.

Combine the equalities or inequalities in the displayed calculation. Establish `hpa : Real.pi ^ ((s - 2) * (k - s - 2)) ≤ (4 : ℝ) ^ (s * k)` using `(pow_le_pow_right₀ hpi1 ha).trans (pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four _)`. Establish `key : ∀ m : ℕ, 1 ≤ m → (3 : ℝ) * 17 * (m : ℝ) * 4 ^ m ≤ 408 ^ m`. Introduce `m hm`. Proceed by induction on `m, hm using Nat.le_induction with`.

Consider the case `base => norm_num`. Consider the case `succ m hm ih`. Establish `h4 : (0 : ℝ) ≤ 4 ^ m` using `by positivity`. Establish `hmR : (1 : ℝ) ≤ m` using `by exact_mod_cast hm`. Rewrite using `[pow_succ (4 : ℝ) m, pow_succ (408 : ℝ) m]`.

Use `push_cast`. Use polynomial arithmetic with `[ih, h4, mul_nonneg (sub_nonneg.mpr hmR) h4]`. Establish `hbase : Real.exp 0.72 * 17 * Real.sqrt (k / (2 * Real.pi)) * Real.pi ^ ((s - 2) * (k - s - 2)) ≤ C ^ (s * k)`. Combine the equalities or inequalities in the displayed calculation. Establish `hL : Real.exp (0.72 * f) * 17 ^ f * Real.sqrt (k / (2 * Real.pi)) ^ f * Real.pi ^ ((s - 2) * (k - s - 2) * f) = (Real.exp 0.72 * 17 * Real.sqrt (k / (2 * Real.pi)) * Real.pi ^ ((s - 2) * (k - s - 2))) ^ f`.

Rewrite using `[mul_comm (0.72 : ℝ), Real.exp_nat_mul, pow_mul, mul_pow, mul_pow, mul_pow]`. Rewrite using `[hL, pow_mul C (s * k) f]`. Conclude with `pow_le_pow_left₀ (by positivity) hbase f`.
-/
theorem xi_factors (f k s : ℕ) (hs : 2 ≤ s) (hk : 1 ≤ k) (C : ℝ) (hC : 408 ≤ C) :
    Real.exp (0.72 * f) * 17 ^ f * Real.sqrt (k / (2 * Real.pi)) ^ f * Real.pi ^ ((s - 2) * (k - s - 2) * f) ≤
      C ^ (s * k * f) := by
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn : k ≤ s * k := by nlinarith
  have ha : (s - 2) * (k - s - 2) ≤ s * k :=
    Nat.mul_le_mul (Nat.sub_le s 2) ((Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have hexp : Real.exp 0.72 ≤ 3 := by
    have h2 : Real.exp 0.72 ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
    linarith [Real.exp_one_lt_d9]
  have hsq : Real.sqrt (k / (2 * Real.pi)) ≤ ((s * k : ℕ) : ℝ) := by
    have h1 : (k : ℝ) / (2 * Real.pi) ≤ (k : ℝ) ^ 2 :=
      (div_le_self (by positivity) (by linarith)).trans (by nlinarith)
    have h3 : ((k : ℕ) : ℝ) ≤ ((s * k : ℕ) : ℝ) := by exact_mod_cast hkn
    calc Real.sqrt (k / (2 * Real.pi)) ≤ Real.sqrt ((k : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = k := Real.sqrt_sq (by positivity)
      _ ≤ _ := h3
  have hpa : Real.pi ^ ((s - 2) * (k - s - 2)) ≤ (4 : ℝ) ^ (s * k) :=
    (pow_le_pow_right₀ hpi1 ha).trans (pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four _)
  have key : ∀ m : ℕ, 1 ≤ m → (3 : ℝ) * 17 * (m : ℝ) * 4 ^ m ≤ 408 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have h4 : (0 : ℝ) ≤ 4 ^ m := by positivity
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [pow_succ (4 : ℝ) m, pow_succ (408 : ℝ) m]
      push_cast
      nlinarith [ih, h4, mul_nonneg (sub_nonneg.mpr hmR) h4]
  have hbase : Real.exp 0.72 * 17 * Real.sqrt (k / (2 * Real.pi)) * Real.pi ^ ((s - 2) * (k - s - 2)) ≤
      C ^ (s * k) := by
    calc Real.exp 0.72 * 17 * Real.sqrt (k / (2 * Real.pi)) * Real.pi ^ ((s - 2) * (k - s - 2))
        ≤ 3 * 17 * ((s * k : ℕ) : ℝ) * (4 : ℝ) ^ (s * k) := by gcongr
      _ ≤ (408 : ℝ) ^ (s * k) := key _ (le_trans hk hkn)
      _ ≤ C ^ (s * k) := pow_le_pow_left₀ (by norm_num) hC _
  have hL : Real.exp (0.72 * f) * 17 ^ f * Real.sqrt (k / (2 * Real.pi)) ^ f *
      Real.pi ^ ((s - 2) * (k - s - 2) * f) =
      (Real.exp 0.72 * 17 * Real.sqrt (k / (2 * Real.pi)) * Real.pi ^ ((s - 2) * (k - s - 2))) ^ f := by
    rw [mul_comm (0.72 : ℝ), Real.exp_nat_mul, pow_mul, mul_pow, mul_pow, mul_pow]
  rw [hL, pow_mul C (s * k) f]
  exact pow_le_pow_left₀ (by positivity) hbase f

/- English proof (translation)
Introduce `hH`. Establish `hm2` using `hM2 hH`. Take `⟨-, -, -, -, -, -, -, -, -, -, h11, -, -, -, -, -, -, -, h19, -⟩` from `hH.1.1`. Establish `hb1` using `one_le_scb large₂`. Establish `hb0 : 0 < large₂.sc.b` using `by linarith`.

Establish `hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2`. Establish `: (1 : ℝ) ≤ (D.R.m : ℝ)` using `by exact_mod_cast (le_trans (by norm_num) D.R.two_le_m)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hf0 : (0 : ℝ) ≤ (D.R.f : ℝ)` using `Nat.cast_nonneg _`. Establish `hmono : (large₂.sc.b ^ (C₂ * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ C₂ ≤ (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ C`.

Rewrite using `[← Real.rpow_mul hb0.le, ← Real.rpow_mul hb0.le]`. Apply `Real.rpow_le_rpow_of_exponent_le hb1` to reduce the goal to its premises. Establish `: C₂ ^ 2 * ((D.R.m : ℝ) ^ 2 * D.R.f) ≤ C ^ 2 * ((D.R.m : ℝ) ^ 2 * D.R.f)` using `mul_le_mul_of_nonneg_right (by linarith) (by positivity)`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨fun V _ _ _ _ h L hs ho => le_trans (hm2 V h L hs ho) hmono, fun s hs hsk HH => ?_⟩` and prove the remaining obligations.

Establish `hx` using `xi_explicit D u h1 h19 s hs hsk HH C`. Establish `hk1 : 1 ≤ D.R.k` using `by omega`. Establish `hfac` using `xi_factors D.R.f D.R.k s hs hk1 C hC`. Establish `hmass : massS D 2 ≤ (large₂.sc.b ^ (C₂ * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ C₂`. Rewrite using `[massS_eq]`.

Conclude with `hm2 _ _ _ (Formalism.MainNotions.StandardLattice.stdForm_symm D.host.E 2) (Formalism.MainNotions.StandardLattice.stdLat_ortho D.host.E 2)`. Establish `hL0 : 0 ≤ large₂.sc.L`. Unfold `Scale.L`. Conclude with `Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _`. Establish `hrd : 2 * D.host.v ≤ large₂.sc.b`.

Establish `e : 2 * D.host.v = D.host.rdE` using `by unfold Host.v; ring`. Rewrite using `[e]`. Establish `hpos : 0 < D.host.rdE` using `by rw [← e]; linarith`. Establish `h2 : Real.log D.host.rdE ≤ large₂.sc.L` using `le_trans h11 (div_le_self hL0 hCl)`. Unfold `Scale.b`.

Conclude with `(Real.log_le_iff_le_exp hpos).1 h2`. Establish `hA : massS D 2 * (2 * D.host.v) ^ D.R.f ≤ Hb large₂.sc.b C D.R.m D.R.f ^ C`. Establish `h3 : (2 * D.host.v) ^ D.R.f ≤ large₂.sc.b ^ (D.R.f : ℝ)`. Rewrite using `[Real.rpow_natCast]`. Conclude with `pow_le_pow_left₀ (by linarith) hrd _`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]`. Use `_ ≤ large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * C) := by`. Apply `Real.rpow_le_rpow_of_exponent_le hb1` to reduce the goal to its premises. Establish `h4 : C₂ ^ 2 * (D.R.m : ℝ) ^ 2 + 1 ≤ C ^ 2 * (D.R.m : ℝ) ^ 2` using `by nlinarith`.

Establish `h5` using `mul_le_mul_of_nonneg_right h4 hf0`. Use the polynomial consequences of the given equalities and inequalities. Use `_ = Hb large₂.sc.b C D.R.m D.R.f ^ C := by`. Unfold `Hb`. Rewrite using `[← Real.rpow_mul hb0.le]`.

Establish `hP : 0 ≤ (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f)`. Establish `: 0 ≤ D.host.v` using `by linarith`. Check the signs of the components of the expression. Establish `hv0 : 0 ≤ 2 * D.host.v` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.

Use `le_trans hx (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ Hb large₂.sc.b C D.R.m D.R.f ^ C * C ^ (s * D.R.k * D.R.f) * (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) := by`. Apply `mul_le_mul_of_nonneg_right _ hP` to reduce the goal to its premises. Conclude with `mul_le_mul hA hfac (by positivity) (by unfold Hb; positivity)`.
-/
theorem first_bound_of_mass_ratio (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C₂ C : ℝ)
    (h1 : VanishingOnXAndXPlusMass.adm1 D) (hM2 : UnitaryVolumeMass.stMass2 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C₂)
    (hC2 : C₂ ^ 2 + 1 ≤ C ^ 2) (hC : 408 ≤ C) (hCl : 1 ≤ Cl) :
    VanishingOnXAndXPlusMass.Conclusion1 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C (Real.exp 1 * Real.pi) := by
  intro hH
  have hm2 := hM2 hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -, -, -, -, -, -, -, h19, -⟩ := hH.1.1
  have hb1 := one_le_scb large₂
  have hb0 : 0 < large₂.sc.b := by linarith
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast (le_trans (by norm_num) D.R.two_le_m)
    nlinarith
  have hf0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have hmono : (large₂.sc.b ^ (C₂ * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ C₂ ≤ (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ C := by
    rw [← Real.rpow_mul hb0.le, ← Real.rpow_mul hb0.le]
    apply Real.rpow_le_rpow_of_exponent_le hb1
    have : C₂ ^ 2 * ((D.R.m : ℝ) ^ 2 * D.R.f) ≤ C ^ 2 * ((D.R.m : ℝ) ^ 2 * D.R.f) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  refine ⟨fun V _ _ _ _ h L hs ho => le_trans (hm2 V h L hs ho) hmono, fun s hs hsk HH => ?_⟩
  have hx := xi_explicit D u h1 h19 s hs hsk HH C
  have hk1 : 1 ≤ D.R.k := by omega
  have hfac := xi_factors D.R.f D.R.k s hs hk1 C hC

  have hmass : massS D 2 ≤ (large₂.sc.b ^ (C₂ * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ C₂ := by
    rw [massS_eq]
    exact hm2 _ _ _ (Formalism.MainNotions.StandardLattice.stdForm_symm D.host.E 2) (Formalism.MainNotions.StandardLattice.stdLat_ortho D.host.E 2)
  have hL0 : 0 ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  have hrd : 2 * D.host.v ≤ large₂.sc.b := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [e]
    have hpos : 0 < D.host.rdE := by rw [← e]; linarith
    have h2 : Real.log D.host.rdE ≤ large₂.sc.L := le_trans h11 (div_le_self hL0 hCl)
    unfold Scale.b
    exact (Real.log_le_iff_le_exp hpos).1 h2
  have hA : massS D 2 * (2 * D.host.v) ^ D.R.f ≤ Hb large₂.sc.b C D.R.m D.R.f ^ C := by
    have h3 : (2 * D.host.v) ^ D.R.f ≤ large₂.sc.b ^ (D.R.f : ℝ) := by
      rw [Real.rpow_natCast]
      exact pow_le_pow_left₀ (by linarith) hrd _
    calc massS D 2 * (2 * D.host.v) ^ D.R.f
        ≤ (large₂.sc.b ^ (C₂ * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ C₂ * large₂.sc.b ^ (D.R.f : ℝ) :=
          mul_le_mul hmass h3 (by have : 0 ≤ 2 * D.host.v := by linarith
                                  positivity) (by positivity)
      _ = large₂.sc.b ^ (C₂ * (D.R.m : ℝ) ^ 2 * D.R.f * C₂ + D.R.f) := by
          rw [← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]
      _ ≤ large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * C) := by
          apply Real.rpow_le_rpow_of_exponent_le hb1
          have h4 : C₂ ^ 2 * (D.R.m : ℝ) ^ 2 + 1 ≤ C ^ 2 * (D.R.m : ℝ) ^ 2 := by nlinarith
          have h5 := mul_le_mul_of_nonneg_right h4 hf0
          nlinarith
      _ = Hb large₂.sc.b C D.R.m D.R.f ^ C := by
          unfold Hb
          rw [← Real.rpow_mul hb0.le]
  have hP : 0 ≤ (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) := by
    have : 0 ≤ D.host.v := by linarith
    positivity
  have hv0 : 0 ≤ 2 * D.host.v := by linarith
  calc XiS D u HH C s
      ≤ (massS D 2 * (2 * D.host.v) ^ D.R.f) *
          (Real.exp (0.72 * D.R.f) * 17 ^ D.R.f * Real.sqrt (D.R.k / (2 * Real.pi)) ^ D.R.f *
            Real.pi ^ ((s - 2) * (D.R.k - s - 2) * D.R.f)) *
          (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) := by
        refine le_trans hx (le_of_eq ?_); ring
    _ ≤ Hb large₂.sc.b C D.R.m D.R.f ^ C * C ^ (s * D.R.k * D.R.f) *
          (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) := by
        apply mul_le_mul_of_nonneg_right _ hP
        exact mul_le_mul hA hfac (by positivity) (by unfold Hb; positivity)

/- English proof (translation)
Take `⟨C₂, x0, hx0⟩` from `hM`. Use `⟨max 408 (|C₂| + 1), Real.exp 1 * Real.pi, x0, fun x hx i u u' => ?_⟩` and prove the remaining obligations. Use `first_bound_of_mass_ratio _ _ u u' _ _ _ _ _ _ _ _ _ C₂ _ (h1 x i) (hx0 x hx i u u') ?_ (le_max_left _ _) hCl` and prove the remaining obligations. Establish `h2 : |C₂| + 1 ≤ max 408 (|C₂| + 1)` using `le_max_right _ _`. Establish `h3 : 0 ≤ |C₂|` using `abs_nonneg _`.

Establish `h4 : C₂ ^ 2 = |C₂| ^ 2` using `(sq_abs C₂).symm`. Rewrite using `[h4]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem family_first_bound_of_mass_ratio {eps : ℝ} (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ) (h1 : VanishingOnXAndXPlusMass.familyUnitInput Fm)
    (hM : AuxiliaryNormPrimes.FamilyRankTwoMassBound Fm Cg cb Cu cT CT C0 A) (hCl : 1 ≤ sCl Fm) : VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 A := by
  obtain ⟨C₂, x0, hx0⟩ := hM
  refine ⟨max 408 (|C₂| + 1), Real.exp 1 * Real.pi, x0, fun x hx i u u' => ?_⟩
  refine first_bound_of_mass_ratio _ _ u u' _ _ _ _ _ _ _ _ _ C₂ _ (h1 x i) (hx0 x hx i u u') ?_ (le_max_left _ _) hCl
  have h2 : |C₂| + 1 ≤ max 408 (|C₂| + 1) := le_max_right _ _
  have h3 : 0 ≤ |C₂| := abs_nonneg _
  have h4 : C₂ ^ 2 = |C₂| ^ 2 := (sq_abs C₂).symm
  rw [h4]
  nlinarith

/- English proof (translation)
Use `show (riemannZeta (M : ℂ)).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M`. Establish `h1 : 1 < ((M : ℂ)).re`. Establish `: (1 : ℝ) < M` using `by exact_mod_cast (by omega : 1 < M)`. Simplify using `using this`. Rewrite using `[zeta_eq_tsum_one_div_nat_add_one_cpow h1]`.

Repeatedly rewrite using `[Complex.cpow_natCast]`. Establish `e : (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ M) = ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_tsum]`. Apply the tactic sequence `push_cast <;> rfl`. Rewrite using `[e, Complex.ofReal_re]`.
-/
theorem riemannZeta_nat_re (M : ℕ) (hM : 2 ≤ M) : (riemannZeta (M : ℂ)).re = Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR M := by
  show (riemannZeta (M : ℂ)).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M
  have h1 : 1 < ((M : ℂ)).re := by
    have : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
    simpa using this
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1]
  simp_rw [Complex.cpow_natCast]
  have e : (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ M) = ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    push_cast <;> rfl
  rw [e, Complex.ofReal_re]

/- English proof (translation)
Introduce `i hi`. Rewrite using `[riemannZeta_nat_re i hi]`. Conclude with `Formalism.MainNotions.StandardLattice.massIdentity_holds D i hi`.
-/
theorem log_L_value_le_log_zeta (D : D7) : UnitaryVolumeMass.stMassL D := by
  intro i hi
  rw [riemannZeta_nat_re i hi]
  exact Formalism.MainNotions.StandardLattice.massIdentity_holds D i hi

/- English proof (translation)
The claim follows from `log_L_value_le_log_zeta D`.
-/
theorem lattice_count_second_admissible (D : D7) : VanishingOnXAndXPlusMass.adm2 D := log_L_value_le_log_zeta D
/- English proof (translation)
The claim follows from `log_L_value_le_log_zeta D`.
-/
theorem mass_bound_log_L_value (D : D7) : AuxiliaryNormPrimes.GL5LogLValueBoundByZeta D := log_L_value_le_log_zeta D
/- English proof (translation)
Introduce `i hi` and use `log_L_value_le_log_zeta D i (by omega)`.
-/
theorem mass_bound_at_each_index (D : D7) : LocalBesselAndTopKernel.GL5LogLValueBoundByZeta D := fun i hi => log_L_value_le_log_zeta D i (by omega)
/- English proof (translation)
The claim follows from `log_L_value_le_log_zeta D`.
-/
theorem log_L_value_bound_admissible (D : D7) : NonGenericAndKTwoTheorems.LogThetaIdentity D := log_L_value_le_log_zeta D

section FamL
variable {eps : ℝ} (Fm : FamP eps)
/- English proof (translation)
Introduce `x i` and use `lattice_count_second_admissible _`.
-/
theorem family_lattice_count_second : VanishingOnXAndXPlusMass.FamilySecondHypothesis Fm := fun x i => lattice_count_second_admissible _
/- English proof (translation)
Introduce `x i` and use `mass_bound_log_L_value _`.
-/
theorem family_mass_bound_log_L : AuxiliaryNormPrimes.BesselFormLine Fm := fun x i => mass_bound_log_L_value _
/- English proof (translation)
Introduce `x i` and use `mass_bound_at_each_index _`.
-/
theorem family_mass_bound_each_index : LocalBesselAndTopKernel.BesselFormLine Fm := fun x i => mass_bound_at_each_index _
/- English proof (translation)
Introduce `x i` and use `log_L_value_bound_admissible _`.
-/
theorem family_log_L_value_bound : NonGenericAndKTwoTheorems.FamilyMassSecondHypothesis Fm := fun x i => log_L_value_bound_admissible _
end FamL

open Formalism.MainNotions.S.Lat in

/- English proof (translation)
Introduce `hT h3 hsp F0 he hz s hs`. Take `⟨e1, e2⟩` from `h hT h3 hsp F0 he hz s hs`. Use `⟨e1, fun Λ hΛ => ⟨e2 Λ hΛ, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[e2 Λ hΛ, e1]`. Establish `hk : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`.

Establish `ha` using `(Formalism.HermitianLatticeCounting.P.powSubOneIdentities (Tu D u) D.R.k D.R.f (by omega) hk).2`. Rewrite `ha` using `[div_pow]`. Establish `hN : NT D u = (Tu D u : ℝ) ^ D.R.f` using `rfl`. Rewrite using `[hN, mul_div_assoc]`. Conclude with `mul_le_mul_of_nonneg_left ha (massS_pos D D.R.k).le`.
-/
theorem lattice_mass_of_row_reps (D : D7) (u : D.what₂.Word)
    (h : (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) →
      ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
      ∀ s : Finset (LatV D), IsRowReps D F0 s →
        massRows D F0 s = massS D D.R.k * ((Tu D u : ℝ) ^ D.R.k - 1) ^ D.R.f ∧
        ∀ Λ : LatV D, IsRowLat D F0 Λ →
          Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) = massRows D F0 s / ((Tu D u : ℝ) - 1) ^ D.R.f) :
    VanishingOnXAndXPlusMass.PointsLemma D u := by
  intro hT h3 hsp F0 he hz s hs
  obtain ⟨e1, e2⟩ := h hT h3 hsp F0 he hz s hs
  refine ⟨e1, fun Λ hΛ => ⟨e2 Λ hΛ, ?_⟩⟩
  rw [e2 Λ hΛ, e1]
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have ha := (Formalism.HermitianLatticeCounting.P.powSubOneIdentities (Tu D u) D.R.k D.R.f (by omega) hk).2
  rw [div_pow] at ha
  have hN : NT D u = (Tu D u : ℝ) ^ D.R.f := rfl
  rw [hN, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left ha (massS_pos D D.R.k).le

/- English proof (translation)
Introduce `j hj V V' _ _ _ _ _ _ _ _ f f' L L' hs hs' ho ho'` and use `h D.host.E D.sp.cm.cmUnram j hj V V' f f' L L' hs hs' ho ho'`.
-/
theorem mass_ratio_of_siegel_cm_unramified (h : Formalism.HermitianLatticesTheory.SiegelMassRatio) (D : D7) : UnitaryVolumeMass.stMassRatio D :=
  fun j hj V V' _ _ _ _ _ _ _ _ f f' L L' hs hs' ho ho' =>
    h D.host.E D.sp.cm.cmUnram j hj V V' f f' L L' hs hs' ho ho'

/- English proof (translation)
The claim follows from `mass_ratio_of_siegel_cm_unramified h D`.
-/
theorem lattice_count_first_of_siegel (h : Formalism.HermitianLatticesTheory.SiegelMassRatio) (D : D7) : VanishingOnXAndXPlusMass.adm1 D := mass_ratio_of_siegel_cm_unramified h D
/- English proof (translation)
The claim follows from `mass_ratio_of_siegel_cm_unramified h D`.
-/
theorem mass_ratio_admissible_of_siegel (h : Formalism.HermitianLatticesTheory.SiegelMassRatio) (D : D7) : AuxiliaryNormPrimes.FamilySchurFormalDegree D := mass_ratio_of_siegel_cm_unramified h D
/- English proof (translation)
The claim follows from `mass_ratio_of_siegel_cm_unramified h D`.
-/
theorem mass_ratio_alt (h : Formalism.HermitianLatticesTheory.SiegelMassRatio) (D : D7) : LocalBesselAndTopKernel.FamilySchurFormalDegree D := mass_ratio_of_siegel_cm_unramified h D
/- English proof (translation)
The claim follows from `mass_ratio_of_siegel_cm_unramified h D`.
-/
theorem mass_ratio_admissible_siegel_alt (h : Formalism.HermitianLatticesTheory.SiegelMassRatio) (D : D7) : NonGenericAndKTwoTheorems.IntegrationByPartsAlt D := mass_ratio_of_siegel_cm_unramified h D

section FamM
variable {eps : ℝ} (Fm : FamP eps)
/- English proof (translation)
Introduce `x i` and use `lattice_count_first_of_siegel h _`.
-/
theorem family_lattice_count_first_of_siegel (h : Formalism.HermitianLatticesTheory.SiegelMassRatio) : VanishingOnXAndXPlusMass.familyUnitInput Fm := fun x i => lattice_count_first_of_siegel h _
/- English proof (translation)
Introduce `x i` and use `mass_ratio_admissible_of_siegel h _`.
-/
theorem family_mass_ratio_siegel_bound (h : Formalism.HermitianLatticesTheory.SiegelMassRatio) : AuxiliaryNormPrimes.SecondSizeStatement Fm := fun x i => mass_ratio_admissible_of_siegel h _
/- English proof (translation)
Introduce `x i` and use `mass_ratio_alt h _`.
-/
theorem family_mass_ratio (h : Formalism.HermitianLatticesTheory.SiegelMassRatio) : LocalBesselAndTopKernel.SecondSizeStatement Fm := fun x i => mass_ratio_alt h _
/- English proof (translation)
Introduce `x i` and use `mass_ratio_admissible_siegel_alt h _`.
-/
theorem family_siegel_mass_ratio_admissible (h : Formalism.HermitianLatticesTheory.SiegelMassRatio) : NonGenericAndKTwoTheorems.FamilyMassFirstHypothesis Fm := fun x i => mass_ratio_admissible_siegel_alt h _
end FamM

/- English proof (translation)
The claim follows from `lattice_count_fourth_admissible`.
-/
theorem hadamard_inequality_admissible : AuxiliaryNormPrimes.HadamardDeterminantInequality := lattice_count_fourth_admissible

/- English proof (translation)
Introduce `N G hG` and use `(h N G hG).trans (Formalism.HermitianLatticeCounting.P.minkowski_number_dvd N)`.
-/
theorem minkowski_divides_factorial_of_bound (h : NonGenericAndKTwoTheorems.adm11) : UnitaryVolumeMass.stBRmink :=
  fun N G hG => (h N G hG).trans (Formalism.HermitianLatticeCounting.P.minkowski_number_dvd N)

/- English proof (translation)
The claim follows from `minkowski_divides_factorial_of_bound h`.
-/
theorem minkowski_admissible_of_bound (h : NonGenericAndKTwoTheorems.adm11) : AuxiliaryNormPrimes.MinkowskiFiniteSubgroupOrder := minkowski_divides_factorial_of_bound h
/- English proof (translation)
The claim follows from `minkowski_divides_factorial_of_bound h`.
-/
theorem lattice_minkowski_of_bound (h : NonGenericAndKTwoTheorems.adm11) : VanishingOnXAndXPlusMass.adm15 := minkowski_divides_factorial_of_bound h

/- English proof (translation)
Take `⟨lift, hlift⟩ : ∃ lift : N ⧸ M' → N, ∀ x, M'.mkQ (lift x) = x` from `⟨fun x => (Submodule.mkQ_surjective M' x).choose, fun x => (Submodule.mkQ_surjective M' x).choose_spec⟩`. Take `⟨rep, hrep⟩ : ∃ rep : R ⧸ I → R, ∀ c, Ideal.Quotient.mk I (rep c) = c` from `⟨fun c => (Ideal.Quotient.mk_surjective c).choose, fun c => (Ideal.Quotient.mk_surjective c).choose_spec⟩`. Set `g : (s → R ⧸ I) → N ⧸ S` to `fun c => S.mkQ (∑ x : s, rep (c x) • lift x)`. Establish `hg : Function.Surjective g`. Introduce `y`.

Take `⟨n, rfl⟩` from `Submodule.mkQ_surjective S y`. Establish `hmem : M'.mkQ n ∈ Submodule.span R (s : Set (N ⧸ M'))`. Rewrite using `[hs]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨f, hf⟩` from `Submodule.mem_span_finset.mp hmem`.

Establish `hf' : ∑ i ∈ s, f i • i = M'.mkQ n` using `by first`. Consider the case `exact hf`. Consider the case `exact hf.2`. Use `⟨fun x => Ideal.Quotient.mk I (f x), ?_⟩` and prove the remaining obligations. Establish `e1 : M'.mkQ (∑ x : s, f x • lift x) = ∑ x : s, f x • (x : N ⧸ M')`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun x _ => by rw [map_smul, hlift]`. Establish `e2` using `e1.trans ((Finset.sum_coe_sort s (fun i => f i • i)).trans hf')`. Establish `hM'mem : ∑ x : s, f x • lift x - n ∈ M'`. Rewrite `e2` using `[Submodule.mkQ_apply, Submodule.mkQ_apply]`.

Conclude with `(Submodule.Quotient.eq M').mp e2`. Use `show S.mkQ (∑ x : s, rep (Ideal.Quotient.mk I (f x)) • lift x) = S.mkQ n`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Establish `h1 : ∑ x : s, rep (Ideal.Quotient.mk I (f x)) • lift x - n = ∑ x : s, (rep (Ideal.Quotient.mk I (f x)) - f x) • lift x + (∑ x : s, f x • lift x - n)`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`.

Normalize the expressions using the abelian group laws. Rewrite using `[h1]`. Use `S.add_mem (S.sum_mem fun x _ => hI _ ?_ _) (hM hM'mem)` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq, hrep]`. Establish `hcard` using `Nat.card_le_card_of_surjective g hg`.

Simplify using `only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_coe] at hcard`. Conclude with `hcard`.
-/
theorem card_quot_le_pow {R : Type} [CommRing R] {N : Type} [AddCommGroup N] [Module R N] (I : Ideal R) [Finite (R ⧸ I)]
    (S M' : Submodule R N) (hM : M' ≤ S) (hI : ∀ a ∈ I, ∀ n : N, a • n ∈ S) (s : Finset (N ⧸ M'))
    (hs : Submodule.span R (s : Set (N ⧸ M')) = ⊤) : Nat.card (N ⧸ S) ≤ Nat.card (R ⧸ I) ^ s.card := by
  classical
  obtain ⟨lift, hlift⟩ : ∃ lift : N ⧸ M' → N, ∀ x, M'.mkQ (lift x) = x :=
    ⟨fun x => (Submodule.mkQ_surjective M' x).choose, fun x => (Submodule.mkQ_surjective M' x).choose_spec⟩
  obtain ⟨rep, hrep⟩ : ∃ rep : R ⧸ I → R, ∀ c, Ideal.Quotient.mk I (rep c) = c :=
    ⟨fun c => (Ideal.Quotient.mk_surjective c).choose, fun c => (Ideal.Quotient.mk_surjective c).choose_spec⟩
  let g : (s → R ⧸ I) → N ⧸ S := fun c => S.mkQ (∑ x : s, rep (c x) • lift x)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective S y
    have hmem : M'.mkQ n ∈ Submodule.span R (s : Set (N ⧸ M')) := by
      rw [hs]
      trivial
    obtain ⟨f, hf⟩ := Submodule.mem_span_finset.mp hmem
    have hf' : ∑ i ∈ s, f i • i = M'.mkQ n := by
      first
        | exact hf
        | exact hf.2
    refine ⟨fun x => Ideal.Quotient.mk I (f x), ?_⟩
    have e1 : M'.mkQ (∑ x : s, f x • lift x) = ∑ x : s, f x • (x : N ⧸ M') := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [map_smul, hlift]
    have e2 := e1.trans ((Finset.sum_coe_sort s (fun i => f i • i)).trans hf')
    have hM'mem : ∑ x : s, f x • lift x - n ∈ M' := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at e2
      exact (Submodule.Quotient.eq M').mp e2
    show S.mkQ (∑ x : s, rep (Ideal.Quotient.mk I (f x)) • lift x) = S.mkQ n
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have h1 : ∑ x : s, rep (Ideal.Quotient.mk I (f x)) • lift x - n =
        ∑ x : s, (rep (Ideal.Quotient.mk I (f x)) - f x) • lift x + (∑ x : s, f x • lift x - n) := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    rw [h1]
    refine S.add_mem (S.sum_mem fun x _ => hI _ ?_ _) (hM hM'mem)
    rw [← Ideal.Quotient.eq, hrep]
  have hcard := Nat.card_le_card_of_surjective g hg
  simp only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_coe] at hcard
  exact hcard

/- English proof (translation)
Establish `h0 : p ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField K)`. Establish `h1 : Ideal.absNorm p ≠ 0` using `fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `h2 : Ideal.absNorm p ≠ 1` using `fun h => hp.ne_top (Ideal.absNorm_eq_one_iff.mp h)`. Use linear arithmetic over natural numbers and integers.
-/
theorem absNorm_ge_two {K : Type} [Field K] [NumberField K] (p : Ideal (𝓞 K)) (hp : p.IsMaximal) :
    2 ≤ Ideal.absNorm p := by
  have h0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField K)
  have h1 : Ideal.absNorm p ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h)
  have h2 : Ideal.absNorm p ≠ 1 := fun h => hp.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

/- English proof (translation)
Unfold `pE`. Rewrite using `[Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E, D.sp.cm.deg2]`.
-/
theorem absNorm_pE (D : D7) (p : Ideal (𝓞 D.host.F)) :
    Ideal.absNorm (pE D.host.F D.host.E p) = Ideal.absNorm p ^ 2 := by
  unfold pE
  rw [Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E, D.sp.cm.deg2]

/- English proof (translation)
Take `⟨s, hs_card, hs_span⟩` from `he`. Establish `h2 : 2 ≤ Ideal.absNorm p` using `absNorm_ge_two p hp`. Establish `hN : Nat.card (𝓞 D.host.E ⧸ pE D.host.F D.host.E p) = Ideal.absNorm p ^ 2`. Rewrite using `[← absNorm_pE D p, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 D.host.E ⧸ pE D.host.F D.host.E p) := Nat.finite_of_card_ne_zero (by rw [hN]; exact pow_ne_zero 2 (by omega))`.

Establish `hI : ∀ a ∈ pE D.host.F D.host.E p, ∀ n : ↥(Formalism.HermitianLatticesTheory.dual h M), a • n ∈ (M ⊔ pE D.host.F D.host.E p • Formalism.HermitianLatticesTheory.dual h M).comap (Formalism.HermitianLatticesTheory.dual h M).subtype` using `fun a ha n => Submodule.mem_sup_right (Submodule.smul_mem_smul ha n.2)`. Establish `hc` using `card_quot_le_pow (pE D.host.F D.host.E p) ((M ⊔ pE D.host.F D.host.E p • Formalism.HermitianLatticesTheory.dual h M).comap (Formalism.HermitianLatticesTheory.dual h M).subtype) (M.comap (Formalism.HermitianLatticesTheory.dual h M).subtype) (Submodule.comap_mono le_sup_left) hI s …`. Rewrite `hc` using `[hN]`. Unfold `eP`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eP_le (D : D7) {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
    (M : Submodule (𝓞 D.host.E) V) (e : ℕ) (he : DiscGen h M e) (p : Ideal (𝓞 D.host.F)) (hp : p.IsMaximal) :
    eP h M p ≤ e := by
  obtain ⟨s, hs_card, hs_span⟩ := he
  have h2 : 2 ≤ Ideal.absNorm p := absNorm_ge_two p hp
  have hN : Nat.card (𝓞 D.host.E ⧸ pE D.host.F D.host.E p) = Ideal.absNorm p ^ 2 := by
    rw [← absNorm_pE D p, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ pE D.host.F D.host.E p) :=
    Nat.finite_of_card_ne_zero (by rw [hN]; exact pow_ne_zero 2 (by omega))
  have hI : ∀ a ∈ pE D.host.F D.host.E p, ∀ n : ↥(Formalism.HermitianLatticesTheory.dual h M),
      a • n ∈ (M ⊔ pE D.host.F D.host.E p • Formalism.HermitianLatticesTheory.dual h M).comap (Formalism.HermitianLatticesTheory.dual h M).subtype :=
    fun a ha n => Submodule.mem_sup_right (Submodule.smul_mem_smul ha n.2)
  have hc := card_quot_le_pow (pE D.host.F D.host.E p)
    ((M ⊔ pE D.host.F D.host.E p • Formalism.HermitianLatticesTheory.dual h M).comap (Formalism.HermitianLatticesTheory.dual h M).subtype)
    (M.comap (Formalism.HermitianLatticesTheory.dual h M).subtype) (Submodule.comap_mono le_sup_left) hI s hs_span
  rw [hN] at hc
  unfold eP
  calc _ ≤ Nat.log (Ideal.absNorm p ^ 2) ((Ideal.absNorm p ^ 2) ^ s.card) := Nat.log_mono_right hc
    _ = s.card := Nat.log_pow (by nlinarith) _
    _ ≤ e := hs_card

/- English proof (translation)
Unfold `Formalism.MainNotions.S.Cnt.thP Formalism.HermitianLatticeCounting.LatticeSumBounds.theta`. Establish `e : j - min ep j = j - ep`. Simplify using `only [min_def]`. Apply the tactic sequence `split <;> omega`. Rewrite using `[e]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_natCast]`.
-/
theorem countTheta_eq_theta (j ep : ℕ) (eta : ℤ) (q : ℕ) :
    thP j ep eta q = Formalism.HermitianLatticeCounting.LatticeSumBounds.theta j (min ep j) (eta : ℝ) (q : ℝ) := by
  unfold Formalism.MainNotions.S.Cnt.thP Formalism.HermitianLatticeCounting.LatticeSumBounds.theta
  have e : j - min ep j = j - ep := by
    simp only [min_def]
    split <;> omega
  rw [e]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_neg, zpow_natCast]

/- English proof (translation)
Establish `hq : 2 ≤ Ideal.absNorm p` using `absNorm_ge_two p hp`. Establish `hqR : (2 : ℝ) ≤ ((Ideal.absNorm p : ℕ) : ℝ)` using `by exact_mod_cast hq`. Establish `hη : ((eta₃ D.host.F D.host.E p : ℤ) : ℝ) = 1 ∨ ((eta₃ D.host.F D.host.E p : ℤ) : ℝ) = -1`. Unfold `eta₃`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hfac : ∀ i ∈ Finset.Icc (j - eP h M p + 1) j, 0 < 1 - ((eta₃ D.host.F D.host.E p : ℤ) : ℝ) ^ i * ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ)) ∧ 1 - ((eta₃ D.host.F D.host.E p : ℤ) : ℝ) ^ i * ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ)) ≤ 2`. Introduce `i hi`. Establish `hi1 : 1 ≤ i`. Rewrite `hi` using `[Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers.

Establish `hQ : (2 : ℝ) ≤ ((Ideal.absNorm p : ℕ) : ℝ) ^ i` using `hqR.trans ((pow_one _).symm.le.trans (pow_le_pow_right₀ (by linarith) hi1))`. Establish `hQ0 : (0 : ℝ) < ((Ideal.absNorm p : ℕ) : ℝ) ^ i` using `by linarith`. Establish `hx : ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ)) = (((Ideal.absNorm p : ℕ) : ℝ) ^ i)⁻¹`. Rewrite using `[zpow_neg, zpow_natCast]`. Establish `hx0 : 0 < ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ))`.

Rewrite using `[hx]`. Conclude with `inv_pos.mpr hQ0`. Establish `hmul : ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ)) * ((Ideal.absNorm p : ℕ) : ℝ) ^ i = 1`. Rewrite using `[hx]`. Conclude with `inv_mul_cancel₀ hQ0.ne'`.

Establish `hxh : ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ)) ≤ 1 / 2`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hQ hx0.le]`. Establish `habs : |((eta₃ D.host.F D.host.E p : ℤ) : ℝ) ^ i| = 1`. Apply the tactic sequence `rcases hη with hη | hη <;> rw [hη] <;> simp`. Establish `hb : |((eta₃ D.host.F D.host.E p : ℤ) : ℝ) ^ i * ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ))| ≤ 1 / 2`.

Rewrite using `[abs_mul, habs, one_mul, abs_of_pos hx0]`. Conclude with `hxh`. Take `⟨hb1, hb2⟩` from `abs_le.mp hb`. Apply the tactic sequence `constructor <;> linarith`. Establish `hcard : (Finset.Icc (j - eP h M p + 1) j).card ≤ e`.

Rewrite using `[Nat.card_Icc]`. Use `eP_le D h M e he p hp` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Unfold `thP`. Use `⟨Finset.prod_pos fun i hi => (hfac i hi).1, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem local_theta_factor_pos_le (D : D7) {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
    (M : Submodule (𝓞 D.host.E) V) (e : ℕ) (he : DiscGen h M e) (j : ℕ) (p : Ideal (𝓞 D.host.F)) (hp : p.IsMaximal) :
    0 < thP j (eP h M p) (eta₃ D.host.F D.host.E p) (Ideal.absNorm p) ∧
      thP j (eP h M p) (eta₃ D.host.F D.host.E p) (Ideal.absNorm p) ≤ (2 : ℝ) ^ e := by
  have hq : 2 ≤ Ideal.absNorm p := absNorm_ge_two p hp
  have hqR : (2 : ℝ) ≤ ((Ideal.absNorm p : ℕ) : ℝ) := by exact_mod_cast hq
  have hη : ((eta₃ D.host.F D.host.E p : ℤ) : ℝ) = 1 ∨ ((eta₃ D.host.F D.host.E p : ℤ) : ℝ) = -1 := by
    unfold eta₃
    split_ifs <;> simp
  have hfac : ∀ i ∈ Finset.Icc (j - eP h M p + 1) j,
      0 < 1 - ((eta₃ D.host.F D.host.E p : ℤ) : ℝ) ^ i * ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ)) ∧
      1 - ((eta₃ D.host.F D.host.E p : ℤ) : ℝ) ^ i * ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ)) ≤ 2 := by
    intro i hi
    have hi1 : 1 ≤ i := by
      rw [Finset.mem_Icc] at hi
      omega
    have hQ : (2 : ℝ) ≤ ((Ideal.absNorm p : ℕ) : ℝ) ^ i :=
      hqR.trans ((pow_one _).symm.le.trans (pow_le_pow_right₀ (by linarith) hi1))
    have hQ0 : (0 : ℝ) < ((Ideal.absNorm p : ℕ) : ℝ) ^ i := by linarith
    have hx : ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ)) = (((Ideal.absNorm p : ℕ) : ℝ) ^ i)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have hx0 : 0 < ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ)) := by
      rw [hx]
      exact inv_pos.mpr hQ0
    have hmul : ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ)) * ((Ideal.absNorm p : ℕ) : ℝ) ^ i = 1 := by
      rw [hx]
      exact inv_mul_cancel₀ hQ0.ne'
    have hxh : ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ)) ≤ 1 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hQ hx0.le]
    have habs : |((eta₃ D.host.F D.host.E p : ℤ) : ℝ) ^ i| = 1 := by
      rcases hη with hη | hη <;> rw [hη] <;> simp
    have hb : |((eta₃ D.host.F D.host.E p : ℤ) : ℝ) ^ i * ((Ideal.absNorm p : ℕ) : ℝ) ^ (-(i : ℤ))| ≤ 1 / 2 := by
      rw [abs_mul, habs, one_mul, abs_of_pos hx0]
      exact hxh
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    constructor <;> linarith
  have hcard : (Finset.Icc (j - eP h M p + 1) j).card ≤ e := by
    rw [Nat.card_Icc]
    have := eP_le D h M e he p hp
    omega
  unfold thP
  refine ⟨Finset.prod_pos fun i hi => (hfac i hi).1, ?_⟩
  calc _ ≤ ∏ _i ∈ Finset.Icc (j - eP h M p + 1) j, (2 : ℝ) :=
        Finset.prod_le_prod (fun i hi => (hfac i hi).1.le) (fun i hi => (hfac i hi).2)
    _ = (2 : ℝ) ^ (Finset.Icc (j - eP h M p + 1) j).card := Finset.prod_const _
    _ ≤ (2 : ℝ) ^ e := pow_le_pow_right₀ (by norm_num) hcard

def Lem3Rest (D : D7) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [FiniteDimensional D.host.E V]
    [Module (𝓞 D.host.E) V] [IsScalarTower (𝓞 D.host.E) D.host.E V]
    (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E), h.IsSymm → IsPosDef h →
    ∀ M : Submodule (𝓞 D.host.E) V, Submodule.IsLattice D.host.E M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ de : ℕ, Formalism.MainNotions.S.Lat.latDetH h M = de → ∀ e : ℕ, DiscGen h M e →
      Formalism.HermitianLatticesTheory.mass h M * levelIdx h M de =
        massU D.host.E (finrank D.host.E V) * (de : ℝ) ^ (finrank D.host.E V) *
          ∏ᶠ p : PrimesOver D.host.F de,
            thP (finrank D.host.E V) (eP h M p.1) (eta₃ D.host.F D.host.E p.1) (Ideal.absNorm p.1) ∧
      Formalism.HermitianLatticesTheory.mass h M ≤ massU D.host.E (finrank D.host.E V) * (de : ℝ) ^ (finrank D.host.E V) *
        (2 : ℝ) ^ (e * omegaF D.host.F de)

/- English proof (translation)
Introduce `V _ _ _ _ _ h hs hpd M hL hI de hde e he`. Take `⟨h1, h3⟩` from `hR V h hs hpd M hL hI de hde e he`. Conclude with `⟨h1, fun p hp => (local_theta_factor_pos_le D h M e he _ p hp).2, h3⟩`.
-/
theorem lattice_lemma_of_remaining_clauses (D : D7) (hR : Lem3Rest D) : VanishingOnXAndXPlusMass.Conclusion2 D := by
  intro V _ _ _ _ _ h hs hpd M hL hI de hde e he
  obtain ⟨h1, h3⟩ := hR V h hs hpd M hL hI de hde e he
  exact ⟨h1, fun p hp => (local_theta_factor_pos_le D h M e he _ p hp).2, h3⟩

/- English proof (translation)
Unfold `Formalism.MainNotions.S.Lat.latDetH`. Apply `Real.sqrt_pos.mpr` to reduce the goal to its premises. Unfold `Formalism.MainNotions.S.Lat.genIdxH`. Use `finprod_induction (fun x : ℝ => 0 < x) one_pos (fun x y hx hy => mul_pos hx hy) ?_` and prove the remaining obligations. Introduce `P`.

Establish `h0 : Ideal.absNorm P.asIdeal ≠ 0` using `fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)`. Establish `h1 : (0 : ℝ) < ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero h0`. Use `first`. Consider the case `exact pow_pos h1 _`. Consider the case `exact zpow_pos h1 _`.
-/
theorem latDetH_pos (D : D7) {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
    (M : Submodule (𝓞 D.host.E) V) : 0 < Formalism.MainNotions.S.Lat.latDetH h M := by
  unfold Formalism.MainNotions.S.Lat.latDetH
  apply Real.sqrt_pos.mpr
  unfold Formalism.MainNotions.S.Lat.genIdxH
  refine finprod_induction (fun x : ℝ => 0 < x) one_pos (fun x y hx hy => mul_pos hx hy) ?_
  intro P
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
  have h1 : (0 : ℝ) < ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
  first
    | exact pow_pos h1 _
    | exact zpow_pos h1 _

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.mass`. Apply the tactic sequence `split_ifs <;> positivity`.
-/
theorem herm_mass_nonneg (D : D7) {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
    (M : Submodule (𝓞 D.host.E) V) : 0 ≤ Formalism.HermitianLatticesTheory.mass h M := by
  unfold Formalism.HermitianLatticesTheory.mass
  split_ifs <;> positivity

/- English proof (translation)
Use `set I : Ideal (𝓞 K) := Ideal.span {((de : ℕ) : 𝓞 K)} with hIdef`. Establish `hI0 : I ≠ ⊥`. Rewrite using `[hIdef, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `(by omega : de ≠ 0)` after adjusting the coercions. Establish `hN : Nat.card (𝓞 K ⧸ I) ≠ 0`.

Rewrite using `[← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]`. Conclude with `fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h)`. Use `haveI : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero hN`. Use `haveI : Finite (Ideal (𝓞 K ⧸ I)) := Finite.of_injective (fun J : Ideal (𝓞 K ⧸ I) => (J : Set (𝓞 K ⧸ I))) SetLike.coe_injective`. Use `Finite.of_injective (fun p : PrimesOver K de => p.1.map (Ideal.Quotient.mk I)) ?_` and prove the remaining obligations.

Introduce `p q hpq`. Establish `hp : I ≤ p.1` using `(Ideal.span_singleton_le_iff_mem _).mpr p.2.2`. Establish `hq : I ≤ q.1` using `(Ideal.span_singleton_le_iff_mem _).mpr q.2.2`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hc` using `congrArg (Ideal.comap (Ideal.Quotient.mk I)) hpq`.

Rewrite `hc` using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hp, sup_eq_left.mpr hq]`. Conclude with `hc`.
-/
theorem finite_primesOver (K : Type) [Field K] [NumberField K] (de : ℕ) (hde : 1 ≤ de) : Finite (PrimesOver K de) := by
  set I : Ideal (𝓞 K) := Ideal.span {((de : ℕ) : 𝓞 K)} with hIdef
  have hI0 : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (by omega : de ≠ 0)
  have hN : Nat.card (𝓞 K ⧸ I) ≠ 0 := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h)
  haveI : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero hN
  haveI : Finite (Ideal (𝓞 K ⧸ I)) :=
    Finite.of_injective (fun J : Ideal (𝓞 K ⧸ I) => (J : Set (𝓞 K ⧸ I))) SetLike.coe_injective
  refine Finite.of_injective (fun p : PrimesOver K de => p.1.map (Ideal.Quotient.mk I)) ?_
  intro p q hpq
  have hp : I ≤ p.1 := (Ideal.span_singleton_le_iff_mem _).mpr p.2.2
  have hq : I ≤ q.1 := (Ideal.span_singleton_le_iff_mem _).mpr q.2.2
  apply Subtype.ext
  have hc := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hpq
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hp, sup_eq_left.mpr hq] at hc
  exact hc

def Lem3Mass (D : D7) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [FiniteDimensional D.host.E V]
    [Module (𝓞 D.host.E) V] [IsScalarTower (𝓞 D.host.E) D.host.E V]
    (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E), h.IsSymm → IsPosDef h →
    ∀ M : Submodule (𝓞 D.host.E) V, Submodule.IsLattice D.host.E M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ de : ℕ, Formalism.MainNotions.S.Lat.latDetH h M = de → ∀ e : ℕ, DiscGen h M e →
      Formalism.HermitianLatticesTheory.mass h M * levelIdx h M de =
        massU D.host.E (finrank D.host.E V) * (de : ℝ) ^ (finrank D.host.E V) *
          ∏ᶠ p : PrimesOver D.host.F de,
            thP (finrank D.host.E V) (eP h M p.1) (eta₃ D.host.F D.host.E p.1) (Ideal.absNorm p.1)

/- English proof (translation)
Establish `hL : L ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0, Nat.cast_zero, mul_zero]`. Combine the linear relations using `[mul_pos hA hP]`. Establish `hL1 : (1 : ℝ) ≤ L` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hL`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mass_bound_lemma (m A P B : ℝ) (L : ℕ) (hm : 0 ≤ m) (hA : 0 < A) (hP : 0 < P) (hPB : P ≤ B)
    (h : m * L = A * P) : m ≤ A * B := by
  have hL : L ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, mul_zero] at h
    linarith [mul_pos hA hP]
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hL
  calc m ≤ m * L := le_mul_of_one_le_right hm hL1
    _ = A * P := h
    _ ≤ A * B := mul_le_mul_of_nonneg_left hPB hA.le

/- English proof (translation)
Use `⟨Finset.prod_pos fun i _ => (hf i).1, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem prod_bound_lemma_2 {ι : Type} [Fintype ι] (f : ι → ℝ) (c : ℝ) (hf : ∀ i, 0 < f i ∧ f i ≤ c) :
    0 < ∏ i, f i ∧ ∏ i, f i ≤ c ^ Fintype.card ι := by
  refine ⟨Finset.prod_pos fun i _ => (hf i).1, ?_⟩
  calc ∏ i, f i ≤ ∏ _i : ι, c := Finset.prod_le_prod (fun i _ => (hf i).1.le) (fun i _ => (hf i).2)
    _ = c ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]

/- English proof (translation)
Use `lattice_lemma_of_remaining_clauses D ?_` and prove the remaining obligations. Introduce `V _ _ _ _ _ h hs hpd M hL hI de hde e he`. Establish `hform` using `hR V h hs hpd M hL hI de hde e he`. Use `⟨hform, ?_⟩` and prove the remaining obligations. Establish `hde0 : (0 : ℝ) < de` using `by rw [← hde]; exact latDetH_pos D h M`.

Establish `hde1 : 1 ≤ de` using `Nat.cast_pos.mp hde0`. Use `haveI : Finite (PrimesOver D.host.F de) := finite_primesOver D.host.F de hde1`. Use `letI : Fintype (PrimesOver D.host.F de) := Fintype.ofFinite _`. Establish `hf2` using `hform`. Rewrite `hf2` using `[finprod_eq_prod_of_fintype]`.

Take `⟨hP, hPB⟩` from `prod_bound_lemma_2 _ ((2 : ℝ) ^ e) (fun p : PrimesOver D.host.F de => local_theta_factor_pos_le D h M e he (finrank D.host.E V) p.1 p.2.1)`. Establish `hA : 0 < massU D.host.E (finrank D.host.E V)` using `massS_pos D (finrank D.host.E V)`. Establish `hc : (2 : ℝ) ^ (e * omegaF D.host.F de) = ((2 : ℝ) ^ e) ^ Fintype.card (PrimesOver D.host.F de)`. Rewrite using `[pow_mul]`. Use `congr 1`.

Conclude with `Nat.card_eq_fintype_card`. Rewrite using `[hc]`. Conclude with `mass_bound_lemma _ _ _ _ _ (herm_mass_nonneg D h M) (mul_pos hA (pow_pos hde0 _)) hP hPB hf2`.
-/
theorem lattice_lemma_of_mass_formula (D : D7) (hR : Lem3Mass D) : VanishingOnXAndXPlusMass.Conclusion2 D := by
  refine lattice_lemma_of_remaining_clauses D ?_
  intro V _ _ _ _ _ h hs hpd M hL hI de hde e he
  have hform := hR V h hs hpd M hL hI de hde e he
  refine ⟨hform, ?_⟩
  have hde0 : (0 : ℝ) < de := by rw [← hde]; exact latDetH_pos D h M
  have hde1 : 1 ≤ de := Nat.cast_pos.mp hde0
  haveI : Finite (PrimesOver D.host.F de) := finite_primesOver D.host.F de hde1
  letI : Fintype (PrimesOver D.host.F de) := Fintype.ofFinite _
  have hf2 := hform
  rw [finprod_eq_prod_of_fintype] at hf2
  obtain ⟨hP, hPB⟩ := prod_bound_lemma_2 _ ((2 : ℝ) ^ e)
    (fun p : PrimesOver D.host.F de => local_theta_factor_pos_le D h M e he (finrank D.host.E V) p.1 p.2.1)
  have hA : 0 < massU D.host.E (finrank D.host.E V) := massS_pos D (finrank D.host.E V)
  have hc : (2 : ℝ) ^ (e * omegaF D.host.F de) = ((2 : ℝ) ^ e) ^ Fintype.card (PrimesOver D.host.F de) := by
    rw [pow_mul]
    congr 1
    exact Nat.card_eq_fintype_card
  rw [hc]
  exact mass_bound_lemma _ _ _ _ _ (herm_mass_nonneg D h M) (mul_pos hA (pow_pos hde0 _)) hP hPB hf2

/- English proof (translation)
Introduce `x i` and use `lattice_lemma_of_mass_formula _ (hR x i)`.
-/
theorem family_lattice_lemma_of_mass_formula {eps : ℝ} (Fm : FamP eps) (hR : ∀ x (i : Fm.Ix x), Lem3Mass (Fm.D x i)) : VanishingOnXAndXPlusMass.Conclusion2Family Fm :=
  fun x i => lattice_lemma_of_mass_formula _ (hR x i)

end Formalism.MainNotions.BridgeLemma

end

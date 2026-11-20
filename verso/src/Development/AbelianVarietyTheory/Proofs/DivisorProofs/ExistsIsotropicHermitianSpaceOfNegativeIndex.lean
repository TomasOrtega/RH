import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicOfIndefinite
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeFromConjugateComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryPosDefHermitianSameRank
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLeOfDiag

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoNegIdx

open ReciprocityTheory.ChartRestriction.G GlobalTheory.Inertia

/- English proof (translation)
Take `⟨e, P, hP⟩` from `h`. Use `set A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix _ _ ℂ).map (starRingEnd ℂ) with hA`. Establish `hAc : A.map (starRingEnd ℂ) = (P : Matrix _ _ ℂ)`. Use extensionality with `i j`. Simplify using `[hA]`.

Establish `hdet : A.det ≠ 0`. Establish `hu` using `Matrix.isUnits_det_units P`. Establish `h2` using `RingHom.map_det (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)`. Rewrite `h2` using `[RingHom.mapMatrix_apply]`. Rewrite using `[hA, ← h2]`.

Conclude with `(map_ne_zero _).2 hu.ne_zero`. Establish `hc : A.transpose * M.reindex e e * A.map (starRingEnd ℂ) = Formalism.UG.Jpq p q`. Rewrite using `[hAc, ← hP]`. Both sides reduce to the same expression. Establish `hcn : A.transpose * (-M).reindex e e * A.map (starRingEnd ℂ) = -Formalism.UG.Jpq p q`.

Rewrite using `[← hc]`. Establish `: (-M).reindex e e = -(M.reindex e e)` using `by ext; simp`. Rewrite using `[this, Matrix.mul_neg, Matrix.neg_mul]`. Establish `hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1))`. Use extensionality with `i j`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Apply the tactic sequence `simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp`. Establish `hJn : -Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (-1 : ℂ)) (fun _ => 1))`. Rewrite using `[hJ, Matrix.diagonal_neg]`. Use `congr 1`.

Apply the tactic sequence `ext i; rcases i with i | i <;> simp`. Establish `hre : ∀ N : Matrix n n ℂ, posIndex N = posIndex (N.reindex e e)` using `fun N => (posIndex_submatrix_equiv N e.symm).symm`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hre, ← posIndex_congr _ hdet, hc, hJ, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]`. Simplify using the standard rewrite rules.

Rewrite using `[hre, ← posIndex_congr _ hdet, hcn, hJn, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]`. Simplify using the standard rewrite rules.
-/
theorem posIndex_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature M p q) : posIndex M = p ∧ posIndex (-M) = q := by
  obtain ⟨e, P, hP⟩ := h
  set A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix _ _ ℂ).map (starRingEnd ℂ) with hA
  have hAc : A.map (starRingEnd ℂ) = (P : Matrix _ _ ℂ) := by
    ext i j; simp [hA]
  have hdet : A.det ≠ 0 := by
    have hu := Matrix.isUnits_det_units P
    have h2 := RingHom.map_det (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    rw [RingHom.mapMatrix_apply] at h2
    rw [hA, ← h2]
    exact (map_ne_zero _).2 hu.ne_zero
  have hc : A.transpose * M.reindex e e * A.map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    rw [hAc, ← hP]; rfl
  have hcn : A.transpose * (-M).reindex e e * A.map (starRingEnd ℂ) = -Formalism.UG.Jpq p q := by
    rw [← hc]
    have : (-M).reindex e e = -(M.reindex e e) := by ext; simp
    rw [this, Matrix.mul_neg, Matrix.neg_mul]
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp
  have hJn : -Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (-1 : ℂ)) (fun _ => 1)) := by
    rw [hJ, Matrix.diagonal_neg]
    congr 1
    ext i; rcases i with i | i <;> simp
  have hre : ∀ N : Matrix n n ℂ, posIndex N = posIndex (N.reindex e e) := fun N =>
    (posIndex_submatrix_equiv N e.symm).symm
  constructor
  · rw [hre, ← posIndex_congr _ hdet, hc, hJ, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]
    simp
  · rw [hre, ← posIndex_congr _ hdet, hcn, hJn, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]
    simp

/- English proof (translation)
Rewrite using `[Module.Basis.equivFun_symm_apply]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hT_coords {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (u : Fin S.rank → E) :
    S.hT (S.frame.equivFun.symm u) (S.frame.equivFun.symm u) = ∑ b, ∑ a, star (u a) * S.gram a b * u b := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [starRingEnd_apply]
  ring

end GlobalTheory.IsoNegIdx

namespace GlobalTheory.IsoNegIdx

open ReciprocityTheory.ChartRestriction.G GlobalTheory.Inertia

/- English proof (translation)
Introduce `D S k hS hk1 hk2 hn`. Use `letI : IsCMField D.host.E := D.host.isCMField_hostE`. Establish `hst : ∀ x : D.host.E, star x = FD.cc x` using `fun _ => rfl`. Establish `hsig : ∀ φ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S.gram.map φ) (S.rank - k) k`. Introduce `φ`.

Take `⟨ρ, h | h⟩` from `GlobalTheory.MassLink.tauE_or' D φ`. Substitute `h` using the available equality. Simplify `hS ρ` using `[gramAt]`. Establish `h1` using `GlobalTheory.BottomIsom.hasSignature_map_star (by simpa [gramAt] using hS ρ)`. Rewrite `h1` using `[Matrix.map_map]`.

Establish `e : (⇑(starRingEnd ℂ) ∘ ⇑(tauE D ρ)) = ⇑φ`. Use function extensionality and compare the values at `x`. Rewrite using `[Function.comp_apply, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis. Use `set G : Matrix (Fin S.rank) (Fin S.rank) D.host.E := S.gram.transpose with hGdef`.

Establish `hG : ∀ a b, FD.cc (G a b) = G b a` using `fun a b => by`. Simplify using `only [hGdef, Matrix.transpose_apply, ← hst]`. Conclude with `S.herm.eq _ _`. Establish `hform : ∀ u, S.hT (S.frame.equivFun.symm u) (S.frame.equivFun.symm u) = FD.herm G u u` using `fun u => by`. Rewrite using `[hT_coords, FD.herm]`.

Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [hGdef, Matrix.transpose_apply, hst]`. Expand and normalize the polynomial expressions, which then agree. Establish `hGφ : ∀ φ : D.host.E →+* ℂ, G.map φ = S.gram.map (ComplexEmbedding.conjugate φ)` using `fun φ => by`. Use extensionality with `a b`.

Simplify using `only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq]`. Rewrite using `[← hG b a, GlobalTheory.Published.embedding_cc]`. Both sides reduce to the same expression. Take `⟨P, d, hP, hPd, hd, -⟩` from `GlobalTheory.HermDiag.exists_congr_diagonal_herm hG`. Establish `key : ∀ u, FD.herm G (P.mulVec u) (P.mulVec u) = FD.herm (Matrix.diagonal d) u u` using `fun u => by`.

Rewrite using `[GlobalTheory.Published.LandherrSt.herm_mulVec, hPd]`. Establish `hne : ∀ u, u ≠ 0 → S.frame.equivFun.symm (P.mulVec u) ≠ 0` using `fun u hu h => by`. Apply `hu` to reduce the goal to its premises. Apply `Matrix.eq_zero_of_mulVec_eq_zero hP` to reduce the goal to its premises. Establish `h3` using `congrArg S.frame.equivFun h`.

Rewrite `h3` using `[LinearEquiv.apply_symm_apply, map_zero]`. Then use the resulting hypothesis. Distinguish the cases in `hz : ∃ i, d i = 0`. Take `⟨i, hi⟩` from `hz`. Use `⟨_, hne (Pi.single i 1) (by simp), ?_⟩` and prove the remaining obligations. Rewrite using `[hform, key, GlobalTheory.UTrans.herm_diagonal_self]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[hi]`. Simplify using `[Pi.single_apply, hj]`.

Use `push_neg at hz`. Establish `hs : ∀ φ : D.host.E →+* ℂ, (∃ i, 0 < (φ (d i)).re) ∧ ∃ j, (φ (d j)).re < 0`. Introduce `φ`. Establish `hc : (P.map φ).transpose * G.map φ * (P.map φ).map (starRingEnd ℂ) = Matrix.diagonal fun i => φ (d i)`. Establish `h1 : (P.map φ).map (starRingEnd ℂ) = (P.map FD.cc).map φ`.

Use extensionality with `a b`. Simplify using `[GlobalTheory.Published.embedding_cc]`. Rewrite using `[h1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hPd, Matrix.diagonal_map (map_zero φ)]`. Establish `hdet : (P.map φ).det ≠ 0`. Establish `h2` using `RingHom.map_det φ P`.

Rewrite `h2` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← h2]`. Conclude with `(map_ne_zero φ).2 hP`. Take `⟨hp, hq⟩` from `posIndex_of_hasSignature (hGφ φ ▸ hsig (ComplexEmbedding.conjugate φ))`. Establish `hcn : (P.map φ).transpose * (-G.map φ) * (P.map φ).map (starRingEnd ℂ) = Matrix.diagonal fun i => -φ (d i)`.

Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, hc, Matrix.diagonal_neg]`. Rewrite `hp` using `[← posIndex_congr _ hdet, hc, posIndex_diagonal]`. Rewrite `hq` using `[← posIndex_congr _ hdet, hcn, posIndex_diagonal]`. Prove the components needed by the constructor for the conclusion. Take `⟨i, hi⟩` from `Finset.card_pos.1 (show 0 < _ by rw [hp]; omega)`.

Conclude with `⟨i, (Finset.mem_filter.1 hi).2⟩`. Take `⟨i, hi⟩` from `Finset.card_pos.1 (show 0 < _ by rw [hq]; omega)`. Use `⟨i, ?_⟩` and prove the remaining obligations. Use `(Finset.mem_filter.1 hi).2` as an intermediate fact. Simplify using `only [Complex.neg_re] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨z, hz0, hzz⟩` from `GlobalTheory.UTrans.exists_isotropic_diagonal hn hd hz hs`. Conclude with `⟨_, hne z hz0, by rw [hform, key, hzz]⟩`.
-/
theorem exists_isotropic_of_negIdx : ∀ (D : D7) (S : HSp D) (k : ℕ), NegIdx S k → 1 ≤ k → k + 1 ≤ S.rank → 3 ≤ S.rank →
    ∃ x : S.V, x ≠ 0 ∧ S.hT x x = 0 := by
  intro D S k hS hk1 hk2 hn
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, star x = FD.cc x := fun _ => rfl

  have hsig : ∀ φ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S.gram.map φ) (S.rank - k) k := by
    intro φ
    obtain ⟨ρ, h | h⟩ := GlobalTheory.MassLink.tauE_or' D φ
    · subst h
      simpa [gramAt] using hS ρ
    · have h1 := GlobalTheory.BottomIsom.hasSignature_map_star (by simpa [gramAt] using hS ρ)
      rw [Matrix.map_map] at h1
      have e : (⇑(starRingEnd ℂ) ∘ ⇑(tauE D ρ)) = ⇑φ := by
        funext x
        rw [Function.comp_apply, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
      rwa [e] at h1

  set G : Matrix (Fin S.rank) (Fin S.rank) D.host.E := S.gram.transpose with hGdef
  have hG : ∀ a b, FD.cc (G a b) = G b a := fun a b => by
    simp only [hGdef, Matrix.transpose_apply, ← hst]
    exact S.herm.eq _ _
  have hform : ∀ u, S.hT (S.frame.equivFun.symm u) (S.frame.equivFun.symm u) = FD.herm G u u := fun u => by
    rw [hT_coords, FD.herm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [hGdef, Matrix.transpose_apply, hst]
    ring
  have hGφ : ∀ φ : D.host.E →+* ℂ, G.map φ = S.gram.map (ComplexEmbedding.conjugate φ) := fun φ => by
    ext a b
    simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq]
    rw [← hG b a, GlobalTheory.Published.embedding_cc]
    rfl
  obtain ⟨P, d, hP, hPd, hd, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  have key : ∀ u, FD.herm G (P.mulVec u) (P.mulVec u) = FD.herm (Matrix.diagonal d) u u := fun u => by
    rw [GlobalTheory.Published.LandherrSt.herm_mulVec, hPd]
  have hne : ∀ u, u ≠ 0 → S.frame.equivFun.symm (P.mulVec u) ≠ 0 := fun u hu h => by
    apply hu
    apply Matrix.eq_zero_of_mulVec_eq_zero hP
    have h3 := congrArg S.frame.equivFun h
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h3
  by_cases hz : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨_, hne (Pi.single i 1) (by simp), ?_⟩
    rw [hform, key, GlobalTheory.UTrans.herm_diagonal_self]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [Pi.single_apply, hj]
  push_neg at hz

  have hs : ∀ φ : D.host.E →+* ℂ, (∃ i, 0 < (φ (d i)).re) ∧ ∃ j, (φ (d j)).re < 0 := by
    intro φ
    have hc : (P.map φ).transpose * G.map φ * (P.map φ).map (starRingEnd ℂ) = Matrix.diagonal fun i => φ (d i) := by
      have h1 : (P.map φ).map (starRingEnd ℂ) = (P.map FD.cc).map φ := by
        ext a b
        simp [GlobalTheory.Published.embedding_cc]
      rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hPd, Matrix.diagonal_map (map_zero φ)]
    have hdet : (P.map φ).det ≠ 0 := by
      have h2 := RingHom.map_det φ P
      rw [RingHom.mapMatrix_apply] at h2
      rw [← h2]
      exact (map_ne_zero φ).2 hP
    obtain ⟨hp, hq⟩ := posIndex_of_hasSignature (hGφ φ ▸ hsig (ComplexEmbedding.conjugate φ))
    have hcn : (P.map φ).transpose * (-G.map φ) * (P.map φ).map (starRingEnd ℂ) =
        Matrix.diagonal fun i => -φ (d i) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hc, Matrix.diagonal_neg]
    rw [← posIndex_congr _ hdet, hc, posIndex_diagonal] at hp
    rw [← posIndex_congr _ hdet, hcn, posIndex_diagonal] at hq
    constructor
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < _ by rw [hp]; omega)
      exact ⟨i, (Finset.mem_filter.1 hi).2⟩
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < _ by rw [hq]; omega)
      refine ⟨i, ?_⟩
      have := (Finset.mem_filter.1 hi).2
      simp only [Complex.neg_re] at this
      linarith
  obtain ⟨z, hz0, hzz⟩ := GlobalTheory.UTrans.exists_isotropic_diagonal hn hd hz hs
  exact ⟨_, hne z hz0, by rw [hform, key, hzz]⟩

end GlobalTheory.IsoNegIdx

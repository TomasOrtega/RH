import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorSemilocalOfCyclicVectorFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorGeneratedAlgebraStructureStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartTensorBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartEtaleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorCommutantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorInvolutionAdjointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleCentralizerPointsOfCommutantAdjStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleTensorQuadraticSplitAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFactorIdempotentsExistStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusOfIdempotentFamilyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusLaurentPolynomialPointsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LaurentPolynomialCharacterIsMonomialStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateFactorPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerSplitRankUpperBoundStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFieldsBaseChangeIsFieldIffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupCommutantScalarsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NontrivialSplitSubtorusNotCentralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReducedFreeAlgebraTraceFormPerfectStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianTraceFormOfTraceFormPerfectStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneSmallMultiplesByCocompactSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProofStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FieldAdelicUnitTranslateBoundedOfSmallMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneBoundedOfUnitBoundedOfAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitTranslateBoundedOfFactorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentraliserPointsBoundedOfNormOneBoundedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientCompactOfBoundedMatricesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetRestrictRangeIdempotentMatrixStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientNotCompactOfSplitIdempotentStatement

noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

section Clauses

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E}

/- English proof (translation)
Establish `hJ` using `h.nondeg`. Establish `: Module.Finite F E` using `quad_finite h.quad`. Establish `: IsArtinianRing E` using `isArtinian_of_tower F inferInstance`. Take `⟨v, hv⟩` from `h1 E n (γ : Matrix n n E) h.sep`. Take `⟨⟨e, he⟩, ⟨b⟩, hbij⟩` from `h2 E n (γ : Matrix n n E) v hv`.

Establish `hinv : adj (σ : E →+* E) J (γ : Matrix n n E) = ((γ⁻¹ : GL n E) : Matrix n n E)` using `adj_eq_inv _ hJ h.mem`. Unfold `ClauseAlg`. Use `⟨⟨e, he⟩, ?_, ⟨b⟩, ⟨v, hbij⟩, ?_, hinv, fun x => adj_algebraMap _ hJ x⟩` and prove the remaining obligations. Establish `: Algebra.Etale E (AdjoinRoot (γ : Matrix n n E).charpoly)`. Apply `etale_adjoinRoot_of_isUnit_derivative (Matrix.charpoly_monic _)` to reduce the goal to its premises.

Take `⟨a, c, hac⟩` from `h.sep`. Establish `h'` using `congrArg (AdjoinRoot.mk (γ : Matrix n n E).charpoly) hac`. Simplify using `only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at h'`. Conclude with `isUnit_iff_exists_inv.2 ⟨_, (mul_comm _ _).trans h'⟩`. Conclude with `Algebra.Etale.of_equiv e`.

Introduce `l hl`. Apply `mem_genAlg_of_commute hbij` to reduce the goal to its premises. Establish `hl' : (γ : Matrix n n E) * l = l * (γ : Matrix n n E)` using `commute_of_mem_genAlg rfl hl`. Establish `key : adj (σ : E →+* E) J l * adj (σ : E →+* E) J (γ : Matrix n n E) = adj (σ : E →+* E) J (γ : Matrix n n E) * adj (σ : E →+* E) J l`. Rewrite using `[← adj_mul _ hJ, ← adj_mul _ hJ, hl']`.

Rewrite `key` using `[hinv]`. Use `set A := adj (σ : E →+* E) J l`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.mul_inv, one_mul]`. Use `_ = (γ : Matrix n n E) * (((γ⁻¹ : GL n E) : Matrix n n E) * A) * (γ : Matrix n n E) := by`.

Simplify using `only [mul_assoc]`. Use `_ = (γ : Matrix n n E) * (A * ((γ⁻¹ : GL n E) : Matrix n n E)) * (γ : Matrix n n E) := by`. Rewrite using `[key]`. Use `_ = (γ : Matrix n n E) * A * (((γ⁻¹ : GL n E) : Matrix n n E) * (γ : Matrix n n E)) := by`. Simplify using `only [mul_assoc]`.

Use `_ = (γ : Matrix n n E) * A := by rw [Units.inv_mul, mul_one]`.
-/
theorem clauseAlg (h1 : CyclicSemilocal) (h2 : CyclicAlgebra) (h : IsRegular σ J γ) :
    ClauseAlg σ J γ := by
  have hJ := h.nondeg
  have : Module.Finite F E := quad_finite h.quad
  have : IsArtinianRing E := isArtinian_of_tower F inferInstance
  obtain ⟨v, hv⟩ := h1 E n (γ : Matrix n n E) h.sep
  obtain ⟨⟨e, he⟩, ⟨b⟩, hbij⟩ := h2 E n (γ : Matrix n n E) v hv
  have hinv : adj (σ : E →+* E) J (γ : Matrix n n E) = ((γ⁻¹ : GL n E) : Matrix n n E) :=
    adj_eq_inv _ hJ h.mem
  unfold ClauseAlg
  refine ⟨⟨e, he⟩, ?_, ⟨b⟩, ⟨v, hbij⟩, ?_, hinv, fun x => adj_algebraMap _ hJ x⟩
  ·
    have : Algebra.Etale E (AdjoinRoot (γ : Matrix n n E).charpoly) := by
      apply etale_adjoinRoot_of_isUnit_derivative (Matrix.charpoly_monic _)
      obtain ⟨a, c, hac⟩ := h.sep
      have h' := congrArg (AdjoinRoot.mk (γ : Matrix n n E).charpoly) hac
      simp only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at h'
      exact isUnit_iff_exists_inv.2 ⟨_, (mul_comm _ _).trans h'⟩
    exact Algebra.Etale.of_equiv e
  ·
    intro l hl
    apply mem_genAlg_of_commute hbij
    have hl' : (γ : Matrix n n E) * l = l * (γ : Matrix n n E) := commute_of_mem_genAlg rfl hl
    have key : adj (σ : E →+* E) J l * adj (σ : E →+* E) J (γ : Matrix n n E) =
        adj (σ : E →+* E) J (γ : Matrix n n E) * adj (σ : E →+* E) J l := by
      rw [← adj_mul _ hJ, ← adj_mul _ hJ, hl']
    rw [hinv] at key
    set A := adj (σ : E →+* E) J l
    calc A * (γ : Matrix n n E)
        = (γ : Matrix n n E) * ((γ⁻¹ : GL n E) : Matrix n n E) * A * (γ : Matrix n n E) := by
          rw [Units.mul_inv, one_mul]
      _ = (γ : Matrix n n E) * (((γ⁻¹ : GL n E) : Matrix n n E) * A) * (γ : Matrix n n E) := by
          simp only [mul_assoc]
      _ = (γ : Matrix n n E) * (A * ((γ⁻¹ : GL n E) : Matrix n n E)) * (γ : Matrix n n E) := by
          rw [key]
      _ = (γ : Matrix n n E) * A * (((γ⁻¹ : GL n E) : Matrix n n E) * (γ : Matrix n n E)) := by
          simp only [mul_assoc]
      _ = (γ : Matrix n n E) * A := by rw [Units.inv_mul, mul_one]

/- English proof (translation)
Take `⟨-, -, -, ⟨v, hv⟩, -⟩` from `hA`. Establish `hJ` using `h.nondeg`. Rewrite using `[centRat, Subgroup.mem_inf, mem_UJ_iff_mul_adj _ hJ, Subgroup.mem_centralizer_iff]`. Simplify using `only [Set.mem_singleton_iff, forall_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hu, hc⟩`. Use `⟨mem_genAlg_of_commute hv ?_, hu⟩` and prove the remaining obligations. Establish `hc'` using `congrArg Units.val hc`. Rewrite `hc'` using `[Units.val_mul, Units.val_mul]`. Conclude with `hc'.symm`.

Introduce and unpack `⟨hm, hu⟩`. Use `⟨hu, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul]`. Conclude with `commute_of_mem_genAlg rfl hm`.
-/
theorem centRat_iff (h : IsRegular σ J γ) (hA : ClauseAlg σ J γ) (g : GL n E) :
    g ∈ centRat σ J γ ↔ (g : Matrix n n E) ∈ genAlg (γ : Matrix n n E) ∧
      (g : Matrix n n E) * adj (σ : E →+* E) J (g : Matrix n n E) = 1 := by
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  have hJ := h.nondeg
  rw [centRat, Subgroup.mem_inf, mem_UJ_iff_mul_adj _ hJ, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨mem_genAlg_of_commute hv ?_, hu⟩
    have hc' := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul] at hc'
    exact hc'.symm
  · rintro ⟨hm, hu⟩
    refine ⟨hu, Units.ext ?_⟩
    rw [Units.val_mul, Units.val_mul]
    exact commute_of_mem_genAlg rfl hm

/- English proof (translation)
Use `hP` as an intermediate fact. Take `⟨I, hI, A, hA, hA', e, -⟩` from `(Algebra.FormallyEtale.iff_exists_algEquiv_prod (K := F) (A := P)).1 inferInstance`. Use `hI` as an intermediate fact. Set `c` to `Finite.equivFin I`. Conclude with `⟨Nat.card I, fun i => A (c.symm i), fun i => hA _, fun i => hA' _, ⟨e.trans (AlgEquiv.piCongrLeft F A c.symm).symm⟩⟩`.
-/
theorem exists_prod_fields (P : Type) [CommRing P] [Algebra F P] (hP : Algebra.Etale F P) :
    ∃ (k : ℕ) (K : Fin k → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)),
      Nonempty (P ≃ₐ[F] ∀ i, K i) := by
  have := hP
  obtain ⟨I, hI, A, hA, hA', e, -⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (K := F) (A := P)).1 inferInstance
  have := hI
  let c := Finite.equivFin I
  exact ⟨Nat.card I, fun i => A (c.symm i), fun i => hA _, fun i => hA' _,
    ⟨e.trans (AlgEquiv.piCongrLeft F A c.symm).symm⟩⟩

/- English proof (translation)
Take `⟨δ, hne, hid, hort, hconj⟩` from `h1 F E σ h.quad (plusAlg σ J (γ : Matrix n n E)) k K e`. Establish `hinj` using `hP.2.2.1`. Use `⟨fun i => ((plusTensor σ J (γ : Matrix n n E) (δ (q i)) : genAlg (γ : Matrix n n E)) : Matrix n n E), ?_⟩` and prove the remaining obligations. Unfold `IsIdemFamily`. Use `⟨fun i => (plusTensor σ J (γ : Matrix n n E) (δ (q i))).2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i hi`. Apply `hne (q i)` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `Subtype.ext hi`.

Introduce `i`. Conclude with `congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) * plusTensor σ J (γ : Matrix n n E) (δ (q i)) = plusTensor σ J (γ : Matrix n n E) (δ (q i)) by`. Rewrite using `[← map_mul, hid])`. Introduce `i j hij`. Conclude with `congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) * plusTensor σ J (γ : Matrix n n E) (δ (q j)) = 0 by`.

Rewrite using `[← map_mul, hort _ _ (hq.ne hij), map_zero])`. Introduce `i j`. Rewrite using `[← plusTensor_tConj h]`. Conclude with `congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) * plusTensor σ J (γ : Matrix n n E) (tConj _ σ (δ (q j))) = 0 by`. Rewrite using `[← map_mul, hconj, map_zero])`.
-/
theorem exists_idemFamily [CharZero F] (h1 : SplitIdempotents) (h : IsRegular σ J γ)
    (hP : ClausePlus σ J γ) (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)]
    (e : Nonempty (plusAlg σ J (γ : Matrix n n E) ≃ₐ[F] ∀ i, K i)) {ι : Type}
    (q : ι → {i : Fin k // ¬ IsField (K i ⊗[F] E)}) (hq : Function.Injective q) :
    ∃ ε : ι → Matrix n n E, IsIdemFamily σ J γ ε := by
  obtain ⟨δ, hne, hid, hort, hconj⟩ := h1 F E σ h.quad (plusAlg σ J (γ : Matrix n n E)) k K e
  have hinj := hP.2.2.1

  refine ⟨fun i => ((plusTensor σ J (γ : Matrix n n E) (δ (q i)) : genAlg (γ : Matrix n n E)) :
    Matrix n n E), ?_⟩
  unfold IsIdemFamily
  refine ⟨fun i => (plusTensor σ J (γ : Matrix n n E) (δ (q i))).2, ?_, ?_, ?_, ?_⟩
  · intro i hi
    apply hne (q i)
    apply hinj
    rw [map_zero]
    exact Subtype.ext hi
  · intro i
    exact congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) *
      plusTensor σ J (γ : Matrix n n E) (δ (q i)) = plusTensor σ J (γ : Matrix n n E) (δ (q i)) by
        rw [← map_mul, hid])
  · intro i j hij
    exact congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) *
      plusTensor σ J (γ : Matrix n n E) (δ (q j)) = 0 by
        rw [← map_mul, hort _ _ (hq.ne hij), map_zero])
  · intro i j
    rw [← plusTensor_tConj h]
    exact congrArg Subtype.val (show plusTensor σ J (γ : Matrix n n E) (δ (q i)) *
      plusTensor σ J (γ : Matrix n n E) (tConj _ σ (δ (q j))) = 0 by
        rw [← map_mul, hconj, map_zero])

/- English proof (translation)
Unfold `ClauseRank`. Use `⟨exists_prod_fields _ hP.1, ?_⟩` and prove the remaining obligations. Introduce `k K _ _ e`. Unfold `HasSplitRank`. Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Set `c` to `Finite.equivFin {i : Fin k // ¬ IsField (K i ⊗[F] E)}`. Take `⟨ε, hε⟩` from `exists_idemFamily h1 h hP k K e c.symm c.symm.injective`. Take `⟨A, -⟩` from `h2 F E n σ J γ h hA _ ε hε`. Conclude with `⟨A⟩`. Introduce and unpack `s ⟨A⟩`.

Conclude with `h3 F E n σ J γ h hP hC k K e s ⟨A⟩`. Introduce `hn`. Take `⟨b⟩` from `hP.2.1`. Take `⟨f⟩` from `e`. Assume the negation of the conclusion as `hk`.

Establish `hk0 : k = 0` using `by omega`. Substitute `hk0` using the available equality. Take `⟨i⟩` from `hn`. Apply `b.ne_zero i` to reduce the goal to its premises. Apply `f.injective` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Conclude with `j.elim0`. Use `quad_nontrivial h.quad` as an intermediate fact. Conclude with `((AlgEquiv.ofBijective _ hP.2.2).toMulEquiv.isField_congr.symm).trans (h4 F E _ k K e)`.
-/
theorem clauseRank [CharZero F] (h1 : SplitIdempotents) (h2 : SubtorusOfIdempotents)
    (h3 : SplitRankUpper) (h4 : TensorFieldIff) (h : IsRegular σ J γ) (hA : ClauseAlg σ J γ)
    (hP : ClausePlus σ J γ) (hC : PointsClause σ J γ) : ClauseRank σ J γ := by
  unfold ClauseRank
  refine ⟨exists_prod_fields _ hP.1, ?_⟩
  intro k K _ _ e
  unfold HasSplitRank
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  ·
    let c := Finite.equivFin {i : Fin k // ¬ IsField (K i ⊗[F] E)}
    obtain ⟨ε, hε⟩ := exists_idemFamily h1 h hP k K e c.symm c.symm.injective
    obtain ⟨A, -⟩ := h2 F E n σ J γ h hA _ ε hε
    exact ⟨A⟩
  · rintro s ⟨A⟩
    exact h3 F E n σ J γ h hP hC k K e s ⟨A⟩
  · intro hn
    obtain ⟨b⟩ := hP.2.1
    obtain ⟨f⟩ := e
    by_contra hk
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨i⟩ := hn
    apply b.ne_zero i
    apply f.injective
    funext j
    exact j.elim0
  · have := quad_nontrivial h.quad
    exact ((AlgEquiv.ofBijective _ hP.2.2).toMulEquiv.isField_congr.symm).trans (h4 F E _ k K e)

/- English proof (translation)
Introduce `a ha b hb`. Take `⟨-, -, hiff⟩` from `hC R`. Take `⟨u, -, hu⟩` from `(hiff a).1 ha`. Take `⟨w, -, hw⟩` from `(hiff b).1 hb`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, Units.val_mul, ← hu, ← hw, ← map_mul, ← map_mul, mul_comm (u : LPts σ J (γ : Matrix n n E) R)]`.
-/
theorem centPts_comm (hC : PointsClause σ J γ) (R : Type) [CommRing R] [Algebra F R] :
    ∀ a ∈ centPts σ J γ R, ∀ b ∈ centPts σ J γ R, a * b = b * a := by
  intro a ha b hb
  obtain ⟨-, -, hiff⟩ := hC R
  obtain ⟨u, -, hu⟩ := (hiff a).1 ha
  obtain ⟨w, -, hw⟩ := (hiff b).1 hb
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← hu, ← hw, ← map_mul, ← map_mul,
    mul_comm (u : LPts σ J (γ : Matrix n n E) R)]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul p e => simp [tConj, Algebra.TensorProduct.map_tmul, hσ]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem tConj_tConj (hσ : ∀ x, σ (σ x) = x) (P : Type) [CommRing P] [Algebra F P]
    (x : P ⊗[F] E) : tConj P σ (tConj P σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p e => simp [tConj, Algebra.TensorProduct.map_tmul, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

end Clauses

/- English proof (translation)
Unfold `RegularSemisimple RegularStructure RegularAdelic`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `F E _ _ _ _ n _ _ σ J γ h`. Establish `hA` using `clauseAlg a1 a2 h`. Establish `hP` using `a4 F E n σ J γ h hA (a3 F E n σ J γ h hA)`.

Establish `hC` using `a5 F E n σ J γ h hA hP`. Use `⟨hA, hP, ?_, clauseRank a7 a8 a9 a10 h hA hP hC, ?_, a12 F E n σ J γ h hA⟩` and prove the remaining obligations. Unfold `ClauseCent`. Use `⟨fun R _ _ => hC R, fun g => centRat_iff h hA g, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ _`.

Conclude with `a6 F E σ h.quad _ n hP.1 hP.2.1 Ω`. Unfold `ClauseProper`. Conclude with `⟨fun R _ _ => centPts_comm hC R, fun hE s hs A => a11 F E n σ J γ h hE s hs A⟩`. Introduce `F E _ _ _ _ n _ _ σ J γ h k K _ _ e`. Establish `hA` using `clauseAlg a1 a2 h`.

Establish `hP` using `a4 F E n σ J γ h hA (a3 F E n σ J γ h hA)`. Establish `hC` using `a5 F E n σ J γ h hA hP`. Prove the components needed by the constructor for the conclusion. Introduce `hc`. Assume the negation of the conclusion as `hne`.

Take `⟨i, hi⟩` from `not_forall.1 hne`. Take `⟨ε, hε⟩` from `exists_idemFamily a7 h hP k K e (ι := Fin 1) (fun _ => ⟨i, hi⟩) (fun a b _ => Subsingleton.elim a b)`. Take `⟨A, hAε⟩` from `a8 F E n σ J γ h hA 1 ε hε`. Take `⟨hmem, hne0, hidem, -, -⟩` from `hε`. Use `a18 F E n σ J γ h (ε 0) (hmem 0) (hne0 0) (hidem 0) ?_ hc` and prove the remaining obligations.

Introduce `t`. Conclude with `⟨A.hom (AdeleRing (𝓞 F) F) (fun _ => t), A.mem (AdeleRing (𝓞 F) F) (fun _ => t), hAε (AdeleRing (𝓞 F) F) (fun _ => t) 0⟩`. Introduce `hf`. Establish `: Module.Finite F E` using `quad_finite h.quad`. Take `⟨b⟩` from `hP.2.1`.

Establish `: Module.Finite F (plusAlg σ J (γ : Matrix n n E))` using `Module.Finite.of_basis b`. Take `⟨f⟩` from `e`. Establish `: ∀ i, Module.Finite F (K i)` using `fun i => Module.Finite.of_surjective ((Pi.evalAlgHom F K i).comp f.toAlgHom).toLinearMap (fun x => ⟨f.symm (Pi.single i x), by simp⟩)`. Establish `hU : ∀ i, UnitBounded F (K i ⊗[F] E) (tConj (K i) σ)` using `fun i => a13 F (K i ⊗[F] E) (tConj (K i) σ) (hf i) (tConj_tConj h.quad.invol (K i))`. Establish `hUP` using `a15 F E σ (plusAlg σ J (γ : Matrix n n E)) k K ⟨f⟩ hU`.

Establish `hN` using `a14 F _ _ hUP`. Conclude with `a17 F E n σ J γ h (a16 F E n σ J γ h hA hP hC hN)`.
-/
theorem regularSemisimple_of (a1 : CyclicSemilocal) (a2 : CyclicAlgebra) (a3 : PlusTensorBijective)
    (a4 : PlusEtale) (a5 : PointsCentraliser) (a6 : SplitClosed) (a7 : SplitIdempotents)
    (a8 : SubtorusOfIdempotents) (a9 : SplitRankUpper) (a10 : TensorFieldIff)
    (a11 : SubtorusNotCentral) (a12 : TraceClause) (a13 : FieldUnitBounded)
    (a14 : NormOfUnitBounded) (a15 : ProductUnitBounded) (a16 : MatOfNormBounded)
    (a17 : CompactOfMatBounded) (a18 : NotCompactOfIdempotent) : RegularSemisimple := by
  unfold RegularSemisimple RegularStructure RegularAdelic
  refine ⟨?_, ?_⟩
  · intro F E _ _ _ _ n _ _ σ J γ h
    have hA := clauseAlg a1 a2 h
    have hP := a4 F E n σ J γ h hA (a3 F E n σ J γ h hA)
    have hC := a5 F E n σ J γ h hA hP
    refine ⟨hA, hP, ?_, clauseRank a7 a8 a9 a10 h hA hP hC, ?_, a12 F E n σ J γ h hA⟩
    · unfold ClauseCent
      refine ⟨fun R _ _ => hC R, fun g => centRat_iff h hA g, ?_⟩
      intro Ω _ _ _
      exact a6 F E σ h.quad _ n hP.1 hP.2.1 Ω
    · unfold ClauseProper
      exact ⟨fun R _ _ => centPts_comm hC R, fun hE s hs A => a11 F E n σ J γ h hE s hs A⟩
  · intro F E _ _ _ _ n _ _ σ J γ h k K _ _ e
    have hA := clauseAlg a1 a2 h
    have hP := a4 F E n σ J γ h hA (a3 F E n σ J γ h hA)
    have hC := a5 F E n σ J γ h hA hP
    constructor
    ·
      intro hc
      by_contra hne
      obtain ⟨i, hi⟩ := not_forall.1 hne
      obtain ⟨ε, hε⟩ := exists_idemFamily a7 h hP k K e (ι := Fin 1) (fun _ => ⟨i, hi⟩)
        (fun a b _ => Subsingleton.elim a b)
      obtain ⟨A, hAε⟩ := a8 F E n σ J γ h hA 1 ε hε
      obtain ⟨hmem, hne0, hidem, -, -⟩ := hε
      refine a18 F E n σ J γ h (ε 0) (hmem 0) (hne0 0) (hidem 0) ?_ hc
      intro t
      exact ⟨A.hom (AdeleRing (𝓞 F) F) (fun _ => t), A.mem (AdeleRing (𝓞 F) F) (fun _ => t),
        hAε (AdeleRing (𝓞 F) F) (fun _ => t) 0⟩
    ·
      intro hf
      have : Module.Finite F E := quad_finite h.quad
      obtain ⟨b⟩ := hP.2.1
      have : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) := Module.Finite.of_basis b
      obtain ⟨f⟩ := e
      have : ∀ i, Module.Finite F (K i) := fun i =>
        Module.Finite.of_surjective ((Pi.evalAlgHom F K i).comp f.toAlgHom).toLinearMap
          (fun x => ⟨f.symm (Pi.single i x), by simp⟩)
      have hU : ∀ i, UnitBounded F (K i ⊗[F] E) (tConj (K i) σ) := fun i =>
        a13 F (K i ⊗[F] E) (tConj (K i) σ) (hf i) (tConj_tConj h.quad.invol (K i))
      have hUP := a15 F E σ (plusAlg σ J (γ : Matrix n n E)) k K ⟨f⟩ hU
      have hN := a14 F _ _ hUP
      exact a17 F E n σ J γ h (a16 F E n σ J γ h hA hP hC hN)

/- English proof (translation)
The claim follows from `regularSemisimple_of (GlobalTheory.T.cyclicVector_semilocal_of_cyclicVector_field GlobalTheory.T.cyclicVector_of_separable_charpoly_field) GlobalTheory.T.cyclicVector_generatedAlgebra_structure GlobalTheory.T.regularSemisimple_selfAdjointPart_tensor_bijective GlobalTheory.T.regul …`.
-/
theorem regularSemisimple : RegularSemisimple :=
  regularSemisimple_of (GlobalTheory.T.cyclicVector_semilocal_of_cyclicVector_field GlobalTheory.T.cyclicVector_of_separable_charpoly_field) GlobalTheory.T.cyclicVector_generatedAlgebra_structure GlobalTheory.T.regularSemisimple_selfAdjointPart_tensor_bijective GlobalTheory.T.regularSemisimple_selfAdjointPart_etale
    (GlobalTheory.T.regularSemisimple_centralizer_points_of_commutant_adjoint GlobalTheory.T.regularSemisimple_tensor_commutant GlobalTheory.T.regularSemisimple_tensor_involution_adjoint) GlobalTheory.T.etale_tensor_quadratic_split_algClosed GlobalTheory.T.split_factor_idempotents_exist GlobalTheory.T.split_subtorus_of_idempotent_family
    (GlobalTheory.T.centralizer_splitRank_upper_bound GlobalTheory.T.split_subtorus_laurentPolynomial_points GlobalTheory.T.laurentPolynomial_character_isMonomial GlobalTheory.T.conjugate_factor_points_separate) GlobalTheory.T.product_fields_baseChange_isField_iff
    (GlobalTheory.T.nontrivial_split_subtorus_not_central GlobalTheory.T.unitaryGroup_commutant_scalars GlobalTheory.T.split_subtorus_laurentPolynomial_points GlobalTheory.T.laurentPolynomial_character_isMonomial) (GlobalTheory.T.hermitianTraceForm_of_traceForm_perfect GlobalTheory.T.reduced_free_algebra_traceForm_perfect)
    (GlobalTheory.T.fieldAdelicUnitTranslateBounded_of_smallMultiples GlobalTheory.T.normOne_small_multiples_by_cocompact_subgroup GlobalTheory.T.finiteAlgebraAdelicLattice_proof) (GlobalTheory.T.normOfUnitBounded_of_tensorLattice' GlobalTheory.T.finiteAlgebraAdelicLattice_proof)
    (GlobalTheory.T.adelic_unit_translate_bounded_of_factors GlobalTheory.T.finiteAlgebraAdelicLattice_proof) GlobalTheory.T.centraliser_points_bounded_of_normOne_bounded (GlobalTheory.T.adelic_quotient_compact_of_bounded_matrices GlobalTheory.T.finiteAlgebraAdelicLattice_proof)
    (GlobalTheory.T.adelic_quotient_not_compact_of_split_idempotent GlobalTheory.T.det_restrict_range_idempotent_matrix)

end GlobalTheory.RegSS

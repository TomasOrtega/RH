import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatSmulMatrixMulVecCompletedSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHyperspecialStableLatticeEqMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceHyperspecialStableLatticeEqMultipleStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.LatMatch

section Abstract
variable {R : Type} [CommRing R] [Nontrivial R]

/- English proof (translation)
Set `e : (Fin b → R) ≃ₗ[R] (Fin a → R)` to `LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B) (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])`. Use `e.finrank_eq` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem card_eq_of_inv {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin a) R)
    (h1 : A * B = 1) (h2 : B * A = 1) : a = b := by
  let e : (Fin b → R) ≃ₗ[R] (Fin a → R) := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := e.finrank_eq
  simpa using this.symm

end Abstract

/- English proof (translation)
Use `haveI : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) := by`. Take `⟨P, hP⟩` from `Ideal.exists_maximal (𝓞 D.host.F)`. Conclude with `(Formalism.UG.evalV D.host.F ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩).toRingHom.domain_nontrivial`. Conclude with `(Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (B := D.host.E) (algebraMap D.host.F D.host.E).injective).nontrivial`.
-/
theorem nontrivial_R (D : D7) : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact (Formalism.UG.evalV D.host.F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩).toRingHom.domain_nontrivial
  exact (Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F)
    (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (B := D.host.E) (algebraMap D.host.F D.host.E).injective).nontrivial

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `D V V' n hF Q Q' hQ hQ' P e f hP`. Use `haveI := nontrivial_R D`. Take `⟨⟨β, β', hb1, hb2, hK⟩, hU⟩` from `hQ`. Take `⟨⟨γ, γ', hc1, hc2, hK'⟩, hU'⟩` from `hQ'`. Establish `hr : V.rank = n` using `card_eq_of_inv β β' hb1 hb2`.

Establish `hr' : V'.rank = n` using `card_eq_of_inv γ γ' hc1 hc2`. Use `⟨hr'.trans hr.symm, ?_⟩` and prove the remaining obligations. Set `X : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)` to `γ * β'`. Set `X' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)` to `β * γ'`. Establish `hX1 : X * X' = 1` using `by show γ * β' * (β * γ') = 1`.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc β' β γ', hb2, Matrix.one_mul, hc1]`. Establish `hX2 : X' * X = 1` using `by show β * γ' * (γ * β') = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc γ' γ β', hc2, Matrix.one_mul, hb1]`. Establish `hconj : ∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * X = X * finMat D.sp.cm.sig V.gram (Q.ψ κ)`. Introduce `κ`.

Rewrite using `[hK' κ, hK κ]`. Use `show _ * (γ * β') = γ * β' * _`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc γ' γ β', hc2, Matrix.one_mul, ← Matrix.mul_assoc β' β, hb2, Matrix.one_mul]`. Take `⟨-, -, T3, -⟩` from `GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V`.

Establish `hff : f * f = f` using `(T3 P e f hP).1`. Use `set φ := finPart D f with hφdef`. Establish `hφ : φ * φ = φ` using `by rw [hφdef, ← map_mul, hff]`. Establish `hφint : φ ∈ intAE D` using `GlobalTheory.AdIdem.idempotent_mem_intAE D φ hφ`. Establish `sm : ∀ (W : HSp D), ∀ a ∈ intAE D, ∀ y ∈ Formalism.L2.NTheta.LamHat W, a • y ∈ Formalism.L2.NTheta.LamHat W` using `fun W a ha y hy => GlobalTheory.LatDual.smul_mem_lamHat W a ha y hy`.

Establish `nsm : ∀ (W : HSp D) (N : ℕ), ∀ y ∈ Formalism.L2.NTheta.LamHat W, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • y ∈ Formalism.L2.NTheta.LamHat W`. Introduce `W N y hy`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `AddSubgroup.nsmul_mem _ hy N`. Take `⟨N1, hN1, hB1⟩` from `GlobalTheory.T.exists_nat_smul_matrix_mulVec_completedSelfDual V V' X`.

Take `⟨N2, hN2, hB2⟩` from `GlobalTheory.T.exists_nat_smul_matrix_mulVec_completedSelfDual V' V X'`. Set `hom : (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →+ (Fin V'.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))` to `(DistribMulAction.toAddMonoidHom _ φ).comp (Matrix.mulVecLin X).toAddMonoidHom`. Establish `hhom : ∀ y, hom y = φ • X.mulVec y` using `fun y => rfl`. Set `M : AddSubgroup (Fin V'.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))` to `(Formalism.L2.NTheta.LamHat V).map hom`. Establish `hM : ∀ z, z ∈ M ↔ ∃ y ∈ Formalism.L2.NTheta.LamHat V, φ • X.mulVec y = z` using `fun z => by`.

Simplify using `only [M, AddSubgroup.mem_map, hhom]`. Establish `c1 : ∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M`. Introduce `a ha z hz`. Take `⟨y, hy, rfl⟩` from `(hM z).1 hz`. Use `(hM _).2 ⟨a • y, sm V a ha y hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_smul, smul_comm]`. Establish `c2 : ∀ z ∈ M, φ • z = z`. Introduce `z hz`. Take `⟨y, hy, rfl⟩` from `(hM z).1 hz`. Rewrite using `[smul_smul, hφ]`.

Establish `c3 : ∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V', ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (φ • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.hos …`. Use `⟨N1 * N2, Nat.mul_pos hN1 hN2, fun y hy => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Use `(hM _).2 ⟨((N1 : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (((N2 : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X'.mulVec y), nsm V N1 _ (hB2 y hy), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hX1, Matrix.one_mulVec]`. Simplify using `only [smul_smul, Nat.cast_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take `⟨y, hy, rfl⟩` from `(hM z).1 hz`. Establish `h1` using `nsm V' N2 _ (sm V' φ hφint _ (hB1 y hy))`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Matrix.mulVec_smul, smul_smul, Nat.cast_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `c4 : ∀ g : GA D V', g ∈ KsphC V' ∅ → SuppF V' f g → ∀ z ∈ M, (finMat D.sp.cm.sig V'.gram g).mulVec z ∈ M`. Introduce `g hg _ z hz`.

Take `⟨y, hy, rfl⟩` from `(hM z).1 hz`. Take `⟨κ, hκ⟩` from `Q'.onto g hg.1`. Establish `hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n` using `(hU' κ).2 (by rw [hκ]; exact hg)`. Establish `hk : Q.ψ κ ∈ KsphC V ∅` using `(hU κ).1 hκU`. Use `(hM _).2 ⟨(finMat D.sp.cm.sig V.gram (Q.ψ κ)).mulVec y, (hk.2.1 y).1 hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hconj κ, hκ]`. Establish `hcore : ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (φ • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V')`. Break down `hP with ⟨hI, hfe⟩ | ⟨hfe, hpl, hint⟩` into its components or cases. Establish `h` using `GlobalTheory.T.splitPlace_hyperspecialStable_lattice_eq_multiple V' P e hI M`. Rewrite `h` using `[← hfe]`.

Conclude with `h c1 c2 c3 c4`. Rewrite `hpl`, `hint` using `[← hfe]`. Conclude with `GlobalTheory.T.inertPlace_hyperspecialStable_lattice_eq_multiple V' P f hpl hint M c1 c2 c3 c4`. Take `⟨c, ⟨u, rfl⟩, hcM⟩` from `hcore`. Use `⟨(u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X, (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.smul_mul (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X, Matrix.mul_smul X (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X', smul_smul, hX1, Units.mul_inv, one_sm …`. Rewrite using `[Matrix.smul_mul (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X', Matrix.mul_smul X' (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X, smul_smul, hX2, Units.inv_mul, one_s …`. Introduce `κ`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, hconj κ]`. Introduce `y`.

Establish `e1 : φ • (((u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X).mulVec y) = (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (φ • X.mulVec y)`. Rewrite using `[Matrix.smul_mulVec, smul_comm]`. Rewrite using `[e1]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hz : φ • X.mulVec y ∈ M` using `(hM _).2 ⟨φ • y, h, by rw [Matrix.mulVec_smul, smul_smul, hφ]⟩`. Conclude with `((hcM _).1 hz).2`. Introduce `h`. Establish `hz : φ • X.mulVec y ∈ M` using `(hcM _).2 ⟨by rw [smul_smul, hφ], h⟩`. Take `⟨y', hy', hyy⟩` from `(hM _).1 hz`.

Use `congrArg X'.mulVec hyy` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX2, Matrix.one_mulVec, Matrix.one_mulVec]`. Rewrite using `[← this]`. Conclude with `sm V φ hφint y' hy'`.
-/
theorem frames_match_lattices : ∀ {D : D7} {V V' : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n) (Q' : principalLevelFrame.RowPsi V' n), StdPsi hF Q → StdPsi hF Q' → ∀ (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → V'.rank = V.rank ∧ ∃ (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), J * J' = 1 ∧ J' * J = 1 ∧ (∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * J = J * finMat D.sp.cm.sig V.gram (Q.ψ κ)) ∧ ∀ y, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  intro D V V' n hF Q Q' hQ hQ' P e f hP
  haveI := nontrivial_R D
  obtain ⟨⟨β, β', hb1, hb2, hK⟩, hU⟩ := hQ
  obtain ⟨⟨γ, γ', hc1, hc2, hK'⟩, hU'⟩ := hQ'
  have hr : V.rank = n := card_eq_of_inv β β' hb1 hb2
  have hr' : V'.rank = n := card_eq_of_inv γ γ' hc1 hc2
  refine ⟨hr'.trans hr.symm, ?_⟩
  let X : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := γ * β'
  let X' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := β * γ'
  have hX1 : X * X' = 1 := by
    show γ * β' * (β * γ') = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc β' β γ', hb2, Matrix.one_mul, hc1]
  have hX2 : X' * X = 1 := by
    show β * γ' * (γ * β') = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ' γ β', hc2, Matrix.one_mul, hb1]
  have hconj : ∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * X = X * finMat D.sp.cm.sig V.gram (Q.ψ κ) := by
    intro κ
    rw [hK' κ, hK κ]
    show _ * (γ * β') = γ * β' * _
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc γ' γ β', hc2, Matrix.one_mul, ← Matrix.mul_assoc β' β, hb2, Matrix.one_mul]
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hff : f * f = f := (T3 P e f hP).1
  set φ := finPart D f with hφdef
  have hφ : φ * φ = φ := by rw [hφdef, ← map_mul, hff]
  have hφint : φ ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D φ hφ
  have sm : ∀ (W : HSp D), ∀ a ∈ intAE D, ∀ y ∈ Formalism.L2.NTheta.LamHat W, a • y ∈ Formalism.L2.NTheta.LamHat W :=
    fun W a ha y hy => GlobalTheory.LatDual.smul_mem_lamHat W a ha y hy
  have nsm : ∀ (W : HSp D) (N : ℕ), ∀ y ∈ Formalism.L2.NTheta.LamHat W, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • y ∈ Formalism.L2.NTheta.LamHat W := by
    intro W N y hy
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hy N
  obtain ⟨N1, hN1, hB1⟩ := GlobalTheory.T.exists_nat_smul_matrix_mulVec_completedSelfDual V V' X
  obtain ⟨N2, hN2, hB2⟩ := GlobalTheory.T.exists_nat_smul_matrix_mulVec_completedSelfDual V' V X'
  let hom : (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →+ (Fin V'.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :=
    (DistribMulAction.toAddMonoidHom _ φ).comp (Matrix.mulVecLin X).toAddMonoidHom
  have hhom : ∀ y, hom y = φ • X.mulVec y := fun y => rfl
  let M : AddSubgroup (Fin V'.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := (Formalism.L2.NTheta.LamHat V).map hom
  have hM : ∀ z, z ∈ M ↔ ∃ y ∈ Formalism.L2.NTheta.LamHat V, φ • X.mulVec y = z := fun z => by
    simp only [M, AddSubgroup.mem_map, hhom]
  have c1 : ∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M := by
    intro a ha z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    refine (hM _).2 ⟨a • y, sm V a ha y hy, ?_⟩
    rw [Matrix.mulVec_smul, smul_comm]
  have c2 : ∀ z ∈ M, φ • z = z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    rw [smul_smul, hφ]
  have c3 : ∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V', ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (φ • y) ∈ M) ∧
      ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V' := by
    refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, fun y hy => ?_, fun z hz => ?_⟩
    · refine (hM _).2 ⟨((N1 : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (((N2 : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X'.mulVec y), nsm V N1 _ (hB2 y hy), ?_⟩
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hX1, Matrix.one_mulVec]
      simp only [smul_smul, Nat.cast_mul]
      congr 1
      ring
    · obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
      have h1 := nsm V' N2 _ (sm V' φ hφint _ (hB1 y hy))
      convert h1 using 1
      simp only [Matrix.mulVec_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
  have c4 : ∀ g : GA D V', g ∈ KsphC V' ∅ → SuppF V' f g → ∀ z ∈ M,
      (finMat D.sp.cm.sig V'.gram g).mulVec z ∈ M := by
    intro g hg _ z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    obtain ⟨κ, hκ⟩ := Q'.onto g hg.1
    have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := (hU' κ).2 (by rw [hκ]; exact hg)
    have hk : Q.ψ κ ∈ KsphC V ∅ := (hU κ).1 hκU
    refine (hM _).2 ⟨(finMat D.sp.cm.sig V.gram (Q.ψ κ)).mulVec y, (hk.2.1 y).1 hy, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hconj κ, hκ]
  have hcore : ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (φ • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V') := by
    rcases hP with ⟨hI, hfe⟩ | ⟨hfe, hpl, hint⟩
    · have h := GlobalTheory.T.splitPlace_hyperspecialStable_lattice_eq_multiple V' P e hI M
      rw [← hfe] at h
      exact h c1 c2 c3 c4
    · rw [← hfe] at hpl hint
      exact GlobalTheory.T.inertPlace_hyperspecialStable_lattice_eq_multiple V' P f hpl hint M c1 c2 c3 c4
  obtain ⟨c, ⟨u, rfl⟩, hcM⟩ := hcore
  refine ⟨(u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X, (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X', ?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X, Matrix.mul_smul X (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X', smul_smul, hX1, Units.mul_inv, one_smul]
  · rw [Matrix.smul_mul (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X', Matrix.mul_smul X' (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X, smul_smul, hX2, Units.inv_mul, one_smul]
  · intro κ
    rw [Matrix.mul_smul, Matrix.smul_mul, hconj κ]
  · intro y
    have e1 : φ • (((u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X).mulVec y) = (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (φ • X.mulVec y) := by
      rw [Matrix.smul_mulVec, smul_comm]
    rw [e1]
    constructor
    · intro h
      have hz : φ • X.mulVec y ∈ M := (hM _).2 ⟨φ • y, h, by rw [Matrix.mulVec_smul, smul_smul, hφ]⟩
      exact ((hcM _).1 hz).2
    · intro h
      have hz : φ • X.mulVec y ∈ M := (hcM _).2 ⟨by rw [smul_smul, hφ], h⟩
      obtain ⟨y', hy', hyy⟩ := (hM _).1 hz
      have := congrArg X'.mulVec hyy
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX2,
        Matrix.one_mulVec, Matrix.one_mulVec] at this
      rw [← this]
      exact sm V φ hφint y' hy'

end GlobalTheory.LatMatch

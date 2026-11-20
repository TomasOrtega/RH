import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOpCommLiB
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

section General

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `set u := UniversalEnvelopingAlgebra.ι ℝ (L := L)`. Establish `h1 : ∀ j, u (φ (b j)) = ∑ i, (ε i * B (b i) (φ (b j))) • u (b i)` using `fun j => by conv_lhs => rw [eq_sum_of_orthogonal hε horth (φ (b j))]`. Simplify using `only [map_sum, map_smul]`. Establish `h2 : ∀ i, u (b i) = ∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j))` using `fun i => by`. Establish `e` using `congrArg φ (eq_sum_of_orthogonal hε horth (ψ (b i)))`.

Rewrite `e` using `[hψ]`. Use `conv_lhs => rw [e]`. Simplify using `only [map_sum, map_smul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hφ (b j) (ψ (b i)), hψ]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hsymm (b i)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ i, ε i • ((∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j))) * u (b i)) := by`. Simplify using `only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]`. Use `_ = ∑ i, ε i • (u (b i) * u (b i)) := Finset.sum_congr rfl fun i _ => by rw [← h2 i]`.
-/
theorem sum_sq_map_eq {B : LinearMap.BilinForm ℝ L} {b : Module.Basis ι ℝ L} {ε : ι → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : L, B X Y = B Y X) (φ ψ : L →ₗ⁅ℝ⁆ L)
    (hφ : ∀ X Y, B (φ X) (φ Y) = B X Y) (hψ : ∀ X, φ (ψ X) = X) :
    ∑ j, ε j • (UniversalEnvelopingAlgebra.ι ℝ (φ (b j)) * UniversalEnvelopingAlgebra.ι ℝ (φ (b j))) =
      ∑ i, ε i • (UniversalEnvelopingAlgebra.ι ℝ (b i) * UniversalEnvelopingAlgebra.ι ℝ (b i)) := by
  set u := UniversalEnvelopingAlgebra.ι ℝ (L := L)
  have h1 : ∀ j, u (φ (b j)) = ∑ i, (ε i * B (b i) (φ (b j))) • u (b i) := fun j => by
    conv_lhs => rw [eq_sum_of_orthogonal hε horth (φ (b j))]
    simp only [map_sum, map_smul]
  have h2 : ∀ i, u (b i) = ∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j)) := fun i => by
    have e := congrArg φ (eq_sum_of_orthogonal hε horth (ψ (b i)))
    rw [hψ] at e
    conv_lhs => rw [e]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hφ (b j) (ψ (b i)), hψ]
  calc ∑ j, ε j • (u (φ (b j)) * u (φ (b j)))
      = ∑ j, ε j • (u (φ (b j)) * ∑ i, (ε i * B (b i) (φ (b j))) • u (b i)) :=
        Finset.sum_congr rfl fun j _ => by rw [← h1 j]
    _ = ∑ i, ∑ j, (ε i * (ε j * B (φ (b j)) (b i))) • (u (φ (b j)) * u (b i)) := by
        simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hsymm (b i)]
        congr 1
        ring
    _ = ∑ i, ε i • ((∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j))) * u (b i)) := by
        simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
    _ = ∑ i, ε i • (u (b i) * u (b i)) :=
        Finset.sum_congr rfl fun i _ => by rw [← h2 i]

end General

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Rewrite using `[archTraceForm_apply, archTraceForm_apply]`. Use `congr 1`. Establish `hgi : mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (((g : (ArchMatrix E a)ˣ)) : ArchMatrix E a) = 1`. Rewrite using `[← mat_mul]`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `Matrix.trace ((mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (X : ArchMatrix E a) * mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a)) * (mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (Y : ArchMatrix E a) * mat (((g⁻¹ : archGroup E a) : (ArchMatrix …`. Generalize the expression as in `mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) = A at *`. Generalize the expression as in `mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) = C at *`. Generalize the expression as in `mat (X : ArchMatrix E a) = x`. Generalize the expression as in `mat (Y : ArchMatrix E a) = y`.

Establish `e : A * x * C * (A * y * C) = A * (x * y * C)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, Matrix.trace_mul_comm, Matrix.mul_assoc, hgi, Matrix.mul_one]`.
-/
theorem archTraceForm_AdLie (g : archGroup E a) (X Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a ((isExpLieAlgebra E a).AdLie g X) ((isExpLieAlgebra E a).AdLie g Y) =
      archTraceForm E a X Y := by
  rw [archTraceForm_apply, archTraceForm_apply]
  congr 1
  have hgi : mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) *
      mat (((g : (ArchMatrix E a)ˣ)) : ArchMatrix E a) = 1 := by
    rw [← mat_mul]
    simp
  change Matrix.trace ((mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (X : ArchMatrix E a) *
      mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a)) *
    (mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (Y : ArchMatrix E a) *
      mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a))) = _
  generalize mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) = A at *
  generalize mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) = C at *
  generalize mat (X : ArchMatrix E a) = x
  generalize mat (Y : ArchMatrix E a) = y
  have e : A * x * C * (A * y * C) = A * (x * y * C) := by
    calc A * x * C * (A * y * C) = A * x * (C * A) * y * C := by simp only [Matrix.mul_assoc]
      _ = A * (x * y * C) := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hgi, Matrix.mul_one]

/- English proof (translation)
Establish `e` using `(isExpLieAlgebra E a).Ad_inv_Ad g⁻¹ ((isExpLieAlgebra E a).ofLie X)`. Rewrite `e` using `[inv_inv]`. Conclude with `Subtype.ext (congrArg Subtype.val e)`.
-/
theorem AdLie_AdLie_inv (g : archGroup E a) (X : (isExpLieAlgebra E a).lieSubalgebra) :
    (isExpLieAlgebra E a).AdLie g ((isExpLieAlgebra E a).AdLie g⁻¹ X) = X := by
  have e := (isExpLieAlgebra E a).Ad_inv_Ad g⁻¹ ((isExpLieAlgebra E a).ofLie X)
  rw [inv_inv] at e
  exact Subtype.ext (congrArg Subtype.val e)

/- English proof (translation)
Simplify using `only [casimir, map_sum, map_smul, map_mul, IsExpLieAlgebra.AdU_ι]`. Conclude with `sum_sq_map_eq hε horth archTraceForm_symm _ ((isExpLieAlgebra E a).AdLie g⁻¹) (archTraceForm_AdLie g) (AdLie_AdLie_inv g)`.
-/
theorem AdU_casimir {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0) (g : archGroup E a) :
    (isExpLieAlgebra E a).AdU g (casimir b ε) = casimir b ε := by
  simp only [casimir, map_sum, map_smul, map_mul, IsExpLieAlgebra.AdU_ι]
  exact sum_sq_map_eq hε horth archTraceForm_symm _ ((isExpLieAlgebra E a).AdLie g⁻¹)
    (archTraceForm_AdLie g) (AdLie_AdLie_inv g)

/- English proof (translation)
Introduce `y` and use `by refine ⟨archEquiv E a (Matrix.GeneralLinearGroup.map (infEq E).toRingHom y), ?_⟩ simp only [toGL, ContinuousMulEquiv.symm_apply_apply] ext i j simp`.
-/
theorem toGL_surjective : Function.Surjective (toGL E a) := fun y => by
  refine ⟨archEquiv E a (Matrix.GeneralLinearGroup.map (infEq E).toRingHom y), ?_⟩
  simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
  ext i j
  simp

/- English proof (translation)
Apply the tactic sequence `have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num`. Take `⟨u, rfl⟩` from `toGL_surjective y`. Rewrite using `[← infEmb_eq]`. Establish `hrt : ∀ φ : Sm E a, smL E a (rt E a (infEmb E a u) φ) = rtInf u (smL E a φ)` using `fun _ => rfl`. Use `LinearMap.ext fun ψ => smL_injective ?_` and prove the remaining obligations.

Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, smL_omegaOp, hrt, uAction_rtInf, AdU_casimir b ε hε2 horth, hrt, smL_omegaOp]`.
-/
theorem omegaOp_comm_rt (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (y : GL (Fin a) (Cinf E)) :
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε * rt E a (infGL E a y) = rt E a (infGL E a y) * GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  obtain ⟨u, rfl⟩ := toGL_surjective y
  rw [← infEmb_eq]
  have hrt : ∀ φ : Sm E a, smL E a (rt E a (infEmb E a u) φ) = rtInf u (smL E a φ) := fun _ => rfl
  refine LinearMap.ext fun ψ => smL_injective ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, smL_omegaOp, hrt, uAction_rtInf,
    AdU_casimir b ε hε2 horth, hrt, smL_omegaOp]

end GlobalTheory.CompanionTheory.HCRep

end

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GelfandTransposeEqOfInvariantWords
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmOfMemGkGen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
open scoped Matrix

noncomputable section

namespace GlobalTheory.GelfSymm

open scoped Matrix

open GlobalTheory.Mem.RealTranslate (derEnd)
open GlobalTheory.RegSch (wordDer)

/- English proof (translation)
The claim follows from `| [] => by simp | a :: l => by rw [List.map_cons, List.prod_cons, prod_map_neg l, List.prod_cons, List.length_cons, pow_succ, mul_smul_comm, neg_mul, mul_comm, mul_smul, neg_one_smul, smul_neg]`.
-/
theorem prod_map_neg {R : Type} [Ring R] [Algebra ℂ R] :
    ∀ l : List R, (l.map fun a => -a).prod = (-1 : ℂ) ^ l.length • l.prod
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.prod_cons, prod_map_neg l, List.prod_cons, List.length_cons, pow_succ,
      mul_smul_comm, neg_mul, mul_comm, mul_smul, neg_one_smul, smul_neg]

/- English proof (translation)
Set `ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Rᵐᵒᵖ` to `(MulOpposite.opLinearEquiv ℂ).toLinearMap ∘ₗ φ`. Establish `h` using `congrArg MulOpposite.unop (GlobalTheory.RegSch.GelfCyc.sum_words ψ M hM k)`. Establish `e : ∀ l : List R, (l.map MulOpposite.op).prod = MulOpposite.op l.reverse.prod` using `fun l => by`. Rewrite using `[MulOpposite.op_list_prod, List.map_reverse, List.reverse_reverse]`. Establish `e' : ∀ l : List R, (l.map MulOpposite.op).reverse.prod = MulOpposite.op l.prod` using `fun l => (MulOpposite.op_list_prod l).symm`.

Establish `hψ : ∀ g : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ, (List.ofFn fun a => ψ (g a)) = (List.ofFn fun a => φ (g a)).map MulOpposite.op`. Introduce `g`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Establish `hs : ∀ f : (Fin (k + 1) → Fin n) → R, ∑ i, MulOpposite.op (f i) = MulOpposite.op (∑ i, f i)` using `fun f => (map_sum MulOpposite.opAddEquiv f _).symm`.

Simplify using `only [hψ, e, e', hs, MulOpposite.unop_smul, MulOpposite.unop_op] at h`. Conclude with `h`.
-/
theorem sum_words_rev {R : Type} [Ring R] [Algebra ℂ R] {n : ℕ} (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] R)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det) (k : ℕ) :
    ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (-(M * (Matrix.single (idx a) (idx (a + 1)) 1)ᵀ * M⁻¹))).reverse.prod =
    (-1 : ℂ) ^ (k + 1) • ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (Matrix.single (idx a) (idx (a + 1)) 1)).prod := by
  let ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Rᵐᵒᵖ := (MulOpposite.opLinearEquiv ℂ).toLinearMap ∘ₗ φ
  have h := congrArg MulOpposite.unop (GlobalTheory.RegSch.GelfCyc.sum_words ψ M hM k)
  have e : ∀ l : List R, (l.map MulOpposite.op).prod = MulOpposite.op l.reverse.prod := fun l => by
    rw [MulOpposite.op_list_prod, List.map_reverse, List.reverse_reverse]
  have e' : ∀ l : List R, (l.map MulOpposite.op).reverse.prod = MulOpposite.op l.prod := fun l =>
    (MulOpposite.op_list_prod l).symm
  have hψ : ∀ g : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ, (List.ofFn fun a => ψ (g a)) = (List.ofFn fun a => φ (g a)).map MulOpposite.op := by
    intro g; rw [List.map_ofFn]; rfl
  have hs : ∀ f : (Fin (k + 1) → Fin n) → R, ∑ i, MulOpposite.op (f i) = MulOpposite.op (∑ i, f i) :=
    fun f => (map_sum MulOpposite.opAddEquiv f _).symm
  simp only [hψ, e, e', hs, MulOpposite.unop_smul, MulOpposite.unop_op] at h
  exact h

end GlobalTheory.GelfSymm

namespace GlobalTheory.GelfSymm

open scoped Matrix
open GlobalTheory.Mem.RealTranslate (derEnd)
open GlobalTheory.RegSch (wordDer)

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

/- English proof (translation)
Simplify using `only [wordDer, List.foldr_append]`.
-/
theorem wordDer_append (τ : D.what₂.Tau) (l l' : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (f : GA D V → ℂ) :
    wordDer θ V τ (l ++ l') f = wordDer θ V τ l (wordDer θ V τ l' f) := by
  simp only [wordDer, List.foldr_append]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact hf`. Consider the case `cons Z l ih => exact hA Z _ ih`.
-/
theorem wordDer_mem {τ : D.what₂.Tau} {A : Submodule ℂ (GA D V → ℂ)} (hA : ∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) {f : GA D V → ℂ} (hf : f ∈ A) : wordDer θ V τ l f ∈ A := by
  induction l with
  | nil => exact hf
  | cons Z l ih => exact hA Z _ ih

/- English proof (translation)
The claim follows from `| [], x, _, y, _ => rfl | Z :: l, x, hx, y, hy => by show b x (RderC θ V τ Z (wordDer θ V τ l y)) = _ rw [hb Z x hx _ (wordDer_mem hA l hy), adj_word hA b hb l _ (hA _ _ hx) y hy, List.reverse_cons, List.map_append, wordDer_append] rfl`.
-/
theorem adj_word {τ : D.what₂.Tau} {A : Submodule ℂ (GA D V → ℂ)} (hA : ∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A)
    (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ)
    (hb : ∀ Z, ∀ x ∈ A, ∀ y ∈ A, b x (RderC θ V τ Z y) =
      b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y) :
    ∀ (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), ∀ x ∈ A, ∀ y ∈ A,
      b x (wordDer θ V τ l y) =
        b (wordDer θ V τ (l.reverse.map fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y
  | [], x, _, y, _ => rfl
  | Z :: l, x, hx, y, hy => by
    show b x (RderC θ V τ Z (wordDer θ V τ l y)) = _
    rw [hb Z x hx _ (wordDer_mem hA l hy), adj_word hA b hb l _ (hA _ _ hx) y hy, List.reverse_cons, List.map_append,
      wordDer_append]
    rfl

end GlobalTheory.GelfSymm

open GlobalTheory.Mem.RealTranslate (derEnd) in
open GlobalTheory.RegSch (wordDer) in
open GlobalTheory.GelfSymm in

/- English proof (translation)
Introduce `D θ V hθ τ A hAS hA b hb k x hx y hy`. Establish `hu : IsUnit (gramAt D V τ).det` using `GlobalTheory.SmoothAutCheck.gramAt_unit V τ`. Establish `hM : IsUnit ((gramAt D V τ)⁻¹).det` using `Matrix.isUnit_nonsing_inv_det_iff.2 hu`. Set `E : (Fin (k + 1) → Fin V.rank) → Fin (k + 1) → Matrix (Fin V.rank) (Fin V.rank) ℂ` to `fun idx a => Matrix.single (idx a) (idx (a + 1)) 1`. Establish `hg : ∀ f, gelf θ V τ k f = ∑ idx, wordDer θ V τ (List.ofFn (E idx)) f`.

Introduce `f`. Use `Finset.sum_congr rfl fun idx _ => ?_` and prove the remaining obligations. Rewrite using `[wordDer, ← List.foldr_map (f := RderC θ V τ) (g := fun A acc => A acc), List.map_ofFn]`. Both sides reduce to the same expression. Establish `hs : ∀ i j, (gramAt D V τ)⁻¹ * Matrix.conjTranspose (Matrix.single i j (1 : ℂ)) * gramAt D V τ = -(-((gramAt D V τ)⁻¹ * (Matrix.single i j (1 : ℂ))ᵀ * (gramAt D V τ)⁻¹⁻¹))`.

Introduce `i j`. Rewrite using `[neg_neg, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.conjTranspose_single, Matrix.transpose_single, star_one]`. Establish `key : ∑ idx, (((List.ofFn (E idx)).reverse.map fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ).map (derEnd hθ τ)).prod = ∑ idx, ((List.ofFn (E idx)).map (derEnd hθ τ)).prod`. Establish `h1` using `sum_words_rev (derEnd hθ τ) (gramAt D V τ)⁻¹ hM k`. Establish `e : ∀ idx, ((List.ofFn (E idx)).reverse.map fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ).map (derEnd hθ τ) = (List.ofFn fun a => derEnd hθ τ (-((gramAt D V τ)⁻¹ * (E idx a)ᵀ * (gramAt D V τ)⁻¹⁻¹))).reverse.map fun a => -a`.

Introduce `idx`. Rewrite using `[List.map_map, List.map_reverse, List.map_reverse, List.map_ofFn, List.map_ofFn]`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Simplify using `only [Function.comp_apply, E, hs, map_neg]`. Simplify using `only [e, prod_map_neg, List.length_reverse, List.length_ofFn, List.map_ofFn]`. Rewrite using `[← Finset.smul_sum, h1, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]`. Both sides reduce to the same expression. Establish `hxS : x ∈ GlobalTheory.Mem.AutSpace.SmFun θ V` using `hAS hx`.

Establish `wx : ∀ w, wordDer θ V τ w x = ((w.map (derEnd hθ τ)).prod ⟨x, hxS⟩).1` using `fun w => GlobalTheory.RegSch.GelfCyc.wordDer_eq hθ τ w ⟨x, hxS⟩`. Establish `hgx : ∑ idx, wordDer θ V τ ((List.ofFn (E idx)).reverse.map fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x = gelf θ V τ k x`. Rewrite using `[hg x]`. Simplify using `only [wx]`. Rewrite using `[← Submodule.coe_sum, ← Submodule.coe_sum, ← LinearMap.sum_apply, ← LinearMap.sum_apply, key]`.

Rewrite using `[hg y, map_sum, ← hgx, map_sum, LinearMap.sum_apply]`. Conclude with `Finset.sum_congr rfl fun idx _ => adj_word hA b hb _ x hx y hy`.
-/
theorem GlobalTheory.GelfSymm.gelf_symm : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (A : Submodule ℂ (GA D V → ℂ)), A ≤ GlobalTheory.Mem.AutSpace.SmFun θ V →
    (∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A) → ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
    (∀ Z, ∀ x ∈ A, ∀ y ∈ A, b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y) →
    ∀ k, ∀ x ∈ A, ∀ y ∈ A, b x (gelf θ V τ k y) = b (gelf θ V τ k x) y := by
  intro D θ V hθ τ A hAS hA b hb k x hx y hy
  have hu : IsUnit (gramAt D V τ).det := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hM : IsUnit ((gramAt D V τ)⁻¹).det := Matrix.isUnit_nonsing_inv_det_iff.2 hu
  let E : (Fin (k + 1) → Fin V.rank) → Fin (k + 1) → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun idx a => Matrix.single (idx a) (idx (a + 1)) 1
  have hg : ∀ f, gelf θ V τ k f = ∑ idx, wordDer θ V τ (List.ofFn (E idx)) f := by
    intro f
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [wordDer, ← List.foldr_map (f := RderC θ V τ) (g := fun A acc => A acc), List.map_ofFn]
    rfl
  have hs : ∀ i j, (gramAt D V τ)⁻¹ * Matrix.conjTranspose (Matrix.single i j (1 : ℂ)) * gramAt D V τ =
      -(-((gramAt D V τ)⁻¹ * (Matrix.single i j (1 : ℂ))ᵀ * (gramAt D V τ)⁻¹⁻¹)) := by
    intro i j
    rw [neg_neg, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.conjTranspose_single, Matrix.transpose_single, star_one]
  have key : ∑ idx, (((List.ofFn (E idx)).reverse.map
        fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ).map (derEnd hθ τ)).prod =
      ∑ idx, ((List.ofFn (E idx)).map (derEnd hθ τ)).prod := by
    have h1 := sum_words_rev (derEnd hθ τ) (gramAt D V τ)⁻¹ hM k
    have e : ∀ idx, ((List.ofFn (E idx)).reverse.map
        fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ).map (derEnd hθ τ) =
        (List.ofFn fun a => derEnd hθ τ (-((gramAt D V τ)⁻¹ * (E idx a)ᵀ * (gramAt D V τ)⁻¹⁻¹))).reverse.map
          fun a => -a := by
      intro idx
      rw [List.map_map, List.map_reverse, List.map_reverse, List.map_ofFn, List.map_ofFn]
      congr 1
      congr 1
      funext a
      simp only [Function.comp_apply, E, hs, map_neg]
    simp only [e, prod_map_neg, List.length_reverse, List.length_ofFn, List.map_ofFn]
    rw [← Finset.smul_sum, h1, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
    rfl
  have hxS : x ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := hAS hx
  have wx : ∀ w, wordDer θ V τ w x = ((w.map (derEnd hθ τ)).prod ⟨x, hxS⟩).1 :=
    fun w => GlobalTheory.RegSch.GelfCyc.wordDer_eq hθ τ w ⟨x, hxS⟩
  have hgx : ∑ idx, wordDer θ V τ ((List.ofFn (E idx)).reverse.map
      fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x = gelf θ V τ k x := by
    rw [hg x]
    simp only [wx]
    rw [← Submodule.coe_sum, ← Submodule.coe_sum, ← LinearMap.sum_apply, ← LinearMap.sum_apply, key]
  rw [hg y, map_sum, ← hgx, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun idx _ => adj_word hA b hb _ x hx y hy

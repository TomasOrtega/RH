import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentificationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTieLP

open GlobalTheory.WeilDeligne

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Use extensionality with `i`. Rewrite using `[zero_smul, Matrix.charpoly_zero, coeff_scaleRoots, M.charpoly_natDegree_eq_dim, coeff_X_pow]`. Distinguish the cases in `hi : i = Fintype.card n`.

Substitute `hi` using the available equality. Use `M.charpoly_monic.coeff_natDegree` as an intermediate fact. Rewrite `this` using `[M.charpoly_natDegree_eq_dim]`. Simplify using `[this]`. Break down `lt_or_gt_of_ne hi with h | h` into its components or cases.

Establish `: Fintype.card n - i ≠ 0` using `by omega`. Simplify using `[hi, this]`. Simplify using `[hi, coeff_eq_zero_of_natDegree_lt (p := M.charpoly) (by rwa [M.charpoly_natDegree_eq_dim])]`. Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `t`.

Establish `h1 : (M.charpoly.scaleRoots c).eval (c * (t / c)) = c ^ M.charpoly.natDegree * M.charpoly.eval (t / c)`. Simplify using `using scaleRoots_eval₂_mul (RingHom.id ℂ) (t / c) c (p := M.charpoly)`. Rewrite `h1` using `[mul_div_cancel₀ _ hc, M.charpoly_natDegree_eq_dim]`. Rewrite using `[h1, Matrix.eval_charpoly, Matrix.eval_charpoly, ← Matrix.det_smul]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[Matrix.scalar_apply, Matrix.sub_apply, Matrix.diagonal_apply, mul_sub]`. Apply the tactic sequence `split_ifs <;> field_simp`.
-/
theorem matrix_charpoly_smul {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (c : ℂ) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  by_cases hc : c = 0
  · subst hc
    ext i
    rw [zero_smul, Matrix.charpoly_zero, coeff_scaleRoots, M.charpoly_natDegree_eq_dim, coeff_X_pow]
    by_cases hi : i = Fintype.card n
    · subst hi
      have := M.charpoly_monic.coeff_natDegree
      rw [M.charpoly_natDegree_eq_dim] at this
      simp [this]
    · rcases lt_or_gt_of_ne hi with h | h
      · have : Fintype.card n - i ≠ 0 := by omega
        simp [hi, this]
      · simp [hi, coeff_eq_zero_of_natDegree_lt (p := M.charpoly) (by rwa [M.charpoly_natDegree_eq_dim])]
  · apply Polynomial.funext
    intro t
    have h1 : (M.charpoly.scaleRoots c).eval (c * (t / c)) = c ^ M.charpoly.natDegree * M.charpoly.eval (t / c) := by
      simpa using scaleRoots_eval₂_mul (RingHom.id ℂ) (t / c) c (p := M.charpoly)
    rw [mul_div_cancel₀ _ hc, M.charpoly_natDegree_eq_dim] at h1
    rw [h1, Matrix.eval_charpoly, Matrix.eval_charpoly, ← Matrix.det_smul]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.diagonal_apply, mul_sub]
    split_ifs <;> field_simp

/- English proof (translation)
Rewrite using `[← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, matrix_charpoly_smul, LinearMap.charpoly_toMatrix]`.
-/
theorem charpoly_smul_end {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (c : ℂ) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, matrix_charpoly_smul,
    LinearMap.charpoly_toMatrix]

/- English proof (translation)
Set `e : L ≃ₗ[ℂ] ℂ` to `LinearEquiv.ofFinrankEq L ℂ (by simp [hL])`. Set `E : TensorProduct ℂ V L ≃ₗ[ℂ] V` to `(TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)`. Establish `key : ∀ x, E (TensorProduct.map f (c • (1 : Module.End ℂ L)) x) = (c • f) (E x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul v l`. Simplify using `[E, TensorProduct.map_tmul, smul_comm c, map_smul]`. Establish `h2 : E.conj (TensorProduct.map f (c • (1 : Module.End ℂ L))) = c • f`.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `E.surjective v`. Simplify `key x` using `[LinearEquiv.conj_apply]`. Rewrite using `[← charpoly_smul_end, ← h2, LinearEquiv.charpoly_conj]`.
-/
theorem charpoly_map_line {V L : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup L] [Module ℂ L] [FiniteDimensional ℂ L] (hL : Module.finrank ℂ L = 1)
    (f : Module.End ℂ V) (c : ℂ) :
    (TensorProduct.map f (c • (1 : Module.End ℂ L))).charpoly = f.charpoly.scaleRoots c := by
  let e : L ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq L ℂ (by simp [hL])
  let E : TensorProduct ℂ V L ≃ₗ[ℂ] V :=
    (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  have key : ∀ x, E (TensorProduct.map f (c • (1 : Module.End ℂ L)) x) = (c • f) (E x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v l =>
      simp [E, TensorProduct.map_tmul, smul_comm c, map_smul]
  have h2 : E.conj (TensorProduct.map f (c • (1 : Module.End ℂ L))) = c • f := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := E.surjective v
    simpa [LinearEquiv.conj_apply] using key x
  rw [← charpoly_smul_end, ← h2, LinearEquiv.charpoly_conj]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

/- English proof (translation)
Proceed by induction on `a using WD.ind with`. Consider the case `hP m a`. Proceed by induction on `c using WD.ind with`. Consider the case `hP n c`. Rewrite `hz` using `[WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk]`.

Rewrite `hc` using `[WD.lpDim_mk]`. Establish `h1` using `LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))`. Rewrite `h1` using `[hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.charPol_mk, WDRep.tensor_ρ, h1, charpoly_map_line hc]`.
-/
theorem inePol_char {a c : WD h} (hc : c.lpDim = 1) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B)
    {z : ℂ} (hz : c.inePol σ = X - C z) : (a.lpChar c).inePol σ = (a.inePol σ).scaleRoots z := by
  induction a using WD.ind with
  | hP m a =>
  induction c using WD.ind with
  | hP n c =>
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk] at hz
    rw [WD.lpDim_mk] at hc
    have h1 := LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))
    rw [hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h1
    rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.charPol_mk,
      WDRep.tensor_ρ, h1, charpoly_map_line hc]

end GlobalTheory.RowTieLP

/- English proof (translation)
Introduce `D T w a b χ χ' s h1 h2`. Take `⟨l1, l2, l3, l4, l5⟩` from `(GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ _ _ T).2.1 w a b χ χ' s h1 h2`. Use `⟨l1, l2, l3, l4, l5, fun σ hσ => ⟨⟨?_, ?_⟩, fun c hc => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ]`. Conclude with `GlobalTheory.WeilDeligne.WD.charPol_monic _ _`.

Rewrite using `[T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ, GlobalTheory.WeilDeligne.WD.charPol_natDegree, T.dim]`. Rewrite `hc` using `[T.inePol w χ σ hσ]`. Establish `hd : (T.e w χ).lpDim = 1` using `by rw [T.dim, h1]`. Rewrite using `[T.inePol w _ σ hσ, T.char _ _ _ h1, T.inePol w a σ hσ]`. Conclude with `GlobalTheory.RowTieLP.inePol_char hd hσ hc`.
-/
theorem GlobalTheory.RowTieLP.main : ∀ (D : D7), WDTie D.nd D.naut → Formalism.MainNotions.SumRepresentations.At.TieLP D.nd D.naut := by
  intro D T w a b χ χ' s h1 h2
  obtain ⟨l1, l2, l3, l4, l5⟩ := (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ _ _ T).2.1 w a b χ χ' s h1 h2
  refine ⟨l1, l2, l3, l4, l5, fun σ hσ => ⟨⟨?_, ?_⟩, fun c hc => ?_⟩⟩
  · rw [T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ]
    exact GlobalTheory.WeilDeligne.WD.charPol_monic _ _
  · rw [T.inePol w a σ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ, GlobalTheory.WeilDeligne.WD.charPol_natDegree, T.dim]
  · rw [T.inePol w χ σ hσ] at hc
    have hd : (T.e w χ).lpDim = 1 := by rw [T.dim, h1]
    rw [T.inePol w _ σ hσ, T.char _ _ _ h1, T.inePol w a σ hσ]
    exact GlobalTheory.RowTieLP.inePol_char hd hσ hc

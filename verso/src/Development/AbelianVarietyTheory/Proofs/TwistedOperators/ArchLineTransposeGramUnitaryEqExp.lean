import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamUnitaryMatrixEqExpLieAlgebraStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LineDecomp

/- English proof (translation)
Establish `h : (u.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J * (u.1.1).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J` using `u.2`. Generalize the expression as in `hm : u.1.1 = m at h`. Establish `e0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J = Formalism.L2.Theta.incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ`. Rewrite using `[hJ]`. Simplify using `only [Equiv.coe_refl, Matrix.submatrix_id_id]`.

Conclude with `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _`. Rewrite `h` using `[e0, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hu : IsUnit (Formalism.L2.Theta.incA D D.host.xi0)` using `(isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _`. Establish `h2` using `hu.smul_left_cancel.1 h`. Establish `h3` using `congrArg Matrix.transpose h2`.

Rewrite `h3` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]`. Establish `e : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ)ᵀ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram` using `rfl`. Rewrite `h3` using `[e, ← hm]`. Use `⟨⟨u.1, h3⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Conclude with `GlobalTheory.TripleRead.toUX_val X (Equiv.refl _) hJ _`.
-/
theorem toUX_surj (D : D7) (X : HSp D) {J : Matrix (Fin X.rank) (Fin X.rank) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
    (u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig J) : ∃ g : GA D X, GlobalTheory.TripleRead.toUX X (Equiv.refl _) hJ g = u := by
  have h : (u.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J * (u.1.1).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J := u.2
  generalize hm : u.1.1 = m at h
  have e0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J = Formalism.L2.Theta.incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
    rw [hJ]
    simp only [Equiv.coe_refl, Matrix.submatrix_id_id]
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _
  rw [e0, Matrix.mul_smul, Matrix.smul_mul] at h
  have hu : IsUnit (Formalism.L2.Theta.incA D D.host.xi0) := (isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have h2 := hu.smul_left_cancel.1 h
  have h3 := congrArg Matrix.transpose h2
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h3
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ)ᵀ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := rfl
  rw [e, ← hm] at h3
  refine ⟨⟨u.1, h3⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact GlobalTheory.TripleRead.toUX_val X (Equiv.refl _) hJ _

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Set `a : AF D.host.F` to `((0 : Ainf D.host.F), (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F))`. Establish `ha : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F a = 0` using `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)`. Establish `h1` using `h a ha`. Set `φ` to `Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)`. Establish `key : ∀ x : AF D.host.F ⊗[D.host.F] D.host.E, φ (a • x) = φ x`.

Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [smul_zero]`. Consider the case `tmul b c`. Rewrite using `[TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_eq_mul, map_mul]`.

Use `congr 1`. Conclude with `one_mul _`. Consider the case `add x y hx hy`. Establish `e1 : a • (x + y) = a • x + a • y` using `smul_add a x y`. Rewrite using `[e1, map_add φ (a • x) (a • y), map_add φ x y, hx, hy]`.

Use `show finHom X g = 1`. Apply `Units.ext` to reduce the goal to its premises. Use `show (Formalism.L2.Theta.mt X g).map φ = 1`. Use extensionality with `i j`. Establish `h2` using `congrArg φ (congrFun (congrFun h1 i) j)`.

Rewrite `h2` using `[Matrix.smul_apply, key, Matrix.zero_apply, map_zero, Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem mem_GinfC_of_at (D : D7) (X : HSp D) (g : GA D X)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Formalism.L2.Theta.mt X g - 1)) : g ∈ GinfC X := by
  let a : AF D.host.F := ((0 : Ainf D.host.F), (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F))
  have ha : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F a = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
  have h1 := h a ha
  let φ := Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
  have key : ∀ x : AF D.host.F ⊗[D.host.F] D.host.E, φ (a • x) = φ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero]
    | tmul b c =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_eq_mul, map_mul]
      congr 1
      exact one_mul _
    | add x y hx hy =>
      have e1 : a • (x + y) = a • x + a • y := smul_add a x y
      rw [e1, map_add φ (a • x) (a • y), map_add φ x y, hx, hy]
  show finHom X g = 1
  apply Units.ext
  show (Formalism.L2.Theta.mt X g).map φ = 1
  ext i j
  have h2 := congrArg φ (congrFun (congrFun h1 i) j)
  rw [Matrix.smul_apply, key, Matrix.zero_apply, map_zero, Matrix.sub_apply, map_sub, sub_eq_zero] at h2
  rw [Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `D θ hθ X Ws hJ γ hγ`. Establish `R` using `(GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ X`. Use `choose g hg using fun t : ℝ => toUX_surj D X hJ (γ (Multiplicative.ofAdd t))`. Establish `hmat : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) = Formalism.L2.Theta.mt X (g t)` using `fun t => by`. Rewrite using `[← hg t]`.

Use `show (GlobalTheory.TripleRead.toUX X _ hJ (g t)).1.1 = _`. Rewrite using `[GlobalTheory.TripleRead.toUX_val]`. Both sides reduce to the same expression. Establish `inj : ∀ a b : GA D X, Formalism.L2.Theta.mt X a = Formalism.L2.Theta.mt X b → a = b` using `fun a b h => Subtype.ext (Units.ext h)`. Establish `mtmul : ∀ a b : GA D X, Formalism.L2.Theta.mt X (a * b) = Formalism.L2.Theta.mt X a * Formalism.L2.Theta.mt X b` using `fun a b => by`.

Simplify using `[Formalism.L2.Theta.mt, map_mul]`. Establish `hmul : ∀ s t, g (s + t) = g s * g t` using `fun s t => inj _ _ (by`. Rewrite using `[mtmul, ← hmat, ← hmat, ← hmat, ofAdd_add, map_mul]`. Use the proof step `rfl)`. Establish `g0 : g 0 = 1` using `inj _ _ (by`.

Rewrite using `[← hmat, ofAdd_zero, map_one]`. Use the proof step `rfl)`. Establish `hinf : ∀ t, g t ∈ GinfC X` using `fun t => mem_GinfC_of_at D X (g t) (by rw [← hmat]; exact hγ.2 _)`. Establish `hcont : Continuous fun t : ℝ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))` using `Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd))`. Establish `hu : ∀ τ, Continuous fun t : ℝ => infMat D.sp.cm.sig X.gram (θ τ) (g t)` using `fun τ => by`.

Use `((hcont.matrix_map (GlobalTheory.Member.Arch.continuous_inf _ _)).matrix_map (GlobalTheory.Mem.VolExists.infEmb_continuous (hθ τ))).congr fun t => ?_` and prove the remaining obligations. Rewrite using `[hmat]`. Both sides reduce to the same expression. Use `choose Y hY hYe using fun τ => GlobalTheory.T.oneParamUnitaryMatrix_eq_exp_lieAlgebra (gramAt D X τ) (fun t => infMat D.sp.cm.sig X.gram (θ τ) (g t)) (hu τ) (by rw [g0]; simp [infMat, HA.mat]; exact Matrix.map_one _ (by simp) (by simp)) (fun s t => by rw [hmul]; exact R.2.2.2.1 _ …`. Set `L : GlobalTheory.SmoothForms.LieN X` to `fun τ => ⟨Y τ, hY τ⟩`.

Use `⟨L, fun t => ?_⟩` and prove the remaining obligations. Establish `hE` using `GlobalTheory.SmoothForms.isExpFam_expInf R (t • L)`. Establish `e : GlobalTheory.SmoothForms.expInf θ X (t • L) = g t` using `R.2.2.1 _ hE.1 _ (hinf t) fun τ => by`. Rewrite using `[hE.2 τ, hYe τ t]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `(hg t).symm`.
-/
theorem line_eq_expInf : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws, ∃ L : GlobalTheory.SmoothForms.LieN X, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (GlobalTheory.SmoothForms.expInf θ X (t • L)) := by
  intro D θ hθ X Ws hJ γ hγ
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ X
  choose g hg using fun t : ℝ => toUX_surj D X hJ (γ (Multiplicative.ofAdd t))
  have hmat : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) = Formalism.L2.Theta.mt X (g t) := fun t => by
    rw [← hg t]
    show (GlobalTheory.TripleRead.toUX X _ hJ (g t)).1.1 = _
    rw [GlobalTheory.TripleRead.toUX_val]
    rfl
  have inj : ∀ a b : GA D X, Formalism.L2.Theta.mt X a = Formalism.L2.Theta.mt X b → a = b := fun a b h =>
    Subtype.ext (Units.ext h)
  have mtmul : ∀ a b : GA D X, Formalism.L2.Theta.mt X (a * b) = Formalism.L2.Theta.mt X a * Formalism.L2.Theta.mt X b := fun a b => by
    simp [Formalism.L2.Theta.mt, map_mul]
  have hmul : ∀ s t, g (s + t) = g s * g t := fun s t => inj _ _ (by
    rw [mtmul, ← hmat, ← hmat, ← hmat, ofAdd_add, map_mul]
    rfl)
  have g0 : g 0 = 1 := inj _ _ (by
    rw [← hmat, ofAdd_zero, map_one]
    rfl)
  have hinf : ∀ t, g t ∈ GinfC X := fun t => mem_GinfC_of_at D X (g t) (by rw [← hmat]; exact hγ.2 _)
  have hcont : Continuous fun t : ℝ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd))
  have hu : ∀ τ, Continuous fun t : ℝ => infMat D.sp.cm.sig X.gram (θ τ) (g t) := fun τ => by
    refine ((hcont.matrix_map (GlobalTheory.Member.Arch.continuous_inf _ _)).matrix_map
      (GlobalTheory.Mem.VolExists.infEmb_continuous (hθ τ))).congr fun t => ?_
    rw [hmat]
    rfl
  choose Y hY hYe using fun τ => GlobalTheory.T.oneParamUnitaryMatrix_eq_exp_lieAlgebra (gramAt D X τ) (fun t => infMat D.sp.cm.sig X.gram (θ τ) (g t)) (hu τ)
    (by rw [g0]; simp [infMat, HA.mat]; exact Matrix.map_one _ (by simp) (by simp))
    (fun s t => by rw [hmul]; exact R.2.2.2.1 _ _ _)
    (fun t => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ X (g t) τ)
  let L : GlobalTheory.SmoothForms.LieN X := fun τ => ⟨Y τ, hY τ⟩
  refine ⟨L, fun t => ?_⟩
  have hE := GlobalTheory.SmoothForms.isExpFam_expInf R (t • L)
  have e : GlobalTheory.SmoothForms.expInf θ X (t • L) = g t := R.2.2.1 _ hE.1 _ (hinf t) fun τ => by
    rw [hE.2 τ, hYe τ t]
    rfl
  rw [e]
  exact (hg t).symm

end GlobalTheory.LineDecomp

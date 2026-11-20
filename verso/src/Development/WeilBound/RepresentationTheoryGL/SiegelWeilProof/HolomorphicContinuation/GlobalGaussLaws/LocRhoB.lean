import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KeepLatticeHyperbolicEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmTypeStatement

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem compFin_eq_finPart (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v z =
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Simplify using `only [reidx, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]`.
-/
theorem reidx_conjTranspose_mul (y : M2 n) : (reidx y)ᴴ * reidx y = reidx (yᴴ * y) := by
  simp only [reidx, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

/- English proof (translation)
Simplify using `[reidx]`.
-/
theorem reidx_one : reidx (1 : M2 n) = 1 := by
  simp [reidx]

/- English proof (translation)
Take `⟨-, hcA, -, -⟩` from `GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ`. Use extensionality with `i j`. Simplify using `only [compAt, Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.conjTranspose_apply]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul]`. Use `congr 1`. Conclude with `hcA (M l i) τ'`.
-/
theorem compAt_cT_mul {θ : InfFam D} (hθ : IsInfFam θ) {m : ℕ} (M : Matrix (Fin m) (Fin m) (AE D)) (τ' : D.what₂.Tau) :
    compAt θ τ' (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * M) =
      (compAt θ τ' M)ᴴ * compAt θ τ' M := by
  obtain ⟨-, hcA, -, -⟩ := GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.conjTranspose_apply]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_mul]
  congr 1
  exact hcA (M l i) τ'

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[Formalism.UG.cT]`. Simplify using `[Formalism.UG.cT, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]`.
-/
theorem cT_one {m : ℕ} : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (1 : Matrix (Fin m) (Fin m) (AE D)) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.UG.cT]
  · simp [Formalism.UG.cT, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

/- English proof (translation)
Take `⟨hinf0, hcA, -, -⟩` from `GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ`. Take `⟨-, hcomp⟩` from `hι`. Take `⟨hτ, hτ', hfin⟩` from `hcomp k`. Rewrite using `[K, GlobalTheory.RegSch.EmbLevel.mem_levelAll_iff]`. Use `set M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (ι k)).1 with hM`.

Establish `hMm : M = mat (ι k)` using `rfl`. Use `⟨fun v y => ?_, fun w => ?_⟩` and prove the remaining obligations. Establish `h1 : M.map (compFin D.host.F D.host.E v) = 1`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`.

Rewrite using `[compFin_eq_finPart]`. Use `congrFun (congrFun hfin i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`. Rewrite `this` using `[← hMm]`. Rewrite using `[this]`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h]`. Rewrite using `[h1, Matrix.one_mulVec]`.

Establish `key : ∀ i j, compInf D.host.F D.host.E w ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig) M * M) i j - (1 : Matrix (Fin (n + n)) (Fin (n + n)) (AE D)) i j) = 0`. Introduce `i j`. Use `((hinf0 _).2 ?_) w` and prove the remaining obligations. Introduce `τ'`. Establish `hc` using `compAt_cT_mul hθ M τ'`.

Establish `hrow : θ τ' (infPart D ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * M) i j)) = ((compAt θ τ' M)ᴴ * compAt θ τ' M) i j` using `congrFun (congrFun hc i) j`. Rewrite using `[map_sub, map_sub, hrow]`. Distinguish the cases in `hττ : τ' = τ`. Substitute `hττ` using the available equality. Establish `e : compAt θ τ' M = reidx (mR k)` using `hτ`.

Rewrite using `[e, reidx_conjTranspose_mul, hk.2, reidx_one]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h]`.

Establish `e : compAt θ τ' M = 1` using `hτ' τ' hττ`. Rewrite using `[e, Matrix.conjTranspose_one, Matrix.one_mul]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply_ne h]`. Simplify using `only [inv_one, Units.val_one, cT_one, Matrix.mul_one]`. Use extensionality with `i j`. Use `key i j` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`.

Simplify `this` using `only [Matrix.map_apply]`.
-/
theorem iota_mem_K {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n} (hθ : IsInfFam θ) (hι : IsPlaceEmb θ τ ι)
    (k : GR n) (hk : InK (mR k)) : ι k ∈ K D n := by
  obtain ⟨hinf0, hcA, -, -⟩ := GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ
  obtain ⟨-, hcomp⟩ := hι
  obtain ⟨hτ, hτ', hfin⟩ := hcomp k
  rw [K, GlobalTheory.RegSch.EmbLevel.mem_levelAll_iff]
  set M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D) := (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (ι k)).1 with hM
  have hMm : M = mat (ι k) := rfl
  refine ⟨fun v y => ?_, fun w => ?_⟩
  · have h1 : M.map (compFin D.host.F D.host.E v) = 1 := by
      ext i j
      simp only [Matrix.map_apply]
      rw [compFin_eq_finPart]
      have := congrFun (congrFun hfin i) j
      simp only [Matrix.map_apply] at this
      rw [← hMm] at this
      rw [this]
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    rw [h1, Matrix.one_mulVec]
  ·
    have key : ∀ i j, compInf D.host.F D.host.E w
        ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig) M * M) i j - (1 : Matrix (Fin (n + n)) (Fin (n + n)) (AE D)) i j) = 0 := by
      intro i j
      refine ((hinf0 _).2 ?_) w
      intro τ'
      have hc := compAt_cT_mul hθ M τ'
      have hrow : θ τ' (infPart D ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * M) i j)) =
          ((compAt θ τ' M)ᴴ * compAt θ τ' M) i j := congrFun (congrFun hc i) j
      rw [map_sub, map_sub, hrow]
      by_cases hττ : τ' = τ
      · subst hττ
        have e : compAt θ τ' M = reidx (mR k) := hτ
        rw [e, reidx_conjTranspose_mul, hk.2, reidx_one]
        by_cases h : i = j
        · subst h; simp
        · simp [Matrix.one_apply_ne h]
      · have e : compAt θ τ' M = 1 := hτ' τ' hττ
        rw [e, Matrix.conjTranspose_one, Matrix.one_mul]
        by_cases h : i = j
        · subst h; simp
        · simp [Matrix.one_apply_ne h]
    simp only [inv_one, Units.val_one, cT_one, Matrix.mul_one]
    ext i j
    have := key i j
    rw [map_sub, sub_eq_zero] at this
    simpa only [Matrix.map_apply] using this

end PositivityTheory.Rg.Sw.Glob.RhoH

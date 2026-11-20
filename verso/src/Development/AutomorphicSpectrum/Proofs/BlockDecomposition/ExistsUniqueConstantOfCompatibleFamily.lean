import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.USt
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis

/- English proof (translation)
Introduce `hS z hz`. Use `choose e he using bc.bij`. Establish `hpure : ∀ (T : C) (r : TrivSqZeroExt R M) (b : F.obj T), e T (r ⊗ₜ[R] b) = r • bc.α T b`. Introduce `T r b`. Establish `h : (r ⊗ₜ[R] b : TrivSqZeroExt R M ⊗[R] F.obj T) = r • ((1 : TrivSqZeroExt R M) ⊗ₜ[R] b)`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Rewrite using `[h, map_smul, he]`. Establish `hnat : ∀ {T T' : C} (φ : T ⟶ T') (x : TrivSqZeroExt R M ⊗[R] F.obj T), e T' ((mp F φ).toLinearMap.lTensor _ x) = mp F' φ (e T x)`. Introduce `T T' φ x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul r b`. Rewrite using `[LinearMap.lTensor_tmul, hpure, hpure, map_smul]`. Conclude with `congrArg (r • ·) (bc.naturality φ b)`. Consider the case `add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]`.

Set `jj : ∀ T : C, M ⊗[R] F.obj T →ₗ[R] TrivSqZeroExt R M ⊗[R] F.obj T` to `fun T ↦ (TrivSqZeroExt.inrHom R M).rTensor _`. Establish `hsnd : ∀ (T : C) (x : M ⊗[R] F.obj T), (TrivSqZeroExt.sndHom R M).rTensor _ (jj T x) = x`. Introduce `T x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => simp [jj]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `hcomm : ∀ {T T' : C} (φ : T ⟶ T') (x : M ⊗[R] F.obj T), jj T' ((mp F φ).toLinearMap.lTensor M x) = (mp F φ).toLinearMap.lTensor _ (jj T x)`. Introduce `T T' φ x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b => simp [jj]`. Consider the case `add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]`. Establish `hconst : ∀ (T : C) (r : TrivSqZeroExt R M), algebraMap (TrivSqZeroExt R M) (F'.obj T) r = e T (r ⊗ₜ[R] (1 : F.obj T))`. Introduce `T r`.

Rewrite using `[hpure, map_one, Algebra.algebraMap_eq_smul_one]`. Set `w : C0 F'` to `fun T ↦ e T (jj T (z T))`. Establish `hw : d0 F' w = 0`. Use function extensionality and compare the values at `T T' φ`. Rewrite using `[amitsur_d0_apply]`.

Simplify using `only [w, Pi.zero_apply]`. Rewrite using `[← hnat, ← hcomm, ← hz, sub_self]`. Take `⟨r, hr⟩` from `(hS.1 w).1 hw`. Establish `hjjr : ∀ T : C, jj T (z T) = r ⊗ₜ[R] (1 : F.obj T)`. Introduce `T`.

Apply `(e T).injective` to reduce the goal to its premises. Rewrite using `[← hconst]`. Conclude with `(congrFun hr T).symm`. Use `⟨r.snd, fun T ↦ ?_, fun m₂ hm₂ ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[← hsnd T (z T), hjjr T]`.

Simplify using the standard rewrite rules. Establish `h0 : algebraMap (TrivSqZeroExt R M) (C0 F') (TrivSqZeroExt.inr (m₂ - r.snd)) = 0`. Use function extensionality and compare the values at `T`. Establish `hd : (m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T) = 0`. Establish `h1 : z T = r.snd ⊗ₜ[R] (1 : F.obj T)`.

Rewrite using `[← hsnd T (z T), hjjr T]`. Simplify using the standard rewrite rules. Rewrite using `[TensorProduct.sub_tmul, ← hm₂ T, ← h1, sub_self]`. Establish `h2 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) = 0`. Establish `: jj T ((m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T)) = (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T)`.

Simplify using `[jj]`. Rewrite using `[← this, hd, map_zero]`. Express the relevant statement in the definitionally equal form `algebraMap (TrivSqZeroExt R M) (F'.obj T) _ = 0`. Rewrite using `[hconst, h2, map_zero]`. Establish `h3 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) = 0` using `hS.2 (h0.trans (map_zero _).symm)`.

Establish `h4` using `congrArg TrivSqZeroExt.snd h3`. Simplify `h4` using `[sub_eq_zero]`.
-/
theorem existsUnique_const_of_trivSqZeroExt (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (M : Type) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (F' : C ⥤ CommAlgCat.{0} (TrivSqZeroExt R M)) (bc : BC F F') :
    Stein F' → ∀ z : ∀ T : C, M ⊗[R] F.obj T,
      (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
      ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T) := by
  intro hS z hz
  choose e he using bc.bij
  have hpure : ∀ (T : C) (r : TrivSqZeroExt R M) (b : F.obj T), e T (r ⊗ₜ[R] b) = r • bc.α T b := by
    intro T r b
    have h : (r ⊗ₜ[R] b : TrivSqZeroExt R M ⊗[R] F.obj T) = r • ((1 : TrivSqZeroExt R M) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h, map_smul, he]
  have hnat : ∀ {T T' : C} (φ : T ⟶ T') (x : TrivSqZeroExt R M ⊗[R] F.obj T),
      e T' ((mp F φ).toLinearMap.lTensor _ x) = mp F' φ (e T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r b =>
      rw [LinearMap.lTensor_tmul, hpure, hpure, map_smul]
      exact congrArg (r • ·) (bc.naturality φ b)
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  let jj : ∀ T : C, M ⊗[R] F.obj T →ₗ[R] TrivSqZeroExt R M ⊗[R] F.obj T :=
    fun T ↦ (TrivSqZeroExt.inrHom R M).rTensor _
  have hsnd : ∀ (T : C) (x : M ⊗[R] F.obj T),
      (TrivSqZeroExt.sndHom R M).rTensor _ (jj T x) = x := by
    intro T x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcomm : ∀ {T T' : C} (φ : T ⟶ T') (x : M ⊗[R] F.obj T),
      jj T' ((mp F φ).toLinearMap.lTensor M x) = (mp F φ).toLinearMap.lTensor _ (jj T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  have hconst : ∀ (T : C) (r : TrivSqZeroExt R M),
      algebraMap (TrivSqZeroExt R M) (F'.obj T) r = e T (r ⊗ₜ[R] (1 : F.obj T)) := by
    intro T r
    rw [hpure, map_one, Algebra.algebraMap_eq_smul_one]
  let w : C0 F' := fun T ↦ e T (jj T (z T))
  have hw : d0 F' w = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply]
    simp only [w, Pi.zero_apply]
    rw [← hnat, ← hcomm, ← hz, sub_self]
  obtain ⟨r, hr⟩ := (hS.1 w).1 hw
  have hjjr : ∀ T : C, jj T (z T) = r ⊗ₜ[R] (1 : F.obj T) := by
    intro T
    apply (e T).injective
    rw [← hconst]
    exact (congrFun hr T).symm
  refine ⟨r.snd, fun T ↦ ?_, fun m₂ hm₂ ↦ ?_⟩
  · rw [← hsnd T (z T), hjjr T]
    simp
  · have h0 : algebraMap (TrivSqZeroExt R M) (C0 F') (TrivSqZeroExt.inr (m₂ - r.snd)) = 0 := by
      funext T
      have hd : (m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have h1 : z T = r.snd ⊗ₜ[R] (1 : F.obj T) := by
          rw [← hsnd T (z T), hjjr T]
          simp
        rw [TensorProduct.sub_tmul, ← hm₂ T, ← h1, sub_self]
      have h2 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have : jj T ((m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T)) =
            (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) := by
          simp [jj]
        rw [← this, hd, map_zero]
      change algebraMap (TrivSqZeroExt R M) (F'.obj T) _ = 0
      rw [hconst, h2, map_zero]
    have h3 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) = 0 :=
      hS.2 (h0.trans (map_zero _).symm)
    have h4 := congrArg TrivSqZeroExt.snd h3
    simpa [sub_eq_zero] using h4

end GlobalTheory.CompanionTheory.Axis

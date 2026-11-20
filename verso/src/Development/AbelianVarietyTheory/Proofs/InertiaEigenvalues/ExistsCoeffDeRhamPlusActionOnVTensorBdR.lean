import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpDR

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `l _ Pl AI Td LL T`. Set `φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V` to `fun o => { toFun := fun v => (o : ↥LL.1) • v map_add' := fun v w => smul_add _ v w map_smul' := fun q v => by`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul, mul_comm] }`. Set `F : ↥(OL LL) → Per.BdRp l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR)` to `fun o b => TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (cD Td b))`.

Establish `hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (cD Td b * c)` using `fun o b v c => rfl`. Establish `hb : ∀ o b b', F o (b + b') = F o b + F o b'` using `fun o b b' => by`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `v c`. Rewrite using `[LinearMap.add_apply, hF, hF, hF, map_add, add_mul, tmul_add]`.

Establish `ho : ∀ o o' b, F (o + o') b = F o b + F o' b` using `fun o o' b => by`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `v c`. Rewrite using `[LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]`. Set `f : ↥(OL LL) →+ Per.BdRp l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)` to `AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom) (fun b b' => AddMonoidHom.ext fun x => by show F o (b + b') x = F o b x + F o b' x`.

Rewrite using `[hb]`. Use the proof step `rfl))`. Use the proof step `(fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by show F (o + o') b x = F o b x + F o' b x`. Rewrite using `[ho]`. Use the proof step `rfl)`.

Establish `hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdRp l), f (z • o) b = f o (z • b)`. Introduce `z o b`. Apply `AddMonoidHom.ext` to reduce the goal to its premises. Introduce `x`. Use `show F (z • o) b x = F o (z • b) x`.

Use `congr 1`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `v c`. Rewrite using `[hF, hF, Algebra.smul_def z b, map_mul, cD_algebraMap, mul_assoc, ← Algebra.smul_def, ← TensorProduct.smul_tmul (R := ℚ_[l])]`. Use `congr 1`.

Use `show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)`. Rewrite using `[smul_assoc]`. Use `⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩` and prove the remaining obligations. Rewrite using `[TensorProduct.liftAddHom_tmul]`. Both sides reduce to the same expression.
-/
theorem exists_odAction : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI)
    (LL : FinExt l) (T : QLat LL), ∃ A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR),
      A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c) := by
  intro l _ Pl AI Td LL T
  let φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V := fun o =>
    { toFun := fun v => (o : ↥LL.1) • v
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun q v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul,
          mul_comm] }
  let F : ↥(OL LL) → Per.BdRp l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR) := fun o b =>
    TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (cD Td b))
  have hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (cD Td b * c) := fun o b v c => rfl
  have hb : ∀ o b b', F o (b + b') = F o b + F o b' := fun o b b' => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, map_add, add_mul, tmul_add]
  have ho : ∀ o o' b, F (o + o') b = F o b + F o' b := fun o o' b => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]
  let f : ↥(OL LL) →+ Per.BdRp l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
    AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom)
      (fun b b' => AddMonoidHom.ext fun x => by
        show F o (b + b') x = F o b x + F o b' x
        rw [hb]; rfl))
      (fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by
        show F (o + o') b x = F o b x + F o' b x
        rw [ho]; rfl)
  have hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdRp l), f (z • o) b = f o (z • b) := by
    intro z o b
    apply AddMonoidHom.ext
    intro x
    show F (z • o) b x = F o (z • b) x
    congr 1
    apply TensorProduct.ext'
    intro v c
    rw [hF, hF, Algebra.smul_def z b, map_mul, cD_algebraMap, mul_assoc, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul (R := ℚ_[l])]
    congr 1
    show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)
    rw [smul_assoc]
  refine ⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩
  rw [TensorProduct.liftAddHom_tmul]
  rfl

end GlobalTheory.BKGal.JumpDR

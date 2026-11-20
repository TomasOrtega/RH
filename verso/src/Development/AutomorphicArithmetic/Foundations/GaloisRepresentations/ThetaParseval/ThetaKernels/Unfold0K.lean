import Development.WeilBound.ThetaLifts.LatticeBasics.Unfold0
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseUnfoldB

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
variable {χ : Chr F E} {z : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n Y r s hB hY h0 χ e hχ he f Ê z _ _ hs hf μ D hμ hD hi φ hφ h`. Establish `hJ` using `_root_.GlobalTheory.ThK.Dbl.aniso_of_k hB hY h0`. Use `haveI := countable_ratU (σ := σ) (Y := Y)`. Use `haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩`. Use `haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)`.

Take `⟨C, hC⟩` from `hφ.2.2 0`. Set `k : UA σ Y.J → ℂ` to `fun g => f (e (1, g)) * (detInv χ g * φ (h * g))`. Establish `ik : Integrable k μ` using `hi.mul_bdd (c := C) ((continuous_detInv hχ).mul (hφ.1.comp (continuous_const_mul h))).aestronglyMeasurable (.of_forall fun g => by simpa [norm_detInv] using hC (h * g))`. Use `An.unfold hD (ik.comp_mul_left h⁻¹)` as an intermediate fact. Rewrite `this` using `[integral_mul_left_eq_self k]`.

Simplify using `only [mul_assoc]`. Use `Eq.trans (integral_congr_ae (.of_forall fun g => ?_)) this` and prove the remaining obligations. Use `(((Law.hasSum hf hχ hJ he (hs _)).mul_right _).tsum_eq.symm).trans (tsum_congr fun δ => ?_)` and prove the remaining obligations. Simplify using `only [k]`. Rewrite using `[← Law.diag hf hJ he h (e _), ← map_mul, ← map_mul, detInv_mul, detInv_mul, detInv_rat hχ δ.2, mul_inv_cancel_left, hφ.2.1 _ δ.2]`.

Establish `: detInv χ h * detInv χ h⁻¹ = 1` using `by rw [← detInv_mul, mul_inv_cancel, detInv_rat hχ (one_mem _)]`. Simplify using `only [Prod.mk_mul_mk, one_mul, mul_one, mul_inv_cancel_left]`. Take the linear combination `(-(f (e (h, δ * g)) * detInv χ g * φ g)) * this`.
-/
theorem unfold0_k : _root_.GlobalTheory.ThK.Dbl.Unfold0_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0 χ e hχ he f Ê z _ _ hs hf μ D hμ hD hi φ hφ h
  have hJ := _root_.GlobalTheory.ThK.Dbl.aniso_of_k hB hY h0
  haveI := countable_ratU (σ := σ) (Y := Y)
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨C, hC⟩ := hφ.2.2 0
  let k : UA σ Y.J → ℂ := fun g => f (e (1, g)) * (detInv χ g * φ (h * g))
  have ik : Integrable k μ := hi.mul_bdd (c := C)
    ((continuous_detInv hχ).mul (hφ.1.comp (continuous_const_mul h))).aestronglyMeasurable
    (.of_forall fun g => by simpa [norm_detInv] using hC (h * g))
  have := An.unfold hD (ik.comp_mul_left h⁻¹)
  rw [integral_mul_left_eq_self k] at this
  simp only [mul_assoc]
  refine Eq.trans (integral_congr_ae (.of_forall fun g => ?_)) this
  refine (((Law.hasSum hf hχ hJ he (hs _)).mul_right _).tsum_eq.symm).trans (tsum_congr fun δ => ?_)
  simp only [k]
  rw [← Law.diag hf hJ he h (e _), ← map_mul, ← map_mul, detInv_mul, detInv_mul, detInv_rat hχ δ.2, mul_inv_cancel_left, hφ.2.1 _ δ.2]
  have : detInv χ h * detInv χ h⁻¹ = 1 := by rw [← detInv_mul, mul_inv_cancel, detInv_rat hχ (one_mem _)]
  simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_inv_cancel_left]
  linear_combination (-(f (e (h, δ * g)) * detInv χ g * φ g)) * this
end GlobalTheory.ThK.Dbl
end
end

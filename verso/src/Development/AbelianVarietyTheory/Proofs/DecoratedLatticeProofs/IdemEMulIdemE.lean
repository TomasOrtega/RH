import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacUnion

variable {D : D7}

open Classical in

def idemF (v : Pl D) : Af D.host.F :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    show (if w = v then (1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.F w) else 0) ∈ _
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_idemF (v w : Pl D) : evalV D.host.F w (idemF v) = if w = v then 1 else 0 := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (funext fun w => h w)`.
-/
theorem af_ext {x y : Af D.host.F} (h : ∀ w, evalV D.host.F w x = evalV D.host.F w y) : x = y :=
  Subtype.ext (funext fun w => h w)

/- English proof (translation)
Use `show ((0 : Ainf D.host.F) * 0, α * β) = ((0 : Ainf D.host.F), α * β)`. Rewrite using `[mul_zero]`.
-/
theorem pairA_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  show ((0 : Ainf D.host.F) * 0, α * β) = ((0 : Ainf D.host.F), α * β)
  rw [mul_zero]

def idemE (v : Pl D) : AE D := algebraMap (AF D.host.F) (AE D) (pairA _ 0 (idemF v))

/- English proof (translation)
Rewrite using `[idemE, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.algebraMap_self, RingHom.id_apply, pairA_mul]`.
-/
theorem idemE_mul_gen (v : Pl D) (α : Af D.host.F) (x : D.host.E) :
    idemE v * (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = pairA D.host.F 0 (idemF v * α) ⊗ₜ[D.host.F] x := by
  rw [idemE, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.algebraMap_self, RingHom.id_apply, pairA_mul]

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.of_apply, idemE_mul_gen]`.
-/
theorem idemE_smul_gen (v : Pl D) (α : Af D.host.F) (x : Fin T.rank → Fin S.rank → D.host.E) :
    idemE v • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j : WO S T) =
      Matrix.of fun i j => pairA D.host.F 0 (idemF v * α) ⊗ₜ[D.host.F] x i j := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.of_apply, idemE_mul_gen]

/- English proof (translation)
Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩` from `hx`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Establish `hα' : ∀ w, evalV D.host.F w α ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F w` using `hα`.

Establish `hmem : idemF v * α ∈ intAf D.host.F`. Simplify using `only [intAf, Set.mem_setOf_eq]`. Introduce `w`. Rewrite using `[map_mul]`. Use `mul_mem ?_ (hα' w)` and prove the remaining obligations.

Rewrite using `[evalV_idemF]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Use `⟨idemF v * α, hmem, fun w hw => ?_, a, ha, s, hs, t, ht, idemE_smul_gen v α _⟩` and prove the remaining obligations.

Rewrite using `[map_mul, evalV_idemF, if_neg hw, zero_mul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem idemE_smul_mem (v : Pl D) {P : Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    idemE v • u ∈ latO S T LS LT (· = v) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    have hα' : ∀ w, evalV D.host.F w α ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F w := hα
    have hmem : idemF v * α ∈ intAf D.host.F := by
      simp only [intAf, Set.mem_setOf_eq]
      intro w
      rw [map_mul]
      refine mul_mem ?_ (hα' w)
      rw [evalV_idemF]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    refine ⟨idemF v * α, hmem, fun w hw => ?_, a, ha, s, hs, t, ht, idemE_smul_gen v α _⟩
    rw [map_mul, evalV_idemF, if_neg hw, zero_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.VacUnion

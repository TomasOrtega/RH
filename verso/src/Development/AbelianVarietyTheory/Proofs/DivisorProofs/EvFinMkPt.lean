import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.VacLine

variable {F : Type} [Field F] [NumberField F]

def mkPt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

def slice {κ : Type} (Φ : (κ → AF F) → ℂ) (x : κ → mixedEmbedding.mixedSpace F) : (κ → Af F) → ℂ :=
  fun y => Φ (mkPt x y)

def finOp (ψ : AddChar (AF F) ℂ) (v : Pl F) {κ : Type} [Fintype κ] (p : (κ → Fv F v) × (κ → Fv F v))
    (g : (κ → Af F) → ℂ) : (κ → Af F) → ℂ :=
  fun y => psiLoc ψ v ((fun i => evalV F v (y i)) ⬝ᵥ p.2 + p.1 ⬝ᵥ p.2 / 2) * g (y + fun i => singleFin v (p.1 i))

def vacProd {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : (κ → Af F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)

/- English proof (translation)
Simplify using `[mkPt, evI]`.
-/
theorem evI_mkPt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) (i : κ) :
    evI F (mkPt x y i) = x i := by
  simp [mkPt, evI]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evFin_mkPt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) (i : κ) (v : Pl F) :
    evFin F v (mkPt x y i) = evalV F v (y i) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1), (z i).2) = z i`. Rewrite using `[RingEquiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem mkPt_eq {κ : Type} (z : κ → AF F) : mkPt (fun i => evI F (z i)) (fun i => (z i).2) = z := by
  funext i
  show ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1), (z i).2) = z i
  rw [RingEquiv.symm_apply_apply]
  rfl

/- English proof (translation)
Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure vacProd`. Simplify using `only [evI_mkPt, evFin_mkPt]`.
-/
theorem pure_mkPt {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ (mkPt x y) = f x * vacProd φ y := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure vacProd
  simp only [evI_mkPt, evFin_mkPt]

/- English proof (translation)
Proceed by induction on `hγ using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, -, x, -, y, -, rfl⟩` from `hz`. Introduce `u hu`. Rewrite using `[← smul_assoc, ha u hu, zero_smul]`.

Consider the case `zero => intro u _`. Conclude with `smul_zero u`. Consider the case `add z z' _ _ hz hz' => intro u hu`. Rewrite using `[smul_add, hz u hu, hz' u hu, add_zero]`. Consider the case `neg z _ hz => intro u hu`.

Rewrite using `[smul_neg, hz u hu, neg_zero]`.
-/
theorem at_latAtV {E : Type} [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    At (evFin F v) γ := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
    intro u hu
    rw [← smul_assoc, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add z z' _ _ hz hz' => intro u hu; rw [smul_add, hz u hu, hz' u hu, add_zero]
  | neg z _ hz => intro u hu; rw [smul_neg, hz u hu, neg_zero]

end GlobalTheory.VacLine

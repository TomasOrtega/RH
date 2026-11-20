import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotIsobaricRigid
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGenAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerMaps

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne Formalism.CyclotomicNorms

namespace GlobalTheory.LabLaws

section WDLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
The claim follows from `WD.lab_lpTw τ γ a s`.
-/
theorem lab_lpTw (τ : Fbar g →* ℂ) (γ : G E Ω) (a : WD h) (s : ℝ) :
    WD.lab τ γ (a.lpTw s) = WD.lab τ γ a :=
  WD.lab_lpTw τ γ a s

/- English proof (translation)
The claim follows from `WD.natDegree_lab_le τ γ a`.
-/
theorem natDegree_lab_le (τ : Fbar g →* ℂ) (γ : G E Ω) (a : WD h) :
    (WD.lab τ γ a).natDegree ≤ a.lpDim :=
  WD.natDegree_lab_le τ γ a

end WDLaws

section Comparison₂

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def LabTie (T : GlobalTheory.RowTie.WDTie N A) (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ)
    (γ : Fin 2 → PlE H → G H.E N.Om) : Prop :=
  ∀ (k : Fin 2) (v : N.PlG k),
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    IsTeich (τ k) ∧ TameGenAt (N.plOm.1 (A.plGw k v)) (γ k (A.plGw k v)) ∧
      ∀ a : A.LP (A.plGw k v), A.items₂ k (A.plGw k v) a = WD.lab (τ k) (γ k (A.plGw k v)) (T.e _ a)

/- English proof (translation)
Use `⟨fun k v a s => ?_, fun k v a => ?_⟩` and prove the remaining obligations. Use `haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩`. Rewrite using `[(hT k v).2.2, (hT k v).2.2, T.tw, WD.lab_lpTw]`. Use `haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩`. Rewrite using `[(hT k v).2.2, ← T.dim]`.

Conclude with `WD.natDegree_lab_le _ _ _`.
-/
theorem tieLab_of_labTie {T : GlobalTheory.RowTie.WDTie N A} {τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ}
    {γ : Fin 2 → PlE H → G H.E N.Om} (hT : LabTie T τ γ) : GlobalTheory.RowCopy.TieLab N A := by
  refine ⟨fun k v a s => ?_, fun k v a => ?_⟩
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, (hT k v).2.2, T.tw, WD.lab_lpTw]
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, ← T.dim]
    exact WD.natDegree_lab_le _ _ _

/- English proof (translation)
Introduce `k v a ha σ hσ hw`. Use `haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩`. Rewrite `ha` using `[(hT k v).2.2, ← T.dim]`. Rewrite using `[T.inePol _ a σ hσ, ← T.dim]`. Conclude with `WD.inePol_wild_of_natDegree_lab ha hw`.
-/
theorem labTame_of_labTie {T : GlobalTheory.RowTie.WDTie N A} {τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ}
    {γ : Fin 2 → PlE H → G H.E N.Om} (hT : LabTie T τ γ) : GlobalTheory.RowTie.LabTame N A := by
  intro k v a ha σ hσ hw
  haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  rw [(hT k v).2.2, ← T.dim] at ha
  rw [T.inePol _ a σ hσ, ← T.dim]
  exact WD.inePol_wild_of_natDegree_lab ha hw

end Comparison₂

section Inhabited

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

end Inhabited

end GlobalTheory.LabLaws

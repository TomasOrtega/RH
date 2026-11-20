import Mathlib
import Formalism.PeriodIntegrals.ScMuExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousUMatApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HJMulVecGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousHPart
import Formalism.RealPlaceAnalysis.FinalF

noncomputable section

open Matrix
open scoped Pointwise

namespace PI.ScMuExists.UnitaryGroupMassFormula

/- English proof (translation)
The claim follows from `(Formalism.REAL.uJEmb n ε).1`.
-/
theorem isClosedEmbedding_uMat {n : ℕ} (ε : Fin n → Bool) :
    Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  (Formalism.REAL.uJEmb n ε).1

/- English proof (translation)
Introduce `I r e f z hF N H hNs hHs C hC`. Set `K : ∀ v, Set (Matrix (Fin I.n) (Fin I.n) ℂ)` to `fun v => hPart (I.ε v) (fun a => rv I v (e a)) (fun a => rv I v (f a)) (rv I v z) '' ((fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v)) '' C)`. Establish `hK : ∀ v, IsCompact (K v)` using `fun v => (hC.image (continuous_uMat_apply I v)).image (continuous_hPart _ _ _ _)`. Set `K2 : Set I.Ginf` to `Set.univ.pi fun v => (fun g : Formalism.REAL.UJ (I.ε v) => Formalism.MainNotions.S.uMat g) ⁻¹' K v`. Establish `hK2 : IsCompact K2` using `isCompact_univ_pi fun v => (isClosedEmbedding_uMat (I.ε v)).isCompact_preimage (hK v)`.

Establish `hsub : {p : I.Ginf × I.Ginf | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C} ⊆ (C * K2⁻¹) ×ˢ K2`. Introduce and unpack `⟨x, h⟩ ⟨hx, hh, hxh⟩`. Establish `hx' : x ∈ Ninf I e z` using `by rw [← hNs]; exact hx`. Establish `hh' : h ∈ Hset I (frameSet I e f z)` using `by rw [← hHs]; exact hh`. Establish `hK2h : h ∈ K2`.

Introduce `v _`. Use `⟨Formalism.MainNotions.S.uMat ((x * h) v), ⟨x * h, hxh, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show hPart _ _ _ _ (Formalism.MainNotions.S.uMat (x v * h v)) = Formalism.MainNotions.S.uMat (h v)`. Rewrite using `[uMat_mul]`. Conclude with `hPart_mul (rFrame_of hF v) (hx' v) (uMat_inUJ (h v)) (fun a => hh' v _ (Or.inl (Or.inl ⟨a, rfl⟩))) (fun a => hh' v _ (Or.inl (Or.inr ⟨a, rfl⟩))) (hh' v _ (Or.inr rfl))`.

Use `⟨?_, hK2h⟩` and prove the remaining obligations. Rewrite using `[← mul_inv_cancel_right x h]`. Conclude with `Set.mul_mem_mul hxh (Set.inv_mem_inv.mpr hK2h)`. Establish `hcl : IsClosed {p : I.Ginf × I.Ginf | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C}`. Establish `hNc : IsClosed (N : Set I.Ginf)` using `by rw [hNs]; exact isClosed_Ninf I e z`.

Establish `hHc : IsClosed (H : Set I.Ginf)` using `by rw [hHs]; exact isClosed_Hset I _`. Conclude with `(hNc.preimage continuous_fst).inter ((hHc.preimage continuous_snd).inter (hC.isClosed.preimage continuous_mul))`. Conclude with `((hC.mul hK2.inv).prod hK2).of_isClosed_subset hcl hsub`.
-/
theorem proper_action_instance : InstProper := by
  intro I r e f z hF N H hNs hHs C hC
  let K : ∀ v, Set (Matrix (Fin I.n) (Fin I.n) ℂ) := fun v =>
    hPart (I.ε v) (fun a => rv I v (e a)) (fun a => rv I v (f a)) (rv I v z) ''
      ((fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v)) '' C)
  have hK : ∀ v, IsCompact (K v) := fun v =>
    (hC.image (continuous_uMat_apply I v)).image (continuous_hPart _ _ _ _)
  let K2 : Set I.Ginf := Set.univ.pi fun v => (fun g : Formalism.REAL.UJ (I.ε v) => Formalism.MainNotions.S.uMat g) ⁻¹' K v
  have hK2 : IsCompact K2 :=
    isCompact_univ_pi fun v => (isClosedEmbedding_uMat (I.ε v)).isCompact_preimage (hK v)
  have hsub : {p : I.Ginf × I.Ginf | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C} ⊆ (C * K2⁻¹) ×ˢ K2 := by
    rintro ⟨x, h⟩ ⟨hx, hh, hxh⟩
    have hx' : x ∈ Ninf I e z := by rw [← hNs]; exact hx
    have hh' : h ∈ Hset I (frameSet I e f z) := by rw [← hHs]; exact hh
    have hK2h : h ∈ K2 := by
      intro v _
      refine ⟨Formalism.MainNotions.S.uMat ((x * h) v), ⟨x * h, hxh, rfl⟩, ?_⟩
      show hPart _ _ _ _ (Formalism.MainNotions.S.uMat (x v * h v)) = Formalism.MainNotions.S.uMat (h v)
      rw [uMat_mul]
      exact hPart_mul (rFrame_of hF v) (hx' v) (uMat_inUJ (h v))
        (fun a => hh' v _ (Or.inl (Or.inl ⟨a, rfl⟩))) (fun a => hh' v _ (Or.inl (Or.inr ⟨a, rfl⟩)))
        (hh' v _ (Or.inr rfl))
    refine ⟨?_, hK2h⟩
    rw [← mul_inv_cancel_right x h]
    exact Set.mul_mem_mul hxh (Set.inv_mem_inv.mpr hK2h)
  have hcl : IsClosed {p : I.Ginf × I.Ginf | p.1 ∈ N ∧ p.2 ∈ H ∧ p.1 * p.2 ∈ C} := by
    have hNc : IsClosed (N : Set I.Ginf) := by rw [hNs]; exact isClosed_Ninf I e z
    have hHc : IsClosed (H : Set I.Ginf) := by rw [hHs]; exact isClosed_Hset I _
    exact (hNc.preimage continuous_fst).inter ((hHc.preimage continuous_snd).inter
      (hC.isClosed.preimage continuous_mul))
  exact ((hC.mul hK2.inv).prod hK2).of_isClosed_subset hcl hsub

end PI.ScMuExists.UnitaryGroupMassFormula

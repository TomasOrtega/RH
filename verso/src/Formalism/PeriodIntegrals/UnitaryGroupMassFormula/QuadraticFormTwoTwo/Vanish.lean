import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.CbStrictMonoOfAnti

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Proceed by induction on `f using DirectSum.induction_on with`. Consider the case `zero => simp`. Consider the case `of i y`. Rewrite using `[DirectSum.coeAddMonoidHom_of, hL i y y.2]`. Express the relevant statement in the definitionally equal form `_ = DirectSum.coeAddMonoidHom S (DFinsupp.mapRange _ (fun j => map_zero _) (DFinsupp.single (β := fun j => S j) i y))`.

Rewrite using `[DFinsupp.mapRange_single]`. Express the relevant statement in the definitionally equal form `_ = DirectSum.coeAddMonoidHom S (DirectSum.of (fun j => S j) i _)`. Rewrite using `[DirectSum.coeAddMonoidHom_of]`. Both sides reduce to the same expression. Consider the case `add f g hf hg => simp only [map_add, hf, hg]`.
-/
private theorem linearMap_coeAddMonoidHom_eq_mapRange_smul {ι : Type*} [DecidableEq ι] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (S : ι → Submodule ℂ W) (L : W →ₗ[ℂ] W) (a : ι → ℂ) (hL : ∀ i, ∀ y ∈ S i, L y = a i • y)
    (f : DirectSum ι (fun i => S i)) :
    L (DirectSum.coeAddMonoidHom S f) = DirectSum.coeAddMonoidHom S
      (DFinsupp.mapRange.addMonoidHom (fun i => DistribSMul.toAddMonoidHom (S i) (a i)) f) := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of i y =>
    rw [DirectSum.coeAddMonoidHom_of, hL i y y.2]
    change _ = DirectSum.coeAddMonoidHom S
      (DFinsupp.mapRange _ (fun j => map_zero _) (DFinsupp.single (β := fun j => S j) i y))
    rw [DFinsupp.mapRange_single]
    change _ = DirectSum.coeAddMonoidHom S (DirectSum.of (fun j => S j) i _)
    rw [DirectSum.coeAddMonoidHom_of]
    rfl
  | add f g hf hg => simp only [map_add, hf, hg]

/- English proof (translation)
Take `⟨S, hS, -, hcap⟩` from `hBr Wp (Pq P) (Pq_OK hP) rfl z e π hz hT hπ he hez hee`. Take `⟨d, hd⟩` from `hS.2 x`. Choose the witnesses or unpack the hypotheses as in `⟨ρ, hρ⟩ : ∃ ρ, d ρ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hx (by rw [← hd, show d = 0 from DFinsupp.ext h, map_zero])`. Use `⟨ρ, fun Y => ?_⟩` and prove the remaining obligations. Establish `hw : Y + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Y` using `add_sub_cancel_right _ _`. Establish `h1` using `linearMap_coeAddMonoidHom_eq_mapRange_smul S (IsLinearMap.mk' _ (hlin (Y + ((P.k : ℂ) - 2) / 2))) (fun σ => M.xC (Pq P) σ Y) (fun σ y hy => (hcap Bs hBs σ _ y hy).trans (congrArg (fun t => M.xC (Pq P) σ t • y) hw)) d`. Establish `h2` using `linearMap_coeAddMonoidHom_eq_mapRange_smul S (μ Y • LinearMap.id) (fun _ => μ Y) (fun _ _ _ => rfl) d`.

Establish `h3 : (DFinsupp.mapRange.addMonoidHom fun i => DistribSMul.toAddMonoidHom (S i) (M.xC (Pq P) i Y)) d = (DFinsupp.mapRange.addMonoidHom fun i => DistribSMul.toAddMonoidHom (S i) (μ Y)) d` using `hS.1 (by`. Rewrite using `[← h1, ← h2, hd]`. Simplify `hμ (Y + ((P.k : ℂ) - 2) / 2))` using `[hw]`. Establish `h4` using `congrArg (fun f => f ρ) h3`. Simplify using `only [DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_apply, DistribSMul.toAddMonoidHom_apply] at h4`.

Conclude with `(smul_left_injective ℂ hρ h4).symm`.
-/
theorem vanish_match (hBr : Branching) {P : M.Par} (hP : P.OK) {Wp : Type} [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
    (hz : inWb P.k P.r z) (hT : 0 < Tz P.k P.r z) (hπ : IsType P.k P.r z π P.u)
    {e : Fin (2 * P.r + P.k + 1) → ℂ} (he : inWb P.k P.r e) (hez : herm (Hpk P.k P.r) e z = 0)
    (hee : herm (Hpk P.k P.r) e e = 1) (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (hBs : IsFrameOf P.k P.r [z, e] Bs) (hlin : ∀ w : ℂ, IsLinearMap ℂ (capRep P.k P.r π Bs w))
    {x : Wp} (hx : x ≠ 0) (μ : ℂ → ℂ) (hμ : ∀ w : ℂ, capRep P.k P.r π Bs w x = μ (w - ((P.k : ℂ) - 2) / 2) • x) :
    ∃ ρ : M.Ty (Pq P), ∀ Y : ℂ, μ Y = M.xC (Pq P) ρ Y := by
  obtain ⟨S, hS, -, hcap⟩ := hBr Wp (Pq P) (Pq_OK hP) rfl z e π hz hT hπ he hez hee
  obtain ⟨d, hd⟩ := hS.2 x
  obtain ⟨ρ, hρ⟩ : ∃ ρ, d ρ ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by rw [← hd, show d = 0 from DFinsupp.ext h, map_zero])
  refine ⟨ρ, fun Y => ?_⟩
  have hw : Y + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Y := add_sub_cancel_right _ _
  have h1 := linearMap_coeAddMonoidHom_eq_mapRange_smul S (IsLinearMap.mk' _ (hlin (Y + ((P.k : ℂ) - 2) / 2)))
    (fun σ => M.xC (Pq P) σ Y)
    (fun σ y hy => (hcap Bs hBs σ _ y hy).trans (congrArg (fun t => M.xC (Pq P) σ t • y) hw)) d
  have h2 := linearMap_coeAddMonoidHom_eq_mapRange_smul S (μ Y • LinearMap.id) (fun _ => μ Y) (fun _ _ _ => rfl) d
  have h3 : (DFinsupp.mapRange.addMonoidHom fun i =>
        DistribSMul.toAddMonoidHom (S i) (M.xC (Pq P) i Y)) d =
      (DFinsupp.mapRange.addMonoidHom fun i => DistribSMul.toAddMonoidHom (S i) (μ Y)) d :=
    hS.1 (by
      rw [← h1, ← h2, hd]
      simpa [hw] using hμ (Y + ((P.k : ℂ) - 2) / 2))
  have h4 := congrArg (fun f => f ρ) h3
  simp only [DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_apply,
    DistribSMul.toAddMonoidHom_apply] at h4
  exact (smul_left_injective ℂ hρ h4).symm

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

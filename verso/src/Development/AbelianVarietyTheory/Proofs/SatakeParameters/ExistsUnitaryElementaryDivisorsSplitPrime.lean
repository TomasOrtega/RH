import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitExist

/- English proof (translation)
Establish `key : ∀ y z : Fin n → R, ε • y = ε • B *ᵥ z → ε • M *ᵥ y = ε • B *ᵥ (fun i => u i * z i)`. Introduce `y z hyz`. Establish `e1 : (fun i => u i * z i) = Matrix.diagonal u *ᵥ z`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec_diagonal]`.

Establish `e2 : ε • (C *ᵥ (B *ᵥ z)) = ε • z`. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, hCB, Matrix.smul_mulVec, Matrix.one_mulVec]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hM, Matrix.smul_mulVec, Matrix.mulVec_smul]`. Use `_ = (B * Matrix.diagonal u) *ᵥ (ε • (C *ᵥ (B *ᵥ z))) := by`.

Rewrite using `[hyz, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Use `_ = ε • B *ᵥ (fun i => u i * z i) := by`. Rewrite using `[e2, e1, Matrix.mulVec_smul, Matrix.mulVec_mulVec]`. Use `⟨B, h1, h2, fun y hy => ?_, fun z hz => ⟨ε • B *ᵥ z, h1 z hz, key _ _ ?_⟩⟩` and prove the remaining obligations. Take `⟨z, hz, e⟩` from `h2 y hy`.

Conclude with `⟨z, hz, key y z e⟩`. Rewrite using `[smul_smul, hε]`.
-/
theorem dv_of_conj {R : Type} [CommRing R] {n : ℕ} {Λ : (Fin n → R) → Prop} {O : R → Prop} {ε : R}
    (hε : ε * ε = ε) {B C M : Matrix (Fin n) (Fin n) R} {u : Fin n → R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B *ᵥ z)
    (hCB : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R))
    (hM : ε • M = ε • (B * Matrix.diagonal u * C)) :
    GlobalTheory.DivDual.Dv Λ O ε u M := by
  have key : ∀ y z : Fin n → R, ε • y = ε • B *ᵥ z →
      ε • M *ᵥ y = ε • B *ᵥ (fun i => u i * z i) := by
    intro y z hyz
    have e1 : (fun i => u i * z i) = Matrix.diagonal u *ᵥ z := by
      funext i; simp [Matrix.mulVec_diagonal]
    have e2 : ε • (C *ᵥ (B *ᵥ z)) = ε • z := by
      rw [Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, hCB, Matrix.smul_mulVec, Matrix.one_mulVec]
    calc ε • M *ᵥ y = (ε • M) *ᵥ y := (Matrix.smul_mulVec _ _ _).symm
      _ = (B * Matrix.diagonal u * C) *ᵥ (ε • y) := by
          rw [hM, Matrix.smul_mulVec, Matrix.mulVec_smul]
      _ = (B * Matrix.diagonal u) *ᵥ (ε • (C *ᵥ (B *ᵥ z))) := by
          rw [hyz, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
            Matrix.mulVec_mulVec]
      _ = ε • B *ᵥ (fun i => u i * z i) := by
          rw [e2, e1, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  refine ⟨B, h1, h2, fun y hy => ?_, fun z hz => ⟨ε • B *ᵥ z, h1 z hz, key _ _ ?_⟩⟩
  · obtain ⟨z, hz, e⟩ := h2 y hy
    exact ⟨z, hz, key y z e⟩
  · rw [smul_smul, hε]

end GlobalTheory.SplitExist

namespace GlobalTheory.SplitExist

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D V P e ϖ d hI h1 h2 hd`. Establish `he : e * e = e` using `hI.1.1`. Establish `hee : finPart D e * finPart D e = finPart D e` using `by rw [← RingHom.map_mul, he]`. Take `⟨B, b1, b2⟩` from `GlobalTheory.SphLabelOps.exists_basis V he hI.2`. Take `⟨C, c1, c2⟩` from `(GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2`.

Establish `hϖ : (ϖ : D.host.E) ≠ 0` using `fun h0 => h2 (by`. Establish `: ϖ = 0` using `by exact_mod_cast h0`. Rewrite using `[this]`. Conclude with `zero_mem _)`. Set `u : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E` to `fun i => finPart D (incA D ((ϖ : D.host.E) ^ (d.getD i.1 0)))`.

Set `u' : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E` to `fun i => finPart D (incA D ((ϖ : D.host.E) ^ (-(d.getD i.1 0))))`. Establish `huu : Matrix.diagonal u * Matrix.diagonal u' = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `only [u, u', ← map_mul, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero, map_one]`. Establish `key : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), finPart D e • (X * (C * B) * Y) = finPart D e • (X * Y)` using `fun X Y => by`. Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul, c2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`. Establish `hmm : finPart D e • ((B * Matrix.diagonal u * C) * (B * Matrix.diagonal u' * C)) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))`. Establish `: (B * Matrix.diagonal u * C) * (B * Matrix.diagonal u' * C) = (B * Matrix.diagonal u) * (C * B) * (Matrix.diagonal u' * C)`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, key, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal u), huu, Matrix.one_mul, c1]`. Take `⟨g, hg, hgm⟩` from `GlobalTheory.SplitLift.split_lift V e hI.1 _ _ hmm`. Conclude with `⟨g, fun i j => hg i j, (GlobalTheory.DivDual.divAt_iff V e _ d g).2 ⟨hd, dv_of_conj hee b1 b2 c2 hgm⟩⟩`.
-/
theorem split_exist : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D)
    (ϖ : 𝓞 D.host.E) (d : List ℤ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    d.length = V.rank → ∃ g : GA D V, SuppF V (e + cA D e) g ∧ DivAt V e (ϖ : D.host.E) d g := by
  intro D V P e ϖ d hI h1 h2 hd
  have he : e * e = e := hI.1.1
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  obtain ⟨B, b1, b2⟩ := GlobalTheory.SphLabelOps.exists_basis V he hI.2
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have hϖ : (ϖ : D.host.E) ≠ 0 := fun h0 => h2 (by
    have : ϖ = 0 := by exact_mod_cast h0
    rw [this]; exact zero_mem _)
  let u : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun i => finPart D (incA D ((ϖ : D.host.E) ^ (d.getD i.1 0)))
  let u' : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun i => finPart D (incA D ((ϖ : D.host.E) ^ (-(d.getD i.1 0))))
  have huu : Matrix.diagonal u * Matrix.diagonal u' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [u, u', ← map_mul, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero, map_one]
  have key : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * (C * B) * Y) = finPart D e • (X * Y) := fun X Y => by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, c2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hmm : finPart D e • ((B * Matrix.diagonal u * C) * (B * Matrix.diagonal u' * C)) =
      finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
    have : (B * Matrix.diagonal u * C) * (B * Matrix.diagonal u' * C) =
        (B * Matrix.diagonal u) * (C * B) * (Matrix.diagonal u' * C) := by
      simp only [Matrix.mul_assoc]
    rw [this, key, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal u), huu, Matrix.one_mul, c1]
  obtain ⟨g, hg, hgm⟩ := GlobalTheory.SplitLift.split_lift V e hI.1 _ _ hmm
  exact ⟨g, fun i j => hg i j, (GlobalTheory.DivDual.divAt_iff V e _ d g).2 ⟨hd, dv_of_conj hee b1 b2 c2 hgm⟩⟩

end GlobalTheory.SplitExist

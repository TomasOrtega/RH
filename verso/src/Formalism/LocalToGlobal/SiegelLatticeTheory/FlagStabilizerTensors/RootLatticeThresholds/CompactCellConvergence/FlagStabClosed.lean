import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.OrbitIdentity
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.C2

variable {k r : ℕ}

/- English proof (translation)
Establish `h1 : IsClosed {l : Matrix (Fin m) (Fin m) ℂ | ∀ i j, i < j → l i j = 0}`. Simplify using `only [Set.ofPred_forall]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const`. Establish `h2 : IsClosed {l : Matrix (Fin m) (Fin m) ℂ | ∀ i, l i i = 1}`. Simplify using `only [Set.ofPred_forall]`.

Conclude with `isClosed_iInter fun i => isClosed_eq ((continuous_apply i).comp (continuous_apply i)) continuous_const`. Conclude with `h1.inter h2`.
-/
theorem ltset_closed (m : ℕ) : IsClosed (LTset m) := by
  have h1 : IsClosed {l : Matrix (Fin m) (Fin m) ℂ | ∀ i j, i < j → l i j = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  have h2 : IsClosed {l : Matrix (Fin m) (Fin m) ℂ | ∀ i, l i i = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq ((continuous_apply i).comp (continuous_apply i)) continuous_const
  exact h1.inter h2

/- English proof (translation)
Establish `hc : Continuous (fun l : Matrix (Fin m) (Fin m) ℂ => P⁻¹ * l * P)` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Conclude with `(ltset_closed m).inter ((ltset_closed m).preimage hc)`.
-/
theorem lpg_closed {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) : IsClosed (LPg P) := by
  have hc : Continuous (fun l : Matrix (Fin m) (Fin m) ℂ => P⁻¹ * l * P) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact (ltset_closed m).inter ((ltset_closed m).preimage hc)

/- English proof (translation)
Establish `hG : IsClosed (Formalism.FourierDecayAlt.B.GV k r)` using `(Formalism.FourierDecayAlt.P.unitary_group_closed k r).closed`. Establish `hF : IsClosed {s : Formalism.FourierDecayAlt.B.Mat k r | ∀ a, s *ᵥ fvec k r z a - fvec k r z a ∈ flagSpan k r z a}`. Simplify using `only [Set.ofPred_forall]`. Conclude with `isClosed_iInter fun a => (Submodule.closed_of_finiteDimensional (flagSpan k r z a)).preimage ((continuous_id.matrix_mulVec continuous_const).sub continuous_const)`. Conclude with `hG.inter hF`.
-/
theorem flagStab_closed (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (FlagStab k r z) := by
  have hG : IsClosed (Formalism.FourierDecayAlt.B.GV k r) := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).closed
  have hF : IsClosed {s : Formalism.FourierDecayAlt.B.Mat k r |
      ∀ a, s *ᵥ fvec k r z a - fvec k r z a ∈ flagSpan k r z a} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => (Submodule.closed_of_finiteDimensional (flagSpan k r z a)).preimage
      ((continuous_id.matrix_mulVec continuous_const).sub continuous_const)
  exact hG.inter hF

/- English proof (translation)
Rewrite using `[← Formalism.FourierDecayAlt.P.standard_flag_property k r z hz]`. Conclude with `flagStab_closed z`.
-/
theorem sset_closed (z : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z) : IsClosed (Sset k r z) := by
  rw [← Formalism.FourierDecayAlt.P.standard_flag_property k r z hz]
  exact flagStab_closed z

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Unfold `uMap herm`. Use `split_ifs`. Conclude with `continuous_const.dotProduct (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))`. Conclude with `(continuous_const.dotProduct (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))).div_const _`.
-/
theorem uMap_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous (uMap k r z) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold uMap herm
  split_ifs
  · exact continuous_const.dotProduct (continuous_const.matrix_mulVec
      (continuous_id.matrix_mulVec continuous_const))
  · exact (continuous_const.dotProduct (continuous_const.matrix_mulVec
      (continuous_id.matrix_mulVec continuous_const))).div_const _

def SgS (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {s | s ∈ Sset k r z ∧ (uMap k r z s)ᴴ ∈ LPg (Formalism.QuantumDeterminants.Zhat k r z z' γ)}

/- English proof (translation)
The claim follows from `(sset_closed z hz).inter ((lpg_closed _).preimage ((uMap_cont z).matrix_conjTranspose))`.
-/
theorem sgS_closed (z z' : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : IsClosed (SgS k r z z' γ) :=
  (sset_closed z hz).inter ((lpg_closed _).preimage ((uMap_cont z).matrix_conjTranspose))

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, ⟨WeylGroupFacts.uh_one, fun a => by simp, by simp⟩, n, hn, by simp⟩`.
-/
theorem n_in_sset (z : Fin (2 * r + k + 1) → ℂ) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨WeylGroupFacts.uh_one, fun a => by simp, by simp⟩, n, hn, by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, hh, 1, WeylGroupFacts.mem_n_one, by simp⟩`.
-/
theorem uw_in_sset (z : Fin (2 * r + k + 1) → ℂ) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, WeylGroupFacts.mem_n_one, by simp⟩

/- English proof (translation)
Establish `hU` using `Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz`. Establish `hT` using `Formalism.FourierDecayAlt.P.c2_tau_mem k r z hz`. Establish `hSG` using `Formalism.QuantumDeterminants.symmetric_group_holds k r z hz.1`. Use extensionality with `s`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨n0, hn0, v, hv, hvL, h, hh, rfl⟩`. Take `⟨hτN, -, hτu⟩` from `hT v hv`. Establish `h1 : n0 ∈ Sset k r z` using `n_in_sset z hn0.1`. Establish `h2 : tauM k r z v ∈ Sset k r z` using `n_in_sset z hτN`. Establish `h3 : h ∈ Sset k r z` using `uw_in_sset z hh`.

Use `⟨hSG.2.1 _ (hSG.2.1 _ h1 _ h2) _ h3, ?_⟩` and prove the remaining obligations. Rewrite using `[(hU.1 _ (hSG.2.1 _ h1 _ h2)).2.2 _ h3, (hU.1 _ h1).2.2 _ h2, hn0.2, hτu, hU.2 h hh]`. Simplify using `using hvL`. Introduce and unpack `⟨hs, hsL⟩`. Take `⟨h, hh, m, hm, rfl⟩` from `hs`.

Establish `hhU : IsUnit h.det` using `WeylGroupFacts.isUnit_of_uh hh.1`. Establish `hn : h * m * h⁻¹ ∈ Nset k r` using `(Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz.1 h hh m hm).1`. Use `set v := uMap k r z (h * m) with hvdef`. Establish `hS : h * m ∈ Sset k r z` using `⟨h, hh, m, hm, rfl⟩`. Establish `hv : v ∈ UTset (r + 1)` using `(hU.1 _ hS).2.1`.

Take `⟨hτN, -, hτu⟩` from `hT v hv`. Establish `hτU : IsUnit (tauM k r z v).det` using `WeylGroupFacts.isUnit_of_uh hτN.1`. Establish `hτi : (tauM k r z v)⁻¹ ∈ Nset k r` using `WeylGroupFacts.mem_n_inv hτN`. Establish `hn0 : h * m * h⁻¹ * (tauM k r z v)⁻¹ ∈ Nset k r` using `WeylGroupFacts.mem_n_mul hn hτi`. Establish `hmul : ∀ a ∈ Sset k r z, ∀ b ∈ Sset k r z, uMap k r z (a * b) = uMap k r z a * uMap k r z b` using `fun a ha b hb => (hU.1 a ha).2.2 b hb`.

Establish `hsplit : h * m = h * m * h⁻¹ * h`. Rewrite using `[Matrix.mul_assoc (h * m), Matrix.nonsing_inv_mul _ hhU, Matrix.mul_one]`. Establish `hun : uMap k r z (h * m * h⁻¹) = v`. Use `hmul _ (n_in_sset z hn) _ (uw_in_sset z hh)` as an intermediate fact. Rewrite `this` using `[← hsplit, hU.2 h hh, Matrix.mul_one]`.

Conclude with `this.symm`. Establish `hone : uMap k r z 1 = 1` using `hU.2 1 ⟨WeylGroupFacts.uh_one, fun a => by simp, by simp⟩`. Establish `huinv : uMap k r z (h * m * h⁻¹ * (tauM k r z v)⁻¹) = 1`. Establish `e1` using `hmul _ (n_in_sset z hn) _ (n_in_sset z hτi)`. Establish `e2` using `hmul _ (n_in_sset z hτN) _ (n_in_sset z hτi)`.

Rewrite `e2` using `[Matrix.mul_nonsing_inv _ hτU, hone, hτu]`. Rewrite using `[e1, hun]`. Conclude with `e2.symm`. Use `⟨_, ⟨hn0, huinv⟩, v, hv, by simpa using hsL, h, hh, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc (h * m * h⁻¹), Matrix.nonsing_inv_mul _ hτU, Matrix.mul_one, ← hsplit]`.
-/
theorem sg_eq (z z' : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Sg k r z z' γ = SgS k r z z' γ := by
  have hU := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have hT := Formalism.FourierDecayAlt.P.c2_tau_mem k r z hz
  have hSG := Formalism.QuantumDeterminants.symmetric_group_holds k r z hz.1
  ext s
  constructor
  · rintro ⟨n0, hn0, v, hv, hvL, h, hh, rfl⟩
    obtain ⟨hτN, -, hτu⟩ := hT v hv
    have h1 : n0 ∈ Sset k r z := n_in_sset z hn0.1
    have h2 : tauM k r z v ∈ Sset k r z := n_in_sset z hτN
    have h3 : h ∈ Sset k r z := uw_in_sset z hh
    refine ⟨hSG.2.1 _ (hSG.2.1 _ h1 _ h2) _ h3, ?_⟩
    rw [(hU.1 _ (hSG.2.1 _ h1 _ h2)).2.2 _ h3, (hU.1 _ h1).2.2 _ h2, hn0.2, hτu, hU.2 h hh]
    simpa using hvL
  · rintro ⟨hs, hsL⟩
    obtain ⟨h, hh, m, hm, rfl⟩ := hs
    have hhU : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hh.1
    have hn : h * m * h⁻¹ ∈ Nset k r := (Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz.1 h hh m hm).1
    set v := uMap k r z (h * m) with hvdef
    have hS : h * m ∈ Sset k r z := ⟨h, hh, m, hm, rfl⟩
    have hv : v ∈ UTset (r + 1) := (hU.1 _ hS).2.1
    obtain ⟨hτN, -, hτu⟩ := hT v hv
    have hτU : IsUnit (tauM k r z v).det := WeylGroupFacts.isUnit_of_uh hτN.1
    have hτi : (tauM k r z v)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv hτN
    have hn0 : h * m * h⁻¹ * (tauM k r z v)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_mul hn hτi
    have hmul : ∀ a ∈ Sset k r z, ∀ b ∈ Sset k r z, uMap k r z (a * b) = uMap k r z a * uMap k r z b :=
      fun a ha b hb => (hU.1 a ha).2.2 b hb
    have hsplit : h * m = h * m * h⁻¹ * h := by
      rw [Matrix.mul_assoc (h * m), Matrix.nonsing_inv_mul _ hhU, Matrix.mul_one]
    have hun : uMap k r z (h * m * h⁻¹) = v := by
      have := hmul _ (n_in_sset z hn) _ (uw_in_sset z hh)
      rw [← hsplit, hU.2 h hh, Matrix.mul_one] at this
      exact this.symm
    have hone : uMap k r z 1 = 1 := hU.2 1 ⟨WeylGroupFacts.uh_one, fun a => by simp, by simp⟩
    have huinv : uMap k r z (h * m * h⁻¹ * (tauM k r z v)⁻¹) = 1 := by
      have e1 := hmul _ (n_in_sset z hn) _ (n_in_sset z hτi)
      have e2 := hmul _ (n_in_sset z hτN) _ (n_in_sset z hτi)
      rw [Matrix.mul_nonsing_inv _ hτU, hone, hτu] at e2
      rw [e1, hun]; exact e2.symm
    refine ⟨_, ⟨hn0, huinv⟩, v, hv, by simpa using hsL, h, hh, ?_⟩
    rw [Matrix.mul_assoc (h * m * h⁻¹), Matrix.nonsing_inv_mul _ hτU, Matrix.mul_one, ← hsplit]

end Formalism.MainNotions.S.Pv.AmpDDPf.CC

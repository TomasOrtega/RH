import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterCommutatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionInvariantHeisenbergWeylStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentAdditiveLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftConjHeisenbergStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

/- English proof (translation)
Introduce `D n ρ p hn M m ψ hψ b₀ χ s f hf η z x h`. Take `⟨hadd, hnorm, -, -⟩` from `GlobalTheory.T.centre_character_properties ψ hψ b₀`. Establish `hjc` using `GlobalTheory.T.centre_character_commutator ψ b₀ η x`. Establish `hsh` using `GlobalTheory.T.shift_conj_heisenberg M η z x`. Establish `hmul` using `GlobalTheory.T.unipotent_heisenberg_mul M`.

Establish `hw` using `GlobalTheory.T.section_invariant_heisenberg_weyl M χ s f hf`. Establish `e1 : M.sh η * (M.nzx z x * h) = M.nzx (z + jc η x) x * (M.sh η * h)`. Rewrite using `[← mul_assoc, hsh, mul_assoc]`. Rewrite using `[e1]`. Generalize the expression as in `M.sh η * h = h'`.

Establish `hc : chz ψ b₀ z * chv ψ b₀ x η = chz ψ b₀ (z + jc η x)` using `by rw [hadd, hjc]`. Rewrite using `[hc]`. Generalize the expression as in `z + jc η x = c`. Establish `hcc : chz ψ b₀ c * conj (chz ψ b₀ c) = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm c]`.

Simplify using the standard rewrite rules. Establish `hconj : ∀ t, conj (chz ψ b₀ t) = conj (chz ψ b₀ (t + c)) * chz ψ b₀ c`. Introduce `t`. Establish `hh : conj (chz ψ b₀ (t + c)) * chz ψ b₀ c = conj (chz ψ b₀ t) * (chz ψ b₀ c * conj (chz ψ b₀ c))`. Rewrite using `[hadd, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hh, hcc, mul_one]`. Establish `hpt : ∀ t : hermA D ρ, f (M.w * M.nzx t 0 * (M.nzx c x * h')) = f (M.w * M.nzx (t + c) 0 * h')`. Introduce `t`. Establish `e2 : M.w * M.nzx t 0 * (M.nzx c x * h') = M.w * M.nzx 0 x * (M.nzx (t + c) 0 * h')`.

Establish `a1 : M.nzx t 0 * M.nzx c x = M.nzx 0 x * M.nzx (t + c) 0`. Rewrite using `[hmul, hmul]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`.

Use `_ = M.w * M.nzx 0 x * (M.nzx (t + c) 0 * h') := by`. Rewrite using `[a1]`. Simplify using `only [mul_assoc]`. Rewrite using `[e2, hw, mul_assoc]`. Use `haveI := m.hz.1`.

Use `haveI : ContinuousAdd (hermA D ρ) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)) _⟩`. Use `haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩`. Use `haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _`. Use `haveI : MeasurableAdd (hermA D ρ) := ContinuousAdd.measurableAdd`. Unfold `Wz`.

Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Use `show f (M.w * M.nzx t 0 * (M.nzx c x * h')) * conj (chz ψ b₀ t) = f (M.w * M.nzx (t + c) 0 * h') * (conj (chz ψ b₀ (t + c)) * chz ψ b₀ c)`. Rewrite using `[hpt, ← hconj]`. Use `_ = ∫ u, f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c) ∂m.lz := integral_add_right_eq_self (μ := m.lz) (fun u => f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c)) c`.

Use `_ = chz ψ b₀ c * ∫ u, f (M.w * M.nzx u 0 * h') * conj (chz ψ b₀ u) ∂m.lz := by`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Use `show _ = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Wz_sh_nzx : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ)
    (f : G D n → ℂ), IsLaw χ s f → ∀ (η : Mx D ρ p) (z : hermA D ρ) (x : Mx D ρ p) (h : G D n),
    Wz M m ψ b₀ f (M.sh η * (M.nzx z x * h)) =
      chz ψ b₀ z * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x η * Wz M m ψ b₀ f (M.sh η * h) := by
  intro D n ρ p hn M m ψ hψ b₀ χ s f hf η z x h
  obtain ⟨hadd, hnorm, -, -⟩ := GlobalTheory.T.centre_character_properties ψ hψ b₀
  have hjc := GlobalTheory.T.centre_character_commutator ψ b₀ η x
  have hsh := GlobalTheory.T.shift_conj_heisenberg M η z x
  have hmul := GlobalTheory.T.unipotent_heisenberg_mul M
  have hw := GlobalTheory.T.section_invariant_heisenberg_weyl M χ s f hf
  have e1 : M.sh η * (M.nzx z x * h) = M.nzx (z + jc η x) x * (M.sh η * h) := by
    rw [← mul_assoc, hsh, mul_assoc]
  rw [e1]
  generalize M.sh η * h = h'
  have hc : chz ψ b₀ z * chv ψ b₀ x η = chz ψ b₀ (z + jc η x) := by rw [hadd, hjc]
  rw [hc]
  generalize z + jc η x = c
  have hcc : chz ψ b₀ c * conj (chz ψ b₀ c) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm c]
    simp
  have hconj : ∀ t, conj (chz ψ b₀ t) = conj (chz ψ b₀ (t + c)) * chz ψ b₀ c := by
    intro t
    have hh : conj (chz ψ b₀ (t + c)) * chz ψ b₀ c = conj (chz ψ b₀ t) * (chz ψ b₀ c * conj (chz ψ b₀ c)) := by
      rw [hadd, map_mul]; ring
    rw [hh, hcc, mul_one]
  have hpt : ∀ t : hermA D ρ, f (M.w * M.nzx t 0 * (M.nzx c x * h')) =
      f (M.w * M.nzx (t + c) 0 * h') := by
    intro t
    have e2 : M.w * M.nzx t 0 * (M.nzx c x * h') = M.w * M.nzx 0 x * (M.nzx (t + c) 0 * h') := by
      have a1 : M.nzx t 0 * M.nzx c x = M.nzx 0 x * M.nzx (t + c) 0 := by
        rw [hmul, hmul]; simp
      calc M.w * M.nzx t 0 * (M.nzx c x * h') = M.w * (M.nzx t 0 * M.nzx c x) * h' := by
            simp only [mul_assoc]
        _ = M.w * M.nzx 0 x * (M.nzx (t + c) 0 * h') := by
            rw [a1]; simp only [mul_assoc]
    rw [e2, hw, mul_assoc]
  haveI := m.hz.1
  haveI : ContinuousAdd (hermA D ρ) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : MeasurableAdd (hermA D ρ) := ContinuousAdd.measurableAdd
  unfold Wz
  calc ∫ t, f (M.w * M.nzx t 0 * (M.nzx c x * h')) * conj (chz ψ b₀ t) ∂m.lz
      = ∫ t, (fun u => f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c)) (t + c) ∂m.lz := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show f (M.w * M.nzx t 0 * (M.nzx c x * h')) * conj (chz ψ b₀ t) = f (M.w * M.nzx (t + c) 0 * h') * (conj (chz ψ b₀ (t + c)) * chz ψ b₀ c)
        rw [hpt, ← hconj]
    _ = ∫ u, f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c) ∂m.lz :=
        integral_add_right_eq_self (μ := m.lz)
          (fun u => f (M.w * M.nzx u 0 * h') * (conj (chz ψ b₀ u) * chz ψ b₀ c)) c
    _ = chz ψ b₀ c * ∫ u, f (M.w * M.nzx u 0 * h') * conj (chz ψ b₀ u) ∂m.lz := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show _ = _
        ring

end GlobalTheory.CompanionTheory.FJE

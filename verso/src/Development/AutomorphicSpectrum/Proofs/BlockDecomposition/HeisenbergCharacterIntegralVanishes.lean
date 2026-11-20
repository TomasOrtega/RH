import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLawsStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

open scoped Pointwise

/- English proof (translation)
Simplify using `[Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']`.
-/
theorem trace_single_mul_eq {R : Type} [CommRing R] {a b : ℕ} (j : Fin a) (i : Fin b) (w : R)
    (M : Matrix (Fin b) (Fin a) R) : Matrix.trace (Matrix.single j i w * M) = w * M i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

/- English proof (translation)
Establish `h2 : Module.finrank D.host.F D.host.E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Use `show Algebra.trace (AF D.host.F) (AE D) (algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)) = t`. Rewrite using `[Algebra.trace_algebraMap, Module.finrank_baseChange, h2, two_nsmul, ← add_mul, ← map_add]`. Evaluate the numerical expressions.
-/
theorem trA_algebraMap_half [Nontrivial (AF D.host.F)] (t : AF D.host.F) :
    trA (D := D) (algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)) = t := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  show Algebra.trace (AF D.host.F) (AE D) (algebraMap (AF D.host.F) (AE D)
    (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)) = t
  rw [Algebra.trace_algebraMap, Module.finrank_baseChange, h2, two_nsmul, ← add_mul, ← map_add]
  norm_num

/- English proof (translation)
Take `⟨-, -, -, t, ht⟩` from `hψ`. Establish `hB : b₀.1 * ζ ≠ 0`. Introduce `h0`. Apply `hζ` to reduce the goal to its premises. Establish `hu : IsUnit b₀.1.det` using `isUnit_iff_ne_zero.2 hdet`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`. Use `_ = 0 := by rw [h0, Matrix.mul_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, (b₀.1 * ζ) i j ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hB (Matrix.ext hc)`. Take `⟨c, hc⟩ : ∃ c : AE D, c = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t) * incA D ((b₀.1 * ζ) i j)⁻¹` from `⟨_, rfl⟩`. Use `⟨adj (Matrix.single j i c), ?_⟩` and prove the remaining obligations. Establish `key : Matrix.trace (pr b₀ (adj (Matrix.single j i c)) (rt ζ)) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t)` using `by show Matrix.trace (adj (adj (Matrix.single j i c)) ⬝ (b₀.1.map (incA D) ⬝ rt ζ)) = _`.

Rewrite using `[adj_adj, show b₀.1.map (incA D) ⬝ rt ζ = rat (b₀.1 * ζ) from (rat_mul _ _).symm, trace_single_mul_eq]`. Use `show c * incA D ((b₀.1 * ζ) i j) = _`. Rewrite using `[hc, mul_assoc, ← map_mul, inv_mul_cancel₀ hij, map_one, mul_one]`. Use `show ψ (trA (Matrix.trace (pr b₀ _ (rt ζ)))) ≠ 1`. Use `haveI : Nontrivial (AF D.host.F) := nontrivial_of_ne t 0 (fun h => ht (by rw [h, AddChar.map_zero_eq_one]))`.

Rewrite using `[key, trA_algebraMap_half]`. Conclude with `ht`.
-/
theorem exists_chv_ne_one (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (hdet : b₀.1.det ≠ 0) (ζ : Matrix (Fin ρ) (Fin p) D.host.E) (hζ : ζ ≠ 0) :
    ∃ x₀ : Mx D ρ p, chv ψ b₀ x₀ (rt ζ) ≠ 1 := by
  obtain ⟨-, -, -, t, ht⟩ := hψ
  have hB : b₀.1 * ζ ≠ 0 := by
    intro h0
    apply hζ
    have hu : IsUnit b₀.1.det := isUnit_iff_ne_zero.2 hdet
    calc ζ = b₀.1⁻¹ * (b₀.1 * ζ) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  obtain ⟨i, j, hij⟩ : ∃ i j, (b₀.1 * ζ) i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hB (Matrix.ext hc)
  obtain ⟨c, hc⟩ : ∃ c : AE D, c = algebraMap (AF D.host.F) (AE D)
      (algebraMap D.host.F (AF D.host.F) (1 / 2) * t) * incA D ((b₀.1 * ζ) i j)⁻¹ := ⟨_, rfl⟩
  refine ⟨adj (Matrix.single j i c), ?_⟩
  have key : Matrix.trace (pr b₀ (adj (Matrix.single j i c)) (rt ζ)) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * t) := by
    show Matrix.trace (adj (adj (Matrix.single j i c)) ⬝ (b₀.1.map (incA D) ⬝ rt ζ)) = _
    rw [adj_adj, show b₀.1.map (incA D) ⬝ rt ζ = rat (b₀.1 * ζ) from (rat_mul _ _).symm,
      trace_single_mul_eq]
    show c * incA D ((b₀.1 * ζ) i j) = _
    rw [hc, mul_assoc, ← map_mul, inv_mul_cancel₀ hij, map_one, mul_one]
  show ψ (trA (Matrix.trace (pr b₀ _ (rt ζ)))) ≠ 1
  haveI : Nontrivial (AF D.host.F) :=
    nontrivial_of_ne t 0 (fun h => ht (by rw [h, AddChar.map_zero_eq_one]))
  rw [key, trA_algebraMap_half]
  exact ht

/- English proof (translation)
Take `⟨x₀, hx₀⟩` from `exists_chv_ne_one ψ hψ b₀ hdet ζ hζ`. Take `⟨hadd, -, -, -, hrat, -⟩` from `GlobalTheory.T.heisenberg_character_bilinear_laws ψ hψ b₀`. Establish `hper : ∀ γ ∈ ratMx D ρ p, ∀ a, chv ψ b₀ (γ + a) (rt ζ) = chv ψ b₀ a (rt ζ)`. Introduce `γ hγ a`. Take `⟨g, rfl⟩` from `mem_ratMx.1 hγ`.

Rewrite using `[hadd, show rat g = rt g from rfl, hrat, one_mul]`. Establish `h` using `covolOne_integral_add m.hμ (fun x => chv ψ b₀ x (rt ζ)) hper x₀`. Simplify using `only [hadd] at h`. Rewrite `h` using `[MeasureTheory.integral_mul_const]`. Establish `h2 : (∫ x in m.𝓕, chv ψ b₀ x (rt ζ) ∂m.μ) * (chv ψ b₀ x₀ (rt ζ) - 1) = 0`.

Rewrite using `[mul_sub, mul_one, h, sub_self]`. Conclude with `(mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hx₀)`.
-/
theorem integral_chv_rt_eq_zero {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (hdet : b₀.1.det ≠ 0)
    (ζ : Matrix (Fin ρ) (Fin p) D.host.E) (hζ : ζ ≠ 0) :
    ∫ x in m.𝓕, chv ψ b₀ x (rt ζ) ∂m.μ = 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_chv_ne_one ψ hψ b₀ hdet ζ hζ
  obtain ⟨hadd, -, -, -, hrat, -⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws ψ hψ b₀
  have hper : ∀ γ ∈ ratMx D ρ p, ∀ a, chv ψ b₀ (γ + a) (rt ζ) = chv ψ b₀ a (rt ζ) := by
    intro γ hγ a
    obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
    rw [hadd, show rat g = rt g from rfl, hrat, one_mul]
  have h := covolOne_integral_add m.hμ (fun x => chv ψ b₀ x (rt ζ)) hper x₀
  simp only [hadd] at h
  rw [MeasureTheory.integral_mul_const] at h
  have h2 : (∫ x in m.𝓕, chv ψ b₀ x (rt ζ) ∂m.μ) * (chv ψ b₀ x₀ (rt ζ) - 1) = 0 := by
    rw [mul_sub, mul_one, h, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hx₀)

end GlobalTheory.CompanionTheory.FJE

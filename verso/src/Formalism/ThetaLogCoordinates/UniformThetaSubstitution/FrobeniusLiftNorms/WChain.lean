import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementGK
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.KernelFromKOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WModel

noncomputable section

open scoped BigOperators

namespace Formalism.InvariantFactorPaths.G7

/- English proof (translation)
Establish `h1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Set `nt : NontriviallyNormedField K0` to `{ i0 with non_trivial := ⟨(p : K0)⁻¹, by rw [norm_inv, hn, inv_inv]; exact h1⟩ }`. Set `nK : NormedField (AlgebraicClosure K0)` to `spectralNorm.normedField K0 (AlgebraicClosure K0)`. Establish `hnorm : ∀ x : AlgebraicClosure K0, ‖x‖ = spectralNorm K0 (AlgebraicClosure K0) x` using `fun _ => rfl`. Establish `hpos : 0 < p ^ 2 - 1`.

Establish `: 2 ^ 2 ≤ p ^ 2` using `Nat.pow_le_pow_left hp.two_le 2`. Use linear arithmetic over natural numbers and integers. Take `⟨ϖ, hϖ⟩` from `IsAlgClosed.exists_pow_nat_eq (p : AlgebraicClosure K0) hpos`. Use `⟨AlgebraicClosure K0, nK, ?_, ?_, algebraMap K0 (AlgebraicClosure K0), ϖ, ?_, hϖ⟩` and prove the remaining obligations. Conclude with `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => isNonarchimedean_spectralNorm x y`.

Conclude with `charZero_of_injective_algebraMap (algebraMap K0 (AlgebraicClosure K0)).injective`. Introduce `a`. Rewrite using `[hnorm]`. Conclude with `spectralNorm_extends a`.
-/
theorem exists_isometric_ext_root (K0 : Type) [i0 : NormedField K0] [IsUltrametricDist K0]
    [CharZero K0] [CompleteSpace K0] (p : ℕ) (hp : p.Prime) (hn : ‖(p : K0)‖ = (p : ℝ)⁻¹) :
    ∃ (K : Type) (_ : NormedField K) (_ : IsUltrametricDist K) (_ : CharZero K) (j : K0 →+* K)
      (ϖ : K), (∀ a, ‖j a‖ = ‖a‖) ∧ ϖ ^ (p ^ 2 - 1) = (p : K) := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  let nt : NontriviallyNormedField K0 :=
    { i0 with
      non_trivial := ⟨(p : K0)⁻¹, by rw [norm_inv, hn, inv_inv]; exact h1⟩ }
  let nK : NormedField (AlgebraicClosure K0) := spectralNorm.normedField K0 (AlgebraicClosure K0)
  have hnorm : ∀ x : AlgebraicClosure K0, ‖x‖ = spectralNorm K0 (AlgebraicClosure K0) x :=
    fun _ => rfl
  have hpos : 0 < p ^ 2 - 1 := by
    have : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
    omega
  obtain ⟨ϖ, hϖ⟩ := IsAlgClosed.exists_pow_nat_eq (p : AlgebraicClosure K0) hpos
  refine ⟨AlgebraicClosure K0, nK, ?_, ?_, algebraMap K0 (AlgebraicClosure K0), ϖ, ?_, hϖ⟩
  · exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
      isNonarchimedean_spectralNorm x y
  · exact charZero_of_injective_algebraMap (algebraMap K0 (AlgebraicClosure K0)).injective
  · intro a
    rw [hnorm]
    exact spectralNorm_extends a

/- English proof (translation)
Use `⟨fun _ _ => by simp, fun _ _ => by simp, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Establish `hlt : ∀ c : ZMod (2 * 1), c.val < 2` using `fun c => ZMod.val_lt c`. Establish `hval : a.val = b.val`. Use `hlt a` as an intermediate fact.

Use `hlt b` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `: a = b` using `ZMod.val_injective _ hval`. Simplify using `[this]`.
-/
theorem omOK_one (K : Type) [NormedField K] (p : ℕ) :
    OmOK p 1 (fun _ _ => (1 : K)) (fun _ _ => (1 : K)) := by
  refine ⟨fun _ _ => by simp, fun _ _ => by simp, ?_⟩
  intro a b hab
  have hlt : ∀ c : ZMod (2 * 1), c.val < 2 := fun c => ZMod.val_lt c
  have hval : a.val = b.val := by
    have := hlt a
    have := hlt b
    omega
  have : a = b := ZMod.val_injective _ hval
  simp [this]

/- English proof (translation)
Introduce `p _ hp2`. Take `⟨K0, i1, h1, h2, h3, σ, F, be, hσ, hζ, hF, hbe, hne⟩` from `BetaNonVacuous_of modelExists_statement Top.lawExists Top.gcIsBeta Top.gcUnique p hp2`. Take `⟨K, i2, k1, k2, j, ϖ, hj, hϖ⟩` from `exists_isometric_ext_root K0 p hσ.1 hσ.2.2.1`. Establish `hpK : ‖(p : K)‖ = (p : ℝ)⁻¹`. Rewrite using `[← map_natCast j, hj, hσ.2.2.1]`.

Take `⟨-, -, μ, hμ0, -, hμ, -, -⟩` from `Top.logRescale K p ϖ hσ.1 hpK hϖ`. Conclude with `⟨K0, i1, h1, h2, h3, σ, F, be, K, i2, k1, k2, j, ϖ, μ, hσ, hζ, hF, hbe, hne, hj, hϖ, hμ0, hμ, omOK_one K p⟩`.
-/
theorem chainModel_statement : ChainModel := by
  intro p _ hp2
  obtain ⟨K0, i1, h1, h2, h3, σ, F, be, hσ, hζ, hF, hbe, hne⟩ :=
    BetaNonVacuous_of modelExists_statement Top.lawExists Top.gcIsBeta Top.gcUnique p hp2
  obtain ⟨K, i2, k1, k2, j, ϖ, hj, hϖ⟩ := exists_isometric_ext_root K0 p hσ.1 hσ.2.2.1
  have hpK : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast j, hj, hσ.2.2.1]
  obtain ⟨-, -, μ, hμ0, -, hμ, -, -⟩ := Top.logRescale K p ϖ hσ.1 hpK hϖ
  exact ⟨K0, i1, h1, h2, h3, σ, F, be, K, i2, k1, k2, j, ϖ, μ, hσ, hζ, hF, hbe, hne, hj, hϖ, hμ0, hμ,
    omOK_one K p⟩

end Formalism.InvariantFactorPaths.G7

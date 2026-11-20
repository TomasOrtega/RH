import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyTensorLeftMulConjOneTmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPosDenominatorOfIsCompactFiniteAdeleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAwayStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.AwayPDen

/- English proof (translation)
Establish `h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) = fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2) ((Matrix.charpoly.univ K (Fin n)).coeff i)`. Use function extensionality and compare the values at `M`. Conclude with `(Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm`. Rewrite using `[h]`. Conclude with `(MvPolynomial.continuous_eval _).comp (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))`.
-/
theorem continuous_charpoly_coeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

/- English proof (translation)
Introduce `p _ G Ω hΩ`. Use `letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)`. Use `haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩`. Use `set d := Module.finrank ℚ G.C`. Set `φ : G.GAf → AfP p ⊗[ℚ] G.C` to `fun g => ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)`.

Establish `hφ : Continuous φ` using `Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)`. Set `F : ℕ → AfP p ⊗[ℚ] G.C → AfP p` to `fun i a => (LevelExists.mulMatAlg (AfP p) G.C a).charpoly.coeff i`. Establish `hF : ∀ i, Continuous (F i)` using `fun i => (continuous_charpoly_coeff d i).comp (IsModuleTopology.continuous_of_linearMap (LevelExists.mulMatAlg (AfP p) G.C).toLinearMap)`. Set `S : Set (AfP p)` to `⋃ i ∈ Finset.range (d + 1), (F i ∘ φ) '' Ω`. Establish `hS : IsCompact S` using `(Finset.range (d + 1)).isCompact_biUnion fun i _ => hΩ.image ((hF i).comp hφ)`.

Take `⟨D, hD0, hD⟩` from `GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway p S hS`. Use `⟨D, hD0, fun g y x hg hx i => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hi : i ≤ d`. Establish `hmem : F i (φ g) ∈ S` using `Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) ⟨g, hg, rfl⟩`. Establish `hval : F i (φ g) = algebraMap ℚ (AfP p) ((LinearMap.mulLeft ℚ y).charpoly.coeff i)` using `by show (LevelExists.mulMatAlg (AfP p) G.C (φ g)).charpoly.coeff i = _`.

Rewrite using `[show φ g = _ from hx]`. Use `GlobalTheory.T.charpoly_tensorLeftMul_conj_one_tmul (AfP p) G.C x y` as an intermediate fact. Simplify using `only [inC] at *`. Rewrite using `[show ((Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C) : G.C →+* AfP p ⊗[ℚ] G.C) y = 1 ⊗ₜ[ℚ] y from rfl]`. Rewrite using `[this, Polynomial.coeff_map]`.

Establish `h2` using `hD _ hmem`. Rewrite `h2` using `[hval]`. Establish `h3 : algebraMap ℚ (AfP p) ((D : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i) ∈ LevelExists.intAfP p`. Rewrite using `[map_mul, map_natCast]`. Conclude with `h2`.

Take `⟨k, a, ha⟩` from `GlobalTheory.T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway p _ h3`. Conclude with `⟨k, a, by rw [← ha]; push_cast; ring⟩`. Use `⟨0, 0, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]`. Simplify using the standard rewrite rules.
-/
theorem charpoly_den_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω → ∃ D : ℕ, 0 < D ∧ ∀ (g : G.GAf) (y : G.C) (x : (AfP p ⊗[ℚ] G.C)ˣ), g ∈ Ω → (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) = (x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) y * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) → ∀ i, ∃ k : ℕ, ∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i = a := by
  intro p _ G Ω hΩ
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  set d := Module.finrank ℚ G.C
  let φ : G.GAf → AfP p ⊗[ℚ] G.C := fun g => ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)
  have hφ : Continuous φ := Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  let F : ℕ → AfP p ⊗[ℚ] G.C → AfP p := fun i a => (LevelExists.mulMatAlg (AfP p) G.C a).charpoly.coeff i
  have hF : ∀ i, Continuous (F i) := fun i =>
    (continuous_charpoly_coeff d i).comp
      (IsModuleTopology.continuous_of_linearMap (LevelExists.mulMatAlg (AfP p) G.C).toLinearMap)
  let S : Set (AfP p) := ⋃ i ∈ Finset.range (d + 1), (F i ∘ φ) '' Ω
  have hS : IsCompact S := (Finset.range (d + 1)).isCompact_biUnion fun i _ => hΩ.image ((hF i).comp hφ)
  obtain ⟨D, hD0, hD⟩ := GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway p S hS
  refine ⟨D, hD0, fun g y x hg hx i => ?_⟩
  by_cases hi : i ≤ d
  · have hmem : F i (φ g) ∈ S :=
      Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) ⟨g, hg, rfl⟩
    have hval : F i (φ g) = algebraMap ℚ (AfP p) ((LinearMap.mulLeft ℚ y).charpoly.coeff i) := by
      show (LevelExists.mulMatAlg (AfP p) G.C (φ g)).charpoly.coeff i = _
      rw [show φ g = _ from hx]
      have := GlobalTheory.T.charpoly_tensorLeftMul_conj_one_tmul (AfP p) G.C x y
      simp only [inC] at *
      rw [show ((Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C) : G.C →+* AfP p ⊗[ℚ] G.C) y = 1 ⊗ₜ[ℚ] y from rfl]
      rw [this, Polynomial.coeff_map]
    have h2 := hD _ hmem
    rw [hval] at h2
    have h3 : algebraMap ℚ (AfP p) ((D : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i) ∈ LevelExists.intAfP p := by
      rw [map_mul, map_natCast]; exact h2
    obtain ⟨k, a, ha⟩ := GlobalTheory.T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway p _ h3
    exact ⟨k, a, by rw [← ha]; push_cast; ring⟩
  · refine ⟨0, 0, ?_⟩
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
    simp

end GlobalTheory.AwayPDen

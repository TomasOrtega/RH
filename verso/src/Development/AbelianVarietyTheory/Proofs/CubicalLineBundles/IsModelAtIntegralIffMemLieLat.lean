import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeEqValuationRingIffIsLocalization
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PointsSumsEqProducts
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebraStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

/- English proof (translation)
Introduce `K _ _ A x φ hf p M hM c`. Take `⟨R, _, _, _, _, _, ρ, xR, φR, hg, hρ, hval, hfib, hdet, hw⟩` from `hM`. Use `letI : Algebra (𝓞 K) R := ρ.toAlgebra`. Use `haveI : IsScalarTower (𝓞 K) R K := IsScalarTower.of_algebraMap_eq' hρ.symm`. Use `haveI : IsLocalization p.asIdeal.primeCompl R := (range_eq_valuationRing_iff_isLocalization K p R).1 hval`.

Establish `hG : IsGrpPullback xR.P.A A.A (spMap (algebraMap (𝓞 K) R)) φR` using `hfib.1`. Establish `n : IsGrpPullback x.P.A A.A (spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R)) φ` using `hf.2.1.congr (by rw [spMap_comp_spMap]; exact congrArg spMap hρ.symm) rfl`. Establish `w : φ ≫ A.A.hom = (x.P.A.hom ≫ spMap (algebraMap R K)) ≫ spMap (algebraMap (𝓞 K) R)` using `n.1.w.trans (Category.assoc _ _ _).symm`. Establish `e₁` using `hG.1.lift_fst _ _ w`. Establish `e₂` using `hG.1.lift_snd _ _ w`.

Generalize the expression as in `hG.1.lift _ _ w = ψ at e₁ e₂`. Establish `hψ : IsGrpPullback x.P.A xR.P.A (spMap (algebraMap R K)) ψ` using `hG.cancel (e₁ ▸ n) e₂`. Use `choose wK hwK hwK' using hw`. Establish `hb : IsLieBasis (fun k : Fin x.P.g => xR.v (k.cast hg.symm))`. Establish `key : ∀ (m : ℕ) (h : xR.P.g = m), IsLieBasis (fun k : Fin m => xR.v (k.cast h.symm))`.

Introduce `m h`. Substitute `h` using the available equality. Conclude with `xR.basis`. Conclude with `key _ hg`. Establish `hov : ∀ k, IsVecOver (algebraMap R K) ψ (xR.v (k.cast hg.symm)) (wK k)`.

Introduce `k`. Use `hG.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, e₁, hwK' k, Category.assoc, points_sums_eq_products.2]`. Rewrite using `[Category.assoc, Category.assoc, e₂, Over.w (xR.v _), ← Category.assoc, Over.w (wK k)]`. Conclude with `(PolFibre.spMap_dual_hom _).symm`.

Take `⟨h1, h2⟩` from `GlobalTheory.T.lieLattice_localization_modelLieAlgebra K A (GenFib.mk x.P φ hf x.v x.basis) R p.asIdeal.primeCompl xR.P.A φR ψ _ wK M hG hψ e₁ hb fun i => ⟨hov i, hwK i⟩`. Establish `hU : IsUnit M.det` using `hdet.isUnit`. Prove the components needed by the constructor for the conclusion. Introduce `hc choose a ha using fun m => (hval _).2 (hc m)`. Take `⟨t, ht⟩` from `IsLocalization.exist_integer_multiples_of_finite p.asIdeal.primeCompl a`.

Use `choose b hb' using ht`. Use `choose s hs hs' using h1`. Establish `hcM : c = ∑ i, Matrix.vecMul c M⁻¹ i • M i`. Rewrite using `[← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hU, Matrix.vecMul_one]`. Use `⟨(∏ i, s i) * t, Submonoid.mul_mem p.asIdeal.primeCompl (Submonoid.prod_mem _ fun i _ => hs i) t.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcM, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `e : (t : 𝓞 K) • Matrix.vecMul c M⁻¹ i = algebraMap (𝓞 K) K (b i)`. Rewrite using `[← ha, IsScalarTower.algebraMap_apply (𝓞 K) R K, hb', Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[mul_smul, ← smul_assoc (t : 𝓞 K), e, algebraMap_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, smul_comm (s i)]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hs' i))`. Introduce and unpack `⟨s, hs, hc⟩ m`. Take `⟨a, ha⟩` from `h2 _ hc`. Establish `e : s • Matrix.vecMul c M⁻¹ = fun i => algebraMap R K (a i)`. Rewrite using `[← Matrix.smul_vecMul]`.

Use `erw [ha]`. Rewrite using `[← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hU, Matrix.vecMul_one]`. Establish `e' : algebraMap (𝓞 K) K s * Matrix.vecMul c M⁻¹ m = algebraMap R K (a m)`. Rewrite using `[← Algebra.smul_def]`. Conclude with `congrFun e m`.

Establish `h3` using `(hval _).1 ⟨a m, e'.symm⟩`. Rewrite `h3` using `[map_mul, (p.valuation_eq_one_iff_notMem (K := K)).2 hs, _root_.one_mul]`. Then use the resulting hypothesis.
-/
theorem isModelAt_integral_iff_mem_lieLat : ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), IsModelAt A x φ p M → ∀ c : Fin x.P.g → K, (∀ m, p.valuation K (Matrix.vecMul c M⁻¹ m) ≤ 1) ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat := by
  intro K _ _ A x φ hf p M hM c
  obtain ⟨R, _, _, _, _, _, ρ, xR, φR, hg, hρ, hval, hfib, hdet, hw⟩ := hM
  letI : Algebra (𝓞 K) R := ρ.toAlgebra
  haveI : IsScalarTower (𝓞 K) R K := IsScalarTower.of_algebraMap_eq' hρ.symm
  haveI : IsLocalization p.asIdeal.primeCompl R := (range_eq_valuationRing_iff_isLocalization K p R).1 hval
  have hG : IsGrpPullback xR.P.A A.A (spMap (algebraMap (𝓞 K) R)) φR := hfib.1
  have n : IsGrpPullback x.P.A A.A (spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R)) φ :=
    hf.2.1.congr (by rw [spMap_comp_spMap]; exact congrArg spMap hρ.symm) rfl
  have w : φ ≫ A.A.hom = (x.P.A.hom ≫ spMap (algebraMap R K)) ≫ spMap (algebraMap (𝓞 K) R) :=
    n.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := hG.1.lift_fst _ _ w
  have e₂ := hG.1.lift_snd _ _ w
  generalize hG.1.lift _ _ w = ψ at e₁ e₂
  have hψ : IsGrpPullback x.P.A xR.P.A (spMap (algebraMap R K)) ψ := hG.cancel (e₁ ▸ n) e₂
  choose wK hwK hwK' using hw
  have hb : IsLieBasis (fun k : Fin x.P.g => xR.v (k.cast hg.symm)) := by
    have key : ∀ (m : ℕ) (h : xR.P.g = m), IsLieBasis (fun k : Fin m => xR.v (k.cast h.symm)) := by
      intro m h
      subst h
      exact xR.basis
    exact key _ hg
  have hov : ∀ k, IsVecOver (algebraMap R K) ψ (xR.v (k.cast hg.symm)) (wK k) := by
    intro k
    refine hG.1.hom_ext ?_ ?_
    · rw [Category.assoc, e₁, hwK' k, Category.assoc, points_sums_eq_products.2]
    · rw [Category.assoc, Category.assoc, e₂, Over.w (xR.v _), ← Category.assoc, Over.w (wK k)]
      exact (PolFibre.spMap_dual_hom _).symm
  obtain ⟨h1, h2⟩ := GlobalTheory.T.lieLattice_localization_modelLieAlgebra K A (GenFib.mk x.P φ hf x.v x.basis) R p.asIdeal.primeCompl xR.P.A φR ψ _ wK M
    hG hψ e₁ hb fun i => ⟨hov i, hwK i⟩
  have hU : IsUnit M.det := hdet.isUnit
  constructor
  · intro hc
    choose a ha using fun m => (hval _).2 (hc m)
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples_of_finite p.asIdeal.primeCompl a
    choose b hb' using ht
    choose s hs hs' using h1
    have hcM : c = ∑ i, Matrix.vecMul c M⁻¹ i • M i := by
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hU, Matrix.vecMul_one]
    refine ⟨(∏ i, s i) * t, Submonoid.mul_mem p.asIdeal.primeCompl (Submonoid.prod_mem _ fun i _ => hs i) t.2, ?_⟩
    rw [hcM, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : (t : 𝓞 K) • Matrix.vecMul c M⁻¹ i = algebraMap (𝓞 K) K (b i) := by
      rw [← ha, IsScalarTower.algebraMap_apply (𝓞 K) R K, hb', Algebra.smul_def, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply]
    rw [mul_smul, ← smul_assoc (t : 𝓞 K), e, algebraMap_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul,
      smul_comm (s i)]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hs' i))
  · rintro ⟨s, hs, hc⟩ m
    obtain ⟨a, ha⟩ := h2 _ hc
    have e : s • Matrix.vecMul c M⁻¹ = fun i => algebraMap R K (a i) := by
      rw [← Matrix.smul_vecMul]
      erw [ha]
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hU, Matrix.vecMul_one]
    have e' : algebraMap (𝓞 K) K s * Matrix.vecMul c M⁻¹ m = algebraMap R K (a m) := by
      rw [← Algebra.smul_def]
      exact congrFun e m
    have h3 := (hval _).1 ⟨a m, e'.symm⟩
    rwa [map_mul, (p.valuation_eq_one_iff_notMem (K := K)).2 hs, _root_.one_mul] at h3

end GlobalTheory.LamF

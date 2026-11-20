import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CobChi

/- English proof (translation)
Introduce `R _ A _ n hn u f g hu ⟨k, hk⟩`. Establish `hf : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D), f D D' φ x = u D D' φ x - (k D' (spOver φ ≫ x) - φ (k D x))`. Introduce `D _ _ D' _ _ φ x`. Establish `h` using `hk D D' φ x (sm_whole x)`. Simplify using `only [Fn1.add, Fn1.neg] at h`.

Take the linear combination `-h`. Use `⟨fun D _ _ x y ↦ g D x y - (k D (x * y) - k D x - k D y), ?_, ?_⟩` and prove the remaining obligations. Introduce `D _ _ D' _ _ φ x y`. Establish `h1` using `hu D D' φ x y`. Simplify using `only [hf, comp_mul, map_sub]`.

Take the linear combination `h1`. Introduce `D _ _ x hx`. Establish `hnD : (n : D) = 0`. Rewrite using `[← map_natCast (algebraMap R D) n, hn, map_zero]`. Establish `hs : ∑ i ∈ Finset.range n, (k D (x ^ i * x) - k D (x ^ i) - k D x) = 0`.

Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]`. Repeatedly rewrite using `[← pow_succ]`. Rewrite using `[Finset.sum_range_sub (fun i ↦ k D (x ^ i)), hx, pow_zero, sub_self, zero_sub, neg_eq_zero, nsmul_eq_mul, hnD, zero_mul]`. Simplify using `only [GlobalTheory.PtExt.chi]`. Rewrite using `[Finset.sum_sub_distrib, hs, sub_zero]`.
-/
theorem exists_isAdd_chi_eq : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (n : ℕ), (n : R) = 0 → ∀ (u f : Fn1 A) (g : Fn2 A), IsAdd u g → Cohom (whole A) u f → ∃ g' : Fn2 A, IsAdd f g' ∧ ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ n = 1 → GlobalTheory.PtExt.chi n g' D x = GlobalTheory.PtExt.chi n g D x := by
  intro R _ A _ n hn u f g hu ⟨k, hk⟩
  have hf : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (x : Pt A D), f D D' φ x = u D D' φ x - (k D' (spOver φ ≫ x) - φ (k D x)) := by
    intro D _ _ D' _ _ φ x
    have h := hk D D' φ x (sm_whole x)
    simp only [Fn1.add, Fn1.neg] at h
    linear_combination -h
  refine ⟨fun D _ _ x y ↦ g D x y - (k D (x * y) - k D x - k D y), ?_, ?_⟩
  · intro D _ _ D' _ _ φ x y
    have h1 := hu D D' φ x y
    simp only [hf, comp_mul, map_sub]
    linear_combination h1
  · intro D _ _ x hx
    have hnD : (n : D) = 0 := by
      rw [← map_natCast (algebraMap R D) n, hn, map_zero]
    have hs : ∑ i ∈ Finset.range n, (k D (x ^ i * x) - k D (x ^ i) - k D x) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      simp_rw [← pow_succ]
      rw [Finset.sum_range_sub (fun i ↦ k D (x ^ i)), hx, pow_zero, sub_self, zero_sub, neg_eq_zero, nsmul_eq_mul,
        hnD, zero_mul]
    simp only [GlobalTheory.PtExt.chi]
    rw [Finset.sum_sub_distrib, hs, sub_zero]

end GlobalTheory.CobChi

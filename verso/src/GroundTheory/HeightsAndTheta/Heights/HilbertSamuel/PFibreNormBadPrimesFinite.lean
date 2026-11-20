import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormBadPrimesFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_map, eval_map]`. Use `congr 1`.
-/
theorem aeval_map_intRat_eq {σ : Type} (x : σ → ℂ) (f : MvPolynomial σ ℤ) :
    aeval x (map (algebraMap ℤ ℚ) f) = eval x (map (Int.castRingHom ℂ) f) := by
  rw [aeval_def, eval₂_map, eval_map]
  congr 1

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D e L _ _ _ _ hC`. Use `set I : Ideal (MvPolynomial (Σ k, ι k) ℤ) := mCoordIdeal y ⊔ Ideal.span (Set.range L) with hIdef`. Establish `key : ∀ c : ∀ k, ι k, ∃ N : ℤ, N ≠ 0 ∧ ∃ r : ℕ, C N * (∏ k, X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ r ∈ I`. Introduce `c`. Use `set f : MvPolynomial (Σ k, ι k) ℤ := ∏ k, X ⟨k, c k⟩`.

Use `set IQ := Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ)) I`. Establish `hv : algebraMap _ (MvPolynomial (Σ k, ι k) ℚ) f ∈ vanishingIdeal ℚ (zeroLocus ℂ IQ)`. Rewrite using `[mem_vanishingIdeal_iff]`. Introduce `x hx`. Rewrite `hx` using `[mem_zeroLocus_iff]`.

Establish `h0 : ∀ g ∈ I, eval x (map (Int.castRingHom ℂ) g) = 0` using `fun g hg => by`. Rewrite using `[← aeval_map_intRat_eq, ← algebraMap_def]`. Conclude with `hx _ (Ideal.mem_map_of_mem _ hg)`. Rewrite using `[algebraMap_def, aeval_map_intRat_eq]`. Assume the negation of the conclusion as `hne`.

Simplify using `only [f, map_prod, map_X, eval_X] at hne`. Establish `hblk : ∀ k, x ⟨k, c k⟩ ≠ 0` using `fun k => (Finset.prod_ne_zero_iff.1 hne) k (Finset.mem_univ _)`. Take `⟨j, hj⟩` from `hC x ⟨fun k => ⟨c k, hblk k⟩, fun g hg => h0 g (Ideal.mem_sup_left hg)⟩`. Conclude with `hj (h0 _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)))`. Rewrite `hv` using `[vanishingIdeal_zeroLocus_eq_radical]`.

Take `⟨r, hr⟩` from `hv`. Rewrite `hr` using `[← map_pow, IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))]`. Take `⟨⟨⟨u, hu⟩, ⟨m, hm⟩⟩, h⟩` from `hr`. Take `⟨n, hn, rfl⟩` from `Submonoid.mem_map.1 hm`. Use `⟨n, nonZeroDivisors.ne_zero hn, r, ?_⟩` and prove the remaining obligations.

Establish `hinj : Function.Injective (map (σ` using `Σ k, ι k) (algebraMap ℤ ℚ)) := map_injective _ (algebraMap ℤ ℚ).injective_int`. Establish `hu' : f ^ r * C n = u` using `hinj (by simpa only [algebraMap_def, map_mul] using h)`. Rewrite using `[mul_comm, hu']`. Conclude with `hu`. Use `choose N hN r hr using key`.

Use `Set.Finite.subset (Set.finite_iUnion fun c => (Set.finite_Iic (N c).natAbs)) ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hH⟩`. Take `⟨z, hz, hP, hL⟩` from `hH`. Use `choose c hc using hz`. Establish `: Fact p.Prime` using `⟨hp⟩`.

Establish `: CharP (AlgebraicClosure (ZMod p)) p` using `charP_of_injective_algebraMap (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective p`. Establish `hker : I ≤ RingHom.ker ((eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p)))))` using `sup_le (fun g hg => hP g hg) (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hL j))`. Establish `h1` using `hker (hr c)`. Simplify using `only [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_pow, map_prod, map_X, eval_X, eq_intCast, map_intCast] at h1`. Establish `hprod : (∏ k, z ⟨k, c k⟩) ^ r c ≠ 0` using `pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun k _ => hc k)`.

Establish `hNz : ((N c : ℤ) : AlgebraicClosure (ZMod p)) = 0` using `(mul_eq_zero.1 h1).resolve_right hprod`. Rewrite `hNz` using `[CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod p)) p]`. Simplify using `only [Set.mem_iUnion, Set.mem_Iic]`. Conclude with `⟨c, Nat.le_of_dvd (Int.natAbs_pos.2 (hN c)) (Int.natCast_dvd.1 hNz)⟩`.
-/
theorem FibreNormBadPrimesFinite.proof : FibreNormBadPrimesFinite.Statement := by
  intro K _ ι _ Ω _ _ y D e L _ _ _ _ hC
  set I : Ideal (MvPolynomial (Σ k, ι k) ℤ) := mCoordIdeal y ⊔ Ideal.span (Set.range L) with hIdef
  have key : ∀ c : ∀ k, ι k, ∃ N : ℤ, N ≠ 0 ∧
      ∃ r : ℕ, C N * (∏ k, X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ r ∈ I := by
    intro c
    set f : MvPolynomial (Σ k, ι k) ℤ := ∏ k, X ⟨k, c k⟩
    set IQ := Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ)) I
    have hv : algebraMap _ (MvPolynomial (Σ k, ι k) ℚ) f ∈ vanishingIdeal ℚ (zeroLocus ℂ IQ) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [mem_zeroLocus_iff] at hx
      have h0 : ∀ g ∈ I, eval x (map (Int.castRingHom ℂ) g) = 0 := fun g hg => by
        rw [← aeval_map_intRat_eq, ← algebraMap_def]
        exact hx _ (Ideal.mem_map_of_mem _ hg)
      rw [algebraMap_def, aeval_map_intRat_eq]
      by_contra hne
      simp only [f, map_prod, map_X, eval_X] at hne
      have hblk : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hne) k (Finset.mem_univ _)
      obtain ⟨j, hj⟩ := hC x ⟨fun k => ⟨c k, hblk k⟩, fun g hg => h0 g (Ideal.mem_sup_left hg)⟩
      exact hj (h0 _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)))
    rw [vanishingIdeal_zeroLocus_eq_radical] at hv
    obtain ⟨r, hr⟩ := hv
    rw [← map_pow, IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))]
      at hr
    obtain ⟨⟨⟨u, hu⟩, ⟨m, hm⟩⟩, h⟩ := hr
    obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.1 hm
    refine ⟨n, nonZeroDivisors.ne_zero hn, r, ?_⟩
    have hinj : Function.Injective (map (σ := Σ k, ι k) (algebraMap ℤ ℚ)) :=
      map_injective _ (algebraMap ℤ ℚ).injective_int
    have hu' : f ^ r * C n = u := hinj (by simpa only [algebraMap_def, map_mul] using h)
    rw [mul_comm, hu']
    exact hu
  choose N hN r hr using key
  refine Set.Finite.subset (Set.finite_iUnion fun c => (Set.finite_Iic (N c).natAbs)) ?_
  rintro p ⟨hp, hH⟩
  obtain ⟨z, hz, hP, hL⟩ := hH
  choose c hc using hz
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective p
  have hker : I ≤ RingHom.ker ((eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p))))) :=
    sup_le (fun g hg => hP g hg) (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hL j))
  have h1 := hker (hr c)
  simp only [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_pow, map_prod, map_X, eval_X, eq_intCast,
    map_intCast] at h1
  have hprod : (∏ k, z ⟨k, c k⟩) ^ r c ≠ 0 :=
    pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun k _ => hc k)
  have hNz : ((N c : ℤ) : AlgebraicClosure (ZMod p)) = 0 := (mul_eq_zero.1 h1).resolve_right hprod
  rw [CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod p)) p] at hNz
  simp only [Set.mem_iUnion, Set.mem_Iic]
  exact ⟨c, Nat.le_of_dvd (Int.natAbs_pos.2 (hN c)) (Int.natCast_dvd.1 hNz)⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStA

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

def traceMat {r δ : ℕ} (D N : ℕ) (g : Fin r → Fin δ → MvPolynomial (Fin (D + 1)) ℤ) :
    Matrix (Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card)) (Fin r) ℤ :=
  Matrix.of fun p j => coeff (Finsupp.equivFunOnFinite.symm (adtEnum D N (finProdFinEquiv.symm p).2))
    (g j (finProdFinEquiv.symm p).1)

/- English proof (translation)
Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval_map]`. Use `congr 1`.
-/
theorem eval_map_int {σ : Type*} (w : σ → ℂ) (p : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom ℂ) p) = aeval w p := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval_map]
  congr 1

/- English proof (translation)
Apply the tactic sequence `have hentry : ∀ i, traceMat D N g (finProdFinEquiv (l, i)) j = coeff (Finsupp.equivFunOnFinite.symm (adtEnum D N i)) (g j l) := by`. Introduce `i`. Simplify using `only [traceMat, Matrix.of_apply, Equiv.symm_apply_apply]`. Simplify using `only [hentry]`. Establish `hR : ∑ i, ((coeff (Finsupp.equivFunOnFinite.symm (adtEnum D N i)) (g j l) : ℤ) : S) * ∏ t, y t ^ adtEnum D N i t = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : S) * ∏ t, y t ^ a t`.

Rewrite using `[← Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple (D + 1) N)]`. Conclude with `(Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm.sum_comp (fun a : (Finset.Nat.antidiagonalTuple (D + 1) N) => ((coeff (Finsupp.equivFunOnFinite.symm (a : Fin (D + 1) → ℕ)) (g j l) : ℤ) : S) * ∏ t, y t ^ (a : Fin (D + 1) → ℕ) t)`. Rewrite using `[hR, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']`. Set `e : (Fin (D + 1) → ℕ) ↪ (Fin (D + 1) →₀ ℕ)` to `⟨Finsupp.equivFunOnFinite.symm, Finsupp.equivFunOnFinite.symm.injective⟩`. Establish `hmap : ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : S) * ∏ t, y t ^ a t = ∑ d ∈ (Finset.Nat.antidiagonalTuple (D + 1) N).map e, algebraMap ℤ S (coeff d (g j l)) * ∏ t, y t ^ d t`.

Rewrite using `[Finset.sum_map]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[e]`. Rewrite using `[hmap]`. Use `Finset.sum_subset (fun d hd => ?_) (fun d _ hd => ?_)` and prove the remaining obligations.

Rewrite using `[Finset.mem_map]`. Use `⟨⇑d, ?_, by simp [e]⟩` and prove the remaining obligations. Establish `h1` using `hg (MvPolynomial.mem_support_iff.mp hd)`. Rewrite using `[Finset.Nat.mem_antidiagonalTuple]`. Simplify `h1` using `[Finsupp.weight_apply, Finsupp.sum_fintype]`.

Rewrite using `[MvPolynomial.notMem_support_iff.mp hd, map_zero, zero_mul]`.
-/
theorem aeval_eq_sum_traceMat {S : Type*} [CommRing S] {r δ N : ℕ}
    (g : Fin r → Fin δ → MvPolynomial (Fin (D + 1)) ℤ) (j : Fin r) (l : Fin δ)
    (hg : (g j l).IsHomogeneous N) (y : Fin (D + 1) → S) :
    aeval y (g j l) = ∑ i, ((traceMat D N g (finProdFinEquiv (l, i)) j : ℤ) : S) *
      ∏ t, y t ^ adtEnum D N i t := by
  classical
  have hentry : ∀ i, traceMat D N g (finProdFinEquiv (l, i)) j =
      coeff (Finsupp.equivFunOnFinite.symm (adtEnum D N i)) (g j l) := by
    intro i; simp only [traceMat, Matrix.of_apply, Equiv.symm_apply_apply]
  simp only [hentry]
  have hR : ∑ i, ((coeff (Finsupp.equivFunOnFinite.symm (adtEnum D N i)) (g j l) : ℤ) : S) *
        ∏ t, y t ^ adtEnum D N i t =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N,
        ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : S) * ∏ t, y t ^ a t := by
    rw [← Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple (D + 1) N)]
    exact (Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm.sum_comp
      (fun a : (Finset.Nat.antidiagonalTuple (D + 1) N) =>
        ((coeff (Finsupp.equivFunOnFinite.symm (a : Fin (D + 1) → ℕ)) (g j l) : ℤ) : S) *
          ∏ t, y t ^ (a : Fin (D + 1) → ℕ) t)
  rw [hR, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  let e : (Fin (D + 1) → ℕ) ↪ (Fin (D + 1) →₀ ℕ) :=
    ⟨Finsupp.equivFunOnFinite.symm, Finsupp.equivFunOnFinite.symm.injective⟩
  have hmap : ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N,
        ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : S) * ∏ t, y t ^ a t =
      ∑ d ∈ (Finset.Nat.antidiagonalTuple (D + 1) N).map e,
        algebraMap ℤ S (coeff d (g j l)) * ∏ t, y t ^ d t := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [e]
  rw [hmap]
  refine Finset.sum_subset (fun d hd => ?_) (fun d _ hd => ?_)
  · rw [Finset.mem_map]
    refine ⟨⇑d, ?_, by simp [e]⟩
    have h1 := hg (MvPolynomial.mem_support_iff.mp hd)
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using h1
  · rw [MvPolynomial.notMem_support_iff.mp hd, map_zero, zero_mul]

/- English proof (translation)
Use `choose F hFh hFb using hb.1`. Establish `hs : ∀ j, aeval x (b j) = aeval x (F j)` using `fun j => by`. Rewrite using `[hFb j, ← algebraMap_int_eq, aeval_map_algebraMap]`. Establish `hmemN : ∀ j l, aeval x (b j) * aeval x (H l) ∈ sec ℤ x (n + k)` using `fun j l => by`. Rewrite using `[hs j, ← map_mul]`.

Conclude with `Submodule.mem_map.mpr ⟨F j * H l, (mem_homogeneousSubmodule _ _).mpr ((hFh j).mul (hH l)), rfl⟩`. Establish `hsn : ∀ j, aeval x (b j) ∈ sec ℤ x n` using `fun j => hb.2.2 ▸ Submodule.subset_span ⟨j, rfl⟩`. Establish `key : ∀ u : Fin r → ℤ, traceMat D (n + k) g *ᵥ u = 0 → u = 0`. Introduce `u hu`. Use `set s := ∑ j, u j • aeval x (b j) with hs_def`.

Establish `hsmem : s ∈ sec ℤ x n` using `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hsn j)`. Establish `h0 : ∀ l, secTrace x e (n + k) (s * aeval x (H l)) = 0`. Introduce `l`. Establish `h1 : s * aeval x (H l) = ((∑ j, u j • (⟨_, hmemN j l⟩ : sec ℤ x (n + k)) : sec ℤ x (n + k)) : Ω)`. Rewrite using `[hs_def, Finset.sum_mul, Submodule.coe_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, smul_mul_assoc]`. Rewrite using `[h1]`. Use `show secTraceHom x e hfr (n + k) (∑ j, u j • (⟨_, hmemN j l⟩ : sec ℤ x (n + k))) = 0`. Rewrite using `[map_sum]`.

Simplify using `only [map_zsmul]`. Establish `h3 : ∀ j, secTraceHom x e hfr (n + k) ⟨_, hmemN j l⟩ = aeval (x ∘ e) (g j l)` using `fun j => (hgv j l).symm`. Simplify using `only [h3, aeval_eq_sum_traceMat g _ l (hgh _ l), Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Establish `hu'` using `congrFun hu (finProdFinEquiv (l, i))`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hu'`. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [hu']; simp`. Establish `hs0` using `eq_zero_of_secTrace_mul_eq_zero x e hfr (fun l => aeval x (H l)) (fun l => Submodule.mem_map.mpr ⟨H l, (mem_homogeneousSubmodule _ _).mpr (hH l), rfl⟩) hli n hsmem h0`.

Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.mp hb.2.1 u hs0 j`. Introduce `v w hvw`. Establish `hd : (traceMat D (n + k) g).map (Int.cast : ℤ → ℚ) *ᵥ (v - w) = 0`. Rewrite using `[Matrix.mulVec_sub, hvw, sub_self]`.

Take `⟨⟨c, hc⟩, hcu⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) (v - w)`. Use `choose u hu using hcu`. Establish `hu2 : ∀ i, ((u i : ℤ) : ℚ) = (c : ℚ) * (v - w) i` using `fun i => by`. Use `hu i` as an intermediate fact. Simplify using `only [zsmul_eq_mul, algebraMap_int_eq, eq_intCast] at this`.

Conclude with `this`. Establish `hMu : traceMat D (n + k) g *ᵥ u = 0`. Use function extensionality and compare the values at `p`. Establish `h1` using `RingHom.map_mulVec (Int.castRingHom ℚ) (traceMat D (n + k) g) u p`. Establish `h2 : (Int.castRingHom ℚ) ∘ u = (c : ℚ) • (v - w)`.

Use function extensionality and compare the values at `i`. Simplify using `[hu2 i]`. Rewrite `h1` using `[h2, Matrix.mulVec_smul]`. Simplify using `only [Int.coe_castRingHom] at h1`. Rewrite `h1` using `[hd, smul_zero]`.

Simplify using `only [Pi.zero_apply] at h1 ⊢`. Conclude with `h1` after adjusting the coercions. Establish `hu0` using `key u hMu`. Establish `hc0 : c ≠ 0` using `mem_nonZeroDivisors_iff_ne_zero.mp hc`. Use function extensionality and compare the values at `i`.

Use `hu2 i` as an intermediate fact. Rewrite `this` using `[hu0]`. Simplify using `only [Pi.zero_apply, Int.cast_zero] at this`. Establish `h3 : (v - w) i = 0`. Break down `mul_eq_zero.mp this.symm with h | h` into its components or cases.

Conclude with `absurd (by exact_mod_cast h) hc0`. Conclude with `h`. Simplify `h3` using `[sub_eq_zero]`.
-/
theorem traceMat_injective {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsRatProjFrame x e)
    {n k r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b)
    (H : Fin (projDeg x e) → MvPolynomial (Ix κ) ℤ) (hH : ∀ l, (H l).IsHomogeneous k)
    (hli : LinearIndependent (fnField (x ∘ e)) fun l => aeval x (H l))
    (g : Fin r → Fin (projDeg x e) → MvPolynomial (Fin (D + 1)) ℤ)
    (hgh : ∀ j l, (g j l).IsHomogeneous (n + k))
    (hgv : ∀ j l, aeval (x ∘ e) (g j l) = secTrace x e (n + k) (aeval x (b j) * aeval x (H l))) :
    Function.Injective ((traceMat D (n + k) g).map (Int.cast : ℤ → ℚ)).mulVec := by
  classical
  choose F hFh hFb using hb.1
  have hs : ∀ j, aeval x (b j) = aeval x (F j) := fun j => by
    rw [hFb j, ← algebraMap_int_eq, aeval_map_algebraMap]
  have hmemN : ∀ j l, aeval x (b j) * aeval x (H l) ∈ sec ℤ x (n + k) := fun j l => by
    rw [hs j, ← map_mul]
    exact Submodule.mem_map.mpr ⟨F j * H l, (mem_homogeneousSubmodule _ _).mpr ((hFh j).mul (hH l)), rfl⟩
  have hsn : ∀ j, aeval x (b j) ∈ sec ℤ x n := fun j => hb.2.2 ▸ Submodule.subset_span ⟨j, rfl⟩
  have key : ∀ u : Fin r → ℤ, traceMat D (n + k) g *ᵥ u = 0 → u = 0 := by
    intro u hu
    set s := ∑ j, u j • aeval x (b j) with hs_def
    have hsmem : s ∈ sec ℤ x n := Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hsn j)
    have h0 : ∀ l, secTrace x e (n + k) (s * aeval x (H l)) = 0 := by
      intro l
      have h1 : s * aeval x (H l) =
          ((∑ j, u j • (⟨_, hmemN j l⟩ : sec ℤ x (n + k)) : sec ℤ x (n + k)) : Ω) := by
        rw [hs_def, Finset.sum_mul, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Submodule.coe_smul, smul_mul_assoc]
      rw [h1]
      show secTraceHom x e hfr (n + k) (∑ j, u j • (⟨_, hmemN j l⟩ : sec ℤ x (n + k))) = 0
      rw [map_sum]
      simp only [map_zsmul]
      have h3 : ∀ j, secTraceHom x e hfr (n + k) ⟨_, hmemN j l⟩ = aeval (x ∘ e) (g j l) :=
        fun j => (hgv j l).symm
      simp only [h3, aeval_eq_sum_traceMat g _ l (hgh _ l), Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hu' := congrFun hu (finProdFinEquiv (l, i))
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hu'
      calc ∑ j, u j • (((traceMat D (n + k) g (finProdFinEquiv (l, i)) j : ℤ) : Ω) *
              ∏ t, (x ∘ e) t ^ adtEnum D (n + k) i t)
          = ((∑ j, traceMat D (n + k) g (finProdFinEquiv (l, i)) j * u j : ℤ) : Ω) *
              ∏ t, (x ∘ e) t ^ adtEnum D (n + k) i t := by
            push_cast
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [zsmul_eq_mul]; ring
        _ = 0 := by rw [hu']; simp
    have hs0 := eq_zero_of_secTrace_mul_eq_zero x e hfr (fun l => aeval x (H l))
      (fun l => Submodule.mem_map.mpr ⟨H l, (mem_homogeneousSubmodule _ _).mpr (hH l), rfl⟩) hli n hsmem h0
    funext j
    exact Fintype.linearIndependent_iff.mp hb.2.1 u hs0 j
  intro v w hvw
  have hd : (traceMat D (n + k) g).map (Int.cast : ℤ → ℚ) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  obtain ⟨⟨c, hc⟩, hcu⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (v - w)
  choose u hu using hcu
  have hu2 : ∀ i, ((u i : ℤ) : ℚ) = (c : ℚ) * (v - w) i := fun i => by
    have := hu i
    simp only [zsmul_eq_mul, algebraMap_int_eq, eq_intCast] at this
    exact this
  have hMu : traceMat D (n + k) g *ᵥ u = 0 := by
    funext p
    have h1 := RingHom.map_mulVec (Int.castRingHom ℚ) (traceMat D (n + k) g) u p
    have h2 : (Int.castRingHom ℚ) ∘ u = (c : ℚ) • (v - w) := by
      funext i; simp [hu2 i]
    rw [h2, Matrix.mulVec_smul] at h1
    simp only [Int.coe_castRingHom] at h1
    rw [hd, smul_zero] at h1
    simp only [Pi.zero_apply] at h1 ⊢
    exact_mod_cast h1
  have hu0 := key u hMu
  have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
  funext i
  have := hu2 i
  rw [hu0] at this
  simp only [Pi.zero_apply, Int.cast_zero] at this
  have h3 : (v - w) i = 0 := by
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd (by exact_mod_cast h) hc0
    · exact h
  simpa [sub_eq_zero] using h3

/- English proof (translation)
Rewrite using `[show Int.castRingHom ℚ = algebraMap ℤ ℚ from RingHom.ext_int _ _, MvPolynomial.aeval_map_algebraMap]`.
-/
theorem aeval_map_intQ (x : Ix κ → Ω) (f : MvPolynomial (Ix κ) ℤ) :
    aeval x (map (Int.castRingHom ℚ) f) = aeval x f := by
  rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from RingHom.ext_int _ _, MvPolynomial.aeval_map_algebraMap]

/- English proof (translation)
Unfold `secFun`. Rewrite using `[MvPolynomial.map_map, show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _]`.
-/
theorem secFun_map_intQ (f : MvPolynomial (Ix κ) ℤ) (z : Ix κ → ℂ) :
    secFun (map (Int.castRingHom ℚ) f) z = eval z (map (Int.castRingHom ℂ) f) := by
  unfold secFun
  rw [MvPolynomial.map_map,
    show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _]

open Matrix in
/- English proof (translation)
Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hP.sub hQ) fun c => ?_` and prove the remaining obligations. Establish `hreal` using `(hP.sub hQ).im_star_dotProduct_mulVec_self c`. Establish `hsplit : star c ⬝ᵥ (P - Q) *ᵥ c = star c ⬝ᵥ P *ᵥ c - star c ⬝ᵥ Q *ᵥ c`. Simplify using `[Matrix.sub_mulVec]`. Rewrite using `[Complex.nonneg_iff]`.

Use `⟨?_, hreal.symm⟩` and prove the remaining obligations. Rewrite using `[hsplit, Complex.sub_re]`. Combine the linear relations using `[h c]`.
-/
theorem psd_sub_of_quad_le {r : ℕ} {P Q : Matrix (Fin r) (Fin r) ℂ} (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) (h : ∀ c : Fin r → ℂ, (star c ⬝ᵥ Q *ᵥ c).re ≤ (star c ⬝ᵥ P *ᵥ c).re) :
    (P - Q).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hP.sub hQ) fun c => ?_
  have hreal := (hP.sub hQ).im_star_dotProduct_mulVec_self c
  have hsplit : star c ⬝ᵥ (P - Q) *ᵥ c = star c ⬝ᵥ P *ᵥ c - star c ⬝ᵥ Q *ᵥ c := by
    simp [Matrix.sub_mulVec]
  rw [Complex.nonneg_iff]
  refine ⟨?_, hreal.symm⟩
  rw [hsplit, Complex.sub_re]
  linarith [h c]

open Matrix in
/- English proof (translation)
Unfold `Matrix.IsHermitian`. Rewrite using `[Matrix.conjTranspose_smul, hG.eq]`. Use `congr 1`. Simplify using `[← Complex.ofReal_pow, Complex.conj_ofReal]`.
-/
theorem isHermitian_sq_smul {r : ℕ} {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.IsHermitian) (A : ℝ) :
    (((A : ℂ) ^ 2) • G).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hG.eq]
  congr 1
  simp [← Complex.ofReal_pow, Complex.conj_ofReal]

open Matrix in
/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]`.
-/
theorem quad_conj {r s : ℕ} (M : Matrix (Fin s) (Fin r) ℂ) (G : Matrix (Fin s) (Fin s) ℂ)
    (c : Fin r → ℂ) :
    star c ⬝ᵥ (Mᴴ * G * M) *ᵥ c = star (M *ᵥ c) ⬝ᵥ G *ᵥ (M *ᵥ c) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

open Matrix in
/- English proof (translation)
Simplify using `only [monoDiag, Matrix.mulVec_diagonal]`. Use `first`. Consider the case `simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]`. Consider the case `simp only [Matrix.dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]`. Rewrite using `[Complex.re_sum, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `try simp only [Equiv.symm_apply_apply]`. Rewrite using `[mul_left_comm, Complex.re_ofReal_mul]`. Use `congr 1`. Rewrite using `[Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]`.
-/
theorem quad_monoDiag (D N δ : ℕ) (v : Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card) → ℂ) :
    (star v ⬝ᵥ monoDiag D N δ *ᵥ v).re =
      ∑ l : Fin δ, ∑ i, monoNormSq (adtEnum D N i) * ‖v (finProdFinEquiv (l, i))‖ ^ 2 := by
  simp only [monoDiag, Matrix.mulVec_diagonal]
  first
  | simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]
  | simp only [Matrix.dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]
  rw [Complex.re_sum, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  try simp only [Equiv.symm_apply_apply]
  rw [mul_left_comm, Complex.re_ofReal_mul]
  congr 1
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/- English proof (translation)
Establish `reidx : ∀ {X : Type} [AddCommMonoid X] (F : (Fin (D + 1) → ℕ) → X), ∑ i, F (adtEnum D N i) = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, F a`. Introduce `X _ F`. Rewrite using `[← Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple (D + 1) N)]`. Conclude with `(Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm.sum_comp (fun a : (Finset.Nat.antidiagonalTuple (D + 1) N) => F (a : Fin (D + 1) → ℕ))`. Set `C : (Fin (D + 1) → ℕ) → ℂ` to `fun a => ∑ j, ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : ℂ) * c j`.

Establish `hentry' : ∀ i, ((traceMat D N g).map (Int.cast : ℤ → ℂ) *ᵥ c) (finProdFinEquiv (l, i)) = C (adtEnum D N i)`. Introduce `i`. Use `first`. Consider the case `simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, traceMat, Matrix.of_apply, Equiv.symm_apply_apply, C]`. Consider the case `simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.map_apply, traceMat, Matrix.of_apply, Equiv.symm_apply_apply, C]`.

Establish `hj : ∀ (j : Fin r) (w : Fin (D + 1) → ℂ), eval w (map (Int.castRingHom ℂ) (g j l)) = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : ℂ) * monoC a w`. Introduce `j w`. Rewrite using `[eval_map_int, aeval_eq_sum_traceMat g j l (hg j l) w, ← reidx (fun a => ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : ℂ) * monoC a w)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [traceMat, Matrix.of_apply, Equiv.symm_apply_apply, monoC]`.

Establish `hint : ∀ w, ∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l)) = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, C a * monoC a w`. Introduce `w`. Simplify using `only [hj, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Simplify using `only [C, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← reidx (fun a => monoNormSq a * ‖C a‖ ^ 2)]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hentry' i]`. Use `_ = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, ‖C a‖ ^ 2 * monoNormSq a := Finset.sum_congr rfl fun a _ => mul_comm _ _`. Use `_ = ∫ z, ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, C a * monoC a z‖ ^ 2 ∂(sphProb (D + 1)) := (integral_form_sq D N C).symm`. Use `_ = ∫ w, ‖∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l))‖ ^ 2 ∂(sphProb (D + 1)) := by`.

Simplify using `only [hint]`.
-/
theorem sum_monoNormSq_traceMat {r δ N : ℕ} (g : Fin r → Fin δ → MvPolynomial (Fin (D + 1)) ℤ)
    (hg : ∀ j l, (g j l).IsHomogeneous N) (c : Fin r → ℂ) (l : Fin δ) :
    ∑ i, monoNormSq (adtEnum D N i) *
        ‖((traceMat D N g).map (Int.cast : ℤ → ℂ) *ᵥ c) (finProdFinEquiv (l, i))‖ ^ 2 =
      ∫ w, ‖∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l))‖ ^ 2 ∂(sphProb (D + 1)) := by
  classical
  have reidx : ∀ {X : Type} [AddCommMonoid X] (F : (Fin (D + 1) → ℕ) → X),
      ∑ i, F (adtEnum D N i) = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, F a := by
    intro X _ F
    rw [← Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple (D + 1) N)]
    exact (Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm.sum_comp
      (fun a : (Finset.Nat.antidiagonalTuple (D + 1) N) => F (a : Fin (D + 1) → ℕ))
  let C : (Fin (D + 1) → ℕ) → ℂ := fun a =>
    ∑ j, ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : ℂ) * c j
  have hentry' : ∀ i, ((traceMat D N g).map (Int.cast : ℤ → ℂ) *ᵥ c) (finProdFinEquiv (l, i)) =
      C (adtEnum D N i) := by
    intro i
    first
    | simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, traceMat, Matrix.of_apply,
        Equiv.symm_apply_apply, C]
    | simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.map_apply, traceMat, Matrix.of_apply,
        Equiv.symm_apply_apply, C]
  have hj : ∀ (j : Fin r) (w : Fin (D + 1) → ℂ), eval w (map (Int.castRingHom ℂ) (g j l)) =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N,
        ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : ℂ) * monoC a w := by
    intro j w
    rw [eval_map_int, aeval_eq_sum_traceMat g j l (hg j l) w,
      ← reidx (fun a => ((coeff (Finsupp.equivFunOnFinite.symm a) (g j l) : ℤ) : ℂ) * monoC a w)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [traceMat, Matrix.of_apply, Equiv.symm_apply_apply, monoC]
  have hint : ∀ w, ∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l)) =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, C a * monoC a w := by
    intro w
    simp only [hj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [C, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc ∑ i, monoNormSq (adtEnum D N i) *
        ‖((traceMat D N g).map (Int.cast : ℤ → ℂ) *ᵥ c) (finProdFinEquiv (l, i))‖ ^ 2
      = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, monoNormSq a * ‖C a‖ ^ 2 := by
        rw [← reidx (fun a => monoNormSq a * ‖C a‖ ^ 2)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hentry' i]
    _ = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, ‖C a‖ ^ 2 * monoNormSq a :=
        Finset.sum_congr rfl fun a _ => mul_comm _ _
    _ = ∫ z, ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, C a * monoC a z‖ ^ 2 ∂(sphProb (D + 1)) :=
        (integral_form_sq D N C).symm
    _ = ∫ w, ‖∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l))‖ ^ 2 ∂(sphProb (D + 1)) := by
        simp only [hint]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

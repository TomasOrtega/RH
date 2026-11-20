import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountIntegrals
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMinkowskiCount
import GroundTheory.HeightsAndTheta.Heights.CovolumeGram
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix

noncomputable section

set_option linter.unusedSectionVars false

namespace SupBoundCount

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

/- English proof (translation)
Establish `hext : coneMap ℤ y = ((aeval fun _ : K => (Polynomial.X : Polynomial Ω)).restrictScalars ℤ).comp (mConeMap y)`. Use `MvPolynomial.algHom_ext fun p => ?_` and prove the remaining obligations. Simplify using `[coneMap, mConeMap]`. Introduce `f hf`. Express the relevant statement in the definitionally equal form `coneMap ℤ y f = 0`.

Rewrite using `[hext, AlgHom.comp_apply]`. Express the relevant statement in the definitionally equal form `_ = 0 at hf`. Establish `hf' : mConeMap y f = 0` using `hf`. Rewrite using `[hf', map_zero]`.
-/
theorem mCoordIdeal_le_coordIdeal (y : (Σ k, ι k) → Ω) : mCoordIdeal y ≤ coordIdeal ℤ y := by
  have hext : coneMap ℤ y =
      ((aeval fun _ : K => (Polynomial.X : Polynomial Ω)).restrictScalars ℤ).comp (mConeMap y) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp [coneMap, mConeMap]
  intro f hf
  change coneMap ℤ y f = 0
  rw [hext, AlgHom.comp_apply]
  change _ = 0 at hf
  have hf' : mConeMap y f = 0 := hf
  rw [hf', map_zero]

/- English proof (translation)
Rewrite using `[← algebraMap_int_eq, aeval_map_algebraMap]`.
-/
theorem aeval_map_int (y : (Σ k, ι k) → Ω) (g : MRing ι) : aeval y (map (Int.castRingHom ℚ) g) = aeval y g := by
  rw [← algebraMap_int_eq, aeval_map_algebraMap]

/- English proof (translation)
Take `⟨z₀, hz₀⟩` from `hne`. Establish `hblk : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`. Introduce `k`. Assume the negation of the conclusion as `hk`. Use `push_neg at hk`.

Take `⟨i, hi⟩` from `hz₀.1 k`. Apply `hi` to reduce the goal to its premises. Establish `hmem : (X ⟨k, i⟩ : MRing ι) ∈ mCoordIdeal y`. Express the relevant statement in the definitionally equal form `mConeMap y (X ⟨k, i⟩) = 0`. Simplify using `[mConeMap, hk i]`.

Simplify using `using hz₀.2 _ hmem`. Use `choose i₀ hi₀ using hblk`. Use `set u : MRing ι := ∏ k, X ⟨k, i₀ k⟩`. Establish `hu : aeval y u ≠ 0`. Simplify using `only [u, map_prod, aeval_X]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => hi₀ k`. Use `set b : Fin r → MvPolynomial (Σ k, ι k) ℚ := fun k => map (Int.castRingHom ℚ) (f k * u)`. Establish `hq : LinearIndependent ℚ fun k => aeval y (f k)` using `(LinearIndependent.iff_fractionRing ℤ ℚ).1 hli`. Establish `hs : LinearIndependent ℚ fun k => aeval y (b k)`. Establish `hinj : LinearMap.ker (LinearMap.mulRight ℚ (aeval y u)) = ⊥` using `LinearMap.ker_eq_bot.2 fun s t hst => mul_right_cancel₀ hu hst`.

Establish `heq : (fun k => aeval y (b k)) = (LinearMap.mulRight ℚ (aeval y u)) ∘ fun k => aeval y (f k)`. Use function extensionality and compare the values at `k`. Simplify using `[b, aeval_map_int, LinearMap.mulRight_apply]`. Rewrite using `[heq]`. Conclude with `hq.map' _ hinj`.

Use `coeff_eq_zero_of_vanish hs fun z hz => ?_` and prove the remaining obligations. Establish `hsec : ∀ k, secFun (b k) z = eval z (map (Int.castRingHom ℂ) (f k)) * eval z (map (Int.castRingHom ℂ) u)`. Introduce `k`. Simplify using `only [secFun, b, eval_map_int_rat, map_mul, eval_mul]`. Simplify using `only [hsec, ← mul_assoc, ← Finset.sum_mul]`.

Distinguish the cases in `hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0`. Rewrite using `[h z ⟨hz', fun g hg => hz g (mCoordIdeal_le_coordIdeal y hg)⟩, zero_mul]`. Use `push_neg at hz'`. Take `⟨k, hk⟩` from `hz'`. Use `mul_eq_zero_of_right _ ?_` and prove the remaining obligations.

Simplify using `only [u, map_prod, map_X, eval_prod, eval_X]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ k) (hk (i₀ k))`.
-/
theorem coeff_eq_zero {y : (Σ k, ι k) → Ω} {r : ℕ} {f : Fin r → MRing ι}
    (hli : LinearIndependent ℤ fun k => aeval y (f k)) (hne : (mcPts (mCoordIdeal y)).Nonempty)
    {a : Fin r → ℂ} (h : ∀ z ∈ mcPts (mCoordIdeal y), ∑ k, a k * eval z (map (Int.castRingHom ℂ) (f k)) = 0) :
    a = 0 := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne

  have hblk : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    by_contra hk
    push_neg at hk
    obtain ⟨i, hi⟩ := hz₀.1 k
    apply hi
    have hmem : (X ⟨k, i⟩ : MRing ι) ∈ mCoordIdeal y := by
      change mConeMap y (X ⟨k, i⟩) = 0
      simp [mConeMap, hk i]
    simpa using hz₀.2 _ hmem
  choose i₀ hi₀ using hblk
  set u : MRing ι := ∏ k, X ⟨k, i₀ k⟩
  have hu : aeval y u ≠ 0 := by
    simp only [u, map_prod, aeval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hi₀ k
  set b : Fin r → MvPolynomial (Σ k, ι k) ℚ := fun k => map (Int.castRingHom ℚ) (f k * u)
  have hq : LinearIndependent ℚ fun k => aeval y (f k) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hs : LinearIndependent ℚ fun k => aeval y (b k) := by
    have hinj : LinearMap.ker (LinearMap.mulRight ℚ (aeval y u)) = ⊥ :=
      LinearMap.ker_eq_bot.2 fun s t hst => mul_right_cancel₀ hu hst
    have heq : (fun k => aeval y (b k)) = (LinearMap.mulRight ℚ (aeval y u)) ∘ fun k => aeval y (f k) := by
      funext k
      simp [b, aeval_map_int, LinearMap.mulRight_apply]
    rw [heq]
    exact hq.map' _ hinj
  refine coeff_eq_zero_of_vanish hs fun z hz => ?_
  have hsec : ∀ k, secFun (b k) z = eval z (map (Int.castRingHom ℂ) (f k)) * eval z (map (Int.castRingHom ℂ) u) := by
    intro k
    simp only [secFun, b, eval_map_int_rat, map_mul, eval_mul]
  simp only [hsec, ← mul_assoc, ← Finset.sum_mul]
  by_cases hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [h z ⟨hz', fun g hg => hz g (mCoordIdeal_le_coordIdeal y hg)⟩, zero_mul]
  · push_neg at hz'
    obtain ⟨k, hk⟩ := hz'
    refine mul_eq_zero_of_right _ ?_
    simp only [u, map_prod, map_X, eval_prod, eval_X]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (hk (i₀ k))

variable {D : ℕ}

/- English proof (translation)
Simplify using `only [pairRe]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairRe_comm (A : HermLine ι) (n : ℕ) (f f' : MRing ι) (z : (Σ k, ι k) → ℂ) :
    pairRe A n f f' z = pairRe A n f' f z := by
  simp only [pairRe]
  ring

/- English proof (translation)
Simplify using `[comb, Finset.mul_sum, mul_assoc]`.
-/
theorem comb_smul {r : ℕ} (f : Fin r → MRing ι) (t : ℝ) (a : Fin r → ℝ) (z : (Σ k, ι k) → ℂ) :
    comb f (t • a) z = t * comb f a z := by
  simp [comb, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Rewrite using `[mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_smul {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (t : ℝ) (a : Fin r → ℝ) :
    (t • a) ⬝ᵥ (G *ᵥ (t • a)) = t ^ 2 * (a ⬝ᵥ (G *ᵥ a)) := by
  rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `comb`. Use `fun_prop`.
-/
theorem continuous_comb {r : ℕ} (f : Fin r → MRing ι) (z : (Σ k, ι k) → ℂ) :
    Continuous fun a : Fin r → ℝ => comb f a z := by
  unfold comb
  fun_prop

/- English proof (translation)
The claim follows from `continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)`.
-/
theorem continuous_quad {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) :
    Continuous fun a : Fin r → ℝ => a ⬝ᵥ (G *ᵥ a) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

/- English proof (translation)
Establish `hint : ∀ m : Fin r → ℤ, ‖comb f (fun k => (m k : ℝ)) z‖ / d.A.h z ^ n ≤ c * Real.sqrt ((fun k => (m k : ℝ)) ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ)))`. Introduce `m`. Rewrite using `[comb_int, ← blockL2Norm_sum_eq_sqrt_gram d n f hf m]`. Conclude with `hsup _ (isMultiHomog_zsum f m hf) z hz`. Establish `hrat : ∀ q : Fin r → ℚ, ‖comb f (fun k => (q k : ℝ)) z‖ / d.A.h z ^ n ≤ c * Real.sqrt ((fun k => (q k : ℝ)) ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (q k : ℝ)))`.

Introduce `q`. Use `set N : ℕ := ∏ k, (q k).den with hNdef`. Establish `hN : (0 : ℝ) < N` using `Nat.cast_pos.2 (Finset.prod_pos fun k _ => (q k).den_pos)`. Use `set m : Fin r → ℤ := fun k => (q k).num * ∏ j ∈ Finset.univ.erase k, ((q j).den : ℤ) with hmdef`. Establish `hm : (fun k => (q k : ℝ)) = (1 / (N : ℝ)) • fun k => (m k : ℝ)`.

Use function extensionality and compare the values at `k`. Establish `h1 : ((q k : ℚ) : ℝ) * ((q k).den : ℝ) = ((q k).num : ℝ)`. Conclude with `Rat.mul_den_eq_num (q k)` after adjusting the coercions. Establish `h2 : (N : ℝ) = ((q k).den : ℝ) * ∏ j ∈ Finset.univ.erase k, ((q j).den : ℝ)`. Rewrite using `[hNdef, ← Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ k)]`.

Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [Pi.smul_apply, smul_eq_mul, hmdef]`. Use `push_cast`. Rewrite using `[← h1, h2]`.

Establish `hd : ((q k).den : ℝ) ≠ 0` using `by exact_mod_cast (q k).den_nz`. Establish `hp : ∏ j ∈ Finset.univ.erase k, ((q j).den : ℝ) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => by exact_mod_cast (q j).den_nz`. Clear the denominators using the available nonvanishing facts. Use `set t : ℝ := 1 / (N : ℝ)`. Establish `ht : 0 < t` using `by positivity`.

Rewrite using `[hm, comb_smul, quad_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le, norm_mul, Complex.norm_of_nonneg ht.le, mul_div_assoc]`. Combine the equalities or inequalities in the displayed calculation. Establish `hd : DenseRange (fun q : Fin r → ℚ => fun k => (q k : ℝ))` using `DenseRange.piMap fun _ => Rat.denseRange_cast`. Use `hd.induction_on a ?_ hrat` and prove the remaining obligations. Conclude with `isClosed_le ((continuous_norm.comp (continuous_comb f z)).div_const _) (continuous_const.mul (Real.continuous_sqrt.comp (continuous_quad _)))`.
-/
theorem sup_real (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n F)
    (a : Fin r → ℝ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal d.y)) :
    ‖comb f a z‖ / d.A.h z ^ n ≤
      c * Real.sqrt (a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a)) := by
  have hint : ∀ m : Fin r → ℤ, ‖comb f (fun k => (m k : ℝ)) z‖ / d.A.h z ^ n ≤
      c * Real.sqrt ((fun k => (m k : ℝ)) ⬝ᵥ
        (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ))) := by
    intro m
    rw [comb_int, ← blockL2Norm_sum_eq_sqrt_gram d n f hf m]
    exact hsup _ (isMultiHomog_zsum f m hf) z hz
  have hrat : ∀ q : Fin r → ℚ, ‖comb f (fun k => (q k : ℝ)) z‖ / d.A.h z ^ n ≤
      c * Real.sqrt ((fun k => (q k : ℝ)) ⬝ᵥ
        (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (q k : ℝ))) := by
    intro q
    set N : ℕ := ∏ k, (q k).den with hNdef
    have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Finset.prod_pos fun k _ => (q k).den_pos)
    set m : Fin r → ℤ := fun k => (q k).num * ∏ j ∈ Finset.univ.erase k, ((q j).den : ℤ) with hmdef
    have hm : (fun k => (q k : ℝ)) = (1 / (N : ℝ)) • fun k => (m k : ℝ) := by
      funext k
      have h1 : ((q k : ℚ) : ℝ) * ((q k).den : ℝ) = ((q k).num : ℝ) := by
        exact_mod_cast Rat.mul_den_eq_num (q k)
      have h2 : (N : ℝ) = ((q k).den : ℝ) * ∏ j ∈ Finset.univ.erase k, ((q j).den : ℝ) := by
        rw [hNdef, ← Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ k)]
        push_cast
        rfl
      simp only [Pi.smul_apply, smul_eq_mul, hmdef]
      push_cast
      rw [← h1, h2]
      have hd : ((q k).den : ℝ) ≠ 0 := by exact_mod_cast (q k).den_nz
      have hp : ∏ j ∈ Finset.univ.erase k, ((q j).den : ℝ) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ => by exact_mod_cast (q j).den_nz
      field_simp
    set t : ℝ := 1 / (N : ℝ)
    have ht : 0 < t := by positivity
    rw [hm, comb_smul, quad_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le, norm_mul,
      Complex.norm_of_nonneg ht.le, mul_div_assoc]
    calc t * (‖comb f (fun k => (m k : ℝ)) z‖ / d.A.h z ^ n)
        ≤ t * (c * Real.sqrt ((fun k => (m k : ℝ)) ⬝ᵥ
          (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ)))) :=
          mul_le_mul_of_nonneg_left (hint m) ht.le
      _ = _ := by ring
  have hd : DenseRange (fun q : Fin r → ℚ => fun k => (q k : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on a ?_ hrat
  exact isClosed_le ((continuous_norm.comp (continuous_comb f z)).div_const _)
    (continuous_const.mul (Real.continuous_sqrt.comp (continuous_quad _)))

/- English proof (translation)
Use `d.vol.1` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨x⟩ : Nonempty d.R.X := by`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`. Establish `h1 : d.dV Set.univ = 1` using `measure_univ`.

Rewrite `h1` using `[Set.univ_eq_empty_iff.mpr h, measure_empty]`. Conclude with `zero_ne_one h1`. Conclude with `⟨_, blockPt_mem d x⟩`.
-/
theorem mcPts_nonempty (d : HSMBlockDatum D K ι Ω) : (mcPts (mCoordIdeal d.y)).Nonempty := by
  have := d.vol.1
  obtain ⟨x⟩ : Nonempty d.R.X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : d.dV Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  exact ⟨_, blockPt_mem d x⟩

/- English proof (translation)
Use `Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun a ha => ?_` and prove the remaining obligations. Use `Matrix.IsHermitian.ext fun k l => ?_` and prove the remaining obligations. Rewrite using `[star_trivial, blockGram_eq d n f hf, blockGram_eq d n f hf]`. Simplify using `only [pairRe_comm d.A n (f l) (f k)]`. Rewrite using `[star_trivial]`.

Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Apply `ha` to reduce the goal to its premises. Establish `hz : ∀ z ∈ mcPts (mCoordIdeal d.y), ∑ k, ((a k : ℝ) : ℂ) * eval z (map (Int.castRingHom ℂ) (f k)) = 0`. Introduce `z hz`.

Establish `h1` using `sup_real d n f hf hc hsup a hz`. Rewrite `h1` using `[Real.sqrt_eq_zero'.2 hle, mul_zero]`. Establish `hp : 0 < d.A.h z ^ n` using `pow_pos (d.A.pos z hz.1) n`. Establish `h2 : ‖comb f a z‖ ≤ 0`. Use `(div_le_iff₀ hp).1 h1` as an intermediate fact.

Simplify using `using this`. Conclude with `norm_eq_zero.1 (le_antisymm h2 (norm_nonneg _))`. Use `coeff_eq_zero hli (mcPts_nonempty d) hz` as an intermediate fact. Use function extensionality and compare the values at `k`. Use `congrFun this k` as an intermediate fact.

Simplify using `using this`.
-/
theorem gram_posDef (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (hli : LinearIndependent ℤ fun k => aeval d.y (f k))
    {c : ℝ} (hc : 0 < c)
    (hsup : ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n F) :
    (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun a ha => ?_
  · refine Matrix.IsHermitian.ext fun k l => ?_
    rw [star_trivial, blockGram_eq d n f hf, blockGram_eq d n f hf]
    simp only [pairRe_comm d.A n (f l) (f k)]
  · rw [star_trivial]
    by_contra hle
    push_neg at hle
    apply ha
    have hz : ∀ z ∈ mcPts (mCoordIdeal d.y),
        ∑ k, ((a k : ℝ) : ℂ) * eval z (map (Int.castRingHom ℂ) (f k)) = 0 := by
      intro z hz
      have h1 := sup_real d n f hf hc hsup a hz
      rw [Real.sqrt_eq_zero'.2 hle, mul_zero] at h1
      have hp : 0 < d.A.h z ^ n := pow_pos (d.A.pos z hz.1) n
      have h2 : ‖comb f a z‖ ≤ 0 := by
        have := (div_le_iff₀ hp).1 h1
        simpa using this
      exact norm_eq_zero.1 (le_antisymm h2 (norm_nonneg _))
    have := coeff_eq_zero hli (mcPts_nonempty d) hz
    funext k
    have := congrFun this k
    simpa using this

/- English proof (translation)
Establish `hu : IsUnit G.det` using `(hG.det_pos).ne'.isUnit`. Use `set a := G⁻¹ *ᵥ x with ha`. Establish `hGa : G *ᵥ a = x` using `by rw [ha, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]`. Establish `hq : 0 ≤ x ⬝ᵥ a`. Use `hG.posSemidef.dotProduct_mulVec_nonneg a` as an intermediate fact.

Rewrite `this` using `[star_trivial, hGa, dotProduct_comm]`. Conclude with `this`. Establish `h1` using `h a`. Rewrite `h1` using `[hGa, dotProduct_comm a x]`. Break down `hq.eq_or_lt with h0 | hpos` into its components or cases.

Rewrite using `[← h0]`. Check the signs of the components of the expression. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem quad_inv_le {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) {x : Fin r → ℝ} {c : ℝ}
    (h : ∀ a : Fin r → ℝ, (a ⬝ᵥ x) ^ 2 ≤ c ^ 2 * (a ⬝ᵥ (G *ᵥ a))) : x ⬝ᵥ (G⁻¹ *ᵥ x) ≤ c ^ 2 := by
  have hu : IsUnit G.det := (hG.det_pos).ne'.isUnit
  set a := G⁻¹ *ᵥ x with ha
  have hGa : G *ᵥ a = x := by rw [ha, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hq : 0 ≤ x ⬝ᵥ a := by
    have := hG.posSemidef.dotProduct_mulVec_nonneg a
    rw [star_trivial, hGa, dotProduct_comm] at this
    exact this
  have h1 := h a
  rw [hGa, dotProduct_comm a x] at h1
  rcases hq.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · nlinarith

/- English proof (translation)
Take `⟨G, hGdef⟩ : ∃ G, G = blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))` from `⟨_, rfl⟩`. Establish `hG : G.PosDef` using `hGdef ▸ gram_posDef d n f hf hli hc hsup`. Establish `hGe : ∀ k l, G k l = (1 / 2) * ((∫ x, pairRe d.A n (f k) (f l) (blockPt d x) ∂d.dV) + ∫ x, pairRe d.A n (f k) (f l) (conjPt (blockPt d x)) ∂d.dV)` using `fun k l => by`. Rewrite using `[hGdef]`. Conclude with `blockGram_eq d n f hf k l`.

Establish `hu : IsUnit G.det` using `hG.det_pos.ne'.isUnit`. Use `d.vol.1` as an intermediate fact. Establish `hr : (r : ℝ) = ∑ k, ∑ l, G⁻¹ k l * G l k * 1`. Establish `h1` using `congrArg Matrix.trace (nonsing_inv_mul G hu)`. Rewrite `h1` using `[trace_one, Fintype.card_fin]`.

Rewrite using `[← h1]`. Simplify using `[trace, mul_apply]`. Establish `hQ : ∀ a, 0 ≤ a ⬝ᵥ (G *ᵥ a)` using `fun a => by`. Simplify using `using hG.posSemidef.dotProduct_mulVec_nonneg a`. Establish `hpt : ∀ w ∈ mcPts (mCoordIdeal d.y), ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) w * 1 ≤ 2 * c ^ 2`.

Introduce `w hw`. Use `set H := d.A.h w ^ n with hH`. Establish `hH0 : 0 < H` using `pow_pos (d.A.pos w hw.1) n`. Use `set x : Fin r → ℝ := fun k => (eval w (map (Int.castRingHom ℂ) (f k))).re / H with hx`. Use `set y' : Fin r → ℝ := fun k => (eval w (map (Int.castRingHom ℂ) (f k))).im / H with hy'`.

Establish `hsum : ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) w * 1 = x ⬝ᵥ (G⁻¹ *ᵥ x) + y' ⬝ᵥ (G⁻¹ *ᵥ y')`. Simplify using `only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [pairRe, hx, hy', hH, pow_mul']`. Clear the denominators using the available nonvanishing facts.

Establish `hbd : ∀ a : Fin r → ℝ, ‖comb f a w‖ / H ≤ c * Real.sqrt (a ⬝ᵥ (G *ᵥ a))` using `fun a => by`. Rewrite using `[hGdef]`. Conclude with `sup_real d n f hf hc hsup a hw`. Establish `hxa : ∀ a, (a ⬝ᵥ x) ^ 2 ≤ c ^ 2 * (a ⬝ᵥ (G *ᵥ a))`. Introduce `a`.

Establish `e : a ⬝ᵥ x = (comb f a w).re / H`. Simplify using `only [dotProduct, hx, comb_re, Finset.sum_div, mul_div_assoc]`. Rewrite using `[e]`. Establish `h1 : |(comb f a w).re| / H ≤ c * Real.sqrt (a ⬝ᵥ (G *ᵥ a))` using `le_trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hH0.le) (hbd a)`. Establish `h0 : 0 ≤ |(comb f a w).re| / H` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Establish `hya : ∀ a, (a ⬝ᵥ y') ^ 2 ≤ c ^ 2 * (a ⬝ᵥ (G *ᵥ a))`. Introduce `a`. Establish `e : a ⬝ᵥ y' = (comb f a w).im / H`. Simplify using `only [dotProduct, hy', comb_im, Finset.sum_div, mul_div_assoc]`.

Rewrite using `[e]`. Establish `h1 : |(comb f a w).im| / H ≤ c * Real.sqrt (a ⬝ᵥ (G *ᵥ a))` using `le_trans (div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) hH0.le) (hbd a)`. Establish `h0 : 0 ≤ |(comb f a w).im| / H` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsum]`.

Use `quad_inv_le hG hxa` as an intermediate fact. Use `quad_inv_le hG hya` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hI : ∀ k l, Integrable (fun x => pairRe d.A n (f l) (f k) (blockPt d x)) d.dV ∧ Integrable (fun x => pairRe d.A n (f l) (f k) (conjPt (blockPt d x))) d.dV` using `fun k l => pairRe_integrable d n (hf l) (hf k)`. Establish `h1` using `sum_integral d.dV (fun k l => G⁻¹ k l) (fun _ _ => 1) (fun k l x => pairRe d.A n (f l) (f k) (blockPt d x)) fun k l => (hI k l).1`.

Establish `h2` using `sum_integral d.dV (fun k l => G⁻¹ k l) (fun _ _ => 1) (fun k l x => pairRe d.A n (f l) (f k) (conjPt (blockPt d x))) fun k l => (hI k l).2`. Establish `hr' : (r : ℝ) = (1 / 2) * ((∑ k, ∑ l, G⁻¹ k l * (∫ x, pairRe d.A n (f l) (f k) (blockPt d x) ∂d.dV) * 1) + ∑ k, ∑ l, G⁻¹ k l * (∫ x, pairRe d.A n (f l) (f k) (conjPt (blockPt d x)) ∂d.dV) * 1)`. Rewrite using `[hr, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[hGe]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hr', h1, h2]`. Establish `hint1 : Integrable (fun x => ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (blockPt d x) * 1) d.dV` using `integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => (((hI k l).1.const_mul _).mul_const _)`.

Establish `hint2 : Integrable (fun x => ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (conjPt (blockPt d x)) * 1) d.dV` using `integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => (((hI k l).2.const_mul _).mul_const _)`. Establish `i1 : ∫ x, ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (blockPt d x) * 1 ∂d.dV ≤ 2 * c ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `i2 : ∫ x, ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (conjPt (blockPt d x)) * 1 ∂d.dV ≤ 2 * c ^ 2`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rank_le (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (hli : LinearIndependent ℤ fun k => aeval d.y (f k))
    {c : ℝ} (hc : 0 < c)
    (hsup : ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n F) :
    (r : ℝ) ≤ 2 * c ^ 2 := by
  obtain ⟨G, hGdef⟩ : ∃ G, G = blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) := ⟨_, rfl⟩
  have hG : G.PosDef := hGdef ▸ gram_posDef d n f hf hli hc hsup
  have hGe : ∀ k l, G k l = (1 / 2) * ((∫ x, pairRe d.A n (f k) (f l) (blockPt d x) ∂d.dV) +
      ∫ x, pairRe d.A n (f k) (f l) (conjPt (blockPt d x)) ∂d.dV) := fun k l => by
    rw [hGdef]
    exact blockGram_eq d n f hf k l
  have hu : IsUnit G.det := hG.det_pos.ne'.isUnit
  have := d.vol.1
  have hr : (r : ℝ) = ∑ k, ∑ l, G⁻¹ k l * G l k * 1 := by
    have h1 := congrArg Matrix.trace (nonsing_inv_mul G hu)
    rw [trace_one, Fintype.card_fin] at h1
    rw [← h1]
    simp [trace, mul_apply]
  have hQ : ∀ a, 0 ≤ a ⬝ᵥ (G *ᵥ a) := fun a => by
    simpa using hG.posSemidef.dotProduct_mulVec_nonneg a
  have hpt : ∀ w ∈ mcPts (mCoordIdeal d.y),
      ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) w * 1 ≤ 2 * c ^ 2 := by
    intro w hw
    set H := d.A.h w ^ n with hH
    have hH0 : 0 < H := pow_pos (d.A.pos w hw.1) n
    set x : Fin r → ℝ := fun k => (eval w (map (Int.castRingHom ℂ) (f k))).re / H with hx
    set y' : Fin r → ℝ := fun k => (eval w (map (Int.castRingHom ℂ) (f k))).im / H with hy'
    have hsum : ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) w * 1 =
        x ⬝ᵥ (G⁻¹ *ᵥ x) + y' ⬝ᵥ (G⁻¹ *ᵥ y') := by
      simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [pairRe, hx, hy', hH, pow_mul']
      field_simp
    have hbd : ∀ a : Fin r → ℝ, ‖comb f a w‖ / H ≤ c * Real.sqrt (a ⬝ᵥ (G *ᵥ a)) := fun a => by
      rw [hGdef]
      exact sup_real d n f hf hc hsup a hw
    have hxa : ∀ a, (a ⬝ᵥ x) ^ 2 ≤ c ^ 2 * (a ⬝ᵥ (G *ᵥ a)) := by
      intro a
      have e : a ⬝ᵥ x = (comb f a w).re / H := by
        simp only [dotProduct, hx, comb_re, Finset.sum_div, mul_div_assoc]
      rw [e]
      have h1 : |(comb f a w).re| / H ≤ c * Real.sqrt (a ⬝ᵥ (G *ᵥ a)) :=
        le_trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hH0.le) (hbd a)
      have h0 : 0 ≤ |(comb f a w).re| / H := by positivity
      calc ((comb f a w).re / H) ^ 2 = (|(comb f a w).re| / H) ^ 2 := by rw [div_pow, div_pow, sq_abs]
        _ ≤ (c * Real.sqrt (a ⬝ᵥ (G *ᵥ a))) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = c ^ 2 * (a ⬝ᵥ (G *ᵥ a)) := by rw [mul_pow, Real.sq_sqrt (hQ a)]
    have hya : ∀ a, (a ⬝ᵥ y') ^ 2 ≤ c ^ 2 * (a ⬝ᵥ (G *ᵥ a)) := by
      intro a
      have e : a ⬝ᵥ y' = (comb f a w).im / H := by
        simp only [dotProduct, hy', comb_im, Finset.sum_div, mul_div_assoc]
      rw [e]
      have h1 : |(comb f a w).im| / H ≤ c * Real.sqrt (a ⬝ᵥ (G *ᵥ a)) :=
        le_trans (div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) hH0.le) (hbd a)
      have h0 : 0 ≤ |(comb f a w).im| / H := by positivity
      calc ((comb f a w).im / H) ^ 2 = (|(comb f a w).im| / H) ^ 2 := by rw [div_pow, div_pow, sq_abs]
        _ ≤ (c * Real.sqrt (a ⬝ᵥ (G *ᵥ a))) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = c ^ 2 * (a ⬝ᵥ (G *ᵥ a)) := by rw [mul_pow, Real.sq_sqrt (hQ a)]
    rw [hsum]
    have := quad_inv_le hG hxa
    have := quad_inv_le hG hya
    linarith
  have hI : ∀ k l, Integrable (fun x => pairRe d.A n (f l) (f k) (blockPt d x)) d.dV ∧
      Integrable (fun x => pairRe d.A n (f l) (f k) (conjPt (blockPt d x))) d.dV :=
    fun k l => pairRe_integrable d n (hf l) (hf k)
  have h1 := sum_integral d.dV (fun k l => G⁻¹ k l) (fun _ _ => 1)
    (fun k l x => pairRe d.A n (f l) (f k) (blockPt d x)) fun k l => (hI k l).1
  have h2 := sum_integral d.dV (fun k l => G⁻¹ k l) (fun _ _ => 1)
    (fun k l x => pairRe d.A n (f l) (f k) (conjPt (blockPt d x))) fun k l => (hI k l).2
  have hr' : (r : ℝ) = (1 / 2) *
      ((∑ k, ∑ l, G⁻¹ k l * (∫ x, pairRe d.A n (f l) (f k) (blockPt d x) ∂d.dV) * 1) +
        ∑ k, ∑ l, G⁻¹ k l * (∫ x, pairRe d.A n (f l) (f k) (conjPt (blockPt d x)) ∂d.dV) * 1) := by
    rw [hr, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hGe]
    ring
  rw [hr', h1, h2]
  have hint1 : Integrable (fun x => ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (blockPt d x) * 1) d.dV :=
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => (((hI k l).1.const_mul _).mul_const _)
  have hint2 : Integrable (fun x => ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (conjPt (blockPt d x)) * 1)
      d.dV :=
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => (((hI k l).2.const_mul _).mul_const _)
  have i1 : ∫ x, ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (blockPt d x) * 1 ∂d.dV ≤ 2 * c ^ 2 :=
    calc _ ≤ ∫ _, 2 * c ^ 2 ∂d.dV := integral_mono hint1 (integrable_const _) fun x => hpt _ (blockPt_mem d x)
      _ = 2 * c ^ 2 := by simp
  have i2 : ∫ x, ∑ k, ∑ l, G⁻¹ k l * pairRe d.A n (f l) (f k) (conjPt (blockPt d x)) * 1 ∂d.dV ≤ 2 * c ^ 2 :=
    calc _ ≤ ∫ _, 2 * c ^ 2 ∂d.dV := integral_mono hint2 (integrable_const _)
          fun x => hpt _ (conjPt_mem_mcPts (blockPt_mem d x))
      _ = 2 * c ^ 2 := by simp
  linarith

/- English proof (translation)
Use `set U : Matrix (Fin r) (Fin r) ℝ := ↑hG.1.eigenvectorUnitary`. Use `set M : Matrix (Fin r) (Fin r) ℝ := diagonal (fun i => Real.sqrt (hG.1.eigenvalues i)) * star U`. Establish `hMM : star M * M = G` using `by conv_rhs => rw [hG.1.spectral_theorem]`. Rewrite using `[Unitary.conjStarAlgAut_apply]`. Simplify using `only [M, U, star_mul, star_star, Matrix.star_eq_conjTranspose, diagonal_conjTranspose, star_trivial, conjTranspose_conjTranspose, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Simplify using `[Real.mul_self_sqrt (hG.eigenvalues_pos i).le]`. Use `⟨fun k => WithLp.toLp 2 (fun i => M i k), ?_⟩` and prove the remaining obligations.

Use extensionality with `k l`. Rewrite using `[Matrix.gram_apply, EuclideanSpace.inner_toLp_toLp, ← hMM]`. Simplify using `[dotProduct, mul_apply, Matrix.star_eq_conjTranspose, mul_comm]`.
-/
theorem exists_gram {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) :
    ∃ B : Fin r → EuclideanSpace ℝ (Fin r), Matrix.gram ℝ B = G := by
  classical
  set U : Matrix (Fin r) (Fin r) ℝ := ↑hG.1.eigenvectorUnitary
  set M : Matrix (Fin r) (Fin r) ℝ := diagonal (fun i => Real.sqrt (hG.1.eigenvalues i)) * star U
  have hMM : star M * M = G := by
    conv_rhs => rw [hG.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    simp only [M, U, star_mul, star_star, Matrix.star_eq_conjTranspose, diagonal_conjTranspose, star_trivial,
      conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
    congr 3
    funext i
    simp [Real.mul_self_sqrt (hG.eigenvalues_pos i).le]
  refine ⟨fun k => WithLp.toLp 2 (fun i => M i k), ?_⟩
  ext k l
  rw [Matrix.gram_apply, EuclideanSpace.inner_toLp_toLp, ← hMM]
  simp [dotProduct, mul_apply, Matrix.star_eq_conjTranspose, mul_comm]

/- English proof (translation)
Take `⟨B, hB⟩` from `exists_gram hG`. Establish `hli : LinearIndependent ℝ B` using `Matrix.linearIndependent_of_posDef_gram (hB ▸ hG)`. Establish `hcard : Fintype.card (Fin r) = Module.finrank ℝ (EuclideanSpace ℝ (Fin r))` using `by simp`. Take `⟨Bb, hBb⟩ : ∃ Bb : Module.Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)), ⇑Bb = B` from `⟨basisOfLinearIndependentOfCardEqFinrank' B hli hcard, coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _⟩`. Set `e : (Fin r → ℤ) → EuclideanSpace ℝ (Fin r)` to `fun m => ∑ k, m k • B k`.

Establish `hnorm : ∀ m, ‖e m‖ ^ 2 = (fun k => (m k : ℝ)) ⬝ᵥ (G *ᵥ fun k => (m k : ℝ))`. Introduce `m`. Rewrite using `[← real_inner_self_eq_norm_sq, ← hB]`. Simplify using `only [e, sum_inner, inner_sum, dotProduct, mulVec, Matrix.gram_apply, Finset.mul_sum, zsmul_eq_mul]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[← Int.cast_smul_eq_zsmul ℝ (m l), ← Int.cast_smul_eq_zsmul ℝ (m k), real_inner_smul_left, real_inner_smul_right, real_inner_comm (B l) (B k)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : ∀ x, x ∈ Submodule.span ℤ (Set.range Bb) ↔ ∃ m, e m = x`. Introduce `x`. Rewrite using `[hBb, Submodule.mem_span_range_iff_exists_fun]`.

Establish `hliZ : LinearIndependent ℤ B` using `hli.restrict_scalars' ℤ`. Establish `heinj : Function.Injective e`. Introduce `m m' h`. Establish `h0 : ∑ k, (m k - m' k) • B k = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`.

Conclude with `sub_eq_zero.2 h`. Use function extensionality and compare the values at `k`. Conclude with `sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hliZ _ h0 k)`. Establish `hfinP : {m | P m}.Finite`. Use `((MinkowskiCount.finite_latticePoints (Submodule.span ℤ (Set.range Bb)) 1).preimage heinj.injOn).subset fun m hm => ⟨(hmem _).2 ⟨m, rfl⟩, ?_⟩` and prove the remaining obligations.

Establish `h1` using `hP2 m hm`. Rewrite `h1` using `[← hnorm]`. Use polynomial arithmetic with `[norm_nonneg (e m)]`. Use `⟨hfinP, ?_⟩` and prove the remaining obligations. Establish `hM` using `MinkowskiCount.proof.1 (EuclideanSpace ℝ (Fin r)) (Submodule.span ℤ (Set.range Bb)) ρ hρ`.

Rewrite `hM` using `[finrank_euclideanSpace_fin]`. Establish `hcov : ZLattice.covolume (Submodule.span ℤ (Set.range Bb)) = Real.sqrt G.det`. Rewrite using `[covolume_eq_sqrt_det_gram _ (Bb.restrictScalars ℤ), ← hB]`. Use `congr 3`. Use function extensionality and compare the values at `k`.

Simplify using `[Module.Basis.restrictScalars_apply, hBb]`. Rewrite `hM` using `[hcov, Real.log_sqrt hG.det_pos.le]`. Establish `hT : {x | x ∈ Submodule.span ℤ (Set.range Bb) ∧ ‖x‖ ≤ ρ} = e '' {m | ‖e m‖ ≤ ρ}`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hxn⟩`. Take `⟨m, rfl⟩` from `(hmem x).1 hx`. Conclude with `⟨m, hxn, rfl⟩`. Introduce and unpack `⟨m, hm, rfl⟩`.

Conclude with `⟨(hmem _).2 ⟨m, rfl⟩, hm⟩`. Rewrite `hM` using `[hT, Set.ncard_image_of_injective _ heinj]`. Establish `hsub : {m | ‖e m‖ ≤ ρ} ⊆ {m | P m}` using `fun m hm => by`. Use `hP1 m ?_` and prove the remaining obligations. Rewrite using `[← hnorm]`.

Establish `: ‖e m‖ ≤ ρ` using `hm`. Use polynomial arithmetic with `[norm_nonneg (e m)]`. Establish `hpos : 0 < ({m | ‖e m‖ ≤ ρ}.ncard : ℝ)`. Establish `h0 : (0 : Fin r → ℤ) ∈ {m | ‖e m‖ ≤ ρ}`. Simplify using `[e, hρ.le]`.

Conclude with `Set.ncard_pos (hfinP.subset hsub) |>.2 ⟨_, h0⟩` after adjusting the coercions. Establish `hle : ({m | ‖e m‖ ≤ ρ}.ncard : ℝ) ≤ (Nat.card {m // P m} : ℝ)` using `by show _ ≤ ((Nat.card ↥{m | P m} : ℕ) : ℝ)`. Rewrite using `[Nat.card_coe_set_eq]`. Conclude with `Set.ncard_le_ncard hsub hfinP` after adjusting the coercions. Use `Real.log_le_log hpos hle` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem count_of_gram {r : ℕ} {G : Matrix (Fin r) (Fin r) ℝ} (hG : G.PosDef) {ρ : ℝ} (hρ : 0 < ρ)
    (P : (Fin r → ℤ) → Prop)
    (hP1 : ∀ m : Fin r → ℤ, (fun k => (m k : ℝ)) ⬝ᵥ (G *ᵥ fun k => (m k : ℝ)) ≤ ρ ^ 2 → P m)
    (hP2 : ∀ m : Fin r → ℤ, P m → (fun k => (m k : ℝ)) ⬝ᵥ (G *ᵥ fun k => (m k : ℝ)) ≤ 1) :
    {m | P m}.Finite ∧
      Real.log (unitBallVolume r) + r * Real.log (ρ / 2) - (1 / 2) * Real.log G.det ≤
        Real.log (Nat.card {m // P m}) := by
  classical
  obtain ⟨B, hB⟩ := exists_gram hG
  have hli : LinearIndependent ℝ B := Matrix.linearIndependent_of_posDef_gram (hB ▸ hG)
  have hcard : Fintype.card (Fin r) = Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) := by simp
  obtain ⟨Bb, hBb⟩ : ∃ Bb : Module.Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)), ⇑Bb = B :=
    ⟨basisOfLinearIndependentOfCardEqFinrank' B hli hcard, coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _⟩
  let e : (Fin r → ℤ) → EuclideanSpace ℝ (Fin r) := fun m => ∑ k, m k • B k
  have hnorm : ∀ m, ‖e m‖ ^ 2 = (fun k => (m k : ℝ)) ⬝ᵥ (G *ᵥ fun k => (m k : ℝ)) := by
    intro m
    rw [← real_inner_self_eq_norm_sq, ← hB]
    simp only [e, sum_inner, inner_sum, dotProduct, mulVec, Matrix.gram_apply, Finset.mul_sum, zsmul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ (m l), ← Int.cast_smul_eq_zsmul ℝ (m k), real_inner_smul_left,
      real_inner_smul_right, real_inner_comm (B l) (B k)]
    ring
  have hmem : ∀ x, x ∈ Submodule.span ℤ (Set.range Bb) ↔ ∃ m, e m = x := by
    intro x
    rw [hBb, Submodule.mem_span_range_iff_exists_fun]
  have hliZ : LinearIndependent ℤ B := hli.restrict_scalars' ℤ
  have heinj : Function.Injective e := by
    intro m m' h
    have h0 : ∑ k, (m k - m' k) • B k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 h
    funext k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hliZ _ h0 k)
  have hfinP : {m | P m}.Finite := by
    refine ((MinkowskiCount.finite_latticePoints (Submodule.span ℤ (Set.range Bb)) 1).preimage
      heinj.injOn).subset fun m hm => ⟨(hmem _).2 ⟨m, rfl⟩, ?_⟩
    have h1 := hP2 m hm
    rw [← hnorm] at h1
    nlinarith [norm_nonneg (e m)]
  refine ⟨hfinP, ?_⟩
  have hM := MinkowskiCount.proof.1 (EuclideanSpace ℝ (Fin r)) (Submodule.span ℤ (Set.range Bb)) ρ hρ
  rw [finrank_euclideanSpace_fin] at hM
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range Bb)) = Real.sqrt G.det := by
    rw [covolume_eq_sqrt_det_gram _ (Bb.restrictScalars ℤ), ← hB]
    congr 3
    funext k
    simp [Module.Basis.restrictScalars_apply, hBb]
  rw [hcov, Real.log_sqrt hG.det_pos.le] at hM
  have hT : {x | x ∈ Submodule.span ℤ (Set.range Bb) ∧ ‖x‖ ≤ ρ} = e '' {m | ‖e m‖ ≤ ρ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hx, hxn⟩
      obtain ⟨m, rfl⟩ := (hmem x).1 hx
      exact ⟨m, hxn, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨(hmem _).2 ⟨m, rfl⟩, hm⟩
  rw [hT, Set.ncard_image_of_injective _ heinj] at hM
  have hsub : {m | ‖e m‖ ≤ ρ} ⊆ {m | P m} := fun m hm => by
    refine hP1 m ?_
    rw [← hnorm]
    have : ‖e m‖ ≤ ρ := hm
    nlinarith [norm_nonneg (e m)]
  have hpos : 0 < ({m | ‖e m‖ ≤ ρ}.ncard : ℝ) := by
    have h0 : (0 : Fin r → ℤ) ∈ {m | ‖e m‖ ≤ ρ} := by
      simp [e, hρ.le]
    exact_mod_cast Set.ncard_pos (hfinP.subset hsub) |>.2 ⟨_, h0⟩
  have hle : ({m | ‖e m‖ ≤ ρ}.ncard : ℝ) ≤ (Nat.card {m // P m} : ℝ) := by
    show _ ≤ ((Nat.card ↥{m | P m} : ℕ) : ℝ)
    rw [Nat.card_coe_set_eq]
    exact_mod_cast Set.ncard_le_ncard hsub hfinP
  have := Real.log_le_log hpos hle
  linarith

/- English proof (translation)
Introduce `m hm`. Simplify using `at hm`.
-/
theorem isMultiHomog_zero' (e : K → ℕ) : IsMultiHomog (0 : MRing ι) e := by
  intro m hm
  simp at hm

/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hf m h k`. Conclude with `hg m h k`.
-/
theorem isMultiHomog_add' {f g : MRing ι} {e : K → ℕ} (hf : IsMultiHomog f e) (hg : IsMultiHomog g e) :
    IsMultiHomog (f + g) e := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

/- English proof (translation)
Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨0, isMultiHomog_zero' e, map_zero _⟩`. Consider the case `add x z _ _ hx hz`. Take `⟨g, hg, rfl⟩` from `hx`.

Take `⟨g', hg', rfl⟩` from `hz`. Conclude with `⟨g + g', isMultiHomog_add' hg hg', map_add _ _ _⟩`. Consider the case `smul a x _ hx`. Take `⟨g, hg, rfl⟩` from `hx`. Use `⟨a • g, fun m hm => hg m (MvPolynomial.support_smul hm), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_zsmul]`.
-/
theorem exists_form_of_mem (y : (Σ k, ι k) → Ω) (e : K → ℕ) {s : Ω}
    (hs : s ∈ Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g e ∧ aeval y g = s}) :
    ∃ g : MRing ι, IsMultiHomog g e ∧ aeval y g = s := by
  induction hs using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, isMultiHomog_zero' e, map_zero _⟩
  | add x z _ _ hx hz =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', rfl⟩ := hz
    exact ⟨g + g', isMultiHomog_add' hg hg', map_add _ _ _⟩
  | smul a x _ hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    refine ⟨a • g, fun m hm => hg m (MvPolynomial.support_smul hm), ?_⟩
    rw [map_zsmul]

/- English proof (translation)
Use `set e := blockDeg k₀ n with he`. Use `set N : Submodule ℤ Ω := Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g e ∧ aeval y g = s} with hN`. Use `set Ms : Set ((Σ k, ι k) →₀ ℕ) := {m | ∀ k, ∑ i, m ⟨k, i⟩ = e k} with hMs`. Establish `hMsf : Ms.Finite`. Use `((Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Iic (e p.1)) fun p => Set.finite_Iic _).preimage (DFunLike.coe_injective.injOn)).subset fun m hm p _ => ?_` and prove the remaining obligations.

Take `⟨k, i⟩` from `p`. Use `show m ⟨k, i⟩ ≤ e k`. Rewrite using `[← hm k]`. Conclude with `Finset.single_le_sum (f := fun j => m ⟨k, j⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Use `set T : Set Ω := (fun m => aeval y (monomial m (1 : ℤ))) '' Ms with hT`.

Establish `hTf : T.Finite` using `hMsf.image _`. Establish `hle : N ≤ Submodule.span ℤ T`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Rewrite using `[g.as_sum, map_sum]`.

Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[← mul_one (coeff m g), ← smul_eq_mul, ← smul_monomial, map_zsmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, fun k => hg m hm k, rfl⟩)`. Establish `: IsNoetherian ℤ (Submodule.span ℤ T)` using `isNoetherian_span_of_finite ℤ hTf`. Establish `: IsNoetherian ℤ N` using `isNoetherian_of_le hle`.

Set `bN` to `Module.finBasis ℤ N`. Establish `hval : ∀ j, ∃ g : MRing ι, IsMultiHomog g e ∧ aeval y g = (bN j : Ω)` using `fun j => exists_form_of_mem y e (bN j).2`. Use `choose g hg hgy using hval`. Use `⟨⟨Module.finrank ℤ N, fun j => map (Int.castRingHom ℚ) (g j)⟩, fun j => ⟨g j, hg j, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (fun j => aeval y (map (Int.castRingHom ℚ) (g j))) = N.subtype ∘ bN`.

Use function extensionality and compare the values at `j`. Simplify using `[aeval_map_int, hgy]`. Rewrite using `[h1]`. Conclude with `bN.linearIndependent.map' _ (Submodule.ker_subtype _)`. Establish `h1 : (Set.range fun j => aeval y (map (Int.castRingHom ℚ) (g j))) = N.subtype '' Set.range bN`.

Rewrite using `[← Set.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `[aeval_map_int, hgy]`. Rewrite using `[h1, Submodule.span_image, bN.span_eq, Submodule.map_subtype_top]`.

Both sides reduce to the same expression.
-/
theorem exists_isSecBasisM (y : (Σ k, ι k) → Ω) (k₀ : K) (n : ℕ) :
    ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM y k₀ n p.2 := by
  classical
  set e := blockDeg k₀ n with he
  set N : Submodule ℤ Ω := Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g e ∧ aeval y g = s} with hN
  set Ms : Set ((Σ k, ι k) →₀ ℕ) := {m | ∀ k, ∑ i, m ⟨k, i⟩ = e k} with hMs
  have hMsf : Ms.Finite := by
    refine ((Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Iic (e p.1)) fun p => Set.finite_Iic _).preimage
      (DFunLike.coe_injective.injOn)).subset fun m hm p _ => ?_
    obtain ⟨k, i⟩ := p
    show m ⟨k, i⟩ ≤ e k
    rw [← hm k]
    exact Finset.single_le_sum (f := fun j => m ⟨k, j⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set T : Set Ω := (fun m => aeval y (monomial m (1 : ℤ))) '' Ms with hT
  have hTf : T.Finite := hMsf.image _
  have hle : N ≤ Submodule.span ℤ T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    rw [g.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [← mul_one (coeff m g), ← smul_eq_mul, ← smul_monomial, map_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, fun k => hg m hm k, rfl⟩)
  have : IsNoetherian ℤ (Submodule.span ℤ T) := isNoetherian_span_of_finite ℤ hTf
  have : IsNoetherian ℤ N := isNoetherian_of_le hle
  let bN := Module.finBasis ℤ N
  have hval : ∀ j, ∃ g : MRing ι, IsMultiHomog g e ∧ aeval y g = (bN j : Ω) := fun j =>
    exists_form_of_mem y e (bN j).2
  choose g hg hgy using hval
  refine ⟨⟨Module.finrank ℤ N, fun j => map (Int.castRingHom ℚ) (g j)⟩, fun j => ⟨g j, hg j, rfl⟩, ?_, ?_⟩
  · have h1 : (fun j => aeval y (map (Int.castRingHom ℚ) (g j))) = N.subtype ∘ bN := by
      funext j
      simp [aeval_map_int, hgy]
    rw [h1]
    exact bN.linearIndependent.map' _ (Submodule.ker_subtype _)
  · have h1 : (Set.range fun j => aeval y (map (Int.castRingHom ℚ) (g j))) = N.subtype '' Set.range bN := by
      rw [← Set.range_comp]
      congr 1
      funext j
      simp [aeval_map_int, hgy]
    rw [h1, Submodule.span_image, bN.span_eq, Submodule.map_subtype_top]
    rfl

/- English proof (translation)
Rewrite using `[← hb.2.2]`. Establish `e : (Submodule.span ℤ (Set.range fun j => aeval y (b j))).toAddSubgroup ≃+ (Submodule.span ℤ (Set.range fun j => aeval y (b j)))` using `AddEquiv.refl _`. Rewrite using `[e.toIntLinearEquiv.finrank_eq, finrank_span_eq_card hb.2.1, Fintype.card_fin]`.
-/
theorem finrank_secM {y : (Σ k, ι k) → Ω} {k₀ : K} {n r : ℕ} {b : Fin r → MvPolynomial (Σ k, ι k) ℚ}
    (hb : IsSecBasisM y k₀ n b) : Module.finrank ℤ (secM y (blockDeg k₀ n)) = r := by
  rw [← hb.2.2]
  have e : (Submodule.span ℤ (Set.range fun j => aeval y (b j))).toAddSubgroup ≃+
      (Submodule.span ℤ (Set.range fun j => aeval y (b j))) := AddEquiv.refl _
  rw [e.toIntLinearEquiv.finrank_eq, finrank_span_eq_card hb.2.1, Fintype.card_fin]

end SupBoundCount

end

end GroundTheory.Heights₂.Heights.HilbertSamuel

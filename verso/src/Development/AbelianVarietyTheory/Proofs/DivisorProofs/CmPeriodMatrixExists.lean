import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

/- English proof (translation)
Introduce `K _ _ d δ io hK hd hδ E _ _ _ _ I _ φ hφ hio c y hc e`. Establish `hEK : Module.finrank K E = Module.finrank ℚ (FR E)`. Establish `h1 : Module.finrank ℚ E = 2 * Module.finrank ℚ (FR E)`. Rewrite using `[← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]`. Establish `h2 : Module.finrank ℚ K * Module.finrank K E = Module.finrank ℚ E` using `Module.finrank_mul_finrank ℚ K E`.

Rewrite `h2` using `[hK, h1]`. Use linear arithmetic over natural numbers and integers. Generalize the expression as in `Module.finrank ℚ (FR E) = f at e hEK ⊢`. Set `b` to `Module.finBasisOfFinrankEq K E hEK`. Take `⟨m, hm0, hm⟩` from `exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b)`.

Take `⟨N, hN0, hNmem, -⟩` from `GlobalTheory.CMVal.LatBound.lattice_between E c hc y`. Establish `hint : ∀ j, IsIntegral ℤ (m • b j)` using `fun j => hm _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))`. Establish `hδint : IsIntegral ℤ (algebraMap K E δ)`. Use `⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Polynomial.monic_X_pow_add_C _ two_ne_zero`.

Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]`. Rewrite using `[← map_pow, hδ]`. Simplify using the standard rewrite rules. Set `u : Fin f → 𝓞 E` to `fun j => ⟨m • b j, hint j⟩`. Set `v : Fin f → 𝓞 E` to `fun j => ⟨algebraMap K E δ * (m • b j), hδint.mul (hint j)⟩`.

Set `w : Fin f → E` to `fun j => (N : E) * (m • b j)`. Establish `hw : ∀ j, w j ∈ lattice c y` using `fun j => hNmem (u j)`. Establish `hδw : ∀ j, algebraMap K E δ * w j ∈ lattice c y` using `fun j => by`. Use `hNmem (v j)` as an intermediate fact. Simplify `this` using `[w, v, mul_left_comm]`.

Establish `hs : ∀ _j : Fin f, IsUnit ((N : K) * (m : K))` using `fun _ => by`. Use `IsUnit.mk0 _ (mul_ne_zero (by exact_mod_cast hN0.ne') (by exact_mod_cast hm0))` and prove the remaining obligations. Set `b'` to `b.isUnitSMul hs`. Establish `hb' : ∀ j, b' j = w j` using `fun j => by`. Simplify using `only [b', Module.Basis.isUnitSMul_apply, w, Algebra.smul_def, zsmul_eq_mul, map_mul, map_natCast, map_intCast]`.

Simplify using `only [algebraMap_int_eq, eq_intCast]`. Expand and normalize the polynomial expressions, which then agree. Set `A : Matrix (Fin f) (Fin f) ℂ` to `fun i j => φ (e i) (w j)`. Use `⟨Matrix.mulVecLin A, ?_, ?_⟩` and prove the remaining obligations. Use `show Function.Surjective A.mulVec`.

Rewrite using `[Matrix.mulVec_surjective_iff_isUnit, ← Matrix.linearIndependent_rows_iff_isUnit]`. Establish `hinj : Function.Injective (fun i : Fin f => ((φ (e i) : E →+* ℂ) : E →* ℂ))`. Introduce `i i' h`. Establish `h' : φ (e i) = φ (e i')` using `RingHom.ext fun x => DFunLike.congr_fun h x`. Take `⟨k, -, hk⟩` from `hφ (φ (e i))`.

Establish `a1` using `hk (e i) (Or.inl rfl)`. Establish `a2` using `hk (e i') (Or.inl h')`. Conclude with `e.injective (a1.trans a2.symm)`. Establish `li : LinearIndependent ℂ (fun i : Fin f => ((((φ (e i) : E →+* ℂ) : E →* ℂ)) : E → ℂ))` using `(linearIndependent_monoidHom E ℂ).comp _ hinj`. Rewrite `li`, the goal using `[Fintype.linearIndependent_iff]`.

Introduce `g hg i`. Use `li g ?_ i` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Establish `hrow : ∀ j, ∑ i, g i * φ (e i) (w j) = 0` using `fun j => by`. Use `congrFun hg j` as an intermediate fact.

Simplify `this` using `[Matrix.row, A, Finset.sum_apply]`. Establish `hx : x = ∑ j, b'.repr x j • w j` using `by conv_lhs => rw [← b'.sum_repr x]`. Simplify using `only [hb']`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, MonoidHom.coe_coe, smul_eq_mul, Pi.zero_apply]`. Rewrite using `[hx]`.

Simplify using `only [map_sum, Algebra.smul_def, map_mul]`. Establish `hio' : ∀ i (k : K), φ (e i) (algebraMap K E k) = io k` using `fun i k => by`. Rewrite using `[← hio (e i)]`. Both sides reduce to the same expression. Simplify using `only [hio']`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Use `_ = 0 := by simp [hrow]`. Introduce `z hz choose a a' ha using hz`. Use `⟨∑ j, ((a j : E) * w j + (a' j : E) * (algebraMap K E δ * w j)), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← coe_latticeSub]`. Use `AddSubgroup.sum_mem _ fun j _ => AddSubgroup.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[← zsmul_eq_mul]`. Conclude with `AddSubgroup.zsmul_mem _ (hw j) _`. Rewrite using `[← zsmul_eq_mul]`.

Conclude with `AddSubgroup.zsmul_mem _ (hδw j) _`. Use function extensionality and compare the values at `i`. Establish `hio' : φ (e i) (algebraMap K E δ) = io δ` using `by rw [← hio (e i)]; rfl`. Use `show A.mulVec z i = φ (e i) _`. Simplify using `only [Matrix.mulVec, dotProduct, A, map_sum, map_add, map_mul, map_intCast, hio', ha]`.

Use `Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem surj_lattice : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ e : Fin (Module.finrank ℚ (FR E)) ≃ I,
      ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ), Function.Surjective M ∧
        ∀ z, (∀ j, ∃ a b : ℤ, z j = a + b * io δ) → ∃ x ∈ lattice c y, M z = fun j ↦ φ (e j) x := by
  intro K _ _ d δ io hK hd hδ E _ _ _ _ I _ φ hφ hio c y hc e
  classical
  have hEK : Module.finrank K E = Module.finrank ℚ (FR E) := by
    have h1 : Module.finrank ℚ E = 2 * Module.finrank ℚ (FR E) := by
      rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
        Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
    have h2 : Module.finrank ℚ K * Module.finrank K E = Module.finrank ℚ E := Module.finrank_mul_finrank ℚ K E
    rw [hK, h1] at h2
    omega
  generalize Module.finrank ℚ (FR E) = f at e hEK ⊢
  let b := Module.finBasisOfFinrankEq K E hEK
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b)
  obtain ⟨N, hN0, hNmem, -⟩ := GlobalTheory.CMVal.LatBound.lattice_between E c hc y

  have hint : ∀ j, IsIntegral ℤ (m • b j) := fun j => hm _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hδint : IsIntegral ℤ (algebraMap K E δ) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      rw [← map_pow, hδ]; simp
  let u : Fin f → 𝓞 E := fun j => ⟨m • b j, hint j⟩
  let v : Fin f → 𝓞 E := fun j => ⟨algebraMap K E δ * (m • b j), hδint.mul (hint j)⟩
  let w : Fin f → E := fun j => (N : E) * (m • b j)
  have hw : ∀ j, w j ∈ lattice c y := fun j => hNmem (u j)
  have hδw : ∀ j, algebraMap K E δ * w j ∈ lattice c y := fun j => by
    have := hNmem (v j)
    simpa [w, v, mul_left_comm] using this

  have hs : ∀ _j : Fin f, IsUnit ((N : K) * (m : K)) := fun _ => by
    refine IsUnit.mk0 _ (mul_ne_zero (by exact_mod_cast hN0.ne') (by exact_mod_cast hm0))
  let b' := b.isUnitSMul hs
  have hb' : ∀ j, b' j = w j := fun j => by
    simp only [b', Module.Basis.isUnitSMul_apply, w, Algebra.smul_def, zsmul_eq_mul, map_mul, map_natCast, map_intCast]
    simp only [algebraMap_int_eq, eq_intCast]
    ring
  let A : Matrix (Fin f) (Fin f) ℂ := fun i j => φ (e i) (w j)
  refine ⟨Matrix.mulVecLin A, ?_, ?_⟩
  ·
    show Function.Surjective A.mulVec
    rw [Matrix.mulVec_surjective_iff_isUnit, ← Matrix.linearIndependent_rows_iff_isUnit]
    have hinj : Function.Injective (fun i : Fin f => ((φ (e i) : E →+* ℂ) : E →* ℂ)) := by
      intro i i' h
      have h' : φ (e i) = φ (e i') := RingHom.ext fun x => DFunLike.congr_fun h x
      obtain ⟨k, -, hk⟩ := hφ (φ (e i))
      have a1 := hk (e i) (Or.inl rfl)
      have a2 := hk (e i') (Or.inl h')
      exact e.injective (a1.trans a2.symm)
    have li : LinearIndependent ℂ (fun i : Fin f => ((((φ (e i) : E →+* ℂ) : E →* ℂ)) : E → ℂ)) :=
      (linearIndependent_monoidHom E ℂ).comp _ hinj
    rw [Fintype.linearIndependent_iff] at li ⊢
    intro g hg i
    refine li g ?_ i
    funext x
    have hrow : ∀ j, ∑ i, g i * φ (e i) (w j) = 0 := fun j => by
      have := congrFun hg j
      simpa [Matrix.row, A, Finset.sum_apply] using this
    have hx : x = ∑ j, b'.repr x j • w j := by
      conv_lhs => rw [← b'.sum_repr x]
      simp only [hb']
    simp only [Finset.sum_apply, Pi.smul_apply, MonoidHom.coe_coe, smul_eq_mul, Pi.zero_apply]
    rw [hx]
    simp only [map_sum, Algebra.smul_def, map_mul]
    have hio' : ∀ i (k : K), φ (e i) (algebraMap K E k) = io k := fun i k => by
      rw [← hio (e i)]; rfl
    simp only [hio']
    calc ∑ i, g i * ∑ j, io (b'.repr x j) * φ (e i) (w j)
        = ∑ j, io (b'.repr x j) * ∑ i, g i * φ (e i) (w j) := by
          simp only [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by simp [hrow]
  · intro z hz
    choose a a' ha using hz
    refine ⟨∑ j, ((a j : E) * w j + (a' j : E) * (algebraMap K E δ * w j)), ?_, ?_⟩
    · rw [← coe_latticeSub]
      refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.add_mem _ ?_ ?_
      · rw [← zsmul_eq_mul]; exact AddSubgroup.zsmul_mem _ (hw j) _
      · rw [← zsmul_eq_mul]; exact AddSubgroup.zsmul_mem _ (hδw j) _
    · funext i
      have hio' : φ (e i) (algebraMap K E δ) = io δ := by rw [← hio (e i)]; rfl
      show A.mulVec z i = φ (e i) _
      simp only [Matrix.mulVec, dotProduct, A, map_sum, map_add, map_mul, map_intCast, hio', ha]
      refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.LatModel

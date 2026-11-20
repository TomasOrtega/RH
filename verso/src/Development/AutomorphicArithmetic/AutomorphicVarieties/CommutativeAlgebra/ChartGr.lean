import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerPow

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Introduce `g hg`. Rewrite `hg` using `[pow_two]`. Establish `hone : ∀ a ∈ RingHom.ker x, 1 ≤ (φ a).order`. Introduce `a ha`. Establish `hxa : x a = 0` using `ha`.

Conclude with `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by rw [hc, hxa, map_zero])`. Establish `hord : ((2 : ℕ) : ℕ∞) ≤ (φ g).order`. Use `Submodule.mul_induction_on (C := fun g => ((2 : ℕ) : ℕ∞) ≤ (φ g).order) hg ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`. Rewrite using `[map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Introduce `a b ha hb`. Rewrite using `[map_add]`. Conclude with `le_trans (le_min ha hb) MvPowerSeries.min_order_le_add`. Apply `MvPowerSeries.coeff_of_lt_order` to reduce the goal to its premises.

Rewrite using `[Finsupp.degree_single]`. Conclude with `lt_of_lt_of_le (by norm_num) hord`.
-/
private lemma lin_coeff_sq {O R K τ : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]
    (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries τ K)
    (hc : ∀ f, constantCoeff (φ f) = algebraMap O K (x f)) (i : τ) :
    ∀ g ∈ RingHom.ker x ^ 2, coeff (Finsupp.single i 1) (φ g) = 0 := by
  intro g hg
  rw [pow_two] at hg
  have hone : ∀ a ∈ RingHom.ker x, 1 ≤ (φ a).order := by
    intro a ha
    have hxa : x a = 0 := ha
    exact MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by rw [hc, hxa, map_zero])
  have hord : ((2 : ℕ) : ℕ∞) ≤ (φ g).order := by
    refine Submodule.mul_induction_on (C := fun g => ((2 : ℕ) : ℕ∞) ≤ (φ g).order) hg ?_ ?_
    · intro a ha b hb
      rw [map_mul]
      calc ((2 : ℕ) : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ (φ a).order + (φ b).order := add_le_add (hone a ha) (hone b hb)
        _ ≤ (φ a * φ b).order := MvPowerSeries.le_order_mul
    · intro a b ha hb
      rw [map_add]
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add
  apply MvPowerSeries.coeff_of_lt_order
  rw [Finsupp.degree_single]
  exact lt_of_lt_of_le (by norm_num) hord

/- English proof (translation)
Introduce `O X R _ _ _ _ _ _ W h _ _ τ wt φ hφ`. Take `⟨hk, hsurj⟩` from `ker_pow O R X W h 2`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j f hf`. Conclude with `hφ.graded j f.val hf`.

Introduce `f`. Conclude with `hφ.const f.val`. Introduce `i`. Take `⟨g, hg1, hg2⟩` from `hφ.onto i`. Take `⟨y, hy⟩` from `hsurj g`.

Establish `hd : ∀ i', coeff (Finsupp.single i' 1) (φ (g - y)) = 0` using `fun i' => lin_coeff_sq (W.origin h) φ hφ.const i' _ hy`. Establish `he : ∀ i', coeff (Finsupp.single i' 1) ((φ.comp W.A.val) y) = coeff (Finsupp.single i' 1) (φ g)`. Introduce `i'`. Use `hd i'` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, sub_eq_zero]`.

Conclude with `this.symm`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `hg1`. Introduce `i' hi'`.

Rewrite using `[he]`. Conclude with `hg2 i' hi'`. Introduce `f hf hco`. Take `⟨c, hc0, hcf⟩` from `hφ.inj f.val hf hco`. Use `⟨c, hc0, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hk, Ideal.mem_comap]`. Conclude with `hcf`.
-/
theorem UpperTheory.V.Alg.chart_gr :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) [Module.Free ℤ X] [Module.Finite ℤ X] (τ : Type) (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ → IsChart W.gr (W.originA h) wt (φ.comp W.A.val) := by
  intro O X R _ _ _ _ _ _ W h _ _ τ wt φ hφ
  obtain ⟨hk, hsurj⟩ := ker_pow O R X W h 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j f hf
    exact hφ.graded j f.val hf
  · intro f
    exact hφ.const f.val
  · intro i
    obtain ⟨g, hg1, hg2⟩ := hφ.onto i
    obtain ⟨y, hy⟩ := hsurj g
    have hd : ∀ i', coeff (Finsupp.single i' 1) (φ (g - y)) = 0 :=
      fun i' => lin_coeff_sq (W.origin h) φ hφ.const i' _ hy
    have he : ∀ i', coeff (Finsupp.single i' 1) ((φ.comp W.A.val) y) =
        coeff (Finsupp.single i' 1) (φ g) := by
      intro i'
      have := hd i'
      rw [map_sub, map_sub, sub_eq_zero] at this
      exact this.symm
    refine ⟨y, ?_, ?_⟩
    · rw [he]
      exact hg1
    · intro i' hi'
      rw [he]
      exact hg2 i' hi'
  · intro f hf hco
    obtain ⟨c, hc0, hcf⟩ := hφ.inj f.val hf hco
    refine ⟨c, hc0, ?_⟩
    rw [← hk, Ideal.mem_comap]
    exact hcf

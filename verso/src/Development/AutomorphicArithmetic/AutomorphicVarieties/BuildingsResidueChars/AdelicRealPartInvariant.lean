import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.Af.BA in
/- English proof (translation)
Introduce `L _ _ N σ hσ`. Use `⟨fun x => ?_, fun h hh => ⟨fun y => ?_, fun g hg => ?_⟩⟩` and prove the remaining obligations. Take `⟨w⟩ : Nonempty (InfinitePlace L)` from `inferInstance`. Establish `e : embO w (σ (σ x)) = embO w x` using `by rw [hσ, hσ]; simp`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Conclude with `w.embedding.injective (by simpa [embO] using e)`. Establish `hz : ∀ w i, toR (sLat σ y) w i = star (toR y w i)` using `fun w i => hσ w (y i)`. Simplify using `only [q, qR]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, hz]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `him : ((mat h w) i j).im = 0` using `hh w i j`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, him]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfix : ∀ i j, σ ((↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) i j) = (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) i j` using `fun i j => by`.

Use `congrArg (fun u : Gm L N => (u : Matrix (Fin N) (Fin N) (𝓞 L)) i j) (mem_Fix.mp (inv_mem hg))` as an intermediate fact. Conclude with `this`. Introduce `w i j`. Establish `hs : g • h = pull (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) h` using `rfl`. Use `show ((mat (g • h) w) i j).im = 0`.

Rewrite using `[hs, mat_pull]`. Use `set B := (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hBdef`. Establish `hB : B.map (starRingEnd ℂ) = B`. Use extensionality with `a b`. Simplify using `only [hBdef, Matrix.map_apply]`.

Rewrite using `[← hσ w, hfix]`. Establish `hM : (mat h w).map (starRingEnd ℂ) = mat h w`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply]`. Conclude with `Complex.conj_eq_iff_im.mpr (hh w a b)`.

Establish `hBt : Bᴴ.map (starRingEnd ℂ) = Bᴴ`. Use extensionality with `a b`. Use `congrFun (congrFun hB b) a` as an intermediate fact. Simplify using `only [Matrix.map_apply, Matrix.conjTranspose_apply] at this ⊢`. Simplify using `only [Complex.star_def, Complex.conj_conj]`.

Conclude with `this.symm`. Establish `hP : (Bᴴ * mat h w * B).map (starRingEnd ℂ) = Bᴴ * mat h w * B`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hBt, hM, hB]`. Use `congrFun (congrFun hP i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`.

Conclude with `Complex.conj_eq_iff_im.mp this`.
-/
theorem UpperTheory.adelic_realPart_invariant :
    UpperTheory.V.Af.BA.ReInv := by
  intro L _ _ N σ hσ
  refine ⟨fun x => ?_, fun h hh => ⟨fun y => ?_, fun g hg => ?_⟩⟩
  · obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
    have e : embO w (σ (σ x)) = embO w x := by rw [hσ, hσ]; simp
    apply RingOfIntegers.coe_injective
    exact w.embedding.injective (by simpa [embO] using e)
  · have hz : ∀ w i, toR (sLat σ y) w i = star (toR y w i) := fun w i => hσ w (y i)
    simp only [q, qR]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, hz]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have him : ((mat h w) i j).im = 0 := hh w i j
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, him]
    ring
  · have hfix : ∀ i j, σ ((↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) i j)
        = (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) i j := fun i j => by
      have := congrArg (fun u : Gm L N => (u : Matrix (Fin N) (Fin N) (𝓞 L)) i j)
        (mem_Fix.mp (inv_mem hg))
      exact this
    intro w i j
    have hs : g • h = pull (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)) h := rfl
    show ((mat (g • h) w) i j).im = 0
    rw [hs, mat_pull]
    set B := (↑g⁻¹ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) with hBdef
    have hB : B.map (starRingEnd ℂ) = B := by
      ext a b
      simp only [hBdef, Matrix.map_apply]
      rw [← hσ w, hfix]
    have hM : (mat h w).map (starRingEnd ℂ) = mat h w := by
      ext a b
      simp only [Matrix.map_apply]
      exact Complex.conj_eq_iff_im.mpr (hh w a b)
    have hBt : Bᴴ.map (starRingEnd ℂ) = Bᴴ := by
      ext a b
      have := congrFun (congrFun hB b) a
      simp only [Matrix.map_apply, Matrix.conjTranspose_apply] at this ⊢
      simp only [Complex.star_def, Complex.conj_conj]
      exact this.symm
    have hP : (Bᴴ * mat h w * B).map (starRingEnd ℂ) = Bᴴ * mat h w * B := by
      rw [Matrix.map_mul, Matrix.map_mul, hBt, hM, hB]
    have := congrFun (congrFun hP i) j
    simp only [Matrix.map_apply] at this
    exact Complex.conj_eq_iff_im.mp this

import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

/- English proof (translation)
Introduce `l _ F R _ _ γ hγ`. Establish `hq : ∀ g, Ideal.Quotient.mk (maximalIdeal R) (γ g : R) = 1` using `fun g => by`. Rewrite using `[← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hγ.red g`. Use `⟨fun m => ⟨hγ.toAnti.mono ?_, ?_, ?_⟩, ⟨hγ.toAnti.mono ?_, ?_, ?_⟩, fun R' _ _ e he => ⟨hγ.toAnti.mono ?_, ?_, ?_⟩⟩` and prove the remaining obligations.

Introduce `g hg`. Rewrite `hg`, the goal using `[MonoidHom.mem_ker]`. Simplify using `[hg]`. Introduce `N`. Establish `hc` using `(hγ.cont N).comp (fun x => x ^ m)`.

Use `hc using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using `[Function.comp]`. Introduce `g`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]`.

Simplify using `[hq g]`. Introduce `g hg`. Rewrite `hg`, the goal using `[MonoidHom.mem_ker]`. Simplify using `[hg]`. Introduce `N`.

Establish `hc` using `(hγ.cont N).comp Ring.inverse`. Use `hc using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using `only [Function.comp, MonoidHom.inv_apply]`. Establish `hu : Ideal.Quotient.mk (maximalIdeal R ^ N) (γ g : R) = ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N) : R →* R ⧸ maximalIdeal R ^ N) (γ g) : _))` using `rfl`.

Rewrite using `[hu, Ring.inverse_unit, Units.coe_map_inv]`. Both sides reduce to the same expression. Introduce `g`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]`. Establish `h2` using `congrArg (Ideal.Quotient.mk (maximalIdeal R)) (γ g).inv_mul`.

Rewrite `h2` using `[map_mul, hq g, mul_one, map_one]`. Simplify using `using h2`. Introduce `g hg`. Rewrite `hg`, the goal using `[MonoidHom.mem_ker]`. Simplify using `[pushCh, hg]`.

Introduce `N`. Establish `hle : maximalIdeal R ^ N ≤ Ideal.comap e (maximalIdeal R' ^ N)`. Rewrite using `[← Ideal.map_le_iff_le_comap, Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr (fun x hx => Ideal.mem_comap.mpr (map_nonunit e x hx))) N`. Establish `hc` using `(hγ.cont N).comp (Ideal.quotientMap _ e hle)`.

Use `hc using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using `[pushCh, Ideal.quotientMap_mk]`. Introduce `g`. Establish `h3` using `map_nonunit e _ (hγ.red g)`.

Simplify `h3` using `[pushCh]`.
-/
theorem UpperTheory.V.Ws.H5.twChOps :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {R : Type} [CommRing R] [IsLocalRing R] (γ : F.G₀ →* Rˣ), TwCh F γ → (∀ m : ℕ, TwCh F (γ ^ m)) ∧ TwCh F γ⁻¹ ∧ ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (e : R →+* R'), IsLocalHom e → TwCh F (pushCh e γ) := by
  intro l _ F R _ _ γ hγ
  have hq : ∀ g, Ideal.Quotient.mk (maximalIdeal R) (γ g : R) = 1 := fun g => by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hγ.red g
  refine ⟨fun m => ⟨hγ.toAnti.mono ?_, ?_, ?_⟩, ⟨hγ.toAnti.mono ?_, ?_, ?_⟩,
    fun R' _ _ e he => ⟨hγ.toAnti.mono ?_, ?_, ?_⟩⟩
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  · intro N
    have hc := (hγ.cont N).comp (fun x => x ^ m)
    convert hc using 1
    funext g
    simp [Function.comp]
  · intro g
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
    simp [hq g]
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  · intro N
    have hc := (hγ.cont N).comp Ring.inverse
    convert hc using 1
    funext g
    simp only [Function.comp, MonoidHom.inv_apply]
    have hu : Ideal.Quotient.mk (maximalIdeal R ^ N) (γ g : R) =
        ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N) : R →* R ⧸ maximalIdeal R ^ N) (γ g) : _)) := rfl
    rw [hu, Ring.inverse_unit, Units.coe_map_inv]
    rfl
  · intro g
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
    have h2 := congrArg (Ideal.Quotient.mk (maximalIdeal R)) (γ g).inv_mul
    rw [map_mul, hq g, mul_one, map_one] at h2
    simpa using h2
  · intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [pushCh, hg]
  · intro N
    have hle : maximalIdeal R ^ N ≤ Ideal.comap e (maximalIdeal R' ^ N) := by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr (fun x hx => Ideal.mem_comap.mpr (map_nonunit e x hx))) N
    have hc := (hγ.cont N).comp (Ideal.quotientMap _ e hle)
    convert hc using 1
    funext g
    simp [pushCh, Ideal.quotientMap_mk]
  · intro g
    have h3 := map_nonunit e _ (hγ.red g)
    simpa [pushCh] using h3

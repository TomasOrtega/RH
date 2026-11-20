import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

/- English proof (translation)
Introduce `G₁ R G _ _ _ _ _ _ _ i d c hi hd hc hs hcomm hk`. Establish `hd1 : ∀ x, d (i x) = 1` using `fun x => (hk _).2 ⟨x, rfl⟩`. Establish `h : ∀ g, ∃ x, i x = g * (c (d g))⁻¹` using `fun g => by`. Establish `h1 : d (g * (c (d g))⁻¹) = 1`. Rewrite using `[map_mul, map_inv, hs, mul_inv_cancel]`.

Conclude with `(hk _).1 h1`. Use `choose f hf using h`. Establish `hfc : Continuous f`. Use `hi.continuous_iff.2 ?_` and prove the remaining obligations. Establish `h2 : (i ∘ f) = fun g => g * (c (d g))⁻¹` using `funext hf`.

Rewrite using `[h2]`. Conclude with `continuous_id.mul (hc.comp hd).inv`. Set `E : G₁ × R ≃* G` to `{ toFun := fun x => i x.1 * c x.2 invFun := fun g => (f g, d g) left_inv := by`. Introduce and unpack `⟨x, r⟩`. Establish `hdr : d (i x * c r) = r` using `by rw [map_mul, hd1, hs, one_mul]`.

Use `Prod.ext (hi.injective ?_) hdr` and prove the remaining obligations. Use `show i (f (i x * c r)) = i x`. Rewrite using `[hf, hdr, mul_inv_cancel_right]`. Use `right_inv := by`. Introduce `g`.

Use `show i (f g) * c (d g) = g`. Rewrite using `[hf, inv_mul_cancel_right]`. Use the proof step `map_mul' := by`. Introduce and unpack `⟨x, r⟩ ⟨y, s⟩`. Use `show i (x * y) * c (r * s) = i x * c r * (i y * c s)`.

Rewrite using `[map_mul, map_mul, mul_assoc (i x) (c r), ← mul_assoc (c r), hcomm r (i y)]`. Simplify using `only [mul_assoc] }`. Conclude with `⟨{ E with continuous_toFun := (hi.continuous.comp continuous_fst).mul (hc.comp continuous_snd) continuous_invFun := hfc.prodMk hd }, fun x => rfl⟩`.
-/
theorem UpperTheory.adelicGL_split_equiv :
    SplitEquiv := by
  intro G₁ R G _ _ _ _ _ _ _ i d c hi hd hc hs hcomm hk
  have hd1 : ∀ x, d (i x) = 1 := fun x => (hk _).2 ⟨x, rfl⟩
  have h : ∀ g, ∃ x, i x = g * (c (d g))⁻¹ := fun g => by
    have h1 : d (g * (c (d g))⁻¹) = 1 := by
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    exact (hk _).1 h1
  choose f hf using h
  have hfc : Continuous f := by
    refine hi.continuous_iff.2 ?_
    have h2 : (i ∘ f) = fun g => g * (c (d g))⁻¹ := funext hf
    rw [h2]
    exact continuous_id.mul (hc.comp hd).inv
  let E : G₁ × R ≃* G :=
    { toFun := fun x => i x.1 * c x.2
      invFun := fun g => (f g, d g)
      left_inv := by
        rintro ⟨x, r⟩
        have hdr : d (i x * c r) = r := by rw [map_mul, hd1, hs, one_mul]
        refine Prod.ext (hi.injective ?_) hdr
        show i (f (i x * c r)) = i x
        rw [hf, hdr, mul_inv_cancel_right]
      right_inv := by
        intro g
        show i (f g) * c (d g) = g
        rw [hf, inv_mul_cancel_right]
      map_mul' := by
        rintro ⟨x, r⟩ ⟨y, s⟩
        show i (x * y) * c (r * s) = i x * c r * (i y * c s)
        rw [map_mul, map_mul, mul_assoc (i x) (c r), ← mul_assoc (c r), hcomm r (i y)]
        simp only [mul_assoc] }
  exact ⟨{ E with
    continuous_toFun := (hi.continuous.comp continuous_fst).mul (hc.comp continuous_snd)
    continuous_invFun := hfc.prodMk hd }, fun x => rfl⟩

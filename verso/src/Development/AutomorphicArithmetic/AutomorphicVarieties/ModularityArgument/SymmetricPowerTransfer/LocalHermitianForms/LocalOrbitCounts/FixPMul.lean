import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Take `⟨hfg, hdual, hstab⟩` from `h`. Establish `hmem : ∀ z, z ∈ ((y : Etau K τ) * ·) '' S ↔ (↑y⁻¹ : Etau K τ) * z ∈ S`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`.

Simplify using `using ha`. Introduce `hz`. Conclude with `⟨_, hz, by simp⟩`. Establish `hy : (y : Etau K τ) = algebraMap K _ (QuadraticAlgebra.norm (y : Etau K τ)) * star (↑y⁻¹ : Etau K τ)`. Rewrite using `[algebraMap_norm_eq_mul_star, mul_assoc, ← star_mul, Units.inv_mul, star_one, mul_one]`.

Establish `key : ∀ a z : Etau K τ, x * ((y : Etau K τ) * a * star z).im = QuadraticAlgebra.norm (y : Etau K τ) * x * (a * star ((↑y⁻¹ : Etau K τ) * z)).im`. Introduce `a z`. Establish `e : (y : Etau K τ) * a * star z = algebraMap K _ (QuadraticAlgebra.norm (y : Etau K τ)) * (a * star ((↑y⁻¹ : Etau K τ) * z))` using `by conv_lhs => rw [hy]`. Rewrite using `[star_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `hfg classical`.

Use `⟨s.image ((y : Etau K τ) * ·), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image]`. Express the relevant statement in the definitionally equal form `⇑(LinearMap.mulLeft O (y : Etau K τ)) '' _ = ↑(Submodule.span O (⇑(LinearMap.mulLeft O (y : Etau K τ)) '' _))`. Rewrite using `[← Submodule.map_coe, Submodule.map_span]`. Introduce `z`.

Rewrite using `[hmem, hdual]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `H _ ⟨a, ha, rfl⟩`. Use `H a ha` as an intermediate fact. Rewrite using `[key]`.

Conclude with `this`. Introduce `H a ha`. Use `H (↑y * a) ⟨a, ha, rfl⟩` as an intermediate fact. Rewrite `this` using `[key]`. Conclude with `this`.

Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `⟨ω * a, hstab a ha, mul_left_comm _ _ _⟩`.
-/
private theorem fixP_mul {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (y : (Etau K τ)ˣ) (x : K) (S : Set (Etau K τ))
    (h : IsFixP O τ (QuadraticAlgebra.norm (y : Etau K τ) * x) S) : IsFixP O τ x (((y : Etau K τ) * ·) '' S) := by
  obtain ⟨hfg, hdual, hstab⟩ := h
  have hmem : ∀ z, z ∈ ((y : Etau K τ) * ·) '' S ↔ (↑y⁻¹ : Etau K τ) * z ∈ S := by
    intro z
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hz
      exact ⟨_, hz, by simp⟩
  have hy : (y : Etau K τ)
      = algebraMap K _ (QuadraticAlgebra.norm (y : Etau K τ)) * star (↑y⁻¹ : Etau K τ) := by
    rw [algebraMap_norm_eq_mul_star, mul_assoc, ← star_mul, Units.inv_mul, star_one, mul_one]
  have key : ∀ a z : Etau K τ, x * ((y : Etau K τ) * a * star z).im
      = QuadraticAlgebra.norm (y : Etau K τ) * x * (a * star ((↑y⁻¹ : Etau K τ) * z)).im := by
    intro a z
    have e : (y : Etau K τ) * a * star z
        = algebraMap K _ (QuadraticAlgebra.norm (y : Etau K τ)) * (a * star ((↑y⁻¹ : Etau K τ) * z)) := by
      conv_lhs => rw [hy]
      rw [star_mul]
      ring
    rw [e]
    simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s, rfl⟩ := hfg
    classical
    refine ⟨s.image ((y : Etau K τ) * ·), ?_⟩
    rw [Finset.coe_image]
    change ⇑(LinearMap.mulLeft O (y : Etau K τ)) '' _
      = ↑(Submodule.span O (⇑(LinearMap.mulLeft O (y : Etau K τ)) '' _))
    rw [← Submodule.map_coe, Submodule.map_span]
  · intro z
    rw [hmem, hdual]
    constructor
    · rintro H _ ⟨a, ha, rfl⟩
      have := H a ha
      rw [key]
      exact this
    · intro H a ha
      have := H (↑y * a) ⟨a, ha, rfl⟩
      rw [key] at this
      exact this
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨ω * a, hstab a ha, mul_left_comm _ _ _⟩

/- English proof (translation)
Use `⟨fun h => ?_, fixP_mul y x S⟩` and prove the remaining obligations. Use `fixP_mul y⁻¹ (QuadraticAlgebra.norm (y : Etau K τ) * x) (((y : Etau K τ) * ·) '' S) (by rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul])` as an intermediate fact. Simplify `this` using `[← Set.image_comp, Function.comp_def]`.
-/
private theorem fixP_iff {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (y : (Etau K τ)ˣ) (x : K) (S : Set (Etau K τ)) :
    IsFixP O τ x (((y : Etau K τ) * ·) '' S) ↔ IsFixP O τ (QuadraticAlgebra.norm (y : Etau K τ) * x) S := by
  refine ⟨fun h => ?_, fixP_mul y x S⟩
  have := fixP_mul y⁻¹ (QuadraticAlgebra.norm (y : Etau K τ) * x) (((y : Etau K τ) * ·) '' S) (by rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul])
  simpa [← Set.image_comp, Function.comp_def] using this

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ hL t ht x`. Take `⟨y, rfl⟩` from `ht`. Use `show pcount O τ (QuadraticAlgebra.norm (y : Etau K τ) * x) = pcount O τ x`. Unfold `pcount`. Use `letI := quoAct (K := K) τ`.

Establish `inv : ∀ (z : (Etau K τ)ˣ) (r : K) (S : Set (Etau K τ)), IsFixP O τ r ((quo z * ·) '' S) ↔ IsFixP O τ r S`. Introduce `z r S`. Establish `hq : QuadraticAlgebra.norm (quo z) = 1`. Rewrite using `[quo, map_mul, QuadraticAlgebra.norm_star, ← map_mul, Units.mul_inv, map_one]`. Set `u : (Etau K τ)ˣ` to `⟨quo z, star (quo z), quo_mul_star z, by rw [mul_comm]; exact quo_mul_star z⟩`.

Use `fixP_iff (O := O) u r S` as an intermediate fact. Rewrite `this` using `[show QuadraticAlgebra.norm (u : Etau K τ) = 1 from hq, one_mul]`. Then use the resulting hypothesis. Use `wTrans _ _ _ (Cint O τ) _ _ (fun S S' => S' = ((y : Etau K τ) * ·) '' S) ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `z S split_ifs with h1 h2 h3`. Both sides reduce to the same expression.

Conclude with `absurd ((inv z _ S).mp h1) h2`. Conclude with `absurd ((inv z _ S).mpr h3) h1`. Both sides reduce to the same expression. Introduce `z S split_ifs with h1 h2 h3`. Both sides reduce to the same expression.

Conclude with `absurd ((inv z _ S).mp h1) h2`. Conclude with `absurd ((inv z _ S).mpr h3) h1`. Both sides reduce to the same expression. Introduce `z S S' h`. Substitute `h` using the available equality.

Use `show (quo z * ·) '' (((y : Etau K τ) * ·) '' S) = ((y : Etau K τ) * ·) '' ((quo z * ·) '' S)`. Rewrite using `[Set.image_image, Set.image_image]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Expand and normalize the polynomial expressions, which then agree.

Introduce `S S' h`. Substitute `h` using the available equality. Establish `e` using `fixP_iff (O := O) y x S`. Use `split_ifs with h1 h2 h3`. Both sides reduce to the same expression.

Conclude with `absurd (e.mpr h1) h2`. Conclude with `absurd (e.mp h3) h1`. Both sides reduce to the same expression. Introduce `S _`. Conclude with `⟨_, rfl, fun _ h => h⟩`.

Introduce `S' _`. Use `⟨((↑y⁻¹ : Etau K τ) * ·) '' S', ?_, fun S h => ?_⟩` and prove the remaining obligations. Use `show S' = ((y : Etau K τ) * ·) '' (((↑y⁻¹ : Etau K τ) * ·) '' S')`. Rewrite using `[Set.image_image]`. Simplify using the standard rewrite rules.

Substitute `h` using the available equality. Rewrite using `[Set.image_image]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Z.Sym.Loc.pNorm : UpperTheory.V.Z.Sym.Loc.PNorm := by
  intro O K _ _ _ _ _ Δ τ hL t ht x
  obtain ⟨y, rfl⟩ := ht
  show pcount O τ (QuadraticAlgebra.norm (y : Etau K τ) * x) = pcount O τ x
  unfold pcount
  letI := quoAct (K := K) τ
  have inv : ∀ (z : (Etau K τ)ˣ) (r : K) (S : Set (Etau K τ)),
      IsFixP O τ r ((quo z * ·) '' S) ↔ IsFixP O τ r S := by
    intro z r S
    have hq : QuadraticAlgebra.norm (quo z) = 1 := by
      rw [quo, map_mul, QuadraticAlgebra.norm_star, ← map_mul, Units.mul_inv, map_one]
    let u : (Etau K τ)ˣ := ⟨quo z, star (quo z), quo_mul_star z, by rw [mul_comm]; exact quo_mul_star z⟩
    have := fixP_iff (O := O) u r S
    rwa [show QuadraticAlgebra.norm (u : Etau K τ) = 1 from hq, one_mul] at this
  refine wTrans _ _ _ (Cint O τ) _ _ (fun S S' => S' = ((y : Etau K τ) * ·) '' S) ?_ ?_ ?_ ?_ ?_ ?_
  · intro z S
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd ((inv z _ S).mp h1) h2
    · exact absurd ((inv z _ S).mpr h3) h1
    · rfl
  · intro z S
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd ((inv z _ S).mp h1) h2
    · exact absurd ((inv z _ S).mpr h3) h1
    · rfl
  · intro z S S' h
    subst h
    show (quo z * ·) '' (((y : Etau K τ) * ·) '' S) = ((y : Etau K τ) * ·) '' ((quo z * ·) '' S)
    rw [Set.image_image, Set.image_image]
    congr 1
    funext a
    ring
  · intro S S' h
    subst h
    have e := fixP_iff (O := O) y x S
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd (e.mpr h1) h2
    · exact absurd (e.mp h3) h1
    · rfl
  · intro S _
    exact ⟨_, rfl, fun _ h => h⟩
  · intro S' _
    refine ⟨((↑y⁻¹ : Etau K τ) * ·) '' S', ?_, fun S h => ?_⟩
    · show S' = ((y : Etau K τ) * ·) '' (((↑y⁻¹ : Etau K τ) * ·) '' S')
      rw [Set.image_image]
      simp
    · subst h
      rw [Set.image_image]
      simp

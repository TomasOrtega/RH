import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem fixP_iff {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (y : (Etau K τ)ˣ) (x : K) (S : Set (Etau K τ)) :
    IsFixP O τ x (((y : Etau K τ) * ·) '' S) ↔ IsFixP O τ (QuadraticAlgebra.norm (y : Etau K τ) * x) S := by
  refine ⟨fun h => ?_, fixP_mul y x S⟩
  have := fixP_mul y⁻¹ (QuadraticAlgebra.norm (y : Etau K τ) * x) (((y : Etau K τ) * ·) '' S) (by rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul])
  simpa [← Set.image_comp, Function.comp_def] using this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Equip the data with the indicated structure. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. Both sides reduce to the same expression.

Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses.

Substitute using the available equality. Establish an intermediate fact. Both sides reduce to the same expression. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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

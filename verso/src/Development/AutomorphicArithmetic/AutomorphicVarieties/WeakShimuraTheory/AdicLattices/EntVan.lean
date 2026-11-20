import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
private theorem adic_bot {X R : Type} [CommRing R] [TopologicalSpace X] (f : X → R) (h : AdicCont ⊥ f) : IsLocallyConstant f := by
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (h 1) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact.

Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
private theorem rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (h : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g)
    (i j : Fin 4) (g : Γ) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have h3 : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    have a0 : Φ.χ 0 g * Φ.χ 3 g = Φ.ν g := h 0 g
    have a1 : Φ.χ 1 g * Φ.χ 2 g = Φ.ν g := h 1 g
    rw [a1, ← a0, mul_comm, inv_mul_cancel_left]
  have key : ∀ i : Fin 4, Φ.χ i g = (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (lamW i) * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (muW i) *
      (Φ.χ 0 g * ((Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (lamW 0) * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (muW 0))⁻¹) := by
    intro i
    apply Additive.ofMul.injective
    fin_cases i <;> simp [lamW, muW, h3] <;> abel
  show (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (lamW i - lamW j) * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (muW i - muW j) * Φ.χ j g = _
  have ki := key i
  have kj := key j
  generalize Φ.χ 0 g * ((Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (lamW 0) * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (muW 0))⁻¹ = c at ki kj
  generalize Φ.χ 0 g * (Φ.χ 1 g)⁻¹ = A at *
  generalize Φ.χ 0 g * (Φ.χ 2 g)⁻¹ = B at *
  rw [ki, kj, zpow_sub, zpow_sub]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Evaluate the decidable proposition.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Ws.Lat.entVan :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k) (P : PD Φ.ι Γ k), PreRes Φ a P →
      (∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) → OddVan Φ a → EntVan Φ a P := by
  intro O Γ _ _ _ Φ k _ a P hP hm hO i j hw hx m hl
  have hij : i ≠ j := by
    rintro rfl
    revert hw
    simp only [wt, sub_self]
    decide
  have hne : ∀ g, a (Φ.χ j g) ≠ 0 := fun g => ((Φ.χ j g).isUnit.map a).ne_zero
  have hrt : ∀ g, a (Φ.rt (wt i j) g) = a (Φ.χ i g) * (a (Φ.χ j g))⁻¹ := fun g => by
    rw [← rt_wt Φ hm i j g, Units.val_mul, map_mul, mul_assoc, mul_inv_cancel₀ (hne g), mul_one]
  have hmul : ∀ g h, P.r (g * h) i j = a (Φ.χ i g) * P.r h i j + P.r g i j * a (Φ.χ j h) := fun g h => by
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_add i j hij, hP.diag, hP.diag]
    · exact fun x _ hx' => hx g h x hx'.1 hx'.2
    · simp
    · simp
  have hz : (fun g => P.r g i j * (P.r g j j)⁻¹) ∈ Φ.Zgl a (wt i j) := by
    refine ⟨(adic_bot _ (hP.cont i j)).mul ((adic_bot _ (hP.cont j j)).comp (·⁻¹)), fun g h => ?_, fun g hg => ?_, fun _ => ?_⟩
    · have := hne g
      have := hne h
      simp only [hP.diag, hmul, hrt, map_mul, Units.val_mul]
      field_simp
      ring
    · simp only [hP.pair.kill g hg, Matrix.one_apply_ne hij, zero_mul]
    · simp only [hP.pair.nrm hij, zero_mul]
  obtain ⟨h1, h2⟩ := hO _ hw _ hz m fun v s hs => by
    have := hne s
    simp only [hP.diag, hl v s hs, hrt]
    field_simp
  refine ⟨fun g => ?_, h2⟩
  have := congrFun h1 g
  simp only [hP.diag, Pi.zero_apply, mul_eq_zero, inv_eq_zero, hne g, or_false] at this
  exact this

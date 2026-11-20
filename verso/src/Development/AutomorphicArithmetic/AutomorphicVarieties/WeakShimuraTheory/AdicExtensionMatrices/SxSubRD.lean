import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `O Γ _ _ Φ Λ R _ _ _ a A D hr hψ h`. Establish `h1 : ∀ i j : Fin 4, (((1 : M4 A) i j : A) : R) = (1 : M4 R) i j` using `fun i j => by`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Set `r' : Γ →* M4 A` to `{ toFun := fun g => Matrix.of fun i j => ⟨D.r g i j, hr g i j⟩ map_one' := by`. Use extensionality with `i j`.

Rewrite using `[h1]`. Simplify using the standard rewrite rules. Use the proof step `map_mul' := fun g g' => by`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply] }`.

Establish `hr' : ∀ g i j, ((r' g i j : A) : R) = D.r g i j` using `fun _ _ _ => rfl`. Use `⟨⟨r', fun v i => (D.ψ v i).codRestrict A (hψ v i)⟩, ?_, fun g => ?_, fun g hg => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Use `RD.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `g i j`. Both sides reduce to the same expression.

Use function extensionality and compare the values at `v i`. Use extensionality with `s`. Both sides reduce to the same expression. Use `h.mult g` as an intermediate fact. Unfold `IsGSp at this ⊢`.

Use extensionality with `i j`. Establish `e` using `congrFun (congrFun this i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, MulMemClass.coe_mul, h1]`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at e`. Use `Eq.trans ?_ e` and prove the remaining obligations.

Simplify using `[Matrix.mul_apply, adj, hr']`. Use extensionality with `i j`. Rewrite using `[h1]`. Use `show D.r g i j = _`. Rewrite using `[h.kill g hg]`.

Conclude with `Subtype.ext (h.nrm hij)`.
-/
theorem UpperTheory.V.Ws.sxSubRD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {Λ R : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] (a : O →+* Λ) (A : Subalgebra Λ R) (D : RD Φ R), (∀ g i j, D.r g i j ∈ A) → (∀ v i s, D.ψ v i s ∈ A) → Φ.IsRep ((algebraMap Λ R).comp a) D.r → ∃ D' : RD Φ A, D'.map (A.val : A →+* R) = D ∧ Φ.IsRep ((algebraMap Λ A).comp a) D'.r := by
  intro O Γ _ _ Φ Λ R _ _ _ a A D hr hψ h
  have h1 : ∀ i j : Fin 4, (((1 : M4 A) i j : A) : R) = (1 : M4 R) i j := fun i j => by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  let r' : Γ →* M4 A :=
    { toFun := fun g => Matrix.of fun i j => ⟨D.r g i j, hr g i j⟩
      map_one' := by
        ext i j
        rw [h1]; simp
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  have hr' : ∀ g i j, ((r' g i j : A) : R) = D.r g i j := fun _ _ _ => rfl
  refine ⟨⟨r', fun v i => (D.ψ v i).codRestrict A (hψ v i)⟩, ?_, fun g => ?_, fun g hg => ?_, fun i j hij => ?_⟩
  · refine RD.ext ?_ ?_
    · ext g i j; rfl
    · funext v i; ext s; rfl
  · have := h.mult g
    unfold IsGSp at this ⊢
    ext i j
    have e := congrFun (congrFun this i) j
    simp only [Matrix.smul_apply, smul_eq_mul, MulMemClass.coe_mul, h1]
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    refine Eq.trans ?_ e
    simp [Matrix.mul_apply, adj, hr']
  · ext i j
    rw [h1]
    show D.r g i j = _
    rw [h.kill g hg]
  · exact Subtype.ext (h.nrm hij)

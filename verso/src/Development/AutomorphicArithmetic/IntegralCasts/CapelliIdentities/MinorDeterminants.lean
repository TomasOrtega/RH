import Mathlib

/- English proof (translation)
Introduce `N J`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Reformulated.B.MinorDeterminants.aux1 :
    ∀ {N : ℕ} (J : Finset (Fin N)), J.card = J.card := by
  intro N J
  rfl

noncomputable def UpperTheory.Reformulated.B.MinorDeterminants.minorIJ :
    {R : Type} → [CommRing R] → {N : ℕ} → Matrix (Fin N) (Fin N) R → Finset (Fin N) → Finset (Fin N) → R :=
    fun {R : Type} [CommRing R] {N : ℕ} (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) ↦
      if e : I.card = J.card then
        (h.submatrix (⇑(I.orderEmbOfFin e) : Fin J.card → Fin N)
            (⇑(J.orderEmbOfFin (UpperTheory.Reformulated.B.MinorDeterminants.aux1 J)) : Fin J.card → Fin N)).det
      else (0 : R)

/- English proof (translation)
Introduce `N C S f hf h0`. Establish `e : (Finset.image f Finset.univ).card = S.card`. Rewrite using `[Finset.card_image_of_injective _ hf]`. Simplify using the standard rewrite rules. Unfold `UpperTheory.Reformulated.B.MinorDeterminants.minorIJ at h0`.

Rewrite `h0` using `[dif_pos e]`. Use `set I := Finset.image f Finset.univ with hI`. Establish `mem : ∀ i, f i ∈ I` using `fun i => by simp [hI]`. Set `σf : Fin S.card → Fin S.card` to `fun i => (I.orderIsoOfFin e).symm ⟨f i, mem i⟩`. Establish `hσ : Function.Injective σf`.

Introduce `a b hab`. Apply `hf` to reduce the goal to its premises. Use `congrArg (fun x => ((I.orderIsoOfFin e x : I) : Fin N)) hab` as an intermediate fact. Simplify `this` using `[σf]`. Set `σ : Equiv.Perm (Fin S.card)` to `Equiv.ofBijective σf hσ.bijective_of_finite`.

Establish `hfg : f = (⇑(I.orderEmbOfFin e)) ∘ σ`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp, σ, Equiv.ofBijective_apply, σf]`. Rewrite using `[← Finset.coe_orderIsoOfFin_apply]`. Simplify using the standard rewrite rules.

Establish `key : C.submatrix f (⇑(S.orderEmbOfFin rfl)) = (C.submatrix (⇑(I.orderEmbOfFin e)) (⇑(S.orderEmbOfFin (UpperTheory.Reformulated.B.MinorDeterminants.aux1 S)))).submatrix σ id`. Rewrite using `[hfg, Matrix.submatrix_submatrix]`. Both sides reduce to the same expression. Rewrite using `[key, Matrix.det_permute, h0, mul_zero]`.
-/
theorem UpperTheory.Reformulated.B.MinorDeterminants.main :
    ∀ {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (f : Fin S.card → Fin N),
      Function.Injective f →
        UpperTheory.Reformulated.B.MinorDeterminants.minorIJ C (Finset.image f Finset.univ) S = (0 : ℂ) →
          (C.submatrix f (⇑(S.orderEmbOfFin rfl) : Fin S.card → Fin N)).det = (0 : ℂ) := by
  intro N C S f hf h0
  have e : (Finset.image f Finset.univ).card = S.card := by
    rw [Finset.card_image_of_injective _ hf]; simp
  unfold UpperTheory.Reformulated.B.MinorDeterminants.minorIJ at h0
  rw [dif_pos e] at h0
  set I := Finset.image f Finset.univ with hI
  have mem : ∀ i, f i ∈ I := fun i => by simp [hI]
  let σf : Fin S.card → Fin S.card := fun i => (I.orderIsoOfFin e).symm ⟨f i, mem i⟩
  have hσ : Function.Injective σf := by
    intro a b hab
    apply hf
    have := congrArg (fun x => ((I.orderIsoOfFin e x : I) : Fin N)) hab
    simpa [σf] using this
  let σ : Equiv.Perm (Fin S.card) := Equiv.ofBijective σf hσ.bijective_of_finite
  have hfg : f = (⇑(I.orderEmbOfFin e)) ∘ σ := by
    funext i
    simp only [Function.comp, σ, Equiv.ofBijective_apply, σf]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp
  have key : C.submatrix f (⇑(S.orderEmbOfFin rfl)) =
      (C.submatrix (⇑(I.orderEmbOfFin e)) (⇑(S.orderEmbOfFin (UpperTheory.Reformulated.B.MinorDeterminants.aux1 S)))).submatrix σ id := by
    rw [hfg, Matrix.submatrix_submatrix]
    rfl
  rw [key, Matrix.det_permute, h0, mul_zero]

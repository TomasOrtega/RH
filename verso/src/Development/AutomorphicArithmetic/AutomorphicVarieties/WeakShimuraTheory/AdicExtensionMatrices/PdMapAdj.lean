import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[adj, Matrix.map_apply]`.
-/
private theorem adj_map_ringHom {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (M : M4 R) :
    adj (M.map f) = (adj M).map f := by
  ext i j
  simp [adj, Matrix.map_apply]

/- English proof (translation)
Simplify using `only [IsGSp] at h ⊢`. Rewrite using `[adj_map_ringHom, ← Matrix.map_mul, h]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.
-/
private theorem sxPdMap_lemma_2 {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (c : R) (M : M4 R)
    (h : IsGSp c M) : IsGSp (f c) (M.map f) := by
  simp only [IsGSp] at h ⊢
  rw [adj_map_ringHom, ← Matrix.map_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/- English proof (translation)
Introduce `O Γ _ _ Φ R R' _ _ a f P`. Establish `hr : ∀ s, mapRep f P.r s = (P.r s).map f` using `fun s => by`. Use extensionality with `i j`. Rewrite using `[mapRep_apply, Matrix.map_apply]`. Establish `hψ : ∀ v i s, (P.map f).ψ v i s = f (P.ψ v i s)` using `fun v i s => by`.

Simplify using `only [PD.map, PD.ψ]`. Rewrite using `[hr, adj_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]`. Use `⟨hψ, fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3, h4, h5, h6⟩` from `h`. Use `⟨fun g => ?_, fun g hg => ?_, ?_, fun v => ?_, fun v s hs => ?_, fun v s hs i => ?_⟩` and prove the remaining obligations.

Simplify using `only [PD.map, hr]`. Conclude with `sxPdMap_lemma_2 f _ _ (h1 g)`. Simplify using `only [PD.map, hr, h2 g hg, Matrix.map_one, map_zero, map_one]`. Simplify using `only [PD.map, hr]`. Conclude with `h3.map (map_zero f)`.

Use `h4 v` as an intermediate fact. Simplify using `only [IsLow] at this ⊢`. Simplify using `only [PD.map]`. Establish `hg` using `sxPdMap_lemma_2 f _ _ this.1`. Rewrite `hg` using `[map_one]`.

Use `⟨hg, fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, this.2.1 i, map_one]`. Rewrite using `[Matrix.map_apply, this.2.2 i j hij, map_zero]`. Use `h5 v s hs` as an intermediate fact. Simplify using `only [IsUp] at this ⊢`.

Simplify using `only [PD.map, hr]`. Introduce `i j hij`. Rewrite using `[adj_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, this i j hij, map_zero]`. Rewrite using `[hψ, h6 v s hs i, map_one]`. Take `⟨h1, h2, h3⟩` from `h`.

Use `⟨fun g i => ?_, fun v s hs i => ?_, ?_⟩` and prove the remaining obligations. Use `show mapRep f P.r g i i = _`. Rewrite using `[mapRep_apply, h1 g i]`. Both sides reduce to the same expression. Rewrite using `[hψ, h2 v s hs i]`.

Both sides reduce to the same expression. Simplify using `only [Supp, SuppM, PD.map] at h3 ⊢`. Break down `h3 with ⟨hA, hB⟩ | hC` into its components or cases. Conclude with `Or.inl ⟨fun g i j h h' => by rw [mapRep_apply, hA g i j h h', map_zero], fun v i j h h' => by rw [Matrix.map_apply, hB v i j h h', map_zero]⟩`. Conclude with `Or.inr fun g i j h h' => by rw [mapRep_apply, hC g i j h h', map_zero]`.
-/
theorem UpperTheory.V.Ws.sxPdMap :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R R' : Type} [CommRing R] [CommRing R'] (a : O →+* R) (f : R →+* R') (P : PD Φ.ι Γ R), (∀ v i s, (P.map f).ψ v i s = f (P.ψ v i s)) ∧ (Φ.IsPair a P → Φ.IsPair (f.comp a) (P.map f)) ∧ (Φ.Res a P → Φ.Res (f.comp a) (P.map f)) := by
  intro O Γ _ _ Φ R R' _ _ a f P
  have hr : ∀ s, mapRep f P.r s = (P.r s).map f := fun s => by
    ext i j
    rw [mapRep_apply, Matrix.map_apply]
  have hψ : ∀ v i s, (P.map f).ψ v i s = f (P.ψ v i s) := fun v i s => by
    simp only [PD.map, PD.ψ]
    rw [hr, adj_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
  refine ⟨hψ, fun h => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨fun g => ?_, fun g hg => ?_, ?_, fun v => ?_, fun v s hs => ?_, fun v s hs i => ?_⟩
    · simp only [PD.map, hr]
      exact sxPdMap_lemma_2 f _ _ (h1 g)
    · simp only [PD.map, hr, h2 g hg, Matrix.map_one, map_zero, map_one]
    · simp only [PD.map, hr]
      exact h3.map (map_zero f)
    · have := h4 v
      simp only [IsLow] at this ⊢
      simp only [PD.map]
      have hg := sxPdMap_lemma_2 f _ _ this.1
      rw [map_one] at hg
      refine ⟨hg, fun i => ?_, fun i j hij => ?_⟩
      · rw [Matrix.map_apply, this.2.1 i, map_one]
      · rw [Matrix.map_apply, this.2.2 i j hij, map_zero]
    · have := h5 v s hs
      simp only [IsUp] at this ⊢
      simp only [PD.map, hr]
      intro i j hij
      rw [adj_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, this i j hij, map_zero]
    · rw [hψ, h6 v s hs i, map_one]
  · obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun g i => ?_, fun v s hs i => ?_, ?_⟩
    · show mapRep f P.r g i i = _
      rw [mapRep_apply, h1 g i]
      rfl
    · rw [hψ, h2 v s hs i]
      rfl
    · simp only [Supp, SuppM, PD.map] at h3 ⊢
      rcases h3 with ⟨hA, hB⟩ | hC
      · exact Or.inl ⟨fun g i j h h' => by rw [mapRep_apply, hA g i j h h', map_zero],
          fun v i j h h' => by rw [Matrix.map_apply, hB v i j h h', map_zero]⟩
      · exact Or.inr fun g i j h h' => by rw [mapRep_apply, hC g i j h h', map_zero]

import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
private theorem mapGL_id' {R : Type} [CommRing R] (n : ℕ) (x : Matrix.GeneralLinearGroup (Fin n) R) :
    PositivityTheory.Rg.Tf.Geo.mapGL n (RingHom.id R) x = x := by
  ext i j
  simp

/- English proof (translation)
Introduce `hP hT hB F _ _ n hn γ`. Establish `hz : ∀ τ : F ≃ₐ[F] F, τ ∈ Subgroup.zpowers (1 : F ≃ₐ[F] F)` using `fun τ => by`. Establish `h1 : τ = 1`. Use extensionality with `x`. Conclude with `τ.commutes x`.

Rewrite using `[h1]`. Conclude with `one_mem _`. Take `⟨hg, hi, -⟩` from `hT F`. Establish `hi' : GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K` using `F) (L := F) = RingHom.id _ := hi`. Establish `hB'` using `hB F F 1 hz n hn γ`.

Establish `hP'` using `(hP F F 1 hz n hn).2 γ γ`. Rewrite `hB'`, `hP'` using `[hg]`. Rewrite `hP'` using `[hi']`. Simplify using `only [mapGL_id'] at hB' hP'`. Use `⟨hB', fun hs D hD => ?_⟩` and prove the remaining obligations.

Establish `hN : PositivityTheory.Rg.Tf.Loc.twNorm (mapGL n (RingHom.id _)) (Module.finrank F F) γ = γ`. Simplify using `[PositivityTheory.Rg.Tf.Loc.twNorm]`. Both sides reduce to the same expression. Take `⟨C, hC, h⟩` from `hP' hs hN D hD`. Conclude with `⟨C, hC, h⟩`.
-/
theorem UpperTheory.infinitePart_finite_of_adelicBound :
    P2 → Triv → BoundE → InfF := by
  intro hP hT hB F _ _ n hn γ
  have hz : ∀ τ : F ≃ₐ[F] F, τ ∈ Subgroup.zpowers (1 : F ≃ₐ[F] F) := fun τ => by
    have h1 : τ = 1 := by
      ext x
      exact τ.commutes x
    rw [h1]
    exact one_mem _
  obtain ⟨hg, hi, -⟩ := hT F
  have hi' : GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := F) = RingHom.id _ := hi
  have hB' := hB F F 1 hz n hn γ
  have hP' := (hP F F 1 hz n hn).2 γ γ
  rw [hg] at hB' hP'
  rw [hi'] at hP'
  simp only [mapGL_id'] at hB' hP'
  refine ⟨hB', fun hs D hD => ?_⟩
  have hN : PositivityTheory.Rg.Tf.Loc.twNorm (mapGL n (RingHom.id _)) (Module.finrank F F) γ = γ := by
    simp [PositivityTheory.Rg.Tf.Loc.twNorm]
    rfl
  obtain ⟨C, hC, h⟩ := hP' hs hN D hD
  exact ⟨C, hC, h⟩

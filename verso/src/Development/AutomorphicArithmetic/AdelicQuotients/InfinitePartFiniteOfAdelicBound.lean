import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
private theorem mapGL_id' {R : Type} [CommRing R] (n : ℕ) (x : Matrix.GeneralLinearGroup (Fin n) R) :
    PositivityTheory.Rg.Tf.Geo.mapGL n (RingHom.id R) x = x := by
  ext i j
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
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

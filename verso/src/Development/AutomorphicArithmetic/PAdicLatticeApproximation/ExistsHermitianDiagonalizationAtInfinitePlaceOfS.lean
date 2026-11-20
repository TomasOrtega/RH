import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Establish `hSu : IsUnit S.det` using `isUnit_iff_ne_zero.mpr hS`. Establish `hgu : IsUnit g.det` using `isUnit_iff_ne_zero.mpr hgd`. Establish `SiS : S⁻¹ * S = 1` using `Matrix.nonsing_inv_mul S hSu`. Establish `SSi : S * S⁻¹ = 1` using `Matrix.mul_nonsing_inv S hSu`. Establish `giG : g⁻¹ * g = 1` using `Matrix.nonsing_inv_mul g hgu`.

Establish `gGi : g * g⁻¹ = 1` using `Matrix.mul_nonsing_inv g hgu`. Establish `h1 : ∀ c, T c * S⁻¹ = S⁻¹ * ψ c` using `fun c => by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, SiS, Matrix.one_mul]`. Use `_ = S⁻¹ * ψ c := by`.

Rewrite using `[← hψ, Matrix.mul_assoc, Matrix.mul_assoc, SSi, Matrix.mul_one]`. Use `set Av := (S⁻¹)ᴴ * A' * S⁻¹ with hAv`. Establish `h2 : ∀ c, Av * ψ (s c) = (ψ c)ᴴ * Av` using `fun c => by`. Establish `e : (S⁻¹)ᴴ * (T c)ᴴ = (ψ c)ᴴ * (S⁻¹)ᴴ`. Rewrite using `[← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hAv, Matrix.mul_assoc _ S⁻¹]`. Use `_ = (S⁻¹)ᴴ * (A' * T (s c)) * S⁻¹ := by`. Rewrite using `[← h1]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = ((S⁻¹)ᴴ * (T c)ᴴ) * A' * S⁻¹ := by`. Rewrite using `[hrel]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (ψ c)ᴴ * Av := by`. Rewrite using `[e, hAv]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `h3 : ∀ c, g * ψ (s c) = (ψ c)ᴴ * g` using `fun c => by`. Rewrite using `[hstar, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gGi, Matrix.one_mul]`. Use `set B := g⁻¹ * Av with hB`. Establish `h4 : ∀ c, B * ψ c = ψ c * B` using `fun c => by`.

Take `⟨d, rfl⟩` from `hs c`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc g g⁻¹, gGi, Matrix.one_mul]`. Use `_ = ψ (s d) * B := by`.

Rewrite using `[hB, ← h3, ← Matrix.mul_assoc g⁻¹ g, giG, Matrix.one_mul]`. Establish `hT : ∀ c, T c = S⁻¹ * ψ c * S` using `fun c => by`. Rewrite using `[← h1, Matrix.mul_assoc, SiS, Matrix.mul_one]`. Establish `h5 : ∀ c, (S⁻¹ * B * S) * T c = T c * (S⁻¹ * B * S)` using `fun c => by`. Rewrite using `[hT]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = S⁻¹ * (B * ψ c) * S := by`. Rewrite using `[SSi, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = S⁻¹ * ψ c * (S * S⁻¹) * B * S := by`. Rewrite using `[h4, SSi, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = S⁻¹ * ψ c * S * (S⁻¹ * B * S) := by`. Simplify using `only [Matrix.mul_assoc]`.

Take `⟨lam, hlam⟩` from `Matrix.mem_range_scalar_of_commute_single (M := S⁻¹ * B * S) (fun i j _ => by`. Take `⟨c, hc⟩` from `hspan i j`. Use `h5 c` as an intermediate fact. Rewrite `this` using `[hc]`. Conclude with `this.symm)`.

Establish `hlam' : S⁻¹ * B * S = lam • (1 : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[← hlam]`. Use extensionality with `i j`. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]`. Establish `hBl : B = lam • (1 : Matrix (Fin n) (Fin n) ℂ)`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[SSi, Matrix.mul_one, ← Matrix.mul_assoc, SSi, Matrix.one_mul]`. Use `_ = lam • (1 : Matrix (Fin n) (Fin n) ℂ) := by`. Rewrite using `[hlam', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, SSi]`.

Establish `hAl : Av = lam • g`. Combine the equalities or inequalities in the displayed calculation. Establish `hsk : Avᴴ = -Av`. Rewrite using `[hAv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hskew]`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`.

Establish `hg0 : g ≠ 0`. Introduce and unpack `rfl`. Use `haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩`. Conclude with `hgd Matrix.det_zero`. Use `⟨lam, ?_, hAl⟩` and prove the remaining obligations.

Rewrite `hsk` using `[hAl, Matrix.conjTranspose_smul, hgH.eq]`. Establish `h6 : ((starRingEnd ℂ) lam + lam) • g = 0`. Rewrite using `[add_smul]`. Establish `: star lam • g = -(lam • g)` using `hsk`. Express the relevant statement in the definitionally equal form `star lam • g + lam • g = 0`.

Rewrite using `[this, neg_add_cancel]`. Break down `smul_eq_zero.mp h6 with h | h` into its components or cases. Conclude with `eq_neg_of_add_eq_zero_left h`. Conclude with `absurd h hg0`.
-/
private lemma archPlace_core {C : Type} [Ring C] {n : ℕ} (hn : 0 < n)
    (ψ : C →+* Matrix (Fin n) (Fin n) ℂ) (T : C → Matrix (Fin n) (Fin n) ℂ) (s : C → C)
    (hs : Function.Surjective s) (S g A' : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.det ≠ 0) (hgH : g.IsHermitian) (hgd : g.det ≠ 0)
    (hψ : ∀ c, ψ c * S = S * T c)
    (hstar : ∀ c, ψ (s c) = g⁻¹ * (ψ c)ᴴ * g)
    (hrel : ∀ c, A' * T (s c) = (T c)ᴴ * A')
    (hskew : A'ᴴ = -A')
    (hspan : ∀ i j, ∃ c, T c = Matrix.single i j (1 : ℂ)) :
    ∃ lam : ℂ, (starRingEnd ℂ) lam = -lam ∧ (S⁻¹)ᴴ * A' * S⁻¹ = lam • g := by
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hS
  have hgu : IsUnit g.det := isUnit_iff_ne_zero.mpr hgd
  have SiS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSu
  have SSi : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSu
  have giG : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hgu
  have gGi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgu
  have h1 : ∀ c, T c * S⁻¹ = S⁻¹ * ψ c := fun c => by
    calc T c * S⁻¹ = S⁻¹ * (S * T c) * S⁻¹ := by
          rw [← Matrix.mul_assoc, SiS, Matrix.one_mul]
      _ = S⁻¹ * ψ c := by
          rw [← hψ, Matrix.mul_assoc, Matrix.mul_assoc, SSi, Matrix.mul_one]
  set Av := (S⁻¹)ᴴ * A' * S⁻¹ with hAv
  have h2 : ∀ c, Av * ψ (s c) = (ψ c)ᴴ * Av := fun c => by
    have e : (S⁻¹)ᴴ * (T c)ᴴ = (ψ c)ᴴ * (S⁻¹)ᴴ := by
      rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_mul]
    calc Av * ψ (s c) = (S⁻¹)ᴴ * A' * (S⁻¹ * ψ (s c)) := by
          rw [hAv, Matrix.mul_assoc _ S⁻¹]
      _ = (S⁻¹)ᴴ * (A' * T (s c)) * S⁻¹ := by
          rw [← h1]; simp only [Matrix.mul_assoc]
      _ = ((S⁻¹)ᴴ * (T c)ᴴ) * A' * S⁻¹ := by
          rw [hrel]; simp only [Matrix.mul_assoc]
      _ = (ψ c)ᴴ * Av := by
          rw [e, hAv]; simp only [Matrix.mul_assoc]
  have h3 : ∀ c, g * ψ (s c) = (ψ c)ᴴ * g := fun c => by
    rw [hstar, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gGi, Matrix.one_mul]
  set B := g⁻¹ * Av with hB
  have h4 : ∀ c, B * ψ c = ψ c * B := fun c => by
    obtain ⟨d, rfl⟩ := hs c
    calc B * ψ (s d) = g⁻¹ * ((ψ d)ᴴ * Av) := by rw [hB, Matrix.mul_assoc, h2]
      _ = (g⁻¹ * ((ψ d)ᴴ * g)) * (g⁻¹ * Av) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc g g⁻¹, gGi, Matrix.one_mul]
      _ = ψ (s d) * B := by
          rw [hB, ← h3, ← Matrix.mul_assoc g⁻¹ g, giG, Matrix.one_mul]
  have hT : ∀ c, T c = S⁻¹ * ψ c * S := fun c => by
    rw [← h1, Matrix.mul_assoc, SiS, Matrix.mul_one]
  have h5 : ∀ c, (S⁻¹ * B * S) * T c = T c * (S⁻¹ * B * S) := fun c => by
    rw [hT]
    calc S⁻¹ * B * S * (S⁻¹ * ψ c * S) = S⁻¹ * B * (S * S⁻¹) * ψ c * S := by
          simp only [Matrix.mul_assoc]
      _ = S⁻¹ * (B * ψ c) * S := by
          rw [SSi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = S⁻¹ * ψ c * (S * S⁻¹) * B * S := by
          rw [h4, SSi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = S⁻¹ * ψ c * S * (S⁻¹ * B * S) := by
          simp only [Matrix.mul_assoc]
  obtain ⟨lam, hlam⟩ := Matrix.mem_range_scalar_of_commute_single (M := S⁻¹ * B * S)
    (fun i j _ => by
      obtain ⟨c, hc⟩ := hspan i j
      have := h5 c
      rw [hc] at this
      exact this.symm)
  have hlam' : S⁻¹ * B * S = lam • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← hlam]; ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hBl : B = lam • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    calc B = S * (S⁻¹ * B * S) * S⁻¹ := by
          simp only [Matrix.mul_assoc]
          rw [SSi, Matrix.mul_one, ← Matrix.mul_assoc, SSi, Matrix.one_mul]
      _ = lam • (1 : Matrix (Fin n) (Fin n) ℂ) := by
          rw [hlam', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, SSi]
  have hAl : Av = lam • g := by
    calc Av = g * B := by rw [hB, ← Matrix.mul_assoc, gGi, Matrix.one_mul]
      _ = lam • g := by rw [hBl, Matrix.mul_smul, Matrix.mul_one]
  have hsk : Avᴴ = -Av := by
    rw [hAv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hskew]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hg0 : g ≠ 0 := by
    rintro rfl
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact hgd Matrix.det_zero
  refine ⟨lam, ?_, hAl⟩
  rw [hAl, Matrix.conjTranspose_smul, hgH.eq] at hsk
  have h6 : ((starRingEnd ℂ) lam + lam) • g = 0 := by
    rw [add_smul]
    have : star lam • g = -(lam • g) := hsk
    change star lam • g + lam • g = 0
    rw [this, neg_add_cancel]
  rcases smul_eq_zero.mp h6 with h | h
  · exact eq_neg_of_add_eq_zero_left h
  · exact absurd h hg0

/- English proof (translation)
Introduce `p _ G σ A hSN _ hskew hrel v`. Set `ψ : Matrix (Fin G.n) (Fin G.n) G.F →+* Matrix (Fin G.n) (Fin G.n) ℂ` to `(G.psi v).comp (σ.symm : Matrix (Fin G.n) (Fin G.n) G.F →ₐ[G.F] G.C).toRingHom`. Establish `hψ : ∀ x : G.F, ψ (Matrix.scalar (Fin G.n) x) = Matrix.scalar (Fin G.n) (v.embedding x)` using `fun x => by`. Establish `e : Matrix.scalar (Fin G.n) x = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) G.F) x`. Rewrite using `[Matrix.algebraMap_eq_diagonal]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `G.psi v (σ.symm (Matrix.scalar (Fin G.n) x)) = _`. Rewrite using `[e, AlgEquiv.commutes, G.psi_F]`. Take `⟨S, hS, hSψ⟩` from `hSN G.F ℂ G.n v.embedding ψ hψ`. Establish `hpsi : ∀ c, G.psi v c * S = S * (σ c).map v.embedding` using `fun c => by`.

Use `hSψ (σ c)` as an intermediate fact. Establish `e : ψ (σ c) = G.psi v c`. Express the relevant statement in the definitionally equal form `G.psi v (σ.symm (σ c)) = _`. Rewrite using `[AlgEquiv.symm_apply_apply]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Establish `hconj : ∀ M : Matrix (Fin G.n) (Fin G.n) G.F, ((M.map (IsCMField.complexConj G.F))ᵀ).map v.embedding = (M.map v.embedding)ᴴ` using `fun M => by`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply, IsCMField.complexEmbedding_complexConj]`. Establish `hrel' : ∀ c, A.map v.embedding * (σ (sh G c)).map v.embedding = ((σ c).map v.embedding)ᴴ * A.map v.embedding` using `fun c => by`. Use `congrArg (fun M => M.map v.embedding) (hrel c)` as an intermediate fact.

Simplify `this` using `only [Matrix.map_mul, hconj]`. Establish `hskew' : (A.map v.embedding)ᴴ = -A.map v.embedding`. Rewrite using `[← hconj, hskew]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Take `⟨lam, h1, h2⟩` from `archPlace_core G.n_pos (G.psi v) (fun c => (σ c).map v.embedding) (sh G) (fun c => ⟨sh G c, by simp [sh, G.star_star]⟩) S (G.gram v) (A.map v.embedding) hS (G.gram_herm v) (G.gram_det v) hpsi (fun c => G.psi_star v c) hrel' hskew' (fun i j => ⟨σ.symm (Matrix.single i j 1), by`. Use extensionality with `a b`. Simplify using `[Matrix.single_apply]⟩)`. Conclude with `⟨S, lam, hS, hpsi, h1, h2⟩`.
-/
theorem UpperTheory.exists_hermitian_diagonalization_at_infinitePlace_of_skewHermitian :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (σ : G.C ≃ₐ[G.F] Matrix (Fin G.n) (Fin G.n) G.F) (A : Matrix (Fin G.n) (Fin G.n) G.F), UpperTheory.Gal.W2.SN → A.det ≠ 0 → (A.map (IsCMField.complexConj G.F))ᵀ = -A → (∀ c, A * σ (sh G c) = ((σ c).map (IsCMField.complexConj G.F))ᵀ * A) → ∀ v : InfinitePlace G.F, ∃ (S : Matrix (Fin G.n) (Fin G.n) ℂ) (lam : ℂ), S.det ≠ 0 ∧ (∀ c, G.psi v c * S = S * (σ c).map v.embedding) ∧ (starRingEnd ℂ) lam = -lam ∧ (S⁻¹)ᴴ * A.map v.embedding * S⁻¹ = lam • G.gram v := by
  intro p _ G σ A hSN _ hskew hrel v
  let ψ : Matrix (Fin G.n) (Fin G.n) G.F →+* Matrix (Fin G.n) (Fin G.n) ℂ :=
    (G.psi v).comp (σ.symm : Matrix (Fin G.n) (Fin G.n) G.F →ₐ[G.F] G.C).toRingHom
  have hψ : ∀ x : G.F, ψ (Matrix.scalar (Fin G.n) x) = Matrix.scalar (Fin G.n) (v.embedding x) := fun x => by
    have e : Matrix.scalar (Fin G.n) x = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) G.F) x := by
      rw [Matrix.algebraMap_eq_diagonal]; rfl
    change G.psi v (σ.symm (Matrix.scalar (Fin G.n) x)) = _
    rw [e, AlgEquiv.commutes, G.psi_F]
  obtain ⟨S, hS, hSψ⟩ := hSN G.F ℂ G.n v.embedding ψ hψ
  have hpsi : ∀ c, G.psi v c * S = S * (σ c).map v.embedding := fun c => by
    have := hSψ (σ c)
    have e : ψ (σ c) = G.psi v c := by
      change G.psi v (σ.symm (σ c)) = _
      rw [AlgEquiv.symm_apply_apply]
    rwa [e] at this
  have hconj : ∀ M : Matrix (Fin G.n) (Fin G.n) G.F,
      ((M.map (IsCMField.complexConj G.F))ᵀ).map v.embedding = (M.map v.embedding)ᴴ := fun M => by
    ext i j
    simp [Matrix.conjTranspose_apply, IsCMField.complexEmbedding_complexConj]
  have hrel' : ∀ c, A.map v.embedding * (σ (sh G c)).map v.embedding
      = ((σ c).map v.embedding)ᴴ * A.map v.embedding := fun c => by
    have := congrArg (fun M => M.map v.embedding) (hrel c)
    simpa only [Matrix.map_mul, hconj] using this
  have hskew' : (A.map v.embedding)ᴴ = -A.map v.embedding := by
    rw [← hconj, hskew]
    ext i j
    simp
  obtain ⟨lam, h1, h2⟩ := archPlace_core G.n_pos (G.psi v) (fun c => (σ c).map v.embedding) (sh G)
    (fun c => ⟨sh G c, by simp [sh, G.star_star]⟩) S (G.gram v) (A.map v.embedding) hS
    (G.gram_herm v) (G.gram_det v) hpsi (fun c => G.psi_star v c) hrel' hskew'
    (fun i j => ⟨σ.symm (Matrix.single i j 1), by
      ext a b
      simp [Matrix.single_apply]⟩)
  exact ⟨S, lam, hS, hpsi, h1, h2⟩

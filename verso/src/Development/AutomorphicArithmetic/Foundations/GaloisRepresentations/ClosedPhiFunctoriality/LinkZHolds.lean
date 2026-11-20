import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrame
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

/- English proof (translation)
Introduce `hA hQ l _ K bk τ hτ N M`. Take `⟨n, hn⟩` from `hQ l K bk N M`. Use `⟨max n M, ?_⟩` and prove the remaining obligations. Introduce `k d d' ρ ρ' F F' Y Y₁ hY hY₁ Q Q' Q₁ Q₁' hS hS₁ Pi R hL`. Take `⟨h1, h2⟩` from `hA l K bk τ hτ N d d' (max n M) ρ ρ' F F' Y Y₁ hY hY₁ Pi R hL`.

Establish `hfz : ∀ z : ℤ_[l], fI l (Per.zA l z) = zC l z` using `fun z => by`. Establish `h` using `(ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z`. Simplify using `only [fI, zC, RingHom.comp_apply]`. Rewrite using `[← GlobalTheory.RingBasics.φA_apply, h]`. Establish `hfe : ∀ s : bk.S, fI l (bk.ev s) = fA bk s` using `fun s => by`.

Simplify using `only [fI, fA, RingHom.comp_apply, bk.ev_frob]`. Establish `hlM : ∀ i j, (l : Per.Acris l) ^ M ∣ (Pi.map (zC l) * Y₁.map (fI l) - Y.map (fI l) * R.map (fA bk)) i j`. Introduce `i j`. Establish `h` using `map_dvd (fI l) (h1 i j)`. Simplify using `only [Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, Matrix.map_apply, hfz, hfe, map_pow, map_natCast] at h ⊢`.

Conclude with `(pow_dvd_pow _ (le_max_right _ _)).trans h`. Establish `h3` using `hn k d d' F.A F'.A F'.A' Q Q' Q₁ Q₁' R F'.A_mul hS hS₁ (fun i j => (pow_dvd_pow _ (le_max_left _ _)).trans (h2 i j))`. Introduce `i j`. Establish `e : Pi.map (zC l) * (Y₁.map (fI l) * Q₁) - (Y.map (fI l) * Q) * R.map (f0 bk) = (Pi.map (zC l) * Y₁.map (fI l) - Y.map (fI l) * R.map (fA bk)) * Q₁ + Y.map (fI l) * (R.map (fA bk) * Q₁ - Q * R.map (f0 bk))`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]`. Conclude with `dvd_add (Finset.dvd_sum fun x _ => (hlM i x).mul_right _) (Finset.dvd_sum fun x _ => (h3 x j).mul_left _)`.
-/
theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkZ_holds :
    LinkA → LinkQ → LinkZ := by
  intro hA hQ l _ K bk τ hτ N M
  obtain ⟨n, hn⟩ := hQ l K bk N M
  refine ⟨max n M, ?_⟩
  intro k d d' ρ ρ' F F' Y Y₁ hY hY₁ Q Q' Q₁ Q₁' hS hS₁ Pi R hL
  obtain ⟨h1, h2⟩ := hA l K bk τ hτ N d d' (max n M) ρ ρ' F F' Y Y₁ hY hY₁ Pi R hL
  have hfz : ∀ z : ℤ_[l], fI l (Per.zA l z) = zC l z := fun z => by
    have h := (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z
    simp only [fI, zC, RingHom.comp_apply]
    rw [← GlobalTheory.RingBasics.φA_apply, h]
  have hfe : ∀ s : bk.S, fI l (bk.ev s) = fA bk s := fun s => by
    simp only [fI, fA, RingHom.comp_apply, bk.ev_frob]
  have hlM : ∀ i j, (l : Per.Acris l) ^ M ∣
      (Pi.map (zC l) * Y₁.map (fI l) - Y.map (fI l) * R.map (fA bk)) i j := by
    intro i j
    have h := map_dvd (fI l) (h1 i j)
    simp only [Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, Matrix.map_apply, hfz, hfe,
      map_pow, map_natCast] at h ⊢
    exact (pow_dvd_pow _ (le_max_right _ _)).trans h
  have h3 := hn k d d' F.A F'.A F'.A' Q Q' Q₁ Q₁' R F'.A_mul hS hS₁
    (fun i j => (pow_dvd_pow _ (le_max_left _ _)).trans (h2 i j))
  intro i j
  have e : Pi.map (zC l) * (Y₁.map (fI l) * Q₁) - (Y.map (fI l) * Q) * R.map (f0 bk) =
      (Pi.map (zC l) * Y₁.map (fI l) - Y.map (fI l) * R.map (fA bk)) * Q₁ +
        Y.map (fI l) * (R.map (fA bk) * Q₁ - Q * R.map (f0 bk)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact dvd_add (Finset.dvd_sum fun x _ => (hlM i x).mul_right _)
    (Finset.dvd_sum fun x _ => (h3 x j).mul_left _)

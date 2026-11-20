import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeM
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeN
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeO
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeQ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section PushForward

variable {e : ℕ} {X : Type} [TopologicalSpace X]

/- English proof (translation)
The claim follows from `locDensChart A Φ hΦ j k y hy hk`.
-/
theorem locDens_chart (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j k : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hk : (A.chart j).symm y ∈ (A.chart k).source) :
    locDens A Φ j y = locDens A Φ k (A.chart k ((A.chart j).symm y)) *
      ‖LinearMap.det (fderiv ℂ (A.chart k ∘ (A.chart j).symm) y :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 :=
  locDensChart A Φ hΦ j k y hy hk

/- English proof (translation)
The claim follows from `pushForward_null' A Φ hΦ q S hS hq hfin g hg`.
-/
theorem pushForward_null [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (q : X → Fin e → ℂ) (S : Set X)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (g : X → ℝ) (hg : MIntegrable A Φ g) :
    mInt A Φ g = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x :=
  pushForward_null' A Φ hΦ q S hS hq hfin g hg

end PushForward

section Res

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

/- English proof (translation)
The claim follows from `volume_projection_zeroSet_null R Ψ hP hΨ j`.
-/
theorem psi0_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 = 0}) = 0 :=
  volume_projection_zeroSet_null R Ψ hP hΨ j

/- English proof (translation)
The claim follows from `ram_null' R Ψ hP hΨ j`.
-/
theorem ram_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 :=
  ram_null' R Ψ hP hΨ j

/- English proof (translation)
Establish `h3 : brBad R Ψ ⊆ {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪ {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ ∃ k, x ∈ (R.A.chart k).source ∧ LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}`. Introduce and unpack `x ((h | h) | ⟨k, hk, hn⟩)`. Conclude with `Or.inl (Or.inl h)`. Conclude with `Or.inl (Or.inr h)`. Distinguish the cases in `h0 : Ψ (segre (R.lift x x)) 0 = 0`.

Conclude with `Or.inl (Or.inr h0)`. Use `Or.inr ⟨h0, k, hk, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hd`. Conclude with `hn ⟨analyticAt_brQ R Ψ x k hk h0, hd⟩`. Use `measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono h3)) ?_` and prove the remaining obligations.

Simplify using `only [Set.preimage_union, Set.inter_union_distrib_left]`. Conclude with `measure_union_null (measure_union_null (R.null j) (psi0_null R Ψ hP hΨ j)) (ram_null R Ψ hP hΨ j)`.
-/
theorem brBad_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ) = 0 := by
  have h3 : brBad R Ψ ⊆ {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
      {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0} := by
    rintro x ((h | h) | ⟨k, hk, hn⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · by_cases h0 : Ψ (segre (R.lift x x)) 0 = 0
      · exact Or.inl (Or.inr h0)
      · refine Or.inr ⟨h0, k, hk, ?_⟩
        by_contra hd
        exact hn ⟨analyticAt_brQ R Ψ x k hk h0, hd⟩
  refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono h3)) ?_
  simp only [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (measure_union_null (R.null j) (psi0_null R Ψ hP hΨ j))
    (ram_null R Ψ hP hΨ j)

/- English proof (translation)
The claim follows from `isPotential_potOf R hL`.
-/
theorem potOf_isPotential (R : AnLogRes P J e) (L : HermLine ι) (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) :=
  isPotential_potOf R hL

/- English proof (translation)
The claim follows from `logAbsLocInt'`.
-/
theorem logAbsLocInt : LogAbsLocIntStatement := logAbsLocInt'

/- English proof (translation)
The claim follows from `brIntegrable_of logAbsLocInt R L A s hL hA hs`.
-/
theorem brIntegrable (R : AnLogRes P J e) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) :=
  brIntegrable_of logAbsLocInt R L A s hL hA hs

/- English proof (translation)
The claim follows from `normPoly_of pcMinContract`.
-/
theorem normPoly : NormPolyStatement := normPoly_of pcMinContract

/- English proof (translation)
The claim follows from `projB_null_of normPoly Ψ hP hΨ hJ hJP`.
-/
theorem projB_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hJ : IsMultiHomogIdeal J) (hJP : ¬ J ≤ P) :
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} = 0 :=
  projB_null_of normPoly Ψ hP hΨ hJ hJP

/- English proof (translation)
The claim follows from `brQ_image_null_of R Ψ (brBad_null R Ψ hP hΨ)`.
-/
theorem brQ_image_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) :
    volume (brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
  brQ_image_null_of R Ψ (brBad_null R Ψ hP hΨ)

/- English proof (translation)
Establish `hN : volume ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪ brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0` using `measure_union_null (projB_null Ψ hP hΨ R.homog R.nondeg) (brQ_image_null R Ψ hP hΨ)`. Establish `hNae : ∀ᵐ y, y ∉ ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪ brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0}))` using `ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hN)`. Use `filter_upwards [hNae, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind`. Establish `hy1 : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y` using `fun h => hyN (Or.inl h)`. Establish `hfib : fibre P Ψ y = brW R Ψ '' (brQ R Ψ ⁻¹' {y} \ brBad R Ψ)`.

Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Take `⟨x, -, hx0, hxq, rfl⟩` from `exists_of_mem_fibre R Ψ hw hy1`. Conclude with `⟨x, ⟨hxq, fun hbad => hyN (Or.inr ⟨x, ⟨hbad, hx0⟩, hxq⟩)⟩, rfl⟩`.

Introduce and unpack `⟨x, hx, rfl⟩`. Use `brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)` as an intermediate fact. Rewrite `this` using `[show brQ R Ψ x = y from hx.1]`. Then use the resulting hypothesis. Rewrite using `[hfib, finsum_mem_image ((brW_injOn R Ψ).mono fun x hx => show _ ∧ _ from ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩)]`. Use `finsum_mem_congr rfl fun x hx => ?_` and prove the remaining obligations.

Take `⟨γ, hγ, hval⟩` from `exists_sheet_brW R Ψ L A s hP hL hs x hx.2`. Rewrite `hγ`, `hval` using `[show brQ R Ψ x = y from hx.1]`. Unfold `sheetDensity`. Rewrite using `[dif_pos ⟨γ, hγ⟩]`. Conclude with `(hind _ _ _ (Exists.choose_spec (⟨γ, hγ⟩ : ∃ γ, IsSheet P Ψ y (brW R Ψ x) γ)) hγ).trans hval`.
-/
theorem brFibreSum_ae (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w =
      ∑ᶠ x ∈ brQ R Ψ ⁻¹' {y} \ brBad R Ψ,
        logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x := by
  have hN : volume ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
    measure_union_null (projB_null Ψ hP hΨ R.homog R.nondeg) (brQ_image_null R Ψ hP hΨ)
  have hNae : ∀ᵐ y, y ∉ ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) :=
    ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hN)
  filter_upwards [hNae, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hy1 : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y := fun h => hyN (Or.inl h)
  have hfib : fibre P Ψ y = brW R Ψ '' (brQ R Ψ ⁻¹' {y} \ brBad R Ψ) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, -, hx0, hxq, rfl⟩ := exists_of_mem_fibre R Ψ hw hy1
      exact ⟨x, ⟨hxq, fun hbad => hyN (Or.inr ⟨x, ⟨hbad, hx0⟩, hxq⟩)⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
      rwa [show brQ R Ψ x = y from hx.1] at this
  rw [hfib, finsum_mem_image ((brW_injOn R Ψ).mono fun x hx => show _ ∧ _ from
    ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩)]
  refine finsum_mem_congr rfl fun x hx => ?_
  obtain ⟨γ, hγ, hval⟩ := exists_sheet_brW R Ψ L A s hP hL hs x hx.2
  rw [show brQ R Ψ x = y from hx.1] at hγ hval
  unfold sheetDensity
  rw [dif_pos ⟨γ, hγ⟩]
  exact (hind _ _ _ (Exists.choose_spec (⟨γ, hγ⟩ : ∃ γ, IsSheet P Ψ y (brW R Ψ x) γ)) hγ).trans hval

end Res

end ReciprocityTheory.ChartRestriction.G.Geo

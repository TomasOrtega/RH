import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariant

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace CExt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth Topology Filter Set
open scoped Manifold

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def colMap (p : (k : K) → ι k) (m : (Σ k, ι k × ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => m ⟨q.1, (q.2, p q.1)⟩

/- English proof (translation)
The claim follows from `contDiff_pi.2 fun q => contDiff_apply ℝ ℂ (⟨q.1, (q.2, p q.1)⟩ : Σ k, ι k × ι k)`.
-/
theorem colMap_contDiff (p : (k : K) → ι k) {n : WithTop ℕ∞} : ContDiff ℝ n (colMap p) :=
  contDiff_pi.2 fun q => contDiff_apply ℝ ℂ (⟨q.1, (q.2, p q.1)⟩ : Σ k, ι k × ι k)

/- English proof (translation)
Use `⟨fun k => (starRingEnd ℂ) (z ⟨k, p k⟩) / (blockSq z k : ℂ), fun k => div_ne_zero ((map_ne_zero _).2 (hp k)) (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne'), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Simplify using `only [colMap, prMap]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sameOrbit_colMap {p : (k : K) → ι k} {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι)
    (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) : SameOrbit (colMap p (prMap z)) z := by
  refine ⟨fun k => (starRingEnd ℂ) (z ⟨k, p k⟩) / (blockSq z k : ℂ), fun k =>
    div_ne_zero ((map_ne_zero _).2 (hp k)) (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne'), ?_⟩
  funext q
  simp only [colMap, prMap]
  ring

/- English proof (translation)
The claim follows from `div_ne_zero (mul_ne_zero hi ((map_ne_zero _).2 hi)) (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne')`.
-/
theorem prMap_diag_ne_zero {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι) {k : K} {i : ι k}
    (hi : z ⟨k, i⟩ ≠ 0) : prMap z ⟨k, (i, i)⟩ ≠ 0 :=
  div_ne_zero (mul_ne_zero hi ((map_ne_zero _).2 hi))
    (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne')

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Simplify using `[prMap, h0]`.
-/
theorem ne_zero_of_prMap_diag {z : (Σ k, ι k) → ℂ} {k : K} {i : ι k}
    (h : prMap z ⟨k, (i, i)⟩ ≠ 0) : z ⟨k, i⟩ ≠ 0 := by
  intro h0
  apply h
  simp [prMap, h0]

/- English proof (translation)
Establish `hA : IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}`. Simplify using `only [setOf_forall]`. Conclude with `isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const`. Establish `hC` using `(isCompact_unitBlocks (K := K) (ι := ι)).inter_right hA`. Establish `hcont : ContinuousOn (prMap (K` using `K) (ι := ι)) (unitBlocks K ι ∩ {z | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}) := fun z hz => (prMap_continuousAt (unitBlocks_subset hz.1)).continuousWithinAt`.

Use `(hC.image_of_continuousOn hcont).isClosed using 1` and compare the differences between its conclusion and the goal. Use extensionality with `m`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Take `⟨c, hc, hu⟩` from `exists_normalize (K := K) (ι := ι) hz.1`.

Conclude with `⟨_, ⟨hu, (mcPts_smul hP c hc hz).2⟩, prMap_smul c z hc⟩`. Introduce and unpack `⟨z, ⟨hu, hz⟩, rfl⟩`. Conclude with `⟨z, ⟨unitBlocks_subset hu, hz⟩, rfl⟩`.
-/
theorem isClosed_prMap_image {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsClosed (prMap '' mcPts P) := by
  have hA : IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have hC := (isCompact_unitBlocks (K := K) (ι := ι)).inter_right hA
  have hcont : ContinuousOn (prMap (K := K) (ι := ι)) (unitBlocks K ι ∩
      {z | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}) := fun z hz =>
    (prMap_continuousAt (unitBlocks_subset hz.1)).continuousWithinAt
  convert (hC.image_of_continuousOn hcont).isClosed using 1
  ext m
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨c, hc, hu⟩ := exists_normalize (K := K) (ι := ι) hz.1
    exact ⟨_, ⟨hu, (mcPts_smul hP c hc hz).2⟩, prMap_smul c z hc⟩
  · rintro ⟨z, ⟨hu, hz⟩, rfl⟩
    exact ⟨z, ⟨unitBlocks_subset hu, hz⟩, rfl⟩

/- English proof (translation)
Establish `ht : ∀ m : (Σ k, ι k × ι k) → ℂ, Convex ℝ {r : ℝ | ∀ z ∈ mcPts P, prMap z = m → r = u z}`. Introduce `m x hx y hy a b _ _ hab z hz hzm`. Rewrite using `[smul_eq_mul, smul_eq_mul, hx z hz hzm, hy z hz hzm, ← add_mul, hab, one_mul]`. Take `⟨g, hg⟩` from `exists_contMDiffMap_forall_mem_convex_of_local (n := (⊤ : ℕ∞)) (M := (Σ k, ι k × ι k) → ℂ) (F := ℝ) 𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) ht (fun x => by`. Distinguish the cases in `hx : x ∈ prMap '' mcPts P`.

Take `⟨z₀, hz₀, rfl⟩` from `hx choose p hp using hz₀.1`. Take `⟨V, w, hV, hmem, hw, hwu⟩` from `hloc (colMap p (prMap z₀)) (mem_mcPts_of_sameOrbit hP (sameOrbit_colMap hz₀.1 hp) hz₀)`. Establish `hO : IsOpen (colMap p ⁻¹' V ∩ {m | ∀ k, m ⟨k, (p k, p k)⟩ ≠ 0})`. Use `(hV.preimage (colMap_contDiff p (n := 0)).continuous).inter ?_` and prove the remaining obligations. Simplify using `only [setOf_forall]`.

Conclude with `isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const`. Use `⟨_, hO.mem_nhds ⟨hmem, fun k => prMap_diag_ne_zero hz₀.1 (hp k)⟩, w ∘ colMap p, ?_, ?_⟩` and prove the remaining obligations. Conclude with `contMDiffOn_iff_contDiffOn.2 (hw.comp (colMap_contDiff p).contDiffOn fun y hy => hy.1)`. Introduce and unpack `y ⟨hy1, hy2⟩ z hz rfl`. Establish `ho` using `sameOrbit_colMap hz.1 fun k => ne_zero_of_prMap_diag (hy2 k)`.

Use `show w (colMap p (prMap z)) = u z`. Rewrite using `[hwu _ ⟨hy1, mem_mcPts_of_sameOrbit hP ho hz⟩]`. Conclude with `hinv z hz _ ho`. Use `⟨_, (isClosed_prMap_image hP).isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, ?_⟩` and prove the remaining obligations. Introduce `y hy z hz hzy`.

Conclude with `absurd ⟨z, hz, hzy⟩ hy)`. Conclude with `⟨g, contMDiff_iff_contDiff.1 g.contMDiff, fun z hz => hg _ z hz rfl⟩`.
-/
theorem exists_smooth_on_matrices {P : Ideal (MRing ι)} {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hP : IsMultiHomogIdeal P) (hinv : ∀ z ∈ mcPts P, ∀ z', SameOrbit z' z → u z' = u z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, ι k) → ℂ)) (w : ((Σ k, ι k) → ℂ) → ℝ), IsOpen V ∧ z ∈ V ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w V ∧ ∀ z' ∈ V ∩ mcPts P, w z' = u z') :
    ∃ g : ((Σ k, ι k × ι k) → ℂ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ z ∈ mcPts P, g (prMap z) = u z := by
  have ht : ∀ m : (Σ k, ι k × ι k) → ℂ,
      Convex ℝ {r : ℝ | ∀ z ∈ mcPts P, prMap z = m → r = u z} := by
    intro m x hx y hy a b _ _ hab z hz hzm
    rw [smul_eq_mul, smul_eq_mul, hx z hz hzm, hy z hz hzm, ← add_mul, hab, one_mul]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local (n := (⊤ : ℕ∞))
    (M := (Σ k, ι k × ι k) → ℂ) (F := ℝ) 𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) ht (fun x => by
    by_cases hx : x ∈ prMap '' mcPts P
    · obtain ⟨z₀, hz₀, rfl⟩ := hx
      choose p hp using hz₀.1
      obtain ⟨V, w, hV, hmem, hw, hwu⟩ := hloc (colMap p (prMap z₀))
        (mem_mcPts_of_sameOrbit hP (sameOrbit_colMap hz₀.1 hp) hz₀)
      have hO : IsOpen (colMap p ⁻¹' V ∩ {m | ∀ k, m ⟨k, (p k, p k)⟩ ≠ 0}) := by
        refine (hV.preimage (colMap_contDiff p (n := 0)).continuous).inter ?_
        simp only [setOf_forall]
        exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
      refine ⟨_, hO.mem_nhds ⟨hmem, fun k => prMap_diag_ne_zero hz₀.1 (hp k)⟩, w ∘ colMap p, ?_, ?_⟩
      · exact contMDiffOn_iff_contDiffOn.2
          (hw.comp (colMap_contDiff p).contDiffOn fun y hy => hy.1)
      · rintro y ⟨hy1, hy2⟩ z hz rfl
        have ho := sameOrbit_colMap hz.1 fun k => ne_zero_of_prMap_diag (hy2 k)
        show w (colMap p (prMap z)) = u z
        rw [hwu _ ⟨hy1, mem_mcPts_of_sameOrbit hP ho hz⟩]
        exact hinv z hz _ ho
    · refine ⟨_, (isClosed_prMap_image hP).isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, ?_⟩
      intro y hy z hz hzy
      exact absurd ⟨z, hz, hzy⟩ hy)
  exact ⟨g, contMDiff_iff_contDiff.1 g.contMDiff, fun z hz => hg _ z hz rfl⟩

variable (ι) in

def expLine (g : ((Σ k, ι k × ι k) → ℂ) → ℝ) : HermLine ι where
  a := 0
  h z := by
    classical
    exact if z ∈ nzBlocks K ι then Real.exp (g (prMap z)) else 1
  pos z hz := by
    split_ifs
    · exact Real.exp_pos _
    · exact one_pos
  smul c z hc := by
    classical
    have hiff : (fun p : Σ k, ι k => c p.1 * z p) ∈ nzBlocks K ι ↔ z ∈ nzBlocks K ι := by
      refine forall_congr' fun k => exists_congr fun i => ?_
      simp [hc k]
    simp only [hiff, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul, prMap_smul c z hc]

end CExt

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

/- English proof (translation)
Introduce `K _ ι _ P u hP hinv hloc`. Take `⟨g, hg, hgu⟩` from `CExt.exists_smooth_on_matrices hP hinv hloc`. Use `⟨CExt.expLine ι g, rfl, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z))) (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.nzBlocks K ι)` using `Real.contDiff_exp.comp_contDiffOn (hg.comp_contDiffOn GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap_contDiffOn)`. Use `h1.congr fun z hz => ?_` and prove the remaining obligations.

Conclude with `if_pos hz`. Establish `h2 : (CExt.expLine ι g).h z = Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z))` using `if_pos hz.1`. Rewrite using `[h2, Real.log_exp, hgu z hz]`.
-/
theorem exists_hermLine_of_local_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (u : ((Σ k, ι k) → ℂ) → ℝ), IsMultiHomogIdeal P → (∀ z ∈ mcPts P, ∀ z', SameOrbit z' z → u z' = u z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, ι k) → ℂ)) (w : ((Σ k, ι k) → ℂ) → ℝ), IsOpen V ∧ z ∈ V ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w V ∧ ∀ z' ∈ V ∩ mcPts P, w z' = u z') → ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ z ∈ mcPts P, Real.log (B.h z) = u z := by
  intro K _ ι _ P u hP hinv hloc
  obtain ⟨g, hg, hgu⟩ := CExt.exists_smooth_on_matrices hP hinv hloc
  refine ⟨CExt.expLine ι g, rfl, ?_, fun z hz => ?_⟩
  · have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z)))
        (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.nzBlocks K ι) :=
      Real.contDiff_exp.comp_contDiffOn
        (hg.comp_contDiffOn GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap_contDiffOn)
    refine h1.congr fun z hz => ?_
    exact if_pos hz
  · have h2 : (CExt.expLine ι g).h z = Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z)) :=
      if_pos hz.1
    rw [h2, Real.log_exp, hgu z hz]

end GlobalTheory.CompanionTheory.Ar.PB

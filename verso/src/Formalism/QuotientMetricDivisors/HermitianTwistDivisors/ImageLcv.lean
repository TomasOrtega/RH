import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

section SlopeTestRemainingChoices

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem imageLcv_mem_locP (p : Ideal R) [p.IsPrime] (A : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p A ↔ ∃ s ∈ p.primeCompl, s • x ∈ A := Iff.rfl

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Submodule.mem_map_equiv, imageLcv_mem_locP, imageLcv_mem_locP]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hx⟩`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Rewrite `hx` using `[Submodule.mem_map_equiv]`. Simplify `hx` using `[map_smul]`. Introduce and unpack `⟨s, hs, hx⟩`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_map_equiv]`.

Simplify `hx` using `[map_smul]`.
-/
theorem localization_map' (p : Ideal R) [p.IsPrime] (f : W ≃ₗ[R] W) (A : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ p (A.map (f : W →ₗ[R] W)) = (Formalism.HermitianLatticesTheory.localization₂ p A).map (f : W →ₗ[R] W) := by
  ext x
  rw [Submodule.mem_map_equiv, imageLcv_mem_locP, imageLcv_mem_locP]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mem_map_equiv] at hx
    simpa [map_smul] using hx
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mem_map_equiv]
    simpa [map_smul] using hx

/- English proof (translation)
Use `symm`. Apply `LinearEquiv.length_eq` to reduce the goal to its premises. Use `Submodule.Quotient.equiv _ _ (f.submoduleMap X) ?_` and prove the remaining obligations. Use extensionality with `⟨z, hz⟩`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, hyz⟩`. Simplify using `only [Submodule.mem_comap, Submodule.subtype_apply] at hy ⊢`. Establish `: (f : W → W) y = z`. Use `congrArg Subtype.val hyz` as an intermediate fact. Simplify using `using this`.

Rewrite using `[← this]`. Conclude with `Submodule.mem_map_of_mem hy`. Introduce `h`. Simplify using `only [Submodule.mem_comap, Submodule.subtype_apply] at h`. Rewrite `h` using `[Submodule.mem_map_equiv]`.

Rewrite `hz` using `[Submodule.mem_map_equiv]`. Use `⟨⟨f.symm z, hz⟩, h, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem imageLcv_len_map (f : W ≃ₗ[R] W) (X Y : Submodule R W) :
    Module.length R (↥(X.map (f : W →ₗ[R] W)) ⧸
        (Y.map (f : W →ₗ[R] W)).comap (X.map (f : W →ₗ[R] W)).subtype) =
      Module.length R (↥X ⧸ Y.comap X.subtype) := by
  symm
  apply LinearEquiv.length_eq
  refine Submodule.Quotient.equiv _ _ (f.submoduleMap X) ?_
  ext ⟨z, hz⟩
  constructor
  · rintro ⟨y, hy, hyz⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hy ⊢
    have : (f : W → W) y = z := by
      have := congrArg Subtype.val hyz
      simpa using this
    rw [← this]
    exact Submodule.mem_map_of_mem hy
  · intro h
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at h
    rw [Submodule.mem_map_equiv] at h
    rw [Submodule.mem_map_equiv] at hz
    refine ⟨⟨f.symm z, hz⟩, h, ?_⟩
    apply Subtype.ext
    simp

/- English proof (translation)
Establish `hinf : A.map (f : W →ₗ[R] W) ⊓ B.map (f : W →ₗ[R] W) = (A ⊓ B).map (f : W →ₗ[R] W)` using `(Submodule.map_inf _ f.injective).symm`. Unfold `Formalism.HermitianLatticesTheory.lidx Formalism.HermitianLatticesTheory.locLen`. Rewrite using `[hinf, localization_map', localization_map', localization_map', imageLcv_len_map, imageLcv_len_map]`.
-/
theorem imageLcv_lidx_map (p : Ideal R) [p.IsPrime] (f : W ≃ₗ[R] W) (A B : Submodule R W) :
    Formalism.HermitianLatticesTheory.lidx p (A.map (f : W →ₗ[R] W)) (B.map (f : W →ₗ[R] W)) = Formalism.HermitianLatticesTheory.lidx p A B := by
  have hinf : A.map (f : W →ₗ[R] W) ⊓ B.map (f : W →ₗ[R] W) = (A ⊓ B).map (f : W →ₗ[R] W) :=
    (Submodule.map_inf _ f.injective).symm
  unfold Formalism.HermitianLatticesTheory.lidx Formalism.HermitianLatticesTheory.locLen
  rw [hinf, localization_map', localization_map', localization_map', imageLcv_len_map,
    imageLcv_len_map]

end SlopeTestRemainingChoices

section Add

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Establish `hfin : ∀ X Y : Submodule R V, X.FG → Formalism.HermitianLatticesTheory.locS (nonZeroDivisors R) Y = ⊤ → Module.length R (↥(Formalism.HermitianLatticesTheory.localization₂ p X) ⧸ (Formalism.HermitianLatticesTheory.localization₂ p Y).comap (Formalism.HermitianLatticesTheory.localiz …`. Introduce `X Y hX hY`. Take `⟨d, hd, hdY⟩` from `Formalism.HermitianLatticesTheory.indexBasic_denom (nonZeroDivisors R) X Y hX (by rw [hY]; exact le_top)`. Conclude with `Module.length_ne_top_iff.mpr (Formalism.HermitianLatticesTheory.indexBasic_finLen p X Y hX hd hdY)`. Establish `hAt` using `Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) A (Submodule.IsLattice.span_eq_top (self := hA))`.

Establish `hBt` using `Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) B (Submodule.IsLattice.span_eq_top (self := hB))`. Establish `hCt` using `Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) C (Submodule.IsLattice.span_eq_top (self := hC))`. Establish `hAfg : A.FG` using `Submodule.IsLattice.fg (self := hA)`. Establish `hBfg : B.FG` using `Submodule.IsLattice.fg (self := hB)`. Establish `hCfg : C.FG` using `Submodule.IsLattice.fg (self := hC)`.

Establish `hDt : Formalism.HermitianLatticesTheory.locS (nonZeroDivisors R) (A ⊓ B ⊓ C) = ⊤`. Rewrite using `[Formalism.HermitianLatticesTheory.locBasic_locS_inf, Formalism.HermitianLatticesTheory.locBasic_locS_inf, hAt, hBt, hCt]`. Simplify using the standard rewrite rules. Establish `hAD` using `hfin A _ hAfg hDt`. Establish `hBD` using `hfin B _ hBfg hDt`.

Establish `hCD` using `hfin C _ hCfg hDt`. Rewrite using `[Formalism.HermitianLatticesTheory.indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right hAD hCD, Formalism.HermitianLatticesTheory.indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) (le_trans inf_le_left inf_le_right) hAD hBD …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem idxLcv_lidx_add (p : Ideal R) [p.IsPrime] (A B C : Submodule R V)
    (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) (hC : Submodule.IsLattice K C) :
    Formalism.HermitianLatticesTheory.lidx p A C = Formalism.HermitianLatticesTheory.lidx p A B + Formalism.HermitianLatticesTheory.lidx p B C := by
  have hfin : ∀ X Y : Submodule R V, X.FG → Formalism.HermitianLatticesTheory.locS (nonZeroDivisors R) Y = ⊤ →
      Module.length R (↥(Formalism.HermitianLatticesTheory.localization₂ p X) ⧸
        (Formalism.HermitianLatticesTheory.localization₂ p Y).comap (Formalism.HermitianLatticesTheory.localization₂ p X).subtype) ≠ ⊤ := by
    intro X Y hX hY
    obtain ⟨d, hd, hdY⟩ :=
      Formalism.HermitianLatticesTheory.indexBasic_denom (nonZeroDivisors R) X Y hX (by rw [hY]; exact le_top)
    exact Module.length_ne_top_iff.mpr (Formalism.HermitianLatticesTheory.indexBasic_finLen p X Y hX hd hdY)
  have hAt := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) A
    (Submodule.IsLattice.span_eq_top (self := hA))
  have hBt := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) B
    (Submodule.IsLattice.span_eq_top (self := hB))
  have hCt := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) C
    (Submodule.IsLattice.span_eq_top (self := hC))
  have hAfg : A.FG := Submodule.IsLattice.fg (self := hA)
  have hBfg : B.FG := Submodule.IsLattice.fg (self := hB)
  have hCfg : C.FG := Submodule.IsLattice.fg (self := hC)
  have hDt : Formalism.HermitianLatticesTheory.locS (nonZeroDivisors R) (A ⊓ B ⊓ C) = ⊤ := by
    rw [Formalism.HermitianLatticesTheory.locBasic_locS_inf, Formalism.HermitianLatticesTheory.locBasic_locS_inf, hAt, hBt, hCt]
    simp
  have hAD := hfin A _ hAfg hDt
  have hBD := hfin B _ hBfg hDt
  have hCD := hfin C _ hCfg hDt
  rw [Formalism.HermitianLatticesTheory.indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      inf_le_right hAD hCD,
    Formalism.HermitianLatticesTheory.indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hAD hBD,
    Formalism.HermitianLatticesTheory.indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right)
      inf_le_right hBD hCD]
  ring

end Add

section Main

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Pi.basisFun_apply]`.
-/
theorem imageLcv_std_eq (d : ℕ) :
    (fun i => (Pi.single i 1 : Fin d → K)) = ⇑(Pi.basisFun K (Fin d)) := by
  funext i
  simp [Pi.basisFun_apply]

/- English proof (translation)
Rewrite using `[imageLcv_std_eq]`. Conclude with `(Pi.basisFun K (Fin d)).linearIndependent`.
-/
theorem imageLcv_std_li (d : ℕ) : LinearIndependent K (fun i => (Pi.single i 1 : Fin d → K)) := by
  rw [imageLcv_std_eq]
  exact (Pi.basisFun K (Fin d)).linearIndependent

/- English proof (translation)
Use `⟨Submodule.fg_span (Set.finite_range _), ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_span_of_tower, imageLcv_std_eq]`. Conclude with `(Pi.basisFun K (Fin d)).span_eq`.
-/
theorem imageLcv_std_lat (d : ℕ) :
    Submodule.IsLattice K
      (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K)))) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [Submodule.span_span_of_tower, imageLcv_std_eq]
  exact (Pi.basisFun K (Fin d)).span_eq

/- English proof (translation)
Take `⟨h1, -⟩` from `Formalism.HN.height_gram_determinant K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX d e he`. Take `⟨-, -, hpos⟩` from `Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX (Submodule.span (𝓞 K) (Set.range e)) (Submodule.fg_span (Set.finite_range e))`. Rewrite `hpos` using `[h1]`. Conclude with `(Finset.prod_ne_zero_iff.mp hpos.ne') v (Finset.mem_univ v)`.
-/
theorem imageLcv_gram_ne [IsTotallyComplex K] {d : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (e : Fin d → Fin d → K) (he : LinearIndependent K e) (v : InfinitePlace K) :
    (gram X v e).det.re ≠ 0 := by
  obtain ⟨h1, -⟩ := Formalism.HN.height_gram_determinant K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX d e he
  obtain ⟨-, -, hpos⟩ := Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX
    (Submodule.span (𝓞 K) (Set.range e)) (Submodule.fg_span (Set.finite_range e))
  rw [h1] at hpos
  exact (Finset.prod_ne_zero_iff.mp hpos.ne') v (Finset.mem_univ v)

end Main

/- English proof (translation)
Introduce `K _ _ _ _ d XS XT hXS hXT φ hφ L hL`. Establish `hu : IsUnit φ` using `(Matrix.isUnit_iff_isUnit_det φ).mpr hφ`. Establish `hinj : Function.Injective φ.mulVec` using `Matrix.mulVec_injective_iff_isUnit.mpr hu`. Establish `hsurj : Function.Surjective φ.mulVec` using `Matrix.mulVec_surjective_iff_isUnit.mpr hu`. Set `f : (Fin d → K) ≃ₗ[𝓞 K] (Fin d → K)` to `LinearEquiv.ofBijective ((Matrix.mulVecLin φ).restrictScalars (𝓞 K)) ⟨hinj, hsurj⟩`.

Establish `hfmap : ∀ A : Submodule (𝓞 K) (Fin d → K), matLat φ A = A.map (f : (Fin d → K) →ₗ[𝓞 K] (Fin d → K))`. Introduce `A`. Use extensionality with `x`. Rewrite using `[matLat, Submodule.mem_map, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`. Establish `hE` using `imageLcv_std_li (K := K) d`.

Establish `hF : LinearIndependent K (fun i => φ.mulVec (Pi.single i 1 : Fin d → K))` using `hE.map' (Matrix.mulVecLin φ) (LinearMap.ker_eq_bot.mpr hinj)`. Establish `hspan : Submodule.span (𝓞 K) (Set.range (fun i => φ.mulVec (Pi.single i 1 : Fin d → K))) = matLat φ (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K))))`. Rewrite using `[matLat, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hLat : Submodule.IsLattice K (matLat φ L)`.

Use `⟨(Submodule.IsLattice.fg (self := hL)).map _, ?_⟩` and prove the remaining obligations. Establish `: ((matLat φ L : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K)) = (Matrix.mulVecLin φ) '' (L : Set (Fin d → K))`. Rewrite using `[matLat, Submodule.map_coe]`. Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, Submodule.IsLattice.span_eq_top (self := hL), Submodule.map_top, LinearMap.range_eq_top]`.

Conclude with `hsurj`. Take `⟨-, h1⟩` from `h K d XT hXT (matLat φ L) hLat _ hF`. Take `⟨-, h2⟩` from `h K d XS hXS L hL _ hE`. Establish `hidx : ∀ w : HeightOneSpectrum (𝓞 K), idx w (Submodule.span (𝓞 K) (Set.range (fun i => φ.mulVec (Pi.single i 1 : Fin d → K)))) (matLat φ L) = idx w (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K)))) L`. Introduce `w`.

Rewrite using `[hspan, hfmap, hfmap]`. Conclude with `imageLcv_lidx_map _ f _ _`. Simplify using `only [hidx] at h1`. Rewrite using `[h1, h2]`. Establish `hdet : ∀ v, Real.log (detRatio XS XT φ v) = Real.log (gram XT v (fun i => φ.mulVec (Pi.single i 1 : Fin d → K))).det.re - Real.log (gram XS v (fun i => (Pi.single i 1 : Fin d → K))).det.re`.

Introduce `v`. Unfold `detRatio`. Conclude with `Real.log_div (imageLcv_gram_ne XT hXT _ hF v) (imageLcv_gram_ne XS hXS _ hE v)`. Simplify using `only [hdet, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem imageLcv_of (h : LcvBasis) : ImageLcv := by
  intro K _ _ _ _ d XS XT hXS hXT φ hφ L hL
  classical
  have hu : IsUnit φ := (Matrix.isUnit_iff_isUnit_det φ).mpr hφ
  have hinj : Function.Injective φ.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hu
  have hsurj : Function.Surjective φ.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  let f : (Fin d → K) ≃ₗ[𝓞 K] (Fin d → K) :=
    LinearEquiv.ofBijective ((Matrix.mulVecLin φ).restrictScalars (𝓞 K)) ⟨hinj, hsurj⟩
  have hfmap : ∀ A : Submodule (𝓞 K) (Fin d → K),
      matLat φ A = A.map (f : (Fin d → K) →ₗ[𝓞 K] (Fin d → K)) := by
    intro A
    ext x
    rw [matLat, Submodule.mem_map, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hE := imageLcv_std_li (K := K) d
  have hF : LinearIndependent K (fun i => φ.mulVec (Pi.single i 1 : Fin d → K)) :=
    hE.map' (Matrix.mulVecLin φ) (LinearMap.ker_eq_bot.mpr hinj)
  have hspan : Submodule.span (𝓞 K) (Set.range (fun i => φ.mulVec (Pi.single i 1 : Fin d → K))) =
      matLat φ (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K)))) := by
    rw [matLat, Submodule.map_span, ← Set.range_comp]
    rfl
  have hLat : Submodule.IsLattice K (matLat φ L) := by
    refine ⟨(Submodule.IsLattice.fg (self := hL)).map _, ?_⟩
    have : ((matLat φ L : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K)) =
        (Matrix.mulVecLin φ) '' (L : Set (Fin d → K)) := by
      rw [matLat, Submodule.map_coe]
      rfl
    rw [this, Submodule.span_image, Submodule.IsLattice.span_eq_top (self := hL), Submodule.map_top,
      LinearMap.range_eq_top]
    exact hsurj
  obtain ⟨-, h1⟩ := h K d XT hXT (matLat φ L) hLat _ hF
  obtain ⟨-, h2⟩ := h K d XS hXS L hL _ hE
  have hidx : ∀ w : HeightOneSpectrum (𝓞 K),
      idx w (Submodule.span (𝓞 K) (Set.range (fun i => φ.mulVec (Pi.single i 1 : Fin d → K))))
        (matLat φ L) =
      idx w (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K)))) L := by
    intro w
    rw [hspan, hfmap, hfmap]
    exact imageLcv_lidx_map _ f _ _
  simp only [hidx] at h1
  rw [h1, h2]
  have hdet : ∀ v, Real.log (detRatio XS XT φ v) =
      Real.log (gram XT v (fun i => φ.mulVec (Pi.single i 1 : Fin d → K))).det.re -
        Real.log (gram XS v (fun i => (Pi.single i 1 : Fin d → K))).det.re := by
    intro v
    unfold detRatio
    exact Real.log_div (imageLcv_gram_ne XT hXT _ hF v) (imageLcv_gram_ne XS hXS _ hE v)
  simp only [hdet, Finset.sum_sub_distrib]
  ring

/- English proof (translation)
Introduce `K _ _ _ _ d X hX A B hA hB`. Establish `hE` using `imageLcv_std_li (K := K) d`. Establish `hS` using `imageLcv_std_lat (K := K) d`. Take `⟨sA, eA⟩` from `h K d X hX A hA _ hE`. Take `⟨sB, eB⟩` from `h K d X hX B hB _ hE`.

Use `set S := Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K))) with hSdef`. Establish `hadd : ∀ w : HeightOneSpectrum (𝓞 K), idx w S B = idx w S A + idx w A B` using `fun w => idxLcv_lidx_add (K := K) w.asIdeal S A B hS hA hB`. Establish `hfun : (fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w A B : ℝ)) = (fun w => lw w * (idx w S B : ℝ)) - (fun w => lw w * (idx w S A : ℝ))`. Use function extensionality and compare the values at `w`. Simplify using `only [Pi.sub_apply, hadd w]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsupp : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w A B : ℝ)).Finite`. Rewrite using `[hfun]`. Conclude with `(sB.union sA).subset (Function.support_sub _ _)`.

Use `⟨hsupp, ?_⟩` and prove the remaining obligations. Establish `hsplit : (fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w S B : ℝ)) = fun w => lw w * (idx w S A : ℝ) + lw w * (idx w A B : ℝ)`. Use function extensionality and compare the values at `w`. Rewrite using `[hadd w]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eB, eA, hsplit, finsum_add_distrib sA hsupp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem idxLcv_of (h : LcvBasis) : IdxLcv := by
  intro K _ _ _ _ d X hX A B hA hB
  classical
  have hE := imageLcv_std_li (K := K) d
  have hS := imageLcv_std_lat (K := K) d
  obtain ⟨sA, eA⟩ := h K d X hX A hA _ hE
  obtain ⟨sB, eB⟩ := h K d X hX B hB _ hE
  set S := Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K))) with hSdef
  have hadd : ∀ w : HeightOneSpectrum (𝓞 K), idx w S B = idx w S A + idx w A B := fun w =>
    idxLcv_lidx_add (K := K) w.asIdeal S A B hS hA hB
  have hfun : (fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w A B : ℝ)) =
      (fun w => lw w * (idx w S B : ℝ)) - (fun w => lw w * (idx w S A : ℝ)) := by
    funext w
    simp only [Pi.sub_apply, hadd w]
    push_cast
    ring
  have hsupp : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w A B : ℝ)).Finite := by
    rw [hfun]
    exact (sB.union sA).subset (Function.support_sub _ _)
  refine ⟨hsupp, ?_⟩
  have hsplit : (fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w S B : ℝ)) =
      fun w => lw w * (idx w S A : ℝ) + lw w * (idx w A B : ℝ) := by
    funext w
    rw [hadd w]
    push_cast
    ring
  rw [eB, eA, hsplit, finsum_add_distrib sA hsupp]
  ring

end Formalism.DivisionValues

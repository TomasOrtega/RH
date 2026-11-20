import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

/- English proof (translation)
Introduce `H R _ I h R₀ _ π hπ hI S _ σ hσ J hJ S₀ _ πS hπS hJk ι₀ hι g A₀ _ A _ i hA AS₀ _ AS _ iS hAS hAab hAg hASab hASg φA ψA hφA hψA hiA g' B₀ _ B _ j hB BS₀ _ BS _ jS hBS hBab hBg hBSab hBSg φB ψB hφB hψB hjB f₀ _ fS₀ _ hf hyp d hd`. Take `⟨_, _, HBC, HR, _⟩` from `H`. Use `letI : Algebra S R := σ.toAlgebra`. Establish `hJI : ∀ a ∈ J, σ a ∈ I` using `fun a ha ↦ by`. Rewrite using `[← hI, RingHom.mem_ker]`.

Establish `: πS a = 0` using `by rw [← RingHom.mem_ker, hJk]; exact ha`. Rewrite using `[← RingHom.comp_apply, ← hι, RingHom.comp_apply, this, map_zero]`. Establish `hdp : IsDPMorphism (divided₂ hJ) (divided₂ h) σ` using `isDPMorphism_sqDP hJ h σ hJI`. Establish `hbase : spMap ι₀ ≫ spMap πS = spMap π ≫ spMap σ`. Rewrite using `[← Cris.spMap_comp, ← Cris.spMap_comp, hι]`.

Establish `mA` using `GrpMor.of_isGrpPullback hdp hbase hψA`. Establish `mB` using `GrpMor.of_isGrpPullback hdp hbase hψB`. Establish `nA` using `GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφA`. Establish `nB` using `GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφB`. Establish `hBCA` using `HBC S AS g hASab hASg R A φA hφA`.

Take `⟨y, hy⟩` from `hBCA.1.exists (crysToDR (divided₂ hJ) hAS d)`. Take `⟨d', rfl⟩` from `(GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective HR hAab hAg (isDPNilpotent_squareZero h) hπ hI hA).2 y`. Establish `hsurj` using `(HR S AS g hASab hASg J (divided₂ hJ) (isDPNilpotent_squareZero hJ) S₀ πS hπS hJk AS₀ iS hAS).2`. Establish `hm : mA.Corr d d'` using `fun c ↦ by`. Take `⟨c0, rfl⟩` from `hsurj c`.

Establish `k` using `(liftMor (divided₂ hJ) hAS).comp mA`. Rewrite using `[GrpMor.pull_pull (liftMor (divided₂ hJ) hAS) mA k (fun _ ↦ rfl) rfl c0, ← GrpMor.pull_pull nA (liftMor (divided₂ h) hA) k (fun _ ↦ rfl) hiA c0]`. Conclude with `(crysToDR_apply _ hA d' _).symm.trans ((hy c0).trans (congrArg σ (crysToDR_apply _ hAS d c0)))`. Establish `hd' : d' ∈ liftFil (divided₂ h) hA`. Establish `hle : PrimitiveSubmodule A ≤ LinearMap.ker (crysToDR (divided₂ h) hA d')`.

Rewrite using `[hBCA.2, Submodule.span_le]`. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, hy c]`. Rewrite `hd` using `[liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator]`. Rewrite using `[hd c hc, map_zero]`.

Conclude with `(Submodule.mem_dualAnnihilator _).2 fun c hc ↦ hle hc`. Establish `hpush` using `hyp d' hd'`. Establish `hcorr` using `GrpMor.Corr.push (m := mA) mB fS₀ f₀ hf.symm hm`. Establish `hx` using `crysToDR_corr (divided₂ hJ) hBS hB mB nB hjB hcorr`. Rewrite using `[liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator]`.

Rewrite `hpush` using `[liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator]`. Introduce `c hc`. Apply `hσ` to reduce the goal to its premises. Use `show σ _ = σ 0`. Rewrite using `[map_zero]`.

Conclude with `(hx c).symm.trans (hpush _ (nB.isMor.pullback1_mem_hodgeFiltration hc))`.
-/
theorem push_mem_liftFil_of_injective : AbelianDeRham →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (S : Type) [CommRing S] (σ : S →+* R), Function.Injective σ →
  ∀ (J : Ideal S) (hJ : J ^ 2 = 0) (S₀ : Type) [CommRing S₀] (πS : S →+* S₀),
    Function.Surjective πS → RingHom.ker πS = J →
  ∀ (ι₀ : S₀ →+* R₀), ι₀.comp πS = π.comp σ →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i)
    (AS₀ : Over (Sp S₀)) [GrpObj AS₀] (AS : Over (Sp S)) [GrpObj AS] (iS : AS₀.left ⟶ AS.left)
    (hAS : IsGrpPullback AS₀ AS (spMap πS) iS), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    IsAbelianScheme AS → SmoothOfRelativeDimension g AS.hom →
  ∀ (φA : A.left ⟶ AS.left) (ψA : A₀.left ⟶ AS₀.left), IsGrpPullback A AS (spMap σ) φA →
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA → i ≫ φA = ψA ≫ iS →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j)
    (BS₀ : Over (Sp S₀)) [GrpObj BS₀] (BS : Over (Sp S)) [GrpObj BS] (jS : BS₀.left ⟶ BS.left)
    (hBS : IsGrpPullback BS₀ BS (spMap πS) jS), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
    IsAbelianScheme BS → SmoothOfRelativeDimension g' BS.hom →
  ∀ (φB : B.left ⟶ BS.left) (ψB : B₀.left ⟶ BS₀.left), IsGrpPullback B BS (spMap σ) φB →
    IsGrpPullback B₀ BS₀ (spMap ι₀) ψB → j ≫ φB = ψB ≫ jS →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (fS₀ : AS₀ ⟶ BS₀) [IsMonHom fS₀], f₀.left ≫ ψB = ψA ≫ fS₀.left →
    (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∀ d ∈ liftFil (divided₂ hJ) hAS, push (divided₂ hJ) (spMap πS) fS₀ d ∈ liftFil (divided₂ hJ) hBS := by
  intro H R _ I h R₀ _ π hπ hI S _ σ hσ J hJ S₀ _ πS hπS hJk ι₀ hι g A₀ _ A _ i hA AS₀ _ AS _ iS hAS hAab hAg
    hASab hASg φA ψA hφA hψA hiA g' B₀ _ B _ j hB BS₀ _ BS _ jS hBS hBab hBg hBSab hBSg φB ψB hφB hψB hjB
    f₀ _ fS₀ _ hf hyp d hd
  obtain ⟨_, _, HBC, HR, _⟩ := H
  letI : Algebra S R := σ.toAlgebra
  have hJI : ∀ a ∈ J, σ a ∈ I := fun a ha ↦ by
    rw [← hI, RingHom.mem_ker]
    have : πS a = 0 := by rw [← RingHom.mem_ker, hJk]; exact ha
    rw [← RingHom.comp_apply, ← hι, RingHom.comp_apply, this, map_zero]
  have hdp : IsDPMorphism (divided₂ hJ) (divided₂ h) σ := isDPMorphism_sqDP hJ h σ hJI
  have hbase : spMap ι₀ ≫ spMap πS = spMap π ≫ spMap σ := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp, hι]
  have mA := GrpMor.of_isGrpPullback hdp hbase hψA
  have mB := GrpMor.of_isGrpPullback hdp hbase hψB
  have nA := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφA
  have nB := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφB
  have hBCA := HBC S AS g hASab hASg R A φA hφA
  obtain ⟨y, hy⟩ := hBCA.1.exists (crysToDR (divided₂ hJ) hAS d)
  obtain ⟨d', rfl⟩ :=
    (GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective HR hAab hAg (isDPNilpotent_squareZero h) hπ hI hA).2 y
  have hsurj := (HR S AS g hASab hASg J (divided₂ hJ) (isDPNilpotent_squareZero hJ) S₀ πS hπS hJk AS₀ iS hAS).2
  have hm : mA.Corr d d' := fun c ↦ by
    obtain ⟨c0, rfl⟩ := hsurj c
    have k := (liftMor (divided₂ hJ) hAS).comp mA
    rw [GrpMor.pull_pull (liftMor (divided₂ hJ) hAS) mA k (fun _ ↦ rfl) rfl c0,
      ← GrpMor.pull_pull nA (liftMor (divided₂ h) hA) k (fun _ ↦ rfl) hiA c0]
    exact (crysToDR_apply _ hA d' _).symm.trans ((hy c0).trans (congrArg σ (crysToDR_apply _ hAS d c0)))
  have hd' : d' ∈ liftFil (divided₂ h) hA := by
    have hle : PrimitiveSubmodule A ≤ LinearMap.ker (crysToDR (divided₂ h) hA d') := by
      rw [hBCA.2, Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hy c]
      rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hd
      rw [hd c hc, map_zero]
    exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ hle hc
  have hpush := hyp d' hd'
  have hcorr := GrpMor.Corr.push (m := mA) mB fS₀ f₀ hf.symm hm
  have hx := crysToDR_corr (divided₂ hJ) hBS hB mB nB hjB hcorr
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator]
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hpush
  intro c hc
  apply hσ
  show σ _ = σ 0
  rw [map_zero]
  exact (hx c).symm.trans (hpush _ (nB.isMor.pullback1_mem_hodgeFiltration hc))

end GlobalTheory.SqLift

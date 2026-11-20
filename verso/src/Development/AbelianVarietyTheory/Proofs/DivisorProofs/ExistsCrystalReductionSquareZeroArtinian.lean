import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open GlobalTheory.ZM GlobalTheory.SiegelTor
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open IsLocalRing
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

namespace GlobalTheory.CrysRed

open GlobalTheory.Published.GrothendieckMessing in

/- English proof (translation)
Introduce `C C₀ _ _ _ _ π hπ hsq A₀ _ _ hA₀ O _ a`. Establish `hI2 : RingHom.ker π ^ 2 = ⊥` using `hsq`. Use `haveI : Nontrivial C₀ := by`. Use `⟨⟨0, 1, fun h ↦ ?_⟩⟩` and prove the remaining obligations. Establish `h1 : (1 : C) ∈ RingHom.ker π` using `by rw [RingHom.mem_ker, map_one]; exact h.symm`.

Establish `h2 : (1 : C) ∈ RingHom.ker π ^ 2`. Rewrite using `[pow_two]`. Simplify using `using Ideal.mul_mem_mul h1 h1`. Rewrite `h2` using `[hI2]`. Conclude with `one_ne_zero ((Submodule.mem_bot C).1 h2)`.

Use `haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ`. Set `κ` to `divided₂ hsq`. Establish `hκ : IsNilDP κ` using `isDPNilpotent_squareZero hsq`. Establish `ADR : GlobalTheory.Published.AbelianDeRham` using `GlobalTheory.abelianDeRham`. Establish `GD : GlobalTheory.Published.GrothendieckDeformation` using `GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers`.

Take `⟨A', _, i', h', hA'⟩` from `GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl A₀ hA₀`. Take `⟨g, hg⟩` from `GlobalTheory.AbelianDim.exists_relDim C A' hA'`. Establish `HC` using `(GD C (RingHom.ker π) κ hκ C₀ π hπ rfl).1`. Take `⟨bij, ⟨N0, hN0⟩, hAdm⟩` from `HC g A₀ A' i' h' hA' hg`. Set `e` to `LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)`.

Establish `ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA` using `e.apply_symm_apply`. Use `letI : Algebra C C₀ := π.toAlgebra`. Establish `hBC` using `(ADR.2.2.1 C A' g hA' hg C₀ A₀ i' h').1`. Take `⟨hfinA, hprojA, -⟩` from `ADR.1.prim hA' hg`. Use `haveI := hfinA`.

Use `haveI := hprojA`. Establish `hfin : Module.Finite C (Crys κ (spMap π) A₀)` using `Module.Finite.equiv e.symm`. Establish `hproj : Module.Projective C (Crys κ (spMap π) A₀)` using `Module.Projective.of_equiv e.symm`. Set `red : Crys κ (spMap π) A₀ →ₛₗ[π] HdR A₀` to `hBC.bcMap.comp (crysToDR κ h')`. Establish `hm : ∀ x, (crysRedMor κ rfl A₀).Corr x (red x)` using `fun x ↦ (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)`.

Establish `hcorr : ∀ d y, (crysRedMor κ rfl A₀).Corr d y ↔ red d = y` using `fun d y ↦ ⟨fun H ↦ by exact hBC.corr_iff.1 ((corr_crysToDR_iff rfl h' bij.2 d y).2 H), fun H ↦ H ▸ hm d⟩`. Establish `hred : Function.Surjective red`. Introduce `y`. Set `l : primDR A' →ₗ[C] C₀` to `{ toFun c := y ((redMor h').pull c) map_add' := by simp map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }`. Take `⟨xA, hx⟩` from `Module.projective_lifting_property (Algebra.linearMap C C₀) l hπ`.

Use `⟨e.symm xA, ?_⟩` and prove the remaining obligations. Use `show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y`. Rewrite using `[ee]`. Conclude with `hBC.corr_iff.1 fun c ↦ (LinearMap.congr_fun hx c).symm`. Establish `hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule C (Crys κ (spMap π) A₀))`.

Introduce `x hx`. Establish `hc` using `hBC.corr_iff.2 hx`. Establish `hmem` using `GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (crysToDR κ h' x) fun c ↦ RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))`. Use `Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hmem` as an intermediate fact. Rewrite `this` using `[Submodule.map_smul'']`.

Establish `ex : e.symm.toLinearMap (crysToDR κ h' x) = x` using `e.symm_apply_apply x`. Rewrite `this` using `[ex]`. Conclude with `Submodule.smul_mono le_rfl le_top this`. Establish `hact : ∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct κ (spMap π) a c d) = GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d)`. Introduce `c d`.

Use `haveI := a.hom c`. Use `(hcorr _ _).1 ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.HTSummand.crysAct_apply, GlobalTheory.HTSummand.crysAct_apply]`. Conclude with `GrpMor.Corr.push (m := crysRedMor κ rfl A₀) (crysRedMor κ rfl A₀) (a.act c) (a.act c) (by simp) (hm d)`. Establish `hFN : IsCompl (liftFil κ h') (N0.comap (crysToDR κ h'))` using `(Submodule.orderIsoMapComap e).symm.isCompl hN0`.

Use `⟨red, hfin, hproj, hred, hker, hcorr, hact, liftFil κ h', N0.comap (crysToDR κ h'), hFN, fun y ↦ ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `hy`. Take `⟨xA, hxA, hc⟩` from `(hAdm y).1 hy`. Use `⟨e.symm xA, ?_, ?_⟩` and prove the remaining obligations. Use `show crysToDR κ h' (e.symm xA) ∈ Fil A'`.

Rewrite using `[ee]`. Conclude with `hxA`. Use `show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y`. Rewrite using `[ee]`. Conclude with `hBC.corr_iff.1 hc`.

Introduce and unpack `⟨d, hd, rfl⟩`. Conclude with `(hAdm (red d)).2 ⟨crysToDR κ h' d, hd, by exact hBC.corr_iff.2 rfl⟩`.
-/
theorem exists_crysRed : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] (a : GlobalTheory.UPel.HT.OActN O A₀), ∃ red : Crys (divided₂ hsq) (spMap π) A₀ →ₛₗ[π] HdR A₀, Module.Finite C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Module.Projective C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Function.Surjective red ∧ (∀ x, red x = 0 → x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀))) ∧ (∀ d y, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl A₀).Corr d y ↔ red d = y) ∧ (∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a c d) = GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d)) ∧ ∃ E' M : Submodule C (Crys (divided₂ hsq) (spMap π) A₀), IsCompl E' M ∧ ∀ y, y ∈ Fil A₀ ↔ ∃ d ∈ E', red d = y := by
  intro C C₀ _ _ _ _ π hπ hsq A₀ _ _ hA₀ O _ a
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hI2] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  let κ := divided₂ hsq
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have GD : GlobalTheory.Published.GrothendieckDeformation :=
    GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl A₀ hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A' hA'
  have HC := (GD C (RingHom.ker π) κ hκ C₀ π hπ rfl).1
  obtain ⟨bij, ⟨N0, hN0⟩, hAdm⟩ := HC g A₀ A' i' h' hA' hg
  let e := LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)
  have ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA := e.apply_symm_apply
  letI : Algebra C C₀ := π.toAlgebra
  have hBC := (ADR.2.2.1 C A' g hA' hg C₀ A₀ i' h').1
  obtain ⟨hfinA, hprojA, -⟩ := ADR.1.prim hA' hg
  haveI := hfinA
  haveI := hprojA
  have hfin : Module.Finite C (Crys κ (spMap π) A₀) := Module.Finite.equiv e.symm
  have hproj : Module.Projective C (Crys κ (spMap π) A₀) := Module.Projective.of_equiv e.symm
  let red : Crys κ (spMap π) A₀ →ₛₗ[π] HdR A₀ := hBC.bcMap.comp (crysToDR κ h')
  have hm : ∀ x, (crysRedMor κ rfl A₀).Corr x (red x) := fun x ↦
    (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)
  have hcorr : ∀ d y, (crysRedMor κ rfl A₀).Corr d y ↔ red d = y := fun d y ↦
    ⟨fun H ↦ by exact hBC.corr_iff.1 ((corr_crysToDR_iff rfl h' bij.2 d y).2 H), fun H ↦ H ▸ hm d⟩
  have hred : Function.Surjective red := by
    intro y
    let l : primDR A' →ₗ[C] C₀ :=
      { toFun c := y ((redMor h').pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨xA, hx⟩ := Module.projective_lifting_property (Algebra.linearMap C C₀) l hπ
    refine ⟨e.symm xA, ?_⟩
    show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
    rw [ee]
    exact hBC.corr_iff.1 fun c ↦ (LinearMap.congr_fun hx c).symm
  have hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule C (Crys κ (spMap π) A₀)) := by
    intro x hx
    have hc := hBC.corr_iff.2 hx
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (crysToDR κ h' x) fun c ↦
      RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))
    have := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hmem
    rw [Submodule.map_smul''] at this
    have ex : e.symm.toLinearMap (crysToDR κ h' x) = x := e.symm_apply_apply x
    rw [ex] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hact : ∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct κ (spMap π) a c d) =
      GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d) := by
    intro c d
    haveI := a.hom c
    refine (hcorr _ _).1 ?_
    rw [GlobalTheory.HTSummand.crysAct_apply, GlobalTheory.HTSummand.crysAct_apply]
    exact GrpMor.Corr.push (m := crysRedMor κ rfl A₀) (crysRedMor κ rfl A₀) (a.act c) (a.act c) (by simp) (hm d)
  have hFN : IsCompl (liftFil κ h') (N0.comap (crysToDR κ h')) :=
    (Submodule.orderIsoMapComap e).symm.isCompl hN0
  refine ⟨red, hfin, hproj, hred, hker, hcorr, hact, liftFil κ h', N0.comap (crysToDR κ h'), hFN, fun y ↦ ⟨?_, ?_⟩⟩
  · intro hy
    obtain ⟨xA, hxA, hc⟩ := (hAdm y).1 hy
    refine ⟨e.symm xA, ?_, ?_⟩
    · show crysToDR κ h' (e.symm xA) ∈ Fil A'
      rw [ee]; exact hxA
    · show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
      rw [ee]; exact hBC.corr_iff.1 hc
  · rintro ⟨d, hd, rfl⟩
    exact (hAdm (red d)).2 ⟨crysToDR κ h' d, hd, by exact hBC.corr_iff.2 rfl⟩

end GlobalTheory.CrysRed

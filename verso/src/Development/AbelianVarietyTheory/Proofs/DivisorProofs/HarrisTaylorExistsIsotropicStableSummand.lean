import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystalReductionSquareZeroArtinian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrysForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalProjectiveOverTensorRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilLagrangianOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianLiftLieSquareZeroHarrisTaylorStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

/- English proof (translation)
Introduce `p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀`. Take `⟨red, hfin, hproj, hsurj, hker, hcorr, hpush, E', M', hE'M', hE'⟩` from `GlobalTheory.CrysRed.exists_crysRed C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act`. Use `haveI := hfin`. Use `haveI := hproj`. Take `⟨φ₀, hφ₀, huniq, hadj, φ', hφ', hrel⟩` from `GlobalTheory.HTDefLift.exists_crysForm p D R b N C C₀ π hπ hsq tR o₀`.

Take `⟨hskew, hbij⟩` from `GlobalTheory.HTPerf.skew_bijective p D R b N C C₀ π hπ hsq tR o₀ φ₀ hφ₀`. Use `haveI : Nontrivial C₀ := by`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Establish `ht : RingHom.ker π = ⊤` using `eq_top_iff.2 fun x _ ↦ RingHom.mem_ker.2 (Subsingleton.elim _ _)`.

Rewrite `hsq` using `[ht, ← Ideal.one_eq_top, one_pow]`. Conclude with `one_ne_zero hsq`. Use `haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ`. Establish `hlagr` using `GlobalTheory.HTLagr.fil_lagrangian p D R b N C₀ _ o₀ φ' (GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A o₀.ab) hφ'`. Establish `hlie` using `GlobalTheory.HTSummand.lie_mod_fil p D R b N C₀ (π.comp tR) _ (GlobalTheory.Cris.spMap_comp tR π).symm o₀`.

Establish `hprojF` using `GlobalTheory.T.crystal_projective_over_tensor_ringOfIntegers D.F C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act`. Establish `hI2 : RingHom.ker π ^ 2 = ⊥` using `hsq`. Set `F : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)` to `(Fil o₀.A).comap red`. Establish `hredI : ∀ x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), red x = 0`. Introduce `x hx`.

Use `Submodule.smul_induction_on hx (fun r hr n _ ↦ ?_) (fun x y hx hy ↦ ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, RingHom.mem_ker.1 hr, zero_smul]`. Rewrite using `[map_add, hx, hy, add_zero]`. Establish `hIF : RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) ≤ F` using `fun x hx ↦ by show red x ∈ Fil o₀.A`. Rewrite using `[hredI x hx]`.

Conclude with `zero_mem _`. Establish `hFstab : ∀ (c : D.O), ∀ x ∈ F, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act c x ∈ F`. Introduce `c x hx`. Use `show red _ ∈ Fil o₀.A`. Rewrite using `[hpush]`.

Use `haveI := o₀.act.hom c`. Conclude with `push_mem_Fil (o₀.act.act c) hx`. Establish `hFiso : ∀ x ∈ F, ∀ y ∈ F, φ₀ x y ∈ RingHom.ker π`. Introduce `x hx y hy`. Rewrite using `[RingHom.mem_ker, ← hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]`.

Conclude with `hlagr.1 _ hx _ hy`. Establish `hFlagr : ∀ x, (∀ y ∈ F, φ₀ x y ∈ RingHom.ker π) → x ∈ F`. Introduce `x hx`. Use `show red x ∈ Fil o₀.A`. Use `hlagr.2 _ fun z hz ↦ ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `hsurj z`. Rewrite using `[hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]`. Conclude with `RingHom.mem_ker.1 (hx y hz)`. Establish `hE'F : E' ⊔ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) = F`. Use `le_antisymm (sup_le (fun d hd ↦ (hE' _).2 ⟨d, hd, rfl⟩) hIF) fun x hx ↦ ?_` and prove the remaining obligations.

Take `⟨d, hd, he⟩` from `(hE' (red x)).1 hx`. Establish `hx' : x = d + (x - d)` using `by abel`. Rewrite using `[hx']`. Conclude with `Submodule.add_mem_sup hd (hker _ (by rw [map_sub, he, sub_self]))`. Establish `hFlie : ∀ d, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D …`.

Introduce `d hd`. Establish `hd' : red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d) ∈ Fil o₀.A` using `hd`. Rewrite `hd'` using `[map_sub, LinearMap.map_smulₛₗ, hpush]`. Take `⟨w₀, hw₀, hsum⟩` from `hlie (red d) hd'`. Use `choose w hw using fun i ↦ hsurj (w₀ i)`.

Use `⟨w, fun i c ↦ ?_, ?_⟩` and prove the remaining obligations. Use `show red _ ∈ Fil o₀.A`. Rewrite using `[map_sub, LinearMap.map_smulₛₗ, hpush, hw]`. Conclude with `hw₀ i c`. Use `show red _ ∈ Fil o₀.A`.

Rewrite using `[map_sub, map_sum]`. Simplify using `only [hw]`. Conclude with `hsum`. Take `⟨E, ⟨M, hEM⟩, hEF, hstab, hiso, hlieE⟩` from `GlobalTheory.T.exists_lagrangian_lift_lie_squareZero_harrisTaylor p D R b C (RingHom.ker π) hI2 tR (Crys (divided₂ hsq) (spMap π) o₀.A) (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act) hprojF φ₀ hskew hbij hadj F hIF hFstab hFiso hFlagr ⟨E', M', hE'M', hE'F⟩ hFlie`. Use `⟨E, ⟨M, hEM⟩, fun y ↦ ⟨fun hy ↦ ?_, fun ⟨d, hd, hc⟩ ↦ ?_⟩, fun c d hd ↦ hstab c d hd, fun φ hφ x hx y hy ↦ by rw [huniq φ hφ]; exact hiso x hx y hy, fun d hd ↦ hlieE d hd⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `hsurj y`. Establish `hx : x ∈ F` using `hy`. Rewrite `hx` using `[← hEF]`. Take `⟨d, hd, j, hj, rfl⟩` from `Submodule.mem_sup.1 hx`. Conclude with `⟨d, hd, (hcorr _ _).2 (by rw [map_add, hredI j hj, add_zero])⟩`.

Rewrite using `[← (hcorr d y).1 hc]`. Establish `: d ∈ F` using `hEF ▸ Submodule.mem_sup_left hd`. Conclude with `this`.
-/
theorem exists_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) ∧ (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀
  obtain ⟨red, hfin, hproj, hsurj, hker, hcorr, hpush, E', M', hE'M', hE'⟩ :=
    GlobalTheory.CrysRed.exists_crysRed C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act
  haveI := hfin
  haveI := hproj
  obtain ⟨φ₀, hφ₀, huniq, hadj, φ', hφ', hrel⟩ := GlobalTheory.HTDefLift.exists_crysForm p D R b N C C₀ π hπ hsq tR o₀
  obtain ⟨hskew, hbij⟩ := GlobalTheory.HTPerf.skew_bijective p D R b N C C₀ π hπ hsq tR o₀ φ₀ hφ₀
  haveI : Nontrivial C₀ := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have ht : RingHom.ker π = ⊤ := eq_top_iff.2 fun x _ ↦ RingHom.mem_ker.2 (Subsingleton.elim _ _)
    rw [ht, ← Ideal.one_eq_top, one_pow] at hsq
    exact one_ne_zero hsq
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  have hlagr := GlobalTheory.HTLagr.fil_lagrangian p D R b N C₀ _ o₀ φ' (GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A o₀.ab) hφ'
  have hlie := GlobalTheory.HTSummand.lie_mod_fil p D R b N C₀ (π.comp tR) _ (GlobalTheory.Cris.spMap_comp tR π).symm o₀
  have hprojF := GlobalTheory.T.crystal_projective_over_tensor_ringOfIntegers D.F C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  let F : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A) := (Fil o₀.A).comap red
  have hredI : ∀ x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), red x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr n _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [LinearMap.map_smulₛₗ, RingHom.mem_ker.1 hr, zero_smul]
    · rw [map_add, hx, hy, add_zero]
  have hIF : RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) ≤ F := fun x hx ↦ by
    show red x ∈ Fil o₀.A
    rw [hredI x hx]; exact zero_mem _
  have hFstab : ∀ (c : D.O), ∀ x ∈ F, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act c x ∈ F := by
    intro c x hx
    show red _ ∈ Fil o₀.A
    rw [hpush]
    haveI := o₀.act.hom c
    exact push_mem_Fil (o₀.act.act c) hx
  have hFiso : ∀ x ∈ F, ∀ y ∈ F, φ₀ x y ∈ RingHom.ker π := by
    intro x hx y hy
    rw [RingHom.mem_ker, ← hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]
    exact hlagr.1 _ hx _ hy
  have hFlagr : ∀ x, (∀ y ∈ F, φ₀ x y ∈ RingHom.ker π) → x ∈ F := by
    intro x hx
    show red x ∈ Fil o₀.A
    refine hlagr.2 _ fun z hz ↦ ?_
    obtain ⟨y, rfl⟩ := hsurj z
    rw [hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]
    exact RingHom.mem_ker.1 (hx y hz)
  have hE'F : E' ⊔ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) = F := by
    refine le_antisymm (sup_le (fun d hd ↦ (hE' _).2 ⟨d, hd, rfl⟩) hIF) fun x hx ↦ ?_
    obtain ⟨d, hd, he⟩ := (hE' (red x)).1 hx
    have hx' : x = d + (x - d) := by abel
    rw [hx']
    exact Submodule.add_mem_sup hd (hker _ (by rw [map_sub, he, sub_self]))
  have hFlie : ∀ d, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F),
        GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧
        d - ∑ i, w i ∈ F := by
    intro d hd
    have hd' : red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d)
        ∈ Fil o₀.A := hd
    rw [map_sub, LinearMap.map_smulₛₗ, hpush] at hd'
    obtain ⟨w₀, hw₀, hsum⟩ := hlie (red d) hd'
    choose w hw using fun i ↦ hsurj (w₀ i)
    refine ⟨w, fun i c ↦ ?_, ?_⟩
    · show red _ ∈ Fil o₀.A
      rw [map_sub, LinearMap.map_smulₛₗ, hpush, hw]
      exact hw₀ i c
    · show red _ ∈ Fil o₀.A
      rw [map_sub, map_sum]
      simp only [hw]
      exact hsum
  obtain ⟨E, ⟨M, hEM⟩, hEF, hstab, hiso, hlieE⟩ := GlobalTheory.T.exists_lagrangian_lift_lie_squareZero_harrisTaylor p D R b C (RingHom.ker π) hI2 tR
    (Crys (divided₂ hsq) (spMap π) o₀.A) (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act) hprojF φ₀ hskew hbij hadj
    F hIF hFstab hFiso hFlagr ⟨E', M', hE'M', hE'F⟩ hFlie
  refine ⟨E, ⟨M, hEM⟩, fun y ↦ ⟨fun hy ↦ ?_, fun ⟨d, hd, hc⟩ ↦ ?_⟩, fun c d hd ↦ hstab c d hd,
    fun φ hφ x hx y hy ↦ by rw [huniq φ hφ]; exact hiso x hx y hy, fun d hd ↦ hlieE d hd⟩
  · obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ F := hy
    rw [← hEF] at hx
    obtain ⟨d, hd, j, hj, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨d, hd, (hcorr _ _).2 (by rw [map_add, hredI j hj, add_zero])⟩
  · rw [← (hcorr d y).1 hc]
    have : d ∈ F := hEF ▸ Submodule.mem_sup_left hd
    exact this

end GlobalTheory.HTSummand

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.VB

/- English proof (translation)
Establish `hex : Function.Exact (φ.app U) ((Limits.cokernel.π φ).app U)` using `QCoh.exact_app_of_exact (S := ShortComplex.mk φ (Limits.cokernel.π φ) (Limits.cokernel.condition φ)) (ShortComplex.exact_cokernel φ) hU`. Establish `hsur` using `QCoh.surjective_app_of_epi (Limits.cokernel.π φ) hU`. Establish `hsm (b : Γ(X, U)) (s : Γ(L, U)) : (Limits.cokernel.π φ).app U (b • s) = b • (Limits.cokernel.π φ).app U s` using `(QCoh.appLinear (Limits.cokernel.π φ) U).map_smul b s`. Rewrite using `[Module.mem_annihilator]`. Prove the components needed by the constructor for the conclusion.

Introduce `H`. Use `(hex _).1 ?_` and prove the remaining obligations. Rewrite using `[hsm]`. Conclude with `H _`. Introduce and unpack `⟨u, hu⟩ m`.

Take `⟨s, rfl⟩` from `hsur m`. Establish `h0 : a • (Limits.cokernel.π φ).app U (l 0) = 0`. Rewrite using `[← hsm]`. Conclude with `(hex _).2 ⟨u, hu⟩`. Establish `hs` using `(hl.basis le_rfl).sum_repr s`.

Rewrite `hs` using `[Fin.sum_univ_one, IsFrame.basis_apply, Twist.resM_self]`. Rewrite using `[← hs, hsm, smul_comm, h0, smul_zero]`.
-/
theorem mem_annihilator_cokernel_iff {X : Scheme.{0}} {E L : X.Modules} (φ : E ⟶ L)
    [SheafOfModules.IsQuasicoherent E] [SheafOfModules.IsQuasicoherent L]
    [QCoh.IsFiniteQC (Limits.cokernel φ)] {U : X.Opens} (hU : IsAffineOpen U)
    {l : Fin 1 → Γ(L, U)} (hl : IsFrame l) (a : Γ(X, U)) :
    a ∈ Module.annihilator Γ(X, U) Γ(Limits.cokernel φ, U) ↔ ∃ u, φ.app U u = a • l 0 := by
  have hex : Function.Exact (φ.app U) ((Limits.cokernel.π φ).app U) :=
    QCoh.exact_app_of_exact (S := ShortComplex.mk φ (Limits.cokernel.π φ)
      (Limits.cokernel.condition φ)) (ShortComplex.exact_cokernel φ) hU
  have hsur := QCoh.surjective_app_of_epi (Limits.cokernel.π φ) hU
  have hsm (b : Γ(X, U)) (s : Γ(L, U)) :
      (Limits.cokernel.π φ).app U (b • s) = b • (Limits.cokernel.π φ).app U s :=
    (QCoh.appLinear (Limits.cokernel.π φ) U).map_smul b s
  rw [Module.mem_annihilator]
  constructor
  · intro H
    refine (hex _).1 ?_
    rw [hsm]
    exact H _
  · rintro ⟨u, hu⟩ m
    obtain ⟨s, rfl⟩ := hsur m
    have h0 : a • (Limits.cokernel.π φ).app U (l 0) = 0 := by
      rw [← hsm]
      exact (hex _).2 ⟨u, hu⟩
    have hs := (hl.basis le_rfl).sum_repr s
    rw [Fin.sum_univ_one, IsFrame.basis_apply, Twist.resM_self] at hs
    rw [← hs, hsm, smul_comm, h0, smul_zero]

/- English proof (translation)
Introduce `X Y _ ρ E L φ r _ hE hL hC y`. Use `haveI := hE.isQuasicoherent`. Use `haveI := hL.isQuasicoherent`. Take `⟨U₀, l₀, hyU₀, hl₀⟩` from `hL (ρ y)`. Take `⟨U, e, hU, hyU, hle, he⟩` from `hE.exists_affine hyU₀`.

Establish `hl` using `hl₀.res hle`. Use `set l : Fin 1 → Γ(L, U) := fun i => resM L hle (l₀ i) with hldef`. Take `⟨U', f, hyU', hf, hI⟩` from `hC y`. Take `⟨h, hhle, hyh⟩` from `U'.2.exists_basicOpen_le (V := ρ ⁻¹ᵁ U) ⟨y, hyU⟩ hyU'`. Set `A : Y.affineOpens` to `Y.affineBasicOpen h`.

Establish `hAU : (A : Y.Opens) ≤ ρ ⁻¹ᵁ U` using `hhle`. Establish `hAU' : A ≤ U'` using `Y.basicOpen_le h`. Establish `hyA : y ∈ (A : Y.Opens)` using `hyh`. Set `g : Γ(Y, A)` to `Y.presheaf.map (homOfLE hAU').op f`. Establish `hI1 : ((QCoh.annihilatorSheaf (Limits.cokernel φ)).comap ρ).ideal A = Ideal.span {g}`.

Rewrite using `[← Scheme.IdealSheafData.map_ideal _ hAU', hI, Ideal.map_span, Set.image_singleton]`. Establish `hI2` using `Principalise.comapIdealAffine (QCoh.annihilatorSheaf (Limits.cokernel φ)) ρ ⟨U, hU⟩ A hAU`. Rewrite `hI2` using `[hI1, QCoh.annihilatorSheaf_ideal]`. Establish `hg : g ≠ 0` using `by haveI : Nonempty (A : Y.Opens) := ⟨⟨y, hyA⟩⟩ haveI : Nonempty (U' : Y.Opens) := ⟨⟨y, hyU'⟩⟩`. Introduce `h0`.

Use `nonZeroDivisors.ne_zero hf ?_` and prove the remaining obligations. Apply `map_injective_of_isIntegral Y (homOfLE (show (A : Y.Opens) ≤ U' from hAU'))` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `h0`. Establish `hres (F : X.Modules) (s : Γ(F, U)) : resM _ hAU (QCoh.pullbackSections ρ F le_rfl s) = QCoh.pullbackSections ρ F hAU s` using `QCoh.res_pullbackSections ρ F le_rfl hAU s`.

Establish `hl' : IsFrame fun i => QCoh.pullbackSections ρ L hAU (l i)`. Simplify `(hl.pullback ρ).res hAU` using `only [hres]`. Establish `he' : IsFrame fun i => QCoh.pullbackSections ρ E hAU (e i)`. Simplify `(he.pullback ρ).res hAU` using `only [hres]`. Use `set l' := QCoh.pullbackSections ρ L hAU (l 0) with hl'def`.

Set `ψ` to `(Scheme.Modules.pullback ρ).map φ`. Establish `key (u : Γ(E, U)) (a : Γ(X, U)) (hu : φ.app U u = a • l 0) : ψ.app A (QCoh.pullbackSections ρ E hAU u) = ρ.appLE U A hAU a • l'`. Rewrite using `[QCoh.pullback_map_app_pullbackSections, hu, QCoh.pullbackSections_smul]`. Set `J : Ideal Γ(Y, A)` to `(LinearMap.range (QCoh.appLinear ψ A)).comap (LinearMap.toSpanSingleton Γ(Y, A) _ l')`. Establish `hgJ : g ∈ J`.

Establish `: Ideal.span {g} ≤ J`. Rewrite using `[hI2, Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Take `⟨u, hu⟩` from `(mem_annihilator_cokernel_iff φ hU hl a).1 ha`. Conclude with `⟨_, key u a hu⟩`.

Conclude with `this (Ideal.subset_span rfl)`. Take `⟨t, ht⟩` from `hgJ`. Establish `hei (i : Fin r) : ∃ c : Γ(Y, A), ψ.app A (QCoh.pullbackSections ρ E hAU (e i)) = c • (g • l')`. Establish `hs` using `(hl.basis le_rfl).sum_repr (φ.app U (e i))`. Rewrite `hs` using `[Fin.sum_univ_one, IsFrame.basis_apply, Twist.resM_self]`.

Establish `hm : ρ.appLE U A hAU ((hl.basis le_rfl).repr (φ.app U (e i)) 0) ∈ Ideal.span {g}`. Rewrite using `[hI2]`. Conclude with `Ideal.mem_map_of_mem _ ((mem_annihilator_cokernel_iff φ hU hl _).2 ⟨_, hs.symm⟩)`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hm`. Conclude with `⟨c, by rw [key _ _ hs.symm, ← hc, mul_smul]⟩`.

Use `choose c hc using hei`. Use `⟨A, _, g, t, hyA, hl', hg, ht, fun W hW s => ?_⟩` and prove the remaining obligations. Use `⟨∑ i, (he'.basis hW).repr s i * resG Y hW (c i), ?_⟩` and prove the remaining obligations. Establish `hs` using `(he'.basis hW).sum_repr s`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hs]`. Both sides reduce to the same expression. Use `_ = _ := by`. Rewrite using `[map_sum, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, IsFrame.basis_apply, QCoh.appLinear_apply, app_resM, hc, resM_smul, mul_smul]`.
-/
theorem exists_image_principal_of_effCartier : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (ρ : Y ⟶ X) (E L : X.Modules) (φ : E ⟶ L) (r : ℕ) [GlobalTheory.QCoh.IsFiniteQC (Limits.cokernel φ)], IsVB E r → IsVB L 1 → ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier ((GlobalTheory.QCoh.annihilatorSheaf (Limits.cokernel φ)).comap ρ) → ∀ y : Y, ∃ (V : Y.Opens) (l : Fin 1 → Γ((Scheme.Modules.pullback ρ).obj L, V)) (g : Γ(Y, V)) (t : Γ((Scheme.Modules.pullback ρ).obj E, V)), y ∈ V ∧ IsFrame l ∧ g ≠ 0 ∧ ((Scheme.Modules.pullback ρ).map φ).app V t = g • l 0 ∧ ∀ (W : Y.Opens) (h : W ≤ V) (s : Γ((Scheme.Modules.pullback ρ).obj E, W)), ∃ a : Γ(Y, W), ((Scheme.Modules.pullback ρ).map φ).app W s = a • GlobalTheory.Twist.resM ((Scheme.Modules.pullback ρ).obj L) h (g • l 0) := by
  intro X Y _ ρ E L φ r _ hE hL hC y
  haveI := hE.isQuasicoherent
  haveI := hL.isQuasicoherent
  obtain ⟨U₀, l₀, hyU₀, hl₀⟩ := hL (ρ y)
  obtain ⟨U, e, hU, hyU, hle, he⟩ := hE.exists_affine hyU₀
  have hl := hl₀.res hle
  set l : Fin 1 → Γ(L, U) := fun i => resM L hle (l₀ i) with hldef
  obtain ⟨U', f, hyU', hf, hI⟩ := hC y
  obtain ⟨h, hhle, hyh⟩ := U'.2.exists_basicOpen_le (V := ρ ⁻¹ᵁ U) ⟨y, hyU⟩ hyU'
  let A : Y.affineOpens := Y.affineBasicOpen h
  have hAU : (A : Y.Opens) ≤ ρ ⁻¹ᵁ U := hhle
  have hAU' : A ≤ U' := Y.basicOpen_le h
  have hyA : y ∈ (A : Y.Opens) := hyh
  let g : Γ(Y, A) := Y.presheaf.map (homOfLE hAU').op f
  have hI1 : ((QCoh.annihilatorSheaf (Limits.cokernel φ)).comap ρ).ideal A = Ideal.span {g} := by
    rw [← Scheme.IdealSheafData.map_ideal _ hAU', hI, Ideal.map_span, Set.image_singleton]
  have hI2 := Principalise.comapIdealAffine (QCoh.annihilatorSheaf (Limits.cokernel φ)) ρ
    ⟨U, hU⟩ A hAU
  rw [hI1, QCoh.annihilatorSheaf_ideal] at hI2
  have hg : g ≠ 0 := by
    haveI : Nonempty (A : Y.Opens) := ⟨⟨y, hyA⟩⟩
    haveI : Nonempty (U' : Y.Opens) := ⟨⟨y, hyU'⟩⟩
    intro h0
    refine nonZeroDivisors.ne_zero hf ?_
    apply map_injective_of_isIntegral Y (homOfLE (show (A : Y.Opens) ≤ U' from hAU'))
    rw [map_zero]
    exact h0
  have hres (F : X.Modules) (s : Γ(F, U)) :
      resM _ hAU (QCoh.pullbackSections ρ F le_rfl s) = QCoh.pullbackSections ρ F hAU s :=
    QCoh.res_pullbackSections ρ F le_rfl hAU s
  have hl' : IsFrame fun i => QCoh.pullbackSections ρ L hAU (l i) := by
    simpa only [hres] using (hl.pullback ρ).res hAU
  have he' : IsFrame fun i => QCoh.pullbackSections ρ E hAU (e i) := by
    simpa only [hres] using (he.pullback ρ).res hAU
  set l' := QCoh.pullbackSections ρ L hAU (l 0) with hl'def
  let ψ := (Scheme.Modules.pullback ρ).map φ
  have key (u : Γ(E, U)) (a : Γ(X, U)) (hu : φ.app U u = a • l 0) :
      ψ.app A (QCoh.pullbackSections ρ E hAU u) = ρ.appLE U A hAU a • l' := by
    rw [QCoh.pullback_map_app_pullbackSections, hu, QCoh.pullbackSections_smul]
  let J : Ideal Γ(Y, A) := (LinearMap.range (QCoh.appLinear ψ A)).comap
    (LinearMap.toSpanSingleton Γ(Y, A) _ l')
  have hgJ : g ∈ J := by
    have : Ideal.span {g} ≤ J := by
      rw [hI2, Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨u, hu⟩ := (mem_annihilator_cokernel_iff φ hU hl a).1 ha
      exact ⟨_, key u a hu⟩
    exact this (Ideal.subset_span rfl)
  obtain ⟨t, ht⟩ := hgJ
  have hei (i : Fin r) : ∃ c : Γ(Y, A),
      ψ.app A (QCoh.pullbackSections ρ E hAU (e i)) = c • (g • l') := by
    have hs := (hl.basis le_rfl).sum_repr (φ.app U (e i))
    rw [Fin.sum_univ_one, IsFrame.basis_apply, Twist.resM_self] at hs
    have hm : ρ.appLE U A hAU ((hl.basis le_rfl).repr (φ.app U (e i)) 0) ∈ Ideal.span {g} := by
      rw [hI2]
      exact Ideal.mem_map_of_mem _ ((mem_annihilator_cokernel_iff φ hU hl _).2 ⟨_, hs.symm⟩)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    exact ⟨c, by rw [key _ _ hs.symm, ← hc, mul_smul]⟩
  choose c hc using hei
  refine ⟨A, _, g, t, hyA, hl', hg, ht, fun W hW s => ?_⟩
  refine ⟨∑ i, (he'.basis hW).repr s i * resG Y hW (c i), ?_⟩
  have hs := (he'.basis hW).sum_repr s
  calc ψ.app W s = QCoh.appLinear ψ W (∑ i, (he'.basis hW).repr s i • he'.basis hW i) := by
        rw [hs]; rfl
    _ = _ := by
      rw [map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, IsFrame.basis_apply, QCoh.appLinear_apply, app_resM, hc, resM_smul, mul_smul]

end GlobalTheory.VB

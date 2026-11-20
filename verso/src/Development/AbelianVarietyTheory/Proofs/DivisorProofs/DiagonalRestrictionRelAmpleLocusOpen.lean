import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.FibreAmple

noncomputable section

namespace GlobalTheory.DiagAmpleLocus

/- English proof (translation)
Introduce `S' _ G _ _ P hG hP`. Use `hG.proper` as an intermediate fact. Establish `: Flat G.hom` using `by have := hG.smooth; infer_instance`. Establish `hD : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB` using `pull_isLB hP _`. Set `good : Set S'` to `{s | ∃ (Y X : Scheme.{0}) (j : Y ⟶ S') (_ : IsOpenImmersion j) (π : X ⟶ G.left) (f : X ⟶ Y), IsPullback π f G.hom j ∧ s ∈ Set.range j.base ∧ RelAmple (Over.mk f) ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull π)}`.

Establish `hopen : IsOpen good`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce and unpack `s ⟨Y, X, j, hj, π, f, h, hs, hA⟩`. Conclude with `⟨Set.range j.base, fun x hx => ⟨Y, X, j, hj, π, f, h, hx, hA⟩, j.isOpenEmbedding.isOpen_range, hs⟩`. Use `⟨⟨good, hopen⟩, fun V hV => ?_, ?_⟩` and prove the remaining obligations.

Set `AV` to `(Over.pullback V.ι).obj G`. Establish `: IsProper AV.hom` using `inferInstanceAs (IsProper (pullback.snd G.hom V.ι))`. Establish `key : RelAmple AV ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (pullback.fst G.hom V.ι))`. Use `GlobalTheory.AmpleLocal.relAmple_of_locally V AV _ (pull_isLB hD _) inferInstance inferInstance fun v => ?_` and prove the remaining obligations. Take `⟨Y, X, j, hj, π, f, h, ⟨y, hy⟩, hA⟩` from `hV v.2`.

Set `V' : V.toScheme.Opens` to `V.ι ⁻¹ᵁ j.opensRange`. Establish `hv : v ∈ V'` using `⟨y, hy⟩`. Establish `hrange : Set.range (V'.ι ≫ V.ι).base ⊆ Set.range j.base`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `w.2`.

Establish `sq : IsPullback ((AV.hom ⁻¹ᵁ V').ι ≫ pullback.fst G.hom V.ι) (AV.hom ∣_ V') G.hom (V'.ι ≫ V.ι)` using `(isPullback_morphismRestrict AV.hom V').flip.paste_horiz (IsPullback.of_hasPullback G.hom V.ι)`. Establish `h₁` using `relAmple_of_factor hD h sq (IsOpenImmersion.lift j _ hrange) (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hD π) (GlobalTheory.lbIso_refl (pull_isLB hD π)) hA`. Establish `: IsProper (Over.mk (AV.hom ∣_ V')).hom` using `inferInstanceAs (IsProper (AV.hom ∣_ V'))`. Conclude with `⟨V', hv, GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _) (pull_isLB (pull_isLB hD _) _) (lbIso_pull_pull hD _ _) h₁⟩`. Establish `e₁ : LBIso ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 AV) (𝟙 AV)).left) (P.pull ((lift (𝟙 AV) (𝟙 AV)).left ≫ Pdiv.PullbackComparison.pφ₂ V.ι G))` using `GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _`.

Rewrite `e₁` using `[GlobalTheory.DiagAmpleBC.diag_comp G AV _ _ (Pdiv.PullbackComparison.isSquare V.ι G)]`. Establish `e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (Pdiv.PullbackComparison.pφ V.ι G)) (P.pull (Pdiv.PullbackComparison.pφ V.ι G ≫ (lift (𝟙 G) (𝟙 G)).left))` using `GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _`. Conclude with `GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _) (pull_isLB (pull_isLB hP _) _) (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hD _) e₁ e₂.symm) key`. Introduce and unpack `T g A' _ φ φ₂ P' hpb hsq hP' e hA _ ⟨t, rfl⟩`. Establish `h₀ : IsPullback φ A'.hom G.hom g` using `hpb.1`.

Establish `: IsProper A'.hom` using `MorphismProperty.of_isPullback (P := @IsProper) h₀ ‹_›`. Establish `e₁ : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) (P.pull ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂))` using `GlobalTheory.ZM.SiegPull.lbIso_pull_comp e _`. Rewrite `e₁` using `[GlobalTheory.DiagAmpleBC.diag_comp G A' φ φ₂ hsq]`. Establish `e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) (P.pull (φ ≫ (lift (𝟙 G) (𝟙 G)).left))` using `GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _`. Establish `hA' : RelAmple A' ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ)` using `GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hP' _) (pull_isLB hD _) (LBIso.trans (pull_isLB hD _) (pull_isLB hP _) (pull_isLB hP' _) e₂ e₁.symm) hA`.

Take `⟨V, hV, hs, -⟩` from `exists_isAffineOpen_mem_and_subset (X := S') (U := ⊤) (x := g.base t) trivial`. Establish `: IsNoetherianRing Γ(S', V)` using `IsLocallyNoetherian.component_noetherian ⟨V, hV⟩`. Take `⟨VT, hVT, ht, hle⟩` from `exists_isAffineOpen_mem_and_subset (X := T) (U := g ⁻¹ᵁ V) (x := t) hs`. Take `⟨q, hq⟩ : t ∈ Set.range hVT.fromSpec.base` from `by rw [hVT.range_fromSpec]; exact ht`. Set `tV : Sp Γ(S', V) ⟶ S'` to `hV.fromSpec`.

Set `φR` to `g.appLE V VT hle`. Establish `sqR : Spec.map φR ≫ hV.fromSpec = hVT.fromSpec ≫ g` using `IsAffineOpen.SpecMap_appLE_fromSpec g hV hVT hle`. Set `p : PrimeSpectrum Γ(S', V)` to `(Spec.map φR).base q`. Establish `hp : tV.base p = g.base t`. Use `congrArg (fun f : Spec Γ(T, VT) ⟶ S' => f.base q) sqR` as an intermediate fact.

Simplify using `only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at this`. Rewrite using `[← hq]`. Conclude with `this`. Establish `: q.asIdeal.IsPrime` using `PrimeSpectrum.isPrime (q : PrimeSpectrum Γ(T, VT))`. Establish `: p.asIdeal.IsPrime` using `PrimeSpectrum.isPrime p`.

Set `k` to `p.asIdeal.ResidueField`. Set `kq` to `q.asIdeal.ResidueField`. Set `gR` to `algebraMap Γ(S', V) k`. Set `i : k →+* kq` to `Ideal.ResidueField.map p.asIdeal q.asIdeal φR.hom rfl`. Establish `hi : spMap (algebraMap Γ(T, VT) kq) ≫ Spec.map φR = spMap i ≫ spMap gR` using `by show Spec.map (CommRingCat.ofHom _) ≫ Spec.map φR = Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom gR)`.

Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `x`. Conclude with `(Ideal.ResidueField.map_algebraMap _ _ _ _ x).symm`. Set `y : Sp kq ⟶ S'` to `spMap i ≫ spMap gR ≫ tV`.

Establish `hu : (spMap (algebraMap Γ(T, VT) kq) ≫ hVT.fromSpec) ≫ g = y`. Rewrite using `[Category.assoc, ← sqR, ← Category.assoc, hi, Category.assoc]`. Establish `hfib` using `relAmple_of_factor hD h₀ (IsPullback.of_hasPullback G.hom y) _ hu (pull_isLB hD φ) (GlobalTheory.lbIso_refl (pull_isLB hD φ)) hA'`. Set `B : Over (Sp Γ(S', V))` to `Over.mk (pullback.snd G.hom tV)`. Establish `: IsProper B.hom` using `inferInstanceAs (IsProper (pullback.snd G.hom tV))`.

Establish `: Flat B.hom` using `inferInstanceAs (Flat (pullback.snd G.hom tV))`. Establish `hB` using `IsPullback.of_hasPullback G.hom tV`. Establish `hL` using `pull_isLB hD (pullback.fst G.hom tV)`. Take `⟨r, hr, hAr⟩` from `GlobalTheory.ProperFinite.relAmple_near_fibre B hL gR (residueField_fraction p.asIdeal) (relAmple_of_fieldExtension hD i ((IsPullback.of_hasPullback B.hom (spMap gR)).paste_horiz hB) (IsPullback.of_hasPullback G.hom _) (pull_isLB hL _) (lbIso_pull_pull hD _ _) hfib)`. Set `Dr : (Sp Γ(S', V)).Opens` to `PrimeSpectrum.basicOpen r`.

Establish `hpD : p ∈ Dr` using `fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)`. Establish `: IsProper (Over.mk (pullback.snd B.hom Dr.ι)).hom` using `inferInstanceAs (IsProper (pullback.snd B.hom Dr.ι))`. Conclude with `⟨Dr.toScheme, _, Dr.ι ≫ tV, inferInstance, pullback.fst B.hom Dr.ι ≫ pullback.fst G.hom tV, pullback.snd B.hom Dr.ι, (IsPullback.of_hasPullback B.hom Dr.ι).paste_horiz hB, ⟨⟨p, hpD⟩, hp⟩, GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hL _) (pull_isLB hD _) (lbIso_pul …`.
-/
theorem diag_relAmple_locus : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → Set.range g.base ⊆ (U : Set S') := by
  intro S' _ G _ _ P hG hP
  have := hG.proper
  have : Flat G.hom := by have := hG.smooth; infer_instance
  have hD : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  let good : Set S' := {s | ∃ (Y X : Scheme.{0}) (j : Y ⟶ S') (_ : IsOpenImmersion j) (π : X ⟶ G.left)
      (f : X ⟶ Y), IsPullback π f G.hom j ∧ s ∈ Set.range j.base ∧
        RelAmple (Over.mk f) ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull π)}
  have hopen : IsOpen good := by
    rw [isOpen_iff_forall_mem_open]
    rintro s ⟨Y, X, j, hj, π, f, h, hs, hA⟩
    exact ⟨Set.range j.base, fun x hx => ⟨Y, X, j, hj, π, f, h, hx, hA⟩,
      j.isOpenEmbedding.isOpen_range, hs⟩
  refine ⟨⟨good, hopen⟩, fun V hV => ?_, ?_⟩
  · let AV := (Over.pullback V.ι).obj G
    have : IsProper AV.hom := inferInstanceAs (IsProper (pullback.snd G.hom V.ι))
    have key : RelAmple AV ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (pullback.fst G.hom V.ι)) := by
      refine GlobalTheory.AmpleLocal.relAmple_of_locally V AV _ (pull_isLB hD _) inferInstance inferInstance
        fun v => ?_
      obtain ⟨Y, X, j, hj, π, f, h, ⟨y, hy⟩, hA⟩ := hV v.2
      let V' : V.toScheme.Opens := V.ι ⁻¹ᵁ j.opensRange
      have hv : v ∈ V' := ⟨y, hy⟩
      have hrange : Set.range (V'.ι ≫ V.ι).base ⊆ Set.range j.base := by
        rintro _ ⟨w, rfl⟩
        exact w.2
      have sq : IsPullback ((AV.hom ⁻¹ᵁ V').ι ≫ pullback.fst G.hom V.ι) (AV.hom ∣_ V') G.hom (V'.ι ≫ V.ι) :=
        (isPullback_morphismRestrict AV.hom V').flip.paste_horiz (IsPullback.of_hasPullback G.hom V.ι)
      have h₁ := relAmple_of_factor hD h sq (IsOpenImmersion.lift j _ hrange)
        (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hD π) (GlobalTheory.lbIso_refl (pull_isLB hD π)) hA
      have : IsProper (Over.mk (AV.hom ∣_ V')).hom := inferInstanceAs (IsProper (AV.hom ∣_ V'))
      exact ⟨V', hv, GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _)
        (pull_isLB (pull_isLB hD _) _) (lbIso_pull_pull hD _ _) h₁⟩
    have e₁ : LBIso ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 AV) (𝟙 AV)).left)
        (P.pull ((lift (𝟙 AV) (𝟙 AV)).left ≫ Pdiv.PullbackComparison.pφ₂ V.ι G)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    rw [GlobalTheory.DiagAmpleBC.diag_comp G AV _ _ (Pdiv.PullbackComparison.isSquare V.ι G)] at e₁
    have e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (Pdiv.PullbackComparison.pφ V.ι G))
        (P.pull (Pdiv.PullbackComparison.pφ V.ι G ≫ (lift (𝟙 G) (𝟙 G)).left)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    exact GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _) (pull_isLB (pull_isLB hP _) _)
      (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hD _) e₁ e₂.symm) key
  · rintro T g A' _ φ φ₂ P' hpb hsq hP' e hA _ ⟨t, rfl⟩
    have h₀ : IsPullback φ A'.hom G.hom g := hpb.1
    have : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) h₀ ‹_›
    have e₁ : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) (P.pull ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp e _
    rw [GlobalTheory.DiagAmpleBC.diag_comp G A' φ φ₂ hsq] at e₁
    have e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) (P.pull (φ ≫ (lift (𝟙 G) (𝟙 G)).left)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    have hA' : RelAmple A' ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) :=
      GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hP' _) (pull_isLB hD _)
        (LBIso.trans (pull_isLB hD _) (pull_isLB hP _) (pull_isLB hP' _) e₂ e₁.symm) hA
    obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S') (U := ⊤) (x := g.base t) trivial
    have : IsNoetherianRing Γ(S', V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    obtain ⟨VT, hVT, ht, hle⟩ := exists_isAffineOpen_mem_and_subset (X := T) (U := g ⁻¹ᵁ V) (x := t) hs
    obtain ⟨q, hq⟩ : t ∈ Set.range hVT.fromSpec.base := by rw [hVT.range_fromSpec]; exact ht
    let tV : Sp Γ(S', V) ⟶ S' := hV.fromSpec
    let φR := g.appLE V VT hle
    have sqR : Spec.map φR ≫ hV.fromSpec = hVT.fromSpec ≫ g := IsAffineOpen.SpecMap_appLE_fromSpec g hV hVT hle
    let p : PrimeSpectrum Γ(S', V) := (Spec.map φR).base q
    have hp : tV.base p = g.base t := by
      have := congrArg (fun f : Spec Γ(T, VT) ⟶ S' => f.base q) sqR
      simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at this
      rw [← hq]
      exact this
    have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime (q : PrimeSpectrum Γ(T, VT))
    have : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    let k := p.asIdeal.ResidueField
    let kq := q.asIdeal.ResidueField
    let gR := algebraMap Γ(S', V) k
    let i : k →+* kq := Ideal.ResidueField.map p.asIdeal q.asIdeal φR.hom rfl
    have hi : spMap (algebraMap Γ(T, VT) kq) ≫ Spec.map φR = spMap i ≫ spMap gR := by
      show Spec.map (CommRingCat.ofHom _) ≫ Spec.map φR = Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom gR)
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (Ideal.ResidueField.map_algebraMap _ _ _ _ x).symm
    let y : Sp kq ⟶ S' := spMap i ≫ spMap gR ≫ tV
    have hu : (spMap (algebraMap Γ(T, VT) kq) ≫ hVT.fromSpec) ≫ g = y := by
      rw [Category.assoc, ← sqR, ← Category.assoc, hi, Category.assoc]
    have hfib := relAmple_of_factor hD h₀ (IsPullback.of_hasPullback G.hom y) _ hu (pull_isLB hD φ)
      (GlobalTheory.lbIso_refl (pull_isLB hD φ)) hA'
    let B : Over (Sp Γ(S', V)) := Over.mk (pullback.snd G.hom tV)
    have : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd G.hom tV))
    have : Flat B.hom := inferInstanceAs (Flat (pullback.snd G.hom tV))
    have hB := IsPullback.of_hasPullback G.hom tV
    have hL := pull_isLB hD (pullback.fst G.hom tV)
    obtain ⟨r, hr, hAr⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hL gR (residueField_fraction p.asIdeal)
      (relAmple_of_fieldExtension hD i ((IsPullback.of_hasPullback B.hom (spMap gR)).paste_horiz hB)
        (IsPullback.of_hasPullback G.hom _) (pull_isLB hL _) (lbIso_pull_pull hD _ _) hfib)
    let Dr : (Sp Γ(S', V)).Opens := PrimeSpectrum.basicOpen r
    have hpD : p ∈ Dr := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
    have : IsProper (Over.mk (pullback.snd B.hom Dr.ι)).hom := inferInstanceAs (IsProper (pullback.snd B.hom Dr.ι))
    exact ⟨Dr.toScheme, _, Dr.ι ≫ tV, inferInstance, pullback.fst B.hom Dr.ι ≫ pullback.fst G.hom tV,
      pullback.snd B.hom Dr.ι, (IsPullback.of_hasPullback B.hom Dr.ι).paste_horiz hB, ⟨⟨p, hpD⟩, hp⟩,
      GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hL _) (pull_isLB hD _) (lbIso_pull_pull hD _ _).symm hAr⟩

end GlobalTheory.DiagAmpleLocus

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue GlobalTheory.CechPic
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)

namespace GlobalTheory

namespace VMetric

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
  {E E' : X.Modules} {r : ℕ}

/- English proof (translation)
The claim follows from `HermLB.isometric_of_chart (L := det H) (M := det (H.map φ)) (fun c : Chart E r => c.map φ) (fun _ => le_rfl) (fun x c c' _ _ => congrArg (gm (𝟙 X) x _) (IsFrame.detUnit_map_iso c.isFrame c'.isFrame φ.hom _ _).symm) fun σ c _ hy => congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => -Re …`.
-/
theorem isometric_det_map {h : VMetric p E r} (H : h.IsCInf) (φ : E ≅ E') :
    (det H).Isometric (det (H.map φ)) :=
  HermLB.isometric_of_chart (L := det H) (M := det (H.map φ)) (fun c : Chart E r => c.map φ)
    (fun _ => le_rfl)
    (fun x c c' _ _ => congrArg (gm (𝟙 X) x _)
      (IsFrame.detUnit_map_iso c.isFrame c'.isFrame φ.hom _ _).symm)
    fun σ c _ hy => congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => -Real.log M.det.re)
      ((h.met σ).map_G φ c hy)

/- English proof (translation)
Use `h.isVB.isQuasicoherent` as an intermediate fact. Use `HermLB.isometric_of_local (L := det (H.pull π hπ)) (M := (det H).pull π hπ) (fun c : Chart E r => π ⁻¹ᵁ c.U) (fun x => ?_) (fun c _ => c) (fun c => c.pull h.isVB π) (fun _ _ h => mem_pull.2 h) (fun _ => le_rfl) (fun _ => 1) (fun x c c' hc hc' => ?_) fun σ c y hy => ?_` and prove the remaining obligations. Conclude with `exists_chart h.isVB.isLB_det (π x)`. Establish `e₁` using `gm_pull_g (VB.det E r) π (𝟙 Y) x (fun _ => c) (fun _ => c') (mem_pull.2 hc) (mem_pull.2 hc')`. Establish `e₂` using `gm_pull (𝟙 Y) π x (c.U ⊓ c'.U) ⟨hc, hc'⟩ ((VB.det E r).g c c')`.

Establish `e₃ : (VB.det _ r).g (c.pull h.isVB π) (c'.pull h.isVB π) = pullU π (c.U ⊓ c'.U) ((VB.det E r).g c c')`. Use `Units.ext ((IsFrame.val_detUnit_pullback c.isFrame c'.isFrame π inf_le_left inf_le_right (T := π ⁻¹ᵁ (c.U ⊓ c'.U)) le_rfl).trans ?_)` and prove the remaining obligations. Rewrite using `[Scheme.Hom.appLE_eq_app]`. Both sides reduce to the same expression. Establish `e₄` using `e₁.trans (e₂.symm.trans (congrArg (gm (𝟙 Y) x _) e₃.symm))`.

Rewrite using `[map_one, map_one, mul_one]`. Conclude with `(mul_inv_eq_one.2 e₄).symm`. Rewrite using `[logSq_one hy, add_zero]`. Use `(((det H).φ σ).pull_φ π hπ _ y).trans ?_` and prove the remaining obligations. Conclude with `congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => -Real.log M.det.re) ((h.met σ).pull_G π hπ c hy).symm`.
-/
theorem isometric_det_pull {h : VMetric p E r} (H : h.IsCInf) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (det (H.pull π hπ)).Isometric ((det H).pull π hπ) := by
  have := h.isVB.isQuasicoherent
  refine HermLB.isometric_of_local (L := det (H.pull π hπ)) (M := (det H).pull π hπ)
    (fun c : Chart E r => π ⁻¹ᵁ c.U) (fun x => ?_) (fun c _ => c) (fun c => c.pull h.isVB π)
    (fun _ _ h => mem_pull.2 h) (fun _ => le_rfl) (fun _ => 1) (fun x c c' hc hc' => ?_)
    fun σ c y hy => ?_
  · exact exists_chart h.isVB.isLB_det (π x)
  · have e₁ := gm_pull_g (VB.det E r) π (𝟙 Y) x (fun _ => c) (fun _ => c') (mem_pull.2 hc)
      (mem_pull.2 hc')
    have e₂ := gm_pull (𝟙 Y) π x (c.U ⊓ c'.U) ⟨hc, hc'⟩ ((VB.det E r).g c c')
    have e₃ : (VB.det _ r).g (c.pull h.isVB π) (c'.pull h.isVB π) =
        pullU π (c.U ⊓ c'.U) ((VB.det E r).g c c') := by
      refine Units.ext ((IsFrame.val_detUnit_pullback c.isFrame c'.isFrame π inf_le_left
        inf_le_right (T := π ⁻¹ᵁ (c.U ⊓ c'.U)) le_rfl).trans ?_)
      rw [Scheme.Hom.appLE_eq_app]
      rfl
    have e₄ := e₁.trans (e₂.symm.trans (congrArg (gm (𝟙 Y) x _) e₃.symm))
    rw [map_one, map_one, mul_one]
    exact (mul_inv_eq_one.2 e₄).symm
  · rw [logSq_one hy, add_zero]
    refine (((det H).φ σ).pull_φ π hπ _ y).trans ?_
    exact congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => -Real.log M.det.re)
      ((h.met σ).pull_G π hπ c hy).symm

/- English proof (translation)
Use `(fl.isVB_gr i).isQuasicoherent` as an intermediate fact. Establish `e : (pullStep fl π i a).quot.e = ((a.quot.pull (fl.isVB_gr i) π).map (fl.pullGrIso π i)).e`. Use function extensionality and compare the values at `j`. Use `Eq.trans ?_ (congrArg ((fl.pullGrIso π i).hom.app _) (QCoh.pullback_map_app_pullbackSections π (fl.π i) le_rfl (a.t j)))` and prove the remaining obligations. Conclude with `(congr(($(fl.map_π_pullGrIso π i)).app _ _)).symm`.

Establish `key : ∀ {F : Y.Modules} {U : Y.Opens} {e e' : Fin 1 → Γ(F, U)} (he : IsFrame e) (he' : IsFrame e'), e = e' → (⟨U, e, he⟩ : Chart F 1) = ⟨U, e', he'⟩`. Introduce and unpack `F U e e' he he' rfl`. Both sides reduce to the same expression. Conclude with `key _ _ e`.
-/
theorem quot_pullStep (fl : Vert.Flag E r) (π : Y ⟶ X) (i : Fin r)
    (a : AdaptedChart (stepSeq fl i) i 1) :
    (pullStep fl π i a).quot = (a.quot.pull (fl.isVB_gr i) π).map (fl.pullGrIso π i) := by
  have := (fl.isVB_gr i).isQuasicoherent
  have e : (pullStep fl π i a).quot.e =
      ((a.quot.pull (fl.isVB_gr i) π).map (fl.pullGrIso π i)).e := by
    funext j
    refine Eq.trans ?_ (congrArg ((fl.pullGrIso π i).hom.app _)
      (QCoh.pullback_map_app_pullbackSections π (fl.π i) le_rfl (a.t j)))
    exact (congr(($(fl.map_π_pullGrIso π i)).app _ _)).symm
  have key : ∀ {F : Y.Modules} {U : Y.Opens} {e e' : Fin 1 → Γ(F, U)} (he : IsFrame e)
      (he' : IsFrame e'), e = e' → (⟨U, e, he⟩ : Chart F 1) = ⟨U, e', he'⟩ := by
    rintro F U e e' he he' rfl
    rfl
  exact key _ _ e

/- English proof (translation)
Use `VMetric.ext (funext fun σ => Met.ext_of_exists fun z => ?_)` and prove the remaining obligations. Take `⟨a, ha⟩` from `Met.exists_adapted (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) (PtsOver.map π hπ _ z)`. Establish `ha' : z ∈ ptsIn q σ (π ⁻¹ᵁ a.U)` using `ha`. Use `⟨(pullStep fl π i a).quot, ha', ?_⟩` and prove the remaining obligations. Use `((((h.pull π hπ).stepMet (fl.pull π) i).met σ).quot_G (stepSeq_shortExact (fl.pull π) i) ((fl.pull π).isVB i.castSucc) ((fl.pull π).isVB_gr i) (pullStep fl π i a) ha').trans ?_` and prove the remaining obligations.

Rewrite using `[gram_pullStep h hπ a ha', quot_pullStep]`. Use `Eq.symm (((((h.grMet fl i).met σ).pull π hπ).map_G (fl.pullGrIso π i) (a.quot.pull (fl.isVB_gr i) π) ha').trans ?_)` and prove the remaining obligations. Use `(((h.grMet fl i).met σ).pull_G π hπ a.quot ha).trans ?_` and prove the remaining obligations. Conclude with `((h.stepMet fl i).met σ).quot_G (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) a ha`.
-/
theorem grMet_pull (h : VMetric p E r) (fl : Vert.Flag E r) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (i : Fin r) : (h.pull π hπ).grMet (fl.pull π) i =
      ((h.grMet fl i).pull π hπ).map (fl.pullGrIso π i) := by
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun z => ?_)
  obtain ⟨a, ha⟩ := Met.exists_adapted (stepSeq_shortExact fl i) (fl.isVB i.castSucc)
    (fl.isVB_gr i) (PtsOver.map π hπ _ z)
  have ha' : z ∈ ptsIn q σ (π ⁻¹ᵁ a.U) := ha
  refine ⟨(pullStep fl π i a).quot, ha', ?_⟩
  refine ((((h.pull π hπ).stepMet (fl.pull π) i).met σ).quot_G (stepSeq_shortExact (fl.pull π) i)
    ((fl.pull π).isVB i.castSucc) ((fl.pull π).isVB_gr i) (pullStep fl π i a) ha').trans ?_
  rw [gram_pullStep h hπ a ha', quot_pullStep]
  refine Eq.symm (((((h.grMet fl i).met σ).pull π hπ).map_G (fl.pullGrIso π i)
    (a.quot.pull (fl.isVB_gr i) π) ha').trans ?_)
  refine (((h.grMet fl i).met σ).pull_G π hπ a.quot ha).trans ?_
  exact ((h.stepMet fl i).met σ).quot_G (stepSeq_shortExact fl i) (fl.isVB i.castSucc)
    (fl.isVB_gr i) a ha

/- English proof (translation)
Establish `key : ∀ {F : Y.Modules} {h₁ h₂ : VMetric q F 1} (H₁ : h₁.IsCInf) (H₂ : h₂.IsCInf), h₁ = h₂ → det H₁ = det H₂`. Introduce and unpack `F h₁ h₂ H₁ H₂ rfl`. Both sides reduce to the same expression. Rewrite using `[grLB, key _ (((H.grMet fl i).pull π hπ).map (fl.pullGrIso π i)) (grMet_pull h fl π hπ i)]`. Conclude with `(isometric_det_map _ _).symm.trans (isometric_det_pull (H.grMet fl i) π hπ)`.
-/
theorem isometric_grLB_pull (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k) (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r)
    (π : Y ⟶ X) (hπ : π ≫ p = q) (i : Fin r) :
    (VMetric.grLB (fl.pull π) i (H.pull π hπ)).Isometric ((VMetric.grLB fl i H).pull π hπ) := by
  have key : ∀ {F : Y.Modules} {h₁ h₂ : VMetric q F 1} (H₁ : h₁.IsCInf) (H₂ : h₂.IsCInf),
      h₁ = h₂ → det H₁ = det H₂ := by
    rintro F h₁ h₂ H₁ H₂ rfl
    rfl
  rw [grLB, key _ (((H.grMet fl i).pull π hπ).map (fl.pullGrIso π i)) (grMet_pull h fl π hπ i)]
  exact (isometric_det_map _ _).symm.trans (isometric_det_pull (H.grMet fl i) π hπ)

end VMetric

end GlobalTheory

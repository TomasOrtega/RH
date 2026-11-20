import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothSchemeDecomposeRelativeDimensionStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HolomorphicLocalSectionsCompatibleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

noncomputable section

namespace GlobalTheory.CompanionTheory.Gaga

open Opposite

/- English proof (translation)
Unfold `valAt'`. Distinguish the cases in `h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)`. Rewrite using `[dif_pos h, dif_pos (show ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]`. Unfold `valAt`. Use `congr 1`.

Rewrite using `[dif_neg h, dif_neg (show ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]`.
-/
theorem val_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]
    unfold valAt
    congr 1
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]

/- English proof (translation)
The claim follows from `congr($(φ.naturality (homOfLE h).op).hom a)`.
-/
theorem app_res {X Y : Scheme.{0}} (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (φ.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (Y.presheaf.map (homOfLE (show φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U from fun _ hy => h hy)).op).hom ((φ.app U).hom a) :=
  congr($(φ.naturality (homOfLE h).op).hom a)

/- English proof (translation)
The claim follows from `Units.ext (app_res φ h u.val).symm`.
-/
theorem res_pullU {X Y : Scheme.{0}} (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    res (show φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U from fun _ hy => h hy) (pullU φ U u) = pullU φ V (res h u) :=
  Units.ext (app_res φ h u.val).symm

def resLB {X Y : Scheme.{0}} (φ : Y ⟶ X) (L : LB X) : LB Y where
  ι := L.ι
  U i := φ ⁻¹ᵁ L.U i
  g i j := pullU φ (L.U i ⊓ L.U j) (L.g i j)

/- English proof (translation)
Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Establish `hy : φ y ∈ (⨆ i, L.U i)` using `by rw [hL.cover]; trivial`. Take `⟨i, hi⟩` from `Opens.mem_iSup.1 hy`. Conclude with `Opens.mem_iSup.2 ⟨i, hi⟩`. Use `g_self i := by`.

Use `(res_pullU φ (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (L.g i i)).trans ?_` and prove the remaining obligations. Conclude with `(congrArg (pullU φ (L.U i)) (hL.g_self i)).trans (map_one _)`. Use `cocycle i j k := by`. Establish `h1` using `res_pullU φ (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) (L.g i j)`. Establish `h2` using `res_pullU φ (le_inf (inf_le_left.trans inf_le_right) inf_le_right : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) (L.g j k)`.

Establish `h3` using `res_pullU φ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) (L.g i k)`. Establish `h4` using `congrArg (pullU φ (L.U i ⊓ L.U j ⊓ L.U k)) (hL.cocycle i j k)`. Rewrite `h4` using `[map_mul]`. Conclude with `(congrArg₂ (· * ·) h1 h2).trans (h4.trans h3.symm)`.
-/
theorem isLB_resLB {X Y : Scheme.{0}} (φ : Y ⟶ X) {L : LB X} (hL : L.IsLB) : (resLB φ L).IsLB where
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    have hy : φ y ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  g_self i := by
    refine (res_pullU φ (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (L.g i i)).trans ?_
    exact (congrArg (pullU φ (L.U i)) (hL.g_self i)).trans (map_one _)
  cocycle i j k := by
    have h1 := res_pullU φ (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) (L.g i j)
    have h2 := res_pullU φ (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) (L.g j k)
    have h3 := res_pullU φ (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) (L.g i k)
    have h4 := congrArg (pullU φ (L.U i ⊓ L.U j ⊓ L.U k)) (hL.cocycle i j k)
    rw [map_mul] at h4
    exact (congrArg₂ (· * ·) h1 h2).trans (h4.trans h3.symm)

/- English proof (translation)
Set `V : ℕ → X.Opens` to `fun D => (W D).ι ''ᵁ (W D).ι ⁻¹ᵁ U`. Establish `hV : ∀ D, V D = W D ⊓ U` using `fun D => by simp [V, Scheme.Hom.image_preimage_eq_opensRange_inf]`. Establish `hle : ∀ D, V D ≤ U` using `fun D => by rw [hV]; exact inf_le_right`. Establish `hcov : U ≤ iSup V`. Introduce `x hx`.

Establish `hy : x ∈ (⨆ D, W D)` using `by rw [hc]; trivial`. Take `⟨D, hD⟩` from `Opens.mem_iSup.1 hy`. Use `Opens.mem_iSup.2 ⟨D, ?_⟩` and prove the remaining obligations. Rewrite using `[hV]`. Conclude with `⟨hD, hx⟩`.

Establish `hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 V a`. Introduce `D D'`. Distinguish the cases in `e : D = D'`. Substitute `e` using the available equality. Both sides reduce to the same expression.

Establish `hb : V D ⊓ V D' = ⊥`. Use `eq_bot_iff.2 ?_` and prove the remaining obligations. Rewrite using `[← hd e, hV, hV]`. Conclude with `inf_le_inf inf_le_left inf_le_left`. Establish `: Subsingleton (X.sheaf.1.obj (op (V D ⊓ V D')))`.

Rewrite using `[hb]`. Conclude with `CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty`. Conclude with `Subsingleton.elim _ _`. Take `⟨b, hb, hu⟩` from `X.sheaf.existsUnique_gluing' V U (fun D => homOfLE (hle D)) hcov a hcomp`. Use `⟨b, fun D => ?_, fun c hc' => hu c fun D => ?_⟩` and prove the remaining obligations.

Rewrite using `[Scheme.Opens.ι_app]`. Conclude with `hb D`. Rewrite using `[← hc' D, Scheme.Opens.ι_app]`. Both sides reduce to the same expression.
-/
theorem glue {X : Scheme.{0}} (W : ℕ → X.Opens) (hc : ⨆ D, W D = ⊤)
    (hd : Pairwise fun D D' => W D ⊓ W D' = ⊥) (U : X.Opens)
    (a : ∀ D, Γ((W D).toScheme, (W D).ι ⁻¹ᵁ U)) :
    ∃! b : Γ(X, U), ∀ D, ((W D).ι.app U).hom b = a D := by
  let V : ℕ → X.Opens := fun D => (W D).ι ''ᵁ (W D).ι ⁻¹ᵁ U
  have hV : ∀ D, V D = W D ⊓ U := fun D => by simp [V, Scheme.Hom.image_preimage_eq_opensRange_inf]
  have hle : ∀ D, V D ≤ U := fun D => by rw [hV]; exact inf_le_right
  have hcov : U ≤ iSup V := by
    intro x hx
    have hy : x ∈ (⨆ D, W D) := by rw [hc]; trivial
    obtain ⟨D, hD⟩ := Opens.mem_iSup.1 hy
    refine Opens.mem_iSup.2 ⟨D, ?_⟩
    rw [hV]
    exact ⟨hD, hx⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 V a := by
    intro D D'
    by_cases e : D = D'
    · subst e
      rfl
    · have hb : V D ⊓ V D' = ⊥ := by
        refine eq_bot_iff.2 ?_
        rw [← hd e, hV, hV]
        exact inf_le_inf inf_le_left inf_le_left
      have : Subsingleton (X.sheaf.1.obj (op (V D ⊓ V D'))) := by
        rw [hb]
        exact CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty
      exact Subsingleton.elim _ _
  obtain ⟨b, hb, hu⟩ := X.sheaf.existsUnique_gluing' V U (fun D => homOfLE (hle D)) hcov a hcomp
  refine ⟨b, fun D => ?_, fun c hc' => hu c fun D => ?_⟩
  · rw [Scheme.Opens.ι_app]
    exact hb D
  · rw [← hc' D, Scheme.Opens.ι_app]
    rfl

/- English proof (translation)
Set `p : Sp ℂ` to `IsLocalRing.closedPoint ℂ`. Establish `hy : x p ∈ (⨆ D, W D)` using `by rw [hc]; trivial`. Take `⟨D, hD⟩` from `Opens.mem_iSup.1 hy`. Establish `hr : Set.range x ⊆ Set.range (W D).ι`. Introduce and unpack `_ ⟨q, rfl⟩`.

Rewrite using `[Subsingleton.elim q p, Scheme.Opens.range_ι]`. Conclude with `hD`. Conclude with `⟨D, IsOpenImmersion.lift (W D).ι x hr, IsOpenImmersion.lift_fac _ _ _⟩`.
-/
theorem exists_factor {X : Scheme.{0}} (W : ℕ → X.Opens) (hc : ⨆ D, W D = ⊤) (x : Sp ℂ ⟶ X) :
    ∃ (D : ℕ) (x' : Sp ℂ ⟶ (W D).toScheme), x' ≫ (W D).ι = x := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hy : x p ∈ (⨆ D, W D) := by rw [hc]; trivial
  obtain ⟨D, hD⟩ := Opens.mem_iSup.1 hy
  have hr : Set.range x ⊆ Set.range (W D).ι := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q p, Scheme.Opens.range_ι]
    exact hD
  exact ⟨D, IsOpenImmersion.lift (W D).ι x hr, IsOpenImmersion.lift_fac _ _ _⟩

/- English proof (translation)
Introduce `X s hp hs L hL h hhol hcomp`. Take `⟨W, hcl, hdim, hc, hd⟩` from `GlobalTheory.T.smooth_scheme_decompose_relative_dimension X s hs`. Establish `hprop : ∀ D, IsProper ((W D).ι ≫ s)` using `fun D => by haveI : IsClosedImmersion (W D).ι := IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hcl D) infer_instance`. Establish `key : ∀ D, ∃ σ : (resLB (W D).ι L).Sec, ∀ (i : L.ι) (x : Sp ℂ ⟶ (W D).toScheme), x ≫ (W D).ι ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ ((W D).ι ⁻¹ᵁ L.U i) → valAt' x ((W D).ι ⁻¹ᵁ L.U i) (σ.f i) = h i (x ≫ (W D).ι)` using `fun D => by`. Use `GlobalTheory.T.holomorphic_local_sections_compatible (W D).toScheme ((W D).ι ≫ s) D (hprop D) (hdim D) (resLB (W D).ι L) (isLB_resLB _ hL) (fun i x => h i (x ≫ (W D).ι)) ?_ ?_` and prove the remaining obligations.

Introduce `i m B y hB hy hcond`. Use `hhol i m B (fun b => y b ≫ (W D).ι) hB ?_ ?_` and prove the remaining obligations. Introduce `U f`. Use `hy ((W D).ι ⁻¹ᵁ U) (((W D).ι.app U).hom f)` as an intermediate fact. Simplify using `only [val_comp]`.

Conclude with `this`. Introduce `b hb`. Use `⟨by simpa using (hcond b hb).1, (hcond b hb).2⟩` and prove the remaining obligations. Introduce `i j x hx hU`. Use `(hcomp i j (x ≫ (W D).ι) (by simpa using hx) hU).trans ?_` and prove the remaining obligations.

Rewrite using `[val_comp]`. Both sides reduce to the same expression. Use `choose σ hσ using key`. Establish `ex` using `fun i => glue W hc hd (L.U i) (fun D => (σ D).f i)`. Use `choose b hb hbu using ex`.

Use `⟨⟨b, fun i j => ?_⟩, fun i x hx hU => ?_⟩` and prove the remaining obligations. Use `(glue W hc hd (L.U i ⊓ L.U j) fun D => ((W D).ι.app _).hom ((X.presheaf.map (homOfLE inf_le_left).op).hom (b i))).unique (fun _ => rfl) fun D => ?_` and prove the remaining obligations. Rewrite using `[map_mul, app_res, app_res, hb, hb]`. Conclude with `((σ D).compat i j).symm`. Take `⟨D, x', rfl⟩` from `exists_factor W hc x`.

Rewrite using `[val_comp, hb]`. Conclude with `hσ D i x' (by simpa using hx) hU`.
-/
theorem gagaSections : GlobalTheory.CompanionTheory.Ar.Flat.GagaSections := by
  intro X s hp hs L hL h hhol hcomp
  obtain ⟨W, hcl, hdim, hc, hd⟩ := GlobalTheory.T.smooth_scheme_decompose_relative_dimension X s hs
  have hprop : ∀ D, IsProper ((W D).ι ≫ s) := fun D => by
    haveI : IsClosedImmersion (W D).ι :=
      IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hcl D)
    infer_instance
  have key : ∀ D, ∃ σ : (resLB (W D).ι L).Sec, ∀ (i : L.ι) (x : Sp ℂ ⟶ (W D).toScheme),
      x ≫ (W D).ι ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ ((W D).ι ⁻¹ᵁ L.U i) →
      valAt' x ((W D).ι ⁻¹ᵁ L.U i) (σ.f i) = h i (x ≫ (W D).ι) := fun D => by
    refine GlobalTheory.T.holomorphic_local_sections_compatible (W D).toScheme ((W D).ι ≫ s) D (hprop D) (hdim D) (resLB (W D).ι L)
      (isLB_resLB _ hL) (fun i x => h i (x ≫ (W D).ι)) ?_ ?_
    · intro i m B y hB hy hcond
      refine hhol i m B (fun b => y b ≫ (W D).ι) hB ?_ ?_
      · intro U f
        have := hy ((W D).ι ⁻¹ᵁ U) (((W D).ι.app U).hom f)
        simp only [val_comp]
        exact this
      · intro b hb
        refine ⟨by simpa using (hcond b hb).1, (hcond b hb).2⟩
    · intro i j x hx hU
      refine (hcomp i j (x ≫ (W D).ι) (by simpa using hx) hU).trans ?_
      rw [val_comp]
      rfl
  choose σ hσ using key
  have ex := fun i => glue W hc hd (L.U i) (fun D => (σ D).f i)
  choose b hb hbu using ex
  refine ⟨⟨b, fun i j => ?_⟩, fun i x hx hU => ?_⟩
  · refine (glue W hc hd (L.U i ⊓ L.U j) fun D => ((W D).ι.app _).hom
      ((X.presheaf.map (homOfLE inf_le_left).op).hom (b i))).unique (fun _ => rfl) fun D => ?_
    rw [map_mul, app_res, app_res, hb, hb]
    exact ((σ D).compat i j).symm
  · obtain ⟨D, x', rfl⟩ := exists_factor W hc x
    rw [val_comp, hb]
    exact hσ D i x' (by simpa using hx) hU

end GlobalTheory.CompanionTheory.Gaga

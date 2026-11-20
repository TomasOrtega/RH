import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IsomorphismTransport
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Rewrite using `[show (⊥ : X.IdealSheafData).comap π = ⊥ from by simp]`. Use `infer_instance`.
-/
private theorem isIso_subschemeι_comap_bot {X X' : Scheme.{u}} (π : X' ⟶ X) :
    IsIso ((⊥ : X.IdealSheafData).comap π).subschemeι := by
  rw [show (⊥ : X.IdealSheafData).comap π = ⊥ from by simp]
  infer_instance

/- English proof (translation)
Establish `: IsIso (AlgebraicGeometry.morphismRestrict f U)` using `inferInstance`. Rewrite using `[← (isPullback_morphismRestrict f U).w]`. Conclude with `Scheme.Hom.ker_comp_of_isIso ..`.
-/
theorem ker_preimage_ι_comp_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Y.Opens) :
    ((f ⁻¹ᵁ U).ι ≫ f).ker = U.ι.ker := by
  have : IsIso (AlgebraicGeometry.morphismRestrict f U) := inferInstance
  rw [← (isPullback_morphismRestrict f U).w]
  exact Scheme.Hom.ker_comp_of_isIso ..

/- English proof (translation)
Apply `TopCat.Presheaf.section_ext X.sheaf U` to reduce the goal to its premises. Introduce `x hx`. Take `⟨V, hV, hxV, hs⟩` from `h x hx`. Establish `h1 : X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hV).op s) = X.presheaf.germ U x hx s` using `X.presheaf.germ_res_apply (homOfLE hV) x hxV s`. Rewrite `h1` using `[hs, map_zero]`.

Use `show X.presheaf.germ U x hx s = X.presheaf.germ U x hx 0`. Rewrite using `[map_zero]`. Conclude with `h1.symm`.
-/
theorem section_eq_zero_of_locally_zero {X : Scheme.{u}} (U : X.Opens)
    (s : X.presheaf.obj (op U))
    (h : ∀ x ∈ U, ∃ V : X.Opens, ∃ hV : V ≤ U, x ∈ V ∧
      X.presheaf.map (homOfLE hV).op s = 0) :
    s = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  obtain ⟨V, hV, hxV, hs⟩ := h x hx
  have h1 : X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hV).op s)
      = X.presheaf.germ U x hx s := X.presheaf.germ_res_apply (homOfLE hV) x hxV s
  rw [hs, map_zero] at h1
  show X.presheaf.germ U x hx s = X.presheaf.germ U x hx 0
  rw [map_zero]
  exact h1.symm

/- English proof (translation)
Establish `hcomp : X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op = X.presheaf.map (homOfLE (h2.trans h1)).op`. Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression. Conclude with `congrArg (fun φ : Γ(X, V) ⟶ Γ(X, V'') => (ConcreteCategory.hom φ) s) hcomp`.
-/
private theorem map_homOfLE_map_homOfLE {X : Scheme.{u}} {V V' V'' : X.Opens} (h1 : V' ≤ V) (h2 : V'' ≤ V')
    (s : Γ(X, V)) :
    X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE h1).op s)
      = X.presheaf.map (homOfLE (h2.trans h1)).op s := by
  have hcomp : X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op
      = X.presheaf.map (homOfLE (h2.trans h1)).op := by
    rw [← Functor.map_comp]
    rfl
  exact congrArg (fun φ : Γ(X, V) ⟶ Γ(X, V'') => (ConcreteCategory.hom φ) s) hcomp

/- English proof (translation)
Establish `hT : W.ι ''ᵁ W.ι ⁻¹ᵁ V ≤ V`. Introduce and unpack `y ⟨z, hz, rfl⟩`. Conclude with `hz`. Establish `hle : V' ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V`. Introduce `y hy`.

Conclude with `⟨⟨y, h2 y hy⟩, h1 hy, rfl⟩`. Establish `hzero : X.presheaf.map (homOfLE hT).op s = 0`. Rewrite `hs` using `[Scheme.Opens.ι_app]`. Conclude with `hs`. Rewrite using `[← map_homOfLE_map_homOfLE hT hle s, hzero, map_zero]`.
-/
private theorem map_eq_zero_of_app_ι_eq_zero {X : Scheme.{u}} (W V V' : X.Opens) (s : Γ(X, V))
    (hs : (W.ι.app V).hom s = 0) (h1 : V' ≤ V) (h2 : ∀ y : ↥X, y ∈ V' → y ∈ W) :
    X.presheaf.map (homOfLE h1).op s = 0 := by
  have hT : W.ι ''ᵁ W.ι ⁻¹ᵁ V ≤ V := by
    rintro y ⟨z, hz, rfl⟩
    exact hz
  have hle : V' ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V := by
    intro y hy
    exact ⟨⟨y, h2 y hy⟩, h1 hy, rfl⟩
  have hzero : X.presheaf.map (homOfLE hT).op s = 0 := by
    rw [Scheme.Opens.ι_app] at hs
    exact hs
  rw [← map_homOfLE_map_homOfLE hT hle s, hzero, map_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem algebraMap_basicOpen {X : Scheme.{u}} {U : X.Opens} (f : Γ(X, U)) (t : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) t
      = X.presheaf.map (homOfLE (X.basicOpen_le f)).op t := rfl

/- English proof (translation)
Introduce `hmem`. Establish `h1 : y ∈ I.supportSet` using `hmem`. Rewrite `h1` using `[Scheme.IdealSheafData.mem_supportSet_iff]`. Establish `h2` using `h1 U`. Rewrite `h2` using `[Scheme.mem_zeroLocus_iff]`.

Conclude with `h2 f hf hy`.
-/
private theorem notMem_support_of_mem_basicOpen {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (f : Γ(X, U.1)) (hf : f ∈ I.ideal U) (y : ↥X) (hy : y ∈ X.basicOpen f) :
    y ∉ I.support := by
  intro hmem
  have h1 : y ∈ I.supportSet := hmem
  rw [Scheme.IdealSheafData.mem_supportSet_iff] at h1
  have h2 := h1 U
  rw [Scheme.mem_zeroLocus_iff] at h2
  exact h2 f hf hy

/- English proof (translation)
Establish `hAaff : IsAffineOpen (X.basicOpen b)` using `hU₀.basicOpen b`. Use `hU₀.isLocalization_basicOpen b` as an intermediate fact. Establish `hAU₀ : X.basicOpen b ≤ U₀` using `X.basicOpen_le b`. Establish `hgnzd : X.presheaf.map (homOfLE hAU₀).op f ∈ nonZeroDivisors Γ(X, X.basicOpen b)`. Establish `hq : X.presheaf.map (homOfLE hAU₀).op f = algebraMap Γ(X, U₀) Γ(X, X.basicOpen b) f` using `rfl`.

Rewrite using `[hq]`. Conclude with `IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers b) Γ(X, X.basicOpen b) hf`. Establish `hbg : X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f) = X.basicOpen b ⊓ X.basicOpen f`. Rewrite using `[Scheme.basicOpen_res]`. Establish `hgV : X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f) ≤ V` using `(X.basicOpen_le _).trans hbV`.

Establish `hres : X.presheaf.map (homOfLE hgV).op s = 0`. Use `map_eq_zero_of_app_ι_eq_zero W V _ s hs hgV ?_` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy` using `[hbg]`. Conclude with `hWf y hy.2`.

Use `hAaff.isLocalization_basicOpen (X.presheaf.map (homOfLE hAU₀).op f)` as an intermediate fact. Establish `hres' : algebraMap Γ(X, X.basicOpen b) Γ(X, X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f)) (X.presheaf.map (homOfLE hbV).op s) = 0`. Rewrite using `[algebraMap_basicOpen, map_homOfLE_map_homOfLE]`. Conclude with `hres`. Take `⟨m, hm⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers (X.presheaf.map (homOfLE hAU₀).op f)) Γ(X, X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f)) (X.presheaf.map (homOfLE hbV).op s)).mp hres'`.

Take `⟨n, hn⟩` from `m.2`. Establish `hmem : (m : Γ(X, X.basicOpen b)) ∈ nonZeroDivisors Γ(X, X.basicOpen b)`. Rewrite using `[← hn]`. Conclude with `pow_mem hgnzd n`. Use `(mem_nonZeroDivisors_iff.mp hmem).1 (X.presheaf.map (homOfLE hbV).op s) ?_` and prove the remaining obligations.

Conclude with `hm`.
-/
private theorem map_basicOpen_eq_zero_of_app_ι_eq_zero {X : Scheme.{u}} (W V U₀ : X.Opens)
    (hU₀ : IsAffineOpen U₀)
    (s : Γ(X, V)) (hs : (W.ι.app V).hom s = 0)
    (f : Γ(X, U₀)) (hf : f ∈ nonZeroDivisors Γ(X, U₀))
    (hWf : ∀ y : ↥X, y ∈ X.basicOpen f → y ∈ W)
    (b : Γ(X, U₀)) (hbV : X.basicOpen b ≤ V) :
    X.presheaf.map (homOfLE hbV).op s = 0 := by
  have hAaff : IsAffineOpen (X.basicOpen b) := hU₀.basicOpen b
  have := hU₀.isLocalization_basicOpen b
  have hAU₀ : X.basicOpen b ≤ U₀ := X.basicOpen_le b
  have hgnzd : X.presheaf.map (homOfLE hAU₀).op f ∈ nonZeroDivisors Γ(X, X.basicOpen b) := by
    have hq : X.presheaf.map (homOfLE hAU₀).op f
        = algebraMap Γ(X, U₀) Γ(X, X.basicOpen b) f := rfl
    rw [hq]
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers b) Γ(X, X.basicOpen b) hf
  have hbg : X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f)
      = X.basicOpen b ⊓ X.basicOpen f := by
    rw [Scheme.basicOpen_res]
  have hgV : X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f) ≤ V :=
    (X.basicOpen_le _).trans hbV
  have hres : X.presheaf.map (homOfLE hgV).op s = 0 := by
    refine map_eq_zero_of_app_ι_eq_zero W V _ s hs hgV ?_
    intro y hy
    rw [hbg] at hy
    exact hWf y hy.2
  have := hAaff.isLocalization_basicOpen (X.presheaf.map (homOfLE hAU₀).op f)
  have hres' : algebraMap Γ(X, X.basicOpen b)
      Γ(X, X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f))
      (X.presheaf.map (homOfLE hbV).op s) = 0 := by
    rw [algebraMap_basicOpen, map_homOfLE_map_homOfLE]
    exact hres
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (X.presheaf.map (homOfLE hAU₀).op f))
    Γ(X, X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f))
    (X.presheaf.map (homOfLE hbV).op s)).mp hres'
  obtain ⟨n, hn⟩ := m.2
  have hmem : (m : Γ(X, X.basicOpen b)) ∈ nonZeroDivisors Γ(X, X.basicOpen b) := by
    rw [← hn]
    exact pow_mem hgnzd n
  refine (mem_nonZeroDivisors_iff.mp hmem).1 (X.presheaf.map (homOfLE hbV).op s) ?_
  exact hm

/- English proof (translation)
Use `le_antisymm (fun U => ?_) bot_le` and prove the remaining obligations. Introduce `s hs`. Establish `hs' : s ∈ RingHom.ker ((Scheme.Opens.ι (X` using `X) I.support.compl).app U.1).hom := Scheme.IdealSheafData.ideal_ofIdeals_le _ U hs`. Rewrite using `[show (⊥ : X.IdealSheafData).ideal U = ⊥ from by simp, Ideal.mem_bot]`. Use `EmbeddedResolution.section_eq_zero_of_locally_zero U.1 s ?_` and prove the remaining obligations.

Introduce `x hx`. Take `⟨U₀, f, hxU₀, hfnzd, hIf⟩` from `h x`. Take `⟨a, b, hab, hxa⟩` from `exists_basicOpen_le_affine_inter U.2 U₀.2 x ⟨hx, hxU₀⟩`. Establish `hbV : X.basicOpen b ≤ U.1` using `hab ▸ X.basicOpen_le a`. Use `⟨X.basicOpen b, hbV, hab ▸ hxa, ?_⟩` and prove the remaining obligations.

Use `_root_.FunctorialResolution.EmbeddedResolution.map_basicOpen_eq_zero_of_app_ι_eq_zero I.support.compl U.1 U₀.1 U₀.2 s (RingHom.mem_ker.mp hs') f hfnzd ?_ b hbV` and prove the remaining obligations. Introduce `y hy`. Use `show y ∉ I.support`. Use `_root_.FunctorialResolution.EmbeddedResolution.notMem_support_of_mem_basicOpen I U₀ f ?_ y hy` and prove the remaining obligations. Rewrite using `[hIf]`.

Conclude with `Ideal.mem_span_singleton_self f`.
-/
theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.ker_supportCompl_ι_eq_bot {X : Scheme.{u}} {I : X.IdealSheafData}
    (h : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor I) :
    (Scheme.Opens.ι (X := X) I.support.compl).ker = ⊥ := by
  refine le_antisymm (fun U => ?_) bot_le
  intro s hs
  have hs' : s ∈ RingHom.ker ((Scheme.Opens.ι (X := X) I.support.compl).app U.1).hom :=
    Scheme.IdealSheafData.ideal_ofIdeals_le _ U hs
  rw [show (⊥ : X.IdealSheafData).ideal U = ⊥ from by simp, Ideal.mem_bot]
  refine EmbeddedResolution.section_eq_zero_of_locally_zero U.1 s ?_
  intro x hx
  obtain ⟨U₀, f, hxU₀, hfnzd, hIf⟩ := h x
  obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter U.2 U₀.2 x ⟨hx, hxU₀⟩
  have hbV : X.basicOpen b ≤ U.1 := hab ▸ X.basicOpen_le a
  refine ⟨X.basicOpen b, hbV, hab ▸ hxa, ?_⟩
  refine _root_.FunctorialResolution.EmbeddedResolution.map_basicOpen_eq_zero_of_app_ι_eq_zero I.support.compl U.1 U₀.1 U₀.2 s
    (RingHom.mem_ker.mp hs') f hfnzd ?_ b hbV
  intro y hy
  show y ∉ I.support
  refine _root_.FunctorialResolution.EmbeddedResolution.notMem_support_of_mem_basicOpen I U₀ f ?_ y hy
  rw [hIf]
  exact Ideal.mem_span_singleton_self f

/- English proof (translation)
Use `isIso_subschemeι_comap_bot π` as an intermediate fact. Rewrite using `[Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq]`. Conclude with `(ker_preimage_ι_comp_of_isIso _ _).trans h.1.ker_supportCompl_ι_eq_bot`.
-/
theorem strictTransform_bot_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}} {π : X' ⟶ X}
    {I : X.IdealSheafData} (h : Blowup.IsBlowupAlongIdealSheaf π I) :
    Blowup.strictTransform π I (⊥ : X.IdealSheafData) = (⊥ : X'.IdealSheafData) := by
  have := isIso_subschemeι_comap_bot π
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq]
  exact (ker_preimage_ι_comp_of_isIso _ _).trans h.1.ker_supportCompl_ι_eq_bot

/- English proof (translation)
Take `⟨hlen, σ, hσ0, hsq, hc⟩` from `h`. Establish `hiso : ∀ (i : ℕ) (hi : i ≤ B'.length), IsIso (σ i hi)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`.

Introduce `hi`. Establish `hz : σ 0 hi = B'.isoZero.hom ≫ φ ≫ B.isoZero.inv`. Rewrite using `[← Category.assoc, ← hσ0]`. Simplify using the standard rewrite rules. Rewrite using `[hz]`.

Use `infer_instance`. Consider the case `succ n ih`. Introduce `hi`. Establish `hn : n < B'.length` using `hi`. Use `ih hn.le` as an intermediate fact.

Conclude with `(hsq n hn).isIso_fst_of_isIso`. Use `⟨hlen, σ, ?_, hσ0, fun i hi => (hsq i hi).w, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Use `hiso i hi` as an intermediate fact. Use `infer_instance`.

Introduce `i hi`. Use `hiso i hi.le` as an intermediate fact. Rewrite using `[hc i hi, imageIdealSheaf_comap]`. Introduce `i hi`. Establish `hi' : i < B.length` using `hlen ▸ hi`.

Use `hiso i hi.le` as an intermediate fact. Use `hiso (i + 1) hi` as an intermediate fact. Rewrite using `[Scheme.Hom.ker_eq_bot_of_isIso, Scheme.Hom.ker_eq_bot_of_isIso, strictTransform_bot_of_isBlowupAlongIdealSheaf (B.isBlowupAlongIdealSheaf_blowupMorphism i hi')]`.
-/
theorem IsPushforwardBlowupSeq.of_isStrictPullback_of_isIso {X' X : Scheme.{u}} (φ : X' ⟶ X)
    [IsIso φ] [IsClosedImmersion φ] {B' : SequenceOfBlowups X'} {B : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq φ B' B) : IsPushforwardBlowupSeq φ B' B := by
  obtain ⟨hlen, σ, hσ0, hsq, hc⟩ := h
  have hiso : ∀ (i : ℕ) (hi : i ≤ B'.length), IsIso (σ i hi) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hz : σ 0 hi = B'.isoZero.hom ≫ φ ≫ B.isoZero.inv := by
          rw [← Category.assoc, ← hσ0]
          simp
        rw [hz]
        infer_instance
    | succ n ih =>
        intro hi
        have hn : n < B'.length := hi
        have := ih hn.le
        exact (hsq n hn).isIso_fst_of_isIso
  refine ⟨hlen, σ, ?_, hσ0, fun i hi => (hsq i hi).w, ?_, ?_⟩
  · intro i hi
    have := hiso i hi
    infer_instance
  · intro i hi
    have := hiso i hi.le
    rw [hc i hi, imageIdealSheaf_comap]
  · intro i hi
    have hi' : i < B.length := hlen ▸ hi
    have := hiso i hi.le
    have := hiso (i + 1) hi
    rw [Scheme.Hom.ker_eq_bot_of_isIso, Scheme.Hom.ker_eq_bot_of_isIso,
      strictTransform_bot_of_isBlowupAlongIdealSheaf (B.isBlowupAlongIdealSheaf_blowupMorphism i hi')]

end FunctorialResolution.EmbeddedResolution

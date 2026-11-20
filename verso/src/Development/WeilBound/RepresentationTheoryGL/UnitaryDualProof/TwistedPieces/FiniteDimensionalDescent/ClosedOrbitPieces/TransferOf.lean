import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.OneFormsMapOfFunctorMorphismSmul

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc.Piece.Tr PositivityTheory.RgUd.TP.Desc.Piece.PTop
open PositivityTheory.PfBern.Loc (SC restr restr_surjective pullL mulInd)
open PositivityTheory.PfBern.Frob (FrobeniusReciprocity IsUnimod eqvF translF Fib fibSmul)

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def actH {N : ℕ} (g : GL (Fin N) k) : Sp k N ≃ₜ Sp k N where
  toFun := act g
  invFun := act g⁻¹
  left_inv q := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv q := by rw [← act_mul, mul_inv_cancel, act_one]
  continuous_toFun := Continuous.actc continuous_const continuous_id
  continuous_invFun := Continuous.actc continuous_const continuous_id

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `hDT hOH hOC hFr p _ _ hU N q Z hZ χ D τ x₀ hx₀ hV ξ hsupp hinv f hf`. Use `haveI : T2Space k := t2k`. Use `haveI : TotallyDisconnectedSpace k := tdk`. Use `haveI : SecondCountableTopology k := sck`. Use `haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) := tdM`.

Use `haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) k) := inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → k))`. Use `haveI : SecondCountableTopology (GL (Fin N) k) := GlobalTheory.SplitFlip.secondCountable_GL`. Use `letI : MeasurableSpace (GL (Fin N) k) := borel _`. Use `haveI : BorelSpace (GL (Fin N) k) := ⟨rfl⟩`. Establish `hP` using `pieceTop k N q Z hZ χ D τ`.

Establish `hCR : CR (Sx D x₀)` using `hP.2.2 x₀ hx₀`. Establish `hB0 : x₀ ∈ Bz Z` using `hx₀.1`. Establish `hχ0 : aeval x₀ χ = 0` using `hx₀.2.1`. Take `⟨e₁, he₁⟩` from `exists_orb_homeo hOC hZ D.hz`. Take `⟨e₂, he₂⟩` from `exists_orb_homeo hOC hCR (sx_span D hB0 hχ0)`.

Establish `hYc : IsClosed (Ys D τ)` using `isClosed_Ys D hOC hZ τ hP.2.1`. Use `haveI : LocallyCompactSpace (Ys D τ) := hYc.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `hp₁` using `oneFormsMapOfFunctorMorphism_smul (τ := τ) he₁`. Establish `hp₂` using `second_orbit_map_equivariant (τ := τ) (hOH := hOH) (hZ := hZ) (hx₀ := hx₀) he₂`. Set `C : Set (Ys D τ)` to `{y | y.1.2.2 = 0}`.

Establish `hCc : IsClosed C` using `isClosed_eq (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)) continuous_const`. Establish `hCinv : ∀ (g : GL (Fin N) k), ∀ y ∈ C, g • y ∈ C`. Introduce `g y hy`. Express the relevant statement in the definitionally equal form `g.val *ᵥ y.1.2.2 = 0`. Rewrite using `[show y.1.2.2 = 0 from hy, Matrix.mulVec_zero]`.

Establish `hyp : ∀ E ∈ eqvF hp₂ ((1 : GL (Fin N) k →* ℂˣ).comp (GzS (Sx D x₀)).subtype), PositivityTheory.PfBern.Frob.SupportedIn E (Subtype.val ⁻¹' C)`. Introduce `E hEeqv φ0 hφ0`. Set `hY` to `hY2 (hOH := hOH) (hZ := hZ) (hx₀ := hx₀) he₂`. Establish `hY2c : IsClosed (Ys2 D τ x₀)` using `isClosed_second_fibre_set hOC hZ x₀`. Set `E' : PositivityTheory.PfBern.Loc.Distr (Ys2 D τ x₀)` to `E.comp (pullL hY)`.

Take `⟨η, hη⟩` from `exists_functional hY2c E'`. Establish `hSη : Supp η (Bz (Sx D x₀) ×ˢ Set.univ)`. Introduce `f hf1 hvan`. Establish `hr : restr hY2c ⟨f, hf1.1⟩ = 0` using `Subtype.ext (funext fun y => hvan y.1 (Ys2_sub hB0 hχ0 y.2))`. Use `hη ⟨f, hf1.1⟩` as an intermediate fact.

Rewrite `this` using `[hr, map_zero]`. Conclude with `this`. Establish `hIη : Inv (Sx D x₀) η`. Introduce `h hh f hf1`. Set `hH : GzS (Sx D x₀)` to `⟨h, hh⟩`.

Set `f1 : SC (Sp k N)` to `pullL (actH k h) ⟨f, hf1.1⟩`. Establish `key : pullL hY (restr hY2c f1) = translF hp₂ hH⁻¹ (pullL hY (restr hY2c ⟨f, hf1.1⟩))`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Express the relevant statement in the definitionally equal form `f (act h (hY z).1) = f (hY (fibSmul hp₂ hH⁻¹⁻¹ z)).1`.

Rewrite using `[second_fibre_homeomorph_smul he₂, inv_inv]`. Establish `h1 : η (fun q => f (act h q)) = η f1` using `rfl`. Rewrite using `[h1, hη f1, hη ⟨f, hf1.1⟩]`. Express the relevant statement in the definitionally equal form `E (pullL hY (restr hY2c f1)) = E (pullL hY (restr hY2c ⟨f, hf1.1⟩))`. Rewrite using `[key]`.

Conclude with `(hEeqv hH⁻¹ _).trans (by simp)`. Establish `hkill` using `hV η hSη hIη`. Set `φ' : SC (Ys2 D τ x₀)` to `pullL hY.symm φ0`. Take `⟨f0, hf0⟩` from `restr_surjective hY2c φ'`. Establish `hsupp' : Function.support (φ' : Ys2 D τ x₀ → ℂ) ⊆ {y | y.1.2 ≠ 0}` using `fun y hy => hφ0 hy`.

Establish `hK : IsCompact (Subtype.val '' Function.support (φ' : Ys2 D τ x₀ → ℂ))` using `(isCompact_support φ'.2).image continuous_subtype_val`. Establish `hKsub : Subtype.val '' Function.support (φ' : Ys2 D τ x₀ → ℂ) ⊆ {q : Sp k N | q.2 ≠ 0}`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hsupp' hy`. Establish `hUo : IsOpen {q : Sp k N | q.2 ≠ 0}` using `isOpen_ne_fun continuous_snd continuous_const`.

Take `⟨Bc, hBc, hBo, hKB, hBU⟩` from `exists_isCompact_isOpen_between hK hUo hKsub`. Set `f : SC (Sp k N)` to `mulInd Bc ⟨hBc.isClosed, hBo⟩ f0`. Establish `hrf : restr hY2c f = φ'`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `y`.

Express the relevant statement in the definitionally equal form `Bc.indicator 1 y.1 * (f0 : Sp k N → ℂ) y.1 = (φ' : Ys2 D τ x₀ → ℂ) y`. Establish `e0 : (f0 : Sp k N → ℂ) y.1 = (φ' : Ys2 D τ x₀ → ℂ) y` using `congrFun (congrArg Subtype.val hf0) y`. Distinguish the cases in `hyB : y.1 ∈ Bc`. Simplify using `[hyB, e0]`. Establish `: (φ' : Ys2 D τ x₀ → ℂ) y = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `hyB (hKB ⟨y, hne, rfl⟩)`. Simplify using `[hyB, this]`. Establish `hfU : (f : Sp k N → ℂ) ∈ supportedIn {q : Sp k N | q.2 ≠ 0}`. Use `⟨f.2, fun q hq => hBU ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hqB`. Conclude with `hq (by simp [f, mulInd, hqB])`. Establish `hz` using `hkill f hfU`. Rewrite `hz` using `[hη f, hrf]`. Establish `e2 : pullL hY φ' = φ0` using `PositivityTheory.PfBern.Loc.pullL_pullL_symm hY φ0`.

Express the relevant statement in the definitionally equal form `E (pullL hY φ') = 0 at hz`. Rewrite `hz` using `[e2]`. Conclude with `hz`. Establish `hPc : IsClosed (piece D τ ×ˢ (Set.univ : Set (Fin N → k)))` using `hP.1.prod isClosed_univ`. Take `⟨Dd, hDd⟩` from `exists_distr_on ξ hPc hsupp`.

Set `hY1'` to `hY1 (τ := τ) e₁ he₁ hZ`. Set `E₁ : PositivityTheory.PfBern.Frob.Distr (Fib (p1 D τ e₁))` to `Dd.comp (pullL hY1'.symm)`. Establish `hE₁ : E₁ ∈ eqvF hp₁ ((1 : GL (Fin N) k →* ℂˣ).comp (GzS Z).subtype)`. Introduce `h φ`. Take `⟨f0, hf0⟩` from `restr_surjective hPc (pullL hY1'.symm φ)`.

Establish `hφ : ∀ w, (φ : Fib (p1 D τ e₁) → ℂ) w = (f0 : Sp k N → ℂ) (hY1' w).1` using `fun w => by`. Use `congrFun (congrArg Subtype.val hf0) (hY1' w)` as an intermediate fact. Express the relevant statement in the definitionally equal form `(f0 : Sp k N → ℂ) (hY1' w).1 = (φ : Fib (p1 D τ e₁) → ℂ) (hY1'.symm (hY1' w)) at this`. Rewrite `this` using `[Homeomorph.symm_apply_apply]`. Conclude with `this.symm`.

Set `f1 : SC (Sp k N)` to `pullL (actH k (h⁻¹).1) f0`. Establish `e1 : pullL hY1'.symm (translF hp₁ h φ) = restr hPc f1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `y`. Express the relevant statement in the definitionally equal form `(φ : Fib (p1 D τ e₁) → ℂ) (fibSmul hp₁ h⁻¹ (hY1'.symm y)) = (f0 : Sp k N → ℂ) (act (h⁻¹).1 y.1)`.

Rewrite using `[hφ, first_fibre_homeomorph_smul he₁ hZ, Homeomorph.apply_symm_apply]`. Simplify using `only [MonoidHom.comp_apply, MonoidHom.one_apply, Units.val_one, one_mul]`. Express the relevant statement in the definitionally equal form `Dd (pullL hY1'.symm (translF hp₁ h φ)) = Dd (pullL hY1'.symm φ)`. Rewrite using `[e1, ← hf0, ← hDd f1, ← hDd f0]`. Conclude with `hinv (h⁻¹).1 (h⁻¹).2 f0 ⟨f0.2, Set.subset_univ _⟩`.

Establish `hSupp` using `hDT hFr (GL (Fin N) k) (GzS Z) (GzS (Sx D x₀)) (isClosed_GzS Z) (isClosed_GzS _) (isUnimod_GL hU) (hU N Z hZ) (hU N _ hCR) (Ys D τ) (p1 D τ e₁) (p2 D τ hOH hZ hx₀ e₂) (continuous_first_orbit_map he₁) continuous_p2 hp₁ hp₂ C hCc hCinv hyp E₁ hE₁`. Establish `hz` using `hSupp (pullL hY1' (restr hPc ⟨f, hf.1⟩)) fun w hw hwC => hw (by`. Express the relevant statement in the definitionally equal form `f w.1.1.2 = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hf.2 hne hwC)`.

Rewrite using `[show ξ f = Dd (restr hPc ⟨f, hf.1⟩) from hDd ⟨f, hf.1⟩, ← PositivityTheory.PfBern.Loc.pullL_pullL_symm hY1'.symm (restr hPc ⟨f, hf.1⟩)]`. Conclude with `hz`.
-/
theorem transfer_of : (PositivityTheory.PfBern.Frob.FrobeniusReciprocity → DoubleTransfer) → OrbHom k → OrbClosed k → Transfer k := by
  intro hDT hOH hOC hFr p _ _ hU N q Z hZ χ D τ x₀ hx₀ hV ξ hsupp hinv f hf
  haveI : T2Space k := t2k
  haveI : TotallyDisconnectedSpace k := tdk
  haveI : SecondCountableTopology k := sck
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) := tdM
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) k) := inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → k))
  haveI : SecondCountableTopology (GL (Fin N) k) := GlobalTheory.SplitFlip.secondCountable_GL
  letI : MeasurableSpace (GL (Fin N) k) := borel _
  haveI : BorelSpace (GL (Fin N) k) := ⟨rfl⟩
  have hP := pieceTop k N q Z hZ χ D τ
  have hCR : CR (Sx D x₀) := hP.2.2 x₀ hx₀
  have hB0 : x₀ ∈ Bz Z := hx₀.1
  have hχ0 : aeval x₀ χ = 0 := hx₀.2.1
  obtain ⟨e₁, he₁⟩ := exists_orb_homeo hOC hZ D.hz
  obtain ⟨e₂, he₂⟩ := exists_orb_homeo hOC hCR (sx_span D hB0 hχ0)
  have hYc : IsClosed (Ys D τ) := isClosed_Ys D hOC hZ τ hP.2.1
  haveI : LocallyCompactSpace (Ys D τ) := hYc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hp₁ := oneFormsMapOfFunctorMorphism_smul (τ := τ) he₁
  have hp₂ := second_orbit_map_equivariant (τ := τ) (hOH := hOH) (hZ := hZ) (hx₀ := hx₀) he₂
  let C : Set (Ys D τ) := {y | y.1.2.2 = 0}
  have hCc : IsClosed C := isClosed_eq (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)) continuous_const
  have hCinv : ∀ (g : GL (Fin N) k), ∀ y ∈ C, g • y ∈ C := by
    intro g y hy
    change g.val *ᵥ y.1.2.2 = 0
    rw [show y.1.2.2 = 0 from hy, Matrix.mulVec_zero]

  have hyp : ∀ E ∈ eqvF hp₂ ((1 : GL (Fin N) k →* ℂˣ).comp (GzS (Sx D x₀)).subtype),
      PositivityTheory.PfBern.Frob.SupportedIn E (Subtype.val ⁻¹' C) := by
    intro E hEeqv φ0 hφ0
    let hY := hY2 (hOH := hOH) (hZ := hZ) (hx₀ := hx₀) he₂
    have hY2c : IsClosed (Ys2 D τ x₀) := isClosed_second_fibre_set hOC hZ x₀
    let E' : PositivityTheory.PfBern.Loc.Distr (Ys2 D τ x₀) := E.comp (pullL hY)
    obtain ⟨η, hη⟩ := exists_functional hY2c E'
    have hSη : Supp η (Bz (Sx D x₀) ×ˢ Set.univ) := by
      intro f hf1 hvan
      have hr : restr hY2c ⟨f, hf1.1⟩ = 0 := Subtype.ext (funext fun y => hvan y.1 (Ys2_sub hB0 hχ0 y.2))
      have := hη ⟨f, hf1.1⟩
      rw [hr, map_zero] at this
      exact this
    have hIη : Inv (Sx D x₀) η := by
      intro h hh f hf1
      let hH : GzS (Sx D x₀) := ⟨h, hh⟩
      let f1 : SC (Sp k N) := pullL (actH k h) ⟨f, hf1.1⟩
      have key : pullL hY (restr hY2c f1) = translF hp₂ hH⁻¹ (pullL hY (restr hY2c ⟨f, hf1.1⟩)) := by
        apply Subtype.ext
        funext z
        change f (act h (hY z).1) = f (hY (fibSmul hp₂ hH⁻¹⁻¹ z)).1
        rw [second_fibre_homeomorph_smul he₂, inv_inv]
      have h1 : η (fun q => f (act h q)) = η f1 := rfl
      rw [h1, hη f1, hη ⟨f, hf1.1⟩]
      change E (pullL hY (restr hY2c f1)) = E (pullL hY (restr hY2c ⟨f, hf1.1⟩))
      rw [key]
      exact (hEeqv hH⁻¹ _).trans (by simp)
    have hkill := hV η hSη hIη
    let φ' : SC (Ys2 D τ x₀) := pullL hY.symm φ0
    obtain ⟨f0, hf0⟩ := restr_surjective hY2c φ'
    have hsupp' : Function.support (φ' : Ys2 D τ x₀ → ℂ) ⊆ {y | y.1.2 ≠ 0} := fun y hy => hφ0 hy
    have hK : IsCompact (Subtype.val '' Function.support (φ' : Ys2 D τ x₀ → ℂ)) :=
      (isCompact_support φ'.2).image continuous_subtype_val
    have hKsub : Subtype.val '' Function.support (φ' : Ys2 D τ x₀ → ℂ) ⊆ {q : Sp k N | q.2 ≠ 0} := by
      rintro _ ⟨y, hy, rfl⟩
      exact hsupp' hy
    have hUo : IsOpen {q : Sp k N | q.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
    obtain ⟨Bc, hBc, hBo, hKB, hBU⟩ := exists_isCompact_isOpen_between hK hUo hKsub
    let f : SC (Sp k N) := mulInd Bc ⟨hBc.isClosed, hBo⟩ f0
    have hrf : restr hY2c f = φ' := by
      apply Subtype.ext
      funext y
      change Bc.indicator 1 y.1 * (f0 : Sp k N → ℂ) y.1 = (φ' : Ys2 D τ x₀ → ℂ) y
      have e0 : (f0 : Sp k N → ℂ) y.1 = (φ' : Ys2 D τ x₀ → ℂ) y := congrFun (congrArg Subtype.val hf0) y
      by_cases hyB : y.1 ∈ Bc
      · simp [hyB, e0]
      · have : (φ' : Ys2 D τ x₀ → ℂ) y = 0 := by
          by_contra hne
          exact hyB (hKB ⟨y, hne, rfl⟩)
        simp [hyB, this]
    have hfU : (f : Sp k N → ℂ) ∈ supportedIn {q : Sp k N | q.2 ≠ 0} := by
      refine ⟨f.2, fun q hq => hBU ?_⟩
      by_contra hqB
      exact hq (by simp [f, mulInd, hqB])
    have hz := hkill f hfU
    rw [hη f, hrf] at hz
    have e2 : pullL hY φ' = φ0 := PositivityTheory.PfBern.Loc.pullL_pullL_symm hY φ0
    change E (pullL hY φ') = 0 at hz
    rw [e2] at hz
    exact hz

  have hPc : IsClosed (piece D τ ×ˢ (Set.univ : Set (Fin N → k))) := hP.1.prod isClosed_univ
  obtain ⟨Dd, hDd⟩ := exists_distr_on ξ hPc hsupp
  let hY1' := hY1 (τ := τ) e₁ he₁ hZ
  let E₁ : PositivityTheory.PfBern.Frob.Distr (Fib (p1 D τ e₁)) := Dd.comp (pullL hY1'.symm)
  have hE₁ : E₁ ∈ eqvF hp₁ ((1 : GL (Fin N) k →* ℂˣ).comp (GzS Z).subtype) := by
    intro h φ
    obtain ⟨f0, hf0⟩ := restr_surjective hPc (pullL hY1'.symm φ)
    have hφ : ∀ w, (φ : Fib (p1 D τ e₁) → ℂ) w = (f0 : Sp k N → ℂ) (hY1' w).1 := fun w => by
      have := congrFun (congrArg Subtype.val hf0) (hY1' w)
      change (f0 : Sp k N → ℂ) (hY1' w).1 = (φ : Fib (p1 D τ e₁) → ℂ) (hY1'.symm (hY1' w)) at this
      rw [Homeomorph.symm_apply_apply] at this
      exact this.symm
    let f1 : SC (Sp k N) := pullL (actH k (h⁻¹).1) f0
    have e1 : pullL hY1'.symm (translF hp₁ h φ) = restr hPc f1 := by
      apply Subtype.ext
      funext y
      change (φ : Fib (p1 D τ e₁) → ℂ) (fibSmul hp₁ h⁻¹ (hY1'.symm y)) = (f0 : Sp k N → ℂ) (act (h⁻¹).1 y.1)
      rw [hφ, first_fibre_homeomorph_smul he₁ hZ, Homeomorph.apply_symm_apply]
    simp only [MonoidHom.comp_apply, MonoidHom.one_apply, Units.val_one, one_mul]
    change Dd (pullL hY1'.symm (translF hp₁ h φ)) = Dd (pullL hY1'.symm φ)
    rw [e1, ← hf0, ← hDd f1, ← hDd f0]
    exact hinv (h⁻¹).1 (h⁻¹).2 f0 ⟨f0.2, Set.subset_univ _⟩
  have hSupp := hDT hFr (GL (Fin N) k) (GzS Z) (GzS (Sx D x₀)) (isClosed_GzS Z) (isClosed_GzS _) (isUnimod_GL hU)
    (hU N Z hZ) (hU N _ hCR) (Ys D τ) (p1 D τ e₁) (p2 D τ hOH hZ hx₀ e₂) (continuous_first_orbit_map he₁) continuous_p2 hp₁ hp₂
    C hCc hCinv hyp E₁ hE₁
  have hz := hSupp (pullL hY1' (restr hPc ⟨f, hf.1⟩)) fun w hw hwC => hw (by
    change f w.1.1.2 = 0
    by_contra hne
    exact hf.2 hne hwC)
  rw [show ξ f = Dd (restr hPc ⟨f, hf.1⟩) from hDd ⟨f, hf.1⟩,
    ← PositivityTheory.PfBern.Loc.pullL_pullL_symm hY1'.symm (restr hPc ⟨f, hf.1⟩)]
  exact hz

end PositivityTheory.RgUd.TP.Desc.Piece.TrI

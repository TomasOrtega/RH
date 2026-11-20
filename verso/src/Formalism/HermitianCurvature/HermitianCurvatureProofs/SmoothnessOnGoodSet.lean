import Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichRhoAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartIntegralLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
Introduce `_ _` and use `⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩`.
-/
lemma ckOn_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ∞) :
    CkOn m (GV k r) (fun _ : Mat k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

/- English proof (translation)
Establish `hR : ∀ w : List (Mat k r), Rw w (fun _ : Mat k r => (0 : E)) = fun _ => 0`. Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons X w ih => show RdV X (Rw w _) = _`.

Rewrite using `[ih]`. Use function extensionality and compare the values at `g`. Simplify using `only [RdV, deriv_const']`. Proceed by induction on `u with`. Consider the case `nil => exact hR v`.

Consider the case `cons X u ih => show LdV X (dLR u v _) = _`. Rewrite using `[ih]`. Use function extensionality and compare the values at `g`. Simplify using `only [LdV, deriv_const']`.
-/
lemma dLR_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (u v : List (Mat k r)) :
    dLR u v (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
  have hR : ∀ w : List (Mat k r), Rw w (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
    intro w
    induction w with
    | nil => rfl
    | cons X w ih =>
      show RdV X (Rw w _) = _
      rw [ih]
      funext g
      simp only [RdV, deriv_const']
  induction u with
  | nil => exact hR v
  | cons X u ih =>
    show LdV X (dLR u v _) = _
    rw [ih]
    funext g
    simp only [LdV, deriv_const']

/- English proof (translation)
Unfold `psi`. Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules.
-/
lemma norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mat k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [Complex.norm_exp]
  simp

/- English proof (translation)
Establish `e : Formalism.FourierDecayAlt.Q.OmPlus k r z z' = (⋂ l : Fin (r + 2), {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0}) ∩ {g | 0 < Gf k r z z' g}`. Use extensionality with `g`. Simplify using `[Formalism.FourierDecayAlt.Q.OmPlus]`. Rewrite using `[e]`. Use `(isOpen_iInter_of_finite fun l => ?_).inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z'))` and prove the remaining obligations.

Distinguish the cases in `hl : l.val ≤ r`. Establish `e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = {g | Dmin k r z z' g l ≠ 0}`. Use extensionality with `g`. Simplify using `[hl]`. Rewrite using `[e2]`.

Conclude with `isOpen_ne_fun (Formalism.FourierDecayAlt.P.Ux8.cont_Dmin k r z z' l) continuous_const`. Establish `e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = Set.univ`. Use extensionality with `g`. Simplify using `[hl]`. Rewrite using `[e2]`.

Conclude with `isOpen_univ`.
-/
lemma isOpen_OmPlus (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Formalism.FourierDecayAlt.Q.OmPlus k r z z') := by
  have e : Formalism.FourierDecayAlt.Q.OmPlus k r z z' =
      (⋂ l : Fin (r + 2), {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0}) ∩ {g | 0 < Gf k r z z' g} := by
    ext g; simp [Formalism.FourierDecayAlt.Q.OmPlus]
  rw [e]
  refine (isOpen_iInter_of_finite fun l => ?_).inter
    (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z'))
  by_cases hl : l.val ≤ r
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = {g | Dmin k r z z' g l ≠ 0} := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_ne_fun (Formalism.FourierDecayAlt.P.Ux8.cont_Dmin k r z z' l) continuous_const
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = Set.univ := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_univ

/- English proof (translation)
Consider the cases of `b`. Conclude with `(Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous`. Establish `h` using `(Formalism.FourierDecayAlt.P.B5.curve_contDiff (1 : Mat k r) (-X)).continuous`. Establish `h2` using `(continuous_mul_const g).comp h`. Use `h2.congr fun t => ?_` and prove the remaining obligations.

Simplify using `[cv, smul_neg]`.
-/
lemma cv_continuous (b : Bool) (X g : Mat k r) : Continuous fun t : ℝ => cv b X t g := by
  cases b
  · exact (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  · have h := (Formalism.FourierDecayAlt.P.B5.curve_contDiff (1 : Mat k r) (-X)).continuous
    have h2 := (continuous_mul_const g).comp h
    refine h2.congr fun t => ?_
    simp [cv, smul_neg]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Unfold `xiP`. Simplify using `[norm_psi]`.
-/
lemma norm_xiP (D : RealPlaceData k r Wp Wq) (p : SS k r) : ‖xiP D p‖ ≤ 1 := by
  unfold xiP
  simp [norm_psi]

/- English proof (translation)
Establish `key : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => ell k r z (Matrix.of M)`. Introduce `z`. Unfold `ell`. Use `continuous_finset_sum _ fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : a.val + 1 < r`.

Simplify using `only [h, ↓reduceDIte, Matrix.of_apply]`. Conclude with `(continuous_apply _).comp (continuous_apply _)`. Simplify using `only [h, ↓reduceDIte, Matrix.mulVec, dotProduct, Matrix.of_apply]`. Use `continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Use `first`.

Consider the case `fun_prop`. Consider the case `exact (((continuous_apply j).comp (continuous_apply (eI k r a))).mul continuous_const :)`. Consider the case `continuity`. Establish `hpsi : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => psi k r z cStd (Matrix.of M)`. Introduce `z`.

Unfold `psi`. Conclude with `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul (key z)))))`. Unfold `xiP`. Conclude with `((hpsi D.z).comp (continuous_snd.comp continuous_fst)).mul (continuous_star.comp ((hpsi D.z').comp (continuous_snd.comp continuous_snd)))`.
-/
lemma continuous_xiP (D : RealPlaceData k r Wp Wq) : Continuous (xiP D) := by
  have key : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => ell k r z (Matrix.of M) := by
    intro z
    unfold ell
    refine continuous_finset_sum _ fun a _ => ?_
    by_cases h : a.val + 1 < r
    · simp only [h, ↓reduceDIte, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [h, ↓reduceDIte, Matrix.mulVec, dotProduct, Matrix.of_apply]
      refine continuous_finset_sum _ fun j _ => ?_
      first
        | fun_prop
        | exact (((continuous_apply j).comp (continuous_apply (eI k r a))).mul continuous_const :)
        | continuity
  have hpsi : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => psi k r z cStd (Matrix.of M) := by
    intro z
    unfold psi
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (key z)))))
  unfold xiP
  exact ((hpsi D.z).comp (continuous_snd.comp continuous_fst)).mul
    (continuous_star.comp ((hpsi D.z').comp (continuous_snd.comp continuous_snd)))

/- English proof (translation)
Establish `ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r` using `WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hp.1.1) (WeylGroupFacts.uh_inv hp.2.1.1)`. Establish `hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r` using `WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1`. Establish `e : rho D p F = fun x => ((ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹))) (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1)))`. Use function extensionality and compare the values at `x`. Simplify using `only [rho, sgs, Matrix.mul_assoc]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Formalism.FourierDecayAlt.P.B5.ckOn_clm (Formalism.FourierDecayAlt.P.B5.ckOn_translate hF ha hb) _`.
-/
lemma ckOn_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ∞} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn m (GV k r) F) : CkOn m (GV k r) (rho D p F) := by
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r :=
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hp.1.1) (WeylGroupFacts.uh_inv hp.2.1.1)
  have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1
  have e : rho D p F = fun x => ((ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹)))
      (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))) := by
    funext x
    simp only [rho, sgs, Matrix.mul_assoc]
    rfl
  rw [e]
  exact Formalism.FourierDecayAlt.P.B5.ckOn_clm (Formalism.FourierDecayAlt.P.B5.ckOn_translate hF ha hb) _

/- English proof (translation)
Rewrite using `[dLR_eq]`. Conclude with `smooth_on_of_word_derivatives _ (allLie_lr hu hv) j (ckOn_mono (by rw [length_lr]; omega) (ckOn_rho D hp hF))`.
-/
lemma ckOn_dLR_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {u v : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X)
    (hv : ∀ X ∈ v, unitLie k r X) (j : ℕ) (hl : j + (u.length + v.length) ≤ m) :
    CkOn ((j : ℕ) : ℕ∞) (GV k r) (dLR u v (rho D p F)) := by
  rw [dLR_eq]
  exact smooth_on_of_word_derivatives _ (allLie_lr hu hv) j (ckOn_mono (by rw [length_lr]; omega) (ckOn_rho D hp hF))

/- English proof (translation)
Use `haveI : TopologicalSpace.PseudoMetrizableSpace (Mat k r) := inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))`. Take `⟨S, hSK, hSc, hKS⟩` from `hK.isSeparable.exists_countable_dense_subset`. Use `haveI := hWS.to_subtype`. Use `haveI := hSc.to_subtype`. Establish `hall : ∀ᵐ p ∂D.μSS, ∀ i : WS × S, ‖rho D p (dLR (i.1.1.1.map (AdL p)) (i.1.1.2.map (AdR p)) F) i.2.1‖ ≤ b p` using `ae_all_iff.2 fun i => hb i.1.1 i.1.2 i.2.1 (hSK i.2.2)`.

Use `filter_upwards [hall, Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp hpS`. Use `⟨hpS, fun uv huv g hg => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `hWSl uv huv`. Establish `hcont : ContinuousOn (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) (GV k r)` using `(Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (ckOn_dLR_rho D hpS hF h1 h2 0 (by omega))).norm`. Establish `hcl : IsClosed (GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p))` using `hcont.preimage_isClosed_of_isClosed Formalism.FourierDecayAlt.P.B5.GV_closed isClosed_Iic`.

Establish `hS : S ⊆ GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p)`. Introduce `x hx`. Use `⟨hKG (hSK hx), ?_⟩` and prove the remaining obligations. Use `show ‖dLR uv.1 uv.2 (rho D p F) x‖ ≤ b p`. Rewrite using `[dLR_rho D hpS]`.

Conclude with `hp ⟨⟨uv, huv⟩, ⟨x, hx⟩⟩`. Conclude with `(hcl.closure_subset_iff.2 hS (hKS hg)).2`.
-/
lemma good_set (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F)
    {K : Set (Mat k r)} (hK : IsCompact K) (hKG : K ⊆ GV k r)
    {WS : Set (List (Mat k r) × List (Mat k r))} (hWS : WS.Countable)
    (hWSl : ∀ uv ∈ WS, (∀ X ∈ uv.1, unitLie k r X) ∧ (∀ X ∈ uv.2, unitLie k r X) ∧ uv.1.length + uv.2.length ≤ m)
    (b : SS k r → ℝ)
    (hb : ∀ uv ∈ WS, ∀ g ∈ K, ∀ᵐ p ∂D.μSS, ‖rho D p (dLR (uv.1.map (AdL p)) (uv.2.map (AdR p)) F) g‖ ≤ b p) :
    ∀ᵐ p ∂D.μSS, D.inSS p ∧ ∀ uv ∈ WS, ∀ g ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g‖ ≤ b p := by
  haveI : TopologicalSpace.PseudoMetrizableSpace (Mat k r) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨S, hSK, hSc, hKS⟩ := hK.isSeparable.exists_countable_dense_subset
  haveI := hWS.to_subtype
  haveI := hSc.to_subtype
  have hall : ∀ᵐ p ∂D.μSS, ∀ i : WS × S,
      ‖rho D p (dLR (i.1.1.1.map (AdL p)) (i.1.1.2.map (AdR p)) F) i.2.1‖ ≤ b p :=
    ae_all_iff.2 fun i => hb i.1.1 i.1.2 i.2.1 (hSK i.2.2)
  filter_upwards [hall, Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp hpS
  refine ⟨hpS, fun uv huv g hg => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hWSl uv huv
  have hcont : ContinuousOn (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) (GV k r) :=
    (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (ckOn_dLR_rho D hpS hF h1 h2 0 (by omega))).norm
  have hcl : IsClosed (GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p)) :=
    hcont.preimage_isClosed_of_isClosed Formalism.FourierDecayAlt.P.B5.GV_closed isClosed_Iic
  have hS : S ⊆ GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p) := by
    intro x hx
    refine ⟨hKG (hSK hx), ?_⟩
    show ‖dLR uv.1 uv.2 (rho D p F) x‖ ≤ b p
    rw [dLR_rho D hpS]
    exact hp ⟨⟨uv, huv⟩, ⟨x, hx⟩⟩
  exact (hcl.closure_subset_iff.2 hS (hKS hg)).2

/- English proof (translation)
Establish `hopen : IsOpen ((fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')` using `(isOpen_OmPlus _ _).preimage (cv_continuous b X g)`. Establish `h0 : (0 : ℝ) ∈ (fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z'` using `by show cv b X 0 g ∈ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z'`. Rewrite using `[cv_zero]`. Conclude with `hg.2`. Take `⟨ε1, hε1, hball⟩` from `Metric.isOpen_iff.1 hopen 0 h0`.

Establish `hg' : g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z'` using `hg`. Use `⟨ε1 / 2, by linarith, fun t ht => (⟨cv_mem hX hg'.1 t, hball ?_⟩ : cv b X t g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')⟩` and prove the remaining obligations. Rewrite `ht` using `[Metric.mem_closedBall]`. Rewrite using `[Metric.mem_ball]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma curve_ball (D : RealPlaceData k r Wp Wq) {g : Mat k r} (hg : g ∈ Om k r D.z D.z') (b : Bool) {X : Mat k r}
    (hX : inLie k r X) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, cv b X t g ∈ Om k r D.z D.z' := by
  have hopen : IsOpen ((fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') :=
    (isOpen_OmPlus _ _).preimage (cv_continuous b X g)
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := by
    show cv b X 0 g ∈ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z'
    rw [cv_zero]; exact hg.2
  obtain ⟨ε1, hε1, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  have hg' : g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := hg
  refine ⟨ε1 / 2, by linarith, fun t ht => (⟨cv_mem hX hg'.1 t, hball ?_⟩ : cv b X t g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')⟩
  rw [Metric.mem_closedBall] at ht
  rw [Metric.mem_ball]
  linarith

end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.BfDep
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.EvEqLc
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.ExtDerivDelG
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.ExtDerivCongrNhds
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.AltSmulRightComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.PosDefOfSphere

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB

namespace WhittakerCocycle

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

def actHom (L : Type) [Field L] [NumberField L] (N : ℕ) : Gm L N →* (HS L N →L[ℝ] HS L N) where
  toFun γ := actL (emb L N γ)
  map_one' := by
    refine ContinuousLinearMap.ext fun h => ?_
    rw [map_one, actL_one]
    rfl
  map_mul' a b := by
    refine ContinuousLinearMap.ext fun h => ?_
    rw [map_mul, actL_mul]
    rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem actHom_apply (γ : Gm L N) (h : HS L N) : actHom L N γ h = actL (emb L N γ) h := rfl

/- English proof (translation)
Rewrite using `[actHom_apply, map_inv]`.
-/
theorem actHom_inv (γ : Gm L N) (h : HS L N) : actHom L N γ⁻¹ h = actL (emb L N γ)⁻¹ h := by
  rw [actHom_apply, map_inv]

/- English proof (translation)
The claim follows from `(pos_open_convex L N).1 convex := (pos_open_convex L N).2 mapsTo g _ hh := actL_pos (emb L N g) hh smooth := P.smooth locFin := by have e : (fun γ : Gm L N => {h : Pos L N | P.φ (actHom L N γ⁻¹ h) ≠ 0}) = fun γ => {h : Pos L N | P.φ (actL (emb L N γ)⁻¹ h.1) ≠ 0} := by funext γ si …`.
-/
theorem hyp_of {Ht : Gp L N → ℝ} (P : PU L N Ht) : Hyp (Pos L N) (actHom L N) P.φ where
  isOpen := (pos_open_convex L N).1
  convex := (pos_open_convex L N).2
  mapsTo g _ hh := actL_pos (emb L N g) hh
  smooth := P.smooth
  locFin := by
    have e : (fun γ : Gm L N => {h : Pos L N | P.φ (actHom L N γ⁻¹ h) ≠ 0}) =
        fun γ => {h : Pos L N | P.φ (actL (emb L N γ)⁻¹ h.1) ≠ 0} := by
      funext γ
      simp only [actHom_inv]
    rw [e]
    exact P.locFin
  sum_one h hh := by
    simp only [actHom_inv]
    exact P.sum_one h hh

/- English proof (translation)
Unfold `intS`. Simplify using `only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]`. Conclude with `integral_const_mul _ _`.
-/
theorem intS_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ} (s : ℝ) (ω : Form V q)
    (y : Fin (q + 1) → V) : intS (s • ω) y = s * intS ω y := by
  unfold intS
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact integral_const_mul _ _

/- English proof (translation)
Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
theorem smul_comp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ} (s : ℝ)
    (f : V [⋀^Fin q]→L[ℝ] ℝ) (T : V →L[ℝ] V) :
    (s • f).compContinuousLinearMap T = s • f.compContinuousLinearMap T := by
  ext v
  simp

/- English proof (translation)
Rewrite using `[Pi.smul_apply, Pi.smul_apply, smul_comp, e]`.
-/
theorem finv_of {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ} (s : ℝ)
    (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (T : V →L[ℝ] V) (h : V)
    (e : (ω (T h)).compContinuousLinearMap T = ω h) :
    ((s • ω) (T h)).compContinuousLinearMap T = (s • ω) h := by
  rw [Pi.smul_apply, Pi.smul_apply, smul_comp, e]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem intS_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {q : ℕ} (ω : Form V q)
    (y : Fin (q + 1) → V) : intS ω y = intS' ω y := rfl

/- English proof (translation)
The claim follows from `((diffAt_of H.isOpen H.smooth hp).hasFDerivAt.comp p (A γ⁻¹).hasFDerivAt).fderiv`.
-/
theorem fderiv_psi' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]
    {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ} (H : Hyp U A φ) (γ : Γ) {p : V} (hp : A γ⁻¹ p ∈ U) :
    fderiv ℝ (psi A φ γ) p = (fderiv ℝ φ (A γ⁻¹ p)).comp (A γ⁻¹) :=
  ((diffAt_of H.isOpen H.smooth hp).hasFDerivAt.comp p (A γ⁻¹).hasFDerivAt).fderiv

end WhittakerCocycle

open WhittakerCocycle

/- English proof (translation)
Introduce `L _ _ N k Ht P hHt hHt0 c hc hdc`. Establish `H` using `hyp_of P`. Establish `hoc : Coc c` using `⟨fun g y => by simpa using hc g y, fun y => by simpa [dC] using congrFun hdc y⟩`. Establish `hL` using `pLoc (Pos L N) (actHom L N) P.φ`. Establish `hSm` using `pSmooth _ _ _ hL`.

Establish `hCl` using `pClosed _ _ _ hSm`. Establish `hD` using `pDep (actHom L N) P.φ`. Establish `hH` using `pHom _ _ _ hL`. Establish `hC` using `pCoc _ _ _ hH hSm hCl`. Establish `hE` using `pEquiv _ _ _ hL hSm`.

Establish `hStk : Stk (Pos L N)` using `fun q ω hω y hy => hSt (HS L N) (Pos L N) H.isOpen H.convex q ω hω y hy`. Take `⟨s, hs, b, hbi, hcb⟩` from `pComp hH hSm hD hC hE H hStk k c hoc (one L N).1 (one L N).2`. Apply the tactic sequence `have hs1 : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp`. Establish `hη : ContDiffOn ℝ (⊤ : ℕ∞) (eta (actHom L N) P.φ c (k + 1) fun _ => 1) (Pos L N)` using `(hSm H k c (k + 1) _).1`. Use `⟨s • eta (actHom L N) P.φ c (k + 1) (fun _ => 1), ⟨hη.continuousOn.const_smul s, ?_⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `y`. Use `show dC (intS (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1)) (fun j => (y j).1) = 0`. Establish `hcd : ContDiffOn ℝ 1 (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) (Pos L N)` using `(hη.const_smul s).of_le (by exact_mod_cast le_top)`. Rewrite using `[hSt (HS L N) (Pos L N) H.isOpen H.convex (k + 1) (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) hcd _ (fun j => (y j).2)]`. Establish `e : intS (extDeriv (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1)) (fun j => (y j).1) = intS' (fun _ => 0) (fun j => (y j).1)` using `intS'_congr H.convex (fun x hx => by show extDeriv (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) x = 0`.

Rewrite using `[extDeriv_smul, hCl H k c (k + 1) _ x hx, smul_zero]) (fun j => (y j).2)`. Rewrite using `[e]`. Simplify using `[intS']`. Introduce `γ h hh`. Establish `e1` using `(hE H k c hoc.inv (actHom L N γ) γ⁻¹ (fun h hh => H.mapsTo γ h hh) (fun γ' h _ => by`.

Simplify using `only [WhittakerCocycle.psi, _root_.mul_inv_rev, inv_inv, map_mul, ContinuousLinearMap.mul_apply]) (k + 1)`. Use the proof step `(fun _ => 1) h hh).1`. Establish `e2` using `eta_top H hD hC c hoc (fun _ => γ⁻¹ * 1) (fun _ => 1) h hh`. Conclude with `finv_of s _ (actHom L N γ) h (e1.trans e2)`. Introduce `s' hs' h hh`.

Take `⟨r, hr, hrh⟩` from `actL_scal (N := N) s' hs'`. Establish `e1` using `(hE H k c hoc.inv (actL (scal L N s')) 1 (fun h hh => actL_pos _ hh) (fun γ h hh => by`. Simplify using `only [WhittakerCocycle.psi, one_mul]`. Rewrite using `[hrh, map_smul]`. Conclude with `P.homog r hr _ (H.mapsTo _ _ hh)) (k + 1) (fun _ => 1) h hh).1`.

Simplify using `only [mul_one] at e1`. Conclude with `finv_of s _ (actL (scal L N s')) h e1`. Introduce `z hz`. Establish `hbInv : Inv (MonoidHom.id (Gm L N)) b` using `fun g y => by simpa using hbi g y`. Establish `key : ev (MonoidHom.id (Gm L N)) c 1 z = ev (MonoidHom.id (Gm L N)) (fun g => s * intS' (eta (actHom L N) P.φ c (k + 1) fun _ => 1) (fun l => actHom L N (g l) (one L N).1)) 1 z + ev (MonoidHom.id (Gm L N)) (dC b) 1 z`.

Unfold `ev`. Rewrite using `[← Finsupp.sum_add]`. Use `Finsupp.sum_congr fun g _ => ?_` and prove the remaining obligations. Rewrite using `[hcb, mul_add]`. Both sides reduce to the same expression.

Rewrite using `[key, pEv b hbInv z hz, add_zero]`. Unfold `ev`. Use `Finsupp.sum_congr fun g _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `show intS (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) _ = _`.

Rewrite using `[intS_smul]`. Use `beta_reduce`. Rewrite using `[intS_eq]`. Use `congr 2`. Use function extensionality and compare the values at `l`.

Simplify using `only [MonoidHom.id_apply, smul_eq_mul, mul_one]`. Both sides reduce to the same expression. Take `⟨Cφ, hCφ⟩` from `P.deriv`. Take `⟨C0, hC0⟩` from `pBound _ _ _ hL hSm hCl hC hD H _ P.overlap (fun γ h hh hm hh' => ⟨h, hh, by`. Establish `e : (emb L N γ)⁻¹ • h = ⟨actHom L N γ⁻¹ h, hm⟩` using `Subtype.ext (actHom_inv γ h).symm`.

Rewrite using `[e]`. Conclude with `hh'⟩) P.bdd k c hoc`. Use `⟨C0 * max Cφ 0 ^ (k + 1), fun x => ?_⟩` and prove the remaining obligations. Establish `hx : actL x (one L N).1 ∈ Pos L N` using `actL_pos x (one L N).2`. Establish `hM : 0 ≤ max Cφ 0 * Ht x` using `mul_nonneg (le_max_right _ _) (hHt0 x)`.

Establish `hder : ∀ γ, ‖(fderiv ℝ (WhittakerCocycle.psi (actHom L N) P.φ γ) (actL x (one L N).1)).comp (actL x)‖ ≤ max Cφ 0 * Ht x`. Introduce `γ`. Establish `hBp : actHom L N γ⁻¹ (actL x (one L N).1) ∈ Pos L N` using `H.mapsTo _ _ hx`. Rewrite using `[fderiv_psi' H γ hBp, ContinuousLinearMap.comp_assoc]`. Establish `e1 : actHom L N γ⁻¹ (actL x (one L N).1) = actL (emb L N γ⁻¹ * x) (one L N).1`.

Rewrite using `[actL_mul]`. Both sides reduce to the same expression. Establish `e2 : (actHom L N γ⁻¹).comp (actL x) = actL (emb L N γ⁻¹ * x)`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[actL_mul]`.

Both sides reduce to the same expression. Rewrite using `[e1, e2]`. Combine the equalities or inequalities in the displayed calculation. Establish `hb` using `hC0 _ hx (actL x) _ hM hder`. Combine the equalities or inequalities in the displayed calculation.

Unfold `fr`. Rewrite using `[Pi.smul_apply, smul_comp, norm_smul, hs1, one_mul]`. Use `_ ≤ C0 * (max Cφ 0 * Ht x) ^ (k + 1) := hb`. Use `_ = C0 * max Cφ 0 ^ (k + 1) * Ht x ^ (k + 1) := by ring`.
-/
theorem sWhit_of (_hEv : SEv) (hSt : SStokes) : SWhit := by
  intro L _ _ N k Ht P hHt hHt0 c hc hdc
  have H := hyp_of P
  have hoc : Coc c := ⟨fun g y => by simpa using hc g y, fun y => by simpa [dC] using congrFun hdc y⟩
  have hL := pLoc (Pos L N) (actHom L N) P.φ
  have hSm := pSmooth _ _ _ hL
  have hCl := pClosed _ _ _ hSm
  have hD := pDep (actHom L N) P.φ
  have hH := pHom _ _ _ hL
  have hC := pCoc _ _ _ hH hSm hCl
  have hE := pEquiv _ _ _ hL hSm
  have hStk : Stk (Pos L N) := fun q ω hω y hy => hSt (HS L N) (Pos L N) H.isOpen H.convex q ω hω y hy
  obtain ⟨s, hs, b, hbi, hcb⟩ := pComp hH hSm hD hC hE H hStk k c hoc (one L N).1 (one L N).2
  have hs1 : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have hη : ContDiffOn ℝ (⊤ : ℕ∞) (eta (actHom L N) P.φ c (k + 1) fun _ => 1) (Pos L N) :=
    (hSm H k c (k + 1) _).1
  refine ⟨s • eta (actHom L N) P.φ c (k + 1) (fun _ => 1), ⟨hη.continuousOn.const_smul s, ?_⟩, ?_, ?_, ?_, ?_⟩
  ·
    funext y
    show dC (intS (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1)) (fun j => (y j).1) = 0
    have hcd : ContDiffOn ℝ 1 (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) (Pos L N) :=
      (hη.const_smul s).of_le (by exact_mod_cast le_top)
    rw [hSt (HS L N) (Pos L N) H.isOpen H.convex (k + 1) (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1)
      hcd _ (fun j => (y j).2)]
    have e : intS (extDeriv (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1)) (fun j => (y j).1) =
        intS' (fun _ => 0) (fun j => (y j).1) :=
      intS'_congr H.convex (fun x hx => by
        show extDeriv (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) x = 0
        rw [extDeriv_smul, hCl H k c (k + 1) _ x hx, smul_zero]) (fun j => (y j).2)
    rw [e]
    simp [intS']
  ·
    intro γ h hh
    have e1 := (hE H k c hoc.inv (actHom L N γ) γ⁻¹ (fun h hh => H.mapsTo γ h hh) (fun γ' h _ => by
      simp only [WhittakerCocycle.psi, _root_.mul_inv_rev, inv_inv, map_mul, ContinuousLinearMap.mul_apply]) (k + 1)
      (fun _ => 1) h hh).1
    have e2 := eta_top H hD hC c hoc (fun _ => γ⁻¹ * 1) (fun _ => 1) h hh
    exact finv_of s _ (actHom L N γ) h (e1.trans e2)
  ·
    intro s' hs' h hh
    obtain ⟨r, hr, hrh⟩ := actL_scal (N := N) s' hs'
    have e1 := (hE H k c hoc.inv (actL (scal L N s')) 1 (fun h hh => actL_pos _ hh) (fun γ h hh => by
      simp only [WhittakerCocycle.psi, one_mul]
      rw [hrh, map_smul]
      exact P.homog r hr _ (H.mapsTo _ _ hh)) (k + 1) (fun _ => 1) h hh).1
    simp only [mul_one] at e1
    exact finv_of s _ (actL (scal L N s')) h e1
  ·
    intro z hz
    have hbInv : Inv (MonoidHom.id (Gm L N)) b := fun g y => by simpa using hbi g y
    have key : ev (MonoidHom.id (Gm L N)) c 1 z =
        ev (MonoidHom.id (Gm L N)) (fun g => s * intS' (eta (actHom L N) P.φ c (k + 1) fun _ => 1)
          (fun l => actHom L N (g l) (one L N).1)) 1 z + ev (MonoidHom.id (Gm L N)) (dC b) 1 z := by
      unfold ev
      rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun g _ => ?_
      rw [hcb, mul_add]
      rfl
    rw [key, pEv b hbInv z hz, add_zero]
    unfold ev
    refine Finsupp.sum_congr fun g _ => ?_
    congr 1
    show intS (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) _ = _
    rw [intS_smul]
    beta_reduce
    rw [intS_eq]
    congr 2
    funext l
    simp only [MonoidHom.id_apply, smul_eq_mul, mul_one]
    rfl
  ·
    obtain ⟨Cφ, hCφ⟩ := P.deriv
    obtain ⟨C0, hC0⟩ := pBound _ _ _ hL hSm hCl hC hD H _ P.overlap (fun γ h hh hm hh' => ⟨h, hh, by
      have e : (emb L N γ)⁻¹ • h = ⟨actHom L N γ⁻¹ h, hm⟩ := Subtype.ext (actHom_inv γ h).symm
      rw [e]
      exact hh'⟩) P.bdd k c hoc
    refine ⟨C0 * max Cφ 0 ^ (k + 1), fun x => ?_⟩
    have hx : actL x (one L N).1 ∈ Pos L N := actL_pos x (one L N).2
    have hM : 0 ≤ max Cφ 0 * Ht x := mul_nonneg (le_max_right _ _) (hHt0 x)
    have hder : ∀ γ, ‖(fderiv ℝ (WhittakerCocycle.psi (actHom L N) P.φ γ) (actL x (one L N).1)).comp (actL x)‖ ≤
        max Cφ 0 * Ht x := by
      intro γ
      have hBp : actHom L N γ⁻¹ (actL x (one L N).1) ∈ Pos L N := H.mapsTo _ _ hx
      rw [fderiv_psi' H γ hBp, ContinuousLinearMap.comp_assoc]
      have e1 : actHom L N γ⁻¹ (actL x (one L N).1) = actL (emb L N γ⁻¹ * x) (one L N).1 := by
        rw [actL_mul]
        rfl
      have e2 : (actHom L N γ⁻¹).comp (actL x) = actL (emb L N γ⁻¹ * x) := by
        refine ContinuousLinearMap.ext fun v => ?_
        rw [actL_mul]
        rfl
      rw [e1, e2]
      calc _ ≤ Cφ * Ht (emb L N γ⁻¹ * x) := hCφ _
        _ = Cφ * Ht x := by rw [hHt]
        _ ≤ max Cφ 0 * Ht x := mul_le_mul_of_nonneg_right (le_max_left _ _) (hHt0 x)
    have hb := hC0 _ hx (actL x) _ hM hder
    calc ‖fr (s • eta (actHom L N) P.φ c (k + 1) fun _ => 1) x‖
        = ‖((eta (actHom L N) P.φ c (k + 1) fun _ => 1) (actL x (one L N).1)).compContinuousLinearMap
            (actL x)‖ := by
          unfold fr
          rw [Pi.smul_apply, smul_comp, norm_smul, hs1, one_mul]
      _ ≤ C0 * (max Cφ 0 * Ht x) ^ (k + 1) := hb
      _ = C0 * max Cφ 0 ^ (k + 1) * Ht x ^ (k + 1) := by ring

end PositivityTheory.KB

end

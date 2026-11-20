import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IteratedFderivRightTranslation

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def WD (Q R : Matrix (Fin n) (Fin n) ℂ) : M2 n := Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹

/- English proof (translation)
The claim follows from `mX_eq' Q R`.
-/
theorem mX_eq (Q R : Matrix (Fin n) (Fin n) ℂ) : mX 1 Q R 1 = 1 + WD Q R := mX_eq' Q R

/- English proof (translation)
Establish `h1 : embOn (blkB j) S * embOn (blkA j) T' = 0` using `embOn_mul_embOn_disj (fun c hc hc' => by`. Simplify using `only [blkB, Finset.mem_compl] at hc`. Conclude with `hc hc') S T'`. Establish `h2 : embOn (blkA j) T * embOn (blkB j) S' = 0` using `embOn_mul_embOn_disj (fun c hc hc' => by`. Simplify using `only [blkB, Finset.mem_compl] at hc'`.

Conclude with `hc' hc) T S'`. Simplify using `only [WD]`. Rewrite using `[WD_prod, h1, h2]`. Simplify using the standard rewrite rules.
-/
theorem WD_mul_WD_B_A (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
    (T' : Matrix (blkA (n := n) j) (blkA j) ℂ) (S' : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    WD (embOn (blkB j) S) (embOn (blkA j) T) * WD (embOn (blkB j) S') (embOn (blkA j) T') = 0 := by
  have h1 : embOn (blkB j) S * embOn (blkA j) T' = 0 :=
    embOn_mul_embOn_disj (fun c hc hc' => by
      simp only [blkB, Finset.mem_compl] at hc
      exact hc hc') S T'
  have h2 : embOn (blkA j) T * embOn (blkB j) S' = 0 :=
    embOn_mul_embOn_disj (fun c hc hc' => by
      simp only [blkB, Finset.mem_compl] at hc'
      exact hc' hc) T S'
  simp only [WD]
  rw [WD_prod, h1, h2]
  simp

/- English proof (translation)
The claim follows from `contDiffOn_scalar_section_of_units p q`.
-/
theorem contDiffOn_scalar_section (p q : ℤ) : ContDiffOn ℂ ∞ (f0 (n := n) p q) {x | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} :=
  contDiffOn_scalar_section_of_units p q

/- English proof (translation)
The claim follows from `contDiffOn_hF' j p q`.
-/
theorem contDiffOn_hF (j : ℕ) (p q : ℤ) : ContDiffOn ℂ ∞ (hF (n := n) j p q) (Dom n) := contDiffOn_hF' j p q

/- English proof (translation)
The claim follows from `contDiffOn_fV' p q`.
-/
theorem contDiffOn_fV (p q : ℤ) : ContDiffOn ℂ ∞ (fV (n := n) p q) (Dom n) := contDiffOn_fV' p q

/- English proof (translation)
Introduce `y hy`. Establish `h` using `(hF.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (i := b) (m := ∞) (by exact_mod_cast le_top)`. Conclude with `((ContinuousMultilinearMap.apply ℂ (fun _ : Fin b => E) G w).contDiff.contDiffAt.comp y h).contDiffWithinAt`.
-/
private theorem contDiffOn_iteratedFDeriv_apply {E G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (F : E → G) (U : Set E) (hU : IsOpen U)
    (hF : ContDiffOn ℂ ∞ F U) (b : ℕ) (w : Fin b → E) :
    ContDiffOn ℂ ∞ (fun y => iteratedFDeriv ℂ b F y w) U := by
  intro y hy
  have h := (hF.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (i := b) (m := ∞)
    (by exact_mod_cast le_top)
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin b => E) G w).contDiff.contDiffAt.comp y h).contDiffWithinAt

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `zero`. Introduce `G _ _ F U hU hF x hx u w`. Establish `hw : Fin.append u w = u`. Use function extensionality and compare the values at `i`.

Conclude with `Fin.append_left u w i`. Rewrite using `[hw]`. Simplify using `only [iteratedFDeriv_zero_apply]`. Both sides reduce to the same expression. Consider the case `succ b ih`.

Introduce `G _ _ F U hU hF x hx u w`. Establish `hF' : ContDiffOn ℂ ∞ (fderiv ℂ F) U` using `hF.fderiv_of_isOpen hU (by exact_mod_cast le_top)`. Set `v : Fin (a + b + 1) → E` to `@Fin.append a (b + 1) E u w`. Establish `h1 : iteratedFDeriv ℂ (a + (b + 1)) F x (Fin.append u w) = iteratedFDeriv ℂ (a + b) (fun y => fderiv ℂ F y) x (Fin.init v) (v (Fin.last (a + b)))` using `iteratedFDeriv_succ_apply_right v`. Establish `hinit : Fin.init v = Fin.append u (Fin.init w)`.

Use function extensionality and compare the values at `i`. Use `Fin.addCases (fun j => ?_) (fun j => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.append_left]`. Conclude with `Fin.append_left u w j`. Rewrite using `[Fin.append_right]`.

Conclude with `Fin.append_right u w j.castSucc`. Establish `hlast : v (Fin.last (a + b)) = w (Fin.last b)` using `Fin.append_right u w (Fin.last b)`. Rewrite using `[h1, hinit, hlast, ih (fderiv ℂ F) U hU hF' x hx u (Fin.init w)]`. Establish `hfun : (fun y => iteratedFDeriv ℂ (b + 1) F y w) = (ContinuousLinearMap.apply ℂ G (w (Fin.last b))) ∘ (fun y => iteratedFDeriv ℂ b (fun z => fderiv ℂ F z) y (Fin.init w))`. Use function extensionality and compare the values at `y`.

Simplify using `[iteratedFDeriv_succ_apply_right]`. Establish `hs : ContDiffAt ℂ ∞ (fun y => iteratedFDeriv ℂ b (fun z => fderiv ℂ F z) y (Fin.init w)) x` using `(contDiffOn_iteratedFDeriv_apply (fderiv ℂ F) U hU hF' b (Fin.init w)).contDiffAt (hU.mem_nhds hx)`. Rewrite using `[hfun, ContinuousLinearMap.iteratedFDeriv_comp_left _ hs (by exact_mod_cast le_top)]`. Both sides reduce to the same expression.
-/
private theorem iteratedFDeriv_add_append_eq_iteratedFDeriv_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a b : ℕ) :
    ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] (F : E → G) (U : Set E), IsOpen U →
      ContDiffOn ℂ ∞ F U → ∀ x ∈ U, ∀ (u : Fin a → E) (w : Fin b → E),
      iteratedFDeriv ℂ (a + b) F x (Fin.append u w) =
        iteratedFDeriv ℂ a (fun y => iteratedFDeriv ℂ b F y w) x u := by
  induction b with
  | zero =>
    intro G _ _ F U hU hF x hx u w
    have hw : Fin.append u w = u := by
      funext i
      exact Fin.append_left u w i
    rw [hw]
    simp only [iteratedFDeriv_zero_apply]
    rfl
  | succ b ih =>
    intro G _ _ F U hU hF x hx u w
    have hF' : ContDiffOn ℂ ∞ (fderiv ℂ F) U := hF.fderiv_of_isOpen hU (by exact_mod_cast le_top)
    let v : Fin (a + b + 1) → E := @Fin.append a (b + 1) E u w
    have h1 : iteratedFDeriv ℂ (a + (b + 1)) F x (Fin.append u w) =
        iteratedFDeriv ℂ (a + b) (fun y => fderiv ℂ F y) x (Fin.init v) (v (Fin.last (a + b))) :=
      iteratedFDeriv_succ_apply_right v
    have hinit : Fin.init v = Fin.append u (Fin.init w) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact Fin.append_left u w j
      · rw [Fin.append_right]
        exact Fin.append_right u w j.castSucc
    have hlast : v (Fin.last (a + b)) = w (Fin.last b) := Fin.append_right u w (Fin.last b)
    rw [h1, hinit, hlast, ih (fderiv ℂ F) U hU hF' x hx u (Fin.init w)]
    have hfun : (fun y => iteratedFDeriv ℂ (b + 1) F y w) =
        (ContinuousLinearMap.apply ℂ G (w (Fin.last b))) ∘
          (fun y => iteratedFDeriv ℂ b (fun z => fderiv ℂ F z) y (Fin.init w)) := by
      funext y
      simp [iteratedFDeriv_succ_apply_right]
    have hs : ContDiffAt ℂ ∞ (fun y => iteratedFDeriv ℂ b (fun z => fderiv ℂ F z) y (Fin.init w)) x :=
      (contDiffOn_iteratedFDeriv_apply (fderiv ℂ F) U hU hF' b (Fin.init w)).contDiffAt (hU.mem_nhds hx)
    rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_left _ hs (by exact_mod_cast le_top)]
    rfl

/- English proof (translation)
Set `F' : E → G` to `fun z => F (y + z)`. Set `U' : Set E` to `{z | y + z ∈ U}`. Establish `hU' : IsOpen U'` using `hU.preimage (continuous_const.add continuous_id)`. Establish `hF' : ContDiffOn ℂ ∞ F' U'` using `hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)`. Establish `h0 : L 0 ∈ U'` using `by show y + L 0 ∈ U`.

Simplify using `using hy`. Establish `hpre : IsOpen (L ⁻¹' U')` using `hU'.preimage L.continuous`. Establish `key` using `L.iteratedFDerivWithin_comp_right hF' hU'.uniqueDiffOn hpre.uniqueDiffOn h0 (i := b) (by exact_mod_cast le_top)`. Establish `e1 : iteratedFDerivWithin ℂ b (F' ∘ L) (L ⁻¹' U') 0 = iteratedFDeriv ℂ b (F' ∘ L) 0` using `iteratedFDerivWithin_of_isOpen b hpre h0`. Establish `e2 : iteratedFDerivWithin ℂ b F' U' (L 0) = iteratedFDeriv ℂ b F' (L 0)` using `iteratedFDerivWithin_of_isOpen b hU' h0`.

Establish `key2 : iteratedFDeriv ℂ b (F' ∘ L) 0 = (iteratedFDeriv ℂ b F' (L 0)).compContinuousLinearMap fun _ => L`. Rewrite using `[← e1, ← e2]`. Conclude with `key`. Establish `e3 : iteratedFDeriv ℂ b F' (L 0) = iteratedFDeriv ℂ b F y`. Use `iteratedFDerivWithin_comp_add_left (𝕜 := ℂ) (f := F) (s := Set.univ) b y (L 0)` as an intermediate fact.

Simplify using `only [iteratedFDerivWithin_univ, Set.vadd_set_univ, map_zero, add_zero] at this`. Rewrite using `[map_zero]`. Conclude with `this`. Establish `hfun : (fun S => F (y + L S)) = F' ∘ L` using `rfl`. Rewrite using `[hfun, key2, e3]`.

Both sides reduce to the same expression.
-/
private theorem iteratedFDeriv_comp_add_clm_zero {E E' G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (F : E → G) (U : Set E) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (y : E) (hy : y ∈ U)
    (L : E' →L[ℂ] E) (b : ℕ) (v : Fin b → E') :
    iteratedFDeriv ℂ b (fun S => F (y + L S)) 0 v = iteratedFDeriv ℂ b F y (fun i => L (v i)) := by
  let F' : E → G := fun z => F (y + z)
  let U' : Set E := {z | y + z ∈ U}
  have hU' : IsOpen U' := hU.preimage (continuous_const.add continuous_id)
  have hF' : ContDiffOn ℂ ∞ F' U' :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)
  have h0 : L 0 ∈ U' := by
    show y + L 0 ∈ U
    simpa using hy
  have hpre : IsOpen (L ⁻¹' U') := hU'.preimage L.continuous
  have key := L.iteratedFDerivWithin_comp_right hF' hU'.uniqueDiffOn hpre.uniqueDiffOn h0 (i := b)
    (by exact_mod_cast le_top)
  have e1 : iteratedFDerivWithin ℂ b (F' ∘ L) (L ⁻¹' U') 0 = iteratedFDeriv ℂ b (F' ∘ L) 0 :=
    iteratedFDerivWithin_of_isOpen b hpre h0
  have e2 : iteratedFDerivWithin ℂ b F' U' (L 0) = iteratedFDeriv ℂ b F' (L 0) :=
    iteratedFDerivWithin_of_isOpen b hU' h0
  have key2 : iteratedFDeriv ℂ b (F' ∘ L) 0 =
      (iteratedFDeriv ℂ b F' (L 0)).compContinuousLinearMap fun _ => L := by
    rw [← e1, ← e2]
    exact key
  have e3 : iteratedFDeriv ℂ b F' (L 0) = iteratedFDeriv ℂ b F y := by
    have := iteratedFDerivWithin_comp_add_left (𝕜 := ℂ) (f := F) (s := Set.univ) b y (L 0)
    simp only [iteratedFDerivWithin_univ, Set.vadd_set_univ, map_zero, add_zero] at this
    rw [map_zero]
    exact this
  have hfun : (fun S => F (y + L S)) = F' ∘ L := rfl
  rw [hfun, key2, e3]
  rfl

/- English proof (translation)
Establish `hΨ : ∀ τ : Equiv.Perm ιB, ContDiffOn ℂ ∞ (fun y => iteratedFDeriv ℂ (Fintype.card ιB) F y (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) U` using `fun τ => contDiffOn_iteratedFDeriv_apply F U hU hF _ _`. Establish `hx' : x₀ + LA 0 ∈ U` using `by simpa using hx`. Establish `hev : (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) =ᶠ[nhds 0] (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T) (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i) …`. Establish `hopen : IsOpen {T : Matrix ιA ιA ℂ | x₀ + LA T ∈ U}` using `hU.preimage (continuous_const.add LA.continuous)`. Use `filter_upwards [hopen.mem_nhds hx'] with T hT`.

Simplify using `only [detD]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Conclude with `congrArg _ (iteratedFDeriv_comp_add_clm_zero F U hU hF (x₀ + LA T) hT LB _ _)`. Establish `hD : iteratedFDeriv ℂ (Fintype.card ιA) (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) 0 = iteratedFDeriv ℂ (Fintype.card ιA) (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T) (fun i => LB (Matrix.single (( …`. Establish `h2` using `hev`.

Rewrite `h2` using `[← nhdsWithin_univ]`. Use `h2.iteratedFDerivWithin_eq (𝕜 := ℂ) hev.eq_of_nhds (Fintype.card ιA)` as an intermediate fact. Simplify `this` using `only [iteratedFDerivWithin_univ]`. Establish `hsum : ∀ u : Fin (Fintype.card ιA) → Matrix ιA ιA ℂ, iteratedFDeriv ℂ (Fintype.card ιA) (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T) (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).s …`. Introduce `u`.

Establish `hcd' : ∀ τ : Equiv.Perm ιB, ContDiffAt ℂ (Fintype.card ιA) (fun T => iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T) (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) 0`. Introduce `τ`. Establish `h1` using `(hΨ τ).contDiffAt (hU.mem_nhds hx')`. Establish `h2 : ContDiffAt ℂ ∞ (fun T : Matrix ιA ιA ℂ => x₀ + LA T) 0` using `(contDiff_const.add LA.contDiff).contDiffAt`. Use `(h1.comp 0 h2).of_le ?_` and prove the remaining obligations.

Conclude with `le_top` after adjusting the coercions. Establish `hcd : ∀ τ ∈ (Finset.univ : Finset (Equiv.Perm ιB)), ContDiffAt ℂ (Fintype.card ιA) (fun T => (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T) (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) 0` using `fun τ _ => contDiffAt_const.mul (hcd' τ)`. Rewrite using `[iteratedFDeriv_fun_sum_apply hcd, ContinuousMultilinearMap.sum_apply]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Establish `hfun : (fun T => (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T) (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) = (Equiv.Perm.sign τ : ℂ) • (fun T => iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T) (f …`.

Use function extensionality and compare the values at `T`. Simplify using the standard rewrite rules. Rewrite using `[hfun, iteratedFDeriv_const_smul_apply (hcd' τ), ContinuousMultilinearMap.smul_apply, smul_eq_mul]`. Use `congr 1`. Conclude with `(iteratedFDeriv_comp_add_clm_zero _ U hU (hΨ τ) x₀ hx LA _ _).trans (iteratedFDeriv_add_append_eq_iteratedFDeriv_apply _ _ F U hU hF x₀ hx _ _).symm`.

Establish `hdef : ∀ G : Matrix ιA ιA ℂ → ℂ, detD G = ∑ σ : Equiv.Perm ιA, (Equiv.Perm.sign σ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιA) G 0 (fun i => Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1)` using `fun G => rfl`. Rewrite using `[hdef (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))), hD]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[hsum, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem detD_detD_comp {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (x₀ : M2 n) (hx : x₀ ∈ U)
    (LA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : Matrix ιB ιB ℂ →L[ℂ] M2 n) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) F x₀
          (Fin.append (fun i => LA (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
  have hΨ : ∀ τ : Equiv.Perm ιB, ContDiffOn ℂ ∞ (fun y => iteratedFDeriv ℂ (Fintype.card ιB) F y
      (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) U :=
    fun τ => contDiffOn_iteratedFDeriv_apply F U hU hF _ _
  have hx' : x₀ + LA 0 ∈ U := by simpa using hx
  have hev : (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) =ᶠ[nhds 0]
      (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
        (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    have hopen : IsOpen {T : Matrix ιA ιA ℂ | x₀ + LA T ∈ U} :=
      hU.preimage (continuous_const.add LA.continuous)
    filter_upwards [hopen.mem_nhds hx'] with T hT
    simp only [detD]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    exact congrArg _ (iteratedFDeriv_comp_add_clm_zero F U hU hF (x₀ + LA T) hT LB _ _)
  have hD : iteratedFDeriv ℂ (Fintype.card ιA) (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) 0 =
      iteratedFDeriv ℂ (Fintype.card ιA) (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 := by
    have h2 := hev
    rw [← nhdsWithin_univ] at h2
    have := h2.iteratedFDerivWithin_eq (𝕜 := ℂ) hev.eq_of_nhds (Fintype.card ιA)
    simpa only [iteratedFDerivWithin_univ] using this
  have hsum : ∀ u : Fin (Fintype.card ιA) → Matrix ιA ιA ℂ,
      iteratedFDeriv ℂ (Fintype.card ιA) (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 u =
      ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) F x₀
        (Fin.append (fun i => LA (u i))
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    intro u
    have hcd' : ∀ τ : Equiv.Perm ιB, ContDiffAt ℂ (Fintype.card ιA) (fun T => iteratedFDeriv ℂ (Fintype.card ιB) F
        (x₀ + LA T) (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i)
          (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 := by
      intro τ
      have h1 := (hΨ τ).contDiffAt (hU.mem_nhds hx')
      have h2 : ContDiffAt ℂ ∞ (fun T : Matrix ιA ιA ℂ => x₀ + LA T) 0 :=
        (contDiff_const.add LA.contDiff).contDiffAt
      refine (h1.comp 0 h2).of_le ?_
      exact_mod_cast le_top
    have hcd : ∀ τ ∈ (Finset.univ : Finset (Equiv.Perm ιB)), ContDiffAt ℂ (Fintype.card ιA)
        (fun T => (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 :=
      fun τ _ => contDiffAt_const.mul (hcd' τ)
    rw [iteratedFDeriv_fun_sum_apply hcd, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    have hfun : (fun T => (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) =
        (Equiv.Perm.sign τ : ℂ) • (fun T => iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
      funext T
      simp
    rw [hfun, iteratedFDeriv_const_smul_apply (hcd' τ), ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    congr 1
    exact (iteratedFDeriv_comp_add_clm_zero _ U hU (hΨ τ) x₀ hx LA _ _).trans
      (iteratedFDeriv_add_append_eq_iteratedFDeriv_apply _ _ F U hU hF x₀ hx _ _).symm
  have hdef : ∀ G : Matrix ιA ιA ℂ → ℂ, detD G = ∑ σ : Equiv.Perm ιA, (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card ιA) G 0
        (fun i => Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1) :=
    fun G => rfl
  rw [hdef (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))), hD]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  ring

/- English proof (translation)
The claim follows from `iterated_fderiv_right_translation F U hU hF W hW x hx`.
-/
theorem iteratedFDeriv_right {N : ℕ} (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (W : Fin (N + 1) → M2 n) (hW : ∀ a b, W a * W b = 0) (x : M2 n) (hx : x ∈ U) :
    fderiv ℂ (fun y => iteratedFDeriv ℂ N F y (fun i => y * W i.succ)) x (x * W 0) =
      iteratedFDeriv ℂ (N + 1) F x (fun i => x * W i) :=
  iterated_fderiv_right_translation F U hU hF W hW x hx

/- English proof (translation)
Establish `hdet : Continuous (fun x : M2 n => x.det)` using `continuous_id.matrix_det`. Establish `hS0 : IsOpen {x : M2 n | x.det ≠ 0}` using `isOpen_ne_fun hdet continuous_const`. Establish `hc1 : Continuous (fun x : M2 n => (u1 x).det)`. Apply `Continuous.matrix_det` to reduce the goal to its premises. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations.

Simplify using `only [u1, Matrix.add_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply, smul_eq_mul]`. Use `fun_prop`. Establish `hc2 : Continuous (fun x : M2 n => (u2 x).det)`. Apply `Continuous.matrix_det` to reduce the goal to its premises. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations.

Simplify using `only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply, smul_eq_mul]`. Use `fun_prop`. Establish `h4 : IsOpen ({x : M2 n | x.det ≠ 0} ∩ (fun x => ub1 x) ⁻¹' {m | m.det ≠ 0})` using `continuousOn_inverse_first_block.isOpen_inter_preimage hS0 (isOpen_ne_fun continuous_id.matrix_det continuous_const)`. Establish `he : Dom n = {x : M2 n | (u1 x).det ≠ 0} ∩ {x : M2 n | (u2 x).det ≠ 0} ∩ ({x : M2 n | x.det ≠ 0} ∩ (fun x => ub1 x) ⁻¹' {m | m.det ≠ 0})`. Use extensionality with `x`.

Simplify using `only [Dom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, isUnit_iff_ne_zero]`. The claim follows by propositional logic. Rewrite using `[he]`. Conclude with `((isOpen_ne_fun hc1 continuous_const).inter (isOpen_ne_fun hc2 continuous_const)).inter h4`.
-/
private theorem isOpen_dom_analytic_determinants : IsOpen (Dom n) := by
  have hdet : Continuous (fun x : M2 n => x.det) := continuous_id.matrix_det
  have hS0 : IsOpen {x : M2 n | x.det ≠ 0} := isOpen_ne_fun hdet continuous_const
  have hc1 : Continuous (fun x : M2 n => (u1 x).det) := by
    apply Continuous.matrix_det
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [u1, Matrix.add_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
    fun_prop
  have hc2 : Continuous (fun x : M2 n => (u2 x).det) := by
    apply Continuous.matrix_det
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, Matrix.of_apply,
      smul_eq_mul]
    fun_prop
  have h4 : IsOpen ({x : M2 n | x.det ≠ 0} ∩ (fun x => ub1 x) ⁻¹' {m | m.det ≠ 0}) :=
    continuousOn_inverse_first_block.isOpen_inter_preimage hS0 (isOpen_ne_fun continuous_id.matrix_det continuous_const)
  have he : Dom n = {x : M2 n | (u1 x).det ≠ 0} ∩ {x : M2 n | (u2 x).det ≠ 0} ∩
      ({x : M2 n | x.det ≠ 0} ∩ (fun x => ub1 x) ⁻¹' {m | m.det ≠ 0}) := by
    ext x
    simp only [Dom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, isUnit_iff_ne_zero]
    tauto
  rw [he]
  exact ((isOpen_ne_fun hc1 continuous_const).inter (isOpen_ne_fun hc2 continuous_const)).inter h4

/- English proof (translation)
Use `⟨isUnit_det_of_inG' hx, det_first_cayley_block_ne_zero hx, det_second_cayley_block_ne_zero hx, ?_⟩` and prove the remaining obligations. Rewrite using `[inverse_first_block_eq_of_group hx, det_conjTranspose]`. Conclude with `star_ne_zero.mpr (det_first_cayley_block_ne_zero hx)`.
-/
private theorem mem_dom_of_inG {x : M2 n} (hx : InG x) : x ∈ Dom n := by
  refine ⟨isUnit_det_of_inG' hx, det_first_cayley_block_ne_zero hx, det_second_cayley_block_ne_zero hx, ?_⟩
  rw [inverse_first_block_eq_of_group hx, det_conjTranspose]
  exact star_ne_zero.mpr (det_first_cayley_block_ne_zero hx)

/- English proof (translation)
Take `⟨hG, h21⟩` from `hP`. Take `⟨hx0, hx1, hx2, hx3⟩` from `hx`. Establish `hPu` using `isUnit_det_of_inG' hG`. Establish `hrel` using `congrArg Matrix.det (par_rel hG h21)`. Rewrite `hrel` using `[det_mul, det_one, det_conjTranspose]`.

Establish `h22 : (toBlocks₂₂ P).det ≠ 0` using `right_ne_zero_of_mul_eq_one hrel`. Establish `h11 : (toBlocks₁₁ P).det ≠ 0`. Use `left_ne_zero_of_mul_eq_one hrel` as an intermediate fact. Conclude with `fun h => this (by rw [h, star_zero])`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[det_mul]`. Conclude with `hPu.mul hx0`. Rewrite using `[automorphy_first_mul_parabolic x h21, det_mul]`. Conclude with `mul_ne_zero h22 hx1`. Rewrite using `[automorphy_second_mul_parabolic x h21, det_mul]`.

Conclude with `mul_ne_zero h22 hx2`. Rewrite using `[inverse_first_block_mul_parabolic h21 hPu, det_mul]`. Use `mul_ne_zero hx3 ?_` and prove the remaining obligations. Conclude with `(Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr h11)).ne_zero`.
-/
private theorem mul_mem_dom_of_inP {P x : M2 n} (hP : InP P) (hx : x ∈ Dom n) : P * x ∈ Dom n := by
  obtain ⟨hG, h21⟩ := hP
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  have hPu := isUnit_det_of_inG' hG
  have hrel := congrArg Matrix.det (par_rel hG h21)
  rw [det_mul, det_one, det_conjTranspose] at hrel
  have h22 : (toBlocks₂₂ P).det ≠ 0 := right_ne_zero_of_mul_eq_one hrel
  have h11 : (toBlocks₁₁ P).det ≠ 0 := by
    have := left_ne_zero_of_mul_eq_one hrel
    exact fun h => this (by rw [h, star_zero])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [det_mul]
    exact hPu.mul hx0
  · rw [automorphy_first_mul_parabolic x h21, det_mul]
    exact mul_ne_zero h22 hx1
  · rw [automorphy_second_mul_parabolic x h21, det_mul]
    exact mul_ne_zero h22 hx2
  · rw [inverse_first_block_mul_parabolic h21 hPu, det_mul]
    refine mul_ne_zero hx3 ?_
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr h11)).ne_zero

/- English proof (translation)
Introduce `x hx`. Establish `hcd : ContDiffAt ℂ ∞ G x` using `hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)`. Establish `h1` using `hcd.fderiv_right (m := ∞) (by simp)`. Establish `h2 : ContDiffAt ℂ ∞ (fun x : M2 n => x * Z) x` using `((LinearMap.mulRight ℂ Z).toContinuousLinearMap).contDiff.contDiffAt`. Conclude with `(h1.clm_apply h2).contDiffWithinAt`.
-/
private theorem contDiffOn_fderiv_apply_mul_right {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) (Z : M2 n) :
    ContDiffOn ℂ ∞ (fun x => fderiv ℂ G x (x * Z)) (Dom n) := by
  intro x hx
  have hcd : ContDiffAt ℂ ∞ G x := hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)
  have h1 := hcd.fderiv_right (m := ∞) (by simp)
  have h2 : ContDiffAt ℂ ∞ (fun x : M2 n => x * Z) x :=
    ((LinearMap.mulRight ℂ Z).toContinuousLinearMap).contDiff.contDiffAt
  exact (h1.clm_apply h2).contDiffWithinAt

/- English proof (translation)
Introduce `x hx`. Establish `: G1 =ᶠ[nhds x] G2` using `Filter.eventuallyEq_of_mem (isOpen_dom_analytic_determinants.mem_nhds hx) h`. Simplify using `only [Filter.EventuallyEq.fderiv_eq (𝕜 := ℂ) this]`.
-/
private theorem eqOn_fderiv_apply_mul_of_eqOn {G1 G2 : M2 n → ℂ} (h : Set.EqOn G1 G2 (Dom n)) (Z : M2 n) :
    Set.EqOn (fun x => fderiv ℂ G1 x (x * Z)) (fun x => fderiv ℂ G2 x (x * Z)) (Dom n) := by
  intro x hx
  have : G1 =ᶠ[nhds x] G2 := Filter.eventuallyEq_of_mem (isOpen_dom_analytic_determinants.mem_nhds hx) h
  simp only [Filter.EventuallyEq.fderiv_eq (𝕜 := ℂ) this]

/- English proof (translation)
Introduce `x hx`. Set `L : M2 n →L[ℂ] M2 n` to `(LinearMap.mulLeft ℂ P).toContinuousLinearMap`. Establish `hPx : P * x ∈ Dom n` using `mul_mem_dom_of_inP hP hx`. Establish `hd1 : DifferentiableAt ℂ G (L x)` using `(hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hPx)).differentiableAt (by simp)`. Establish `hd2 : DifferentiableAt ℂ G x` using `(hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)).differentiableAt (by simp)`.

Establish `heq : (G ∘ L) =ᶠ[nhds x] (fun y => c * G y)` using `Filter.eventually_of_mem (isOpen_dom_analytic_determinants.mem_nhds hx) (fun y hy => h y hy)`. Establish `hA : HasFDerivAt (G ∘ L) ((fderiv ℂ G (L x)).comp L) x` using `hd1.hasFDerivAt.comp x L.hasFDerivAt`. Establish `hA' : HasFDerivAt (fun y => c * G y) ((fderiv ℂ G (L x)).comp L) x` using `hA.congr_of_eventuallyEq heq.symm`. Establish `hB : HasFDerivAt (fun y => c * G y) (c • fderiv ℂ G x) x` using `hd2.hasFDerivAt.const_mul c`. Establish `e3` using `hA'.unique hB`.

Establish `e4 : ((fderiv ℂ G (L x)).comp L) (x * Z) = (c • fderiv ℂ G x) (x * Z)` using `by rw [e3]`. Rewrite using `[Matrix.mul_assoc]`. Conclude with `e4`.
-/
private theorem fderiv_apply_mul_equivariant_of_equivariant {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) {P : M2 n} (hP : InP P) (c : ℂ)
    (h : ∀ x ∈ Dom n, G (P * x) = c * G x) (Z : M2 n) :
    ∀ x ∈ Dom n, fderiv ℂ G (P * x) (P * x * Z) = c * fderiv ℂ G x (x * Z) := by
  intro x hx
  let L : M2 n →L[ℂ] M2 n := (LinearMap.mulLeft ℂ P).toContinuousLinearMap
  have hPx : P * x ∈ Dom n := mul_mem_dom_of_inP hP hx
  have hd1 : DifferentiableAt ℂ G (L x) :=
    (hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hPx)).differentiableAt (by simp)
  have hd2 : DifferentiableAt ℂ G x := (hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)).differentiableAt (by simp)
  have heq : (G ∘ L) =ᶠ[nhds x] (fun y => c * G y) :=
    Filter.eventually_of_mem (isOpen_dom_analytic_determinants.mem_nhds hx) (fun y hy => h y hy)
  have hA : HasFDerivAt (G ∘ L) ((fderiv ℂ G (L x)).comp L) x := hd1.hasFDerivAt.comp x L.hasFDerivAt
  have hA' : HasFDerivAt (fun y => c * G y) ((fderiv ℂ G (L x)).comp L) x := hA.congr_of_eventuallyEq heq.symm
  have hB : HasFDerivAt (fun y => c * G y) (c • fderiv ℂ G x) x := hd2.hasFDerivAt.const_mul c
  have e3 := hA'.unique hB
  have e4 : ((fderiv ℂ G (L x)).comp L) (x * Z) = (c • fderiv ℂ G x) (x * Z) := by rw [e3]
  rw [Matrix.mul_assoc]
  exact e4

/- English proof (translation)
Introduce `x hx`. Establish `hcd : ContDiffAt ℂ ∞ G x` using `hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)`. Establish `hsym : IsSymmSndFDerivAt ℂ G x` using `hcd.isSymmSndFDerivAt (by`. Simplify using `only [minSmoothness_of_isRCLikeNormedField]`. Conclude with `WithTop.coe_le_coe.mpr le_top)`.

Establish `hdd : DifferentiableAt ℂ (fderiv ℂ G) x` using `(hcd.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)`. Establish `key : ∀ c d : M2 n, c * d = 0 → fderiv ℂ (fun y => fderiv ℂ G y (y * d)) x (x * c) = fderiv ℂ (fderiv ℂ G) x (x * c) (x * d)`. Introduce `c d hcd0`. Set `R : M2 n →L[ℂ] M2 n` to `(LinearMap.mulRight ℂ d).toContinuousLinearMap`. Establish `hfd` using `hdd.hasFDerivAt.clm_apply R.hasFDerivAt`.

Establish `h0 : R (x * c) = 0` using `by show x * c * d = 0`. Rewrite using `[Matrix.mul_assoc, hcd0, Matrix.mul_zero]`. Establish `e1 : fderiv ℂ (fun y => fderiv ℂ G y (y * d)) x (x * c) = fderiv ℂ G x (R (x * c)) + fderiv ℂ (fderiv ℂ G) x (x * c) (R x)` using `congrArg (fun T => T (x * c)) hfd.fderiv`. Rewrite using `[e1, h0, map_zero, zero_add]`. Both sides reduce to the same expression.

Rewrite using `[key a b hab, key b a hba]`. Conclude with `hsym.eq _ _`.
-/
private theorem fderiv_fderiv_mul_comm_of_mul_zero {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) {a b : M2 n} (hab : a * b = 0)
    (hba : b * a = 0) :
    ∀ x ∈ Dom n, fderiv ℂ (fun y => fderiv ℂ G y (y * b)) x (x * a) =
      fderiv ℂ (fun y => fderiv ℂ G y (y * a)) x (x * b) := by
  intro x hx
  have hcd : ContDiffAt ℂ ∞ G x := hG.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)
  have hsym : IsSymmSndFDerivAt ℂ G x := hcd.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  have hdd : DifferentiableAt ℂ (fderiv ℂ G) x :=
    (hcd.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have key : ∀ c d : M2 n, c * d = 0 →
      fderiv ℂ (fun y => fderiv ℂ G y (y * d)) x (x * c) = fderiv ℂ (fderiv ℂ G) x (x * c) (x * d) := by
    intro c d hcd0
    let R : M2 n →L[ℂ] M2 n := (LinearMap.mulRight ℂ d).toContinuousLinearMap
    have hfd := hdd.hasFDerivAt.clm_apply R.hasFDerivAt
    have h0 : R (x * c) = 0 := by
      show x * c * d = 0
      rw [Matrix.mul_assoc, hcd0, Matrix.mul_zero]
    have e1 : fderiv ℂ (fun y => fderiv ℂ G y (y * d)) x (x * c) =
        fderiv ℂ G x (R (x * c)) + fderiv ℂ (fderiv ℂ G) x (x * c) (R x) :=
      congrArg (fun T => T (x * c)) hfd.fderiv
    rw [e1, h0, map_zero, zero_add]
    rfl
  rw [key a b hab, key b a hba]
  exact hsym.eq _ _

/- English proof (translation)
Set `Lm : M2 n →L[ℂ] (M2 n →L[ℂ] M2 n)` to `(LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℂ (M2 n)).toContinuousLinearMap`. Establish `hcd : ContDiffAt ℂ ∞ F x` using `hF.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)`. Establish `hΦ : DifferentiableAt ℂ (iteratedFDeriv ℂ m F) x` using `hcd.differentiableAt_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m))`. Establish `hfd` using `hΦ.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap (g := fun _ : Fin m => fun y => Lm y) (fun _ => Lm.hasFDerivAt)`. Establish `hfd2` using `hfd.continuousMultilinear_apply_const (fun i => W i.succ)`.

Establish `eL : iteratedFDeriv ℂ (m + 1) F x (fun i => x * W i) = fderiv ℂ (iteratedFDeriv ℂ m F) x (x * W 0) (fun i => x * W i.succ)` using `iteratedFDeriv_succ_apply_left _`. Establish `e1 : fderiv ℂ (fun y => iteratedFDeriv ℂ m F y (fun i => y * W i.succ)) x (x * W 0) = fderiv ℂ (iteratedFDeriv ℂ m F) x (x * W 0) (fun i => x * W i.succ) + (iteratedFDeriv ℂ m F x).fderivCompContinuousLinearMap (fun _ => Lm x) (fun _ => Lm (x * W 0)) (fun i => W i.succ)` using `congrArg (fun T => T (x * W 0)) hfd2.fderiv`. Establish `hS : (iteratedFDeriv ℂ m F x).fderivCompContinuousLinearMap (fun _ => Lm x) (fun _ => Lm (x * W 0)) (fun i => W i.succ) = 0`. Use `(ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply (iteratedFDeriv ℂ m F x) (fun _ => Lm x) (fun _ => Lm (x * W 0)) (fun i => W i.succ)).trans ?_` and prove the remaining obligations. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `i _`. Apply `ContinuousMultilinearMap.map_coord_zero _ i` to reduce the goal to its premises. Use `(congrArg (fun f : M2 n →L[ℂ] M2 n => f (W i.succ)) (Function.update_self i (Lm (x * W 0)) (fun _ : Fin m => Lm x))).trans ?_` and prove the remaining obligations. Use `show x * W 0 * W i.succ = 0`. Rewrite using `[Matrix.mul_assoc, hW i, Matrix.mul_zero]`.

Rewrite using `[eL, e1, hS, add_zero]`.
-/
private theorem iteratedFDeriv_succ_mul_eq_fderiv_of_mul_zero {F : M2 n → ℂ} (hF : ContDiffOn ℂ ∞ F (Dom n)) {m : ℕ} (W : Fin (m + 1) → M2 n)
    (hW : ∀ i : Fin m, W 0 * W i.succ = 0) {x : M2 n} (hx : x ∈ Dom n) :
    iteratedFDeriv ℂ (m + 1) F x (fun i => x * W i) =
      fderiv ℂ (fun y => iteratedFDeriv ℂ m F y (fun i => y * W i.succ)) x (x * W 0) := by
  let Lm : M2 n →L[ℂ] (M2 n →L[ℂ] M2 n) :=
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℂ (M2 n)).toContinuousLinearMap
  have hcd : ContDiffAt ℂ ∞ F x := hF.contDiffAt (isOpen_dom_analytic_determinants.mem_nhds hx)
  have hΦ : DifferentiableAt ℂ (iteratedFDeriv ℂ m F) x :=
    hcd.differentiableAt_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m))
  have hfd := hΦ.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (g := fun _ : Fin m => fun y => Lm y) (fun _ => Lm.hasFDerivAt)
  have hfd2 := hfd.continuousMultilinear_apply_const (fun i => W i.succ)
  have eL : iteratedFDeriv ℂ (m + 1) F x (fun i => x * W i) =
      fderiv ℂ (iteratedFDeriv ℂ m F) x (x * W 0) (fun i => x * W i.succ) :=
    iteratedFDeriv_succ_apply_left _
  have e1 : fderiv ℂ (fun y => iteratedFDeriv ℂ m F y (fun i => y * W i.succ)) x (x * W 0) =
      fderiv ℂ (iteratedFDeriv ℂ m F) x (x * W 0) (fun i => x * W i.succ) +
        (iteratedFDeriv ℂ m F x).fderivCompContinuousLinearMap (fun _ => Lm x) (fun _ => Lm (x * W 0))
          (fun i => W i.succ) :=
    congrArg (fun T => T (x * W 0)) hfd2.fderiv
  have hS : (iteratedFDeriv ℂ m F x).fderivCompContinuousLinearMap (fun _ => Lm x) (fun _ => Lm (x * W 0))
      (fun i => W i.succ) = 0 := by
    refine (ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply (iteratedFDeriv ℂ m F x)
      (fun _ => Lm x) (fun _ => Lm (x * W 0)) (fun i => W i.succ)).trans ?_
    apply Finset.sum_eq_zero
    intro i _
    apply ContinuousMultilinearMap.map_coord_zero _ i
    refine (congrArg (fun f : M2 n →L[ℂ] M2 n => f (W i.succ))
      (Function.update_self i (Lm (x * W 0)) (fun _ : Fin m => Lm x))).trans ?_
    show x * W 0 * W i.succ = 0
    rw [Matrix.mul_assoc, hW i, Matrix.mul_zero]
  rw [eL, e1, hS, add_zero]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact hG`. Consider the case `cons a l ih => exact contDiffOn_fderiv_apply_mul_right ih a`.
-/
private theorem contDiffOn_foldr_fderiv_mul (l : List (M2 n)) {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) :
    ContDiffOn ℂ ∞ (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G) (Dom n) := by
  induction l with
  | nil => exact hG
  | cons a l ih => exact contDiffOn_fderiv_apply_mul_right ih a

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact h`. Consider the case `cons a l ih => exact fderiv_apply_mul_equivariant_of_equivariant (contDiffOn_foldr_fderiv_mul l hG) hP c ih a`.
-/
private theorem foldr_fderiv_mul_left_eq_of_equivariant (l : List (M2 n)) {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) {P : M2 n}
    (hP : InP P) (c : ℂ) (h : ∀ x ∈ Dom n, G (P * x) = c * G x) :
    ∀ x ∈ Dom n, l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G (P * x) =
      c * l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G x := by
  induction l with
  | nil => exact h
  | cons a l ih => exact fderiv_apply_mul_equivariant_of_equivariant (contDiffOn_foldr_fderiv_mul l hG) hP c ih a

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `W _ x _`. Simplify using `[iteratedFDeriv_zero_apply]`.

Consider the case `succ m ih`. Introduce `W hW x hx`. Rewrite using `[iteratedFDeriv_succ_mul_eq_fderiv_of_mul_zero hF W (fun i => hW 0 i.succ) hx, List.ofFn_succ, List.foldr_cons]`. Conclude with `eqOn_fderiv_apply_mul_of_eqOn (fun y hy => ih (fun i => W i.succ) (fun i j => hW _ _) y hy) (W 0) hx`.
-/
private theorem iteratedFDeriv_mul_eq_foldr_fderiv_of_mul_zero {F : M2 n → ℂ} (hF : ContDiffOn ℂ ∞ F (Dom n)) :
    ∀ (m : ℕ) (W : Fin m → M2 n), (∀ i j, W i * W j = 0) → ∀ x ∈ Dom n,
      iteratedFDeriv ℂ m F x (fun i => x * W i) =
        (List.ofFn W).foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) F x := by
  intro m
  induction m with
  | zero =>
    intro W _ x _
    simp [iteratedFDeriv_zero_apply]
  | succ m ih =>
    intro W hW x hx
    rw [iteratedFDeriv_succ_mul_eq_fderiv_of_mul_zero hF W (fun i => hW 0 i.succ) hx, List.ofFn_succ, List.foldr_cons]
    exact eqOn_fderiv_apply_mul_of_eqOn (fun y hy => ih (fun i => W i.succ) (fun i j => hW _ _) y hy) (W 0) hx

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => intro x _`. Both sides reduce to the same expression. Consider the case `cons a l ih`. Introduce `x hx`.

Establish `ha : Z * a = 0 ∧ a * Z = 0` using `hZ a (by simp)`. Establish `h1` using `fderiv_fderiv_mul_comm_of_mul_zero (contDiffOn_foldr_fderiv_mul l hG) ha.1 ha.2 x hx`. Establish `h2` using `eqOn_fderiv_apply_mul_of_eqOn (ih (fun b hb => hZ b (List.mem_cons_of_mem a hb))) a hx`. Conclude with `h1.trans h2`.
-/
private theorem foldr_fderiv_comm_fderiv_of_mul_zero (l : List (M2 n)) {G : M2 n → ℂ} (hG : ContDiffOn ℂ ∞ G (Dom n)) (Z : M2 n)
    (hZ : ∀ a ∈ l, Z * a = 0 ∧ a * Z = 0) :
    Set.EqOn (fun x => fderiv ℂ (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G) x (x * Z))
      (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) (fun x => fderiv ℂ G x (x * Z))) (Dom n) := by
  induction l with
  | nil => intro x _; rfl
  | cons a l ih =>
    intro x hx
    have ha : Z * a = 0 ∧ a * Z = 0 := hZ a (by simp)
    have h1 := fderiv_fderiv_mul_comm_of_mul_zero (contDiffOn_foldr_fderiv_mul l hG) ha.1 ha.2 x hx
    have h2 := eqOn_fderiv_apply_mul_of_eqOn (ih (fun b hb => hZ b (List.mem_cons_of_mem a hb))) a hx
    exact h1.trans h2

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => intro G _ _ x _`. Both sides reduce to the same expression. Consider the case `cons a l ih`. Introduce `G hG hl x hx`.

Establish `e1` using `ih (contDiffOn_fderiv_apply_mul_right hG a) (fun b hb c hc => hl b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc)) hx`. Establish `e2` using `foldr_fderiv_comm_fderiv_of_mul_zero l hG a (fun b hb => ⟨hl a (by simp) b (by simp [hb]), hl b (by simp [hb]) a (by simp)⟩) hx`. Rewrite using `[List.reverse_cons, List.foldr_append]`. Conclude with `e1.trans e2.symm`.
-/
private theorem foldr_fderiv_reverse_eqOn_of_mul_zero (l : List (M2 n)) :
    ∀ {G : M2 n → ℂ}, ContDiffOn ℂ ∞ G (Dom n) → (∀ a ∈ l, ∀ b ∈ l, a * b = 0) →
      Set.EqOn (l.reverse.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G)
        (l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G) (Dom n) := by
  induction l with
  | nil => intro G _ _ x _; rfl
  | cons a l ih =>
    intro G hG hl x hx
    have e1 := ih (contDiffOn_fderiv_apply_mul_right hG a)
      (fun b hb c hc => hl b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc)) hx
    have e2 := foldr_fderiv_comm_fderiv_of_mul_zero l hG a
      (fun b hb => ⟨hl a (by simp) b (by simp [hb]), hl b (by simp [hb]) a (by simp)⟩) hx
    rw [List.reverse_cons, List.foldr_append]
    exact e1.trans e2.symm

/- English proof (translation)
Establish `hin : ∀ k, ι k ∈ Dom n` using `fun k => mem_dom_of_inG ((hK _).mpr ⟨k, rfl⟩).1`. Establish `hint : ∀ H K : M2 n → ℂ, ContDiffOn ℂ ∞ H (Dom n) → ContDiffOn ℂ ∞ K (Dom n) → Integrable (fun k => H (ι k) * K (ι k)) μ`. Introduce `H K hH hK'`. Establish `c1 : Continuous (fun k => H (ι k))` using `hH.continuousOn.comp_continuous hι hin`. Establish `c2 : Continuous (fun k => K (ι k))` using `hK'.continuousOn.comp_continuous hι hin`.

Conclude with `(c1.mul c2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Proceed by induction on `l with`. Consider the case `nil`. Introduce `G2 _ _`. Simplify using the standard rewrite rules.

Consider the case `cons a l ih`. Introduce `G2 hG2 h2`. Establish `hl' : ∀ b ∈ l, ∀ c ∈ l, b * c = 0` using `fun b hb c hc => hl b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc)`. Use `set H1 := l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G1 with hH1def`. Establish `hH1 : ContDiffOn ℂ ∞ H1 (Dom n)` using `contDiffOn_foldr_fderiv_mul l hG1`.

Establish `hH1e : ∀ P x, InP P → x ∈ Dom n → H1 (P * x) = χ1 P * H1 x` using `fun P x hP hx => foldr_fderiv_mul_left_eq_of_equivariant l hG1 hP (χ1 P) (fun y hy => h1 P y hP hy) x hx`. Establish `hG2' : ContDiffOn ℂ ∞ (fun x => fderiv ℂ G2 x (x * a)) (Dom n)` using `contDiffOn_fderiv_apply_mul_right hG2 a`. Establish `h2' : ∀ P x, InP P → x ∈ Dom n → fderiv ℂ G2 (P * x) (P * x * a) = χ2 P * fderiv ℂ G2 x (x * a)` using `fun P x hP hx => fderiv_apply_mul_equivariant_of_equivariant hG2 hP (χ2 P) (fun y hy => h2 P y hP hy) a x hx`. Establish `hinv` using `hI n H1 G2 (Dom n) isOpen_dom_analytic_determinants (fun x hx => mem_dom_of_inG hx) hH1 hG2 (by`. Introduce `p x hp hp21 hx`.

Establish `hP : InP p` using `⟨hp, hp21⟩`. Establish `hxD` using `mem_dom_of_inG hx`. Rewrite using `[hH1e p x hP hxD, h2 p x hP hxD, ← h12 p hP]`. Use the proof step `ring) Kg μ ι hι hK a`. Rewrite `hinv` using `[integral_add (hint _ _ (contDiffOn_fderiv_apply_mul_right hH1 a) hG2) (hint _ _ hH1 hG2')]`.

Establish `eA : ∫ k, (fun x => fderiv ℂ H1 x (x * a)) (ι k) * G2 (ι k) ∂μ = -∫ k, H1 (ι k) * (fun x => fderiv ℂ G2 x (x * a)) (ι k) ∂μ` using `eq_neg_of_add_eq_zero_left hinv`. Establish `eB` using `ih hl' (fun x => fderiv ℂ G2 x (x * a)) hG2' h2'`. Simplify using `only [List.foldr_cons, List.reverse_cons, List.foldr_append, List.foldr_nil, List.length_cons]`. Rewrite using `[eA, eB, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem transpose_lemma_14 (hI : InfInv) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg]
    [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n)
    (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (χ1 χ2 : M2 n → ℂ)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (l : List (M2 n)) (hl : ∀ a ∈ l, ∀ b ∈ l, a * b = 0) (G1 : M2 n → ℂ) (hG1 : ContDiffOn ℂ ∞ G1 (Dom n))
    (h1 : ∀ P x, InP P → x ∈ Dom n → G1 (P * x) = χ1 P * G1 x) :
    ∀ (G2 : M2 n → ℂ), ContDiffOn ℂ ∞ G2 (Dom n) → (∀ P x, InP P → x ∈ Dom n → G2 (P * x) = χ2 P * G2 x) →
      ∫ k, l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G1 (ι k) * G2 (ι k) ∂μ =
        (-1) ^ l.length * ∫ k, G1 (ι k) * l.reverse.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G2 (ι k) ∂μ := by
  have hin : ∀ k, ι k ∈ Dom n := fun k => mem_dom_of_inG ((hK _).mpr ⟨k, rfl⟩).1
  have hint : ∀ H K : M2 n → ℂ, ContDiffOn ℂ ∞ H (Dom n) → ContDiffOn ℂ ∞ K (Dom n) →
      Integrable (fun k => H (ι k) * K (ι k)) μ := by
    intro H K hH hK'
    have c1 : Continuous (fun k => H (ι k)) := hH.continuousOn.comp_continuous hι hin
    have c2 : Continuous (fun k => K (ι k)) := hK'.continuousOn.comp_continuous hι hin
    exact (c1.mul c2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  induction l with
  | nil =>
    intro G2 _ _
    simp
  | cons a l ih =>
    intro G2 hG2 h2
    have hl' : ∀ b ∈ l, ∀ c ∈ l, b * c = 0 :=
      fun b hb c hc => hl b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc)
    set H1 := l.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) G1 with hH1def
    have hH1 : ContDiffOn ℂ ∞ H1 (Dom n) := contDiffOn_foldr_fderiv_mul l hG1
    have hH1e : ∀ P x, InP P → x ∈ Dom n → H1 (P * x) = χ1 P * H1 x :=
      fun P x hP hx => foldr_fderiv_mul_left_eq_of_equivariant l hG1 hP (χ1 P) (fun y hy => h1 P y hP hy) x hx
    have hG2' : ContDiffOn ℂ ∞ (fun x => fderiv ℂ G2 x (x * a)) (Dom n) := contDiffOn_fderiv_apply_mul_right hG2 a
    have h2' : ∀ P x, InP P → x ∈ Dom n → fderiv ℂ G2 (P * x) (P * x * a) = χ2 P * fderiv ℂ G2 x (x * a) :=
      fun P x hP hx => fderiv_apply_mul_equivariant_of_equivariant hG2 hP (χ2 P) (fun y hy => h2 P y hP hy) a x hx
    have hinv := hI n H1 G2 (Dom n) isOpen_dom_analytic_determinants (fun x hx => mem_dom_of_inG hx) hH1 hG2
      (by
        intro p x hp hp21 hx
        have hP : InP p := ⟨hp, hp21⟩
        have hxD := mem_dom_of_inG hx
        rw [hH1e p x hP hxD, h2 p x hP hxD, ← h12 p hP]
        ring) Kg μ ι hι hK a
    rw [integral_add (hint _ _ (contDiffOn_fderiv_apply_mul_right hH1 a) hG2) (hint _ _ hH1 hG2')] at hinv
    have eA : ∫ k, (fun x => fderiv ℂ H1 x (x * a)) (ι k) * G2 (ι k) ∂μ =
        -∫ k, H1 (ι k) * (fun x => fderiv ℂ G2 x (x * a)) (ι k) ∂μ := eq_neg_of_add_eq_zero_left hinv
    have eB := ih hl' (fun x => fderiv ℂ G2 x (x * a)) hG2' h2'
    simp only [List.foldr_cons, List.reverse_cons, List.foldr_append, List.foldr_nil, List.length_cons]
    rw [eA, eB, pow_succ]
    ring

/- English proof (translation)
Establish `hin : ∀ k, ι k ∈ Dom n` using `fun k => mem_dom_of_inG ((hK _).mpr ⟨k, rfl⟩).1`. Establish `hl : ∀ a ∈ List.ofFn W, ∀ b ∈ List.ofFn W, a * b = 0`. Introduce `a ha b hb`. Take `⟨i, rfl⟩` from `List.mem_ofFn.mp ha`. Take `⟨j, rfl⟩` from `List.mem_ofFn.mp hb`.

Conclude with `hW i j`. Establish `eA : ∀ k, iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W i) = (List.ofFn W).foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) F1 (ι k)` using `fun k => iteratedFDeriv_mul_eq_foldr_fderiv_of_mul_zero hF1 N W hW (ι k) (hin k)`. Establish `eB : ∀ k, iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W i) = (List.ofFn W).reverse.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) F2 (ι k)` using `fun k => (iteratedFDeriv_mul_eq_foldr_fderiv_of_mul_zero hF2 N W hW (ι k) (hin k)).trans (foldr_fderiv_reverse_eqOn_of_mul_zero (List.ofFn W) hF2 hl (hin k)).symm`. Repeatedly rewrite using `[eA, eB]`. Establish `key` using `transpose_lemma_14 hI Kg μ ι hι hK χ1 χ2 h12 (List.ofFn W) hl F1 hF1 h1 F2 hF2 h2`.

Rewrite `key` using `[List.length_ofFn]`. Conclude with `key`.
-/
theorem transpose (hI : InfInv) (F1 F2 : M2 n → ℂ) (χ1 χ2 : M2 n → ℂ) (hF1 : ContDiffOn ℂ ∞ F1 (Dom n))
    (hF2 : ContDiffOn ℂ ∞ F2 (Dom n)) (h1 : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = χ1 P * F1 x)
    (h2 : ∀ P x, InP P → x ∈ Dom n → F2 (P * x) = χ2 P * F2 x)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (N : ℕ) (W : Fin N → M2 n) (hW : ∀ a b, W a * W b = 0) :
    ∫ k, iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W i) * F2 (ι k) ∂μ =
      (-1) ^ N * ∫ k, F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W i) ∂μ := by
  have hin : ∀ k, ι k ∈ Dom n := fun k => mem_dom_of_inG ((hK _).mpr ⟨k, rfl⟩).1
  have hl : ∀ a ∈ List.ofFn W, ∀ b ∈ List.ofFn W, a * b = 0 := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    exact hW i j
  have eA : ∀ k, iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W i) =
      (List.ofFn W).foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) F1 (ι k) :=
    fun k => iteratedFDeriv_mul_eq_foldr_fderiv_of_mul_zero hF1 N W hW (ι k) (hin k)
  have eB : ∀ k, iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W i) =
      (List.ofFn W).reverse.foldr (fun Z H => fun x => fderiv ℂ H x (x * Z)) F2 (ι k) :=
    fun k => (iteratedFDeriv_mul_eq_foldr_fderiv_of_mul_zero hF2 N W hW (ι k) (hin k)).trans (foldr_fderiv_reverse_eqOn_of_mul_zero (List.ofFn W) hF2 hl (hin k)).symm
  simp_rw [eA, eB]
  have key := transpose_lemma_14 hI Kg μ ι hι hK χ1 χ2 h12 (List.ofFn W) hl F1 hF1 h1 F2 hF2 h2
  rw [List.length_ofFn] at key
  exact key

/- English proof (translation)
Set `g : M2 n →L[ℂ] M2 n` to `(LinearMap.mulLeft ℂ M).toContinuousLinearMap`. Establish `hpre : IsOpen (g ⁻¹' U)` using `hU.preimage g.continuous`. Establish `hx' : x ∈ g ⁻¹' U` using `hx`. Establish `key` using `g.iteratedFDerivWithin_comp_right hF hU.uniqueDiffOn hpre.uniqueDiffOn hx' (i := N) (by exact_mod_cast le_top)`. Establish `e1 : iteratedFDerivWithin ℂ N (F ∘ g) (g ⁻¹' U) x = iteratedFDeriv ℂ N (F ∘ g) x` using `iteratedFDerivWithin_of_isOpen N hpre hx'`.

Establish `e2 : iteratedFDerivWithin ℂ N F U (g x) = iteratedFDeriv ℂ N F (g x)` using `iteratedFDerivWithin_of_isOpen N hU hx`. Establish `key2 : iteratedFDeriv ℂ N (F ∘ g) x = (iteratedFDeriv ℂ N F (g x)).compContinuousLinearMap fun _ => g`. Rewrite using `[← e1, ← e2]`. Conclude with `key`. Establish `hfg : (fun y => F (M * y)) = F ∘ g` using `rfl`.

Rewrite using `[hfg, key2]`. Both sides reduce to the same expression.
-/
theorem iteratedFDeriv_left_mul (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (M x : M2 n)
    (hx : M * x ∈ U) (N : ℕ) (v : Fin N → M2 n) :
    iteratedFDeriv ℂ N (fun y => F (M * y)) x v = iteratedFDeriv ℂ N F (M * x) (fun i => M * v i) := by
  let g : M2 n →L[ℂ] M2 n := (LinearMap.mulLeft ℂ M).toContinuousLinearMap
  have hpre : IsOpen (g ⁻¹' U) := hU.preimage g.continuous
  have hx' : x ∈ g ⁻¹' U := hx
  have key := g.iteratedFDerivWithin_comp_right hF hU.uniqueDiffOn hpre.uniqueDiffOn hx' (i := N)
    (by exact_mod_cast le_top)
  have e1 : iteratedFDerivWithin ℂ N (F ∘ g) (g ⁻¹' U) x = iteratedFDeriv ℂ N (F ∘ g) x :=
    iteratedFDerivWithin_of_isOpen N hpre hx'
  have e2 : iteratedFDerivWithin ℂ N F U (g x) = iteratedFDeriv ℂ N F (g x) :=
    iteratedFDerivWithin_of_isOpen N hU hx
  have key2 : iteratedFDeriv ℂ N (F ∘ g) x =
      (iteratedFDeriv ℂ N F (g x)).compContinuousLinearMap fun _ => g := by
    rw [← e1, ← e2]
    exact key
  have hfg : (fun y => F (M * y)) = F ∘ g := rfl
  rw [hfg, key2]
  rfl

/- English proof (translation)
Set `Lm : M2 n →L[ℂ] (M2 n →L[ℂ] M2 n)` to `(LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℂ (M2 n)).toContinuousLinearMap`. Establish `key : ∀ y ∈ Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}, iteratedFDeriv ℂ N (fun x => F (ι y.1 * x) * c y.1) y.2 = c y.1 • ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ (fun _ => Lm (ι y.1)) (iteratedFDeriv ℂ N F (ι y.1 * …`. Introduce and unpack `⟨k, x⟩ ⟨-, hx⟩`. Establish `hx' : ι k * x ∈ U` using `hx k`. Establish `hcd : ContDiffAt ℂ N (fun z => F (ι k * z)) x`.

Establish `h1 : ContDiffAt ℂ ∞ F (Lm (ι k) x)` using `hF.contDiffAt (hU.mem_nhds hx')`. Conclude with `(h1.comp x (Lm (ι k)).contDiff.contDiffAt).of_le (by exact_mod_cast le_top)`. Establish `hfun : (fun z => F (ι k * z) * c k) = c k • (fun z => F (ι k * z))`. Use function extensionality and compare the values at `z`. Simplify using `[mul_comm]`.

Simplify using `only`. Rewrite using `[hfun, iteratedFDeriv_const_smul_apply hcd]`. Use `congr 1`. Use extensionality with `v`. Rewrite using `[iteratedFDeriv_left_mul F U hU hF (ι k) x hx' N v]`.

Both sides reduce to the same expression. Use `ContinuousOn.congr ?_ key` and prove the remaining obligations. Use `ContinuousOn.smul (hc.comp continuous_fst).continuousOn ?_` and prove the remaining obligations. Establish `hD : ContinuousOn (iteratedFDeriv ℂ N F) U`. Use `hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) hU.uniqueDiffOn` as an intermediate fact.

Conclude with `this.congr (fun y hy => (iteratedFDerivWithin_of_isOpen N hU hy).symm)`. Establish `h1 : ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N F (ι y.1 * y.2)) (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U})` using `hD.comp ((hι.comp continuous_fst).mul continuous_snd).continuousOn (fun y hy => hy.2 y.1)`. Establish `h2 : Continuous (fun y : Kg × M2 n => ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ (fun _ => Lm (ι y.1)))` using `(ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ).cont.comp (continuous_pi fun _ => Lm.continuous.comp (hι.comp continuous_fst))`. Conclude with `h2.continuousOn.clm_apply h1`.
-/
theorem continuousOn_iteratedFDeriv_translate (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (Kg : Type) [TopologicalSpace Kg] (ι : Kg → M2 n) (hι : Continuous ι) (c : Kg → ℂ) (hc : Continuous c) (N : ℕ) :
    ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N (fun x => F (ι y.1 * x) * c y.1) y.2)
      (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}) := by
  let Lm : M2 n →L[ℂ] (M2 n →L[ℂ] M2 n) :=
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℂ (M2 n)).toContinuousLinearMap
  have key : ∀ y ∈ Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U},
      iteratedFDeriv ℂ N (fun x => F (ι y.1 * x) * c y.1) y.2 =
        c y.1 • ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
          (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ (fun _ => Lm (ι y.1))
          (iteratedFDeriv ℂ N F (ι y.1 * y.2)) := by
    rintro ⟨k, x⟩ ⟨-, hx⟩
    have hx' : ι k * x ∈ U := hx k
    have hcd : ContDiffAt ℂ N (fun z => F (ι k * z)) x := by
      have h1 : ContDiffAt ℂ ∞ F (Lm (ι k) x) := hF.contDiffAt (hU.mem_nhds hx')
      exact (h1.comp x (Lm (ι k)).contDiff.contDiffAt).of_le (by exact_mod_cast le_top)
    have hfun : (fun z => F (ι k * z) * c k) = c k • (fun z => F (ι k * z)) := by
      funext z
      simp [mul_comm]
    simp only
    rw [hfun, iteratedFDeriv_const_smul_apply hcd]
    congr 1
    ext v
    rw [iteratedFDeriv_left_mul F U hU hF (ι k) x hx' N v]
    rfl
  refine ContinuousOn.congr ?_ key
  refine ContinuousOn.smul (hc.comp continuous_fst).continuousOn ?_
  have hD : ContinuousOn (iteratedFDeriv ℂ N F) U := by
    have := hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) hU.uniqueDiffOn
    exact this.congr (fun y hy => (iteratedFDerivWithin_of_isOpen N hU hy).symm)
  have h1 : ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N F (ι y.1 * y.2))
      (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}) :=
    hD.comp ((hι.comp continuous_fst).mul continuous_snd).continuousOn (fun y hy => hy.2 y.1)
  have h2 : Continuous (fun y : Kg × M2 n =>
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ (fun _ => Lm (ι y.1))) :=
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
        (fun _ : Fin N => M2 n) (fun _ => M2 n) ℂ).cont.comp
      (continuous_pi fun _ => Lm.continuous.comp (hι.comp continuous_fst))
  exact h2.continuousOn.clm_apply h1

end PositivityTheory.Rg.Sw.LVs

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.GelfandHW

noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def smoothS (n : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  carrier := {F | ContDiffOn ℂ ∞ F (OmegaSet n)}
  add_mem' hF hG := hF.add hG
  zero_mem' := contDiffOn_const
  smul_mem' c _ hF := hF.const_smul c

/- English proof (translation)
Use `show IsOpen {z : Matrix (Fin n) (Fin n) ℂ | ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0}`. Rewrite using `[Set.setOf_forall]`. Use `isOpen_iInter_of_finite fun i => isOpen_ne_fun ?_ continuous_const` and prove the remaining obligations. Use `show Continuous fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z`. Distinguish the cases in `h : (i : ℕ) + 1 ≤ n`.

Establish `e : (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z) = fun z => (z.submatrix (Fin.castLE h) (Fin.castLE h)).det` using `funext fun z => dif_pos h`. Rewrite using `[e]`. Conclude with `(continuous_id.matrix_submatrix _ _).matrix_det`. Establish `e : (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z) = fun _ => 0`. Use function extensionality and compare the values at `fun z => dif_neg h`.

Rewrite using `[e]`. Conclude with `continuous_const`.
-/
private theorem isOpen_OmegaSet' : IsOpen (OmegaSet n) := by
  show IsOpen {z : Matrix (Fin n) (Fin n) ℂ | ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0}
  rw [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_ne_fun ?_ continuous_const
  show Continuous fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z
  by_cases h : (i : ℕ) + 1 ≤ n
  · have e : (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z) =
        fun z => (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := funext fun z => dif_pos h
    rw [e]
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  · have e : (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z) = fun _ => 0 :=
      funext fun z => dif_neg h
    rw [e]
    exact continuous_const

/- English proof (translation)
Use `show fderiv ℂ G z (X * z) = fderiv ℂ H z (X * z)`. Rewrite using `[Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (isOpen_OmegaSet'.mem_nhds hz) h)]`.
-/
theorem lhol_congr {X : Matrix (Fin n) (Fin n) ℂ} {G H : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : Set.EqOn G H (OmegaSet n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol X G z = Lhol X H z := by
  show fderiv ℂ G z (X * z) = fderiv ℂ H z (X * z)
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (isOpen_OmegaSet'.mem_nhds hz) h)]

/- English proof (translation)
Establish `h1` using `((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_OmegaSet').1 hF).2`. Establish `h2 : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => X * z)`. Use `contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply]`. Conclude with `ContDiff.sum fun c _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id c) b)`.

Conclude with `h1.clm_apply h2.contDiffOn`.
-/
theorem lhol_mem {X : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) : ContDiffOn ℂ ∞ (Lhol X F) (OmegaSet n) := by
  have h1 :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_OmegaSet').1 hF).2
  have h2 : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => X * z) := by
    refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun c _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id c) b)
  exact h1.clm_apply h2.contDiffOn

def ltOp (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  (OmegaSet n).indicator (Lhol X F)

/- English proof (translation)
Conclude with `Set.indicator_of_mem hz _`.
-/
theorem ltOp_of_mem {X : Matrix (Fin n) (Fin n) ℂ} (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) : ltOp X F z = Lhol X F z := by
  exact Set.indicator_of_mem hz _

/- English proof (translation)
Simplify using `[ltOp, hz]`.
-/
theorem ltOp_of_not_mem {X : Matrix (Fin n) (Fin n) ℂ} (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∉ OmegaSet n) : ltOp X F z = 0 := by
  simp [ltOp, hz]

/- English proof (translation)
Conclude with `(lhol_mem hF).congr fun z hz => ltOp_of_mem F hz`.
-/
theorem ltOp_mem {X : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) : ContDiffOn ℂ ∞ (ltOp X F) (OmegaSet n) := by
  exact (lhol_mem hF).congr fun z hz => ltOp_of_mem F hz

/- English proof (translation)
Apply the tactic sequence `exact ((hF.differentiableOn (by simp <;> exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) z hz).differentiableAt (isOpen_OmegaSet'.mem_nhds hz)`.
-/
theorem differentiableAt_of_mem {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ F z := by
  exact ((hF.differentiableOn (by simp <;> exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) z hz).differentiableAt (isOpen_OmegaSet'.mem_nhds hz)

def eOp (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (smoothS n) where
  toFun F := ⟨ltOp X F, ltOp_mem F.2⟩
  map_add' F G := by
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp only [Submodule.coe_add, Pi.add_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (F.1 + G.1) z (X * z) = fderiv ℂ F.1 z (X * z) + fderiv ℂ G.1 z (X * z)
      erw [((differentiableAt_of_mem F.2 hz).hasFDerivAt.add (differentiableAt_of_mem G.2 hz).hasFDerivAt).fderiv]
      rfl
    · simp only [Submodule.coe_add, Pi.add_apply, ltOp_of_not_mem _ hz, add_zero]
  map_smul' c F := by
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (c • F.1) z (X * z) = c • fderiv ℂ F.1 z (X * z)
      erw [fderiv_const_smul (differentiableAt_of_mem F.2 hz)]
      rfl
    · simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, ltOp_of_not_mem _ hz, smul_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eOp_apply (X : Matrix (Fin n) (Fin n) ℂ) (F : smoothS n) :
    ((eOp X F : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) = ltOp X F := rfl

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `F`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Use `show ltOp (X - Y) F.1 z = ltOp X F.1 z - ltOp Y F.1 z`.

Distinguish the cases in `hz : z ∈ OmegaSet n`. Rewrite using `[ltOp_of_mem _ hz, ltOp_of_mem _ hz, ltOp_of_mem _ hz] show fderiv ℂ F.1 z ((X - Y) * z) = fderiv ℂ F.1 z (X * z) - fderiv ℂ F.1 z (Y * z)`. Rewrite using `[Matrix.sub_mul, map_sub]`. Rewrite using `[ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, sub_zero]`.
-/
theorem eOp_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : eOp (X - Y) = eOp X - eOp Y := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext z
  show ltOp (X - Y) F.1 z = ltOp X F.1 z - ltOp Y F.1 z
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, ltOp_of_mem _ hz, ltOp_of_mem _ hz]
    show fderiv ℂ F.1 z ((X - Y) * z) = fderiv ℂ F.1 z (X * z) - fderiv ℂ F.1 z (Y * z)
    rw [Matrix.sub_mul, map_sub]
  · rw [ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, sub_zero]

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `F`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Use `show ltOp 0 F z = 0`.

Distinguish the cases in `hz : z ∈ OmegaSet n`. Rewrite using `[ltOp_of_mem _ hz] show fderiv ℂ F.1 z (0 * z) = 0`. Rewrite using `[Matrix.zero_mul, map_zero]`. Rewrite using `[ltOp_of_not_mem _ hz]`.
-/
theorem eOp_zero : eOp (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  apply LinearMap.ext; intro F
  apply Subtype.ext; funext z
  show ltOp 0 F z = 0
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz]
    show fderiv ℂ F.1 z (0 * z) = 0
    rw [Matrix.zero_mul, map_zero]
  · rw [ltOp_of_not_mem _ hz]

/- English proof (translation)
Establish `hc` using `hF.contDiffAt (isOpen_OmegaSet'.mem_nhds hz)`. Establish `h1` using `((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_OmegaSet').1 hF).2`. Apply the tactic sequence `have hd := ((h1.differentiableOn (by simp <;> exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) z hz).differentiableAt (isOpen_OmegaSet'.mem_nhds hz) |>.hasFDerivAt`. Apply the tactic sequence `have hs := hc.isSymmSndFDerivAt (by first | exact le_top | (simp; done) | (simp <;> exact (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) : ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω))) | (simp <;> decide))`. Set `LX : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toContinuousLinearMap { toFun := fun w => X * w map_add' := fun a b => Matrix.mul_add X a b map_smul' := fun c a => Matrix.mul_smul X c a }`.

Set `LY : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toContinuousLinearMap { toFun := fun w => Y * w map_add' := fun a b => Matrix.mul_add Y a b map_smul' := fun c a => Matrix.mul_smul Y c a }`. Use `show fderiv ℂ (fun w => fderiv ℂ F w (LY w)) z (X * z) - fderiv ℂ (fun w => fderiv ℂ F w (LX w)) z (Y * z) = fderiv ℂ F z ((Y * X - X * Y) * z)`. Use `erw [(hd.clm_apply LY.hasFDerivAt).fderiv, (hd.clm_apply LX.hasFDerivAt).fderiv]`. Use `show fderiv ℂ F z (Y * (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) - (fderiv ℂ F z (X * (Y * z)) + fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z)) = _`. Rewrite using `[show fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) = fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z) from hs (X * z) (Y * z)]`.

Rewrite using `[Matrix.sub_mul, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
private theorem Lhol_commutator_on_OmegaSet {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : ContDiffOn ℂ ∞ F (OmegaSet n))
    (X Y : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol X (Lhol Y F) z - Lhol Y (Lhol X F) z = Lhol (Y * X - X * Y) F z := by
  have hc := hF.contDiffAt (isOpen_OmegaSet'.mem_nhds hz)
  have h1 := ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_OmegaSet').1 hF).2
  have hd := ((h1.differentiableOn (by simp <;> exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) z hz).differentiableAt
    (isOpen_OmegaSet'.mem_nhds hz) |>.hasFDerivAt
  have hs := hc.isSymmSndFDerivAt (by first | exact le_top | (simp; done) | (simp <;> exact (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) : ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω))) | (simp <;> decide))
  let LX : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun w => X * w
      map_add' := fun a b => Matrix.mul_add X a b
      map_smul' := fun c a => Matrix.mul_smul X c a }
  let LY : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun w => Y * w
      map_add' := fun a b => Matrix.mul_add Y a b
      map_smul' := fun c a => Matrix.mul_smul Y c a }
  show fderiv ℂ (fun w => fderiv ℂ F w (LY w)) z (X * z) -
      fderiv ℂ (fun w => fderiv ℂ F w (LX w)) z (Y * z) = fderiv ℂ F z ((Y * X - X * Y) * z)
  erw [(hd.clm_apply LY.hasFDerivAt).fderiv, (hd.clm_apply LX.hasFDerivAt).fderiv]
  show fderiv ℂ F z (Y * (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) -
      (fderiv ℂ F z (X * (Y * z)) + fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z)) = _
  rw [show fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) = fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z) from
    hs (X * z) (Y * z)]
  rw [Matrix.sub_mul, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  abel

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `F`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Use `show ltOp X (ltOp Y F) z - ltOp Y (ltOp X F) z = ltOp (Y * X - X * Y) F z`.

Distinguish the cases in `hz : z ∈ OmegaSet n`. Rewrite using `[ltOp_of_mem _ hz, ltOp_of_mem _ hz, ltOp_of_mem _ hz, lhol_congr (fun w hw => ltOp_of_mem F hw) hz, lhol_congr (fun w hw => ltOp_of_mem F hw) hz]`. Conclude with `Lhol_commutator_on_OmegaSet F.2 X Y hz`. Rewrite using `[ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, sub_zero]`.
-/
theorem eOp_comm (X Y : Matrix (Fin n) (Fin n) ℂ) :
    eOp X * eOp Y - eOp Y * eOp X = eOp (Y * X - X * Y) := by
  apply LinearMap.ext; intro F
  apply Subtype.ext; funext z
  show ltOp X (ltOp Y F) z - ltOp Y (ltOp X F) z = ltOp (Y * X - X * Y) F z
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, ltOp_of_mem _ hz, ltOp_of_mem _ hz,
      lhol_congr (fun w hw => ltOp_of_mem F hw) hz, lhol_congr (fun w hw => ltOp_of_mem F hw) hz]
    exact Lhol_commutator_on_OmegaSet F.2 X Y hz
  · rw [ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, sub_zero]

/- English proof (translation)
Introduce `a b c d`. Rewrite using `[eOp_comm, hX a b c d, eOp_sub]`. Apply the tactic sequence `split_ifs <;> simp [eOp_zero]`.
-/
theorem isGlRep_eOp (X : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ a b c d, X c d * X a b - X a b * X c d =
      (if b = c then X a d else 0) - (if d = a then X c b else 0)) :
    IsGlRep (fun a b => eOp (X a b)) := by
  intro a b c d
  rw [eOp_comm, hX a b c d, eOp_sub]
  split_ifs <;> simp [eOp_zero]

/- English proof (translation)
Unfold `ePow`. Simplify using `only [Bl.ThirdBlockLemmaA.goal1]`. Proceed by induction on `k generalizing a b with`. Consider the case `zero`. Introduce `z hz`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[opPow, Matrix.one_apply, hFG hz]`. Establish `hs : σ a ≠ σ b` using `fun h => hab (σ.injective h)`. Simplify using `[opPow, Matrix.one_apply, hab, hs]`.

Consider the case `succ k ih`. Introduce `z hz`. Establish `hterm : ∀ d, Lhol (Y a d) (opPow (fun a b => Lhol (Y a b)) k d b F) z = c ^ (k + 1) * ((eOp (X (σ a) (σ d)) ((((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G) : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z`. Introduce `d`. Use `set g : smoothS n := (((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G with hg`.

Rewrite using `[lhol_congr (ih d b) hz, eOp_apply, ltOp_of_mem _ hz]`. Use `show fderiv ℂ (fun w => c ^ k * (g : Matrix (Fin n) (Fin n) ℂ → ℂ) w) z (Y a d * z) = c ^ (k + 1) * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (X (σ a) (σ d) * z)`. Use `erw [fderiv_const_mul (differentiableAt_of_mem g.2 hz) (c ^ k)]`. Rewrite using `[hY a d, Matrix.smul_mul]`. Use `show c ^ k * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (c • (X (σ a) (σ d) * z)) = _`.

Rewrite using `[map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [opPow, Finset.sum_apply]`. Rewrite using `[Finset.sum_congr rfl fun d _ => hterm d, pow_succ' (Matrix.of fun a b => eOp (X a b)) k, Matrix.mul_apply]`. Simplify using `only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Module.End.mul_apply, Matrix.of_apply, Finset.mul_sum]`.

Conclude with `Fintype.sum_equiv σ _ _ (fun d => rfl)`.
-/
theorem opPow_eqOn (X Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (c : ℂ)
    (hY : ∀ a b, Y a b = c • X (σ a) (σ b)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (hFG : Set.EqOn F G (OmegaSet n)) (k : ℕ) (a b : Fin n) :
    Set.EqOn (opPow (fun a b => Lhol (Y a b)) k a b F)
      (fun z => c ^ k * ((ePow (fun a b => eOp (X a b)) k (σ a) (σ b) G : smoothS n) :
        Matrix (Fin n) (Fin n) ℂ → ℂ) z) (OmegaSet n) := by
  unfold ePow
  simp only [Bl.ThirdBlockLemmaA.goal1]
  induction k generalizing a b with
  | zero =>
    intro z hz
    by_cases hab : a = b
    · subst hab
      simp [opPow, Matrix.one_apply, hFG hz]
    · have hs : σ a ≠ σ b := fun h => hab (σ.injective h)
      simp [opPow, Matrix.one_apply, hab, hs]
  | succ k ih =>
    intro z hz
    have hterm : ∀ d, Lhol (Y a d) (opPow (fun a b => Lhol (Y a b)) k d b F) z =
        c ^ (k + 1) * ((eOp (X (σ a) (σ d)) ((((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G) :
          smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
      intro d
      set g : smoothS n := (((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G with hg
      rw [lhol_congr (ih d b) hz, eOp_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (fun w => c ^ k * (g : Matrix (Fin n) (Fin n) ℂ → ℂ) w) z (Y a d * z) =
        c ^ (k + 1) * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (X (σ a) (σ d) * z)
      erw [fderiv_const_mul (differentiableAt_of_mem g.2 hz) (c ^ k)]
      rw [hY a d, Matrix.smul_mul]
      show c ^ k * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (c • (X (σ a) (σ d) * z)) = _
      rw [map_smul, smul_eq_mul]
      ring
    simp only [opPow, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun d _ => hterm d, pow_succ' (Matrix.of fun a b => eOp (X a b)) k,
      Matrix.mul_apply]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Module.End.mul_apply,
      Matrix.of_apply, Finset.mul_sum]
    exact Fintype.sum_equiv σ _ _ (fun d => rfl)

/- English proof (translation)
Simplify using `only [opGelfand, gelfand, Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum, Finset.mul_sum]`. Conclude with `Fintype.sum_equiv σ (fun a => opPow (fun a b => Lhol (Y a b)) k a a F z) (fun a => c ^ k * ((ePow (fun a b => eOp (X a b)) k a a G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z) fun a => opPow_eqOn X Y σ c hY F G hFG k a a hz`.
-/
theorem opGelfand_eq (X Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (c : ℂ)
    (hY : ∀ a b, Y a b = c • X (σ a) (σ b)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (hFG : Set.EqOn F G (OmegaSet n)) (k : ℕ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    opGelfand (fun a b => Lhol (Y a b)) k F z =
      c ^ k * ((gelfand (fun a b => eOp (X a b)) k G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
  simp only [opGelfand, gelfand, Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum,
    Finset.mul_sum]
  exact Fintype.sum_equiv σ (fun a => opPow (fun a b => Lhol (Y a b)) k a a F z)
    (fun a => c ^ k * ((ePow (fun a b => eOp (X a b)) k a a G : smoothS n) :
      Matrix (Fin n) (Fin n) ℂ → ℂ) z)
    fun a => opPow_eqOn X Y σ c hY F G hFG k a a hz

end ReciprocityTheory.ChartRestriction.DS.S7

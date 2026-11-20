import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens
import Lemmata.CurryModusPonens.CurryMp

noncomputable section

open Finset Matrix MeasureTheory Set

namespace ReciprocityTheory.ChartRestriction.DS

namespace ChartWRAux

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.CurryModusPonens.goal1 .. | (apply Bl.CurryModusPonens.goal1 <;> assumption) | (intros; apply Bl.CurryModusPonens.goal1 <;> assumption)`.
-/
theorem mp_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (Function.curry : (ι × κ → ℂ) → ι → κ → ℂ) volume volume := by
  first | exact Bl.CurryModusPonens.goal1 .. | (apply Bl.CurryModusPonens.goal1 <;> assumption) | (intros; apply Bl.CurryModusPonens.goal1 <;> assumption)

/- English proof (translation)
Establish `h1` using `measurePreserving_prodAssoc μa μb (μc.prod μd)`. Establish `h2` using `(MeasurePreserving.id μa).prod ((measurePreserving_prodAssoc μb μc μd).symm _)`. Establish `h3` using `(MeasurePreserving.id μa).prod (((Measure.measurePreserving_swap (μ := μb) (ν := μc))).prod (MeasurePreserving.id μd))`. Establish `h4` using `(MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)`. Establish `h5` using `(measurePreserving_prodAssoc μa μc (μb.prod μd)).symm _`.

Establish `h6` using `(Measure.measurePreserving_swap (μ := μa) (ν := μc)).prod (MeasurePreserving.id (μb.prod μd))`. Establish `h` using `h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression.
-/
theorem mp_perm4 {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SigmaFinite μa] [SigmaFinite μb] [SigmaFinite μc] [SigmaFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.2.1, p.1.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μc.prod μa).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod
    ((measurePreserving_prodAssoc μb μc μd).symm _)
  have h3 := (MeasurePreserving.id μa).prod
    (((Measure.measurePreserving_swap (μ := μb) (ν := μc))).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm _
  have h6 := (Measure.measurePreserving_swap (μ := μa) (ν := μc)).prod (MeasurePreserving.id (μb.prod μd))
  have h := h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))
  convert h using 1
  funext p
  rfl

abbrev Lo (N : ℕ) : Type := {ab : Fin N × Fin N // ab.2 < ab.1}

abbrev Up (N : ℕ) : Type := {ab : Fin N × Fin N // ab.1 < ab.2}

variable {N : ℕ}

local instance volTri : (volume : Measure (TriCo N)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
local instance volUCo : (volume : Measure (UCo N)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

def idx (N : ℕ) : Fin N ⊕ (Lo N ⊕ Up N) ≃ Fin N × Fin N where
  toFun i := match i with
    | Sum.inl a => (a, a)
    | Sum.inr (Sum.inl ab) => ab.1
    | Sum.inr (Sum.inr ab) => ab.1
  invFun ab := if h : ab.1 = ab.2 then Sum.inl ab.1 else if h' : ab.2 < ab.1 then Sum.inr (Sum.inl ⟨ab, h'⟩)
    else Sum.inr (Sum.inr ⟨ab, lt_of_le_of_ne (not_lt.1 h') h⟩)
  left_inv := by
    rintro (a | ⟨ab, h⟩ | ⟨ab, h⟩)
    · simp
    · simp [h.ne', h]
    · simp [h.ne, not_lt.2 h.le]
  right_inv := by
    rintro ⟨a, b⟩
    dsimp only
    split_ifs with h h'
    · simp [h]
    · rfl
    · rfl

def rho (p : UCo N × TriCo N) : Fin N → Fin N → ℂ := fun a b =>
  if a = b then ((p.2.1 a : ℝ) : ℂ) + ((p.1.1 a : ℝ) : ℂ) * Complex.I
  else if h : b < a then p.1.2 ⟨(a, b), h⟩ else if h' : a < b then p.2.2 ⟨(a, b), h'⟩ else 0

def e2 (q : (Fin N → ℝ) × (Fin N → ℝ)) : Fin N → ℂ := fun a => ⟨q.1 a, q.2 a⟩

/- English proof (translation)
Establish `h1` using `(volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N)).symm _`. Establish `h2` using `volume_preserving_pi (fun _ : Fin N => (Complex.volume_preserving_equiv_real_prod).symm _)`. Conclude with `h2.comp h1`.
-/
theorem measurePreserving_second_reorder : MeasurePreserving (e2 (N := N)) volume volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N)).symm _
  have h2 := volume_preserving_pi (fun _ : Fin N => (Complex.volume_preserving_equiv_real_prod).symm _)
  exact h2.comp h1

def rho0 (p : UCo N × TriCo N) : Fin N → Fin N → ℂ :=
  Function.curry (MeasurableEquiv.piCongrLeft (fun _ : Fin N × Fin N => ℂ) (idx N)
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)).symm
      (e2 (p.2.1, p.1.1), (MeasurableEquiv.sumPiEquivProdPi (fun _ : Lo N ⊕ Up N => ℂ)).symm (p.1.2, p.2.2))))

/- English proof (translation)
Establish `h1` using `mp_perm4 (volume : Measure (Fin N → ℝ)) (volume : Measure (Lo N → ℂ)) (volume : Measure (Fin N → ℝ)) (volume : Measure (Up N → ℂ))`. Establish `h2` using `(measurePreserving_second_reorder (N := N)).prod (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Lo N ⊕ Up N => ℂ))`. Establish `h3` using `volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)`. Establish `h4` using `volume_measurePreserving_piCongrLeft (fun _ : Fin N × Fin N => ℂ) (idx N)`. Establish `h5` using `mp_curry (Fin N) (Fin N)`.

Conclude with `h5.comp (h4.comp (h3.comp (h2.comp h1)))`.
-/
theorem measurePreserving_rho_reorder : MeasurePreserving (rho0 (N := N)) volume volume := by
  have h1 := mp_perm4 (volume : Measure (Fin N → ℝ)) (volume : Measure (Lo N → ℂ))
    (volume : Measure (Fin N → ℝ)) (volume : Measure (Up N → ℂ))
  have h2 := (measurePreserving_second_reorder (N := N)).prod (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Lo N ⊕ Up N => ℂ))
  have h3 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)
  have h4 := volume_measurePreserving_piCongrLeft (fun _ : Fin N × Fin N => ℂ) (idx N)
  have h5 := mp_curry (Fin N) (Fin N)
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/- English proof (translation)
Use function extensionality and compare the values at `p a b`. Establish `key : ∀ i, rho0 p (idx N i).1 (idx N i).2 = (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)).symm (e2 (p.2.1, p.1.1), (MeasurableEquiv.sumPiEquivProdPi (fun _ : Lo N ⊕ Up N => ℂ)).symm (p.1.2, p.2.2)) i` using `fun i => MeasurableEquiv.piCongrLeft_apply_apply (idx N) (β := fun _ => ℂ) _ i`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Establish `k` using `key (Sum.inr (Sum.inr ⟨(a, b), h⟩))`. Simplify using `only [rho, h.ne, not_lt.2 h.le, h, if_false, dif_neg, dif_pos, not_false_eq_true]`.

Conclude with `k`. Establish `k` using `key (Sum.inl a)`. Simplify using `only [rho, if_true]`. Use `k.trans ?_` and prove the remaining obligations. Apply the tactic sequence `apply Complex.ext <;> simp <;> rfl`.

Establish `k` using `key (Sum.inr (Sum.inl ⟨(a, b), h⟩))`. Simplify using `only [rho, h.ne', h, if_false, dif_pos]`. Conclude with `k`.
-/
theorem rho_reorder_eq_rho : rho0 (N := N) = rho := by
  funext p a b
  have key : ∀ i, rho0 p (idx N i).1 (idx N i).2 =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin N ⊕ (Lo N ⊕ Up N) => ℂ)).symm
        (e2 (p.2.1, p.1.1), (MeasurableEquiv.sumPiEquivProdPi (fun _ : Lo N ⊕ Up N => ℂ)).symm (p.1.2, p.2.2)) i :=
    fun i => MeasurableEquiv.piCongrLeft_apply_apply (idx N) (β := fun _ => ℂ) _ i
  rcases lt_trichotomy a b with h | rfl | h
  · have k := key (Sum.inr (Sum.inr ⟨(a, b), h⟩))
    simp only [rho, h.ne, not_lt.2 h.le, h, if_false, dif_neg, dif_pos, not_false_eq_true]
    exact k
  · have k := key (Sum.inl a)
    simp only [rho, if_true]
    refine k.trans ?_
    apply Complex.ext <;> simp <;> rfl
  · have k := key (Sum.inr (Sum.inl ⟨(a, b), h⟩))
    simp only [rho, h.ne', h, if_false, dif_pos]
    exact k

/- English proof (translation)
Rewrite using `[← rho_reorder_eq_rho]`. Conclude with `measurePreserving_rho_reorder`.
-/
theorem mp_rho : MeasurePreserving (rho (N := N)) volume volume := by
  rw [← rho_reorder_eq_rho]; exact measurePreserving_rho_reorder

def sh (p : UCo N × TriCo N) : UCo N × TriCo N :=
  (p.1, (p.2.1, fun ab => p.2.2 ab - star (p.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)))

/- English proof (translation)
Establish `hc : Continuous (fun q : UCo N × TriCo N => ((0 : Fin N → ℝ), fun ab : Up N => -star (q.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + q.2)`. Use `(continuous_const.prodMk (continuous_pi fun ab => ?_)).add continuous_snd` and prove the remaining obligations. Conclude with `((continuous_apply _).comp (continuous_snd.comp continuous_fst)).star.neg`. Establish `h` using `(MeasurePreserving.id (volume : Measure (UCo N))).skew_product (g := fun x (t : TriCo N) => ((0 : Fin N → ℝ), fun ab : Up N => -star (x.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + t) (μc := (volume : Measure (TriCo N))) (μd := (volume : Measure (TriCo N))) hc.measurable (Filter.Eventually.of_ …`. Establish `e : sh (N` using `N) = fun p => (id p.1, ((0 : Fin N → ℝ), fun ab : Up N => -star (p.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + p.2) := by`.

Use function extensionality and compare the values at `p`. Use `Prod.ext rfl (Prod.ext ?_ ?_)` and prove the remaining obligations. Simplify using `[sh]`. Use function extensionality and compare the values at `ab`. Simplify using `[sh, sub_eq_add_neg, add_comm]`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem mp_sh : MeasurePreserving (sh (N := N)) volume volume := by
  have hc : Continuous (fun q : UCo N × TriCo N =>
      ((0 : Fin N → ℝ), fun ab : Up N => -star (q.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + q.2) := by
    refine (continuous_const.prodMk (continuous_pi fun ab => ?_)).add continuous_snd
    exact ((continuous_apply _).comp (continuous_snd.comp continuous_fst)).star.neg
  have h := (MeasurePreserving.id (volume : Measure (UCo N))).skew_product
    (g := fun x (t : TriCo N) => ((0 : Fin N → ℝ), fun ab : Up N => -star (x.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + t)
    (μc := (volume : Measure (TriCo N))) (μd := (volume : Measure (TriCo N)))
    hc.measurable (Filter.Eventually.of_forall fun x => map_add_left_eq_self (volume : Measure (TriCo N)) _)
  have e : sh (N := N) = fun p => (id p.1,
      ((0 : Fin N → ℝ), fun ab : Up N => -star (p.1.2 ⟨(ab.1.2, ab.1.1), ab.2⟩)) + p.2) := by
    funext p
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp [sh]
    · funext ab
      simp [sh, sub_eq_add_neg, add_comm]
  rw [e]; exact h

def lam (p : UCo N × TriCo N) : Fin N → Fin N → ℂ := Matrix.of.symm (skMat p.1 + upMat p.2)

/- English proof (translation)
Use function extensionality and compare the values at `p a b`. Simplify using `only [lam, Function.comp_apply, rho, sh, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Simplify using `[h.ne, not_lt.2 h.le, h]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h.ne', h, not_lt.2 h.le]`.
-/
theorem lam_eq : lam (N := N) = rho ∘ sh := by
  funext p a b
  simp only [lam, Function.comp_apply, rho, sh, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, not_lt.2 h.le, h]; ring
  · simp; ring
  · simp [h.ne', h, not_lt.2 h.le]

/- English proof (translation)
Rewrite using `[lam_eq]`. Conclude with `mp_rho.comp mp_sh`.
-/
theorem mp_lam : MeasurePreserving (lam (N := N)) volume volume := by
  rw [lam_eq]; exact mp_rho.comp mp_sh

def lamInv (Z : Fin N → Fin N → ℂ) : UCo N × TriCo N :=
  ((fun a => (Z a a).im, fun ab => Z ab.1.1 ab.1.2),
   (fun a => (Z a a).re, fun ab => Z ab.1.1 ab.1.2 + star (Z ab.1.2 ab.1.1)))

/- English proof (translation)
Take `⟨⟨x1, x2⟩, ⟨t1, t2⟩⟩` from `p`. Simplify using `only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]`. Use `Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules.

Use function extensionality and compare the values at `ab`. Take `⟨⟨a, b⟩, h⟩` from `ab`. Simplify using `[h.ne', h, not_lt.2 h.le]`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules.

Use function extensionality and compare the values at `ab`. Take `⟨⟨a, b⟩, h⟩` from `ab`. Simplify using `[h.ne, h.ne', h, not_lt.2 h.le]`.
-/
theorem lamInv_lam (p : UCo N × TriCo N) : lamInv (lam p) = p := by
  obtain ⟨⟨x1, x2⟩, ⟨t1, t2⟩⟩ := p
  simp only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · funext a; simp
  · funext ab; obtain ⟨⟨a, b⟩, h⟩ := ab; simp [h.ne', h, not_lt.2 h.le]
  · funext a; simp
  · funext ab; obtain ⟨⟨a, b⟩, h⟩ := ab; simp [h.ne, h.ne', h, not_lt.2 h.le]

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Simplify using `only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Simplify using `[h.ne, not_lt.2 h.le, h]`. Apply the tactic sequence `apply Complex.ext <;> simp`.

Simplify using `[h.ne', h, not_lt.2 h.le]`.
-/
theorem lam_lamInv (Z : Fin N → Fin N → ℂ) : lam (lamInv Z) = Z := by
  funext a b
  simp only [lamInv, lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.ne, not_lt.2 h.le, h]
  · apply Complex.ext <;> simp
  · simp [h.ne', h, not_lt.2 h.le]

def lamL : (UCo N × TriCo N) →ₗ[ℝ] (Fin N → Fin N → ℂ) where
  toFun := lam
  map_add' p q := by
    funext a b
    simp only [lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat, Prod.fst_add, Prod.snd_add,
      Pi.add_apply]
    split_ifs <;> (try simp [star_add]) <;> (try ring)
  map_smul' c p := by
    funext a b
    simp only [lam, Matrix.of_symm_apply, Matrix.add_apply, skMat, upMat, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

def lamE : (UCo N × TriCo N) ≃L[ℝ] (Fin N → Fin N → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { lamL with invFun := lamInv, left_inv := lamInv_lam, right_inv := lam_lamInv }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lamE_apply (p : UCo N × TriCo N) : lamE p = lam p := rfl

end ChartWRAux

end ReciprocityTheory.ChartRestriction.DS

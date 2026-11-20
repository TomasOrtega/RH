import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRead
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelReductionExtendEvaluatedIntegrated
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearMapKillingPartialEvalIntegralKernelTransla
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.FlatFactor.UpStage

/- English proof (translation)
Set `e` to `MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => k) p`. Establish `he : MeasurePreserving e (Measure.pi fun _ : ι => ν) ((Measure.pi fun _ : {i // p i} => ν).prod (Measure.pi fun _ : {i // ¬p i} => ν))` using `measurePreserving_piEquivPiSubtypeProd (fun _ : ι => ν) p`. Set `w : ({i // p i} → k) → ({i // ¬p i} → k)` to `fun x j => v (e.symm (x, 0)) j.1`. Establish `hw : Measurable w`. Use `measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations.

Conclude with `(measurable_pi_apply j.1).comp (hv.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))`. Establish `hF : MeasurePreserving (fun q : ({i // p i} → k) × ({i // ¬p i} → k) => (id q.1, q.2 + w q.1)) ((Measure.pi fun _ : {i // p i} => ν).prod (Measure.pi fun _ : {i // ¬p i} => ν)) ((Measure.pi fun _ : {i // p i} => ν).prod (Measure.pi fun _ : {i // ¬p i} => ν))` using `(MeasurePreserving.id _).skew_product (measurable_snd.add (hw.comp measurable_fst)) (Filter.Eventually.of_forall fun x => map_add_right_eq_self _ _)`. Establish `hc` using `(he.symm e).comp (hF.comp he)`. Use `hc using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `α`.

Establish `hα : v (e.symm ((fun j : {i // p i} => α j.1), 0)) = v α`. Apply `hd` to reduce the goal to its premises. Introduce `i hi`. Simplify using `[e, MeasurableEquiv.piEquivPiSubtypeProd, hi]`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hi : p i`. Simplify using `[e, w, MeasurableEquiv.piEquivPiSubtypeProd, hi, h0 α i hi]`. Simplify using `[e, w, MeasurableEquiv.piEquivPiSubtypeProd, hi]`. Conclude with `(congrFun hα i).symm`.
-/
theorem measurePreserving_shear {k ι : Type} [AddCommGroup k] [MeasurableSpace k] [MeasurableAdd₂ k] [Fintype ι]
    (ν : Measure k) [SigmaFinite ν] [ν.IsAddRightInvariant] (p : ι → Prop) [DecidablePred p]
    (v : (ι → k) → ι → k) (hv : Measurable v) (h0 : ∀ α i, p i → v α i = 0)
    (hd : ∀ α α', (∀ i, p i → α i = α' i) → v α = v α') :
    MeasurePreserving (fun α => α + v α) (Measure.pi fun _ : ι => ν) (Measure.pi fun _ : ι => ν) := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => k) p
  have he : MeasurePreserving e (Measure.pi fun _ : ι => ν)
      ((Measure.pi fun _ : {i // p i} => ν).prod (Measure.pi fun _ : {i // ¬p i} => ν)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => ν) p
  let w : ({i // p i} → k) → ({i // ¬p i} → k) := fun x j => v (e.symm (x, 0)) j.1
  have hw : Measurable w := by
    refine measurable_pi_lambda _ fun j => ?_
    exact (measurable_pi_apply j.1).comp (hv.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))
  have hF : MeasurePreserving (fun q : ({i // p i} → k) × ({i // ¬p i} → k) => (id q.1, q.2 + w q.1))
      ((Measure.pi fun _ : {i // p i} => ν).prod (Measure.pi fun _ : {i // ¬p i} => ν))
      ((Measure.pi fun _ : {i // p i} => ν).prod (Measure.pi fun _ : {i // ¬p i} => ν)) :=
    (MeasurePreserving.id _).skew_product (measurable_snd.add (hw.comp measurable_fst))
      (Filter.Eventually.of_forall fun x => map_add_right_eq_self _ _)
  have hc := (he.symm e).comp (hF.comp he)
  convert hc using 1
  funext α
  have hα : v (e.symm ((fun j : {i // p i} => α j.1), 0)) = v α := by
    apply hd
    intro i hi
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, hi]
  funext i
  by_cases hi : p i
  · simp [e, w, MeasurableEquiv.piEquivPiSubtypeProd, hi, h0 α i hi]
  · simp [e, w, MeasurableEquiv.piEquivPiSubtypeProd, hi]
    exact (congrFun hα i).symm

section Gen
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

def rowAdd (r₀ r₁ : m) (a : k) (x : Matrix m m' k) : Matrix m m' k :=
  Matrix.of fun r q => x r q + if r = r₀ then a * x r₁ q else 0

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Use `GlobalTheory.SplitWeil.secondCountable k` as an intermediate fact. Use `GlobalTheory.SplitWeil.t2Space k` as an intermediate fact. Set `v : ({e : m × m' // e ∈ it} → k) → {e : m × m' // e ∈ it} → k` to `fun α e => if e.1.1 = r₀ then a * fill ev it β t α r₁ e.1.2 else 0`. Establish `hfm : ∀ q, Measurable fun α : {e : m × m' // e ∈ it} → k => fill ev it β t α r₁ q`. Introduce `q`.

Simplify using `only [fill, Matrix.of_apply]`. Use `split_ifs with h1`. Conclude with `measurable_pi_apply _`. Conclude with `measurable_const`. Conclude with `measurable_const`.

Establish `hvm : Measurable v`. Use `measurable_pi_lambda _ fun e => ?_` and prove the remaining obligations. Use `show Measurable fun α => if e.1.1 = r₀ then a * fill ev it β t α r₁ e.1.2 else 0`. Use `split_ifs`. Conclude with `(hfm e.1.2).const_mul a`.

Conclude with `measurable_const`. Establish `h0' : ∀ (α : {e : m × m' // e ∈ it} → k) (e : {e : m × m' // e ∈ it}), e.1.1 ≠ r₀ → v α e = 0`. Introduce `α e he`. Simplify using `[v, he]`. Establish `hdep : ∀ α α' : {e : m × m' // e ∈ it} → k, (∀ e : {e : m × m' // e ∈ it}, e.1.1 ≠ r₀ → α e = α' e) → v α = v α'`.

Introduce `α α' hα`. Establish `hfe : ∀ q, fill ev it β t α r₁ q = fill ev it β t α' r₁ q`. Introduce `q`. Simplify using `only [fill, Matrix.of_apply]`. Use `split_ifs with h1`.

Conclude with `hα ⟨(r₁, q), h1⟩ hr`. Both sides reduce to the same expression. Both sides reduce to the same expression. Use function extensionality and compare the values at `e`. Simplify using `only [v, hfe]`.

Establish `hv_add : ∀ α, v (α + v α) = v α` using `fun α => hdep _ _ fun e he => by simp [h0' α e he]`. Establish `hv_sub : ∀ α, v (α - v α) = v α` using `fun α => hdep _ _ fun e he => by simp [h0' α e he]`. Set `φ : ({e : m × m' // e ∈ it} → k) ≃ᵐ ({e : m × m' // e ∈ it} → k)` to `{ toFun := fun α => α + v α invFun := fun α => α - v α left_inv := fun α => by show (α + v α) - v (α + v α) = α`. Rewrite using `[hv_add, add_sub_cancel_right]`. Use `right_inv := fun α => by show (α - v α) + v (α - v α) = α`.

Rewrite using `[hv_sub, sub_add_cancel]`. Use `measurable_toFun := measurable_id.add hvm`. Use `measurable_invFun := measurable_id.sub hvm }`. Establish `hmp : MeasurePreserving φ (Measure.pi fun _ => ν) (Measure.pi fun _ => ν)` using `measurePreserving_shear ν (fun e : {e : m × m' // e ∈ it} => e.1.1 ≠ r₀) v hvm h0' hdep`. Establish `hfill : ∀ α, rowAdd r₀ r₁ a (fill ev it β t α) = fill ev it β t' (φ α)`.

Introduce `α`. Use extensionality with `r q`. Distinguish the cases in `hq : (r, q) ∈ it`. Simplify using `[rowAdd, fill, hq, v, φ]`. Rewrite using `[h α r q hq]`.

Simplify using `[fill, hq]`. Unfold `red`. Simplify using `only [hfill]`. Conclude with `hmp.integral_comp' (fun α => Θ (fill ev it β t' α))`.
-/
theorem red_rowAdd (ν : Measure k) [ν.IsAddHaarMeasure] (ev it : Finset (m × m')) (β t t' : Matrix m m' k)
    (r₀ r₁ : m) (hr : r₁ ≠ r₀) (a : k) (Θ : Matrix m m' k → ℂ) (hΘ : Continuous Θ)
    (h : ∀ α r q, (r, q) ∉ it → rowAdd r₀ r₁ a (fill ev it β t α) r q = fill ev it β t' α r q) :
    red ν ev it β (fun x => Θ (rowAdd r₀ r₁ a x)) t = red ν ev it β Θ t' := by
  classical
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  let v : ({e : m × m' // e ∈ it} → k) → {e : m × m' // e ∈ it} → k := fun α e =>
    if e.1.1 = r₀ then a * fill ev it β t α r₁ e.1.2 else 0
  have hfm : ∀ q, Measurable fun α : {e : m × m' // e ∈ it} → k => fill ev it β t α r₁ q := by
    intro q
    simp only [fill, Matrix.of_apply]
    split_ifs with h1
    · exact measurable_pi_apply _
    · exact measurable_const
    · exact measurable_const
  have hvm : Measurable v := by
    refine measurable_pi_lambda _ fun e => ?_
    show Measurable fun α => if e.1.1 = r₀ then a * fill ev it β t α r₁ e.1.2 else 0
    split_ifs
    · exact (hfm e.1.2).const_mul a
    · exact measurable_const
  have h0' : ∀ (α : {e : m × m' // e ∈ it} → k) (e : {e : m × m' // e ∈ it}), e.1.1 ≠ r₀ → v α e = 0 := by
    intro α e he
    simp [v, he]
  have hdep : ∀ α α' : {e : m × m' // e ∈ it} → k,
      (∀ e : {e : m × m' // e ∈ it}, e.1.1 ≠ r₀ → α e = α' e) → v α = v α' := by
    intro α α' hα
    have hfe : ∀ q, fill ev it β t α r₁ q = fill ev it β t α' r₁ q := by
      intro q
      simp only [fill, Matrix.of_apply]
      split_ifs with h1
      · exact hα ⟨(r₁, q), h1⟩ hr
      · rfl
      · rfl
    funext e
    simp only [v, hfe]
  have hv_add : ∀ α, v (α + v α) = v α := fun α =>
    hdep _ _ fun e he => by simp [h0' α e he]
  have hv_sub : ∀ α, v (α - v α) = v α := fun α =>
    hdep _ _ fun e he => by simp [h0' α e he]
  let φ : ({e : m × m' // e ∈ it} → k) ≃ᵐ ({e : m × m' // e ∈ it} → k) :=
    { toFun := fun α => α + v α
      invFun := fun α => α - v α
      left_inv := fun α => by
        show (α + v α) - v (α + v α) = α
        rw [hv_add, add_sub_cancel_right]
      right_inv := fun α => by
        show (α - v α) + v (α - v α) = α
        rw [hv_sub, sub_add_cancel]
      measurable_toFun := measurable_id.add hvm
      measurable_invFun := measurable_id.sub hvm }
  have hmp : MeasurePreserving φ (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) :=
    measurePreserving_shear ν (fun e : {e : m × m' // e ∈ it} => e.1.1 ≠ r₀) v hvm h0' hdep
  have hfill : ∀ α, rowAdd r₀ r₁ a (fill ev it β t α) = fill ev it β t' (φ α) := by
    intro α
    ext r q
    by_cases hq : (r, q) ∈ it
    · simp [rowAdd, fill, hq, v, φ]
    · rw [h α r q hq]
      simp [fill, hq]
  unfold red
  simp only [hfill]
  exact hmp.integral_comp' (fun α => Θ (fill ev it β t' α))

/- English proof (translation)
Use `GlobalTheory.SplitWeil.secondCountable k` as an intermediate fact. Use `GlobalTheory.SplitWeil.t2Space k` as an intermediate fact. Establish `hint : ∀ (Φ : SB (Matrix m m' k)) t, Integrable (fun x => Φ.1 (fill ev it β t x)) (Measure.pi fun _ => ν)`. Introduce `Φ t`. Establish `hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1` using `Φ.2`.

Conclude with `(hΦ.1.continuous.comp (continuous_fill ev it β t)).integrable_of_hasCompactSupport (hasCompactSupport_comp_fill ev it β t _ hΦ.2)`. Establish `h0 : l (Θ - Θ') = 0`. Apply `hK` to reduce the goal to its premises. Introduce `t`. Express the relevant statement in the definitionally equal form `∫ x, (Θ.1 - Θ'.1) (fill ev it β t x) ∂(Measure.pi fun _ => ν) = 0`.

Simplify using `only [Pi.sub_apply]`. Rewrite using `[integral_sub (hint Θ t) (hint Θ' t)]`. Conclude with `sub_eq_zero.2 (h t)`. Rewrite `h0` using `[map_sub]`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem kerRed_eq {M : Type} [AddCommGroup M] [Module ℂ M] (ν : Measure k) [ν.IsAddHaarMeasure]
    (ev it : Finset (m × m')) (β : Matrix m m' k) (l : SB (Matrix m m' k) →ₗ[ℂ] M) (hK : KerRed ν ev it β l)
    (Θ Θ' : SB (Matrix m m' k)) (h : ∀ t, red ν ev it β Θ.1 t = red ν ev it β Θ'.1 t) : l Θ = l Θ' := by
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have hint : ∀ (Φ : SB (Matrix m m' k)) t,
      Integrable (fun x => Φ.1 (fill ev it β t x)) (Measure.pi fun _ => ν) := by
    intro Φ t
    have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
    exact (hΦ.1.continuous.comp (continuous_fill ev it β t)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_fill ev it β t _ hΦ.2)
  have h0 : l (Θ - Θ') = 0 := by
    apply hK
    intro t
    change ∫ x, (Θ.1 - Θ'.1) (fill ev it β t x) ∂(Measure.pi fun _ => ν) = 0
    simp only [Pi.sub_apply]
    rw [integral_sub (hint Θ t) (hint Θ' t)]
    exact sub_eq_zero.2 (h t)
  rw [map_sub] at h0
  exact sub_eq_zero.1 h0

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Use extensionality with `r q`. Distinguish the cases in `hrq : r₀ = r ∧ q₀ = q`. Take `⟨rfl, rfl⟩` from `hrq`. Simplify using `[fill, Matrix.single_apply, h1, h2]`. Simplify using `[fill, Matrix.single_apply, hrq]`.
-/
theorem fill_add_single_of_notMem (ev it : Finset (m × m')) (β t : Matrix m m' k) (x : {e : m × m' // e ∈ it} → k)
    (r₀ : m) (q₀ : m') (h1 : (r₀, q₀) ∉ ev) (h2 : (r₀, q₀) ∉ it) (a : k) :
    fill ev it β t x + Matrix.single r₀ q₀ a = fill ev it β (t + Matrix.single r₀ q₀ a) x := by
  ext r q
  by_cases hrq : r₀ = r ∧ q₀ = q
  · obtain ⟨rfl, rfl⟩ := hrq
    simp [fill, Matrix.single_apply, h1, h2]
  · simp [fill, Matrix.single_apply, hrq]

omit [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Establish `hc : Continuous fun t : Matrix m m' k => g.val * t` using `continuous_const.matrix_mul continuous_id`. Establish `hc' : Continuous fun t : Matrix m m' k => (g⁻¹).val * t` using `continuous_const.matrix_mul continuous_id`. Set `h : Matrix m m' k ≃ₜ Matrix m m' k` to `{ toFun := fun t => g.val * t invFun := fun t => (g⁻¹).val * t left_inv := fun t => by simp [← Matrix.mul_assoc] right_inv := fun t => by simp [← Matrix.mul_assoc] continuous_toFun := hc continuous_invFun := hc' }`. Establish `hΘ : IsLocallyConstant Θ.1 ∧ HasCompactSupport Θ.1` using `Θ.2`. Conclude with `⟨hΘ.1.comp_continuous hc, hΘ.2.comp_homeomorph h⟩`.
-/
theorem mem_SB_mul_left (g : GL m k) (Θ : SB (Matrix m m' k)) :
    (fun t => Θ.1 (g.val * t)) ∈ SB (Matrix m m' k) := by
  have hc : Continuous fun t : Matrix m m' k => g.val * t := continuous_const.matrix_mul continuous_id
  have hc' : Continuous fun t : Matrix m m' k => (g⁻¹).val * t := continuous_const.matrix_mul continuous_id
  let h : Matrix m m' k ≃ₜ Matrix m m' k :=
    { toFun := fun t => g.val * t
      invFun := fun t => (g⁻¹).val * t
      left_inv := fun t => by simp [← Matrix.mul_assoc]
      right_inv := fun t => by simp [← Matrix.mul_assoc]
      continuous_toFun := hc
      continuous_invFun := hc' }
  have hΘ : IsLocallyConstant Θ.1 ∧ HasCompactSupport Θ.1 := Θ.2
  exact ⟨hΘ.1.comp_continuous hc, hΘ.2.comp_homeomorph h⟩

end Gen

section Pos
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)

open Classical in

def itUp (j : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ ≤ i.val ∨ j ≤ i.val

/- English proof (translation)
Use extensionality with `e`. Simplify using `[itUp, itB]`.
-/
theorem itUp_top : itUp n n' c ρ ρ = itB n n' c ρ := by
  ext e
  simp [itUp, itB]

/- English proof (translation)
Use extensionality with `e`. Simplify using `[itUp, itFree]`.
-/
theorem itUp_zero : itUp n n' c ρ 0 = itFree n n' c ρ := by
  ext e
  simp [itUp, itFree]

variable {n n' c ρ}

/- English proof (translation)
Simplify using `[itUp]`.
-/
theorem mem_itUp {j : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} :
    e ∈ itUp n n' c ρ j ↔ Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ ≤ i.val ∨ j ≤ i.val := by
  simp [itUp]

/- English proof (translation)
Simplify using `[evAll]`.
-/
theorem mem_evAll {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} :
    e ∈ evAll n n' c ρ ↔ ¬ Free (ρ + 1) e ∧ ¬ IsRead n n' c ρ e := by
  simp [evAll]

variable {k : Type} [Field k]

def tv (i j : Fin c) (h : i ≠ j) (a : k) : GL (Fin c) k :=
  ⟨transvection i j a, transvection i j (-a),
    by rw [transvection_mul_transvection_same i j h, add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same i j h, neg_add_cancel, transvection_zero]⟩

/- English proof (translation)
Use extensionality with `r q`. Break down `r with r | r` into its components or cases. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, rowAdd, Matrix.one_apply]`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, rowAdd, transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, add_mul, Finset.sum_add_distrib, ite_mul]`. Distinguish the cases in `hri : i = r`.

Substitute `hri` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hri, Ne.symm hri]`.
-/
theorem fromBlocks_transvection_mul {m' : Type} (i j : Fin c) (a : k) (x : Matrix (n ⊕ Fin c) m' k) :
    (fromBlocks 1 0 0 (transvection i j a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * x =
      rowAdd (Sum.inr i) (Sum.inr j) a x := by
  ext r q
  rcases r with r | r
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, rowAdd, Matrix.one_apply]
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, rowAdd, transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, add_mul, Finset.sum_add_distrib, ite_mul]
    by_cases hri : i = r
    · subst hri
      simp
    · simp [hri, Ne.symm hri]

/- English proof (translation)
Conclude with `fromBlocks_transvection_mul i j a x`.
-/
theorem embA_tv_mul {m' : Type} (i j : Fin c) (h : i ≠ j) (a : k) (x : Matrix (n ⊕ Fin c) m' k) :
    (embA n (tv i j h a)).val * x = rowAdd (Sum.inr i) (Sum.inr j) a x := by
  exact fromBlocks_transvection_mul i j a x

/- English proof (translation)
Rewrite using `[← map_inv]`. Conclude with `fromBlocks_transvection_mul i j (-a) x`.
-/
theorem embA_tv_inv_mul {m' : Type} (i j : Fin c) (h : i ≠ j) (a : k) (x : Matrix (n ⊕ Fin c) m' k) :
    ((embA n (tv i j h a))⁻¹).val * x = rowAdd (Sum.inr i) (Sum.inr j) (-a) x := by
  rw [← map_inv]
  exact fromBlocks_transvection_mul i j (-a) x

/- English proof (translation)
Simplify using `[ch, rowAdd, Finset.sum_add_distrib]`.
-/
theorem ch_rowAdd (i j : Fin c) (a : k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch (rowAdd (Sum.inr i) (Sum.inr j) a x) - ch x = a * x (Sum.inr j) (Sum.inr i.succ) := by
  simp [ch, rowAdd, Finset.sum_add_distrib]

/- English proof (translation)
Establish `key : ∀ i' j' : Fin c, (if j'.val = i'.val + 1 then ((1 : Matrix (Fin c) (Fin c) k) + Matrix.single i j a) i' j' else 0) = if i' = i then (if j' = j then (if j.val = i.val + 1 then a else 0) else 0) else 0`. Introduce `i' j'`. Distinguish the cases in `h1 : j'.val = i'.val + 1`. Establish `hne : i' ≠ j'` using `fun e => by rw [e] at h1; omega`. Distinguish the cases in `h2 : i' = i`.

Distinguish the cases in `h3 : j' = j`. Substitute `h2` using the available equality. Substitute `h3` using the available equality. Simplify using `[h1, Matrix.one_apply_ne hne]`. Substitute `h2` using the available equality.

Simplify using `[h1, h3, Matrix.one_apply_ne hne, Ne.symm h3]`. Simplify using `[h1, h2, Matrix.one_apply_ne hne, Ne.symm h2]`. Distinguish the cases in `h2 : i' = i`. Distinguish the cases in `h3 : j' = j`. Substitute `h2` using the available equality.

Substitute `h3` using the available equality. Simplify using `[h1]`. Simplify using `[h1, h3]`. Simplify using `[h1, h2]`. Express the relevant statement in the definitionally equal form `(∑ i' : Fin c, ∑ j' : Fin c, if j'.val = i'.val + 1 then (fromBlocks 1 0 0 (transvection i j a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i') (Sum.inr j') else 0) = _`.

Simplify using `only [fromBlocks_apply₂₂, transvection, key]`. Simplify using the standard rewrite rules.
-/
theorem simpleSum_tv (i j : Fin c) (h : i ≠ j) (a : k) :
    simpleSum (embA n (tv i j h a)) = if j.val = i.val + 1 then a else 0 := by
  have key : ∀ i' j' : Fin c, (if j'.val = i'.val + 1 then
      ((1 : Matrix (Fin c) (Fin c) k) + Matrix.single i j a) i' j' else 0) =
      if i' = i then (if j' = j then (if j.val = i.val + 1 then a else 0) else 0) else 0 := by
    intro i' j'
    by_cases h1 : j'.val = i'.val + 1
    · have hne : i' ≠ j' := fun e => by rw [e] at h1; omega
      by_cases h2 : i' = i
      · by_cases h3 : j' = j
        · subst h2; subst h3; simp [h1, Matrix.one_apply_ne hne]
        · subst h2; simp [h1, h3, Matrix.one_apply_ne hne, Ne.symm h3]
      · simp [h1, h2, Matrix.one_apply_ne hne, Ne.symm h2]
    · by_cases h2 : i' = i
      · by_cases h3 : j' = j
        · subst h2; subst h3; simp [h1]
        · simp [h1, h3]
      · simp [h1, h2]
  change (∑ i' : Fin c, ∑ j' : Fin c, if j'.val = i'.val + 1 then
      (fromBlocks 1 0 0 (transvection i j a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i') (Sum.inr j') else 0) = _
  simp only [fromBlocks_apply₂₂, transvection, key]
  simp

/- English proof (translation)
Use `Subgroup.subset_closure (fun r s hrs => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(fromBlocks 1 0 0 (transvection i j a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s = _`. Apply the tactic sequence `rcases r with r | r <;> rcases s with s | s`. Simplify using `[Matrix.one_apply]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using `only [lev, Sum.elim_inr] at hrs`. Establish `hrs' : ¬ (i = r ∧ j = s)`. Introduce and unpack `⟨rfl, rfl⟩`. Use linear arithmetic over natural numbers and integers.

Simplify using `[transvection, hrs', Matrix.one_apply]`.
-/
theorem embA_tv_mem (i j : Fin c) (h : i ≠ j) (hij : i.val < j.val) (a : k) (p : ℕ) :
    embA n (tv i j h a) ∈ N k n c p := by
  refine Subgroup.subset_closure (fun r s hrs => ?_)
  change (fromBlocks 1 0 0 (transvection i j a) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s = _
  rcases r with r | r <;> rcases s with s | s
  · simp [Matrix.one_apply]
  · simp
  · simp
  · simp only [lev, Sum.elim_inr] at hrs
    have hrs' : ¬ (i = r ∧ j = s) := by
      rintro ⟨rfl, rfl⟩
      omega
    simp [transvection, hrs', Matrix.one_apply]

/- English proof (translation)
Establish `h'` using `h`. Rewrite `h` using `[mem_itUp]`. Simplify using `only [rowAdd, fill, Matrix.of_apply, Matrix.add_apply, Matrix.single_apply, dif_neg h']`. Distinguish the cases in `hr : r = Sum.inr l`. Substitute `hr` using the available equality.

Break down `q with q | i` into its components or cases. Conclude with `absurd ⟨by simp only [Free]; omega, by simp⟩ h`. Establish `hij : i.val ≤ j.val`. Assume the negation of the conclusion as `hc`. Conclude with `h ⟨by simp only [Free]; omega, fun i' hi' => by cases hi'; omega⟩`.

Establish `hj' : (Sum.inr j, Sum.inr i) ∉ itUp n n' c ρ (j.val + 1)`. Rewrite using `[mem_itUp]`. Introduce and unpack `⟨hf, -⟩`. Simplify using `only [Free] at hf`. Use linear arithmetic over natural numbers and integers.

Establish `hjev : (Sum.inr j, Sum.inr i) ∈ evAll n n' c ρ`. Rewrite using `[mem_evAll]`. Simplify using `only [Free, IsRead, not_false_eq_true, and_true]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg hj', if_pos hjev]`.

Distinguish the cases in `hli : l.val < i.val`. Establish `hlev : (Sum.inr l, Sum.inr i) ∉ evAll n n' c ρ`. Rewrite using `[mem_evAll]`. Simplify using `only [Free]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg hlev, if_neg hlev]`. Distinguish the cases in `hji : j.val = i.val`. Simplify using `[basePt, Fin.ext_iff, hji]`. Simplify using `[basePt, Fin.ext_iff, hji]`. Establish `hlev : (Sum.inr l, Sum.inr i) ∈ evAll n n' c ρ`.

Rewrite using `[mem_evAll]`. Simplify using `only [Free, IsRead, not_false_eq_true, and_true]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos hlev, if_pos hlev]`. Establish `hji : j.val ≠ i.val` using `by omega`.

Simplify using `[basePt, hji]`. Simplify using `[hr, Ne.symm hr]`.
-/
theorem rowAdd_fill (l j : Fin c) (hl : l.val < j.val) (hj : j.val < ρ) (a : k)
    (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (α) (r) (q) (h : (r, q) ∉ itUp n n' c ρ (j.val + 1)) :
    rowAdd (Sum.inr l) (Sum.inr j) a
        (fill (evAll n n' c ρ) (itUp n n' c ρ (j.val + 1)) (basePt c (0 : Matrix n n' k)) t α) r q =
      fill (evAll n n' c ρ) (itUp n n' c ρ (j.val + 1)) (basePt c (0 : Matrix n n' k))
        (t + Matrix.single (Sum.inr l) (Sum.inr j.castSucc) a) α r q := by
  have h' := h
  rw [mem_itUp] at h
  simp only [rowAdd, fill, Matrix.of_apply, Matrix.add_apply, Matrix.single_apply, dif_neg h']
  by_cases hr : r = Sum.inr l
  · subst hr
    rcases q with q | i
    · exact absurd ⟨by simp only [Free]; omega, by simp⟩ h
    · have hij : i.val ≤ j.val := by
        by_contra hc
        exact h ⟨by simp only [Free]; omega, fun i' hi' => by cases hi'; omega⟩
      have hj' : (Sum.inr j, Sum.inr i) ∉ itUp n n' c ρ (j.val + 1) := by
        rw [mem_itUp]
        rintro ⟨hf, -⟩
        simp only [Free] at hf
        omega
      have hjev : (Sum.inr j, Sum.inr i) ∈ evAll n n' c ρ := by
        rw [mem_evAll]
        simp only [Free, IsRead, not_false_eq_true, and_true]
        omega
      rw [dif_neg hj', if_pos hjev]
      by_cases hli : l.val < i.val
      · have hlev : (Sum.inr l, Sum.inr i) ∉ evAll n n' c ρ := by
          rw [mem_evAll]
          simp only [Free]
          omega
        rw [if_neg hlev, if_neg hlev]
        by_cases hji : j.val = i.val
        · simp [basePt, Fin.ext_iff, hji]
        · simp [basePt, Fin.ext_iff, hji]
      · have hlev : (Sum.inr l, Sum.inr i) ∈ evAll n n' c ρ := by
          rw [mem_evAll]
          simp only [Free, IsRead, not_false_eq_true, and_true]
          omega
        rw [if_pos hlev, if_pos hlev]
        have hji : j.val ≠ i.val := by omega
        simp [basePt, hji]
  · simp [hr, Ne.symm hr]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Establish `hΘ : IsLocallyConstant Θ.1 ∧ HasCompactSupport Θ.1` using `Θ.2`. Conclude with `⟨(((GlobalTheory.RootEx.OpenKernel.characters_locallyConstant k).2 ψ hψ).comp_continuous hf).mul hΘ.1, hΘ.2.mul_left⟩`.
-/
private theorem addChar_comp_mul_mem_SB {X : Type} [TopologicalSpace X] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (f : X → k) (hf : Continuous f) (Θ : SB X) : (fun t => (ψ (f t) : ℂ) * Θ.1 t) ∈ SB X := by
  have hΘ : IsLocallyConstant Θ.1 ∧ HasCompactSupport Θ.1 := Θ.2
  exact ⟨(((GlobalTheory.RootEx.OpenKernel.characters_locallyConstant k).2 ψ hψ).comp_continuous hf).mul hΘ.1, hΘ.2.mul_left⟩

/- English proof (translation)
Use `GlobalTheory.SplitWeil.secondCountable k` as an intermediate fact. Use `GlobalTheory.SplitWeil.t2Space k` as an intermediate fact. Establish `hlj : l ≠ j` using `fun e => by rw [e] at hl; exact lt_irrefl _ hl`. Establish `hsb : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1` using `fun Φ => Φ.2`. Establish `hnev : (Sum.inr l, Sum.inr j.castSucc) ∉ evAll n n' c ρ`.

Rewrite using `[mem_evAll]`. Introduce `hc`. Conclude with `hc.1 (by simpa [Free] using hl)`. Establish `hnit : (Sum.inr l, Sum.inr j.castSucc) ∉ itUp n n' c ρ (j.val + 1)`. Rewrite using `[mem_itUp]`.

Introduce and unpack `⟨-, h2⟩`. Apply the tactic sequence `rcases h2 _ rfl with h3 | h3 <;> simp at h3 <;> omega`. Establish `hnit2 : (Sum.inr j, Sum.inr l.succ) ∉ itUp n n' c ρ (j.val + 1)`. Rewrite using `[mem_itUp]`. Introduce and unpack `⟨hf, -⟩`.

Simplify using `only [Free, Fin.val_succ] at hf`. Use linear arithmetic over natural numbers and integers. Establish `hev2 : (Sum.inr j, Sum.inr l.succ) ∈ evAll n n' c ρ`. Rewrite using `[mem_evAll]`. Simplify using `only [Free, IsRead, Fin.val_succ, not_false_eq_true, and_true]`.

Use linear arithmetic over natural numbers and integers. Use `set u : GL (Fin c) k := tv l j hlj (-a) with hu`. Establish `hmem : embA n u ∈ N k n c (ρ + 1)` using `embA_tv_mem l j hlj hl (-a) (ρ + 1)`. Establish `hzero : ∀ i j' : Fin c, i.val < ρ → ρ ≤ j'.val → u.val i j' = 0`. Introduce `i j' hi hj'`.

Establish `h1 : i ≠ j'` using `fun e => by rw [e] at hi; omega`. Establish `h2 : j ≠ j'` using `fun e => by rw [← e] at hj'; omega`. Use `show (transvection l j (-a) : Matrix (Fin c) (Fin c) k) i j' = 0`. Simplify using `[transvection, Matrix.one_apply_ne h1, h2]`. Set `Θ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)` to `⟨fun t => Θ.1 (((embA n u)⁻¹).val * t), mem_SB_mul_left _ Θ⟩`.

Establish `hcoord : Continuous fun t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => -a * t (Sum.inr j) (Sum.inr l.succ)` using `continuous_const.mul (continuous_id.matrix_elem (Sum.inr j) (Sum.inr l.succ))`. Set `Θ₂ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)` to `⟨fun t => (ψ (-a * t (Sum.inr j) (Sum.inr l.succ)) : ℂ) * Θ.1 t, addChar_comp_mul_mem_SB ψ hψ _ hcoord Θ⟩`. Establish `hlaw : L Θ₁ = (ψ (-simpleSum (embA n u)) : ℂ) • L Θ₂`. Use `hT u hmem hzero Θ Θ₁ Θ₂ (fun t => rfl) (fun t => ?_)` and prove the remaining obligations. Use `show (ψ (-a * t (Sum.inr j) (Sum.inr l.succ)) : ℂ) * Θ.1 t = _`.

Rewrite using `[hu, embA_tv_mul, ch_rowAdd]`. Establish `h1 : L Θ₁ = L Θ'`. Use `kerRed_eq ν _ _ _ L hK Θ₁ Θ' fun t => ?_` and prove the remaining obligations. Establish `e1 : Θ₁.1 = fun x => Θ.1 (rowAdd (Sum.inr l) (Sum.inr j) a x)`. Use function extensionality and compare the values at `x`.

Use `show Θ.1 (((embA n (tv l j hlj (-a)))⁻¹).val * x) = _`. Rewrite using `[embA_tv_inv_mul, neg_neg]`. Rewrite using `[e1, red_rowAdd ν _ _ _ t (t + Matrix.single (Sum.inr l) (Sum.inr j.castSucc) a) (Sum.inr l) (Sum.inr j) (Sum.inr_injective.ne (Ne.symm hlj)) a Θ.1 (hsb Θ).1.continuous (fun α r q hrq => rowAdd_fill l j hl hj a t α r q hrq)]`. Unfold `red`. Use `congr 1`.

Use function extensionality and compare the values at `α`. Rewrite using `[h, fill_add_single_of_notMem _ _ _ _ _ _ _ hnev hnit]`. Establish `h2 : (ψ (-simpleSum (embA n u)) : ℂ) • L Θ₂ = L Θ`. Rewrite using `[← map_smul]`. Use `kerRed_eq ν _ _ _ L hK _ Θ fun t => ?_` and prove the remaining obligations.

Unfold `red`. Use `congr 1`. Use function extensionality and compare the values at `α`. Establish `hfv : fill (evAll n n' c ρ) (itUp n n' c ρ (j.val + 1)) (basePt c (0 : Matrix n n' k)) t α (Sum.inr j) (Sum.inr l.succ) = if j.val = l.val + 1 then 1 else 0`. Simplify using `only [fill, Matrix.of_apply]`.

Rewrite using `[dif_neg hnit2, if_pos hev2]`. Simplify using `[basePt]`. Use `show (ψ (-simpleSum (embA n u)) : ℂ) * ((ψ (-a * _) : ℂ) * Θ.1 _) = Θ.1 _`. Rewrite using `[← mul_assoc, hfv, hu, simpleSum_tv]`. Apply the tactic sequence `split_ifs <;> simp [← Circle.coe_mul, ← AddChar.map_add_eq_mul]`.

Rewrite using `[← h1, hlaw, h2]`.
-/
theorem translate_law (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) [ν.IsAddHaarMeasure]
    {M : Type} [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hT : TwLaw ρ ψ L) (l j : Fin c) (hl : l.val < j.val) (hj : j.val < ρ)
    (hK : KerRed ν (evAll n n' c ρ) (itUp n n' c ρ (j.val + 1)) (basePt c (0 : Matrix n n' k)) L)
    (a : k) (Θ Θ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (h : ∀ t, Θ'.1 t = Θ.1 (t + Matrix.single (Sum.inr l) (Sum.inr j.castSucc) a)) : L Θ' = L Θ := by
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have hlj : l ≠ j := fun e => by rw [e] at hl; exact lt_irrefl _ hl
  have hsb : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 :=
    fun Φ => Φ.2
  have hnev : (Sum.inr l, Sum.inr j.castSucc) ∉ evAll n n' c ρ := by
    rw [mem_evAll]
    intro hc
    exact hc.1 (by simpa [Free] using hl)
  have hnit : (Sum.inr l, Sum.inr j.castSucc) ∉ itUp n n' c ρ (j.val + 1) := by
    rw [mem_itUp]
    rintro ⟨-, h2⟩
    rcases h2 _ rfl with h3 | h3 <;> simp at h3 <;> omega
  have hnit2 : (Sum.inr j, Sum.inr l.succ) ∉ itUp n n' c ρ (j.val + 1) := by
    rw [mem_itUp]
    rintro ⟨hf, -⟩
    simp only [Free, Fin.val_succ] at hf
    omega
  have hev2 : (Sum.inr j, Sum.inr l.succ) ∈ evAll n n' c ρ := by
    rw [mem_evAll]
    simp only [Free, IsRead, Fin.val_succ, not_false_eq_true, and_true]
    omega
  set u : GL (Fin c) k := tv l j hlj (-a) with hu
  have hmem : embA n u ∈ N k n c (ρ + 1) := embA_tv_mem l j hlj hl (-a) (ρ + 1)
  have hzero : ∀ i j' : Fin c, i.val < ρ → ρ ≤ j'.val → u.val i j' = 0 := by
    intro i j' hi hj'
    have h1 : i ≠ j' := fun e => by rw [e] at hi; omega
    have h2 : j ≠ j' := fun e => by rw [← e] at hj'; omega
    show (transvection l j (-a) : Matrix (Fin c) (Fin c) k) i j' = 0
    simp [transvection, Matrix.one_apply_ne h1, h2]
  let Θ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    ⟨fun t => Θ.1 (((embA n u)⁻¹).val * t), mem_SB_mul_left _ Θ⟩
  have hcoord : Continuous fun t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => -a * t (Sum.inr j) (Sum.inr l.succ) :=
    continuous_const.mul (continuous_id.matrix_elem (Sum.inr j) (Sum.inr l.succ))
  let Θ₂ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    ⟨fun t => (ψ (-a * t (Sum.inr j) (Sum.inr l.succ)) : ℂ) * Θ.1 t, addChar_comp_mul_mem_SB ψ hψ _ hcoord Θ⟩
  have hlaw : L Θ₁ = (ψ (-simpleSum (embA n u)) : ℂ) • L Θ₂ := by
    refine hT u hmem hzero Θ Θ₁ Θ₂ (fun t => rfl) (fun t => ?_)
    show (ψ (-a * t (Sum.inr j) (Sum.inr l.succ)) : ℂ) * Θ.1 t = _
    rw [hu, embA_tv_mul, ch_rowAdd]
  have h1 : L Θ₁ = L Θ' := by
    refine kerRed_eq ν _ _ _ L hK Θ₁ Θ' fun t => ?_
    have e1 : Θ₁.1 = fun x => Θ.1 (rowAdd (Sum.inr l) (Sum.inr j) a x) := by
      funext x
      show Θ.1 (((embA n (tv l j hlj (-a)))⁻¹).val * x) = _
      rw [embA_tv_inv_mul, neg_neg]
    rw [e1, red_rowAdd ν _ _ _ t (t + Matrix.single (Sum.inr l) (Sum.inr j.castSucc) a) (Sum.inr l) (Sum.inr j)
      (Sum.inr_injective.ne (Ne.symm hlj)) a Θ.1 (hsb Θ).1.continuous
      (fun α r q hrq => rowAdd_fill l j hl hj a t α r q hrq)]
    unfold red
    congr 1
    funext α
    rw [h, fill_add_single_of_notMem _ _ _ _ _ _ _ hnev hnit]
  have h2 : (ψ (-simpleSum (embA n u)) : ℂ) • L Θ₂ = L Θ := by
    rw [← map_smul]
    refine kerRed_eq ν _ _ _ L hK _ Θ fun t => ?_
    unfold red
    congr 1
    funext α
    have hfv : fill (evAll n n' c ρ) (itUp n n' c ρ (j.val + 1)) (basePt c (0 : Matrix n n' k)) t α (Sum.inr j) (Sum.inr l.succ)
        = if j.val = l.val + 1 then 1 else 0 := by
      simp only [fill, Matrix.of_apply]
      rw [dif_neg hnit2, if_pos hev2]
      simp [basePt]
    show (ψ (-simpleSum (embA n u)) : ℂ) * ((ψ (-a * _) : ℂ) * Θ.1 _) = Θ.1 _
    rw [← mul_assoc, hfv, hu, simpleSum_tv]
    split_ifs <;> simp [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  rw [← h1, hlaw, h2]

end Pos

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ψ ν hψ hψ1 hν n n' _ _ _ _ c ρ M _ _ l hc hT hB`. Establish `step : ∀ j : ℕ, j < ρ → KerRed ν (evAll n n' c ρ) (itUp n n' c ρ (j + 1)) (basePt c (0 : Matrix n n' k)) l → KerRed ν (evAll n n' c ρ) (itUp n n' c ρ j) (basePt c (0 : Matrix n n' k)) l`. Introduce `j hj hK`. Use `KerRedStep.kerRed_extend k ψ ν hψ hψ1 hν _ _ M l _ _ _ _ _ subset_rfl ?_ ?_ hK ?_ ?_` and prove the remaining obligations. Introduce `e he`.

Rewrite `he`, the goal using `[mem_itUp]`. Conclude with `⟨he.1, fun i hi => (he.2 i hi).imp_right (by omega)⟩`. Rewrite using `[Finset.disjoint_left]`. Introduce `e he he'`. Rewrite `he` using `[mem_evAll]`.

Rewrite `he'` using `[mem_itUp]`. Conclude with `he.1 he'.1`. Introduce `e he he'`. Conclude with `absurd he he'`. Introduce and unpack `⟨r, q⟩ he he' b Θ Θ' hΘ`.

Rewrite `he`, `he'` using `[mem_itUp]`. Take `⟨hf, hcol⟩` from `he`. Break down `q with q | i` into its components or cases. Conclude with `absurd ⟨hf, fun i hi => by cases hi⟩ he'`. Establish `hi : i.val = j`.

Assume the negation of the conclusion as `hne`. Apply `he'` to reduce the goal to its premises. Use `⟨hf, fun i' hi' => ?_⟩` and prove the remaining obligations. Consider the cases of `hi'`. Break down `hcol i rfl with h1 | h1` into its components or cases.

Conclude with `Or.inl h1`. Conclude with `Or.inr (by omega)`. Break down `r with r | l'` into its components or cases. Simplify using `only [Free] at hf`. Use linear arithmetic over natural numbers and integers.

Establish `hjc : j < c` using `by omega`. Establish `hi' : i = (⟨j, hjc⟩ : Fin c).castSucc` using `Fin.ext (by simp [hi])`. Substitute `hi'` using the available equality. Simplify using `only [Free, Fin.val_castSucc] at hf`. Conclude with `translate_law ψ ν hψ l hT l' ⟨j, hjc⟩ hf hj hK b Θ Θ' hΘ`.

Establish `main : ∀ d, d ≤ ρ → KerRed ν (evAll n n' c ρ) (itUp n n' c ρ (ρ - d)) (basePt c (0 : Matrix n n' k)) l`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `_`.

Rewrite using `[Nat.sub_zero, itUp_top]`. Conclude with `hB`. Consider the case `succ d ih`. Introduce `hd`. Establish `h1 : ρ - d = (ρ - (d + 1)) + 1` using `by omega`.

Use `step _ (by omega) ?_` and prove the remaining obligations. Rewrite using `[← h1]`. Conclude with `ih (by omega)`. Use `main ρ le_rfl` as an intermediate fact. Rewrite `this` using `[Nat.sub_self, itUp_zero]`. Then use the resulting hypothesis.
-/
theorem kerRed_itFree : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → GlobalTheory.FlatFactor.TwLaw ρ ψ l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) l := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν n n' _ _ _ _ c ρ M _ _ l hc hT hB
  have step : ∀ j : ℕ, j < ρ →
      KerRed ν (evAll n n' c ρ) (itUp n n' c ρ (j + 1)) (basePt c (0 : Matrix n n' k)) l →
      KerRed ν (evAll n n' c ρ) (itUp n n' c ρ j) (basePt c (0 : Matrix n n' k)) l := by
    intro j hj hK
    refine KerRedStep.kerRed_extend k ψ ν hψ hψ1 hν _ _ M l _ _ _ _ _ subset_rfl ?_ ?_ hK ?_ ?_
    · intro e he
      rw [mem_itUp] at he ⊢
      exact ⟨he.1, fun i hi => (he.2 i hi).imp_right (by omega)⟩
    · rw [Finset.disjoint_left]
      intro e he he'
      rw [mem_evAll] at he
      rw [mem_itUp] at he'
      exact he.1 he'.1
    · intro e he he'
      exact absurd he he'
    · rintro ⟨r, q⟩ he he' b Θ Θ' hΘ
      rw [mem_itUp] at he he'
      obtain ⟨hf, hcol⟩ := he
      rcases q with q | i
      · exact absurd ⟨hf, fun i hi => by cases hi⟩ he'
      · have hi : i.val = j := by
          by_contra hne
          apply he'
          refine ⟨hf, fun i' hi' => ?_⟩
          cases hi'
          rcases hcol i rfl with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (by omega)
        rcases r with r | l'
        · simp only [Free] at hf
          omega
        · have hjc : j < c := by omega
          have hi' : i = (⟨j, hjc⟩ : Fin c).castSucc := Fin.ext (by simp [hi])
          subst hi'
          simp only [Free, Fin.val_castSucc] at hf
          exact translate_law ψ ν hψ l hT l' ⟨j, hjc⟩ hf hj hK b Θ Θ' hΘ
  have main : ∀ d, d ≤ ρ →
      KerRed ν (evAll n n' c ρ) (itUp n n' c ρ (ρ - d)) (basePt c (0 : Matrix n n' k)) l := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, itUp_top]
      exact hB
    | succ d ih =>
      intro hd
      have h1 : ρ - d = (ρ - (d + 1)) + 1 := by omega
      refine step _ (by omega) ?_
      rw [← h1]
      exact ih (by omega)
  have := main ρ le_rfl
  rwa [Nat.sub_self, itUp_zero] at this

end GlobalTheory.FlatFactor.UpStage

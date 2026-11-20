import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Topology Filter Set
open scoped ContDiff

noncomputable section

namespace SimpleNormalCrossingSliceCharts

variable {X : Type} [TopologicalSpace X]

/- English proof (translation)
Rewrite using `[← isOpen_compl_iff, isOpen_iff_forall_mem_open]`. Introduce `x hx`. Take `⟨ψ, -, hxψ, -, σ, -, hW, -⟩` from `h x`. Establish `hWk` using `hW k`. Consider the cases of `hσ : σ k with`.

Consider the case `none`. Use `⟨ψ.source, ?_, ψ.open_source, hxψ⟩` and prove the remaining obligations. Introduce `y hy hyW`. Establish `hm : y ∈ W k ∩ ψ.source` using `⟨hyW, hy⟩`. Rewrite `hm` using `[hWk]`.

Take `⟨i, hi, -⟩` from `hm.2`. Rewrite `hi` using `[hσ]`. Conclude with `absurd hi (by simp)`. Consider the case `some i`. Use `⟨ψ.source ∩ ψ ⁻¹' {v | v i ≠ 0}, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `y ⟨hy, hyi⟩ hyW`. Establish `hm : y ∈ W k ∩ ψ.source` using `⟨hyW, hy⟩`. Rewrite `hm` using `[hWk]`. Take `⟨j, hj, hj0⟩` from `hm.2`. Rewrite `hj` using `[hσ, Option.some.injEq]`.

Rewrite `hj0` using `[← hj]`. Conclude with `hyi hj0`. Conclude with `ψ.continuousOn.isOpen_inter_preimage ψ.open_source (isOpen_ne_fun (continuous_apply i) continuous_const)`. Use `⟨hxψ, ?_⟩` and prove the remaining obligations. Introduce `hxi`.

Establish `hm : x ∈ {y ∈ ψ.source | ∃ j, σ k = some j ∧ ψ y j = 0}` using `⟨hxψ, i, hσ, hxi⟩`. Rewrite `hm` using `[← hWk]`. Conclude with `hx hm.1`.
-/
theorem isClosed_divisorComponent {e : ℕ} (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ}
    (m : Fin r → ℕ) (W : Fin r → Set X) (h : IsSNC A L s m W) (k : Fin r) : IsClosed (W k) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨ψ, -, hxψ, -, σ, -, hW, -⟩ := h x
  have hWk := hW k
  cases hσ : σ k with
  | none =>
    refine ⟨ψ.source, ?_, ψ.open_source, hxψ⟩
    intro y hy hyW
    have hm : y ∈ W k ∩ ψ.source := ⟨hyW, hy⟩
    rw [hWk] at hm
    obtain ⟨i, hi, -⟩ := hm.2
    rw [hσ] at hi
    exact absurd hi (by simp)
  | some i =>
    refine ⟨ψ.source ∩ ψ ⁻¹' {v | v i ≠ 0}, ?_, ?_, ?_⟩
    · rintro y ⟨hy, hyi⟩ hyW
      have hm : y ∈ W k ∩ ψ.source := ⟨hyW, hy⟩
      rw [hWk] at hm
      obtain ⟨j, hj, hj0⟩ := hm.2
      rw [hσ, Option.some.injEq] at hj
      rw [← hj] at hj0
      exact hyi hj0
    · exact ψ.continuousOn.isOpen_inter_preimage ψ.open_source
        (isOpen_ne_fun (continuous_apply i) continuous_const)
    · refine ⟨hxψ, ?_⟩
      intro hxi
      have hm : x ∈ {y ∈ ψ.source | ∃ j, σ k = some j ∧ ψ y j = 0} := ⟨hxψ, i, hσ, hxi⟩
      rw [← hWk] at hm
      exact hx hm.1

open Classical in

def sliceChart {e : ℕ} (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)) (i : Fin (e + 1))
    (S : Set X) (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w0 : S) :
    OpenPartialHomeomorph S (Fin e → ℂ) where
  toFun w := i.removeNth (ψ w)
  invFun z := if h : Fin.insertNth (α := fun _ => ℂ) i 0 z ∈ ψ.target then
      ⟨ψ.symm (Fin.insertNth (α := fun _ => ℂ) i 0 z),
        (hS _ (ψ.map_target h)).2 (by rw [ψ.right_inv h]; simp)⟩ else w0
  source := Subtype.val ⁻¹' ψ.source
  target := {z | Fin.insertNth (α := fun _ => ℂ) i 0 z ∈ ψ.target}
  map_source' := by
    intro w hw
    show Fin.insertNth (α := fun _ => ℂ) i 0 (i.removeNth (ψ w)) ∈ ψ.target
    have h1 : ψ w i = 0 := (hS _ hw).1 w.2
    have h2 : Fin.insertNth (α := fun _ => ℂ) i 0 (i.removeNth (ψ w)) = ψ w := by
      rw [Fin.insertNth_removeNth, Function.update_eq_self_iff, h1]
    rw [h2]
    exact ψ.map_source hw
  map_target' := by
    intro z hz
    simp only [mem_ofPred_eq] at hz
    simp only [mem_preimage, dif_pos hz]
    exact ψ.map_target hz
  left_inv' := by
    intro w hw
    have h1 : ψ w i = 0 := (hS _ hw).1 w.2
    have h2 : Fin.insertNth (α := fun _ => ℂ) i 0 (i.removeNth (ψ w)) = ψ w := by
      rw [Fin.insertNth_removeNth, Function.update_eq_self_iff, h1]
    have hmem : Fin.insertNth (α := fun _ => ℂ) i 0 (i.removeNth (ψ w)) ∈ ψ.target :=
      by rw [h2]; exact ψ.map_source hw
    simp only [dif_pos hmem]
    apply Subtype.ext
    simp only [h2]
    exact ψ.left_inv hw
  right_inv' := by
    intro z hz
    simp only [mem_ofPred_eq] at hz
    simp only [dif_pos hz, ψ.right_inv hz, Fin.removeNth_insertNth]
  open_source := ψ.open_source.preimage continuous_subtype_val
  open_target := ψ.open_target.preimage (continuous_const.finInsertNth i continuous_id)
  continuousOn_toFun := by
    have hR : Continuous (fun v : Fin (e + 1) → ℂ => i.removeNth v) :=
      continuous_pi fun l => continuous_apply _
    exact hR.comp_continuousOn (ψ.continuousOn.comp continuous_subtype_val.continuousOn
      (fun w hw => hw))
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hI : Continuous (fun z : Fin e → ℂ => Fin.insertNth (α := fun _ => ℂ) i 0 z) :=
      continuous_const.finInsertNth i continuous_id
    refine (ψ.continuousOn_symm.comp hI.continuousOn (fun z hz => hz)).congr ?_
    intro z hz
    have hz' : Fin.insertNth (α := fun _ => ℂ) i 0 z ∈ ψ.target := hz
    simp only [Function.comp_apply, dif_pos hz']

open Classical in
/- English proof (translation)
Take `⟨w, hw⟩ : ∃ w, w = (sliceChart ψ i S hS w0).symm z` from `⟨_, rfl⟩`. Rewrite using `[← hw]`. Establish `hws : w ∈ (sliceChart ψ i S hS w0).source`. Rewrite using `[hw]`. Conclude with `(sliceChart ψ i S hS w0).map_target hz`.

Establish `hwz : (sliceChart ψ i S hS w0) w = z`. Rewrite using `[hw]`. Conclude with `(sliceChart ψ i S hS w0).right_inv hz`. Establish `hψw : (w : X) ∈ ψ.source` using `hws`. Establish `h0 : ψ w i = 0` using `(hS _ hψw).1 w.2`.

Establish `hrem : i.removeNth (ψ w) = z` using `hwz`. Establish `h2 : Fin.insertNth (α` using `fun _ => ℂ) i 0 (i.removeNth (ψ w)) = ψ w := by`. Rewrite using `[Fin.insertNth_removeNth, Function.update_eq_self_iff, h0]`. Rewrite `h2` using `[hrem]`. Rewrite using `[h2, ψ.left_inv hψw]`.
-/
theorem sliceChart_symm_val {e : ℕ} (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ))
    (i : Fin (e + 1)) (S : Set X) (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w0 : S)
    {z : Fin e → ℂ} (hz : Fin.insertNth (α := fun _ => ℂ) i 0 z ∈ ψ.target) :
    ((sliceChart ψ i S hS w0).symm z : X) = ψ.symm (Fin.insertNth (α := fun _ => ℂ) i 0 z) := by
  obtain ⟨w, hw⟩ : ∃ w, w = (sliceChart ψ i S hS w0).symm z := ⟨_, rfl⟩
  rw [← hw]
  have hws : w ∈ (sliceChart ψ i S hS w0).source := by
    rw [hw]
    exact (sliceChart ψ i S hS w0).map_target hz
  have hwz : (sliceChart ψ i S hS w0) w = z := by
    rw [hw]
    exact (sliceChart ψ i S hS w0).right_inv hz
  have hψw : (w : X) ∈ ψ.source := hws
  have h0 : ψ w i = 0 := (hS _ hψw).1 w.2
  have hrem : i.removeNth (ψ w) = z := hwz
  have h2 : Fin.insertNth (α := fun _ => ℂ) i 0 (i.removeNth (ψ w)) = ψ w := by
    rw [Fin.insertNth_removeNth, Function.update_eq_self_iff, h0]
  rw [hrem] at h2
  rw [h2, ψ.left_inv hψw]

/- English proof (translation)
Rewrite using `[analyticAt_pi_iff]`. Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Fin.insertNth_apply_same]`.

Conclude with `analyticAt_const`. Take `⟨j', rfl⟩` from `Fin.exists_succAbove_eq hj`. Simplify using `only [Fin.insertNth_apply_succAbove]`. Conclude with `analyticAt_pi_iff.1 analyticAt_id j'`.
-/
theorem analyticAt_ins {e : ℕ} (i : Fin (e + 1)) (z : Fin e → ℂ) :
    AnalyticAt ℂ (fun z' : Fin e → ℂ => Fin.insertNth (α := fun _ => ℂ) i 0 z') z := by
  rw [analyticAt_pi_iff]
  intro j
  by_cases hj : j = i
  · subst hj
    simp only [Fin.insertNth_apply_same]
    exact analyticAt_const
  · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [Fin.insertNth_apply_succAbove]
    exact analyticAt_pi_iff.1 analyticAt_id j'

/- English proof (translation)
Rewrite `hF`, the goal using `[analyticAt_pi_iff]`. Introduce `j`. Conclude with `hF (i.succAbove j)`.
-/
theorem analyticAt_removeNth_comp {e : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (e + 1)) {F : E → Fin (e + 1) → ℂ} {z : E} (hF : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (fun z' => i.removeNth (F z')) z := by
  rw [analyticAt_pi_iff] at hF ⊢
  intro j
  exact hF (i.succAbove j)

/- English proof (translation)
Take `⟨j, hj⟩` from `A.cover (ψ₁.symm v)`. Establish `ha : AnalyticAt ℂ (A.chart j ∘ ψ₁.symm) v` using `(h₁ j).2 v ⟨hv, hj⟩`. Establish `hb : AnalyticAt ℂ (ψ₂ ∘ (A.chart j).symm) ((A.chart j ∘ ψ₁.symm) v)`. Apply `(h₂ j).1` to reduce the goal to its premises. Use `⟨(A.chart j).map_source hj, ?_⟩` and prove the remaining obligations.

Use `show (A.chart j).symm ((A.chart j) (ψ₁.symm v)) ∈ ψ₂.source`. Rewrite using `[(A.chart j).left_inv hj]`. Conclude with `hv2`. Establish `hc` using `hb.comp ha`. Apply `hc.congr` to reduce the goal to its premises.

Establish `hn : ψ₁.symm ⁻¹' (A.chart j).source ∈ 𝓝 v` using `(ψ₁.continuousAt_symm hv).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)`. Use `filter_upwards [hn] with w hw`. Simplify using `only [Function.comp_apply, (A.chart j).left_inv hw]`.
-/
theorem compat_trans {e : ℕ} (A : FinHolAtlas e X) {ψ₁ ψ₂ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (h₁ : IsCompatChart A ψ₁) (h₂ : IsCompatChart A ψ₂) {v : Fin e → ℂ} (hv : v ∈ ψ₁.target)
    (hv2 : ψ₁.symm v ∈ ψ₂.source) : AnalyticAt ℂ (ψ₂ ∘ ψ₁.symm) v := by
  obtain ⟨j, hj⟩ := A.cover (ψ₁.symm v)
  have ha : AnalyticAt ℂ (A.chart j ∘ ψ₁.symm) v := (h₁ j).2 v ⟨hv, hj⟩
  have hb : AnalyticAt ℂ (ψ₂ ∘ (A.chart j).symm) ((A.chart j ∘ ψ₁.symm) v) := by
    apply (h₂ j).1
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm ((A.chart j) (ψ₁.symm v)) ∈ ψ₂.source
    rw [(A.chart j).left_inv hj]
    exact hv2
  have hc := hb.comp ha
  apply hc.congr
  have hn : ψ₁.symm ⁻¹' (A.chart j).source ∈ 𝓝 v :=
    (ψ₁.continuousAt_symm hv).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
  filter_upwards [hn] with w hw
  simp only [Function.comp_apply, (A.chart j).left_inv hw]

/- English proof (translation)
Introduce `z hz`. Establish `hzt : Fin.insertNth (α` using `fun _ => ℂ) i₁ 0 z ∈ ψ₁.target := hz.1`. Establish `hval` using `sliceChart_symm_val ψ₁ i₁ S h₁ w₁ hzt`. Establish `hsrc : ψ₁.symm (Fin.insertNth (α` using `fun _ => ℂ) i₁ 0 z) ∈ ψ₂.source := by`. Establish `h2` using `hz.2`.

Rewrite using `[← hval]`. Conclude with `h2`. Establish `hF : AnalyticAt ℂ (fun z' : Fin e → ℂ => (ψ₂ ∘ ψ₁.symm) (Fin.insertNth (α` using `fun _ => ℂ) i₁ 0 z')) z := (compat_trans A hc₁ hc₂ hzt hsrc).comp (analyticAt_ins i₁ z)`. Establish `hG` using `analyticAt_removeNth_comp i₂ hF`. Apply `hG.congr` to reduce the goal to its premises.

Use `filter_upwards [(sliceChart ψ₁ i₁ S h₁ w₁).open_target.mem_nhds hz.1] with z' hz'`. Use `show _ = i₂.removeNth (ψ₂ (((sliceChart ψ₁ i₁ S h₁ w₁).symm z' : S) : X))`. Rewrite using `[sliceChart_symm_val ψ₁ i₁ S h₁ w₁ hz']`. Both sides reduce to the same expression.
-/
theorem slice_trans {e : ℕ} (A : FinHolAtlas (e + 1) X) (S : Set X)
    {ψ₁ ψ₂ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i₁ i₂ : Fin (e + 1)}
    (h₁ : ∀ y ∈ ψ₁.source, y ∈ S ↔ ψ₁ y i₁ = 0) (h₂ : ∀ y ∈ ψ₂.source, y ∈ S ↔ ψ₂ y i₂ = 0)
    (w₁ w₂ : S) (hc₁ : IsCompatChart A ψ₁) (hc₂ : IsCompatChart A ψ₂) :
    AnalyticOnNhd ℂ (sliceChart ψ₂ i₂ S h₂ w₂ ∘ (sliceChart ψ₁ i₁ S h₁ w₁).symm)
      ((sliceChart ψ₁ i₁ S h₁ w₁).target ∩
        (sliceChart ψ₁ i₁ S h₁ w₁).symm ⁻¹' (sliceChart ψ₂ i₂ S h₂ w₂).source) := by
  intro z hz
  have hzt : Fin.insertNth (α := fun _ => ℂ) i₁ 0 z ∈ ψ₁.target := hz.1
  have hval := sliceChart_symm_val ψ₁ i₁ S h₁ w₁ hzt
  have hsrc : ψ₁.symm (Fin.insertNth (α := fun _ => ℂ) i₁ 0 z) ∈ ψ₂.source := by
    have h2 := hz.2
    rw [← hval]
    exact h2
  have hF : AnalyticAt ℂ
      (fun z' : Fin e → ℂ => (ψ₂ ∘ ψ₁.symm) (Fin.insertNth (α := fun _ => ℂ) i₁ 0 z')) z :=
    (compat_trans A hc₁ hc₂ hzt hsrc).comp (analyticAt_ins i₁ z)
  have hG := analyticAt_removeNth_comp i₂ hF
  apply hG.congr
  filter_upwards [(sliceChart ψ₁ i₁ S h₁ w₁).open_target.mem_nhds hz.1] with z' hz'
  show _ = i₂.removeNth (ψ₂ (((sliceChart ψ₁ i₁ S h₁ w₁).symm z' : S) : X))
  rw [sliceChart_symm_val ψ₁ i₁ S h₁ w₁ hz']
  rfl

/- English proof (translation)
Introduce `z hz`. Establish `hzt : Fin.insertNth (α` using `fun _ => ℂ) i 0 z ∈ ψ.target := hz.1`. Establish `hval` using `sliceChart_symm_val ψ i S hS w0 hzt`. Establish `hsrc : ψ.symm (Fin.insertNth (α` using `fun _ => ℂ) i 0 z) ∈ (A.chart k).source := by`. Establish `h2` using `hz.2`.

Rewrite using `[← hval]`. Conclude with `h2`. Establish `hF : AnalyticAt ℂ (fun z' : Fin e → ℂ => (A.chart k ∘ ψ.symm) (Fin.insertNth (α` using `fun _ => ℂ) i 0 z')) z := ((hc k).2 _ ⟨hzt, hsrc⟩).comp (analyticAt_ins i z)`. Apply `hF.congr` to reduce the goal to its premises. Use `filter_upwards [(sliceChart ψ i S hS w0).open_target.mem_nhds hz.1] with z' hz'`.

Use `show _ = A.chart k (((sliceChart ψ i S hS w0).symm z' : S) : X)`. Rewrite using `[sliceChart_symm_val ψ i S hS w0 hz']`. Both sides reduce to the same expression.
-/
theorem slice_holo {e : ℕ} (A : FinHolAtlas (e + 1) X) (S : Set X)
    {ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)} {i : Fin (e + 1)}
    (hS : ∀ y ∈ ψ.source, y ∈ S ↔ ψ y i = 0) (w0 : S) (hc : IsCompatChart A ψ) (k : Fin A.n) :
    AnalyticOnNhd ℂ (A.chart k ∘ Subtype.val ∘ (sliceChart ψ i S hS w0).symm)
      ((sliceChart ψ i S hS w0).target ∩
        (sliceChart ψ i S hS w0).symm ⁻¹' (Subtype.val ⁻¹' (A.chart k).source)) := by
  intro z hz
  have hzt : Fin.insertNth (α := fun _ => ℂ) i 0 z ∈ ψ.target := hz.1
  have hval := sliceChart_symm_val ψ i S hS w0 hzt
  have hsrc : ψ.symm (Fin.insertNth (α := fun _ => ℂ) i 0 z) ∈ (A.chart k).source := by
    have h2 := hz.2
    rw [← hval]
    exact h2
  have hF : AnalyticAt ℂ
      (fun z' : Fin e → ℂ => (A.chart k ∘ ψ.symm) (Fin.insertNth (α := fun _ => ℂ) i 0 z')) z :=
    ((hc k).2 _ ⟨hzt, hsrc⟩).comp (analyticAt_ins i z)
  apply hF.congr
  filter_upwards [(sliceChart ψ i S hS w0).open_target.mem_nhds hz.1] with z' hz'
  show _ = A.chart k (((sliceChart ψ i S hS w0).symm z' : S) : X)
  rw [sliceChart_symm_val ψ i S hS w0 hz']
  rfl

end SimpleNormalCrossingSliceCharts

open SimpleNormalCrossingSliceCharts

def SNCClosedStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ) (W : Fin r → Set X), IsSNC A L s m W →
      ∀ k, IsClosed (W k)

/- English proof (translation)
Unfold `SNCClosedStatement`. Introduce `e X _ A L s r m W h k`. Conclude with `isClosed_divisorComponent A L s m W h k`.
-/
theorem sncClosed : SNCClosedStatement := by
  unfold SNCClosedStatement
  intro e X _ A L s r m W h k
  exact isClosed_divisorComponent A L s m W h k

/- English proof (translation)
Unfold `SNCInducedAtlasStatement`. Introduce `e X _ _ _ A L s r m W _ _ h k`. Establish `hK : IsCompact (W k)` using `(isClosed_divisorComponent A L s m W h k).isCompact`. Unfold `IsSNC at h`. Use `choose ψ hψ using h`.

Establish `h' : ∀ x, ∃ σ : Fin r → Option (Fin (e + 1)), ∀ k', W k' ∩ (ψ x).source = {y ∈ (ψ x).source | ∃ i, σ k' = some i ∧ (ψ x) y i = 0}`. Introduce `x`. Take `⟨-, -, -, σ, -, hW, -⟩` from `hψ x`. Conclude with `⟨σ, hW⟩`. Use `choose σ hσ using h'`.

Establish `hι : ∀ x : W k, ∃ i, σ x.1 k = some i`. Introduce `x`. Establish `hm : (x : X) ∈ W k ∩ (ψ x.1).source` using `⟨x.2, (hψ x.1).2.1⟩`. Rewrite `hm` using `[hσ x.1 k]`. Take `⟨i, hi, -⟩` from `hm.2`.

Conclude with `⟨i, hi⟩`. Use `choose ι hι using hι`. Establish `hS : ∀ x : W k, ∀ y ∈ (ψ x.1).source, y ∈ W k ↔ (ψ x.1) y (ι x) = 0`. Introduce `x y hy`. Prove the components needed by the constructor for the conclusion.

Introduce `hyW`. Establish `hm : y ∈ W k ∩ (ψ x.1).source` using `⟨hyW, hy⟩`. Rewrite `hm` using `[hσ x.1 k]`. Take `⟨i', hi', h0⟩` from `hm.2`. Rewrite `hi'` using `[hι x, Option.some.injEq]`.

Rewrite using `[hi']`. Conclude with `h0`. Introduce `h0`. Establish `hm : y ∈ {y ∈ (ψ x.1).source | ∃ i', σ x.1 k = some i' ∧ (ψ x.1) y i' = 0}` using `⟨hy, ι x, hι x, h0⟩`. Rewrite `hm` using `[← hσ x.1 k]`.

Conclude with `hm.1`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun x : W k => (ψ x.1).source) (fun x => (ψ x.1).open_source) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, (hψ y).2.1⟩)`. Use `⟨{ n := t.card chart := fun j => sliceChart (ψ (t.equivFin.symm j).1.1) (ι (t.equivFin.symm j).1) (W k) (hS (t.equivFin.symm j).1) (t.equivFin.symm j).1 cover := ?_ holo := fun j j' => slice_trans A (W k) (hS (t.equivFin.symm j).1) (hS (t.equivFin.symm j').1) (t.equivFin.symm j). …` and prove the remaining obligations. Introduce `y`. Take `⟨x, hxt, hyx⟩` from `Set.mem_iUnion₂.1 (ht y.2)`.

Use `⟨t.equivFin ⟨x, hxt⟩, ?_⟩` and prove the remaining obligations. Use `show (y : X) ∈ (ψ (t.equivFin.symm (t.equivFin ⟨x, hxt⟩)).1.1).source`. Rewrite using `[Equiv.symm_apply_apply]`. Conclude with `hyx`. Unfold `HoloMap`.

Use `⟨continuous_subtype_val, fun j k' => ?_⟩` and prove the remaining obligations. Conclude with `slice_holo A (W k) (hS (t.equivFin.symm j).1) (t.equivFin.symm j).1 (hψ (t.equivFin.symm j).1.1).1 k'`.
-/
theorem sncInducedAtlas : SNCInducedAtlasStatement := by
  unfold SNCInducedAtlasStatement
  intro e X _ _ _ A L s r m W _ _ h k
  have hK : IsCompact (W k) := (isClosed_divisorComponent A L s m W h k).isCompact
  unfold IsSNC at h
  choose ψ hψ using h
  have h' : ∀ x, ∃ σ : Fin r → Option (Fin (e + 1)),
      ∀ k', W k' ∩ (ψ x).source = {y ∈ (ψ x).source | ∃ i, σ k' = some i ∧ (ψ x) y i = 0} := by
    intro x
    obtain ⟨-, -, -, σ, -, hW, -⟩ := hψ x
    exact ⟨σ, hW⟩
  choose σ hσ using h'
  have hι : ∀ x : W k, ∃ i, σ x.1 k = some i := by
    intro x
    have hm : (x : X) ∈ W k ∩ (ψ x.1).source := ⟨x.2, (hψ x.1).2.1⟩
    rw [hσ x.1 k] at hm
    obtain ⟨i, hi, -⟩ := hm.2
    exact ⟨i, hi⟩
  choose ι hι using hι
  have hS : ∀ x : W k, ∀ y ∈ (ψ x.1).source, y ∈ W k ↔ (ψ x.1) y (ι x) = 0 := by
    intro x y hy
    constructor
    · intro hyW
      have hm : y ∈ W k ∩ (ψ x.1).source := ⟨hyW, hy⟩
      rw [hσ x.1 k] at hm
      obtain ⟨i', hi', h0⟩ := hm.2
      rw [hι x, Option.some.injEq] at hi'
      rw [hi']
      exact h0
    · intro h0
      have hm : y ∈ {y ∈ (ψ x.1).source | ∃ i', σ x.1 k = some i' ∧ (ψ x.1) y i' = 0} :=
        ⟨hy, ι x, hι x, h0⟩
      rw [← hσ x.1 k] at hm
      exact hm.1
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : W k => (ψ x.1).source)
    (fun x => (ψ x.1).open_source) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, (hψ y).2.1⟩)
  refine ⟨{ n := t.card
            chart := fun j => sliceChart (ψ (t.equivFin.symm j).1.1) (ι (t.equivFin.symm j).1) (W k)
              (hS (t.equivFin.symm j).1) (t.equivFin.symm j).1
            cover := ?_
            holo := fun j j' => slice_trans A (W k) (hS (t.equivFin.symm j).1)
              (hS (t.equivFin.symm j').1) (t.equivFin.symm j).1 (t.equivFin.symm j').1
              (hψ (t.equivFin.symm j).1.1).1 (hψ (t.equivFin.symm j').1.1).1 }, ?_⟩
  · intro y
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht y.2)
    refine ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
    show (y : X) ∈ (ψ (t.equivFin.symm (t.equivFin ⟨x, hxt⟩)).1.1).source
    rw [Equiv.symm_apply_apply]
    exact hyx
  · unfold HoloMap
    refine ⟨continuous_subtype_val, fun j k' => ?_⟩
    exact slice_holo A (W k) (hS (t.equivFin.symm j).1) (t.equivFin.symm j).1
      (hψ (t.equivFin.symm j).1.1).1 k'

end

end ReciprocityTheory.AnForm.M

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableMmRight

open MeasureTheory Matrix
open scoped ENNReal NNReal

noncomputable section

namespace PI.QuotInvW

variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}

def avgS (μS : Measure (MtM m)) (f : MtM m → ℝ≥0∞) (x : MtM m) : ℝ≥0∞ := ∫⁻ s, f (mm s x) ∂μS

/- English proof (translation)
Conclude with `(hf.comp (measurable_mm (m := m))).lintegral_prod_left'`.
-/
lemma measurable_avgS [SFinite μS] {f : MtM m → ℝ≥0∞} (hf : Measurable f) :
    Measurable (avgS μS f) := by
  exact (hf.comp (measurable_mm (m := m))).lintegral_prod_left'

/- English proof (translation)
Establish `hR : μS.map (rmulQ (Matrix.of t)) = μS` using `h.2.2.2.2.2.2.1 _ ht`. Establish `hg : Measurable fun s => f (mm s y)` using `hf.comp (measurable_mm_left y)`. Unfold `avgS`. Use `symm`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[← mm_assoc]`. Both sides reduce to the same expression.
-/
lemma avgS_mm (h : QuotientSetting G S μG μS ν) {f : MtM m → ℝ≥0∞} (hf : Measurable f)
    {t : MtM m} (ht : Matrix.of t ∈ S) (y : MtM m) : avgS μS f (mm t y) = avgS μS f y := by
  have hR : μS.map (rmulQ (Matrix.of t)) = μS := h.2.2.2.2.2.2.1 _ ht
  have hg : Measurable fun s => f (mm s y) := hf.comp (measurable_mm_left y)
  unfold avgS
  symm
  calc ∫⁻ s, f (mm s y) ∂μS = ∫⁻ s, f (mm s y) ∂(μS.map (rmulQ (Matrix.of t))) := by rw [hR]
    _ = ∫⁻ s, f (mm (rmulQ (Matrix.of t) s) y) ∂μS := lintegral_map hg (measurable_mm_left t)
    _ = ∫⁻ s, f (mm s (mm t y)) ∂μS := by
        congr 1; funext s
        rw [← mm_assoc]; rfl

/- English proof (translation)
Introduce `h0`. Unfold `avgS at h0`. Establish `h1` using `(lintegral_eq_zero_iff (f := fun s => f (mm s x)) (hf.comp (measurable_mm_left x))).1 h0`. Establish `hμ : μS Set.univ = 0`. Use `ae_iff.1 h1` as an intermediate fact.

Simplify `this` using `[hpos]`. Conclude with `h.2.2.2.2.1.2.1 (Measure.measure_univ_eq_zero.1 hμ)`.
-/
lemma avgS_ne_zero (h : QuotientSetting G S μG μS ν) {f : MtM m → ℝ≥0∞} (hf : Measurable f)
    (hpos : ∀ x, f x ≠ 0) (x : MtM m) : avgS μS f x ≠ 0 := by
  intro h0
  unfold avgS at h0
  have h1 := (lintegral_eq_zero_iff (f := fun s => f (mm s x)) (hf.comp (measurable_mm_left x))).1 h0
  have hμ : μS Set.univ = 0 := by
    have := ae_iff.1 h1
    simpa [hpos] using this
  exact h.2.2.2.2.1.2.1 (Measure.measure_univ_eq_zero.1 hμ)

/- English proof (translation)
Establish `hGg` using `h.1`. Use `haveI : SigmaFinite μG := h.2.2.2.1.1`. Use `haveI : SigmaFinite μS := h.2.2.2.2.1.1`. Take `⟨f0, hf0pos, hf0m, hf0int⟩` from `exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero`. Use `set f : MtM m → ℝ≥0∞ := fun x => (f0 x : ℝ≥0∞) with hfdef`.

Establish `hfm : Measurable f` using `measurable_coe_nnreal_ennreal.comp hf0m`. Establish `hfpos : ∀ x, f x ≠ 0` using `fun x => by simp [f, (hf0pos x).ne']`. Establish `ham : Measurable (avgS μS f)` using `measurable_avgS hfm`. Establish `ha0 : ∀ x, avgS μS f x ≠ 0` using `avgS_ne_zero h hfm hfpos`. Establish `hafin : ∀ᵐ x ∂ν, avgS μS f x < ⊤`.

Apply `ae_lt_top ham` to reduce the goal to its premises. Use `weil h hfm` as an intermediate fact. Express the relevant statement in the definitionally equal form `∫⁻ x, (∫⁻ s, f (mm s x) ∂μS) ∂ν ≠ ⊤`. Rewrite using `[← this]`. Conclude with `(hf0int.trans ENNReal.one_lt_top).ne`.

Take `⟨hginvG, hgg⟩` from `hGg.2.2.2 _ hg`. Establish `hgiG : Matrix.of (minv g) ∈ G` using `hginvG`. Establish `hdet : IsUnit (Matrix.of g).det` using `isUnit_iff_exists_inv.2 ⟨(Matrix.of g)⁻¹.det, by rw [← Matrix.det_mul, hgg, Matrix.det_one]⟩`. Establish `hgig : mm (minv g) g = oneM`. Use `Matrix.nonsing_inv_mul (Matrix.of g) hdet` as an intermediate fact.

Use function extensionality and compare the values at `i j`. Conclude with `congrFun (congrFun this i) j`. Establish `hggi : mm g (minv g) = oneM`. Use function extensionality and compare the values at `i j`. Conclude with `congrFun (congrFun hgg i) j`.

Establish `hRG : μG.map (rmulQ (Matrix.of (minv g))) = μG` using `h.2.2.2.2.2.1 _ hgiG`. Use `set F' : MtM m → ℝ≥0∞ := fun x => F x / avgS μS f (mm x (minv g)) with hF'def`. Establish `hF'm : Measurable F'` using `hF.div (ham.comp (measurable_mm_left (minv g)))`. Establish `hF'i0 : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F' (mm s x) = F' x`. Introduce `s hs x hx`.

Simplify using `only [F']`. Rewrite using `[hFi s hs x hx, mm_assoc, avgS_mm h hfm hs]`. Establish `hF'i : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F' (mm s x) = F' x` using `fun s hs x hx => hF'i0 (Matrix.of.symm s) hs x hx`. Establish `hL : ∫⁻ x, F' (mm x g) * avgS μS f x ∂ν = ∫⁻ x, F' (mm x g) * f x ∂μG`. Use `weil_inv h (H := fun x => F' (mm x g)) (f := f) (hF'm.comp (measurable_mm_left g)) hfm (by` as an intermediate fact.

Introduce `s hs x hx`. Establish `key : ∀ s' : MtM m, Matrix.of s' ∈ S → F' (mm (mm s' x) g) = F' (mm x g)`. Introduce `s' hs'`. Rewrite using `[mm_assoc]`. Conclude with `hF'i0 s' hs' (mm x g) (mm_mem hGg hx hg)`.

Conclude with `key (Matrix.of.symm s) hs)`. Conclude with `this.symm`. Establish `hmid : ∫⁻ x, F' (mm x g) * f x ∂μG = ∫⁻ x, F' x * f (mm x (minv g)) ∂μG`. Establish `hφ : Measurable fun x => F' (mm x g) * f x` using `(hF'm.comp (measurable_mm_left g)).mul hfm`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `e : mm (rmulQ (Matrix.of (minv g)) x) g = x`. Express the relevant statement in the definitionally equal form `mm (mm x (minv g)) g = x`. Rewrite using `[mm_assoc, hgig, mm_oneM]`.

Rewrite using `[e]`. Both sides reduce to the same expression. Establish `hR : ∫⁻ x, F' x * f (mm x (minv g)) ∂μG = ∫⁻ x, F' x * avgS μS f (mm x (minv g)) ∂ν`. Use `weil_inv h (H := F') (f := fun x => f (mm x (minv g))) hF'm (hfm.comp (measurable_mm_left (minv g))) hF'i` as an intermediate fact. Rewrite using `[this]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Use `congr 1`. Unfold `avgS`. Use `congr 1`.

Use function extensionality and compare the values at `s`. Simplify using `only [mm_assoc]`. Establish `hRHS : ∫⁻ x, F' x * avgS μS f (mm x (minv g)) ∂ν ≤ ∫⁻ x, F x ∂ν`. Apply `lintegral_mono` to reduce the goal to its premises. Introduce `x`.

Simplify using `only [F']`. Distinguish the cases in `hx : avgS μS f (mm x (minv g)) = ⊤`. Rewrite using `[hx]`. Simplify using the standard rewrite rules. Rewrite using `[ENNReal.div_mul_cancel (ha0 _) hx]`.

Establish `hLHS : ∫⁻ x, F (mm x g) ∂ν = ∫⁻ x, F' (mm x g) * avgS μS f x ∂ν`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hafin] with x hx`. Simplify using `only [F']`. Rewrite using `[mm_assoc, hggi, mm_oneM, ENNReal.div_mul_cancel (ha0 x) hx.ne]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem ineq (h : QuotientSetting G S μG μS ν) {F : MtM m → ℝ≥0∞} (hF : Measurable F)
    (hFi : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x)
    {g : MtM m} (hg : Matrix.of g ∈ G) :
    ∫⁻ x, F (mm x g) ∂ν ≤ ∫⁻ x, F x ∂ν := by
  have hGg := h.1
  haveI : SigmaFinite μG := h.2.2.2.1.1
  haveI : SigmaFinite μS := h.2.2.2.2.1.1
  obtain ⟨f0, hf0pos, hf0m, hf0int⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set f : MtM m → ℝ≥0∞ := fun x => (f0 x : ℝ≥0∞) with hfdef
  have hfm : Measurable f := measurable_coe_nnreal_ennreal.comp hf0m
  have hfpos : ∀ x, f x ≠ 0 := fun x => by simp [f, (hf0pos x).ne']
  have ham : Measurable (avgS μS f) := measurable_avgS hfm
  have ha0 : ∀ x, avgS μS f x ≠ 0 := avgS_ne_zero h hfm hfpos

  have hafin : ∀ᵐ x ∂ν, avgS μS f x < ⊤ := by
    apply ae_lt_top ham
    have := weil h hfm
    change ∫⁻ x, (∫⁻ s, f (mm s x) ∂μS) ∂ν ≠ ⊤
    rw [← this]
    exact (hf0int.trans ENNReal.one_lt_top).ne
  obtain ⟨hginvG, hgg⟩ := hGg.2.2.2 _ hg
  have hgiG : Matrix.of (minv g) ∈ G := hginvG
  have hdet : IsUnit (Matrix.of g).det :=
    isUnit_iff_exists_inv.2 ⟨(Matrix.of g)⁻¹.det, by rw [← Matrix.det_mul, hgg, Matrix.det_one]⟩
  have hgig : mm (minv g) g = oneM := by
    have := Matrix.nonsing_inv_mul (Matrix.of g) hdet
    funext i j; exact congrFun (congrFun this i) j
  have hggi : mm g (minv g) = oneM := by
    funext i j; exact congrFun (congrFun hgg i) j
  have hRG : μG.map (rmulQ (Matrix.of (minv g))) = μG := h.2.2.2.2.2.1 _ hgiG

  set F' : MtM m → ℝ≥0∞ := fun x => F x / avgS μS f (mm x (minv g)) with hF'def
  have hF'm : Measurable F' := hF.div (ham.comp (measurable_mm_left (minv g)))
  have hF'i0 : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F' (mm s x) = F' x := by
    intro s hs x hx
    simp only [F']
    rw [hFi s hs x hx, mm_assoc, avgS_mm h hfm hs]
  have hF'i : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F' (mm s x) = F' x :=
    fun s hs x hx => hF'i0 (Matrix.of.symm s) hs x hx
  have hL : ∫⁻ x, F' (mm x g) * avgS μS f x ∂ν = ∫⁻ x, F' (mm x g) * f x ∂μG := by
    have := weil_inv h (H := fun x => F' (mm x g)) (f := f) (hF'm.comp (measurable_mm_left g)) hfm
      (by
        intro s hs x hx
        have key : ∀ s' : MtM m, Matrix.of s' ∈ S → F' (mm (mm s' x) g) = F' (mm x g) := by
          intro s' hs'
          rw [mm_assoc]
          exact hF'i0 s' hs' (mm x g) (mm_mem hGg hx hg)
        exact key (Matrix.of.symm s) hs)
    exact this.symm
  have hmid : ∫⁻ x, F' (mm x g) * f x ∂μG = ∫⁻ x, F' x * f (mm x (minv g)) ∂μG := by
    have hφ : Measurable fun x => F' (mm x g) * f x := (hF'm.comp (measurable_mm_left g)).mul hfm
    calc ∫⁻ x, F' (mm x g) * f x ∂μG
        = ∫⁻ x, F' (mm x g) * f x ∂(μG.map (rmulQ (Matrix.of (minv g)))) := by rw [hRG]
      _ = ∫⁻ x, F' (mm (rmulQ (Matrix.of (minv g)) x) g) * f (rmulQ (Matrix.of (minv g)) x) ∂μG :=
          lintegral_map hφ (measurable_mm_left (minv g))
      _ = ∫⁻ x, F' x * f (mm x (minv g)) ∂μG := by
        congr 1; funext x
        have e : mm (rmulQ (Matrix.of (minv g)) x) g = x := by
          change mm (mm x (minv g)) g = x
          rw [mm_assoc, hgig, mm_oneM]
        rw [e]; rfl
  have hR : ∫⁻ x, F' x * f (mm x (minv g)) ∂μG = ∫⁻ x, F' x * avgS μS f (mm x (minv g)) ∂ν := by
    have := weil_inv h (H := F') (f := fun x => f (mm x (minv g))) hF'm
      (hfm.comp (measurable_mm_left (minv g))) hF'i
    rw [this]
    congr 1; funext x; congr 1
    unfold avgS
    congr 1; funext s; simp only [mm_assoc]
  have hRHS : ∫⁻ x, F' x * avgS μS f (mm x (minv g)) ∂ν ≤ ∫⁻ x, F x ∂ν := by
    apply lintegral_mono; intro x
    simp only [F']
    by_cases hx : avgS μS f (mm x (minv g)) = ⊤
    · rw [hx]; simp
    · rw [ENNReal.div_mul_cancel (ha0 _) hx]
  have hLHS : ∫⁻ x, F (mm x g) ∂ν = ∫⁻ x, F' (mm x g) * avgS μS f x ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hafin] with x hx
    simp only [F']
    rw [mm_assoc, hggi, mm_oneM, ENNReal.div_mul_cancel (ha0 x) hx.ne]
  calc ∫⁻ x, F (mm x g) ∂ν = _ := hLHS
    _ = _ := hL
    _ = _ := hmid
    _ = _ := hR
    _ ≤ _ := hRHS

/- English proof (translation)
Introduce `m G S μG μS ν h F hF hFi g0 hg0`. Take `⟨g, rfl⟩ : ∃ g : MtM m, Matrix.of g = g0` from `⟨Matrix.of.symm g0, rfl⟩`. Establish `hg : Matrix.of g ∈ G` using `hg0`. Establish `hFi' : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x` using `fun s hs x hx => hFi s hs x hx`. Establish `h1 : ∫⁻ x, F (mm x g) ∂ν ≤ ∫⁻ x, F x ∂ν` using `ineq h hF hFi' (g := g) hg`.

Take `⟨hginvG, hgg⟩` from `h.1.2.2.2 _ hg`. Establish `hdet : IsUnit (Matrix.of g).det` using `isUnit_iff_exists_inv.2 ⟨(Matrix.of g)⁻¹.det, by rw [← Matrix.det_mul, hgg, Matrix.det_one]⟩`. Establish `hgig : mm (minv g) g = oneM`. Use `Matrix.nonsing_inv_mul (Matrix.of g) hdet` as an intermediate fact. Use function extensionality and compare the values at `i j`.

Conclude with `congrFun (congrFun this i) j`. Establish `h2 : ∫⁻ x, F (mm (mm x (minv g)) g) ∂ν ≤ ∫⁻ x, F (mm x g) ∂ν` using `ineq h (F := fun x => F (mm x g)) (hF.comp (measurable_mm_left g)) (by`. Introduce `s hs x hx`. Rewrite using `[mm_assoc]`. Conclude with `hFi' s hs _ (mm_mem h.1 hx hg))`.

Use the proof step `(g := minv g) hginvG`. Simplify using `only [mm_assoc, hgig, mm_oneM] at h2`. Conclude with `le_antisymm h1 h2`.
-/
theorem quotInv : PI.QuotInv := by
  intro m G S μG μS ν h F hF hFi g0 hg0
  obtain ⟨g, rfl⟩ : ∃ g : MtM m, Matrix.of g = g0 := ⟨Matrix.of.symm g0, rfl⟩
  have hg : Matrix.of g ∈ G := hg0
  have hFi' : ∀ s : MtM m, Matrix.of s ∈ S → ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x :=
    fun s hs x hx => hFi s hs x hx
  have h1 : ∫⁻ x, F (mm x g) ∂ν ≤ ∫⁻ x, F x ∂ν := ineq h hF hFi' (g := g) hg
  obtain ⟨hginvG, hgg⟩ := h.1.2.2.2 _ hg
  have hdet : IsUnit (Matrix.of g).det :=
    isUnit_iff_exists_inv.2 ⟨(Matrix.of g)⁻¹.det, by rw [← Matrix.det_mul, hgg, Matrix.det_one]⟩
  have hgig : mm (minv g) g = oneM := by
    have := Matrix.nonsing_inv_mul (Matrix.of g) hdet
    funext i j; exact congrFun (congrFun this i) j
  have h2 : ∫⁻ x, F (mm (mm x (minv g)) g) ∂ν ≤ ∫⁻ x, F (mm x g) ∂ν :=
    ineq h (F := fun x => F (mm x g)) (hF.comp (measurable_mm_left g))
      (by
        intro s hs x hx
        rw [mm_assoc]
        exact hFi' s hs _ (mm_mem h.1 hx hg))
      (g := minv g) hginvG
  simp only [mm_assoc, hgig, mm_oneM] at h2
  exact le_antisymm h1 h2

end PI.QuotInvW

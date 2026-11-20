import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M OnePoint Filter Topology MeasureTheory

namespace ProjectiveLineResolution

abbrev Pt := (Σ k, PBlk 2 k) → ℂ

abbrev JJ : Ideal (MRing (PBlk 2)) := Ideal.span {Xc 2 0}

def vec (a b : ℂ) : Pt := fun q => ![a, b] q.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma vec0 (a b : ℂ) : vec a b ⟨(), 0⟩ = a := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma vec1 (a b : ℂ) : vec a b ⟨(), 1⟩ = b := rfl

/- English proof (translation)
Use function extensionality and compare the values at `⟨k, i⟩`. Consider the cases of `k`. Use `fin_cases i`. Conclude with `h0`. Conclude with `h1`.
-/
lemma pt_ext {z z' : Pt} (h0 : z ⟨(), 0⟩ = z' ⟨(), 0⟩) (h1 : z ⟨(), 1⟩ = z' ⟨(), 1⟩) : z = z' := by
  funext ⟨k, i⟩
  cases k
  fin_cases i
  · exact h0
  · exact h1

open scoped Classical in

def lift (x y : OnePoint ℂ) : Pt := if x = ∞ then vec (crd1 y) 1 else vec 1 (crd0 y)

/- English proof (translation)
The claim follows from `if_pos rfl`.
-/
lemma lift_infty (y : OnePoint ℂ) : lift ∞ y = vec (crd1 y) 1 := if_pos rfl
/- English proof (translation)
The claim follows from `if_neg (coe_ne_infty z)`.
-/
lemma lift_coe (z : ℂ) (y : OnePoint ℂ) : lift (z : OnePoint ℂ) y = vec 1 (crd0 y) :=
  if_neg (coe_ne_infty z)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `h2 _ (Ideal.subset_span rfl)` as an intermediate fact. Simplify `this` using `[Xc]`.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hf`. Simplify using `[Xc, h2]`.
-/
lemma mem_J_iff (z : Pt) : z ∈ mcPts JJ ↔ (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ z ⟨(), 0⟩ = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := h2 _ (Ideal.subset_span rfl)
    simpa [Xc] using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun f hf => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    simp [Xc, h2]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, fun f hf => by rw [Ideal.mem_bot.mp hf]; simp⟩`.
-/
lemma mem_bot (z : Pt) (h : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : z ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) :=
  ⟨h, fun f hf => by rw [Ideal.mem_bot.mp hf]; simp⟩

/- English proof (translation)
Introduce `_` and use `⟨0, h⟩`.
-/
lemma vec_ne (a b : ℂ) (h : a ≠ 0) : ∀ k, ∃ i, vec a b ⟨k, i⟩ ≠ 0 := fun _ => ⟨0, h⟩
/- English proof (translation)
Introduce `_` and use `⟨1, one_ne_zero⟩`.
-/
lemma vec_ne' (a : ℂ) : ∀ k, ∃ i, vec a 1 ⟨k, i⟩ ≠ 0 := fun _ => ⟨1, one_ne_zero⟩

/- English proof (translation)
Proceed by induction on `x with`. Consider the case `infty => rw [lift_infty]`. Conclude with `mem_bot _ (vec_ne' _)`. Consider the case `coe z => rw [lift_coe]`. Conclude with `mem_bot _ (vec_ne _ _ one_ne_zero)`.
-/
lemma lift_mem_bot (x y : OnePoint ℂ) : lift x y ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) := by
  induction x with
  | infty => rw [lift_infty]; exact mem_bot _ (vec_ne' _)
  | coe z => rw [lift_coe]; exact mem_bot _ (vec_ne _ _ one_ne_zero)

/- English proof (translation)
Proceed by induction on `x with`. Consider the case `infty`. Use `iff_of_true ?_ rfl` and prove the remaining obligations. Rewrite using `[lift_infty]`. Conclude with `(mem_J_iff _).2 ⟨vec_ne' _, by simp⟩`.

Consider the case `coe z`. Use `iff_of_false (fun h => ?_) (coe_ne_infty z)` and prove the remaining obligations. Rewrite `h` using `[lift_coe]`. Conclude with `one_ne_zero ((mem_J_iff _).1 h).2`.
-/
lemma lift_mem_J (x : OnePoint ℂ) : lift x x ∈ mcPts JJ ↔ x = ∞ := by
  induction x with
  | infty =>
    refine iff_of_true ?_ rfl
    rw [lift_infty]
    exact (mem_J_iff _).2 ⟨vec_ne' _, by simp⟩
  | coe z =>
    refine iff_of_false (fun h => ?_) (coe_ne_infty z)
    rw [lift_coe] at h
    exact one_ne_zero ((mem_J_iff _).1 h).2

/- English proof (translation)
Break down `p with ⟨⟨⟩, i⟩` into its components or cases. Proceed by induction on `x with`. Consider the case `infty`. Rewrite using `[fsPot_U_infty]`. Use `fin_cases i`.

Establish `e : (fun y => lift ∞ y ⟨(), 0⟩) = crd1` using `funext fun y => by rw [lift_infty]; rfl show p1.HoloOn _ (fun y => lift ∞ y ⟨(), 0⟩)`. Rewrite using `[e]`. Conclude with `holomorphicOn_infiniteCoord`. Establish `e : (fun y => lift ∞ y ⟨(), 1⟩) = fun _ => 1` using `funext fun y => by rw [lift_infty]; rfl show p1.HoloOn _ (fun y => lift ∞ y ⟨(), 1⟩)`. Rewrite using `[e]`.

Conclude with `holoOn_const _ 1`. Consider the case `coe z`. Rewrite using `[fsPot_U_coe]`. Use `fin_cases i`. Establish `e : (fun y => lift (z : OnePoint ℂ) y ⟨(), 0⟩) = fun _ => 1`.

Use function extensionality and compare the values at `fun y => by rw [lift_coe]; rfl`. Use `show p1.HoloOn _ (fun y => lift (z : OnePoint ℂ) y ⟨(), 0⟩)`. Rewrite using `[e]`. Conclude with `holoOn_const _ 1`. Establish `e : (fun y => lift (z : OnePoint ℂ) y ⟨(), 1⟩) = crd0`.

Use function extensionality and compare the values at `fun y => by rw [lift_coe]; rfl`. Use `show p1.HoloOn _ (fun y => lift (z : OnePoint ℂ) y ⟨(), 1⟩)`. Rewrite using `[e]`. Conclude with `holomorphicOn_finiteCoord`.
-/
theorem holo (x : OnePoint ℂ) (p : Σ k, PBlk 2 k) :
    p1.HoloOn (fsPot.U x) (fun y => lift x y p) := by
  rcases p with ⟨⟨⟩, i⟩
  induction x with
  | infty =>
    rw [fsPot_U_infty]
    fin_cases i
    · have e : (fun y => lift ∞ y ⟨(), 0⟩) = crd1 := funext fun y => by rw [lift_infty]; rfl
      show p1.HoloOn _ (fun y => lift ∞ y ⟨(), 0⟩)
      rw [e]; exact holomorphicOn_infiniteCoord
    · have e : (fun y => lift ∞ y ⟨(), 1⟩) = fun _ => 1 := funext fun y => by rw [lift_infty]; rfl
      show p1.HoloOn _ (fun y => lift ∞ y ⟨(), 1⟩)
      rw [e]; exact holoOn_const _ 1
  | coe z =>
    rw [fsPot_U_coe]
    fin_cases i
    · have e : (fun y => lift (z : OnePoint ℂ) y ⟨(), 0⟩) = fun _ => 1 :=
        funext fun y => by rw [lift_coe]; rfl
      show p1.HoloOn _ (fun y => lift (z : OnePoint ℂ) y ⟨(), 0⟩)
      rw [e]; exact holoOn_const _ 1
    · have e : (fun y => lift (z : OnePoint ℂ) y ⟨(), 1⟩) = crd0 :=
        funext fun y => by rw [lift_coe]; rfl
      show p1.HoloOn _ (fun y => lift (z : OnePoint ℂ) y ⟨(), 1⟩)
      rw [e]; exact holomorphicOn_finiteCoord

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => 1, fun _ => one_ne_zero, by funext p; simp⟩`.
-/
lemma sameOrbit_refl (z : Pt) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by funext p; simp⟩

/- English proof (translation)
Proceed by induction on `x with`. Consider the case `infty`. Proceed by induction on `x' with`. Consider the case `infty => exact sameOrbit_refl _`. Consider the case `coe z'`.

Rewrite `hy` using `[fsPot_U_infty, fsPot_U_coe]`. Take `⟨h0, ⟨ζ, rfl⟩⟩` from `hy`. Establish `hζ : ζ ≠ 0` using `fun h => h0 (by rw [h])`. Rewrite using `[lift_infty, lift_coe]`. Use `⟨fun _ => ζ⁻¹, fun _ => inv_ne_zero hζ, pt_ext ?_ ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify using `[hζ]`. Consider the case `coe z`. Proceed by induction on `x' with`. Consider the case `infty`.

Rewrite `hy` using `[fsPot_U_infty, fsPot_U_coe]`. Take `⟨⟨ζ, rfl⟩, h0⟩` from `hy`. Establish `hζ : ζ ≠ 0` using `fun h => h0 (by rw [h])`. Rewrite using `[lift_infty, lift_coe]`. Use `⟨fun _ => ζ, fun _ => hζ, pt_ext ?_ ?_⟩` and prove the remaining obligations.

Simplify using `[hζ]`. Simplify using the standard rewrite rules. Consider the case `coe z'`. Rewrite using `[lift_coe, lift_coe]`. Conclude with `sameOrbit_refl _`.
-/
theorem compat (x x' : OnePoint ℂ) (y : OnePoint ℂ) (hy : y ∈ fsPot.U x ∩ fsPot.U x') :
    SameOrbit (lift x y) (lift x' y) := by
  induction x with
  | infty =>
    induction x' with
    | infty => exact sameOrbit_refl _
    | coe z' =>
      rw [fsPot_U_infty, fsPot_U_coe] at hy
      obtain ⟨h0, ⟨ζ, rfl⟩⟩ := hy
      have hζ : ζ ≠ 0 := fun h => h0 (by rw [h])
      rw [lift_infty, lift_coe]
      refine ⟨fun _ => ζ⁻¹, fun _ => inv_ne_zero hζ, pt_ext ?_ ?_⟩
      · simp
      · simp [hζ]
  | coe z =>
    induction x' with
    | infty =>
      rw [fsPot_U_infty, fsPot_U_coe] at hy
      obtain ⟨⟨ζ, rfl⟩, h0⟩ := hy
      have hζ : ζ ≠ 0 := fun h => h0 (by rw [h])
      rw [lift_infty, lift_coe]
      refine ⟨fun _ => ζ, fun _ => hζ, pt_ext ?_ ?_⟩
      · simp [hζ]
      · simp
    | coe z' =>
      rw [lift_coe, lift_coe]
      exact sameOrbit_refl _

/- English proof (translation)
Establish `h0 : z ⟨(), 0⟩ ≠ 0` using `fun h => hzJ ((mem_J_iff z).2 ⟨hz.1, h⟩)`. Use `⟨((z ⟨(), 1⟩ / z ⟨(), 0⟩ : ℂ) : OnePoint ℂ), fun _ => (z ⟨(), 0⟩)⁻¹, fun _ => inv_ne_zero h0, ?_⟩` and prove the remaining obligations. Rewrite using `[lift_coe]`. Use `pt_ext ?_ ?_` and prove the remaining obligations. Simplify using `[h0]`.

Simplify using `[div_eq_inv_mul]`.
-/
theorem surj (z : Pt) (hz : z ∈ mcPts (⊥ : Ideal (MRing (PBlk 2)))) (hzJ : z ∉ mcPts JJ) :
    ∃ x, SameOrbit (lift x x) z := by
  have h0 : z ⟨(), 0⟩ ≠ 0 := fun h => hzJ ((mem_J_iff z).2 ⟨hz.1, h⟩)
  refine ⟨((z ⟨(), 1⟩ / z ⟨(), 0⟩ : ℂ) : OnePoint ℂ), fun _ => (z ⟨(), 0⟩)⁻¹,
    fun _ => inv_ne_zero h0, ?_⟩
  rw [lift_coe]
  refine pt_ext ?_ ?_
  · simp [h0]
  · simp [div_eq_inv_mul]

/- English proof (translation)
Proceed by induction on `x with`. Consider the case `infty => exact absurd ((lift_mem_J ∞).2 rfl) hx`. Consider the case `coe ζ`. Take `⟨c, hc, he⟩` from `h`. Proceed by induction on `x' with`.

Consider the case `infty`. Establish `e0` using `congrFun he ⟨(), 0⟩`. Rewrite `e0` using `[lift_coe, lift_infty]`. Simplify using `at e0`. Consider the case `coe ζ'`.

Establish `e0` using `congrFun he ⟨(), 0⟩`. Establish `e1` using `congrFun he ⟨(), 1⟩`. Rewrite `e0`, `e1` using `[lift_coe, lift_coe]`. Simplify using `only [vec0, vec1, finiteCoord_coe, mul_one] at e0 e1`. Rewrite using `[e1, ← e0, one_mul]`.
-/
theorem inj (x x' : OnePoint ℂ) (hx : lift x x ∉ mcPts JJ)
    (h : SameOrbit (lift x x) (lift x' x')) : x = x' := by
  induction x with
  | infty => exact absurd ((lift_mem_J ∞).2 rfl) hx
  | coe ζ =>
    obtain ⟨c, hc, he⟩ := h
    induction x' with
    | infty =>
      have e0 := congrFun he ⟨(), 0⟩
      rw [lift_coe, lift_infty] at e0
      simp at e0
    | coe ζ' =>
      have e0 := congrFun he ⟨(), 0⟩
      have e1 := congrFun he ⟨(), 1⟩
      rw [lift_coe, lift_coe] at e0 e1
      simp only [vec0, vec1, finiteCoord_coe, mul_one] at e0 e1
      rw [e1, ← e0, one_mul]

/- English proof (translation)
Establish `h1` using `(hasFDerivAt_apply (𝕜 := ℂ) q (F y0)).comp y0 hF.hasFDerivAt`. Establish `e : (fun f : κ → ℂ => f q) ∘ F = g ∘ (fun y : Fin 1 → ℂ => y 0)` using `funext hq`. Rewrite `h1` using `[e]`. Establish `h2` using `hg.comp_hasFDerivAt y0 (hasFDerivAt_apply (𝕜 := ℂ) (0 : Fin 1) y0)`. Establish `he` using `h1.unique h2`.

Use `(Submodule.eq_bot_iff _).2 fun v hv => ?_` and prove the remaining obligations. Establish `hv' : fderiv ℂ F y0 v = 0` using `hv`. Establish `h3` using `congrArg (fun L : (Fin 1 → ℂ) →L[ℂ] ℂ => L v) he`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_apply, hv', Pi.zero_apply, smul_eq_mul] at h3`. Establish `hv0 : v 0 = 0`.

Break down `mul_eq_zero.1 h3.symm with h | h` into its components or cases. Conclude with `absurd h hd`. Conclude with `h`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`.

Conclude with `hv0`.
-/
lemma ker_eq_bot_of_coord {κ : Type*} [Fintype κ] {F : (Fin 1 → ℂ) → κ → ℂ} {y0 : Fin 1 → ℂ}
    (hF : DifferentiableAt ℂ F y0) (q : κ) (g : ℂ → ℂ) (d : ℂ) (hq : ∀ y, F y q = g (y 0))
    (hg : HasDerivAt g d (y0 0)) (hd : d ≠ 0) : (fderiv ℂ F y0).ker = ⊥ := by
  have h1 := (hasFDerivAt_apply (𝕜 := ℂ) q (F y0)).comp y0 hF.hasFDerivAt
  have e : (fun f : κ → ℂ => f q) ∘ F = g ∘ (fun y : Fin 1 → ℂ => y 0) := funext hq
  rw [e] at h1
  have h2 := hg.comp_hasFDerivAt y0 (hasFDerivAt_apply (𝕜 := ℂ) (0 : Fin 1) y0)
  have he := h1.unique h2
  refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
  have hv' : fderiv ℂ F y0 v = 0 := hv
  have h3 := congrArg (fun L : (Fin 1 → ℂ) →L[ℂ] ℂ => L v) he
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_apply, hv', Pi.zero_apply, smul_eq_mul] at h3
  have hv0 : v 0 = 0 := by
    rcases mul_eq_zero.1 h3.symm with h | h
    · exact absurd h hd
    · exact h
  funext i
  rw [Subsingleton.elim i 0]
  exact hv0

/- English proof (translation)
Establish `hy0 : p1.chart j x ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x`. Use `⟨(p1.chart j).map_source hj, ?_⟩` and prove the remaining obligations. Use `show (p1.chart j).symm (p1.chart j x) ∈ fsPot.U x`. Rewrite using `[(p1.chart j).left_inv hj]`. Conclude with `fsPot.mem_U x`.

Establish `hd : ∀ q, DifferentiableAt ℂ (fun y => lift x ((p1.chart j).symm y) q) (p1.chart j x)` using `fun q => (holo x q j _ hy0).differentiableAt`. Use `differentiableAt_pi.2 fun q => ?_` and prove the remaining obligations. Use `show DifferentiableAt ℂ (fun y => lift x ((p1.chart j).symm y) q / lift x ((p1.chart j).symm y) ⟨q.1, p q.1⟩) _`. Establish `hne : lift x ((p1.chart j).symm (p1.chart j x)) ⟨q.1, p q.1⟩ ≠ 0`. Rewrite using `[(p1.chart j).left_inv hj]`.

Conclude with `hp q.1`. Repeatedly rewrite using `[div_eq_mul_inv]`. Conclude with `(hd q).mul ((hd _).inv hne)`.
-/
lemma diffAt (x : OnePoint ℂ) (p : (k : Unit) → PBlk 2 k) (hp : ∀ k, lift x x ⟨k, p k⟩ ≠ 0)
    (j : Fin p1.n) (hj : x ∈ (p1.chart j).source) :
    DifferentiableAt ℂ (fun y => affCoord p (lift x ((p1.chart j).symm y))) (p1.chart j x) := by
  have hy0 : p1.chart j x ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x := by
    refine ⟨(p1.chart j).map_source hj, ?_⟩
    show (p1.chart j).symm (p1.chart j x) ∈ fsPot.U x
    rw [(p1.chart j).left_inv hj]
    exact fsPot.mem_U x
  have hd : ∀ q, DifferentiableAt ℂ (fun y => lift x ((p1.chart j).symm y) q) (p1.chart j x) :=
    fun q => (holo x q j _ hy0).differentiableAt
  refine differentiableAt_pi.2 fun q => ?_
  show DifferentiableAt ℂ (fun y => lift x ((p1.chart j).symm y) q /
    lift x ((p1.chart j).symm y) ⟨q.1, p q.1⟩) _
  have hne : lift x ((p1.chart j).symm (p1.chart j x)) ⟨q.1, p q.1⟩ ≠ 0 := by
    rw [(p1.chart j).left_inv hj]
    exact hp q.1
  simp_rw [div_eq_mul_inv]
  exact (hd q).mul ((hd _).inv hne)

/- English proof (translation)
Generalize the expression as in `p () = i`. Use `fin_cases i`. Use `left`. Both sides reduce to the same expression. Use `right`.

Both sides reduce to the same expression.
-/
lemma p_cases (p : (k : Unit) → PBlk 2 k) : p () = 0 ∨ p () = 1 := by
  generalize p () = i
  fin_cases i
  · left; rfl
  · right; rfl

/- English proof (translation)
Establish `hD` using `diffAt x p hp j hj`. Proceed by induction on `x with`. Consider the case `infty => exact absurd ((lift_mem_J ∞).2 rfl) hx`. Consider the case `coe ζ`. Establish `hp0` using `hp ()`.

Rewrite `hp0` using `[lift_coe]`. Use `fin_cases j`. Break down `p_cases p with h | h` into its components or cases. Use `ker_eq_bot_of_coord hD ⟨(), 1⟩ id 1 (fun y => ?_) (hasDerivAt_id _) one_ne_zero` and prove the remaining obligations. Simplify using `[affCoord, lift_coe, h]`.

Both sides reduce to the same expression. Rewrite `hp0` using `[h]`. Establish `hζ : ζ ≠ 0` using `by simpa using hp0`. Use `ker_eq_bot_of_coord hD ⟨(), 0⟩ (fun w => w⁻¹) _ (fun y => ?_) (hasDerivAt_inv hζ) (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 hζ)))` and prove the remaining obligations. Simplify using `[affCoord, lift_coe, h]`.

Both sides reduce to the same expression. Establish `hζ : ζ ≠ 0` using `fun h0 => hj (by rw [h0])`. Break down `p_cases p with h | h` into its components or cases. Use `ker_eq_bot_of_coord hD ⟨(), 1⟩ (fun w => w⁻¹) _ (fun y => ?_) (hasDerivAt_inv (inv_ne_zero hζ)) (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 (inv_ne_zero hζ))))` and prove the remaining obligations. Simplify using `[affCoord, lift_coe, h]`.

Conclude with `finiteCoord_projLineChart1_symm y`. Use `ker_eq_bot_of_coord hD ⟨(), 0⟩ id 1 (fun y => ?_) (hasDerivAt_id _) one_ne_zero` and prove the remaining obligations. Simplify using `[affCoord, lift_coe, h]`. Conclude with `(congrArg (·⁻¹) (finiteCoord_projLineChart1_symm y)).trans (inv_inv _)`.
-/
theorem immersion (x : OnePoint ℂ) (hx : lift x x ∉ mcPts JJ) (p : (k : Unit) → PBlk 2 k)
    (hp : ∀ k, lift x x ⟨k, p k⟩ ≠ 0) (j : Fin p1.n) (hj : x ∈ (p1.chart j).source) :
    (fderiv ℂ (fun y => affCoord p (lift x ((p1.chart j).symm y))) (p1.chart j x)).ker = ⊥ := by
  have hD := diffAt x p hp j hj
  induction x with
  | infty => exact absurd ((lift_mem_J ∞).2 rfl) hx
  | coe ζ =>
    have hp0 := hp ()
    rw [lift_coe] at hp0
    fin_cases j
    · rcases p_cases p with h | h
      · refine ker_eq_bot_of_coord hD ⟨(), 1⟩ id 1 (fun y => ?_) (hasDerivAt_id _) one_ne_zero
        simp [affCoord, lift_coe, h]
        rfl
      · rw [h] at hp0
        have hζ : ζ ≠ 0 := by simpa using hp0
        refine ker_eq_bot_of_coord hD ⟨(), 0⟩ (fun w => w⁻¹) _ (fun y => ?_)
          (hasDerivAt_inv hζ) (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 hζ)))
        simp [affCoord, lift_coe, h]
        rfl
    · have hζ : ζ ≠ 0 := fun h0 => hj (by rw [h0])
      rcases p_cases p with h | h
      · refine ker_eq_bot_of_coord hD ⟨(), 1⟩ (fun w => w⁻¹) _ (fun y => ?_)
          (hasDerivAt_inv (inv_ne_zero hζ))
          (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 (inv_ne_zero hζ))))
        simp [affCoord, lift_coe, h]
        exact finiteCoord_projLineChart1_symm y
      · refine ker_eq_bot_of_coord hD ⟨(), 0⟩ id 1 (fun y => ?_) (hasDerivAt_id _) one_ne_zero
        simp [affCoord, lift_coe, h]
        exact (congrArg (·⁻¹) (finiteCoord_projLineChart1_symm y)).trans (inv_inv _)

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p n hp => simp [hp]`.
-/
lemma eval_aeval (v : (Σ k, PBlk 2 k) → Polynomial ℂ) (F : MvPolynomial (Σ k, PBlk 2 k) ℂ)
    (w : ℂ) : (aeval v F).eval w = eval (fun q => (v q).eval w) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

/- English proof (translation)
Rewrite using `[eval_aeval, show (fun q : Σ k, PBlk 2 k => ((![a, b] q.2 : Polynomial ℂ)).eval w) = vec (a.eval w) (b.eval w) from pt_ext rfl rfl]`.
-/
lemma eval_vec_poly (a b : Polynomial ℂ) (F : MvPolynomial (Σ k, PBlk 2 k) ℂ) (w : ℂ) :
    (aeval (fun q : Σ k, PBlk 2 k => ![a, b] q.2) F).eval w = eval (vec (a.eval w) (b.eval w)) F := by
  rw [eval_aeval, show (fun q : Σ k, PBlk 2 k => ((![a, b] q.2 : Polynomial ℂ)).eval w) =
    vec (a.eval w) (b.eval w) from pt_ext rfl rfl]

/- English proof (translation)
Use `set G := aeval (fun q : Σ k, PBlk 2 k => ![(Polynomial.X : Polynomial ℂ), 1] q.2) F with hGdef`. Establish `hG : ∀ w, G.eval w = eval (vec w 1) F` using `fun w => by`. Rewrite using `[hGdef, eval_vec_poly]`. Simplify using the standard rewrite rules. Establish `hne : G ≠ 0` using `fun h0 => hF 1 one_ne_zero (by rw [← hG, h0, Polynomial.eval_zero])`.

Take `⟨h, hfac, hnd⟩` from `G.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hne 0`. Establish `hev : ∀ w, eval (vec w 1) F = w ^ G.rootMultiplicity 0 * h.eval w` using `fun w => by`. Rewrite using `[← hG]`. Use `conv_lhs => rw [hfac]`. Simplify using the standard rewrite rules.

Use `⟨h, G.rootMultiplicity 0, hev, fun w h0 => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hw : w = 0`. Substitute `hw` using the available equality. Conclude with `hnd (Polynomial.dvd_iff_isRoot.2 h0)`. Conclude with `hF w hw (by rw [hev, h0, mul_zero])`.
-/
lemma factor (F : MvPolynomial (Σ k, PBlk 2 k) ℂ) (hF : ∀ w : ℂ, w ≠ 0 → eval (vec w 1) F ≠ 0) :
    ∃ (h : Polynomial ℂ) (m : ℕ), (∀ w, eval (vec w 1) F = w ^ m * h.eval w) ∧
      ∀ w, h.eval w ≠ 0 := by
  set G := aeval (fun q : Σ k, PBlk 2 k => ![(Polynomial.X : Polynomial ℂ), 1] q.2) F with hGdef
  have hG : ∀ w, G.eval w = eval (vec w 1) F := fun w => by
    rw [hGdef, eval_vec_poly]; simp
  have hne : G ≠ 0 := fun h0 => hF 1 one_ne_zero (by rw [← hG, h0, Polynomial.eval_zero])
  obtain ⟨h, hfac, hnd⟩ := G.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hne 0
  have hev : ∀ w, eval (vec w 1) F = w ^ G.rootMultiplicity 0 * h.eval w := fun w => by
    rw [← hG]
    conv_lhs => rw [hfac]
    simp
  refine ⟨h, G.rootMultiplicity 0, hev, fun w h0 => ?_⟩
  by_cases hw : w = 0
  · subst hw
    exact hnd (Polynomial.dvd_iff_isRoot.2 h0)
  · exact hF w hw (by rw [hev, h0, mul_zero])

/- English proof (translation)
Introduce `j w hw` and use `(P.differentiable.analyticAt _).comp (hc j w hw)`.
-/
lemma holoOn_poly {U : Set (OnePoint ℂ)} {c : OnePoint ℂ → ℂ} (hc : p1.HoloOn U c)
    (P : Polynomial ℂ) : p1.HoloOn U (fun y => P.eval (c y)) :=
  fun j w hw => (P.differentiable.analyticAt _).comp (hc j w hw)

/- English proof (translation)
Use `set F := map (Int.castRingHom ℂ) f with hFdef`. Establish `nz : ∀ a b : ℂ, a ≠ 0 → eval (vec a b) F ≠ 0` using `fun a b ha h0 => ha ((mem_J_iff _).1 (hf _ (mem_bot _ (vec_ne a b ha)) h0)).2`. Take `⟨h, m, hev, hh⟩` from `factor F fun w hw => nz w 1 hw`. Use `⟨1, ![m], ![{∞}], ?_⟩` and prove the remaining obligations. Introduce `x`.

Proceed by induction on `x with`. Consider the case `infty`. Use `⟨projectiveLineChartAtInfinity, projLine_isCompatibleChart 1, OnePoint.infty_ne_coe 0, ?_, fun _ => Option.some 0, ?_, ?_, fun y => h.eval (crd1 y), holoOn_poly holomorphicOn_infiniteCoord h, fun y _ => hh _, ?_⟩` and prove the remaining obligations. Use `show projectiveLineChartAtInfinity.source ⊆ fsPot.U ∞`. Rewrite using `[fsPot_U_infty]`.

Introduce `k k' i _ _`. Conclude with `Subsingleton.elim _ _`. Introduce `k`. Take `rfl : k = 0` from `Subsingleton.elim _ _`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy1, hy2⟩`. Simplify using `only [Matrix.cons_val_fin_one, Set.mem_singleton_iff] at hy1`. Substitute `hy1` using the available equality. Conclude with `⟨hy2, 0, rfl, rfl⟩`.

Introduce and unpack `⟨hy, i, _, hi⟩`. Use `⟨?_, hy⟩` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_fin_one, Set.mem_singleton_iff]`. Proceed by induction on `y with`. Consider the case `infty => rfl`.

Consider the case `coe ζ`. Establish `hζ : ζ ≠ 0` using `fun e => hy (by rw [e])`. Conclude with `absurd hi (by simp [projLineChart1_apply, hζ])`. Introduce `y _`. Simplify using `only [Fin.prod_univ_one, Matrix.cons_val_fin_one, projLineChart1_apply]`.

Rewrite using `[lift_infty, hev, mul_comm]`. Consider the case `coe z`. Use `⟨projectiveLineChartAtZero, projLine_isCompatibleChart 0, ⟨z, rfl⟩, ?_, fun _ => none, ?_, ?_, fun y => eval (vec 1 (crd0 y)) F, ?_, fun y _ => nz 1 _ one_ne_zero, ?_⟩` and prove the remaining obligations. Use `show projectiveLineChartAtZero.source ⊆ fsPot.U (z : OnePoint ℂ)`. Rewrite using `[fsPot_U_coe]`.

Introduce `k k' i h`. Consider the cases of `h`. Introduce `k`. Take `rfl : k = 0` from `Subsingleton.elim _ _`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy1, hy2⟩`. Simplify using `only [Matrix.cons_val_fin_one, Set.mem_singleton_iff] at hy1`. Substitute `hy1` using the available equality. Conclude with `absurd hy2 OnePoint.infty_notMem_range_coe`.

Introduce and unpack `⟨_, i, h, _⟩`. Consider the cases of `h`. Establish `e : (fun y => eval (vec 1 (crd0 y)) F) = fun y => (aeval (fun q : Σ k, PBlk 2 k => ![(1 : Polynomial ℂ), Polynomial.X] q.2) F).eval (crd0 y)`. Use function extensionality and compare the values at `y`. Rewrite using `[eval_vec_poly]`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `holoOn_poly holomorphicOn_finiteCoord _`. Introduce `y _`. Simplify using `only [Fin.prod_univ_one, mul_one]`.

Rewrite using `[lift_coe]`.
-/
theorem snc (f : MRing (PBlk 2)) (hf : ∀ z ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))),
      eval z (map (Int.castRingHom ℂ) f) = 0 → z ∈ mcPts JJ) :
    ∃ (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set (OnePoint ℂ)),
      IsSNC p1 (⟨fsPot.U, fsPot.isOpen_U, fsPot.mem_U, fun _ _ => 0⟩ : LocPot (OnePoint ℂ))
        (fun x y => eval (lift x y) (map (Int.castRingHom ℂ) f)) m W := by
  set F := map (Int.castRingHom ℂ) f with hFdef
  have nz : ∀ a b : ℂ, a ≠ 0 → eval (vec a b) F ≠ 0 := fun a b ha h0 =>
    ha ((mem_J_iff _).1 (hf _ (mem_bot _ (vec_ne a b ha)) h0)).2
  obtain ⟨h, m, hev, hh⟩ := factor F fun w hw => nz w 1 hw
  refine ⟨1, ![m], ![{∞}], ?_⟩
  intro x
  induction x with
  | infty =>
    refine ⟨projectiveLineChartAtInfinity, projLine_isCompatibleChart 1, OnePoint.infty_ne_coe 0, ?_, fun _ => Option.some 0, ?_, ?_,
      fun y => h.eval (crd1 y), holoOn_poly holomorphicOn_infiniteCoord h, fun y _ => hh _, ?_⟩
    · show projectiveLineChartAtInfinity.source ⊆ fsPot.U ∞
      rw [fsPot_U_infty]
    · intro k k' i _ _; exact Subsingleton.elim _ _
    · intro k
      obtain rfl : k = 0 := Subsingleton.elim _ _
      ext y
      constructor
      · rintro ⟨hy1, hy2⟩
        simp only [Matrix.cons_val_fin_one, Set.mem_singleton_iff] at hy1
        subst hy1
        exact ⟨hy2, 0, rfl, rfl⟩
      · rintro ⟨hy, i, _, hi⟩
        refine ⟨?_, hy⟩
        simp only [Matrix.cons_val_fin_one, Set.mem_singleton_iff]
        induction y with
        | infty => rfl
        | coe ζ =>
          have hζ : ζ ≠ 0 := fun e => hy (by rw [e])
          exact absurd hi (by simp [projLineChart1_apply, hζ])
    · intro y _
      simp only [Fin.prod_univ_one, Matrix.cons_val_fin_one, projLineChart1_apply]
      rw [lift_infty, hev, mul_comm]
  | coe z =>
    refine ⟨projectiveLineChartAtZero, projLine_isCompatibleChart 0, ⟨z, rfl⟩, ?_, fun _ => none, ?_, ?_,
      fun y => eval (vec 1 (crd0 y)) F, ?_, fun y _ => nz 1 _ one_ne_zero, ?_⟩
    · show projectiveLineChartAtZero.source ⊆ fsPot.U (z : OnePoint ℂ)
      rw [fsPot_U_coe]
    · intro k k' i h; cases h
    · intro k
      obtain rfl : k = 0 := Subsingleton.elim _ _
      ext y
      constructor
      · rintro ⟨hy1, hy2⟩
        simp only [Matrix.cons_val_fin_one, Set.mem_singleton_iff] at hy1
        subst hy1
        exact absurd hy2 OnePoint.infty_notMem_range_coe
      · rintro ⟨_, i, h, _⟩
        cases h
    · have e : (fun y => eval (vec 1 (crd0 y)) F) =
          fun y => (aeval (fun q : Σ k, PBlk 2 k => ![(1 : Polynomial ℂ), Polynomial.X] q.2) F).eval (crd0 y) := by
        funext y; rw [eval_vec_poly]; simp
      rw [e]
      exact holoOn_poly holomorphicOn_finiteCoord _
    · intro y _
      simp only [Fin.prod_univ_one, mul_one]
      rw [lift_coe]

/- English proof (translation)
Use `measure_mono_null ?_ (measure_singleton (0 : Fin 1 → ℂ))` and prove the remaining obligations. Introduce and unpack `y ⟨_, hy⟩`. Establish `hy' : (p1.chart j).symm y = ∞` using `(lift_mem_J _).1 hy`. Use `fin_cases j`. Conclude with `absurd hy' (OnePoint.coe_ne_infty _)`.

Establish `h1` using `infiniteCoord_projLineChart1_symm y`. Rewrite `h1` using `[show projectiveLineChartAtInfinity.symm y = ∞ from hy', infiniteCoord_infty]`. Conclude with `Set.mem_singleton_iff.2 (funext fun i => by rw [Subsingleton.elim i 0]; exact h1.symm)`.
-/
theorem null (j : Fin p1.n) : volume ((p1.chart j).target ∩
    (p1.chart j).symm ⁻¹' {x | lift x x ∈ mcPts JJ}) = 0 := by
  refine measure_mono_null ?_ (measure_singleton (0 : Fin 1 → ℂ))
  rintro y ⟨_, hy⟩
  have hy' : (p1.chart j).symm y = ∞ := (lift_mem_J _).1 hy
  fin_cases j
  · exact absurd hy' (OnePoint.coe_ne_infty _)
  · have h1 := infiniteCoord_projLineChart1_symm y
    rw [show projectiveLineChartAtInfinity.symm y = ∞ from hy', infiniteCoord_infty] at h1
    exact Set.mem_singleton_iff.2 (funext fun i => by rw [Subsingleton.elim i 0]; exact h1.symm)

/- English proof (translation)
Use `⟨{Xc 2 0}, ?_, rfl⟩` and prove the remaining obligations. Introduce and unpack `f rfl`. Use `⟨fun _ => 1, fun m hm k => ?_⟩` and prove the remaining obligations. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality.

Consider the cases of `k`. Simplify using `[Finsupp.single_apply]`.
-/
theorem homog : IsMultiHomogIdeal JJ := by
  refine ⟨{Xc 2 0}, ?_, rfl⟩
  rintro f rfl
  refine ⟨fun _ => 1, fun m hm k => ?_⟩
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  cases k
  simp [Finsupp.single_apply]

/- English proof (translation)
Introduce `h` and use `X_ne_zero _ (Ideal.mem_bot.mp (h (Ideal.subset_span (Set.mem_singleton _))))`.
-/
theorem nondeg : ¬ JJ ≤ ⊥ := fun h =>
  X_ne_zero _ (Ideal.mem_bot.mp (h (Ideal.subset_span (Set.mem_singleton _))))

def res : AnLogRes (⊥ : Ideal (MRing (PBlk 2))) JJ 1 where
  homog := homog
  nondeg := nondeg
  X := OnePoint ℂ
  A := p1
  U := fsPot.U
  isOpen_U := fsPot.isOpen_U
  mem_U := fsPot.mem_U
  lift := lift
  holo := holo
  mem x y _ := lift_mem_bot x y
  compat x x' y hy := compat x x' y hy
  surj := surj
  inj := inj
  immersion x hx p hp j hj := immersion x hx p hp j hj
  snc f _ _ _ hf := snc f hf
  null := null

end ProjectiveLineResolution

end ReciprocityTheory.ChartRestriction.G.Geo

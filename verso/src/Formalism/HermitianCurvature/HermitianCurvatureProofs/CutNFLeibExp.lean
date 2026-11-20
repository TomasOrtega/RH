import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree

namespace Formalism.FourierDecayAlt.P.CutBP.LeibExp

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Gc (z z' : Fin (2 * r + k + 1) → ℂ) : B.Mat k r → ℂ := fun g => ((Gf k r z z' g : ℝ) : ℂ)

/- English proof (translation)
Apply `ListSumSplittings.polyClass_of_isPolyDeg` to reduce the goal to its premises. Take `⟨q, hq, h⟩` from `Formalism.FourierDecayAlt.P.gram_function_polynomial k r z z'`. Conclude with `⟨q, hq, h⟩`.
-/
theorem gc_poly (z z' : Fin (2 * r + k + 1) → ℂ) : ListSumSplittings.PolyClass (2 * r + 2) (Gc (k := k) (r := r) z z') := by
  apply ListSumSplittings.polyClass_of_isPolyDeg
  obtain ⟨q, hq, h⟩ := Formalism.FourierDecayAlt.P.gram_function_polynomial k r z z'
  exact ⟨q, hq, h⟩

abbrev Tm (k r : ℕ) := ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)

def coefT (z z' : Fin (2 * r + k + 1) → ℂ) (Ψ : ℕ → ℝ → ℝ) (t : Tm k r) (y : B.Mat k r) : ℂ :=
  ((Ψ t.1 (Gf k r z z' y) : ℝ) : ℂ) * t.2.1 y * ((Gf k r z z' y : ℝ) : ℂ)⁻¹ ^ t.2.2.1

def step (z z' : Fin (2 * r + k + 1) → ℂ) (X : B.Mat k r) (t : Tm k r) : List (Tm k r) :=
  [(t.1 + 1, fun y => Formalism.REAL.RdV X (Gc z z') y * t.2.1 y, t.2.2.1 + 1, t.2.2.2),
   (t.1, Formalism.REAL.RdV X t.2.1, t.2.2.1, t.2.2.2),
   (t.1, fun y => (-(t.2.2.1 : ℂ)) * (Formalism.REAL.RdV X (Gc z z') y * t.2.1 y), t.2.2.1 + 1, t.2.2.2),
   (t.1, t.2.1, t.2.2.1, X :: t.2.2.2)]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih => simp [ih]`.
-/
theorem sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (f : α → List β) (g : β → M) :
    ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

/- English proof (translation)
Take `⟨q, P, j, v⟩` from `t`. Simplify using `only at hP hv ⊢`. Establish `hPC : B.CkOn ⊤ (B.GV k r) P` using `by rcases hP with h | h; exact h.1; exact h`. Use `set c : ℝ → B.Mat k r := fun s => x * NormedSpace.exp ((s : ℂ) • X) with hcdef`. Establish `hc0 : c 0 = x` using `B5.curve_zero x X`.

Establish `hGc : HasDerivAt (fun s => Gc z z' (c s)) (Formalism.REAL.RdV X (Gc z z') x) 0` using `JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top (gc_poly z z').1) hxG hxG hX`. Establish `hdiff : DifferentiableAt ℝ (fun s => Gf k r z z' (c s)) 0`. Establish `h1 : Differentiable ℝ (fun g : B.Mat k r => Gf k r z z' g)` using `(Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z').differentiable (by simp)`. Establish `h2 : Differentiable ℝ c` using `(B5.curve_contDiff x X).differentiable (by simp)`. Conclude with `(h1 (c 0)).comp (0 : ℝ) (h2 0)`.

Use `set dG : ℝ := deriv (fun s => Gf k r z z' (c s)) 0 with hdG`. Establish `hGr : HasDerivAt (fun s => Gf k r z z' (c s)) dG 0` using `hdiff.hasDerivAt`. Establish `hD : Formalism.REAL.RdV X (Gc z z') x = (dG : ℂ)`. Establish `h2` using `hGr.ofReal_comp`. Conclude with `hGc.unique (by simpa [Gc] using h2)`.

Establish `hGx : Gf k r z z' (c 0) = Gf k r z z' x` using `by rw [hc0]`. Establish `hne : Gf k r z z' (c 0) ≠ 0` using `by rw [hGx]; exact hxp.ne'`. Establish `hΨq : HasDerivAt (Ψ q) (Ψ (q + 1) (Gf k r z z' x) / Gf k r z z' x) (Gf k r z z' (c 0))`. Rewrite using `[hGx]`. Conclude with `hΨ q _ hxp`.

Establish `hψ` using `(hΨq.comp (0 : ℝ) hGr).ofReal_comp`. Establish `hPd : HasDerivAt (fun s => P (c s)) (Formalism.REAL.RdV X P x) 0` using `JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top hPC) hxG hxG hX`. Establish `hI` using `((hGr.inv hne).pow j).ofReal_comp`. Establish `hR : HasDerivAt (fun s => B.Rw v F (c s)) (Formalism.REAL.RdV X (B.Rw v F) x) 0` using `JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top (JFxI.ckOn_Rw_top' hF v hv)) hxG hxG hX`. Establish `hA` using `((hψ.mul hPd).mul hI).smul hR`.

Use `(hA.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_` and prove the remaining obligations. Simplify using `only [coefT, Function.comp_apply, Pi.pow_apply, Pi.inv_apply, Complex.ofReal_pow, Complex.ofReal_inv]`. Both sides reduce to the same expression. Simplify using `only [step, coefT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hc0, Function.comp_apply, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, hD]`. Establish `hRw : B.Rw (X :: v) F x = Formalism.REAL.RdV X (B.Rw v F) x` using `rfl`.

Rewrite using `[hRw]`. Break down `j with _ | j` into its components or cases. Move the coercions through the operations in `module`. Simplify using `only [Nat.add_sub_cancel]`. Use `push_cast`.

Use `module`.
-/
theorem term_deriv (z z' : Fin (2 * r + k + 1) → ℂ) (Ψ : ℕ → ℝ → ℝ) (hΨ : ThChain Ψ) (t : Tm k r)
    (hP : ListSumSplittings.PolyClass 0 t.2.1 ∨ B.CkOn ⊤ (B.GV k r) t.2.1)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : B.CkOn ⊤ (B.GV k r) F) (hv : ∀ Y ∈ t.2.2.2, B.inLie k r Y)
    {X x : B.Mat k r} (hX : B.inLie k r X) (hxG : x ∈ B.GV k r) (hxp : 0 < Gf k r z z' x) :
    HasDerivAt (fun s : ℝ => coefT z z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
        B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X)))
      (((step z z' X t).map fun t' => coefT z z' Ψ t' x • B.Rw t'.2.2.2 F x).sum) 0 := by
  obtain ⟨q, P, j, v⟩ := t
  simp only at hP hv ⊢
  have hPC : B.CkOn ⊤ (B.GV k r) P := by rcases hP with h | h; exact h.1; exact h
  set c : ℝ → B.Mat k r := fun s => x * NormedSpace.exp ((s : ℂ) • X) with hcdef
  have hc0 : c 0 = x := B5.curve_zero x X
  have hGc : HasDerivAt (fun s => Gc z z' (c s)) (Formalism.REAL.RdV X (Gc z z') x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top (gc_poly z z').1) hxG hxG hX
  have hdiff : DifferentiableAt ℝ (fun s => Gf k r z z' (c s)) 0 := by
    have h1 : Differentiable ℝ (fun g : B.Mat k r => Gf k r z z' g) :=
      (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z').differentiable (by simp)
    have h2 : Differentiable ℝ c := (B5.curve_contDiff x X).differentiable (by simp)
    exact (h1 (c 0)).comp (0 : ℝ) (h2 0)
  set dG : ℝ := deriv (fun s => Gf k r z z' (c s)) 0 with hdG
  have hGr : HasDerivAt (fun s => Gf k r z z' (c s)) dG 0 := hdiff.hasDerivAt
  have hD : Formalism.REAL.RdV X (Gc z z') x = (dG : ℂ) := by
    have h2 := hGr.ofReal_comp
    exact hGc.unique (by simpa [Gc] using h2)
  have hGx : Gf k r z z' (c 0) = Gf k r z z' x := by rw [hc0]
  have hne : Gf k r z z' (c 0) ≠ 0 := by rw [hGx]; exact hxp.ne'
  have hΨq : HasDerivAt (Ψ q) (Ψ (q + 1) (Gf k r z z' x) / Gf k r z z' x) (Gf k r z z' (c 0)) := by
    rw [hGx]; exact hΨ q _ hxp
  have hψ := (hΨq.comp (0 : ℝ) hGr).ofReal_comp
  have hPd : HasDerivAt (fun s => P (c s)) (Formalism.REAL.RdV X P x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top hPC) hxG hxG hX
  have hI := ((hGr.inv hne).pow j).ofReal_comp
  have hR : HasDerivAt (fun s => B.Rw v F (c s)) (Formalism.REAL.RdV X (B.Rw v F) x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top (JFxI.ckOn_Rw_top' hF v hv)) hxG hxG hX
  have hA := ((hψ.mul hPd).mul hI).smul hR
  refine (hA.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp only [coefT, Function.comp_apply, Pi.pow_apply, Pi.inv_apply, Complex.ofReal_pow, Complex.ofReal_inv]
    rfl
  simp only [step, coefT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hc0,
    Function.comp_apply, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, hD]
  have hRw : B.Rw (X :: v) F x = Formalism.REAL.RdV X (B.Rw v F) x := rfl
  rw [hRw]
  rcases j with _ | j
  · push_cast
    module
  · simp only [Nat.add_sub_cancel]
    push_cast
    module

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil`. Use `⟨[(0, fun _ => 1, 0, [])], ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Simplify using `only [List.mem_singleton] at ht`.

Substitute `ht` using the available equality. Use `⟨le_rfl, ?_, List.Sublist.refl _⟩` and prove the remaining obligations. Rewrite using `[List.length_nil, mul_zero]`. Conclude with `ListSumSplittings.polyClass_const 1`. Introduce `Ψ _ F _ x _`.

Simplify using `[coefT, B.Rw]`. Consider the case `cons X w ih`. Establish `hwL : ∀ Y ∈ w, B.inLie k r Y` using `fun Y hY => hw Y (List.mem_cons_of_mem _ hY)`. Establish `hXL : B.inLie k r X` using `hw X List.mem_cons_self`. Take `⟨terms, hprop, hid⟩` from `ih hwL`.

Use `⟨terms.flatMap (step Bs.z Bs.z' X), ?_, ?_⟩` and prove the remaining obligations. Introduce `t' ht'`. Rewrite `ht'` using `[List.mem_flatMap]`. Take `⟨t, ht, ht'⟩` from `ht'`. Take `⟨h1, h2, h3⟩` from `hprop t ht`.

Establish `hGp` using `gc_poly (k := k) (r := r) Bs.z Bs.z'`. Establish `hdeg : (2 * r + 2) * w.length ≤ (2 * r + 2) * (X :: w).length`. Simplify using `only [List.length_cons]`. Conclude with `Nat.mul_le_mul_left _ (Nat.le_succ _)`. Establish `hdeg2 : (2 * r + 2) + (2 * r + 2) * w.length = (2 * r + 2) * (X :: w).length`.

Simplify using `only [List.length_cons]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [step, List.mem_cons, List.not_mem_nil, or_false] at ht'`. Break down `ht' with rfl | rfl | rfl | rfl` into its components or cases. Use `⟨by simp only [List.length_cons]; omega, ?_, h3.cons X⟩` and prove the remaining obligations.

Rewrite using `[← hdeg2]`. Conclude with `ListSumSplittings.polyClass_mul (ListSumSplittings.polyClass_op hGp false hXL) h2`. Conclude with `⟨by simp only [List.length_cons]; omega, ListSumSplittings.polyClass_mono hdeg (ListSumSplittings.polyClass_op h2 false hXL), h3.cons X⟩`. Use `⟨by simp only [List.length_cons]; omega, ?_, h3.cons X⟩` and prove the remaining obligations. Rewrite using `[← hdeg2]`.

Conclude with `ListSumSplittings.polyClass_cmul _ (ListSumSplittings.polyClass_mul (ListSumSplittings.polyClass_op hGp false hXL) h2)`. Conclude with `⟨by simp only [List.length_cons]; omega, ListSumSplittings.polyClass_mono hdeg h2, h3.cons_cons X⟩`. Introduce `Ψ hΨ F hF x hx`. Establish `hVo : IsOpen {g : B.Mat k r | 0 < Gf k r Bs.z Bs.z' g}` using `isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous`. Establish `hloc` using `PositiveOrbitOpen.rdV_local (f₁ := B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y)) (f₂ := fun y => (terms.map fun t => coefT Bs.z Bs.z' Ψ t y • B.Rw t.2.2.2 F y).sum) hVo (fun y hy hyG => hid Ψ hΨ F hF y ⟨hyG, hy, fun l hl => absurd hl (Finset.notMem_empty l)⟩) hXL …`.

Express the relevant statement in the definitionally equal form `Formalism.REAL.RdV X (B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y)) x = _`. Rewrite using `[hloc]`. Establish `hd` using `JFxI.hasDerivAt_list_sum terms (fun t s => coefT Bs.z Bs.z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) • B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X))) (fun t => ((step Bs.z Bs.z' X t).map fun t' => coefT Bs.z Bs.z' Ψ t' x • B.Rw t'.2.2.2 F x).sum) (t := 0) (fun t ht => term_de …`. Express the relevant statement in the definitionally equal form `deriv (fun s : ℝ => (terms.map fun t => coefT Bs.z Bs.z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) • B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X))).sum) 0 = _`. Rewrite using `[hd.deriv, sum_flatMap]`.
-/
theorem exp_main (Bs : B.RealPlaceData k r Wp Wq) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) :
    ∃ terms : List (Tm k r),
      (∀ t ∈ terms, t.1 ≤ w.length ∧ ListSumSplittings.PolyClass ((2 * r + 2) * w.length) t.2.1 ∧ t.2.2.2.Sublist w) ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            (terms.map fun t => coefT Bs.z Bs.z' Ψ t x • B.Rw t.2.2.2 F x).sum := by
  induction w with
  | nil =>
    refine ⟨[(0, fun _ => 1, 0, [])], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      refine ⟨le_rfl, ?_, List.Sublist.refl _⟩
      rw [List.length_nil, mul_zero]
      exact ListSumSplittings.polyClass_const 1
    · intro Ψ _ F _ x _
      simp [coefT, B.Rw]
  | cons X w ih =>
    have hwL : ∀ Y ∈ w, B.inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hXL : B.inLie k r X := hw X List.mem_cons_self
    obtain ⟨terms, hprop, hid⟩ := ih hwL
    refine ⟨terms.flatMap (step Bs.z Bs.z' X), ?_, ?_⟩
    · intro t' ht'
      rw [List.mem_flatMap] at ht'
      obtain ⟨t, ht, ht'⟩ := ht'
      obtain ⟨h1, h2, h3⟩ := hprop t ht
      have hGp := gc_poly (k := k) (r := r) Bs.z Bs.z'
      have hdeg : (2 * r + 2) * w.length ≤ (2 * r + 2) * (X :: w).length := by
        simp only [List.length_cons]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
      have hdeg2 : (2 * r + 2) + (2 * r + 2) * w.length = (2 * r + 2) * (X :: w).length := by
        simp only [List.length_cons]; ring
      simp only [step, List.mem_cons, List.not_mem_nil, or_false] at ht'
      rcases ht' with rfl | rfl | rfl | rfl
      · refine ⟨by simp only [List.length_cons]; omega, ?_, h3.cons X⟩
        rw [← hdeg2]
        exact ListSumSplittings.polyClass_mul (ListSumSplittings.polyClass_op hGp false hXL) h2
      · exact ⟨by simp only [List.length_cons]; omega,
          ListSumSplittings.polyClass_mono hdeg (ListSumSplittings.polyClass_op h2 false hXL), h3.cons X⟩
      · refine ⟨by simp only [List.length_cons]; omega, ?_, h3.cons X⟩
        rw [← hdeg2]
        exact ListSumSplittings.polyClass_cmul _ (ListSumSplittings.polyClass_mul (ListSumSplittings.polyClass_op hGp false hXL) h2)
      · exact ⟨by simp only [List.length_cons]; omega, ListSumSplittings.polyClass_mono hdeg h2, h3.cons_cons X⟩
    · intro Ψ hΨ F hF x hx
      have hVo : IsOpen {g : B.Mat k r | 0 < Gf k r Bs.z Bs.z' g} :=
        isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
      have hloc := PositiveOrbitOpen.rdV_local (f₁ := B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y))
        (f₂ := fun y => (terms.map fun t => coefT Bs.z Bs.z' Ψ t y • B.Rw t.2.2.2 F y).sum) hVo
        (fun y hy hyG => hid Ψ hΨ F hF y ⟨hyG, hy, fun l hl => absurd hl (Finset.notMem_empty l)⟩) hXL x hx.2.1 hx.1
      change Formalism.REAL.RdV X (B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y)) x = _
      rw [hloc]
      have hd := JFxI.hasDerivAt_list_sum terms
        (fun t s => coefT Bs.z Bs.z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
          B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X)))
        (fun t => ((step Bs.z Bs.z' X t).map fun t' => coefT Bs.z Bs.z' Ψ t' x • B.Rw t'.2.2.2 F x).sum)
        (t := 0) (fun t ht => term_deriv Bs.z Bs.z' Ψ hΨ t (Or.inr (hprop t ht).2.1.1) F hF
          (fun Y hY => hwL Y ((hprop t ht).2.2.subset hY)) hXL hx.1 hx.2.1)
      change deriv (fun s : ℝ => (terms.map fun t => coefT Bs.z Bs.z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
          B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X))).sum) 0 = _
      rw [hd.deriv, sum_flatMap]

end

end Formalism.FourierDecayAlt.P.CutBP.LeibExp

namespace Formalism.FourierDecayAlt.P.CutBP

/- English proof (translation)
Unfold `NFLeibExp`. Introduce `k r Wp Wq _ _ _ _ Bs w hw`. Conclude with `LeibExp.exp_main Bs w hw`.
-/
theorem leibniz_expansion_holds : NFLeibExp := by
  unfold NFLeibExp
  intro k r Wp Wq _ _ _ _ Bs w hw
  exact LeibExp.exp_main Bs w hw

end Formalism.FourierDecayAlt.P.CutBP

import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainBSt

noncomputable section

open Matrix Metric

namespace PositivityTheory.Rg.Sw.WR.K.GB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Use `letI : NormedAddCommGroup (Mc n →L[ℂ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup`. Use `letI : NormedSpace ℂ (Mc n →L[ℂ] ℂ) := ContinuousLinearMap.toNormedSpace`. Establish `hle : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)`. Rewrite using `[← WithTop.coe_one, ← WithTop.coe_add, top_add]`. Establish `h1 : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => fderiv ℂ F b) U` using `hF.fderiv_of_isOpen (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hU hle`.

Establish `h2` using `(ContinuousLinearMap.apply ℂ ℂ (Matrix.single i j (1 : ℂ))).contDiff.comp_contDiffOn h1`. Conclude with `h2`.
-/
theorem contDiffOn_cpart {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U)
    (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (i j : Fin n) : ContDiffOn ℂ (⊤ : ℕ∞) (cpart i j F) U := by
  letI : NormedAddCommGroup (Mc n →L[ℂ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (Mc n →L[ℂ] ℂ) := ContinuousLinearMap.toNormedSpace
  have hle : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]
  have h1 : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => fderiv ℂ F b) U :=
    hF.fderiv_of_isOpen (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hU hle
  have h2 := (ContinuousLinearMap.apply ℂ ℂ (Matrix.single i j (1 : ℂ))).contDiff.comp_contDiffOn h1
  exact h2

/- English proof (translation)
The claim follows from `| [] => hF | ij :: L => contDiffOn_cpart hU (contDiffOn_word hU hF L) ij.1 ij.2`.
-/
theorem contDiffOn_word {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U)
    (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) : ∀ L : List (Fin n × Fin n), ContDiffOn ℂ (⊤ : ℕ∞) (word L F) U
  | [] => hF
  | ij :: L => contDiffOn_cpart hU (contDiffOn_word hU hF L) ij.1 ij.2

/- English proof (translation)
Introduce `i j`. Simplify using `only [sub_self, norm_zero]`. Conclude with `(hr i j).le`.
-/
theorem mem_pdisc_self (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) : b ∈ pdisc b r := by
  intro i j
  simp only [sub_self, norm_zero]
  exact (hr i j).le

/- English proof (translation)
Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_left]`. Distinguish the cases in `h : i = a ∧ j = c`. Take `⟨rfl, rfl⟩` from `h`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.single_apply_of_ne _ _ _ _ _ h, if_neg h, mul_zero]`.
-/
theorem shift_apply (b : Mc n) (w : ℂ) (i j a c : Fin n) :
    (b + w • Matrix.single i j (1 : ℂ)) a c - b a c = if i = a ∧ j = c then w else 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_left]
  by_cases h : i = a ∧ j = c
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ h, if_neg h, mul_zero]

/- English proof (translation)
Introduce `a c`. Rewrite using `[shift_apply]`. Use `split_ifs with h`. Take `⟨rfl, rfl⟩` from `h`. Conclude with `hw`.

Simplify using `using (hr a c).le`.
-/
theorem shift_mem (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) (i j : Fin n) {w : ℂ}
    (hw : ‖w‖ ≤ r i j) : b + w • Matrix.single i j (1 : ℂ) ∈ pdisc b r := by
  intro a c
  rw [shift_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact hw
  · simpa using (hr a c).le

/- English proof (translation)
Introduce `x hx a c`. Establish `h1` using `hx a c`. Establish `h2 : ‖x a c - b a c‖ ≤ ‖x a c - (b + w • Matrix.single i j (1 : ℂ)) a c‖ + ‖(b + w • Matrix.single i j (1 : ℂ)) a c - b a c‖` using `norm_sub_le_norm_sub_add_norm_sub _ _ _`. Rewrite `h2` using `[shift_apply]`. Establish `hlK' : l / K ≤ 1` using `by rw [div_le_one hK]; linarith`.

Use `split_ifs at h2 with h`. Take `⟨rfl, rfl⟩` from `h`. Rewrite `h2` using `[hw]`. Establish `: r i j * (l / K) + r i j / K = r i j`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[← hlK]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [norm_zero, add_zero] at h2`. Use `mul_le_of_le_one_right (hr a c).le hlK'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem shift_sub (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) (i j : Fin n) {w : ℂ}
    {K l : ℝ} (hK : 0 < K) (hl : 0 ≤ l) (hlK : l + 1 = K) (hw : ‖w‖ = r i j / K) :
    pdisc (b + w • Matrix.single i j (1 : ℂ)) (fun a c => r a c * (l / K)) ⊆ pdisc b r := by
  intro x hx a c
  have h1 := hx a c
  have h2 : ‖x a c - b a c‖ ≤ ‖x a c - (b + w • Matrix.single i j (1 : ℂ)) a c‖ +
      ‖(b + w • Matrix.single i j (1 : ℂ)) a c - b a c‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [shift_apply] at h2
  have hlK' : l / K ≤ 1 := by rw [div_le_one hK]; linarith
  split_ifs at h2 with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [hw] at h2
    have : r i j * (l / K) + r i j / K = r i j := by
      field_simp
      rw [← hlK]
    linarith
  · simp only [norm_zero, add_zero] at h2
    have := mul_le_of_le_one_right (hr a c).le hlK'
    linarith

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `b r hr _ hM`. Simplify using `only [word, List.foldr_nil, List.map_nil, List.prod_nil, one_mul]`.

Conclude with `hM b (mem_pdisc_self b hr)`. Consider the case `cons ij L ih`. Introduce `b r hr hsub hM`. Use `set K : ℝ := (L.length : ℝ) + 1 with hKdef`. Establish `hK : 0 < K` using `by positivity`.

Use `set δ : ℝ := r ij.1 ij.2 / K with hδdef`. Establish `hδ : 0 < δ` using `div_pos (hr _ _) hK`. Establish `hδr : δ ≤ r ij.1 ij.2` using `div_le_self (hr _ _).le (by simp [hKdef])`. Use `set E : Mc n := Matrix.single ij.1 ij.2 (1 : ℂ) with hE`. Use `set G : Mc n → ℂ := word L F with hG`.

Establish `hGd : ContDiffOn ℂ (⊤ : ℕ∞) G U` using `contDiffOn_word hU hF L`. Use `set f : ℂ → ℂ := fun w => G (b + w • E) with hf`. Establish `hφ : ∀ w : ℂ, HasDerivAt (fun w : ℂ => b + w • E) E w`. Introduce `w`. Establish `h` using `((hasDerivAt_id w).smul_const E).const_add b`.

Rewrite `h` using `[one_smul]`. Conclude with `h`. Establish `hin : ∀ w : ℂ, ‖w‖ ≤ δ → b + w • E ∈ U` using `fun w hw => hsub (shift_mem b hr ij.1 ij.2 (hw.trans hδr))`. Establish `hdiffG : ∀ x ∈ U, DifferentiableAt ℂ G x` using `fun x hx => ((hGd.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))`. Establish `hfd : DifferentiableOn ℂ f (closedBall 0 δ)`.

Introduce `w hw`. Establish `hw' : ‖w‖ ≤ δ` using `by simpa using hw`. Conclude with `((hdiffG _ (hin w hw')).hasFDerivAt.comp_hasDerivAt w (hφ w)).differentiableAt.differentiableWithinAt`. Establish `hderiv : deriv f 0 = word (ij :: L) F b`. Establish `h0 : b + (0 : ℂ) • E = b` using `by simp`.

Establish `hb : DifferentiableAt ℂ G (b + (0 : ℂ) • E)`. Rewrite using `[h0]`. Conclude with `hdiffG b (hsub (mem_pdisc_self b hr))`. Establish `h3 : HasDerivAt f (fderiv ℂ G (b + (0 : ℂ) • E) E) 0` using `hb.hasFDerivAt.comp_hasDerivAt (0 : ℂ) (hφ 0)`. Rewrite using `[h3.deriv, h0]`.

Both sides reduce to the same expression. Use `set B : ℝ := (L.map fun ij => K / r ij.1 ij.2).prod * M with hB`. Establish `hsphere : ∀ w ∈ sphere (0 : ℂ) δ, ‖f w‖ ≤ B`. Introduce `w hw`. Establish `hw' : ‖w‖ = δ` using `by simpa using hw`.

Break down `Nat.eq_zero_or_pos L.length with hL | hL` into its components or cases. Establish `hLnil : L = []` using `List.length_eq_zero_iff.mp hL`. Substitute `hLnil` using the available equality. Use `show ‖F (b + w • E)‖ ≤ B`. Simplify using `only [hB, List.map_nil, List.prod_nil, one_mul]`.

Conclude with `hM _ (shift_mem b hr ij.1 ij.2 (hw'.le.trans hδr))`. Establish `hl : (0 : ℝ) < L.length` using `by exact_mod_cast hL set r' : Fin n → Fin n → ℝ := fun a c => r a c * ((L.length : ℝ) / K) with hr'`. Establish `hr'pos : ∀ a c, 0 < r' a c` using `fun a c => mul_pos (hr a c) (div_pos hl hK)`. Establish `hs` using `shift_sub b hr ij.1 ij.2 (w := w) hK hl.le (by simp [hKdef]) hw'`. Use `ih (b + w • E) r' hr'pos (hs.trans hsub) (fun x hx => hM x (hs hx))` as an intermediate fact.

Establish `heq : (L.map fun ij => (L.length : ℝ) / r' ij.1 ij.2) = (L.map fun ij => K / r ij.1 ij.2)`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `x _`. Simplify using `only [hr']`. Clear the denominators using the available nonvanishing facts.

Rewrite `this` using `[heq]`. Conclude with `this`. Establish `hc` using `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ (hfd.diffContOnCl_ball subset_rfl) hsphere`. Rewrite `hc` using `[hderiv]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]`. Rewrite using `[hB, hδdef, ← hKdef]`. Clear the denominators using the available nonvanishing facts.
-/
theorem cauchy_gen {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    (M : ℝ) : ∀ (L : List (Fin n × Fin n)) (b : Mc n) (r : Fin n → Fin n → ℝ), (∀ i j, 0 < r i j) →
      pdisc b r ⊆ U → (∀ x ∈ pdisc b r, ‖F x‖ ≤ M) →
      ‖word L F b‖ ≤ (L.map fun ij => (L.length : ℝ) / r ij.1 ij.2).prod * M := by
  intro L
  induction L with
  | nil =>
    intro b r hr _ hM
    simp only [word, List.foldr_nil, List.map_nil, List.prod_nil, one_mul]
    exact hM b (mem_pdisc_self b hr)
  | cons ij L ih =>
    intro b r hr hsub hM
    set K : ℝ := (L.length : ℝ) + 1 with hKdef
    have hK : 0 < K := by positivity
    set δ : ℝ := r ij.1 ij.2 / K with hδdef
    have hδ : 0 < δ := div_pos (hr _ _) hK
    have hδr : δ ≤ r ij.1 ij.2 := div_le_self (hr _ _).le (by simp [hKdef])
    set E : Mc n := Matrix.single ij.1 ij.2 (1 : ℂ) with hE
    set G : Mc n → ℂ := word L F with hG
    have hGd : ContDiffOn ℂ (⊤ : ℕ∞) G U := contDiffOn_word hU hF L
    set f : ℂ → ℂ := fun w => G (b + w • E) with hf
    have hφ : ∀ w : ℂ, HasDerivAt (fun w : ℂ => b + w • E) E w := by
      intro w
      have h := ((hasDerivAt_id w).smul_const E).const_add b
      rw [one_smul] at h
      exact h
    have hin : ∀ w : ℂ, ‖w‖ ≤ δ → b + w • E ∈ U := fun w hw =>
      hsub (shift_mem b hr ij.1 ij.2 (hw.trans hδr))
    have hdiffG : ∀ x ∈ U, DifferentiableAt ℂ G x := fun x hx =>
      ((hGd.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    have hfd : DifferentiableOn ℂ f (closedBall 0 δ) := by
      intro w hw
      have hw' : ‖w‖ ≤ δ := by simpa using hw
      exact ((hdiffG _ (hin w hw')).hasFDerivAt.comp_hasDerivAt w (hφ w)).differentiableAt.differentiableWithinAt
    have hderiv : deriv f 0 = word (ij :: L) F b := by
      have h0 : b + (0 : ℂ) • E = b := by simp
      have hb : DifferentiableAt ℂ G (b + (0 : ℂ) • E) := by
        rw [h0]; exact hdiffG b (hsub (mem_pdisc_self b hr))
      have h3 : HasDerivAt f (fderiv ℂ G (b + (0 : ℂ) • E) E) 0 := hb.hasFDerivAt.comp_hasDerivAt (0 : ℂ) (hφ 0)
      rw [h3.deriv, h0]
      rfl
    set B : ℝ := (L.map fun ij => K / r ij.1 ij.2).prod * M with hB
    have hsphere : ∀ w ∈ sphere (0 : ℂ) δ, ‖f w‖ ≤ B := by
      intro w hw
      have hw' : ‖w‖ = δ := by simpa using hw
      rcases Nat.eq_zero_or_pos L.length with hL | hL
      · have hLnil : L = [] := List.length_eq_zero_iff.mp hL
        subst hLnil
        show ‖F (b + w • E)‖ ≤ B
        simp only [hB, List.map_nil, List.prod_nil, one_mul]
        exact hM _ (shift_mem b hr ij.1 ij.2 (hw'.le.trans hδr))
      · have hl : (0 : ℝ) < L.length := by exact_mod_cast hL
        set r' : Fin n → Fin n → ℝ := fun a c => r a c * ((L.length : ℝ) / K) with hr'
        have hr'pos : ∀ a c, 0 < r' a c := fun a c => mul_pos (hr a c) (div_pos hl hK)
        have hs := shift_sub b hr ij.1 ij.2 (w := w) hK hl.le (by simp [hKdef]) hw'
        have := ih (b + w • E) r' hr'pos (hs.trans hsub) (fun x hx => hM x (hs hx))
        have heq : (L.map fun ij => (L.length : ℝ) / r' ij.1 ij.2) = (L.map fun ij => K / r ij.1 ij.2) := by
          apply List.map_congr_left
          intro x _
          simp only [hr']
          field_simp
        rw [heq] at this
        exact this
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
      (hfd.diffContOnCl_ball subset_rfl) hsphere
    rw [hderiv] at hc
    calc ‖word (ij :: L) F b‖ ≤ B / δ := hc
      _ = ((ij :: L).map fun ij' => ((ij :: L).length : ℝ) / r ij'.1 ij'.2).prod * M := by
        simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [hB, hδdef, ← hKdef]
        field_simp

/- English proof (translation)
Introduce `n F U hU hF b₀ ρ hρ hP M hM L`. Conclude with `cauchy_gen hU hF M L b₀ ρ hρ hP hM`.
-/
theorem cauchyW : CauchyW := by
  intro n F U hU hF b₀ ρ hρ hP M hM L
  exact cauchy_gen hU hF M L b₀ ρ hρ hP hM

end PositivityTheory.Rg.Sw.WR.K.GB

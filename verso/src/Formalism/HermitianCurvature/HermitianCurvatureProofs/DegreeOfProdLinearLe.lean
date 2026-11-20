import Formalism.HermitianCurvature.StatementLE
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset

/- English proof (translation)
Introduce `hConst hRed hGrid hSign hFit hClaimAll hStep hInd hBox hLB hLA hL2 hPair hCoef hLeib hCut`. Introduce `CR Cd CP h1 h2 h3 C₂ hC2 C₆ hC6 S hr hL hI hRoots hI1 hJ hP hSI hFI`. Establish `hK0 : 0 ≤ 2 * Real.exp 1 * √(C7 CR Cd CP)` using `by positivity`. Establish `hC2' : 64 ≤ C₂` using `by linarith`. Establish `hN : (1:ℝ) ≤ S.Ntot` using `by exact_mod_cast (by omega : 1 ≤ S.Ntot)`.

Establish `hr1 : (1:ℝ) ≤ ((S.r:ℝ)+1)^2`. Establish `: (0:ℝ) ≤ S.r` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Establish `hc` using `hConst S.k S.r S.Ntot C₂ C₆ (S.β - S.α) hr (by linarith) hC6 hI`. Establish `hNr : (1:ℝ) ≤ S.Ntot * ((S.r:ℝ)+1)^2` using `by nlinarith`.

Establish `hL64 : 64 ≤ S.L`. Rewrite using `[hL, mul_assoc]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h6 : 6 * (S.Ntot:ℝ) * S.L ≤ S.β - S.α` using `by rw [hL]; exact hc.2.2`. Apply `hRed hGrid hSign hFit S (by linarith) h6 hRoots hI1` to reduce the goal to its premises.

Apply `hBox hLB hLA hL2 hPair hCoef hLeib hCut S (by linarith) hFI hP` to reduce the goal to its premises. Apply `hClaimAll hStep hInd S (4 * S.Ntot) CR Cd CP (by linarith) h1 h2 h3 (by linarith) _ hJ hSI` to reduce the goal to its premises. Rewrite using `[hL]`. Establish `: 64 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) * (S.Ntot * ((S.r:ℝ)+1)^2) ≤ C₂ * (S.Ntot * ((S.r:ℝ)+1)^2)` using `mul_le_mul_of_nonneg_right hC2 (by linarith)`. Use polynomial arithmetic with `[this]`.
-/
theorem t_LemmaEFromSteps : LemmaEFromSteps := by
  intro hConst hRed hGrid hSign hFit hClaimAll hStep hInd hBox hLB hLA hL2 hPair hCoef hLeib hCut
  intro CR Cd CP h1 h2 h3 C₂ hC2 C₆ hC6 S hr hL hI hRoots hI1 hJ hP hSI hFI
  have hK0 : 0 ≤ 2 * Real.exp 1 * √(C7 CR Cd CP) := by positivity
  have hC2' : 64 ≤ C₂ := by linarith
  have hN : (1:ℝ) ≤ S.Ntot := by exact_mod_cast (by omega : 1 ≤ S.Ntot)
  have hr1 : (1:ℝ) ≤ ((S.r:ℝ)+1)^2 := by
    have : (0:ℝ) ≤ S.r := Nat.cast_nonneg _
    nlinarith
  have hc := hConst S.k S.r S.Ntot C₂ C₆ (S.β - S.α) hr (by linarith) hC6 hI
  have hNr : (1:ℝ) ≤ S.Ntot * ((S.r:ℝ)+1)^2 := by nlinarith
  have hL64 : 64 ≤ S.L := by
    rw [hL, mul_assoc]; nlinarith
  have h6 : 6 * (S.Ntot:ℝ) * S.L ≤ S.β - S.α := by rw [hL]; exact hc.2.2
  apply hRed hGrid hSign hFit S (by linarith) h6 hRoots hI1
  apply hBox hLB hLA hL2 hPair hCoef hLeib hCut S (by linarith) hFI hP
  apply hClaimAll hStep hInd S (4 * S.Ntot) CR Cd CP (by linarith) h1 h2 h3 (by linarith) _ hJ hSI
  rw [hL]
  have : 64 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) * (S.Ntot * ((S.r:ℝ)+1)^2) ≤ C₂ * (S.Ntot * ((S.r:ℝ)+1)^2) :=
    mul_le_mul_of_nonneg_right hC2 (by linarith)
  nlinarith [this]

/- English proof (translation)
Introduce `S hJ hstep w`. Proceed by induction on `w with`. Consider the case `nil`. Introduce `_ _`. Use `⟨hJ, ?_⟩` and prove the remaining obligations.

Simplify using `[Sys.size, plus, Sys.jn]`. Consider the case `cons Y w ih`. Introduce `hOn hlen`. Establish `hlen' : w.length < S.Ntot` using `by simpa [Nat.succ_le_iff] using hlen`. Establish `hc` using `ih hOn.2 hlen'.le`.

Establish `h` using `hstep w Y hOn hlen' hc.1`. Use `⟨h.1, ?_⟩` and prove the remaining obligations. Rewrite using `[h.2, hc.2]`. Simplify using `[Sys.size, plus]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem t_ClaimInduction : ClaimInduction := by
  intro S hJ hstep w
  induction w with
  | nil =>
    intro _ _
    refine ⟨hJ, ?_⟩
    simp [Sys.size, plus, Sys.jn]
  | cons Y w ih =>
    intro hOn hlen
    have hlen' : w.length < S.Ntot := by simpa [Nat.succ_le_iff] using hlen
    have hc := ih hOn.2 hlen'.le
    have h := hstep w Y hOn hlen' hc.1
    refine ⟨h.1, ?_⟩
    rw [h.2, hc.2]
    simp [Sys.size, plus]
    ring

/- English proof (translation)
Introduce `hStep hInd S σ CR Cd CP hσ h1 h2 h3 hL hLL hJ hSI`. Apply `hInd S hJ` to reduce the goal to its premises. Introduce `w Y hOn hlen hint`. Establish `hY : Y ∈ (S.step w).J`. Use `hOn.1` as an intermediate fact.

Simplify `this` using `[Step.J, Sys.box, S.step_a, S.step_L]`. Establish `h` using `hStep S.B (S.step w) S.c σ CR Cd CP hσ h1 h2 h3 (by rw [S.step_L]; exact hL) (by rw [S.step_L, S.step_r]; exact hLL) (hSI w hOn.2 hlen) hint Y hY`. Establish `e : S.dens (Y :: w) = LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y)`. Use function extensionality and compare the values at `ω`. Conclude with `S.step_new w Y ω`.

Rewrite using `[e]`. Use `⟨h.1, ?_⟩` and prove the remaining obligations. Rewrite using `[h.2, S.step_P]`. Both sides reduce to the same expression.
-/
theorem t_ClaimAll : ClaimAll := by
  intro hStep hInd S σ CR Cd CP hσ h1 h2 h3 hL hLL hJ hSI
  apply hInd S hJ
  intro w Y hOn hlen hint
  have hY : Y ∈ (S.step w).J := by
    have := hOn.1
    simpa [Step.J, Sys.box, S.step_a, S.step_L] using this
  have h := hStep S.B (S.step w) S.c σ CR Cd CP hσ h1 h2 h3 (by rw [S.step_L]; exact hL)
    (by rw [S.step_L, S.step_r]; exact hLL) (hSI w hOn.2 hlen) hint Y hY
  have e : S.dens (Y :: w) = LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) := by
    funext ω; exact S.step_new w Y ω
  rw [e]
  refine ⟨h.1, ?_⟩
  rw [h.2, S.step_P]
  rfl

/- English proof (translation)
Unfold `Sys.size`. Apply `List.prod_ne_zero` to reduce the goal to its premises. Introduce `h0`. Rewrite `h0` using `[List.mem_map]`. Take `⟨x, hx, hx0⟩` from `h0`.

Establish `hP : S.P x.2 = 0` using `abs_eq_zero.mp hx0`. Unfold `Sys.P at hP`. Rewrite `hP` using `[Finset.prod_eq_zero_iff]`. Take `⟨s, _, hs⟩` from `hP`. Apply `hR s` to reduce the goal to its premises.

Establish `: -S.lam s = x.2` using `by linarith`. Rewrite using `[this]`. Conclude with `hA.1 x hx`.
-/
theorem size_ne_zero (S : Sys) (hR : S.RootsOut) (w : List (Bool × ℝ)) (hA : S.admitted w) : S.size w ≠ 0 := by
  unfold Sys.size
  apply List.prod_ne_zero
  intro h0
  rw [List.mem_map] at h0
  obtain ⟨x, hx, hx0⟩ := h0
  have hP : S.P x.2 = 0 := abs_eq_zero.mp hx0
  unfold Sys.P at hP
  rw [Finset.prod_eq_zero_iff] at hP
  obtain ⟨s, _, hs⟩ := hP
  apply hR s
  have : -S.lam s = x.2 := by linarith
  rw [this]
  exact hA.1 x hx

/- English proof (translation)
Introduce `E W _ D S loc hN hRoots hAdm hwt hgram hJ0 hlim`. Establish `hj : ∀ v, (S v).jsq = (S v).jn`. Introduce `v`. Unfold `Sys.jn Sys.jsq`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun ω => (hJ0 v ω).symm)`.

Simplify using `only [hj]`. Introduce `w hw`. Establish `hwW : w ∈ D.Wall ∧ D.cnt w ≤ D.Ntop` using `by simpa [TB.Data.Wb] using hw`. Establish `hsz : ∀ v, (S v).size (loc w v) ≠ 0` using `fun v => size_ne_zero (S v) (hRoots v) _ (hAdm w hwW.1 v).1`. Establish `hl : Tendsto (fun ε : ℝ => ∏ v, (S v).principalHermitianLattice ε (loc w v)) (𝓝[>] 0) (𝓝 (∏ v, ((S v).size (loc w v) * (S v).jn)))` using `tendsto_finset_prod _ (fun v _ => hlim v _ (hAdm w hwW.1 v).1 (by rw [hN]; exact (hAdm w hwW.1 v).2.trans hwW.2))`.

Establish `h2` using `hl.div_const (D.wt w)`. Establish `hval : (∏ v, ((S v).size (loc w v) * (S v).jn)) / D.wt w = ∏ v, (S v).jn`. Rewrite using `[hwt w hwW.1, Finset.prod_mul_distrib]`. Establish `: (∏ v, (S v).size (loc w v)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr (fun v _ => hsz v)`. Clear the denominators using the available nonvanishing facts.

Rewrite `h2` using `[hval]`. Use `h2.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Rewrite using `[hgram ε hε w hwW.1]`.
-/
theorem t_EstEJoint : EstEJoint := by
  intro E W _ D S loc hN hRoots hAdm hwt hgram hJ0 hlim
  have hj : ∀ v, (S v).jsq = (S v).jn := by
    intro v
    unfold Sys.jn Sys.jsq
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hJ0 v ω).symm)
  simp only [hj]
  intro w hw
  have hwW : w ∈ D.Wall ∧ D.cnt w ≤ D.Ntop := by simpa [TB.Data.Wb] using hw
  have hsz : ∀ v, (S v).size (loc w v) ≠ 0 := fun v => size_ne_zero (S v) (hRoots v) _ (hAdm w hwW.1 v).1
  have hl : Tendsto (fun ε : ℝ => ∏ v, (S v).principalHermitianLattice ε (loc w v)) (𝓝[>] 0)
      (𝓝 (∏ v, ((S v).size (loc w v) * (S v).jn))) :=
    tendsto_finset_prod _ (fun v _ => hlim v _ (hAdm w hwW.1 v).1
      (by rw [hN]; exact (hAdm w hwW.1 v).2.trans hwW.2))
  have h2 := hl.div_const (D.wt w)
  have hval : (∏ v, ((S v).size (loc w v) * (S v).jn)) / D.wt w = ∏ v, (S v).jn := by
    rw [hwt w hwW.1, Finset.prod_mul_distrib]
    have : (∏ v, (S v).size (loc w v)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => hsz v)
    field_simp
  rw [hval] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hgram ε hε w hwW.1]

/- English proof (translation)
Introduce `k r N C₂ C₆ I hr hC h6 hI`. Establish `hk : (0:ℝ) ≤ k` using `Nat.cast_nonneg _`. Establish `hN0 : (0:ℝ) ≤ N` using `Nat.cast_nonneg _`. Establish `hr0 : (0:ℝ) ≤ r` using `Nat.cast_nonneg _`. Establish `hrN : (r:ℝ) + 1 ≤ N` using `by exact_mod_cast hr`.

Establish `hq : (0:ℝ) ≤ ((r:ℝ)+1)^2` using `by positivity`. Establish `hA : (0:ℝ) ≤ (k:ℝ) * N * ((r:ℝ)+1)^2` using `by positivity`. Establish `hB : (0:ℝ) ≤ (N:ℝ)^2 * ((r:ℝ)+1)^2` using `by positivity`. Establish `hC6 : C₂ ≤ C₆` using `by linarith`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `: (k:ℝ) * (C₂ * N * ((r:ℝ)+1)^2) = C₂ * ((k:ℝ) * N * ((r:ℝ)+1)^2)` using `by ring`. Rewrite using `[this]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hC6) hA, mul_nonneg (le_trans hC.le hC6) hB]`. Use `push_cast`. Establish `e : ((k:ℝ) + 2 * r + 1) * (C₂ * N * ((r:ℝ)+1)^2) = C₂ * ((k:ℝ) * N * ((r:ℝ)+1)^2) + C₂ * ((2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2)` using `by ring`.

Rewrite using `[e]`. Establish `h2 : (2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2 ≤ 2 * ((N:ℝ)^2 * ((r:ℝ)+1)^2)`. Establish `: (2 * (r:ℝ) + 1) * N ≤ 2 * (N:ℝ)^2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : C₂ * ((2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2) ≤ C₂ * (2 * ((N:ℝ)^2 * ((r:ℝ)+1)^2))` using `mul_le_mul_of_nonneg_left h2 hC.le`.

Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hC6) hA, mul_nonneg (sub_nonneg.mpr h6) hB, mul_nonneg hC.le hB]`. Establish `: 6 * (N:ℝ) * (C₂ * N * ((r:ℝ)+1)^2) = 6 * C₂ * ((N:ℝ)^2 * ((r:ℝ)+1)^2)` using `by ring`. Rewrite using `[this]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr h6) hB, mul_nonneg (le_trans hC.le hC6) hA]`.
-/
theorem t_Constants : Constants := by
  intro k r N C₂ C₆ I hr hC h6 hI
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hrN : (r:ℝ) + 1 ≤ N := by exact_mod_cast hr
  have hq : (0:ℝ) ≤ ((r:ℝ)+1)^2 := by positivity
  have hA : (0:ℝ) ≤ (k:ℝ) * N * ((r:ℝ)+1)^2 := by positivity
  have hB : (0:ℝ) ≤ (N:ℝ)^2 * ((r:ℝ)+1)^2 := by positivity
  have hC6 : C₂ ≤ C₆ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have : (k:ℝ) * (C₂ * N * ((r:ℝ)+1)^2) = C₂ * ((k:ℝ) * N * ((r:ℝ)+1)^2) := by ring
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC6) hA, mul_nonneg (le_trans hC.le hC6) hB]
  · push_cast
    have e : ((k:ℝ) + 2 * r + 1) * (C₂ * N * ((r:ℝ)+1)^2)
        = C₂ * ((k:ℝ) * N * ((r:ℝ)+1)^2) + C₂ * ((2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2) := by ring
    rw [e]
    have h2 : (2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2 ≤ 2 * ((N:ℝ)^2 * ((r:ℝ)+1)^2) := by
      have : (2 * (r:ℝ) + 1) * N ≤ 2 * (N:ℝ)^2 := by nlinarith
      nlinarith
    have h3 : C₂ * ((2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2) ≤ C₂ * (2 * ((N:ℝ)^2 * ((r:ℝ)+1)^2)) :=
      mul_le_mul_of_nonneg_left h2 hC.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hC6) hA, mul_nonneg (sub_nonneg.mpr h6) hB, mul_nonneg hC.le hB]
  · have : 6 * (N:ℝ) * (C₂ * N * ((r:ℝ)+1)^2) = 6 * C₂ * ((N:ℝ)^2 * ((r:ℝ)+1)^2) := by ring
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.mpr h6) hB, mul_nonneg (le_trans hC.le hC6) hA]

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => intro Y`. Simplify using `[Sys.OnBoxes]`. Consider the case `succ N ih`.

Introduce `Y`. Rewrite using `[List.ofFn_succ]`. Use `show (Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧ S.OnBoxes (List.ofFn fun i => Y i.succ)) ↔ _`. Rewrite using `[List.length_ofFn, ih]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h0, h1⟩ a`. Use `Fin.cases ?_ (fun b => ?_) a` and prove the remaining obligations. Simplify using `using h0`. Use `h1 b` as an intermediate fact. Establish `e : N + 1 - 1 - ((b.succ : Fin (N+1)) : ℕ) = N - 1 - (b : ℕ)`.

Simplify using `only [Fin.val_succ]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`. Conclude with `this`. Introduce `h`.

Use `⟨by simpa using h 0, fun b => ?_⟩` and prove the remaining obligations. Use `h b.succ` as an intermediate fact. Establish `e : N + 1 - 1 - ((b.succ : Fin (N+1)) : ℕ) = N - 1 - (b : ℕ)`. Simplify using `only [Fin.val_succ]`. Use linear arithmetic over natural numbers and integers.

Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem onBoxes_ofFn (S : Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    S.OnBoxes (List.ofFn Y) ↔ ∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ)) := by
  intro N
  induction N with
  | zero => intro Y; simp [Sys.OnBoxes]
  | succ N ih =>
    intro Y
    rw [List.ofFn_succ]
    show (Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧ S.OnBoxes (List.ofFn fun i => Y i.succ)) ↔ _
    rw [List.length_ofFn, ih]
    constructor
    · rintro ⟨h0, h1⟩ a
      refine Fin.cases ?_ (fun b => ?_) a
      · simpa using h0
      · have := h1 b
        have e : N + 1 - 1 - ((b.succ : Fin (N+1)) : ℕ) = N - 1 - (b : ℕ) := by
          simp only [Fin.val_succ]; omega
        rw [e]; exact this
    · intro h
      refine ⟨by simpa using h 0, fun b => ?_⟩
      have := h b.succ
      have e : N + 1 - 1 - ((b.succ : Fin (N+1)) : ℕ) = N - 1 - (b : ℕ) := by
        simp only [Fin.val_succ]; omega
      rw [e] at this; exact this

/- English proof (translation)
Rewrite using `[onBoxes_ofFn]`. Unfold `Fam.On`. Prove the components needed by the constructor for the conclusion. Introduce `h a`. Use `h a` as an intermediate fact.

Rewrite `this` using `[S.fam_J]`. Conclude with `this`. Introduce `h a`. Rewrite using `[S.fam_J]`. Conclude with `h a`.
-/
theorem on_iff (S : Sys) (N : ℕ) (Y : Fin N → ℝ) : (S.fam N).On Y ↔ S.OnBoxes (List.ofFn Y) := by
  rw [onBoxes_ofFn]
  unfold Fam.On
  constructor
  · intro h a; have := h a; rw [S.fam_J] at this; exact this
  · intro h a; rw [S.fam_J]; exact h a

/- English proof (translation)
Introduce `hLB hLA hL2 hPair hCoef hLeib hCut S hL hFI hP hClaim`. Establish `key : ∀ (N : ℕ) (Y : Fin N → ℝ), N ≤ S.Ntot → S.OnBoxes (List.ofFn Y) → Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (plus (List.ofFn Y))) (𝓝[>] 0) (𝓝 (S.size (plus (List.ofFn Y)) * S.jn))`. Introduce `N Y hN hOn`. Establish `hinf : ∀ a, ((S.fam N).J a).Infinite`. Introduce `a; rw [S.fam_J]; exact Set.Icc_infinite (by linarith)`.

Establish `hde : ∀ Y' : Fin N → ℝ, LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u) = S.dens (List.ofFn Y')`. Introduce `Y'`. Use function extensionality and compare the values at `ω`. Conclude with `(S.fam_dens N Y' ω).symm`. Establish `hcl : ∀ Y', (S.fam N).On Y' → Integrable (LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u)) S.B.μ`.

Introduce `Y' h'`. Rewrite using `[hde]`. Conclude with `(hClaim _ ((on_iff S N Y').mp h') (by rw [List.length_ofFn]; exact hN)).1`. Establish `h` using `hLB hLA hL2 hPair hCoef hLeib hCut S.B N (S.fam N) S.c hinf (hFI N hN) hcl Y ((on_iff S N Y).mpr hOn)`. Rewrite `h` using `[hde, (hClaim _ hOn (by rw [List.length_ofFn]; exact hN)).2]`.

Use `h.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Conclude with `(hP N Y hN hOn ε hε).symm`. Introduce `w hOn hlen`. Use `key w.length w.get hlen (by rw [List.ofFn_get]; exact hOn)` as an intermediate fact.

Rewrite `this` using `[List.ofFn_get]`. Then use the resulting hypothesis.
-/
theorem t_BoxLimitFromClaim : BoxLimitFromClaim := by
  intro hLB hLA hL2 hPair hCoef hLeib hCut S hL hFI hP hClaim
  have key : ∀ (N : ℕ) (Y : Fin N → ℝ), N ≤ S.Ntot → S.OnBoxes (List.ofFn Y) →
      Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (plus (List.ofFn Y))) (𝓝[>] 0)
        (𝓝 (S.size (plus (List.ofFn Y)) * S.jn)) := by
    intro N Y hN hOn
    have hinf : ∀ a, ((S.fam N).J a).Infinite := by
      intro a; rw [S.fam_J]; exact Set.Icc_infinite (by linarith)
    have hde : ∀ Y' : Fin N → ℝ, LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u) = S.dens (List.ofFn Y') := by
      intro Y'; funext ω; exact (S.fam_dens N Y' ω).symm
    have hcl : ∀ Y', (S.fam N).On Y' →
        Integrable (LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u)) S.B.μ := by
      intro Y' h'
      rw [hde]
      exact (hClaim _ ((on_iff S N Y').mp h') (by rw [List.length_ofFn]; exact hN)).1
    have h := hLB hLA hL2 hPair hCoef hLeib hCut S.B N (S.fam N) S.c hinf (hFI N hN) hcl Y ((on_iff S N Y).mpr hOn)
    rw [hde, (hClaim _ hOn (by rw [List.length_ofFn]; exact hN)).2] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hP N Y hN hOn ε hε).symm
  intro w hOn hlen
  have := key w.length w.get hlen (by rw [List.ofFn_get]; exact hOn)
  rwa [List.ofFn_get] at this

/- English proof (translation)
Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => intro _ y hy`. Simplify using `at hy`. Consider the case `cons Y w ih`.

Introduce `h y hy`. Break down `List.mem_cons.mp hy with rfl | hy'` into its components or cases. Conclude with `⟨w.length, by simp, h.1⟩`. Take `⟨a, ha, hm⟩` from `ih h.2 y hy'`. Conclude with `⟨a, by simp; omega, hm⟩`.
-/
theorem onBoxes_mem (S : Sys) : ∀ w : List ℝ, S.OnBoxes w → ∀ y ∈ w, ∃ a, a < w.length ∧ y ∈ S.box a := by
  intro w
  induction w with
  | nil => intro _ y hy; simp at hy
  | cons Y w ih =>
    intro h y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨w.length, by simp, h.1⟩
    · obtain ⟨a, ha, hm⟩ := ih h.2 y hy'
      exact ⟨a, by simp; omega, hm⟩

/- English proof (translation)
Introduce `S hL h6`. Establish `hsub : ∀ a, a < S.Ntot → S.box a ⊆ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3)`. Introduce `a ha x hx`. Establish `ha' : (a:ℝ) + 1 ≤ S.Ntot` using `by exact_mod_cast ha`. Establish `ha0 : (0:ℝ) ≤ a` using `Nat.cast_nonneg _`.

Take `⟨h1, h2⟩` from `hx`. Prove the components needed by the constructor for the conclusion. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Establish `hdist : ∀ a b, a < b → ∀ x ∈ S.box a, ∀ y ∈ S.box b, S.L ≤ y - x`.

Introduce `a b hab x hx y hy`. Establish `hab' : (a:ℝ) + 1 ≤ b` using `by exact_mod_cast hab`. Take `⟨_, h2⟩` from `hx`. Take `⟨h3, _⟩` from `hy`. Use the polynomial consequences of the given equalities and inequalities.

Use `⟨hsub, hdist, ?_⟩` and prove the remaining obligations. Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => intro _ _; exact ⟨by simp [plus], by simp [plus]⟩`. Consider the case `cons Y w ih`.

Introduce `hOn hlen`. Establish `hlen' : w.length < S.Ntot` using `by simpa [Nat.succ_le_iff] using hlen`. Establish `hA` using `ih hOn.2 hlen'.le`. Establish `hN : (1:ℝ) ≤ S.Ntot` using `by exact_mod_cast (by omega : 1 ≤ S.Ntot)`. Establish `hI : 0 ≤ S.β - S.α` using `by nlinarith`.

Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Simplify using `only [plus, List.map_cons, List.mem_cons] at hx`. Break down `hx with rfl | hx` into its components or cases. Use `hsub _ hlen' hOn.1` as an intermediate fact.

Conclude with `⟨by linarith [this.1], by linarith [this.2]⟩`. Conclude with `hA.1 x hx`. Simplify using `only [plus, List.map_cons, List.pairwise_cons]`. Use `⟨?_, hA.2⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[List.mem_map]`. Take `⟨y, hy, rfl⟩` from `hx`. Take `⟨a, ha, hm⟩` from `onBoxes_mem S w hOn.2 y hy`. Use `hdist a w.length ha y hm Y hOn.1` as an intermediate fact. Use `show 2 < |Y - y|`.

Rewrite using `[abs_of_nonneg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem t_BoxesFit : BoxesFit := by
  intro S hL h6
  have hsub : ∀ a, a < S.Ntot → S.box a ⊆ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3) := by
    intro a ha x hx
    have ha' : (a:ℝ) + 1 ≤ S.Ntot := by exact_mod_cast ha
    have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
    obtain ⟨h1, h2⟩ := hx
    constructor
    · nlinarith
    · nlinarith
  have hdist : ∀ a b, a < b → ∀ x ∈ S.box a, ∀ y ∈ S.box b, S.L ≤ y - x := by
    intro a b hab x hx y hy
    have hab' : (a:ℝ) + 1 ≤ b := by exact_mod_cast hab
    obtain ⟨_, h2⟩ := hx
    obtain ⟨h3, _⟩ := hy
    nlinarith
  refine ⟨hsub, hdist, ?_⟩
  intro w
  induction w with
  | nil => intro _ _; exact ⟨by simp [plus], by simp [plus]⟩
  | cons Y w ih =>
    intro hOn hlen
    have hlen' : w.length < S.Ntot := by simpa [Nat.succ_le_iff] using hlen
    have hA := ih hOn.2 hlen'.le
    have hN : (1:ℝ) ≤ S.Ntot := by exact_mod_cast (by omega : 1 ≤ S.Ntot)
    have hI : 0 ≤ S.β - S.α := by nlinarith
    constructor
    · intro x hx
      simp only [plus, List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · have := hsub _ hlen' hOn.1
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      · exact hA.1 x hx
    · simp only [plus, List.map_cons, List.pairwise_cons]
      refine ⟨?_, hA.2⟩
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨a, ha, hm⟩ := onBoxes_mem S w hOn.2 y hy
      have := hdist a w.length ha y hm Y hOn.1
      show 2 < |Y - y|
      rw [abs_of_nonneg (by linarith)]
      linarith

open MvPolynomial in
/- English proof (translation)
Use `(degreeOf_mul_le _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[degreeOf_C, zero_add]`. Use `(degreeOf_prod_le _ _ _).trans ?_` and prove the remaining obligations. Establish `h1 : ∀ b : Fin N, degreeOf a (∏ s : Fin n, (X b + C (lam s)) : MvPolynomial (Fin N) ℝ) ≤ if a = b then n else 0`. Introduce `b`.

Use `(degreeOf_prod_le _ _ _).trans ?_` and prove the remaining obligations. Establish `h2 : ∀ s : Fin n, degreeOf a (X b + C (lam s) : MvPolynomial (Fin N) ℝ) ≤ if a = b then 1 else 0`. Introduce `s`. Use `(degreeOf_add_le _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[degreeOf_C, degreeOf_X]`.

Simplify using the standard rewrite rules. Use `(Finset.sum_le_sum fun s _ => h2 s).trans ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Use `(Finset.sum_le_sum fun b _ => h1 b).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem degreeOf_prod_linear_le (N n : ℕ) (lam : Fin n → ℝ) (c : ℝ) (a : Fin N) :
    (C c * ∏ b : Fin N, ∏ s : Fin n, (X b + C (lam s)) : MvPolynomial (Fin N) ℝ).degreeOf a ≤ n := by
  classical
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [degreeOf_C, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  have h1 : ∀ b : Fin N, degreeOf a (∏ s : Fin n, (X b + C (lam s)) : MvPolynomial (Fin N) ℝ) ≤ if a = b then n else 0 := by
    intro b
    refine (degreeOf_prod_le _ _ _).trans ?_
    have h2 : ∀ s : Fin n, degreeOf a (X b + C (lam s) : MvPolynomial (Fin N) ℝ) ≤ if a = b then 1 else 0 := by
      intro s
      refine (degreeOf_add_le _ _ _).trans ?_
      rw [degreeOf_C, degreeOf_X]
      simp
    refine (Finset.sum_le_sum fun s _ => h2 s).trans ?_
    split_ifs <;> simp
  refine (Finset.sum_le_sum fun b _ => h1 b).trans ?_
  simp

/- English proof (translation)
Unfold `Sys.size`. Rewrite using `[List.map_ofFn, List.prod_ofFn]`. Both sides reduce to the same expression.
-/
theorem size_ofFn (S : Sys) (N : ℕ) (sg : Fin N → Bool) (Y : Fin N → ℝ) :
    S.size (List.ofFn fun a => (sg a, Y a)) = ∏ a, |S.P (Y a)| := by
  unfold Sys.size
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

/- English proof (translation)
Introduce `hGrid hSign hFit S hL h6 hRoots hI1 hBox w hA hlen`. Take `⟨sgn, _, hsgn⟩` from `hSign _ S.lam S.α S.β hRoots`. Take `⟨hsub, _, hAdm⟩` from `hFit S hL h6`. Establish `key : ∀ (N : ℕ), N ≤ S.Ntot → ∀ (sg : Fin N → Bool) (Y : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg a, Y a)) → Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (List.ofFn fun a => (sg a, Y a))) (𝓝[>] 0) (𝓝 (S.size (List.ofFn fun a => (sg a, Y a)) * S.jn))`. Introduce `N hN sg Y hAY`.

Set `Q : ℝ → MvPolynomial (Fin N) ℝ` to `fun ε => if h : 0 < ε then (hI1 ε h N hN).choose else 0`. Set `Q₀ : MvPolynomial (Fin N) ℝ` to `MvPolynomial.C (sgn ^ N * S.jn) * ∏ b : Fin N, ∏ s, (MvPolynomial.X b + MvPolynomial.C (S.lam s))`. Establish `hQ : ∀ ε, 0 < ε → ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) → S.principalHermitianLattice ε (List.ofFn fun a => (sg' a, Y' a)) = MvPolynomial.eval Y' (Q ε)`. Introduce `ε hε sg' Y' h'`. Simplify using `only [Q, dif_pos hε]`.

Conclude with `(hI1 ε hε N hN).choose_spec.2 sg' Y' h'`. Establish `hQd : ∀ ε a, (Q ε).degreeOf a ≤ S.k + 2 * S.r + 1`. Introduce `ε a`. Distinguish the cases in `hε : 0 < ε`. Simplify using `only [Q, dif_pos hε]`.

Conclude with `(hI1 ε hε N hN).choose_spec.1 a`. Simplify using `[Q, dif_neg hε]`. Establish `hQ0 : ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) → S.size (List.ofFn fun a => (sg' a, Y' a)) * S.jn = MvPolynomial.eval Y' Q₀`. Introduce `sg' Y' h'`. Rewrite using `[size_ofFn]`.

Establish `: ∀ a, |S.P (Y' a)| = sgn * S.P (Y' a)`. Introduce `a`. Apply `hsgn` to reduce the goal to its premises. Conclude with `h'.1 (sg' a, Y' a) (by rw [List.mem_ofFn]; exact ⟨a, rfl⟩)`. Rewrite using `[Finset.prod_congr rfl (fun a _ => this a), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Simplify using `only [Q₀, map_mul, MvPolynomial.eval_C, map_prod, map_add, MvPolynomial.eval_X, Sys.P]`. Expand and normalize the polynomial expressions, which then agree. Set `n` to `S.k + 2 * S.r + 1`. Set `lo : Fin N → ℝ` to `fun a => S.α + (S.β - S.α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * S.L`. Set `grid : Fin N → Finset ℝ` to `fun a => (Finset.range (n + 1)).image fun i : ℕ => lo a + S.L * ((i : ℝ) / (n + 1))`.

Establish `hcard : ∀ a, (grid a).card = n + 1`. Introduce `a`. Rewrite using `[Finset.card_image_of_injective, Finset.card_range]`. Introduce `i i' h`. Establish `hn : ((n : ℝ) + 1) ≠ 0` using `by positivity`.

Establish `hL0 : S.L ≠ 0` using `by linarith`. Establish `h1 : S.L * ((i : ℝ) / (n + 1)) = S.L * ((i' : ℝ) / (n + 1))` using `by simpa using h`. Establish `h2` using `mul_left_cancel₀ hL0 h1`. Establish `h3 : (i : ℝ) = i'` using `by field_simp at h2; exact h2`. Conclude with `h3` after adjusting the coercions.

Establish `hgm : ∀ a, ∀ y ∈ grid a, y ∈ S.box (N - 1 - (a : ℕ))`. Introduce `a y hy`. Simplify using `only [grid, Finset.mem_image, Finset.mem_range] at hy`. Take `⟨i, hi, rfl⟩` from `hy`. Establish `hi' : (i : ℝ) ≤ n` using `by exact_mod_cast Nat.lt_succ_iff.mp hi`.

Establish `h01 : (i : ℝ) / (n + 1) ≤ 1`. Rewrite using `[div_le_one (by positivity)]; linarith`. Establish `h00 : (0:ℝ) ≤ (i : ℝ) / (n + 1)` using `by positivity`. Prove the components needed by the constructor for the conclusion. Use `show lo a ≤ _`.

Use the polynomial consequences of the given equalities and inequalities. Use `show _ ≤ lo a + S.L`. Use the polynomial consequences of the given equalities and inequalities. Establish `hconv` using `hGrid N n ℝ (𝓝[>] 0) Q Q₀ grid hQd (fun a => degreeOf_prod_linear_le N _ S.lam _ a) hcard (by`. Introduce `Y' hY'`.

Establish `hOn : S.OnBoxes (List.ofFn Y')` using `(onBoxes_ofFn S N Y').mpr fun a => hgm a _ (hY' a)`. Establish `hlen' : (List.ofFn Y').length ≤ S.Ntot` using `by rw [List.length_ofFn]; exact hN`. Establish `hb` using `hBox _ hOn hlen'`. Establish `hAd` using `hAdm _ hOn hlen'`. Establish `e : plus (List.ofFn Y') = List.ofFn fun a => (true, Y' a)`.

Unfold `plus`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Rewrite `hb`, `hAd` using `[e]`. Rewrite `hb` using `[hQ0 _ _ hAd]`.

Use `hb.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Conclude with `hQ ε hε _ _ hAd) Y`. Rewrite using `[hQ0 _ _ hAY]`. Use `hconv.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Conclude with `(hQ ε hε _ _ hAY).symm`. Establish `e : (List.ofFn fun a => ((w.get a).1, (w.get a).2)) = w`. Establish `: (fun a => ((w.get a).1, (w.get a).2)) = w.get` using `by funext a; rfl`. Rewrite using `[this, List.ofFn_get]`.

Use `key w.length hlen (fun a => (w.get a).1) (fun a => (w.get a).2) (by rw [e]; exact hA)` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem t_ReduceToBoxes : ReduceToBoxes := by
  classical
  intro hGrid hSign hFit S hL h6 hRoots hI1 hBox w hA hlen
  obtain ⟨sgn, _, hsgn⟩ := hSign _ S.lam S.α S.β hRoots
  obtain ⟨hsub, _, hAdm⟩ := hFit S hL h6
  have key : ∀ (N : ℕ), N ≤ S.Ntot → ∀ (sg : Fin N → Bool) (Y : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg a, Y a)) →
      Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (List.ofFn fun a => (sg a, Y a))) (𝓝[>] 0)
        (𝓝 (S.size (List.ofFn fun a => (sg a, Y a)) * S.jn)) := by
    intro N hN sg Y hAY
    let Q : ℝ → MvPolynomial (Fin N) ℝ := fun ε => if h : 0 < ε then (hI1 ε h N hN).choose else 0
    let Q₀ : MvPolynomial (Fin N) ℝ :=
      MvPolynomial.C (sgn ^ N * S.jn) * ∏ b : Fin N, ∏ s, (MvPolynomial.X b + MvPolynomial.C (S.lam s))
    have hQ : ∀ ε, 0 < ε → ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) →
        S.principalHermitianLattice ε (List.ofFn fun a => (sg' a, Y' a)) = MvPolynomial.eval Y' (Q ε) := by
      intro ε hε sg' Y' h'
      simp only [Q, dif_pos hε]
      exact (hI1 ε hε N hN).choose_spec.2 sg' Y' h'
    have hQd : ∀ ε a, (Q ε).degreeOf a ≤ S.k + 2 * S.r + 1 := by
      intro ε a
      by_cases hε : 0 < ε
      · simp only [Q, dif_pos hε]; exact (hI1 ε hε N hN).choose_spec.1 a
      · simp [Q, dif_neg hε]
    have hQ0 : ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) →
        S.size (List.ofFn fun a => (sg' a, Y' a)) * S.jn = MvPolynomial.eval Y' Q₀ := by
      intro sg' Y' h'
      rw [size_ofFn]
      have : ∀ a, |S.P (Y' a)| = sgn * S.P (Y' a) := by
        intro a
        apply hsgn
        exact h'.1 (sg' a, Y' a) (by rw [List.mem_ofFn]; exact ⟨a, rfl⟩)
      rw [Finset.prod_congr rfl (fun a _ => this a), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      simp only [Q₀, map_mul, MvPolynomial.eval_C, map_prod, map_add, MvPolynomial.eval_X, Sys.P]
      ring
    let n := S.k + 2 * S.r + 1
    let lo : Fin N → ℝ := fun a => S.α + (S.β - S.α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * S.L
    let grid : Fin N → Finset ℝ := fun a => (Finset.range (n + 1)).image fun i : ℕ => lo a + S.L * ((i : ℝ) / (n + 1))
    have hcard : ∀ a, (grid a).card = n + 1 := by
      intro a
      rw [Finset.card_image_of_injective, Finset.card_range]
      intro i i' h
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hL0 : S.L ≠ 0 := by linarith
      have h1 : S.L * ((i : ℝ) / (n + 1)) = S.L * ((i' : ℝ) / (n + 1)) := by simpa using h
      have h2 := mul_left_cancel₀ hL0 h1
      have h3 : (i : ℝ) = i' := by field_simp at h2; exact h2
      exact_mod_cast h3
    have hgm : ∀ a, ∀ y ∈ grid a, y ∈ S.box (N - 1 - (a : ℕ)) := by
      intro a y hy
      simp only [grid, Finset.mem_image, Finset.mem_range] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      have hi' : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hi
      have h01 : (i : ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have h00 : (0:ℝ) ≤ (i : ℝ) / (n + 1) := by positivity
      constructor
      · show lo a ≤ _
        nlinarith
      · show _ ≤ lo a + S.L
        nlinarith
    have hconv := hGrid N n ℝ (𝓝[>] 0) Q Q₀ grid hQd (fun a => degreeOf_prod_linear_le N _ S.lam _ a) hcard (by
      intro Y' hY'
      have hOn : S.OnBoxes (List.ofFn Y') := (onBoxes_ofFn S N Y').mpr fun a => hgm a _ (hY' a)
      have hlen' : (List.ofFn Y').length ≤ S.Ntot := by rw [List.length_ofFn]; exact hN
      have hb := hBox _ hOn hlen'
      have hAd := hAdm _ hOn hlen'
      have e : plus (List.ofFn Y') = List.ofFn fun a => (true, Y' a) := by
        unfold plus; rw [List.map_ofFn]; rfl
      rw [e] at hb hAd
      rw [hQ0 _ _ hAd] at hb
      refine hb.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hQ ε hε _ _ hAd) Y
    rw [hQ0 _ _ hAY]
    refine hconv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hQ ε hε _ _ hAY).symm
  have e : (List.ofFn fun a => ((w.get a).1, (w.get a).2)) = w := by
    have : (fun a => ((w.get a).1, (w.get a).2)) = w.get := by funext a; rfl
    rw [this, List.ofFn_get]
  have := key w.length hlen (fun a => (w.get a).1) (fun a => (w.get a).2) (by rw [e]; exact hA)
  rwa [e] at this

/- English proof (translation)
Introduce `n lam α β L Y s hαβ hR hL hnL hs h1 h2 h3 h4`. Establish `hI : 0 < β - α` using `by linarith`. Rewrite using `[Finset.abs_prod, Finset.abs_prod]`. Establish `hx0 : 0 ≤ 3 * L / (β - α)` using `by positivity`. Establish `hfac : ∀ t, |Y + lam t| ≤ (1 + 3 * L / (β - α)) * |Y + s + lam t|`.

Introduce `t`. Establish `hdist : (β - α) / 3 ≤ |Y + s + lam t|`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hR t` to reduce the goal to its premises.

Rewrite `hc` using `[abs_lt]`. Apply the tactic sequence `constructor <;> linarith [hc.1, hc.2]`. Establish `h5 : |Y + lam t| ≤ |Y + s + lam t| + |s|`. Apply the tactic sequence `rcases abs_cases (Y + lam t) with h | h <;> rcases abs_cases (Y + s + lam t) with h' | h' <;>`. Apply the tactic sequence `rcases abs_cases s with h'' | h'' <;> linarith [h.1, h'.1, h''.1]`.

Establish `h3L : L ≤ 3 * L / (β - α) * |Y + s + lam t|`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hI]`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `_ ≤ Real.exp 3 * ∏ t, |Y + s + lam t| := by`. Apply `mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => abs_nonneg _)` to reduce the goal to its premises. Establish `h6 : 1 + 3 * L / (β - α) ≤ Real.exp (3 * L / (β - α))`. Combine the linear relations using `[Real.add_one_le_exp (3 * L / (β - α))]`.

Combine the equalities or inequalities in the displayed calculation. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Rewrite using `[mul_div_assoc', div_le_iff₀ hI]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem t_PRatioMiddle : PRatioMiddle := by
  intro n lam α β L Y s hαβ hR hL hnL hs h1 h2 h3 h4
  have hI : 0 < β - α := by linarith
  rw [Finset.abs_prod, Finset.abs_prod]
  have hx0 : 0 ≤ 3 * L / (β - α) := by positivity
  have hfac : ∀ t, |Y + lam t| ≤ (1 + 3 * L / (β - α)) * |Y + s + lam t| := by
    intro t
    have hdist : (β - α) / 3 ≤ |Y + s + lam t| := by
      by_contra hc
      push_neg at hc
      apply hR t
      rw [abs_lt] at hc
      constructor <;> linarith [hc.1, hc.2]
    have h5 : |Y + lam t| ≤ |Y + s + lam t| + |s| := by
      rcases abs_cases (Y + lam t) with h | h <;> rcases abs_cases (Y + s + lam t) with h' | h' <;>
        rcases abs_cases s with h'' | h'' <;> linarith [h.1, h'.1, h''.1]
    have h3L : L ≤ 3 * L / (β - α) * |Y + s + lam t| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hI]; nlinarith
    nlinarith
  calc ∏ t, |Y + lam t| ≤ ∏ t, (1 + 3 * L / (β - α)) * |Y + s + lam t| :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun t _ => hfac t)
    _ = (1 + 3 * L / (β - α)) ^ n * ∏ t, |Y + s + lam t| := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ Real.exp 3 * ∏ t, |Y + s + lam t| := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        have h6 : 1 + 3 * L / (β - α) ≤ Real.exp (3 * L / (β - α)) := by
          linarith [Real.add_one_le_exp (3 * L / (β - α))]
        calc (1 + 3 * L / (β - α)) ^ n ≤ (Real.exp (3 * L / (β - α))) ^ n :=
              pow_le_pow_left₀ (by positivity) h6 n
          _ = Real.exp (n * (3 * L / (β - α))) := by rw [Real.exp_nat_mul]
          _ ≤ Real.exp 3 := by
              apply Real.exp_le_exp.mpr
              rw [mul_div_assoc', div_le_iff₀ hI]; nlinarith

/- English proof (translation)
Introduce `n lam α β hR`. It suffices to establish `h : ∀ T : Finset (Fin n), ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ ∀ Y ∈ Set.Icc α β, |∏ s ∈ T, (Y + lam s)| = sg * ∏ s ∈ T, (Y + lam s) from h Finset.univ`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact ⟨1, Or.inl rfl, fun Y _ => by simp⟩`.

Consider the case `insert s T hs ih`. Take `⟨sg, hsg, h⟩` from `ih`. Establish `hcase : (∀ Y ∈ Set.Icc α β, 0 < Y + lam s) ∨ (∀ Y ∈ Set.Icc α β, Y + lam s < 0)`. Distinguish the cases in `h1 : -lam s < α`. Use `left`.

Introduce `Y hY`. Combine the linear relations using `[hY.1]`. Distinguish the cases in `h2 : β < -lam s`. Use `right`. Introduce `Y hY`.

Combine the linear relations using `[hY.2]`. Conclude with `absurd ⟨not_lt.mp h1, not_lt.mp h2⟩ (hR s)`. Break down `hcase with hp | hn` into its components or cases. Use `⟨sg, hsg, fun Y hY => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_insert hs, abs_mul, h Y hY, abs_of_pos (hp Y hY)]`.

Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `refine ⟨-sg, by rcases hsg with rfl | rfl <;> simp, fun Y hY => ?_⟩`. Rewrite using `[Finset.prod_insert hs, abs_mul, h Y hY, abs_of_neg (hn Y hY)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem t_ConstSign : ConstSign := by
  classical
  intro n lam α β hR
  suffices h : ∀ T : Finset (Fin n), ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧
      ∀ Y ∈ Set.Icc α β, |∏ s ∈ T, (Y + lam s)| = sg * ∏ s ∈ T, (Y + lam s) from h Finset.univ
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨1, Or.inl rfl, fun Y _ => by simp⟩
  | insert s T hs ih =>
    obtain ⟨sg, hsg, h⟩ := ih
    have hcase : (∀ Y ∈ Set.Icc α β, 0 < Y + lam s) ∨ (∀ Y ∈ Set.Icc α β, Y + lam s < 0) := by
      by_cases h1 : -lam s < α
      · left; intro Y hY; linarith [hY.1]
      · by_cases h2 : β < -lam s
        · right; intro Y hY; linarith [hY.2]
        · exact absurd ⟨not_lt.mp h1, not_lt.mp h2⟩ (hR s)
    rcases hcase with hp | hn
    · refine ⟨sg, hsg, fun Y hY => ?_⟩
      rw [Finset.prod_insert hs, abs_mul, h Y hY, abs_of_pos (hp Y hY)]; ring
    · refine ⟨-sg, by rcases hsg with rfl | rfl <;> simp, fun Y hY => ?_⟩
      rw [Finset.prod_insert hs, abs_mul, h Y hY, abs_of_neg (hn Y hY)]; ring

/- English proof (translation)
Introduce `hPR hFit S hL h6 hn hRoots w hlen`. Take `⟨hsub, _, _⟩` from `hFit S hL h6`. Establish `hN : (1:ℝ) ≤ S.Ntot` using `by exact_mod_cast (by omega : 1 ≤ S.Ntot)`. Establish `hI : S.α < S.β` using `by nlinarith`. Establish `hJ : (S.step w).J = S.box w.length`.

Simplify using `[Step.J, Sys.box, S.step_a, S.step_L]`. Establish `hPf : (S.step w).P = fun Y => ∏ s, (Y + S.lam s)` using `by funext Y; exact S.step_P w Y`. Establish `hmid` using `hsub w.length hlen`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hPf]`.

Apply `Continuous.continuousOn` to reduce the goal to its premises. Use `fun_prop`. Introduce `Y hY h0`. Rewrite `hY` using `[hJ]`. Establish `hm` using `hmid hY`.

Rewrite `h0` using `[S.step_P, Finset.prod_eq_zero_iff]`. Take `⟨s, _, hs⟩` from `h0`. Apply `hRoots s` to reduce the goal to its premises. Establish `: -S.lam s = Y` using `by linarith`. Rewrite using `[this]`.

Conclude with `⟨by linarith [hm.1], by linarith [hm.2]⟩`. Introduce `Y s hY hYs`. Rewrite `hY`, `hYs` using `[hJ]`. Establish `hm` using `hmid hY`. Establish `hms` using `hmid hYs`.

Rewrite using `[S.step_P, S.step_P]`. Establish `hs : |(-s)| ≤ S.L`. Rewrite using `[abs_neg, abs_le]`. Apply the tactic sequence `constructor <;> linarith [hY.1, hY.2, hYs.1, hYs.2]`. Use `hPR _ S.lam S.α S.β S.L (Y + s) (-s) hI (fun t ht => hRoots t ⟨ht.1.le, ht.2.le⟩) (by linarith) hn hs hms.1 hms.2 (by rw [add_neg_cancel_right]; exact hm.1) (by rw [add_neg_cancel_right]; exact hm.2)` as an intermediate fact.

Simplify `this` using `[add_neg_cancel_right]`.
-/
theorem t_PImportsHold : PImportsHold := by
  intro hPR hFit S hL h6 hn hRoots w hlen
  obtain ⟨hsub, _, _⟩ := hFit S hL h6
  have hN : (1:ℝ) ≤ S.Ntot := by exact_mod_cast (by omega : 1 ≤ S.Ntot)
  have hI : S.α < S.β := by nlinarith
  have hJ : (S.step w).J = S.box w.length := by
    simp [Step.J, Sys.box, S.step_a, S.step_L]
  have hPf : (S.step w).P = fun Y => ∏ s, (Y + S.lam s) := by funext Y; exact S.step_P w Y
  have hmid := hsub w.length hlen
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hPf]
    apply Continuous.continuousOn
    fun_prop
  · intro Y hY h0
    rw [hJ] at hY
    have hm := hmid hY
    rw [S.step_P, Finset.prod_eq_zero_iff] at h0
    obtain ⟨s, _, hs⟩ := h0
    apply hRoots s
    have : -S.lam s = Y := by linarith
    rw [this]
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  · intro Y s hY hYs
    rw [hJ] at hY hYs
    have hm := hmid hY
    have hms := hmid hYs
    rw [S.step_P, S.step_P]
    have hs : |(-s)| ≤ S.L := by
      rw [abs_neg, abs_le]
      constructor <;> linarith [hY.1, hY.2, hYs.1, hYs.2]
    have := hPR _ S.lam S.α S.β S.L (Y + s) (-s) hI
      (fun t ht => hRoots t ⟨ht.1.le, ht.2.le⟩) (by linarith) hn hs hms.1 hms.2
      (by rw [add_neg_cancel_right]; exact hm.1) (by rw [add_neg_cancel_right]; exact hm.2)
    simpa [add_neg_cancel_right] using this

end Formalism.FourierDecayAlt.P.LEx2

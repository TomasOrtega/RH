import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOnGroupOfSpecialStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFreeDerivCongrOnUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixUnitDerivEqTraceFreeAddDegreeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdShiftedCyclicWordExpansionStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.GelfCentral

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `h₁ g₀ hg₀`. Take `⟨U', F', hU', hgU', hF', hfF'⟩` from `h₂ g₀ hg₀`. Use `⟨U ∩ U', F + F', hU.inter hU', ⟨hgU, hgU'⟩, (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), ?_⟩` and prove the remaining obligations. Introduce `g hg hgJ`.

Simplify using `[hfF g hg.1 hgJ, hfF' g hg.2 hgJ]`.
-/
theorem smoothOnG_add {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h₁ : SmoothOnG ε G₁) (h₂ : SmoothOnG ε G₂) : SmoothOnG ε (G₁ + G₂) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := h₁ g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := h₂ g₀ hg₀
  refine ⟨U ∩ U', F + F', hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), ?_⟩
  intro g hg hgJ
  simp [hfF g hg.1 hgJ, hfF' g hg.2 hgJ]

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `h g₀ hg₀`. Use `⟨U, fun x => c * F x, hU, hgU, contDiffOn_const.mul hF, ?_⟩` and prove the remaining obligations. Introduce `g hg hgJ`. Simplify using `[hfF g hg hgJ]`.
-/
theorem smoothOnG_smul {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (h : SmoothOnG ε G) : SmoothOnG ε (c • G) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := h g₀ hg₀
  refine ⟨U, fun x => c * F x, hU, hgU, contDiffOn_const.mul hF, ?_⟩
  intro g hg hgJ
  simp [hfF g hg hgJ]

/- English proof (translation)
Introduce `g₀ _`. Conclude with `⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩`.
-/
theorem smoothOnG_zero (ε : Fin n → Bool) : SmoothOnG ε (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
  intro g₀ _
  exact ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

/- English proof (translation)
Unfold `inUJ at *`. Establish `h1 : star z * z = 1`. Rewrite using `[Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]`. Evaluate the numerical expressions. Establish `h2 : z * star z = 1` using `by rw [mul_comm]; exact h1`.

Simplify using `only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx, h1, h2, one_smul]`.
-/
theorem inUJ_smul {ε : Fin n → Bool} {z : ℂ} (hz : ‖z‖ = 1) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : inUJ ε x) : inUJ ε (z • x) := by
  unfold inUJ at *
  have h1 : star z * z = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]; norm_num
  have h2 : z * star z = 1 := by rw [mul_comm]; exact h1
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hx, h1, h2, one_smul]

def Cent (ε : Fin n → Bool) (m : ℤ) (G : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ∀ x, inUJ ε x → G (z • x) = z ^ m * G x

/- English proof (translation)
Unfold `Rd`. Use `congr 1`. Use function extensionality and compare the values at `t`. Conclude with `h _ (indefinite_unitary_mul_mem ε hx (exp_indefinite_unitary_holds n ε X hX t))`.
-/
theorem rd_congr {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ x, inUJ ε x → G₁ x = G₂ x) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : inUJ ε x) : Rd X G₁ x = Rd X G₂ x := by
  unfold Rd
  congr 1
  funext t
  exact h _ (indefinite_unitary_mul_mem ε hx (exp_indefinite_unitary_holds n ε X hX t))

/- English proof (translation)
Take `⟨h1, h2, -, -⟩` from `complex_parts_mem_lie_algebra_holds n ε Z`. Unfold `Ec`. Rewrite using `[rd_congr h h1 hx, rd_congr h h2 hx]`.
-/
theorem ec_congr {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ x, inUJ ε x → G₁ x = G₂ x) (Z : Matrix (Fin n) (Fin n) ℂ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : inUJ ε x) : Ec ε Z G₁ x = Ec ε Z G₂ x := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε Z
  unfold Ec
  rw [rd_congr h h1 hx, rd_congr h h2 hx]

/- English proof (translation)
Introduce `z hz x hx`. Unfold `Rd`. Establish `e : (fun t : ℝ => G (z • x * NormedSpace.exp ((t : ℂ) • X))) = fun t : ℝ => z ^ m * G (x * NormedSpace.exp ((t : ℂ) • X))`. Use function extensionality and compare the values at `t`. Rewrite using `[Matrix.smul_mul]`.

Conclude with `h z hz _ (indefinite_unitary_mul_mem ε hx (exp_indefinite_unitary_holds n ε X hX t))`. Rewrite using `[e]`. Conclude with `deriv_const_mul_field _`.
-/
theorem rd_cent {ε : Fin n → Bool} {m : ℤ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : Cent ε m G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : Cent ε m (Rd X G) := by
  intro z hz x hx
  unfold Rd
  have e : (fun t : ℝ => G (z • x * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => z ^ m * G (x * NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [Matrix.smul_mul]
    exact h z hz _ (indefinite_unitary_mul_mem ε hx (exp_indefinite_unitary_holds n ε X hX t))
  rw [e]
  exact deriv_const_mul_field _

/- English proof (translation)
Take `⟨h1, h2, -, -⟩` from `complex_parts_mem_lie_algebra_holds n ε Z`. Introduce `z hz x hx`. Unfold `Ec`. Rewrite using `[rd_cent h h1 z hz x hx, rd_cent h h2 z hz x hx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ec_cent {ε : Fin n → Bool} {m : ℤ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : Cent ε m G)
    (Z : Matrix (Fin n) (Fin n) ℂ) : Cent ε m (Ec ε Z G) := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε Z
  intro z hz x hx
  unfold Ec
  rw [rd_cent h h1 z hz x hx, rd_cent h h2 z hz x hx]
  ring

/- English proof (translation)
Take `⟨h1, h2, -, -⟩` from `complex_parts_mem_lie_algebra_holds n ε Z`. Establish `s1` using `rdSmooth_of right_derivative_extends n ε G _ h h1`. Establish `s2` using `rdSmooth_of right_derivative_extends n ε G _ h h2`. Establish `e : Ec ε Z G = Rd (cpart1 ε Z) G + Complex.I • Rd (cpart2 ε Z) G`. Use function extensionality and compare the values at `g`.

Simplify using `[Ec]`. Rewrite using `[e]`. Conclude with `smoothOnG_add s1 (smoothOnG_smul Complex.I s2)`.
-/
theorem ec_smooth {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : SmoothOnG ε G)
    (Z : Matrix (Fin n) (Fin n) ℂ) : SmoothOnG ε (Ec ε Z G) := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε Z
  have s1 := rdSmooth_of right_derivative_extends n ε G _ h h1
  have s2 := rdSmooth_of right_derivative_extends n ε G _ h h2
  have e : Ec ε Z G = Rd (cpart1 ε Z) G + Complex.I • Rd (cpart2 ε Z) G := by
    funext g; simp [Ec]
  rw [e]
  exact smoothOnG_add s1 (smoothOnG_smul Complex.I s2)

/- English proof (translation)
Use `(right_derivative_linear n ε G₁ G₂ X X 1 1 x h₁ h₂ hX hX hx).2.2` as an intermediate fact. Establish `e : (G₁ + G₂) = fun h => G₁ h + (1 : ℂ) * G₂ h` using `by funext h; simp`. Rewrite using `[e, this, one_mul]`.
-/
theorem rd_add {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h₁ : SmoothOnG ε G₁) (h₂ : SmoothOnG ε G₂) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : inUJ ε x) : Rd X (G₁ + G₂) x = Rd X G₁ x + Rd X G₂ x := by
  have := (right_derivative_linear n ε G₁ G₂ X X 1 1 x h₁ h₂ hX hX hx).2.2
  have e : (G₁ + G₂) = fun h => G₁ h + (1 : ℂ) * G₂ h := by funext h; simp
  rw [e, this, one_mul]

/- English proof (translation)
Use `show deriv (fun t : ℝ => c * G (x * NormedSpace.exp ((t : ℂ) • X))) 0 = c * deriv (fun t : ℝ => G (x * NormedSpace.exp ((t : ℂ) • X))) 0`. Conclude with `deriv_const_mul_field c`.
-/
theorem rd_smul {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ) (X x : Matrix (Fin n) (Fin n) ℂ) :
    Rd X (c • G) x = c * Rd X G x := by
  show deriv (fun t : ℝ => c * G (x * NormedSpace.exp ((t : ℂ) • X))) 0 =
    c * deriv (fun t : ℝ => G (x * NormedSpace.exp ((t : ℂ) • X))) 0
  exact deriv_const_mul_field c

/- English proof (translation)
Take `⟨c1, c2, -, -⟩` from `complex_parts_mem_lie_algebra_holds n ε Z`. Unfold `Ec`. Rewrite using `[rd_add h₁ h₂ c1 hx, rd_add h₁ h₂ c2 hx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ec_add {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h₁ : SmoothOnG ε G₁) (h₂ : SmoothOnG ε G₂) (Z : Matrix (Fin n) (Fin n) ℂ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : inUJ ε x) : Ec ε Z (G₁ + G₂) x = Ec ε Z G₁ x + Ec ε Z G₂ x := by
  obtain ⟨c1, c2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε Z
  unfold Ec
  rw [rd_add h₁ h₂ c1 hx, rd_add h₁ h₂ c2 hx]
  ring

/- English proof (translation)
Unfold `Ec`. Rewrite using `[rd_smul, rd_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ec_smul {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (Z x : Matrix (Fin n) (Fin n) ℂ) : Ec ε Z (c • G) x = c * Ec ε Z G x := by
  unfold Ec
  rw [rd_smul, rd_smul]
  ring

def V (ε : Fin n → Bool) (m : ℤ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  carrier := {G | SmoothOnG ε G ∧ Cent ε m G}
  add_mem' := by
    rintro G₁ G₂ ⟨s1, c1⟩ ⟨s2, c2⟩
    refine ⟨smoothOnG_add s1 s2, fun z hz x hx => ?_⟩
    simp only [Pi.add_apply, c1 z hz x hx, c2 z hz x hx]
    ring
  zero_mem' := ⟨smoothOnG_zero ε, fun z hz x hx => by simp⟩
  smul_mem' := by
    rintro c G ⟨s, cG⟩
    refine ⟨smoothOnG_smul c s, fun z hz x hx => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, cG z hz x hx]
    ring

open Classical in

def trunc (ε : Fin n → Bool) (G : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun x => if inUJ ε x then G x else 0

/- English proof (translation)
Simplify using `[trunc, hx]`.
-/
theorem trunc_of {ε : Fin n → Bool} (G : Matrix (Fin n) (Fin n) ℂ → ℂ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : inUJ ε x) : trunc ε G x = G x := by
  simp [trunc, hx]

/- English proof (translation)
Simplify using `[trunc, hx]`.
-/
theorem trunc_not {ε : Fin n → Bool} (G : Matrix (Fin n) (Fin n) ℂ → ℂ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : ¬ inUJ ε x) : trunc ε G x = 0 := by
  simp [trunc, hx]

/- English proof (translation)
Use `⟨fun g₀ hg₀ => ?_, fun z hz x hx => ?_⟩` and prove the remaining obligations. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hs g₀ hg₀`. Conclude with `⟨U, F, hU, hgU, hF, fun g hg hgJ => by rw [trunc_of G hgJ, hfF g hg hgJ]⟩`. Rewrite using `[trunc_of G hx, trunc_of G (inUJ_smul hz hx), hc z hz x hx]`.
-/
theorem trunc_mem {ε : Fin n → Bool} {m : ℤ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hs : SmoothOnG ε G)
    (hc : Cent ε m G) : trunc ε G ∈ V ε m := by
  refine ⟨fun g₀ hg₀ => ?_, fun z hz x hx => ?_⟩
  · obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hs g₀ hg₀
    exact ⟨U, F, hU, hgU, hF, fun g hg hgJ => by rw [trunc_of G hgJ, hfF g hg hgJ]⟩
  · rw [trunc_of G hx, trunc_of G (inUJ_smul hz hx), hc z hz x hx]

def T (ε : Fin n → Bool) (m : ℤ) (a b : Fin n) : Module.End ℂ (V ε m) where
  toFun G := ⟨trunc ε (Ec ε (E0 a b) G.1), trunc_mem (ec_smooth G.2.1 _) (ec_cent G.2.2 _)⟩
  map_add' G₁ G₂ := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_add, Pi.add_apply]
    by_cases hx : inUJ ε x
    · rw [trunc_of _ hx, trunc_of _ hx, trunc_of _ hx]
      exact ec_add G₁.2.1 G₂.2.1 _ hx
    · rw [trunc_not _ hx, trunc_not _ hx, trunc_not _ hx, add_zero]
  map_smul' c G := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    by_cases hx : inUJ ε x
    · rw [trunc_of _ hx, trunc_of _ hx]
      exact ec_smul c _ x
    · rw [trunc_not _ hx, trunc_not _ hx, mul_zero]

/- English proof (translation)
The claim follows from `trunc_of _ hx`.
-/
theorem T_apply {ε : Fin n → Bool} {m : ℤ} (a b : Fin n) (G : V ε m) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : inUJ ε x) : ((T ε m a b G : V ε m) : Matrix (Fin n) (Fin n) ℂ → ℂ) x = Ec ε (E0 a b) G.1 x :=
  trunc_of _ hx

def Sop (ε : Fin n → Bool) (m : ℤ) (p : Fin n × Fin n) : Module.End ℂ (V ε m) :=
  T ε m p.1 p.2 + if p.1 = p.2 then algebraMap ℂ (Module.End ℂ (V ε m)) ((m : ℂ) / n) else 0

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => intro x _`. Both sides reduce to the same expression. Consider the case `cons p w ih`. Introduce `x hx`.

Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply]`. Generalize the expression as in `hH : (w.map (Sop ε m)).prod G = H at ih ⊢`. Use `show Eab ε p.1 p.2 (Eword ε w G.1) x = _`. Establish `e2 : Eab ε p.1 p.2 (Eword ε w G.1) x = Eab ε p.1 p.2 H.1 x` using `ec_congr ih _ hx`. Rewrite using `[e2, GlobalTheory.T.matrixUnitDeriv_eq_traceFree_add_degree n hn ε m H.1 H.2.1 H.2.2 p.1 p.2 x hx]`.

Unfold `Sop`. Rewrite using `[LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, T_apply _ _ _ hx]`. Distinguish the cases in `h : p.1 = p.2`. Rewrite using `[if_pos h, if_pos h, Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[if_neg h, if_neg h, LinearMap.zero_apply, Submodule.coe_zero, Pi.zero_apply, zero_mul]`.
-/
theorem eword_eval (hn : 1 ≤ n) (ε : Fin n → Bool) (m : ℤ) (w : List (Fin n × Fin n)) (G : V ε m) :
    ∀ x, inUJ ε x → Eword ε w G.1 x = (((w.map (Sop ε m)).prod G : V ε m) : _ → ℂ) x := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    generalize hH : (w.map (Sop ε m)).prod G = H at ih ⊢
    show Eab ε p.1 p.2 (Eword ε w G.1) x = _
    have e2 : Eab ε p.1 p.2 (Eword ε w G.1) x = Eab ε p.1 p.2 H.1 x := ec_congr ih _ hx
    rw [e2, GlobalTheory.T.matrixUnitDeriv_eq_traceFree_add_degree n hn ε m H.1 H.2.1 H.2.2 p.1 p.2 x hx]
    unfold Sop
    rw [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, T_apply _ _ _ hx]
    by_cases h : p.1 = p.2
    · rw [if_pos h, if_pos h, Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    · rw [if_neg h, if_neg h, LinearMap.zero_apply, Submodule.coe_zero, Pi.zero_apply, zero_mul]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => intro x _`. Both sides reduce to the same expression. Consider the case `cons p w ih`. Introduce `x hx`.

Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply]`. Generalize the expression as in `hH : (w.map (fun p => T ε m p.1 p.2)).prod G = H at ih ⊢`. Use `show Ec ε (E0 p.1 p.2) (EwordS ε w G.1) x = _`. Rewrite using `[ec_congr ih _ hx, T_apply _ _ _ hx]`.
-/
theorem ewordS_eval (ε : Fin n → Bool) (m : ℤ) (w : List (Fin n × Fin n)) (G : V ε m) :
    ∀ x, inUJ ε x → EwordS ε w G.1 x =
      (((w.map (fun p => T ε m p.1 p.2)).prod G : V ε m) : _ → ℂ) x := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    generalize hH : (w.map (fun p => T ε m p.1 p.2)).prod G = H at ih ⊢
    show Ec ε (E0 p.1 p.2) (EwordS ε w G.1) x = _
    rw [ec_congr ih _ hx, T_apply _ _ _ hx]

/- English proof (translation)
Rewrite using `[LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]`. Conclude with `Finset.sum_congr rfl fun a _ => ewordS_eval ε m _ G x hx`.
-/
theorem gelfS_eval (ε : Fin n → Bool) (m : ℤ) (j : ℕ) (G : V ε m) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : inUJ ε x) : gelfS ε j G.1 x = (((∑ a : Fin (j + 1) → Fin n,
      ((cycWord a).map (fun p => T ε m p.1 p.2)).prod) G : V ε m) : _ → ℂ) x := by
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => ewordS_eval ε m _ G x hx

/- English proof (translation)
Establish `e1 : gelf ε k G.1 x = (((∑ a : Fin (k + 1) → Fin n, ((cycWord a).map (Sop ε m)).prod) G : V ε m) : _ → ℂ) x`. Rewrite using `[LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]`. Conclude with `Finset.sum_congr rfl fun a _ => eword_eval hn ε m _ G x hx`. Establish `hL` using `GlobalTheory.T.prod_shifted_cyclic_word_expansion (Module.End ℂ (V ε m)) n (T ε m) ((m : ℂ) / n) k`. Rewrite using `[e1]`.

Unfold `Sop`. Rewrite using `[hL]`. Simplify using `only [gelfS_eval ε m _ G hx, LinearMap.add_apply, Module.algebraMap_end_apply, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]`.
-/
theorem gelf_eval (hn : 1 ≤ n) (ε : Fin n → Bool) (m : ℤ) (k : ℕ) (G : V ε m)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : inUJ ε x) :
    gelf ε k G.1 x = ((m : ℂ) / n) ^ (k + 1) * n * G.1 x + ∑ j ∈ range (k + 1),
      ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k - j) * gelfS ε j G.1 x := by
  have e1 : gelf ε k G.1 x = (((∑ a : Fin (k + 1) → Fin n, ((cycWord a).map (Sop ε m)).prod) G : V ε m) :
      _ → ℂ) x := by
    rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => eword_eval hn ε m _ G x hx
  have hL := GlobalTheory.T.prod_shifted_cyclic_word_expansion (Module.End ℂ (V ε m)) n (T ε m) ((m : ℂ) / n) k
  rw [e1]
  unfold Sop
  rw [hL]
  simp only [gelfS_eval ε m _ G hx, LinearMap.add_apply, Module.algebraMap_end_apply, LinearMap.sum_apply,
    Module.End.mul_apply, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h`. Consider the case `cons p w ih => exact ec_cent ih _`.
-/
theorem ewordS_cent {ε : Fin n → Bool} {m : ℤ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : Cent ε m G)
    (w : List (Fin n × Fin n)) : Cent ε m (EwordS ε w G) := by
  induction w with
  | nil => exact h
  | cons p w ih => exact ec_cent ih _

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact h`. Consider the case `cons p w ih => exact GlobalTheory.T.traceFreeDeriv_congr_on_unitaryGroup n ε _ _ p.1 p.2 ih`.
-/
theorem ewordS_SU {ε : Fin n → Bool} {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g ∈ SUset ε, G₁ g = G₂ g) (w : List (Fin n × Fin n)) :
    ∀ g ∈ SUset ε, EwordS ε w G₁ g = EwordS ε w G₂ g := by
  induction w with
  | nil => exact h
  | cons p w ih => exact GlobalTheory.T.traceFreeDeriv_congr_on_unitaryGroup n ε _ _ p.1 p.2 ih

/- English proof (translation)
Introduce `n hn ε m f f' hff' hs'`. Establish `hsm : SmoothOnG ε f` using `GlobalTheory.T.smooth_on_group_of_special n hn ε m f f' hff' hs'`. Use `⟨hsm, ?_⟩` and prove the remaining obligations. Establish `hcent : Cent ε m f`. Introduce `z hz x hx`.

Take `⟨w, hw, g₀, hg₀, rfl, -⟩` from `(GlobalTheory.T.unitary_to_special_unitary_local n hn ε).1 x hx`. Rewrite using `[smul_smul, hff' (z * w) (by rw [norm_mul, hz, hw, one_mul]) g₀ hg₀, hff' w hw g₀ hg₀, mul_zpow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfg : ∀ g ∈ SUset ε, f g = f' g` using `fun g hg => by`. Simplify using `using hff' 1 (by simp) g hg`.

Introduce `k z hz g hg`. Establish `hgU : inUJ ε g` using `hg.1`. Establish `hx : inUJ ε (z • g)` using `inUJ_smul hz hgU`. Establish `e` using `gelf_eval hn ε m k ⟨f, hsm, hcent⟩ hx`. Simplify using `only at e`.

Rewrite using `[e]`. Establish `hgS : ∀ j, gelfS ε j f (z • g) = z ^ m * gelfS ε j f' g`. Introduce `j`. Simplify using `only [gelfS, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[ewordS_cent hcent _ z hz g hgU, ewordS_SU hfg _ g hg]`. Simplify using `only [hgS, hff' z hz g hg, mul_add, Finset.mul_sum]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gelf_central : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, f (z • g) = z ^ m * f' g) → SmoothS ε f' → SmoothOnG ε f ∧ ∀ (k : ℕ) (z : ℂ), ‖z‖ = 1 → ∀ g ∈ SUset ε, gelf ε k f (z • g) = z ^ m * (((m : ℂ) / n) ^ (k + 1) * n * f' g + ∑ j ∈ range (k + 1), ((k + 1).choose (j + 1) : ℂ) * ((m : ℂ) / n) ^ (k - j) * gelfS ε j f' g) := by
  intro n hn ε m f f' hff' hs'
  have hsm : SmoothOnG ε f := GlobalTheory.T.smooth_on_group_of_special n hn ε m f f' hff' hs'
  refine ⟨hsm, ?_⟩
  have hcent : Cent ε m f := by
    intro z hz x hx
    obtain ⟨w, hw, g₀, hg₀, rfl, -⟩ := (GlobalTheory.T.unitary_to_special_unitary_local n hn ε).1 x hx
    rw [smul_smul, hff' (z * w) (by rw [norm_mul, hz, hw, one_mul]) g₀ hg₀, hff' w hw g₀ hg₀, mul_zpow]
    ring
  have hfg : ∀ g ∈ SUset ε, f g = f' g := fun g hg => by
    simpa using hff' 1 (by simp) g hg
  intro k z hz g hg
  have hgU : inUJ ε g := hg.1
  have hx : inUJ ε (z • g) := inUJ_smul hz hgU
  have e := gelf_eval hn ε m k ⟨f, hsm, hcent⟩ hx
  simp only at e
  rw [e]
  have hgS : ∀ j, gelfS ε j f (z • g) = z ^ m * gelfS ε j f' g := by
    intro j
    simp only [gelfS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ewordS_cent hcent _ z hz g hgU, ewordS_SU hfg _ g hg]
  simp only [hgS, hff' z hz g hg, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    ring

end GlobalTheory.GelfCentral

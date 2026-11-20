import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCompose
import Formalism.FormalDegreeBessel.FinalG

open Matrix Set
open scoped ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

/- English proof (translation)
Introduce `g hg` and use `hf g (h hg)`.
-/
theorem ck_mono_set {m : ℕ∞} {UU VV : Set (Mat k r)} (h : UU ⊆ VV) {f : Mat k r → E₁} (hf : CkOn m VV f) :
    CkOn m UU f := fun g hg => hf g (h hg)

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, a', hU, hgU, hc, hff⟩` from `ha g₀ hg₀`. Take `⟨U₂, Φ', hU₂, hgU₂, hc₂, hff₂⟩` from `hΦ g₀ hg₀`. Use `⟨U ∩ U₂, fun g => a' g (Φ' g), hU.inter hU₂, ⟨hgU, hgU₂⟩, ?_, fun g hg hgG => by simp only [hff g hg.1 hgG, hff₂ g hg.2 hgG]⟩` and prove the remaining obligations. Establish `h1 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun g => ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ (a' g)) (U ∩ U₂)` using `(ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ).contDiff.comp_contDiffOn (hc.mono Set.inter_subset_left)`.

Conclude with `h1.clm_apply (hc₂.mono Set.inter_subset_right)`.
-/
theorem ck_ap {m : ℕ∞} {UU : Set (Mat k r)} {a : Mat k r → (E₁ →L[ℂ] E₂)} {Φ : Mat k r → E₁}
    (ha : CkOn m UU a) (hΦ : CkOn m UU Φ) : CkOn m UU (fun g => a g (Φ g)) := by
  intro g₀ hg₀
  obtain ⟨U, a', hU, hgU, hc, hff⟩ := ha g₀ hg₀
  obtain ⟨U₂, Φ', hU₂, hgU₂, hc₂, hff₂⟩ := hΦ g₀ hg₀
  refine ⟨U ∩ U₂, fun g => a' g (Φ' g), hU.inter hU₂, ⟨hgU, hgU₂⟩, ?_,
    fun g hg hgG => by simp only [hff g hg.1 hgG, hff₂ g hg.2 hgG]⟩
  have h1 : ContDiffOn ℝ (m : WithTop ℕ∞)
      (fun g => ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ (a' g)) (U ∩ U₂) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ).contDiff.comp_contDiffOn
      (hc.mono Set.inter_subset_left)
  exact h1.clm_apply (hc₂.mono Set.inter_subset_right)

/- English proof (translation)
Rewrite using `[← Dw_wR]`. Apply `CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) hw x (by simpa [wL] using hx))` to reduce the goal to its premises. Establish `e : (wR w).length = w.length` using `by simp [wR]`. Rewrite using `[e]`. Conclude with `hf`.
-/
theorem ck_Rw' {m : ℕ∞} {UU : Set (Mat k r)} {w : List (Mat k r)} (hw : ∀ X ∈ w, inLie k r X)
    {f : Mat k r → E₁} (hf : CkOn (m + w.length) UU f) : CkOn m UU (Rw w f) := by
  rw [← Dw_wR]
  apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) hw x (by simpa [wL] using hx))
  have e : (wR w).length = w.length := by simp [wR]
  rw [e]; exact hf

/- English proof (translation)
Take `⟨U, F, hU, hgU, hc, he⟩` from `hJ g₀ hg₀`. Take `⟨ρ, hρ, hball⟩` from `Metric.isOpen_iff.1 hU g₀ hgU`. Set `bb : ContDiffBump g₀` to `⟨ρ / 4, ρ / 2, by positivity, by linarith⟩`. Use `⟨fun x => (bb x : ℝ) • F x, Metric.ball g₀ (ρ / 4), ?_, Metric.isOpen_ball, Metric.mem_ball_self (by positivity), fun x hx hxG => ?_⟩` and prove the remaining obligations. Introduce `y _`.

Distinguish the cases in `hy : y ∈ Metric.closedBall g₀ (ρ / 2)`. Use `⟨U, fun x => (bb x : ℝ) • F x, hU, hball (Metric.closedBall_subset_ball (by linarith) hy), ?_, fun _ _ _ => rfl⟩` and prove the remaining obligations. Conclude with `((bb.contDiff (n := ⊤)).of_le (by exact_mod_cast le_top)).contDiffOn.smul hc`. Use `⟨(Metric.closedBall g₀ (ρ / 2))ᶜ, fun _ => 0, Metric.isClosed_closedBall.isOpen_compl, hy, contDiffOn_const, fun x hx _ => ?_⟩` and prove the remaining obligations. Establish `: bb x = 0`.

Rewrite using `[← Function.notMem_support, bb.support_eq]`. Conclude with `fun h => hx (Metric.ball_subset_closedBall h)`. Simplify using `[this]`. Establish `h1 : bb x = 1` using `bb.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)`. Establish `hxU : x ∈ U` using `hball (Metric.ball_subset_ball (by linarith) hx)`.

Simplify using `only [h1, one_smul]`. Conclude with `(he x hxU hxG).symm`.
-/
theorem ext_loc {m : ℕ∞} {UU : Set (Mat k r)} {J : Mat k r → E₁} (hJ : CkOn m UU J) {g₀ : Mat k r} (hg₀ : g₀ ∈ UU) :
    ∃ (f : Mat k r → E₁) (U : Set (Mat k r)), CkOn m (GV k r) f ∧ IsOpen U ∧ g₀ ∈ U ∧
      ∀ x ∈ U, x ∈ GV k r → f x = J x := by
  obtain ⟨U, F, hU, hgU, hc, he⟩ := hJ g₀ hg₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU g₀ hgU
  let bb : ContDiffBump g₀ := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  refine ⟨fun x => (bb x : ℝ) • F x, Metric.ball g₀ (ρ / 4), ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), fun x hx hxG => ?_⟩
  · intro y _
    by_cases hy : y ∈ Metric.closedBall g₀ (ρ / 2)
    · refine ⟨U, fun x => (bb x : ℝ) • F x, hU, hball (Metric.closedBall_subset_ball (by linarith) hy), ?_,
        fun _ _ _ => rfl⟩
      exact ((bb.contDiff (n := ⊤)).of_le (by exact_mod_cast le_top)).contDiffOn.smul hc
    · refine ⟨(Metric.closedBall g₀ (ρ / 2))ᶜ, fun _ => 0, Metric.isClosed_closedBall.isOpen_compl, hy,
        contDiffOn_const, fun x hx _ => ?_⟩
      have : bb x = 0 := by
        rw [← Function.notMem_support, bb.support_eq]
        exact fun h => hx (Metric.ball_subset_closedBall h)
      simp [this]
  · have h1 : bb x = 1 := bb.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have hxU : x ∈ U := hball (Metric.ball_subset_ball (by linarith) hx)
    simp only [h1, one_smul]
    exact (he x hxU hxG).symm

end gen

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Unfold `opApply`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `T _`. Use `congr 1`.

Rewrite using `[← Dw_wR, ← Dw_wR]`. Conclude with `Dw_congr_loc (fun x hx => by`. Simplify using `only [wR, List.mem_map] at hx`. Take `⟨X, hX, rfl⟩` from `hx`. Conclude with `T.word_lie X hX) hO h g hg hgO`.
-/
theorem op_congr (Θ : DiffOp k r Wp Wq) {O : Set (Mat k r)} (hO : IsOpen O) {H H' : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, g ∈ O → H g = H' g) {g : Mat k r} (hg : g ∈ GV k r) (hgO : g ∈ O) :
    opApply Θ H g = opApply Θ H' g := by
  unfold opApply
  congr 1
  apply List.map_congr_left
  intro T _
  congr 1
  rw [← Dw_wR, ← Dw_wR]
  exact Dw_congr_loc (fun x hx => by
    simp only [wR, List.mem_map] at hx; obtain ⟨X, hX, rfl⟩ := hx; exact T.word_lie X hX) hO h g hg hgO

/- English proof (translation)
Unfold `opApply`. Rewrite using `[List.smul_sum, List.map_map]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `T _`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[← Dw_wR, ← Dw_wR, Dw_smul, map_smul]`.
-/
theorem op_smul (Θ : DiffOp k r Wp Wq) (c : ℂ) (H : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    opApply Θ (fun x => c • H x) g = c • opApply Θ H g := by
  unfold opApply
  rw [List.smul_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro T _
  simp only [Function.comp_apply]
  rw [← Dw_wR, ← Dw_wR, Dw_smul, map_smul]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `[opApply]`.
-/
theorem op_cons (T : DTerm k r Wp Wq) (Θ : DiffOp k r Wp Wq) (J : Mat k r → (Wq →L[ℂ] Wp)) :
    opApply (T :: Θ) J = fun g => T.coef g (Rw T.word J g) + opApply Θ J g := by
  funext g; simp [opApply]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `[opApply]`.
-/
theorem op_nil (J : Mat k r → (Wq →L[ℂ] Wp)) : opApply ([] : DiffOp k r Wp Wq) J = fun _ => 0 := by
  funext g; simp [opApply]

/- English proof (translation)
The claim follows from `| [], _ => by rw [op_nil]; exact CkOn_zero | T :: Θ, h => by rw [op_cons] have hT := h T (by simp) refine CkOn_add (ck_ap (sCkOn_mono le_top hT.1) (ck_Rw' T.word_lie (sCkOn_mono ?_ hJ))) (ck_op hJ Θ (fun T' hT' => h T' (by simp [hT']))) have : (T.word.length : ℕ∞) ≤ (o : ℕ∞) := b …`.
-/
theorem ck_op {m : ℕ∞} {o : ℕ} {UU : Set (Mat k r)} {J : Mat k r → (Wq →L[ℂ] Wp)} (hJ : CkOn (m + o) UU J) :
    ∀ Θ : DiffOp k r Wp Wq, (∀ T ∈ Θ, CkOn ⊤ UU T.coef ∧ T.word.length ≤ o) → CkOn m UU (opApply Θ J)
  | [], _ => by rw [op_nil]; exact CkOn_zero
  | T :: Θ, h => by
    rw [op_cons]
    have hT := h T (by simp)
    refine CkOn_add (ck_ap (sCkOn_mono le_top hT.1) (ck_Rw' T.word_lie (sCkOn_mono ?_ hJ)))
      (ck_op hJ Θ (fun T' hT' => h T' (by simp [hT'])))
    have : (T.word.length : ℕ∞) ≤ (o : ℕ∞) := by exact_mod_cast hT.2
    exact add_le_add le_rfl this

/- English proof (translation)
Proceed by induction on `Θ with`. Consider the case `nil => simp`. Consider the case `cons T Θ ih`. Introduce `T' hT'`. Unfold `opOrder at ih ⊢`.

Simplify using `only [List.map_cons, List.foldr_cons]`. Break down `List.mem_cons.1 hT' with rfl | h` into its components or cases. Conclude with `le_max_left _ _`. Conclude with `(ih T' h).trans (le_max_right _ _)`.
-/
theorem word_le_opOrder (Θ : DiffOp k r Wp Wq) : ∀ T ∈ Θ, T.word.length ≤ opOrder Θ := by
  induction Θ with
  | nil => simp
  | cons T Θ ih =>
    intro T' hT'
    unfold opOrder at ih ⊢
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 hT' with rfl | h
    · exact le_max_left _ _
    · exact (ih T' h).trans (le_max_right _ _)

/- English proof (translation)
Unfold `opOrder`. Proceed by induction on `Θ with`. Consider the case `nil => simp`. Consider the case `cons T Θ ih`. Simplify using `only [List.map_cons, List.foldr_cons]`.

Conclude with `max_le (h T (by simp)) (ih fun T' hT' => h T' (by simp [hT']))`.
-/
theorem opOrder_le (Θ : DiffOp k r Wp Wq) {n : ℕ} (h : ∀ T ∈ Θ, T.word.length ≤ n) : opOrder Θ ≤ n := by
  unfold opOrder
  induction Θ with
  | nil => simp
  | cons T Θ ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h T (by simp)) (ih fun T' hT' => h T' (by simp [hT']))

/- English proof (translation)
Unfold `sgs`. Conclude with `((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_mul continuous_const`.
-/
theorem sgs_cont (p : SS k r) : Continuous (sgs p) := by
  unfold sgs
  exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_mul continuous_const

/- English proof (translation)
The claim follows from `gv_mul (gv_mul (gv_mul (gv_mul (gv_inv hp.1.1) (gv_inv hp.2.1.1)) hg) hp.2.2.2.1) hp.2.2.1.1`.
-/
theorem sgs_gv (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {g : Mat k r} (hg : g ∈ GV k r) :
    sgs p g ∈ GV k r :=
  gv_mul (gv_mul (gv_mul (gv_mul (gv_inv hp.1.1) (gv_inv hp.2.1.1)) hg) hp.2.2.2.1) hp.2.2.1.1

/- English proof (translation)
Take `⟨f, U, hf, hU, hgU, he⟩` from `ext_loc hJ hgV`. Establish `e1 : opApply Θ (rho D p J) g = opApply Θ (rho D p f) g` using `op_congr Θ (hU.preimage (sgs_cont p)) (fun x hx hxU => by`. Simplify using `only [rho]`. Rewrite using `[he _ hxU (sgs_gv D hp hx)]) hgG hgU`. Establish `e2 : opApply Θ f (sgs p g) = opApply Θ J (sgs p g)` using `op_congr Θ hU (fun x hx hxU => he x hxU hx) (sgs_gv D hp hgG) hgU`.

Rewrite using `[e1, hC p hp f hf g hg]`. Simplify using `only [rho]`. Rewrite using `[e2]`.
-/
theorem commutes_loc (D : RealPlaceData k r Wp Wq) {UU : Set (Mat k r)} {Θ : DiffOp k r Wp Wq} (hC : Commutes D UU Θ)
    {p : SS k r} (hp : D.inSS p) {VV : Set (Mat k r)} {J : Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : CkOn (opOrder Θ : ℕ∞) VV J) {g : Mat k r} (hg : g ∈ UU) (hgG : g ∈ GV k r) (hgV : sgs p g ∈ VV) :
    opApply Θ (rho D p J) g = rho D p (opApply Θ J) g := by
  obtain ⟨f, U, hf, hU, hgU, he⟩ := ext_loc hJ hgV
  have e1 : opApply Θ (rho D p J) g = opApply Θ (rho D p f) g :=
    op_congr Θ (hU.preimage (sgs_cont p)) (fun x hx hxU => by
      simp only [rho]; rw [he _ hxU (sgs_gv D hp hx)]) hgG hgU
  have e2 : opApply Θ f (sgs p g) = opApply Θ J (sgs p g) :=
    op_congr Θ hU (fun x hx hxU => he x hxU hx) (sgs_gv D hp hgG) hgU
  rw [e1, hC p hp f hf g hg]
  simp only [rho]
  rw [e2]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h.1, fun hg => ⟨hg, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩⟩`.
-/
theorem level_zero_iff (g : Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ GV k r :=
  ⟨fun h => h.1, fun hg => ⟨hg, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩⟩

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hc, he⟩` from `hJ g₀ ⟨(level_zero_iff _).2 hg₀.1, hg₀.2⟩`. Conclude with `⟨U, F, hU, hgU, hc, fun g hg hgG => he g hg ((level_zero_iff _).2 hgG)⟩`.
-/
theorem ck_of_smoothLev {E₁ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] {O : Set (Mat k r)} {J : Mat k r → E₁}
    (hJ : Q.SmoothLev k r 0 O J) : CkOn ⊤ (GV k r ∩ O) J := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hc, he⟩ := hJ g₀ ⟨(level_zero_iff _).2 hg₀.1, hg₀.2⟩
  exact ⟨U, F, hU, hgU, hc, fun g hg hgG => he g hg ((level_zero_iff _).2 hgG)⟩

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hc, he⟩` from `hJ g₀ ⟨hg₀.1.1, hg₀.2⟩`. Conclude with `⟨U, F, hU, hgU, hc, fun g hg hgG => he g hg hgG.1⟩`.
-/
theorem smoothLev_of_ck {E₁ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] {O : Set (Mat k r)} {J : Mat k r → E₁}
    (hJ : CkOn ⊤ (GV k r ∩ O) J) : Q.SmoothLev k r 0 O J := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hc, he⟩ := hJ g₀ ⟨hg₀.1.1, hg₀.2⟩
  exact ⟨U, F, hU, hgU, hc, fun g hg hgG => he g hg hgG.1⟩

def mkSS (a b c d : Mat k r) : SS k r := ((a, b), (c, d))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sgs_mk (a b c d g : Mat k r) : sgs (mkSS a b c d) g = a⁻¹ * b⁻¹ * g * d * c := rfl

omit [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rho_mk (D : RealPlaceData k r Wp Wq) (a b c d : Mat k r) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    rho D (mkSS a b c d) F g = (D.π a).comp ((F (sgs (mkSS a b c d) g)).comp (D.π' c⁻¹)) := rfl

omit [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨ha, hb, hc, hd⟩`.
-/
theorem inSS_mk (D : RealPlaceData k r Wp Wq) {a b c d : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ Nset k r)
    (hc : c ∈ UWset k r D.z') (hd : d ∈ Nset k r) : D.inSS (mkSS a b c d) := ⟨ha, hb, hc, hd⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨gv_one, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩`.
-/
theorem uw_one (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat k r) ∈ UWset k r z :=
  ⟨gv_one, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩

/- English proof (translation)
Establish `hJc : CkOn ⊤ (GV k r ∩ O) J` using `ck_of_smoothLev hJ.1`. Establish `n1 : (1 : Mat k r) ∈ Nset k r` using `(Formalism.QuantumDeterminants.nSubgroup k r).1`. Establish `n1' : (1 : Mat k r) ∈ Q.Nlev k r 0` using `⟨n1, (level_zero_iff _).2 gv_one⟩`. Establish `key : ∀ (p : SS k r), D.inSS p → ∀ c : ℂ, (∀ x ∈ GV k r, x ∈ O → rho D p J x = c • J x) → ∀ g ∈ GV k r, g ∈ O → sgs p g ∈ O → rho D p (opApply Θ J) g = c • opApply Θ J g`. Introduce `p hp c hc g hg hgO hsO`.

Rewrite using `[← commutes_loc D hC hp (sCkOn_mono le_top hJc) (hOU g hgO hg) hg ⟨sgs_gv D hp hg, hsO⟩, op_congr Θ hO.1 hc hg hgO, op_smul]`. Establish `hπ1 : D.π 1 = ContinuousLinearMap.id ℂ Wp` using `D.π_rep.1`. Establish `hπ1' : D.π' 1 = ContinuousLinearMap.id ℂ Wq` using `D.π'_rep.1`. Use `⟨smoothLev_of_ck (ck_op (m := ⊤) (o := opOrder Θ) (by rw [top_add]; exact hJc) Θ fun T hT => ⟨ck_mono_set (fun g hg => hOU g hg.2 hg.1) (hS T hT), word_le_opOrder Θ T hT⟩), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg n hn`.

Establish `hni : n⁻¹ ∈ Nset k r` using `(Formalism.QuantumDeterminants.nSubgroup k r).2.2 _ hn.1`. Set `p : SS k r` to `mkSS 1 n⁻¹ 1 1`. Establish `hp : D.inSS p` using `inSS_mk D (uw_one _) hni (uw_one _) n1`. Establish `hs : ∀ x, sgs p x = n * x` using `fun x => by`. Rewrite using `[sgs_mk, inv_one, Matrix.nonsing_inv_nonsing_inv _ (gv_unit hn.1.1)]`.

Simplify using the standard rewrite rules. Establish `hr : ∀ (F : Mat k r → (Wq →L[ℂ] Wp)) x, rho D p F x = F (n * x)` using `fun F x => by`. Rewrite using `[rho_mk, inv_one, hπ1, hπ1', hs]`. Simplify using the standard rewrite rules. Establish `hO' : n * g ∈ O`.

Use `hO.2 g hg n ⟨1, uw_one _, n, hn, by simp⟩ 1 ⟨1, uw_one _, 1, n1', by simp⟩` as an intermediate fact. Simplify using `using this`. Rewrite using `[← hr (opApply Θ J) g]`. Conclude with `key p hp _ (fun x hx hxO => by rw [hr]; exact hJ.2.1 x ⟨(level_zero_iff _).2 hx, hxO⟩ n hn) g hg.1.1 hg.2 (by rw [hs]; exact hO')`. Introduce `g hg n hn`.

Set `p : SS k r` to `mkSS 1 1 1 n`. Establish `hp : D.inSS p` using `inSS_mk D (uw_one _) n1 (uw_one _) hn.1`. Establish `hs : ∀ x, sgs p x = x * n` using `fun x => by`. Rewrite using `[sgs_mk, inv_one]`. Simplify using the standard rewrite rules.

Establish `hr : ∀ (F : Mat k r → (Wq →L[ℂ] Wp)) x, rho D p F x = F (x * n)` using `fun F x => by`. Rewrite using `[rho_mk, inv_one, hπ1, hπ1', hs]`. Simplify using the standard rewrite rules. Establish `hO' : g * n ∈ O`. Use `hO.2 g hg 1 ⟨1, uw_one _, 1, n1', by simp⟩ n ⟨1, uw_one _, n, hn, by simp⟩` as an intermediate fact.

Simplify using `using this`. Rewrite using `[← hr (opApply Θ J) g]`. Conclude with `key p hp _ (fun x hx hxO => by rw [hr]; exact hJ.2.2.1 x ⟨(level_zero_iff _).2 hx, hxO⟩ n hn) g hg.1.1 hg.2 (by rw [hs]; exact hO')`. Introduce `g hg h hh h' hh'`. Establish `hi : h⁻¹ ∈ UWset k r D.z` using `Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh`.

Establish `hi' : h'⁻¹ ∈ UWset k r D.z'` using `Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh'`. Set `p : SS k r` to `mkSS h⁻¹ 1 h' 1`. Establish `hp : D.inSS p` using `inSS_mk D hi n1 hh' n1`. Establish `hs : ∀ x, sgs p x = h * x * h'` using `fun x => by`. Rewrite using `[sgs_mk, inv_one, Matrix.nonsing_inv_nonsing_inv _ (gv_unit hh.1)]`.

Simplify using the standard rewrite rules. Establish `hr : ∀ (F : Mat k r → (Wq →L[ℂ] Wp)) x, rho D p F x = (D.π h⁻¹).comp ((F (h * x * h')).comp (D.π' h'⁻¹))` using `fun F x => by`. Rewrite using `[rho_mk, hs]`. Establish `a1 : (D.π h⁻¹).comp (D.π h) = ContinuousLinearMap.id ℂ Wp`. Rewrite using `[← D.π_rep.2 _ hi _ hh, Matrix.nonsing_inv_mul _ (gv_unit hh.1), hπ1]`.

Establish `a2 : (D.π h).comp (D.π h⁻¹) = ContinuousLinearMap.id ℂ Wp`. Rewrite using `[← D.π_rep.2 _ hh _ hi, Matrix.mul_nonsing_inv _ (gv_unit hh.1), hπ1]`. Establish `b1 : (D.π' h'⁻¹).comp (D.π' h') = ContinuousLinearMap.id ℂ Wq`. Rewrite using `[← D.π'_rep.2 _ hi' _ hh', Matrix.nonsing_inv_mul _ (gv_unit hh'.1), hπ1']`. Establish `b2 : (D.π' h').comp (D.π' h'⁻¹) = ContinuousLinearMap.id ℂ Wq`.

Rewrite using `[← D.π'_rep.2 _ hh' _ hi', Matrix.mul_nonsing_inv _ (gv_unit hh'.1), hπ1']`. Establish `hO' : h * g * h' ∈ O` using `hO.2 g hg h ⟨h, hh, 1, n1', by simp⟩ h' ⟨h', hh', 1, n1', by simp⟩`. Establish `k1` using `key p hp 1 (fun x hx hxO => by`. Rewrite using `[hr, hJ.2.2.2 x ⟨(level_zero_iff _).2 hx, hxO⟩ h hh h' hh', one_smul, ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, a1, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc, b2, ContinuousLinearMap.comp_id]) g hg.1.1 hg.2 (by rw [hs]; exact hO')`. Rewrite `k1` using `[hr, one_smul]`.

Rewrite using `[← k1, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, b1, ContinuousLinearMap.comp_id, ← ContinuousLinearMap.comp_assoc, a2, ContinuousLinearMap.id_comp]`.
-/
theorem ffl_opApply (D : RealPlaceData k r Wp Wq) {O UU : Set (Mat k r)} (hO : Q.IsDom k r D.z D.z' 0 O)
    (hOU : ∀ g ∈ O, g ∈ GV k r → g ∈ UU) {Θ : DiffOp k r Wp Wq} (hS : ∀ T ∈ Θ, CkOn ⊤ UU T.coef)
    (hC : Commutes D UU Θ) {J : Mat k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 O) :
    opApply Θ J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 O := by
  have hJc : CkOn ⊤ (GV k r ∩ O) J := ck_of_smoothLev hJ.1
  have n1 : (1 : Mat k r) ∈ Nset k r := (Formalism.QuantumDeterminants.nSubgroup k r).1
  have n1' : (1 : Mat k r) ∈ Q.Nlev k r 0 := ⟨n1, (level_zero_iff _).2 gv_one⟩
  have key : ∀ (p : SS k r), D.inSS p → ∀ c : ℂ, (∀ x ∈ GV k r, x ∈ O → rho D p J x = c • J x) →
      ∀ g ∈ GV k r, g ∈ O → sgs p g ∈ O → rho D p (opApply Θ J) g = c • opApply Θ J g := by
    intro p hp c hc g hg hgO hsO
    rw [← commutes_loc D hC hp (sCkOn_mono le_top hJc) (hOU g hgO hg) hg ⟨sgs_gv D hp hg, hsO⟩,
      op_congr Θ hO.1 hc hg hgO, op_smul]
  have hπ1 : D.π 1 = ContinuousLinearMap.id ℂ Wp := D.π_rep.1
  have hπ1' : D.π' 1 = ContinuousLinearMap.id ℂ Wq := D.π'_rep.1
  refine ⟨smoothLev_of_ck (ck_op (m := ⊤) (o := opOrder Θ) (by rw [top_add]; exact hJc) Θ fun T hT =>
    ⟨ck_mono_set (fun g hg => hOU g hg.2 hg.1) (hS T hT), word_le_opOrder Θ T hT⟩), ?_, ?_, ?_⟩
  · intro g hg n hn
    have hni : n⁻¹ ∈ Nset k r := (Formalism.QuantumDeterminants.nSubgroup k r).2.2 _ hn.1
    let p : SS k r := mkSS 1 n⁻¹ 1 1
    have hp : D.inSS p := inSS_mk D (uw_one _) hni (uw_one _) n1
    have hs : ∀ x, sgs p x = n * x := fun x => by
      rw [sgs_mk, inv_one, Matrix.nonsing_inv_nonsing_inv _ (gv_unit hn.1.1)]; simp
    have hr : ∀ (F : Mat k r → (Wq →L[ℂ] Wp)) x, rho D p F x = F (n * x) := fun F x => by
      rw [rho_mk, inv_one, hπ1, hπ1', hs]; simp
    have hO' : n * g ∈ O := by
      have := hO.2 g hg n ⟨1, uw_one _, n, hn, by simp⟩ 1 ⟨1, uw_one _, 1, n1', by simp⟩
      simpa using this
    rw [← hr (opApply Θ J) g]
    exact key p hp _ (fun x hx hxO => by rw [hr]; exact hJ.2.1 x ⟨(level_zero_iff _).2 hx, hxO⟩ n hn) g hg.1.1 hg.2
      (by rw [hs]; exact hO')
  · intro g hg n hn
    let p : SS k r := mkSS 1 1 1 n
    have hp : D.inSS p := inSS_mk D (uw_one _) n1 (uw_one _) hn.1
    have hs : ∀ x, sgs p x = x * n := fun x => by
      rw [sgs_mk, inv_one]; simp
    have hr : ∀ (F : Mat k r → (Wq →L[ℂ] Wp)) x, rho D p F x = F (x * n) := fun F x => by
      rw [rho_mk, inv_one, hπ1, hπ1', hs]; simp
    have hO' : g * n ∈ O := by
      have := hO.2 g hg 1 ⟨1, uw_one _, 1, n1', by simp⟩ n ⟨1, uw_one _, n, hn, by simp⟩
      simpa using this
    rw [← hr (opApply Θ J) g]
    exact key p hp _ (fun x hx hxO => by rw [hr]; exact hJ.2.2.1 x ⟨(level_zero_iff _).2 hx, hxO⟩ n hn) g hg.1.1 hg.2
      (by rw [hs]; exact hO')
  · intro g hg h hh h' hh'
    have hi : h⁻¹ ∈ UWset k r D.z := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh
    have hi' : h'⁻¹ ∈ UWset k r D.z' := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh'
    let p : SS k r := mkSS h⁻¹ 1 h' 1
    have hp : D.inSS p := inSS_mk D hi n1 hh' n1
    have hs : ∀ x, sgs p x = h * x * h' := fun x => by
      rw [sgs_mk, inv_one, Matrix.nonsing_inv_nonsing_inv _ (gv_unit hh.1)]; simp
    have hr : ∀ (F : Mat k r → (Wq →L[ℂ] Wp)) x,
        rho D p F x = (D.π h⁻¹).comp ((F (h * x * h')).comp (D.π' h'⁻¹)) := fun F x => by
      rw [rho_mk, hs]
    have a1 : (D.π h⁻¹).comp (D.π h) = ContinuousLinearMap.id ℂ Wp := by
      rw [← D.π_rep.2 _ hi _ hh, Matrix.nonsing_inv_mul _ (gv_unit hh.1), hπ1]
    have a2 : (D.π h).comp (D.π h⁻¹) = ContinuousLinearMap.id ℂ Wp := by
      rw [← D.π_rep.2 _ hh _ hi, Matrix.mul_nonsing_inv _ (gv_unit hh.1), hπ1]
    have b1 : (D.π' h'⁻¹).comp (D.π' h') = ContinuousLinearMap.id ℂ Wq := by
      rw [← D.π'_rep.2 _ hi' _ hh', Matrix.nonsing_inv_mul _ (gv_unit hh'.1), hπ1']
    have b2 : (D.π' h').comp (D.π' h'⁻¹) = ContinuousLinearMap.id ℂ Wq := by
      rw [← D.π'_rep.2 _ hh' _ hi', Matrix.mul_nonsing_inv _ (gv_unit hh'.1), hπ1']
    have hO' : h * g * h' ∈ O :=
      hO.2 g hg h ⟨h, hh, 1, n1', by simp⟩ h' ⟨h', hh', 1, n1', by simp⟩
    have k1 := key p hp 1 (fun x hx hxO => by
      rw [hr, hJ.2.2.2 x ⟨(level_zero_iff _).2 hx, hxO⟩ h hh h' hh', one_smul, ← ContinuousLinearMap.comp_assoc,
        ← ContinuousLinearMap.comp_assoc, a1, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc, b2,
        ContinuousLinearMap.comp_id]) g hg.1.1 hg.2 (by rw [hs]; exact hO')
    rw [hr, one_smul] at k1
    rw [← k1, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, b1, ContinuousLinearMap.comp_id,
      ← ContinuousLinearMap.comp_assoc, a2, ContinuousLinearMap.id_comp]

/- English proof (translation)
Take `⟨q, -, hq⟩` from `hP`. Establish `e : P = fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q` using `funext hq`. Rewrite using `[e]`. Use `clear hq e`. Establish `hv : ∀ i j, ContDiff ℝ ∞ (fun g : Mat k r => g i j)` using `fun i j => contDiff_apply_apply ℝ ℂ i j`.

Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simpa using contDiff_const`. Consider the case `add p q hp hq => simpa using hp.add hq`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, MvPolynomial.eval_X]`.

Use `hp.mul ?_` and prove the remaining obligations. Break down `i with x | x` into its components or cases. Conclude with `hv _ _`. Conclude with `Complex.conjCLE.contDiff.comp (hv x.1 x.2)`.
-/
theorem contDiff_poly {κ : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg κ P) : ContDiff ℝ ∞ P := by
  obtain ⟨q, -, hq⟩ := hP
  have e : P = fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q := funext hq
  rw [e]
  clear hq e
  have hv : ∀ i j, ContDiff ℝ ∞ (fun g : Mat k r => g i j) := fun i j => contDiff_apply_apply ℝ ℂ i j
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases i with x | x
    · exact hv _ _
    · exact Complex.conjCLE.contDiff.comp (hv x.1 x.2)

/- English proof (translation)
Introduce `_ _` and use `⟨Set.univ, _, isOpen_univ, Set.mem_univ _, ((contDiff_poly hP).smul contDiff_const).contDiffOn, fun _ _ _ => rfl⟩`.
-/
theorem ck_scal {κ : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg κ P) (UU : Set (Mat k r)) :
    CkOn ⊤ UU (fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) := fun _ _ =>
  ⟨Set.univ, _, isOpen_univ, Set.mem_univ _, ((contDiff_poly hP).smul contDiff_const).contDiffOn, fun _ _ _ => rfl⟩

/- English proof (translation)
Introduce `T hT`. Take `⟨-, P, hP, hc, -⟩` from `h T hT`. Establish `e : T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)` using `funext hc`. Rewrite using `[e]`. Conclude with `ck_scal hP UU`.
-/
theorem polyOp_ck {o κ : ℕ} {Θ : DiffOp k r Wp Wq} (h : CutMP.PolyOp o κ Θ) (UU : Set (Mat k r)) :
    ∀ T ∈ Θ, CkOn ⊤ UU T.coef := by
  intro T hT
  obtain ⟨-, P, hP, hc, -⟩ := h T hT
  have e : T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := funext hc
  rw [e]; exact ck_scal hP UU

def scalTerm (P : Mat k r → ℂ) (w : List (Mat k r)) (hw : ∀ X ∈ w, inLie k r X) : DTerm k r Wp Wq where
  coef g := P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  coefAdj g := star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  word := w
  word_lie := hw
  adj_id := by
    intro x A B
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hsInner,
      PI.UnitaryGroupMassFormula.UsCompose.hsVec_smul, inner_smul_right, inner_smul_left, Complex.star_def, Complex.conj_conj]

/- English proof (translation)
Take `⟨q, hq, he⟩` from `hP`. Conclude with `⟨q, hq.trans h, he⟩`.
-/
theorem polyDeg_mono {κ κ' : ℕ} (h : κ ≤ κ') {P : Mat k r → ℂ} (hP : U.IsPolyDeg κ P) : U.IsPolyDeg κ' P := by
  obtain ⟨q, hq, he⟩ := hP
  exact ⟨q, hq.trans h, he⟩

/- English proof (translation)
Introduce `T hT` and use `by obtain ⟨h1, P, hP, h2⟩ := h T hT exact ⟨h1.trans ho, P, polyDeg_mono hκ hP, h2⟩`.
-/
theorem polyOp_mono {o κ o' κ' : ℕ} (ho : o ≤ o') (hκ : κ ≤ κ') {Θ : DiffOp k r Wp Wq} (h : CutMP.PolyOp o κ Θ) :
    CutMP.PolyOp o' κ' Θ := fun T hT => by
  obtain ⟨h1, P, hP, h2⟩ := h T hT
  exact ⟨h1.trans ho, P, polyDeg_mono hκ hP, h2⟩

/- English proof (translation)
The claim follows from `| [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ => rfl⟩ | T :: Θ, h => by obtain ⟨Θ', h1, h2⟩ := exists_polyOp Θ fun T' hT' => h T' (by simp [hT']) obtain ⟨hl, P, hP, hc⟩ := h T (by simp) refine ⟨scalTerm P T.word T.word_lie :: Θ', fun T' hT' => ?_, fun F => ?_⟩ · rca …`.
-/
theorem exists_polyOp {o κ : ℕ} : ∀ Θ : DiffOp k r Wp Wq,
    (∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ P : Mat k r → ℂ, U.IsPolyDeg κ P ∧
      ∀ g, T.coef g = P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) →
    ∃ Θ' : DiffOp k r Wp Wq, CutMP.PolyOp o κ Θ' ∧ ∀ F, opApply Θ' F = opApply Θ F
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | T :: Θ, h => by
    obtain ⟨Θ', h1, h2⟩ := exists_polyOp Θ fun T' hT' => h T' (by simp [hT'])
    obtain ⟨hl, P, hP, hc⟩ := h T (by simp)
    refine ⟨scalTerm P T.word T.word_lie :: Θ', fun T' hT' => ?_, fun F => ?_⟩
    · rcases List.mem_cons.1 hT' with rfl | h'
      · exact ⟨hl, P, hP, fun _ => rfl, fun _ => rfl⟩
      · exact h1 T' h'
    · rw [op_cons, op_cons, h2]
      funext g
      rw [hc g]; rfl

/- English proof (translation)
Introduce `r hr`. Substitute `hr` using the available equality. Introduce `o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ h₁ h₂`. Establish `hD : ∀ g : Mat k (0 + ρ), U.DjU k 0 ρ g = 1` using `fun g => by`. Unfold `U.DjU`.

Conclude with `Matrix.det_isEmpty`. Establish `toDD : ∀ {o κ : ℕ} {Θ : DiffOp k (0 + ρ) Wp Wq}, CutMP.PolyOp o κ Θ → U.InDD k 0 ρ o κ Θ`. Introduce `o κ Θ h T hT`. Take `⟨hl, P, hP, hc, -⟩` from `h T hT`. Conclude with `⟨hl, P, 0, 0, hP, fun g => by rw [hc g]; simp⟩`.

Take `⟨Θ, hΘ, he⟩` from `differential_operator_compose k 0 ρ Wp Wq o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ (toDD h₁) (toDD h₂)`. Take `⟨Θ', h1, h2⟩` from `exists_polyOp (o := o₁ + o₂) (κ := κ₁ + κ₂) Θ fun T hT => by`. Take `⟨hl, P, a, b, hP, hc⟩` from `hΘ T hT`. Conclude with `⟨hl, P, by simpa using hP, fun g => by rw [hc g, hD]; simp⟩`. Conclude with `⟨Θ', h1, fun F hF g hg => by rw [h2]; exact he F hF g hg (by rw [hD]; exact one_ne_zero)⟩`.
-/
theorem comp_raw (ρ : ℕ) : ∀ (r : ℕ), r = 0 + ρ → ∀ (o₁ κ₁ o₂ κ₂ : ℕ) (Θ₁ Θ₂ : DiffOp k r Wp Wq),
    CutMP.PolyOp o₁ κ₁ Θ₁ → CutMP.PolyOp o₂ κ₂ Θ₂ →
    ∃ Θ : DiffOp k r Wp Wq, CutMP.PolyOp (o₁ + o₂) (κ₁ + κ₂) Θ ∧
      ∀ F : Mat k r → (Wq →L[ℂ] Wp), CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (GV k r) F →
        ∀ g ∈ GV k r, opApply Θ F g = opApply Θ₁ (opApply Θ₂ F) g := by
  intro r hr
  subst hr
  intro o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ h₁ h₂
  have hD : ∀ g : Mat k (0 + ρ), U.DjU k 0 ρ g = 1 := fun g => by
    unfold U.DjU; exact Matrix.det_isEmpty
  have toDD : ∀ {o κ : ℕ} {Θ : DiffOp k (0 + ρ) Wp Wq}, CutMP.PolyOp o κ Θ → U.InDD k 0 ρ o κ Θ := by
    intro o κ Θ h T hT
    obtain ⟨hl, P, hP, hc, -⟩ := h T hT
    exact ⟨hl, P, 0, 0, hP, fun g => by rw [hc g]; simp⟩
  obtain ⟨Θ, hΘ, he⟩ := differential_operator_compose k 0 ρ Wp Wq o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ (toDD h₁) (toDD h₂)
  obtain ⟨Θ', h1, h2⟩ := exists_polyOp (o := o₁ + o₂) (κ := κ₁ + κ₂) Θ fun T hT => by
    obtain ⟨hl, P, a, b, hP, hc⟩ := hΘ T hT
    exact ⟨hl, P, by simpa using hP, fun g => by rw [hc g, hD]; simp⟩
  exact ⟨Θ', h1, fun F hF g hg => by rw [h2]; exact he F hF g hg (by rw [hD]; exact one_ne_zero)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨MvPolynomial.C c, by simp, fun _ => by simp⟩`.
-/
theorem polyDeg_const (κ : ℕ) (c : ℂ) : U.IsPolyDeg κ (fun _ : Mat k r => c) :=
  ⟨MvPolynomial.C c, by simp, fun _ => by simp⟩

/- English proof (translation)
Unfold `inLie`. Simplify using the standard rewrite rules.
-/
theorem lie_zero : inLie k r (0 : Mat k r) := by unfold inLie; simp

/- English proof (translation)
Take `⟨Θ₀, hP, he⟩` from `comp_raw (k := k) (Wp := Wp) (Wq := Wq) r r (Nat.zero_add r).symm o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ h₁ h₂`. Set `Z : DTerm k r Wp Wq` to `scalTerm (fun _ => 0) (List.replicate (o₁ + o₂) 0) (fun X hX => by rw [List.eq_of_mem_replicate hX]; exact lie_zero)`. Establish `hZ : ∀ F, opApply (Z :: Θ₀) F = opApply Θ₀ F` using `fun F => by`. Rewrite using `[op_cons]`. Use function extensionality and compare the values at `g`.

Simplify using `[Z, scalTerm]`. Establish `hord : o₁ + o₂ ≤ opOrder (Z :: Θ₀)`. Use `word_le_opOrder (Z :: Θ₀) Z (by simp)` as an intermediate fact. Simplify `this` using `[Z, scalTerm]`. Establish `hloc : ∀ (VV : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp)), CkOn ((o₁ + o₂ : ℕ) : ℕ∞) VV F → ∀ g ∈ VV, g ∈ GV k r → opApply (Z :: Θ₀) F g = opApply Θ₁ (opApply Θ₂ F) g`.

Introduce `VV F hF g hgV hg`. Take `⟨f, U, hf, hU, hgU, hfe⟩` from `ext_loc hF hgV`. Rewrite using `[← op_congr (Z :: Θ₀) hU (fun x hx hxU => hfe x hxU hx) hg hgU, hZ, he f hf g hg]`. Conclude with `op_congr Θ₁ hU (fun x hx hxU => op_congr Θ₂ hU (fun y hy hyU => hfe y hyU hy) hx hxU) hg hgU`. Use `⟨Z :: Θ₀, fun T hT => ?_, hloc, ?_⟩` and prove the remaining obligations.

Break down `List.mem_cons.1 hT with rfl | h'` into its components or cases. Conclude with `⟨by simp [Z, scalTerm], fun _ => 0, polyDeg_const _ 0, fun _ => rfl, fun _ => rfl⟩`. Conclude with `hP T h'`. Introduce `D O hO c₁ c₂ p hp f hf g hg`. Establish `hf' : CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (GV k r) f` using `sCkOn_mono (by exact_mod_cast hord) hf`.

Establish `hρf : CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (GV k r) (rho D p f)`. Rewrite using `[rho_eq_trn]`. Conclude with `CkOn_trn _ (gv_mul (gv_inv hp.1.1) (gv_inv hp.2.1.1)) (gv_mul hp.2.2.2.1 hp.2.2.1.1) hf'`. Establish `o1 : opOrder Θ₁ ≤ o₁` using `opOrder_le Θ₁ fun T hT => (h₁ T hT).1`. Establish `o2 : opOrder Θ₂ ≤ o₂` using `opOrder_le Θ₂ fun T hT => (h₂ T hT).1`.

Establish `hf2 : CkOn (opOrder Θ₂ : ℕ∞) (GV k r) f` using `sCkOn_mono (by exact_mod_cast o2.trans (Nat.le_add_left _ _)) hf'`. Establish `hφ : CkOn (opOrder Θ₁ : ℕ∞) (GV k r) (opApply Θ₂ f)` using `sCkOn_mono (by exact_mod_cast o1) (ck_op (m := (o₁ : ℕ∞)) (o := o₂) (by exact_mod_cast hf') Θ₂ fun T hT => ⟨polyOp_ck h₂ _ T hT, (h₂ T hT).1⟩)`. Rewrite using `[hloc _ _ hρf g hg.1 hg.1, op_congr Θ₁ hO (fun x hx hxO => c₂ p hp f hf2 x ⟨hx, hxO⟩) hg.1 hg.2, c₁ p hp _ hφ g hg]`. Simplify using `only [rho]`. Rewrite using `[hloc _ f hf' _ (sgs_gv D hp hg.1) (sgs_gv D hp hg.1)]`.
-/
theorem polyOp_comp [FiniteDimensional ℂ Wp] {o₁ κ₁ o₂ κ₂ : ℕ} {Θ₁ Θ₂ : DiffOp k r Wp Wq}
    (h₁ : CutMP.PolyOp o₁ κ₁ Θ₁) (h₂ : CutMP.PolyOp o₂ κ₂ Θ₂) :
    ∃ Θ : DiffOp k r Wp Wq, CutMP.PolyOp (o₁ + o₂) (κ₁ + κ₂) Θ ∧
      (∀ (VV : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp)), CkOn ((o₁ + o₂ : ℕ) : ℕ∞) VV F →
        ∀ g ∈ VV, g ∈ GV k r → opApply Θ F g = opApply Θ₁ (opApply Θ₂ F) g) ∧
      ∀ (D : RealPlaceData k r Wp Wq) (O : Set (Mat k r)), IsOpen O →
        Commutes D (GV k r ∩ O) Θ₁ → Commutes D (GV k r ∩ O) Θ₂ → Commutes D (GV k r ∩ O) Θ := by
  obtain ⟨Θ₀, hP, he⟩ := comp_raw (k := k) (Wp := Wp) (Wq := Wq) r r (Nat.zero_add r).symm o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ h₁ h₂
  let Z : DTerm k r Wp Wq := scalTerm (fun _ => 0) (List.replicate (o₁ + o₂) 0)
    (fun X hX => by rw [List.eq_of_mem_replicate hX]; exact lie_zero)
  have hZ : ∀ F, opApply (Z :: Θ₀) F = opApply Θ₀ F := fun F => by
    rw [op_cons]; funext g; simp [Z, scalTerm]
  have hord : o₁ + o₂ ≤ opOrder (Z :: Θ₀) := by
    have := word_le_opOrder (Z :: Θ₀) Z (by simp)
    simpa [Z, scalTerm] using this
  have hloc : ∀ (VV : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp)), CkOn ((o₁ + o₂ : ℕ) : ℕ∞) VV F →
      ∀ g ∈ VV, g ∈ GV k r → opApply (Z :: Θ₀) F g = opApply Θ₁ (opApply Θ₂ F) g := by
    intro VV F hF g hgV hg
    obtain ⟨f, U, hf, hU, hgU, hfe⟩ := ext_loc hF hgV
    rw [← op_congr (Z :: Θ₀) hU (fun x hx hxU => hfe x hxU hx) hg hgU, hZ, he f hf g hg]
    exact op_congr Θ₁ hU (fun x hx hxU => op_congr Θ₂ hU (fun y hy hyU => hfe y hyU hy) hx hxU) hg hgU
  refine ⟨Z :: Θ₀, fun T hT => ?_, hloc, ?_⟩
  · rcases List.mem_cons.1 hT with rfl | h'
    · exact ⟨by simp [Z, scalTerm], fun _ => 0, polyDeg_const _ 0, fun _ => rfl, fun _ => rfl⟩
    · exact hP T h'
  · intro D O hO c₁ c₂ p hp f hf g hg
    have hf' : CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (GV k r) f := sCkOn_mono (by exact_mod_cast hord) hf
    have hρf : CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (GV k r) (rho D p f) := by
      rw [rho_eq_trn]
      exact CkOn_trn _ (gv_mul (gv_inv hp.1.1) (gv_inv hp.2.1.1)) (gv_mul hp.2.2.2.1 hp.2.2.1.1) hf'
    have o1 : opOrder Θ₁ ≤ o₁ := opOrder_le Θ₁ fun T hT => (h₁ T hT).1
    have o2 : opOrder Θ₂ ≤ o₂ := opOrder_le Θ₂ fun T hT => (h₂ T hT).1
    have hf2 : CkOn (opOrder Θ₂ : ℕ∞) (GV k r) f := sCkOn_mono (by exact_mod_cast o2.trans (Nat.le_add_left _ _)) hf'
    have hφ : CkOn (opOrder Θ₁ : ℕ∞) (GV k r) (opApply Θ₂ f) :=
      sCkOn_mono (by exact_mod_cast o1) (ck_op (m := (o₁ : ℕ∞)) (o := o₂) (by exact_mod_cast hf') Θ₂
        fun T hT => ⟨polyOp_ck h₂ _ T hT, (h₂ T hT).1⟩)
    rw [hloc _ _ hρf g hg.1 hg.1,
      op_congr Θ₁ hO (fun x hx hxO => c₂ p hp f hf2 x ⟨hx, hxO⟩) hg.1 hg.2, c₁ p hp _ hφ g hg]
    simp only [rho]
    rw [hloc _ f hf' _ (sgs_gv D hp hg.1) (sgs_gv D hp hg.1)]

/- English proof (translation)
Establish `e : ∀ F : Mat k r → (Wq →L[ℂ] Wp), opApply [scalTerm (Wp` using `Wp) (Wq := Wq) (fun _ => 1) [] (by simp)] F = F := fun F => by`. Use function extensionality and compare the values at `g`. Simplify using `[opApply, scalTerm, Rw]`. Use `⟨[scalTerm (fun _ => 1) [] (by simp)], fun T hT => ?_, e, fun D UU p _ f _ g _ => by rw [e, e]⟩` and prove the remaining obligations. Rewrite `hT` using `[List.mem_singleton]`.

Substitute `hT` using the available equality. Conclude with `⟨by simp [scalTerm], fun _ => 1, polyDeg_const _ 1, fun _ => rfl, fun _ => rfl⟩`.
-/
theorem polyOp_one : ∃ Θ : DiffOp k r Wp Wq, CutMP.PolyOp 0 0 Θ ∧ (∀ F, opApply Θ F = F) ∧
    ∀ (D : RealPlaceData k r Wp Wq) (UU : Set (Mat k r)), Commutes D UU Θ := by
  have e : ∀ F : Mat k r → (Wq →L[ℂ] Wp),
      opApply [scalTerm (Wp := Wp) (Wq := Wq) (fun _ => 1) [] (by simp)] F = F := fun F => by
    funext g; simp [opApply, scalTerm, Rw]
  refine ⟨[scalTerm (fun _ => 1) [] (by simp)], fun T hT => ?_, e, fun D UU p _ f _ g _ => by rw [e, e]⟩
  rw [List.mem_singleton] at hT
  subst hT
  exact ⟨by simp [scalTerm], fun _ => 1, polyDeg_const _ 1, fun _ => rfl, fun _ => rfl⟩

end ops

end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms

import Formalism.HermitianCurvature.HermitianCurvatureProofs.HpkMulSingleEsI
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AAInvTrans
import Formalism.FormalDegreeBessel.FinalG

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.PBG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hg, fun a ha => by simp at ha⟩`.
-/
theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

/- English proof (translation)
The claim follows from `| [], _, _, _, he => by simpa using he | T :: L, hT, h₁, h₂, he => by intro x hx hxG simp only [List.foldr_cons] exact hT T (by simp) _ _ (fold_congrV V L (fun T' hT' => hT T' (by simp [hT'])) h₁ h₂ he) x hx hxG`.
-/
theorem fold_congrV (V : Set (Mat k r)) :
    ∀ (L : List ((Mat k r → E) → (Mat k r → E))),
    (∀ T ∈ L, ∀ h₁ h₂ : Mat k r → E, (∀ x ∈ V, x ∈ GV k r → h₁ x = h₂ x) →
      ∀ x ∈ V, x ∈ GV k r → T h₁ x = T h₂ x) →
    ∀ h₁ h₂ : Mat k r → E, (∀ x ∈ V, x ∈ GV k r → h₁ x = h₂ x) →
      ∀ x ∈ V, x ∈ GV k r → L.foldr (fun T h => T h) h₁ x = L.foldr (fun T h => T h) h₂ x
  | [], _, _, _, he => by simpa using he
  | T :: L, hT, h₁, h₂, he => by
    intro x hx hxG
    simp only [List.foldr_cons]
    exact hT T (by simp) _ _ (fold_congrV V L (fun T' hT' => hT T' (by simp [hT'])) h₁ h₂ he) x hx hxG

/- English proof (translation)
Unfold `qminorOp`. Rewrite using `[Finset.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply]`. Use `congr 1`.

Use `fold_congrV V _ ?_ f₁ f₂ he x hx hxG` and prove the remaining obligations. Introduce `T hT h₁ h₂ he' y hy hyG`. Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 hT`. Conclude with `top_congr' V hV _ _ _ he' y hy hyG`.
-/
theorem qminorOp_congr {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) {V : Set (Mat k r)} (hV : IsOpen V)
    {f₁ f₂ : Mat k r → E} (he : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) (x : Mat k r) (hx : x ∈ V)
    (hxG : x ∈ GV k r) : qminorOp (EabH (Hpk k r)) a b u f₁ x = qminorOp (EabH (Hpk k r)) a b u f₂ x := by
  unfold qminorOp
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Pi.smul_apply]
  congr 1
  refine fold_congrV V _ ?_ f₁ f₂ he x hx hxG
  intro T hT h₁ h₂ he' y hy hyG
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
  exact top_congr' V hV _ _ _ he' y hy hyG

/- English proof (translation)
Unfold `D.vLet C3.AAop C3.AAvop`. Use `split_ifs`. Both sides reduce to the same expression. Use `congr 1`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Rewrite using `[qminorOp_congr _ _ _ hV he x hx hxG]`. Both sides reduce to the same expression. Use `congr 1`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Rewrite using `[qminorOp_congr _ _ _ hV he x hx hxG]`. Both sides reduce to the same expression.
-/
theorem vLet_congr (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {V : Set (Mat k r)} (hV : IsOpen V) {f₁ f₂ : Mat k r → E} (he : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x)
    (x : Mat k r) (hx : x ∈ V) (hxG : x ∈ GV k r) :
    D.vLet k r z z' i hi l e f₁ x = D.vLet k r z z' i hi l e f₂ x := by
  unfold D.vLet C3.AAop C3.AAvop
  split_ifs
  · rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminorOp_congr _ _ _ hV he x hx hxG]
    · rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [qminorOp_congr _ _ _ hV he x hx hxG]
    · rfl

/- English proof (translation)
Take `⟨U, F, a, b, c, d⟩` from `hf g hg`. Conclude with `⟨U, F, a, b, c, d⟩`.
-/
theorem loc_of_smoothOnH {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) (g : Mat k r) (hg : g ∈ GV k r) :
    Loc (⊤ : ℕ∞) f g := by
  obtain ⟨U, F, a, b, c, d⟩ := hf g hg
  exact ⟨U, F, a, b, c, d⟩

/- English proof (translation)
Take `⟨U, F, hU, hpU, hF, hΦF⟩` from `hΦ p ⟨glev0 hpG, hp⟩`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 (hU.inter hDm) p ⟨hpU, hp⟩`. Set `χ : ContDiffBump p` to `⟨ε / 3, ε / 2, by positivity, by linarith⟩`. Use `⟨Metric.ball p (ε / 3), Metric.isOpen_ball, Metric.mem_ball_self (by positivity), fun x hx => (hball (Metric.ball_subset_ball (by linarith) hx)).2, fun x => ((χ x : ℝ) : ℂ) • F x, ?_, ?_⟩` and prove the remaining obligations. Introduce `g₀ hg₀`.

Distinguish the cases in `hg : g₀ ∈ U`. Conclude with `⟨U, fun x => ((χ x : ℝ) : ℂ) • F x, hU, hg, ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffOn).smul hF, fun _ _ _ => rfl⟩`. Use `⟨(tsupport χ)ᶜ, fun _ => 0, (isClosed_tsupport _).isOpen_compl, ?_, contDiffOn_const, fun x hx _ => ?_⟩` and prove the remaining obligations. Introduce `hs`. Apply `hg` to reduce the goal to its premises.

Establish `h2 : g₀ ∈ Metric.closedBall p (ε / 2)` using `χ.tsupport_eq.subset hs`. Conclude with `(hball (Metric.closedBall_subset_ball (by linarith) h2)).1`. Establish `h0 : χ x = 0`. Assume the negation of the conclusion as `h`. Conclude with `hx (subset_tsupport χ (Function.mem_support.2 h))`.

Simplify using `[h0]`. Introduce `x hx hxG`. Establish `h1 : χ x = 1` using `χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)`. Use `show ((χ x : ℝ) : ℂ) • F x = Φ x`. Rewrite using `[h1, Complex.ofReal_one, one_smul]`.

Conclude with `(hΦF x (hball (Metric.ball_subset_ball (by linarith) hx)).1 (glev0 hxG)).symm`.
-/
theorem bump_ext {Φ : Mat k r → E} {Dm : Set (Mat k r)} (hDm : IsOpen Dm) (hΦ : Q.SmoothLev k r 0 Dm Φ)
    {p : Mat k r} (hp : p ∈ Dm) (hpG : p ∈ GV k r) :
    ∃ V : Set (Mat k r), IsOpen V ∧ p ∈ V ∧ V ⊆ Dm ∧
      ∃ f : Mat k r → E, SmoothOnH (Hpk k r) f ∧ ∀ x ∈ V, x ∈ GV k r → f x = Φ x := by
  obtain ⟨U, F, hU, hpU, hF, hΦF⟩ := hΦ p ⟨glev0 hpG, hp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.inter hDm) p ⟨hpU, hp⟩
  let χ : ContDiffBump p := ⟨ε / 3, ε / 2, by positivity, by linarith⟩
  refine ⟨Metric.ball p (ε / 3), Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
    fun x hx => (hball (Metric.ball_subset_ball (by linarith) hx)).2,
    fun x => ((χ x : ℝ) : ℂ) • F x, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hg : g₀ ∈ U
    · exact ⟨U, fun x => ((χ x : ℝ) : ℂ) • F x, hU, hg,
        ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffOn).smul hF, fun _ _ _ => rfl⟩
    · refine ⟨(tsupport χ)ᶜ, fun _ => 0, (isClosed_tsupport _).isOpen_compl, ?_, contDiffOn_const,
        fun x hx _ => ?_⟩
      · intro hs
        apply hg
        have h2 : g₀ ∈ Metric.closedBall p (ε / 2) := χ.tsupport_eq.subset hs
        exact (hball (Metric.closedBall_subset_ball (by linarith) h2)).1
      · have h0 : χ x = 0 := by
          by_contra h
          exact hx (subset_tsupport χ (Function.mem_support.2 h))
        simp [h0]
  · intro x hx hxG
    have h1 : χ x = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    show ((χ x : ℝ) : ℂ) • F x = Φ x
    rw [h1, Complex.ofReal_one, one_smul]
    exact (hΦF x (hball (Metric.ball_subset_ball (by linarith) hx)).1 (glev0 hxG)).symm

/- English proof (translation)
Set `fW : Wsm (E` to `E) (Set.univ : Set (Mat k r)) := ⟨f, fun g _ hgG => loc_of_smoothOnH hf g hgG⟩`. Establish `ec : ((c • fW : Wsm (E` using `E) (Set.univ : Set (Mat k r))) : Mat k r → E) = fun y => c • f y := rfl`. Establish `hA : ∀ m (hm : m ≤ r) u, C3.AAop k r m hm u (fun y => c • f y) x = c • C3.AAop k r m hm u f x`. Introduce `m hm u`. Establish `e1` using `AAop_eq Set.univ isOpen_univ m hm u (c • fW) x trivial hx`.

Establish `e2` using `AAop_eq Set.univ isOpen_univ m hm u fW x trivial hx`. Rewrite `e1` using `[ec]`. Rewrite using `[e1, e2, map_smul]`. Both sides reduce to the same expression. Establish `hAv : ∀ m (hm : m ≤ r) u, C3.AAvop k r m hm u (fun y => c • f y) x = c • C3.AAvop k r m hm u f x`.

Introduce `m hm u`. Establish `e1` using `AAvop_eq Set.univ isOpen_univ m hm u (c • fW) x trivial hx`. Establish `e2` using `AAvop_eq Set.univ isOpen_univ m hm u fW x trivial hx`. Rewrite `e1` using `[ec]`. Rewrite using `[e1, e2, map_smul]`.

Both sides reduce to the same expression. Unfold `D.vLet`. Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[hA, smul_comm]`.

Rewrite using `[hAv, smul_comm]`.
-/
theorem vLet_smul (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) {x : Mat k r} (hx : x ∈ GV k r) (c : ℂ) :
    D.vLet k r z z' i hi l e (fun y => c • f y) x = c • D.vLet k r z z' i hi l e f x := by
  let fW : Wsm (E := E) (Set.univ : Set (Mat k r)) := ⟨f, fun g _ hgG => loc_of_smoothOnH hf g hgG⟩
  have ec : ((c • fW : Wsm (E := E) (Set.univ : Set (Mat k r))) : Mat k r → E) = fun y => c • f y := rfl
  have hA : ∀ m (hm : m ≤ r) u, C3.AAop k r m hm u (fun y => c • f y) x = c • C3.AAop k r m hm u f x := by
    intro m hm u
    have e1 := AAop_eq Set.univ isOpen_univ m hm u (c • fW) x trivial hx
    have e2 := AAop_eq Set.univ isOpen_univ m hm u fW x trivial hx
    rw [ec] at e1
    rw [e1, e2, map_smul]
    rfl
  have hAv : ∀ m (hm : m ≤ r) u, C3.AAvop k r m hm u (fun y => c • f y) x = c • C3.AAvop k r m hm u f x := by
    intro m hm u
    have e1 := AAvop_eq Set.univ isOpen_univ m hm u (c • fW) x trivial hx
    have e2 := AAvop_eq Set.univ isOpen_univ m hm u fW x trivial hx
    rw [ec] at e1
    rw [e1, e2, map_smul]
    rfl
  unfold D.vLet
  split_ifs
  · simp
  · rw [hA, smul_comm]
  · rw [hAv, smul_comm]

/- English proof (translation)
Establish `hD : ∀ l', Dmin k r z z' (s * g * s') l' = Dmin k r z z' g l'` using `fun l' => dInv k r z z' hz hz' s hs s' hs' g l'`. Establish `hX` using `fun m (hm : m ≤ r) u ell => operators_commute_translations E k r z z' m hm u ell f hz hz' hf s hs s' hs' g hg`. Unfold `D.vLet`. Use `split_ifs`. Both sides reduce to the same expression.

Rewrite using `[hD, (hX _ _ _ 0).1]`. Rewrite using `[hD, (hX _ _ 0 _).2]`.
-/
theorem vLet_transl (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (i : ℕ) (hi : i ≤ r)
    (l : C.Letter) (e : Fin 2) {f : Mat k r → E} (hf : SmoothOnH (Hpk k r) f) {s s' : Mat k r}
    (hs : s ∈ Sset k r z) (hs' : s' ∈ Sset k r z') {g : Mat k r} (hg : g ∈ GV k r) :
    D.vLet k r z z' i hi l e f (s * g * s') = D.vLet k r z z' i hi l e (fun x => f (s * x * s')) g := by
  have hD : ∀ l', Dmin k r z z' (s * g * s') l' = Dmin k r z z' g l' :=
    fun l' => dInv k r z z' hz hz' s hs s' hs' g l'
  have hX := fun m (hm : m ≤ r) u ell => operators_commute_translations E k r z z' m hm u ell f hz hz' hf s hs s' hs' g hg
  unfold D.vLet
  split_ifs
  · rfl
  · rw [hD, (hX _ _ _ 0).1]
  · rw [hD, (hX _ _ 0 _).2]

/- English proof (translation)
Introduce and unpack `g₀ ⟨hg₀G', hg₀D⟩`. Establish `hg₀G : g₀ ∈ GV k r` using `hg₀G'.1`. Take `⟨V, hV, hpV, hVD, f, hf, hfe⟩` from `bump_ext hDm hΦ hg₀D hg₀G`. Set `fW : Wsm (E` to `E) (Sd z z' i hi) := ⟨f, fun g _ hgG => loc_of_smoothOnH hf g hgG⟩`. Establish `hL : Loc (⊤ : ℕ∞) (D.vLet k r z z' i hi l e f) g₀` using `vLet_mem z z' i hi l e fW g₀ (hne g₀ hg₀D) hg₀G`.

Establish `hL2 : Loc (⊤ : ℕ∞) (D.vLet k r z z' i hi l e Φ) g₀` using `loc_of_eq hL hV hpV (fun x hx hxG => vLet_congr z z' i hi l e hV (fun y hy hyG => (hfe y hy hyG).symm) x hx hxG)`. Take `⟨U, F, hU, hgU, hF, hFe⟩` from `hL2`. Conclude with `⟨U, F, hU, hgU, hF, fun g hg hgl => hFe g hg hgl.1⟩`.
-/
theorem smooth_vLet (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) (hi : i ≤ r) (l : C.Letter) (e : Fin 2)
    {Dm : Set (Mat k r)} (hDm : IsOpen Dm) {Φ : Mat k r → E} (hΦ : Q.SmoothLev k r 0 Dm Φ)
    (hne : ∀ g ∈ Dm, Dmin k r z z' g ⟨i, by omega⟩ ≠ 0) :
    Q.SmoothLev k r 0 Dm (D.vLet k r z z' i hi l e Φ) := by
  rintro g₀ ⟨hg₀G', hg₀D⟩
  have hg₀G : g₀ ∈ GV k r := hg₀G'.1
  obtain ⟨V, hV, hpV, hVD, f, hf, hfe⟩ := bump_ext hDm hΦ hg₀D hg₀G
  let fW : Wsm (E := E) (Sd z z' i hi) := ⟨f, fun g _ hgG => loc_of_smoothOnH hf g hgG⟩
  have hL : Loc (⊤ : ℕ∞) (D.vLet k r z z' i hi l e f) g₀ :=
    vLet_mem z z' i hi l e fW g₀ (hne g₀ hg₀D) hg₀G
  have hL2 : Loc (⊤ : ℕ∞) (D.vLet k r z z' i hi l e Φ) g₀ :=
    loc_of_eq hL hV hpV (fun x hx hxG =>
      vLet_congr z z' i hi l e hV (fun y hy hyG => (hfe y hy hyG).symm) x hx hxG)
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hL2
  exact ⟨U, F, hU, hgU, hF, fun g hg hgl => hFe g hg hgl.1⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, BigCellZetaMinors.one_uw z, n, hn, (Matrix.one_mul n).symm⟩`.
-/
theorem one_mem_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, BigCellZetaMinors.one_uw z, n, hn, (Matrix.one_mul n).symm⟩

/- English proof (translation)
Take `⟨hS, hRt, hLt⟩` from `hR`. Establish `hne : ∀ g ∈ Dm, Dmin k r z z' g ⟨i, by omega⟩ ≠ 0`. Introduce `g hg`. Take `⟨h1, h2, _⟩` from `hDJ hg`. Break down `hij with rfl | rfl` into its components or cases.

Conclude with `h1`. Conclude with `h2`. Use `⟨smooth_vLet z z' i (by omega) l e hDm hS hne, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨hgG', hgD⟩ n hn`. Establish `hgnD` using `(hRt g ⟨hgG', hgD⟩ n hn).1`.

Use `⟨hgnD, ?_⟩` and prove the remaining obligations. Establish `hgG : g ∈ GV k r` using `hgG'.1`. Establish `hgnG : g * n ∈ GV k r` using `AAInvW.inUH_mul hgG hn.1`. Take `⟨Va, hVa, hpa, _, fa, hfa, hfae⟩` from `bump_ext hDm hS hgnD hgnG`. Take `⟨Vb, hVb, hpb, hVbD, fb, hfb, hfbe⟩` from `bump_ext hDm hS hgD hgG`.

Establish `hW : IsOpen (Vb ∩ (fun x : Mat k r => x * n) ⁻¹' Va)` using `hVb.inter (hVa.preimage (continuous_id.matrix_mul continuous_const))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.one_mul]`. Conclude with `vLet_congr z z' i _ l e hVa (fun y hy hyG => (hfae y hy hyG).symm) _ hpa hgnG`. Use `_ = D.vLet k r z z' i _ l e (fun x => fa (1 * x * n)) g := vLet_transl z z' hz hz' i _ l e hfa (one_mem_S z WeylGroupFacts.mem_n_one) (one_mem_S z' hn) hgG`.

Use `_ = D.vLet k r z z' i _ l e (fun x => psi k r z' cStd n • fb x) g := by`. Use `vLet_congr z z' i _ l e hW (fun y hy hyG => ?_) g ⟨hpb, hpa⟩ hgG` and prove the remaining obligations. Rewrite using `[Matrix.one_mul, hfae (y * n) hy.2 (AAInvW.inUH_mul hyG hn.1), (hRt y ⟨glev0 hyG, hVbD hy.1⟩ n hn).2, hfbe y hy.1 hyG]`. Use `_ = psi k r z' cStd n • D.vLet k r z z' i _ l e fb g := vLet_smul z z' i _ l e hfb hgG _`. Use `_ = psi k r z' cStd n • D.vLet k r z z' i _ l e Φ g := by`.

Rewrite using `[vLet_congr z z' i _ l e hVb (fun y hy hyG => hfbe y hy hyG) g hpb hgG]`. Introduce and unpack `g ⟨hgG', hgD⟩ a`. Establish `hgnD` using `(hLt g ⟨hgG', hgD⟩ a).1`. Use `⟨hgnD, ?_⟩` and prove the remaining obligations. Use `set s := LevelPointCoordinates.nL k r j hj a with hs_def`.

Establish `hsN : s ∈ Nset k r` using `nL_mem j hj a`. Establish `hgG : g ∈ GV k r` using `hgG'.1`. Establish `hsgG : s * g ∈ GV k r` using `AAInvW.inUH_mul hsN.1 hgG`. Take `⟨Va, hVa, hpa, _, fa, hfa, hfae⟩` from `bump_ext hDm hS hgnD hsgG`. Take `⟨Vb, hVb, hpb, hVbD, fb, hfb, hfbe⟩` from `bump_ext hDm hS hgD hgG`.

Establish `hW : IsOpen (Vb ∩ (fun x : Mat k r => s * x) ⁻¹' Va)` using `hVb.inter (hVa.preimage (continuous_const.matrix_mul continuous_id))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_one]`. Conclude with `vLet_congr z z' i _ l e hVa (fun y hy hyG => (hfae y hy hyG).symm) _ hpa hsgG`. Use `_ = D.vLet k r z z' i _ l e (fun x => fa (s * x * 1)) g := vLet_transl z z' hz hz' i _ l e hfa (one_mem_S z hsN) (one_mem_S z' WeylGroupFacts.mem_n_one) hgG`.

Use `_ = D.vLet k r z z' i _ l e (fun x => psi k r z cStd s • fb x) g := by`. Use `vLet_congr z z' i _ l e hW (fun y hy hyG => ?_) g ⟨hpb, hpa⟩ hgG` and prove the remaining obligations. Rewrite using `[Matrix.mul_one, hfae (s * y) hy.2 (AAInvW.inUH_mul hsN.1 hyG), (hLt y ⟨glev0 hyG, hVbD hy.1⟩ a).2, hfbe y hy.1 hyG]`. Use `_ = psi k r z cStd s • D.vLet k r z z' i _ l e fb g := vLet_smul z z' i _ l e hfb hgG _`. Use `_ = psi k r z cStd s • D.vLet k r z z' i _ l e Φ g := by`.

Rewrite using `[vLet_congr z z' i _ l e hVb (fun y hy hyG => hfbe y hy hyG) g hpb hgG]`.
-/
theorem rulesOn_vLet (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) (hz : inWb k r z)
    (hz' : inWb k r z') (hDm : IsOpen Dm) (hDJ : Dm ⊆ LevelPointCoordinates.domJ k r j hj z z')
    (hR : LevelPointCoordinates.RulesOn k r j hj z z' Dm Φ) (i : ℕ) (hi : i ≤ j + 1) (hij : i = j ∨ i = j + 1)
    (l : C.Letter) (e : Fin 2) :
    LevelPointCoordinates.RulesOn k r j hj z z' Dm (D.vLet k r z z' i (by omega) l e Φ) := by
  obtain ⟨hS, hRt, hLt⟩ := hR
  have hne : ∀ g ∈ Dm, Dmin k r z z' g ⟨i, by omega⟩ ≠ 0 := by
    intro g hg
    obtain ⟨h1, h2, _⟩ := hDJ hg
    rcases hij with rfl | rfl
    · exact h1
    · exact h2
  refine ⟨smooth_vLet z z' i (by omega) l e hDm hS hne, ?_, ?_⟩
  · rintro g ⟨hgG', hgD⟩ n hn
    have hgnD := (hRt g ⟨hgG', hgD⟩ n hn).1
    refine ⟨hgnD, ?_⟩
    have hgG : g ∈ GV k r := hgG'.1
    have hgnG : g * n ∈ GV k r := AAInvW.inUH_mul hgG hn.1
    obtain ⟨Va, hVa, hpa, _, fa, hfa, hfae⟩ := bump_ext hDm hS hgnD hgnG
    obtain ⟨Vb, hVb, hpb, hVbD, fb, hfb, hfbe⟩ := bump_ext hDm hS hgD hgG
    have hW : IsOpen (Vb ∩ (fun x : Mat k r => x * n) ⁻¹' Va) :=
      hVb.inter (hVa.preimage (continuous_id.matrix_mul continuous_const))
    calc D.vLet k r z z' i _ l e Φ (g * n) = D.vLet k r z z' i _ l e fa (1 * g * n) := by
          rw [Matrix.one_mul]
          exact vLet_congr z z' i _ l e hVa (fun y hy hyG => (hfae y hy hyG).symm) _ hpa hgnG
      _ = D.vLet k r z z' i _ l e (fun x => fa (1 * x * n)) g :=
          vLet_transl z z' hz hz' i _ l e hfa (one_mem_S z WeylGroupFacts.mem_n_one) (one_mem_S z' hn) hgG
      _ = D.vLet k r z z' i _ l e (fun x => psi k r z' cStd n • fb x) g := by
          refine vLet_congr z z' i _ l e hW (fun y hy hyG => ?_) g ⟨hpb, hpa⟩ hgG
          rw [Matrix.one_mul, hfae (y * n) hy.2 (AAInvW.inUH_mul hyG hn.1),
            (hRt y ⟨glev0 hyG, hVbD hy.1⟩ n hn).2, hfbe y hy.1 hyG]
      _ = psi k r z' cStd n • D.vLet k r z z' i _ l e fb g := vLet_smul z z' i _ l e hfb hgG _
      _ = psi k r z' cStd n • D.vLet k r z z' i _ l e Φ g := by
          rw [vLet_congr z z' i _ l e hVb (fun y hy hyG => hfbe y hy hyG) g hpb hgG]
  · rintro g ⟨hgG', hgD⟩ a
    have hgnD := (hLt g ⟨hgG', hgD⟩ a).1
    refine ⟨hgnD, ?_⟩
    set s := LevelPointCoordinates.nL k r j hj a with hs_def
    have hsN : s ∈ Nset k r := nL_mem j hj a
    have hgG : g ∈ GV k r := hgG'.1
    have hsgG : s * g ∈ GV k r := AAInvW.inUH_mul hsN.1 hgG
    obtain ⟨Va, hVa, hpa, _, fa, hfa, hfae⟩ := bump_ext hDm hS hgnD hsgG
    obtain ⟨Vb, hVb, hpb, hVbD, fb, hfb, hfbe⟩ := bump_ext hDm hS hgD hgG
    have hW : IsOpen (Vb ∩ (fun x : Mat k r => s * x) ⁻¹' Va) :=
      hVb.inter (hVa.preimage (continuous_const.matrix_mul continuous_id))
    calc D.vLet k r z z' i _ l e Φ (s * g) = D.vLet k r z z' i _ l e fa (s * g * 1) := by
          rw [Matrix.mul_one]
          exact vLet_congr z z' i _ l e hVa (fun y hy hyG => (hfae y hy hyG).symm) _ hpa hsgG
      _ = D.vLet k r z z' i _ l e (fun x => fa (s * x * 1)) g :=
          vLet_transl z z' hz hz' i _ l e hfa (one_mem_S z hsN) (one_mem_S z' WeylGroupFacts.mem_n_one) hgG
      _ = D.vLet k r z z' i _ l e (fun x => psi k r z cStd s • fb x) g := by
          refine vLet_congr z z' i _ l e hW (fun y hy hyG => ?_) g ⟨hpb, hpa⟩ hgG
          rw [Matrix.mul_one, hfae (s * y) hy.2 (AAInvW.inUH_mul hsN.1 hyG),
            (hLt y ⟨glev0 hyG, hVbD hy.1⟩ a).2, hfbe y hy.1 hyG]
      _ = psi k r z cStd s • D.vLet k r z z' i _ l e fb g := vLet_smul z z' i _ l e hfb hgG _
      _ = psi k r z cStd s • D.vLet k r z z' i _ l e Φ g := by
          rw [vLet_congr z z' i _ l e hVb (fun y hy hyG => hfbe y hy hyG) g hpb hgG]

end Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `k r j hj z z' E _ _ Dm Φ hz hz' hDm hDJ hR i hi hij l e` and use `SingleEntryHermitianProducts.rulesOn_vLet k r j hj z z' E Dm Φ hz hz' hDm hDJ hR i hi hij l e`.
-/
theorem rules_closed : Formalism.FourierDecayAlt.P.LevelPointCoordinates.RulesClosed :=
  fun k r j hj z z' E _ _ Dm Φ hz hz' hDm hDJ hR i hi hij l e =>
    SingleEntryHermitianProducts.rulesOn_vLet k r j hj z z' E Dm Φ hz hz' hDm hDJ hR i hi hij l e

end Formalism.FourierDecayAlt.P

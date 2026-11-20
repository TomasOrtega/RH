import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorAddSmulCompactCoefficientsStatement

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace GlobalTheory.TopVec

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
/- English proof (translation)
Unfold `_root_.Formalism.FourierDecayAlt.D.vecV`. Use `split_ifs with h h'`. Rewrite using `[_root_.Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF, _root_.Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat _ _ _ _ h'.choose_spec.2.1]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
private lemma vecV_cutoff_lemma {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (B : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : _root_.Formalism.FourierDecayAlt.B.Mat k r)
    (H : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (q : _root_.Formalism.FourierDecayAlt.C.LPt) (ψ : ℝ → ℝ) (t : ℝ) :
    _root_.Formalism.FourierDecayAlt.D.vecV B ν' m₀ (_root_.Formalism.FourierDecayAlt.D.cutF B ψ H t) q =
      ((ψ (_root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r B.z * _root_.Formalism.QuantumDeterminants.Tz k r B.z') r q / t) : ℝ) : ℂ) •
        _root_.Formalism.FourierDecayAlt.D.vecV B ν' m₀ H q := by
  unfold _root_.Formalism.FourierDecayAlt.D.vecV
  split_ifs with h h'
  · rw [_root_.Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF, _root_.Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat _ _ _ _ h'.choose_spec.2.1]
  · simp
  · simp

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons X w ih`. Rewrite using `[List.foldr_cons, ih]`. Use function extensionality and compare the values at `g`.

Unfold `_root_.Formalism.REAL.RdV`. Simplify using the standard rewrite rules.
-/
private lemma foldr_RdV_zero {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : List (_root_.Formalism.FourierDecayAlt.B.Mat k r)) : List.foldr _root_.Formalism.REAL.RdV (fun _ => (0 : E)) w = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    rw [List.foldr_cons, ih]
    funext g
    unfold _root_.Formalism.REAL.RdV
    simp

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
/- English proof (translation)
Unfold `_root_.Formalism.FourierDecayAlt.B.opApply`. Apply `List.sum_eq_zero` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [List.mem_map] at hx`. Take `⟨T, -, rfl⟩` from `hx`.

Unfold `_root_.Formalism.FourierDecayAlt.B.Rw`. Rewrite using `[foldr_RdV_zero]`. Simplify using the standard rewrite rules.
-/
private lemma opApply_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (D : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply D (fun _ => 0) g = 0 := by
  unfold _root_.Formalism.FourierDecayAlt.B.opApply
  apply List.sum_eq_zero
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨T, -, rfl⟩ := hx
  unfold _root_.Formalism.FourierDecayAlt.B.Rw
  rw [foldr_RdV_zero]
  simp

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
/- English proof (translation)
Use `set q := _root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c with hq`. Use `set G := _root_.Formalism.FourierDecayAlt.TBB.Gp p q with hGdef`. Establish `hG : G = _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z * _root_.Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z') P.r q` using `rfl`. Establish `hV : ∀ H, p.V H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q` using `fun H => rfl`. Establish `hcut : ∀ (ψ : ℝ → ℝ) (H : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp) (t : ℝ) (g : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r), _root_.Formalism.FourierDecayAlt.D.cutF p.T.base ψ H t g = ((ψ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.bas …` using `fun _ _ _ _ => rfl`.

Establish `hcont : Continuous (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z')` using `_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont _ _`. Establish `hzero : ∀ F' : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp, (∀ e, p.V (p.Θ.Θ w e F') q = 0) → _root_.GlobalTheory.TopVec.tv p F' w c = 0`. Introduce `F' h`. Unfold `_root_.GlobalTheory.TopVec.tv`. Simplify using `[← hq, h, _root_.Formalism.FourierDecayAlt.B.hsVec]`.

Use function extensionality and compare the values at `x`. Apply the tactic sequence `try simp only [Pi.zero_apply]`. Rewrite using `[← Pi.zero_def, WithLp.toLp_zero, smul_zero]`. Establish `htv : ∀ F₁ F₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp, (∀ e, p.V (p.Θ.Θ w e F₁) q = p.V (p.Θ.Θ w e F₂) q) → _root_.GlobalTheory.TopVec.tv p F₁ w c = _root_.GlobalTheory.TopVec.tv p F₂ w c`. Introduce `F₁ F₂ h`.

Unfold `_root_.GlobalTheory.TopVec.tv`. Simplify using `only [← hq, h]`. Establish `hV0 : G ≤ 0 → ∀ H, p.V H q = 0`. Introduce `h H`. Rewrite using `[hV]`.

Unfold `_root_.Formalism.FourierDecayAlt.D.vecV`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨-, h'⟩`. Rewrite `h'` using `[← hG]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨?_, ?_, fun h => hzero F fun e => hV0 h _⟩` and prove the remaining obligations. Introduce `hlt`. Establish `hGpos : 0 < G` using `hε.trans hlt`. Apply `htv` to reduce the goal to its premises. Introduce `e`.

Take `⟨nf, fib, o, κ, Dop, -, -, -, -, hDop⟩` from `hD w hw e`. Rewrite using `[hV, hV]`. Establish `h1 : ∀ H, _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if ε / G < x then 1 else 0) H G) q`. Introduce `H`. Rewrite using `[vecV_cutoff_lemma, ← hG, div_self hGpos.ne', if_pos ((div_lt_one hGpos).mpr hlt)]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, h1 (p.Θ.Θ w e F)]`. Apply `_root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos` to reduce the goal to its premises. Introduce `g hg`. Rewrite using `[hcut, hcut]`.

Distinguish the cases in `hgε : ε < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g`. Establish `hOQ : g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅` using `⟨hg.1, hg.2, by simp⟩`. Establish `hloc : _root_.Formalism.FourierDecayAlt.B.opApply Dop (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) g = _root_.Formalism.FourierDecayAlt.B.opApply Dop F g`. Apply `_root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Dop (isOpen_lt continuous_const hcont) _ g hgε` to reduce the goal to its premises. Introduce `x hx`.

Establish `hx' : ε < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' x` using `hx`. Rewrite using `[hcut, hχ.2.2 _ ((le_div_iff₀ hε).mpr (by linarith))]`. Simplify using the standard rewrite rules. Rewrite using `[hDop _ g hOQ, hDop _ g hOQ, hloc]`. Establish `: ¬ (ε / G < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g / G)`.

Rewrite using `[div_lt_div_iff_of_pos_right hGpos]`. Conclude with `hgε`. Simplify using `[this]`. Introduce `hlt`. Break down `le_or_gt G 0 with hG0 | hGpos` into its components or cases.

Conclude with `hzero _ fun e => hV0 hG0 _`. Apply `hzero` to reduce the goal to its premises. Introduce `e`. Take `⟨nf, fib, o, κ, Dop, -, -, -, -, hDop⟩` from `hD w hw e`. Rewrite using `[hV]`.

Establish `h1 : ∀ H, _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if x < δ * ε / G then 1 else 0) H G) q`. Introduce `H`. Rewrite using `[vecV_cutoff_lemma, ← hG, div_self hGpos.ne', if_pos ((one_lt_div hGpos).mpr hlt)]`. Simplify using the standard rewrite rules. Rewrite using `[h1]`.

Establish `h2 : _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if x < δ * ε / G then 1 else 0) (p.Θ.Θ w e (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε)) G) q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base …`. Apply `_root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos` to reduce the goal to its premises. Introduce `g hg`. Rewrite using `[hcut, hcut]`. Distinguish the cases in `hgd : _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g < δ * ε`.

Establish `hOQ : g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅` using `⟨hg.1, hg.2, by simp⟩`. Establish `hloc : _root_.Formalism.FourierDecayAlt.B.opApply Dop (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) g = _root_.Formalism.FourierDecayAlt.B.opApply Dop (fun _ => 0) g`. Apply `_root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Dop (isOpen_lt hcont continuous_const) _ g hgd` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' x < δ * ε` using `hx`.

Rewrite using `[hcut, hδ _ ((div_lt_iff₀ hε).mpr hx')]`. Simplify using the standard rewrite rules. Rewrite using `[hDop _ g hOQ, hloc, opApply_zero]`. Establish `: ¬ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g / G < δ * ε / G)`. Rewrite using `[div_lt_div_iff_of_pos_right hGpos]`.

Conclude with `hgd`. Simplify using `[this]`. Establish `h3 : _root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if x < δ * ε / G then 1 else 0) (fun _ => (0 : Wq →L[ℂ] Wp)) G = _root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun _ => 0) (fun _ => 0) G`. Use function extensionality and compare the values at `g`. Rewrite using `[hcut, hcut]`.

Simplify using the standard rewrite rules. Rewrite using `[h2, h3, vecV_cutoff_lemma]`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.TopVec.tv_cutF (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq)
    (Cb : ℝ) (χ : ℝ → ℝ) (δ ε : ℝ) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List _root_.Formalism.FourierDecayAlt.C.Letter)
    (c : Fin (P.r + 1) → ℂ) (hD : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hw : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w)
    (hχ : _root_.Formalism.FourierDecayAlt.C6.IsCut0 χ) (hδ : ∀ x, x < δ → χ x = 0) (hε : 0 < ε)
    (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F) :
    (ε < _root_.Formalism.FourierDecayAlt.TBB.Gp p (_root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c) →
      _root_.GlobalTheory.TopVec.tv p (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) w c = _root_.GlobalTheory.TopVec.tv p F w c) ∧
    (_root_.Formalism.FourierDecayAlt.TBB.Gp p (_root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c) < δ * ε →
      _root_.GlobalTheory.TopVec.tv p (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) w c = 0) ∧
    (_root_.Formalism.FourierDecayAlt.TBB.Gp p (_root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c) ≤ 0 → _root_.GlobalTheory.TopVec.tv p F w c = 0) := by
  set q := _root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c with hq
  set G := _root_.Formalism.FourierDecayAlt.TBB.Gp p q with hGdef
  have hG : G = _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z * _root_.Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z') P.r q := rfl
  have hV : ∀ H, p.V H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q := fun H => rfl
  have hcut : ∀ (ψ : ℝ → ℝ) (H : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp) (t : ℝ) (g : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r),
      _root_.Formalism.FourierDecayAlt.D.cutF p.T.base ψ H t g =
        ((ψ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g / t) : ℝ) : ℂ) • H g := fun _ _ _ _ => rfl
  have hcont : Continuous (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z') := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont _ _
  have hzero : ∀ F' : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp,
      (∀ e, p.V (p.Θ.Θ w e F') q = 0) → _root_.GlobalTheory.TopVec.tv p F' w c = 0 := by
    intro F' h
    unfold _root_.GlobalTheory.TopVec.tv
    simp [← hq, h, _root_.Formalism.FourierDecayAlt.B.hsVec]
    funext x
    try simp only [Pi.zero_apply]
    rw [← Pi.zero_def, WithLp.toLp_zero, smul_zero]
  have htv : ∀ F₁ F₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp,
      (∀ e, p.V (p.Θ.Θ w e F₁) q = p.V (p.Θ.Θ w e F₂) q) →
        _root_.GlobalTheory.TopVec.tv p F₁ w c = _root_.GlobalTheory.TopVec.tv p F₂ w c := by
    intro F₁ F₂ h
    unfold _root_.GlobalTheory.TopVec.tv
    simp only [← hq, h]
  have hV0 : G ≤ 0 → ∀ H, p.V H q = 0 := by
    intro h H
    rw [hV]
    unfold _root_.Formalism.FourierDecayAlt.D.vecV
    rw [dif_neg]
    rintro ⟨-, h'⟩
    rw [← hG] at h'
    linarith
  refine ⟨?_, ?_, fun h => hzero F fun e => hV0 h _⟩
  · intro hlt
    have hGpos : 0 < G := hε.trans hlt
    apply htv
    intro e
    obtain ⟨nf, fib, o, κ, Dop, -, -, -, -, hDop⟩ := hD w hw e
    rw [hV, hV]
    have h1 : ∀ H, _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀
        (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if ε / G < x then 1 else 0) H G) q := by
      intro H
      rw [vecV_cutoff_lemma, ← hG, div_self hGpos.ne', if_pos ((div_lt_one hGpos).mpr hlt)]
      simp
    rw [h1, h1 (p.Θ.Θ w e F)]
    apply _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos
    intro g hg
    rw [hcut, hcut]
    by_cases hgε : ε < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g
    · have hOQ : g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅ := ⟨hg.1, hg.2, by simp⟩
      have hloc : _root_.Formalism.FourierDecayAlt.B.opApply Dop (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) g = _root_.Formalism.FourierDecayAlt.B.opApply Dop F g := by
        apply _root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Dop (isOpen_lt continuous_const hcont) _ g hgε
        intro x hx
        have hx' : ε < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' x := hx
        rw [hcut, hχ.2.2 _ ((le_div_iff₀ hε).mpr (by linarith))]
        simp
      rw [hDop _ g hOQ, hDop _ g hOQ, hloc]
    · have : ¬ (ε / G < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g / G) := by
        rw [div_lt_div_iff_of_pos_right hGpos]; exact hgε
      simp [this]
  · intro hlt
    rcases le_or_gt G 0 with hG0 | hGpos
    · exact hzero _ fun e => hV0 hG0 _
    apply hzero
    intro e
    obtain ⟨nf, fib, o, κ, Dop, -, -, -, -, hDop⟩ := hD w hw e
    rw [hV]
    have h1 : ∀ H, _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀
        (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if x < δ * ε / G then 1 else 0) H G) q := by
      intro H
      rw [vecV_cutoff_lemma, ← hG, div_self hGpos.ne', if_pos ((one_lt_div hGpos).mpr hlt)]
      simp
    rw [h1]
    have h2 : _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base
          (fun x => if x < δ * ε / G then 1 else 0) (p.Θ.Θ w e (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε)) G) q =
        _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base
          (fun x => if x < δ * ε / G then 1 else 0) (fun _ => 0) G) q := by
      apply _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos
      intro g hg
      rw [hcut, hcut]
      by_cases hgd : _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g < δ * ε
      · have hOQ : g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅ := ⟨hg.1, hg.2, by simp⟩
        have hloc : _root_.Formalism.FourierDecayAlt.B.opApply Dop (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) g = _root_.Formalism.FourierDecayAlt.B.opApply Dop (fun _ => 0) g := by
          apply _root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Dop (isOpen_lt hcont continuous_const) _ g hgd
          intro x hx
          have hx' : _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' x < δ * ε := hx
          rw [hcut, hδ _ ((div_lt_iff₀ hε).mpr hx')]
          simp
        rw [hDop _ g hOQ, hloc, opApply_zero]
      · have : ¬ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g / G < δ * ε / G) := by
          rw [div_lt_div_iff_of_pos_right hGpos]; exact hgd
        simp [this]
    have h3 : _root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if x < δ * ε / G then 1 else 0)
        (fun _ => (0 : Wq →L[ℂ] Wp)) G = _root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun _ => 0) (fun _ => 0) G := by
      funext g
      rw [hcut, hcut]
      simp
    rw [h2, h3, vecV_cutoff_lemma]
    simp

end GlobalTheory.TopVec

import Formalism.HermitianCurvature.HermitianCurvatureProofs.PosCoreQ

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section lin

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Introduce `g hg`. Establish `hw : ∀ x ∈ BetaSesquilinearity.wR v, B.inLie k r x.2`. Introduce `x hx`. Simplify using `only [BetaSesquilinearity.wR, List.mem_map] at hx`. Take `⟨X, hX, rfl⟩` from `hx`.

Conclude with `hv X hX`. Establish `e : (fun x => F₁ x - F₂ x) = fun x => F₁ x + (-1 : ℂ) • F₂ x`. Use function extensionality and compare the values at `x`. Simplify using `[sub_eq_add_neg]`. Rewrite using `[← BetaSesquilinearity.Dw_wR, ← BetaSesquilinearity.Dw_wR, ← BetaSesquilinearity.Dw_wR, e, BetaSesquilinearity.Dw_add hw (BetaSesquilinearity.sCkOn_mono le_top h₁) (BetaSesquilinearity.sCkOn_mono le_top (BetaSesquilinearity.CkOn_smul (-1) h₂)) g hg, BetaSesquilinearity.Dw_smul]`.

Simplify using `[sub_eq_add_neg]`.
-/
theorem rw_sub (v : List (B.Mat k r)) (hv : ∀ X ∈ v, B.inLie k r X) {F₁ F₂ : B.Mat k r → E}
    (h₁ : B.CkOn ⊤ (B.GV k r) F₁) (h₂ : B.CkOn ⊤ (B.GV k r) F₂) :
    ∀ g ∈ B.GV k r, B.Rw v (fun x => F₁ x - F₂ x) g = B.Rw v F₁ g - B.Rw v F₂ g := by
  intro g hg
  have hw : ∀ x ∈ BetaSesquilinearity.wR v, B.inLie k r x.2 := by
    intro x hx
    simp only [BetaSesquilinearity.wR, List.mem_map] at hx
    obtain ⟨X, hX, rfl⟩ := hx
    exact hv X hX
  have e : (fun x => F₁ x - F₂ x) = fun x => F₁ x + (-1 : ℂ) • F₂ x := by
    funext x; simp [sub_eq_add_neg]
  rw [← BetaSesquilinearity.Dw_wR, ← BetaSesquilinearity.Dw_wR, ← BetaSesquilinearity.Dw_wR, e,
    BetaSesquilinearity.Dw_add hw (BetaSesquilinearity.sCkOn_mono le_top h₁) (BetaSesquilinearity.sCkOn_mono le_top (BetaSesquilinearity.CkOn_smul (-1) h₂)) g hg, BetaSesquilinearity.Dw_smul]
  simp [sub_eq_add_neg]

/- English proof (translation)
Substitute `e` using the available equality. Establish `e' : D.castF (rfl : a = a) F = F`. Use function extensionality and compare the values at `g`. Simplify using `[D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]`. Rewrite using `[e']` and apply the resulting hypothesis.
-/
theorem ccle_castF {a b : ℕ} (e : a = b) {A : ℝ} {m : ℕ} {F : B.Mat k b → E} {c : ℝ} (h : B.CCle A m F c) :
    B.CCle A m (D.castF e F) c := by
  subst e
  have e' : D.castF (rfl : a = a) F = F := by
    funext g; simp [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rwa [e']

end lin

/- English proof (translation)
Introduce `g hg`. Unfold `B.opApply`. Proceed by induction on `Θ with`. Consider the case `nil => simp`. Consider the case `cons T L ih`.

Simplify using `only [List.map_cons, List.sum_cons, ih]`. Rewrite using `[rw_sub T.word T.word_lie h₁ h₂ g hg, map_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem opApply_sub {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (Θ : B.DiffOp k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : B.CkOn ⊤ (B.GV k r) F₁) (h₂ : B.CkOn ⊤ (B.GV k r) F₂) :
    ∀ g ∈ B.GV k r, B.opApply Θ (fun x => F₁ x - F₂ x) g = B.opApply Θ F₁ g - B.opApply Θ F₂ g := by
  intro g hg
  unfold B.opApply
  induction Θ with
  | nil => simp
  | cons T L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [rw_sub T.word T.word_lie h₁ h₂ g hg, map_sub]
    abel

/- English proof (translation)
Take `⟨Cp, hCp0, hCp⟩` from `posCoreQ`. Use `⟨Cp, hCp0, ?_⟩` and prove the remaining obligations. Introduce `Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi hi1 w hw p hc hp a`. Choose the witnesses or unpack the hypotheses as in `⟨h, n, t, rfl⟩ : ∃ (h : C.LPt) (n : ℕ) (t : ℂ), p = h ++ [(n + 1, t)] := by`. Establish `hne : p ≠ []`.

Introduce and unpack `rfl`. Use `hp.2` as an intermediate fact. Simplify using `[D.ptSize] at this`. Use linear arithmetic over natural numbers and integers. Use `⟨p.dropLast, (p.getLast hne).1 - 1, (p.getLast hne).2, ?_⟩` and prove the remaining obligations.

Establish `h1 : 1 ≤ (p.getLast hne).1` using `(hp.1 _ (List.getLast_mem hne)).1`. Rewrite using `[Nat.sub_add_cancel h1]`. Conclude with `(List.dropLast_append_getLast hne).symm`. Take `⟨hpb, hps⟩` from `hp`. Substitute `hps` using the available equality.

Use `set ph := D.ptSize h with hph`. Establish `hP : D.ptSize (h ++ [(n + 1, t)]) = ph + (n + 1)` using `Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h (n + 1) t`. Establish `ht : t ≠ 0` using `(hpb (n + 1, t) (by simp)).2`. Establish `hloc : D.IsLocPt (h ++ [(n + 1, t)]) (D.ptSize (h ++ [(n + 1, t)]))` using `⟨hpb, rfl⟩`. Establish `hlocH` using `Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc`.

Establish `hd0 : ∀ q, D.ptDiag h q ≠ 0` using `fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2`. Use `set ρ := r - D.ptSize (h ++ [(n + 1, t)]) with hρ`. Establish `hsum : ph + (n + 1) + ρ = r` using `by omega`. Establish `hspec` using `(Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1`. Establish `hspec'` using `(Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1`.

Establish `hσ : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])), ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n` using `n) (D.ptPerm h)) (Fin.cast hP q)).val = (D.ptPerm (h ++ [(n + 1, t)]) q).val := by`. Introduce `q`. Rewrite using `[hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h q.val (by have := q.isLt; omega)]`. Distinguish the cases in `h1 : q.val < D.ptSize h`. Rewrite using `[if_pos h1]`.

Establish `e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩` using `Fin.ext rfl`. Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]`. Conclude with `hspec' ⟨q.val, h1⟩`. Rewrite using `[if_neg h1]`. Establish `e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have` using `q.isLt; omega⟩ := Fin.ext (by simp; omega)`.

Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]`. Simplify using `only [Fin.val_natAdd, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Establish `hd : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])), Formalism.FourierDecayAlt.P.Dx2.SL.dP (n` using `n) (D.ptDiag h) t (Fin.cast hP q) = D.ptDiag (h ++ [(n + 1, t)]) q := by`. Introduce `q`.

Simplify using `only [D.ptDiag]`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h q.val (by have := q.isLt; omega)]`. Distinguish the cases in `h1 : q.val < D.ptSize h`. Rewrite using `[if_pos h1]`. Establish `e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩` using `Fin.ext rfl`.

Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]`. Both sides reduce to the same expression. Rewrite using `[if_neg h1]`. Establish `e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have` using `q.isLt; omega⟩ := Fin.ext (by simp; omega)`. Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]`.

Establish `hdP : ∀ q, Formalism.FourierDecayAlt.P.Dx2.SL.dP (n` using `n) (D.ptDiag h) t q ≠ 0 := by`. Introduce `q`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) q` and prove the remaining obligations. Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]`. Conclude with `hd0 i`.

Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]`. Conclude with `ht`. Establish `hS : ∀ (Gx : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ), D.sliceAt k r T.base.z T.base.z' Gx (h ++ [(n + 1, t)]) γ = U.PhiFun (p` using `ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gx) (fun a => a.elim0) γ := by`. Introduce `Gx γ`. Take `⟨-, hT2⟩` from `Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gx) γ`.

Unfold `D.sliceAt`. Rewrite using `[dif_pos (by omega), hT2]`. Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]`. Establish `e1 : r = ph + (n + 1) + ρ` using `hsum.symm`. Establish `e2 : ph + (n + 1) + ρ = r` using `hsum`.

Establish `hj1 : 1 ≤ ph + (n + 1)` using `by omega`. Take `⟨Θ, hΘ, hΘF⟩` from `Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (ph + (n + 1)) ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z') (by omega) w a hj1`. Establish `hU : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh → ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 → D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g = B.opApply Θ (D.castF e2 (D.cutF T.base χ hh …`. Introduce `hh hsm g hg hD`. Establish `hFc : B.CkOn ⊤ (B.GV k r) (D.cutF T.base χ hh ε)` using `Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hsm ε`.

Establish `h1 : D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) = D.uwG k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e2 (D.cutF T.base χ hh ε)) (ph + (n + 1)) (by omega) w a`. Rewrite using `[Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hP _ _ w a`. Rewrite using `[h1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD]`. Establish `hFrel : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh → ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 → D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g = B.opApply Θ (fun x => ((χ (Gf k (ph + (n …`.

Introduce `hh hsm g hg hD`. Rewrite using `[hU hh hsm g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]`. Use `set nd := 2 * r + k + 1 with hnd`. Use `set As := 11 * (N * nd ^ 2 + nd ^ 3) + 5 with hAs`. Take `⟨b1, b2, b3, b4, b5⟩` from `Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs r k N w.length (ph + (n + 1)) hk2 hw (by omega)`.

Establish `hmmU : P5.mmUser P0 N = 5 + 3 * (r + 1) * (N + 2) * nd + N * r`. Simplify using `only [P5.mmUser, P5.nV, hPk, hPr, hnd]`. Establish `hAU : P5.Auser P0 N = 127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)`. Simplify using `only [P5.Auser, P5.nV, hPk, hPr, hnd]`. Apply the tactic sequence `try (push_cast; try ring)`.

Establish `hX1 : (1 : ℝ) ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3` using `by exact_mod_cast b5`. Establish `hAsR : (As : ℝ) = 11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5`. Rewrite using `[hAs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hR1 : (1 : ℝ) ≤ (r : ℝ) + 1` using `by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith`. Establish `hsumR : (((ph + (n + 1) + ρ : ℕ) : ℝ)) = (r : ℝ)` using `by exact_mod_cast hsum`. Take `⟨ε', K, hε', hK0, hQ⟩` from `hCp k ph n ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z') (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem) Θ _ _ hΘ χ A₀ ε hχ hε (D.ptPerm h) (D.ptDiag h) t hd0 ht As (P5.mmUser P0 N) (P5.Au …`. Rewrite using `[hsumR, hAU, hAsR]`. Establish `hR3 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3` using `one_le_pow₀ hR1`.

Establish `: 0 ≤ ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)` using `by positivity`. Use the proof step `nlinarith)`. Use the proof step `(by`. Rewrite using `[hsumR, hAsR]`. Establish `hR4 : 0 ≤ ((r : ℝ) + 1) ^ 4` using `by positivity`.

Establish `hX0 : 0 ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3` using `by linarith`. Establish `s1 : Cp * ((r : ℝ) + 1) ^ 4 * (11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5) ≤ Cp * ((r : ℝ) + 1) ^ 4 * (16 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3))`. Apply `mul_le_mul_of_nonneg_left _ (by positivity); linarith` to reduce the goal to its premises. Establish `s2 : 16 * Cp * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) ≤ Cc * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3))` using `mul_le_mul_of_nonneg_right hCc (by positivity)`. Establish `s3 : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) ≤ A₀`.

Establish `hndR : (nd : ℝ) = 2 * (r : ℝ) + k + 1` using `by rw [hnd]; push_cast; ring`. Rewrite using `[hndR]`. Conclude with `hA₀`. Use the proof step `nlinarith)`. Establish `hfun : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) (h ++ [(n + 1, t)])) = fun γ => U.PhiFun (p` using `ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi …`.

Introduce `hh`. Rewrite using `[Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]`. Use function extensionality and compare the values at `γ`. Conclude with `hS _ γ`. Establish `hz1 : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z) = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z`.

Establish `hzl : T.base.z = D.castV (by omega) (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z)` using `(T.z_lev _ hi).symm`. Rewrite using `[hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _`. Establish `hz1' : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z') = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z'`. Establish `hzl' : T.base.z' = D.castV (by omega) (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z')` using `(T.z'_lev _ hi).symm`.

Rewrite using `[hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _`. Establish `hZ0 : G.detM (fun a => a.elim0 : G.Mat 0) ≠ 0`. Unfold `G.detM`. Rewrite using `[Matrix.det_isEmpty]`.

Conclude with `one_ne_zero`. Use `⟨ε', K, hε', hK0, ?_, ?_⟩` and prove the remaining obligations. Introduce `hh c hsm hcl`. Take `⟨h1, h2, -⟩` from `hQ (D.castF e2 hh) c (ccle_castF e2 hcl) _ (hFrel hh hsm)`. Rewrite using `[hfun hh]`.

Use `⟨⟨h1.1, ⟨_, h1⟩, fun γ hγ hne => ?_⟩, h1⟩` and prove the remaining obligations. Use `h2 γ hγ hne` as an intermediate fact. Rewrite `this` using `[hz1, hz1']`. Then use the resulting hypothesis. Introduce `h₁ h₂ c₁ c₂ hs₁ hs₂ hc₁ hc₂ γ hγ`. Establish `hs₁₂ : B.CkOn ⊤ (B.GV k r) (fun g => h₁ g - h₂ g)`.

Use `BetaSesquilinearity.CkOn_add hs₁ (BetaSesquilinearity.CkOn_smul (-1) hs₂)` as an intermediate fact. Use `this using 2 with g` and compare the differences between its conclusion and the goal. Simplify using `[sub_eq_add_neg]`. Establish `I₁` using `(hQ (D.castF e2 h₁) c₁ (ccle_castF e2 hc₁) _ (hFrel h₁ hs₁)).2.2 γ hγ`. Establish `I₂` using `(hQ (D.castF e2 h₂) c₂ (ccle_castF e2 hc₂) _ (hFrel h₂ hs₂)).2.2 γ hγ`.

Rewrite using `[hfun h₁, hfun h₂, hfun (fun g => h₁ g - h₂ g)]`. Use `show U.PhiFun _ _ _ _ _ _ _ _ γ - U.PhiFun _ _ _ _ _ _ _ _ γ = U.PhiFun _ _ _ _ _ _ _ _ γ`. Unfold `U.PhiFun`. Rewrite using `[← integral_sub I₁ I₂]`. Use `integral_congr_ae (Eventually.of_forall fun ξ => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← smul_sub]`. Use `congr 1`. Use `set y := U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ with hy`. Establish `hyG : y ∈ B.GV k (ph + (n + 1) + 0 + ρ)` using `Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation _ _ hdP ξ _ hZ0 hγ`.

Establish `hDj : U.DjU k (ph + (n + 1) + 0) ρ y ≠ 0`. Rewrite using `[Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice]`. Conclude with `mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hdP) hZ0`. Establish `hc₁'` using `Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hs₁ ε)`. Establish `hc₂'` using `Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hs₂ ε)`.

Rewrite using `[hU h₁ hs₁ y hyG hDj, hU h₂ hs₂ y hyG hDj, hU _ hs₁₂ y hyG hDj, ← opApply_sub Θ hc₁' hc₂' y hyG]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [D.castF, D.cutF, smul_sub]`.
-/
theorem levQ : ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ Cc : ℝ, 16 * Cp ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r), 1 ≤ i → ∀ (w : List C.Letter), w.length ≤ N →
      ∀ (p : C.LPt) (hc : r - i = r - D.ptSize p), D.IsLocPt p i → ∀ (a : Wd.Ix (Fin w.length)),
      ∃ ε' K : ℝ, 0 < ε' ∧ 0 ≤ K ∧
      (∀ (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
          (D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ h ε) i hi w a) p)) ∧
        B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N)
          (D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ h ε) i hi w a) p))
          (K * c)) ∧
      ∀ (h₁ h₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (c₁ c₂ : ℝ), B.CkOn ⊤ (B.GV k r) h₁ → B.CkOn ⊤ (B.GV k r) h₂ →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h₁ c₁ →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h₂ c₂ →
        ∀ γ ∈ B.GV k (r - i),
          D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ h₁ ε) i hi w a) p) γ -
          D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ h₂ ε) i hi w a) p) γ =
          D.castF hc (D.sliceAt k r T.base.z T.base.z'
            (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ (fun g => h₁ g - h₂ g) ε) i hi w a) p) γ := by
  obtain ⟨Cp, hCp0, hCp⟩ := posCoreQ
  refine ⟨Cp, hCp0, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi hi1 w hw p hc hp a

  obtain ⟨h, n, t, rfl⟩ : ∃ (h : C.LPt) (n : ℕ) (t : ℂ), p = h ++ [(n + 1, t)] := by
    have hne : p ≠ [] := by
      rintro rfl
      have := hp.2
      simp [D.ptSize] at this
      omega
    refine ⟨p.dropLast, (p.getLast hne).1 - 1, (p.getLast hne).2, ?_⟩
    have h1 : 1 ≤ (p.getLast hne).1 := (hp.1 _ (List.getLast_mem hne)).1
    rw [Nat.sub_add_cancel h1]
    exact (List.dropLast_append_getLast hne).symm
  obtain ⟨hpb, hps⟩ := hp
  subst hps
  set ph := D.ptSize h with hph
  have hP : D.ptSize (h ++ [(n + 1, t)]) = ph + (n + 1) := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h (n + 1) t
  have ht : t ≠ 0 := (hpb (n + 1, t) (by simp)).2
  have hloc : D.IsLocPt (h ++ [(n + 1, t)]) (D.ptSize (h ++ [(n + 1, t)])) := ⟨hpb, rfl⟩
  have hlocH := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc
  have hd0 : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2
  set ρ := r - D.ptSize (h ++ [(n + 1, t)]) with hρ
  have hsum : ph + (n + 1) + ρ = r := by omega
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  have hσ : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h)) (Fin.cast hP q)).val = (D.ptPerm (h ++ [(n + 1, t)]) q).val := by
    intro q
    rw [hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨q.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t (Fin.cast hP q) = D.ptDiag (h ++ [(n + 1, t)]) q := by
    intro q
    simp only [D.ptDiag]
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]
  have hdP : ∀ q, Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t q ≠ 0 := by
    intro q
    refine Fin.addCases (fun i => ?_) (fun i => ?_) q
    · simp only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; exact hd0 i
    · simp only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]; exact ht
  have hS : ∀ (Gx : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ), D.sliceAt k r T.base.z T.base.z' Gx (h ++ [(n + 1, t)]) γ =
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z')
        (D.castF (by omega) Gx) (fun a => a.elim0) γ := by
    intro Gx γ
    obtain ⟨-, hT2⟩ := Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd
      (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gx) γ
    unfold D.sliceAt
    rw [dif_pos (by omega), hT2]
    simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]
  have e1 : r = ph + (n + 1) + ρ := hsum.symm
  have e2 : ph + (n + 1) + ρ = r := hsum
  have hj1 : 1 ≤ ph + (n + 1) := by omega
  obtain ⟨Θ, hΘ, hΘF⟩ := Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (ph + (n + 1)) ρ Wp Wq (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (by omega) w a hj1
  have hU : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g =
        B.opApply Θ (D.castF e2 (D.cutF T.base χ hh ε)) g := by
    intro hh hsm g hg hD
    have hFc : B.CkOn ⊤ (B.GV k r) (D.cutF T.base χ hh ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hsm ε
    have h1 : D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) =
        D.uwG k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.cutF T.base χ hh ε)) (ph + (n + 1)) (by omega) w a := by
      rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hP _ _ w a
    rw [h1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD]
  have hFrel : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g =
        B.opApply Θ (fun x => ((χ (Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z)
          (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 hh x) g := by
    intro hh hsm g hg hD
    rw [hU hh hsm g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]
  set nd := 2 * r + k + 1 with hnd
  set As := 11 * (N * nd ^ 2 + nd ^ 3) + 5 with hAs
  obtain ⟨b1, b2, b3, b4, b5⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs r k N w.length (ph + (n + 1)) hk2 hw (by omega)
  have hmmU : P5.mmUser P0 N = 5 + 3 * (r + 1) * (N + 2) * nd + N * r := by
    simp only [P5.mmUser, P5.nV, hPk, hPr, hnd]
  have hAU : P5.Auser P0 N = 127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by
    simp only [P5.Auser, P5.nV, hPk, hPr, hnd]
    try (push_cast; try ring)
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by exact_mod_cast b5
  have hAsR : (As : ℝ) = 11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5 := by
    rw [hAs]; push_cast; ring
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  have hsumR : (((ph + (n + 1) + ρ : ℕ) : ℝ)) = (r : ℝ) := by exact_mod_cast hsum
  obtain ⟨ε', K, hε', hK0, hQ⟩ := hCp k ph n ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
    Θ _ _ hΘ χ A₀ ε hχ hε (D.ptPerm h) (D.ptDiag h) t hd0 ht As (P5.mmUser P0 N) (P5.Auser P0 N + 1)
    b1 b2 (by rw [hmmU]; exact b3) (by rw [hsum]; exact b4)
    (by
      rw [hsumR, hAU, hAsR]
      have hR3 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
      have : 0 ≤ ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by positivity
      nlinarith)
    (by
      rw [hsumR, hAsR]
      have hR4 : 0 ≤ ((r : ℝ) + 1) ^ 4 := by positivity
      have hX0 : 0 ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by linarith
      have s1 : Cp * ((r : ℝ) + 1) ^ 4 * (11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5) ≤
          Cp * ((r : ℝ) + 1) ^ 4 * (16 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      have s2 : 16 * Cp * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) ≤
          Cc * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_right hCc (by positivity)
      have s3 : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) ≤ A₀ := by
        have hndR : (nd : ℝ) = 2 * (r : ℝ) + k + 1 := by rw [hnd]; push_cast; ring
        rw [hndR]; exact hA₀
      nlinarith)
  have hfun : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp),
      D.castF hc (D.sliceAt k r T.base.z T.base.z'
        (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) (h ++ [(n + 1, t)])) =
      fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a))
        (fun a => a.elim0) γ := by
    intro hh
    rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]
    funext γ
    exact hS _ γ
  have hz1 : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z) = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z := by
    have hzl : T.base.z = D.castV (by omega)
        (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z) :=
      (T.z_lev _ hi).symm
    rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _
  have hz1' : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z') = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z' := by
    have hzl' : T.base.z' = D.castV (by omega)
        (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z') :=
      (T.z'_lev _ hi).symm
    rw [hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _
  have hZ0 : G.detM (fun a => a.elim0 : G.Mat 0) ≠ 0 := by
    unfold G.detM; rw [Matrix.det_isEmpty]; exact one_ne_zero
  refine ⟨ε', K, hε', hK0, ?_, ?_⟩
  · intro hh c hsm hcl
    obtain ⟨h1, h2, -⟩ := hQ (D.castF e2 hh) c (ccle_castF e2 hcl) _ (hFrel hh hsm)
    rw [hfun hh]
    refine ⟨⟨h1.1, ⟨_, h1⟩, fun γ hγ hne => ?_⟩, h1⟩
    have := h2 γ hγ hne
    rwa [hz1, hz1'] at this
  · intro h₁ h₂ c₁ c₂ hs₁ hs₂ hc₁ hc₂ γ hγ
    have hs₁₂ : B.CkOn ⊤ (B.GV k r) (fun g => h₁ g - h₂ g) := by
      have := BetaSesquilinearity.CkOn_add hs₁ (BetaSesquilinearity.CkOn_smul (-1) hs₂)
      convert this using 2 with g
      simp [sub_eq_add_neg]
    have I₁ := (hQ (D.castF e2 h₁) c₁ (ccle_castF e2 hc₁) _ (hFrel h₁ hs₁)).2.2 γ hγ
    have I₂ := (hQ (D.castF e2 h₂) c₂ (ccle_castF e2 hc₂) _ (hFrel h₂ hs₂)).2.2 γ hγ
    rw [hfun h₁, hfun h₂, hfun (fun g => h₁ g - h₂ g)]
    show U.PhiFun _ _ _ _ _ _ _ _ γ - U.PhiFun _ _ _ _ _ _ _ _ γ = U.PhiFun _ _ _ _ _ _ _ _ γ
    unfold U.PhiFun
    rw [← integral_sub I₁ I₂]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [← smul_sub]
    congr 1
    set y := U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
      (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ with hy
    have hyG : y ∈ B.GV k (ph + (n + 1) + 0 + ρ) :=
      Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation _ _ hdP ξ _ hZ0 hγ
    have hDj : U.DjU k (ph + (n + 1) + 0) ρ y ≠ 0 := by
      rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice]
      exact mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hdP) hZ0
    have hc₁' := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hs₁ ε)
    have hc₂' := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hs₂ ε)
    rw [hU h₁ hs₁ y hyG hDj, hU h₂ hs₂ y hyG hDj, hU _ hs₁₂ y hyG hDj, ← opApply_sub Θ hc₁' hc₂' y hyG]
    congr 1
    funext x
    simp only [D.castF, D.cutF, smul_sub]

end Formalism.FourierDecayAlt.P.PBE

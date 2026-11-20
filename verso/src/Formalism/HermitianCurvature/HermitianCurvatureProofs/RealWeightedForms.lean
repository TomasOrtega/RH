import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualKernelLemmas

namespace Formalism.FourierDecayAlt.P.RealWeightedForms

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix

/- English proof (translation)
Introduce `S _ _ q w Y hq hw`. Proceed by induction on `w with`. Consider the case `nil`. Simplify using `only [qw, List.map_nil]`. Conclude with `Complex.ext (by simp) (by simpa using hq)`.

Consider the case `cons l w ih`. Establish `him` using `hw l (List.mem_cons_self ..)`. Establish `ih'` using `ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))`. Take `⟨plus, intersection_update_fsHerm_neg_one, pt⟩` from `l`. Take `⟨p, rfl⟩ : ∃ p : ℝ, pt = p` from `⟨pt.re, Complex.ext (by simp) (by simpa using him)⟩`.

Apply the tactic sequence `cases plus <;> simp [qw, ih']`.
-/
theorem qwOfReal : QwOfReal := by
  intro S _ _ q w Y hq hw
  induction w with
  | nil =>
    simp only [qw, List.map_nil]
    exact Complex.ext (by simp) (by simpa using hq)
  | cons l w ih =>
    have him := hw l (List.mem_cons_self ..)
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨plus, intersection_update_fsHerm_neg_one, pt⟩ := l
    obtain ⟨p, rfl⟩ : ∃ p : ℝ, pt = p := ⟨pt.re, Complex.ext (by simp) (by simpa using him)⟩
    cases plus <;> simp [qw, ih']

section admitted

variable {S : Type}

def Cnd (l l' : Letter ℂ S) : Prop :=
  if l'.plus then
    2 < |l.pt.re - l'.pt.re| ∧ 2 < |l.pt.re - l'.pt.re + 1| ∧ 2 < |l.pt.re - l'.pt.re - 1|
  else
    2 < |l'.pt.re - l.pt.re| ∧ 2 < |l'.pt.re - l.pt.re - 1| ∧ 2 < |l'.pt.re - l.pt.re - 2|

/- English proof (translation)
Rewrite using `[List.pairwise_iff_get]`. Introduce `i j hij`. Conclude with `⟨h.2.2 i j (ne_of_lt hij), h.2.2 j i (ne_of_lt hij).symm⟩`.
-/
theorem admissible_word_pairwise_condition {α β : ℝ} {w : List (Letter ℂ S)} (h : GrowthHypotheses α β w) :
    w.Pairwise (fun l l' => Cnd l l' ∧ Cnd l' l) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  exact ⟨h.2.2 i j (ne_of_lt hij), h.2.2 j i (ne_of_lt hij).symm⟩

/- English proof (translation)
Unfold `Cnd at h`. Unfold `RegL`. Consider the cases of `hp : l'.plus`. Simplify using `only [hp, Bool.false_eq_true, if_false] at h ⊢`. Introduce `he`.

Establish `hre` using `congrArg Complex.re he`. Simplify using `only [Complex.sub_re, Complex.one_re] at hre`. Rewrite `h` using `[hre]`. Evaluate the numerical expressions using `at h`. Simplify using `only [hp, if_true] at h ⊢`.

Introduce `he`. Establish `hre` using `congrArg Complex.re he`. Simplify using `only [Complex.sub_re, Complex.one_re] at hre`. Rewrite `h` using `[hre]`. Evaluate the numerical expressions using `at h`.
-/
theorem regL_of_cnd {l l' : Letter ℂ S} (h : Cnd l l') : RegL l' l.pt := by
  unfold Cnd at h
  unfold RegL
  cases hp : l'.plus
  · simp only [hp, Bool.false_eq_true, if_false] at h ⊢
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hre] at h
    norm_num at h
  · simp only [hp, if_true] at h ⊢
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hre] at h
    norm_num at h

/- English proof (translation)
Use `⟨h.1, fun l hl => ?_, (admissible_word_pairwise_condition h).imp fun hc => regL_of_cnd hc.1⟩` and prove the remaining obligations. Rewrite using `[Complex.star_def]`. Conclude with `Complex.conj_eq_iff_im.2 (h.2.1 l hl).1`.
-/
theorem good_of_adm {α β : ℝ} {w : List (Letter ℂ S)} (h : GrowthHypotheses α β w) : Good w := by
  refine ⟨h.1, fun l hl => ?_, (admissible_word_pairwise_condition h).imp fun hc => regL_of_cnd hc.1⟩
  rw [Complex.star_def]
  exact Complex.conj_eq_iff_im.2 (h.2.1 l hl).1

/- English proof (translation)
Use `⟨by simp [hz.1], ?_⟩` and prove the remaining obligations. Establish `e : (z * r).re = z.re * r` using `by simp [hz.1]`. Rewrite using `[e]`. Conclude with `mul_pos hz.2 hr`.
-/
theorem pos_mul_ofReal {z : ℂ} {r : ℝ} (hz : z.im = 0 ∧ 0 < z.re) (hr : 0 < r) :
    (z * r).im = 0 ∧ 0 < (z * r).re := by
  refine ⟨by simp [hz.1], ?_⟩
  have e : (z * r).re = z.re * r := by simp [hz.1]
  rw [e]
  exact mul_pos hz.2 hr

/- English proof (translation)
Apply the tactic sequence `rcases lt_abs.1 ha with ha' | ha' <;> rcases hab with rfl | rfl`. Conclude with `div_pos (by linarith) (by linarith)`. Conclude with `div_pos (by linarith) (by linarith)`. Conclude with `div_pos_of_neg_of_neg (by linarith) (by linarith)`. Conclude with `div_pos_of_neg_of_neg (by linarith) (by linarith)`.
-/
theorem same_sign_pos {a b : ℝ} (ha : 2 < |a|) (hb : 2 < |b|) (hab : b = a + 1 ∨ b = a - 1) :
    0 < a / b := by
  rcases lt_abs.1 ha with ha' | ha' <;> rcases hab with rfl | rfl
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)

def CndY (Y : ℝ) (l' : Letter ℂ S) : Prop :=
  if l'.plus then
    2 < |Y - l'.pt.re| ∧ 2 < |Y - l'.pt.re + 1| ∧ 2 < |Y - l'.pt.re - 1|
  else
    2 < |l'.pt.re - Y| ∧ 2 < |l'.pt.re - Y - 1| ∧ 2 < |l'.pt.re - Y - 2|

/- English proof (translation)
Introduce `w`. Proceed by induction on `w with`. Consider the case `nil`. Introduce `_`. Simplify `hq` using `[qw]`.

Consider the case `cons l w ih`. Introduce `hw`. Take `⟨hl, hc⟩` from `hw l (List.mem_cons_self ..)`. Establish `ih'` using `ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))`. Take `⟨plus, intersection_update_fsHerm_neg_one, pt⟩` from `l`.

Take `⟨p, rfl⟩ : ∃ p : ℝ, pt = p` from `⟨pt.re, Complex.ext (by simp) (by simpa using hl)⟩`. Consider the cases of `plus`. Simplify using `only [CndY, Bool.false_eq_true, if_false, Complex.ofReal_re] at hc`. Establish `hpos` using `same_sign_pos hc.1 hc.2.1 (Or.inr rfl)`. Establish `e : qw q ({ plus` using `false, intersection_update_fsHerm_neg_one := intersection_update_fsHerm_neg_one, pt := (p : ℂ) } :: w) (Y : ℂ) = qw q w (Y : ℂ) * (((p - Y) / (p - Y - 1) : ℝ) : ℂ) := by`.

Simplify using `[qw]`. Rewrite using `[e]`. Conclude with `pos_mul_ofReal ih' hpos`. Simplify using `only [CndY, if_true, Complex.ofReal_re] at hc`. Establish `hpos` using `same_sign_pos hc.2.1 hc.1 (Or.inr (by ring))`.

Establish `e : qw q ({ plus` using `true, intersection_update_fsHerm_neg_one := intersection_update_fsHerm_neg_one, pt := (p : ℂ) } :: w) (Y : ℂ) = qw q w (Y : ℂ) * (((Y - p + 1) / (Y - p) : ℝ) : ℂ) := by`. Simplify using `[qw]`. Rewrite using `[e]`. Conclude with `pos_mul_ofReal ih' hpos`.
-/
theorem qw_pos (q : ℂ → ℂ) (Y : ℝ) (hq : (q Y).im = 0 ∧ 0 < (q Y).re) :
    ∀ w : List (Letter ℂ S), (∀ l' ∈ w, l'.pt.im = 0 ∧ CndY Y l') →
      (qw q w (Y : ℂ)).im = 0 ∧ 0 < (qw q w (Y : ℂ)).re := by
  intro w
  induction w with
  | nil =>
    intro _
    simpa [qw] using hq
  | cons l w ih =>
    intro hw
    obtain ⟨hl, hc⟩ := hw l (List.mem_cons_self ..)
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨plus, intersection_update_fsHerm_neg_one, pt⟩ := l
    obtain ⟨p, rfl⟩ : ∃ p : ℝ, pt = p := ⟨pt.re, Complex.ext (by simp) (by simpa using hl)⟩
    cases plus
    · simp only [CndY, Bool.false_eq_true, if_false, Complex.ofReal_re] at hc
      have hpos := same_sign_pos hc.1 hc.2.1 (Or.inr rfl)
      have e : qw q ({ plus := false, intersection_update_fsHerm_neg_one := intersection_update_fsHerm_neg_one, pt := (p : ℂ) } :: w) (Y : ℂ) =
          qw q w (Y : ℂ) * (((p - Y) / (p - Y - 1) : ℝ) : ℂ) := by
        simp [qw]
      rw [e]
      exact pos_mul_ofReal ih' hpos
    · simp only [CndY, if_true, Complex.ofReal_re] at hc
      have hpos := same_sign_pos hc.2.1 hc.1 (Or.inr (by ring))
      have e : qw q ({ plus := true, intersection_update_fsHerm_neg_one := intersection_update_fsHerm_neg_one, pt := (p : ℂ) } :: w) (Y : ℂ) =
          qw q w (Y : ℂ) * (((Y - p + 1) / (Y - p) : ℝ) : ℂ) := by
        simp [qw]
      rw [e]
      exact pos_mul_ofReal ih' hpos

end admitted

/- English proof (translation)
Introduce `S _ _ α β q w L hL hG h1 h2`. Establish `hpw` using `List.pairwise_append.1 (admissible_word_pairwise_condition h1)`. Establish `hreal : ∀ l ∈ L, l.pt = ((l.pt.re : ℝ) : ℂ)` using `fun l hl => Complex.ext (by simp) (by simpa using (h1.2.1 l (List.mem_append_left w hl)).1)`. Establish `hpos : ∀ l ∈ L, (qw q w l.pt).im = 0 ∧ 0 < (qw q w l.pt).re`. Introduce `l hl`.

Establish `hq` using `hG l.pt.re (h1.2.1 l (List.mem_append_left w hl)).2.1`. Rewrite using `[hreal l hl]`. Use `qw_pos q l.pt.re hq w fun l' hl' => ⟨(h1.2.1 l' (List.mem_append_right L hl')).1, ?_⟩` and prove the remaining obligations. Establish `hc` using `(hpw.2.2 l hl l' hl').1`. Unfold `Cnd at hc`.

Conclude with `hc`. Use `⟨⟨hL, good_of_adm h1, good_of_adm h2, ?_, fun l hl => ?_⟩, hpos⟩` and prove the remaining obligations. Use `hpw.1.imp_of_mem fun {l l'} hl hl' hc => ?_` and prove the remaining obligations. Establish `hc1` using `hc.1`. Unfold `Cnd at hc1`.

Rewrite `hc1` using `[if_pos (hL l' hl')]`. Rewrite using `[hreal l hl, hreal l' hl']`. Use `⟨fun he => ?_, fun he => ?_, fun he => ?_⟩` and prove the remaining obligations. Establish `hre` using `congrArg Complex.re he`. Simplify using `only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre`.

Rewrite `hc1` using `[hre]`. Evaluate the numerical expressions using `at hc1`. Establish `hre` using `congrArg Complex.re he`. Simplify using `only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at hre`. Rewrite `hc1` using `[hre]`.

Evaluate the numerical expressions using `at hc1`. Establish `hre` using `congrArg Complex.re he`. Simplify using `only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re, Complex.one_re] at hre`. Rewrite `hc1` using `[hre]`. Evaluate the numerical expressions using `at hc1`.

Introduce `h0`. Use `(hpos l hl).2` as an intermediate fact. Rewrite `this` using `[h0, Complex.zero_re]`. Conclude with `lt_irrefl _ this`.
-/
theorem admissible_dual_kernel_identity : AdmDK := by
  intro S _ _ α β q w L hL hG h1 h2
  have hpw := List.pairwise_append.1 (admissible_word_pairwise_condition h1)
  have hreal : ∀ l ∈ L, l.pt = ((l.pt.re : ℝ) : ℂ) := fun l hl =>
    Complex.ext (by simp) (by simpa using (h1.2.1 l (List.mem_append_left w hl)).1)
  have hpos : ∀ l ∈ L, (qw q w l.pt).im = 0 ∧ 0 < (qw q w l.pt).re := by
    intro l hl
    have hq := hG l.pt.re (h1.2.1 l (List.mem_append_left w hl)).2.1
    rw [hreal l hl]
    refine qw_pos q l.pt.re hq w fun l' hl' => ⟨(h1.2.1 l' (List.mem_append_right L hl')).1, ?_⟩
    have hc := (hpw.2.2 l hl l' hl').1
    unfold Cnd at hc
    exact hc
  refine ⟨⟨hL, good_of_adm h1, good_of_adm h2, ?_, fun l hl => ?_⟩, hpos⟩
  · refine hpw.1.imp_of_mem fun {l l'} hl hl' hc => ?_
    have hc1 := hc.1
    unfold Cnd at hc1
    rw [if_pos (hL l' hl')] at hc1
    rw [hreal l hl, hreal l' hl']
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
      rw [hre] at hc1
      norm_num at hc1
    · have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at hre
      rw [hre] at hc1
      norm_num at hc1
    · have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re, Complex.one_re] at hre
      rw [hre] at hc1
      norm_num at hc1
  · intro h0
    have := (hpos l hl).2
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this

/- English proof (translation)
Rewrite using `[Complex.div_ofReal_re, Complex.mul_re, hu, zero_mul, sub_zero]`.
-/
theorem re_mul_div (u v : ℂ) (r : ℝ) (hu : u.im = 0) : (u * v / r).re = u.re * v.re / r := by
  rw [Complex.div_ofReal_re, Complex.mul_re, hu, zero_mul, sub_zero]

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

/- English proof (translation)
Establish `hPA` using `fun (M N : SlopeTestRemainingChoices S A) (Y Y' : Ix S → V) => GramProductIdentities.pairAdj A S V ρ M N 1 Y Y'`. Unfold `frm`. Establish `h1` using `(hPA (star W) 1 (act RR (act W X)) X').2.2.2`. Rewrite `h1` using `[star_star]`. Rewrite using `[← h1, ← (hPA (star W) RR (act W X) X').1, ← (hPA (star W * RR) W X X').1, hW]`.
-/
theorem frm_act_act_of_star_mul_mul_eq (ρ : Rep A V) (RR W : SlopeTestRemainingChoices S A) (hW : star W * RR * W = RR) (X X' : Ix S → V) :
    frm ρ RR (act W X) (act W X') = frm ρ RR X X' := by
  have hPA := fun (M N : SlopeTestRemainingChoices S A) (Y Y' : Ix S → V) => GramProductIdentities.pairAdj A S V ρ M N 1 Y Y'
  unfold frm
  have h1 := (hPA (star W) 1 (act RR (act W X)) X').2.2.2
  rw [star_star] at h1
  rw [← h1, ← (hPA (star W) RR (act W X) X').1, ← (hPA (star W * RR) W X X').1, hW]

end Rep

/- English proof (translation)
Unfold `Lp`. Rewrite using `[List.mem_ofFn]`. Conclude with `⟨a, rfl⟩`.
-/
theorem mem_Lp {S : Type} {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ) (a : Fin K) :
    (⟨true, sl a, (y a : ℂ)⟩ : Letter ℂ S) ∈ Lp sl y := by
  unfold Lp
  rw [List.mem_ofFn]
  exact ⟨a, rfl⟩

/- English proof (translation)
Introduce `l hl`. Unfold `Lp at hl`. Rewrite `hl` using `[List.mem_ofFn]`. Take `⟨a, rfl⟩` from `hl`. Both sides reduce to the same expression.
-/
theorem plus_Lp {S : Type} {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ) :
    ∀ l ∈ Lp sl y, l.plus = true := by
  intro l hl
  unfold Lp at hl
  rw [List.mem_ofFn] at hl
  obtain ⟨a, rfl⟩ := hl
  rfl

/- English proof (translation)
Unfold `Lp`. Rewrite using `[List.map_ofFn, List.prod_ofFn]`. Both sides reduce to the same expression.
-/
theorem prod_Lp {S : Type} {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ) (g : ℂ → ℂ) :
    ((Lp sl y).map fun l => g l.pt).prod = ∏ a, g (y a) := by
  unfold Lp
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

/- English proof (translation)
Introduce `hDK hPW hPA hAdm A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x α β y hD hG hI h1 h2`. Take `⟨hS, hW, hWQ, -, -, -, -, -, -, -, -⟩` from `hD`. Take `⟨hDKH, hpos⟩` from `hAdm S α β q w (Lp sl y) (plus_Lp sl y) hG h1 h2`. Take `⟨-, -, hinv, -⟩` from `hPW ℂ A S QQ f fi s (Lp sl y ++ w) hW hWQ h1.1`. Take `⟨-, hle⟩` from `hDK A S V ρ QQ q w (Lp sl y) hS hDKH (hI _ h1) (act (Vw f s (Lp sl y ++ w)) (letters vA vB (Lp sl y) x)) (letters vAv vBv ((Lp sl y).map dl) x)`.

Rewrite `hle` using `[frm_act_act_of_star_mul_mul_eq ρ _ _ hinv]`. Establish `hWK : WK ρ QQ f s w vA vB vAv vBv sl y x = pair ρ (act (JL (Lp sl y) * RRw QQ w) (act (Vw f s (Lp sl y ++ w)) (letters vA vB (Lp sl y) x))) (letters vAv vBv ((Lp sl y).map dl) x)`. Unfold `WK`. Use `congr 1`. Conclude with `(hPA A S V ρ (JL (Lp sl y) * RRw QQ w) (Vw f s (Lp sl y ++ w)) 1 (letters vA vB (Lp sl y) x) (letters vAv vBv ((Lp sl y).map dl) x)).1`.

Rewrite using `[hWK]`. Use `hle.trans_eq ?_` and prove the remaining obligations. Establish `hP : ((Lp sl y).map fun l => qw q w l.pt).prod = ((∏ a, (qw q w (y a)).re : ℝ) : ℂ)`. Rewrite using `[prod_Lp sl y (qw q w), Complex.ofReal_prod]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Establish `hm` using `(hpos _ (mem_Lp sl y a)).1`. Conclude with `Complex.ext (by simp) (by simpa using hm)`. Rewrite using `[hP, re_mul_div _ _ _ ((hI _ h1) _).2]`.
-/
private theorem sizeBoundOfParts_statement : SizeBoundOfParts := by
  intro hDK hPW hPA hAdm A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x α β y hD hG hI h1 h2
  obtain ⟨hS, hW, hWQ, -, -, -, -, -, -, -, -⟩ := hD
  obtain ⟨hDKH, hpos⟩ := hAdm S α β q w (Lp sl y) (plus_Lp sl y) hG h1 h2
  obtain ⟨-, -, hinv, -⟩ := hPW ℂ A S QQ f fi s (Lp sl y ++ w) hW hWQ h1.1
  obtain ⟨-, hle⟩ := hDK A S V ρ QQ q w (Lp sl y) hS hDKH (hI _ h1)
    (act (Vw f s (Lp sl y ++ w)) (letters vA vB (Lp sl y) x)) (letters vAv vBv ((Lp sl y).map dl) x)
  rw [frm_act_act_of_star_mul_mul_eq ρ _ _ hinv] at hle
  have hWK : WK ρ QQ f s w vA vB vAv vBv sl y x =
      pair ρ (act (JL (Lp sl y) * RRw QQ w) (act (Vw f s (Lp sl y ++ w)) (letters vA vB (Lp sl y) x)))
        (letters vAv vBv ((Lp sl y).map dl) x) := by
    unfold WK
    congr 1
    exact (hPA A S V ρ (JL (Lp sl y) * RRw QQ w) (Vw f s (Lp sl y ++ w)) 1
      (letters vA vB (Lp sl y) x) (letters vAv vBv ((Lp sl y).map dl) x)).1
  rw [hWK]
  refine hle.trans_eq ?_
  have hP : ((Lp sl y).map fun l => qw q w l.pt).prod = ((∏ a, (qw q w (y a)).re : ℝ) : ℂ) := by
    rw [prod_Lp sl y (qw q w), Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hm := (hpos _ (mem_Lp sl y a)).1
    exact Complex.ext (by simp) (by simpa using hm)
  rw [hP, re_mul_div _ _ _ ((hI _ h1) _).2]

/- English proof (translation)
Conclude with `sizeBoundOfParts_statement DualKernelLemmas.lemmaDK Formalism.FourierDecayAlt.P.plane_wave_word_identity GramProductIdentities.pairAdj admissible_dual_kernel_identity`.
-/
theorem first_polynomial_size : AdmissiblePointSizeBound := by
  exact sizeBoundOfParts_statement DualKernelLemmas.lemmaDK Formalism.FourierDecayAlt.P.plane_wave_word_identity GramProductIdentities.pairAdj admissible_dual_kernel_identity

/- English proof (translation)
The claim follows from `sizeBoundOfParts_statement`.
-/
theorem first_polynomial_size_of_parts : SizeBoundOfParts := sizeBoundOfParts_statement

end Formalism.FourierDecayAlt.P.RealWeightedForms

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.RealWeightedForms.qwOfReal`.
-/
theorem Formalism.FourierDecayAlt.P.weighted_quadratic_of_real : Formalism.FourierDecayAlt.FormPairingAction.QwOfReal := Formalism.FourierDecayAlt.P.RealWeightedForms.qwOfReal
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.RealWeightedForms.admissible_dual_kernel_identity`.
-/
theorem Formalism.FourierDecayAlt.P.admDK_statement : Formalism.FourierDecayAlt.FormPairingAction.AdmDK := Formalism.FourierDecayAlt.P.RealWeightedForms.admissible_dual_kernel_identity
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size`.
-/
theorem Formalism.FourierDecayAlt.P.admissible_point_size_bound : Formalism.FourierDecayAlt.FormPairingAction.AdmissiblePointSizeBound := Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size_of_parts`.
-/
theorem Formalism.FourierDecayAlt.P.first_polynomial_size_of_clauses : Formalism.FourierDecayAlt.FormPairingAction.SizeBoundOfParts := Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size_of_parts

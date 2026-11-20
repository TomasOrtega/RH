import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecDesc

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

open Formalism.FourierDecayAlt.P.Qx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section iter

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ}

def lev (r i : ℕ) : Fin (r + 1) := ⟨min i r, by omega⟩

/- English proof (translation)
The claim follows from `Fin.ext (by simp [lev]; omega)`.
-/
theorem lev_castSucc (i : ℕ) (h : i < r) : (⟨i, h⟩ : Fin r).castSucc = lev r i := Fin.ext (by simp [lev]; omega)
/- English proof (translation)
The claim follows from `Fin.ext (by simp [lev]; omega)`.
-/
theorem lev_succ (i : ℕ) (h : i < r) : (⟨i, h⟩ : Fin r).succ = lev r (i + 1) := Fin.ext (by simp [lev]; omega)
/- English proof (translation)
The claim follows from `Fin.ext (by simp [lev])`.
-/
theorem lev_r : lev r r = Fin.last r := Fin.ext (by simp [lev])
/- English proof (translation)
The claim follows from `Fin.ext (by simp [lev])`.
-/
theorem lev_zero : lev r 0 = 0 := Fin.ext (by simp [lev])

def Dn (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) : Set (Mx k r) :=
  if h : i < r then D0 k r ⟨i, h⟩ (Dn z z' (i + 1)) else Qx8.Dp k r z z'
termination_by r - i

def Kn (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) (i : ℕ) : Fn k r (Wq →L[ℂ] Wp) :=
  if h : i < r then JxF ⟨i, h⟩ z z' (Kn z z' Φ (i + 1)) else Φ
termination_by r - i

/- English proof (translation)
Rewrite using `[Dn, dif_pos h]`.
-/
theorem Dn_lt (z z' : Fin (2 * r + k + 1) → ℂ) {i : ℕ} (h : i < r) :
    Dn z z' i = D0 k r ⟨i, h⟩ (Dn z z' (i + 1)) := by
  rw [Dn, dif_pos h]

/- English proof (translation)
Rewrite using `[Dn, dif_neg h]`.
-/
theorem Dn_ge (z z' : Fin (2 * r + k + 1) → ℂ) {i : ℕ} (h : ¬ i < r) : Dn z z' i = Qx8.Dp k r z z' := by
  rw [Dn, dif_neg h]

/- English proof (translation)
Rewrite using `[Kn, dif_pos h]`.
-/
theorem Kn_lt (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) {i : ℕ} (h : i < r) :
    Kn z z' Φ i = JxF ⟨i, h⟩ z z' (Kn z z' Φ (i + 1)) := by
  rw [Kn, dif_pos h]

/- English proof (translation)
Rewrite using `[Kn, dif_neg h]`.
-/
theorem Kn_ge (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) {i : ℕ} (h : ¬ i < r) :
    Kn z z' Φ i = Φ := by
  rw [Kn, dif_neg h]

/- English proof (translation)
Use `⟨fun c hc => ?_, fun c₀ hc₀ g₀ hg₀ => ?_⟩` and prove the remaining obligations. Establish `h` using `Qx8.slice_FF hz hz' hΦ hc`. Conclude with `⟨h.2.1, h.2.2.1, h.2.2.2⟩`. Take `⟨U, F, hU, hx, hF, hΦF⟩` from `hΦ.2.1 (c₀, g₀) ⟨hc₀, hg₀.1, hg₀.2⟩`. Conclude with `⟨U, F, hU, hx, hF, fun x hx _ hg _ => hΦF x hx hg⟩`.
-/
theorem famR {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    FamD z z' π π' (Fin.last r) (Qx8.Dp k r z z') Φ := by
  refine ⟨fun c hc => ?_, fun c₀ hc₀ g₀ hg₀ => ?_⟩
  · have h := Qx8.slice_FF hz hz' hΦ hc
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  · obtain ⟨U, F, hU, hx, hF, hΦF⟩ := hΦ.2.1 (c₀, g₀) ⟨hc₀, hg₀.1, hg₀.2⟩
    exact ⟨U, F, hU, hx, hF, fun x hx _ hg _ => hΦF x hx hg⟩

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_`. Simplify using `only [Nat.sub_zero]`.

Rewrite using `[lev_r, Dn_ge z z' (lt_irrefl r), Kn_ge z z' Φ (lt_irrefl r)]`. Conclude with `⟨Qx8.Dp_dom k r z z', famR hz hz' hΦ⟩`. Consider the case `succ j ih`. Introduce `hj`. Take `⟨hD, hF⟩` from `ih (by omega)`.

Establish `hi : r - (j + 1) < r` using `by omega`. Establish `e : r - j = r - (j + 1) + 1` using `by omega`. Rewrite `hD`, `hF` using `[e, ← lev_succ _ hi]`. Rewrite using `[← lev_castSucc _ hi, Dn_lt z z' hi, Kn_lt z z' Φ hi]`. Conclude with `⟨descended_set_is_domain _ hD, famStep hz hz' _ hF⟩`.
-/
theorem allLev {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    ∀ j, j ≤ r → IsDom k r z z' (lev r (r - j)) (Dn z z' (r - j)) ∧
      FamD z z' π π' (lev r (r - j)) (Dn z z' (r - j)) (Kn z z' Φ (r - j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.sub_zero]
    rw [lev_r, Dn_ge z z' (lt_irrefl r), Kn_ge z z' Φ (lt_irrefl r)]
    exact ⟨Qx8.Dp_dom k r z z', famR hz hz' hΦ⟩
  | succ j ih =>
    intro hj
    obtain ⟨hD, hF⟩ := ih (by omega)
    have hi : r - (j + 1) < r := by omega
    have e : r - j = r - (j + 1) + 1 := by omega
    rw [e, ← lev_succ _ hi] at hD hF
    rw [← lev_castSucc _ hi, Dn_lt z z' hi, Kn_lt z z' Φ hi]
    exact ⟨descended_set_is_domain _ hD, famStep hz hz' _ hF⟩

def mix (i : ℕ) (c d : Fin r → ℂ) : Fin r → ℂ := fun a => if a.val < i then c a else d a

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_ X hX`. Establish `hm : mix 0 c d = d` using `funext fun a => by simp [mix]`.

Rewrite `hX`, the goal using `[lev_zero]`. Rewrite using `[Qx6.wCell_zero, Matrix.one_mul, hm]`. Conclude with `⟨hX, rfl⟩`. Consider the case `succ i ih`. Introduce `hi X hX`.

Establish `hlt : i < r` using `by omega`. Take `⟨l, hl⟩ : ∃ l : Fin r, l = ⟨i, hlt⟩` from `⟨_, rfl⟩`. Establish `hli : l.val = i` using `by rw [hl]`. Establish `hcs : l.castSucc = lev r i` using `by rw [hl]; exact lev_castSucc i hlt`. Establish `hsc : l.succ = lev r (i + 1)` using `by rw [hl]; exact lev_succ i hlt`.

Establish `hDi : Dn z z' i = D0 k r l (Dn z z' (i + 1))` using `by rw [hl]; exact Dn_lt z z' hlt`. Establish `hKi : Kn z z' Φ i = JxF l z z' (Kn z z' Φ (i + 1))` using `by rw [hl]; exact Kn_lt z z' Φ hlt`. Rewrite `hX`, the goal using `[← hsc]`. Establish `hcl : c l ≠ 0` using `hc l`. Establish `hX' : w1 k r l (c l) * X ∈ Glev k r (lev r i) ∩ Dn z z' i`.

Rewrite using `[← hcs, hDi]`. Conclude with `⟨glev_mul (weyl_cell_mem_level_group (l := l) hcl) (glev_succ_le hX.1), (w1_mul_mem_descended_set_iff l _ hcl hX.1).2 hX.2⟩`. Take `⟨hmem, hval⟩` from `ih (by omega) _ hX'`. Establish `hmix : Function.update (mix i c d) l (c l) = mix (i + 1) c d`. Use function extensionality and compare the values at `a`.

Distinguish the cases in `ha : a = l`. Substitute `ha` using the available equality. Simplify using `[mix, hli]`. Establish `hne : a.val ≠ i` using `fun h => ha (Fin.ext (by rw [h, hli]))`. Simplify using `only [mix, Function.update_apply, ha, if_false]`.

Distinguish the cases in `h1 : a.val < i`. Rewrite using `[if_pos h1, if_pos (by omega)]`. Rewrite using `[if_neg h1, if_neg (by omega)]`. Rewrite using `[Qx6.wCell_succ, Matrix.mul_assoc, hcs]`. Use `⟨hmem, ?_⟩` and prove the remaining obligations.

Rewrite using `[hval, hKi, descended_function_apply_w1_mul hz hz' l _ _ hcl hX.1, hmix]`.
-/
theorem vals {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (Φ : Fn k r (Wq →L[ℂ] Wp))
    (d : Fin r → ℂ) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    ∀ i, i ≤ r → ∀ X ∈ Glev k r (lev r i) ∩ Dn z z' i,
      wCell k r (lev r i) c * X ∈ Glev k r 0 ∩ Dn z z' 0 ∧
        Kn z z' Φ 0 d (wCell k r (lev r i) c * X) = Kn z z' Φ i (mix i c d) X := by
  intro i
  induction i with
  | zero =>
    intro _ X hX
    have hm : mix 0 c d = d := funext fun a => by simp [mix]
    rw [lev_zero] at hX ⊢
    rw [Qx6.wCell_zero, Matrix.one_mul, hm]
    exact ⟨hX, rfl⟩
  | succ i ih =>
    intro hi X hX
    have hlt : i < r := by omega
    obtain ⟨l, hl⟩ : ∃ l : Fin r, l = ⟨i, hlt⟩ := ⟨_, rfl⟩
    have hli : l.val = i := by rw [hl]
    have hcs : l.castSucc = lev r i := by rw [hl]; exact lev_castSucc i hlt
    have hsc : l.succ = lev r (i + 1) := by rw [hl]; exact lev_succ i hlt
    have hDi : Dn z z' i = D0 k r l (Dn z z' (i + 1)) := by rw [hl]; exact Dn_lt z z' hlt
    have hKi : Kn z z' Φ i = JxF l z z' (Kn z z' Φ (i + 1)) := by rw [hl]; exact Kn_lt z z' Φ hlt
    rw [← hsc] at hX ⊢
    have hcl : c l ≠ 0 := hc l
    have hX' : w1 k r l (c l) * X ∈ Glev k r (lev r i) ∩ Dn z z' i := by
      rw [← hcs, hDi]
      exact ⟨glev_mul (weyl_cell_mem_level_group (l := l) hcl) (glev_succ_le hX.1), (w1_mul_mem_descended_set_iff l _ hcl hX.1).2 hX.2⟩
    obtain ⟨hmem, hval⟩ := ih (by omega) _ hX'
    have hmix : Function.update (mix i c d) l (c l) = mix (i + 1) c d := by
      funext a
      by_cases ha : a = l
      · subst ha; simp [mix, hli]
      · have hne : a.val ≠ i := fun h => ha (Fin.ext (by rw [h, hli]))
        simp only [mix, Function.update_apply, ha, if_false]
        by_cases h1 : a.val < i
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    rw [Qx6.wCell_succ, Matrix.mul_assoc, hcs]
    refine ⟨hmem, ?_⟩
    rw [hval, hKi, descended_function_apply_w1_mul hz hz' l _ _ hcl hX.1, hmix]

end iter

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ k r z z' π π' hz hz' Φ hΦ`. Establish `hall` using `allLev (π := π) (π' := π') hz hz' hΦ r le_rfl`. Rewrite `hall` using `[Nat.sub_self, lev_zero]`. Take `⟨hD, hF⟩` from `hall`. Use `⟨Dn z z' 0, hD, Kn z z' Φ 0 (fun _ => 1), famD_FFl hD.1 hF (fun _ => one_ne_zero), ?_⟩` and prove the remaining obligations.

Introduce `c hc g hg hGG`. Establish `hv` using `vals hz hz' Φ (fun _ => 1) hc r le_rfl g ⟨by rw [lev_r]; exact hg, by rw [Dn_ge z z' (lt_irrefl r)]; exact hGG⟩`. Rewrite `hv` using `[lev_r]`. Establish `hm : mix r c (fun _ => 1) = c` using `funext fun a => by simp [mix, a.isLt]`. Rewrite `hv` using `[hm, Kn_ge z z' Φ (lt_irrefl r)]`.

Conclude with `⟨hv.1.2, hv.2⟩`.
-/
theorem self_adjoint_descent_holds : SADescend := by
  intro Wp Wq _ _ _ _ k r z z' π π' hz hz' Φ hΦ
  have hall := allLev (π := π) (π' := π') hz hz' hΦ r le_rfl
  rw [Nat.sub_self, lev_zero] at hall
  obtain ⟨hD, hF⟩ := hall
  refine ⟨Dn z z' 0, hD, Kn z z' Φ 0 (fun _ => 1), famD_FFl hD.1 hF (fun _ => one_ne_zero), ?_⟩
  intro c hc g hg hGG
  have hv := vals hz hz' Φ (fun _ => 1) hc r le_rfl g
    ⟨by rw [lev_r]; exact hg, by rw [Dn_ge z z' (lt_irrefl r)]; exact hGG⟩
  rw [lev_r] at hv
  have hm : mix r c (fun _ => 1) = c := funext fun a => by simp [mix, a.isLt]
  rw [hm, Kn_ge z z' Φ (lt_irrefl r)] at hv
  exact ⟨hv.1.2, hv.2⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

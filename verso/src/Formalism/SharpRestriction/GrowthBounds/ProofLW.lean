import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumFEx

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Loc

variable {n' k1 : ℕ}

/- English proof (translation)
Unfold `de`. Use `set ℓ := Real.logb p A with hℓ`. Establish `hN1' : (1 : ℝ) ≤ NN k1 t j` using `by unfold NN; push_cast; nlinarith`. Establish `hNM : 1 ≤ NM` using `le_trans hN1' hN1`. Establish `hN0' : (0 : ℝ) ≤ NN k1 t (j - 1)` using `by positivity`.

Establish `hα : ∀ s, (lgp p (al TT lam0 s) : ℝ) ≤ 2 * ℓ` using `fun s => by`. Use `nc_lgp_le p hp _ A 1 hA (by rw [pow_one]; exact hal s) hl; push_cast at this; linarith` as an intermediate fact. Establish `hlz : ∀ s, (lgp p (lsz t TT lam0 w j s) : ℝ) ≤ 3 * ℓ` using `fun s => by`. Use `nc_lgp_le p hp _ A 2 hA (hls s) hl` as an intermediate fact. Move the coercions through the operations in `at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hα0 : ∀ s, (0 : ℝ) ≤ lgp p (al TT lam0 s)` using `fun s => by positivity`. Establish `hlz0 : ∀ s, (0 : ℝ) ≤ lgp p (lsz t TT lam0 w j s)` using `fun s => by positivity`. Establish `h1 : ∑ s : Fin n', ((NN k1 t j : ℝ) * lgp p (al TT lam0 s) + (NN k1 t (j - 1) : ℝ) * (NN k1 t j : ℝ) * lgp p (lsz t TT lam0 w j s)) ≤ ∑ _s : Fin n', (5 * NM ^ 2 * ℓ)`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `s _`. Establish `e1 : (NN k1 t j : ℝ) * lgp p (al TT lam0 s) ≤ NM * (2 * ℓ)` using `mul_le_mul hN1 (hα s) (hα0 s) (by linarith)`. Establish `e2 : (NN k1 t (j - 1) : ℝ) * (NN k1 t j : ℝ) * lgp p (lsz t TT lam0 w j s) ≤ NM * NM * (3 * ℓ)` using `mul_le_mul (mul_le_mul hN0 hN1 (by positivity) (by linarith)) (hlz s) (hlz0 s) (by nlinarith)`. Establish `e3 : NM * (2 * ℓ) ≤ NM * NM * (2 * ℓ)`. Establish `: 0 ≤ NM * (2 * ℓ)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : ∑ s ∈ TT, ((lgp p (al TT lam0 s) : ℝ)) ^ 2 ≤ ∑ _s ∈ TT, (4 * ℓ ^ 2)`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `s _`.

Use `hα s` as an intermediate fact. Use `hα0 s` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite `h1` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Rewrite `h2` using `[Finset.sum_const, nsmul_eq_mul]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lw_de_le (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (A : ℝ) (NM : ℝ) (hA : 1 ≤ A) (hl : 1 ≤ Real.logb p A) (hN1 : (NN k1 t j : ℝ) ≤ NM)
    (hN0 : (NN k1 t (j - 1) : ℝ) ≤ NM) (hal : ∀ s, (al TT lam0 s : ℝ) ≤ A)
    (hls : ∀ s, (lsz t TT lam0 w j s : ℝ) ≤ A ^ 2) :
    de p t TT lam0 w j ≤ 5 * (n' : ℝ) * NM ^ 2 * Real.logb p A + 4 * (TT.card : ℝ) * Real.logb p A ^ 2 := by
  unfold de
  set ℓ := Real.logb p A with hℓ
  have hN1' : (1 : ℝ) ≤ NN k1 t j := by unfold NN; push_cast; nlinarith
  have hNM : 1 ≤ NM := le_trans hN1' hN1
  have hN0' : (0 : ℝ) ≤ NN k1 t (j - 1) := by positivity
  have hα : ∀ s, (lgp p (al TT lam0 s) : ℝ) ≤ 2 * ℓ := fun s => by
    have := nc_lgp_le p hp _ A 1 hA (by rw [pow_one]; exact hal s) hl; push_cast at this; linarith
  have hlz : ∀ s, (lgp p (lsz t TT lam0 w j s) : ℝ) ≤ 3 * ℓ := fun s => by
    have := nc_lgp_le p hp _ A 2 hA (hls s) hl; push_cast at this; linarith
  have hα0 : ∀ s, (0 : ℝ) ≤ lgp p (al TT lam0 s) := fun s => by positivity
  have hlz0 : ∀ s, (0 : ℝ) ≤ lgp p (lsz t TT lam0 w j s) := fun s => by positivity
  have h1 : ∑ s : Fin n', ((NN k1 t j : ℝ) * lgp p (al TT lam0 s) +
      (NN k1 t (j - 1) : ℝ) * (NN k1 t j : ℝ) * lgp p (lsz t TT lam0 w j s)) ≤
      ∑ _s : Fin n', (5 * NM ^ 2 * ℓ) := by
    apply Finset.sum_le_sum
    intro s _
    have e1 : (NN k1 t j : ℝ) * lgp p (al TT lam0 s) ≤ NM * (2 * ℓ) :=
      mul_le_mul hN1 (hα s) (hα0 s) (by linarith)
    have e2 : (NN k1 t (j - 1) : ℝ) * (NN k1 t j : ℝ) * lgp p (lsz t TT lam0 w j s) ≤ NM * NM * (3 * ℓ) :=
      mul_le_mul (mul_le_mul hN0 hN1 (by positivity) (by linarith)) (hlz s) (hlz0 s) (by nlinarith)
    have e3 : NM * (2 * ℓ) ≤ NM * NM * (2 * ℓ) := by
      have : 0 ≤ NM * (2 * ℓ) := by positivity
      nlinarith
    nlinarith
  have h2 : ∑ s ∈ TT, ((lgp p (al TT lam0 s) : ℝ)) ^ 2 ≤ ∑ _s ∈ TT, (4 * ℓ ^ 2) := by
    apply Finset.sum_le_sum
    intro s _
    have := hα s
    have := hα0 s
    nlinarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  nlinarith

end Loc

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

def lw_Size (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  (∀ s, (al ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) s : ℝ) ≤ 2 * L.sc.a) ∧
  (∀ s, (lsz (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
    ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j s : ℝ) ≤ (2 * L.sc.a) ^ 2)

/- English proof (translation)
Establish `hp : 2 ≤ D.what₂.places.resChar w` using `hg.1.two_le`. Establish `hA : (1 : ℝ) ≤ 2 * L.sc.a` using `by have := nc_a_ge (L := L); linarith`. Establish `hmt` using `(hL u w hg)`. Establish `ht : (Y.Fl u w hg).t = D.R.t` using `hmt.2.1`. Establish `hk` using `hT.gat_k u w hg`.

Establish `hjm : j ≤ D.R.m` using `(Finset.mem_Icc.1 hj).2`. Establish `hN1 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) ≤ (D.R.N D.R.m : ℝ)`. Unfold `NN Ranks.N`. Rewrite using `[ht]`. Establish `: (D.gat u w hg).P.m + 1 + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1)`.

Rewrite using `[hk]`. Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_right _ hjm) _`. Conclude with `this` after adjusting the coercions. Establish `hN0 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t (j - 1) : ℝ) ≤ (D.R.N D.R.m : ℝ)`. Unfold `NN Ranks.N`.

Rewrite using `[ht]`. Establish `: (D.gat u w hg).P.m + 1 + (j - 1) * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1)`. Rewrite using `[hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _`. Conclude with `this` after adjusting the coercions. Establish `hde` using `lw_de_le (D.what₂.places.resChar w) (Y.Fl u w hg).t _ _ _ j hp (2 * L.sc.a) (D.R.N D.R.m : ℝ) hA hlog hN1 hN0 hS.1 hS.2`.

Establish `hinj` using `nc_iota_inj X Y hT hL u w hg t0 ht0`. Establish `hNv : (Formalism.MainNotions.G.Nv X (D.what₂.places.resChar w) t0 : ℝ) = ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card`. Unfold `Formalism.MainNotions.G.Nv`. Rewrite using `[nc_topsOn X Y hT hL u w hg t0 ht0, Finset.card_image_of_injective _ hinj]`. Establish `hnP : (Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) : ℝ) = ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ)`.

Unfold `Formalism.MainNotions.G.nP`. Rewrite using `[if_neg (nc_notSg hg), nc_n_eq X Y hT hL u w hg t0 ht0]`. Unfold `nc_De Formalism.MainNotions.G.dl Formalism.MainNotions.G.Nm`. Rewrite using `[hNv, hnP]`. Establish `hl0 : 0 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a)` using `by linarith`.

Establish `hc1 : (0 : ℝ) ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) (2 * L.sc.a)` using `by positivity`. Establish `hc2 : (0 : ℝ) ≤ (((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card : ℝ) * Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) ^ 2` using `by positivity`. Establish `g1` using `mul_le_mul_of_nonneg_right h1 hc1`. Establish `g2` using `mul_le_mul_of_nonneg_right h2 hc2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lw_de (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (hT : GatTies D)
    (hL : Formalism.MainNotions.G.LatTied hT X Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D)
    (h1 : 5 ≤ K.dl1) (h2 : 4 ≤ K.dl2) (hlog : 1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a))
    (hS : lw_Size D L Y u w hg t0 j) : nc_De D L X Y K u w hg t0 j := by
  have hp : 2 ≤ D.what₂.places.resChar w := hg.1.two_le
  have hA : (1 : ℝ) ≤ 2 * L.sc.a := by have := nc_a_ge (L := L); linarith
  have hmt := (hL u w hg)
  have ht : (Y.Fl u w hg).t = D.R.t := hmt.2.1
  have hk := hT.gat_k u w hg
  have hjm : j ≤ D.R.m := (Finset.mem_Icc.1 hj).2
  have hN1 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    unfold NN Ranks.N
    rw [ht]
    have : (D.gat u w hg).P.m + 1 + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1) := by
      rw [hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hjm) _
    exact_mod_cast this
  have hN0 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t (j - 1) : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    unfold NN Ranks.N
    rw [ht]
    have : (D.gat u w hg).P.m + 1 + (j - 1) * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1) := by
      rw [hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    exact_mod_cast this
  have hde := lw_de_le (D.what₂.places.resChar w) (Y.Fl u w hg).t _ _ _ j hp (2 * L.sc.a) (D.R.N D.R.m : ℝ) hA hlog
    hN1 hN0 hS.1 hS.2
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hNv : (Formalism.MainNotions.G.Nv X (D.what₂.places.resChar w) t0 : ℝ) = ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card := by
    unfold Formalism.MainNotions.G.Nv
    rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.card_image_of_injective _ hinj]
  have hnP : (Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) : ℝ) = ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := by
    unfold Formalism.MainNotions.G.nP
    rw [if_neg (nc_notSg hg), nc_n_eq X Y hT hL u w hg t0 ht0]
  unfold nc_De Formalism.MainNotions.G.dl Formalism.MainNotions.G.Nm
  rw [hNv, hnP]
  have hl0 : 0 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) := by linarith
  have hc1 : (0 : ℝ) ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) * (D.R.N D.R.m : ℝ) ^ 2 *
      Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) := by positivity
  have hc2 : (0 : ℝ) ≤ (((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card : ℝ) *
      Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) ^ 2 := by positivity
  have g1 := mul_le_mul_of_nonneg_right h1 hc1
  have g2 := mul_le_mul_of_nonneg_right h2 hc2
  linarith

/- English proof (translation)
Take `⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hDel, _⟩` from `hS`. Establish `h4` using `hDel.2.2.2.1`. Establish `hk` using `nd_k_ge (D := D)`. Establish `h2 : 5 * L.Sc ≤ (D.R.k : ℝ) * L.Sc` using `mul_le_mul_of_nonneg_right hk L.Sc_pos.le`. Unfold `Formalism.MainNotions.G.cG`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lw_c_le (hS : Formalism.MainNotions.SizesAt L) : Formalism.MainNotions.G.cG L ≤ 4 / 5 * L.sc.w'' D.R.n := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hDel, _⟩ := hS
  have h4 := hDel.2.2.2.1
  have hk := nd_k_ge (D := D)
  have h2 : 5 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := mul_le_mul_of_nonneg_right hk L.Sc_pos.le
  unfold Formalism.MainNotions.G.cG
  linarith

/- English proof (translation)
Take `⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hEta, _⟩` from `hS`. Establish `h5` using `hEta.2.2.2.2.1`. Establish `hm` using `nd_m_ge (D := D)`. Establish `ht : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Establish `h1 : (2 : ℝ) ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)` using `by nlinarith`.

Establish `h2 : 2 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz` using `mul_le_mul_of_nonneg_right h1 L.etaSz_pos.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lw_eta_le (hS : Formalism.MainNotions.SizesAt L) : 2 * L.etaSz ≤ L.sc.w'' D.R.n := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hEta, _⟩ := hS
  have h5 := hEta.2.2.2.2.1
  have hm := nd_m_ge (D := D)
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have h1 : (2 : ℝ) ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by nlinarith
  have h2 : 2 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz :=
    mul_le_mul_of_nonneg_right h1 L.etaSz_pos.le
  linarith

/- English proof (translation)
Establish `h` using `(L.aT_win t).2`. Establish `ha` using `nc_a_ge (L := L)`. Establish `hk` using `nd_k_ge (D := D)`. Establish `hx : (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2)` using `Real.one_le_rpow (nd_x_ge (L := L)) (by unfold Scale.A; norm_num)`. Establish `h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)` using `by nlinarith`.

Establish `h1 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5` using `div_le_div_of_nonneg_left (by linarith) (by norm_num) h5`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lw_aT_le (t : D.host.TT) : (L.aT t : ℝ) ≤ 6 / 5 * L.sc.a := by
  have h := (L.aT_win t).2
  have ha := nc_a_ge (L := L)
  have hk := nd_k_ge (D := D)
  have hx : (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow (nd_x_ge (L := L)) (by unfold Scale.A; norm_num)
  have h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by nlinarith
  have h1 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) h5
  linarith

/- English proof (translation)
Establish `hm` using `nc_m_ge hT u w hg`. Take `⟨_, ht, hc, _, _, _, hloc⟩` from `hL u w hg`. Take `⟨_, hs⟩` from `hloc t0 ht0`. Establish `hj1 : 1 ≤ j` using `(Finset.mem_Icc.1 hj).1`. Establish `hjm : j ≤ D.R.m` using `(Finset.mem_Icc.1 hj).2`.

Establish `ha` using `nc_a_ge (L := L)`. Establish `hw2` using `nd_w''_le (L := L)`. Establish `hb1` using `nd_b'_le (L := L)`. Establish `hb0` using `nd_b'_nonneg (L := L)`. Establish `hc' : ((Y.Fl u w hg).c : ℝ) ≤ 4 / 5 * L.sc.b'`.

Use `lw_c_le hS` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun s => ?_, fun s => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hsT : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)`. Take `⟨_, hTT, hab, _⟩` from `hs s`.

Establish `h1` using `nd_al_le (Y.Fl u w hg) (Y.vOf u w hg t0) s hsT hm`. Establish `h2` using `(hab hsT).1`. Establish `h3 : (al ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) s : ℝ) ≤ (((Y.Fl u w hg).a (Y.vOf u w hg t0) s + ((Y.Fl u w hg).c : ℤ) : ℤ) : ℝ)` using `by exact_mod_cast h1`. Rewrite `h3` using `[h2]`. Move the coercions through the operations in `at h3`.

Establish `h4 : (Formalism.MainNotions.G.aL L (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) : ℝ) ≤ 6 / 5 * L.sc.a`. Unfold `Formalism.MainNotions.G.aL`. Rewrite using `[dif_pos (hTT.1 hsT)]`. Conclude with `lw_aT_le _`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `al`. Rewrite using `[if_neg hsT]`. Use `push_cast`. Check the signs of the components of the expression. Establish `h1` using `nd_lsz_le (Y.Fl u w hg) (Y.vOf u w hg t0) s hm j hj1`.

Establish `h2 : (lsz (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j s : ℝ) ≤ (((NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℤ) * (((Y.Fl u w hg).c : ℤ) + (Y.Fl u w hg).w (Y.vOf u w hg t0) j s) : ℤ) : ℝ)` using `by exact_mod_cast h1`. Move the coercions through the operations in `at h2`. Establish `hk` using `hT.gat_k u w hg`. Establish `hN1 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) ≤ (D.R.N D.R.m : ℝ)`. Unfold `NN Ranks.N`.

Rewrite using `[ht]`. Establish `: (D.gat u w hg).P.m + 1 + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1)`. Rewrite using `[hk]`. Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_right _ hjm) _`. Conclude with `this` after adjusting the coercions.

Establish `hN` using `le_trans hN1 (nd_N_le hS)`. Establish `he` using `lw_eta_le hS`. Establish `hw1 : ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ 11 / 4 * L.sc.b'`. Distinguish the cases in `hsT : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)`. Establish `g1` using `ne_w_top X Y hT hL u w hg t0 ht0 j hj s hsT`.

Establish `g2` using `(ne_b_top X Y hT hL u w hg t0 ht0 hS s hsT).2`. Establish `g3 : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb0 (nd_x_ge (L := L))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `g1` using `ne_w_non X Y hT hL u w hg t0 ht0 j hj s hsT`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hw0 : (0 : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) + ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ)`. Establish `h5` using `nd_c_le_w (Y.Fl u w hg) (Y.vOf u w hg t0) s j hj1`. Establish `h6 : (((Y.Fl u w hg).c : ℤ) : ℝ) ≤ ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ)` using `by exact_mod_cast h5`. Establish `h7 : (0 : ℝ) ≤ ((Y.Fl u w hg).c : ℝ)` using `Nat.cast_nonneg _`. Move the coercions through the operations in `at h6`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h8 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) * (((Y.Fl u w hg).c : ℝ) + ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ)) ≤ L.sc.a * (4 * L.sc.a)` using `mul_le_mul hN (by linarith) hw0 (by linarith)`. Establish `h9 : L.sc.a * (4 * L.sc.a) = (2 * L.sc.a) ^ 2` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lw_size (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hS : Formalism.MainNotions.SizesAt L) (hT : GatTies D)
    (hL : Formalism.MainNotions.G.LatTied hT X Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    lw_Size D L Y u w hg t0 j := by
  have hm := nc_m_ge hT u w hg
  obtain ⟨_, ht, hc, _, _, _, hloc⟩ := hL u w hg
  obtain ⟨_, hs⟩ := hloc t0 ht0
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
  have hjm : j ≤ D.R.m := (Finset.mem_Icc.1 hj).2
  have ha := nc_a_ge (L := L)
  have hw2 := nd_w''_le (L := L)
  have hb1 := nd_b'_le (L := L)
  have hb0 := nd_b'_nonneg (L := L)
  have hc' : ((Y.Fl u w hg).c : ℝ) ≤ 4 / 5 * L.sc.b' := by
    have := lw_c_le hS
    linarith
  refine ⟨fun s => ?_, fun s => ?_⟩
  · by_cases hsT : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)
    · obtain ⟨_, hTT, hab, _⟩ := hs s
      have h1 := nd_al_le (Y.Fl u w hg) (Y.vOf u w hg t0) s hsT hm
      have h2 := (hab hsT).1
      have h3 : (al ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) s : ℝ) ≤
          (((Y.Fl u w hg).a (Y.vOf u w hg t0) s + ((Y.Fl u w hg).c : ℤ) : ℤ) : ℝ) := by exact_mod_cast h1
      rw [h2] at h3
      push_cast at h3
      have h4 : (Formalism.MainNotions.G.aL L (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) : ℝ) ≤ 6 / 5 * L.sc.a := by
        unfold Formalism.MainNotions.G.aL
        rw [dif_pos (hTT.1 hsT)]
        exact lw_aT_le _
      linarith
    · unfold al
      rw [if_neg hsT]
      push_cast
      positivity
  · have h1 := nd_lsz_le (Y.Fl u w hg) (Y.vOf u w hg t0) s hm j hj1
    have h2 : (lsz (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
        ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j s : ℝ) ≤
        (((NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℤ) *
          (((Y.Fl u w hg).c : ℤ) + (Y.Fl u w hg).w (Y.vOf u w hg t0) j s) : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have hk := hT.gat_k u w hg
    have hN1 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      unfold NN Ranks.N
      rw [ht]
      have : (D.gat u w hg).P.m + 1 + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1) := by
        rw [hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hjm) _
      exact_mod_cast this
    have hN := le_trans hN1 (nd_N_le hS)
    have he := lw_eta_le hS
    have hw1 : ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ 11 / 4 * L.sc.b' := by
      by_cases hsT : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)
      · have g1 := ne_w_top X Y hT hL u w hg t0 ht0 j hj s hsT
        have g2 := (ne_b_top X Y hT hL u w hg t0 ht0 hS s hsT).2
        have g3 : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb0 (nd_x_ge (L := L))
        linarith
      · have g1 := ne_w_non X Y hT hL u w hg t0 ht0 j hj s hsT
        linarith
    have hw0 : (0 : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) + ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) := by
      have h5 := nd_c_le_w (Y.Fl u w hg) (Y.vOf u w hg t0) s j hj1
      have h6 : (((Y.Fl u w hg).c : ℤ) : ℝ) ≤ ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) := by exact_mod_cast h5
      have h7 : (0 : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) := Nat.cast_nonneg _
      push_cast at h6
      linarith
    have h8 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) *
        (((Y.Fl u w hg).c : ℝ) + ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ)) ≤ L.sc.a * (4 * L.sc.a) :=
      mul_le_mul hN (by linarith) hw0 (by linarith)
    have h9 : L.sc.a * (4 * L.sc.a) = (2 * L.sc.a) ^ 2 := by ring
    linarith

open Classical in

/- English proof (translation)
Introduce `hT hL u w hg hlog t0 ht0 j hj`. Take `⟨e1, e2, c1, c0, c2, c3, cx⟩` from `nc_loc X Y K hT hL u w hg t0 ht0 j hj`. Establish `hDe` using `lw_de X Y K hT hL u w hg t0 ht0 j hj h1 h2 hlog (lw_size X Y hS hT hL u w hg t0 ht0 j hj)`. Establish `hPr` using `priceBound_of_largePrimes_of_smallPrimes 1 price_bound_large_primes price_bound_small_primes D L X Y K h3 ⟨h4, h4'⟩ hS hT hL u w hg hlog t0 ht0 j hj`. Establish `hp : 2 ≤ D.what₂.places.resChar w` using `hg.1.two_le`.

Use `⟨?_, ?_, hPr⟩` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `nc_gB_ge _ _ _ _ _ j hp _ _ _ c1 c2 c3 hDe`. Rewrite using `[e2]`. Conclude with `nc_gA_ge _ _ _ _ _ j hp _ _ _ _ c1 c0 c2 c3 cx hDe`.
-/
theorem numeric_comparison_of_constants (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D)
    (K : Formalism.MainNotions.G.Consts) (h1 : 5 ≤ K.dl1) (h2 : 4 ≤ K.dl2) (h3 : 1 ≤ K.Pr1) (h4 : Formalism.MainNotions.G.rG L.sc < D.R.k)
    (h4' : 2 ≤ L.sc.x) (hS : Formalism.MainNotions.SizesAt L) : Formalism.MainNotions.FormalGroupSystem.SmallResidueCharComparison D L X Y K := by
  intro hT hL u w hg hlog t0 ht0 j hj
  obtain ⟨e1, e2, c1, c0, c2, c3, cx⟩ := nc_loc X Y K hT hL u w hg t0 ht0 j hj
  have hDe := lw_de X Y K hT hL u w hg t0 ht0 j hj h1 h2 hlog (lw_size X Y hS hT hL u w hg t0 ht0 j hj)
  have hPr := priceBound_of_largePrimes_of_smallPrimes 1 price_bound_large_primes price_bound_small_primes D L X Y K h3 ⟨h4, h4'⟩ hS hT hL u w hg hlog t0 ht0 j hj
  have hp : 2 ≤ D.what₂.places.resChar w := hg.1.two_le
  refine ⟨?_, ?_, hPr⟩
  · rw [e1]
    exact nc_gB_ge _ _ _ _ _ j hp _ _ _ c1 c2 c3 hDe
  · rw [e2]
    exact nc_gA_ge _ _ _ _ _ j hp _ _ _ _ c1 c0 c2 c3 cx hDe

end Formalism.MainNotions.FormalGroupSystem.Pf

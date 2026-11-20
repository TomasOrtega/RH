import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NeNeedPrice

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Local

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

/- English proof (translation)
Unfold `al`. Rewrite using `[if_pos hs, lambda_index_one v s hm, lambda_index_two v s hm]`. Establish `hb` using `(Fl.base v s).1 hs`. Use `(abs_le.1 (hb.2.2 ⟨1, by omega⟩ (by simp) (by simp; omega))).1` as an intermediate fact. Establish `h0 : G.P.lam0 v s ⟨0, by omega⟩ = Fl.a v s` using `hb.1`.

Use linear arithmetic over natural numbers and integers.
-/
theorem nd_al_le (s : Fin (G.P.n' v)) (hs : s ∈ Fl.TT v) (hm : 2 ≤ G.P.m) :
    al (Fl.TT v) (G.P.lam0 v) s ≤ Fl.a v s + (Fl.c : ℤ) := by
  unfold al
  rw [if_pos hs, lambda_index_one v s hm, lambda_index_two v s hm]
  have hb := (Fl.base v s).1 hs
  have := (abs_le.1 (hb.2.2 ⟨1, by omega⟩ (by simp) (by simp; omega))).1
  have h0 : G.P.lam0 v s ⟨0, by omega⟩ = Fl.a v s := hb.1
  omega

/- English proof (translation)
The claim follows from `le_trans (le_trans (le_max_left _ _) (Fl.w_ge v s)) (nc_w_ge Fl v s l hl)`.
-/
theorem nd_c_le_w (s : Fin (G.P.n' v)) (l : ℕ) (hl : 1 ≤ l) : (Fl.c : ℤ) ≤ Fl.w v l s :=
  le_trans (le_trans (le_max_left _ _) (Fl.w_ge v s)) (nc_w_ge Fl v s l hl)

/- English proof (translation)
Unfold `lamI`. Rewrite using `[dif_pos ⟨h1, h2⟩]`. Establish `hb` using `Fl.base v s`. Distinguish the cases in `hs : s ∈ Fl.TT v`. Establish `h3` using `(abs_le.1 ((hb.1 hs).2.2 ⟨1, by omega⟩ (by simp) (by simp; omega))).2`.

Establish `hd : Antitone (G.P.lam0 v s)` using `G.P.dom v s`. Establish `h4` using `hd (show (⟨1, by omega⟩ : Fin (G.P.m + 1)) ≤ ⟨i - 1, by omega⟩ by`. Rewrite using `[Fin.le_def]`. Use `h hs` as an intermediate fact. Simplify using `only`.

Use the proof step `omega)`. Use linear arithmetic over natural numbers and integers. Conclude with `(abs_le.1 (hb.2 hs _)).2`.
-/
theorem nd_lam_le (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ G.P.m + 1)
    (h : s ∈ Fl.TT v → 2 ≤ i) : lamI (G.P.lam0 v) s i ≤ (Fl.c : ℤ) := by
  unfold lamI
  rw [dif_pos ⟨h1, h2⟩]
  have hb := Fl.base v s
  by_cases hs : s ∈ Fl.TT v
  · have h3 := (abs_le.1 ((hb.1 hs).2.2 ⟨1, by omega⟩ (by simp) (by simp; omega))).2
    have hd : Antitone (G.P.lam0 v s) := G.P.dom v s
    have h4 := hd (show (⟨1, by omega⟩ : Fin (G.P.m + 1)) ≤ ⟨i - 1, by omega⟩ by
      rw [Fin.le_def]; have := h hs; simp only; omega)
    omega
  · exact (abs_le.1 (hb.2 hs _)).2

/- English proof (translation)
Unfold `lsz`. Establish `h1N : 1 ∈ Icc 1 (NN G.P.m Fl.t j)` using `Finset.mem_Icc.2 ⟨le_rfl, by unfold NN; omega⟩`. Establish `e : ∑ i ∈ Icc 1 (NN G.P.m Fl.t j), nu Fl.t (G.P.lam0 v) (Fl.w v) j s i - al (Fl.TT v) (G.P.lam0 v) s = ∑ i ∈ Icc 1 (NN G.P.m Fl.t j), (nu Fl.t (G.P.lam0 v) (Fl.w v) j s i - if i = 1 then al (Fl.TT v) (G.P.lam0 v) s else 0)`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_ite_eq' _ 1, if_pos h1N]`. Rewrite using `[e]`.

Establish `hb : ∀ i ∈ Icc 1 (NN G.P.m Fl.t j), (nu Fl.t (G.P.lam0 v) (Fl.w v) j s i - if i = 1 then al (Fl.TT v) (G.P.lam0 v) s else 0) ≤ (Fl.c : ℤ) + Fl.w v j s`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Icc]`. Unfold `nu`. Distinguish the cases in `hik : i ≤ G.P.m + 1`.

Rewrite using `[if_pos ⟨hi.1, hik⟩]`. Distinguish the cases in `hi1 : i = 1`. Substitute `hi1` using the available equality. Rewrite using `[if_pos rfl]`. Unfold `al`.

Distinguish the cases in `hs : s ∈ Fl.TT v`. Rewrite using `[if_pos hs]`. Use `nd_lam_le Fl v s hm 2 (by omega) (by omega) (fun _ => le_rfl)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hs]`.

Use `nd_lam_le Fl v s hm 1 le_rfl (by omega) (fun h => absurd h hs)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hi1]`. Use `nd_lam_le Fl v s hm i hi.1 hik (fun _ => by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg (fun h => hik h.2), if_pos ⟨by omega, hi.2⟩, if_neg (by omega)]`. Use `nd_c_le_w Fl v s ((i - (G.P.m + 2)) / (Fl.t + 1) + 1) (Nat.le_add_left 1 _)` as an intermediate fact. Establish `hc : (0 : ℤ) ≤ (Fl.c : ℤ)` using `Int.natCast_nonneg _`. Use linear arithmetic over natural numbers and integers. Use `Finset.sum_le_sum hb` as an intermediate fact.

Rewrite `this` using `[Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]`. Simplify using `using this`.
-/
theorem nd_lsz_le (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) (j : ℕ) (hj : 1 ≤ j) :
    lsz Fl.t (Fl.TT v) (G.P.lam0 v) (Fl.w v) j s ≤ (NN G.P.m Fl.t j : ℤ) * ((Fl.c : ℤ) + Fl.w v j s) := by
  unfold lsz
  have h1N : 1 ∈ Icc 1 (NN G.P.m Fl.t j) := Finset.mem_Icc.2 ⟨le_rfl, by unfold NN; omega⟩
  have e : ∑ i ∈ Icc 1 (NN G.P.m Fl.t j), nu Fl.t (G.P.lam0 v) (Fl.w v) j s i - al (Fl.TT v) (G.P.lam0 v) s =
      ∑ i ∈ Icc 1 (NN G.P.m Fl.t j), (nu Fl.t (G.P.lam0 v) (Fl.w v) j s i -
        if i = 1 then al (Fl.TT v) (G.P.lam0 v) s else 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' _ 1, if_pos h1N]
  rw [e]
  have hb : ∀ i ∈ Icc 1 (NN G.P.m Fl.t j), (nu Fl.t (G.P.lam0 v) (Fl.w v) j s i -
        if i = 1 then al (Fl.TT v) (G.P.lam0 v) s else 0) ≤ (Fl.c : ℤ) + Fl.w v j s := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    unfold nu
    by_cases hik : i ≤ G.P.m + 1
    · rw [if_pos ⟨hi.1, hik⟩]
      by_cases hi1 : i = 1
      · subst hi1
        rw [if_pos rfl]
        unfold al
        by_cases hs : s ∈ Fl.TT v
        · rw [if_pos hs]
          have := nd_lam_le Fl v s hm 2 (by omega) (by omega) (fun _ => le_rfl)
          omega
        · rw [if_neg hs]
          have := nd_lam_le Fl v s hm 1 le_rfl (by omega) (fun h => absurd h hs)
          omega
      · rw [if_neg hi1]
        have := nd_lam_le Fl v s hm i hi.1 hik (fun _ => by omega)
        omega
    · rw [if_neg (fun h => hik h.2), if_pos ⟨by omega, hi.2⟩, if_neg (by omega)]
      have := nd_c_le_w Fl v s ((i - (G.P.m + 2)) / (Fl.t + 1) + 1) (Nat.le_add_left 1 _)
      have hc : (0 : ℤ) ≤ (Fl.c : ℤ) := Int.natCast_nonneg _
      omega
  have := Finset.sum_le_sum hb
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at this
  simpa using this

end Local

end Formalism.MainNotions.FormalGroupSystem.Pf

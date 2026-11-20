import Formalism.LocalToGlobal.Columns.TiedGlMat
import Formalism.LocalToGlobal.Columns.RecLevelDiv
import Formalism.LocalToGlobal.HermitianForms.FormsTied

open Matrix NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions (Ranks)
open Formalism.L2.Forms (InJ aOf skipOf fcOf)

/- English proof (translation)
Unfold `Ranks.N`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gll_N (R : Ranks) (j : ℕ) : R.N j = R.k + j + j * R.t := by unfold Ranks.N; ring

/- English proof (translation)
Use `R.rank_add_five_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem gll_t_pos (R : Ranks) : 0 < R.t := by have := R.rank_add_five_le; omega

/- English proof (translation)
Rewrite using `[gll_N]`. Unfold `Ranks.r`. Use `R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem gll_Nm (R : Ranks) : R.N R.m = R.r + R.m * R.t + 1 := by
  rw [gll_N]; unfold Ranks.r; have := R.two_le_m; omega

section Steps

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {k' : Type} [Field k']

/- English proof (translation)
Rewrite using `[glm_InJ_map]`. Establish `ht` using `gll_t_pos R`. Distinguish the cases in `h1 : j + 1 < R.m`. Establish `ha : aOf R j = R.k + j` using `if_pos (by omega)`. Establish `hf : fcOf R j = R.N j` using `if_neg (by omega)`.

Establish `hd : decide (j = R.m) = false` using `decide_eq_false (by omega)`. Rewrite using `[ha, hf, hd, glm_InJ_false (j := j) ht (by rw [gll_N]; omega), glm_fixCol_top le_rfl, inf_top_eq, colLevS_of_lt Ch h1]`. Unfold `colLev`. Rewrite using `[if_pos (by omega)]`. Distinguish the cases in `h2 : j + 1 = R.m`.

Establish `ha : aOf R j = R.k + j` using `if_pos (by omega)`. Establish `hf : fcOf R j = R.k` using `if_pos (by omega)`. Establish `hd : decide (j = R.m) = false` using `decide_eq_false (by omega)`. Rewrite using `[ha, hf, hd, glm_InJ_false (j := j) ht (by rw [gll_N]; omega)]`. Unfold `colLevS`.

Rewrite using `[if_neg h1, if_pos h2]`. Establish `hjm : j = R.m` using `by omega`. Substitute `hjm` using the available equality. Establish `ha : aOf R R.m = R.r` using `if_neg (by omega)`. Establish `hf : fcOf R R.m = R.k` using `if_pos (by omega)`.

Establish `hd : decide (R.m = R.m) = true` using `decide_eq_true rfl`. Rewrite using `[ha, hf, hd, glm_InJ_true (j := R.m) ht (gll_Nm R), colLevS_top_H Ch le_rfl]`. Both sides reduce to the same expression.
-/
theorem colLevS_mem_iff {j : ℕ} (hj : j ≤ R.m) (w : Pr.vGs) (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* k')
    (M : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)) :
    M ∈ (colLevS Ch j w).H ↔
      InJ (aOf R j) R.t (fcOf R j) (decide (j = R.m)) ((M : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)).map e) := by
  rw [glm_InJ_map]
  have ht := gll_t_pos R
  by_cases h1 : j + 1 < R.m
  · have ha : aOf R j = R.k + j := if_pos (by omega)
    have hf : fcOf R j = R.N j := if_neg (by omega)
    have hd : decide (j = R.m) = false := decide_eq_false (by omega)
    rw [ha, hf, hd, glm_InJ_false (j := j) ht (by rw [gll_N]; omega), glm_fixCol_top le_rfl, inf_top_eq, colLevS_of_lt Ch h1]
    unfold colLev
    rw [if_pos (by omega)]
  · by_cases h2 : j + 1 = R.m
    · have ha : aOf R j = R.k + j := if_pos (by omega)
      have hf : fcOf R j = R.k := if_pos (by omega)
      have hd : decide (j = R.m) = false := decide_eq_false (by omega)
      rw [ha, hf, hd, glm_InJ_false (j := j) ht (by rw [gll_N]; omega)]
      unfold colLevS
      rw [if_neg h1, if_pos h2]
    · have hjm : j = R.m := by omega
      subst hjm
      have ha : aOf R R.m = R.r := if_neg (by omega)
      have hf : fcOf R R.m = R.k := if_pos (by omega)
      have hd : decide (R.m = R.m) = true := decide_eq_true rfl
      rw [ha, hf, hd, glm_InJ_true (j := R.m) ht (gll_Nm R), colLevS_top_H Ch le_rfl]
      rfl

/- English proof (translation)
Establish `ht` using `gll_t_pos R`. Establish `key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N j), l = colLevS Ch j w → ∀ hM' : M ∈ l.H, σ₀ ((l.lam ⟨M, hM'⟩ : X.Kˣ) : X.K) = Formalism.L2.Forms.lamJ (glmPsi e σ₀ (Ch.psi0 w)) (fun s => glmChi e σ₀ (extChi (fun s => Ch.chi s w) s)) (aOf R j) R.t j (skipOf R j) ((M : Matrix (Fin ( …`. Introduce `l hl hM'`. Distinguish the cases in `h1 : j + 1 < R.m`. Establish `ha : aOf R j = R.k + j` using `if_pos (by omega)`.

Establish `hs : skipOf R j = R.k` using `if_pos h1`. Rewrite using `[ha, hs]`. Establish `hl' : l = ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j, lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j⟩`. Rewrite using `[hl]; unfold colLevS colLev; rw [if_pos h1, if_pos (by omega)]`. Substitute `hl'` using the available equality.

Use `glm_lamGen e σ₀ _ _ (SX R.k R.m j) ht (by rw [gll_N]) (fun x hx => ?_) ⟨M, hM'⟩` and prove the remaining obligations. Unfold `SX`. Rewrite using `[Finset.mem_filter, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h | h⟩`.

Conclude with `h`. Use linear arithmetic over natural numbers and integers. Introduce `h; exact ⟨by omega, Or.inl h⟩`. Distinguish the cases in `h2 : j + 1 = R.m`. Establish `ha : aOf R j = R.k + j` using `if_pos (by omega)`.

Establish `hs : skipOf R j = R.N j` using `if_neg h1`. Rewrite using `[ha, hs]`. Establish `hl' : l = ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j ⊓ fixCol (R.N j) (𝓞 X.E ⧸ w.1.asIdeal) R.k, (lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j).comp (Subgroup.inclusion inf_le_left)⟩`. Rewrite using `[hl]`. Unfold `colLevS`.

Rewrite using `[if_neg h1, if_pos h2]`. Substitute `hl'` using the available equality. Use `glm_lamGen e σ₀ _ _ (SX R.k R.m j) ht (by rw [gll_N]) (fun x hx => ?_) ⟨M, hM'.1⟩` and prove the remaining obligations. Unfold `SX`. Rewrite using `[Finset.mem_filter, Finset.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce `_`. Rewrite using `[gll_N]`. Use linear arithmetic over natural numbers and integers. Introduce `_; exact ⟨by omega, Or.inr h2⟩`.

Establish `hjm : j = R.m` using `by omega`. Substitute `hjm` using the available equality. Establish `ha : aOf R R.m = R.r` using `if_neg (by omega)`. Establish `hs : skipOf R R.m = R.N R.m` using `if_neg h1`. Rewrite using `[ha, hs]`.

Establish `hl' : l = ⟨HXmsharp (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m) R.k R.r R.t R.m, lamXmsharp (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N R.m) R.k R.r R.t R.m⟩`. Rewrite using `[hl]`. Unfold `colLevS`. Rewrite using `[if_neg h1, if_neg h2]`. Substitute `hl'` using the available equality.

Use `glm_lamGen e σ₀ _ _ (Finset.range (R.r - 1)) ht (by rw [gll_Nm]; omega) (fun x hx => ?_) ⟨M, hM'.1.1⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `_`. Rewrite using `[gll_Nm]`.

Use linear arithmetic over natural numbers and integers. Introduce `_`. Use linear arithmetic over natural numbers and integers. Conclude with `key _ rfl hM`.
-/
theorem colLevS_lam_eq {j : ℕ} (hj : j ≤ R.m) (w : Pr.vGs) (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* k') (σ₀ : X.K →+* ℂ)
    (M : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)) (hM : M ∈ (colLevS Ch j w).H) :
    σ₀ (((colLevS Ch j w).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
      Formalism.L2.Forms.lamJ (glmPsi e σ₀ (Ch.psi0 w)) (fun s => glmChi e σ₀ (extChi (fun s => Ch.chi s w) s)) (aOf R j) R.t j (skipOf R j)
        ((M : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)).map e) := by
  have ht := gll_t_pos R
  have key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N j), l = colLevS Ch j w → ∀ hM' : M ∈ l.H,
      σ₀ ((l.lam ⟨M, hM'⟩ : X.Kˣ) : X.K) =
        Formalism.L2.Forms.lamJ (glmPsi e σ₀ (Ch.psi0 w)) (fun s => glmChi e σ₀ (extChi (fun s => Ch.chi s w) s)) (aOf R j) R.t j
          (skipOf R j) ((M : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)).map e) := by
    intro l hl hM'
    by_cases h1 : j + 1 < R.m
    · have ha : aOf R j = R.k + j := if_pos (by omega)
      have hs : skipOf R j = R.k := if_pos h1
      rw [ha, hs]
      have hl' : l = ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j,
          lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j⟩ := by
        rw [hl]; unfold colLevS colLev; rw [if_pos h1, if_pos (by omega)]
      subst hl'
      refine glm_lamGen e σ₀ _ _ (SX R.k R.m j) ht (by rw [gll_N]) (fun x hx => ?_) ⟨M, hM'⟩
      unfold SX
      rw [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨-, h | h⟩
        · exact h
        · omega
      · intro h; exact ⟨by omega, Or.inl h⟩
    · by_cases h2 : j + 1 = R.m
      · have ha : aOf R j = R.k + j := if_pos (by omega)
        have hs : skipOf R j = R.N j := if_neg h1
        rw [ha, hs]
        have hl' : l = ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j ⊓ fixCol (R.N j) (𝓞 X.E ⧸ w.1.asIdeal) R.k,
            (lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j).comp (Subgroup.inclusion inf_le_left)⟩ := by
          rw [hl]; unfold colLevS; rw [if_neg h1, if_pos h2]
        subst hl'
        refine glm_lamGen e σ₀ _ _ (SX R.k R.m j) ht (by rw [gll_N]) (fun x hx => ?_) ⟨M, hM'.1⟩
        unfold SX
        rw [Finset.mem_filter, Finset.mem_range]
        constructor
        · intro _; rw [gll_N]; omega
        · intro _; exact ⟨by omega, Or.inr h2⟩
      · have hjm : j = R.m := by omega
        subst hjm
        have ha : aOf R R.m = R.r := if_neg (by omega)
        have hs : skipOf R R.m = R.N R.m := if_neg h1
        rw [ha, hs]
        have hl' : l = ⟨HXmsharp (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m) R.k R.r R.t R.m,
            lamXmsharp (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N R.m) R.k R.r R.t R.m⟩ := by
          rw [hl]; unfold colLevS; rw [if_neg h1, if_neg h2]
        subst hl'
        refine glm_lamGen e σ₀ _ _ (Finset.range (R.r - 1)) ht (by rw [gll_Nm]; omega) (fun x hx => ?_) ⟨M, hM'.1.1⟩
        rw [Finset.mem_range]
        constructor
        · intro _; rw [gll_Nm]; omega
        · intro _; omega
  exact key _ rfl hM

/- English proof (translation)
Establish `hf : fcOf R R.m = R.k` using `if_pos (by omega)`. Rewrite using `[glm_InJ_map, hf, glm_InJ_false (j := R.m) (gll_t_pos R) (by rw [gll_Nm]; omega), rowTyG_sharp_H]`. Both sides reduce to the same expression.
-/
theorem rowTyG_sharp_mem_iff (w : Pr.vGs) (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* k')
    (M : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) :
    M ∈ (rowTyG Ch (rPsharp Ch) w).H ↔
      InJ R.r R.t (fcOf R R.m) false ((M : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)).map e) := by
  have hf : fcOf R R.m = R.k := if_pos (by omega)
  rw [glm_InJ_map, hf, glm_InJ_false (j := R.m) (gll_t_pos R) (by rw [gll_Nm]; omega), rowTyG_sharp_H]
  rfl

/- English proof (translation)
Establish `h2 : M ∈ HJsharp (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m` using `(rowTyG_sharp_H Ch w) ▸ hM`. Establish `h0 : M ∈ (rowTyG Ch (rP0 Ch) w).H` using `by rw [rowLevel_unipotent_group]; exact h2.1`. Establish `e1 : (rowTyG Ch (rPsharp Ch) w).lam ⟨M, hM⟩ = (rowTyG Ch (rP0 Ch) w).lam ⟨M, h0⟩` using `rfl`. Rewrite using `[e1, rowLevel_unipotent_character Ch w M h0 h2.1]`. Use `glm_lamGen e σ₀ _ _ (Finset.range (R.r - 1)) (gll_t_pos R) (by rw [gll_Nm]; omega) (fun x hx => ?_) ⟨M, h2.1⟩` and prove the remaining obligations.

Rewrite using `[Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `_`. Rewrite using `[gll_Nm]`. Use linear arithmetic over natural numbers and integers.

Introduce `_`. Use linear arithmetic over natural numbers and integers.
-/
theorem rowTyG_sharp_lam_eq (w : Pr.vGs) (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* k') (σ₀ : X.K →+* ℂ)
    (M : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hM : M ∈ (rowTyG Ch (rPsharp Ch) w).H) :
    σ₀ (((rowTyG Ch (rPsharp Ch) w).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
      Formalism.L2.Forms.lamJ (glmPsi e σ₀ (Ch.psi0 w)) (fun s => glmChi e σ₀ (extChi (fun s => Ch.chi s w) s)) R.r R.t R.m (R.N R.m)
        ((M : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)).map e) := by
  have h2 : M ∈ HJsharp (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m := (rowTyG_sharp_H Ch w) ▸ hM
  have h0 : M ∈ (rowTyG Ch (rP0 Ch) w).H := by rw [rowLevel_unipotent_group]; exact h2.1
  have e1 : (rowTyG Ch (rPsharp Ch) w).lam ⟨M, hM⟩ = (rowTyG Ch (rP0 Ch) w).lam ⟨M, h0⟩ := rfl
  rw [e1, rowLevel_unipotent_character Ch w M h0 h2.1]
  refine glm_lamGen e σ₀ _ _ (Finset.range (R.r - 1)) (gll_t_pos R) (by rw [gll_Nm]; omega) (fun x hx => ?_) ⟨M, h2.1⟩
  rw [Finset.mem_range]
  constructor
  · intro _; rw [gll_Nm]; omega
  · intro _; omega

end Steps

end Formalism.L2.Col

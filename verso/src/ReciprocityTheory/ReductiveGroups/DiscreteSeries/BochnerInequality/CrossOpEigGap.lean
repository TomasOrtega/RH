import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.InnerCrossOpEigEqZero

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section OneBAux

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

/- English proof (translation)
Establish `hd : Disjoint (univ.filter fun b => a < b ∧ e b ≠ e a) (univ.filter fun b => b < a ∧ e b ≠ e a)`. Rewrite using `[Finset.disjoint_filter]`. Introduce `b _ h1 h2`. Conclude with `lt_asymm h1.1 h2.1`. Rewrite using `[← Nat.cast_add, ← Finset.card_union_of_disjoint hd]`.

Conclude with `Finset.card_le_card (fun b hb => by` after adjusting the coercions. Simplify using `only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢`. Break down `hb with h | h` into its components or cases. Conclude with `h.2`. Conclude with `h.2)`.
-/
private lemma card_opposite_sign_above_add_below_le (e : Fin n → Bool) (a : Fin n) :
    ((univ.filter fun b => a < b ∧ e b ≠ e a).card : ℝ) +
      ((univ.filter fun b => b < a ∧ e b ≠ e a).card : ℝ) ≤
      ((univ.filter fun b => e b ≠ e a).card : ℝ) := by
  have hd : Disjoint (univ.filter fun b => a < b ∧ e b ≠ e a)
      (univ.filter fun b => b < a ∧ e b ≠ e a) := by
    rw [Finset.disjoint_filter]
    intro b _ h1 h2
    exact lt_asymm h1.1 h2.1
  rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hd]
  exact_mod_cast Finset.card_le_card (fun b hb => by
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rcases hb with h | h
    · exact h.2
    · exact h.2)

/- English proof (translation)
Establish `key : ∀ x y z : Bool, x ≠ y → x ≠ z → y ≠ z → False` using `by decide`. Establish `hd : Disjoint (univ.filter fun b => e b ≠ e r) (univ.filter fun b => e b ≠ e s)`. Rewrite using `[Finset.disjoint_filter]`. Introduce `b _ h1 h2`. Conclude with `key _ _ _ h1 h2 hrs`.

Rewrite using `[← Nat.cast_add, ← Finset.card_union_of_disjoint hd]`. Conclude with `(Finset.card_le_univ _).trans (by simp)` after adjusting the coercions.
-/
private lemma card_opposite_sign_add_le_of_ne (e : Fin n → Bool) {r s : Fin n} (hrs : e r ≠ e s) :
    ((univ.filter fun b => e b ≠ e r).card : ℝ) + ((univ.filter fun b => e b ≠ e s).card : ℝ) ≤ n := by
  have key : ∀ x y z : Bool, x ≠ y → x ≠ z → y ≠ z → False := by decide
  have hd : Disjoint (univ.filter fun b => e b ≠ e r) (univ.filter fun b => e b ≠ e s) := by
    rw [Finset.disjoint_filter]
    intro b _ h1 h2
    exact key _ _ _ h1 h2 hrs
  rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hd]
  exact_mod_cast (Finset.card_le_univ _).trans (by simp)

/- English proof (translation)
Establish `hVfd : FiniteDimensional ℂ V` using `hV.1`. Use `haveI := finiteDimensional_ncV (ε := ε) hVfd 1`. Use `set S := Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 with hSdef`. Use `haveI hfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_right`. Establish `hSst : IsKStableSub ε (bAct E 1) S`.

Introduce `a b hab v hv`. Take `⟨hv1, hv2⟩` from `Submodule.mem_inf.1 hv`. Use `Submodule.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hv1`, the goal using `[Module.End.mem_eigenspace_iff]`. Establish `hc` using `congrArg (fun T : Module.End ℂ (Big n 1 M) => T v) (crossOp_comm hE 1 0 hab)`.

Simplify using `only [Module.End.mul_apply] at hc`. Rewrite using `[hc, hv1, map_smul]`. Simplify using `only [bAct, LinearMap.add_apply, LinearMap.sum_apply]`. Conclude with `Submodule.add_mem _ (BigCasimir.mAct_mem_ncV hV.2.1 1 hab hv2) (Submodule.sum_mem _ fun i _ => BigCasimir.factorAd_mem_ncV i hab hv2)`. Establish `hCS : ∀ x ∈ S, casimirK ε (bAct E 1) x ∈ S` using `fun x hx => casimirK_mem_of_kStable hSst hx`.

Set `T : Module.End ℂ S` to `(casimirK ε (bAct E 1)).restrict hCS`. Use `haveI : Nontrivial S := ⟨⟨⟨y, hy⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue T`. Take `⟨v, hv⟩` from `hc.exists_hasEigenvector`. Establish `hvT` using `Module.End.mem_eigenspace_iff.1 hv.1`.

Establish `hx0 : (v : Big n 1 M) ≠ 0` using `fun h => hv.2 (Subtype.ext h)`. Establish `hxθ : casimirK ε (bAct E 1) (v : Big n 1 M) = c • (v : Big n 1 M)` using `congrArg Subtype.val hvT`. Take `⟨w, hwS, hw0, -, μ, hμw, -⟩` from `eig_casimirK (bAct_isGlRep hE 1) (bAct_isKUnitary hU 1) hfd hSst v.2 hx0 hxθ`. Take `⟨hw1, hw2⟩` from `Submodule.mem_inf.1 hwS`. Take `⟨r, s, hε, hμ, hcross⟩` from `crossOp_khw hE hU hV hw2 hw0 hμw`.

Establish `hθw : crossOp ε E 1 0 w = (θ : ℂ) • w` using `Module.End.mem_eigenspace_iff.1 hw1`. Rewrite `hcross` using `[hθw, smul_smul]`. Establish `h2` using `smul_left_injective ℂ hw0 hcross`. Establish `h2θ : 2 * θ = casValK ε μ - n - casValK ε (lowK ε lam)`. Establish `h3 : ((2 * θ : ℝ) : ℂ) = ((casValK ε μ - n - casValK ε (lowK ε lam) : ℝ) : ℂ)`.

Rewrite using `[← h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h3` after adjusting the coercions. Establish `hrs : r ≠ s` using `fun h => hε (congrArg ε h)`.

Establish `hroot : ∀ u : Fin n → ℝ, nsq (u + root r s) - nsq u = 2 * (u r - u s) + 2`. Introduce `u`. Establish `hs : ∀ a, root r s a = (if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0)` using `fun a => by`. Simplify using `[root, Pi.single_apply]`. Simplify using `only [nsq, dot, Pi.add_apply, hs]`.

Rewrite using `[← Finset.sum_sub_distrib]`. Establish `e : ∀ a, (u a + ((if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0))) * (u a + ((if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0))) - u a * u a = 2 * (if a = r then u a else 0) - 2 * (if a = s then u a else 0) + (if a = r then (1 : ℝ) else 0) + (if a = s then (1 : …` using `fun a => by split_ifs with h1 h2 h2`. Conclude with `absurd (h1.symm.trans h2) hrs`. Apply the tactic sequence `all_goals ring`. Simplify using `only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcas : casValK ε μ - casValK ε (lowK ε lam) = 2 * ((lowK ε lam + rhoC ε) r - (lowK ε lam + rhoC ε) s) + 2`. Rewrite using `[hμ]`. Unfold `casValK`. Rewrite using `[show lowK ε lam + root r s + rhoC ε = (lowK ε lam + rhoC ε) + root r s by abel]`.

Combine the linear relations using `[hroot (lowK ε lam + rhoC ε)]`. Establish `hL : ∀ a, (lowK ε lam + rhoC ε) a = lam a + rhoN ε a` using `fun a => by simp [lowK]`. Rewrite `hcas` using `[hL r, hL s]`. Establish `hθ : θ = (lam r + rhoN ε r) - (lam s + rhoN ε s) + 1 - n / 2` using `by linarith`. Establish `hrN : ∀ a, rhoN ε a = (((univ.filter fun b => a < b ∧ ε b ≠ ε a).card : ℝ) - ((univ.filter fun b => b < a ∧ ε b ≠ ε a).card : ℝ)) / 2` using `fun a => rfl`.

Establish `hPr` using `card_opposite_sign_above_add_below_le ε r`. Establish `hPs` using `card_opposite_sign_above_add_below_le ε s`. Establish `hO` using `card_opposite_sign_add_le_of_ne ε hε`. Establish `hpq : 1 ≤ (pOf ε : ℝ) ∧ 1 ≤ (qOf ε : ℝ)`. Establish `key : ∀ x y c : Bool, x ≠ y → x ≠ c → y = c` using `by decide`.

Establish `hmem : ∀ c : Bool, ∃ a, ε a = c` using `fun c => by`. Distinguish the cases in `h1 : ε r = c`. Conclude with `⟨r, h1⟩`. Conclude with `⟨s, key _ _ _ hε h1⟩`. Unfold `pOf qOf`.

Take `⟨a1, ha1⟩` from `hmem true`. Take `⟨a2, ha2⟩` from `hmem false`. Conclude with `⟨Nat.one_le_cast.2 (Finset.card_pos.2 ⟨a1, by simp [ha1]⟩), Nat.one_le_cast.2 (Finset.card_pos.2 ⟨a2, by simp [ha2]⟩)⟩`. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hpq1 : (1 : ℝ) * 1 ≤ (pOf ε : ℝ) * (qOf ε : ℝ)` using `mul_le_mul hpq.1 hpq.2 zero_le_one (by linarith [hpq.1])`.

Establish `hnpq : (n : ℝ) * 1 ≤ (n : ℝ) * ((pOf ε : ℝ) * (qOf ε : ℝ))`. Rewrite `hpq1` using `[one_mul]`. Conclude with `mul_le_mul_of_nonneg_left hpq1 hn0`. Establish `hhn : (n : ℝ) + 1 < h` using `by nlinarith`. Break down `le_abs'.1 (hh r s hε) with hcase | hcase` into its components or cases.

Establish `hlt : s < r` using `not_le.1 fun hle => absurd (hmono.antitone hle) (not_le.2 (by linarith))`. Establish `h1 : (1 : ℝ) ≤ ((univ.filter fun b => s < b ∧ ε b ≠ ε s).card : ℝ)` using `Nat.one_le_cast.2 (Finset.card_pos.2 ⟨r, by simp [hlt, hε]⟩)`. Establish `h2' : (1 : ℝ) ≤ ((univ.filter fun b => b < r ∧ ε b ≠ ε r).card : ℝ)` using `Nat.one_le_cast.2 (Finset.card_pos.2 ⟨s, by simp [hlt, Ne.symm hε]⟩)`. Use `right`. Use `⟨?_, by linarith⟩` and prove the remaining obligations.

Rewrite using `[hθ, hrN r, hrN s]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlt : r < s` using `not_le.1 fun hle => absurd (hmono.antitone hle) (not_le.2 (by linarith))`. Establish `h1 : (1 : ℝ) ≤ ((univ.filter fun b => r < b ∧ ε b ≠ ε r).card : ℝ)` using `Nat.one_le_cast.2 (Finset.card_pos.2 ⟨s, by simp [hlt, Ne.symm hε]⟩)`. Establish `h2' : (1 : ℝ) ≤ ((univ.filter fun b => b < s ∧ ε b ≠ ε s).card : ℝ)` using `Nat.one_le_cast.2 (Finset.card_pos.2 ⟨r, by simp [hlt, hε]⟩)`.

Use `left`. Use `⟨by linarith, ?_⟩` and prove the remaining obligations. Rewrite using `[hθ, hrN r, hrN s]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem crossOp_eig_gap (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {θ : ℝ} {y : Big n 1 M}
    (hy : y ∈ Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) (hy0 : y ≠ 0) :
    (0 < h - n + 1 ∧ h - n + 1 ≤ θ) ∨ (θ ≤ -h - 1 ∧ -h - 1 < 0) := by
  classical
  have hVfd : FiniteDimensional ℂ V := hV.1
  haveI := finiteDimensional_ncV (ε := ε) hVfd 1
  set S := Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 with hSdef
  haveI hfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_right

  have hSst : IsKStableSub ε (bAct E 1) S := by
    intro a b hab v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff] at hv1 ⊢
      have hc := congrArg (fun T : Module.End ℂ (Big n 1 M) => T v) (crossOp_comm hE 1 0 hab)
      simp only [Module.End.mul_apply] at hc
      rw [hc, hv1, map_smul]
    · simp only [bAct, LinearMap.add_apply, LinearMap.sum_apply]
      exact Submodule.add_mem _ (BigCasimir.mAct_mem_ncV hV.2.1 1 hab hv2)
        (Submodule.sum_mem _ fun i _ => BigCasimir.factorAd_mem_ncV i hab hv2)

  have hCS : ∀ x ∈ S, casimirK ε (bAct E 1) x ∈ S := fun x hx => casimirK_mem_of_kStable hSst hx
  let T : Module.End ℂ S := (casimirK ε (bAct E 1)).restrict hCS
  haveI : Nontrivial S := ⟨⟨⟨y, hy⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hvT := Module.End.mem_eigenspace_iff.1 hv.1
  have hx0 : (v : Big n 1 M) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hxθ : casimirK ε (bAct E 1) (v : Big n 1 M) = c • (v : Big n 1 M) := congrArg Subtype.val hvT
  obtain ⟨w, hwS, hw0, -, μ, hμw, -⟩ :=
    eig_casimirK (bAct_isGlRep hE 1) (bAct_isKUnitary hU 1) hfd hSst v.2 hx0 hxθ
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hwS
  obtain ⟨r, s, hε, hμ, hcross⟩ := crossOp_khw hE hU hV hw2 hw0 hμw
  have hθw : crossOp ε E 1 0 w = (θ : ℂ) • w := Module.End.mem_eigenspace_iff.1 hw1
  rw [hθw, smul_smul] at hcross
  have h2 := smul_left_injective ℂ hw0 hcross
  have h2θ : 2 * θ = casValK ε μ - n - casValK ε (lowK ε lam) := by
    have h3 : ((2 * θ : ℝ) : ℂ) = ((casValK ε μ - n - casValK ε (lowK ε lam) : ℝ) : ℂ) := by
      rw [← h2]
      push_cast
      ring
    exact_mod_cast h3

  have hrs : r ≠ s := fun h => hε (congrArg ε h)
  have hroot : ∀ u : Fin n → ℝ, nsq (u + root r s) - nsq u = 2 * (u r - u s) + 2 := by
    intro u
    have hs : ∀ a, root r s a = (if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0) := fun a => by
      simp [root, Pi.single_apply]
    simp only [nsq, dot, Pi.add_apply, hs]
    rw [← Finset.sum_sub_distrib]
    have e : ∀ a, (u a + ((if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0))) *
        (u a + ((if a = r then (1 : ℝ) else 0) - (if a = s then 1 else 0))) - u a * u a =
        2 * (if a = r then u a else 0) - 2 * (if a = s then u a else 0) +
          (if a = r then (1 : ℝ) else 0) + (if a = s then (1 : ℝ) else 0) := fun a => by
      split_ifs with h1 h2 h2
      · exact absurd (h1.symm.trans h2) hrs
      all_goals ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hcas : casValK ε μ - casValK ε (lowK ε lam) =
      2 * ((lowK ε lam + rhoC ε) r - (lowK ε lam + rhoC ε) s) + 2 := by
    rw [hμ]
    unfold casValK
    rw [show lowK ε lam + root r s + rhoC ε = (lowK ε lam + rhoC ε) + root r s by abel]
    linarith [hroot (lowK ε lam + rhoC ε)]
  have hL : ∀ a, (lowK ε lam + rhoC ε) a = lam a + rhoN ε a := fun a => by simp [lowK]
  rw [hL r, hL s] at hcas
  have hθ : θ = (lam r + rhoN ε r) - (lam s + rhoN ε s) + 1 - n / 2 := by linarith

  have hrN : ∀ a, rhoN ε a = (((univ.filter fun b => a < b ∧ ε b ≠ ε a).card : ℝ) -
      ((univ.filter fun b => b < a ∧ ε b ≠ ε a).card : ℝ)) / 2 := fun a => rfl
  have hPr := card_opposite_sign_above_add_below_le ε r
  have hPs := card_opposite_sign_above_add_below_le ε s
  have hO := card_opposite_sign_add_le_of_ne ε hε
  have hpq : 1 ≤ (pOf ε : ℝ) ∧ 1 ≤ (qOf ε : ℝ) := by
    have key : ∀ x y c : Bool, x ≠ y → x ≠ c → y = c := by decide
    have hmem : ∀ c : Bool, ∃ a, ε a = c := fun c => by
      by_cases h1 : ε r = c
      · exact ⟨r, h1⟩
      · exact ⟨s, key _ _ _ hε h1⟩
    unfold pOf qOf
    obtain ⟨a1, ha1⟩ := hmem true
    obtain ⟨a2, ha2⟩ := hmem false
    exact ⟨Nat.one_le_cast.2 (Finset.card_pos.2 ⟨a1, by simp [ha1]⟩),
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨a2, by simp [ha2]⟩)⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpq1 : (1 : ℝ) * 1 ≤ (pOf ε : ℝ) * (qOf ε : ℝ) :=
    mul_le_mul hpq.1 hpq.2 zero_le_one (by linarith [hpq.1])
  have hnpq : (n : ℝ) * 1 ≤ (n : ℝ) * ((pOf ε : ℝ) * (qOf ε : ℝ)) := by
    rw [one_mul] at hpq1
    exact mul_le_mul_of_nonneg_left hpq1 hn0
  have hhn : (n : ℝ) + 1 < h := by nlinarith
  rcases le_abs'.1 (hh r s hε) with hcase | hcase
  ·
    have hlt : s < r := not_le.1 fun hle => absurd (hmono.antitone hle) (not_le.2 (by linarith))
    have h1 : (1 : ℝ) ≤ ((univ.filter fun b => s < b ∧ ε b ≠ ε s).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨r, by simp [hlt, hε]⟩)
    have h2' : (1 : ℝ) ≤ ((univ.filter fun b => b < r ∧ ε b ≠ ε r).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨s, by simp [hlt, Ne.symm hε]⟩)
    right
    refine ⟨?_, by linarith⟩
    rw [hθ, hrN r, hrN s]
    linarith
  ·
    have hlt : r < s := not_le.1 fun hle => absurd (hmono.antitone hle) (not_le.2 (by linarith))
    have h1 : (1 : ℝ) ≤ ((univ.filter fun b => r < b ∧ ε b ≠ ε r).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨s, by simp [hlt, Ne.symm hε]⟩)
    have h2' : (1 : ℝ) ≤ ((univ.filter fun b => b < s ∧ ε b ≠ ε s).card : ℝ) :=
      Nat.one_le_cast.2 (Finset.card_pos.2 ⟨r, by simp [hlt, hε]⟩)
    left
    refine ⟨by linarith, ?_⟩
    rw [hθ, hrN r, hrN s]
    linarith

end OneBAux

end ReciprocityTheory.ChartRestriction.DS

import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Conclude with `(hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.1`.
-/
private lemma lft_uni' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β)
    (L : Finset κ) : lft (uni b L) = b := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.1

/- English proof (translation)
Conclude with `(hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.2.1`.
-/
private lemma rgt_uni' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β)
    (L : Finset κ) : rgt (uni b L) = L := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.2.1

/- English proof (translation)
Conclude with `(hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.2.2.1`.
-/
private lemma card_uni' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β)
    (L : Finset κ) : (uni b L).card = b.card + L.card := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.2.2.1

/- English proof (translation)
Conclude with `(hU β κ ℂ (fun _ => 0) (fun _ => 0) ∅ ∅).2.2.2.2 s`.
-/
private lemma uni_lr' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ]
    (s : Finset (β ⊕ₗ κ)) : uni (lft s) (rgt s) = s := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) ∅ ∅).2.2.2.2 s

/- English proof (translation)
Use `show c ∈ Submodule.pi Set.univ _ ↔ _`. Simplify using `only [Submodule.mem_pi, Set.mem_univ, true_implies]`.
-/
private lemma mem_acxC {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥) := by
  show c ∈ Submodule.pi Set.univ _ ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]

/- English proof (translation)
Simplify using `only [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]`. Conclude with `Finset.sum_eq_zero fun i hi => by rw [h i hi]; simp`.
-/
private lemma wd_eq_zero {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (w : σ → Module.End ℂ E) (f : Finset σ → E) (t : Finset σ)
    (h : ∀ i ∈ t, f (t.erase i) = 0) : wd w f t = 0 := by
  simp only [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  exact Finset.sum_eq_zero fun i hi => by rw [h i hi]; simp

section
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
  (T : Sys d S E) {κ : Type} [LinearOrder κ]

/- English proof (translation)
The claim follows from `mem_acxC _ _ _ _`.
-/
private lemma col_iff (n : κ → ℕ × ℕ) (z : κ → S) (I J : Finset (Fin (d + 1))) (m : ℤ)
    (x : Finset κ → E) : x ∈ (T.colCx n z I J).C m ↔ ∀ L, x L ∈ (if (L.card : ℤ) = m then
      (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) else ⊥) :=
  mem_acxC _ _ _ _

/- English proof (translation)
Establish `key : ∀ (I J : Finset (Fin (d + 1))) (L : Finset κ), (if (((uni (uni I J) L).card : ℕ) : ℤ) = N then mixF (fun I' J' => Submodule.map (T.act ((∏ l ∈ rgt (uni (uni I J) L), T.u n (pk I') (pk J') l : Sˣ) : S)) (T.M I' J')) (lft (uni (uni I J) L)) else ⊥) = (if I.Nonempty ∧ J.Nonemp …`. Introduce `I J L`. Simplify using `only [lft_uni' hU, rgt_uni' hU, card_uni' hU, mixF]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; tauto)`. Use `(mem_acxC _ _ N c).trans ?_` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `h I J L`. Rewrite using `[← key]`. Conclude with `h _`. Introduce `h s`.

Take `⟨I, J, L, rfl⟩ : ∃ I J L, s = uni (uni I J) L` from `⟨_, _, _, by rw [uni_lr' hU, uni_lr' hU]⟩`. Rewrite using `[key]`. Conclude with `h I J L`.
-/
private lemma cx_iff (hU : WdUni) (n : κ → ℕ × ℕ) (z : κ → S) (N : ℤ)
    (c : Finset (Two d ⊕ₗ κ) → E) : c ∈ (T.cx n z).C N ↔ ∀ I J L, c (uni (uni I J) L) ∈
      (if I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = N then
        (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) else ⊥) := by
  have key : ∀ (I J : Finset (Fin (d + 1))) (L : Finset κ),
      (if (((uni (uni I J) L).card : ℕ) : ℤ) = N then
        mixF (fun I' J' => Submodule.map (T.act ((∏ l ∈ rgt (uni (uni I J) L),
          T.u n (pk I') (pk J') l : Sˣ) : S)) (T.M I' J')) (lft (uni (uni I J) L)) else ⊥) =
      (if I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = N then
        (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) else ⊥) := by
    intro I J L
    simp only [lft_uni' hU, rgt_uni' hU, card_uni' hU, mixF]
    split_ifs <;> first | rfl | (exfalso; tauto)
  refine (mem_acxC _ _ N c).trans ?_
  constructor
  · intro h I J L
    rw [← key]
    exact h _
  · intro h s
    obtain ⟨I, J, L, rfl⟩ : ∃ I J L, s = uni (uni I J) L :=
      ⟨_, _, _, by rw [uni_lr' hU, uni_lr' hU]⟩
    rw [key]
    exact h I J L

/- English proof (translation)
Use `(mem_acxC _ _ N _).mpr ?_` and prove the remaining obligations. Introduce `b`. Take `⟨I, J, rfl⟩ : ∃ I J, b = uni I J` from `⟨lft b, rgt b, (uni_lr' hU b).symm⟩`. Establish `h1` using `(cx_iff T hU n z N c).mp hc I J ∅`. Simplify using `only [top, mixF, lft_uni' hU, rgt_uni' hU, card_uni' hU, Finset.prod_empty, Finset.card_empty, add_zero, Units.val_one, map_one] at h1 ⊢`.

Rewrite `h1` using `[Module.End.one_eq_id, Submodule.map_id]`. Apply the tactic sequence `split_ifs at h1 ⊢ <;> first | exact h1 | (exfalso; tauto) | simp_all`.
-/
private lemma top_C (hU : WdUni) (n : κ → ℕ × ℕ) (z : κ → S) (N : ℤ)
    (c : Finset (Two d ⊕ₗ κ) → E) (hc : c ∈ (T.cx n z).C N) : top c ∈ T.mix.C N := by
  refine (mem_acxC _ _ N _).mpr ?_
  intro b
  obtain ⟨I, J, rfl⟩ : ∃ I J, b = uni I J := ⟨lft b, rgt b, (uni_lr' hU b).symm⟩
  have h1 := (cx_iff T hU n z N c).mp hc I J ∅
  simp only [top, mixF, lft_uni' hU, rgt_uni' hU, card_uni' hU, Finset.prod_empty,
    Finset.card_empty, add_zero, Units.val_one, map_one] at h1 ⊢
  rw [Module.End.one_eq_id, Submodule.map_id] at h1
  split_ifs at h1 ⊢ <;> first | exact h1 | (exfalso; tauto) | simp_all

/- English proof (translation)
Use function extensionality and compare the values at `b`. Simplify using `only [top]`. Rewrite using `[(hU _ _ _ (T.wt z) c b ∅).1]`. Establish `h0 : wd (fun l => T.wt z (inrE l)) (fun L' => c (uni b L')) ∅ = 0`. Simplify using `[wd]`.

Rewrite using `[h0, smul_zero, add_zero]`. Establish `hw : (fun i => T.wt z (inlE i)) = fun _ : Two d => (1 : Module.End ℂ E)`. Use function extensionality and compare the values at `i`. Simplify using `[Sys.wt, inlE]`. Rewrite using `[hw]`.

Both sides reduce to the same expression.
-/
private lemma top_D (hU : WdUni) (z : κ → S) (c : Finset (Two d ⊕ₗ κ) → E) :
    top (wd (T.wt z) c) = wd (fun _ : Two d => (1 : Module.End ℂ E)) (top c) := by
  funext b
  simp only [top]
  rw [(hU _ _ _ (T.wt z) c b ∅).1]
  have h0 : wd (fun l => T.wt z (inrE l)) (fun L' => c (uni b L')) ∅ = 0 := by
    simp [wd]
  rw [h0, smul_zero, add_zero]
  have hw : (fun i => T.wt z (inlE i)) = fun _ : Two d => (1 : Module.End ℂ E) := by
    funext i
    simp [Sys.wt, inlE]
  rw [hw]
  rfl

end

/- English proof (translation)
Establish `hwl : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (i : Two d), T.wt z₀ (inlE i) = 1`. Introduce `κ₀ _ z₀ i`. Simplify using `[Sys.wt, inlE]`. Establish `hwr : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (l : κ₀), T.wt z₀ (inrE l) = T.act (z₀ l)`. Introduce `κ₀ _ z₀ l`.

Simplify using `[Sys.wt, inrE]`. Use function extensionality and compare the values at `s`. Take `⟨b, L, rfl⟩ : ∃ b L, s = uni b L` from `⟨lft s, rgt s, (uni_lr' hU s).symm⟩`. Rewrite using `[(hU _ _ _ _ (resK e c) b L).1]`. Establish `hres : ∀ b' L', resK e c (uni b' L') = c (uni b' (L'.map e.toEmbedding))`.

Introduce `b' L'`. Simplify using `only [resK, lft_uni' hU, rgt_uni' hU]`. Establish `hmap : wd (fun l => T.act (z (e l))) (fun L' => c (uni b (L'.map e.toEmbedding))) L = wd (fun l => T.act (z l)) (fun L' => c (uni b L')) (L.map e.toEmbedding)` using `(hB κ E (fun _ => ⊥) (fun l => T.act (z l))).2.2.2.2.2 κ' e (fun L' => c (uni b L')) L`. Establish `e2` using `(hU _ _ _ (T.wt z) c b (L.map e.toEmbedding)).1`. Rewrite `e2` using `[hD]`.

Simplify using `only [hres, hwl, hwr]`. Rewrite using `[hmap]`. Simplify using `only [hwl, hwr] at e2`. Rewrite using `[← e2]`. Both sides reduce to the same expression.
-/
private theorem wd_wt_resK_eq_zero_of_wd_eq_zero (hU : WdUni) (hB : WdBasic) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) {κ : Type} [LinearOrder κ] [Fintype κ]
    (z : κ → S) {κ' : Type} [LinearOrder κ'] (e : κ' ↪o κ) (c : Finset (Two d ⊕ₗ κ) → E)
    (hD : wd (T.wt z) c = 0) : wd (T.wt fun l => z (e l)) (resK e c) = 0 := by
  have hwl : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (i : Two d), T.wt z₀ (inlE i) = 1 := by
    intro κ₀ _ z₀ i
    simp [Sys.wt, inlE]
  have hwr : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (l : κ₀), T.wt z₀ (inrE l) = T.act (z₀ l) := by
    intro κ₀ _ z₀ l
    simp [Sys.wt, inrE]
  funext s
  obtain ⟨b, L, rfl⟩ : ∃ b L, s = uni b L := ⟨lft s, rgt s, (uni_lr' hU s).symm⟩
  rw [(hU _ _ _ _ (resK e c) b L).1]
  have hres : ∀ b' L', resK e c (uni b' L') = c (uni b' (L'.map e.toEmbedding)) := by
    intro b' L'
    simp only [resK, lft_uni' hU, rgt_uni' hU]
  have hmap : wd (fun l => T.act (z (e l))) (fun L' => c (uni b (L'.map e.toEmbedding))) L =
      wd (fun l => T.act (z l)) (fun L' => c (uni b L')) (L.map e.toEmbedding) :=
    (hB κ E (fun _ => ⊥) (fun l => T.act (z l))).2.2.2.2.2 κ' e (fun L' => c (uni b L')) L
  have e2 := (hU _ _ _ (T.wt z) c b (L.map e.toEmbedding)).1
  rw [hD] at e2
  simp only [hres, hwl, hwr]
  rw [hmap]
  simp only [hwl, hwr] at e2
  rw [← e2]
  rfl

/- English proof (translation)
Introduce `hU hB d S E _ _ _ _ T κ _ _ n z N`. Establish `hmem : ∀ c, c ∈ (T.cx n z).C N → ∀ (I J : Finset (Fin (d + 1))) (L : Finset κ), ¬ (I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = N) → c (uni (uni I J) L) = 0`. Introduce `c hc I J L h`. Use `(cx_iff T hU n z N c).mp hc I J L` as an intermediate fact. Rewrite `this` using `[if_neg h]`.

Conclude with `(Submodule.mem_bot ℂ).mp this`. Establish `h2 : ∀ c : Finset (Two d ⊕ₗ κ) → E, c ∈ (T.cx n z).C N ↔ ∀ (I J : Finset (Fin (d + 1))), col c (uni I J) ∈ (if I.Nonempty ∧ J.Nonempty then (T.colCx n z I J).C (N - I.card - J.card) else ⊥)`. Introduce `c`. Rewrite using `[cx_iff T hU]`. Use `forall_congr' fun I => forall_congr' fun J => ?_` and prove the remaining obligations.

Distinguish the cases in `hIJ : I.Nonempty ∧ J.Nonempty`. Rewrite using `[if_pos hIJ, col_iff]`. Use `forall_congr' fun L => ?_` and prove the remaining obligations. Simplify using `only [col]`. Distinguish the cases in `hL : (L.card : ℤ) = N - I.card - J.card`.

Rewrite using `[if_pos hL, if_pos ⟨hIJ.1, hIJ.2, by push_cast; omega⟩]`. Rewrite using `[if_neg hL, if_neg (fun h => hL (by have := h.2.2; push_cast at this; omega))]`. Rewrite using `[if_neg hIJ, Submodule.mem_bot, funext_iff]`. Use `forall_congr' fun L => ?_` and prove the remaining obligations. Rewrite using `[if_neg (fun h => hIJ ⟨h.1, h.2.1⟩), Submodule.mem_bot]`.

Both sides reduce to the same expression. Establish `hwr : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (l : κ₀), T.wt z₀ (inrE l) = T.act (z₀ l)`. Introduce `κ₀ _ z₀ l`. Simplify using `[Sys.wt, inrE]`. Use `⟨?_, h2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `c hc I J L h`. Apply `hmem c hc I J L` to reduce the goal to its premises. Introduce and unpack `⟨hI, hJ, hN⟩`. Break down `h with h | h | h` into its components or cases. Substitute `h` using the available equality.

Conclude with `Finset.not_nonempty_empty hI`. Substitute `h` using the available equality. Conclude with `Finset.not_nonempty_empty hJ`. Conclude with `h hN`. Introduce `c hc`.

Take `⟨hC, hD⟩` from `Submodule.mem_inf.mp hc`. Use `Submodule.mem_inf.mpr ⟨top_C T hU n z N c hC, ?_⟩` and prove the remaining obligations. Rewrite `hD`, the goal using `[LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `wd (fun _ : Two d => (1 : Module.End ℂ E)) (top c) = 0`. Rewrite using `[← top_D T hU z c]`.

Express the relevant statement in the definitionally equal form `wd (T.wt z) c = 0 at hD`. Rewrite using `[hD]`. Both sides reduce to the same expression. Introduce `c hc`. Take `⟨c', hc', rfl⟩` from `Submodule.mem_map.mp hc`.

Conclude with `Submodule.mem_map.mpr ⟨top c', top_C T hU n z (N - 1) c' hc', (top_D T hU z c').symm⟩`. Introduce `c hc I J hI hJ hlow`. Take `⟨hC, hD⟩` from `Submodule.mem_inf.mp hc`. Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Use `(h2 c).mp hC I J` as an intermediate fact.

Rewrite `this` using `[if_pos ⟨hI, hJ⟩]`. Then use the resulting hypothesis. Rewrite `hD`, the goal using `[LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `wd (fun l => T.act (z l)) (col c (uni I J)) = 0`. Express the relevant statement in the definitionally equal form `wd (T.wt z) c = 0 at hD`. Use function extensionality and compare the values at `L`.

Establish `e1` using `(hU _ _ _ (T.wt z) c (uni I J) L).1`. Rewrite `e1` using `[hD]`. Establish `key : ∀ t : Finset (Two d), t.card < (uni I J).card → c (uni t L) = 0`. Introduce `t ht`. Rewrite using `[← uni_lr' hU t]`.

Apply `hlow` to reduce the goal to its premises. Establish `h3` using `card_uni' hU (lft t) (rgt t)`. Rewrite `h3` using `[uni_lr' hU]`. Rewrite `ht` using `[card_uni' hU]`. Use linear arithmetic over natural numbers and integers.

Establish `hz1 : wd (fun b => T.wt z (inlE b)) (fun b' => c (uni b' L)) (uni I J) = 0`. Apply `wd_eq_zero` to reduce the goal to its premises. Introduce `i hi`. Conclude with `key _ (Finset.card_erase_lt_of_mem hi)`. Rewrite `e1` using `[hz1, zero_add]`.

Simplify using `only [hwr, Pi.zero_apply] at e1 ⊢`. Apply the tactic sequence `rcases neg_one_pow_eq_or ℤ (uni I J).card with h | h <;> rw [h] at e1 <;> simp at e1 <;> first | exact e1.symm | exact e1 | exact neg_eq_zero.mp e1.symm`. Introduce `κ' _ _ e c hc`. Take `⟨hC, hD⟩` from `Submodule.mem_inf.mp hc`. Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[cx_iff T hU]`. Introduce `I J L`. Use `(cx_iff T hU n z N c).mp hC I J (L.map e.toEmbedding)` as an intermediate fact. Simplify using `only [resK, lft_uni' hU, rgt_uni' hU]`. Rewrite `this` using `[Finset.card_map, Finset.prod_map]`.

Conclude with `this`. Rewrite `hD`, the goal using `[LinearMap.mem_ker]`. Conclude with `wd_wt_resK_eq_zero_of_wd_eq_zero hU hB T z e c hD`.
-/
theorem UpperTheory.Gal.productCup_of_system.sysBasic_of :
    WdUni → WdBasic → SysBasic := by
  intro hU hB d S E _ _ _ _ T κ _ _ n z N
  have hmem : ∀ c, c ∈ (T.cx n z).C N → ∀ (I J : Finset (Fin (d + 1))) (L : Finset κ),
      ¬ (I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = N) →
      c (uni (uni I J) L) = 0 := by
    intro c hc I J L h
    have := (cx_iff T hU n z N c).mp hc I J L
    rw [if_neg h] at this
    exact (Submodule.mem_bot ℂ).mp this
  have h2 : ∀ c : Finset (Two d ⊕ₗ κ) → E, c ∈ (T.cx n z).C N ↔
      ∀ (I J : Finset (Fin (d + 1))), col c (uni I J) ∈
        (if I.Nonempty ∧ J.Nonempty then (T.colCx n z I J).C (N - I.card - J.card) else ⊥) := by
    intro c
    rw [cx_iff T hU]
    refine forall_congr' fun I => forall_congr' fun J => ?_
    by_cases hIJ : I.Nonempty ∧ J.Nonempty
    · rw [if_pos hIJ, col_iff]
      refine forall_congr' fun L => ?_
      simp only [col]
      by_cases hL : (L.card : ℤ) = N - I.card - J.card
      · rw [if_pos hL, if_pos ⟨hIJ.1, hIJ.2, by push_cast; omega⟩]
      · rw [if_neg hL, if_neg (fun h => hL (by have := h.2.2; push_cast at this; omega))]
    · rw [if_neg hIJ, Submodule.mem_bot, funext_iff]
      refine forall_congr' fun L => ?_
      rw [if_neg (fun h => hIJ ⟨h.1, h.2.1⟩), Submodule.mem_bot]
      rfl
  have hwr : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (l : κ₀), T.wt z₀ (inrE l) = T.act (z₀ l) := by
    intro κ₀ _ z₀ l
    simp [Sys.wt, inrE]
  refine ⟨?_, h2, ?_, ?_, ?_, ?_⟩
  · intro c hc I J L h
    apply hmem c hc I J L
    rintro ⟨hI, hJ, hN⟩
    rcases h with h | h | h
    · subst h; exact Finset.not_nonempty_empty hI
    · subst h; exact Finset.not_nonempty_empty hJ
    · exact h hN
  · intro c hc
    obtain ⟨hC, hD⟩ := Submodule.mem_inf.mp hc
    refine Submodule.mem_inf.mpr ⟨top_C T hU n z N c hC, ?_⟩
    rw [LinearMap.mem_ker] at hD ⊢
    change wd (fun _ : Two d => (1 : Module.End ℂ E)) (top c) = 0
    rw [← top_D T hU z c]
    change wd (T.wt z) c = 0 at hD
    rw [hD]
    rfl
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := Submodule.mem_map.mp hc
    exact Submodule.mem_map.mpr ⟨top c', top_C T hU n z (N - 1) c' hc', (top_D T hU z c').symm⟩
  · intro c hc I J hI hJ hlow
    obtain ⟨hC, hD⟩ := Submodule.mem_inf.mp hc
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · have := (h2 c).mp hC I J
      rwa [if_pos ⟨hI, hJ⟩] at this
    · rw [LinearMap.mem_ker] at hD ⊢
      change wd (fun l => T.act (z l)) (col c (uni I J)) = 0
      change wd (T.wt z) c = 0 at hD
      funext L
      have e1 := (hU _ _ _ (T.wt z) c (uni I J) L).1
      rw [hD] at e1
      have key : ∀ t : Finset (Two d), t.card < (uni I J).card → c (uni t L) = 0 := by
        intro t ht
        rw [← uni_lr' hU t]
        apply hlow
        have h3 := card_uni' hU (lft t) (rgt t)
        rw [uni_lr' hU] at h3
        rw [card_uni' hU] at ht
        omega
      have hz1 : wd (fun b => T.wt z (inlE b)) (fun b' => c (uni b' L)) (uni I J) = 0 := by
        apply wd_eq_zero
        intro i hi
        exact key _ (Finset.card_erase_lt_of_mem hi)
      rw [hz1, zero_add] at e1
      simp only [hwr, Pi.zero_apply] at e1 ⊢
      rcases neg_one_pow_eq_or ℤ (uni I J).card with h | h <;> rw [h] at e1 <;> simp at e1 <;>
        first | exact e1.symm | exact e1 | exact neg_eq_zero.mp e1.symm
  · intro κ' _ _ e c hc
    obtain ⟨hC, hD⟩ := Submodule.mem_inf.mp hc
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [cx_iff T hU]
      intro I J L
      have := (cx_iff T hU n z N c).mp hC I J (L.map e.toEmbedding)
      simp only [resK, lft_uni' hU, rgt_uni' hU]
      rw [Finset.card_map, Finset.prod_map] at this
      exact this
    · rw [LinearMap.mem_ker] at hD ⊢
      exact wd_wt_resK_eq_zero_of_wd_eq_zero hU hB T z e c hD

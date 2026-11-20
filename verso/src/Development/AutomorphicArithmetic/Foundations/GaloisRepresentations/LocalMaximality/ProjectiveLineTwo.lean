import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system.ProjectiveLineTwo

variable {E : Type} [AddCommGroup E] [Module ℂ E]

/- English proof (translation)
Use `show c ∈ Submodule.pi Set.univ _ ↔ _`. Simplify using `only [Submodule.mem_pi, Set.mem_univ, true_implies]`.
-/
private lemma mem_acxC {σ : Type} [LinearOrder σ] (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E)
    (n : ℤ) (c : Finset σ → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) := by
  show c ∈ Submodule.pi Set.univ _ ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]

/- English proof (translation)
Use `(mem_acxC A w n c).1 h s` as an intermediate fact. Rewrite `this` using `[if_neg hs]`. Simplify using `using this`.
-/
private lemma val_zero {σ : Type} [LinearOrder σ] {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    {n : ℤ} {c : Finset σ → E} (h : c ∈ (acx A w).C n) (s : Finset σ) (hs : (s.card : ℤ) ≠ n) : c s = 0 := by
  have := (mem_acxC A w n c).1 h s
  rw [if_neg hs] at this
  simpa using this

/- English proof (translation)
Use `(mem_acxC A w n c).1 h s` as an intermediate fact. Rewrite `this` using `[if_pos hs]`. Then use the resulting hypothesis.
-/
private lemma val_mem {σ : Type} [LinearOrder σ] {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    {n : ℤ} {c : Finset σ → E} (h : c ∈ (acx A w).C n) (s : Finset σ) (hs : (s.card : ℤ) = n) : c s ∈ A s := by
  have := (mem_acxC A w n c).1 h s
  rwa [if_pos hs] at this

/- English proof (translation)
Simplify using `[wd, LinearMap.sum_apply]`.
-/
private lemma wd_apply' {σ : Type} [LinearOrder σ] (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

/- English proof (translation)
Rewrite using `[wd_apply', wd_apply']`. Conclude with `Finset.sum_congr rfl fun i hi => by rw [h i hi]`.
-/
private lemma wd_congr' {σ : Type} [LinearOrder σ] (w : σ → Module.End ℂ E) (c c' : Finset σ → E) (t : Finset σ)
    (h : ∀ i ∈ t, c (t.erase i) = c' (t.erase i)) : wd w c t = wd w c' t := by
  rw [wd_apply', wd_apply']
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi]

/- English proof (translation)
Rewrite using `[wd_apply']`. Simplify using the standard rewrite rules.
-/
private lemma wd_zero' {σ : Type} [LinearOrder σ] (c : Finset σ → E) (t : Finset σ) :
    wd (fun _ => (0 : Module.End ℂ E)) c t = 0 := by
  rw [wd_apply']
  simp

/- English proof (translation)
Establish `h : s ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding = (rgt s).map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding`. Use extensionality with `t`. Take `⟨t, rfl⟩` from `toLex.surjective t`. Apply the tactic sequence `rcases t with t | t <;> simp [rgt, inrE]`. Rewrite using `[h, Finset.card_map]`.
-/
private lemma inter_card {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (s : Finset (β ⊕ₗ κ)) :
    (s ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding).card = (rgt s).card := by
  have h : s ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding = (rgt s).map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
    ext t
    obtain ⟨t, rfl⟩ := toLex.surjective t
    rcases t with t | t <;> simp [rgt, inrE]
  rw [h, Finset.card_map]

end UpperTheory.Gal.productCup_of_system.ProjectiveLineTwo

open UpperTheory.Gal.productCup_of_system.ProjectiveLineTwo in
/- English proof (translation)
Introduce `hG hC hU β κ E _ _ _ _ _ _ A w d n hW hK c0 hZ hB`. Take `⟨Q, hQ⟩ : ∃ Q, Q = Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding` from `⟨_, rfl⟩`. Establish `hQex : QEx A w Q d` using `by rw [hQ]; exact hC β κ E A w d hK`. Establish `hcap : ∀ s : Finset (β ⊕ₗ κ), (s ∩ Q).card = (rgt s).card` using `fun s => by rw [hQ]; exact inter_card s`. Establish `hinl : ∀ i : β, (inlE i : β ⊕ₗ κ) ∉ Q` using `fun i => by simp [hQ, inlE, inrE]`.

Establish `hinr : ∀ l : κ, (inrE l : β ⊕ₗ κ) ∈ Q` using `fun l => by simp [hQ]`. Establish `hl : ∀ (b : Finset β) (L : Finset κ), lft (uni b L) = b` using `fun b L => (hU β κ E w 0 b L).2.1`. Establish `hr : ∀ (b : Finset β) (L : Finset κ), rgt (uni b L) = L` using `fun b L => (hU β κ E w 0 b L).2.2.1`. Establish `hcd : ∀ (b : Finset β) (L : Finset κ), (uni b L).card = b.card + L.card` using `fun b L => (hU β κ E w 0 b L).2.2.2.1`. Establish `hs : ∀ s : Finset (β ⊕ₗ κ), uni (lft s) (rgt s) = s` using `(hU β κ E w 0 ∅ ∅).2.2.2.2`.

Establish `hsc : ∀ s : Finset (β ⊕ₗ κ), s.card = (lft s).card + (rgt s).card` using `fun s => by conv_lhs => rw [← hs s]`. Conclude with `hcd _ _`. Establish `wdQ : ∀ (c : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ), wd (wOn Q w) c (uni b L) = ((-1 : ℤ) ^ b.card) • wd (fun l => w (inrE l)) (fun L' => c (uni b L')) L`. Introduce `c b L`. Rewrite using `[(hU β κ E (wOn Q w) c b L).1]`.

Establish `h1 : (fun i => wOn Q w (inlE i)) = fun _ => (0 : Module.End ℂ E)`. Use function extensionality and compare the values at `i`. Simplify using `[wOn, hinl]`. Establish `h2 : (fun l => wOn Q w (inrE l)) = fun l => w (inrE l)`. Use function extensionality and compare the values at `l`.

Simplify using `[wOn, hinr]`. Rewrite using `[h1, h2, wd_zero', zero_add]`. Establish `wdQc : ∀ (c : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ), wd (wOn Qᶜ w) c (uni b L) = wd (fun i => w (inlE i)) (fun b' => c (uni b' L)) b`. Introduce `c b L`. Rewrite using `[(hU β κ E (wOn Qᶜ w) c b L).1]`.

Establish `h1 : (fun i => wOn Qᶜ w (inlE i)) = fun i => w (inlE i)`. Use function extensionality and compare the values at `i`. Simplify using `[wOn, hinl]`. Establish `h2 : (fun l => wOn Qᶜ w (inrE l)) = fun _ => (0 : Module.End ℂ E)`. Use function extensionality and compare the values at `l`.

Simplify using `[wOn, hinr]`. Rewrite using `[h1, h2, wd_zero', smul_zero, add_zero]`. Establish `hc0 : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d → (L.card : ℤ) ≠ d → c0 b L = 0` using `fun b L hb hL => val_zero (Submodule.mem_inf.1 (hZ b hb)).1 L hL`. Establish `hc0m : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d → (L.card : ℤ) = d → c0 b L ∈ A (uni b L)` using `fun b L hb hL => val_mem (Submodule.mem_inf.1 (hZ b hb)).1 L hL`. Set `c' : Finset (β ⊕ₗ κ) → E` to `fun s => if ((lft s).card : ℤ) = n - d then c0 (lft s) (rgt s) else 0`.

Establish `hcu : ∀ (b : Finset β) (L : Finset κ), c' (uni b L) = if (b.card : ℤ) = n - d then c0 b L else 0`. Introduce `b L`. Simplify using `only [c', hl, hr]`. Establish `hc'C : c' ∈ (acx A w).C n`. Rewrite using `[mem_acxC]`.

Introduce `s`. Establish `hcs` using `hsc s`. Distinguish the cases in `hsn : (s.card : ℤ) = n`. Rewrite using `[if_pos hsn]`. Simplify using `only [c']`.

Use `split_ifs with hb`. Use `hc0m (lft s) (rgt s) hb (by omega)` as an intermediate fact. Rewrite `this` using `[hs]`. Then use the resulting hypothesis. Conclude with `zero_mem _`. Rewrite using `[if_neg hsn]`.

Simplify using `only [c']`. Use `split_ifs with hb`. Rewrite using `[hc0 _ _ hb (by omega)]; exact zero_mem _`. Conclude with `zero_mem _`. Establish `hc'L : Lev Q (· = d) c'`.

Introduce `s hs'`. Rewrite `hs'` using `[hcap]`. Simplify using `only [c']`. Use `split_ifs with hb`. Conclude with `hc0 _ _ hb hs'`.

Both sides reduce to the same expression. Establish `hQ0 : wd (wOn Q w) c' = 0`. Use function extensionality and compare the values at `s`. Take `⟨b, L, rfl⟩ : ∃ b L, s = uni b L` from `⟨_, _, (hs s).symm⟩`. Rewrite using `[wdQ]`.

Simplify using `only [hcu]`. Distinguish the cases in `hb : (b.card : ℤ) = n - d`. Simplify using `only [if_pos hb]`. Establish `h0 : wd (fun l => w (inrE l)) (c0 b) = 0` using `(Submodule.mem_inf.1 (hZ b hb)).2`. Establish `h1 : (fun L' => c0 b L') = c0 b` using `rfl`.

Rewrite using `[h1, h0]`. Simplify using the standard rewrite rules. Simplify using `only [if_neg hb]`. Establish `h1 : (fun _ : Finset κ => (0 : E)) = 0` using `rfl`. Rewrite using `[h1, map_zero]`.

Simplify using the standard rewrite rules. Establish `hy : ∀ b : Finset β, ∃ y : Finset κ → E, (b.card : ℤ) = n - d + 1 → y ∈ (colA A w b).C (d - 1) ∧ wd (fun l => w (inrE l)) y = fun L => wd (fun i => w (inlE i)) (fun b' => c0 b' L) b`. Introduce `b`. Distinguish the cases in `hb : (b.card : ℤ) = n - d + 1`. Take `⟨y, hy1, hy2⟩` from `hB b hb`.

Conclude with `⟨y, fun _ => ⟨hy1, hy2⟩⟩`. Conclude with `⟨0, fun h => absurd h hb⟩`. Use `choose yb hyb using hy`. Set `y : Finset (β ⊕ₗ κ) → E` to `fun s => if ((lft s).card : ℤ) = n - d + 1 then ((-1 : ℤ) ^ (lft s).card) • yb (lft s) (rgt s) else 0`. Establish `hyu : ∀ (b : Finset β) (L : Finset κ), y (uni b L) = if (b.card : ℤ) = n - d + 1 then ((-1 : ℤ) ^ b.card) • yb b L else 0`.

Introduce `b L`. Simplify using `only [y, hl, hr]`. Establish `hyz : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d + 1 → (L.card : ℤ) ≠ d - 1 → yb b L = 0` using `fun b L hb hL => val_zero (hyb b hb).1 L hL`. Establish `hym : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d + 1 → (L.card : ℤ) = d - 1 → yb b L ∈ A (uni b L)` using `fun b L hb hL => val_mem (hyb b hb).1 L hL`. Establish `hyC : y ∈ (acx A w).C n`.

Rewrite using `[mem_acxC]`. Introduce `s`. Establish `hcs` using `hsc s`. Distinguish the cases in `hsn : (s.card : ℤ) = n`. Rewrite using `[if_pos hsn]`.

Simplify using `only [y]`. Use `split_ifs with hb`. Use `hym (lft s) (rgt s) hb (by omega)` as an intermediate fact. Rewrite `this` using `[hs]`. Conclude with `(A s).smul_of_tower_mem _ this`.

Conclude with `zero_mem _`. Rewrite using `[if_neg hsn]`. Simplify using `only [y]`. Use `split_ifs with hb`. Rewrite using `[hyz _ _ hb (by omega), smul_zero]; exact zero_mem _`.

Conclude with `zero_mem _`. Establish `hyL : Lev Q (· = d - 1) y`. Introduce `s hs'`. Rewrite `hs'` using `[hcap]`. Simplify using `only [y]`.

Use `split_ifs with hb`. Rewrite using `[hyz _ _ hb hs', smul_zero]`. Both sides reduce to the same expression. Establish `hyE : wd (wOn Q w) y = wd (wOn Qᶜ w) c'`. Use function extensionality and compare the values at `s`.

Take `⟨b, L, rfl⟩ : ∃ b L, s = uni b L` from `⟨_, _, (hs s).symm⟩`. Rewrite using `[wdQ, wdQc]`. Distinguish the cases in `hb : (b.card : ℤ) = n - d + 1`. Establish `h1 : (fun L' => y (uni b L')) = ((-1 : ℤ) ^ b.card) • yb b`. Use function extensionality and compare the values at `L'`.

Rewrite using `[hyu, if_pos hb]`. Both sides reduce to the same expression. Rewrite using `[h1, map_zsmul, Pi.smul_apply, smul_smul, (hyb b hb).2, ← mul_pow]`. Simplify using `only [neg_mul, one_mul, neg_neg, one_pow, one_smul]`. Use `wd_congr' _ _ _ _ fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[hcu, if_pos]`. Rewrite using `[Finset.card_erase_of_mem hi]`. Establish `: 0 < b.card` using `Finset.card_pos.2 ⟨i, hi⟩`. Use linear arithmetic over natural numbers and integers. Establish `h1 : (fun L' => y (uni b L')) = 0`.

Use function extensionality and compare the values at `L'`. Rewrite using `[hyu, if_neg hb]`. Both sides reduce to the same expression. Rewrite using `[h1, map_zero, Pi.zero_apply, smul_zero]`. Use `symm`.

Establish `h2 : wd (fun i => w (inlE i)) (fun b' => c' (uni b' L)) b = wd (fun i => w (inlE i)) 0 b`. Use `wd_congr' _ _ _ _ fun i hi => ?_` and prove the remaining obligations. Rewrite using `[hcu, if_neg, Pi.zero_apply]`. Rewrite using `[Finset.card_erase_of_mem hi]`. Establish `: 0 < b.card` using `Finset.card_pos.2 ⟨i, hi⟩`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h2, map_zero, Pi.zero_apply]`. Take `⟨c, hcZ, hcl⟩` from `hG (β ⊕ₗ κ) E A w Q d n hW hQex c' hc'C hc'L hQ0 ⟨y, hyC, hyL, hyE⟩`. Establish `hcC : c ∈ (acx A w).C n` using `(Submodule.mem_inf.1 hcZ).1`. Establish `hlev : ∀ (b : Finset β) (L : Finset κ), d ≤ (L.card : ℤ) → c (uni b L) = c' (uni b L)`.

Introduce `b L hL`. Use `hcl (uni b L) (by` as an intermediate fact. Introduce `h`. Use `beta_reduce at h`. Establish `h' : (((uni b L ∩ Q).card : ℕ) : ℤ) < d` using `by convert h`.

Rewrite `h'` using `[hcap, hr]`. Use the proof step `omega)`. Conclude with `sub_eq_zero.1 this`. Use `⟨c, hcZ, ?_, ?_⟩` and prove the remaining obligations. Introduce `b hb`.

Use function extensionality and compare the values at `L`. Use `show c (uni b L) = c0 b L`. Distinguish the cases in `hL : d ≤ (L.card : ℤ)`. Rewrite using `[hlev b L hL, hcu, if_pos hb]`. Rewrite using `[val_zero hcC _ (by rw [hcd]; push_cast; omega), hc0 b L hb (by omega)]`.

Introduce `b L hL`. Rewrite using `[hlev b L hL.le, hcu]`. Use `split_ifs with hb`. Conclude with `hc0 b L hb (by omega)`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.productCup_of_system.localTwo_of_gl2 :
    FiltrationCocycleLiftCriterion → ColQEx → WdUni → L2 := by
  intro hG hC hU β κ E _ _ _ _ _ _ A w d n hW hK c0 hZ hB
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := ⟨_, rfl⟩
  have hQex : QEx A w Q d := by rw [hQ]; exact hC β κ E A w d hK
  have hcap : ∀ s : Finset (β ⊕ₗ κ), (s ∩ Q).card = (rgt s).card := fun s => by rw [hQ]; exact inter_card s
  have hinl : ∀ i : β, (inlE i : β ⊕ₗ κ) ∉ Q := fun i => by simp [hQ, inlE, inrE]
  have hinr : ∀ l : κ, (inrE l : β ⊕ₗ κ) ∈ Q := fun l => by simp [hQ]
  have hl : ∀ (b : Finset β) (L : Finset κ), lft (uni b L) = b := fun b L => (hU β κ E w 0 b L).2.1
  have hr : ∀ (b : Finset β) (L : Finset κ), rgt (uni b L) = L := fun b L => (hU β κ E w 0 b L).2.2.1
  have hcd : ∀ (b : Finset β) (L : Finset κ), (uni b L).card = b.card + L.card :=
    fun b L => (hU β κ E w 0 b L).2.2.2.1
  have hs : ∀ s : Finset (β ⊕ₗ κ), uni (lft s) (rgt s) = s := (hU β κ E w 0 ∅ ∅).2.2.2.2
  have hsc : ∀ s : Finset (β ⊕ₗ κ), s.card = (lft s).card + (rgt s).card := fun s => by
    conv_lhs => rw [← hs s]
    exact hcd _ _
  have wdQ : ∀ (c : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ), wd (wOn Q w) c (uni b L) =
      ((-1 : ℤ) ^ b.card) • wd (fun l => w (inrE l)) (fun L' => c (uni b L')) L := by
    intro c b L
    rw [(hU β κ E (wOn Q w) c b L).1]
    have h1 : (fun i => wOn Q w (inlE i)) = fun _ => (0 : Module.End ℂ E) := by
      funext i; simp [wOn, hinl]
    have h2 : (fun l => wOn Q w (inrE l)) = fun l => w (inrE l) := by
      funext l; simp [wOn, hinr]
    rw [h1, h2, wd_zero', zero_add]
  have wdQc : ∀ (c : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ), wd (wOn Qᶜ w) c (uni b L) =
      wd (fun i => w (inlE i)) (fun b' => c (uni b' L)) b := by
    intro c b L
    rw [(hU β κ E (wOn Qᶜ w) c b L).1]
    have h1 : (fun i => wOn Qᶜ w (inlE i)) = fun i => w (inlE i) := by
      funext i; simp [wOn, hinl]
    have h2 : (fun l => wOn Qᶜ w (inrE l)) = fun _ => (0 : Module.End ℂ E) := by
      funext l; simp [wOn, hinr]
    rw [h1, h2, wd_zero', smul_zero, add_zero]
  have hc0 : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d → (L.card : ℤ) ≠ d → c0 b L = 0 :=
    fun b L hb hL => val_zero (Submodule.mem_inf.1 (hZ b hb)).1 L hL
  have hc0m : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d → (L.card : ℤ) = d → c0 b L ∈ A (uni b L) :=
    fun b L hb hL => val_mem (Submodule.mem_inf.1 (hZ b hb)).1 L hL
  let c' : Finset (β ⊕ₗ κ) → E := fun s => if ((lft s).card : ℤ) = n - d then c0 (lft s) (rgt s) else 0
  have hcu : ∀ (b : Finset β) (L : Finset κ), c' (uni b L) = if (b.card : ℤ) = n - d then c0 b L else 0 := by
    intro b L; simp only [c', hl, hr]
  have hc'C : c' ∈ (acx A w).C n := by
    rw [mem_acxC]
    intro s
    have hcs := hsc s
    by_cases hsn : (s.card : ℤ) = n
    · rw [if_pos hsn]
      simp only [c']
      split_ifs with hb
      · have := hc0m (lft s) (rgt s) hb (by omega)
        rwa [hs] at this
      · exact zero_mem _
    · rw [if_neg hsn]
      simp only [c']
      split_ifs with hb
      · rw [hc0 _ _ hb (by omega)]; exact zero_mem _
      · exact zero_mem _
  have hc'L : Lev Q (· = d) c' := by
    intro s hs'
    rw [hcap] at hs'
    simp only [c']
    split_ifs with hb
    · exact hc0 _ _ hb hs'
    · rfl
  have hQ0 : wd (wOn Q w) c' = 0 := by
    funext s
    obtain ⟨b, L, rfl⟩ : ∃ b L, s = uni b L := ⟨_, _, (hs s).symm⟩
    rw [wdQ]
    simp only [hcu]
    by_cases hb : (b.card : ℤ) = n - d
    · simp only [if_pos hb]
      have h0 : wd (fun l => w (inrE l)) (c0 b) = 0 := (Submodule.mem_inf.1 (hZ b hb)).2
      have h1 : (fun L' => c0 b L') = c0 b := rfl
      rw [h1, h0]; simp
    · simp only [if_neg hb]
      have h1 : (fun _ : Finset κ => (0 : E)) = 0 := rfl
      rw [h1, map_zero]; simp
  have hy : ∀ b : Finset β, ∃ y : Finset κ → E, (b.card : ℤ) = n - d + 1 →
      y ∈ (colA A w b).C (d - 1) ∧
        wd (fun l => w (inrE l)) y = fun L => wd (fun i => w (inlE i)) (fun b' => c0 b' L) b := by
    intro b
    by_cases hb : (b.card : ℤ) = n - d + 1
    · obtain ⟨y, hy1, hy2⟩ := hB b hb
      exact ⟨y, fun _ => ⟨hy1, hy2⟩⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose yb hyb using hy
  let y : Finset (β ⊕ₗ κ) → E := fun s =>
    if ((lft s).card : ℤ) = n - d + 1 then ((-1 : ℤ) ^ (lft s).card) • yb (lft s) (rgt s) else 0
  have hyu : ∀ (b : Finset β) (L : Finset κ), y (uni b L) =
      if (b.card : ℤ) = n - d + 1 then ((-1 : ℤ) ^ b.card) • yb b L else 0 := by
    intro b L; simp only [y, hl, hr]
  have hyz : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d + 1 → (L.card : ℤ) ≠ d - 1 → yb b L = 0 :=
    fun b L hb hL => val_zero (hyb b hb).1 L hL
  have hym : ∀ (b : Finset β) (L : Finset κ), (b.card : ℤ) = n - d + 1 → (L.card : ℤ) = d - 1 →
      yb b L ∈ A (uni b L) := fun b L hb hL => val_mem (hyb b hb).1 L hL
  have hyC : y ∈ (acx A w).C n := by
    rw [mem_acxC]
    intro s
    have hcs := hsc s
    by_cases hsn : (s.card : ℤ) = n
    · rw [if_pos hsn]
      simp only [y]
      split_ifs with hb
      · have := hym (lft s) (rgt s) hb (by omega)
        rw [hs] at this
        exact (A s).smul_of_tower_mem _ this
      · exact zero_mem _
    · rw [if_neg hsn]
      simp only [y]
      split_ifs with hb
      · rw [hyz _ _ hb (by omega), smul_zero]; exact zero_mem _
      · exact zero_mem _
  have hyL : Lev Q (· = d - 1) y := by
    intro s hs'
    rw [hcap] at hs'
    simp only [y]
    split_ifs with hb
    · rw [hyz _ _ hb hs', smul_zero]
    · rfl
  have hyE : wd (wOn Q w) y = wd (wOn Qᶜ w) c' := by
    funext s
    obtain ⟨b, L, rfl⟩ : ∃ b L, s = uni b L := ⟨_, _, (hs s).symm⟩
    rw [wdQ, wdQc]
    by_cases hb : (b.card : ℤ) = n - d + 1
    · have h1 : (fun L' => y (uni b L')) = ((-1 : ℤ) ^ b.card) • yb b := by
        funext L'; rw [hyu, if_pos hb]; rfl
      rw [h1, map_zsmul, Pi.smul_apply, smul_smul, (hyb b hb).2, ← mul_pow]
      simp only [neg_mul, one_mul, neg_neg, one_pow, one_smul]
      refine wd_congr' _ _ _ _ fun i hi => ?_
      rw [hcu, if_pos]
      rw [Finset.card_erase_of_mem hi]
      have : 0 < b.card := Finset.card_pos.2 ⟨i, hi⟩
      omega
    · have h1 : (fun L' => y (uni b L')) = 0 := by
        funext L'; rw [hyu, if_neg hb]; rfl
      rw [h1, map_zero, Pi.zero_apply, smul_zero]
      symm
      have h2 : wd (fun i => w (inlE i)) (fun b' => c' (uni b' L)) b = wd (fun i => w (inlE i)) 0 b := by
        refine wd_congr' _ _ _ _ fun i hi => ?_
        rw [hcu, if_neg, Pi.zero_apply]
        rw [Finset.card_erase_of_mem hi]
        have : 0 < b.card := Finset.card_pos.2 ⟨i, hi⟩
        omega
      rw [h2, map_zero, Pi.zero_apply]
  obtain ⟨c, hcZ, hcl⟩ := hG (β ⊕ₗ κ) E A w Q d n hW hQex c' hc'C hc'L hQ0 ⟨y, hyC, hyL, hyE⟩
  have hcC : c ∈ (acx A w).C n := (Submodule.mem_inf.1 hcZ).1
  have hlev : ∀ (b : Finset β) (L : Finset κ), d ≤ (L.card : ℤ) → c (uni b L) = c' (uni b L) := by
    intro b L hL
    have := hcl (uni b L) (by
      intro h
      beta_reduce at h
      have h' : (((uni b L ∩ Q).card : ℕ) : ℤ) < d := by convert h
      rw [hcap, hr] at h'
      omega)
    exact sub_eq_zero.1 this
  refine ⟨c, hcZ, ?_, ?_⟩
  · intro b hb
    funext L
    show c (uni b L) = c0 b L
    by_cases hL : d ≤ (L.card : ℤ)
    · rw [hlev b L hL, hcu, if_pos hb]
    · rw [val_zero hcC _ (by rw [hcd]; push_cast; omega), hc0 b L hb (by omega)]
  · intro b L hL
    rw [hlev b L hL.le, hcu]
    split_ifs with hb
    · exact hc0 b L hb (by omega)
    · rfl

import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Simplify using `[wd, LinearMap.sum_apply]`.
-/
private lemma wd_apply' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Rewrite using `[wd_apply']`. Simplify using `[deltaL, GlobalTheory.DI.delta]`.
-/
private lemma wd_one_eq {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (c : Finset ι → E) : wd (fun _ => (1 : Module.End ℂ E)) c = deltaL ℂ ι E c := by
  funext t
  rw [wd_apply']
  simp [deltaL, GlobalTheory.DI.delta]

/- English proof (translation)
Rewrite using `[wd_apply']`. Use `split_ifs with h`. Take `⟨l, rfl⟩` from `Finset.card_eq_one.1 h`. Simplify using `[GlobalTheory.cubeSign, Finset.filter_singleton]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations.

Establish `: L.erase i ≠ ∅`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Use `Finset.card_erase_of_mem hi` as an intermediate fact. Rewrite `this` using `[h0, Finset.card_empty]`.

Use `Finset.card_pos.2 ⟨i, hi⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `[this]`.
-/
private lemma wd_tail {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (v : E) (L : Finset ι)
    (hL : L.Nonempty) :
    wd (fun _ => (1 : Module.End ℂ E)) (fun L' : Finset ι => if L' = ∅ then v else 0) L =
      if L.card = 1 then v else 0 := by
  rw [wd_apply']
  split_ifs with h
  · obtain ⟨l, rfl⟩ := Finset.card_eq_one.1 h
    simp [GlobalTheory.cubeSign, Finset.filter_singleton]
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : L.erase i ≠ ∅ := by
      intro h0
      apply h
      have := Finset.card_erase_of_mem hi
      rw [h0, Finset.card_empty] at this
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [this]

/- English proof (translation)
Introduce `hU ι E _ _ _ _ G d x hx hB`. Take `⟨y, hyC, hy⟩` from `hB`. Establish `hxC` using `hx.1`. Establish `hxd : deltaL ℂ ι E x = 0` using `hx.2`. Establish `hy' : wd (fun _ => (1 : Module.End ℂ E)) y = edge1 x` using `hy`.

Establish `hyC' : ∀ s, y s ∈ (if (s.card : ℤ) = ((d : ℤ) + 2 - 1) then mixF (fun I J => G (uni I J)) s else ⊥)` using `fun s => hyC s (Set.mem_univ s)`. Establish `hxC' : ∀ I, x I ∈ (if I.Nonempty ∧ (I.card : ℤ) = (d : ℤ) + 1 then G (uni I ∅) else ⊥)` using `fun I => hxC I (Set.mem_univ I)`. Establish `hUn` using `hU ι ι E (fun _ => 1)`. Establish `hl : ∀ (b L : Finset ι), lft (uni b L) = b` using `fun b L => (hUn y b L).2.1`. Establish `hr : ∀ (b L : Finset ι), rgt (uni b L) = L` using `fun b L => (hUn y b L).2.2.1`.

Establish `hc : ∀ (b L : Finset ι), (uni b L).card = b.card + L.card` using `fun b L => (hUn y b L).2.2.2.1`. Establish `hs : ∀ s : Finset (ι ⊕ₗ ι), uni (lft s) (rgt s) = s` using `(hUn y ∅ ∅).2.2.2.2`. Establish `hx0 : ∀ I : Finset ι, (I.card : ℤ) ≠ (d : ℤ) + 1 → x I = 0`. Introduce `I hI`. Use `hxC' I` as an intermediate fact.

Rewrite `this` using `[if_neg (fun h => hI h.2)]`. Simplify using `using this`. Establish `hy0 : ∀ s, ¬ ((lft s).Nonempty ∧ (rgt s).Nonempty) → y s = 0`. Introduce `s h`. Use `hyC' s` as an intermediate fact.

Use `split_ifs at this`. Simplify `this` using `[mixF, h]`. Simplify using `using this`. Set `e : Finset (ι ⊕ₗ ι) → E` to `fun s => if rgt s = ∅ then x (lft s) else 0`. Establish `he : ∀ b L, e (uni b L) = if L = ∅ then x b else 0`.

Introduce `b L`. Simplify using `only [e, hl, hr]`. Establish `hwe : ∀ s, wd (fun _ => (1 : Module.End ℂ E)) e s = (-((-1 : ℤ) ^ d)) • edge1 x s`. Introduce `s`. Rewrite using `[← hs s]`.

Generalize the expression as in `lft s = b`. Generalize the expression as in `rgt s = L`. Establish `h1` using `(hU ι ι E (fun _ => 1) e b L).1`. Simplify using `only [he] at h1`. Rewrite using `[h1]`.

Distinguish the cases in `hL : L = ∅`. Substitute `hL` using the available equality. Establish `: edge1 (κ` using `ι) x (uni b ∅) = 0 := by simp [edge1, hr]`. Rewrite using `[this, smul_zero]`. Establish `hd : wd (fun _ => (1 : Module.End ℂ E)) x = 0` using `by rw [wd_one_eq, hxd]`.

Establish `e1 : (fun b' : Finset ι => if (∅ : Finset ι) = ∅ then x b' else 0) = x`. Use function extensionality and compare the values at `b'`. Simplify using the standard rewrite rules. Rewrite using `[e1, hd]`. Simplify using `[wd_apply']`.

Establish `hLn : L.Nonempty` using `Finset.nonempty_iff_ne_empty.2 hL`. Simplify using `only [hL, if_false]`. Establish `h0 : wd (fun _ => (1 : Module.End ℂ E)) (fun _ : Finset ι => (0 : E)) b = 0`. Simplify using `[wd_apply']`. Establish `h2` using `wd_tail (x b) L hLn`.

Rewrite using `[h0, h2, zero_add]`. Simplify using `only [edge1, hl, hr]`. Use `split_ifs with h1c`. Distinguish the cases in `hb : (b.card : ℤ) = (d : ℤ) + 1`. Establish `hb' : b.card = d + 1` using `by exact_mod_cast hb`.

Rewrite using `[hb', pow_succ]`. Simplify using the standard rewrite rules. Simplify using `[hx0 b hb]`. Simplify using the standard rewrite rules. Use `⟨e + ((-1 : ℤ) ^ d) • y, ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce `s _`. Express the relevant statement in the definitionally equal form `(e + ((-1 : ℤ) ^ d) • y) s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (d : ℤ) + 1 then G s else ⊥)`. Distinguish the cases in `hr0 : rgt s = ∅`. Establish `hys : y s = 0` using `hy0 s (fun h => h.2.ne_empty hr0)`. Establish `hs' : uni (lft s) ∅ = s`.

Use `hs s` as an intermediate fact. Rewrite `this` using `[hr0]`. Then use the resulting hypothesis. Establish `hcard : s.card = (lft s).card`. Use `hc (lft s) ∅` as an intermediate fact. Rewrite `this` using `[hs']`.

Simplify using `using this`. Establish `hval : (e + ((-1 : ℤ) ^ d) • y) s = x (lft s)`. Simplify using `[e, hr0, hys]`. Rewrite using `[hval]`. Use `split_ifs with h`.

Use `hxC' (lft s)` as an intermediate fact. Establish `hlc : ((lft s).card : ℤ) = (d : ℤ) + 1` using `by rw [← hcard]; exact h.2`. Establish `hne : (lft s).Nonempty`. Apply `Finset.card_pos.1` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.

Rewrite `this` using `[if_pos ⟨hne, hlc⟩, hs']`. Conclude with `this`. Establish `: x (lft s) = 0`. Apply `hx0` to reduce the goal to its premises. Introduce `hlc`.

Apply `h` to reduce the goal to its premises. Establish `hsc : (s.card : ℤ) = (d : ℤ) + 1` using `by rw [hcard]; exact hlc`. Use `⟨Finset.card_pos.1 ?_, hsc⟩` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers. Simplify using `[this]`.

Establish `hval : (e + ((-1 : ℤ) ^ d) • y) s = ((-1 : ℤ) ^ d) • y s`. Simplify using `[e, hr0]`. Rewrite using `[hval]`. Distinguish the cases in `hcs : (s.card : ℤ) = (d : ℤ) + 2 - 1`. Distinguish the cases in `hlr : (lft s).Nonempty ∧ (rgt s).Nonempty`.

Use `hyC' s` as an intermediate fact. Rewrite `this` using `[if_pos hcs]`. Simplify using `only [mixF, if_pos hlr, hs s] at this`. Establish `hsc : (s.card : ℤ) = (d : ℤ) + 1` using `by omega`. Rewrite using `[if_pos ⟨Finset.card_pos.1 (by omega), hsc⟩]`.

Conclude with `zsmul_mem this _`. Simplify using `[hy0 s hlr]`. Use `hyC' s` as an intermediate fact. Rewrite `this` using `[if_neg hcs]`. Establish `h0 : y s = 0` using `by simpa using this`.

Simplify using `[h0]`. Express the relevant statement in the definitionally equal form `deltaL ℂ (ι ⊕ₗ ι) E (e + ((-1 : ℤ) ^ d) • y) = 0`. Rewrite using `[← wd_one_eq, map_add, map_zsmul, hy']`. Use function extensionality and compare the values at `s`. Simplify using `[hwe]`.

Introduce `J`. Establish `h1 : y (uni ∅ J) = 0` using `hy0 _ (fun h => by`. Use `h.1` as an intermediate fact. Rewrite `this` using `[hl]`. Simplify using `at this)`.

Establish `h2 : x ∅ = 0` using `hx0 ∅ (by simp; omega)`. Simplify using `[he, h1, h2]`. Introduce `I`. Establish `h1 : y (uni I ∅) = 0` using `hy0 _ (fun h => by`. Use `h.2` as an intermediate fact.

Rewrite `this` using `[hr]`. Simplify using `at this)`. Simplify using `[he, h1]`.
-/
theorem UpperTheory.Gal.productCup_of_system.edgeInj_of :
    WdUni → EdgeInj := by
  intro hU ι E _ _ _ _ G d x hx hB
  obtain ⟨y, hyC, hy⟩ := hB
  have hxC := hx.1
  have hxd : deltaL ℂ ι E x = 0 := hx.2
  have hy' : wd (fun _ => (1 : Module.End ℂ E)) y = edge1 x := hy
  have hyC' : ∀ s, y s ∈ (if (s.card : ℤ) = ((d : ℤ) + 2 - 1) then
      mixF (fun I J => G (uni I J)) s else ⊥) := fun s => hyC s (Set.mem_univ s)
  have hxC' : ∀ I, x I ∈ (if I.Nonempty ∧ (I.card : ℤ) = (d : ℤ) + 1 then G (uni I ∅) else ⊥) :=
    fun I => hxC I (Set.mem_univ I)
  have hUn := hU ι ι E (fun _ => 1)
  have hl : ∀ (b L : Finset ι), lft (uni b L) = b := fun b L => (hUn y b L).2.1
  have hr : ∀ (b L : Finset ι), rgt (uni b L) = L := fun b L => (hUn y b L).2.2.1
  have hc : ∀ (b L : Finset ι), (uni b L).card = b.card + L.card := fun b L => (hUn y b L).2.2.2.1
  have hs : ∀ s : Finset (ι ⊕ₗ ι), uni (lft s) (rgt s) = s := (hUn y ∅ ∅).2.2.2.2
  have hx0 : ∀ I : Finset ι, (I.card : ℤ) ≠ (d : ℤ) + 1 → x I = 0 := by
    intro I hI
    have := hxC' I
    rw [if_neg (fun h => hI h.2)] at this
    simpa using this
  have hy0 : ∀ s, ¬ ((lft s).Nonempty ∧ (rgt s).Nonempty) → y s = 0 := by
    intro s h
    have := hyC' s
    split_ifs at this
    · simpa [mixF, h] using this
    · simpa using this
  let e : Finset (ι ⊕ₗ ι) → E := fun s => if rgt s = ∅ then x (lft s) else 0
  have he : ∀ b L, e (uni b L) = if L = ∅ then x b else 0 := by
    intro b L
    simp only [e, hl, hr]
  have hwe : ∀ s, wd (fun _ => (1 : Module.End ℂ E)) e s = (-((-1 : ℤ) ^ d)) • edge1 x s := by
    intro s
    rw [← hs s]
    generalize lft s = b
    generalize rgt s = L
    have h1 := (hU ι ι E (fun _ => 1) e b L).1
    simp only [he] at h1
    rw [h1]
    by_cases hL : L = ∅
    · subst hL
      have : edge1 (κ := ι) x (uni b ∅) = 0 := by simp [edge1, hr]
      rw [this, smul_zero]
      have hd : wd (fun _ => (1 : Module.End ℂ E)) x = 0 := by rw [wd_one_eq, hxd]
      have e1 : (fun b' : Finset ι => if (∅ : Finset ι) = ∅ then x b' else 0) = x := by
        funext b'
        simp
      rw [e1, hd]
      simp [wd_apply']
    · have hLn : L.Nonempty := Finset.nonempty_iff_ne_empty.2 hL
      simp only [hL, if_false]
      have h0 : wd (fun _ => (1 : Module.End ℂ E)) (fun _ : Finset ι => (0 : E)) b = 0 := by
        simp [wd_apply']
      have h2 := wd_tail (x b) L hLn
      rw [h0, h2, zero_add]
      simp only [edge1, hl, hr]
      split_ifs with h1c
      · by_cases hb : (b.card : ℤ) = (d : ℤ) + 1
        · have hb' : b.card = d + 1 := by exact_mod_cast hb
          rw [hb', pow_succ]
          simp
        · simp [hx0 b hb]
      · simp
  refine ⟨e + ((-1 : ℤ) ^ d) • y, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro s _
    change (e + ((-1 : ℤ) ^ d) • y) s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (d : ℤ) + 1 then G s else ⊥)
    by_cases hr0 : rgt s = ∅
    · have hys : y s = 0 := hy0 s (fun h => h.2.ne_empty hr0)
      have hs' : uni (lft s) ∅ = s := by
        have := hs s
        rwa [hr0] at this
      have hcard : s.card = (lft s).card := by
        have := hc (lft s) ∅
        rw [hs'] at this
        simpa using this
      have hval : (e + ((-1 : ℤ) ^ d) • y) s = x (lft s) := by
        simp [e, hr0, hys]
      rw [hval]
      split_ifs with h
      · have := hxC' (lft s)
        have hlc : ((lft s).card : ℤ) = (d : ℤ) + 1 := by rw [← hcard]; exact h.2
        have hne : (lft s).Nonempty := by
          apply Finset.card_pos.1
          omega
        rw [if_pos ⟨hne, hlc⟩, hs'] at this
        exact this
      · have : x (lft s) = 0 := by
          apply hx0
          intro hlc
          apply h
          have hsc : (s.card : ℤ) = (d : ℤ) + 1 := by rw [hcard]; exact hlc
          refine ⟨Finset.card_pos.1 ?_, hsc⟩
          omega
        simp [this]
    · have hval : (e + ((-1 : ℤ) ^ d) • y) s = ((-1 : ℤ) ^ d) • y s := by
        simp [e, hr0]
      rw [hval]
      by_cases hcs : (s.card : ℤ) = (d : ℤ) + 2 - 1
      · by_cases hlr : (lft s).Nonempty ∧ (rgt s).Nonempty
        · have := hyC' s
          rw [if_pos hcs] at this
          simp only [mixF, if_pos hlr, hs s] at this
          have hsc : (s.card : ℤ) = (d : ℤ) + 1 := by omega
          rw [if_pos ⟨Finset.card_pos.1 (by omega), hsc⟩]
          exact zsmul_mem this _
        · simp [hy0 s hlr]
      · have := hyC' s
        rw [if_neg hcs] at this
        have h0 : y s = 0 := by simpa using this
        simp [h0]
  · change deltaL ℂ (ι ⊕ₗ ι) E (e + ((-1 : ℤ) ^ d) • y) = 0
    rw [← wd_one_eq, map_add, map_zsmul, hy']
    funext s
    simp [hwe]
  · intro J
    have h1 : y (uni ∅ J) = 0 := hy0 _ (fun h => by
      have := h.1
      rw [hl] at this
      simp at this)
    have h2 : x ∅ = 0 := hx0 ∅ (by simp; omega)
    simp [he, h1, h2]
  · intro I
    have h1 : y (uni I ∅) = 0 := hy0 _ (fun h => by
      have := h.2
      rw [hr] at this
      simp at this)
    simp [he, h1]

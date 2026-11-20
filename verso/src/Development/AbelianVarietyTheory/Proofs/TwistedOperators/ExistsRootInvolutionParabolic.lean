import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical

noncomputable section

namespace GlobalTheory.ChamberFlip

open Finset GlobalTheory.Chamber

variable {k : ℕ}

/- English proof (translation)
Introduce `_ _` and use `rfl`.
-/
theorem below_refl (u : SV k) : Below u u := fun _ _ => rfl

/- English proof (translation)
Introduce `i hi` and use `(h' i (h i hi ▸ hi)).trans (h i hi)`.
-/
theorem below_trans {a b c : SV k} (h : Below a b) (h' : Below b c) : Below a c :=
  fun i hi => (h' i (h i hi ▸ hi)).trans (h i hi)

/- English proof (translation)
The claim follows from `funext fun i => by by_cases e : a i = 0 · by_cases e' : b i = 0 · rw [e, e'] · exact h' i e' · exact (h i e).symm`.
-/
theorem below_antisymm {a b : SV k} (h : Below a b) (h' : Below b a) : a = b := funext fun i => by
  by_cases e : a i = 0
  · by_cases e' : b i = 0
    · rw [e, e']
    · exact h' i e'
  · exact (h i e).symm

/- English proof (translation)
Introduce `_ hi` and use `(hi rfl).elim`.
-/
theorem zero_below (a : SV k) : Below 0 a := fun _ hi => (hi rfl).elim

/- English proof (translation)
Use `by_contra! hn`. Conclude with `hne (funext fun i => by`. Distinguish the cases in `e : a i = 0`. Rewrite using `[e, hn i e]`. Conclude with `(h i e).symm)`.
-/
theorem exists_gap {a b : SV k} (h : Below a b) (hne : a ≠ b) : ∃ i, a i = 0 ∧ b i ≠ 0 := by
  by_contra! hn
  exact hne (funext fun i => by
    by_cases e : a i = 0
    · rw [e, hn i e]
    · exact (h i e).symm)

def lowTop (S : Finset (SV k)) : SV k :=
  if h : ∃ a ∈ insert 0 S, ∀ b ∈ insert 0 S, Below b a then h.choose else 0

def upBot (S : Finset (SV k)) : SV k :=
  if h : ∃ a ∈ S, ∀ b ∈ S, Below a b then h.choose else 0

/- English proof (translation)
Establish `h : ∃ a ∈ insert 0 S, ∀ b ∈ insert 0 S, Below b a` using `exists_top (r := Below) (fun a b c h h' => below_trans h h') _ (insert_nonempty _ _) fun x hx y hy => by`. Break down `mem_insert.1 hx with rfl | hx` into its components or cases. Conclude with `.inl (zero_below _)`. Break down `mem_insert.1 hy with rfl | hy` into its components or cases. Conclude with `.inr (zero_below _)`.

Conclude with `hS x hx y hy`. Rewrite using `[lowTop, dif_pos h]`. Conclude with `⟨h.choose_spec.1, fun b hb => h.choose_spec.2 b (mem_insert_of_mem hb)⟩`.
-/
theorem lowTop_spec {S : Finset (SV k)} (hS : ∀ x ∈ S, ∀ y ∈ S, Below x y ∨ Below y x) :
    lowTop S ∈ insert 0 S ∧ ∀ b ∈ S, Below b (lowTop S) := by
  have h : ∃ a ∈ insert 0 S, ∀ b ∈ insert 0 S, Below b a :=
    exists_top (r := Below) (fun a b c h h' => below_trans h h') _ (insert_nonempty _ _) fun x hx y hy => by
      rcases mem_insert.1 hx with rfl | hx
      · exact .inl (zero_below _)
      rcases mem_insert.1 hy with rfl | hy
      · exact .inr (zero_below _)
      exact hS x hx y hy
  rw [lowTop, dif_pos h]
  exact ⟨h.choose_spec.1, fun b hb => h.choose_spec.2 b (mem_insert_of_mem hb)⟩

/- English proof (translation)
Establish `h : ∃ a ∈ S, ∀ b ∈ S, Below a b` using `exists_top (r := fun a b => Below b a) (fun a b c h h' => below_trans h' h) S hn fun x hx y hy => hS y hy x hx`. Rewrite using `[upBot, dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem upBot_spec {S : Finset (SV k)} (hn : S.Nonempty) (hS : ∀ x ∈ S, ∀ y ∈ S, Below x y ∨ Below y x) :
    upBot S ∈ S ∧ ∀ b ∈ S, Below (upBot S) b := by
  have h : ∃ a ∈ S, ∀ b ∈ S, Below a b :=
    exists_top (r := fun a b => Below b a) (fun a b c h h' => below_trans h' h) S hn fun x hx y hy => hS y hy x hx
  rw [upBot, dif_pos h]
  exact h.choose_spec

def lowSet (W : Finset (SV k)) (v : SV k) : Finset (SV k) := W.filter (Below · v)

def highSet (W : Finset (SV k)) (v : SV k) : Finset (SV k) := W.filter (Below v ·)

def wallFlip (W : Finset (SV k)) (v : SV k) : SV k :=
  if (highSet W v).Nonempty then fun i => if v i = 0 then upBot (highSet W v) i else lowTop (lowSet W v) i
  else fun i => if lowTop (lowSet W v) i = 0 then -v i else lowTop (lowSet W v) i

/- English proof (translation)
Use `⟨fun h => ?_, fun x hx y hy => ?_⟩` and prove the remaining obligations. Break down `mem_insert.1 h with e | e` into its components or cases. Conclude with `h0 e.symm`. Conclude with `hW.1 e`. Break down `mem_insert.1 hx with e | hx'` into its components or cases.

Break down `mem_insert.1 hy with e' | hy'` into its components or cases. Conclude with `.inl (e ▸ e' ▸ below_refl _)`. Conclude with `e ▸ (hc y hy').symm`. Break down `mem_insert.1 hy with e' | hy'` into its components or cases. Conclude with `e' ▸ hc x hx'`.

Conclude with `hW.2 x hx' y hy'`.
-/
theorem isPar_insert {W : Finset (SV k)} (hW : IsPar W) {v : SV k} (h0 : v ≠ 0)
    (hc : ∀ w ∈ W, Below w v ∨ Below v w) : IsPar (insert v W) := by
  refine ⟨fun h => ?_, fun x hx y hy => ?_⟩
  · rcases mem_insert.1 h with e | e
    · exact h0 e.symm
    · exact hW.1 e
  rcases mem_insert.1 hx with e | hx'
  · rcases mem_insert.1 hy with e' | hy'
    · exact .inl (e ▸ e' ▸ below_refl _)
    · exact e ▸ (hc y hy').symm
  · rcases mem_insert.1 hy with e' | hy'
    · exact e' ▸ hc x hx'
    · exact hW.2 x hx' y hy'

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem neg_self_sign : ∀ s : SignType, -s = s → s = 0 := by decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem neg_zero_sign : ∀ s : SignType, -s = 0 → s = 0 := by decide

/- English proof (translation)
Introduce `k W hW`. Establish `hS : ∀ S ⊆ W, ∀ x ∈ S, ∀ y ∈ S, Below x y ∨ Below y x` using `fun S hS x hx y hy => hW.2 x (hS hx) y (hS hy)`. Use `⟨wallFlip W, fun u huW hu => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ w ∈ W, Below w u ∨ Below u w` using `fun w hw => hu.2 w (mem_insert_of_mem hw) u (mem_insert_self _ _)`. Establish `hu0 : u ≠ 0` using `fun e => hu.1 (e ▸ mem_insert_self _ _)`.

Take `⟨ha, haA⟩` from `lowTop_spec (hS (lowSet W u) (filter_subset _ _))`. Use `set a := lowTop (lowSet W u) with ha_def`. Establish `hau : Below a u`. Break down `mem_insert.1 ha with e | e` into its components or cases. Rewrite using `[e]`.

Conclude with `zero_below _`. Conclude with `(mem_filter.1 e).2`. Establish `haW : ∀ w ∈ W, Below w u → Below w a` using `fun w hw h => haA w (mem_filter.2 ⟨hw, h⟩)`. Establish `hvA : vec a ∈ aP W`. Break down `mem_insert.1 ha with e | e` into its components or cases.

Rewrite using `[e, show vec (0 : SV k) = 0 by ext i; simp [vec]]; exact zero_mem _`. Conclude with `Submodule.subset_span ⟨_, (mem_filter.1 e).1, rfl⟩`. Establish `hane : a ≠ u` using `fun e => by`. Break down `mem_insert.1 ha with e' | e'` into its components or cases. Conclude with `hu0 (e.symm.trans e')`.

Conclude with `huW (e ▸ (mem_filter.1 e').1)`. Take `⟨j, haj, huj⟩` from `exists_gap hau hane`. Distinguish the cases in `hB : (highSet W u).Nonempty`. Take `⟨hb, hbB⟩` from `upBot_spec hB (hS _ (filter_subset _ _)) set b := upBot (highSet W u) with hb_def`. Establish `hbW : b ∈ W` using `(mem_filter.1 hb).1`.

Establish `hub : Below u b` using `(mem_filter.1 hb).2`. Establish `hbW' : ∀ w ∈ W, Below u w → Below b w` using `fun w hw h => hbB w (mem_filter.2 ⟨hw, h⟩)`. Establish `hvi : ∀ i, wallFlip W u i = if u i = 0 then b i else a i` using `fun i => by rw [wallFlip, if_pos hB]`. Generalize the expression as in `wallFlip W u = v at hvi ⊢`. Establish `hua : ∀ i, u i = 0 → a i = 0` using `fun i e => by`.

Assume the negation of the conclusion as `h`. Conclude with `h ((hau i h).symm.trans e)`. Take `⟨i, hui, hbi⟩` from `exists_gap hub (fun e => huW (e ▸ hbW))`. Establish `hvi1 : v i = b i` using `by rw [hvi, if_pos hui]`. Establish `hvj : v j = a j` using `by rw [hvi, if_neg huj]`.

Establish `hv0 : v ≠ 0` using `fun e => hbi (by rw [← hvi1, e]; rfl)`. Establish `hvu : v ≠ u` using `fun e => hbi (by rw [← hvi1, e, hui])`. Establish `hva : v ≠ a` using `fun e => hbi (by rw [← hvi1, e, hua i hui])`. Establish `hvb' : v ≠ b` using `fun e => huj (by rw [← hub j huj, ← e, hvj, haj])`. Establish `hav : Below a v` using `fun i hi => by rw [hvi, if_neg (by rw [hau i hi]; exact hi)]`.

Establish `hvb : Below v b` using `fun i hi => by`. Distinguish the cases in `e : u i = 0`. Rewrite `hi`, the goal using `[hvi, if_pos e]`. Establish `e2 : v i = a i` using `by rw [hvi, if_neg e]`. Rewrite `hi`, the goal using `[e2]`.

Rewrite using `[hub i e, hau i hi]`. Establish `hcv : ∀ w ∈ W, Below w v ∨ Below v w` using `fun w hw => (hc w hw).imp (fun h => below_trans (haW w hw h) hav) (fun h => below_trans hvb (hbW' w hw h))`. Establish `hvW : v ∉ W` using `fun hv => (hc v hv).elim (fun h => hva (below_antisymm (haW v hv h) hav)) (fun h => hvb' (below_antisymm hvb (hbW' v hv h)))`. Establish `key : ∀ i, (u i : ℝ) + v i = a i + b i` using `fun i => by`. Distinguish the cases in `e : u i = 0`.

Rewrite using `[hvi, if_pos e, e, hua i e]`. Rewrite using `[hvi, if_neg e, hub i e, add_comm]`. Establish `hsum : vec u + vec v = vec a + vec b` using `by ext i; simpa [vec] using key i`. Establish `hL : lowSet W v = lowSet W u` using `filter_congr fun w hw => ⟨fun h => (hc w hw).resolve_right (fun h' => hvW (by rw [← below_antisymm h (below_trans hvb (hbW' w hw h'))]; exact hw)), fun h => below_trans (haW w hw h) hav⟩`. Establish `hH : highSet W v = highSet W u` using `filter_congr fun w hw => ⟨fun h => (hc w hw).resolve_left (fun h' => hvW (by rw [below_antisymm h (below_trans (haW w hw h') hav)]; exact hw)), fun h => below_trans hvb (hbW' w hw h)⟩`.

Use `⟨hvW, hvu, isPar_insert hW hv0 hcv, hsum ▸ add_mem hvA (Submodule.subset_span ⟨b, hbW, rfl⟩), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[wallFlip, hH, hL, if_pos hB]`. Use `show (if v i = 0 then b i else a i) = u i`. Distinguish the cases in `e : u i = 0`.

Establish `ev : v i = b i` using `by rw [hvi, if_pos e]`. Rewrite using `[ev, e]`. Distinguish the cases in `eb : b i = 0`. Rewrite using `[if_pos eb, eb]`. Rewrite using `[if_neg eb, hua i e]`.

Establish `ev : v i = a i` using `by rw [hvi, if_neg e]`. Rewrite using `[ev]`. Distinguish the cases in `ea : a i = 0`. Rewrite using `[if_pos ea, hub i e]`. Rewrite using `[if_neg ea]`.

Conclude with `(hau i ea).symm`. Establish `hall : ∀ w ∈ W, Below w u` using `fun w hw => (hc w hw).resolve_right (fun h => hB ⟨w, mem_filter.2 ⟨hw, h⟩⟩)`. Establish `hvi : ∀ i, wallFlip W u i = if a i = 0 then -u i else a i` using `fun i => by rw [wallFlip, if_neg hB]`. Generalize the expression as in `wallFlip W u = v at hvi ⊢`. Establish `hav : Below a v` using `fun i hi => by rw [hvi, if_neg hi]`.

Establish `hvj : v j = -u j` using `by rw [hvi, if_pos haj]`. Establish `hv0 : v ≠ 0` using `fun e => huj (neg_zero_sign _ (hvj.symm.trans (congrFun e j)))`. Establish `hvu : v ≠ u` using `fun e => huj (neg_self_sign _ (hvj.symm.trans (congrFun e j)))`. Establish `hva : v ≠ a` using `fun e => huj (neg_zero_sign _ (hvj.symm.trans ((congrFun e j).trans haj)))`. Establish `hwv : ∀ w ∈ W, Below w v` using `fun w hw => below_trans (haW w hw (hall w hw)) hav`.

Establish `hvW : v ∉ W` using `fun hv => hva (below_antisymm (haW v hv (hall v hv)) hav)`. Establish `key : ∀ i, (u i : ℝ) + v i = 2 * a i` using `fun i => by`. Distinguish the cases in `ea : a i = 0`. Rewrite using `[hvi, if_pos ea, ea]`. Simplify using the standard rewrite rules.

Rewrite using `[hvi, if_neg ea, ← hau i ea]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : vec u + vec v = (2 : ℝ) • vec a` using `by ext i; simpa [vec] using key i`. Establish `hL : lowSet W v = lowSet W u` using `filter_congr fun w hw => iff_of_true (hwv w hw) (hall w hw)`. Establish `hH : highSet W v = highSet W u` using `filter_congr fun w hw => iff_of_false (fun h => hvW (by rw [below_antisymm h (hwv w hw)]; exact hw)) (fun h => hB ⟨w, mem_filter.2 ⟨hw, h⟩⟩)`.

Establish `hB' : ¬ (highSet W v).Nonempty` using `hH ▸ hB`. Use `⟨hvW, hvu, isPar_insert hW hv0 fun w hw => .inl (hwv w hw), hsum ▸ Submodule.smul_mem _ _ hvA, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[wallFlip, if_neg hB', hL]`. Use `show (if a i = 0 then -v i else a i) = u i`.

Distinguish the cases in `ea : a i = 0`. Rewrite using `[if_pos ea, hvi, if_pos ea, neg_neg]`. Rewrite using `[if_neg ea]`. Conclude with `(hau i ea).symm`.
-/
theorem chain_flip : ∀ {k : ℕ} (W : Finset (SV k)), IsPar W → ∃ f : SV k → SV k, ∀ u, u ∉ W → IsPar (insert u W) →
    f u ∉ W ∧ f u ≠ u ∧ IsPar (insert (f u) W) ∧ vec u + vec (f u) ∈ aP W ∧ f (f u) = u := by
  intro k W hW
  have hS : ∀ S ⊆ W, ∀ x ∈ S, ∀ y ∈ S, Below x y ∨ Below y x := fun S hS x hx y hy => hW.2 x (hS hx) y (hS hy)
  refine ⟨wallFlip W, fun u huW hu => ?_⟩
  have hc : ∀ w ∈ W, Below w u ∨ Below u w := fun w hw => hu.2 w (mem_insert_of_mem hw) u (mem_insert_self _ _)
  have hu0 : u ≠ 0 := fun e => hu.1 (e ▸ mem_insert_self _ _)
  obtain ⟨ha, haA⟩ := lowTop_spec (hS (lowSet W u) (filter_subset _ _))
  set a := lowTop (lowSet W u) with ha_def
  have hau : Below a u := by
    rcases mem_insert.1 ha with e | e
    · rw [e]; exact zero_below _
    · exact (mem_filter.1 e).2
  have haW : ∀ w ∈ W, Below w u → Below w a := fun w hw h => haA w (mem_filter.2 ⟨hw, h⟩)
  have hvA : vec a ∈ aP W := by
    rcases mem_insert.1 ha with e | e
    · rw [e, show vec (0 : SV k) = 0 by ext i; simp [vec]]; exact zero_mem _
    · exact Submodule.subset_span ⟨_, (mem_filter.1 e).1, rfl⟩
  have hane : a ≠ u := fun e => by
    rcases mem_insert.1 ha with e' | e'
    · exact hu0 (e.symm.trans e')
    · exact huW (e ▸ (mem_filter.1 e').1)
  obtain ⟨j, haj, huj⟩ := exists_gap hau hane
  by_cases hB : (highSet W u).Nonempty
  · obtain ⟨hb, hbB⟩ := upBot_spec hB (hS _ (filter_subset _ _))
    set b := upBot (highSet W u) with hb_def
    have hbW : b ∈ W := (mem_filter.1 hb).1
    have hub : Below u b := (mem_filter.1 hb).2
    have hbW' : ∀ w ∈ W, Below u w → Below b w := fun w hw h => hbB w (mem_filter.2 ⟨hw, h⟩)
    have hvi : ∀ i, wallFlip W u i = if u i = 0 then b i else a i := fun i => by rw [wallFlip, if_pos hB]
    generalize wallFlip W u = v at hvi ⊢
    have hua : ∀ i, u i = 0 → a i = 0 := fun i e => by
      by_contra h; exact h ((hau i h).symm.trans e)
    obtain ⟨i, hui, hbi⟩ := exists_gap hub (fun e => huW (e ▸ hbW))
    have hvi1 : v i = b i := by rw [hvi, if_pos hui]
    have hvj : v j = a j := by rw [hvi, if_neg huj]
    have hv0 : v ≠ 0 := fun e => hbi (by rw [← hvi1, e]; rfl)
    have hvu : v ≠ u := fun e => hbi (by rw [← hvi1, e, hui])
    have hva : v ≠ a := fun e => hbi (by rw [← hvi1, e, hua i hui])
    have hvb' : v ≠ b := fun e => huj (by rw [← hub j huj, ← e, hvj, haj])
    have hav : Below a v := fun i hi => by rw [hvi, if_neg (by rw [hau i hi]; exact hi)]
    have hvb : Below v b := fun i hi => by
      by_cases e : u i = 0
      · rw [hvi, if_pos e] at hi ⊢
      · have e2 : v i = a i := by rw [hvi, if_neg e]
        rw [e2] at hi ⊢; rw [hub i e, hau i hi]
    have hcv : ∀ w ∈ W, Below w v ∨ Below v w := fun w hw => (hc w hw).imp
      (fun h => below_trans (haW w hw h) hav) (fun h => below_trans hvb (hbW' w hw h))
    have hvW : v ∉ W := fun hv => (hc v hv).elim (fun h => hva (below_antisymm (haW v hv h) hav))
      (fun h => hvb' (below_antisymm hvb (hbW' v hv h)))
    have key : ∀ i, (u i : ℝ) + v i = a i + b i := fun i => by
      by_cases e : u i = 0
      · rw [hvi, if_pos e, e, hua i e]
      · rw [hvi, if_neg e, hub i e, add_comm]
    have hsum : vec u + vec v = vec a + vec b := by ext i; simpa [vec] using key i
    have hL : lowSet W v = lowSet W u := filter_congr fun w hw => ⟨fun h => (hc w hw).resolve_right
      (fun h' => hvW (by rw [← below_antisymm h (below_trans hvb (hbW' w hw h'))]; exact hw)),
      fun h => below_trans (haW w hw h) hav⟩
    have hH : highSet W v = highSet W u := filter_congr fun w hw => ⟨fun h => (hc w hw).resolve_left
      (fun h' => hvW (by rw [below_antisymm h (below_trans (haW w hw h') hav)]; exact hw)),
      fun h => below_trans hvb (hbW' w hw h)⟩
    refine ⟨hvW, hvu, isPar_insert hW hv0 hcv, hsum ▸ add_mem hvA (Submodule.subset_span ⟨b, hbW, rfl⟩), ?_⟩
    funext i
    rw [wallFlip, hH, hL, if_pos hB]
    show (if v i = 0 then b i else a i) = u i
    by_cases e : u i = 0
    · have ev : v i = b i := by rw [hvi, if_pos e]
      rw [ev, e]
      by_cases eb : b i = 0
      · rw [if_pos eb, eb]
      · rw [if_neg eb, hua i e]
    · have ev : v i = a i := by rw [hvi, if_neg e]
      rw [ev]
      by_cases ea : a i = 0
      · rw [if_pos ea, hub i e]
      · rw [if_neg ea]; exact (hau i ea).symm
  · have hall : ∀ w ∈ W, Below w u := fun w hw =>
      (hc w hw).resolve_right (fun h => hB ⟨w, mem_filter.2 ⟨hw, h⟩⟩)
    have hvi : ∀ i, wallFlip W u i = if a i = 0 then -u i else a i := fun i => by rw [wallFlip, if_neg hB]
    generalize wallFlip W u = v at hvi ⊢
    have hav : Below a v := fun i hi => by rw [hvi, if_neg hi]
    have hvj : v j = -u j := by rw [hvi, if_pos haj]
    have hv0 : v ≠ 0 := fun e => huj (neg_zero_sign _ (hvj.symm.trans (congrFun e j)))
    have hvu : v ≠ u := fun e => huj (neg_self_sign _ (hvj.symm.trans (congrFun e j)))
    have hva : v ≠ a := fun e => huj (neg_zero_sign _ (hvj.symm.trans ((congrFun e j).trans haj)))
    have hwv : ∀ w ∈ W, Below w v := fun w hw => below_trans (haW w hw (hall w hw)) hav
    have hvW : v ∉ W := fun hv => hva (below_antisymm (haW v hv (hall v hv)) hav)
    have key : ∀ i, (u i : ℝ) + v i = 2 * a i := fun i => by
      by_cases ea : a i = 0
      · rw [hvi, if_pos ea, ea]; simp
      · rw [hvi, if_neg ea, ← hau i ea]; ring
    have hsum : vec u + vec v = (2 : ℝ) • vec a := by ext i; simpa [vec] using key i
    have hL : lowSet W v = lowSet W u := filter_congr fun w hw => iff_of_true (hwv w hw) (hall w hw)
    have hH : highSet W v = highSet W u := filter_congr fun w hw => iff_of_false
      (fun h => hvW (by rw [below_antisymm h (hwv w hw)]; exact hw)) (fun h => hB ⟨w, mem_filter.2 ⟨hw, h⟩⟩)
    have hB' : ¬ (highSet W v).Nonempty := hH ▸ hB
    refine ⟨hvW, hvu, isPar_insert hW hv0 fun w hw => .inl (hwv w hw), hsum ▸ Submodule.smul_mem _ _ hvA, ?_⟩
    funext i
    rw [wallFlip, if_neg hB', hL]
    show (if a i = 0 then -v i else a i) = u i
    by_cases ea : a i = 0
    · rw [if_pos ea, hvi, if_pos ea, neg_neg]
    · rw [if_neg ea]; exact (hau i ea).symm

end GlobalTheory.ChamberFlip

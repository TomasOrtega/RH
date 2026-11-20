import Formalism.SharpRestriction.Divisibility.OrbitPlaces

noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

def wOrb (D : D7) (p i : ℕ) (z : Pl D) (s : ZMod (nP D p)) : ℝ := wPl D (i + 1) (orbMap D p z s)

def eOrb (E : Ent D) (p : ℕ) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (s : ZMod (nP D p)) : ℝ :=
  if IsTopPl D (orbMap D p z s) then
    E.size u i (orbMap D p z s) - E.row u i (orbMap D p z s) 0 -
      (((D.R.k : ℝ) - 1) * wOrb D p i z s - 2 * wOrb D p i z s)
  else E.size u i (orbMap D p z s) - ((D.R.k : ℝ) - 1) * wOrb D p i z s

/- English proof (translation)
Establish `h` using `D.R.m_add_three_le_k`. Use linear arithmetic over natural numbers and integers.
-/
theorem three_le_k (D : D7) : 3 ≤ D.R.k := by
  have h := D.R.m_add_three_le_k
  omega

/- English proof (translation)
Establish `hxa` using `hS.xa`. Establish `ha1 : 1 < L.sc.a` using `hxa.2`. Establish `hp5 : (5 : ℝ) ≤ (p : ℝ)` using `by exact_mod_cast h.five`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (p : ℝ) ≤ L.sc.a ^ 2`.

Use polynomial arithmetic with `[hxa.1]`. Introduce `s`. Conclude with `hS.sizeA u i hi _`. Use `show 2 * Real.logb p (L.sc.a ^ 2) + 2 ≤ ((D.R.N i : ℕ) : ℝ) - 1`. Establish `hk` using `hS.rankA`.

Establish `hx : 1 ≤ L.sc.a ^ 2` using `by nlinarith`. Establish `hlog : Real.logb p (L.sc.a ^ 2) ≤ Real.logb 5 (L.sc.a ^ 2)`. Unfold `Real.logb`. Establish `hl5 : 0 < Real.log 5` using `Real.log_pos (by norm_num)`. Establish `hlp : Real.log 5 ≤ Real.log p` using `Real.log_le_log (by norm_num) hp5`.

Establish `hx0 : 0 ≤ Real.log (L.sc.a ^ 2)` using `Real.log_nonneg hx`. Rewrite using `[div_le_div_iff₀ (by linarith) hl5]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hN : (D.R.k : ℝ) ≤ (D.R.N i : ℝ)`. Establish `: D.R.k ≤ D.R.N i`.

Unfold `Formalism.BasicNotions.Ranks.N`. Conclude with `Nat.le_add_right _ _`. Conclude with `this` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem setting_sq {X : Inst D L} {E : Ent D} (hS : Shape D L X E) {p : ℕ} [Fact p.Prime] (h : OrbOK D p)
    (hp : (p : ℝ) ≤ L.sc.X'' D.R.n) (u : D.what₂.Word) {i : ℕ} (hi : i < D.R.m) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p]) :
    (orbLoc E p h u i z Th).HidaSetting (L.sc.a ^ 2) := by
  have hxa := hS.xa
  have ha1 : 1 < L.sc.a := hxa.2
  have hp5 : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.five
  refine ⟨?_, ?_, ?_⟩
  · show (p : ℝ) ≤ L.sc.a ^ 2
    nlinarith [hxa.1]
  · intro s
    exact hS.sizeA u i hi _
  · show 2 * Real.logb p (L.sc.a ^ 2) + 2 ≤ ((D.R.N i : ℕ) : ℝ) - 1
    have hk := hS.rankA
    have hx : 1 ≤ L.sc.a ^ 2 := by nlinarith
    have hlog : Real.logb p (L.sc.a ^ 2) ≤ Real.logb 5 (L.sc.a ^ 2) := by
      unfold Real.logb
      have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
      have hlp : Real.log 5 ≤ Real.log p := Real.log_le_log (by norm_num) hp5
      have hx0 : 0 ≤ Real.log (L.sc.a ^ 2) := Real.log_nonneg hx
      rw [div_le_div_iff₀ (by linarith) hl5]
      nlinarith
    have hN : (D.R.k : ℝ) ≤ (D.R.N i : ℝ) := by
      have : D.R.k ≤ D.R.N i := by
        unfold Formalism.BasicNotions.Ranks.N
        exact Nat.le_add_right _ _
      exact_mod_cast this
    linarith

/- English proof (translation)
Unfold `wOrb`. Conclude with `hS.wpos i hi _`.
-/
theorem wOrb_pos {X : Inst D L} {E : Ent D} (hS : Shape D L X E) (p : ℕ) {i : ℕ} (hi : i < D.R.m) (z : Pl D)
    (s : ZMod (nP D p)) : 0 < wOrb D p i z s := by
  unfold wOrb
  exact hS.wpos i hi _

/- English proof (translation)
Unfold `eOrb wOrb`. Use `split_ifs with ht`. Conclude with `hS.top u i hi _ ht`. Conclude with `hS.low u i hi _ ht`.
-/
theorem eOrb_bounds {X : Inst D L} {E : Ent D} (hS : Shape D L X E) (p : ℕ) (u : D.what₂.Word) {i : ℕ}
    (hi : i < D.R.m) (z : Pl D) (s : ZMod (nP D p)) :
    0 ≤ eOrb E p u i z s ∧ eOrb E p u i z s ≤ 4 * wOrb D p i z s := by
  unfold eOrb wOrb
  split_ifs with ht
  · exact hS.top u i hi _ ht
  · exact hS.low u i hi _ ht

/- English proof (translation)
Establish `ht : ¬ IsTopPl D (orbMap D p z s)` using `fun ht => hs (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩)`. Establish `hsz : ((orbLoc E p h u i z Th).Dl s : ℝ) = E.size u i (orbMap D p z s)`. Establish `h1 : (orbLoc E p h u i z Th).Dl s = (E.nu u i (orbMap D p z s)).cells.card`. Unfold `Formalism.MainNotions.product_zeroth_first_parts.Loc.Dl`. Use `split_ifs with hh`.

Conclude with `absurd hh hs`. Both sides reduce to the same expression. Rewrite using `[h1]`. Both sides reduce to the same expression. Rewrite using `[hsz]`.

Unfold `eOrb`. Rewrite using `[if_neg ht]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dl_off {E : Ent D} {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
    (s : ZMod (nP D p)) (hs : s ∉ (orbLoc E p h u i z Th).TT) :
    ((orbLoc E p h u i z Th).Dl s : ℝ) = ((D.R.k : ℝ) - 1) * wOrb D p i z s + eOrb E p u i z s := by
  have ht : ¬ IsTopPl D (orbMap D p z s) := fun ht => hs (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩)
  have hsz : ((orbLoc E p h u i z Th).Dl s : ℝ) = E.size u i (orbMap D p z s) := by
    have h1 : (orbLoc E p h u i z Th).Dl s = (E.nu u i (orbMap D p z s)).cells.card := by
      unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.Dl
      split_ifs with hh
      · exact absurd hh hs
      · rfl
    rw [h1]
    rfl
  rw [hsz]
  unfold eOrb
  rw [if_neg ht]
  ring

/- English proof (translation)
Establish `ht : IsTopPl D (orbMap D p z s)` using `(Finset.mem_filter.1 hs).2`. Establish `hA : (E.nu u i (orbMap D p z s)).rowLen 0 ≤ (E.nu u i (orbMap D p z s)).cells.card`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `x hx`.

Simplify using `only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hx`. Take `⟨j, hj, rfl⟩` from `hx`. Conclude with `YoungDiagram.mem_iff_lt_rowLen.2 hj`. Establish `hsz : ((orbLoc E p h u i z Th).Dl s : ℝ) = E.size u i (orbMap D p z s) - E.row u i (orbMap D p z s) 0`. Establish `h1 : (orbLoc E p h u i z Th).Dl s = (E.nu u i (orbMap D p z s)).cells.card - (E.nu u i (orbMap D p z s)).rowLen 0`.

Unfold `Formalism.MainNotions.product_zeroth_first_parts.Loc.Dl`. Use `split_ifs with hh`. Both sides reduce to the same expression. Conclude with `absurd hs hh`. Rewrite using `[h1, Nat.cast_sub hA]`.

Both sides reduce to the same expression. Rewrite using `[hsz]`. Unfold `eOrb`. Rewrite using `[if_pos ht]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dl_on {E : Ent D} {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
    (s : ZMod (nP D p)) (hs : s ∈ (orbLoc E p h u i z Th).TT) :
    ((orbLoc E p h u i z Th).Dl s : ℝ) =
      ((D.R.k : ℝ) - 1) * wOrb D p i z s - 2 * wOrb D p i z s + eOrb E p u i z s := by
  have ht : IsTopPl D (orbMap D p z s) := (Finset.mem_filter.1 hs).2
  have hA : (E.nu u i (orbMap D p z s)).rowLen 0 ≤ (E.nu u i (orbMap D p z s)).cells.card := by
    calc (E.nu u i (orbMap D p z s)).rowLen 0
        = ((Finset.range ((E.nu u i (orbMap D p z s)).rowLen 0)).map
            ⟨fun j => ((0 : ℕ), j), fun a b hab => by simpa using hab⟩).card := by simp
      _ ≤ (E.nu u i (orbMap D p z s)).cells.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          exact YoungDiagram.mem_iff_lt_rowLen.2 hj
  have hsz : ((orbLoc E p h u i z Th).Dl s : ℝ) =
      E.size u i (orbMap D p z s) - E.row u i (orbMap D p z s) 0 := by
    have h1 : (orbLoc E p h u i z Th).Dl s =
        (E.nu u i (orbMap D p z s)).cells.card - (E.nu u i (orbMap D p z s)).rowLen 0 := by
      unfold Formalism.MainNotions.product_zeroth_first_parts.Loc.Dl
      split_ifs with hh
      · rfl
      · exact absurd hs hh
    rw [h1, Nat.cast_sub hA]
    rfl
  rw [hsz]
  unfold eOrb
  rw [if_pos ht]
  ring

end PI.OrbBoundFW

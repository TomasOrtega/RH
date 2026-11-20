import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompRA

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.CRH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def cs (cost : Mat k r → ℕ) (w : List (Bool × Mat k r)) : ℕ := (w.map fun x => cost x.2).sum

/- English proof (translation)
Simplify using `[cs, List.map_append, List.sum_append]`.
-/
lemma cs_append (cost : Mat k r → ℕ) (w w' : List (Bool × Mat k r)) : cs cost (w ++ w') = cs cost w + cs cost w' := by
  simp [cs, List.map_append, List.sum_append]

/- English proof (translation)
Unfold `cs`. Conclude with `(h.map _).sum_eq`.
-/
lemma cs_perm (cost : Mat k r → ℕ) {w w' : List (Bool × Mat k r)} (h : w.Perm w') : cs cost w = cs cost w' := by
  unfold cs
  exact (h.map _).sum_eq

/- English proof (translation)
Simplify using `[cs, wL, wR, List.map_append, List.map_map, Function.comp_def]`.
-/
lemma cs_LR (cost : Mat k r → ℕ) (u v : List (Mat k r)) :
    ((u ++ v).map cost).sum = cs cost (wL u ++ wR v) := by
  simp [cs, wL, wR, List.map_append, List.map_map, Function.comp_def]

def admitted (n : ℕ) (w : List (Bool × Mat k r)) : Prop :=
  ∃ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) ∧ (∀ X ∈ v, unitLie k r X) ∧ u.length + v.length ≤ n ∧
    w = wL u ++ wR v

/- English proof (translation)
Take `⟨u, v, hu, hv, hl, rfl⟩` from `hw`. Take `⟨r₁, r₂, rfl, h1, h2⟩` from `List.sublist_append_iff.1 h`. Take `⟨u', hu', rfl⟩` from `List.sublist_map_iff.1 (show r₁.Sublist (u.map (Prod.mk true)) from h1)`. Take `⟨v', hv', rfl⟩` from `List.sublist_map_iff.1 (show r₂.Sublist (v.map (Prod.mk false)) from h2)`. Use `⟨u', v', fun X hX => hu X (hu'.subset hX), fun X hX => hv X (hv'.subset hX), ?_, rfl⟩` and prove the remaining obligations.

Use `hu'.length_le` as an intermediate fact. Use `hv'.length_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma Adm_sub {n : ℕ} {w w' : List (Bool × Mat k r)} (h : w'.Sublist w) (hw : admitted n w) : admitted n w' := by
  obtain ⟨u, v, hu, hv, hl, rfl⟩ := hw
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := List.sublist_append_iff.1 h
  obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.1 (show r₁.Sublist (u.map (Prod.mk true)) from h1)
  obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.1 (show r₂.Sublist (v.map (Prod.mk false)) from h2)
  refine ⟨u', v', fun X hX => hu X (hu'.subset hX), fun X hX => hv X (hv'.subset hX), ?_, rfl⟩
  have := hu'.length_le
  have := hv'.length_le
  omega

/- English proof (translation)
Rewrite using `[iteratedDeriv_eq_iterate]`. Conclude with `ContDiff.iterate_deriv q hh`.
-/
lemma cd_iter {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (q : ℕ) : ContDiff ℝ ∞ (iteratedDeriv q h) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv q hh

/- English proof (translation)
The claim follows from `Complex.ofRealCLM.contDiff.comp hψ`.
-/
lemma cd_ofReal {ψ : Mat k r → ℝ} (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (fun g => ((ψ g : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hψ

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `h0 : crv x g 0 = g` using `by simp [crv]`. Establish `hψc` using `hd_Dx x (dif (cd_ofReal hψ)) g`. Use `set D := Dx x (fun g => ((ψ g : ℝ) : ℂ)) g with hDdef`. Establish `hre : HasDerivAt (fun t => ψ (crv x g t)) D.re 0`.

Use `Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hψc` as an intermediate fact. Establish `hf : (⇑Complex.reCLM ∘ fun t => ((ψ (crv x g t) : ℝ) : ℂ)) = fun t => ψ (crv x g t)`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Rewrite `this` using `[hf]`.

Conclude with `this.congr_deriv (by simp)`. Establish `hD : D = (D.re : ℂ)` using `hψc.unique (by simpa using hre.ofReal_comp)`. Establish `hit : HasDerivAt (iteratedDeriv q h) (iteratedDeriv (q + 1) h (ψ g)) (ψ (crv x g 0))`. Rewrite using `[h0, iteratedDeriv_succ]`. Conclude with `((dif (cd_iter hh q)) (ψ g)).hasDerivAt`.

Establish `hcomp` using `(hit.comp (0 : ℝ) hre).ofReal_comp`. Establish `hF` using `hd_Dx x (dif (cd_ofReal ((cd_iter hh q).comp hψ))) g`. Establish `e1 : Dx x (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) g = ((iteratedDeriv (q + 1) h (ψ g) * D.re : ℝ) : ℂ)` using `hF.unique hcomp`. Rewrite using `[e1, Complex.ofReal_mul, ← hD]`.
-/
lemma chain (x : Bool × Mat k r) {ψ : Mat k r → ℝ} {h : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hh : ContDiff ℝ ∞ h)
    (q : ℕ) :
    Dx x (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) =
      fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ) * Dx x (fun g => ((ψ g : ℝ) : ℂ)) g := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have hψc := hd_Dx x (dif (cd_ofReal hψ)) g
  set D := Dx x (fun g => ((ψ g : ℝ) : ℂ)) g with hDdef
  have hre : HasDerivAt (fun t => ψ (crv x g t)) D.re 0 := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hψc
    have hf : (⇑Complex.reCLM ∘ fun t => ((ψ (crv x g t) : ℝ) : ℂ)) = fun t => ψ (crv x g t) := by
      funext t; simp
    rw [hf] at this
    exact this.congr_deriv (by simp)
  have hD : D = (D.re : ℂ) := hψc.unique (by simpa using hre.ofReal_comp)
  have hit : HasDerivAt (iteratedDeriv q h) (iteratedDeriv (q + 1) h (ψ g)) (ψ (crv x g 0)) := by
    rw [h0, iteratedDeriv_succ]
    exact ((dif (cd_iter hh q)) (ψ g)).hasDerivAt
  have hcomp := (hit.comp (0 : ℝ) hre).ofReal_comp
  have hF := hd_Dx x (dif (cd_ofReal ((cd_iter hh q).comp hψ))) g
  have e1 : Dx x (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) g
      = ((iteratedDeriv (q + 1) h (ψ g) * D.re : ℝ) : ℂ) := hF.unique hcomp
  rw [e1, Complex.ofReal_mul, ← hD]

/- English proof (translation)
Unfold `Dw`. Rewrite using `[List.foldr_append]`. Both sides reduce to the same expression.
-/
private lemma Dw_append_singleton (w : List (Bool × Mat k r)) (x : Bool × Mat k r) (f : Mat k r → ℂ) :
    Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl

/- English proof (translation)
Establish `hgN : ∀ g : Mat k r, 0 ≤ gN g`. Introduce `g`. Use `first`. Consider the case `(unfold gN; positivity)`. Consider the case `(simp only [gN]; positivity)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `q`. Take `⟨c, hc⟩` from `hb q`.

Use `⟨max c 0, le_max_right _ _, fun w _ hw g _ => ?_⟩` and prove the remaining obligations. Establish `: w = []` using `List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)`. Substitute `this` using the available equality. Simplify using `only [Dw, List.foldr_nil, cs, List.map_nil, List.sum_nil, pow_zero, mul_one, Complex.norm_real]`. Conclude with `(hc _).trans (le_max_left _ _)`.

Consider the case `succ m ih`. Introduce `q`. Take `⟨K₁, hK₁, h₁⟩` from `ih q`. Take `⟨K₂, hK₂, h₂⟩` from `ih (q + 1)`. Use `⟨max K₁ (2 ^ m * (K₂ * max C₀ 0)), le_max_of_le_left hK₁, fun w hw hlen g hg => ?_⟩` and prove the remaining obligations.

Break down `Nat.lt_or_ge w.length (m + 1) with hlt | hge` into its components or cases. Conclude with `(h₁ w hw (by omega) g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hgN g) _))`. Choose the witnesses or unpack the hypotheses as in `⟨w', x, rfl⟩ : ∃ w' x, w = w' ++ [x] := by`. Break down `List.eq_nil_or_concat w with h0 | ⟨w', x, hx⟩` into its components or cases. Substitute `h0` using the available equality.

Simplify using `at hge`. Conclude with `⟨w', x, by rw [hx, List.concat_eq_append]⟩`. Establish `hlen' : w'.length = m` using `by simp at hlen hge; omega`. Rewrite using `[Dw_append_singleton, chain x hψ hh q]`. Establish `hyp : ∀ w₁ w₂, Spl w' w₁ w₂ → ‖Dw w₁ (fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ)) g‖ * ‖Dw w₂ (Dx x fun g => ((ψ g : ℝ) : ℂ)) g‖ ≤ K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x])`.

Introduce and unpack `w₁ w₂ ⟨s1, s2, hp⟩`. Establish `hA1 : admitted n w₁` using `Adm_sub (s1.trans (List.sublist_append_left _ _)) hw`. Establish `hA2 : admitted n (w₂ ++ [x])` using `Adm_sub (s2.append (List.Sublist.refl _)) hw`. Establish `hl1 : w₁.length ≤ m` using `by have := s1.length_le; omega`. Establish `e1` using `h₂ w₁ hA1 hl1 g hg`.

Establish `e2` using `H (w₂ ++ [x]) hA2 (by simp) g hg`. Rewrite `e2` using `[Dw_append_singleton]`. Establish `hcs : cs cost w₁ + cs cost (w₂ ++ [x]) = cs cost (w' ++ [x])`. Rewrite using `[← cs_append]`. Conclude with `cs_perm cost (by rw [← List.append_assoc]; exact hp.append_right [x])`.

Combine the equalities or inequalities in the displayed calculation. Establish `hM` using `leibB g (K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x])) w' (fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ)) (Dx x fun g => ((ψ g : ℝ) : ℂ)) (cd_ofReal ((cd_iter hh (q + 1)).comp hψ)) (cd_Dx x (cd_ofReal hψ)) hyp`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem main (ψ : Mat k r → ℝ) (h : ℝ → ℝ) (cost : Mat k r → ℕ) (n : ℕ) (C₀ : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hh : ContDiff ℝ ∞ h) (hb : ∀ q : ℕ, ∃ c : ℝ, ∀ x, ‖iteratedDeriv q h x‖ ≤ c)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r,
      ‖Dw w (fun g => ((ψ g : ℝ) : ℂ)) g‖ ≤ C₀ * gN g ^ cs cost w) :
    ∀ m q : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ w, admitted n w → w.length ≤ m → ∀ g ∈ GV k r,
      ‖Dw w (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) g‖ ≤ K * gN g ^ cs cost w := by
  have hgN : ∀ g : Mat k r, 0 ≤ gN g := by
    intro g
    first
    | (unfold gN; positivity)
    | (simp only [gN]; positivity)
  intro m
  induction m with
  | zero =>
    intro q
    obtain ⟨c, hc⟩ := hb q
    refine ⟨max c 0, le_max_right _ _, fun w _ hw g _ => ?_⟩
    have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
    subst this
    simp only [Dw, List.foldr_nil, cs, List.map_nil, List.sum_nil, pow_zero, mul_one, Complex.norm_real]
    exact (hc _).trans (le_max_left _ _)
  | succ m ih =>
    intro q
    obtain ⟨K₁, hK₁, h₁⟩ := ih q
    obtain ⟨K₂, hK₂, h₂⟩ := ih (q + 1)
    refine ⟨max K₁ (2 ^ m * (K₂ * max C₀ 0)), le_max_of_le_left hK₁, fun w hw hlen g hg => ?_⟩
    rcases Nat.lt_or_ge w.length (m + 1) with hlt | hge
    · exact (h₁ w hw (by omega) g hg).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hgN g) _))
    · obtain ⟨w', x, rfl⟩ : ∃ w' x, w = w' ++ [x] := by
        rcases List.eq_nil_or_concat w with h0 | ⟨w', x, hx⟩
        · subst h0; simp at hge
        · exact ⟨w', x, by rw [hx, List.concat_eq_append]⟩
      have hlen' : w'.length = m := by simp at hlen hge; omega
      rw [Dw_append_singleton, chain x hψ hh q]
      have hyp : ∀ w₁ w₂, Spl w' w₁ w₂ →
          ‖Dw w₁ (fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ)) g‖ *
            ‖Dw w₂ (Dx x fun g => ((ψ g : ℝ) : ℂ)) g‖ ≤ K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x]) := by
        rintro w₁ w₂ ⟨s1, s2, hp⟩
        have hA1 : admitted n w₁ := Adm_sub (s1.trans (List.sublist_append_left _ _)) hw
        have hA2 : admitted n (w₂ ++ [x]) := Adm_sub (s2.append (List.Sublist.refl _)) hw
        have hl1 : w₁.length ≤ m := by have := s1.length_le; omega
        have e1 := h₂ w₁ hA1 hl1 g hg
        have e2 := H (w₂ ++ [x]) hA2 (by simp) g hg
        rw [Dw_append_singleton] at e2
        have hcs : cs cost w₁ + cs cost (w₂ ++ [x]) = cs cost (w' ++ [x]) := by
          rw [← cs_append]
          exact cs_perm cost (by rw [← List.append_assoc]; exact hp.append_right [x])
        calc _ ≤ (K₂ * gN g ^ cs cost w₁) * (max C₀ 0 * gN g ^ cs cost (w₂ ++ [x])) :=
              mul_le_mul e1 (e2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
                (pow_nonneg (hgN g) _))) (norm_nonneg _) (mul_nonneg hK₂ (pow_nonneg (hgN g) _))
          _ = K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x]) := by rw [← hcs, pow_add]; ring
      have hM := leibB g (K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x])) w'
        (fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ)) (Dx x fun g => ((ψ g : ℝ) : ℂ))
        (cd_ofReal ((cd_iter hh (q + 1)).comp hψ)) (cd_Dx x (cd_ofReal hψ)) hyp
      calc _ ≤ 2 ^ w'.length * (K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x])) := hM
        _ = (2 ^ m * (K₂ * max C₀ 0)) * gN g ^ cs cost (w' ++ [x]) := by rw [hlen']; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (hgN g) _)

end PI.UnitaryCorollaryDerivatives.CRH

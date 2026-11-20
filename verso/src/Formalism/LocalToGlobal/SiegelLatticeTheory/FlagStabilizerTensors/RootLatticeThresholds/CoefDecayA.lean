import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.SmoothClassInFiniteOrder

open Matrix Finset

noncomputable section

namespace Formalism.L2.SG.Pf.CoefDecay

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt PI.ComplexConjugateDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def CCw (k r : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F : B.Mat k r → E) : Prop :=
  SS k r F ∧ ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
    ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖B.dLR u v F g‖ ≤ C

open Classical in

def cstW {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (u v : List (B.Mat k r)) : ℝ :=
  if h : (∀ X ∈ u, B.unitLie k r X) ∧ (∀ X ∈ v, B.unitLie k r X) then Classical.choose (hF.2 u v h.1 h.2) else 0

/- English proof (translation)
Unfold `cstW`. Rewrite using `[dif_pos ⟨hu, hv⟩]`. Conclude with `Classical.choose_spec (hF.2 u v hu hv) g hg`.
-/
theorem cstW_spec {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (u v : List (B.Mat k r))
    (hu : ∀ X ∈ u, B.unitLie k r X) (hv : ∀ X ∈ v, B.unitLie k r X) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    B.gN g ^ A * ‖B.dLR u v F g‖ ≤ cstW hF u v := by
  unfold cstW
  rw [dif_pos ⟨hu, hv⟩]
  exact Classical.choose_spec (hF.2 u v hu hv) g hg

def termW {N : ℕ} (e : Fin N → B.Mat k r) (K : ℝ) {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F)
    (a b : ℕ) : ℝ :=
  K ^ (a + b) * bsum e (List.replicate a true ++ List.replicate b false)
    (fun β => max (cstW hF (β.take a) (β.drop a)) 0)

/- English proof (translation)
Take `⟨N, e, c, K, hK, he, hc, hcK⟩` from `basis_exists k r`. Establish `he' : ∀ i, B.inLie k r (e i)` using `fun i => (he i).1`. Establish `hgN : ∀ g : B.Mat k r, 0 ≤ B.gN g ^ A` using `fun g => Real.rpow_nonneg (Real.sqrt_nonneg _) A`. Establish `hterm : ∀ a b, 0 ≤ termW e K hF a b` using `fun a b => mul_nonneg (pow_nonneg hK _) (bsum_nonneg e _ _ fun β => le_max_right _ _)`. Establish `hword : ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → ∀ g ∈ B.GV k r, B.gN g ^ A * ‖B.dLR u v F g‖ ≤ termW e K hF u.length v.length`.

Introduce `u v hu hv g hg`. Use `set ks := List.replicate u.length true ++ List.replicate v.length false with hks`. Establish `hlen : (u ++ v).length = ks.length` using `by simp [hks]`. Establish `hxs : ∀ X ∈ u ++ v, B.inLie k r X ∧ ∀ i, |c i X| ≤ K`. Introduce `X hX`.

Establish `hX' : B.unitLie k r X`. Break down `List.mem_append.1 hX with h | h` into its components or cases. Conclude with `hu X h`. Conclude with `hv X h`. Conclude with `⟨hX'.1, hcK X hX'⟩`.

Establish `hexp` using `expand e c hK he' hc ks (u ++ v) hlen hxs id good_id F hF.1 g hg`. Rewrite using `[B.dLR, ← B.dLR, dLR_eq_ev]`. Establish `hl : (u ++ v).length = u.length + v.length` using `List.length_append`. Rewrite `hexp` using `[hl]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[bsum_mul]`. Simplify using `only [id]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ termW e K hF u.length v.length := by`. Unfold `termW`.

Use `mul_le_mul_of_nonneg_left ?_ (pow_nonneg hK _)` and prove the remaining obligations. Use `bsum_mono e ks _ _ ?_` and prove the remaining obligations. Introduce `β hβ hβe`. Establish `hβl : β.length = u.length + v.length` using `by rw [hβ]; simp [hks]`. Establish `h1 : (β.take u.length).length = u.length` using `by simp [List.length_take, hβl]`.

Establish `h2 : (β.drop u.length).length = v.length` using `by simp [List.length_drop, hβl]`. Establish `hev : ev ks β F = B.dLR (β.take u.length) (β.drop u.length) F`. Rewrite using `[dLR_eq_ev, h1, h2, List.take_append_drop]`. Establish `hunit : ∀ X ∈ β, B.unitLie k r X`. Introduce `X hX`.

Take `⟨i, rfl⟩` from `hβe X hX`. Conclude with `he i`. Rewrite using `[hev]`. Conclude with `(cstW_spec hF _ _ (fun X hX => hunit X (List.mem_of_mem_take hX)) (fun X hX => hunit X (List.mem_of_mem_drop hX)) hg).trans (le_max_left _ _)`. Use `⟨∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), termW e K hF a b, ?_, ?_⟩` and prove the remaining obligations.

Introduce `g₀ hg₀`. Take `⟨U, f', hU, hgU, hf', hff'⟩` from `hF.1 g₀ hg₀`. Conclude with `⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast le_top), hff'⟩`. Introduce `u v hu hv hl g hg`. Use `(hword u v hu hv g hg).trans ?_` and prove the remaining obligations.

Establish `ha : u.length ∈ Finset.range (m + 1)` using `Finset.mem_range.2 (by omega)`. Establish `hb : v.length ∈ Finset.range (m + 1)` using `Finset.mem_range.2 (by omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inCC_of_CCw {A : ℝ} {F : B.Mat k r → E} (hF : CCw k r A F) (m : ℕ) :
    B.InCC (k := k) (r := r) A m F := by
  obtain ⟨N, e, c, K, hK, he, hc, hcK⟩ := basis_exists k r
  have he' : ∀ i, B.inLie k r (e i) := fun i => (he i).1
  have hgN : ∀ g : B.Mat k r, 0 ≤ B.gN g ^ A := fun g => Real.rpow_nonneg (Real.sqrt_nonneg _) A
  have hterm : ∀ a b, 0 ≤ termW e K hF a b := fun a b =>
    mul_nonneg (pow_nonneg hK _) (bsum_nonneg e _ _ fun β => le_max_right _ _)

  have hword : ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      ∀ g ∈ B.GV k r, B.gN g ^ A * ‖B.dLR u v F g‖ ≤ termW e K hF u.length v.length := by
    intro u v hu hv g hg
    set ks := List.replicate u.length true ++ List.replicate v.length false with hks
    have hlen : (u ++ v).length = ks.length := by simp [hks]
    have hxs : ∀ X ∈ u ++ v, B.inLie k r X ∧ ∀ i, |c i X| ≤ K := by
      intro X hX
      have hX' : B.unitLie k r X := by
        rcases List.mem_append.1 hX with h | h
        · exact hu X h
        · exact hv X h
      exact ⟨hX'.1, hcK X hX'⟩
    have hexp := expand e c hK he' hc ks (u ++ v) hlen hxs id good_id F hF.1 g hg
    rw [B.dLR, ← B.dLR, dLR_eq_ev]
    have hl : (u ++ v).length = u.length + v.length := List.length_append
    rw [hl] at hexp
    calc B.gN g ^ A * ‖ev ks (u ++ v) F g‖
        ≤ B.gN g ^ A * (K ^ (u.length + v.length) * bsum e ks (fun β => ‖id (ev ks β F) g‖)) :=
          mul_le_mul_of_nonneg_left hexp (hgN g)
      _ = K ^ (u.length + v.length) * bsum e ks (fun β => B.gN g ^ A * ‖ev ks β F g‖) := by
          rw [bsum_mul]; simp only [id]; ring
      _ ≤ termW e K hF u.length v.length := by
          unfold termW
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hK _)
          refine bsum_mono e ks _ _ ?_
          intro β hβ hβe
          have hβl : β.length = u.length + v.length := by rw [hβ]; simp [hks]
          have h1 : (β.take u.length).length = u.length := by simp [List.length_take, hβl]
          have h2 : (β.drop u.length).length = v.length := by simp [List.length_drop, hβl]
          have hev : ev ks β F = B.dLR (β.take u.length) (β.drop u.length) F := by
            rw [dLR_eq_ev, h1, h2, List.take_append_drop]
          have hunit : ∀ X ∈ β, B.unitLie k r X := by
            intro X hX
            obtain ⟨i, rfl⟩ := hβe X hX
            exact he i
          rw [hev]
          exact (cstW_spec hF _ _ (fun X hX => hunit X (List.mem_of_mem_take hX))
            (fun X hX => hunit X (List.mem_of_mem_drop hX)) hg).trans (le_max_left _ _)
  refine ⟨∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), termW e K hF a b, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff'⟩ := hF.1 g₀ hg₀
    exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast le_top), hff'⟩
  · intro u v hu hv hl g hg
    refine (hword u v hu hv g hg).trans ?_
    have ha : u.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    have hb : v.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    calc termW e K hF u.length v.length
        ≤ ∑ b ∈ Finset.range (m + 1), termW e K hF u.length b :=
          Finset.single_le_sum (fun b _ => hterm _ b) hb
      _ ≤ ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1), termW e K hF a b :=
          Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range (m + 1), termW e K hF a b)
            (fun a _ => Finset.sum_nonneg fun b _ => hterm a b) ha

end Formalism.L2.SG.Pf.CoefDecay

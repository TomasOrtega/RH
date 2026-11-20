import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a t ih`. Establish `ha : 0 ≤ f a ∧ f a ≤ c` using `hf a (by simp)`. Establish `ht : ∀ x ∈ t, 0 ≤ f x ∧ f x ≤ c` using `fun x hx => hf x (by simp [hx])`.

Establish `h0 : 0 ≤ (t.map f).prod`. Apply `List.prod_nonneg` to reduce the goal to its premises. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `List.mem_map.1 hy`. Conclude with `(ht x hx).1`.

Rewrite using `[List.map_cons, List.prod_cons, List.length_cons, pow_succ']`. Conclude with `mul_le_mul ha.2 (ih ht) h0 hc`.
-/
theorem top_prod_map_le {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ)
    (hf : ∀ x ∈ l, 0 ≤ f x ∧ f x ≤ c) (hc : 0 ≤ c) : (l.map f).prod ≤ c ^ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : 0 ≤ f a ∧ f a ≤ c := hf a (by simp)
    have ht : ∀ x ∈ t, 0 ≤ f x ∧ f x ≤ c := fun x hx => hf x (by simp [hx])
    have h0 : 0 ≤ (t.map f).prod := by
      apply List.prod_nonneg
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact (ht x hx).1
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul ha.2 (ih ht) h0 hc

/- English proof (translation)
Unfold `lsz`. Conclude with `le_max_left _ _`.
-/
theorem top_lsz_ge_one {k r : ℕ} (X : B.Mat k r) : 1 ≤ lsz X := by
  unfold lsz
  exact le_max_left _ _

/- English proof (translation)
Apply `List.prod_nonneg` to reduce the goal to its premises. Introduce `a ha`. Take `⟨X, -, rfl⟩` from `List.mem_map.1 ha`. Conclude with `le_trans zero_le_one (top_lsz_ge_one X)`.
-/
theorem top_prod_lsz_nonneg {k r : ℕ} (l : List (B.Mat k r)) : 0 ≤ (l.map lsz).prod := by
  apply List.prod_nonneg
  intro a ha
  obtain ⟨X, -, rfl⟩ := List.mem_map.1 ha
  exact le_trans zero_le_one (top_lsz_ge_one X)

/- English proof (translation)
Unfold `B.gN`. Conclude with `Real.sqrt_nonneg _`.
-/
theorem top_gN_nonneg {k r : ℕ} (g : B.Mat k r) : 0 ≤ B.gN g := by
  unfold B.gN
  exact Real.sqrt_nonneg _

/- English proof (translation)
Introduce `hM hR hRt hLt hZt hD hS21`. Introduce `k p s ρ σ d hd hs K hK hKpos Q`. Take `⟨CL, hCL⟩` from `hL k (p + s) ρ`. Take `⟨CS, hCS⟩` from `hS21 k p s ρ σ d hd hs K hK hKpos`. Use `choose Cz hCz using fun q : ℕ => hZ hM hR hZt hD hS21 k p s ρ σ d hd hs K hK hKpos q`.

Use `set C1 : ℝ := max 1 (CL * CS ^ 2) with hC1def`. Establish `hC1ge : 1 ≤ C1` using `le_max_left _ _`. Use `⟨(∑ q ∈ Finset.range (Q + 1), max (Cz q) 0) * C1 ^ Q, ?_⟩` and prove the remaining obligations. Introduce `E _ _ F₁ A₁ B₁ hStar ξ u v q hu hv hq Z γ hZdet hγ`. Set `u'` to `u.map (cj k (p + s) ρ ξ.1.1)`.

Set `v'` to `v.map (cj k (p + s) ρ ξ.1.2)`. Set `H : B.Mat k (p + s + ρ) → E` to `B.dLR u' v' F₁`. Establish `hfun : (fun Z' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) = fun Z' => H (gaXi k ρ σ d ξ Z' γ)`. Use function extensionality and compare the values at `Z'`. Conclude with `congrFun (hW hLt hRt k p s ρ σ d ξ Z' E F₁ u v) γ`.

Rewrite using `[hfun]`. Establish `hcjP : ∀ (x : RC k (p + s) ρ) (Y : B.Mat k ρ), B.unitLie k ρ Y → inLieP k (p + s) ρ (cj k (p + s) ρ x Y)` using `fun x Y hY => (hD k (p + s) ρ x).1 Y hY.1`. Establish `hu' : ∀ X ∈ u', inLieP k (p + s) ρ X`. Introduce `X hX`. Take `⟨Y, hY, rfl⟩` from `List.mem_map.1 hX`.

Conclude with `hcjP _ Y (hu Y hY)`. Establish `hv' : ∀ X ∈ v', inLieP k (p + s) ρ X`. Introduce `X hX`. Take `⟨Y, hY, rfl⟩` from `List.mem_map.1 hX`. Conclude with `hcjP _ Y (hv Y hY)`.

Establish `hwl : ∀ x ∈ wL u' ++ wR v', B.inLie k (p + s + ρ) x.2`. Introduce `x hx`. Simplify using `only [List.mem_append, wL, wR, List.mem_map] at hx`. Break down `hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩` into its components or cases. Conclude with `(hu' X hX).1`.

Conclude with `(hv' X hX).1`. Establish `hHeq : H = Dw (wL u' ++ wR v') F₁` using `dLR_eq _ _ _`. Establish `hg0 : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ)` using `(hZS hM hR k p s ρ σ d hd E F₁ Q hStar.1 ξ Z γ hZdet hγ).1`. Establish `hB₁ : 0 ≤ B₁`. Establish `h0` using `hStar.2.2 [] [] (by simp [unitP]) (by simp [unitP]) (by simp) _ hg0`.

Conclude with `le_trans (mul_nonneg (Real.rpow_nonneg (top_gN_nonneg _) _) (norm_nonneg _)) h0`. Establish `hC0 : 0 ≤ (∑ q ∈ Finset.range (Q + 1), max (Cz q) 0) * C1 ^ Q` using `mul_nonneg (Finset.sum_nonneg fun q _ => le_max_right _ _) (pow_nonneg (le_trans zero_le_one hC1ge) _)`. Distinguish the cases in `hKg : ‖DjU k (p + s) ρ (gaXi k ρ σ d ξ Z γ)‖ ∈ K`. Take `⟨hg1, hRn1, hRn2, -⟩` from `hCS ξ Z γ hγ hKg set g0 := gaXi k ρ σ d ξ Z γ with hg0def set X0 := B.gN g0 with hX0def`. Establish `hX0pos : 0 < X0` using `lt_of_lt_of_le zero_lt_one hg1`.

Establish `hX0nn : 0 ≤ X0` using `hX0pos.le`. Establish `hCkH : B.CkOn (q : ℕ∞) (B.GV k (p + s + ρ)) H`. Rewrite using `[hHeq]`. Apply `CkOn_Dw hwl` to reduce the goal to its premises. Apply `sCkOn_mono _ hStar.1` to reduce the goal to its premises.

Establish `hl : q + (u.length + v.length) ≤ Q` using `by omega`. Simplify using `only [List.length_append, wL, wR, List.length_map, u', v']`. Conclude with `hl` after adjusting the coercions. Set `β : ℝ` to `B₁ * X0 ^ (-A₁) * ((u'.map lsz).prod * (v'.map lsz).prod)`. Establish `hw : ∀ w : List (B.Mat k (p + s + ρ)), (∀ X ∈ w, inLieP k (p + s) ρ X) → w.length ≤ q → ‖B.Rw w H g0‖ ≤ β * (w.map lsz).prod`.

Introduce `w hwP hwl'`. Establish `hcomm` using `hC k (p + s + ρ) E F₁ Q hStar.1 u' v' w (fun X hX => (hu' X hX).1) (fun X hX => (hv' X hX).1) (fun X hX => (hwP X hX).1) (by simp only [List.length_map, u', v']; omega) g0 hg0`. Rewrite using `[hcomm]`. Establish `hsc` using `hS k (p + s) ρ E F₁ A₁ Q B₁ K hStar u' (w ++ v') hu' (by`. Introduce `X hX`.

Break down `List.mem_append.1 hX with h | h` into its components or cases. Conclude with `hwP X h`. Conclude with `hv' X h)`. Use the proof step `(by simp only [List.length_append, List.length_map, u', v']; omega) g0 hg0`. Establish `hprod : ((u' ++ (w ++ v')).map lsz).prod = (u'.map lsz).prod * ((w.map lsz).prod * (v'.map lsz).prod)`.

Simplify using `only [List.map_append, List.prod_append]`. Rewrite `hsc` using `[hprod]`. Establish `hpowpos : 0 < X0 ^ A₁` using `Real.rpow_pos_of_pos hX0pos _`. Establish `hle : ‖B.dLR u' (w ++ v') F₁ g0‖ ≤ B₁ * ((u'.map lsz).prod * ((w.map lsz).prod * (v'.map lsz).prod)) / X0 ^ A₁`. Rewrite using `[le_div_iff₀ hpowpos]`.

Combine the linear relations using `[hsc]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [β]`. Rewrite using `[Real.rpow_neg hX0nn]`. Clear the denominators using the available nonvanishing facts.

Take `⟨hcd, hbd⟩` from `hCz q E H β hCkH ξ Z γ hZdet hγ hKg hw`. Use `⟨hcd, le_trans hbd ?_⟩` and prove the remaining obligations. Establish `hlet : ∀ x : RC k (p + s) ρ, B.gN (Rn k (p + s) ρ x) ≤ CS * X0 ^ (p + s) → ∀ Y, B.unitLie k ρ Y → lsz (cj k (p + s) ρ x Y) ≤ C1 * X0 ^ (2 * (p + s + ρ))`. Introduce `x hx Y hY`. Establish `h1` using `hCL x Y hY.2`.

Establish `hn0 : 0 ≤ B.gN (Rn k (p + s) ρ x)` using `top_gN_nonneg _`. Establish `hl1` using `top_lsz_ge_one (cj k (p + s) ρ x Y)`. Establish `hCL0 : 0 ≤ CL` using `by nlinarith [sq_nonneg (B.gN (Rn k (p + s) ρ x))]`. Establish `hsq : B.gN (Rn k (p + s) ρ x) ^ 2 ≤ (CS * X0 ^ (p + s)) ^ 2` using `pow_le_pow_left₀ hn0 hx 2`. Combine the equalities or inequalities in the displayed calculation.

Establish `hc : 0 ≤ C1 * X0 ^ (2 * (p + s + ρ))` using `mul_nonneg (le_trans zero_le_one hC1ge) (pow_nonneg hX0nn _)`. Establish `hu'b : (u'.map lsz).prod ≤ (C1 * X0 ^ (2 * (p + s + ρ))) ^ u.length`. Establish `h` using `top_prod_map_le u' lsz (C1 * X0 ^ (2 * (p + s + ρ))) (fun X hX => by`. Take `⟨Y, hY, rfl⟩` from `List.mem_map.1 hX`. Conclude with `⟨le_trans zero_le_one (top_lsz_ge_one _), hlet _ hRn1 Y (hu Y hY)⟩) hc`.

Simplify `h` using `only [List.length_map, u']`. Establish `hv'b : (v'.map lsz).prod ≤ (C1 * X0 ^ (2 * (p + s + ρ))) ^ v.length`. Establish `h` using `top_prod_map_le v' lsz (C1 * X0 ^ (2 * (p + s + ρ))) (fun X hX => by`. Take `⟨Y, hY, rfl⟩` from `List.mem_map.1 hX`. Conclude with `⟨le_trans zero_le_one (top_lsz_ge_one _), hlet _ hRn2 Y (hv Y hY)⟩) hc`.

Simplify `h` using `only [List.length_map, v']`. Establish `hβ : β ≤ B₁ * X0 ^ (-A₁) * (C1 ^ Q * X0 ^ (2 * (p + s + ρ) * (u.length + v.length)))`. Establish `h1 : (u'.map lsz).prod * (v'.map lsz).prod ≤ (C1 * X0 ^ (2 * (p + s + ρ))) ^ (u.length + v.length)`. Rewrite using `[pow_add]`. Conclude with `mul_le_mul hu'b hv'b (top_prod_lsz_nonneg _) (pow_nonneg hc _)`.

Establish `h2 : (C1 * X0 ^ (2 * (p + s + ρ))) ^ (u.length + v.length) ≤ C1 ^ Q * X0 ^ (2 * (p + s + ρ) * (u.length + v.length))`. Rewrite using `[mul_pow, ← pow_mul]`. Conclude with `mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1ge (by omega)) (pow_nonneg hX0nn _)`. Conclude with `mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hB₁ (Real.rpow_nonneg hX0nn _))`. Establish `hβ0 : 0 ≤ β` using `mul_nonneg (mul_nonneg hB₁ (Real.rpow_nonneg hX0nn _)) (mul_nonneg (top_prod_lsz_nonneg _) (top_prod_lsz_nonneg _))`.

Establish `hX5 : 0 ≤ X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ))` using `Real.rpow_nonneg hX0nn _`. Establish `hexp : X0 ^ (-A₁ + 5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ) + 2 * ((p + s + ρ : ℕ) : ℝ) * ((u.length + v.length : ℕ) : ℝ)) = X0 ^ (-A₁) * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) * X0 ^ (2 * (p + s + ρ) * (u.length + v.length))`. Rewrite using `[Real.rpow_add hX0pos, Real.rpow_add hX0pos, ← Real.rpow_natCast]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hmax : max (Cz q) 0 ≤ ∑ q ∈ Finset.range (Q + 1), max (Cz q) 0` using `Finset.single_le_sum (f := fun q => max (Cz q) 0) (fun i _ => le_max_right _ _) (Finset.mem_range.mpr (by omega))`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX0nn _)` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_right _ hB₁` to reduce the goal to its premises.

Conclude with `mul_le_mul_of_nonneg_right hmax (pow_nonneg (le_trans zero_le_one hC1ge) _)`. Establish `hcont : Continuous fun g : B.Mat k (p + s + ρ) => ‖DjU k (p + s) ρ g‖`. Establish `hZc : Continuous fun g : B.Mat k (p + s + ρ) => Zh k (p + s) ρ g` using `continuous_pi fun a => continuous_pi fun b => (continuous_apply _).comp (continuous_apply _)`. Conclude with `hZc.matrix_det.norm`. Establish `hOopen : IsOpen {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K}` using `hK.isClosed.isOpen_compl.preimage hcont`.

Establish `hF0 : ∀ g ∈ B.GV k (p + s + ρ), g ∈ {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K} → F₁ g = 0`. Introduce `g hg hgO`. Assume the negation of the conclusion as `hne`. Conclude with `hgO (hStar.2.1 g hg hne)`. Establish `hH0 : ∀ g ∈ B.GV k (p + s + ρ), g ∈ {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K} → H g = 0`.

Introduce `g hg hgO`. Rewrite using `[hHeq]`. Conclude with `Dw_vanish hOopen hwl hF0 g hg hgO`. Take `⟨hcd, hz⟩` from `hO hM hR k p s ρ σ d hd E H _ hOopen hH0 ξ Z γ hZdet hγ hKg q`. Use `⟨hcd, ?_⟩` and prove the remaining obligations.

Rewrite using `[hz, norm_zero]`. Conclude with `mul_nonneg (mul_nonneg hC0 hB₁) (Real.rpow_nonneg (top_gN_nonneg _) _)`.
-/
theorem unitarySum_cost_of_parts (hW : WordsId) (hL : LetterSize) (hS : StarScale) (hC : CommLR) (hO : OffK)
    (hZS : ZSmooth) (hZ : ZCost) : DerivativeCostFromComponents := by
  intro hM hR hRt hLt hZt hD hS21
  intro k p s ρ σ d hd hs K hK hKpos Q
  obtain ⟨CL, hCL⟩ := hL k (p + s) ρ
  obtain ⟨CS, hCS⟩ := hS21 k p s ρ σ d hd hs K hK hKpos
  choose Cz hCz using fun q : ℕ => hZ hM hR hZt hD hS21 k p s ρ σ d hd hs K hK hKpos q
  set C1 : ℝ := max 1 (CL * CS ^ 2) with hC1def
  have hC1ge : 1 ≤ C1 := le_max_left _ _
  refine ⟨(∑ q ∈ Finset.range (Q + 1), max (Cz q) 0) * C1 ^ Q, ?_⟩
  intro E _ _ F₁ A₁ B₁ hStar ξ u v q hu hv hq Z γ hZdet hγ
  let u' := u.map (cj k (p + s) ρ ξ.1.1)
  let v' := v.map (cj k (p + s) ρ ξ.1.2)
  let H : B.Mat k (p + s + ρ) → E := B.dLR u' v' F₁
  have hfun : (fun Z' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) =
      fun Z' => H (gaXi k ρ σ d ξ Z' γ) := by
    funext Z'
    exact congrFun (hW hLt hRt k p s ρ σ d ξ Z' E F₁ u v) γ
  rw [hfun]
  have hcjP : ∀ (x : RC k (p + s) ρ) (Y : B.Mat k ρ), B.unitLie k ρ Y →
      inLieP k (p + s) ρ (cj k (p + s) ρ x Y) :=
    fun x Y hY => (hD k (p + s) ρ x).1 Y hY.1
  have hu' : ∀ X ∈ u', inLieP k (p + s) ρ X := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact hcjP _ Y (hu Y hY)
  have hv' : ∀ X ∈ v', inLieP k (p + s) ρ X := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact hcjP _ Y (hv Y hY)
  have hwl : ∀ x ∈ wL u' ++ wR v', B.inLie k (p + s + ρ) x.2 := by
    intro x hx
    simp only [List.mem_append, wL, wR, List.mem_map] at hx
    rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu' X hX).1
    · exact (hv' X hX).1
  have hHeq : H = Dw (wL u' ++ wR v') F₁ := dLR_eq _ _ _
  have hg0 : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) :=
    (hZS hM hR k p s ρ σ d hd E F₁ Q hStar.1 ξ Z γ hZdet hγ).1
  have hB₁ : 0 ≤ B₁ := by
    have h0 := hStar.2.2 [] [] (by simp [unitP]) (by simp [unitP]) (by simp) _ hg0
    exact le_trans (mul_nonneg (Real.rpow_nonneg (top_gN_nonneg _) _) (norm_nonneg _)) h0
  have hC0 : 0 ≤ (∑ q ∈ Finset.range (Q + 1), max (Cz q) 0) * C1 ^ Q :=
    mul_nonneg (Finset.sum_nonneg fun q _ => le_max_right _ _) (pow_nonneg (le_trans zero_le_one hC1ge) _)
  by_cases hKg : ‖DjU k (p + s) ρ (gaXi k ρ σ d ξ Z γ)‖ ∈ K
  · obtain ⟨hg1, hRn1, hRn2, -⟩ := hCS ξ Z γ hγ hKg
    set g0 := gaXi k ρ σ d ξ Z γ with hg0def
    set X0 := B.gN g0 with hX0def
    have hX0pos : 0 < X0 := lt_of_lt_of_le zero_lt_one hg1
    have hX0nn : 0 ≤ X0 := hX0pos.le
    have hCkH : B.CkOn (q : ℕ∞) (B.GV k (p + s + ρ)) H := by
      rw [hHeq]
      apply CkOn_Dw hwl
      apply sCkOn_mono _ hStar.1
      have hl : q + (u.length + v.length) ≤ Q := by omega
      simp only [List.length_append, wL, wR, List.length_map, u', v']
      exact_mod_cast hl
    let β : ℝ := B₁ * X0 ^ (-A₁) * ((u'.map lsz).prod * (v'.map lsz).prod)
    have hw : ∀ w : List (B.Mat k (p + s + ρ)), (∀ X ∈ w, inLieP k (p + s) ρ X) → w.length ≤ q →
        ‖B.Rw w H g0‖ ≤ β * (w.map lsz).prod := by
      intro w hwP hwl'
      have hcomm := hC k (p + s + ρ) E F₁ Q hStar.1 u' v' w (fun X hX => (hu' X hX).1)
        (fun X hX => (hv' X hX).1) (fun X hX => (hwP X hX).1)
        (by simp only [List.length_map, u', v']; omega) g0 hg0
      rw [hcomm]
      have hsc := hS k (p + s) ρ E F₁ A₁ Q B₁ K hStar u' (w ++ v') hu'
        (by
          intro X hX
          rcases List.mem_append.1 hX with h | h
          · exact hwP X h
          · exact hv' X h)
        (by simp only [List.length_append, List.length_map, u', v']; omega) g0 hg0
      have hprod : ((u' ++ (w ++ v')).map lsz).prod =
          (u'.map lsz).prod * ((w.map lsz).prod * (v'.map lsz).prod) := by
        simp only [List.map_append, List.prod_append]
      rw [hprod] at hsc
      have hpowpos : 0 < X0 ^ A₁ := Real.rpow_pos_of_pos hX0pos _
      have hle : ‖B.dLR u' (w ++ v') F₁ g0‖ ≤
          B₁ * ((u'.map lsz).prod * ((w.map lsz).prod * (v'.map lsz).prod)) / X0 ^ A₁ := by
        rw [le_div_iff₀ hpowpos]
        linarith [hsc]
      calc ‖B.dLR u' (w ++ v') F₁ g0‖
          ≤ B₁ * ((u'.map lsz).prod * ((w.map lsz).prod * (v'.map lsz).prod)) / X0 ^ A₁ := hle
        _ = β * (w.map lsz).prod := by
          simp only [β]
          rw [Real.rpow_neg hX0nn]
          field_simp
    obtain ⟨hcd, hbd⟩ := hCz q E H β hCkH ξ Z γ hZdet hγ hKg hw
    refine ⟨hcd, le_trans hbd ?_⟩
    have hlet : ∀ x : RC k (p + s) ρ, B.gN (Rn k (p + s) ρ x) ≤ CS * X0 ^ (p + s) →
        ∀ Y, B.unitLie k ρ Y → lsz (cj k (p + s) ρ x Y) ≤ C1 * X0 ^ (2 * (p + s + ρ)) := by
      intro x hx Y hY
      have h1 := hCL x Y hY.2
      have hn0 : 0 ≤ B.gN (Rn k (p + s) ρ x) := top_gN_nonneg _
      have hl1 := top_lsz_ge_one (cj k (p + s) ρ x Y)
      have hCL0 : 0 ≤ CL := by nlinarith [sq_nonneg (B.gN (Rn k (p + s) ρ x))]
      have hsq : B.gN (Rn k (p + s) ρ x) ^ 2 ≤ (CS * X0 ^ (p + s)) ^ 2 := pow_le_pow_left₀ hn0 hx 2
      calc lsz (cj k (p + s) ρ x Y) ≤ CL * B.gN (Rn k (p + s) ρ x) ^ 2 := h1
        _ ≤ CL * (CS * X0 ^ (p + s)) ^ 2 := mul_le_mul_of_nonneg_left hsq hCL0
        _ = (CL * CS ^ 2) * X0 ^ (2 * (p + s)) := by ring
        _ ≤ C1 * X0 ^ (2 * (p + s + ρ)) :=
          mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hg1 (by omega)) (pow_nonneg hX0nn _)
            (le_trans zero_le_one hC1ge)
    have hc : 0 ≤ C1 * X0 ^ (2 * (p + s + ρ)) :=
      mul_nonneg (le_trans zero_le_one hC1ge) (pow_nonneg hX0nn _)
    have hu'b : (u'.map lsz).prod ≤ (C1 * X0 ^ (2 * (p + s + ρ))) ^ u.length := by
      have h := top_prod_map_le u' lsz (C1 * X0 ^ (2 * (p + s + ρ)))
        (fun X hX => by
          obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
          exact ⟨le_trans zero_le_one (top_lsz_ge_one _), hlet _ hRn1 Y (hu Y hY)⟩) hc
      simpa only [List.length_map, u'] using h
    have hv'b : (v'.map lsz).prod ≤ (C1 * X0 ^ (2 * (p + s + ρ))) ^ v.length := by
      have h := top_prod_map_le v' lsz (C1 * X0 ^ (2 * (p + s + ρ)))
        (fun X hX => by
          obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
          exact ⟨le_trans zero_le_one (top_lsz_ge_one _), hlet _ hRn2 Y (hv Y hY)⟩) hc
      simpa only [List.length_map, v'] using h
    have hβ : β ≤ B₁ * X0 ^ (-A₁) * (C1 ^ Q * X0 ^ (2 * (p + s + ρ) * (u.length + v.length))) := by
      have h1 : (u'.map lsz).prod * (v'.map lsz).prod ≤
          (C1 * X0 ^ (2 * (p + s + ρ))) ^ (u.length + v.length) := by
        rw [pow_add]
        exact mul_le_mul hu'b hv'b (top_prod_lsz_nonneg _) (pow_nonneg hc _)
      have h2 : (C1 * X0 ^ (2 * (p + s + ρ))) ^ (u.length + v.length) ≤
          C1 ^ Q * X0 ^ (2 * (p + s + ρ) * (u.length + v.length)) := by
        rw [mul_pow, ← pow_mul]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1ge (by omega)) (pow_nonneg hX0nn _)
      exact mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hB₁ (Real.rpow_nonneg hX0nn _))
    have hβ0 : 0 ≤ β :=
      mul_nonneg (mul_nonneg hB₁ (Real.rpow_nonneg hX0nn _))
        (mul_nonneg (top_prod_lsz_nonneg _) (top_prod_lsz_nonneg _))
    have hX5 : 0 ≤ X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) := Real.rpow_nonneg hX0nn _
    have hexp : X0 ^ (-A₁ + 5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ) +
          2 * ((p + s + ρ : ℕ) : ℝ) * ((u.length + v.length : ℕ) : ℝ)) =
        X0 ^ (-A₁) * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) *
          X0 ^ (2 * (p + s + ρ) * (u.length + v.length)) := by
      rw [Real.rpow_add hX0pos, Real.rpow_add hX0pos, ← Real.rpow_natCast]
      congr 2
      push_cast
      ring
    have hmax : max (Cz q) 0 ≤ ∑ q ∈ Finset.range (Q + 1), max (Cz q) 0 :=
      Finset.single_le_sum (f := fun q => max (Cz q) 0) (fun i _ => le_max_right _ _)
        (Finset.mem_range.mpr (by omega))
    calc Cz q * β * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ))
        ≤ max (Cz q) 0 * β * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hβ0) hX5
      _ ≤ max (Cz q) 0 * (B₁ * X0 ^ (-A₁) * (C1 ^ Q * X0 ^ (2 * (p + s + ρ) * (u.length + v.length)))) *
            X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ (le_max_right _ _)) hX5
      _ = max (Cz q) 0 * C1 ^ Q * B₁ * (X0 ^ (-A₁) * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) *
            X0 ^ (2 * (p + s + ρ) * (u.length + v.length))) := by ring
      _ = max (Cz q) 0 * C1 ^ Q * B₁ * X0 ^ (-A₁ + 5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ) +
            2 * ((p + s + ρ : ℕ) : ℝ) * ((u.length + v.length : ℕ) : ℝ)) := by rw [hexp]
      _ ≤ (∑ q ∈ Finset.range (Q + 1), max (Cz q) 0) * C1 ^ Q * B₁ * X0 ^ (-A₁ +
            5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ) + 2 * ((p + s + ρ : ℕ) : ℝ) * ((u.length + v.length : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX0nn _)
          apply mul_le_mul_of_nonneg_right _ hB₁
          exact mul_le_mul_of_nonneg_right hmax (pow_nonneg (le_trans zero_le_one hC1ge) _)
  · have hcont : Continuous fun g : B.Mat k (p + s + ρ) => ‖DjU k (p + s) ρ g‖ := by
      have hZc : Continuous fun g : B.Mat k (p + s + ρ) => Zh k (p + s) ρ g :=
        continuous_pi fun a => continuous_pi fun b => (continuous_apply _).comp (continuous_apply _)
      exact hZc.matrix_det.norm
    have hOopen : IsOpen {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K} :=
      hK.isClosed.isOpen_compl.preimage hcont
    have hF0 : ∀ g ∈ B.GV k (p + s + ρ), g ∈ {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K} →
        F₁ g = 0 := by
      intro g hg hgO
      by_contra hne
      exact hgO (hStar.2.1 g hg hne)
    have hH0 : ∀ g ∈ B.GV k (p + s + ρ), g ∈ {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K} →
        H g = 0 := by
      intro g hg hgO
      rw [hHeq]
      exact Dw_vanish hOopen hwl hF0 g hg hgO
    obtain ⟨hcd, hz⟩ := hO hM hR k p s ρ σ d hd E H _ hOopen hH0 ξ Z γ hZdet hγ hKg q
    refine ⟨hcd, ?_⟩
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg hC0 hB₁) (Real.rpow_nonneg (top_gN_nonneg _) _)

end PI.UnitaryGroupMassFormula.UsCost

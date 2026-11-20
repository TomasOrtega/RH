import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.ContinuousOnOrbit

open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace CompanionTheory.Bmu

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Proceed by induction on `W with`. Consider the case `nil => simp`. Consider the case `cons X W ih`. Rewrite using `[List.map_cons, List.prod_cons, List.length_cons, pow_succ']`. Establish `h0 : 0 ≤ (W.map fun X => ‖X‖).prod` using `List.prod_nonneg fun x hx => by`.

Take `⟨Y, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `norm_nonneg _`. Conclude with `mul_le_mul (h X List.mem_cons_self) (ih fun Y hY => h Y (List.mem_cons_of_mem _ hY)) h0 ((norm_nonneg X).trans (h X List.mem_cons_self))`.
-/
theorem prod_norm_le {n : ℕ} (W : List (Mat n)) {a : ℝ} (h : ∀ X ∈ W, ‖X‖ ≤ a) :
    (W.map fun X => ‖X‖).prod ≤ a ^ W.length := by
  induction W with
  | nil => simp
  | cons X W ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    have h0 : 0 ≤ (W.map fun X => ‖X‖).prod := List.prod_nonneg fun x hx => by
      obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    exact mul_le_mul (h X List.mem_cons_self) (ih fun Y hY => h Y (List.mem_cons_of_mem _ hY)) h0
      ((norm_nonneg X).trans (h X List.mem_cons_self))

/- English proof (translation)
Introduce `n Hm H _ _ _ σ hU V _ _ _ B hB e Q hQ C m hC hQB C₀ c w hw`. Take `⟨N, Wd, β, hWd, hβ⟩` from `hF n Hm H σ hU V B hB`. Take `⟨Cw, hCw, hW⟩` from `hWB n Hm H σ hU w hw (m + c * m)`. Use `set A : ℝ := max 1 C₀ with hA`. Establish `hA1 : 1 ≤ A` using `le_max_left _ _`.

Use `⟨C * (Cw * A ^ (m + c * m)), fun g hg M hM hconj hcase => ?_⟩` and prove the remaining obligations. Establish `hMc : 1 ≤ M ^ c` using `one_le_pow₀ hM`. Establish `main : ∀ R : List (Mat n), LieWd Hm R → R.length ≤ c * m → (∀ X ∈ R, ‖X‖ ≤ A) → ‖B (σ g (dsW σ R w))‖ ≤ C * (Cw * A ^ (m + c * m) * M ^ (c * m))`. Introduce `R hR hRl hRn`. Establish `hu : IsSm (UH Hm) σ (dsW σ R w)` using `hw.dsW hU.rep hR.lieW`.

Use `hQB _ (hu.apply hU.rep hg) _ fun P hP => ?_` and prove the remaining obligations. Establish `hPL : LieWd Hm (P.map Q)` using `fun X hX => by`. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hX`. Conclude with `hQ i`. Take `⟨h1, h2⟩` from `hAd n Hm H σ hU g hg _ hPL`.

Rewrite using `[h2 _ hu, hU.iso g hg]`. Use `set P' := (P.map Q).map fun X => g⁻¹ * X * g with hP'`. Establish `hl : P'.length = P.length` using `by simp [hP']`. Establish `e1 : dsW σ P' (dsW σ R w) = dsW σ (P' ++ R) w` using `by unfold dsW; rw [List.foldr_append]`. Rewrite using `[e1]`.

Use `(hW (P' ++ R) (fun X hX => (List.mem_append.1 hX).elim (h1 X) (hR X)) (by rw [List.length_append, hl]; omega)).trans ?_` and prove the remaining obligations. Rewrite using `[List.map_append, List.prod_append, mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ hCw` and prove the remaining obligations. Establish `b1 : (P'.map fun X => ‖X‖).prod ≤ (A * M ^ c) ^ m`. Use `(prod_norm_le P' (a := A * M ^ c) fun X hX => ?_).trans ?_` and prove the remaining obligations.

Take `⟨Y, hY, rfl⟩` from `List.mem_map.1 hX`. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hY`. Conclude with `(hconj i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))`. Conclude with `pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hA1 hMc) (hl ▸ hP)`. Establish `b2 : (R.map fun X => ‖X‖).prod ≤ A ^ (c * m)` using `(prod_norm_le R hRn).trans (pow_le_pow_right₀ hA1 hRl)`.

Establish `h0 : 0 ≤ (R.map fun X => ‖X‖).prod` using `List.prod_nonneg fun x hx => by`. Take `⟨Y, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Break down `hcase with h1 | ⟨Y, lam, hY, hYn, hlam, hχ⟩` into its components or cases.

Use `main [] (fun _ h => absurd h List.not_mem_nil) (Nat.zero_le _) (fun _ h => absurd h List.not_mem_nil)` as an intermediate fact. Rewrite `this` using `[h1, one_pow, mul_one]`. Conclude with `this`. Establish `step : ∀ u, IsSm (UH Hm) σ u → B (σ g (ds σ Y u)) = (Complex.I * lam) • B (σ g u)`. Introduce `u hu`.

Establish `hds : IsSm (UH Hm) σ (ds σ Y u)` using `hu.dsW hU.rep (W := [Y]) (LieWd.lieW fun X hX => by rw [List.mem_singleton.1 hX]; exact hY)`. Establish `d1 : HasDerivAt (fun τ : ℝ => ∑ i, β i (dsW σ (Wd i) (σ (g * ex Y τ) u))) (∑ i, β i (dsW σ (Wd i) (σ g (ds σ Y u)))) 0` using `HasDerivAt.fun_sum fun i _ => ((β i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hDer n Hm H σ hU _ (hWd i) g hg Y hY u hu)`. Establish `e1 : (fun τ : ℝ => ∑ i, β i (dsW σ (Wd i) (σ (g * ex Y τ) u))) = fun τ : ℝ => Complex.exp (Complex.I * (lam * τ : ℝ)) • B (σ g u)`. Use function extensionality and compare the values at `τ`. Rewrite using `[← hβ _ (hu.apply hU.rep (hU.rep.mul_mem _ hg _ (ex_mem_of_lie hY τ))), hχ τ u hu]`.

Establish `d2 : HasDerivAt (fun τ : ℝ => Complex.exp (Complex.I * (lam * τ : ℝ))) (Complex.I * lam) 0`. Establish `h1 : HasDerivAt (fun τ : ℝ => Complex.I * ((lam * τ : ℝ) : ℂ)) (Complex.I * lam) 0`. Use `(((hasDerivAt_id (0 : ℝ)).const_mul lam).ofReal_comp).const_mul Complex.I` as an intermediate fact. Simplify using `using this`. Simplify using `using h1.cexp`.

Rewrite `d1` using `[e1, ← hβ _ (hds.apply hU.rep hg)]`. Conclude with `d1.unique (d2.smul_const _)`. Establish `iter : ∀ j : ℕ, B (σ g (dsW σ (List.replicate j Y) w)) = (Complex.I * lam) ^ j • B (σ g w)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => simp [dsW]`. Consider the case `succ j ih`. Establish `hu : IsSm (UH Hm) σ (dsW σ (List.replicate j Y) w)` using `hw.dsW hU.rep (LieWd.lieW fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hY)`. Rewrite using `[List.replicate_succ, dsW_cons, step _ hu, ih, smul_smul, pow_succ']`. Establish `h` using `main (List.replicate (c * m) Y) (fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hY) (by simp) (fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hYn.trans (le_max_right _ _))`.

Rewrite `h` using `[iter, norm_smul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]`. Establish `hMp : 0 < M ^ (c * m)` using `by positivity`. Establish `h2 : M ^ (c * m) * ‖B (σ g w)‖ ≤ |lam| ^ (c * m) * ‖B (σ g w)‖` using `mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hlam _) (norm_nonneg _)`. Use `le_of_mul_le_mul_left (h2.trans (h.trans_eq ?_)) hMp` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem absBound_of (hF : Factor) (hAd : DsAd) (hDer : DsDer) (hWB : WordBd) : AbsBound := by
  intro n Hm H _ _ _ σ hU V _ _ _ B hB e Q hQ C m hC hQB C₀ c w hw
  obtain ⟨N, Wd, β, hWd, hβ⟩ := hF n Hm H σ hU V B hB
  obtain ⟨Cw, hCw, hW⟩ := hWB n Hm H σ hU w hw (m + c * m)
  set A : ℝ := max 1 C₀ with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  refine ⟨C * (Cw * A ^ (m + c * m)), fun g hg M hM hconj hcase => ?_⟩
  have hMc : 1 ≤ M ^ c := one_le_pow₀ hM

  have main : ∀ R : List (Mat n), LieWd Hm R → R.length ≤ c * m → (∀ X ∈ R, ‖X‖ ≤ A) →
      ‖B (σ g (dsW σ R w))‖ ≤ C * (Cw * A ^ (m + c * m) * M ^ (c * m)) := by
    intro R hR hRl hRn
    have hu : IsSm (UH Hm) σ (dsW σ R w) := hw.dsW hU.rep hR.lieW
    refine hQB _ (hu.apply hU.rep hg) _ fun P hP => ?_
    have hPL : LieWd Hm (P.map Q) := fun X hX => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hX; exact hQ i
    obtain ⟨h1, h2⟩ := hAd n Hm H σ hU g hg _ hPL
    rw [h2 _ hu, hU.iso g hg]
    set P' := (P.map Q).map fun X => g⁻¹ * X * g with hP'
    have hl : P'.length = P.length := by simp [hP']
    have e1 : dsW σ P' (dsW σ R w) = dsW σ (P' ++ R) w := by unfold dsW; rw [List.foldr_append]
    rw [e1]
    refine (hW (P' ++ R) (fun X hX => (List.mem_append.1 hX).elim (h1 X) (hR X))
      (by rw [List.length_append, hl]; omega)).trans ?_
    rw [List.map_append, List.prod_append, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hCw
    have b1 : (P'.map fun X => ‖X‖).prod ≤ (A * M ^ c) ^ m := by
      refine (prod_norm_le P' (a := A * M ^ c) fun X hX => ?_).trans ?_
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hY
        exact (hconj i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      · exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hA1 hMc) (hl ▸ hP)
    have b2 : (R.map fun X => ‖X‖).prod ≤ A ^ (c * m) := (prod_norm_le R hRn).trans (pow_le_pow_right₀ hA1 hRl)
    have h0 : 0 ≤ (R.map fun X => ‖X‖).prod := List.prod_nonneg fun x hx => by
      obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    calc _ ≤ (A * M ^ c) ^ m * A ^ (c * m) := mul_le_mul b1 b2 h0 (by positivity)
      _ = A ^ (m + c * m) * M ^ (c * m) := by rw [mul_pow, ← pow_mul, pow_add]; ring
  rcases hcase with h1 | ⟨Y, lam, hY, hYn, hlam, hχ⟩
  · have := main [] (fun _ h => absurd h List.not_mem_nil) (Nat.zero_le _) (fun _ h => absurd h List.not_mem_nil)
    rw [h1, one_pow, mul_one] at this
    exact this
  · have step : ∀ u, IsSm (UH Hm) σ u → B (σ g (ds σ Y u)) = (Complex.I * lam) • B (σ g u) := by
      intro u hu
      have hds : IsSm (UH Hm) σ (ds σ Y u) :=
        hu.dsW hU.rep (W := [Y]) (LieWd.lieW fun X hX => by rw [List.mem_singleton.1 hX]; exact hY)
      have d1 : HasDerivAt (fun τ : ℝ => ∑ i, β i (dsW σ (Wd i) (σ (g * ex Y τ) u)))
          (∑ i, β i (dsW σ (Wd i) (σ g (ds σ Y u)))) 0 :=
        HasDerivAt.fun_sum fun i _ => ((β i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
          (hDer n Hm H σ hU _ (hWd i) g hg Y hY u hu)
      have e1 : (fun τ : ℝ => ∑ i, β i (dsW σ (Wd i) (σ (g * ex Y τ) u))) =
          fun τ : ℝ => Complex.exp (Complex.I * (lam * τ : ℝ)) • B (σ g u) := by
        funext τ
        rw [← hβ _ (hu.apply hU.rep (hU.rep.mul_mem _ hg _ (ex_mem_of_lie hY τ))), hχ τ u hu]
      have d2 : HasDerivAt (fun τ : ℝ => Complex.exp (Complex.I * (lam * τ : ℝ))) (Complex.I * lam) 0 := by
        have h1 : HasDerivAt (fun τ : ℝ => Complex.I * ((lam * τ : ℝ) : ℂ)) (Complex.I * lam) 0 := by
          have := (((hasDerivAt_id (0 : ℝ)).const_mul lam).ofReal_comp).const_mul Complex.I
          simpa using this
        simpa using h1.cexp
      rw [e1, ← hβ _ (hds.apply hU.rep hg)] at d1
      exact d1.unique (d2.smul_const _)
    have iter : ∀ j : ℕ, B (σ g (dsW σ (List.replicate j Y) w)) = (Complex.I * lam) ^ j • B (σ g w) := by
      intro j
      induction j with
      | zero => simp [dsW]
      | succ j ih =>
        have hu : IsSm (UH Hm) σ (dsW σ (List.replicate j Y) w) :=
          hw.dsW hU.rep (LieWd.lieW fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hY)
        rw [List.replicate_succ, dsW_cons, step _ hu, ih, smul_smul, pow_succ']
    have h := main (List.replicate (c * m) Y) (fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hY)
      (by simp) (fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hYn.trans (le_max_right _ _))
    rw [iter, norm_smul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h
    have hMp : 0 < M ^ (c * m) := by positivity
    have h2 : M ^ (c * m) * ‖B (σ g w)‖ ≤ |lam| ^ (c * m) * ‖B (σ g w)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hlam _) (norm_nonneg _)
    refine le_of_mul_le_mul_left (h2.trans (h.trans_eq ?_)) hMp
    ring

end CompanionTheory.Bmu

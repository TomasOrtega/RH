import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

variable {F : Type} [Field F]

namespace UpperTheory.Esk.MinkowskiHeightLemmas

/- English proof (translation)
The claim follows from `|(Matrix.GeneralLinearGroup.map σ γ • z).1.im| / ‖(σ (s 0) : ℂ) * (Matrix.GeneralLinearGroup.map σ γ • z).1 + (σ (s 1) : ℂ)‖ ^ 2 = |σ γ.val.det| * (|z.1.im| / ‖(σ ((s ᵥ* γ.val) 0) : ℂ) * z.1 + (σ ((s ᵥ* γ.val) 1) : ℂ)‖ ^ 2) := by set g := Matrix.GeneralLinearGroup.map σ γ have hd …`.
-/
private theorem term (σ : F →+* ℝ) (γ : GL (Fin 2) F) (s : Fin 2 → F) (z : P) :
    |(Matrix.GeneralLinearGroup.map σ γ • z).1.im| /
      ‖(σ (s 0) : ℂ) * (Matrix.GeneralLinearGroup.map σ γ • z).1 + (σ (s 1) : ℂ)‖ ^ 2 =
    |σ γ.val.det| * (|z.1.im| / ‖(σ ((s ᵥ* γ.val) 0) : ℂ) * z.1 + (σ ((s ᵥ* γ.val) 1) : ℂ)‖ ^ 2) := by
  set g := Matrix.GeneralLinearGroup.map σ γ
  have hd : den g z.1 ≠ 0 := den_ne g z.2
  have hdet : g.val.det = σ γ.val.det := by
    rw [det_eq, Matrix.det_fin_two]; simp [g]
  have e : (σ (s 0) : ℂ) * (g • z).1 + (σ (s 1) : ℂ) =
      ((σ ((s ᵥ* γ.val) 0) : ℂ) * z.1 + (σ ((s ᵥ* γ.val) 1) : ℂ)) / den g z.1 := by
    rw [coe_smul, eq_div_iff hd, add_mul, mul_assoc, div_mul_cancel₀ _ hd]
    simp [g, num, den, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  rw [e, coe_smul, im_div, hdet, norm_div, div_pow, Complex.normSq_eq_norm_sq, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg ‖den g z.1‖)]
  have hn : ‖den g z.1‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hd)
  by_cases h0 : ‖(σ ((s ᵥ* γ.val) 0) : ℂ) * z.1 + (σ ((s ᵥ* γ.val) 1) : ℂ)‖ ^ 2 = 0
  · rw [h0]; simp
  · field_simp

/- English proof (translation)
Simplify using `only [Dat.Ht, Dat.act, Dat.r, term, Finset.prod_mul_distrib, ← hrat]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ht_act {I Gf : Type} [Group Gf] [Fintype I] (D : Dat F I Gf) (s : Fin 2 → F) (γ : GL (Fin 2) F)
    (z : X I) (x : Gf) (hrat : D.hf s (D.j γ * x) * ∏ v, |D.σ v γ.val.det| = D.hf (s ᵥ* γ.val) x) :
    D.Ht (s ᵥ* γ.val) z x = D.Ht s (D.act γ z) (D.j γ * x) := by
  simp only [Dat.Ht, Dat.act, Dat.r, term, Finset.prod_mul_distrib, ← hrat]
  ring

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg Complex.im h`. Simplify using `[hw] at h1`. Rewrite `h` using `[h1]`. Simplify using `at h`.

Apply the tactic sequence `exact hs (funext fun i => by fin_cases i <;> simp [h1, h])`.
-/
private theorem row_ne {σ : F →+* ℝ} {s : Fin 2 → F} (hs : s ≠ 0) {w : ℂ} (hw : w.im ≠ 0) :
    (σ (s 0) : ℂ) * w + (σ (s 1) : ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  simp [hw] at h1
  rw [h1] at h
  simp at h
  exact hs (funext fun i => by fin_cases i <;> simp [h1, h])

/- English proof (translation)
Establish `e : (σ (((N : F) • s) 0) : ℂ) * w + (σ (((N : F) • s) 1) : ℂ) = (N : ℂ) * ((σ (s 0) : ℂ) * w + (σ (s 1) : ℂ))`. Simplify using `[Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hY` using `row_ne (σ := σ) hs hw`. Establish `hY2 : 0 < ‖(σ (s 0) : ℂ) * w + (σ (s 1) : ℂ)‖ ^ 2` using `by positivity`.

Establish `hN2 : (0 : ℝ) < (N : ℝ) ^ 2` using `by positivity`. Rewrite using `[e, norm_mul, mul_pow, Complex.norm_natCast, div_le_div_iff₀ (by positivity) (by positivity)]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hb hN2.le]`.
-/
private theorem arch_le {σ : F →+* ℝ} {N : ℕ} (hN : N ≠ 0) {C : ℝ} (hC : 0 < C) {s : Fin 2 → F} (hs : s ≠ 0)
    {w : ℂ} (hw : w.im ≠ 0) (hb : ‖(σ (s 0) : ℂ) * w + (σ (s 1) : ℂ)‖ ^ 2 ≤ C * |w.im|) :
    1 / ((N : ℝ) ^ 2 * C) ≤ |w.im| / ‖(σ (((N : F) • s) 0) : ℂ) * w + (σ (((N : F) • s) 1) : ℂ)‖ ^ 2 := by
  have e : (σ (((N : F) • s) 0) : ℂ) * w + (σ (((N : F) • s) 1) : ℂ) = (N : ℂ) * ((σ (s 0) : ℂ) * w + (σ (s 1) : ℂ)) := by
    simp [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]; ring
  have hY := row_ne (σ := σ) hs hw
  have hY2 : 0 < ‖(σ (s 0) : ℂ) * w + (σ (s 1) : ℂ)‖ ^ 2 := by positivity
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  rw [e, norm_mul, mul_pow, Complex.norm_natCast, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hb hN2.le]

/- English proof (translation)
Distinguish the cases in `hS : S.Nonempty`. Take `⟨a, -, ha⟩` from `S.exists_min_image f hS`. Conclude with `⟨f a, hf a, ha⟩`. Conclude with `⟨1, one_pos, fun a ha => absurd ⟨a, ha⟩ hS⟩`.
-/
private theorem fin_min {α : Type} (S : Finset α) (f : α → ℝ) (hf : ∀ a, 0 < f a) : ∃ c : ℝ, 0 < c ∧ ∀ a ∈ S, c ≤ f a := by
  by_cases hS : S.Nonempty
  · obtain ⟨a, -, ha⟩ := S.exists_min_image f hS
    exact ⟨f a, hf a, ha⟩
  · exact ⟨1, one_pos, fun a ha => absurd ⟨a, ha⟩ hS⟩

/- English proof (translation)
Take `⟨t, k, hk, hrow⟩` from `(hRow F ((N : F) • s0) x).1 hs`. Rewrite using `[(hRow F _ x).2 t k hk hrow]`. Establish `hM` using `hMem F`. Establish `hmem : ∀ i, rowF ((N : F) • s0) x i ∈ Ohat F` using `fun i => by`. Simplify using `only [rowF, Matrix.vecMul, dotProduct]`.

Use `Subring.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `e : algebraMap F (Af F) (((N : F) • s0) j) * x.val j i = algebraMap F (Af F) (s0 j) * ((N : Af F) * x.val j i)`. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Subring.mul_mem _ ((hM.2.2.2.2.2.1 (s0 j)).1 (hint j)) (hNx j i)`. Combine the equalities or inequalities in the displayed calculation. Establish `hv : ∀ i, Valued.v (pLoc F w (rowF ((N : F) • s0) x i)) ≤ 1` using `fun i => (hM.2.1 _).1 (hmem i) w`. Take `⟨-, hmax⟩` from `hM.2.2.2.2.1 k hk w`. Rewrite using `[Units.val_one, map_one, map_one]`.

Apply the tactic sequence `rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with h | h <;> rw [h] at hmax`. Use `hv 0` as an intermediate fact. Rewrite `this` using `[hrow 0, map_mul, map_mul, hmax, mul_one]`. Then use the resulting hypothesis. Use `hv 1` as an intermediate fact. Rewrite using `[hrow 1, map_mul, map_mul, hmax, mul_one] at this)` and apply the resulting hypothesis.

Use `_ = 1 := by simp [absF]`.
-/
private theorem nF_le (hMem : AMem) (hMono : AMono) (hRow : ARow) [NumberField F] {x : GF F} {N : ℕ}
    (hNx : ∀ i j, (N : Af F) * x.val i j ∈ Ohat F) {s0 : Fin 2 → F} (hint : ∀ i, IsIntegral ℤ (s0 i))
    (hs : (N : F) • s0 ≠ 0) : nF ((N : F) • s0) x ≤ 1 := by
  obtain ⟨t, k, hk, hrow⟩ := (hRow F ((N : F) • s0) x).1 hs
  rw [(hRow F _ x).2 t k hk hrow]
  have hM := hMem F
  have hmem : ∀ i, rowF ((N : F) • s0) x i ∈ Ohat F := fun i => by
    simp only [rowF, Matrix.vecMul, dotProduct]
    refine Subring.sum_mem _ fun j _ => ?_
    have e : algebraMap F (Af F) (((N : F) • s0) j) * x.val j i = algebraMap F (Af F) (s0 j) * ((N : Af F) * x.val j i) := by
      rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]; ring
    rw [e]
    exact Subring.mul_mem _ ((hM.2.2.2.2.2.1 (s0 j)).1 (hint j)) (hNx j i)
  calc absF t ≤ absF 1 := hMono F t 1 (fun w => by
        have hv : ∀ i, Valued.v (pLoc F w (rowF ((N : F) • s0) x i)) ≤ 1 := fun i => (hM.2.1 _).1 (hmem i) w
        obtain ⟨-, hmax⟩ := hM.2.2.2.2.1 k hk w
        rw [Units.val_one, map_one, map_one]
        rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with h | h <;> rw [h] at hmax
        · have := hv 0
          rwa [hrow 0, map_mul, map_mul, hmax, mul_one] at this
        · have := hv 1
          rwa [hrow 1, map_mul, map_mul, hmax, mul_one] at this)
    _ = 1 := by simp [absF]

/- English proof (translation)
Take `⟨C, hC, hmink⟩` from `hMink F`. Take `⟨N, hN, hNx⟩` from `(hMem F).2.2.2.2.2.2.1 x`. Establish `hpos : ∀ s : Fin 2 → F, s ≠ 0 → 0 < absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2` using `fun s hs => (hHt F c hc χ).1 s hs x`. Establish `ha : 0 < absF (Matrix.GeneralLinearGroup.det x)`. Assume the negation of the conclusion as `h`.

Use `replace h := not_lt.1 h`. Conclude with `(hpos ![1, 0] (by intro h; simpa using congrFun h 0)).not_ge (div_nonpos_of_nonpos_of_nonneg h (sq_nonneg _))`. Use `⟨absF (Matrix.GeneralLinearGroup.det x) * (1 / ((N : ℝ) ^ 2 * C)) ^ Fintype.card (InfinitePlace F), by positivity, fun z => ?_⟩` and prove the remaining obligations. Take `⟨s0, hs0, hint, hb⟩` from `hmink (fun v => (z v).1) (fun v => (z v).2)`. Establish `hs : (N : F) • s0 ≠ 0` using `smul_ne_zero (Nat.cast_ne_zero.2 hN) hs0`.

Use `⟨_, hs, ?_⟩` and prove the remaining obligations. Establish `hn` using `nF_le hMem hMono hRow hNx hint hs`. Establish `hn0 : 0 ≤ nF ((N : F) • s0) x` using `finprod_nonneg fun w => (norm_nonneg _).trans (le_max_left _ _)`. Establish `hp` using `hpos _ hs`. Establish `hfin : absF (Matrix.GeneralLinearGroup.det x) ≤ absF (Matrix.GeneralLinearGroup.det x) / nF ((N : F) • s0) x ^ 2`.

Establish `h2 : 0 < nF ((N : F) • s0) x ^ 2`. Break down `(pow_nonneg hn0 2).lt_or_eq with h | h` into its components or cases. Conclude with `h`. Rewrite `hp` using `[← h, div_zero]`. Conclude with `absurd hp (lt_irrefl 0)`.

Rewrite using `[le_div_iff₀ h2]`. Use polynomial arithmetic with `[pow_le_one₀ hn0 hn (n := 2)]`. Establish `harch : (1 / ((N : ℝ) ^ 2 * C)) ^ Fintype.card (InfinitePlace F) ≤ ∏ v, |(z v).1.im| / ‖((mkDat c χ).σ v (((N : F) • s0) 0) : ℂ) * (z v).1 + ((mkDat c χ).σ v (((N : F) • s0) 1) : ℂ)‖ ^ 2`. Rewrite using `[← Finset.card_univ, ← Finset.prod_const]`. Conclude with `Finset.prod_le_prod (fun _ _ => by positivity) fun v _ => arch_le hN hC hs0 (z v).2 (hb v)`.

Establish `hm` using `mul_le_mul harch hfin ha.le (Finset.prod_nonneg fun _ _ => by positivity)`. Unfold `Dat.Ht`. Express the relevant statement in the definitionally equal form `_ ≤ _ * (absF (Matrix.GeneralLinearGroup.det x) / nF ((N : F) • s0) x ^ 2)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem exists_height_lower_bound (hMem : AMem) (hMono : AMono) (hRow : ARow) (hMink : AMink) (hHt : DHt) (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (c : Pl F → ℕ) (hc : {w | c w ≠ 0}.Finite) (χ : Hc c →* ℂˣ) (x : GF F) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ z : X (InfinitePlace F), ∃ s, s ≠ 0 ∧ c₀ ≤ (mkDat c χ).Ht s z x := by
  obtain ⟨C, hC, hmink⟩ := hMink F
  obtain ⟨N, hN, hNx⟩ := (hMem F).2.2.2.2.2.2.1 x
  have hpos : ∀ s : Fin 2 → F, s ≠ 0 → 0 < absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 :=
    fun s hs => (hHt F c hc χ).1 s hs x
  have ha : 0 < absF (Matrix.GeneralLinearGroup.det x) := by
    by_contra h
    replace h := not_lt.1 h
    exact (hpos ![1, 0] (by intro h; simpa using congrFun h 0)).not_ge (div_nonpos_of_nonpos_of_nonneg h (sq_nonneg _))
  refine ⟨absF (Matrix.GeneralLinearGroup.det x) * (1 / ((N : ℝ) ^ 2 * C)) ^ Fintype.card (InfinitePlace F), by positivity,
    fun z => ?_⟩
  obtain ⟨s0, hs0, hint, hb⟩ := hmink (fun v => (z v).1) (fun v => (z v).2)
  have hs : (N : F) • s0 ≠ 0 := smul_ne_zero (Nat.cast_ne_zero.2 hN) hs0
  refine ⟨_, hs, ?_⟩
  have hn := nF_le hMem hMono hRow hNx hint hs
  have hn0 : 0 ≤ nF ((N : F) • s0) x := finprod_nonneg fun w => (norm_nonneg _).trans (le_max_left _ _)
  have hp := hpos _ hs
  have hfin : absF (Matrix.GeneralLinearGroup.det x) ≤ absF (Matrix.GeneralLinearGroup.det x) / nF ((N : F) • s0) x ^ 2 := by
    have h2 : 0 < nF ((N : F) • s0) x ^ 2 := by
      rcases (pow_nonneg hn0 2).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at hp; exact absurd hp (lt_irrefl 0)
    rw [le_div_iff₀ h2]
    nlinarith [pow_le_one₀ hn0 hn (n := 2)]
  have harch : (1 / ((N : ℝ) ^ 2 * C)) ^ Fintype.card (InfinitePlace F) ≤ ∏ v, |(z v).1.im| /
      ‖((mkDat c χ).σ v (((N : F) • s0) 0) : ℂ) * (z v).1 + ((mkDat c χ).σ v (((N : F) • s0) 1) : ℂ)‖ ^ 2 := by
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by positivity) fun v _ => arch_le hN hC hs0 (z v).2 (hb v)
  have hm := mul_le_mul harch hfin ha.le (Finset.prod_nonneg fun _ _ => by positivity)
  unfold Dat.Ht
  change _ ≤ _ * (absF (Matrix.GeneralLinearGroup.det x) / nF ((N : F) • s0) x ^ 2)
  linarith

end UpperTheory.Esk.MinkowskiHeightLemmas

open UpperTheory.Esk.MinkowskiHeightLemmas in
/- English proof (translation)
Introduce `hMem hMono hRow hBnfH hMink hHt hMul F _ _ _ c hc χ`. Take `⟨S, hS⟩` from `hBnfH F c hc`. Use `choose cf hcf hcz using fun x => exists_height_lower_bound hMem hMono hRow hMink hHt F c hc χ x`. Take `⟨c₀, hc₀, hle⟩` from `fin_min S cf hcf`. Use `⟨c₀, hc₀, fun z x => ?_⟩` and prove the remaining obligations.

Take `⟨b, -, x', hx', h, hh, e⟩` from `hS x`. Take `⟨s', hs', hs'le⟩` from `hcz x' ((mkDat c χ).act b z)`. Use `⟨s' ᵥ* b.val, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hs'` to reduce the goal to its premises.

Use `congrArg (· ᵥ* (b⁻¹ : GL (Fin 2) F).val) h0` as an intermediate fact. Simplify `this` using `[Matrix.vecMul_vecMul]`. Rewrite using `[ht_act _ _ _ _ _ ((hHt F c hc χ).2.1 s' hs' b x)]`. Establish `ej : (mkDat c χ).j b * x = x' * h` using `e`. Establish `hH : h ∈ (mkDat c χ).H` using `Subgroup.mem_sup_left hh`.

Establish `hl` using `(hMul F c hc χ).1 s' hs' x' h hH`. Rewrite using `[ej]`. Unfold `Dat.Ht at hs'le ⊢`. Rewrite using `[hl]`. Conclude with `(hle x' hx').trans hs'le`.
-/
theorem UpperTheory.Esk.dMink : UpperTheory.Esk.AMem → UpperTheory.Esk.AMono → UpperTheory.Esk.ARow → UpperTheory.Esk.ABnfH → UpperTheory.Esk.AMink → UpperTheory.Esk.DHt → UpperTheory.Esk.DMul → UpperTheory.Esk.DMink := by
  intro hMem hMono hRow hBnfH hMink hHt hMul F _ _ _ c hc χ
  obtain ⟨S, hS⟩ := hBnfH F c hc
  choose cf hcf hcz using fun x => exists_height_lower_bound hMem hMono hRow hMink hHt F c hc χ x
  obtain ⟨c₀, hc₀, hle⟩ := fin_min S cf hcf
  refine ⟨c₀, hc₀, fun z x => ?_⟩
  obtain ⟨b, -, x', hx', h, hh, e⟩ := hS x
  obtain ⟨s', hs', hs'le⟩ := hcz x' ((mkDat c χ).act b z)
  refine ⟨s' ᵥ* b.val, ?_, ?_⟩
  · intro h0
    apply hs'
    have := congrArg (· ᵥ* (b⁻¹ : GL (Fin 2) F).val) h0
    simpa [Matrix.vecMul_vecMul] using this
  · rw [ht_act _ _ _ _ _ ((hHt F c hc χ).2.1 s' hs' b x)]
    have ej : (mkDat c χ).j b * x = x' * h := e
    have hH : h ∈ (mkDat c χ).H := Subgroup.mem_sup_left hh
    have hl := (hMul F c hc χ).1 s' hs' x' h hH
    rw [ej]
    unfold Dat.Ht at hs'le ⊢
    rw [hl]
    exact (hle x' hx').trans hs'le

import Formalism.HermitianCurvature.StatementTA

open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace

namespace Formalism.FourierDecayAlt.P.TA2

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `p hp`. Consider the cases of `n with`.

Consider the case `zero`. Simplify using `[PT] at hp; subst hp; exact ⟨by simp [lvl], by simp⟩`. Consider the case `succ n`. Rewrite `hp` using `[PT]`. Simplify using `only [mem_biUnion, mem_attach, true_and, mem_image, Subtype.exists, mem_range] at hp`.

Take `⟨m, hm, h, hh, t, ht, rfl⟩` from `hp`. Establish `h0` using `ih m (by omega) h hh`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `h0.1` as an intermediate fact. Simplify using `only [lvl] at this`.

Simplify using `[lvl, Formalism.FourierDecayAlt.TA.ext, this]`. Use linear arithmetic over natural numbers and integers. Introduce `b hb`. Simplify using `only [Formalism.FourierDecayAlt.TA.ext, List.mem_append, List.mem_singleton] at hb`. Break down `hb with hb | rfl` into its components or cases.

Conclude with `h0.2 b hb`. Conclude with `⟨by simp; omega, hNZ _ _ t ht⟩`.
-/
theorem isPt_PT {E : Type} [Field E] [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n p, p ∈ PT Sg n → IsPt n p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hp
    cases n with
    | zero =>
      simp [PT] at hp; subst hp; exact ⟨by simp [lvl], by simp⟩
    | succ n =>
      rw [PT] at hp
      simp only [mem_biUnion, mem_attach, true_and, mem_image, Subtype.exists, mem_range] at hp
      obtain ⟨m, hm, h, hh, t, ht, rfl⟩ := hp
      have h0 := ih m (by omega) h hh
      refine ⟨?_, ?_⟩
      · have := h0.1
        simp only [lvl] at this
        simp [lvl, Formalism.FourierDecayAlt.TA.ext, this]; omega
      · intro b hb
        simp only [Formalism.FourierDecayAlt.TA.ext, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact h0.2 b hb
        · exact ⟨by simp; omega, hNZ _ _ t ht⟩

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `hh.1` as an intermediate fact. Simplify using `only [lvl] at this`. Simplify using `[lvl, Formalism.FourierDecayAlt.TA.ext, this]`. Use linear arithmetic over natural numbers and integers.

Introduce `b hb`. Simplify using `only [Formalism.FourierDecayAlt.TA.ext, List.mem_append, List.mem_singleton] at hb`. Break down `hb with hb | rfl` into its components or cases. Conclude with `hh.2 b hb`. Conclude with `⟨hs, ht⟩`.
-/
theorem isPt_ext {E : Type} [Zero E] {i s : ℕ} (hs : 1 ≤ s) (hsi : s ≤ i) {h : Pt E} {t : E}
    (hh : IsPt (i - s) h) (ht : t ≠ 0) : IsPt i (ext h s t) := by
  refine ⟨?_, ?_⟩
  · have := hh.1
    simp only [lvl] at this
    simp [lvl, Formalism.FourierDecayAlt.TA.ext, this]; omega
  · intro b hb
    simp only [Formalism.FourierDecayAlt.TA.ext, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hh.2 b hb
    · exact ⟨hs, ht⟩

/- English proof (translation)
Set `S : Submodule ℂ H` to `Submodule.span ℂ (V '' (P : Set α))`. Establish `: FiniteDimensional ℂ S` using `FiniteDimensional.span_of_finite ℂ ((P.finite_toSet).image V)`. Establish `hmem : ∀ x ∈ P, V x ∈ S` using `fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩`. Set `v : α → S` to `fun x => if hx : x ∈ P then ⟨V x, hmem x hx⟩ else 0`. Establish `hv : ∀ x ∈ P, ((v x : S) : H) = V x` using `fun x hx => by simp [v, hx]`.

Set `b` to `stdOrthonormalBasis ℂ S`. Establish `key : ∀ x ∈ P, ∀ y ∈ P, ⟪V x, V y⟫_ℂ = ∑ j, conj (⟪b j, v x⟫_ℂ) * ⟪b j, v y⟫_ℂ`. Introduce `x hx y hy`. Rewrite using `[← hv x hx, ← hv y hy, ← Submodule.coe_inner, ← b.sum_inner_mul_inner]`. Use `sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[inner_conj_symm]`. Establish `e : ∑ x ∈ P, ∑ y ∈ P, k x y * ⟪V x, V y⟫_ℂ = ∑ j, ∑ x ∈ P, ∑ y ∈ P, conj (⟪b j, v x⟫_ℂ) * k x y * ⟪b j, v y⟫_ℂ`. Use `symm`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[sum_comm]`. Use `sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Rewrite using `[key x hx y hy, mul_sum]`. Conclude with `sum_congr rfl fun j _ => by ring`. Rewrite using `[e, Complex.re_sum]`.

Conclude with `sum_nonneg fun j _ => hk.2 fun x => ⟪b j, v x⟫_ℂ`.
-/
theorem gram_nonneg {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : Finset α) (k : α → α → ℂ) (V : α → H) (hk : PSDOn P k) :
    0 ≤ (∑ x ∈ P, ∑ y ∈ P, k x y * ⟪V x, V y⟫_ℂ).re := by
  classical
  let S : Submodule ℂ H := Submodule.span ℂ (V '' (P : Set α))
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ ((P.finite_toSet).image V)
  have hmem : ∀ x ∈ P, V x ∈ S := fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  let v : α → S := fun x => if hx : x ∈ P then ⟨V x, hmem x hx⟩ else 0
  have hv : ∀ x ∈ P, ((v x : S) : H) = V x := fun x hx => by simp [v, hx]
  let b := stdOrthonormalBasis ℂ S
  have key : ∀ x ∈ P, ∀ y ∈ P,
      ⟪V x, V y⟫_ℂ = ∑ j, conj (⟪b j, v x⟫_ℂ) * ⟪b j, v y⟫_ℂ := by
    intro x hx y hy
    rw [← hv x hx, ← hv y hy, ← Submodule.coe_inner, ← b.sum_inner_mul_inner]
    refine sum_congr rfl fun j _ => ?_
    rw [inner_conj_symm]
  have e : ∑ x ∈ P, ∑ y ∈ P, k x y * ⟪V x, V y⟫_ℂ
      = ∑ j, ∑ x ∈ P, ∑ y ∈ P, conj (⟪b j, v x⟫_ℂ) * k x y * ⟪b j, v y⟫_ℂ := by
    symm
    rw [sum_comm]
    refine sum_congr rfl fun x hx => ?_
    rw [sum_comm]
    refine sum_congr rfl fun y hy => ?_
    rw [key x hx y hy, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [e, Complex.re_sum]
  exact sum_nonneg fun j _ => hk.2 fun x => ⟪b j, v x⟫_ℂ

/- English proof (translation)
Establish `hinj : Function.Injective f` using `Function.LeftInverse.injective hg`. Use `⟨fun x hx y hy => hk.1 _ (mem_image_of_mem f hx) _ (mem_image_of_mem f hy), fun a => ?_⟩` and prove the remaining obligations. Use `hk.2 (fun p => a (g p))` as an intermediate fact. Rewrite `this` using `[sum_image (fun x _ y _ h => hinj h)]`. Use `this.trans_eq ?_` and prove the remaining obligations.

Use `congr 1`. Use `sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[sum_image (fun x _ y _ h => hinj h)]`. Simplify using `only [hg]`.
-/
theorem psdOn_comp {α β : Type} [DecidableEq β] (f : α → β) (g : β → α) (hg : ∀ x, g (f x) = x)
    (P : Finset α) (k : β → β → ℂ) (hk : PSDOn (P.image f) k) :
    PSDOn P (fun x y => k (f x) (f y)) := by
  have hinj : Function.Injective f := Function.LeftInverse.injective hg
  refine ⟨fun x hx y hy => hk.1 _ (mem_image_of_mem f hx) _ (mem_image_of_mem f hy), fun a => ?_⟩
  have := hk.2 (fun p => a (g p))
  rw [sum_image (fun x _ y _ h => hinj h)] at this
  refine this.trans_eq ?_
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [sum_image (fun x _ y _ h => hinj h)]
  simp only [hg]

/- English proof (translation)
Establish `e : ∑ t ∈ T, ∑ t' ∈ T, c t t' * ((A t + B t') / 2) = (∑ t ∈ T, A t * ∑ t' ∈ T, c t t' + ∑ t' ∈ T, B t' * ∑ t ∈ T, c t t') / 2`. Establish `e2 : ∑ t' ∈ T, B t' * ∑ t ∈ T, c t t' = ∑ t ∈ T, ∑ t' ∈ T, B t' * c t t'`. Rewrite using `[sum_comm]`. Conclude with `sum_congr rfl fun _ _ => mul_sum _ _ _`. Rewrite using `[e2, ← sum_add_distrib, sum_div]`.

Use `sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[mul_sum, ← sum_add_distrib, sum_div]`. Conclude with `sum_congr rfl fun t' _ => by ring`. Rewrite using `[e]`. Establish `h1 : ∑ t ∈ T, A t * ∑ t' ∈ T, c t t' ≤ ∑ t ∈ T, A t * ep` using `sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (row t ht) (hA t ht)`.

Establish `h2 : ∑ t' ∈ T, B t' * ∑ t ∈ T, c t t' ≤ ∑ t ∈ T, B t * ep` using `sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (col t ht) (hB t ht)`. Rewrite `h1`, `h2` using `[← sum_mul]`. Establish `e3 : ep * ((∑ t ∈ T, A t + ∑ t ∈ T, B t) / 2) = ((∑ t ∈ T, A t) * ep + (∑ t ∈ T, B t) * ep) / 2` using `by ring`. Rewrite using `[e3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem schur_abs {α : Type} (T : Finset α) (c : α → α → ℝ) (A B : α → ℝ) (ep : ℝ)
    (hA : ∀ t ∈ T, 0 ≤ A t) (hB : ∀ t ∈ T, 0 ≤ B t)
    (row : ∀ t ∈ T, ∑ t' ∈ T, c t t' ≤ ep) (col : ∀ t' ∈ T, ∑ t ∈ T, c t t' ≤ ep) :
    ∑ t ∈ T, ∑ t' ∈ T, c t t' * ((A t + B t') / 2)
      ≤ ep * ((∑ t ∈ T, A t + ∑ t ∈ T, B t) / 2) := by
  have e : ∑ t ∈ T, ∑ t' ∈ T, c t t' * ((A t + B t') / 2)
      = (∑ t ∈ T, A t * ∑ t' ∈ T, c t t' + ∑ t' ∈ T, B t' * ∑ t ∈ T, c t t') / 2 := by
    have e2 : ∑ t' ∈ T, B t' * ∑ t ∈ T, c t t' = ∑ t ∈ T, ∑ t' ∈ T, B t' * c t t' := by
      rw [sum_comm]; exact sum_congr rfl fun _ _ => mul_sum _ _ _
    rw [e2, ← sum_add_distrib, sum_div]
    refine sum_congr rfl fun t _ => ?_
    rw [mul_sum, ← sum_add_distrib, sum_div]
    exact sum_congr rfl fun t' _ => by ring
  rw [e]
  have h1 : ∑ t ∈ T, A t * ∑ t' ∈ T, c t t' ≤ ∑ t ∈ T, A t * ep :=
    sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (row t ht) (hA t ht)
  have h2 : ∑ t' ∈ T, B t' * ∑ t ∈ T, c t t' ≤ ∑ t ∈ T, B t * ep :=
    sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (col t ht) (hB t ht)
  rw [← sum_mul] at h1 h2
  have e3 : ep * ((∑ t ∈ T, A t + ∑ t ∈ T, B t) / 2)
      = ((∑ t ∈ T, A t) * ep + (∑ t ∈ T, B t) * ep) / 2 := by ring
  rw [e3]; linarith

/- English proof (translation)
Establish `hle : ∀ w, len w ≤ B → g w ≤ wsup len B g` using `fun w hw => le_ciSup (f := fun w : {w // len w ≤ B} => g w.1) (Set.finite_range _).bddAbove ⟨w, hw⟩`. Establish `hone : ∑ x, th x * wsup len B g = wsup len B g` using `by rw [← sum_mul, hth.2.1, one_mul]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← hone]`. Use `sum_le_sum fun x _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h0 : th x = 0`. Simplify using `[h0]`. Conclude with `mul_le_mul_of_nonneg_left (hle _ (hth.2.2 x h0).1) (hth.1 x)`. Rewrite using `[← hone]`. Use `sum_le_sum fun x _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h0 : th x = 0`. Simplify using `[h0]`. Conclude with `mul_le_mul_of_nonneg_left (hle _ (hth.2.2 x h0).2) (hth.1 x)`.
-/
theorem mean_le_wsup {W : Type} [Fintype W] (len : W → ℕ) (B : ℕ) (th : W × W → ℝ)
    (hth : IsProb2 len B th) (g : W → ℝ) :
    ∑ x, th x * g x.1 ≤ wsup len B g ∧ ∑ x, th x * g x.2 ≤ wsup len B g := by
  have hle : ∀ w, len w ≤ B → g w ≤ wsup len B g := fun w hw =>
    le_ciSup (f := fun w : {w // len w ≤ B} => g w.1) (Set.finite_range _).bddAbove ⟨w, hw⟩
  have hone : ∑ x, th x * wsup len B g = wsup len B g := by rw [← sum_mul, hth.2.1, one_mul]
  constructor
  · rw [← hone]
    refine sum_le_sum fun x _ => ?_
    by_cases h0 : th x = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (hle _ (hth.2.2 x h0).1) (hth.1 x)
  · rw [← hone]
    refine sum_le_sum fun x _ => ?_
    by_cases h0 : th x = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (hle _ (hth.2.2 x h0).2) (hth.1 x)

end Formalism.FourierDecayAlt.P.TA2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.TA2

/- English proof (translation)
Introduce `E _ _ H _ _ W _ len Kl Nw D Sg Φ Pat3 _ pat3 c3 ep3 i s w hNZ hs hsi hi hK hA2 h73 hLat hw`. Take `⟨th, hth, hest⟩` from `h73 w hw`. Establish `hHdPt : ∀ h ∈ PT Sg (i - s), IsPt (i - s) h` using `fun h hh => isPt_PT Sg hNZ _ h hh`. Establish `hTnz : ∀ t ∈ Sg i s, t ≠ 0` using `fun t ht => hNZ _ _ t ht`. Establish `hPSD : PSDOn ((PT Sg (i - s) ×ˢ Sg i s).image fun x => ext x.1 s x.2) (D.K i)` using `hK.2 i hi _ (by`.

Introduce `p hp`. Simplify using `only [mem_image, mem_product] at hp`. Take `⟨x, ⟨h1, h2⟩, rfl⟩` from `hp`. Conclude with `isPt_ext hs hsi (hHdPt _ h1) (hTnz _ h2))`. Establish `hdiagPSD : ∀ t ∈ Sg i s, PSDOn (PT Sg (i - s)) (offK (D.K i) s t t)`.

Introduce `t ht`. Use `psdOn_comp (fun h => ext h s t) List.dropLast (fun h => by simp [Formalism.FourierDecayAlt.TA.ext]) _ _ (hK.2 i hi _ ?_)` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [mem_image] at hp`. Take `⟨h, hh, rfl⟩` from `hp`.

Conclude with `isPt_ext hs hsi (hHdPt _ hh) (hTnz _ ht)`. Establish `hest'` using `hest (PT Sg (i - s)) (D.K i) (Sg i s) hHdPt hTnz hPSD`. Use `set N : E → E → ℂ := fun t t' => Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t') s t t' with hN`. Use `set d : W → E → ℝ := fun w' t => (Nst (Φ w') (PT Sg (i - s)) (offK (D.K i) s t t) s t t).re with hd`. Establish `hdnn : ∀ w', ∀ t ∈ Sg i s, 0 ≤ d w' t` using `fun w' t ht => gram_nonneg (PT Sg (i - s)) (offK (D.K i) s t t) (fun h => Φ w' (ext h s t)) (hdiagPSD t ht)`.

Use `set c : E → E → ℝ := fun t t' => if t ≠ t' ∧ 1 / t - 1 / t' ∈ D.Lf i s then c3 (1 / t - 1 / t') else 0 with hc`. Use `set A : E → ℝ := fun t => ∑ π, ∑ x, th π x * d x.1 t with hA`. Use `set B : E → ℝ := fun t => ∑ π, ∑ x, th π x * d x.2 t with hB`. Establish `hAnn : ∀ t ∈ Sg i s, 0 ≤ A t` using `fun t ht => sum_nonneg fun π _ => sum_nonneg fun x _ => mul_nonneg ((hth π).1 x) (hdnn _ t ht)`. Establish `hBnn : ∀ t ∈ Sg i s, 0 ≤ B t` using `fun t ht => sum_nonneg fun π _ => sum_nonneg fun x _ => mul_nonneg ((hth π).1 x) (hdnn _ t ht)`.

Establish `hep : 0 ≤ ep3` using `by simpa using hLat.2 ∅ (by simp)`. Establish `hoff : ∀ t ∈ Sg i s, ∀ t' ∈ Sg i s, t ≠ t' → (N t t').re ≤ c t t' * ((A t + B t') / 2)`. Introduce `t ht t' ht' hne`. Distinguish the cases in `hl : 1 / t - 1 / t' ∈ D.Lf i s`. Establish `hcv : c t t' = c3 (1 / t - 1 / t')` using `if_pos ⟨hne, hl⟩`.

Rewrite using `[hcv]`. Use `(Complex.re_le_norm _).trans ((hest' t ht t' ht' hne).trans ?_)` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (hLat.1 _)` and prove the remaining obligations. Establish `e : (A t + B t') / 2 = ∑ π, ∑ x, th π x * ((d x.1 t + d x.2 t') / 2)`. Simplify using `only [hA, hB]`.

Rewrite using `[← sum_add_distrib, sum_div]`. Use `sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[← sum_add_distrib, sum_div]`. Conclude with `sum_congr rfl fun x _ => by ring`. Rewrite using `[e]`.

Conclude with `single_le_sum (f := fun π => ∑ x, th π x * ((d x.1 t + d x.2 t') / 2)) (fun π _ => sum_nonneg fun x _ => mul_nonneg ((hth π).1 x) (by have := hdnn x.1 t ht; have := hdnn x.2 t' ht'; positivity)) (mem_univ (pat3 t t'))`. Establish `hcv : c t t' = 0` using `if_neg fun h => hl h.2`. Establish `hz : N t t' = 0`. Simplify using `only [hN, Nst]`. Use `sum_eq_zero fun h hh => sum_eq_zero fun h' hh' => ?_` and prove the remaining obligations.

Use `hA2 i s hs hsi hi h h' t t' (hHdPt h hh) (hHdPt h' hh') (hTnz t ht) (hTnz t' ht') (Or.inl hl)` as an intermediate fact. Simplify using `[offK, this]`. Rewrite using `[hcv, hz]`. Simplify using the standard rewrite rules. Establish `hrow : ∀ t ∈ Sg i s, ∑ t' ∈ Sg i s, c t t' ≤ ep3`.

Introduce `t ht`. Simplify using `only [hc]`. Rewrite using `[← sum_filter]`. Establish `hinj : Set.InjOn (fun t' : E => 1 / t - 1 / t') ((Sg i s).filter fun t' => t ≠ t' ∧ 1 / t - 1 / t' ∈ D.Lf i s : Finset E)`. Introduce `a _ b _ hab`.

Establish `: (1 : E) / a = 1 / b` using `by simpa using hab`. Simplify using `using this`. Rewrite using `[← sum_image (f := c3) hinj]`. Use `hLat.2 _ ?_` and prove the remaining obligations. Introduce `x hx`.

Simplify using `only [mem_image, mem_filter] at hx`. Take `⟨t', ⟨_, hne, hl⟩, rfl⟩` from `hx`. Use `⟨hl, fun h0 => hne ?_⟩` and prove the remaining obligations. Establish `: (1 : E) / t = 1 / t'` using `sub_eq_zero.mp h0`. Simplify using `using this`.

Establish `hcol : ∀ t' ∈ Sg i s, ∑ t ∈ Sg i s, c t t' ≤ ep3`. Introduce `t' ht'`. Simplify using `only [hc]`. Rewrite using `[← sum_filter]`. Establish `hinj : Set.InjOn (fun t : E => 1 / t - 1 / t') ((Sg i s).filter fun t => t ≠ t' ∧ 1 / t - 1 / t' ∈ D.Lf i s : Finset E)`.

Introduce `a _ b _ hab`. Establish `: (1 : E) / a = 1 / b` using `by simpa using hab`. Simplify using `using this`. Rewrite using `[← sum_image (f := c3) hinj]`. Use `hLat.2 _ ?_` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [mem_image, mem_filter] at hx`. Take `⟨t, ⟨_, hne, hl⟩, rfl⟩` from `hx`. Use `⟨hl, fun h0 => hne ?_⟩` and prove the remaining obligations. Establish `: (1 : E) / t = 1 / t'` using `sub_eq_zero.mp h0`.

Simplify using `using this`. Establish `hschur` using `schur_abs (Sg i s) c A B ep3 hAnn hBnn hrow hcol`. Use `set M : ℝ := wsup len (len w + Kl) (fun w' => Diag D Sg Φ w' i s) with hM`. Establish `hDiag : ∀ w', Diag D Sg Φ w' i s = ∑ t ∈ Sg i s, d w' t` using `fun w' => rfl`. Establish `hsumA : ∑ t ∈ Sg i s, A t ≤ Fintype.card Pat3 * M`.

Establish `e : ∑ t ∈ Sg i s, A t = ∑ π : Pat3, ∑ x, th π x * Diag D Sg Φ x.1 i s`. Simplify using `only [hA, hDiag]`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[sum_comm]`.

Conclude with `sum_congr rfl fun x _ => (mul_sum _ _ _).symm`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsumB : ∑ t ∈ Sg i s, B t ≤ Fintype.card Pat3 * M`. Establish `e : ∑ t ∈ Sg i s, B t = ∑ π : Pat3, ∑ x, th π x * Diag D Sg Φ x.2 i s`.

Simplify using `only [hB, hDiag]`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[sum_comm]`. Conclude with `sum_congr rfl fun x _ => (mul_sum _ _ _).symm`.

Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsplit : Ssplit D Sg Φ w i s = ∑ t ∈ Sg i s, ∑ t' ∈ Sg i s, (N t t').re`. Simplify using `only [Ssplit, hN, Complex.re_sum]`. Establish `hterm : ∀ t ∈ Sg i s, ∑ t' ∈ Sg i s, (N t t').re ≤ d w t + ∑ t' ∈ Sg i s, c t t' * ((A t + B t') / 2)`.

Introduce `t ht`. Establish `h1 : ∀ t' ∈ Sg i s, (N t t').re ≤ (if t = t' then d w t else 0) + c t t' * ((A t + B t') / 2)`. Introduce `t' ht'`. Distinguish the cases in `hne : t = t'`. Substitute `hne` using the available equality.

Simplify using `[hc, hN, hd]`. Simplify `hoff t ht t' ht' hne` using `[hne]`. Use `(sum_le_sum h1).trans_eq ?_` and prove the remaining obligations. Rewrite using `[sum_add_distrib, sum_ite_eq, if_pos ht]`. Rewrite using `[hsplit, hDiag w]`.

Establish `h2` using `sum_le_sum hterm`. Rewrite `h2` using `[sum_add_distrib]`. Establish `h3 : ep3 * ((∑ t ∈ Sg i s, A t + ∑ t ∈ Sg i s, B t) / 2) ≤ Fintype.card Pat3 * ep3 * M`. Establish `: (∑ t ∈ Sg i s, A t + ∑ t ∈ Sg i s, B t) / 2 ≤ Fintype.card Pat3 * M` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem off_diagonal_schur_complement : Formalism.FourierDecayAlt.TA.OffDiagSchur := by
  classical
  intro E _ _ H _ _ W _ len Kl Nw D Sg Φ Pat3 _ pat3 c3 ep3 i s w hNZ hs hsi hi hK hA2 h73 hLat hw
  obtain ⟨th, hth, hest⟩ := h73 w hw
  have hHdPt : ∀ h ∈ PT Sg (i - s), IsPt (i - s) h := fun h hh => isPt_PT Sg hNZ _ h hh
  have hTnz : ∀ t ∈ Sg i s, t ≠ 0 := fun t ht => hNZ _ _ t ht
  have hPSD : PSDOn ((PT Sg (i - s) ×ˢ Sg i s).image fun x => ext x.1 s x.2) (D.K i) :=
    hK.2 i hi _ (by
      intro p hp
      simp only [mem_image, mem_product] at hp
      obtain ⟨x, ⟨h1, h2⟩, rfl⟩ := hp
      exact isPt_ext hs hsi (hHdPt _ h1) (hTnz _ h2))
  have hdiagPSD : ∀ t ∈ Sg i s, PSDOn (PT Sg (i - s)) (offK (D.K i) s t t) := by
    intro t ht
    refine psdOn_comp (fun h => ext h s t) List.dropLast (fun h => by simp [Formalism.FourierDecayAlt.TA.ext]) _ _
      (hK.2 i hi _ ?_)
    intro p hp
    simp only [mem_image] at hp
    obtain ⟨h, hh, rfl⟩ := hp
    exact isPt_ext hs hsi (hHdPt _ hh) (hTnz _ ht)
  have hest' := hest (PT Sg (i - s)) (D.K i) (Sg i s) hHdPt hTnz hPSD

  set N : E → E → ℂ := fun t t' => Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t') s t t' with hN
  set d : W → E → ℝ := fun w' t => (Nst (Φ w') (PT Sg (i - s)) (offK (D.K i) s t t) s t t).re with hd
  have hdnn : ∀ w', ∀ t ∈ Sg i s, 0 ≤ d w' t := fun w' t ht =>
    gram_nonneg (PT Sg (i - s)) (offK (D.K i) s t t) (fun h => Φ w' (ext h s t)) (hdiagPSD t ht)
  set c : E → E → ℝ := fun t t' =>
    if t ≠ t' ∧ 1 / t - 1 / t' ∈ D.Lf i s then c3 (1 / t - 1 / t') else 0 with hc
  set A : E → ℝ := fun t => ∑ π, ∑ x, th π x * d x.1 t with hA
  set B : E → ℝ := fun t => ∑ π, ∑ x, th π x * d x.2 t with hB
  have hAnn : ∀ t ∈ Sg i s, 0 ≤ A t := fun t ht =>
    sum_nonneg fun π _ => sum_nonneg fun x _ => mul_nonneg ((hth π).1 x) (hdnn _ t ht)
  have hBnn : ∀ t ∈ Sg i s, 0 ≤ B t := fun t ht =>
    sum_nonneg fun π _ => sum_nonneg fun x _ => mul_nonneg ((hth π).1 x) (hdnn _ t ht)
  have hep : 0 ≤ ep3 := by simpa using hLat.2 ∅ (by simp)

  have hoff : ∀ t ∈ Sg i s, ∀ t' ∈ Sg i s, t ≠ t' → (N t t').re ≤ c t t' * ((A t + B t') / 2) := by
    intro t ht t' ht' hne
    by_cases hl : 1 / t - 1 / t' ∈ D.Lf i s
    · have hcv : c t t' = c3 (1 / t - 1 / t') := if_pos ⟨hne, hl⟩
      rw [hcv]
      refine (Complex.re_le_norm _).trans ((hest' t ht t' ht' hne).trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ (hLat.1 _)
      have e : (A t + B t') / 2 = ∑ π, ∑ x, th π x * ((d x.1 t + d x.2 t') / 2) := by
        simp only [hA, hB]
        rw [← sum_add_distrib, sum_div]
        refine sum_congr rfl fun π _ => ?_
        rw [← sum_add_distrib, sum_div]
        exact sum_congr rfl fun x _ => by ring
      rw [e]
      exact single_le_sum (f := fun π => ∑ x, th π x * ((d x.1 t + d x.2 t') / 2))
        (fun π _ => sum_nonneg fun x _ => mul_nonneg ((hth π).1 x)
          (by have := hdnn x.1 t ht; have := hdnn x.2 t' ht'; positivity)) (mem_univ (pat3 t t'))
    · have hcv : c t t' = 0 := if_neg fun h => hl h.2
      have hz : N t t' = 0 := by
        simp only [hN, Nst]
        refine sum_eq_zero fun h hh => sum_eq_zero fun h' hh' => ?_
        have := hA2 i s hs hsi hi h h' t t' (hHdPt h hh) (hHdPt h' hh') (hTnz t ht) (hTnz t' ht')
          (Or.inl hl)
        simp [offK, this]
      rw [hcv, hz]; simp

  have hrow : ∀ t ∈ Sg i s, ∑ t' ∈ Sg i s, c t t' ≤ ep3 := by
    intro t ht
    simp only [hc]
    rw [← sum_filter]
    have hinj : Set.InjOn (fun t' : E => 1 / t - 1 / t')
        ((Sg i s).filter fun t' => t ≠ t' ∧ 1 / t - 1 / t' ∈ D.Lf i s : Finset E) := by
      intro a _ b _ hab
      have : (1 : E) / a = 1 / b := by simpa using hab
      simpa using this
    rw [← sum_image (f := c3) hinj]
    refine hLat.2 _ ?_
    intro x hx
    simp only [mem_image, mem_filter] at hx
    obtain ⟨t', ⟨_, hne, hl⟩, rfl⟩ := hx
    refine ⟨hl, fun h0 => hne ?_⟩
    have : (1 : E) / t = 1 / t' := sub_eq_zero.mp h0
    simpa using this
  have hcol : ∀ t' ∈ Sg i s, ∑ t ∈ Sg i s, c t t' ≤ ep3 := by
    intro t' ht'
    simp only [hc]
    rw [← sum_filter]
    have hinj : Set.InjOn (fun t : E => 1 / t - 1 / t')
        ((Sg i s).filter fun t => t ≠ t' ∧ 1 / t - 1 / t' ∈ D.Lf i s : Finset E) := by
      intro a _ b _ hab
      have : (1 : E) / a = 1 / b := by simpa using hab
      simpa using this
    rw [← sum_image (f := c3) hinj]
    refine hLat.2 _ ?_
    intro x hx
    simp only [mem_image, mem_filter] at hx
    obtain ⟨t, ⟨_, hne, hl⟩, rfl⟩ := hx
    refine ⟨hl, fun h0 => hne ?_⟩
    have : (1 : E) / t = 1 / t' := sub_eq_zero.mp h0
    simpa using this
  have hschur := schur_abs (Sg i s) c A B ep3 hAnn hBnn hrow hcol

  set M : ℝ := wsup len (len w + Kl) (fun w' => Diag D Sg Φ w' i s) with hM
  have hDiag : ∀ w', Diag D Sg Φ w' i s = ∑ t ∈ Sg i s, d w' t := fun w' => rfl
  have hsumA : ∑ t ∈ Sg i s, A t ≤ Fintype.card Pat3 * M := by
    have e : ∑ t ∈ Sg i s, A t = ∑ π : Pat3, ∑ x, th π x * Diag D Sg Φ x.1 i s := by
      simp only [hA, hDiag]
      rw [sum_comm]
      refine sum_congr rfl fun π _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun x _ => (mul_sum _ _ _).symm
    rw [e]
    calc ∑ π : Pat3, ∑ x, th π x * Diag D Sg Φ x.1 i s ≤ ∑ _π : Pat3, M :=
          sum_le_sum fun π _ => (mean_le_wsup len _ (th π) (hth π) (fun w' => Diag D Sg Φ w' i s)).1
      _ = Fintype.card Pat3 * M := by simp
  have hsumB : ∑ t ∈ Sg i s, B t ≤ Fintype.card Pat3 * M := by
    have e : ∑ t ∈ Sg i s, B t = ∑ π : Pat3, ∑ x, th π x * Diag D Sg Φ x.2 i s := by
      simp only [hB, hDiag]
      rw [sum_comm]
      refine sum_congr rfl fun π _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun x _ => (mul_sum _ _ _).symm
    rw [e]
    calc ∑ π : Pat3, ∑ x, th π x * Diag D Sg Φ x.2 i s ≤ ∑ _π : Pat3, M :=
          sum_le_sum fun π _ => (mean_le_wsup len _ (th π) (hth π) (fun w' => Diag D Sg Φ w' i s)).2
      _ = Fintype.card Pat3 * M := by simp

  have hsplit : Ssplit D Sg Φ w i s = ∑ t ∈ Sg i s, ∑ t' ∈ Sg i s, (N t t').re := by
    simp only [Ssplit, hN, Complex.re_sum]
  have hterm : ∀ t ∈ Sg i s, ∑ t' ∈ Sg i s, (N t t').re
      ≤ d w t + ∑ t' ∈ Sg i s, c t t' * ((A t + B t') / 2) := by
    intro t ht
    have h1 : ∀ t' ∈ Sg i s, (N t t').re
        ≤ (if t = t' then d w t else 0) + c t t' * ((A t + B t') / 2) := by
      intro t' ht'
      by_cases hne : t = t'
      · subst hne
        simp [hc, hN, hd]
      · simpa [hne] using hoff t ht t' ht' hne
    refine (sum_le_sum h1).trans_eq ?_
    rw [sum_add_distrib, sum_ite_eq, if_pos ht]
  rw [hsplit, hDiag w]
  have h2 := sum_le_sum hterm
  rw [sum_add_distrib] at h2
  have h3 : ep3 * ((∑ t ∈ Sg i s, A t + ∑ t ∈ Sg i s, B t) / 2) ≤ Fintype.card Pat3 * ep3 * M := by
    have : (∑ t ∈ Sg i s, A t + ∑ t ∈ Sg i s, B t) / 2 ≤ Fintype.card Pat3 * M := by linarith
    calc _ ≤ ep3 * (Fintype.card Pat3 * M) := mul_le_mul_of_nonneg_left this hep
      _ = _ := by ring
  linarith

end Formalism.FourierDecayAlt.P

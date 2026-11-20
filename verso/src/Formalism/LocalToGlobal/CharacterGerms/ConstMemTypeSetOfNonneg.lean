import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section TyS

variable {l : ℕ} (hl : 2 ≤ l)

include hl

/- English proof (translation)
Unfold `tyS`. Rewrite using `[PowerSeries.coeff_mk]`. Establish `hinj : ∀ t, l ^ t = l ^ s ↔ t = s` using `fun t => (Nat.pow_right_injective hl).eq_iff`. Simplify using `only [hinj]`. Rewrite using `[Finset.sum_ite_eq', if_pos]`.

Establish `hs : s < l ^ s` using `Nat.lt_pow_self (by omega)`. Conclude with `Finset.mem_range.2 (by omega)`.
-/
theorem coeff_tyS_pow (a : ℕ → C) (s : ℕ) : PowerSeries.coeff (l ^ s) (tyS l a) = a s := by
  unfold tyS
  rw [PowerSeries.coeff_mk]
  have hinj : ∀ t, l ^ t = l ^ s ↔ t = s := fun t => (Nat.pow_right_injective hl).eq_iff
  simp only [hinj]
  rw [Finset.sum_ite_eq', if_pos]
  have hs : s < l ^ s := Nat.lt_pow_self (by omega)
  exact Finset.mem_range.2 (by omega)

omit hl in
/- English proof (translation)
Unfold `tyS`. Rewrite using `[PowerSeries.coeff_mk]`. Conclude with `Finset.sum_eq_zero fun s _ => if_neg (hm s)`.
-/
theorem coeff_tyS_of_ne (a : ℕ → C) (m : ℕ) (hm : ∀ s, l ^ s ≠ m) : PowerSeries.coeff m (tyS l a) = 0 := by
  unfold tyS
  rw [PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero fun s _ => if_neg (hm s)

/- English proof (translation)
Use extensionality with `m`. Distinguish the cases in `h : ∃ s, l ^ s = m`. Take `⟨s, rfl⟩` from `h`. Rewrite using `[coeff_tyS_pow hl, h1]`. Use `push_neg at h`.

Rewrite using `[coeff_tyS_of_ne a m h, h2 m h]`.
-/
theorem tyS_eq (a : ℕ → C) (f : PowerSeries C) (h1 : ∀ s, PowerSeries.coeff (l ^ s) f = a s)
    (h2 : ∀ m, (∀ s, l ^ s ≠ m) → PowerSeries.coeff m f = 0) : tyS l a = f := by
  ext m
  by_cases h : ∃ s, l ^ s = m
  · obtain ⟨s, rfl⟩ := h
    rw [coeff_tyS_pow hl, h1]
  · push_neg at h
    rw [coeff_tyS_of_ne a m h, h2 m h]

omit hl in
/- English proof (translation)
Use extensionality with `m`. Unfold `tyS`. Simplify using the standard rewrite rules.
-/
theorem tyS_zero : tyS l (fun _ => (0 : C)) = 0 := by
  ext m
  unfold tyS
  simp

end TyS

section Repar

/- English proof (translation)
Introduce `ν hν`. Establish `hν0 : ν = 0`. Use extensionality with `w`. Assume the negation of the conclusion as `hw`. Conclude with `hν w (Finsupp.mem_support_iff.2 hw) (Set.mem_univ w)`.

Substitute `hν0` using the available equality. Simplify using `using h`.
-/
theorem van_univ {τ : Type} {f : MvPowerSeries τ C} (h : MvPowerSeries.constantCoeff f = 0) :
    Van Set.univ f := by
  intro ν hν
  have hν0 : ν = 0 := by
    ext w
    by_contra hw
    exact hν w (Finsupp.mem_support_iff.2 hw) (Set.mem_univ w)
  subst hν0
  simpa using h

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `d`. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod]`. Simplify using `only [map_pow, ha]`.

Distinguish the cases in `hd : d = 0`. Substitute `hd` using the available equality. Simplify using `[hf]`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, d s ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hd (Finsupp.ext h)`. Establish `h0 : (∏ x ∈ d.support, (0 : C) ^ d x) = 0` using `Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (zero_pow hs)`. Rewrite using `[h0, smul_zero]`.
-/
theorem constantCoeff_subst_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod]
  simp only [map_pow, ha]
  by_cases hd : d = 0
  · subst hd
    simp [hf]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : (∏ x ∈ d.support, (0 : C) ^ d x) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (zero_pow hs)
    rw [h0, smul_zero]

/- English proof (translation)
Unfold `alongCv`. Establish `hγs : MvPowerSeries.HasSubst γ` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hγ`. Establish `hτs : MvPowerSeries.HasSubst (fun _ : Unit => τ)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hτ)`. Conclude with `(MvPowerSeries.subst_comp_subst_apply hγs hτs f).symm`.
-/
theorem alongCv_repar {σ : Type} [Finite σ] {γ : σ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {τ : PowerSeries C} (hτ : PowerSeries.constantCoeff τ = 0)
    (f : MvPowerSeries σ C) :
    alongCv (fun i => PowerSeries.subst τ (γ i)) f = PowerSeries.subst τ (alongCv γ f) := by
  unfold alongCv
  have hγs : MvPowerSeries.HasSubst γ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ
  have hτs : MvPowerSeries.HasSubst (fun _ : Unit => τ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hτ)
  exact (MvPowerSeries.subst_comp_subst_apply hγs hτs f).symm

/- English proof (translation)
Unfold `alongCv`. Establish `ha : MvPowerSeries.HasSubst (fun _ : σ => (0 : PowerSeries C))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => map_zero _)`. Use `MvPowerSeries.ext fun e => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_subst ha, map_zero]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises.

Introduce `d`. Distinguish the cases in `hd : d = 0`. Substitute `hd` using the available equality. Simplify using `[hf]`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, d s ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hd (Finsupp.ext h)`. Establish `h0 : (d.prod fun _ e => (0 : PowerSeries C) ^ e) = 0` using `Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (zero_pow hs)`. Simplify using `only [h0, map_zero, smul_zero]`.
-/
theorem alongCv_zero {σ : Type} [Finite σ] {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    alongCv (fun _ : σ => (0 : PowerSeries C)) f = 0 := by
  unfold alongCv
  have ha : MvPowerSeries.HasSubst (fun _ : σ => (0 : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => map_zero _)
  refine MvPowerSeries.ext fun e => ?_
  rw [MvPowerSeries.coeff_subst ha, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    simp [hf]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : (d.prod fun _ e => (0 : PowerSeries C) ^ e) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (zero_pow hs)
    simp only [h0, map_zero, smul_zero]

end Repar

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((0 : ℝ) : WithTop ℝ) ≤ V.v 0`. Rewrite using `[AddValuation.map_zero]`. Conclude with `le_top`.
-/
private theorem ge_zero_lemma (V : VF C) : V.Ge 0 (0 : C) := by
  change ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
  rw [AddValuation.map_zero]
  exact le_top

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((0 : ℝ) : WithTop ℝ) ≤ V.v (a * b)`. Rewrite using `[AddValuation.map_mul]`. Establish `h` using `add_le_add (show ((0 : ℝ) : WithTop ℝ) ≤ V.v a from ha) (show ((0 : ℝ) : WithTop ℝ) ≤ V.v b from hb)`. Simplify using `using h`.
-/
private theorem ge_mul_lemma_2 (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) : V.Ge 0 (a * b) := by
  change ((0 : ℝ) : WithTop ℝ) ≤ V.v (a * b)
  rw [AddValuation.map_mul]
  have h := add_le_add (show ((0 : ℝ) : WithTop ℝ) ≤ V.v a from ha) (show ((0 : ℝ) : WithTop ℝ) ≤ V.v b from hb)
  simpa using h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Express the relevant statement in the definitionally equal form `((0 : ℝ) : WithTop ℝ) ≤ V.v (a ^ 0)`. Rewrite using `[pow_zero, AddValuation.map_one]`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Conclude with `ge_mul_lemma_2 V ih ha`.
-/
private theorem ge_zero_pow' (V : VF C) {a : C} (ha : V.Ge 0 a) (n : ℕ) : V.Ge 0 (a ^ n) := by
  induction n with
  | zero =>
    change ((0 : ℝ) : WithTop ℝ) ≤ V.v (a ^ 0)
    rw [pow_zero, AddValuation.map_one]
    simp
  | succ n ih =>
    rw [pow_succ]
    exact ge_mul_lemma_2 V ih ha

/- English proof (translation)
Take `⟨γ, lam, hγ, hlam, h1, h2⟩` from `hx`. Establish `hτs : PowerSeries.HasSubst τ` using `PowerSeries.HasSubst.of_constantCoeff_zero' hτ`. Establish `hs : ∀ f : PowerSeries C, PowerSeries.subst τ f = PowerSeries.substAlgHom hτs f` using `fun f => by`. Rewrite using `[PowerSeries.coe_substAlgHom]`. Establish `hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0` using `fun j => (hγ j).1`.

Use `⟨fun i => PowerSeries.subst τ (γ i), fun q => PowerSeries.subst τ (lam q), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Conclude with `⟨constantCoeff_subst_zero (a := fun _ : Unit => τ) (fun _ => hτ) (hγ i).1, hint _ (hγ i).2⟩`. Introduce `q`. Conclude with `⟨constantCoeff_subst_zero (a := fun _ : Unit => τ) (fun _ => hτ) (hlam q).1, hint _ (hlam q).2⟩`.

Introduce `i`. Rewrite using `[alongCv_repar hγ0 hτ, h1 i]`. Simplify using `only [hxx, hs, map_sum, map_smul]`. Introduce `q`. Rewrite using `[hxx, h2 q, alongCv_repar hγ0 hτ]`.

Simplify using `only [hxx, hs, map_add, map_sub, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem TySet_repar {V : VF C} {g : Fin 2} (τ : PowerSeries C) (hτ : PowerSeries.constantCoeff τ = 0)
    (hint : ∀ f : PowerSeries C, (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
      ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.subst τ f)))
    {x x' : ℕ → I g ⊕ JJ I g → C} (hx : x ∈ X.TySet V g)
    (hxx : ∀ n, tyS V.l (fun s => x' s n) = PowerSeries.subst τ (tyS V.l fun s => x s n)) :
    x' ∈ X.TySet V g := by
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  have hτs : PowerSeries.HasSubst τ := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hs : ∀ f : PowerSeries C, PowerSeries.subst τ f = PowerSeries.substAlgHom hτs f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  refine ⟨fun i => PowerSeries.subst τ (γ i), fun q => PowerSeries.subst τ (lam q), ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨constantCoeff_subst_zero (a := fun _ : Unit => τ) (fun _ => hτ) (hγ i).1, hint _ (hγ i).2⟩
  · intro q
    exact ⟨constantCoeff_subst_zero (a := fun _ : Unit => τ) (fun _ => hτ) (hlam q).1, hint _ (hlam q).2⟩
  · intro i
    rw [alongCv_repar hγ0 hτ, h1 i]
    simp only [hxx, hs, map_sum, map_smul]
  · intro q
    rw [hxx, h2 q, alongCv_repar hγ0 hτ]
    simp only [hxx, hs, map_add, map_sub, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> simp

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [PowerSeries.smul_eq_C_mul])), finsum_eq_single _ n]`. Rewrite using `[smul_pow, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_self, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `d hd`. Rewrite using `[smul_pow, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, if_neg (Ne.symm hd), smul_zero, smul_zero]`.
-/
private theorem coeff_subst_smul_X (c : C) (f : PowerSeries C) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst (c • (PowerSeries.X : PowerSeries C)) f) = c ^ n * PowerSeries.coeff n f := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [PowerSeries.smul_eq_C_mul])),
    finsum_eq_single _ n]
  · rw [smul_pow, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_self, smul_eq_mul]
    ring
  · intro d hd
    rw [smul_pow, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, if_neg (Ne.symm hd), smul_zero, smul_zero]

/- English proof (translation)
Establish `hl` using `V.l_prime.two_le`. Use `X.TySet_repar (c • PowerSeries.X) (by simp [PowerSeries.smul_eq_C_mul]) (fun f hf n => ?_) hx (fun m => ?_)` and prove the remaining obligations. Rewrite using `[coeff_subst_smul_X]`. Conclude with `ge_mul_lemma_2 V (ge_zero_pow' V hc n) (hf n)`. Use `tyS_eq hl _ _ (fun s => ?_) (fun k hk => ?_)` and prove the remaining obligations.

Rewrite using `[coeff_subst_smul_X, coeff_tyS_pow hl]`. Both sides reduce to the same expression. Rewrite using `[coeff_subst_smul_X, coeff_tyS_of_ne _ _ hk, mul_zero]`.
-/
theorem teich_mem (V : VF C) (g : Fin 2) (c : C) (hc : V.Ge 0 c) (x : ℕ → I g ⊕ JJ I g → C)
    (hx : x ∈ X.TySet V g) : teich V.l c x ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  refine X.TySet_repar (c • PowerSeries.X) (by simp [PowerSeries.smul_eq_C_mul]) (fun f hf n => ?_) hx (fun m => ?_)
  · rw [coeff_subst_smul_X]
    exact ge_mul_lemma_2 V (ge_zero_pow' V hc n) (hf n)
  · refine tyS_eq hl _ _ (fun s => ?_) (fun k hk => ?_)
    · rw [coeff_subst_smul_X, coeff_tyS_pow hl]
      rfl
    · rw [coeff_subst_smul_X, coeff_tyS_of_ne _ _ hk, mul_zero]

end RawChart

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])), finsum_eq_single _ q]`. Rewrite using `[← pow_mul, PowerSeries.coeff_X_pow_self, smul_eq_mul, mul_one]`. Introduce `d hd`. Rewrite using `[← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]`. Introduce `h`.

Conclude with `hd (Nat.eq_of_mul_eq_mul_left hl h).symm`.
-/
theorem coeff_subst_X_pow {l : ℕ} (hl : 0 < l) (f : PowerSeries C) (q : ℕ) :
    PowerSeries.coeff (l * q) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) = PowerSeries.coeff q f := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])), finsum_eq_single _ q]
  · rw [← pow_mul, PowerSeries.coeff_X_pow_self, smul_eq_mul, mul_one]
  · intro d hd
    rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]
    intro h
    exact hd (Nat.eq_of_mul_eq_mul_left hl h).symm

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne']))]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `d`. Rewrite using `[← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]`. Introduce and unpack `rfl`.

Conclude with `hm (dvd_mul_right l d)`.
-/
theorem coeff_subst_X_pow_of_not_dvd {l : ℕ} (hl : 0 < l) (f : PowerSeries C) (m : ℕ) (hm : ¬ l ∣ m) :
    PowerSeries.coeff m (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) = 0 := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne']))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]
  rintro rfl
  exact hm (dvd_mul_right l d)

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

/- English proof (translation)
Establish `hl` using `V.l_prime.two_le`. Establish `hl0 : 0 < V.l` using `by omega`. Use `X.TySet_repar (PowerSeries.X ^ V.l) (by simp [hl0.ne']) (fun f hf m => ?_) hx (fun m => ?_)` and prove the remaining obligations. Distinguish the cases in `hd : V.l ∣ m`. Take `⟨q, rfl⟩` from `hd`.

Rewrite using `[coeff_subst_X_pow hl0]`. Conclude with `hf q`. Rewrite using `[coeff_subst_X_pow_of_not_dvd hl0 _ _ hd]`. Conclude with `ge_zero_lemma V`. Use `tyS_eq hl _ _ (fun s => ?_) (fun k hk => ?_)` and prove the remaining obligations.

Consider the cases of `s with`. Consider the case `zero`. Rewrite using `[pow_zero, coeff_subst_X_pow_of_not_dvd hl0 _ _ V.l_prime.not_dvd_one]`. Simplify using `[Vpow]`. Consider the case `succ s`.

Rewrite using `[pow_succ', coeff_subst_X_pow hl0, coeff_tyS_pow hl]`. Simplify using `[Vpow]`. Distinguish the cases in `hd : V.l ∣ k`. Take `⟨q, rfl⟩` from `hd`. Rewrite using `[coeff_subst_X_pow hl0, coeff_tyS_of_ne _ _ (fun s hs => hk (s + 1) (by rw [pow_succ', hs]))]`.

Rewrite using `[coeff_subst_X_pow_of_not_dvd hl0 _ _ hd]`.
-/
theorem V_mem (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    Vpow 1 x ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  refine X.TySet_repar (PowerSeries.X ^ V.l) (by simp [hl0.ne']) (fun f hf m => ?_) hx (fun m => ?_)
  · by_cases hd : V.l ∣ m
    · obtain ⟨q, rfl⟩ := hd
      rw [coeff_subst_X_pow hl0]
      exact hf q
    · rw [coeff_subst_X_pow_of_not_dvd hl0 _ _ hd]
      exact ge_zero_lemma V
  · refine tyS_eq hl _ _ (fun s => ?_) (fun k hk => ?_)
    · cases s with
      | zero =>
        rw [pow_zero, coeff_subst_X_pow_of_not_dvd hl0 _ _ V.l_prime.not_dvd_one]
        simp [Vpow]
      | succ s =>
        rw [pow_succ', coeff_subst_X_pow hl0, coeff_tyS_pow hl]
        simp [Vpow]
    · by_cases hd : V.l ∣ k
      · obtain ⟨q, rfl⟩ := hd
        rw [coeff_subst_X_pow hl0, coeff_tyS_of_ne _ _ (fun s hs => hk (s + 1) (by rw [pow_succ', hs]))]
      · rw [coeff_subst_X_pow_of_not_dvd hl0 _ _ hd]

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Express the relevant statement in the definitionally equal form `-∑ i, v i * MvPowerSeries.coeff ((0 : κ →₀ ℕ).mapDomain (fun x : κ => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), i) 1) X.h = 0`. Simplify using `only [Finsupp.mapDomain_zero, zero_add]`. Rewrite using `[Finset.sum_eq_zero, neg_zero]`. Introduce `i _`.

Rewrite using `[hh _ ?_, mul_zero]`. Introduce `s hs`. Rewrite `hs` using `[Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]`. Rewrite using `[hs]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_sg (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (v : κ → C) : MvPowerSeries.constantCoeff (X.sg v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change -∑ i, v i * MvPowerSeries.coeff ((0 : κ →₀ ℕ).mapDomain (fun x : κ => ((0 : Fin 2), x)) +
    Finsupp.single ((1 : Fin 2), i) 1) X.h = 0
  simp only [Finsupp.mapDomain_zero, zero_add]
  rw [Finset.sum_eq_zero, neg_zero]
  intro i _
  rw [hh _ ?_, mul_zero]
  intro s hs
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hs
  rw [hs]
  simp

/- English proof (translation)
Establish `hl` using `V.l_prime.two_le`. Establish `hinl : ∀ c : I g, tyS V.l (fun s => const0 (Sum.elim 0 ζ) s (Sum.inl c : I g ⊕ JJ I g)) = 0`. Introduce `c`. Rewrite using `[show (fun s => const0 (Sum.elim 0 ζ) s (Sum.inl c : I g ⊕ JJ I g)) = fun _ => (0 : C) by`. Use function extensionality and compare the values at `s`.

Simplify using `[const0]]`. Conclude with `tyS_zero`. Establish `hinr : ∀ q : JJ I g, tyS V.l (fun s => const0 (Sum.elim 0 ζ) s (Sum.inr q : I g ⊕ JJ I g)) = ζ q • PowerSeries.X`. Introduce `q`. Use `tyS_eq hl _ _ (fun s => ?_) (fun m hm => ?_)` and prove the remaining obligations.

Consider the cases of `s with`. Consider the case `zero => simp [const0]`. Consider the case `succ s`. Establish `h1 : 1 < V.l ^ (s + 1)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hl1 : V.l ≠ 1` using `by omega`. Simplify using `[const0, PowerSeries.coeff_X, h1.ne', hl1]`. Establish `hm1 : m ≠ 1` using `fun h => hm 0 (by simp [h])`. Simplify using `[PowerSeries.coeff_X, hm1]`. Use `⟨fun _ => 0, fun q => ζ q • PowerSeries.X, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i`. Conclude with `⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩`. Introduce `q`. Use `⟨by simp, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_smul, PowerSeries.coeff_X]`.

Use `split_ifs`. Simplify using `using hζ q`. Simplify using `using ge_zero_lemma V`. Introduce `i`. Rewrite using `[alongCv_zero (hlg i)]`.

Simplify using `[hinl]`. Introduce `q`. Rewrite using `[hinr, alongCv_zero (X.constantCoeff_sg hh _)]`. Simplify using `[hinl]`.
-/
theorem const_mem_type_set_of_nonneg (hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (V : VF C) (g : Fin 2) (ζ : JJ I g → C) (hζ : ∀ q, V.Ge 0 (ζ q)) :
    const0 (Sum.elim 0 ζ) ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  have hinl : ∀ c : I g, tyS V.l (fun s => const0 (Sum.elim 0 ζ) s (Sum.inl c : I g ⊕ JJ I g)) = 0 := by
    intro c
    rw [show (fun s => const0 (Sum.elim 0 ζ) s (Sum.inl c : I g ⊕ JJ I g)) = fun _ => (0 : C) by
      funext s
      simp [const0]]
    exact tyS_zero
  have hinr : ∀ q : JJ I g, tyS V.l (fun s => const0 (Sum.elim 0 ζ) s (Sum.inr q : I g ⊕ JJ I g)) =
      ζ q • PowerSeries.X := by
    intro q
    refine tyS_eq hl _ _ (fun s => ?_) (fun m hm => ?_)
    · cases s with
      | zero => simp [const0]
      | succ s =>
        have h1 : 1 < V.l ^ (s + 1) :=
          calc 1 < V.l := by omega
            _ = V.l ^ 1 := (pow_one _).symm
            _ ≤ V.l ^ (s + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hl1 : V.l ≠ 1 := by omega
        simp [const0, PowerSeries.coeff_X, h1.ne', hl1]
    · have hm1 : m ≠ 1 := fun h => hm 0 (by simp [h])
      simp [PowerSeries.coeff_X, hm1]
  refine ⟨fun _ => 0, fun q => ζ q • PowerSeries.X, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro q
    refine ⟨by simp, fun n => ?_⟩
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_X]
    split_ifs
    · simpa using hζ q
    · simpa using ge_zero_lemma V
  · intro i
    rw [alongCv_zero (hlg i)]
    simp [hinl]
  · intro q
    rw [hinr, alongCv_zero (X.constantCoeff_sg hh _)]
    simp [hinl]

/- English proof (translation)
Use `⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Conclude with `⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩`. Introduce `q`. Conclude with `⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩`.

Introduce `i`. Rewrite using `[alongCv_zero (hlg i)]`. Simplify using `[tyS_zero]`. Introduce `q`. Rewrite using `[alongCv_zero (X.constantCoeff_sg hh _)]`.

Simplify using `[tyS_zero]`.
-/
theorem zero_mem (hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (V : VF C) (g : Fin 2) : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g := by
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro q
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro i
    rw [alongCv_zero (hlg i)]
    simp [tyS_zero]
  · intro q
    rw [alongCv_zero (X.constantCoeff_sg hh _)]
    simp [tyS_zero]

end RawChart

end Formalism.L2.FormalSeriesBounds

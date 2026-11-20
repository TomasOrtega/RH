import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelMoves

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]

section bichar
variable {c : B → A → k}

/- English proof (translation)
Establish `h` using `hc.2.2 b 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_left_cancel₀ (hc.1 b 0) (by rw [mul_one]; exact h.symm)`.
-/
theorem IsBichar.map_zero_right (hc : IsBichar c) (b : B) : c b 0 = 1 := by
  have h := hc.2.2 b 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (hc.1 b 0) (by rw [mul_one]; exact h.symm)

/- English proof (translation)
Establish `h` using `hc.2.1 0 0 a`. Rewrite `h` using `[add_zero]`. Conclude with `mul_left_cancel₀ (hc.1 0 a) (by rw [mul_one]; exact h.symm)`.
-/
theorem IsBichar.map_zero_left (hc : IsBichar c) (a : A) : c 0 a = 1 := by
  have h := hc.2.1 0 0 a
  rw [add_zero] at h
  exact mul_left_cancel₀ (hc.1 0 a) (by rw [mul_one]; exact h.symm)

/- English proof (translation)
Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← hc.2.2, neg_add_cancel, hc.map_zero_right]`.
-/
theorem IsBichar.map_neg_right (hc : IsBichar c) (b : B) (a : A) : c b (-a) = (c b a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hc.2.2, neg_add_cancel, hc.map_zero_right]

/- English proof (translation)
Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← hc.2.1, neg_add_cancel, hc.map_zero_left]`.
-/
theorem IsBichar.map_neg_left (hc : IsBichar c) (b : B) (a : A) : c (-b) a = (c b a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hc.2.1, neg_add_cancel, hc.map_zero_left]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, hc.2.2, hc.map_neg_right]`.
-/
theorem IsBichar.map_sub_right (hc : IsBichar c) (b : B) (a a' : A) : c b (a - a') = c b a * (c b a')⁻¹ := by
  rw [sub_eq_add_neg, hc.2.2, hc.map_neg_right]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, hc.2.1, hc.map_neg_left]`.
-/
theorem IsBichar.map_sub_left (hc : IsBichar c) (b b' : B) (a : A) : c (b - b') a = c b a * (c b' a)⁻¹ := by
  rw [sub_eq_add_neg, hc.2.1, hc.map_neg_left]

end bichar

/- English proof (translation)
Unfold `ind`. Conclude with `if_pos h`.
-/
theorem ind_of_mem {S : Set A} {t : A} (h : t ∈ S) : ind (k := k) S t = 1 := by
  unfold ind; exact if_pos h

/- English proof (translation)
Unfold `ind`. Conclude with `if_neg h`.
-/
theorem ind_of_not_mem {S : Set A} {t : A} (h : t ∉ S) : ind (k := k) S t = 0 := by
  unfold ind; exact if_neg h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gen_apply (c : B → A → k) (A₀ : AddSubgroup A) (a : A) (b : B) (t : A) :
    gen c A₀ a b t = c b (t + a) * ind (A₀ : Set A) (t + a) := rfl

/- English proof (translation)
Take `⟨hSN, hSinj, hSsurj⟩` from `hS`. Use `choose! σ hσ using hSsurj`. Establish `hfσ : ∀ y ∈ N, f (σ y) = f y`. Introduce `y hy`. Establish `h1 : y = (y - σ y) + σ y` using `by abel`.

Use `conv_rhs => rw [h1, hadd, hM _ (hσ y hy).2, one_mul]`. Establish `key : ∑ x ∈ S, f g₀ * f x = ∑ x ∈ S, f x`. Use `Finset.sum_nbij (fun x => σ (g₀ + x)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `(hσ _ (N.add_mem hg₀ (hSN x hx))).1`.

Introduce `x hx y hy hxy`. Establish `hx'` using `(hσ _ (N.add_mem hg₀ (hSN x hx))).2`. Establish `hy'` using `(hσ _ (N.add_mem hg₀ (hSN y hy))).2`. Simplify using `only at hxy`. Rewrite `hx'` using `[hxy]`.

Apply `hSinj x hx y hy` to reduce the goal to its premises. Use `M.sub_mem hx' hy'` as an intermediate fact. Establish `e : g₀ + x - σ (g₀ + y) - (g₀ + y - σ (g₀ + y)) = x - y` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Introduce `y hy`.

Establish `hyN : y - g₀ ∈ N` using `N.sub_mem (hSN y hy) hg₀`. Establish `h1` using `hσ _ hyN`. Use `⟨σ (y - g₀), h1.1, ?_⟩` and prove the remaining obligations. Establish `h2` using `hσ _ (N.add_mem hg₀ (hSN _ h1.1))`. Simplify using `only`.

Use `symm`. Apply `hSinj y hy _ h2.1` to reduce the goal to its premises. Use `M.add_mem h1.2 h2.2` as an intermediate fact. Establish `e : y - g₀ - σ (y - g₀) + (g₀ + σ (y - g₀) - σ (g₀ + σ (y - g₀))) = y - σ (g₀ + σ (y - g₀))` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Introduce `x hx`. Rewrite using `[hfσ _ (N.add_mem hg₀ (hSN x hx)), hadd]`. Rewrite `key` using `[← Finset.mul_sum]`. Establish `h2 : (f g₀ - 1) * ∑ x ∈ S, f x = 0` using `by rw [sub_mul, key, one_mul, sub_self]`. Break down `mul_eq_zero.mp h2 with h | h` into its components or cases.

Conclude with `absurd (sub_eq_zero.mp h) hne`. Conclude with `h`.
-/
theorem sum_reps_eq_zero {G : Type*} [AddCommGroup G] (M N : AddSubgroup G) (S : Finset G) (hS : IsRepsG M N S)
    (f : G → k) (hadd : ∀ x y, f (x + y) = f x * f y) (hM : ∀ x ∈ M, f x = 1) (g₀ : G) (hg₀ : g₀ ∈ N)
    (hne : f g₀ ≠ 1) : ∑ x ∈ S, f x = 0 := by
  obtain ⟨hSN, hSinj, hSsurj⟩ := hS
  choose! σ hσ using hSsurj
  have hfσ : ∀ y ∈ N, f (σ y) = f y := by
    intro y hy
    have h1 : y = (y - σ y) + σ y := by abel
    conv_rhs => rw [h1, hadd, hM _ (hσ y hy).2, one_mul]
  have key : ∑ x ∈ S, f g₀ * f x = ∑ x ∈ S, f x := by
    refine Finset.sum_nbij (fun x => σ (g₀ + x)) ?_ ?_ ?_ ?_
    · intro x hx
      exact (hσ _ (N.add_mem hg₀ (hSN x hx))).1
    · intro x hx y hy hxy
      have hx' := (hσ _ (N.add_mem hg₀ (hSN x hx))).2
      have hy' := (hσ _ (N.add_mem hg₀ (hSN y hy))).2
      simp only at hxy
      rw [hxy] at hx'
      apply hSinj x hx y hy
      have := M.sub_mem hx' hy'
      have e : g₀ + x - σ (g₀ + y) - (g₀ + y - σ (g₀ + y)) = x - y := by abel
      rwa [e] at this
    · intro y hy
      have hyN : y - g₀ ∈ N := N.sub_mem (hSN y hy) hg₀
      have h1 := hσ _ hyN
      refine ⟨σ (y - g₀), h1.1, ?_⟩
      have h2 := hσ _ (N.add_mem hg₀ (hSN _ h1.1))
      simp only
      symm
      apply hSinj y hy _ h2.1
      have := M.add_mem h1.2 h2.2
      have e : y - g₀ - σ (y - g₀) + (g₀ + σ (y - g₀) - σ (g₀ + σ (y - g₀))) = y - σ (g₀ + σ (y - g₀)) := by abel
      rwa [e] at this
    · intro x hx
      rw [hfσ _ (N.add_mem hg₀ (hSN x hx)), hadd]
  rw [← Finset.mul_sum] at key
  have h2 : (f g₀ - 1) * ∑ x ∈ S, f x = 0 := by rw [sub_mul, key, one_mul, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/- English proof (translation)
Take `⟨hSN, hSinj, hSsurj⟩` from `hS`. Distinguish the cases in `ht : t ∈ N`. Take `⟨x, hxS, hx⟩` from `hSsurj (-t) (N.neg_mem ht)`. Establish `hxM : t + x ∈ M`. Use `M.neg_mem hx` as an intermediate fact.

Establish `e : -(-t - x) = t + x` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[Finset.sum_eq_single x]`. Rewrite using `[ind_of_mem (show t + x ∈ (M : Set G) from hxM), ind_of_mem (show t + x ∈ (N : Set G) from N.add_mem ht (hSN x hxS)), ind_of_mem (show t ∈ (N : Set G) from ht), one_mul]`. Introduce `a haS hax`.

Establish `: t + a ∉ (M : Set G)`. Introduce `h`. Apply `hax` to reduce the goal to its premises. Apply `hSinj a haS x hxS` to reduce the goal to its premises. Use `M.add_mem h hx` as an intermediate fact.

Establish `e : t + a + (-t - x) = a - x` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[ind_of_not_mem this, zero_mul]`. Introduce `h`. Conclude with `absurd hxS h`.

Rewrite using `[ind_of_not_mem (show t ∉ (N : Set G) from ht)]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a ha`. Establish `: t + a ∉ (N : Set G)`. Introduce `h`.

Apply `ht` to reduce the goal to its premises. Use `N.sub_mem h (hSN a ha)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Then use the resulting hypothesis. Rewrite using `[ind_of_not_mem this, mul_zero]`.
-/
theorem sum_reps_ind {G : Type*} [AddCommGroup G] (M N : AddSubgroup G) (S : Finset G) (hS : IsRepsG M N S) (t : G) :
    ∑ a ∈ S, ind (k := k) (M : Set G) (t + a) * ind (k := k) (N : Set G) (t + a) = ind (k := k) (N : Set G) t := by
  obtain ⟨hSN, hSinj, hSsurj⟩ := hS
  by_cases ht : t ∈ N
  · obtain ⟨x, hxS, hx⟩ := hSsurj (-t) (N.neg_mem ht)
    have hxM : t + x ∈ M := by
      have := M.neg_mem hx
      have e : -(-t - x) = t + x := by abel
      rwa [e] at this
    rw [Finset.sum_eq_single x]
    · rw [ind_of_mem (show t + x ∈ (M : Set G) from hxM),
        ind_of_mem (show t + x ∈ (N : Set G) from N.add_mem ht (hSN x hxS)),
        ind_of_mem (show t ∈ (N : Set G) from ht), one_mul]
    · intro a haS hax
      have : t + a ∉ (M : Set G) := by
        intro h
        apply hax
        apply hSinj a haS x hxS
        have := M.add_mem h hx
        have e : t + a + (-t - x) = a - x := by abel
        rwa [e] at this
      rw [ind_of_not_mem this, zero_mul]
    · intro h; exact absurd hxS h
  · rw [ind_of_not_mem (show t ∉ (N : Set G) from ht)]
    apply Finset.sum_eq_zero
    intro a ha
    have : t + a ∉ (N : Set G) := by
      intro h
      apply ht
      have := N.sub_mem h (hSN a ha)
      rwa [add_sub_cancel_right] at this
    rw [ind_of_not_mem this, mul_zero]

/- English proof (translation)
Introduce `k _ A B _ _ c hc A₁ A₂ B₁ B₂ hB₁ h22 hA SA SB hSA hSB`. Use function extensionality and compare the values at `t`. Establish `hL : (∑ a ∈ SA, ∑ b ∈ SB, rhoA a (rhoB c b (ind (A₁ : Set A)))) t = ∑ a ∈ SA, ∑ b ∈ SB, c b (t + a) * ind (A₁ : Set A) (t + a)`. Simplify using `only [Finset.sum_apply]`. Both sides reduce to the same expression.

Establish `inner : ∀ u : A, ∑ b ∈ SB, c b u * ind (A₁ : Set A) u = (SB.card : k) * (ind (A₁ : Set A) u * ind (A₂ : Set A) u)`. Introduce `u`. Distinguish the cases in `hu1 : u ∈ A₁`. Rewrite using `[ind_of_mem (show u ∈ (A₁ : Set A) from hu1)]`. Distinguish the cases in `hu2 : u ∈ A₂`.

Rewrite using `[ind_of_mem (show u ∈ (A₂ : Set A) from hu2)]`. Rewrite using `[Finset.sum_congr rfl (fun b hb => by rw [h22 b (hSB.1 b hb) u hu2])]`. Simplify using the standard rewrite rules. Rewrite using `[ind_of_not_mem (show u ∉ (A₂ : Set A) from hu2)]`. Establish `hex : ∃ b₀ ∈ B₂, c b₀ u ≠ 1`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hu2 (hA u hu1 hcon)`. Take `⟨b₀, hb₀, hne⟩` from `hex`. Use `sum_reps_eq_zero B₁ B₂ SB hSB (fun b => c b u) (fun x y => hc.2.1 x y u) (fun x hx => (hB₁ x).mp hx u hu1) b₀ hb₀ hne` as an intermediate fact.

Simplify using `only [mul_one, mul_zero]`. Conclude with `this`. Rewrite using `[ind_of_not_mem (show u ∉ (A₁ : Set A) from hu1)]`. Simplify using the standard rewrite rules. Rewrite using `[hL, Finset.sum_congr rfl (fun a _ => inner (t + a)), ← Finset.mul_sum, sum_reps_ind A₁ A₂ SA hSA t]`.

Both sides reduce to the same expression.
-/
theorem model_moves_hold : ModelMoves := by
  intro k _ A B _ _ c hc A₁ A₂ B₁ B₂ hB₁ h22 hA SA SB hSA hSB
  funext t
  have hL : (∑ a ∈ SA, ∑ b ∈ SB, rhoA a (rhoB c b (ind (A₁ : Set A)))) t
      = ∑ a ∈ SA, ∑ b ∈ SB, c b (t + a) * ind (A₁ : Set A) (t + a) := by
    simp only [Finset.sum_apply]; rfl
  have inner : ∀ u : A, ∑ b ∈ SB, c b u * ind (A₁ : Set A) u
      = (SB.card : k) * (ind (A₁ : Set A) u * ind (A₂ : Set A) u) := by
    intro u
    by_cases hu1 : u ∈ A₁
    · rw [ind_of_mem (show u ∈ (A₁ : Set A) from hu1)]
      by_cases hu2 : u ∈ A₂
      · rw [ind_of_mem (show u ∈ (A₂ : Set A) from hu2)]
        rw [Finset.sum_congr rfl (fun b hb => by rw [h22 b (hSB.1 b hb) u hu2])]
        simp
      · rw [ind_of_not_mem (show u ∉ (A₂ : Set A) from hu2)]
        have hex : ∃ b₀ ∈ B₂, c b₀ u ≠ 1 := by
          by_contra hcon
          push Not at hcon
          exact hu2 (hA u hu1 hcon)
        obtain ⟨b₀, hb₀, hne⟩ := hex
        have := sum_reps_eq_zero B₁ B₂ SB hSB (fun b => c b u) (fun x y => hc.2.1 x y u)
          (fun x hx => (hB₁ x).mp hx u hu1) b₀ hb₀ hne
        simp only [mul_one, mul_zero]
        exact this
    · rw [ind_of_not_mem (show u ∉ (A₁ : Set A) from hu1)]
      simp
  rw [hL, Finset.sum_congr rfl (fun a _ => inner (t + a)), ← Finset.mul_sum, sum_reps_ind A₁ A₂ SA hSA t]
  rfl

section Heisenberg₂
variable {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T}

/- English proof (translation)
Rewrite using `[hW.1]`. Both sides reduce to the same expression.
-/
theorem IsHeis.WA_zero (hW : IsHeis c WA WB) (x : T) : WA 0 x = x := by rw [hW.1]; rfl

/- English proof (translation)
Rewrite using `[hW.2.2.1]`. Both sides reduce to the same expression.
-/
theorem IsHeis.WB_zero (hW : IsHeis c WA WB) (x : T) : WB 0 x = x := by rw [hW.2.2.1]; rfl

/- English proof (translation)
Rewrite using `[hW.2.1]`. Both sides reduce to the same expression.
-/
theorem IsHeis.WA_add (hW : IsHeis c WA WB) (a a' : A) (x : T) : WA (a + a') x = WA a (WA a' x) := by
  rw [hW.2.1]; rfl

/- English proof (translation)
Rewrite using `[hW.2.2.2.1]`. Both sides reduce to the same expression.
-/
theorem IsHeis.WB_add (hW : IsHeis c WA WB) (b b' : B) (x : T) : WB (b + b') x = WB b (WB b' x) := by
  rw [hW.2.2.2.1]; rfl

/- English proof (translation)
The claim follows from `LinearMap.congr_fun (hW.2.2.2.2 a b) x`.
-/
theorem IsHeis.comm (hW : IsHeis c WA WB) (a : A) (b : B) (x : T) : WA a (WB b x) = c b a • WB b (WA a x) :=
  LinearMap.congr_fun (hW.2.2.2.2 a b) x

end Heisenberg₂

/- English proof (translation)
Use extensionality with `⟨Φ, hΦ⟩`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨a, b⟩, rfl⟩` from `hx`. Conclude with `h a b`.

Consider the case `zero`. Establish `e : (⟨0, Submodule.zero_mem _⟩ : Sch c A₀) = 0` using `rfl`. Rewrite using `[e, map_zero, map_zero]`. Consider the case `add x y hx hy ihx ihy`. Establish `e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : Sch c A₀) = ⟨x, hx⟩ + ⟨y, hy⟩` using `rfl`.

Rewrite using `[e, map_add, map_add, ihx, ihy]`. Consider the case `smul r x hx ih`. Establish `e : (⟨r • x, Submodule.smul_mem _ r hx⟩ : Sch c A₀) = r • ⟨x, hx⟩` using `rfl`. Rewrite using `[e, map_smul, map_smul, ih]`.
-/
theorem Sch_ext {c : B → A → k} {A₀ : AddSubgroup A} {f g : Sch c A₀ →ₗ[k] T}
    (h : ∀ a b, f ⟨gen c A₀ a b, gen_mem c A₀ a b⟩ = g ⟨gen c A₀ a b, gen_mem c A₀ a b⟩) : f = g := by
  ext ⟨Φ, hΦ⟩
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact h a b
  | zero =>
    have e : (⟨0, Submodule.zero_mem _⟩ : Sch c A₀) = 0 := rfl
    rw [e, map_zero, map_zero]
  | add x y hx hy ihx ihy =>
    have e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : Sch c A₀) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, map_add, map_add, ihx, ihy]
  | smul r x hx ih =>
    have e : (⟨r • x, Submodule.smul_mem _ r hx⟩ : Sch c A₀) = r • ⟨x, hx⟩ := rfl
    rw [e, map_smul, map_smul, ih]

def chi (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) : Multiplicative A₀ →* k where
  toFun s := c b ((Multiplicative.toAdd s : A₀) : A)
  map_one' := hc.map_zero_right b
  map_mul' _ _ := hc.2.2 b _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chi_apply (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) (s : A₀) :
    chi c hc A₀ b (Multiplicative.ofAdd s) = c b (s : A) := rfl

def eFam (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) : A → k := by
  classical exact fun t => if h : t + i.1.out ∈ A₀ then i.2 (Multiplicative.ofAdd ⟨t + i.1.out, h⟩) else 0

/- English proof (translation)
Unfold `eFam`. Conclude with `dif_pos h`.
-/
theorem eFam_of_mem (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) (t : A) (h : t + i.1.out ∈ A₀) :
    eFam A₀ i t = i.2 (Multiplicative.ofAdd ⟨t + i.1.out, h⟩) := by
  unfold eFam; exact dif_pos h

/- English proof (translation)
Unfold `eFam`. Conclude with `dif_neg h`.
-/
theorem eFam_of_not_mem (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) (t : A) (h : t + i.1.out ∉ A₀) :
    eFam A₀ i t = 0 := by
  unfold eFam; exact dif_neg h

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientAddGroup.mk_out_eq_add A₀ a`. Rewrite using `[hh]`. Establish `e : a - (a + (h : A)) = -(h : A)` using `by abel`. Rewrite using `[e]`. Conclude with `A₀.neg_mem h.2`.
-/
theorem out_sub_mem (A₀ : AddSubgroup A) (a : A) : a - (QuotientAddGroup.mk a : A ⧸ A₀).out ∈ A₀ := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add A₀ a
  rw [hh]
  have e : a - (a + (h : A)) = -(h : A) := by abel
  rw [e]
  exact A₀.neg_mem h.2

/- English proof (translation)
Rewrite using `[← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']`. Use `symm`. Rewrite using `[QuotientAddGroup.eq]`. Establish `e : -q'.out + q.out = q.out - q'.out` using `by abel`. Rewrite using `[e]` and apply the resulting hypothesis.
-/
theorem eq_of_out_sub_mem (A₀ : AddSubgroup A) (q q' : A ⧸ A₀) (h : q.out - q'.out ∈ A₀) : q = q' := by
  rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
  symm
  rw [QuotientAddGroup.eq]
  have e : -q'.out + q.out = q.out - q'.out := by abel
  rwa [e]

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce and unpack `s g hg ⟨q₀, χ₀⟩ hi₀`. Establish `hli` using `linearIndependent_monoidHom (Multiplicative A₀) k`. Rewrite `hli` using `[linearIndependent_iff']`. Use `hli ((s.filter (fun i => i.1 = q₀)).image Prod.snd) (fun χ => g (q₀, χ)) ?_ χ₀ ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Establish `h1` using `congrFun hg (((Multiplicative.toAdd x : A₀) : A) - q₀.out)`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢`. Rewrite using `[Finset.sum_image, Finset.sum_filter]`. Use `(Finset.sum_congr rfl ?_).trans h1` and prove the remaining obligations.

Introduce and unpack `⟨q, χ⟩ _`. Distinguish the cases in `hq : q = q₀`. Substitute `hq` using the available equality. Establish `hm : ((Multiplicative.toAdd x : A₀) : A) - q.out + q.out ∈ A₀`. Rewrite using `[sub_add_cancel]`.

Conclude with `(Multiplicative.toAdd x).2`. Rewrite using `[if_pos rfl, eFam_of_mem A₀ (q, χ) _ hm]`. Use `congr 2`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Establish `hm : ((Multiplicative.toAdd x : A₀) : A) - q₀.out + q.out ∉ A₀`. Introduce `hm`. Apply `hq` to reduce the goal to its premises. Apply `eq_of_out_sub_mem A₀` to reduce the goal to its premises. Use `A₀.sub_mem hm (Multiplicative.toAdd x).2` as an intermediate fact.

Establish `e : ((Multiplicative.toAdd x : A₀) : A) - q₀.out + q.out - ((Multiplicative.toAdd x : A₀) : A) = q.out - q₀.out` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[if_neg hq, eFam_of_not_mem A₀ (q, χ) _ hm, mul_zero]`. Introduce and unpack `⟨q, χ⟩ h ⟨q', χ'⟩ h' hh`. Rewrite `h`, `h'` using `[Finset.mem_coe, Finset.mem_filter]`.

Simplify using `only at hh`. Conclude with `Prod.ext (h.2.trans h'.2.symm) hh`. Conclude with `Finset.mem_image.mpr ⟨(q₀, χ₀), Finset.mem_filter.mpr ⟨hi₀, rfl⟩, rfl⟩`.
-/
theorem eFam_li (A₀ : AddSubgroup A) : LinearIndependent k (eFam (k := k) A₀) := by
  classical
  rw [linearIndependent_iff']
  rintro s g hg ⟨q₀, χ₀⟩ hi₀
  have hli := linearIndependent_monoidHom (Multiplicative A₀) k
  rw [linearIndependent_iff'] at hli
  refine hli ((s.filter (fun i => i.1 = q₀)).image Prod.snd) (fun χ => g (q₀, χ)) ?_ χ₀ ?_
  · funext x
    have h1 := congrFun hg (((Multiplicative.toAdd x : A₀) : A) - q₀.out)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
    rw [Finset.sum_image, Finset.sum_filter]
    · refine (Finset.sum_congr rfl ?_).trans h1
      rintro ⟨q, χ⟩ _
      by_cases hq : q = q₀
      · subst hq
        have hm : ((Multiplicative.toAdd x : A₀) : A) - q.out + q.out ∈ A₀ := by
          rw [sub_add_cancel]; exact (Multiplicative.toAdd x).2
        rw [if_pos rfl, eFam_of_mem A₀ (q, χ) _ hm]
        congr 2
        apply Subtype.ext
        simp
      · have hm : ((Multiplicative.toAdd x : A₀) : A) - q₀.out + q.out ∉ A₀ := by
          intro hm
          apply hq
          apply eq_of_out_sub_mem A₀
          have := A₀.sub_mem hm (Multiplicative.toAdd x).2
          have e : ((Multiplicative.toAdd x : A₀) : A) - q₀.out + q.out - ((Multiplicative.toAdd x : A₀) : A)
              = q.out - q₀.out := by abel
          rwa [e] at this
        rw [if_neg hq, eFam_of_not_mem A₀ (q, χ) _ hm, mul_zero]
    · rintro ⟨q, χ⟩ h ⟨q', χ'⟩ h' hh
      rw [Finset.mem_coe, Finset.mem_filter] at h h'
      simp only at hh
      exact Prod.ext (h.2.trans h'.2.symm) hh
  · exact Finset.mem_image.mpr ⟨(q₀, χ₀), Finset.mem_filter.mpr ⟨hi₀, rfl⟩, rfl⟩

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `h0` using `out_sub_mem A₀ a`. Rewrite using `[gen_apply, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `h : t + (QuotientAddGroup.mk a : A ⧸ A₀).out ∈ A₀`. Establish `h' : t + a ∈ A₀`.

Use `A₀.add_mem h h0` as an intermediate fact. Establish `e : t + (QuotientAddGroup.mk a : A ⧸ A₀).out + (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) = t + a` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[ind_of_mem (show t + a ∈ (A₀ : Set A) from h'), mul_one, eFam_of_mem A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) t h, chi_apply, ← hc.2.2]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `t + a = a - (QuotientAddGroup.mk a : A ⧸ A₀).out + (t + (QuotientAddGroup.mk a : A ⧸ A₀).out)`. Normalize the expressions using the abelian group laws. Establish `h' : t + a ∉ (A₀ : Set A)`. Introduce `h'`. Apply `h` to reduce the goal to its premises.

Use `A₀.sub_mem h' h0` as an intermediate fact. Establish `e : t + a - (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) = t + (QuotientAddGroup.mk a : A ⧸ A₀).out` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[ind_of_not_mem h', eFam_of_not_mem A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) t h, mul_zero, mul_zero]`.
-/
theorem gen_eq_eFam (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (a : A) (b : B) :
    gen c A₀ a b = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
      eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) := by
  funext t
  have h0 := out_sub_mem A₀ a
  rw [gen_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : t + (QuotientAddGroup.mk a : A ⧸ A₀).out ∈ A₀
  · have h' : t + a ∈ A₀ := by
      have := A₀.add_mem h h0
      have e : t + (QuotientAddGroup.mk a : A ⧸ A₀).out + (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) = t + a := by abel
      rwa [e] at this
    rw [ind_of_mem (show t + a ∈ (A₀ : Set A) from h'), mul_one,
      eFam_of_mem A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) t h, chi_apply, ← hc.2.2]
    congr 1
    change t + a = a - (QuotientAddGroup.mk a : A ⧸ A₀).out + (t + (QuotientAddGroup.mk a : A ⧸ A₀).out)
    abel
  · have h' : t + a ∉ (A₀ : Set A) := by
      intro h'
      apply h
      have := A₀.sub_mem h' h0
      have e : t + a - (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) = t + (QuotientAddGroup.mk a : A ⧸ A₀).out := by abel
      rwa [e] at this
    rw [ind_of_not_mem h', eFam_of_not_mem A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) t h, mul_zero, mul_zero]

def wFam (c : B → A → k) (hc : IsBichar c) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T) (A₀ : AddSubgroup A) (θ : T)
    (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) : T := by
  classical exact if h : ∃ b, chi c hc A₀ b = i.2 then WA i.1.out (WB h.choose θ) else 0

/- English proof (translation)
Establish `h0` using `out_sub_mem A₀ a`. Establish `hex : ∃ b', chi c hc A₀ b' = chi c hc A₀ b` using `⟨b, rfl⟩`. Establish `hw : wFam c hc WA WB A₀ θ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) = WA (QuotientAddGroup.mk a : A ⧸ A₀).out (WB hex.choose θ)`. Unfold `wFam`. Conclude with `dif_pos hex`.

Establish `hb' : ∀ s ∈ A₀, c hex.choose s = c b s`. Introduce `s hs`. Use `DFunLike.congr_fun hex.choose_spec (Multiplicative.ofAdd (⟨s, hs⟩ : A₀))` as an intermediate fact. Rewrite `this` using `[chi_apply, chi_apply]`. Then use the resulting hypothesis. Establish `hθ : WB b θ = WB hex.choose θ`.

Establish `e : b = hex.choose + (b - hex.choose)` using `by abel`. Use `conv_lhs => rw [e, hW.WB_add]`. Rewrite using `[hB (b - hex.choose)]`. Introduce `s hs`. Rewrite using `[hc.map_sub_left, hb' s hs, mul_inv_cancel₀ (hc.1 b s)]`.

Rewrite using `[hw, hθ]`. Establish `e : a = (QuotientAddGroup.mk a : A ⧸ A₀).out + (a - (QuotientAddGroup.mk a : A ⧸ A₀).out)` using `by abel`. Use `conv_lhs => rw [e, hW.WA_add, hW.comm, hA _ h0, map_smul, hb' _ h0]`.
-/
theorem W_eq_wFam (c : B → A → k) (hc : IsBichar c) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T) (hW : IsHeis c WA WB)
    (A₀ : AddSubgroup A) (θ : T) (hA : ∀ a ∈ A₀, WA a θ = θ) (hB : ∀ b, (∀ a ∈ A₀, c b a = 1) → WB b θ = θ)
    (a : A) (b : B) :
    WA a (WB b θ) = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
      wFam c hc WA WB A₀ θ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) := by
  have h0 := out_sub_mem A₀ a
  have hex : ∃ b', chi c hc A₀ b' = chi c hc A₀ b := ⟨b, rfl⟩
  have hw : wFam c hc WA WB A₀ θ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b)
      = WA (QuotientAddGroup.mk a : A ⧸ A₀).out (WB hex.choose θ) := by
    unfold wFam; exact dif_pos hex
  have hb' : ∀ s ∈ A₀, c hex.choose s = c b s := by
    intro s hs
    have := DFunLike.congr_fun hex.choose_spec (Multiplicative.ofAdd (⟨s, hs⟩ : A₀))
    rwa [chi_apply, chi_apply] at this
  have hθ : WB b θ = WB hex.choose θ := by
    have e : b = hex.choose + (b - hex.choose) := by abel
    conv_lhs => rw [e, hW.WB_add]
    rw [hB (b - hex.choose)]
    intro s hs
    rw [hc.map_sub_left, hb' s hs, mul_inv_cancel₀ (hc.1 b s)]
  rw [hw, hθ]
  have e : a = (QuotientAddGroup.mk a : A ⧸ A₀).out + (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) := by abel
  conv_lhs => rw [e, hW.WA_add, hW.comm, hA _ h0, map_smul, hb' _ h0]

/- English proof (translation)
Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨⟨a, b⟩, rfl⟩`. Simplify using `only`. Rewrite using `[gen_eq_eFam c hc A₀ a b]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`.
-/
theorem Sch_le_span_eFam (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) :
    Sch c A₀ ≤ Submodule.span k (Set.range (eFam (k := k) A₀)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, b⟩, rfl⟩
  simp only
  rw [gen_eq_eFam c hc A₀ a b]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/- English proof (translation)
Introduce `k _ A B T _ _ _ _ c WA WB hc hW A₀ θ hA hB`. Use `⟨(Finsupp.linearCombination k (wFam c hc WA WB A₀ θ)) ∘ₗ (eFam_li (k := k) A₀).repr ∘ₗ Submodule.inclusion (Sch_le_span_eFam c hc A₀), ?_, ?_⟩` and prove the remaining obligations. Introduce `a b`. Establish `e : Submodule.inclusion (Sch_le_span_eFam c hc A₀) ⟨gen c A₀ a b, gen_mem c A₀ a b⟩ = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) • (⟨eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b), Submodule.subset_span ⟨_, rfl⟩⟩ : Submodule.span k (Set.range (eFam (k` using `k) A₀))) := by`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `gen_eq_eFam c hc A₀ a b`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, e, map_smul, map_smul, (eFam_li (k := k) A₀).repr_eq_single ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) _ rfl, Finsupp.linearCombination_single, one_smul]`. Conclude with `(W_eq_wFam c hc WA WB hW A₀ θ hA hB a b).symm`. Introduce `Xi' hXi'`. Apply `Sch_ext` to reduce the goal to its premises.

Introduce `a b`. Rewrite using `[hXi' a b]`. Establish `e : Submodule.inclusion (Sch_le_span_eFam c hc A₀) ⟨gen c A₀ a b, gen_mem c A₀ a b⟩ = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) • (⟨eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b), Submodule.subset_span ⟨_, rfl⟩⟩ : Submodule.span k (Set.range (eFam (k` using `k) A₀))) := by`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `gen_eq_eFam c hc A₀ a b`.

Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, e, map_smul, map_smul, (eFam_li (k := k) A₀).repr_eq_single ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) _ rfl, Finsupp.linearCombination_single, one_smul]`. Conclude with `W_eq_wFam c hc WA WB hW A₀ θ hA hB a b`.
-/
theorem xi_existence_holds : XiExists := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ θ hA hB
  refine ⟨(Finsupp.linearCombination k (wFam c hc WA WB A₀ θ)) ∘ₗ (eFam_li (k := k) A₀).repr ∘ₗ
    Submodule.inclusion (Sch_le_span_eFam c hc A₀), ?_, ?_⟩
  · intro a b
    have e : Submodule.inclusion (Sch_le_span_eFam c hc A₀) ⟨gen c A₀ a b, gen_mem c A₀ a b⟩
        = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
          (⟨eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b), Submodule.subset_span ⟨_, rfl⟩⟩ :
            Submodule.span k (Set.range (eFam (k := k) A₀))) := by
      apply Subtype.ext
      exact gen_eq_eFam c hc A₀ a b
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e, map_smul, map_smul,
      (eFam_li (k := k) A₀).repr_eq_single ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) _ rfl,
      Finsupp.linearCombination_single, one_smul]
    exact (W_eq_wFam c hc WA WB hW A₀ θ hA hB a b).symm
  · intro Xi' hXi'
    apply Sch_ext
    intro a b
    rw [hXi' a b]
    have e : Submodule.inclusion (Sch_le_span_eFam c hc A₀) ⟨gen c A₀ a b, gen_mem c A₀ a b⟩
        = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
          (⟨eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b), Submodule.subset_span ⟨_, rfl⟩⟩ :
            Submodule.span k (Set.range (eFam (k := k) A₀))) := by
      apply Subtype.ext
      exact gen_eq_eFam c hc A₀ a b
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e, map_smul, map_smul,
      (eFam_li (k := k) A₀).repr_eq_single ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) _ rfl,
      Finsupp.linearCombination_single, one_smul]
    exact W_eq_wFam c hc WA WB hW A₀ θ hA hB a b

/- English proof (translation)
Use function extensionality and compare the values at `t`. Express the relevant statement in the definitionally equal form `gen c A₀ a b (t + a') = _`. Rewrite using `[gen_apply, gen_apply, add_assoc]`.
-/
theorem rhoA_gen (c : B → A → k) (A₀ : AddSubgroup A) (a' a : A) (b : B) :
    rhoA a' (gen c A₀ a b) = gen c A₀ (a' + a) b := by
  funext t
  change gen c A₀ a b (t + a') = _
  rw [gen_apply, gen_apply, add_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Express the relevant statement in the definitionally equal form `c b' t * gen c A₀ a b t = (c b' a)⁻¹ * gen c A₀ a (b' + b) t`. Rewrite using `[gen_apply, gen_apply, hc.2.1, hc.2.2 b' t a]`. Establish `h` using `hc.1 b' a`. Clear the denominators using the available nonvanishing facts.
-/
theorem rhoB_gen (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b' : B) (a : A) (b : B) :
    rhoB c b' (gen c A₀ a b) = (c b' a)⁻¹ • gen c A₀ a (b' + b) := by
  funext t
  change c b' t * gen c A₀ a b t = (c b' a)⁻¹ * gen c A₀ a (b' + b) t
  rw [gen_apply, gen_apply, hc.2.1, hc.2.2 b' t a]
  have h := hc.1 b' a
  field_simp

/- English proof (translation)
Introduce `Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨a', b⟩, rfl⟩` from `hx`. Simplify using `only`.

Rewrite using `[rhoA_gen]`. Conclude with `gen_mem c A₀ _ _`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ ihx ihy => rw [map_add]`.

Conclude with `Submodule.add_mem _ ihx ihy`. Consider the case `smul r x _ ih => rw [map_smul]`. Conclude with `Submodule.smul_mem _ r ih`.
-/
theorem rhoA_mem (c : B → A → k) (A₀ : AddSubgroup A) (a : A) : ∀ Φ ∈ Sch c A₀, rhoA a Φ ∈ Sch c A₀ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a', b⟩, rfl⟩ := hx
    simp only
    rw [rhoA_gen]
    exact gen_mem c A₀ _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

/- English proof (translation)
Introduce `Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨a, b'⟩, rfl⟩` from `hx`. Simplify using `only`.

Rewrite using `[rhoB_gen c hc]`. Conclude with `Submodule.smul_mem _ _ (gen_mem c A₀ _ _)`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ ihx ihy => rw [map_add]`.

Conclude with `Submodule.add_mem _ ihx ihy`. Consider the case `smul r x _ ih => rw [map_smul]`. Conclude with `Submodule.smul_mem _ r ih`.
-/
theorem rhoB_mem (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) :
    ∀ Φ ∈ Sch c A₀, rhoB c b Φ ∈ Sch c A₀ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b'⟩, rfl⟩ := hx
    simp only
    rw [rhoB_gen c hc]
    exact Submodule.smul_mem _ _ (gen_mem c A₀ _ _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

/- English proof (translation)
Introduce `k _ A B T _ _ _ _ c WA WB hc hW A₀ θ Xi hXi Φ hΦ`. Prove the components needed by the constructor for the conclusion. Introduce `a`. Use `⟨rhoA_mem c A₀ a Φ hΦ, ?_⟩` and prove the remaining obligations. Establish `key : Xi ∘ₗ (rhoA a).restrict (rhoA_mem c A₀ a) = WA a ∘ₗ Xi`.

Apply `Sch_ext` to reduce the goal to its premises. Introduce `a' b`. Establish `e : (rhoA a).restrict (rhoA_mem c A₀ a) ⟨gen c A₀ a' b, gen_mem c A₀ a' b⟩ = ⟨gen c A₀ (a + a') b, gen_mem c A₀ (a + a') b⟩` using `Subtype.ext (rhoA_gen c A₀ a a' b)`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hXi, e, hXi, hW.WA_add]`. Conclude with `LinearMap.congr_fun key ⟨Φ, hΦ⟩`.

Introduce `b`. Use `⟨rhoB_mem c hc A₀ b Φ hΦ, ?_⟩` and prove the remaining obligations. Establish `key : Xi ∘ₗ (rhoB c b).restrict (rhoB_mem c hc A₀ b) = WB b ∘ₗ Xi`. Apply `Sch_ext` to reduce the goal to its premises. Introduce `a b'`.

Establish `e : (rhoB c b).restrict (rhoB_mem c hc A₀ b) ⟨gen c A₀ a b', gen_mem c A₀ a b'⟩ = (c b a)⁻¹ • ⟨gen c A₀ a (b + b'), gen_mem c A₀ a (b + b')⟩` using `Subtype.ext (rhoB_gen c hc A₀ b a b')`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hXi, e, map_smul, hXi, hW.WB_add, hW.comm, smul_smul, inv_mul_cancel₀ (hc.1 b a), one_smul]`. Conclude with `LinearMap.congr_fun key ⟨Φ, hΦ⟩`.
-/
theorem xi_intersection_holds : XiInter := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ θ Xi hXi Φ hΦ
  constructor
  · intro a
    refine ⟨rhoA_mem c A₀ a Φ hΦ, ?_⟩
    have key : Xi ∘ₗ (rhoA a).restrict (rhoA_mem c A₀ a) = WA a ∘ₗ Xi := by
      apply Sch_ext
      intro a' b
      have e : (rhoA a).restrict (rhoA_mem c A₀ a) ⟨gen c A₀ a' b, gen_mem c A₀ a' b⟩
          = ⟨gen c A₀ (a + a') b, gen_mem c A₀ (a + a') b⟩ := Subtype.ext (rhoA_gen c A₀ a a' b)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hXi, e, hXi, hW.WA_add]
    exact LinearMap.congr_fun key ⟨Φ, hΦ⟩
  · intro b
    refine ⟨rhoB_mem c hc A₀ b Φ hΦ, ?_⟩
    have key : Xi ∘ₗ (rhoB c b).restrict (rhoB_mem c hc A₀ b) = WB b ∘ₗ Xi := by
      apply Sch_ext
      intro a b'
      have e : (rhoB c b).restrict (rhoB_mem c hc A₀ b) ⟨gen c A₀ a b', gen_mem c A₀ a b'⟩
          = (c b a)⁻¹ • ⟨gen c A₀ a (b + b'), gen_mem c A₀ a (b + b')⟩ := Subtype.ext (rhoB_gen c hc A₀ b a b')
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hXi, e, map_smul, hXi, hW.WB_add, hW.comm, smul_smul,
        inv_mul_cancel₀ (hc.1 b a), one_smul]
    exact LinearMap.congr_fun key ⟨Φ, hΦ⟩

/- English proof (translation)
Substitute `hΦ` using the available equality. Use `⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (gen_mem c A₀ _ _), ?_⟩` and prove the remaining obligations. Establish `e : (⟨∑ i ∈ s, r i • gen c A₀ (a i) (b i), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (gen_mem c A₀ _ _)⟩ : Sch c A₀) = ∑ i ∈ s, r i • ⟨gen c A₀ (a i) (b i), gen_mem c A₀ (a i) (b i)⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Rewrite using `[e, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hXi]`.
-/
theorem Xi_of_eq_sum {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T} {A₀ : AddSubgroup A} {θ : T}
    {Xi : Sch c A₀ →ₗ[k] T} (hXi : IsXi c WA WB A₀ θ Xi) {ι : Type*} (s : Finset ι) (r : ι → k) (a : ι → A)
    (b : ι → B) (Φ : A → k) (hΦ : Φ = ∑ i ∈ s, r i • gen c A₀ (a i) (b i)) :
    ∃ h : Φ ∈ Sch c A₀, Xi ⟨Φ, h⟩ = ∑ i ∈ s, r i • WA (a i) (WB (b i) θ) := by
  subst hΦ
  refine ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (gen_mem c A₀ _ _), ?_⟩
  have e : (⟨∑ i ∈ s, r i • gen c A₀ (a i) (b i),
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (gen_mem c A₀ _ _)⟩ : Sch c A₀)
      = ∑ i ∈ s, r i • ⟨gen c A₀ (a i) (b i), gen_mem c A₀ (a i) (b i)⟩ := by
    apply Subtype.ext
    simp
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hXi]

/- English proof (translation)
Introduce `k _ A B T _ _ _ _ c WA WB hc hW A₀ A₁ B₀ B₁ θ Xi hXi hB₀ h11 hA SA SB hSA hSB hcard`. Establish `hM : ∑ a ∈ SA, ∑ b ∈ SB, gen c A₀ a b = (SB.card : k) • ind (A₁ : Set A)` using `model_moves_hold k A B c hc A₀ A₁ B₀ B₁ hB₀ h11 hA SA SB hSA hSB`. Establish `hexp : ind (A₁ : Set A) = ∑ i ∈ SA ×ˢ SB, (SB.card : k)⁻¹ • gen c A₀ i.1 i.2`. Rewrite using `[← Finset.smul_sum, Finset.sum_product, hM, smul_smul, inv_mul_cancel₀ hcard, one_smul]`. Take `⟨h, hval⟩` from `Xi_of_eq_sum hXi (SA ×ˢ SB) (fun _ => (SB.card : k)⁻¹) Prod.fst Prod.snd _ hexp`.

Use `⟨h, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, ← Finset.smul_sum, smul_smul, mul_inv_cancel₀ hcard, one_smul, Finset.sum_product]`.
-/
theorem lattice_moves_hold : Moves := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ A₁ B₀ B₁ θ Xi hXi hB₀ h11 hA SA SB hSA hSB hcard
  have hM : ∑ a ∈ SA, ∑ b ∈ SB, gen c A₀ a b = (SB.card : k) • ind (A₁ : Set A) :=
    model_moves_hold k A B c hc A₀ A₁ B₀ B₁ hB₀ h11 hA SA SB hSA hSB
  have hexp : ind (A₁ : Set A) = ∑ i ∈ SA ×ˢ SB, (SB.card : k)⁻¹ • gen c A₀ i.1 i.2 := by
    rw [← Finset.smul_sum, Finset.sum_product, hM, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  obtain ⟨h, hval⟩ := Xi_of_eq_sum hXi (SA ×ˢ SB) (fun _ => (SB.card : k)⁻¹) Prod.fst Prod.snd _ hexp
  refine ⟨h, ?_⟩
  rw [hval, ← Finset.smul_sum, smul_smul, mul_inv_cancel₀ hcard, one_smul, Finset.sum_product]

/- English proof (translation)
Establish `e : gen c A₀ a 0 = gen c A₀ 0 0`. Use function extensionality and compare the values at `t`. Rewrite using `[gen_apply, gen_apply, hc.map_zero_left, hc.map_zero_left, add_zero]`. Distinguish the cases in `ht : t ∈ A₀`. Rewrite using `[ind_of_mem (show t ∈ (A₀ : Set A) from ht), ind_of_mem (show t + a ∈ (A₀ : Set A) from A₀.add_mem ht ha)]`.

Establish `: t + a ∉ (A₀ : Set A)`. Introduce `h`. Apply `ht` to reduce the goal to its premises. Use `A₀.sub_mem h ha` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Then use the resulting hypothesis.

Rewrite using `[ind_of_not_mem (show t ∉ (A₀ : Set A) from ht), ind_of_not_mem this]`. Establish `h1` using `hXi a 0`. Establish `h2` using `hXi 0 0`. Establish `e' : (⟨gen c A₀ a 0, gen_mem c A₀ a 0⟩ : Sch c A₀) = ⟨gen c A₀ 0 0, gen_mem c A₀ 0 0⟩` using `Subtype.ext e`. Rewrite `h1` using `[e', h2, hW.WB_zero, hW.WA_zero]`.

Conclude with `h1.symm`.
-/
theorem IsXi.fixed {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T} {A₀ : AddSubgroup A} {θ : T}
    {Xi : Sch c A₀ →ₗ[k] T} (hXi : IsXi c WA WB A₀ θ Xi) (hc : IsBichar c) (hW : IsHeis c WA WB) (a : A)
    (ha : a ∈ A₀) : WA a θ = θ := by
  have e : gen c A₀ a 0 = gen c A₀ 0 0 := by
    funext t
    rw [gen_apply, gen_apply, hc.map_zero_left, hc.map_zero_left, add_zero]
    by_cases ht : t ∈ A₀
    · rw [ind_of_mem (show t ∈ (A₀ : Set A) from ht), ind_of_mem (show t + a ∈ (A₀ : Set A) from A₀.add_mem ht ha)]
    · have : t + a ∉ (A₀ : Set A) := by
        intro h
        apply ht
        have := A₀.sub_mem h ha
        rwa [add_sub_cancel_right] at this
      rw [ind_of_not_mem (show t ∉ (A₀ : Set A) from ht), ind_of_not_mem this]
  have h1 := hXi a 0
  have h2 := hXi 0 0
  have e' : (⟨gen c A₀ a 0, gen_mem c A₀ a 0⟩ : Sch c A₀) = ⟨gen c A₀ 0 0, gen_mem c A₀ 0 0⟩ := Subtype.ext e
  rw [e', h2, hW.WB_zero, hW.WA_zero] at h1
  exact h1.symm

/- English proof (translation)
Introduce `k _ A B T _ _ _ _ c WA WB hc hW A₀ A₂ B₀ B₂ θ Xi hXi h20 hB₀ hB₂ hA SA SB hSA hSB hcard Φ hsupp hinv`. Establish `hreps0 : IsRepsG A₀ A₂ ({0} : Finset A)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Finset.mem_singleton]`.

Rewrite using `[hx]`. Conclude with `A₂.zero_mem`. Introduce `x hx y hy _`. Rewrite `hx`, `hy` using `[Finset.mem_singleton]`. Rewrite using `[hx, hy]`.

Introduce `y hy`. Conclude with `⟨0, Finset.mem_singleton_self 0, by rw [sub_zero]; exact h20 hy⟩`. Establish `hM : ∑ b ∈ SB, gen c A₀ 0 b = (SB.card : k) • ind (A₂ : Set A)`. Use `model_moves_hold k A B c hc A₀ A₂ B₀ B₂ hB₀ (fun b hb a ha => (hB₂ b).mp hb a ha) hA {0} SB hreps0 hSB` as an intermediate fact. Rewrite `this` using `[Finset.sum_singleton]`. Then use the resulting hypothesis.

Establish `hexp : Φ = ∑ i ∈ SA ×ˢ SB, (Φ i.1 * (SB.card : k)⁻¹) • gen c A₀ (-i.1) i.2`. Use function extensionality and compare the values at `u`. Rewrite using `[Finset.sum_product, Finset.sum_apply]`. Establish `hin : ∀ t : A, (∑ b ∈ SB, (Φ t * (SB.card : k)⁻¹) • gen c A₀ (-t) b) u = Φ t * ind (A₂ : Set A) (u - t)`. Introduce `t`.

Establish `h1` using `congrFun hM (u - t)`. Rewrite `h1` using `[Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← Finset.smul_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]`. Establish `h2 : ∑ b ∈ SB, gen c A₀ (-t) b u = ∑ b ∈ SB, gen c A₀ 0 b (u - t)`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[gen_apply, gen_apply, add_zero, sub_eq_add_neg]`. Rewrite using `[h2, h1, mul_assoc, ← mul_assoc _ (SB.card : k), inv_mul_cancel₀ hcard, one_mul]`. Rewrite using `[Finset.sum_congr rfl (fun t _ => hin t)]`. Distinguish the cases in `hu : u ∈ A₀`. Take `⟨x, hxS, hx⟩` from `hSA.2.2 u hu`.

Rewrite using `[Finset.sum_eq_single x]`. Rewrite using `[ind_of_mem (show u - x ∈ (A₂ : Set A) from hx), mul_one]`. Use `hinv x (u - x) hx` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Introduce `t htS htx`.

Establish `: u - t ∉ (A₂ : Set A)`. Introduce `h`. Apply `htx` to reduce the goal to its premises. Apply `hSA.2.1 t htS x hxS` to reduce the goal to its premises. Use `A₂.sub_mem hx h` as an intermediate fact.

Establish `e : u - x - (u - t) = t - x` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Rewrite using `[ind_of_not_mem this, mul_zero]`. Introduce `h`. Conclude with `absurd hxS h`.

Rewrite using `[hsupp u hu]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `t ht`. Establish `: u - t ∉ (A₂ : Set A)`.

Introduce `h`. Apply `hu` to reduce the goal to its premises. Use `A₀.add_mem (h20 h) (hSA.1 t ht)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Rewrite using `[ind_of_not_mem this, mul_zero]`.

Take `⟨h, hval⟩` from `Xi_of_eq_sum hXi (SA ×ˢ SB) (fun i => Φ i.1 * (SB.card : k)⁻¹) (fun i => -i.1) Prod.snd _ hexp`. Use `⟨h, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, Finset.sum_product_right]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Rewrite using `[hW.comm, hXi.fixed hc hW (-t) (A₀.neg_mem (hSA.1 t ht)), hc.map_neg_right, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourier_transform_identity_holds : Fourier := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ A₂ B₀ B₂ θ Xi hXi h20 hB₀ hB₂ hA SA SB hSA hSB hcard Φ hsupp hinv
  have hreps0 : IsRepsG A₀ A₂ ({0} : Finset A) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]; exact A₂.zero_mem
    · intro x hx y hy _
      rw [Finset.mem_singleton] at hx hy
      rw [hx, hy]
    · intro y hy
      exact ⟨0, Finset.mem_singleton_self 0, by rw [sub_zero]; exact h20 hy⟩
  have hM : ∑ b ∈ SB, gen c A₀ 0 b = (SB.card : k) • ind (A₂ : Set A) := by
    have := model_moves_hold k A B c hc A₀ A₂ B₀ B₂ hB₀ (fun b hb a ha => (hB₂ b).mp hb a ha) hA {0} SB hreps0 hSB
    rwa [Finset.sum_singleton] at this
  have hexp : Φ = ∑ i ∈ SA ×ˢ SB, (Φ i.1 * (SB.card : k)⁻¹) • gen c A₀ (-i.1) i.2 := by
    funext u
    rw [Finset.sum_product, Finset.sum_apply]
    have hin : ∀ t : A, (∑ b ∈ SB, (Φ t * (SB.card : k)⁻¹) • gen c A₀ (-t) b) u = Φ t * ind (A₂ : Set A) (u - t) := by
      intro t
      have h1 := congrFun hM (u - t)
      rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [← Finset.smul_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      have h2 : ∑ b ∈ SB, gen c A₀ (-t) b u = ∑ b ∈ SB, gen c A₀ 0 b (u - t) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gen_apply, gen_apply, add_zero, sub_eq_add_neg]
      rw [h2, h1, mul_assoc, ← mul_assoc _ (SB.card : k), inv_mul_cancel₀ hcard, one_mul]
    rw [Finset.sum_congr rfl (fun t _ => hin t)]
    by_cases hu : u ∈ A₀
    · obtain ⟨x, hxS, hx⟩ := hSA.2.2 u hu
      rw [Finset.sum_eq_single x]
      · rw [ind_of_mem (show u - x ∈ (A₂ : Set A) from hx), mul_one]
        have := hinv x (u - x) hx
        rwa [add_sub_cancel] at this
      · intro t htS htx
        have : u - t ∉ (A₂ : Set A) := by
          intro h
          apply htx
          apply hSA.2.1 t htS x hxS
          have := A₂.sub_mem hx h
          have e : u - x - (u - t) = t - x := by abel
          rwa [e] at this
        rw [ind_of_not_mem this, mul_zero]
      · intro h; exact absurd hxS h
    · rw [hsupp u hu]
      symm
      apply Finset.sum_eq_zero
      intro t ht
      have : u - t ∉ (A₂ : Set A) := by
        intro h
        apply hu
        have := A₀.add_mem (h20 h) (hSA.1 t ht)
        rwa [sub_add_cancel] at this
      rw [ind_of_not_mem this, mul_zero]
  obtain ⟨h, hval⟩ := Xi_of_eq_sum hXi (SA ×ˢ SB) (fun i => Φ i.1 * (SB.card : k)⁻¹) (fun i => -i.1) Prod.snd _ hexp
  refine ⟨h, ?_⟩
  rw [hval, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hW.comm, hXi.fixed hc hW (-t) (A₀.neg_mem (hSA.1 t ht)), hc.map_neg_right, smul_smul]
  congr 1
  ring

/- English proof (translation)
The claim follows from `lattice_moves_hold`.
-/
theorem Moves_of (_h1 : ModelMoves) (_h3 : XiInter) : Moves := lattice_moves_hold

/- English proof (translation)
The claim follows from `fourier_transform_identity_holds`.
-/
theorem Fourier_of (_h1 : ModelMoves) (_h3 : XiInter) : Fourier := fourier_transform_identity_holds

end Formalism.L2.PairingIndexBounds.Mv

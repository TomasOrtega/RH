import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private def dM {n : ℕ} (x : Wt n) : ℝ := ∑ a, ∑ b, (x a - x b) ^ 2

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _`.
-/
private theorem dM_nonneg {n : ℕ} (x : Wt n) : 0 ≤ dM x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/- English proof (translation)
Unfold `dM`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem dM_perm {n : ℕ} (x : Wt n) (w : Equiv.Perm (Fin n)) : dM (x ∘ w) = dM x := by
  unfold dM
  calc ∑ a, ∑ b, ((x ∘ w) a - (x ∘ w) b) ^ 2 = ∑ a, ∑ b, (x (w a) - x b) ^ 2 :=
        Finset.sum_congr rfl fun a _ => Equiv.sum_comp w (fun b => (x (w a) - x b) ^ 2)
    _ = ∑ a, ∑ b, (x a - x b) ^ 2 := Equiv.sum_comp w (fun a => ∑ b, (x a - x b) ^ 2)

/- English proof (translation)
Establish `h : ∀ a, ∑ b, (x a - x b) ^ 2 = n * x a ^ 2 - 2 * x a * (∑ b, x b) + ∑ b, x b ^ 2`. Introduce `a`. Simplify using `only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Unfold `dM`. Simplify using `only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dM_eq {n : ℕ} (x : Wt n) :
    dM x = 2 * n * ∑ a, x a ^ 2 - 2 * (∑ a, x a) ^ 2 := by
  have h : ∀ a, ∑ b, (x a - x b) ^ 2 = n * x a ^ 2 - 2 * x a * (∑ b, x b) + ∑ b, x b ^ 2 := by
    intro a
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold dM
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/- English proof (translation)
Use `choose m hm using h`. Establish `h1 : dM x = ((∑ a, ∑ b, (m a b) ^ 2 : ℤ) : ℝ)`. Simplify using `[dM, hm]`. Establish `h0 : 0 ≤ ∑ a, ∑ b, (m a b) ^ 2` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _`. Take `⟨k, hk⟩` from `Int.eq_ofNat_of_zero_le h0`.

Conclude with `⟨k, by rw [h1, hk]; simp⟩`.
-/
private theorem dM_nat {n : ℕ} (x : Wt n) (h : ∀ a b, ∃ m : ℤ, x a - x b = m) :
    ∃ k : ℕ, dM x = k := by
  choose m hm using h
  have h1 : dM x = ((∑ a, ∑ b, (m a b) ^ 2 : ℤ) : ℝ) := by
    simp [dM, hm]
  have h0 : 0 ≤ ∑ a, ∑ b, (m a b) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h0
  exact ⟨k, by rw [h1, hk]; simp⟩

/- English proof (translation)
Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases. Take `⟨m, hm⟩` from `h a b hab`. Conclude with `⟨m, by simp [hm]⟩`. Conclude with `⟨0, by simp⟩`. Take `⟨m, hm⟩` from `h b a hab`.

Conclude with `⟨-m, by push_cast; linarith⟩`.
-/
private theorem dom_int {n : ℕ} {x : Wt n} (h : Dom x) (a b : Fin n) :
    ∃ m : ℤ, x a - x b = m := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨m, hm⟩ := h a b hab
    exact ⟨m, by simp [hm]⟩
  · exact ⟨0, by simp⟩
  · obtain ⟨m, hm⟩ := h b a hab
    exact ⟨-m, by push_cast; linarith⟩

/- English proof (translation)
Establish `h : ∑ i, (r i * u (Equiv.swap a b i) - r i * u i) = (r a - r b) * (u b - u a)`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ {a, b})]`. Rewrite using `[Finset.sum_pair hab]`. Simplify using `only [Equiv.swap_apply_left, Equiv.swap_apply_right]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `i _ hi`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne hi.1 hi.2, sub_self]`. Rewrite `h` using `[Finset.sum_sub_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem sum_swap {n : ℕ} (r u : Wt n) {a b : Fin n} (hab : a ≠ b) :
    ∑ i, r i * u (Equiv.swap a b i) = ∑ i, r i * u i + (r a - r b) * (u b - u a) := by
  have h : ∑ i, (r i * u (Equiv.swap a b i) - r i * u i) = (r a - r b) * (u b - u a) := by
    rw [← Finset.sum_subset (Finset.subset_univ {a, b})]
    · rw [Finset.sum_pair hab]
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    · intro i _ hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [Equiv.swap_apply_of_ne_of_ne hi.1 hi.2, sub_self]
  rw [Finset.sum_sub_distrib] at h
  linarith

/- English proof (translation)
Take `⟨hre, hdom, hanti, -, -, -⟩` from `rearr n`. Establish `hex : ∃ a b, a < b ∧ (κ ∘ w) a < (κ ∘ w) b`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hu : Antitone (κ ∘ w)`.

Introduce `a b hab`. Break down `hab.lt_or_eq with h | rfl` into its components or cases. Conclude with `hcon a b h`. Conclude with `le_rfl`. Apply `hne` to reduce the goal to its premises.

Establish `h1` using `(hdom (κ ∘ w)).2.2.1 hu`. Establish `h2` using `(hdom κ).2.2.2.1 w`. Establish `h3` using `(hdom κ).2.2.1 hκ`. Rewrite using `[← h1, h2, h3]`. Take `⟨a, b, hab, hlt⟩` from `hex`.

Establish `h1` using `(hre (rhoV n) κ hanti.antitone hκ (w * Equiv.swap a b)).1`. Establish `h2` using `sum_swap (rhoV n) (κ ∘ w) hab.ne`. Establish `h3 : ∑ i, rhoV n i * (κ ∘ w) (Equiv.swap a b i) = ∑ i, rhoV n i * κ ((w * Equiv.swap a b) i)` using `rfl`. Establish `h4 : 0 < (rhoV n a - rhoV n b) * ((κ ∘ w) b - (κ ∘ w) a)` using `mul_pos (sub_pos.2 (hanti hab)) (sub_pos.2 hlt)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem rho_strict {n : ℕ} {κ : Wt n} (hκ : Antitone κ) (w : Equiv.Perm (Fin n))
    (hne : κ ∘ w ≠ κ) : ∑ a, rhoV n a * (κ ∘ w) a < ∑ a, rhoV n a * κ a := by
  obtain ⟨hre, hdom, hanti, -, -, -⟩ := rearr n
  have hex : ∃ a b, a < b ∧ (κ ∘ w) a < (κ ∘ w) b := by
    by_contra hcon
    push_neg at hcon
    have hu : Antitone (κ ∘ w) := by
      intro a b hab
      rcases hab.lt_or_eq with h | rfl
      · exact hcon a b h
      · exact le_rfl
    apply hne
    have h1 := (hdom (κ ∘ w)).2.2.1 hu
    have h2 := (hdom κ).2.2.2.1 w
    have h3 := (hdom κ).2.2.1 hκ
    rw [← h1, h2, h3]
  obtain ⟨a, b, hab, hlt⟩ := hex
  have h1 := (hre (rhoV n) κ hanti.antitone hκ (w * Equiv.swap a b)).1
  have h2 := sum_swap (rhoV n) (κ ∘ w) hab.ne
  have h3 : ∑ i, rhoV n i * (κ ∘ w) (Equiv.swap a b i) = ∑ i, rhoV n i * κ ((w * Equiv.swap a b) i) := rfl
  have h4 : 0 < (rhoV n a - rhoV n b) * ((κ ∘ w) b - (κ ∘ w) a) :=
    mul_pos (sub_pos.2 (hanti hab)) (sub_pos.2 hlt)
  linarith

/- English proof (translation)
Establish `hs` using `rho_strict hκ w hne`. Establish `hn : 0 < n`. Break down `Nat.eq_zero_or_pos n with rfl | h` into its components or cases. Simplify using `at hs`. Conclude with `h`.

Establish `hnR : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `e1 : ∑ a, (κ ∘ w) a = ∑ a, κ a` using `Equiv.sum_comp w κ`. Establish `e2 : ∑ a, (κ ∘ w) a ^ 2 = ∑ a, κ a ^ 2` using `Equiv.sum_comp w (fun a => κ a ^ 2)`. Establish `q : ∀ u : Wt n, ∑ a, (u + rhoV n) a ^ 2 = ∑ a, u a ^ 2 + 2 * ∑ a, rhoV n a * u a + ∑ a, rhoV n a ^ 2`. Introduce `u`.

Simplify using `only [Pi.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]`. Use `congr 1`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`. Establish `l : ∀ u : Wt n, ∑ a, (u + rhoV n) a = ∑ a, u a + ∑ a, rhoV n a`.

Introduce `u`. Simplify using `only [Pi.add_apply, Finset.sum_add_distrib]`. Rewrite using `[dM_eq, dM_eq, q, q, l, l, e1, e2]`. Use `mul_lt_mul_of_pos_left hs hnR` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem dM_lt {n : ℕ} {κ : Wt n} (hκ : Antitone κ) (w : Equiv.Perm (Fin n))
    (hne : κ ∘ w ≠ κ) : dM (κ ∘ w + rhoV n) < dM (κ + rhoV n) := by
  have hs := rho_strict hκ w hne
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hs
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : ∑ a, (κ ∘ w) a = ∑ a, κ a := Equiv.sum_comp w κ
  have e2 : ∑ a, (κ ∘ w) a ^ 2 = ∑ a, κ a ^ 2 := Equiv.sum_comp w (fun a => κ a ^ 2)
  have q : ∀ u : Wt n, ∑ a, (u + rhoV n) a ^ 2 =
      ∑ a, u a ^ 2 + 2 * ∑ a, rhoV n a * u a + ∑ a, rhoV n a ^ 2 := by
    intro u
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring
  have l : ∀ u : Wt n, ∑ a, (u + rhoV n) a = ∑ a, u a + ∑ a, rhoV n a := by
    intro u
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [dM_eq, dM_eq, q, q, l, l, e1, e2]
  have := mul_lt_mul_of_pos_left hs hnR
  nlinarith

/- English proof (translation)
Establish `key : ∀ (d a : ℕ) (h : a + d < n), (d : ℝ) ≤ x ⟨a, by omega⟩ - x ⟨a + d, h⟩`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro a h`. Simplify using the standard rewrite rules.

Consider the case `succ d ih`. Introduce `a h`. Establish `h1` using `ih a (by omega)`. Establish `h2 : x ⟨a + d + 1, h⟩ < x ⟨a + d, by omega⟩` using `hx (by simp [Fin.lt_def])`. Take `⟨m, hm⟩` from `hi ⟨a + d, by omega⟩ ⟨a + d + 1, h⟩`.

Establish `h3 : (0 : ℝ) < m` using `by rw [← hm]; linarith`. Establish `h4 : (1 : ℝ) ≤ m` using `by exact_mod_cast (by exact_mod_cast h3 : (0 : ℤ) < m)`. Establish `h5 : x ⟨a + (d + 1), h⟩ = x ⟨a + d + 1, h⟩` using `rfl`. Use `push_cast`. Rewrite using `[h5]`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `a b hab`. Take `⟨m, hm⟩` from `hi a b`. Establish `hd : a.val + (b.val - a.val) < n` using `by have := b.2; have := Fin.lt_def.1 hab; omega`. Establish `h1` using `key (b.val - a.val) a.val hd`.

Establish `h2 : (⟨a.val + (b.val - a.val), hd⟩ : Fin n) = b` using `by ext; have := Fin.lt_def.1 hab; simp; omega`. Rewrite `h1` using `[h2]`. Establish `h3 : (((b.val - a.val : ℕ) : ℤ) : ℝ) ≤ m`. Rewrite using `[← hm]`. Simplify using `using h1`.

Establish `h4 : ((b.val - a.val : ℕ) : ℤ) ≤ m` using `by exact_mod_cast h3`. Take `⟨t, ht⟩` from `Int.eq_ofNat_of_zero_le (sub_nonneg.2 h4)`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `h5 : ((b.val - a.val : ℕ) : ℝ) = (b.val : ℝ) - a.val`. Rewrite using `[Nat.cast_sub (Fin.lt_def.1 hab).le]`.

Establish `h6 : (t : ℝ) = (m : ℝ) - ((b.val - a.val : ℕ) : ℝ)`. Establish `: ((t : ℤ) : ℝ) = ((m - ((b.val - a.val : ℕ) : ℤ) : ℤ) : ℝ)` using `by rw [ht]`. Simplify using `using this`. Simplify using `only [Pi.sub_apply, rhoV]`. Rewrite using `[h6, h5, ← hm]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dom_sub {n : ℕ} {x : Wt n} (hx : StrictAnti x)
    (hi : ∀ a b, ∃ m : ℤ, x a - x b = m) : Dom (x - rhoV n) := by
  have key : ∀ (d a : ℕ) (h : a + d < n),
      (d : ℝ) ≤ x ⟨a, by omega⟩ - x ⟨a + d, h⟩ := by
    intro d
    induction d with
    | zero => intro a h; simp
    | succ d ih =>
      intro a h
      have h1 := ih a (by omega)
      have h2 : x ⟨a + d + 1, h⟩ < x ⟨a + d, by omega⟩ := hx (by simp [Fin.lt_def])
      obtain ⟨m, hm⟩ := hi ⟨a + d, by omega⟩ ⟨a + d + 1, h⟩
      have h3 : (0 : ℝ) < m := by rw [← hm]; linarith
      have h4 : (1 : ℝ) ≤ m := by exact_mod_cast (by exact_mod_cast h3 : (0 : ℤ) < m)
      have h5 : x ⟨a + (d + 1), h⟩ = x ⟨a + d + 1, h⟩ := rfl
      push_cast
      rw [h5]
      linarith
  intro a b hab
  obtain ⟨m, hm⟩ := hi a b
  have hd : a.val + (b.val - a.val) < n := by have := b.2; have := Fin.lt_def.1 hab; omega
  have h1 := key (b.val - a.val) a.val hd
  have h2 : (⟨a.val + (b.val - a.val), hd⟩ : Fin n) = b := by
    ext; have := Fin.lt_def.1 hab; simp; omega
  rw [h2] at h1
  have h3 : (((b.val - a.val : ℕ) : ℤ) : ℝ) ≤ m := by
    rw [← hm]; simpa using h1
  have h4 : ((b.val - a.val : ℕ) : ℤ) ≤ m := by exact_mod_cast h3
  obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h4)
  refine ⟨t, ?_⟩
  have h5 : ((b.val - a.val : ℕ) : ℝ) = (b.val : ℝ) - a.val := by
    rw [Nat.cast_sub (Fin.lt_def.1 hab).le]
  have h6 : (t : ℝ) = (m : ℝ) - ((b.val - a.val : ℕ) : ℝ) := by
    have : ((t : ℤ) : ℝ) = ((m - ((b.val - a.val : ℕ) : ℤ) : ℤ) : ℝ) := by rw [ht]
    simpa using this
  simp only [Pi.sub_apply, rhoV]
  rw [h6, h5, ← hm]
  ring

/- English proof (translation)
Simplify using `[cf, ex, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]`.
-/
private theorem cf_ex {n : ℕ} (x y : Wt n) : cf (ex y) x = if y = x then 1 else 0 := by
  simp [cf, ex, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/- English proof (translation)
Simplify using `[cf]`.
-/
private theorem cf_zero {n : ℕ} (x : Wt n) : cf (0 : FR n) x = 0 := by
  simp [cf]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [cf_zero]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ((cfBasic n).2.2.2.1 _ _ 0 x).1, ih]`.
-/
private theorem cf_sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → FR n) (x : Wt n) :
    cf (∑ i ∈ s, f i) x = ∑ i ∈ s, cf (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cf_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ((cfBasic n).2.2.2.1 _ _ 0 x).1, ih]

/- English proof (translation)
Introduce `_ x` and use `by rw [cf_zero, cf_zero]`.
-/
private theorem sym_zero {n : ℕ} : Sym (0 : FR n) := fun _ x => by rw [cf_zero, cf_zero]

/- English proof (translation)
Introduce `w x` and use `by rw [((cfBasic n).2.2.2.1 f g 0 _).1, ((cfBasic n).2.2.2.1 f g 0 x).1, hf, hg]`.
-/
private theorem sym_add {n : ℕ} {f g : FR n} (hf : Sym f) (hg : Sym g) : Sym (f + g) := fun w x => by
  rw [((cfBasic n).2.2.2.1 f g 0 _).1, ((cfBasic n).2.2.2.1 f g 0 x).1, hf, hg]

/- English proof (translation)
Introduce `w x` and use `by rw [((cfBasic n).2.2.2.1 f f c _).2, ((cfBasic n).2.2.2.1 f f c x).2, hf]`.
-/
private theorem sym_smul {n : ℕ} {f : FR n} (c : ℂ) (hf : Sym f) : Sym (c • f) := fun w x => by
  rw [((cfBasic n).2.2.2.1 f f c _).2, ((cfBasic n).2.2.2.1 f f c x).2, hf]

/- English proof (translation)
Introduce `w x` and use `by rw [cf_sum, cf_sum] exact Finset.sum_congr rfl fun i hi => h i hi w x`.
-/
private theorem sym_sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → FR n) (h : ∀ i ∈ s, Sym (f i)) :
    Sym (∑ i ∈ s, f i) := fun w x => by
  rw [cf_sum, cf_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi w x

/- English proof (translation)
Introduce `v x`. Rewrite using `[cf_sum, cf_sum]`. Simplify using `only [cf_ex]`. Rewrite using `[← Equiv.sum_comp (Equiv.mulRight v⁻¹) (fun w : Equiv.Perm (Fin n) => if κ ∘ w = x then (1 : ℂ) else 0)]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Establish `: (κ ∘ w = x ∘ v) ↔ (κ ∘ (Equiv.mulRight v⁻¹ w) = x)`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `b`. Use `congrFun h (v⁻¹ b)` as an intermediate fact.

Simplify using `using this`. Introduce `h`. Use function extensionality and compare the values at `a`. Use `congrFun h (v a)` as an intermediate fact. Simplify using `using this`.

Simplify using `only [this]`.
-/
private theorem sym_orbit {n : ℕ} (κ : Wt n) : Sym (∑ w : Equiv.Perm (Fin n), ex (κ ∘ w)) := by
  classical
  intro v x
  rw [cf_sum, cf_sum]
  simp only [cf_ex]
  rw [← Equiv.sum_comp (Equiv.mulRight v⁻¹) (fun w : Equiv.Perm (Fin n) => if κ ∘ w = x then (1 : ℂ) else 0)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : (κ ∘ w = x ∘ v) ↔ (κ ∘ (Equiv.mulRight v⁻¹ w) = x) := by
    constructor
    · intro h
      funext b
      have := congrFun h (v⁻¹ b)
      simpa using this
    · intro h
      funext a
      have := congrFun h (v a)
      simpa using this
  simp only [this]

/- English proof (translation)
Establish `hadd` using `(cfBasic n).1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [alt, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc]`. Rewrite using `[Finset.sum_comm]`. Use `_ = ∑ v : Equiv.Perm (Fin n), ∑ w : Equiv.Perm (Fin n), sg v • (ex (rhoV n ∘ v) * ex (κ ∘ (w * v : Equiv.Perm (Fin n)))) := Finset.sum_congr rfl fun v _ => (Equiv.sum_comp (Equiv.mulRight v) (fun w : Equiv.Perm (Fin n) => sg v • (ex (rhoV n ∘ v) * ex (κ ∘ w)))).symm`.

Use `_ = ∑ w : Equiv.Perm (Fin n), alt (κ ∘ w + rhoV n) := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [alt]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[← hadd]`. Use `congr 2`. Use extensionality with `a`. Simplify using `[add_comm]`.
-/
private theorem alt_orbit {n : ℕ} (κ : Wt n) :
    alt (rhoV n) * ∑ w : Equiv.Perm (Fin n), ex (κ ∘ w) =
      ∑ w : Equiv.Perm (Fin n), alt (κ ∘ w + rhoV n) := by
  have hadd := (cfBasic n).1
  calc alt (rhoV n) * ∑ w : Equiv.Perm (Fin n), ex (κ ∘ w)
      = ∑ v : Equiv.Perm (Fin n), ∑ w : Equiv.Perm (Fin n),
          sg v • (ex (rhoV n ∘ v) * ex (κ ∘ w)) := by
        simp only [alt, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc]
        rw [Finset.sum_comm]
    _ = ∑ v : Equiv.Perm (Fin n), ∑ w : Equiv.Perm (Fin n),
          sg v • (ex (rhoV n ∘ v) * ex (κ ∘ (w * v : Equiv.Perm (Fin n)))) :=
        Finset.sum_congr rfl fun v _ => (Equiv.sum_comp (Equiv.mulRight v)
          (fun w : Equiv.Perm (Fin n) => sg v • (ex (rhoV n ∘ v) * ex (κ ∘ w)))).symm
    _ = ∑ w : Equiv.Perm (Fin n), alt (κ ∘ w + rhoV n) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [alt]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← hadd]
        congr 2
        ext a
        simp [add_comm]

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h | h <;> simp [h]`.
-/
private theorem sg_sq {n : ℕ} (u : Equiv.Perm (Fin n)) : sg u * sg u = 1 := by
  unfold sg
  rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h | h <;> simp [h]

/- English proof (translation)
Distinguish the cases in `hinj : Function.Injective z`. Take `⟨-, hdom, -, -, -, -⟩` from `rearr n`. Take `⟨han, ⟨u, hu⟩, -⟩` from `hdom z`. Establish `hs : StrictAnti (domC z)` using `han.strictAnti_of_injective (by rw [hu]; exact hinj.comp u.injective)`. Establish `hi' : ∀ a b, ∃ m : ℤ, domC z a - domC z b = m`.

Introduce `a b`. Rewrite using `[hu]`. Conclude with `hi _ _`. Establish `hD` using `dom_sub hs hi'`. Establish `hlt : dM (domC z - rhoV n + rhoV n) < N`.

Rewrite using `[sub_add_cancel, hu, dM_perm]`. Conclude with `hz`. Take `⟨χ, hS, hχ⟩` from `ih _ hD hlt`. Rewrite `hχ` using `[sub_add_cancel, hu, (cfBasic n).2.2.2.2.2.2.2.1 z u]`. Use `⟨sg u • χ, sym_smul _ hS, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_smul_comm, hχ, smul_smul, sg_sq, one_smul]`. Use `⟨0, sym_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_zero, (cfBasic n).2.2.2.2.2.2.2.2.2.2.2.2 z hinj]`.
-/
private theorem step {n N : ℕ}
    (ih : ∀ κ : Wt n, Dom κ → dM (κ + rhoV n) < N →
      ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt (κ + rhoV n))
    (z : Wt n) (hi : ∀ a b, ∃ m : ℤ, z a - z b = m) (hz : dM z < N) :
    ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt z := by
  by_cases hinj : Function.Injective z
  · obtain ⟨-, hdom, -, -, -, -⟩ := rearr n
    obtain ⟨han, ⟨u, hu⟩, -⟩ := hdom z
    have hs : StrictAnti (domC z) :=
      han.strictAnti_of_injective (by rw [hu]; exact hinj.comp u.injective)
    have hi' : ∀ a b, ∃ m : ℤ, domC z a - domC z b = m := by
      intro a b
      rw [hu]
      exact hi _ _
    have hD := dom_sub hs hi'
    have hlt : dM (domC z - rhoV n + rhoV n) < N := by
      rw [sub_add_cancel, hu, dM_perm]
      exact hz
    obtain ⟨χ, hS, hχ⟩ := ih _ hD hlt
    rw [sub_add_cancel, hu, (cfBasic n).2.2.2.2.2.2.2.1 z u] at hχ
    refine ⟨sg u • χ, sym_smul _ hS, ?_⟩
    rw [mul_smul_comm, hχ, smul_smul, sg_sq, one_smul]
  · refine ⟨0, sym_zero, ?_⟩
    rw [mul_zero, (cfBasic n).2.2.2.2.2.2.2.2.2.2.2.2 z hinj]

/- English proof (translation)
Introduce `n`. Take `⟨-, -, -, hDρ, hDD, -⟩` from `rearr n`. Establish `hint : ∀ κ : Wt n, Dom κ → ∀ (w : Equiv.Perm (Fin n)) a b, ∃ m : ℤ, (κ ∘ w + rhoV n) a - (κ ∘ w + rhoV n) b = m`. Introduce `κ hκ w a b`. Take `⟨m, hm⟩` from `dom_int hκ (w a) (w b)`.

Take `⟨m', hm'⟩` from `dom_int hDρ a b`. Use `⟨m + m', ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Function.comp]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `main : ∀ N : ℕ, ∀ κ : Wt n, Dom κ → dM (κ + rhoV n) < N → ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt (κ + rhoV n)`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `κ _ h`.

Conclude with `absurd h (by simpa using dM_nonneg _)`. Consider the case `succ N ih`. Introduce `κ hκ hlt`. Establish `hanti` using `(hDD κ hκ).1`. Take `⟨k, hk⟩` from `dM_nat (κ ∘ (1 : Equiv.Perm (Fin n)) + rhoV n) (hint κ hκ 1)`.

Establish `hk' : dM (κ + rhoV n) = k` using `hk`. Establish `hterm : ∀ w : Equiv.Perm (Fin n), κ ∘ w ≠ κ → ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt (κ ∘ w + rhoV n)`. Introduce `w hw`. Use `step ih _ (hint κ hκ w) ?_` and prove the remaining obligations. Take `⟨k', hk''⟩` from `dM_nat _ (hint κ hκ w)`.

Establish `h1` using `dM_lt hanti w hw`. Rewrite `h1` using `[hk'', hk']`. Rewrite `hlt` using `[hk']`. Rewrite using `[hk'']`. Establish `h2 : k' < k` using `by exact_mod_cast h1`.

Establish `h3 : k < N + 1` using `by exact_mod_cast hlt`. Conclude with `(by omega : k' < N)` after adjusting the coercions. Use `choose! χ hχS hχ using hterm`. Use `set S : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter (fun w => κ ∘ w = κ) with hS`. Establish `hc : ((S.card : ℂ)) ≠ 0`.

Establish `: 0 < S.card` using `Finset.card_pos.2 ⟨1, by simp [hS]⟩`. Conclude with `this.ne'` after adjusting the coercions. Use `set T : FR n := ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ¬ κ ∘ w = κ), χ w with hT`. Use `⟨(S.card : ℂ)⁻¹ • ((∑ w : Equiv.Perm (Fin n), ex (κ ∘ w)) + (-1 : ℂ) • T), sym_smul _ (sym_add (sym_orbit κ) (sym_smul _ (sym_sum _ _ fun w hw => hχS w (by simpa using hw)))), ?_⟩` and prove the remaining obligations. Establish `e1 : alt (rhoV n) * T = ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ¬ κ ∘ w = κ), alt (κ ∘ w + rhoV n)`.

Rewrite using `[hT, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun w hw => hχ w (by simpa using hw)`. Establish `e2 : ∑ w ∈ S, alt (κ ∘ w + rhoV n) = (S.card : ℂ) • alt (κ + rhoV n)`. Establish `: ∀ w ∈ S, alt (κ ∘ w + rhoV n) = alt (κ + rhoV n)` using `fun w hw => by`. Rewrite using `[(Finset.mem_filter.1 hw).2]`.

Rewrite using `[Finset.sum_congr rfl this, Finset.sum_const, Nat.cast_smul_eq_nsmul]`. Establish `e3` using `Finset.sum_filter_add_sum_filter_not Finset.univ (fun w : Equiv.Perm (Fin n) => κ ∘ w = κ) (fun w => alt (κ ∘ w + rhoV n))`. Rewrite using `[mul_smul_comm, mul_add, mul_smul_comm, alt_orbit, e1, ← e3, ← hS, e2]`. Simplify using `[smul_smul, hc]`. Introduce `κ hκ`.

Take `⟨k, hk⟩` from `dM_nat (κ ∘ (1 : Equiv.Perm (Fin n)) + rhoV n) (hint κ hκ 1)`. Establish `hk' : dM (κ + rhoV n) = k` using `hk`. Conclude with `main (k + 1) κ hκ (by rw [hk']; exact_mod_cast Nat.lt_succ_self k)`.
-/
theorem UpperTheory.RealTr.divEx :
    ∀ (n : ℕ) (κ : Wt n), Dom κ → ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt (κ + rhoV n) := by
  classical
  intro n
  obtain ⟨-, -, -, hDρ, hDD, -⟩ := rearr n
  have hint : ∀ κ : Wt n, Dom κ → ∀ (w : Equiv.Perm (Fin n)) a b,
      ∃ m : ℤ, (κ ∘ w + rhoV n) a - (κ ∘ w + rhoV n) b = m := by
    intro κ hκ w a b
    obtain ⟨m, hm⟩ := dom_int hκ (w a) (w b)
    obtain ⟨m', hm'⟩ := dom_int hDρ a b
    refine ⟨m + m', ?_⟩
    simp only [Pi.add_apply, Function.comp]
    push_cast
    linarith
  have main : ∀ N : ℕ, ∀ κ : Wt n, Dom κ → dM (κ + rhoV n) < N →
      ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt (κ + rhoV n) := by
    intro N
    induction N with
    | zero =>
      intro κ _ h
      exact absurd h (by simpa using dM_nonneg _)
    | succ N ih =>
      intro κ hκ hlt
      have hanti := (hDD κ hκ).1
      obtain ⟨k, hk⟩ := dM_nat (κ ∘ (1 : Equiv.Perm (Fin n)) + rhoV n) (hint κ hκ 1)
      have hk' : dM (κ + rhoV n) = k := hk
      have hterm : ∀ w : Equiv.Perm (Fin n), κ ∘ w ≠ κ →
          ∃ χ : FR n, Sym χ ∧ alt (rhoV n) * χ = alt (κ ∘ w + rhoV n) := by
        intro w hw
        refine step ih _ (hint κ hκ w) ?_
        obtain ⟨k', hk''⟩ := dM_nat _ (hint κ hκ w)
        have h1 := dM_lt hanti w hw
        rw [hk'', hk'] at h1
        rw [hk'] at hlt
        rw [hk'']
        have h2 : k' < k := by exact_mod_cast h1
        have h3 : k < N + 1 := by exact_mod_cast hlt
        exact_mod_cast (by omega : k' < N)
      choose! χ hχS hχ using hterm
      set S : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter (fun w => κ ∘ w = κ) with hS
      have hc : ((S.card : ℂ)) ≠ 0 := by
        have : 0 < S.card := Finset.card_pos.2 ⟨1, by simp [hS]⟩
        exact_mod_cast this.ne'
      set T : FR n := ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ¬ κ ∘ w = κ), χ w with hT
      refine ⟨(S.card : ℂ)⁻¹ • ((∑ w : Equiv.Perm (Fin n), ex (κ ∘ w)) + (-1 : ℂ) • T),
        sym_smul _ (sym_add (sym_orbit κ) (sym_smul _ (sym_sum _ _ fun w hw => hχS w (by simpa using hw)))), ?_⟩
      have e1 : alt (rhoV n) * T =
          ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ¬ κ ∘ w = κ), alt (κ ∘ w + rhoV n) := by
        rw [hT, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w hw => hχ w (by simpa using hw)
      have e2 : ∑ w ∈ S, alt (κ ∘ w + rhoV n) = (S.card : ℂ) • alt (κ + rhoV n) := by
        have : ∀ w ∈ S, alt (κ ∘ w + rhoV n) = alt (κ + rhoV n) := fun w hw => by
          rw [(Finset.mem_filter.1 hw).2]
        rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.cast_smul_eq_nsmul]
      have e3 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun w : Equiv.Perm (Fin n) => κ ∘ w = κ)
        (fun w => alt (κ ∘ w + rhoV n))
      rw [mul_smul_comm, mul_add, mul_smul_comm, alt_orbit, e1, ← e3, ← hS, e2]
      simp [smul_smul, hc]
  intro κ hκ
  obtain ⟨k, hk⟩ := dM_nat (κ ∘ (1 : Equiv.Perm (Fin n)) + rhoV n) (hint κ hκ 1)
  have hk' : dM (κ + rhoV n) = k := hk
  exact main (k + 1) κ hκ (by rw [hk']; exact_mod_cast Nat.lt_succ_self k)

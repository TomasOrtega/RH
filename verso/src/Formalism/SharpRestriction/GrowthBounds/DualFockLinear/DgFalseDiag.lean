import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.IsMultiHom

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model (Nv Nv_true_eq Nv_false_eq)
open scoped MonomialOrder

def Mv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  if vec = true then initMinor R (fun _ : Fin 1 => c) (Nat.succ_le_succ (Nat.zero_le m))
  else initMinor R c.succAbove (Nat.le_succ m)

def dg (m : ℕ) (vec : Bool) (c : Fin (m + 1)) : Fin (m + 1) × Fin (m + 1) →₀ ℕ :=
  if vec = true then Finsupp.single (c, 0) 1
  else ∑ p : Fin m, Finsupp.single (c.succAbove p, Fin.castLE (Nat.le_succ m) p) 1

/- English proof (translation)
Unfold `Mv dg`. Consider the cases of `vec`. Simplify using `only [Bool.false_eq_true, if_false]`. Conclude with `colLexInitMinor F (m + 1) (m + 1) m c.succAbove (Nat.le_succ m) (Fin.strictMono_succAbove c)`. Simplify using `only [if_true]`.

Establish `hsm : StrictMono (fun _ : Fin 1 => c)`. Introduce `a b hab`. Conclude with `absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl b)`. Take `⟨h1, h2⟩` from `colLexInitMinor F (m + 1) (m + 1) 1 (fun _ : Fin 1 => c) (Nat.succ_le_succ (Nat.zero_le m)) hsm`. Use `⟨?_, h2⟩` and prove the remaining obligations.

Rewrite using `[h1, Fin.sum_univ_one]`. Use `congr 2`.
-/
theorem Mv_deg (F : Type) [Field F] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    (colLex (m + 1) (m + 1)).degree (Mv F m vec c) = dg m vec c ∧
      (colLex (m + 1) (m + 1)).leadingCoeff (Mv F m vec c) = 1 := by
  unfold Mv dg
  cases vec
  · simp only [Bool.false_eq_true, if_false]
    exact colLexInitMinor F (m + 1) (m + 1) m c.succAbove (Nat.le_succ m) (Fin.strictMono_succAbove c)
  · simp only [if_true]
    have hsm : StrictMono (fun _ : Fin 1 => c) := by
      intro a b hab
      exact absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl b)
    obtain ⟨h1, h2⟩ := colLexInitMinor F (m + 1) (m + 1) 1 (fun _ : Fin 1 => c)
      (Nat.succ_le_succ (Nat.zero_le m)) hsm
    refine ⟨?_, h2⟩
    rw [h1, Fin.sum_univ_one]
    congr 2

def sg (F : Type) [Field F] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) : Fˣ :=
  if vec = true then 1 else (-1) ^ ((c : ℕ) + m)

/- English proof (translation)
Consider the cases of `vec`. Rewrite using `[Nv_false_eq]`. Simplify using `only [sg, Mv, Bool.false_eq_true, if_false, Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]`. Rewrite using `[smul_eq_C_mul, map_pow, map_neg, map_one]`. Rewrite using `[Nv_true_eq]`.

Simplify using `only [sg, Mv, if_true, one_smul]`.
-/
theorem Nv_eq (F : Type) [Field F] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    Nv F m vec c = sg F m vec c • Mv F m vec c := by
  cases vec
  · rw [Nv_false_eq]
    simp only [sg, Mv, Bool.false_eq_true, if_false, Units.smul_def, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one]
    rw [smul_eq_C_mul, map_pow, map_neg, map_one]
  · rw [Nv_true_eq]
    simp only [sg, Mv, if_true, one_smul]

/- English proof (translation)
Establish `hP1 : ∀ c, (colLex (m + 1) (m + 1)).degree (Mv F m vec c ^ α c) = α c • dg m vec c`. Introduce `c`. Rewrite using `[MonomialOrder.degree_pow, (Mv_deg F m vec c).1]`. Establish `hP2 : ∀ c, (colLex (m + 1) (m + 1)).leadingCoeff (Mv F m vec c ^ α c) = 1`. Introduce `c`.

Rewrite using `[MonomialOrder.leadingCoeff_pow, (Mv_deg F m vec c).2, one_pow]`. Establish `hdeg : (colLex (m + 1) (m + 1)).degree (∏ c, Mv F m vec c ^ α c) = ∑ c, α c • dg m vec c`. Establish `h` using `(colLex (m + 1) (m + 1)).degree_prod_of_regular (P := fun c => Mv F m vec c ^ α c) (s := Finset.univ) (fun c _ => by simp only [hP2]; exact isRegular_one)`. Simplify using `only [hP1] at h`. Conclude with `h`.

Establish `hlc : (colLex (m + 1) (m + 1)).leadingCoeff (∏ c, Mv F m vec c ^ α c) = 1`. Establish `h` using `(colLex (m + 1) (m + 1)).coeff_prod_sum_degree (fun c => Mv F m vec c ^ α c) Finset.univ`. Simplify using `only [hP1, hP2, Finset.prod_const_one] at h`. Rewrite using `[MonomialOrder.leadingCoeff, hdeg]`. Conclude with `h`.

Establish `hne1 : (∏ c, Mv F m vec c ^ α c) ≠ 0`. Introduce `h0`. Rewrite `hlc` using `[h0, MonomialOrder.leadingCoeff_zero]`. Conclude with `zero_ne_one hlc`. Establish `hne2 : g ≠ 0`.

Introduce `h0`. Establish `h2` using `hg.2`. Rewrite `h2` using `[h0, MonomialOrder.leadingCoeff_zero]`. Conclude with `zero_ne_one h2`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[MonomialOrder.degree_mul hne1 hne2, hdeg, hg.1]`. Rewrite using `[MonomialOrder.leadingCoeff_mul, hlc, hg.2, one_mul]`.
-/
theorem fam_deg (F : Type) [Field F] (m : ℕ) (vec : Bool) (α : Fin (m + 1) →₀ ℕ)
    (g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) F) (e : Fin (m + 1) × Fin (m + 1) →₀ ℕ)
    (hg : (colLex (m + 1) (m + 1)).degree g = e ∧ (colLex (m + 1) (m + 1)).leadingCoeff g = 1) :
    (colLex (m + 1) (m + 1)).degree ((∏ c, Mv F m vec c ^ α c) * g) = (∑ c, α c • dg m vec c) + e ∧
      (colLex (m + 1) (m + 1)).leadingCoeff ((∏ c, Mv F m vec c ^ α c) * g) = 1 := by
  have hP1 : ∀ c, (colLex (m + 1) (m + 1)).degree (Mv F m vec c ^ α c) = α c • dg m vec c := by
    intro c
    rw [MonomialOrder.degree_pow, (Mv_deg F m vec c).1]
  have hP2 : ∀ c, (colLex (m + 1) (m + 1)).leadingCoeff (Mv F m vec c ^ α c) = 1 := by
    intro c
    rw [MonomialOrder.leadingCoeff_pow, (Mv_deg F m vec c).2, one_pow]
  have hdeg : (colLex (m + 1) (m + 1)).degree (∏ c, Mv F m vec c ^ α c) = ∑ c, α c • dg m vec c := by
    have h := (colLex (m + 1) (m + 1)).degree_prod_of_regular (P := fun c => Mv F m vec c ^ α c)
      (s := Finset.univ) (fun c _ => by simp only [hP2]; exact isRegular_one)
    simp only [hP1] at h
    exact h
  have hlc : (colLex (m + 1) (m + 1)).leadingCoeff (∏ c, Mv F m vec c ^ α c) = 1 := by
    have h := (colLex (m + 1) (m + 1)).coeff_prod_sum_degree (fun c => Mv F m vec c ^ α c) Finset.univ
    simp only [hP1, hP2, Finset.prod_const_one] at h
    rw [MonomialOrder.leadingCoeff, hdeg]
    exact h
  have hne1 : (∏ c, Mv F m vec c ^ α c) ≠ 0 := by
    intro h0
    rw [h0, MonomialOrder.leadingCoeff_zero] at hlc
    exact zero_ne_one hlc
  have hne2 : g ≠ 0 := by
    intro h0
    have h2 := hg.2
    rw [h0, MonomialOrder.leadingCoeff_zero] at h2
    exact zero_ne_one h2
  refine ⟨?_, ?_⟩
  · rw [MonomialOrder.degree_mul hne1 hne2, hdeg, hg.1]
  · rw [MonomialOrder.leadingCoeff_mul, hlc, hg.2, one_mul]

/- English proof (translation)
Simplify using `only [dg, Bool.false_eq_true, if_false, Finsupp.finset_sum_apply, Finsupp.single_apply]`. Rewrite using `[Finset.sum_eq_single (⟨t.val, ht⟩ : Fin m)]`. Distinguish the cases in `htc : t < c`. Rewrite using `[if_pos htc, if_pos]`. Simplify using `only [Prod.mk.injEq]`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[Fin.succAbove_of_castSucc_lt]`. Conclude with `Fin.ext rfl`. Conclude with `htc`. Conclude with `Fin.ext rfl`.

Rewrite using `[if_neg htc, if_neg]`. Simplify using `only [Prod.mk.injEq, not_and]`. Introduce `h _`. Rewrite `h` using `[Fin.succAbove_of_le_castSucc _ _ (not_lt.mp htc)]`. Rewrite `h` using `[Fin.ext_iff]`.

Simplify using `at h`. Introduce `p _ hp`. Rewrite using `[if_neg]`. Simplify using `only [Prod.mk.injEq, not_and]`. Introduce `_ h2`.

Apply `hp` to reduce the goal to its premises. Use `ext`. Rewrite `h2` using `[Fin.ext_iff]`. Conclude with `h2`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem dg_false_diag (m : ℕ) (c t : Fin (m + 1)) (ht : t.val < m) :
    dg m false c (t, t) = if t < c then 1 else 0 := by
  simp only [dg, Bool.false_eq_true, if_false, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single (⟨t.val, ht⟩ : Fin m)]
  · by_cases htc : t < c
    · rw [if_pos htc, if_pos]
      simp only [Prod.mk.injEq]
      constructor
      · rw [Fin.succAbove_of_castSucc_lt]
        · exact Fin.ext rfl
        · exact htc
      · exact Fin.ext rfl
    · rw [if_neg htc, if_neg]
      simp only [Prod.mk.injEq, not_and]
      intro h _
      rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.mp htc)] at h
      rw [Fin.ext_iff] at h
      simp at h
  · intro p _ hp
    rw [if_neg]
    simp only [Prod.mk.injEq, not_and]
    intro _ h2
    apply hp
    ext
    rw [Fin.ext_iff] at h2
    exact h2
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hset : (Finset.univ.filter fun c : Fin k => n ≤ c.val) = insert ⟨n, hn⟩ (Finset.univ.filter fun c : Fin k => n + 1 ≤ c.val)`. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hset, Finset.sum_insert]`.

Simplify using the standard rewrite rules.
-/
theorem tail_step {k : ℕ} (f : Fin k → ℕ) (n : ℕ) (hn : n < k) :
    (∑ c : Fin k with n ≤ c.val, f c) = f ⟨n, hn⟩ + ∑ c : Fin k with n + 1 ≤ c.val, f c := by
  have hset : (Finset.univ.filter fun c : Fin k => n ≤ c.val) =
      insert ⟨n, hn⟩ (Finset.univ.filter fun c : Fin k => n + 1 ≤ c.val) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hset, Finset.sum_insert]
  simp

/- English proof (translation)
Use function extensionality and compare the values at `c`. Establish `h1` using `h c.val`. Establish `h2` using `h (c.val + 1)`. Rewrite `h1` using `[tail_step f c.val c.isLt, tail_step g c.val c.isLt, h2]`. Conclude with `Nat.add_right_cancel h1`.
-/
theorem tail_inj {k : ℕ} (f g : Fin k → ℕ)
    (h : ∀ n, (∑ c : Fin k with n ≤ c.val, f c) = ∑ c : Fin k with n ≤ c.val, g c) : f = g := by
  funext c
  have h1 := h c.val
  have h2 := h (c.val + 1)
  rw [tail_step f c.val c.isLt, tail_step g c.val c.isLt, h2] at h1
  exact Nat.add_right_cancel h1

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `t a _ ha`. Conclude with `h0 a (Nat.le_zero.mp ha) t`.

Consider the case `succ n ih`. Introduce `t a ht ha`. Establish `hn : n < k`. Use `t.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hI'` using `hI ⟨n, hn⟩ t (by simp [ht]) a`. Establish `hzero : ∑ b : Fin k with b < a, x (b, ⟨n, hn⟩) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b hb`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb`.

Rewrite `hb` using `[Fin.lt_def]`. Conclude with `ih ⟨n, hn⟩ b rfl (by omega)`. Rewrite `hI'` using `[hzero, add_zero]`. Establish `hle : x (a, t) ≤ ∑ b : Fin k with b ≤ a, x (b, t)` using `Finset.single_le_sum (f := fun b => x (b, t)) (fun _ _ => Nat.zero_le _) (by simp)`. Use linear arithmetic over natural numbers and integers.
-/
theorem no_zero_low {k : ℕ} (x : Fin k × Fin k →₀ ℕ) (hI : Interlaced x) (h0 : ∀ (z : Fin k), z.val = 0 → ∀ t, x (z, t) = 0) :
    ∀ (n : ℕ) (t a : Fin k), t.val = n → a.val ≤ n → x (a, t) = 0 := by
  intro n
  induction n with
  | zero =>
    intro t a _ ha
    exact h0 a (Nat.le_zero.mp ha) t
  | succ n ih =>
    intro t a ht ha
    have hn : n < k := by
      have := t.isLt
      omega
    have hI' := hI ⟨n, hn⟩ t (by simp [ht]) a
    have hzero : ∑ b : Fin k with b < a, x (b, ⟨n, hn⟩) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [Fin.lt_def] at hb
      exact ih ⟨n, hn⟩ b rfl (by omega)
    rw [hzero, add_zero] at hI'
    have hle : x (a, t) ≤ ∑ b : Fin k with b ≤ a, x (b, t) :=
      Finset.single_le_sum (f := fun b => x (b, t)) (fun _ _ => Nat.zero_le _) (by simp)
    omega

/- English proof (translation)
Rewrite using `[Finset.sum_filter]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `c _`. Rewrite using `[dg_false_diag m c t ht]`. Distinguish the cases in `hc : t < c`.

Rewrite `hc` using `[Fin.lt_def]`. Rewrite using `[if_pos (Fin.lt_def.mpr hc), if_pos (by omega), mul_one]`. Rewrite `hc` using `[Fin.lt_def]`. Rewrite using `[if_neg (fun h => hc (Fin.lt_def.mp h)), if_neg (by omega), mul_zero]`.
-/
private theorem sum_mul_dg_diag_eq_sum_filter (m n : ℕ) (β : Fin (m + 1) →₀ ℕ) (t : Fin (m + 1)) (ht : t.val < m)
    (hn : t.val + 1 = n) :
    ∑ c, β c * dg m false c (t, t) = ∑ c : Fin (m + 1) with n ≤ c.val, β c := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  rw [dg_false_diag m c t ht]
  by_cases hc : t < c
  · rw [Fin.lt_def] at hc
    rw [if_pos (Fin.lt_def.mpr hc), if_pos (by omega), mul_one]
  · rw [Fin.lt_def] at hc
    rw [if_neg (fun h => hc (Fin.lt_def.mp h)), if_neg (by omega), mul_zero]

/- English proof (translation)
Use extensionality with `c`. Consider the cases of `top`. Establish `hd` using `htop rfl`. Establish `h1 : α c = 0` using `Finset.sum_eq_zero_iff.mp (hα.trans hd) c (Finset.mem_univ c)`. Establish `h2 : α' c = 0` using `Finset.sum_eq_zero_iff.mp (hα'.trans hd) c (Finset.mem_univ c)`.

Rewrite using `[h1, h2]`. Consider the cases of `vec`. Establish `hz : ∀ y : Xs m true false ν, ∀ t : Fin (m + 1), y.1 (t, t) = 0`. Introduce `y t`. Take `⟨⟨hI, _⟩, htop'⟩` from `y.2`.

Establish `hrow` using `(htop' rfl).2 rfl`. Conclude with `no_zero_low y.1 hI (fun z hz t' => by`. Establish `hz0 : z = 0` using `Fin.ext hz`. Rewrite using `[hz0]`. Conclude with `hrow t') t.val t t rfl le_rfl`.

Establish `htail : ∀ n, (∑ c : Fin (m + 1) with n ≤ c.val, α c) = ∑ c : Fin (m + 1) with n ≤ c.val, α' c`. Introduce `n`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Establish `z0 : ∀ β : Fin (m + 1) →₀ ℕ, (∑ c : Fin (m + 1) with 0 ≤ c.val, β c) = ∑ c, β c`.

Introduce `β`. Rewrite using `[Finset.filter_true_of_mem (fun c _ => Nat.zero_le c.val)]`. Rewrite using `[z0 α, z0 α', hα, hα']`. Distinguish the cases in `hnm : n ≤ m`. Establish `ht : n - 1 < m + 1` using `by omega`.

Establish `he` using `congrArg (fun f => f ((⟨n - 1, ht⟩ : Fin (m + 1)), (⟨n - 1, ht⟩ : Fin (m + 1)))) h`. Simplify using `only [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at he`. Rewrite `he` using `[hz x, hz x', add_zero, add_zero, sum_mul_dg_diag_eq_sum_filter m n α _ (by show n - 1 < m; omega) (by show n - 1 + 1 = n; omega), sum_mul_dg_diag_eq_sum_filter m n α' _ (by show n - 1 < m; omega) (by show n - 1 + 1 = n; omega)]`. Conclude with `he`. Establish `z1 : ∀ β : Fin (m + 1) →₀ ℕ, (∑ c : Fin (m + 1) with n ≤ c.val, β c) = 0`.

Introduce `β`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c hc`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc`. Use `c.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[z1 α, z1 α']`. Establish `hfun` using `tail_inj (fun c => α c) (fun c => α' c) htail`. Conclude with `congrFun hfun c`. Establish `hcol : ∀ y : Xs m true true ν, ∀ a : Fin (m + 1), y.1 (a, 0) = if a = 0 then ν 0 else 0`.

Introduce `y a`. Take `⟨⟨_, hs⟩, htop'⟩` from `y.2`. Establish `h00 : y.1 (0, 0) = ν 0` using `(htop' rfl).1 rfl`. Establish `hsum` using `hs 0`. Rewrite `hsum` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1))), h00]`.

Establish `hrest : ∑ b ∈ Finset.univ.erase (0 : Fin (m + 1)), y.1 (b, 0) = 0` using `by omega`. Use `split_ifs with ha`. Rewrite using `[ha]`. Conclude with `h00`. Conclude with `Finset.sum_eq_zero_iff.mp hrest a (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩)`.

Establish `he` using `congrArg (fun f => f (c, (0 : Fin (m + 1)))) h`. Simplify using `only [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at he`. Rewrite `he` using `[hcol x, hcol x']`. Establish `hs1 : ∀ β : Fin (m + 1) →₀ ℕ, ∑ c', β c' * dg m true c' (c, 0) = β c`. Introduce `β`.

Rewrite using `[Finset.sum_eq_single c]`. Simplify using `[dg]`. Introduce `b _ hb`. Simplify using `[dg, Finsupp.single_apply, hb]`. Introduce `hc`.

Conclude with `absurd (Finset.mem_univ c) hc`. Rewrite `he` using `[hs1 α, hs1 α']`. Apply the tactic sequence `split_ifs at he <;> omega`.
-/
theorem key_inj (m : ℕ) (top vec : Bool) (d : ℕ) (ν : Fin (m + 1) → ℕ) (htop : top = false → d = 0)
    (α α' : Fin (m + 1) →₀ ℕ) (hα : ∑ c, α c = d) (hα' : ∑ c, α' c = d) (x x' : Xs m top vec ν)
    (h : (∑ c, α c • dg m vec c) + x.1 = (∑ c, α' c • dg m vec c) + x'.1) : α = α' := by
  ext c
  cases top
  · have hd := htop rfl
    have h1 : α c = 0 := Finset.sum_eq_zero_iff.mp (hα.trans hd) c (Finset.mem_univ c)
    have h2 : α' c = 0 := Finset.sum_eq_zero_iff.mp (hα'.trans hd) c (Finset.mem_univ c)
    rw [h1, h2]
  · cases vec
    · have hz : ∀ y : Xs m true false ν, ∀ t : Fin (m + 1), y.1 (t, t) = 0 := by
        intro y t
        obtain ⟨⟨hI, _⟩, htop'⟩ := y.2
        have hrow := (htop' rfl).2 rfl
        exact no_zero_low y.1 hI (fun z hz t' => by
          have hz0 : z = 0 := Fin.ext hz
          rw [hz0]
          exact hrow t') t.val t t rfl le_rfl
      have htail : ∀ n, (∑ c : Fin (m + 1) with n ≤ c.val, α c) =
          ∑ c : Fin (m + 1) with n ≤ c.val, α' c := by
        intro n
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          have z0 : ∀ β : Fin (m + 1) →₀ ℕ, (∑ c : Fin (m + 1) with 0 ≤ c.val, β c) = ∑ c, β c := by
            intro β
            rw [Finset.filter_true_of_mem (fun c _ => Nat.zero_le c.val)]
          rw [z0 α, z0 α', hα, hα']
        · by_cases hnm : n ≤ m
          · have ht : n - 1 < m + 1 := by omega
            have he := congrArg (fun f => f ((⟨n - 1, ht⟩ : Fin (m + 1)), (⟨n - 1, ht⟩ : Fin (m + 1)))) h
            simp only [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at he
            rw [hz x, hz x', add_zero, add_zero,
              sum_mul_dg_diag_eq_sum_filter m n α _ (by show n - 1 < m; omega) (by show n - 1 + 1 = n; omega),
              sum_mul_dg_diag_eq_sum_filter m n α' _ (by show n - 1 < m; omega) (by show n - 1 + 1 = n; omega)] at he
            exact he
          · have z1 : ∀ β : Fin (m + 1) →₀ ℕ, (∑ c : Fin (m + 1) with n ≤ c.val, β c) = 0 := by
              intro β
              apply Finset.sum_eq_zero
              intro c hc
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
              have := c.isLt
              omega
            rw [z1 α, z1 α']
      have hfun := tail_inj (fun c => α c) (fun c => α' c) htail
      exact congrFun hfun c
    · have hcol : ∀ y : Xs m true true ν, ∀ a : Fin (m + 1), y.1 (a, 0) = if a = 0 then ν 0 else 0 := by
        intro y a
        obtain ⟨⟨_, hs⟩, htop'⟩ := y.2
        have h00 : y.1 (0, 0) = ν 0 := (htop' rfl).1 rfl
        have hsum := hs 0
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1))), h00] at hsum
        have hrest : ∑ b ∈ Finset.univ.erase (0 : Fin (m + 1)), y.1 (b, 0) = 0 := by omega
        split_ifs with ha
        · rw [ha]
          exact h00
        · exact Finset.sum_eq_zero_iff.mp hrest a (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩)
      have he := congrArg (fun f => f (c, (0 : Fin (m + 1)))) h
      simp only [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at he
      rw [hcol x, hcol x'] at he
      have hs1 : ∀ β : Fin (m + 1) →₀ ℕ, ∑ c', β c' * dg m true c' (c, 0) = β c := by
        intro β
        rw [Finset.sum_eq_single c]
        · simp [dg]
        · intro b _ hb
          simp [dg, Finsupp.single_apply, hb]
        · intro hc
          exact absurd (Finset.mem_univ c) hc
      rw [hs1 α, hs1 α'] at he
      split_ifs at he <;> omega

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hg i hi`. Assume the negation of the conclusion as `hne`. Establish `hne' : (s.filter fun j => g j ≠ 0).Nonempty` using `⟨i, Finset.mem_filter.mpr ⟨hi, hne⟩⟩`. Take `⟨i0, hi0, hmax⟩` from `Finset.exists_max_image (s.filter fun j => g j ≠ 0) (fun j => M.toSyn (M.degree (v j))) hne'`.

Rewrite `hi0` using `[Finset.mem_filter]`. Establish `hc` using `congrArg (MvPolynomial.coeff (M.degree (v i0))) hg`. Rewrite `hc` using `[MvPolynomial.coeff_sum, MvPolynomial.coeff_zero]`. Rewrite `hc` using `[Finset.sum_eq_single i0]`. Rewrite `hc` using `[MvPolynomial.coeff_smul, smul_eq_mul]`.

Establish `hlc : MvPolynomial.coeff (M.degree (v i0)) (v i0) ≠ 0` using `M.leadingCoeff_ne_zero_iff.mpr (hv i0)`. Conclude with `mul_ne_zero hi0.2 hlc hc`. Introduce `j hj hji0`. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`. Distinguish the cases in `hgj : g j = 0`.

Rewrite using `[hgj, zero_mul]`. Establish `hle` using `hmax j (Finset.mem_filter.mpr ⟨hj, hgj⟩)`. Establish `hlt : M.toSyn (M.degree (v j)) < M.toSyn (M.degree (v i0))`. Use `lt_of_le_of_ne hle ?_` and prove the remaining obligations. Introduce `heq`.

Conclude with `hji0 (hinj (M.toSyn.injective heq))`. Rewrite using `[M.coeff_eq_zero_of_lt hlt, mul_zero]`. Introduce `h`. Conclude with `absurd hi0.1 h`.
-/
private theorem linearIndependent_of_degree_injective {σ ι F : Type} [Field F] (M : MonomialOrder σ) (v : ι → MvPolynomial σ F)
    (hv : ∀ i, v i ≠ 0) (hinj : Function.Injective fun i => M.degree (v i)) : LinearIndependent F v := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hne
  have hne' : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hne⟩⟩
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (s.filter fun j => g j ≠ 0)
    (fun j => M.toSyn (M.degree (v j))) hne'
  rw [Finset.mem_filter] at hi0
  have hc := congrArg (MvPolynomial.coeff (M.degree (v i0))) hg
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single i0] at hc
  · rw [MvPolynomial.coeff_smul, smul_eq_mul] at hc
    have hlc : MvPolynomial.coeff (M.degree (v i0)) (v i0) ≠ 0 := M.leadingCoeff_ne_zero_iff.mpr (hv i0)
    exact mul_ne_zero hi0.2 hlc hc
  · intro j hj hji0
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hgj : g j = 0
    · rw [hgj, zero_mul]
    · have hle := hmax j (Finset.mem_filter.mpr ⟨hj, hgj⟩)
      have hlt : M.toSyn (M.degree (v j)) < M.toSyn (M.degree (v i0)) := by
        refine lt_of_le_of_ne hle ?_
        intro heq
        exact hji0 (hinj (M.toSyn.injective heq))
      rw [M.coeff_eq_zero_of_lt hlt, mul_zero]
  · intro h
    exact absurd hi0.1 h

/- English proof (translation)
Use `⟨∏ c, ((sg F m vec c : Fˣ) : F) ^ α c, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.mpr (fun c _ => pow_ne_zero _ (Units.ne_zero _))`. Rewrite using `[smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `c _`.

Rewrite using `[Nv_eq, Units.smul_def, smul_eq_C_mul, mul_pow, map_pow]`.
-/
private theorem exists_ne_zero_prod_Nv_pow_eq_smul_prod_Mv (F : Type) [Field F] (m : ℕ) (vec : Bool) (α : Fin (m + 1) →₀ ℕ) :
    ∃ u : F, u ≠ 0 ∧ ∏ c, Nv F m vec c ^ α c = u • ∏ c, Mv F m vec c ^ α c := by
  refine ⟨∏ c, ((sg F m vec c : Fˣ) : F) ^ α c, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun c _ => pow_ne_zero _ (Units.ne_zero _))
  · rw [smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro c _
    rw [Nv_eq, Units.smul_def, smul_eq_C_mul, mul_pow, map_pow]

/- English proof (translation)
Unfold `PosInd`. Introduce `F _ m _ top vec d ν htop _ b hb`. Establish `hdeg : ∀ y : {α : Fin (m + 1) →₀ ℕ // ∑ c, α c = d} × Xs m top vec ν, (colLex (m + 1) (m + 1)).degree ((∏ c, Nv F m vec c ^ y.1.1 c) * b y.2) = (∑ c, y.1.1 c • dg m vec c) + y.2.1 ∧ (∏ c, Nv F m vec c ^ y.1.1 c) * b y.2 ≠ 0`. Introduce `y`. Take `⟨u, hu, he⟩` from `exists_ne_zero_prod_Nv_pow_eq_smul_prod_Mv F m vec y.1.1`.

Take `⟨h1, h2⟩` from `fam_deg F m vec y.1.1 (b y.2) y.2.1 (hb y.2)`. Establish `hne : (∏ c, Mv F m vec c ^ y.1.1 c) * b y.2 ≠ 0`. Introduce `h0`. Rewrite `h2` using `[h0, MonomialOrder.leadingCoeff_zero]`. Conclude with `zero_ne_one h2`.

Rewrite using `[he, smul_mul_assoc]`. Use `⟨?_, smul_ne_zero hu hne⟩` and prove the remaining obligations. Rewrite using `[MonomialOrder.degree_smul_of_isRegular (isRegular_of_ne_zero hu), h1]`. Apply `linearIndependent_of_degree_injective (colLex (m + 1) (m + 1))` to reduce the goal to its premises. Introduce `y`.

Conclude with `(hdeg y).2`. Introduce `y y' hyy`. Establish `e : (∑ c, y.1.1 c • dg m vec c) + y.2.1 = (∑ c, y'.1.1 c • dg m vec c) + y'.2.1`. Rewrite using `[← (hdeg y).1, ← (hdeg y').1]`. Conclude with `hyy`.

Establish `hα` using `key_inj m top vec d ν htop y.1.1 y'.1.1 y.1.2 y'.1.2 y.2 y'.2 e`. Establish `h2 : y.2.1 = y'.2.1`. Rewrite `e` using `[hα]`. Conclude with `add_left_cancel e`. Conclude with `Prod.ext (Subtype.ext hα) (Subtype.ext h2)`.
-/
theorem posInd : PosInd := by
  unfold PosInd
  intro F _ m _ top vec d ν htop _ b hb
  have hdeg : ∀ y : {α : Fin (m + 1) →₀ ℕ // ∑ c, α c = d} × Xs m top vec ν,
      (colLex (m + 1) (m + 1)).degree ((∏ c, Nv F m vec c ^ y.1.1 c) * b y.2) =
          (∑ c, y.1.1 c • dg m vec c) + y.2.1 ∧
        (∏ c, Nv F m vec c ^ y.1.1 c) * b y.2 ≠ 0 := by
    intro y
    obtain ⟨u, hu, he⟩ := exists_ne_zero_prod_Nv_pow_eq_smul_prod_Mv F m vec y.1.1
    obtain ⟨h1, h2⟩ := fam_deg F m vec y.1.1 (b y.2) y.2.1 (hb y.2)
    have hne : (∏ c, Mv F m vec c ^ y.1.1 c) * b y.2 ≠ 0 := by
      intro h0
      rw [h0, MonomialOrder.leadingCoeff_zero] at h2
      exact zero_ne_one h2
    rw [he, smul_mul_assoc]
    refine ⟨?_, smul_ne_zero hu hne⟩
    rw [MonomialOrder.degree_smul_of_isRegular (isRegular_of_ne_zero hu), h1]
  apply linearIndependent_of_degree_injective (colLex (m + 1) (m + 1))
  · intro y
    exact (hdeg y).2
  · intro y y' hyy
    have e : (∑ c, y.1.1 c • dg m vec c) + y.2.1 = (∑ c, y'.1.1 c • dg m vec c) + y'.2.1 := by
      rw [← (hdeg y).1, ← (hdeg y').1]
      exact hyy
    have hα := key_inj m top vec d ν htop y.1.1 y'.1.1 y.1.2 y'.1.2 y.2 y'.2 e
    have h2 : y.2.1 = y'.2.1 := by
      rw [hα] at e
      exact add_left_cancel e
    exact Prod.ext (Subtype.ext hα) (Subtype.ext h2)

end Formalism.MainNotions.TestSideCounting

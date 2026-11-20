import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

noncomputable section

namespace GlobalTheory.Branching.SsInj

def ps {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (a : ℕ) (t : Fin k) : ℕ :=
  ∑ b : Fin r, if b.val < a then m (b, t) else 0

/- English proof (translation)
Simplify using `only [Interlaced, InterlacedAt, ps, Finset.sum_filter, zero_add, Nat.lt_succ_iff, Fin.le_def, Fin.lt_def]`.
-/
theorem interlaced_iff {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) :
    Interlaced m ↔ ∀ l j : Fin k, j.val = l.val + 1 → ∀ a : Fin r, ps m (a.val + 1) j ≤ ps m a.val l := by
  simp only [Interlaced, InterlacedAt, ps, Finset.sum_filter, zero_add, Nat.lt_succ_iff, Fin.le_def, Fin.lt_def]

/- English proof (translation)
Simplify using `[ps]`.
-/
theorem ps_zero {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (t : Fin k) : ps m 0 t = 0 := by simp [ps]

/- English proof (translation)
Establish `: m (a, t) = ∑ b : Fin r, if b = a then m (b, t) else 0` using `by simp`. Rewrite using `[this, ps, ps, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : b = a`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Establish `h' : b.val ≠ a.val` using `fun e => h (Fin.ext e)`. Rewrite using `[if_neg h]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem ps_succ {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (a : Fin r) (t : Fin k) :
    ps m (a.val + 1) t = ps m a.val t + m (a, t) := by
  have : m (a, t) = ∑ b : Fin r, if b = a then m (b, t) else 0 := by simp
  rw [this, ps, ps, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b = a
  · subst h; simp
  · have h' : b.val ≠ a.val := fun e => h (Fin.ext e)
    rw [if_neg h]
    split_ifs <;> omega

/- English proof (translation)
Simplify using `[ps]`.
-/
theorem ps_top {r k : ℕ} (m : Fin r × Fin k →₀ ℕ) (t : Fin k) : ps m r t = ∑ b, m (b, t) := by
  simp [ps]

/- English proof (translation)
The claim follows from `| 0, _ => ps_zero m _ | t + 1, ht => by have h1 := (interlaced_iff m).1 hm ⟨t, by omega⟩ ⟨t + 1, ht⟩ rfl ⟨t, by omega⟩ have h2 := ps_diag m hm t (by omega) simp only at h1 omega`.
-/
theorem ps_diag {r : ℕ} (m : Fin r × Fin r →₀ ℕ) (hm : Interlaced m) :
    ∀ (t : ℕ) (ht : t < r), ps m t ⟨t, ht⟩ = 0
  | 0, _ => ps_zero m _
  | t + 1, ht => by
    have h1 := (interlaced_iff m).1 hm ⟨t, by omega⟩ ⟨t + 1, ht⟩ rfl ⟨t, by omega⟩
    have h2 := ps_diag m hm t (by omega)
    simp only at h1
    omega

/- English proof (translation)
Consider the cases of `r with`. Consider the case `zero => intro a`. Conclude with `a.elim0`. Consider the case `succ r`. Use `Fin.antitone_iff_succ_le.2 fun i => ?_` and prove the remaining obligations.

Establish `h1` using `(interlaced_iff m).1 hm i.castSucc i.succ (by simp) i.succ`. Establish `h2` using `ps_succ m i.succ i.succ`. Establish `h3` using `ps_succ m i.castSucc i.castSucc`. Establish `h4 : ps m i.succ.val i.succ = 0` using `ps_diag m hm _ i.succ.2`. Establish `h5 : ps m i.castSucc.val i.castSucc = 0` using `ps_diag m hm _ i.castSucc.2`.

Simplify using `only [Fin.val_succ, Fin.val_castSucc] at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem diag_anti {r : ℕ} (m : Fin r × Fin r →₀ ℕ) (hm : Interlaced m) :
    Antitone fun t : Fin r => m (t, t) := by
  cases r with
  | zero => intro a; exact a.elim0
  | succ r =>
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have h1 := (interlaced_iff m).1 hm i.castSucc i.succ (by simp) i.succ
    have h2 := ps_succ m i.succ i.succ
    have h3 := ps_succ m i.castSucc i.castSucc
    have h4 : ps m i.succ.val i.succ = 0 := ps_diag m hm _ i.succ.2
    have h5 : ps m i.castSucc.val i.castSucc = 0 := ps_diag m hm _ i.castSucc.2
    simp only [Fin.val_succ, Fin.val_castSucc] at *
    omega

def res {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => m (v.1.castSucc, v.2.castSucc)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem res_apply {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (a t : Fin n) :
    res m (a, t) = m (a.castSucc, t.castSucc) := rfl

/- English proof (translation)
Establish `: ¬ n < a` using `by omega`. Simplify using `[ps, Fin.sum_univ_castSucc, res_apply, this]`.
-/
theorem ps_res {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (a : ℕ) (ha : a ≤ n) (t : Fin n) :
    ps (res m) a t = ps m a t.castSucc := by
  have : ¬ n < a := by omega
  simp [ps, Fin.sum_univ_castSucc, res_apply, this]

/- English proof (translation)
Rewrite `hm`, the goal using `[interlaced_iff]`. Introduce `l j hj a`. Rewrite using `[ps_res _ _ (by omega), ps_res _ _ (by omega)]`. Conclude with `hm l.castSucc j.castSucc hj a.castSucc`.
-/
theorem res_interlaced {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (hm : Interlaced m) :
    Interlaced (res m) := by
  rw [interlaced_iff] at hm ⊢
  intro l j hj a
  rw [ps_res _ _ (by omega), ps_res _ _ (by omega)]
  exact hm l.castSucc j.castSucc hj a.castSucc

def subDiag {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => m v - if v.1 = v.2 then c else 0

/- English proof (translation)
Establish `e : subDiag m c (a, t) = m (a, t) - if a = t then c else 0` using `rfl`. Rewrite using `[e]`. Use `split_ifs with h`. Substitute `h` using the available equality. Use `hc a` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.
-/
theorem subDiag_add {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t)) (a t : Fin n) :
    subDiag m c (a, t) + (if a = t then c else 0) = m (a, t) := by
  have e : subDiag m c (a, t) = m (a, t) - if a = t then c else 0 := rfl
  rw [e]
  split_ifs with h
  · subst h
    have := hc a
    omega
  · simp

/- English proof (translation)
Establish `: (if t.val < a then c else 0) = ∑ b : Fin n, if b = t then (if t.val < a then c else 0) else 0` using `by simp`. Rewrite using `[this, ps, ps, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `subDiag_add m c hc b t` as an intermediate fact. Distinguish the cases in `h : b = t`.

Substitute `h` using the available equality. Simplify using `only [if_true] at this ⊢`. Apply the tactic sequence `split_ifs <;> omega`. Apply the tactic sequence `simp only [if_neg h] at this ⊢ split_ifs <;> omega`.
-/
theorem ps_subDiag {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t)) (a : ℕ) (t : Fin n) :
    ps (subDiag m c) a t + (if t.val < a then c else 0) = ps m a t := by
  have : (if t.val < a then c else 0) = ∑ b : Fin n, if b = t then (if t.val < a then c else 0) else 0 := by simp
  rw [this, ps, ps, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := subDiag_add m c hc b t
  by_cases h : b = t
  · subst h
    simp only [if_true] at this ⊢
    split_ifs <;> omega
  · simp only [if_neg h] at this ⊢
    split_ifs <;> omega

/- English proof (translation)
Rewrite `hm`, the goal using `[interlaced_iff]`. Introduce `l j hj a`. Establish `h1` using `hm l j hj a`. Establish `h2` using `ps_subDiag m c hc (a.val + 1) j`. Establish `h3` using `ps_subDiag m c hc a.val l`.

Apply the tactic sequence `split_ifs at h2 h3 <;> omega`.
-/
theorem subDiag_interlaced {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (c : ℕ) (hc : ∀ t, c ≤ m (t, t))
    (hm : Interlaced m) : Interlaced (subDiag m c) := by
  rw [interlaced_iff] at hm ⊢
  intro l j hj a
  have h1 := hm l j hj a
  have h2 := ps_subDiag m c hc (a.val + 1) j
  have h3 := ps_subDiag m c hc a.val l
  split_ifs at h2 h3 <;> omega

/- English proof (translation)
Establish `h0 : 0 < N` using `t.pos`. Use `lam.anti (show t ≤ ⟨N - 1, by omega⟩ from Fin.le_def.2 (by have := t.2; simp only; omega))` as an intermediate fact. Simplify using `only [DomWeight.natW, DomWeight.detShift, dif_pos h0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem natW_cast {N : ℕ} (lam : DomWeight N) (t : Fin N) :
    (lam.natW t : ℤ) = lam.w t - lam.detShift := by
  have h0 : 0 < N := t.pos
  have := lam.anti (show t ≤ ⟨N - 1, by omega⟩ from Fin.le_def.2 (by have := t.2; simp only; omega))
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos h0]
  omega

/- English proof (translation)
Take `⟨m, hm, hcol⟩` from `m`. Establish `hup : ∀ t : Fin n, lam.detShift + ps m n t.castSucc ≤ lam.w t.castSucc` using `fun t => by`. Establish `h1` using `ps_succ m (Fin.last n) t.castSucc`. Establish `h2` using `ps_top m t.castSucc`. Establish `h3` using `hcol t.castSucc`.

Establish `h4` using `natW_cast lam t.castSucc`. Simplify using `only [Fin.val_last] at h1`. Use linear arithmetic over natural numbers and integers. Establish `hlo : ∀ t : Fin n, lam.w t.succ ≤ lam.detShift + ps m n t.castSucc` using `fun t => by`. Establish `h1` using `(interlaced_iff m).1 hm t.castSucc t.succ (by simp) (Fin.last n)`.

Establish `h2` using `ps_top m t.succ`. Establish `h3` using `hcol t.succ`. Establish `h4` using `natW_cast lam t.succ`. Simplify using `only [Fin.val_last] at h1`. Use linear arithmetic over natural numbers and integers.

Set `mu : DomWeight n` to `⟨fun t => lam.detShift + ps m n t.castSucc, fun i j hij => by`. Break down `hij.eq_or_lt with rfl | hlt` into its components or cases. Conclude with `le_rfl`. Conclude with `(hup j).trans ((lam.anti (Fin.le_def.2 (by simpa using hlt))).trans (hlo i))⟩`. Establish `hI : Interlace rfl lam mu` using `fun i => ⟨hup i, hlo i⟩`.

Establish `hr` using `res_interlaced m hm`. Establish `hc' : ∀ h0 : 0 < n, mu.detShift - lam.detShift = (res m (⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩) : ℕ)` using `fun h0 => by`. Establish `h1` using `ps_succ (res m) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩`. Establish `h2` using `ps_diag (res m) hr (n - 1) (by omega)`. Establish `h3` using `ps_res m n le_rfl ⟨n - 1, by omega⟩`.

Establish `h4 : mu.detShift = lam.detShift + ps m n (Fin.castSucc ⟨n - 1, by omega⟩)`. Simplify using `only [DomWeight.detShift, dif_pos h0, mu]`. Establish `h5 : n - 1 + 1 = n` using `by omega`. Simplify using `only [h5] at h1`. Use linear arithmetic over natural numbers and integers.

Establish `hc : ∀ t, (mu.detShift - lam.detShift).toNat ≤ res m (t, t)` using `fun t => by`. Establish `h0 : 0 < n` using `t.pos`. Rewrite using `[hc' h0, Int.toNat_natCast]`. Conclude with `diag_anti _ hr (Fin.le_def.2 (by have := t.2; simp only; omega))`. Use `⟨⟨⟨mu, hI⟩, subDiag (res m) _, subDiag_interlaced _ _ hc hr, fun t => ?_⟩, fun _ => rfl, fun a t => subDiag_add _ _ hc a t⟩` and prove the remaining obligations.

Establish `h1` using `ps_subDiag _ _ hc n t`. Rewrite `h1` using `[if_pos t.2, ps_top, ps_res m n le_rfl]`. Establish `h2` using `natW_cast mu t`. Establish `h3 : mu.w t = lam.detShift + ps m n t.castSucc` using `rfl`. Establish `h4` using `hc' t.pos`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_image (n : ℕ) (lam : DomWeight (n + 1)) (m : ssIdx (n + 1) (n + 1) lam.natW) :
    ∃ x : (Σ mu : Below rfl lam, ssIdx n n mu.1.natW),
      (∀ t, x.1.1.w t = lam.detShift + ps m.1 n t.castSucc) ∧
      ∀ a t, x.2.1 (a, t) + (if a = t then (x.1.1.detShift - lam.detShift).toNat else 0) =
        m.1 (a.castSucc, t.castSucc) := by
  obtain ⟨m, hm, hcol⟩ := m
  have hup : ∀ t : Fin n, lam.detShift + ps m n t.castSucc ≤ lam.w t.castSucc := fun t => by
    have h1 := ps_succ m (Fin.last n) t.castSucc
    have h2 := ps_top m t.castSucc
    have h3 := hcol t.castSucc
    have h4 := natW_cast lam t.castSucc
    simp only [Fin.val_last] at h1
    omega
  have hlo : ∀ t : Fin n, lam.w t.succ ≤ lam.detShift + ps m n t.castSucc := fun t => by
    have h1 := (interlaced_iff m).1 hm t.castSucc t.succ (by simp) (Fin.last n)
    have h2 := ps_top m t.succ
    have h3 := hcol t.succ
    have h4 := natW_cast lam t.succ
    simp only [Fin.val_last] at h1
    omega
  let mu : DomWeight n := ⟨fun t => lam.detShift + ps m n t.castSucc, fun i j hij => by
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (hup j).trans ((lam.anti (Fin.le_def.2 (by simpa using hlt))).trans (hlo i))⟩
  have hI : Interlace rfl lam mu := fun i => ⟨hup i, hlo i⟩
  have hr := res_interlaced m hm
  have hc' : ∀ h0 : 0 < n, mu.detShift - lam.detShift =
      (res m (⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩) : ℕ) := fun h0 => by
    have h1 := ps_succ (res m) ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩
    have h2 := ps_diag (res m) hr (n - 1) (by omega)
    have h3 := ps_res m n le_rfl ⟨n - 1, by omega⟩
    have h4 : mu.detShift = lam.detShift + ps m n (Fin.castSucc ⟨n - 1, by omega⟩) := by
      simp only [DomWeight.detShift, dif_pos h0, mu]
    have h5 : n - 1 + 1 = n := by omega
    simp only [h5] at h1
    omega
  have hc : ∀ t, (mu.detShift - lam.detShift).toNat ≤ res m (t, t) := fun t => by
    have h0 : 0 < n := t.pos
    rw [hc' h0, Int.toNat_natCast]
    exact diag_anti _ hr (Fin.le_def.2 (by have := t.2; simp only; omega))
  refine ⟨⟨⟨mu, hI⟩, subDiag (res m) _, subDiag_interlaced _ _ hc hr, fun t => ?_⟩, fun _ => rfl,
    fun a t => subDiag_add _ _ hc a t⟩
  have h1 := ps_subDiag _ _ hc n t
  rw [if_pos t.2, ps_top, ps_res m n le_rfl] at h1
  have h2 := natW_cast mu t
  have h3 : mu.w t = lam.detShift + ps m n t.castSucc := rfl
  have h4 := hc' t.pos
  simp only
  omega

end GlobalTheory.Branching.SsInj

namespace GlobalTheory.Branching

open SsInj

/- English proof (translation)
Introduce `n N h lam`. Substitute `h` using the available equality. Use `choose F hF1 hF2 using exists_image n lam`. Use `⟨F, fun m m' e => ?_⟩` and prove the remaining obligations. Establish `hin : ∀ a t : Fin n, m.1 (a.castSucc, t.castSucc) = m'.1 (a.castSucc, t.castSucc)` using `fun a t => by`.

Rewrite using `[← hF2 m a t, ← hF2 m' a t, e]`. Establish `hlast : ∀ x : ssIdx (n + 1) (n + 1) lam.natW, ∀ a, x.1 (a, Fin.last n) = 0` using `fun x a => by`. Establish `h1` using `x.2.2 (Fin.last n)`. Establish `h2 : lam.natW (Fin.last n) = 0`. Simplify using `[DomWeight.natW, DomWeight.detShift, Fin.last]`.

Rewrite `h1` using `[h2]`. Conclude with `Finset.sum_eq_zero_iff.1 h1 a (Finset.mem_univ a)`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `⟨a, t⟩`. Proceed by induction on `t using Fin.lastCases with`.

Consider the case `last => rw [hlast, hlast]`. Consider the case `cast t`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `cast a => exact hin a t`. Consider the case `last`.

Establish `h1` using `m.2.2 t.castSucc`. Establish `h2` using `m'.2.2 t.castSucc`. Rewrite `h1`, `h2` using `[Fin.sum_univ_castSucc]`. Simplify using `only [hin] at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_ssIdx_injective : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N),
    ∃ F : ssIdx N N lam.natW → (Σ mu : Below h lam, ssIdx n n mu.1.natW), Function.Injective F := by
  intro n N h lam
  subst h
  choose F hF1 hF2 using exists_image n lam
  refine ⟨F, fun m m' e => ?_⟩
  have hin : ∀ a t : Fin n, m.1 (a.castSucc, t.castSucc) = m'.1 (a.castSucc, t.castSucc) := fun a t => by
    rw [← hF2 m a t, ← hF2 m' a t, e]
  have hlast : ∀ x : ssIdx (n + 1) (n + 1) lam.natW, ∀ a, x.1 (a, Fin.last n) = 0 := fun x a => by
    have h1 := x.2.2 (Fin.last n)
    have h2 : lam.natW (Fin.last n) = 0 := by
      simp [DomWeight.natW, DomWeight.detShift, Fin.last]
    rw [h2] at h1
    exact Finset.sum_eq_zero_iff.1 h1 a (Finset.mem_univ a)
  apply Subtype.ext
  ext ⟨a, t⟩
  induction t using Fin.lastCases with
  | last => rw [hlast, hlast]
  | cast t =>
    induction a using Fin.lastCases with
    | cast a => exact hin a t
    | last =>
      have h1 := m.2.2 t.castSucc
      have h2 := m'.2.2 t.castSucc
      rw [Fin.sum_univ_castSucc] at h1 h2
      simp only [hin] at h1
      omega

end GlobalTheory.Branching

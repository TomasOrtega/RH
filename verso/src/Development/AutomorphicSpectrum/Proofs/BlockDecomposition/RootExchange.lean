import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement

open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.RootExch

section Abstract

variable {G : Type*} [Group G] [Fintype G]

/- English proof (translation)
Establish `h` using `hm 1 H.one_mem 1 H.one_mem`. Establish `h0` using `hne 1 H.one_mem`. Simplify using `only [mul_one] at h`. Conclude with `(mul_right_inj' h0).1 (by rw [mul_one]; exact h.symm)`.
-/
theorem lam_one (H : Subgroup G) (lam : G → ℂ)
    (hm : ∀ a ∈ H, ∀ b ∈ H, lam (a * b) = lam a * lam b) (hne : ∀ a ∈ H, lam a ≠ 0) : lam 1 = 1 := by
  have h := hm 1 H.one_mem 1 H.one_mem
  have h0 := hne 1 H.one_mem
  simp only [mul_one] at h
  exact (mul_right_inj' h0).1 (by rw [mul_one]; exact h.symm)

/- English proof (translation)
Establish `h` using `hm a ha a⁻¹ (H.inv_mem ha)`. Rewrite `h` using `[mul_inv_cancel, lam_one H lam hm hne]`. Conclude with `eq_inv_of_mul_eq_one_right h.symm`.
-/
theorem lam_inv (H : Subgroup G) (lam : G → ℂ)
    (hm : ∀ a ∈ H, ∀ b ∈ H, lam (a * b) = lam a * lam b) (hne : ∀ a ∈ H, lam a ≠ 0)
    (a : G) (ha : a ∈ H) : lam a⁻¹ = (lam a)⁻¹ := by
  have h := hm a ha a⁻¹ (H.inv_mem ha)
  rw [mul_inv_cancel, lam_one H lam hm hne] at h
  exact eq_inv_of_mul_eq_one_right h.symm

open Classical in

/- English proof (translation)
Take `⟨c, hcdef⟩ : ∃ c, c = h * y * h⁻¹ * y⁻¹` from `⟨_, rfl⟩`. Rewrite `hc`, `hl` using `[← hcdef]`. Set `e : G ≃ G` to `(MulAut.conj h).toEquiv.trans (Equiv.mulRight c)`. Establish `he : ∀ u, e u = h * u * h⁻¹ * c` using `fun u => rfl`. Establish `hmem : ∀ u, e u ∈ H ↔ u ∈ H`.

Introduce `u`. Rewrite using `[he]`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Establish `h1 : h⁻¹ * (h * u * h⁻¹ * c * c⁻¹) * h = u` using `by group`.

Rewrite using `[← h1]`. Conclude with `H.mul_mem (H.mul_mem (H.inv_mem hh) (H.mul_mem hu (H.inv_mem hc))) hh`. Introduce `hu`. Conclude with `H.mul_mem (H.mul_mem (H.mul_mem hh hu) (H.inv_mem hh)) hc`. Establish `hcne` using `hne c hc`.

Establish `key : (∑ u, if u ∈ H then (lam u)⁻¹ * χ (u * y) else 0) = (lam c)⁻¹ * ∑ u, if u ∈ H then (lam u)⁻¹ * χ (u * y) else 0` using `by conv_lhs => rw [← Equiv.sum_comp e]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Distinguish the cases in `hu : u ∈ H`. Rewrite using `[if_pos ((hmem u).2 hu), if_pos hu]`.

Establish `h1 : e u * y = h * (u * y) * h⁻¹`. Rewrite using `[he, hcdef]`. Use `group`. Establish `h2 : lam (e u) = lam u * lam c`. Rewrite using `[he, hm _ (H.mul_mem (H.mul_mem hh hu) (H.inv_mem hh)) _ hc, hm _ (H.mul_mem hh hu) _ (H.inv_mem hh), hm _ hh _ hu, lam_inv H lam hm hne h hh]`.

Use `hne h hh` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite using `[h1, hχ, h2, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (fun h' => hu ((hmem u).1 h')), if_neg hu, mul_zero]`.

Assume the negation of the conclusion as `hD`. Apply `hl` to reduce the goal to its premises. Establish `h3 : (lam c)⁻¹ = 1` using `mul_right_cancel₀ hD (by rw [one_mul]; exact key.symm)`. Conclude with `inv_eq_one.1 h3`.
-/
theorem sum_twist_zero (H : Subgroup G) (lam χ : G → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g)
    (hm : ∀ a ∈ H, ∀ b ∈ H, lam (a * b) = lam a * lam b) (hne : ∀ a ∈ H, lam a ≠ 0)
    (y h : G) (hh : h ∈ H) (hc : h * y * h⁻¹ * y⁻¹ ∈ H) (hl : lam (h * y * h⁻¹ * y⁻¹) ≠ 1) :
    (∑ u, if u ∈ H then (lam u)⁻¹ * χ (u * y) else 0) = 0 := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = h * y * h⁻¹ * y⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hc hl
  let e : G ≃ G := (MulAut.conj h).toEquiv.trans (Equiv.mulRight c)
  have he : ∀ u, e u = h * u * h⁻¹ * c := fun u => rfl
  have hmem : ∀ u, e u ∈ H ↔ u ∈ H := by
    intro u
    rw [he]
    constructor
    · intro hu
      have h1 : h⁻¹ * (h * u * h⁻¹ * c * c⁻¹) * h = u := by group
      rw [← h1]
      exact H.mul_mem (H.mul_mem (H.inv_mem hh) (H.mul_mem hu (H.inv_mem hc))) hh
    · intro hu
      exact H.mul_mem (H.mul_mem (H.mul_mem hh hu) (H.inv_mem hh)) hc
  have hcne := hne c hc
  have key : (∑ u, if u ∈ H then (lam u)⁻¹ * χ (u * y) else 0) =
      (lam c)⁻¹ * ∑ u, if u ∈ H then (lam u)⁻¹ * χ (u * y) else 0 := by
    conv_lhs => rw [← Equiv.sum_comp e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ H
    · rw [if_pos ((hmem u).2 hu), if_pos hu]
      have h1 : e u * y = h * (u * y) * h⁻¹ := by
        rw [he, hcdef]; group
      have h2 : lam (e u) = lam u * lam c := by
        rw [he, hm _ (H.mul_mem (H.mul_mem hh hu) (H.inv_mem hh)) _ hc,
          hm _ (H.mul_mem hh hu) _ (H.inv_mem hh), hm _ hh _ hu, lam_inv H lam hm hne h hh]
        have := hne h hh
        field_simp
      rw [h1, hχ, h2, mul_inv]
      ring
    · rw [if_neg (fun h' => hu ((hmem u).1 h')), if_neg hu, mul_zero]
  by_contra hD
  apply hl
  have h3 : (lam c)⁻¹ = 1 := mul_right_cancel₀ hD (by rw [one_mul]; exact key.symm)
  exact inv_eq_one.1 h3

open Classical in
/- English proof (translation)
Establish `hterm : ∀ v, (if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) = if v ∈ P ∧ v ∈ Q then ∑ u, (if u ∈ P then (lam u)⁻¹ * χ u else 0) else 0`. Introduce `v`. Distinguish the cases in `hvQ : v ∈ Q`. Distinguish the cases in `hvP : v ∈ P`. Rewrite using `[if_pos hvQ, if_pos ⟨hvP, hvQ⟩, ← Equiv.sum_comp (Equiv.mulRight v⁻¹), Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Establish `hiff : u * v⁻¹ ∈ P ↔ u ∈ P` using `P.mul_mem_cancel_right (P.inv_mem hvP)`. Rewrite using `[show (Equiv.mulRight v⁻¹) u = u * v⁻¹ from rfl]`. Distinguish the cases in `hu : u ∈ P`. Rewrite using `[if_pos (hiff.2 hu), if_pos hu, hm _ hu _ (P.inv_mem hvP), lam_inv P lam hm hne v hvP, inv_mul_cancel_right]`.

Use `hne v hvP` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite using `[if_neg (fun h' => hu (hiff.1 h')), if_neg hu, mul_zero]`. Take `⟨h, hh, hc, hl⟩` from `hPQ v hvQ hvP`. Rewrite using `[if_pos hvQ, if_neg (fun h' => hvP h'.1), sum_twist_zero P lam χ hχ hm hne v h hh hc hl, mul_zero]`.

Rewrite using `[if_neg hvQ, if_neg (fun h' => hvQ h'.2)]`. Rewrite using `[Finset.sum_congr rfl fun v _ => hterm v, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`.
-/
theorem one_side (P Q : Subgroup G) (lam χ : G → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g)
    (hm : ∀ a ∈ P, ∀ b ∈ P, lam (a * b) = lam a * lam b) (hne : ∀ a ∈ P, lam a ≠ 0)
    (hPQ : ∀ v ∈ Q, v ∉ P → ∃ h ∈ P, h * v * h⁻¹ * v⁻¹ ∈ P ∧ lam (h * v * h⁻¹ * v⁻¹) ≠ 1) :
    (∑ v, if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) =
      ((Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q).card : ℂ) *
        ∑ u, if u ∈ P then (lam u)⁻¹ * χ u else 0 := by
  have hterm : ∀ v, (if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) =
      if v ∈ P ∧ v ∈ Q then ∑ u, (if u ∈ P then (lam u)⁻¹ * χ u else 0) else 0 := by
    intro v
    by_cases hvQ : v ∈ Q
    · by_cases hvP : v ∈ P
      · rw [if_pos hvQ, if_pos ⟨hvP, hvQ⟩, ← Equiv.sum_comp (Equiv.mulRight v⁻¹), Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        have hiff : u * v⁻¹ ∈ P ↔ u ∈ P := P.mul_mem_cancel_right (P.inv_mem hvP)
        rw [show (Equiv.mulRight v⁻¹) u = u * v⁻¹ from rfl]
        by_cases hu : u ∈ P
        · rw [if_pos (hiff.2 hu), if_pos hu, hm _ hu _ (P.inv_mem hvP), lam_inv P lam hm hne v hvP,
            inv_mul_cancel_right]
          have := hne v hvP
          field_simp
        · rw [if_neg (fun h' => hu (hiff.1 h')), if_neg hu, mul_zero]
      · obtain ⟨h, hh, hc, hl⟩ := hPQ v hvQ hvP
        rw [if_pos hvQ, if_neg (fun h' => hvP h'.1),
          sum_twist_zero P lam χ hχ hm hne v h hh hc hl, mul_zero]
    · rw [if_neg hvQ, if_neg (fun h' => hvQ h'.2)]
  rw [Finset.sum_congr rfl fun v _ => hterm v, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

open Classical in

/- English proof (translation)
Establish `h1` using `one_side P Q lam χ hχ hmP hneP hPQ`. Establish `h2` using `one_side Q P lam χ hχ hmQ hneQ hQP`. Establish `hswap : (∑ v, if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) = ∑ v, if v ∈ P then (lam v)⁻¹ * (∑ u, if u ∈ Q then (lam u)⁻¹ * χ (u * v) else 0) else 0`. Establish `e1 : ∀ v, (if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) = ∑ u, if v ∈ Q ∧ u ∈ P then (lam v)⁻¹ * ((lam u)⁻¹ * χ (u * v)) else 0`. Introduce `v`.

Distinguish the cases in `hv : v ∈ Q`. Simplify using `only [hv, if_true, true_and, Finset.mul_sum, mul_ite, mul_zero]`. Simplify using `[hv]`. Establish `e2 : ∀ v, (if v ∈ P then (lam v)⁻¹ * (∑ u, if u ∈ Q then (lam u)⁻¹ * χ (u * v) else 0) else 0) = ∑ u, if v ∈ P ∧ u ∈ Q then (lam v)⁻¹ * ((lam u)⁻¹ * χ (u * v)) else 0`. Introduce `v`.

Distinguish the cases in `hv : v ∈ P`. Simplify using `only [hv, if_true, true_and, Finset.mul_sum, mul_ite, mul_zero]`. Simplify using `[hv]`. Rewrite using `[Finset.sum_congr rfl fun v _ => e1 v, Finset.sum_congr rfl fun v _ => e2 v, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Establish `hc : χ (u * v) = χ (v * u)`. Use `hχ v (u * v)` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Use `group`.

Distinguish the cases in `hh : v ∈ Q ∧ u ∈ P`. Rewrite using `[if_pos hh, if_pos ⟨hh.2, hh.1⟩, hc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hh, if_neg (fun h' => hh ⟨h'.2, h'.1⟩)]`. Establish `hn : ((Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q).card : ℂ) ≠ 0`.

Establish `: (Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q).Nonempty` using `⟨1, by simp [P.one_mem, Q.one_mem]⟩`. Conclude with `this.card_pos.ne'` after adjusting the coercions. Establish `hcard : (Finset.univ.filter fun v => v ∈ Q ∧ v ∈ P) = Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q`. Use extensionality with `v`. Simplify using `[and_comm]`.

Rewrite `h1` using `[hswap, h2, hcard]`. Conclude with `(mul_left_cancel₀ hn h1).symm`.
-/
theorem exchange (P Q : Subgroup G) (lam χ : G → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g)
    (hmP : ∀ a ∈ P, ∀ b ∈ P, lam (a * b) = lam a * lam b) (hneP : ∀ a ∈ P, lam a ≠ 0)
    (hmQ : ∀ a ∈ Q, ∀ b ∈ Q, lam (a * b) = lam a * lam b) (hneQ : ∀ a ∈ Q, lam a ≠ 0)
    (hPQ : ∀ v ∈ Q, v ∉ P → ∃ h ∈ P, h * v * h⁻¹ * v⁻¹ ∈ P ∧ lam (h * v * h⁻¹ * v⁻¹) ≠ 1)
    (hQP : ∀ v ∈ P, v ∉ Q → ∃ h ∈ Q, h * v * h⁻¹ * v⁻¹ ∈ Q ∧ lam (h * v * h⁻¹ * v⁻¹) ≠ 1) :
    (∑ u, if u ∈ P then (lam u)⁻¹ * χ u else 0) = ∑ u, if u ∈ Q then (lam u)⁻¹ * χ u else 0 := by
  have h1 := one_side P Q lam χ hχ hmP hneP hPQ
  have h2 := one_side Q P lam χ hχ hmQ hneQ hQP
  have hswap : (∑ v, if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) =
      ∑ v, if v ∈ P then (lam v)⁻¹ * (∑ u, if u ∈ Q then (lam u)⁻¹ * χ (u * v) else 0) else 0 := by
    have e1 : ∀ v, (if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) =
        ∑ u, if v ∈ Q ∧ u ∈ P then (lam v)⁻¹ * ((lam u)⁻¹ * χ (u * v)) else 0 := by
      intro v
      by_cases hv : v ∈ Q
      · simp only [hv, if_true, true_and, Finset.mul_sum, mul_ite, mul_zero]
      · simp [hv]
    have e2 : ∀ v, (if v ∈ P then (lam v)⁻¹ * (∑ u, if u ∈ Q then (lam u)⁻¹ * χ (u * v) else 0) else 0) =
        ∑ u, if v ∈ P ∧ u ∈ Q then (lam v)⁻¹ * ((lam u)⁻¹ * χ (u * v)) else 0 := by
      intro v
      by_cases hv : v ∈ P
      · simp only [hv, if_true, true_and, Finset.mul_sum, mul_ite, mul_zero]
      · simp [hv]
    rw [Finset.sum_congr rfl fun v _ => e1 v, Finset.sum_congr rfl fun v _ => e2 v, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    have hc : χ (u * v) = χ (v * u) := by
      have := hχ v (u * v)
      rw [← this]; congr 1; group
    by_cases hh : v ∈ Q ∧ u ∈ P
    · rw [if_pos hh, if_pos ⟨hh.2, hh.1⟩, hc]; ring
    · rw [if_neg hh, if_neg (fun h' => hh ⟨h'.2, h'.1⟩)]
  have hn : ((Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q).card : ℂ) ≠ 0 := by
    have : (Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q).Nonempty :=
      ⟨1, by simp [P.one_mem, Q.one_mem]⟩
    exact_mod_cast this.card_pos.ne'
  have hcard : (Finset.univ.filter fun v => v ∈ Q ∧ v ∈ P) = Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q := by
    ext v; simp [and_comm]
  rw [hswap, h2, hcard] at h1
  exact (mul_left_cancel₀ hn h1).symm

end Abstract

end GlobalTheory.CompanionTheory.RootExch

namespace GlobalTheory.CompanionTheory.RootExch

section Mat

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

def tv (r t : ι) (h : r ≠ t) (s : K) : GL ι K :=
  ⟨Matrix.transvection r t s, Matrix.transvection r t (-s),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Matrix.transvection r t s) i j = _`. Simplify using `[Matrix.transvection, Matrix.single_apply, eq_comm]`.
-/
theorem tv_apply (r t : ι) (h : r ≠ t) (s : K) (i j : ι) :
    ((tv r t h s : GL ι K) : Matrix ι ι K) i j = (1 : Matrix ι ι K) i j + if i = r ∧ j = t then s else 0 := by
  change (Matrix.transvection r t s) i j = _
  simp [Matrix.transvection, Matrix.single_apply, eq_comm]

/- English proof (translation)
Take `⟨M, hM⟩ : ∃ M : Matrix ι ι K, M = (g : Matrix ι ι K)` from `⟨_, rfl⟩`. Take `⟨N, hN⟩ : ∃ N : Matrix ι ι K, N = ((g⁻¹ : GL ι K) : Matrix ι ι K)` from `⟨_, rfl⟩`. Establish `hMN : M * N = 1` using `by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hval : ((tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ : GL ι K) : Matrix ι ι K) = (1 + Matrix.single r t s) * M * (1 + Matrix.single r t (-s)) * N`. Rewrite using `[hM, hN]`.

Both sides reduce to the same expression. Establish `hz : Matrix.single r t s * M * Matrix.single r t (-s) = 0`. Rewrite using `[Matrix.single_mul_mul_single, hM, hg]`. Simplify using the standard rewrite rules. Establish `hexp : (1 + Matrix.single r t s) * M * (1 + Matrix.single r t (-s)) * N = 1 + Matrix.single r t s + M * Matrix.single r t (-s) * N`.

Combine the equalities or inequalities in the displayed calculation. Establish `hent : (M * Matrix.single r t (-s) * N) i j = - (s * M i r * N t j)`. Establish `h1 : ∀ k, (M * Matrix.single r t (-s)) i k = if k = t then M i r * (-s) else 0`. Introduce `k`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single r]`.

Distinguish the cases in `hk : k = t`. Substitute `hk` using the available equality. Simplify using `[Matrix.single_apply]`. Simplify using `[Matrix.single_apply, hk, Ne.symm hk]`. Introduce `b _ hb`.

Simplify using `[Matrix.single_apply, Ne.symm hb]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_apply, Finset.sum_congr rfl fun k _ => by rw [h1 k]]`. Simplify using `only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hval, hexp, Matrix.add_apply, Matrix.add_apply, hent, ← hM, ← hN, sub_eq_add_neg]`. Simplify using `[Matrix.single_apply, eq_comm]`.
-/
theorem comm_entry (g : GL ι K) (r t : ι) (h : r ≠ t) (s : K) (hg : (g : Matrix ι ι K) t r = 0) (i j : ι) :
    ((tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ : GL ι K) : Matrix ι ι K) i j =
      (1 : Matrix ι ι K) i j + (if i = r ∧ j = t then s else 0) -
        s * (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix ι ι K, M = (g : Matrix ι ι K) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix ι ι K, N = ((g⁻¹ : GL ι K) : Matrix ι ι K) := ⟨_, rfl⟩
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hval : ((tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ : GL ι K) : Matrix ι ι K) =
      (1 + Matrix.single r t s) * M * (1 + Matrix.single r t (-s)) * N := by
    rw [hM, hN]; rfl
  have hz : Matrix.single r t s * M * Matrix.single r t (-s) = 0 := by
    rw [Matrix.single_mul_mul_single, hM, hg]
    simp
  have hexp : (1 + Matrix.single r t s) * M * (1 + Matrix.single r t (-s)) * N =
      1 + Matrix.single r t s + M * Matrix.single r t (-s) * N := by
    calc _ = M * N + Matrix.single r t s * (M * N) + M * Matrix.single r t (-s) * N
          + Matrix.single r t s * M * Matrix.single r t (-s) * N := by noncomm_ring
      _ = _ := by rw [hMN, hz]; simp
  have hent : (M * Matrix.single r t (-s) * N) i j = - (s * M i r * N t j) := by
    have h1 : ∀ k, (M * Matrix.single r t (-s)) i k = if k = t then M i r * (-s) else 0 := by
      intro k
      rw [Matrix.mul_apply, Finset.sum_eq_single r]
      · by_cases hk : k = t
        · subst hk; simp [Matrix.single_apply]
        · simp [Matrix.single_apply, hk, Ne.symm hk]
      · intro b _ hb
        simp [Matrix.single_apply, Ne.symm hb]
      · simp
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => by rw [h1 k]]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hval, hexp, Matrix.add_apply, Matrix.add_apply, hent, ← hM, ← hN, sub_eq_add_neg]
  simp [Matrix.single_apply, eq_comm]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h ((hg i j).2 hc.1 hc.2)`.
-/
theorem nz_of_mem {Φ : ι → ι → Prop} {g : GL ι K} (hg : g ∈ patSet K Φ) {i j : ι}
    (h : (g : Matrix ι ι K) i j ≠ 0) : i = j ∨ Φ i j := by
  by_contra hc
  push_neg at hc
  exact h ((hg i j).2 hc.1 hc.2)

/- English proof (translation)
Introduce `i j` and use `⟨(hg i j).1, fun hij hn => (hg i j).2 hij fun hΦ => hn (h i j hΦ)⟩`.
-/
theorem patSet_mono {Φ Ψ : ι → ι → Prop} (h : ∀ i j, Φ i j → Ψ i j) {g : GL ι K} (hg : g ∈ patSet K Φ) :
    g ∈ patSet K Ψ := fun i j => ⟨(hg i j).1, fun hij hn => (hg i j).2 hij fun hΦ => hn (h i j hΦ)⟩

/- English proof (translation)
Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `hij`. Substitute `hij` using the available equality. Establish `hh : ¬ (i = r ∧ i = t)` using `fun h' => h (h'.1.symm.trans h'.2)`.

Rewrite using `[tv_apply, if_neg hh]`. Simplify using the standard rewrite rules. Introduce `hij hn`. Establish `hh : ¬ (i = r ∧ j = t)`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `hn hrt`. Rewrite using `[tv_apply, if_neg hh]`. Simplify using `[Matrix.one_apply, hij]`.
-/
theorem tv_mem {Ψ : ι → ι → Prop} (r t : ι) (h : r ≠ t) (s : K) (hrt : Ψ r t) :
    tv r t h s ∈ patSet K Ψ := by
  intro i j
  constructor
  · intro hij
    subst hij
    have hh : ¬ (i = r ∧ i = t) := fun h' => h (h'.1.symm.trans h'.2)
    rw [tv_apply, if_neg hh]
    simp
  · intro hij hn
    have hh : ¬ (i = r ∧ j = t) := by
      rintro ⟨rfl, rfl⟩
      exact hn hrt
    rw [tv_apply, if_neg hh]
    simp [Matrix.one_apply, hij]

/- English proof (translation)
Establish `htr : (g : Matrix ι ι K) t r = 0`. Assume the negation of the conclusion as `hc`. Break down `nz_of_mem hg hc with h' | h'` into its components or cases. Conclude with `h h'.symm`. Conclude with `hΦ.1 _ (hΦ.2 _ _ _ h' hrt)`.

Establish `hirr : ∀ i, (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t i = 0`. Introduce `i`. Assume the negation of the conclusion as `hc`. Establish `h1` using `nz_of_mem hg (left_ne_zero_of_mul hc)`. Establish `h2` using `nz_of_mem hgi (right_ne_zero_of_mul hc)`.

Establish `hΦrr : Φ r r ∨ r = t`. Apply the tactic sequence `rcases h1 with rfl | h1 <;> rcases h2 with h2 | h2`. Conclude with `Or.inr h2.symm`. Conclude with `Or.inl (hΦ.2 _ _ _ hrt h2)`. Substitute `h2` using the available equality.

Conclude with `Or.inl (hΦ.2 _ _ _ hrt h1)`. Conclude with `Or.inl (hΦ.2 _ _ _ hrt (hΦ.2 _ _ _ h2 h1))`. Break down `hΦrr with h3 | h3` into its components or cases. Conclude with `hΦ.1 _ h3`. Conclude with `h h3`.

Prove the components needed by the constructor for the conclusion. Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `hij`. Substitute `hij` using the available equality.

Establish `hh : ¬ (i = r ∧ i = t)` using `fun h' => h (h'.1.symm.trans h'.2)`. Apply the tactic sequence `rw [comm_entry g r t h s htr, if_neg hh, mul_assoc, hirr]`. Simplify using the standard rewrite rules. Introduce `hij hn`. Apply the tactic sequence `rw [comm_entry g r t h s htr]`.

Distinguish the cases in `hrt' : i = r ∧ j = t`. Take `⟨rfl, rfl⟩` from `hrt'`. Rewrite using `[(hg i i).1 rfl, (hgi j j).1 rfl]`. Simplify using `[Matrix.one_apply, hij]`. Establish `hz : (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j = 0`.

Assume the negation of the conclusion as `hc`. Conclude with `hn (hΨ i j (nz_of_mem hg (left_ne_zero_of_mul hc)) (nz_of_mem hgi (right_ne_zero_of_mul hc)) hrt')`. Rewrite using `[if_neg hrt', mul_assoc, hz]`. Simplify using `[Matrix.one_apply, hij]`. Unfold `patChar`.

Use `congr 1`. Establish `hterm : ∀ i j, E i j * ((tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ : GL ι K) : Matrix ι ι K) i j = if i = p ∧ j = q then -(s * E p q * (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q) else 0`. Introduce `i j`. Distinguish the cases in `hE : E i j = 0`. Rewrite using `[hE, zero_mul] split_ifs with hpq`.

Take `⟨rfl, rfl⟩` from `hpq`. Rewrite using `[hE]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Establish `hΦij` using `hsupp i j hE`.

Establish `hij : i ≠ j` using `fun h' => hΦ.1 j (h' ▸ hΦij)`. Establish `hrt' : ¬ (i = r ∧ j = t)`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hE hErt`. Apply the tactic sequence `rw [comm_entry g r t h s htr, if_neg hrt']`.

Distinguish the cases in `hz : (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j = 0`. Use `split_ifs with hpq`. Take `⟨rfl, rfl⟩` from `hpq`. Establish `: s * E i j * (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j = s * E i j * ((g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j)` using `by ring`. Rewrite using `[this, hz, mul_assoc, hz]`.

Simplify using `[Matrix.one_apply, hij]`. Rewrite using `[mul_assoc, hz]`. Simplify using `[Matrix.one_apply, hij]`. Establish `h1` using `nz_of_mem hg (left_ne_zero_of_mul hz)`. Establish `h2` using `nz_of_mem hgi (right_ne_zero_of_mul hz)`.

Establish `hpq : i = p ∧ j = q`. Break down `h1 with h1 | h1` into its components or cases. Break down `h2 with h2 | h2` into its components or cases. Conclude with `absurd ⟨h1, h2.symm⟩ hrt'`. Substitute `h1` using the available equality.

Conclude with `hcomp _ _ _ hrt h2 hE`. Break down `h2 with h2 | h2` into its components or cases. Substitute `h2` using the available equality. Conclude with `hcomp _ _ _ h1 hrt hE`. Conclude with `hcomp _ _ _ h1 (hΦ.2 _ _ _ hrt h2) hE`.

Take `⟨rfl, rfl⟩` from `hpq`. Rewrite using `[if_pos ⟨rfl, rfl⟩]`. Simplify using `only [Matrix.one_apply, if_neg hij]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hterm]`.

Distinguish the cases in `hp : True`. Rewrite using `[Finset.sum_eq_single p, Finset.sum_eq_single q]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Conclude with `absurd trivial hp`.
-/
theorem comm_data {Φ Ψ : ι → ι → Prop} {E : ι → ι → K} (ψ₀ : AddChar K ℂ) (hΦ : IsPat Φ)
    (hsupp : ∀ i j, E i j ≠ 0 → Φ i j) (p q r t : ι)
    (hcomp : ∀ i j k, Φ i j → Φ j k → E i k ≠ 0 → i = p ∧ k = q)
    (g : GL ι K) (hg : g ∈ patSet K Φ) (hgi : g⁻¹ ∈ patSet K Φ) (hrt : Φ r t)
    (hΨ : ∀ i j, (i = r ∨ Φ i r) → (t = j ∨ Φ t j) → ¬ (i = r ∧ j = t) → Ψ i j)
    (hErt : E r t = 0) (h : r ≠ t) (s : K) :
    tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ ∈ patSet K Ψ ∧
      patChar E ψ₀ (tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹) =
        ψ₀ (-(s * E p q * (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)) := by
  have htr : (g : Matrix ι ι K) t r = 0 := by
    by_contra hc
    rcases nz_of_mem hg hc with h' | h'
    · exact h h'.symm
    · exact hΦ.1 _ (hΦ.2 _ _ _ h' hrt)
  have hirr : ∀ i, (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t i = 0 := by
    intro i
    by_contra hc
    have h1 := nz_of_mem hg (left_ne_zero_of_mul hc)
    have h2 := nz_of_mem hgi (right_ne_zero_of_mul hc)
    have hΦrr : Φ r r ∨ r = t := by
      rcases h1 with rfl | h1 <;> rcases h2 with h2 | h2
      · exact Or.inr h2.symm
      · exact Or.inl (hΦ.2 _ _ _ hrt h2)
      · subst h2; exact Or.inl (hΦ.2 _ _ _ hrt h1)
      · exact Or.inl (hΦ.2 _ _ _ hrt (hΦ.2 _ _ _ h2 h1))
    rcases hΦrr with h3 | h3
    · exact hΦ.1 _ h3
    · exact h h3
  constructor
  · intro i j
    constructor
    · intro hij
      subst hij
      have hh : ¬ (i = r ∧ i = t) := fun h' => h (h'.1.symm.trans h'.2)
      rw [comm_entry g r t h s htr, if_neg hh, mul_assoc, hirr]
      simp
    · intro hij hn
      rw [comm_entry g r t h s htr]
      by_cases hrt' : i = r ∧ j = t
      · obtain ⟨rfl, rfl⟩ := hrt'
        rw [(hg i i).1 rfl, (hgi j j).1 rfl]
        simp [Matrix.one_apply, hij]
      · have hz : (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j = 0 := by
          by_contra hc
          exact hn (hΨ i j (nz_of_mem hg (left_ne_zero_of_mul hc))
            (nz_of_mem hgi (right_ne_zero_of_mul hc)) hrt')
        rw [if_neg hrt', mul_assoc, hz]
        simp [Matrix.one_apply, hij]
  · unfold patChar
    congr 1
    have hterm : ∀ i j, E i j * ((tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ : GL ι K) : Matrix ι ι K) i j =
        if i = p ∧ j = q then
          -(s * E p q * (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q) else 0 := by
      intro i j
      by_cases hE : E i j = 0
      · rw [hE, zero_mul]
        split_ifs with hpq
        · obtain ⟨rfl, rfl⟩ := hpq
          rw [hE]; simp
        · rfl
      · have hΦij := hsupp i j hE
        have hij : i ≠ j := fun h' => hΦ.1 j (h' ▸ hΦij)
        have hrt' : ¬ (i = r ∧ j = t) := by
          rintro ⟨rfl, rfl⟩
          exact hE hErt
        rw [comm_entry g r t h s htr, if_neg hrt']
        by_cases hz : (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j = 0
        · split_ifs with hpq
          · obtain ⟨rfl, rfl⟩ := hpq
            have : s * E i j * (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j =
              s * E i j * ((g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j) := by ring
            rw [this, hz, mul_assoc, hz]
            simp [Matrix.one_apply, hij]
          · rw [mul_assoc, hz]
            simp [Matrix.one_apply, hij]
        · have h1 := nz_of_mem hg (left_ne_zero_of_mul hz)
          have h2 := nz_of_mem hgi (right_ne_zero_of_mul hz)
          have hpq : i = p ∧ j = q := by
            rcases h1 with h1 | h1
            · rcases h2 with h2 | h2
              · exact absurd ⟨h1, h2.symm⟩ hrt'
              · subst h1; exact hcomp _ _ _ hrt h2 hE
            · rcases h2 with h2 | h2
              · subst h2; exact hcomp _ _ _ h1 hrt hE
              · exact hcomp _ _ _ h1 (hΦ.2 _ _ _ hrt h2) hE
          obtain ⟨rfl, rfl⟩ := hpq
          rw [if_pos ⟨rfl, rfl⟩]
          simp only [Matrix.one_apply, if_neg hij]
          ring
    simp only [hterm]
    by_cases hp : True
    · rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
      · simp
      · intro b _ hb; simp [hb]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · exact absurd trivial hp

/- English proof (translation)
Establish `hrne : r ≠ t` using `fun h' => hΦ.1 t (h' ▸ hrt)`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, ψ₀ a ≠ 1 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hψ (by ext x; simpa using hc x)`.

Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s : K, -(s * E p q * (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q) = a := by`. Use `⟨-a / (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)), ?_⟩` and prove the remaining obligations. Establish `h0` using `mul_ne_zero hEpq hne`. Establish `h3 : -a / (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)) * E p q * (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q = -a / (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)) * (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : G …` using `by ring`. Rewrite using `[h3, div_mul_cancel₀ _ h0, neg_neg]`.

Take `⟨h1, h2⟩` from `comm_data ψ₀ hΦ hsupp p q r t hcomp g hg hgi hrt hΨ hErt hrne s`. Use `⟨tv r t hrne s, tv_mem r t hrne s hΨrt, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, hs]`. Conclude with `ha`.
-/
theorem exists_twist {Φ Ψ : ι → ι → Prop} {E : ι → ι → K} (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (hΦ : IsPat Φ)
    (hsupp : ∀ i j, E i j ≠ 0 → Φ i j) (p q r t : ι)
    (hcomp : ∀ i j k, Φ i j → Φ j k → E i k ≠ 0 → i = p ∧ k = q)
    (g : GL ι K) (hg : g ∈ patSet K Φ) (hgi : g⁻¹ ∈ patSet K Φ) (hrt : Φ r t) (hΨrt : Ψ r t)
    (hΨ : ∀ i j, (i = r ∨ Φ i r) → (t = j ∨ Φ t j) → ¬ (i = r ∧ j = t) → Ψ i j)
    (hErt : E r t = 0) (hEpq : E p q ≠ 0)
    (hne : (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q ≠ 0) :
    ∃ h ∈ patSet K Ψ, h * g * h⁻¹ * g⁻¹ ∈ patSet K Ψ ∧ patChar E ψ₀ (h * g * h⁻¹ * g⁻¹) ≠ 1 := by
  have hrne : r ≠ t := fun h' => hΦ.1 t (h' ▸ hrt)
  obtain ⟨a, ha⟩ : ∃ a, ψ₀ a ≠ 1 := by
    by_contra hc
    push_neg at hc
    exact hψ (by ext x; simpa using hc x)
  obtain ⟨s, hs⟩ : ∃ s : K, -(s * E p q * (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q) = a := by
    refine ⟨-a / (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)), ?_⟩
    have h0 := mul_ne_zero hEpq hne
    have h3 : -a / (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)) * E p q *
        (g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q =
        -a / (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)) *
          (E p q * ((g : Matrix ι ι K) p r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t q)) := by ring
    rw [h3, div_mul_cancel₀ _ h0, neg_neg]
  obtain ⟨h1, h2⟩ := comm_data ψ₀ hΦ hsupp p q r t hcomp g hg hgi hrt hΨ hErt hrne s
  refine ⟨tv r t hrne s, tv_mem r t hrne s hΨrt, h1, ?_⟩
  rw [h2, hs]
  exact ha

end Mat

end GlobalTheory.CompanionTheory.RootExch

namespace GlobalTheory.CompanionTheory.RootExch

/- English proof (translation)
Set `R : Finset (ι × ι)` to `Finset.univ.filter fun x => Φ x.1 x.2`. Set `Wf : Finset ι` to `Finset.univ.filter W`. Set `A : Finset (ι × ι)` to `Wf.image fun w => (w, q)`. Set `B : Finset (ι × ι)` to `Wf.image fun w => (p, w)`. Establish `hA : A ⊆ R`.

Introduce `x hx`. Take `⟨w, hw, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `Finset.mem_filter.2 ⟨Finset.mem_univ _, (h1 w (Finset.mem_filter.1 hw).2).2⟩`. Establish `hB : B ⊆ R`. Introduce `x hx`.

Take `⟨w, hw, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `Finset.mem_filter.2 ⟨Finset.mem_univ _, (h1 w (Finset.mem_filter.1 hw).2).1⟩`. Establish `cA : A.card = Wf.card` using `Finset.card_image_of_injective _ fun a b h => (Prod.ext_iff.1 h).1`. Establish `cB : B.card = Wf.card` using `Finset.card_image_of_injective _ fun a b h => (Prod.ext_iff.1 h).2`. Establish `c1 : Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (W x.1 ∧ x.2 = q)} = (R \ A).card`.

Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 1`. Use extensionality with `⟨a, b⟩`. Simplify using `only [R, A, Wf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_image, Prod.mk.injEq, not_exists, not_and]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h, h'⟩`. Conclude with `⟨h, fun w hw hwa hq => h' (hwa ▸ hw) hq.symm⟩`. Introduce and unpack `⟨h, h'⟩`. Conclude with `⟨h, fun hW hb => h' a hW rfl hb.symm⟩`. Establish `c2 : Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (x.1 = p ∧ W x.2)} = (R \ B).card`.

Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 1`. Use extensionality with `⟨a, b⟩`. Simplify using `only [R, B, Wf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_image, Prod.mk.injEq, not_exists, not_and]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h, h'⟩`. Conclude with `⟨h, fun w hw hp hwb => h' hp.symm (hwb ▸ hw)⟩`. Introduce and unpack `⟨h, h'⟩`. Conclude with `⟨h, fun hp hW => h' b hW hp.symm rfl⟩`. Establish `s1` using `Finset.card_sdiff_add_card_eq_card hA`.

Establish `s2` using `Finset.card_sdiff_add_card_eq_card hB`. Rewrite using `[c1, c2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_pairs {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) (W : ι → Prop) (p q : ι)
    (h1 : ∀ w, W w → Φ p w ∧ Φ w q) :
    Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (W x.1 ∧ x.2 = q)} =
      Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (x.1 = p ∧ W x.2)} := by
  classical
  let R : Finset (ι × ι) := Finset.univ.filter fun x => Φ x.1 x.2
  let Wf : Finset ι := Finset.univ.filter W
  let A : Finset (ι × ι) := Wf.image fun w => (w, q)
  let B : Finset (ι × ι) := Wf.image fun w => (p, w)
  have hA : A ⊆ R := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (h1 w (Finset.mem_filter.1 hw).2).2⟩
  have hB : B ⊆ R := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (h1 w (Finset.mem_filter.1 hw).2).1⟩
  have cA : A.card = Wf.card := Finset.card_image_of_injective _ fun a b h => (Prod.ext_iff.1 h).1
  have cB : B.card = Wf.card := Finset.card_image_of_injective _ fun a b h => (Prod.ext_iff.1 h).2
  have c1 : Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (W x.1 ∧ x.2 = q)} = (R \ A).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext ⟨a, b⟩
    simp only [R, A, Wf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_image,
      Prod.mk.injEq, not_exists, not_and]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h, fun w hw hwa hq => h' (hwa ▸ hw) hq.symm⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, fun hW hb => h' a hW rfl hb.symm⟩
  have c2 : Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (x.1 = p ∧ W x.2)} = (R \ B).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext ⟨a, b⟩
    simp only [R, B, Wf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_image,
      Prod.mk.injEq, not_exists, not_and]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h, fun w hw hp hwb => h' hp.symm (hwb ▸ hw)⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, fun hp hW => h' b hW hp.symm rfl⟩
  have s1 := Finset.card_sdiff_add_card_eq_card hA
  have s2 := Finset.card_sdiff_add_card_eq_card hB
  rw [c1, c2]
  omega

/- English proof (translation)
Introduce `K _ _ _ ι _ _ Φ E ψ₀ W p q χ hΦ hψ hχ h1 hEpq hsupp hEW hc1 hc2 hcomp`. Establish `hcomp' : ∀ i j k, Φ i j → Φ j k → E i k ≠ 0 → i = p ∧ k = q` using `fun i j k a b c => ⟨(hcomp i j k a b c).1, (hcomp i j k a b c).2.1⟩`. Establish `pat1 : IsPat (fun i j => Φ i j ∧ ¬ (W i ∧ j = q))`. Use `⟨fun i h => hΦ.1 i h.1, fun i j k hij hjk => ⟨hΦ.2 _ _ _ hij.1 hjk.1, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨hWi, rfl⟩`.

Conclude with `hjk.2 ⟨hc1 i j hWi hij.1 hjk.1, rfl⟩`. Establish `pat2 : IsPat (fun i j => Φ i j ∧ ¬ (i = p ∧ W j))`. Use `⟨fun i h => hΦ.1 i h.1, fun i j k hij hjk => ⟨hΦ.2 _ _ _ hij.1 hjk.1, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨rfl, hWk⟩`. Conclude with `hij.2 ⟨rfl, hc2 k j hWk hij.1 hjk.1⟩`.

Establish `char1 : IsPatChar (fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) E`. Use `⟨fun i j hE => ⟨hsupp i j hE, ?_⟩, fun i j k hij hjk => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨hW, rfl⟩`. Conclude with `hE (hEW i hW).2`. Assume the negation of the conclusion as `hE`.

Take `⟨_, hk, hWj⟩` from `hcomp i j k hij.1 hjk.1 hE`. Conclude with `hjk.2 ⟨hWj, hk⟩`. Establish `char2 : IsPatChar (fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) E`. Use `⟨fun i j hE => ⟨hsupp i j hE, ?_⟩, fun i j k hij hjk => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨rfl, hW⟩`.

Conclude with `hE (hEW j hW).1`. Assume the negation of the conclusion as `hE`. Take `⟨hi, _, hWj⟩` from `hcomp i j k hij.1 hjk.1 hE`. Conclude with `hij.2 ⟨hi, hWj⟩`. Take `⟨⟨P, hP⟩, cardP, hcharP⟩` from `GlobalTheory.CompanionTheory.PatGrp.patGroup K ι _ pat1`.

Take `⟨⟨Q, hQ⟩, cardQ, hcharQ⟩` from `GlobalTheory.CompanionTheory.PatGrp.patGroup K ι _ pat2`. Establish `mulP` using `(hcharP E ψ₀ char1).1`. Establish `mulQ` using `(hcharQ E ψ₀ char2).1`. Establish `memP : ∀ u, u ∈ P ↔ u ∈ patSet K (fun i j => Φ i j ∧ ¬ (W i ∧ j = q))` using `fun u => by`. Rewrite using `[← hP]`.

Both sides reduce to the same expression. Establish `memQ : ∀ u, u ∈ Q ↔ u ∈ patSet K (fun i j => Φ i j ∧ ¬ (i = p ∧ W j))` using `fun u => by`. Rewrite using `[← hQ]`. Both sides reduce to the same expression. Establish `hne : ∀ u : GL ι K, patChar E ψ₀ u ≠ 0` using `fun u => (ψ₀.val_isUnit _).ne_zero`.

Establish `hsum` using `exchange P Q (patChar E ψ₀) χ hχ (fun a ha b hb => mulP a ((memP a).1 ha) b ((memP b).1 hb)) (fun a _ => hne a) (fun a ha b hb => mulQ a ((memQ a).1 ha) b ((memQ b).1 hb)) (fun a _ => hne a) (by`. Introduce `v hvQ hvP`. Establish `vQ` using `(memQ v).1 hvQ`. Establish `viQ` using `(memQ _).1 (Q.inv_mem hvQ)`. Establish `viP : v⁻¹ ∉ patSet K (fun i j => Φ i j ∧ ¬ (W i ∧ j = q))` using `fun h => hvP (by simpa using P.inv_mem ((memP _).2 h))`.

Choose the witnesses or unpack the hypotheses as in `⟨w, hw, hnz⟩ : ∃ w, W w ∧ ((v⁻¹ : GL ι K) : Matrix ι ι K) w q ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `viP` to reduce the goal to its premises. Introduce `i j`.

Use `⟨(viQ i j).1, fun hij hn => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hx`. Break down `nz_of_mem viQ hx with h | h` into its components or cases. Conclude with `hij h`. Establish `h3 : W i ∧ j = q`.

Assume the negation of the conclusion as `h'`. Conclude with `hn ⟨h.1, h'⟩`. Take `⟨hWi, rfl⟩` from `h3`. Conclude with `hx (hc i hWi)`. Take `⟨h, hh, hc, hl⟩` from `exists_twist (Ψ := fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) ψ₀ hψ hΦ hsupp p q p w hcomp' v (patSet_mono (fun _ _ h => h.1) vQ) (patSet_mono (fun _ _ h => h.1) viQ) (h1 w hw).1 ⟨(h1 w hw).1, fun hh => hΦ.1 p (h1 p hh.1).1⟩ (by`.

Introduce `i j hi hj hn`. Use `⟨?_, fun hh => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rcases hi with rfl | hi <;> rcases hj with rfl | hj`. Conclude with `absurd ⟨rfl, rfl⟩ hn`. Conclude with `hΦ.2 _ _ _ (h1 w hw).1 hj`.

Conclude with `hΦ.2 _ _ _ hi (h1 _ hw).1`. Conclude with `hΦ.2 _ _ _ hi (hΦ.2 _ _ _ (h1 w hw).1 hj)`. Break down `hi with rfl | hi` into its components or cases. Conclude with `hΦ.1 _ (h1 _ hh.1).1`. Conclude with `hΦ.1 _ (hΦ.2 _ _ _ hi (h1 _ hh.1).1))`.

Use the proof step `(hEW w hw).1 hEpq`. Use the proof step `(by rw [(vQ p p).1 rfl, one_mul]; exact hnz)`. Conclude with `⟨h, (memP _).2 hh, (memP _).2 hc, hl⟩)`. Use the proof step `(by`. Introduce `v hvP hvQ`.

Establish `vP` using `(memP v).1 hvP`. Establish `viP` using `(memP _).1 (P.inv_mem hvP)`. Establish `vQ' : v ∉ patSet K (fun i j => Φ i j ∧ ¬ (i = p ∧ W j))` using `fun h => hvQ ((memQ v).2 h)`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw, hnz⟩ : ∃ w, W w ∧ (v : Matrix ι ι K) p w ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Apply `vQ'` to reduce the goal to its premises. Introduce `i j`. Use `⟨(vP i j).1, fun hij hn => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hx`.

Break down `nz_of_mem vP hx with h | h` into its components or cases. Conclude with `hij h`. Establish `h3 : i = p ∧ W j`. Assume the negation of the conclusion as `h'`. Conclude with `hn ⟨h.1, h'⟩`.

Take `⟨rfl, hWj⟩` from `h3`. Conclude with `hx (hc j hWj)`. Take `⟨h, hh, hc, hl⟩` from `exists_twist (Ψ := fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) ψ₀ hψ hΦ hsupp p q w q hcomp' v (patSet_mono (fun _ _ h => h.1) vP) (patSet_mono (fun _ _ h => h.1) viP) (h1 w hw).2 ⟨(h1 w hw).2, fun hh => hΦ.1 q (h1 q hh.2).2⟩ (by`. Introduce `i j hi hj hn`. Use `⟨?_, fun hh => ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `rcases hi with rfl | hi <;> rcases hj with rfl | hj`. Conclude with `absurd ⟨rfl, rfl⟩ hn`. Conclude with `hΦ.2 _ _ _ (h1 _ hw).2 hj`. Conclude with `hΦ.2 _ _ _ hi (h1 w hw).2`. Conclude with `hΦ.2 _ _ _ hi (hΦ.2 _ _ _ (h1 w hw).2 hj)`.

Break down `hj with rfl | hj` into its components or cases. Conclude with `hΦ.1 _ (h1 _ hh.2).2`. Conclude with `hΦ.1 _ (hΦ.2 _ _ _ hj (h1 _ hh.2).2))`. Use the proof step `(hEW w hw).2 hEpq`. Use the proof step `(by rw [(viP q q).1 rfl, mul_one]; exact hnz)`.

Conclude with `⟨h, (memQ _).2 hh, (memQ _).2 hc, hl⟩)`. Establish `hcard : (patSet K (fun i j => Φ i j ∧ ¬ (W i ∧ j = q))).ncard = (patSet K (fun i j => Φ i j ∧ ¬ (i = p ∧ W j))).ncard`. Rewrite using `[cardP, cardQ]`. Use `congr 1`. Conclude with `card_pairs Φ W p q h1`.

Unfold `wh`. Rewrite using `[hcard]`. Use `congr 1`. Use `(Finset.sum_congr rfl fun u _ => ?_).trans (hsum.trans (Finset.sum_congr rfl fun u _ => ?_))` and prove the remaining obligations. Distinguish the cases in `h : u ∈ P`.

Rewrite using `[if_pos h, if_pos ((memP u).1 h)]`. Rewrite using `[if_neg h, if_neg (fun h' => h ((memP u).2 h'))]`. Distinguish the cases in `h : u ∈ Q`. Rewrite using `[if_pos h, if_pos ((memQ u).1 h)]`. Rewrite using `[if_neg h, if_neg (fun h' => h ((memQ u).2 h'))]`.
-/
theorem rootExchange : ReciprocityTheory.Ty.Fin.St.RootExchange := by
  intro K _ _ _ ι _ _ Φ E ψ₀ W p q χ hΦ hψ hχ h1 hEpq hsupp hEW hc1 hc2 hcomp
  have hcomp' : ∀ i j k, Φ i j → Φ j k → E i k ≠ 0 → i = p ∧ k = q :=
    fun i j k a b c => ⟨(hcomp i j k a b c).1, (hcomp i j k a b c).2.1⟩
  have pat1 : IsPat (fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) := by
    refine ⟨fun i h => hΦ.1 i h.1, fun i j k hij hjk => ⟨hΦ.2 _ _ _ hij.1 hjk.1, ?_⟩⟩
    rintro ⟨hWi, rfl⟩
    exact hjk.2 ⟨hc1 i j hWi hij.1 hjk.1, rfl⟩
  have pat2 : IsPat (fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) := by
    refine ⟨fun i h => hΦ.1 i h.1, fun i j k hij hjk => ⟨hΦ.2 _ _ _ hij.1 hjk.1, ?_⟩⟩
    rintro ⟨rfl, hWk⟩
    exact hij.2 ⟨rfl, hc2 k j hWk hij.1 hjk.1⟩
  have char1 : IsPatChar (fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) E := by
    refine ⟨fun i j hE => ⟨hsupp i j hE, ?_⟩, fun i j k hij hjk => ?_⟩
    · rintro ⟨hW, rfl⟩
      exact hE (hEW i hW).2
    · by_contra hE
      obtain ⟨_, hk, hWj⟩ := hcomp i j k hij.1 hjk.1 hE
      exact hjk.2 ⟨hWj, hk⟩
  have char2 : IsPatChar (fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) E := by
    refine ⟨fun i j hE => ⟨hsupp i j hE, ?_⟩, fun i j k hij hjk => ?_⟩
    · rintro ⟨rfl, hW⟩
      exact hE (hEW j hW).1
    · by_contra hE
      obtain ⟨hi, _, hWj⟩ := hcomp i j k hij.1 hjk.1 hE
      exact hij.2 ⟨hi, hWj⟩
  obtain ⟨⟨P, hP⟩, cardP, hcharP⟩ := GlobalTheory.CompanionTheory.PatGrp.patGroup K ι _ pat1
  obtain ⟨⟨Q, hQ⟩, cardQ, hcharQ⟩ := GlobalTheory.CompanionTheory.PatGrp.patGroup K ι _ pat2
  have mulP := (hcharP E ψ₀ char1).1
  have mulQ := (hcharQ E ψ₀ char2).1
  have memP : ∀ u, u ∈ P ↔ u ∈ patSet K (fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) := fun u => by
    rw [← hP]; rfl
  have memQ : ∀ u, u ∈ Q ↔ u ∈ patSet K (fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) := fun u => by
    rw [← hQ]; rfl
  have hne : ∀ u : GL ι K, patChar E ψ₀ u ≠ 0 := fun u => (ψ₀.val_isUnit _).ne_zero
  have hsum := exchange P Q (patChar E ψ₀) χ hχ
    (fun a ha b hb => mulP a ((memP a).1 ha) b ((memP b).1 hb)) (fun a _ => hne a)
    (fun a ha b hb => mulQ a ((memQ a).1 ha) b ((memQ b).1 hb)) (fun a _ => hne a)
    (by
      intro v hvQ hvP
      have vQ := (memQ v).1 hvQ
      have viQ := (memQ _).1 (Q.inv_mem hvQ)
      have viP : v⁻¹ ∉ patSet K (fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) := fun h =>
        hvP (by simpa using P.inv_mem ((memP _).2 h))
      obtain ⟨w, hw, hnz⟩ : ∃ w, W w ∧ ((v⁻¹ : GL ι K) : Matrix ι ι K) w q ≠ 0 := by
        by_contra hc
        push_neg at hc
        apply viP
        intro i j
        refine ⟨(viQ i j).1, fun hij hn => ?_⟩
        by_contra hx
        rcases nz_of_mem viQ hx with h | h
        · exact hij h
        · have h3 : W i ∧ j = q := by
            by_contra h'
            exact hn ⟨h.1, h'⟩
          obtain ⟨hWi, rfl⟩ := h3
          exact hx (hc i hWi)
      obtain ⟨h, hh, hc, hl⟩ := exists_twist (Ψ := fun i j => Φ i j ∧ ¬ (W i ∧ j = q)) ψ₀ hψ hΦ hsupp p q p w hcomp' v
        (patSet_mono (fun _ _ h => h.1) vQ) (patSet_mono (fun _ _ h => h.1) viQ) (h1 w hw).1
        ⟨(h1 w hw).1, fun hh => hΦ.1 p (h1 p hh.1).1⟩
        (by
          intro i j hi hj hn
          refine ⟨?_, fun hh => ?_⟩
          · rcases hi with rfl | hi <;> rcases hj with rfl | hj
            · exact absurd ⟨rfl, rfl⟩ hn
            · exact hΦ.2 _ _ _ (h1 w hw).1 hj
            · exact hΦ.2 _ _ _ hi (h1 _ hw).1
            · exact hΦ.2 _ _ _ hi (hΦ.2 _ _ _ (h1 w hw).1 hj)
          · rcases hi with rfl | hi
            · exact hΦ.1 _ (h1 _ hh.1).1
            · exact hΦ.1 _ (hΦ.2 _ _ _ hi (h1 _ hh.1).1))
        (hEW w hw).1 hEpq
        (by rw [(vQ p p).1 rfl, one_mul]; exact hnz)
      exact ⟨h, (memP _).2 hh, (memP _).2 hc, hl⟩)
    (by
      intro v hvP hvQ
      have vP := (memP v).1 hvP
      have viP := (memP _).1 (P.inv_mem hvP)
      have vQ' : v ∉ patSet K (fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) := fun h => hvQ ((memQ v).2 h)
      obtain ⟨w, hw, hnz⟩ : ∃ w, W w ∧ (v : Matrix ι ι K) p w ≠ 0 := by
        by_contra hc
        push_neg at hc
        apply vQ'
        intro i j
        refine ⟨(vP i j).1, fun hij hn => ?_⟩
        by_contra hx
        rcases nz_of_mem vP hx with h | h
        · exact hij h
        · have h3 : i = p ∧ W j := by
            by_contra h'
            exact hn ⟨h.1, h'⟩
          obtain ⟨rfl, hWj⟩ := h3
          exact hx (hc j hWj)
      obtain ⟨h, hh, hc, hl⟩ := exists_twist (Ψ := fun i j => Φ i j ∧ ¬ (i = p ∧ W j)) ψ₀ hψ hΦ hsupp p q w q hcomp' v
        (patSet_mono (fun _ _ h => h.1) vP) (patSet_mono (fun _ _ h => h.1) viP) (h1 w hw).2
        ⟨(h1 w hw).2, fun hh => hΦ.1 q (h1 q hh.2).2⟩
        (by
          intro i j hi hj hn
          refine ⟨?_, fun hh => ?_⟩
          · rcases hi with rfl | hi <;> rcases hj with rfl | hj
            · exact absurd ⟨rfl, rfl⟩ hn
            · exact hΦ.2 _ _ _ (h1 _ hw).2 hj
            · exact hΦ.2 _ _ _ hi (h1 w hw).2
            · exact hΦ.2 _ _ _ hi (hΦ.2 _ _ _ (h1 w hw).2 hj)
          · rcases hj with rfl | hj
            · exact hΦ.1 _ (h1 _ hh.2).2
            · exact hΦ.1 _ (hΦ.2 _ _ _ hj (h1 _ hh.2).2))
        (hEW w hw).2 hEpq
        (by rw [(viP q q).1 rfl, mul_one]; exact hnz)
      exact ⟨h, (memQ _).2 hh, (memQ _).2 hc, hl⟩)
  have hcard : (patSet K (fun i j => Φ i j ∧ ¬ (W i ∧ j = q))).ncard =
      (patSet K (fun i j => Φ i j ∧ ¬ (i = p ∧ W j))).ncard := by
    rw [cardP, cardQ]
    congr 1
    exact card_pairs Φ W p q h1
  unfold wh
  rw [hcard]
  congr 1
  refine (Finset.sum_congr rfl fun u _ => ?_).trans (hsum.trans (Finset.sum_congr rfl fun u _ => ?_))
  · by_cases h : u ∈ P
    · rw [if_pos h, if_pos ((memP u).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((memP u).2 h'))]
  · by_cases h : u ∈ Q
    · rw [if_pos h, if_pos ((memQ u).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((memQ u).2 h'))]

end GlobalTheory.CompanionTheory.RootExch

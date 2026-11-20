import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FourModel

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.IndefR.Fin.Four

variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]

section SB

variable {L X : AddSubgroup W}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun t h => absurd rfl h, 1, one_pos, fun _ _ _ => rfl, fun t h => absurd rfl h⟩`.
-/
theorem isSB_zero : IsSB L X (0 : W → ℂ) :=
  ⟨fun t h => absurd rfl h, 1, one_pos, fun _ _ _ => rfl, fun t h => absurd rfl h⟩

/- English proof (translation)
Take `⟨hs, k, hk, hi, hl⟩` from `h`. Take `⟨hs', k', hk', hi', hl'⟩` from `h'`. Establish `hor : ∀ t, (Φ + Φ') t ≠ 0 → Φ t ≠ 0 ∨ Φ' t ≠ 0`. Introduce `t ht`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Apply `ht` to reduce the goal to its premises. Simplify using `[hc.1, hc.2]`. Use `⟨fun t ht => (hor t ht).elim (hs t) (hs' t), k * k', Nat.mul_pos hk hk', fun u hu t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Establish `h1 : (k * k') • u = k • (k' • u)` using `(smul_smul k k' u).symm`.

Establish `h2 : (k * k') • u = k' • (k • u)` using `by rw [mul_comm]; exact (smul_smul k' k u).symm`. Simplify using `only [Pi.add_apply]`. Use `congr 1`. Rewrite using `[h1]`. Conclude with `hi _ ((L ⊓ X).nsmul_mem hu k') t`.

Rewrite using `[h2]`. Conclude with `hi' _ ((L ⊓ X).nsmul_mem hu k) t`. Break down `hor t ht with h0 | h0` into its components or cases. Rewrite using `[mul_comm, ← smul_smul]`. Conclude with `L.nsmul_mem (hl t h0) k'`.

Rewrite using `[← smul_smul]`. Conclude with `L.nsmul_mem (hl' t h0) k`.
-/
theorem IsSB.add {Φ Φ' : W → ℂ} (h : IsSB L X Φ) (h' : IsSB L X Φ') : IsSB L X (Φ + Φ') := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  obtain ⟨hs', k', hk', hi', hl'⟩ := h'
  have hor : ∀ t, (Φ + Φ') t ≠ 0 → Φ t ≠ 0 ∨ Φ' t ≠ 0 := by
    intro t ht
    by_contra hc
    push_neg at hc
    apply ht
    simp [hc.1, hc.2]
  refine ⟨fun t ht => (hor t ht).elim (hs t) (hs' t), k * k', Nat.mul_pos hk hk', fun u hu t => ?_,
    fun t ht => ?_⟩
  · have h1 : (k * k') • u = k • (k' • u) := (smul_smul k k' u).symm
    have h2 : (k * k') • u = k' • (k • u) := by rw [mul_comm]; exact (smul_smul k' k u).symm
    simp only [Pi.add_apply]
    congr 1
    · rw [h1]; exact hi _ ((L ⊓ X).nsmul_mem hu k') t
    · rw [h2]; exact hi' _ ((L ⊓ X).nsmul_mem hu k) t
  · rcases hor t ht with h0 | h0
    · rw [mul_comm, ← smul_smul]; exact L.nsmul_mem (hl t h0) k'
    · rw [← smul_smul]; exact L.nsmul_mem (hl' t h0) k

/- English proof (translation)
Take `⟨hs, k, hk, hi, hl⟩` from `h`. Establish `hne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0` using `fun t ht h0 => ht (by simp [h0])`. Conclude with `⟨fun t ht => hs t (hne t ht), k, hk, fun u hu t => by simp [hi u hu t], fun t ht => hl t (hne t ht)⟩`.
-/
theorem IsSB.smul {Φ : W → ℂ} (h : IsSB L X Φ) (c : ℂ) : IsSB L X (c • Φ) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  have hne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by simp [h0])
  exact ⟨fun t ht => hs t (hne t ht), k, hk, fun u hu t => by simp [hi u hu t],
    fun t ht => hl t (hne t ht)⟩

/- English proof (translation)
Take `⟨hs, k, hk, hi, hl⟩` from `h`. Take `⟨k2, hk2, hx2⟩` from `hoX x hx`. Use `⟨fun t ht => ?_, k * k2, Nat.mul_pos hk hk2, fun u hu t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Establish `h1` using `hs _ ht`. Simplify using `using X.sub_mem h1 hx`.

Use `show Φ (t + (k * k2) • u + x) = Φ (t + x)`. Rewrite using `[← smul_smul, add_right_comm]`. Conclude with `hi _ ((L ⊓ X).nsmul_mem hu k2) _`. Establish `h1` using `hl _ ht`. Establish `h2 : (k * k2) • t = k2 • (k • (t + x)) - k • (k2 • x)`.

Simplify using `only [smul_add, smul_smul]`. Rewrite using `[mul_comm k2 k]`. Normalize the expressions using the abelian group laws. Rewrite using `[h2]`. Conclude with `L.sub_mem (L.nsmul_mem h1 k2) (L.nsmul_mem hx2 k)`.
-/
theorem IsSB.trans (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) {Φ : W → ℂ} (h : IsSB L X Φ) {x : W}
    (hx : x ∈ X) : IsSB L X (fun t => Φ (t + x)) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  obtain ⟨k2, hk2, hx2⟩ := hoX x hx
  refine ⟨fun t ht => ?_, k * k2, Nat.mul_pos hk hk2, fun u hu t => ?_, fun t ht => ?_⟩
  · have h1 := hs _ ht
    simpa using X.sub_mem h1 hx
  · show Φ (t + (k * k2) • u + x) = Φ (t + x)
    rw [← smul_smul, add_right_comm]
    exact hi _ ((L ⊓ X).nsmul_mem hu k2) _
  · have h1 := hl _ ht
    have h2 : (k * k2) • t = k2 • (k • (t + x)) - k • (k2 • x) := by
      simp only [smul_add, smul_smul]
      rw [mul_comm k2 k]
      abel
    rw [h2]
    exact L.sub_mem (L.nsmul_mem h1 k2) (L.nsmul_mem hx2 k)

/- English proof (translation)
Take `⟨hs, k, hk, hi, hl⟩` from `h`. Take `⟨k3, hk3, hy3⟩` from `hoY y hy`. Establish `h0 : ∀ b, χ 0 b = 1`. Introduce `b`. Establish `h1` using `hχl 0 0 b`.

Rewrite `h1` using `[add_zero]`. Conclude with `mul_left_cancel₀ (hχ0 0 b) (h1.symm.trans (mul_one _).symm)`. Establish `h0' : ∀ a, χ a 0 = 1`. Introduce `a`. Establish `h1` using `hχr a 0 0`.

Rewrite `h1` using `[add_zero]`. Conclude with `mul_left_cancel₀ (hχ0 a 0) (h1.symm.trans (mul_one _).symm)`. Establish `hpow : ∀ (n : ℕ) (a b : W), χ (n • a) b = χ a b ^ n`. Introduce `n a b`. Proceed by induction on `n with`.

Consider the case `zero => rw [zero_smul, pow_zero, h0]`. Consider the case `succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]`. Establish `hpow' : ∀ (n : ℕ) (a b : W), χ a (n • b) = χ a b ^ n`. Introduce `n a b`. Proceed by induction on `n with`.

Consider the case `zero => rw [zero_smul, pow_zero, h0']`. Consider the case `succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]`. Use `⟨fun t ht => hs t (fun h0t => ht (by show χ t y * Φ t = 0; rw [h0t, mul_zero])), k * k3, Nat.mul_pos hk hk3, fun u hu t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Use `show χ (t + (k * k3) • u) y * Φ (t + (k * k3) • u) = χ t y * Φ t`. Establish `hΦ : Φ (t + (k * k3) • u) = Φ t`.

Rewrite using `[← smul_smul]`. Conclude with `hi _ ((L ⊓ X).nsmul_mem hu k3) t`. Establish `hχu : χ ((k * k3) • u) y = 1`. Rewrite using `[hpow, mul_comm, pow_mul, ← hpow', hLL u hu (k3 • y) ⟨hy3, Y.nsmul_mem hy k3⟩, one_pow]`. Rewrite using `[hΦ, hχl, hχu, mul_one]`.

Establish `hΦt : Φ t ≠ 0` using `fun h0t => ht (by show χ t y * Φ t = 0; rw [h0t, mul_zero])`. Rewrite using `[mul_comm, ← smul_smul]`. Conclude with `L.nsmul_mem (hl t hΦt) k3`.
-/
theorem IsSB.modul {Y : AddSubgroup W} {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
    (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
    {Φ : W → ℂ} (h : IsSB L X Φ) {y : W} (hy : y ∈ Y) : IsSB L X (fun t => χ t y * Φ t) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  obtain ⟨k3, hk3, hy3⟩ := hoY y hy
  have h0 : ∀ b, χ 0 b = 1 := by
    intro b
    have h1 := hχl 0 0 b
    rw [add_zero] at h1
    exact mul_left_cancel₀ (hχ0 0 b) (h1.symm.trans (mul_one _).symm)
  have h0' : ∀ a, χ a 0 = 1 := by
    intro a
    have h1 := hχr a 0 0
    rw [add_zero] at h1
    exact mul_left_cancel₀ (hχ0 a 0) (h1.symm.trans (mul_one _).symm)
  have hpow : ∀ (n : ℕ) (a b : W), χ (n • a) b = χ a b ^ n := by
    intro n a b
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
  have hpow' : ∀ (n : ℕ) (a b : W), χ a (n • b) = χ a b ^ n := by
    intro n a b
    induction n with
    | zero => rw [zero_smul, pow_zero, h0']
    | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]
  refine ⟨fun t ht => hs t (fun h0t => ht (by show χ t y * Φ t = 0; rw [h0t, mul_zero])),
    k * k3, Nat.mul_pos hk hk3, fun u hu t => ?_, fun t ht => ?_⟩
  · show χ (t + (k * k3) • u) y * Φ (t + (k * k3) • u) = χ t y * Φ t
    have hΦ : Φ (t + (k * k3) • u) = Φ t := by
      rw [← smul_smul]; exact hi _ ((L ⊓ X).nsmul_mem hu k3) t
    have hχu : χ ((k * k3) • u) y = 1 := by
      rw [hpow, mul_comm, pow_mul, ← hpow', hLL u hu (k3 • y) ⟨hy3, Y.nsmul_mem hy k3⟩, one_pow]
    rw [hΦ, hχl, hχu, mul_one]
  · have hΦt : Φ t ≠ 0 := fun h0t => ht (by show χ t y * Φ t = 0; rw [h0t, mul_zero])
    rw [mul_comm, ← smul_smul]
    exact L.nsmul_mem (hl t hΦt) k3

open Classical in
/- English proof (translation)
Use `⟨fun t ht => ?_, 1, one_pos, fun u hu t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Apply `ht` to reduce the goal to its premises. Simplify using `[h]`. Simplify using `only [one_smul, L.add_mem_cancel_right hu.1, X.add_mem_cancel_right hu.2]`.

Rewrite using `[one_smul]`. Assume the negation of the conclusion as `h`. Apply `ht` to reduce the goal to its premises. Simplify using `[h]`.
-/
theorem isSB_ind : IsSB L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) := by
  refine ⟨fun t ht => ?_, 1, one_pos, fun u hu t => ?_, fun t ht => ?_⟩
  · by_contra h
    apply ht
    simp [h]
  · simp only [one_smul, L.add_mem_cancel_right hu.1, X.add_mem_cancel_right hu.2]
  · rw [one_smul]
    by_contra h
    apply ht
    simp [h]

/- English proof (translation)
Use `Set.Finite.of_finite_image (f := fun q : W ⧸ H => if hq : k • q.out ∈ H then (QuotientAddGroup.mk (⟨k • q.out, hq⟩ : H) : Qt k H) else 0) (Set.toFinite _) ?_` and prove the remaining obligations. Introduce `q hq q' hq' heq`. Establish `hq1 : k • q.out ∈ H` using `hq`. Establish `hq2 : k • q'.out ∈ H` using `hq'`. Simplify using `only [dif_pos hq1, dif_pos hq2] at heq`.

Rewrite `heq` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Simplify using `only [smulSub, AddSubgroup.mem_map] at heq`. Take `⟨h, hh, hh'⟩` from `heq`. Simplify using `only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg] at hh'`. Establish `hkey : k • (-q.out + q'.out - h) = 0`.

Rewrite using `[smul_sub, smul_add, smul_neg, hh']`. Normalize the expressions using the abelian group laws. Establish `h3` using `htf _ hkey`. Rewrite using `[← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]`. Establish `h4 : -q.out + q'.out = h` using `sub_eq_zero.1 h3`.

Rewrite using `[h4]`. Conclude with `hh`.
-/
theorem finite_nsmul_out (H : AddSubgroup W) {k : ℕ} [Finite (Qt k H)]
    (htf : ∀ t : W, k • t = 0 → t = 0) : {q : W ⧸ H | k • q.out ∈ H}.Finite := by
  classical
  refine Set.Finite.of_finite_image (f := fun q : W ⧸ H => if hq : k • q.out ∈ H then
      (QuotientAddGroup.mk (⟨k • q.out, hq⟩ : H) : Qt k H) else 0) (Set.toFinite _) ?_
  intro q hq q' hq' heq
  have hq1 : k • q.out ∈ H := hq
  have hq2 : k • q'.out ∈ H := hq'
  simp only [dif_pos hq1, dif_pos hq2] at heq
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at heq
  simp only [smulSub, AddSubgroup.mem_map] at heq
  obtain ⟨h, hh, hh'⟩ := heq
  simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg] at hh'
  have hkey : k • (-q.out + q'.out - h) = 0 := by
    rw [smul_sub, smul_add, smul_neg, hh']
    abel
  have h3 := htf _ hkey
  rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
  have h4 : -q.out + q'.out = h := sub_eq_zero.1 h3
  rw [h4]
  exact hh

end SB

section Main

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
  (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
  (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀) (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀)

include hχl hχr hχ0 hLL hoY in
/- English proof (translation)
Take `⟨hs, k, hk, hi, hl⟩` from `h`. Take `⟨k3, hk3, hy3⟩` from `hoY y hy`. Establish `h0 : ∀ b, χ 0 b = 1`. Introduce `b`. Establish `h1` using `hχl 0 0 b`.

Rewrite `h1` using `[add_zero]`. Conclude with `mul_left_cancel₀ (hχ0 0 b) (h1.symm.trans (mul_one _).symm)`. Establish `h0' : ∀ a, χ a 0 = 1`. Introduce `a`. Establish `h1` using `hχr a 0 0`.

Rewrite `h1` using `[add_zero]`. Conclude with `mul_left_cancel₀ (hχ0 a 0) (h1.symm.trans (mul_one _).symm)`. Establish `hpow : ∀ (n : ℕ) (a b : W), χ (n • a) b = χ a b ^ n`. Introduce `n a b`. Proceed by induction on `n with`.

Consider the case `zero => rw [zero_smul, pow_zero, h0]`. Consider the case `succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]`. Establish `hpow' : ∀ (n : ℕ) (a b : W), χ a (n • b) = χ a b ^ n`. Introduce `n a b`. Proceed by induction on `n with`.

Consider the case `zero => rw [zero_smul, pow_zero, h0']`. Consider the case `succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]`. Use `⟨k * k3, Nat.mul_pos hk hk3, fun t _ u hu => ?_⟩` and prove the remaining obligations. Use `show Φ (a + (t + (k * k3) • u)) * (χ (t + (k * k3) • u) y)⁻¹ = Φ (a + t) * (χ t y)⁻¹`. Establish `hΦ : Φ (a + t + (k * k3) • u) = Φ (a + t)`.

Rewrite using `[← smul_smul]`. Conclude with `hi _ ((L ⊓ X).nsmul_mem hu k3) (a + t)`. Establish `hχu : χ ((k * k3) • u) y = 1`. Rewrite using `[hpow, mul_comm, pow_mul, ← hpow', hLL u hu (k3 • y) ⟨hy3, Y.nsmul_mem hy k3⟩, one_pow]`. Rewrite using `[← add_assoc, hΦ, hχl, hχu, mul_one]`.
-/
theorem coef_inv {Φ : W → ℂ} (h : IsSB L X Φ) (a : W) {y : W} (hy : y ∈ Y) :
    ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  obtain ⟨k3, hk3, hy3⟩ := hoY y hy
  have h0 : ∀ b, χ 0 b = 1 := by
    intro b
    have h1 := hχl 0 0 b
    rw [add_zero] at h1
    exact mul_left_cancel₀ (hχ0 0 b) (h1.symm.trans (mul_one _).symm)
  have h0' : ∀ a, χ a 0 = 1 := by
    intro a
    have h1 := hχr a 0 0
    rw [add_zero] at h1
    exact mul_left_cancel₀ (hχ0 a 0) (h1.symm.trans (mul_one _).symm)
  have hpow : ∀ (n : ℕ) (a b : W), χ (n • a) b = χ a b ^ n := by
    intro n a b
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
  have hpow' : ∀ (n : ℕ) (a b : W), χ a (n • b) = χ a b ^ n := by
    intro n a b
    induction n with
    | zero => rw [zero_smul, pow_zero, h0']
    | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]
  refine ⟨k * k3, Nat.mul_pos hk hk3, fun t _ u hu => ?_⟩
  show Φ (a + (t + (k * k3) • u)) * (χ (t + (k * k3) • u) y)⁻¹ = Φ (a + t) * (χ t y)⁻¹
  have hΦ : Φ (a + t + (k * k3) • u) = Φ (a + t) := by
    rw [← smul_smul]; exact hi _ ((L ⊓ X).nsmul_mem hu k3) (a + t)
  have hχu : χ ((k * k3) • u) y = 1 := by
    rw [hpow, mul_comm, pow_mul, ← hpow', hLL u hu (k3 • y) ⟨hy3, Y.nsmul_mem hy k3⟩, one_pow]
  rw [← add_assoc, hΦ, hχl, hχu, mul_one]

include hχl hχr hχ0 hLL hoY hfinX in
/- English proof (translation)
Establish `inv_mul : ∀ (H : AddSubgroup W) (g : W → ℂ) (k m : ℕ), IsInv k H g → IsInv (k * m) H g`. Introduce `H g k m h t ht u hu`. Rewrite using `[← smul_smul]`. Conclude with `h t ht _ (H.nsmul_mem hu m)`. Establish `avg_mul : ∀ (H : AddSubgroup W) (g : W → ℂ) (k m : ℕ), Finite (Qt k H) → Finite (Qt (k * m) H) → IsInv k H g → avg (k * m) H g = avg k H g`.

Introduce `H g k m hfk hfkm hg`. Use `haveI := Fintype.ofFinite (Qt k H)`. Use `haveI := Fintype.ofFinite (Qt (k * m) H)`. Establish `hle : (smulSub (k * m) H).addSubgroupOf H ≤ (smulSub k H).addSubgroupOf H`. Introduce `h hh`.

Rewrite `hh`, the goal using `[AddSubgroup.mem_addSubgroupOf]`. Simplify using `only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at hh ⊢`. Take `⟨v, hv, hv'⟩` from `hh`. Conclude with `⟨m • v, H.nsmul_mem hv m, by rw [← hv', smul_smul]⟩`. Set `π : Qt (k * m) H →+ Qt k H` to `QuotientAddGroup.map _ _ (AddMonoidHom.id H) (fun x hx => hle hx)`.

Establish `hπ : ∀ x : H, π (QuotientAddGroup.mk x) = QuotientAddGroup.mk x` using `fun x => rfl`. Establish `hsurj : Function.Surjective π`. Introduce `r`. Use `⟨QuotientAddGroup.mk r.out, ?_⟩` and prove the remaining obligations. Rewrite using `[hπ, QuotientAddGroup.out_eq']`.

Establish `hval : ∀ q : Qt (k * m) H, g ((q.out : H) : W) = g (((π q).out : H) : W)`. Introduce `q`. Establish `hq : π q = QuotientAddGroup.mk q.out` using `by rw [← hπ, QuotientAddGroup.out_eq']`. Establish `h1` using `(QuotientAddGroup.out_eq' (π q)).trans hq`. Rewrite `h1` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`.

Simplify using `only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at h1`. Take `⟨v, hv, hv'⟩` from `h1`. Establish `h2 : ((q.out : H) : W) = ((π q).out : H) + k • v`. Rewrite using `[hv']`. Use `push_cast`.

Normalize the expressions using the abelian group laws. Rewrite using `[h2]`. Conclude with `hg _ ((π q).out).2 v hv`. Take `⟨N, hN⟩ : ∃ N, N = (Finset.univ.filter fun q : Qt (k * m) H => π q = 0).card` from `⟨_, rfl⟩`. Establish `hfib : ∀ r : Qt k H, (Finset.univ.filter fun q : Qt (k * m) H => π q = r).card = N`.

Introduce `r`. Rewrite using `[hN]`. Conclude with `AddMonoidHom.card_fiber_eq_of_mem_range π (hsurj r) (hsurj 0)`. Establish `hN0 : N ≠ 0`. Rewrite using `[hN]`.

Conclude with `(Finset.card_pos.2 ⟨0, by simp⟩).ne'`. Establish `hsum : ∑ q : Qt (k * m) H, g ((q.out : H) : W) = N * ∑ r : Qt k H, g ((r.out : H) : W)`. Rewrite using `[Fintype.sum_congr _ _ hval, Finset.sum_comp (fun r : Qt k H => g ((r.out : H) : W)) π, Finset.image_univ_of_surjective hsurj]`. Repeatedly rewrite using `[hfib]`. Rewrite using `[← Finset.smul_sum, nsmul_eq_mul]`.

Establish `hcard : Fintype.card (Qt (k * m) H) = N * Fintype.card (Qt k H)`. Rewrite using `[← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]`. Repeatedly rewrite using `[hfib]`. Simplify using `[mul_comm]`. Unfold `avg`.

Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hsum, hcard]`. Establish `hN0' : (N : ℂ) ≠ 0` using `by exact_mod_cast hN0`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take `⟨k1, hk1, hi1⟩` from `coef_inv (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hoY := hoY) h a hy`.

Take `⟨k2, hk2, hi2⟩` from `coef_inv (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hoY := hoY) h' a hy`. Unfold `coef`. Take `⟨g1, hg1⟩ : ∃ g : W → ℂ, g = fun t => Φ (a + t) * (χ t y)⁻¹` from `⟨_, rfl⟩`. Take `⟨g2, hg2⟩ : ∃ g : W → ℂ, g = fun t => Φ' (a + t) * (χ t y)⁻¹` from `⟨_, rfl⟩`. Rewrite `hi1` using `[← hg1]`.

Rewrite `hi2` using `[← hg2]`. Rewrite using `[← hg1, ← hg2]`. Establish `hsum : (fun t => (Φ + Φ') (a + t) * (χ t y)⁻¹) = fun t => g1 t + g2 t`. Use function extensionality and compare the values at `t`. Rewrite using `[hg1, hg2]`.

Simplify using `[add_mul]`. Rewrite using `[hsum]`. Establish `hi3 : IsInv (k1 * k2) (L ⊓ X) (fun t => g1 t + g2 t)`. Introduce `t ht u hu`. Establish `e1` using `inv_mul _ _ k1 k2 hi1 t ht u hu`.

Establish `e2` using `inv_mul _ _ k2 k1 hi2 t ht u hu`. Rewrite `e2` using `[mul_comm k2 k1]`. Use `show g1 (t + (k1 * k2) • u) + g2 (t + (k1 * k2) • u) = g1 t + g2 t`. Rewrite using `[e1, e2]`. Establish `hex1 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g1` using `⟨k1, hk1, hi1⟩`.

Establish `hex2 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g2` using `⟨k2, hk2, hi2⟩`. Establish `hex3 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => g1 t + g2 t)` using `⟨k1 * k2, Nat.mul_pos hk1 hk2, hi3⟩`. Unfold `integ`. Rewrite using `[dif_pos hex1, dif_pos hex2, dif_pos hex3]`. Establish `hK1` using `hex1.choose_spec.1`.

Establish `hI1` using `hex1.choose_spec.2`. Establish `hK2` using `hex2.choose_spec.1`. Establish `hI2` using `hex2.choose_spec.2`. Establish `hK3` using `hex3.choose_spec.1`. Establish `hI3` using `hex3.choose_spec.2`.

Establish `hpos : 0 < hex1.choose * (hex2.choose * hex3.choose)` using `by positivity`. Establish `f1` using `avg_mul _ _ hex1.choose (hex2.choose * hex3.choose) (hfinX _ hK1) (hfinX _ hpos) hI1`. Establish `f2` using `avg_mul _ _ hex2.choose (hex1.choose * hex3.choose) (hfinX _ hK2) (hfinX _ (by positivity)) hI2`. Establish `f3` using `avg_mul _ _ hex3.choose (hex1.choose * hex2.choose) (hfinX _ hK3) (hfinX _ (by positivity)) hI3`. Establish `e2 : hex2.choose * (hex1.choose * hex3.choose) = hex1.choose * (hex2.choose * hex3.choose)` using `by ring`.

Establish `e3 : hex3.choose * (hex1.choose * hex2.choose) = hex1.choose * (hex2.choose * hex3.choose)` using `by ring`. Rewrite `f2` using `[e2]`. Rewrite `f3` using `[e3]`. Rewrite using `[← f1, ← f2, ← f3]`. Use `haveI := hfinX _ hpos`.

Simplify using `only [avg]`. Rewrite using `[finsum_add_distrib (Set.toFinite _) (Set.toFinite _), mul_add]`.
-/
theorem coef_add {Φ Φ' : W → ℂ} (h : IsSB L X Φ) (h' : IsSB L X Φ') (a : W) {y : W} (hy : y ∈ Y) :
    coef χ L X (Φ + Φ') a y = coef χ L X Φ a y + coef χ L X Φ' a y := by
  have inv_mul : ∀ (H : AddSubgroup W) (g : W → ℂ) (k m : ℕ), IsInv k H g → IsInv (k * m) H g := by
    intro H g k m h t ht u hu
    rw [← smul_smul]
    exact h t ht _ (H.nsmul_mem hu m)
  have avg_mul : ∀ (H : AddSubgroup W) (g : W → ℂ) (k m : ℕ), Finite (Qt k H) → Finite (Qt (k * m) H) →
      IsInv k H g → avg (k * m) H g = avg k H g := by
    intro H g k m hfk hfkm hg
    classical
    haveI := Fintype.ofFinite (Qt k H)
    haveI := Fintype.ofFinite (Qt (k * m) H)
    have hle : (smulSub (k * m) H).addSubgroupOf H ≤ (smulSub k H).addSubgroupOf H := by
      intro h hh
      rw [AddSubgroup.mem_addSubgroupOf] at hh ⊢
      simp only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at hh ⊢
      obtain ⟨v, hv, hv'⟩ := hh
      exact ⟨m • v, H.nsmul_mem hv m, by rw [← hv', smul_smul]⟩
    let π : Qt (k * m) H →+ Qt k H := QuotientAddGroup.map _ _ (AddMonoidHom.id H) (fun x hx => hle hx)
    have hπ : ∀ x : H, π (QuotientAddGroup.mk x) = QuotientAddGroup.mk x := fun x => rfl
    have hsurj : Function.Surjective π := by
      intro r
      refine ⟨QuotientAddGroup.mk r.out, ?_⟩
      rw [hπ, QuotientAddGroup.out_eq']
    have hval : ∀ q : Qt (k * m) H, g ((q.out : H) : W) = g (((π q).out : H) : W) := by
      intro q
      have hq : π q = QuotientAddGroup.mk q.out := by rw [← hπ, QuotientAddGroup.out_eq']
      have h1 := (QuotientAddGroup.out_eq' (π q)).trans hq
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
      simp only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at h1
      obtain ⟨v, hv, hv'⟩ := h1
      have h2 : ((q.out : H) : W) = ((π q).out : H) + k • v := by
        rw [hv']
        push_cast
        abel
      rw [h2]
      exact hg _ ((π q).out).2 v hv
    obtain ⟨N, hN⟩ : ∃ N, N = (Finset.univ.filter fun q : Qt (k * m) H => π q = 0).card := ⟨_, rfl⟩
    have hfib : ∀ r : Qt k H, (Finset.univ.filter fun q : Qt (k * m) H => π q = r).card = N := by
      intro r
      rw [hN]
      exact AddMonoidHom.card_fiber_eq_of_mem_range π (hsurj r) (hsurj 0)
    have hN0 : N ≠ 0 := by
      rw [hN]
      exact (Finset.card_pos.2 ⟨0, by simp⟩).ne'
    have hsum : ∑ q : Qt (k * m) H, g ((q.out : H) : W) = N * ∑ r : Qt k H, g ((r.out : H) : W) := by
      rw [Fintype.sum_congr _ _ hval, Finset.sum_comp (fun r : Qt k H => g ((r.out : H) : W)) π,
        Finset.image_univ_of_surjective hsurj]
      simp_rw [hfib]
      rw [← Finset.smul_sum, nsmul_eq_mul]
    have hcard : Fintype.card (Qt (k * m) H) = N * Fintype.card (Qt k H) := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
      simp_rw [hfib]
      simp [mul_comm]
    unfold avg
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, hsum, hcard]
    have hN0' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
    push_cast
    field_simp
  obtain ⟨k1, hk1, hi1⟩ := coef_inv (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hoY := hoY) h a hy
  obtain ⟨k2, hk2, hi2⟩ := coef_inv (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hoY := hoY) h' a hy
  unfold coef
  obtain ⟨g1, hg1⟩ : ∃ g : W → ℂ, g = fun t => Φ (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ g : W → ℂ, g = fun t => Φ' (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  rw [← hg1] at hi1
  rw [← hg2] at hi2
  rw [← hg1, ← hg2]
  have hsum : (fun t => (Φ + Φ') (a + t) * (χ t y)⁻¹) = fun t => g1 t + g2 t := by
    funext t; rw [hg1, hg2]; simp [add_mul]
  rw [hsum]
  have hi3 : IsInv (k1 * k2) (L ⊓ X) (fun t => g1 t + g2 t) := by
    intro t ht u hu
    have e1 := inv_mul _ _ k1 k2 hi1 t ht u hu
    have e2 := inv_mul _ _ k2 k1 hi2 t ht u hu
    rw [mul_comm k2 k1] at e2
    show g1 (t + (k1 * k2) • u) + g2 (t + (k1 * k2) • u) = g1 t + g2 t
    rw [e1, e2]
  have hex1 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g1 := ⟨k1, hk1, hi1⟩
  have hex2 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g2 := ⟨k2, hk2, hi2⟩
  have hex3 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => g1 t + g2 t) := ⟨k1 * k2, Nat.mul_pos hk1 hk2, hi3⟩
  unfold integ
  rw [dif_pos hex1, dif_pos hex2, dif_pos hex3]
  have hK1 := hex1.choose_spec.1
  have hI1 := hex1.choose_spec.2
  have hK2 := hex2.choose_spec.1
  have hI2 := hex2.choose_spec.2
  have hK3 := hex3.choose_spec.1
  have hI3 := hex3.choose_spec.2
  have hpos : 0 < hex1.choose * (hex2.choose * hex3.choose) := by positivity
  have f1 := avg_mul _ _ hex1.choose (hex2.choose * hex3.choose) (hfinX _ hK1) (hfinX _ hpos) hI1
  have f2 := avg_mul _ _ hex2.choose (hex1.choose * hex3.choose) (hfinX _ hK2)
    (hfinX _ (by positivity)) hI2
  have f3 := avg_mul _ _ hex3.choose (hex1.choose * hex2.choose) (hfinX _ hK3)
    (hfinX _ (by positivity)) hI3
  have e2 : hex2.choose * (hex1.choose * hex3.choose) = hex1.choose * (hex2.choose * hex3.choose) := by ring
  have e3 : hex3.choose * (hex1.choose * hex2.choose) = hex1.choose * (hex2.choose * hex3.choose) := by ring
  rw [e2] at f2
  rw [e3] at f3
  rw [← f1, ← f2, ← f3]
  haveI := hfinX _ hpos
  simp only [avg]
  rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _), mul_add]

include hfinX in
/- English proof (translation)
Unfold `coef`. Take `⟨g, hg⟩ : ∃ g : W → ℂ, g = fun t => Φ (a + t) * (χ t y)⁻¹` from `⟨_, rfl⟩`. Establish `hg' : (fun t => (c • Φ) (a + t) * (χ t y)⁻¹) = fun t => c * g t`. Use function extensionality and compare the values at `t`. Simplify using `[hg, mul_assoc]`.

Rewrite using `[hg', ← hg]`. Unfold `integ`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Simplify using `only [zero_mul]`.

Use `split_ifs with h1`. Unfold `avg`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Establish `hiff : ∀ k, IsInv k (L ⊓ X) (fun t => c * g t) ↔ IsInv k (L ⊓ X) g`.

Introduce `k`. Unfold `IsInv`. Prove the components needed by the constructor for the conclusion. Introduce `h t ht u hu`. Conclude with `mul_left_cancel₀ hc (h t ht u hu)`.

Introduce `h t ht u hu`. Use `show c * g (t + k • u) = c * g t`. Rewrite using `[h t ht u hu]`. Establish `hpred : (fun k => 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t)) = (fun k => 0 < k ∧ IsInv k (L ⊓ X) g)`. Use function extensionality and compare the values at `fun k => propext (and_congr_right' (hiff k))`.

Establish `key : ∀ (p q : ℕ → Prop) (hp : ∃ k, p k) (hq : ∃ k, q k), p = q → hp.choose = hq.choose`. Introduce `p q hp hq h`. Substitute `h` using the available equality. Both sides reduce to the same expression. Distinguish the cases in `hex : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g`.

Establish `hex' : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t)` using `by rw [hpred]; exact hex`. Rewrite using `[dif_pos hex', dif_pos hex, key _ _ hex' hex hpred]`. Use `haveI := hfinX _ hex.choose_spec.1`. Unfold `avg`. Rewrite using `[← mul_finsum _ c]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hex' : ¬ ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t)` using `by rw [hpred]; exact hex`. Rewrite using `[dif_neg hex', dif_neg hex, mul_zero]`.
-/
theorem coef_smul (Φ : W → ℂ) (c : ℂ) (a y : W) : coef χ L X (c • Φ) a y = c * coef χ L X Φ a y := by
  unfold coef
  obtain ⟨g, hg⟩ : ∃ g : W → ℂ, g = fun t => Φ (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  have hg' : (fun t => (c • Φ) (a + t) * (χ t y)⁻¹) = fun t => c * g t := by
    funext t; simp [hg, mul_assoc]
  rw [hg', ← hg]
  unfold integ
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    split_ifs with h1
    · unfold avg; simp
    · rfl
  · have hiff : ∀ k, IsInv k (L ⊓ X) (fun t => c * g t) ↔ IsInv k (L ⊓ X) g := by
      intro k
      unfold IsInv
      constructor
      · intro h t ht u hu; exact mul_left_cancel₀ hc (h t ht u hu)
      · intro h t ht u hu; show c * g (t + k • u) = c * g t; rw [h t ht u hu]
    have hpred : (fun k => 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t)) =
        (fun k => 0 < k ∧ IsInv k (L ⊓ X) g) :=
      funext fun k => propext (and_congr_right' (hiff k))
    have key : ∀ (p q : ℕ → Prop) (hp : ∃ k, p k) (hq : ∃ k, q k), p = q → hp.choose = hq.choose := by
      intro p q hp hq h; subst h; rfl
    by_cases hex : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g
    · have hex' : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t) := by rw [hpred]; exact hex
      rw [dif_pos hex', dif_pos hex, key _ _ hex' hex hpred]
      haveI := hfinX _ hex.choose_spec.1
      unfold avg
      rw [← mul_finsum _ c]
      ring
    · have hex' : ¬ ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => c * g t) := by rw [hpred]; exact hex
      rw [dif_neg hex', dif_neg hex, mul_zero]

include hχl hχr hχ0 hLL hdY hoY hfinX in

/- English proof (translation)
Unfold `coef at hc`. Take `⟨G, hG⟩ : ∃ G : W → ℂ, G = fun t => Φ (a + t) * (χ t y)⁻¹` from `⟨_, rfl⟩`. Rewrite `hc` using `[← hG]`. Unfold `integ at hc`. Distinguish the cases in `hex : ∃ K, 0 < K ∧ IsInv K (L ⊓ X) G`.

Use `swap`. Rewrite `hc` using `[dif_neg hex]`. Conclude with `absurd rfl hc`. Rewrite `hc` using `[dif_pos hex]`. Establish `hK` using `hex.choose_spec.1`.

Establish `hI` using `hex.choose_spec.2`. Use `haveI := hfinX _ hK`. Use `haveI := Fintype.ofFinite (Qt hex.choose (L ⊓ X))`. Unfold `avg at hc`. Rewrite `hc` using `[finsum_eq_sum_of_fintype]`.

Establish `hS : ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) ≠ 0`. Introduce `h0`. Apply `hc` to reduce the goal to its premises. Rewrite using `[h0, mul_zero]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hno push_neg at hno`. Apply `hS` to reduce the goal to its premises. Use `Finset.sum_eq_zero fun q _ => ?_` and prove the remaining obligations. Simplify using `only [hG]`. Rewrite using `[hno _ (q.out).2, zero_mul]`.

Establish `h0 : ∀ b, χ 0 b = 1`. Introduce `b`. Establish `h1` using `hχl 0 0 b`. Rewrite `h1` using `[add_zero]`. Conclude with `mul_left_cancel₀ (hχ0 0 b) (h1.symm.trans (mul_one _).symm)`.

Establish `h0' : ∀ a, χ a 0 = 1`. Introduce `a`. Establish `h1` using `hχr a 0 0`. Rewrite `h1` using `[add_zero]`. Conclude with `mul_left_cancel₀ (hχ0 a 0) (h1.symm.trans (mul_one _).symm)`.

Establish `hpow : ∀ (n : ℕ) (a b : W), χ (n • a) b = χ a b ^ n`. Introduce `n a b`. Proceed by induction on `n with`. Consider the case `zero => rw [zero_smul, pow_zero, h0]`. Consider the case `succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]`.

Establish `hpow' : ∀ (n : ℕ) (a b : W), χ a (n • b) = χ a b ^ n`. Introduce `n a b`. Proceed by induction on `n with`. Consider the case `zero => rw [zero_smul, pow_zero, h0']`. Consider the case `succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]`.

Apply `hdY (k • y) (Y.nsmul_mem hy k)` to reduce the goal to its premises. Introduce `x hx`. Establish `hGshift : ∀ t, G (t + k • x) = (χ x (k • y))⁻¹ * G t`. Introduce `t`. Simplify using `only [hG]`.

Rewrite using `[← add_assoc, hi x hx (a + t), hχl, hpow, ← hpow', mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨z, hz⟩ : ∃ z : ↥(L ⊓ X), (z : W) = k • x` from `⟨⟨k • x, (L ⊓ X).nsmul_mem hx k⟩, rfl⟩`. Establish `hshift : ∀ q : Qt hex.choose (L ⊓ X), G (((q.out : ↥(L ⊓ X)) : W) + k • x) = G (((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out : ↥(L ⊓ X)) : W)`. Introduce `q`.

Establish `hq : (q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))) = QuotientAddGroup.mk (q.out + z)`. Rewrite using `[QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']`. Establish `h1` using `(QuotientAddGroup.out_eq' (q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X)))).trans hq`. Rewrite `h1` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Simplify using `only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at h1`.

Take `⟨v, hv, hv'⟩` from `h1`. Establish `h2 : ((q.out : ↥(L ⊓ X)) : W) + k • x = ((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out : ↥(L ⊓ X)) + hex.choose • v`. Rewrite using `[hv', ← hz]`. Use `push_cast`. Use `first`.

Consider the case `exact (add_neg_cancel_left _ _).symm`. Consider the case `simp`. Consider the case `abel`. Rewrite using `[h2]`. Conclude with `hI _ ((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out).2 v hv`.

Establish `hshift_sum : ∑ q : Qt hex.choose (L ⊓ X), G (((q.out : ↥(L ⊓ X)) : W) + k • x) = ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W)`. Rewrite using `[Fintype.sum_congr _ _ hshift]`. Conclude with `Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))) (fun q => G ((q.out : ↥(L ⊓ X)) : W))`. Establish `hmul : (χ x (k • y))⁻¹ * ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) = ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W)`. Rewrite using `[Finset.mul_sum]`.

Repeatedly rewrite using `[← hGshift]`. Conclude with `hshift_sum`. Establish `h1` using `mul_right_cancel₀ hS (hmul.trans (one_mul _).symm)`. Conclude with `inv_eq_one.1 h1`.
-/
theorem coef_ne_zero {Φ : W → ℂ} (h : IsSB L X Φ) {k : ℕ} (hk : 0 < k) (hi : ∀ u ∈ L ⊓ X, ∀ t, Φ (t + k • u) = Φ t)
    {a y : W} (hy : y ∈ Y) (hc : coef χ L X Φ a y ≠ 0) : (∃ t ∈ L ⊓ X, Φ (a + t) ≠ 0) ∧ k • y ∈ L := by
  unfold coef at hc
  obtain ⟨G, hG⟩ : ∃ G : W → ℂ, G = fun t => Φ (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  rw [← hG] at hc
  unfold integ at hc
  by_cases hex : ∃ K, 0 < K ∧ IsInv K (L ⊓ X) G
  swap
  · rw [dif_neg hex] at hc; exact absurd rfl hc
  rw [dif_pos hex] at hc
  have hK := hex.choose_spec.1
  have hI := hex.choose_spec.2
  haveI := hfinX _ hK
  classical
  haveI := Fintype.ofFinite (Qt hex.choose (L ⊓ X))
  unfold avg at hc
  rw [finsum_eq_sum_of_fintype] at hc
  have hS : ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) ≠ 0 := by
    intro h0; apply hc; rw [h0, mul_zero]
  refine ⟨?_, ?_⟩
  · by_contra hno
    push_neg at hno
    apply hS
    refine Finset.sum_eq_zero fun q _ => ?_
    simp only [hG]
    rw [hno _ (q.out).2, zero_mul]
  · have h0 : ∀ b, χ 0 b = 1 := by
      intro b
      have h1 := hχl 0 0 b
      rw [add_zero] at h1
      exact mul_left_cancel₀ (hχ0 0 b) (h1.symm.trans (mul_one _).symm)
    have h0' : ∀ a, χ a 0 = 1 := by
      intro a
      have h1 := hχr a 0 0
      rw [add_zero] at h1
      exact mul_left_cancel₀ (hχ0 a 0) (h1.symm.trans (mul_one _).symm)
    have hpow : ∀ (n : ℕ) (a b : W), χ (n • a) b = χ a b ^ n := by
      intro n a b
      induction n with
      | zero => rw [zero_smul, pow_zero, h0]
      | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
    have hpow' : ∀ (n : ℕ) (a b : W), χ a (n • b) = χ a b ^ n := by
      intro n a b
      induction n with
      | zero => rw [zero_smul, pow_zero, h0']
      | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]
    apply hdY (k • y) (Y.nsmul_mem hy k)
    intro x hx
    have hGshift : ∀ t, G (t + k • x) = (χ x (k • y))⁻¹ * G t := by
      intro t
      simp only [hG]
      rw [← add_assoc, hi x hx (a + t), hχl, hpow, ← hpow', mul_inv]
      ring
    obtain ⟨z, hz⟩ : ∃ z : ↥(L ⊓ X), (z : W) = k • x := ⟨⟨k • x, (L ⊓ X).nsmul_mem hx k⟩, rfl⟩
    have hshift : ∀ q : Qt hex.choose (L ⊓ X), G (((q.out : ↥(L ⊓ X)) : W) + k • x) =
        G (((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out : ↥(L ⊓ X)) : W) := by
      intro q
      have hq : (q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))) =
          QuotientAddGroup.mk (q.out + z) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      have h1 := (QuotientAddGroup.out_eq' (q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X)))).trans hq
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
      simp only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at h1
      obtain ⟨v, hv, hv'⟩ := h1
      have h2 : ((q.out : ↥(L ⊓ X)) : W) + k • x =
          ((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out : ↥(L ⊓ X)) + hex.choose • v := by
        rw [hv', ← hz]
        push_cast
        first
          | exact (add_neg_cancel_left _ _).symm
          | simp
          | abel
      rw [h2]
      exact hI _ ((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out).2 v hv
    have hshift_sum : ∑ q : Qt hex.choose (L ⊓ X), G (((q.out : ↥(L ⊓ X)) : W) + k • x) =
        ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) := by
      rw [Fintype.sum_congr _ _ hshift]
      exact Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X)))
        (fun q => G ((q.out : ↥(L ⊓ X)) : W))
    have hmul : (χ x (k • y))⁻¹ * ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) =
        ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) := by
      rw [Finset.mul_sum]
      simp_rw [← hGshift]
      exact hshift_sum
    have h1 := mul_right_cancel₀ hS (hmul.trans (one_mul _).symm)
    exact inv_eq_one.1 h1

include hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf in
open Classical in
/- English proof (translation)
Take `⟨hs, k, hk, hi, hl⟩` from `id h`. Use `haveI := hfinX k hk`. Use `haveI := hfinY k hk`. Establish `hS1` using `finite_nsmul_out (L ⊓ X) (htf k hk)`. Establish `hS2` using `finite_nsmul_out (L ⊓ Y) (htf k hk)`.

Use `(hS1.prod hS2).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨q1, q2⟩ hq`. Rewrite `hq` using `[Function.mem_support]`. Use `split_ifs at hq with hy`. Establish `hc : coef χ L X Φ q1.out q2.out ≠ 0` using `fun h0 => hq (by simp [term, h0])`.

Take `⟨⟨t, ht, hΦ⟩, hky⟩` from `coef_ne_zero (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hdY := hdY) (hoY := hoY) (hfinX := hfinX) h hk hi hy hc`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show k • q1.out ∈ L ⊓ X`. Establish `hX : q1.out + t ∈ X` using `hs _ hΦ`. Establish `hL' : k • (q1.out + t) ∈ L` using `hl _ hΦ`.

Establish `hx : q1.out ∈ X` using `by simpa using X.sub_mem hX ht.2`. Use `⟨?_, X.nsmul_mem hx k⟩` and prove the remaining obligations. Establish `h5 : k • q1.out = k • (q1.out + t) - k • t` using `by rw [smul_add]; abel`. Rewrite using `[h5]`. Conclude with `L.sub_mem hL' (L.nsmul_mem ht.1 k)`.

Conclude with `⟨hky, Y.nsmul_mem hy k⟩`. Conclude with `absurd rfl hq`.
-/
theorem term_support_finite {Φ : W → ℂ} (h : IsSB L X Φ) :
    (Function.support fun q : QX L X × QY L Y =>
      if q.2.out ∈ Y then term ρ χ L X f₀ Φ q.1.out q.2.out else 0).Finite := by
  obtain ⟨hs, k, hk, hi, hl⟩ := id h
  haveI := hfinX k hk
  haveI := hfinY k hk
  have hS1 := finite_nsmul_out (L ⊓ X) (htf k hk)
  have hS2 := finite_nsmul_out (L ⊓ Y) (htf k hk)
  refine (hS1.prod hS2).subset ?_
  rintro ⟨q1, q2⟩ hq
  rw [Function.mem_support] at hq
  split_ifs at hq with hy
  · have hc : coef χ L X Φ q1.out q2.out ≠ 0 := fun h0 => hq (by simp [term, h0])
    obtain ⟨⟨t, ht, hΦ⟩, hky⟩ := coef_ne_zero (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL)
      (hdY := hdY) (hoY := hoY) (hfinX := hfinX) h hk hi hy hc
    refine ⟨?_, ?_⟩
    · show k • q1.out ∈ L ⊓ X
      have hX : q1.out + t ∈ X := hs _ hΦ
      have hL' : k • (q1.out + t) ∈ L := hl _ hΦ
      have hx : q1.out ∈ X := by simpa using X.sub_mem hX ht.2
      refine ⟨?_, X.nsmul_mem hx k⟩
      have h5 : k • q1.out = k • (q1.out + t) - k • t := by rw [smul_add]; abel
      rw [h5]
      exact L.sub_mem hL' (L.nsmul_mem ht.1 k)
    · exact ⟨hky, Y.nsmul_mem hy k⟩
  · exact absurd rfl hq

end Main

end Formalism.IndefR.Fin.Four

end

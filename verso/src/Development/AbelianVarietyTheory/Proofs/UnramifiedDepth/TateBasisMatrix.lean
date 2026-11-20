import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

namespace GlobalTheory

/- English proof (translation)
Establish `h : (N : ℤ) ∣ a - ((a : ZMod N).val : ℤ)`. Rewrite using `[← ZMod.intCast_eq_intCast_iff_dvd_sub]`. Simplify using the standard rewrite rules. Take `⟨c, hc⟩` from `h`. Establish `h2 : a = ((a : ZMod N).val : ℤ) + c * N` using `by linarith`.

Use `conv_rhs => rw [h2, add_smul, mul_smul, natCast_zsmul, natCast_zsmul, hx, smul_zero, add_zero]`.
-/
private theorem tateMat_val_smul {Γ : Type} [AddCommGroup Γ] {N : ℕ} [NeZero N] {x : Γ}
    (hx : N • x = 0) (a : ℤ) : ((a : ZMod N).val) • x = a • x := by
  have h : (N : ℤ) ∣ a - ((a : ZMod N).val : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]; simp
  obtain ⟨c, hc⟩ := h
  have h2 : a = ((a : ZMod N).val : ℤ) + c * N := by linarith
  conv_rhs => rw [h2, add_smul, mul_smul, natCast_zsmul, natCast_zsmul, hx, smul_zero, add_zero]

section
variable {p : ℕ} [hp : Fact p.Prime] {κ Γ : Type} [Fintype κ] [AddCommGroup Γ] {τ : κ → ℕ → Γ}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [ih, h2 j n, pow_succ, mul_smul]`.
-/
private theorem tateMat_zero (h2 : ∀ i n, τ i n = p • τ i (n + 1)) (j : κ) (n : ℕ) :
    τ j 0 = (p ^ n) • τ j n := by
  induction n with
  | zero => simp
  | succ n ih => rw [ih, h2 j n, pow_succ, mul_smul]

/- English proof (translation)
Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[h2 j n, smul_comm]`.
-/
private theorem tateMat_step (h2 : ∀ i n, τ i n = p • τ i (n + 1)) (a : κ → ℤ) (n : ℕ) :
    ∑ j, a j • τ j n = p • ∑ j, a j • τ j (n + 1) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h2 j n, smul_comm]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `x hx`. Take `⟨t, ht, -⟩` from `h3 x (by simpa using hx)`. Conclude with `⟨fun j => ((t j).val : ℤ), by simpa only [natCast_zsmul] using ht⟩`.

Consider the case `succ n ih`. Introduce `x hx`. Take `⟨a, ha⟩` from `ih (p • x) (by rw [← mul_smul, ← pow_succ, hx])`. Take `⟨t, ht, -⟩` from `h3 (x - ∑ j, a j • τ j (n + 1)) (by`. Rewrite using `[smul_sub, ← tateMat_step h2, ha, sub_self])`.

Use `⟨fun j => a j + (((t j).val * p ^ (n + 1) : ℕ) : ℤ), ?_⟩` and prove the remaining obligations. Simplify using `only [add_smul, Finset.sum_add_distrib, natCast_zsmul, mul_smul, ← tateMat_zero h2]`. Rewrite using `[← ht]`. Normalize the expressions using the abelian group laws.
-/
private theorem tateMat_exists (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) (n : ℕ) :
    ∀ x : Γ, (p ^ (n + 1)) • x = 0 → ∃ a : κ → ℤ, x = ∑ j, a j • τ j n := by
  induction n with
  | zero =>
    intro x hx
    obtain ⟨t, ht, -⟩ := h3 x (by simpa using hx)
    exact ⟨fun j => ((t j).val : ℤ), by simpa only [natCast_zsmul] using ht⟩
  | succ n ih =>
    intro x hx
    obtain ⟨a, ha⟩ := ih (p • x) (by rw [← mul_smul, ← pow_succ, hx])
    obtain ⟨t, ht, -⟩ := h3 (x - ∑ j, a j • τ j (n + 1)) (by
      rw [smul_sub, ← tateMat_step h2, ha, sub_self])
    refine ⟨fun j => a j + (((t j).val * p ^ (n + 1) : ℕ) : ℤ), ?_⟩
    simp only [add_smul, Finset.sum_add_distrib, natCast_zsmul, mul_smul, ← tateMat_zero h2]
    rw [← ht]; abel

/- English proof (translation)
Use `haveI : NeZero p := ⟨hp.out.ne_zero⟩`. Establish `base : ∀ a : κ → ℤ, ∑ j, a j • τ j 0 = 0 → ∀ j, (p : ℤ) ∣ a j`. Introduce `a ha j`. Establish `hu` using `(h3 0 (smul_zero _)).unique (y₁ := fun j => (a j : ZMod p)) (y₂ := fun _ => 0) (by`. Rewrite using `[← ha]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `(tateMat_val_smul (by simpa using h1 k 0) _).symm)`. Use the proof step `(by simp)`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun hu j)`. Proceed by induction on `n with`.

Consider the case `zero => intro a ha j`. Simplify using `using base a ha j`. Consider the case `succ n ih`. Introduce `a ha j`. Establish `hd` using `ih a (by rw [tateMat_step h2, ha, smul_zero])`.

Use `choose b hb using hd`. Use `base b (by` as an intermediate fact. Rewrite using `[← ha]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hb k, tateMat_zero h2 k (n + 1), mul_comm, mul_smul, natCast_zsmul]) j`.

Rewrite using `[hb j, pow_succ p (n + 1)]`. Use `push_cast`. Conclude with `mul_dvd_mul_left _ this`.
-/
private theorem tateMat_dvd (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) (n : ℕ) :
    ∀ a : κ → ℤ, ∑ j, a j • τ j n = 0 → ∀ j, ((p ^ (n + 1) : ℕ) : ℤ) ∣ a j := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have base : ∀ a : κ → ℤ, ∑ j, a j • τ j 0 = 0 → ∀ j, (p : ℤ) ∣ a j := by
    intro a ha j
    have hu := (h3 0 (smul_zero _)).unique (y₁ := fun j => (a j : ZMod p)) (y₂ := fun _ => 0)
      (by
        rw [← ha]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact (tateMat_val_smul (by simpa using h1 k 0) _).symm)
      (by simp)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun hu j)
  induction n with
  | zero => intro a ha j; simpa using base a ha j
  | succ n ih =>
    intro a ha j
    have hd := ih a (by rw [tateMat_step h2, ha, smul_zero])
    choose b hb using hd
    have := base b (by
      rw [← ha]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb k, tateMat_zero h2 k (n + 1), mul_comm, mul_smul, natCast_zsmul]) j
    rw [hb j, pow_succ p (n + 1)]
    push_cast
    exact mul_dvd_mul_left _ this

/- English proof (translation)
Use `tateMat_dvd h1 h2 h3 n (fun j => b j - a j) ?_ j` and prove the remaining obligations. Simplify using `only [sub_smul, Finset.sum_sub_distrib, h, sub_self]`.
-/
private theorem tateMat_congr (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) (n : ℕ)
    (a b : κ → ℤ) (h : ∑ j, a j • τ j n = ∑ j, b j • τ j n) (j : κ) :
    ((p ^ (n + 1) : ℕ) : ℤ) ∣ b j - a j := by
  refine tateMat_dvd h1 h2 h3 n (fun j => b j - a j) ?_ j
  simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]

/- English proof (translation)
Use `haveI : NeZero p := ⟨hp.out.ne_zero⟩`. Establish `hex : ∀ n, ∃ a : κ → ℤ, f (τ j n) = ∑ k, a k • τ k n` using `fun n => tateMat_exists h2 h3 n _ (by rw [← map_nsmul, h1, map_zero])`. Use `choose a ha using hex`. Establish `hc : ∀ k i, (p : ℤ) ^ i ∣ (fun i => a (i - 1) k) (i + 1) - (fun i => a (i - 1) k) i`. Introduce `k i`.

Consider the cases of `i with`. Consider the case `zero => simp`. Consider the case `succ m`. Use `tateMat_congr h1 h2 h3 m (a m) (a (m + 1)) (by` as an intermediate fact. Rewrite using `[← ha, tateMat_step h2, ← ha, ← map_nsmul, ← h2]) k`.

Simplify using `using this`. Use `⟨fun k => PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun i => a (i - 1) k) p (hc k)), fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[ha n]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun i => a (i - 1) k) p (hc k) (n + 1)]`.

Conclude with `(tateMat_val_smul (h1 k n) _).symm`.
-/
private theorem tateMat_limit (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0)
    (f : AddMonoid.End Γ) (j : κ) :
    ∃ c : κ → ℤ_[p], ∀ n, f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (c k)).val • τ k n := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hex : ∀ n, ∃ a : κ → ℤ, f (τ j n) = ∑ k, a k • τ k n := fun n =>
    tateMat_exists h2 h3 n _ (by rw [← map_nsmul, h1, map_zero])
  choose a ha using hex
  have hc : ∀ k i, (p : ℤ) ^ i ∣ (fun i => a (i - 1) k) (i + 1) - (fun i => a (i - 1) k) i := by
    intro k i
    cases i with
    | zero => simp
    | succ m =>
      have := tateMat_congr h1 h2 h3 m (a m) (a (m + 1)) (by
        rw [← ha, tateMat_step h2, ← ha, ← map_nsmul, ← h2]) k
      simpa using this
  refine ⟨fun k => PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun i => a (i - 1) k) p (hc k)), fun n => ?_⟩
  rw [ha n]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun i => a (i - 1) k) p (hc k) (n + 1)]
  exact (tateMat_val_smul (h1 k n) _).symm

/- English proof (translation)
Use `haveI : NeZero p := ⟨hp.out.ne_zero⟩`. Rewrite using `[← PadicInt.ext_of_toZModPow]`. Introduce `n`. Consider the cases of `n with`. Consider the case `zero => haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance`.

Conclude with `Subsingleton.elim _ _`. Consider the case `succ n`. Use `tateMat_congr h1 h2 h3 n (fun k => ((PadicInt.toZModPow (n + 1) (c k)).val : ℤ)) (b n) (by simpa only [natCast_zsmul] using h n) k` as an intermediate fact. Rewrite `this` using `[← ZMod.intCast_eq_intCast_iff_dvd_sub, hb]`. Simplify using `using this`.
-/
private theorem tateMat_unique (h1 : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (h2 : ∀ i n, τ i n = p • τ i (n + 1))
    (h3 : ∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0)
    (c d : κ → ℤ_[p]) (b : ℕ → κ → ℤ)
    (hb : ∀ n k, (b n k : ZMod (p ^ (n + 1))) = PadicInt.toZModPow (n + 1) (d k))
    (h : ∀ n, ∑ k, (PadicInt.toZModPow (n + 1) (c k)).val • τ k n = ∑ k, b n k • τ k n)
    (k : κ) : c k = d k := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    have := tateMat_congr h1 h2 h3 n
      (fun k => ((PadicInt.toZModPow (n + 1) (c k)).val : ℤ)) (b n)
      (by simpa only [natCast_zsmul] using h n) k
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, hb] at this
    simpa using this

end

/- English proof (translation)
Introduce `p hp κ Γ _ _ _ τ h1 h2 h3`. Use `haveI : NeZero p := ⟨hp.out.ne_zero⟩`. Use `⟨fun n x hx => ?_, ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `tateMat_exists h2 h3 n x hx`. Establish `key : ∀ t : κ → ZMod (p ^ (n + 1)), x = ∑ j, (t j).val • τ j n → t = fun j => (a j : ZMod (p ^ (n + 1)))`.

Introduce `t ht`. Use function extensionality and compare the values at `j`. Use `tateMat_congr h1 h2 h3 n (fun j => ((t j).val : ℤ)) a (by simpa only [natCast_zsmul, ← ha] using ht.symm) j` as an intermediate fact. Rewrite `this` using `[← ZMod.intCast_eq_intCast_iff_dvd_sub]`. Simplify using `using this`.

Use `⟨fun j => (a j : ZMod (p ^ (n + 1))), ?_, key⟩` and prove the remaining obligations. Rewrite using `[ha]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `(tateMat_val_smul (h1 k n) _).symm`. Use `choose c hc using tateMat_limit h1 h2 h3`.

Set `r : AddMonoid.End Γ → Matrix κ κ ℤ_[p]` to `fun f => Matrix.of fun k j => c f j k`. Establish `hr : ∀ f k j, r f k j = c f j k` using `fun _ _ _ => rfl`. Use `⟨⟨⟨⟨r, ?_⟩, ?_⟩, ?_, ?_⟩, fun f j n => hc f j n⟩` and prove the remaining obligations. Use extensionality with `k j`. Use `tateMat_unique h1 h2 h3 (c 1 j) (fun k => (1 : Matrix κ κ ℤ_[p]) k j) (fun _ k => if k = j then 1 else 0) (fun n k => ?_) (fun n => ?_) k` and prove the remaining obligations.

Apply the tactic sequence `by_cases h : k = j <;> simp [Matrix.one_apply, h]`. Rewrite using `[← hc]`. Simplify using the standard rewrite rules. Introduce `f g`. Use extensionality with `k j`.

Use `tateMat_unique h1 h2 h3 (c (f * g) j) (fun k => (r f * r g) k j) (fun n k => ∑ l, ((PadicInt.toZModPow (n + 1) (c f l k)).val : ℤ) * ((PadicInt.toZModPow (n + 1) (c g j l)).val : ℤ)) (fun n k => ?_) (fun n => ?_) k` and prove the remaining obligations. Simplify using `[Matrix.mul_apply, hr]`. Rewrite using `[← hc, AddMonoid.End.coe_mul, Function.comp_apply, hc g j n, map_sum]`. Simplify using `only [Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_nsmul, hc f l n, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul, natCast_zsmul, natCast_zsmul]`. Use extensionality with `k j`.

Use `tateMat_unique h1 h2 h3 (c 0 j) (fun _ => 0) (fun _ _ => 0) (fun n k => ?_) (fun n => ?_) k` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[← hc]`. Simplify using the standard rewrite rules. Introduce `f g`.

Use extensionality with `k j`. Use `tateMat_unique h1 h2 h3 (c (f + g) j) (fun k => c f j k + c g j k) (fun n k => ((PadicInt.toZModPow (n + 1) (c f j k)).val : ℤ) + ((PadicInt.toZModPow (n + 1) (c g j k)).val : ℤ)) (fun n k => ?_) (fun n => ?_) k` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[← hc]`. Simplify using `only [add_smul, Finset.sum_add_distrib, natCast_zsmul, ← hc]`.

Both sides reduce to the same expression.
-/
theorem tate_basis_matrix :
    (∀ (p : ℕ) [Fact p.Prime] (κ Γ : Type) [Fintype κ] [DecidableEq κ] [AddCommGroup Γ] (τ : κ → ℕ → Γ),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : Γ, p • x = 0 → ∃! t : κ → ZMod p, x = ∑ j, (t j).val • τ j 0) →
    (∀ n (x : Γ), (p ^ (n + 1)) • x = 0 → ∃! t : κ → ZMod (p ^ (n + 1)), x = ∑ j, (t j).val • τ j n) ∧
    ∃ ρ : AddMonoid.End Γ →+* Matrix κ κ ℤ_[p], ∀ (f : AddMonoid.End Γ) j n,
      f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (ρ f k j)).val • τ k n) := by
  intro p hp κ Γ _ _ _ τ h1 h2 h3
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine ⟨fun n x hx => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := tateMat_exists h2 h3 n x hx
    have key : ∀ t : κ → ZMod (p ^ (n + 1)), x = ∑ j, (t j).val • τ j n →
        t = fun j => (a j : ZMod (p ^ (n + 1))) := by
      intro t ht
      funext j
      have := tateMat_congr h1 h2 h3 n (fun j => ((t j).val : ℤ)) a
        (by simpa only [natCast_zsmul, ← ha] using ht.symm) j
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      simpa using this
    refine ⟨fun j => (a j : ZMod (p ^ (n + 1))), ?_, key⟩
    rw [ha]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (tateMat_val_smul (h1 k n) _).symm
  · choose c hc using tateMat_limit h1 h2 h3
    let r : AddMonoid.End Γ → Matrix κ κ ℤ_[p] := fun f => Matrix.of fun k j => c f j k
    have hr : ∀ f k j, r f k j = c f j k := fun _ _ _ => rfl
    refine ⟨⟨⟨⟨r, ?_⟩, ?_⟩, ?_, ?_⟩, fun f j n => hc f j n⟩
    · ext k j
      refine tateMat_unique h1 h2 h3 (c 1 j) (fun k => (1 : Matrix κ κ ℤ_[p]) k j)
        (fun _ k => if k = j then 1 else 0) (fun n k => ?_) (fun n => ?_) k
      · by_cases h : k = j <;> simp [Matrix.one_apply, h]
      · rw [← hc]; simp
    · intro f g
      ext k j
      refine tateMat_unique h1 h2 h3 (c (f * g) j) (fun k => (r f * r g) k j)
        (fun n k => ∑ l, ((PadicInt.toZModPow (n + 1) (c f l k)).val : ℤ) *
          ((PadicInt.toZModPow (n + 1) (c g j l)).val : ℤ)) (fun n k => ?_) (fun n => ?_) k
      · simp [Matrix.mul_apply, hr]
      · rw [← hc, AddMonoid.End.coe_mul, Function.comp_apply, hc g j n, map_sum]
        simp only [Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_nsmul, hc f l n, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_comm, mul_smul, natCast_zsmul, natCast_zsmul]
    · ext k j
      refine tateMat_unique h1 h2 h3 (c 0 j) (fun _ => 0)
        (fun _ _ => 0) (fun n k => ?_) (fun n => ?_) k
      · simp
      · rw [← hc]; simp
    · intro f g
      ext k j
      refine tateMat_unique h1 h2 h3 (c (f + g) j) (fun k => c f j k + c g j k)
        (fun n k => ((PadicInt.toZModPow (n + 1) (c f j k)).val : ℤ) +
          ((PadicInt.toZModPow (n + 1) (c g j k)).val : ℤ)) (fun n k => ?_) (fun n => ?_) k
      · simp
      · rw [← hc]
        simp only [add_smul, Finset.sum_add_distrib, natCast_zsmul, ← hc]
        rfl

end GlobalTheory

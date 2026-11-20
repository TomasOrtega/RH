import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.WeilBound.LevelCriteria.IsLevOneIff

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

namespace Pre

open GlobalTheory.PDA.Model TensorProduct

variable {B : Type} [CommRing B]

def liftL (c : ℕ → B) (h0 : c 0 = 1) (hm : ∀ m n, c m * c n = ((m + n).choose m : B) * c (m + n)) : L →ₐ[ℤ] B :=
  AlgHom.ofLinearMap (bL.constr ℤ c) (by rw [← bL_zero, Module.Basis.constr_basis, h0]) (by
    intro x y
    have key : (LinearMap.mul ℤ L).compr₂ (bL.constr ℤ c) =
        (LinearMap.mul ℤ B).compl₁₂ (bL.constr ℤ c) (bL.constr ℤ c) := by
      refine bL.ext fun m ↦ bL.ext fun n ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        Module.Basis.constr_basis, bL_mul]
      rw [← nsmul_eq_mul, map_nsmul, Module.Basis.constr_basis, nsmul_eq_mul, hm]
    exact congrArg (fun g ↦ g x y) key)

/- English proof (translation)
The claim follows from `bL.constr_basis ℤ c n`.
-/
theorem liftL_bL (c : ℕ → B) (h0 : c 0 = 1) (hm : ∀ m n, c m * c n = ((m + n).choose m : B) * c (m + n))
    (n : ℕ) : liftL c h0 hm (bL n) = c n := bL.constr_basis ℤ c n

/- English proof (translation)
Rewrite `h` using `[← nsmul_eq_mul, ← nsmul_eq_mul]`. Use `(bL.tensorProduct bL).repr.injective (Finsupp.ext fun i ↦ ?_)` and prove the remaining obligations. Use `congrArg (fun z ↦ (bL.tensorProduct bL).repr z i) h` as an intermediate fact. Simplify using `only [map_nsmul, Finsupp.smul_apply] at this`. Rewrite `this` using `[nsmul_eq_mul, nsmul_eq_mul]`.

Conclude with `mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) this`.
-/
theorem cancel {n : ℕ} (hn : n ≠ 0) {x y : L ⊗[ℤ] L} (h : (n : L ⊗[ℤ] L) * x = n * y) : x = y := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul] at h
  refine (bL.tensorProduct bL).repr.injective (Finsupp.ext fun i ↦ ?_)
  have := congrArg (fun z ↦ (bL.tensorProduct bL).repr z i) h
  simp only [map_nsmul, Finsupp.smul_apply] at this
  rw [nsmul_eq_mul, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) this

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [h0]`. Consider the case `succ n ih`. Rewrite using `[pow_succ', ← ih, mul_left_comm, hm, Nat.factorial_succ, add_comm 1 n]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fact_mul {D : Type} [CommRing D] (u : ℕ → D) (h0 : u 0 = 1)
    (hm : ∀ m n, u m * u n = ((m + n).choose m : D) * u (m + n)) (n : ℕ) :
    (n.factorial : D) * u n = u 1 ^ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [pow_succ', ← ih, mul_left_comm, hm, Nat.factorial_succ, add_comm 1 n]
    simp; ring

/- English proof (translation)
Rewrite using `[(Commute.all x y).add_pow', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k hk ↦ ?_` and prove the remaining obligations. Establish `hk' : k.1 + k.2 = m` using `by simpa using hk`. Rewrite using `[← hw, ← hw', ← hk', ← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]`. Use `push_cast`.

Rewrite using `[nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fact_sum {D : Type} [CommRing D] (x y : D) (w w' : ℕ → D) (hw : ∀ k, (k.factorial : D) * w k = x ^ k)
    (hw' : ∀ k, (k.factorial : D) * w' k = y ^ k) (m : ℕ) :
    (m.factorial : D) * ∑ k ∈ Finset.HasAntidiagonal.antidiagonal m, w k.1 * w' k.2 = (x + y) ^ m := by
  rw [(Commute.all x y).add_pow', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k.1 + k.2 = m := by simpa using hk
  rw [← hw, ← hw', ← hk', ← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
  push_cast
  rw [nsmul_eq_mul]; ring

/- English proof (translation)
Use `hc (n := n.factorial ^ m) (by positivity) ?_` and prove the remaining obligations. Establish `h` using `congrArg (Nat.cast : ℕ → D) (Nat.uniformBell_mul_eq m hn)`. Move the coercions through the operations in `at h ⊢`. Rewrite using `[← mul_pow, hz, ← pow_mul, mul_comm n m, ← hz, ← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eq_ub {D : Type} [CommRing D] (hc : ∀ {n : ℕ}, n ≠ 0 → ∀ {x y : D}, (n : D) * x = n * y → x = y)
    (t : D) (z : ℕ → D) (hz : ∀ k, (k.factorial : D) * z k = t ^ k) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (m.factorial : D) * ((m.uniformBell n : D) * z (m * n)) = z n ^ m := by
  refine hc (n := n.factorial ^ m) (by positivity) ?_
  have h := congrArg (Nat.cast : ℕ → D) (Nat.uniformBell_mul_eq m hn)
  push_cast at h ⊢
  rw [← mul_pow, hz, ← pow_mul, mul_comm n m, ← hz, ← h]; ring

/- English proof (translation)
Set `u : ℕ → L ⊗[ℤ] L` to `fun k ↦ bL k ⊗ₜ 1`. Set `v : ℕ → L ⊗[ℤ] L` to `fun k ↦ 1 ⊗ₜ bL k`. Establish `hu : ∀ k, (k.factorial : L ⊗[ℤ] L) * u k = u 1 ^ k` using `fact_mul u (by simp only [u, bL_zero]; rfl) fun i j ↦ by`. Simplify using `only [u, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bL_mul]`. Rewrite using `[← nsmul_eq_mul, ← nsmul_eq_mul, smul_tmul']`.

Establish `hv : ∀ k, (k.factorial : L ⊗[ℤ] L) * v k = v 1 ^ k` using `fact_mul v (by simp only [v, bL_zero]; rfl) fun i j ↦ by`. Simplify using `only [v, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bL_mul]`. Rewrite using `[← nsmul_eq_mul, ← nsmul_eq_mul, tmul_smul]`. Set `ψ : L ⊗[ℤ] L →ₐ[ℤ] B` to `Algebra.TensorProduct.lift (liftL (fun k ↦ γ k a) (H.zero a ha) fun i j ↦ H.mul_dpow i j a ha) (liftL (fun k ↦ γ k b) (H.zero b hb) fun i j ↦ H.mul_dpow i j b hb) fun _ _ ↦ Commute.all _ _`. Establish `ψu : ∀ k, ψ (u k) = γ k a` using `fun k ↦ by simp [ψ, u, liftL_bL]`.

Establish `ψv : ∀ k, ψ (v k) = γ k b` using `fun k ↦ by simp [ψ, v, liftL_bL]`. Set `W : Ideal (L ⊗[ℤ] L)` to `{ carrier := {z | ψ z ∈ J ∧ ∀ k : ℕ, ∃ w, (k.factorial : L ⊗[ℤ] L) * w = z ^ k ∧ ψ w = γ k (ψ z)} zero_mem' := ⟨by simp, fun k ↦ by`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Conclude with `⟨1, by simp, by rw [map_one, map_zero, H.zero _ J.zero_mem]⟩`. Use `⟨0, by simp [hk.ne'], ?_⟩` and prove the remaining obligations.

Use `H.mul k 0 0 J.zero_mem` as an intermediate fact. Rewrite `this` using `[mul_zero, zero_pow hk.ne', zero_mul]`. Rewrite using `[map_zero, this]⟩`. Use the proof step `add_mem' := fun {x y} hx hy ↦ ⟨by rw [map_add]; exact J.add_mem hx.1 hy.1, fun k ↦ by choose w hw hw' using hx.2 choose w₁ hw₁ hw₁' using hy.2`. Use `⟨_, fact_sum x y w w₁ hw hw₁ k, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, H.add k _ hx.1 _ hy.1, map_sum]`. Simplify using `only [map_mul, hw', hw₁']⟩`. Use the proof step `smul_mem' := fun c x hx ↦ ⟨by rw [smul_eq_mul, map_mul]; exact J.mul_mem_left _ hx.1, fun k ↦ by`. Take `⟨w, hw, hw'⟩` from `hx.2 k`. Use `⟨c ^ k * w, by rw [smul_eq_mul, mul_pow, ← hw]; ring, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_eq_mul, map_mul, map_mul, H.mul _ _ _ hx.1, hw', map_pow]⟩ }`. Establish `uW : ∀ i, i ≠ 0 → u i ∈ W` using `fun i hi ↦ ⟨by rw [ψu]; exact H.mem i hi a ha, fun k ↦ ⟨_, eq_ub cancel _ u hu k hi, by rw [map_mul, map_natCast, ψu, ψu, ka k i hi]⟩⟩`. Establish `vW : ∀ i, i ≠ 0 → v i ∈ W` using `fun i hi ↦ ⟨by rw [ψv]; exact H.mem i hi b hb, fun k ↦ ⟨_, eq_ub cancel _ v hv k hi, by rw [map_mul, map_natCast, ψv, ψv, kb k i hi]⟩⟩`. Set `z : ℕ → L ⊗[ℤ] L` to `fun k ↦ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, u p.1 * v p.2`. Establish `hz : ∀ k, (k.factorial : L ⊗[ℤ] L) * z k = (u 1 + v 1) ^ k` using `fact_sum _ _ u v hu hv`.

Establish `ψz : ∀ k, ψ (z k) = γ k (a + b)` using `fun k ↦ by`. Rewrite using `[H.add k a ha b hb, map_sum]`. Simplify using `only [map_mul, ψu, ψv]`. Establish `zW : z n ∈ W` using `Ideal.sum_mem _ fun p hp ↦ by`. Establish `hp' : p.1 + p.2 = n` using `by simpa using hp`.

Distinguish the cases in `h : p.1 = 0`. Conclude with `W.mul_mem_left _ (vW _ (by omega))`. Conclude with `W.mul_mem_right _ (uW _ h)`. Take `⟨w, hw, hw'⟩` from `zW.2 m`. Establish `e` using `cancel m.factorial_ne_zero (hw.trans (eq_ub cancel _ z hz m hn).symm)`.

Rewrite using `[← ψz n, ← hw', e, map_mul, map_natCast, ψz]`.
-/
theorem comp_add {J : Ideal B} {γ : ℕ → B → B} (H : IsPreDP J γ) {a b : B} (ha : a ∈ J) (hb : b ∈ J)
    (ka : ∀ m n : ℕ, n ≠ 0 → γ m (γ n a) = (m.uniformBell n : B) * γ (m * n) a)
    (kb : ∀ m n : ℕ, n ≠ 0 → γ m (γ n b) = (m.uniformBell n : B) * γ (m * n) b) (m n : ℕ) (hn : n ≠ 0) :
    γ m (γ n (a + b)) = (m.uniformBell n : B) * γ (m * n) (a + b) := by
  let u : ℕ → L ⊗[ℤ] L := fun k ↦ bL k ⊗ₜ 1
  let v : ℕ → L ⊗[ℤ] L := fun k ↦ 1 ⊗ₜ bL k
  have hu : ∀ k, (k.factorial : L ⊗[ℤ] L) * u k = u 1 ^ k := fact_mul u (by simp only [u, bL_zero]; rfl) fun i j ↦ by
    simp only [u, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bL_mul]
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, smul_tmul']
  have hv : ∀ k, (k.factorial : L ⊗[ℤ] L) * v k = v 1 ^ k := fact_mul v (by simp only [v, bL_zero]; rfl) fun i j ↦ by
    simp only [v, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bL_mul]
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, tmul_smul]
  let ψ : L ⊗[ℤ] L →ₐ[ℤ] B := Algebra.TensorProduct.lift
    (liftL (fun k ↦ γ k a) (H.zero a ha) fun i j ↦ H.mul_dpow i j a ha)
    (liftL (fun k ↦ γ k b) (H.zero b hb) fun i j ↦ H.mul_dpow i j b hb) fun _ _ ↦ Commute.all _ _
  have ψu : ∀ k, ψ (u k) = γ k a := fun k ↦ by simp [ψ, u, liftL_bL]
  have ψv : ∀ k, ψ (v k) = γ k b := fun k ↦ by simp [ψ, v, liftL_bL]
  let W : Ideal (L ⊗[ℤ] L) :=
    { carrier := {z | ψ z ∈ J ∧ ∀ k : ℕ, ∃ w, (k.factorial : L ⊗[ℤ] L) * w = z ^ k ∧ ψ w = γ k (ψ z)}
      zero_mem' := ⟨by simp, fun k ↦ by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact ⟨1, by simp, by rw [map_one, map_zero, H.zero _ J.zero_mem]⟩
        · refine ⟨0, by simp [hk.ne'], ?_⟩
          have := H.mul k 0 0 J.zero_mem
          rw [mul_zero, zero_pow hk.ne', zero_mul] at this
          rw [map_zero, this]⟩
      add_mem' := fun {x y} hx hy ↦ ⟨by rw [map_add]; exact J.add_mem hx.1 hy.1, fun k ↦ by
        choose w hw hw' using hx.2
        choose w₁ hw₁ hw₁' using hy.2
        refine ⟨_, fact_sum x y w w₁ hw hw₁ k, ?_⟩
        rw [map_add, H.add k _ hx.1 _ hy.1, map_sum]
        simp only [map_mul, hw', hw₁']⟩
      smul_mem' := fun c x hx ↦ ⟨by rw [smul_eq_mul, map_mul]; exact J.mul_mem_left _ hx.1, fun k ↦ by
        obtain ⟨w, hw, hw'⟩ := hx.2 k
        refine ⟨c ^ k * w, by rw [smul_eq_mul, mul_pow, ← hw]; ring, ?_⟩
        rw [smul_eq_mul, map_mul, map_mul, H.mul _ _ _ hx.1, hw', map_pow]⟩ }
  have uW : ∀ i, i ≠ 0 → u i ∈ W := fun i hi ↦ ⟨by rw [ψu]; exact H.mem i hi a ha, fun k ↦
    ⟨_, eq_ub cancel _ u hu k hi, by rw [map_mul, map_natCast, ψu, ψu, ka k i hi]⟩⟩
  have vW : ∀ i, i ≠ 0 → v i ∈ W := fun i hi ↦ ⟨by rw [ψv]; exact H.mem i hi b hb, fun k ↦
    ⟨_, eq_ub cancel _ v hv k hi, by rw [map_mul, map_natCast, ψv, ψv, kb k i hi]⟩⟩
  let z : ℕ → L ⊗[ℤ] L := fun k ↦ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, u p.1 * v p.2
  have hz : ∀ k, (k.factorial : L ⊗[ℤ] L) * z k = (u 1 + v 1) ^ k := fact_sum _ _ u v hu hv
  have ψz : ∀ k, ψ (z k) = γ k (a + b) := fun k ↦ by
    rw [H.add k a ha b hb, map_sum]; simp only [map_mul, ψu, ψv]
  have zW : z n ∈ W := Ideal.sum_mem _ fun p hp ↦ by
    have hp' : p.1 + p.2 = n := by simpa using hp
    by_cases h : p.1 = 0
    · exact W.mul_mem_left _ (vW _ (by omega))
    · exact W.mul_mem_right _ (uW _ h)
  obtain ⟨w, hw, hw'⟩ := zW.2 m
  have e := cancel m.factorial_ne_zero (hw.trans (eq_ub cancel _ z hz m hn).symm)
  rw [← ψz n, ← hw', e, map_mul, map_natCast, ψz]

end Pre

/- English proof (translation)
Introduce `B _ J γ s H hs h`. Establish `key : ∀ x ∈ J, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x`. Substitute `hs` using the available equality. Establish `smul : ∀ c, ∀ x ∈ Ideal.span s, (∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) → ∀ m n : ℕ, n ≠ 0 → γ m (γ n (c * x)) = (m.uniformBell n : B) * γ (m * n) (c * x)`. Introduce `c x hx ih m n hn`.

Rewrite using `[H.mul n c x hx, H.mul m _ _ (H.mem n hn x hx), ih m n hn, H.mul _ c x hx, ← pow_mul, mul_comm n m]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`.

Consider the case `zero`. Introduce `m n hn`. Establish `z : ∀ k, k ≠ 0 → γ k 0 = 0` using `fun k hk ↦ by`. Use `H.mul k 0 0 (Ideal.zero_mem _)` as an intermediate fact. Rewrite `this` using `[mul_zero, zero_pow hk, zero_mul]`. Then use the resulting hypothesis.

Rewrite using `[z n hn]`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Simplify using `[Nat.uniformBell_zero_left]`. Rewrite using `[z m hm.ne', z _ (Nat.mul_ne_zero hm.ne' hn), mul_zero]`. Consider the case `add x y hx hy ihx ihy => exact Pre.comp_add H hx hy ihx ihy`.

Consider the case `smul c x hx ih => exact smul c x hx ih`. Conclude with `⟨{ dpow := γ dpow_null := fun hx ↦ H.null _ _ hx dpow_zero := fun hx ↦ H.zero _ hx dpow_one := fun hx ↦ H.one _ hx dpow_mem := fun hn hx ↦ H.mem _ hn _ hx dpow_add := fun hx hy ↦ H.add _ _ hx _ hy dpow_mul := fun hx ↦ H.mul _ _ _ hx mul_dpow := fun hx ↦ H.mul_dpow _ _ _ hx dpow_c …`.
-/
theorem dp_of_pre' : ∀ (B : Type) [CommRing B] (J : Ideal B) (γ : ℕ → B → B) (s : Set B), IsPreDP J γ → J = Ideal.span s → (∀ x ∈ s, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) → ∃ δ : DividedPowers J, δ.dpow = γ := by
  intro B _ J γ s H hs h
  have key : ∀ x ∈ J, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x := by
    subst hs
    have smul : ∀ c, ∀ x ∈ Ideal.span s, (∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) →
        ∀ m n : ℕ, n ≠ 0 → γ m (γ n (c * x)) = (m.uniformBell n : B) * γ (m * n) (c * x) := by
      intro c x hx ih m n hn
      rw [H.mul n c x hx, H.mul m _ _ (H.mem n hn x hx), ih m n hn, H.mul _ c x hx, ← pow_mul, mul_comm n m]
      ring
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero =>
      intro m n hn
      have z : ∀ k, k ≠ 0 → γ k 0 = 0 := fun k hk ↦ by
        have := H.mul k 0 0 (Ideal.zero_mem _)
        rwa [mul_zero, zero_pow hk, zero_mul] at this
      rw [z n hn]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [Nat.uniformBell_zero_left]
      · rw [z m hm.ne', z _ (Nat.mul_ne_zero hm.ne' hn), mul_zero]
    | add x y hx hy ihx ihy => exact Pre.comp_add H hx hy ihx ihy
    | smul c x hx ih => exact smul c x hx ih
  exact ⟨{ dpow := γ
           dpow_null := fun hx ↦ H.null _ _ hx
           dpow_zero := fun hx ↦ H.zero _ hx
           dpow_one := fun hx ↦ H.one _ hx
           dpow_mem := fun hn hx ↦ H.mem _ hn _ hx
           dpow_add := fun hx hy ↦ H.add _ _ hx _ hy
           dpow_mul := fun hx ↦ H.mul _ _ _ hx
           mul_dpow := fun hx ↦ H.mul_dpow _ _ _ hx
           dpow_comp := fun hn hx ↦ key _ hx _ _ hn }, rfl⟩

end FubiniStudyChowHeightFormula₂.Adr

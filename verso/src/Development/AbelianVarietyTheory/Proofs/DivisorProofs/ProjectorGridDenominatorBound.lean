import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut.GridIntProof

variable {V : Type} [AddCommGroup V] [Module ℚ V]

/- English proof (translation)
Establish `hc : Commute (LinearMap.mulLeft ℚ x) ((-1 : ℚ) • LinearMap.mulRight ℚ x)` using `(LinearMap.commute_mulLeft_right x x).smul_right _`. Establish `h1 : adj x = LinearMap.mulLeft ℚ x + (-1 : ℚ) • LinearMap.mulRight ℚ x`. Simplify using `[adj, sub_eq_add_neg]`. Rewrite using `[h1, hc.add_pow, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations.

Rewrite using `[smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]`. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul ℚ, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]`.
-/
theorem adj_pow_apply (x U : Module.End ℚ V) (k : ℕ) :
    (adj x ^ k) U = ∑ t ∈ Finset.range (k + 1),
      (((-1 : ℚ) ^ (k - t) * (k.choose t : ℚ)) • (x ^ t * U * x ^ (k - t))) := by
  have hc : Commute (LinearMap.mulLeft ℚ x) ((-1 : ℚ) • LinearMap.mulRight ℚ x) :=
    (LinearMap.commute_mulLeft_right x x).smul_right _
  have h1 : adj x = LinearMap.mulLeft ℚ x + (-1 : ℚ) • LinearMap.mulRight ℚ x := by
    simp [adj, sub_eq_add_neg]
  rw [h1, hc.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul ℚ, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]

def IntOn (L M : Submodule ℤ V) (c : ℕ) (U : Module.End ℚ V) : Prop := ∀ x ∈ L, ((c : ℕ) : ℤ) • U x ∈ M

/- English proof (translation)
Introduce `y hy`. Establish `hE : ((c : ℕ) : ℤ) • (((k.factorial : ℚ)⁻¹ • (adj e ^ k) U) y) = ∑ t ∈ Finset.range (k + 1), ((-1 : ℤ) ^ (k - t)) • ((t.factorial : ℚ)⁻¹ • (e ^ t) (((c : ℕ) : ℤ) • U (((k - t).factorial : ℚ)⁻¹ • (e ^ (k - t)) y)))`. Rewrite using `[LinearMap.smul_apply, adj_pow_apply, LinearMap.sum_apply, Finset.smul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Establish `ht' : t ≤ k` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)`.

Establish `hch` using `Nat.choose_mul_factorial_mul_factorial ht'`. Simplify using `only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, LinearMap.sum_apply, Finset.smul_sum]`. Use `congr 1`. Establish `h1 : ((k.choose t : ℕ) : ℚ) * (t.factorial : ℚ) * ((k - t).factorial : ℚ) = (k.factorial : ℚ)`. Conclude with `hch` after adjusting the coercions.

Establish `h2 : (t.factorial : ℚ) ≠ 0` using `by positivity`. Establish `h3 : ((k - t).factorial : ℚ) ≠ 0` using `by positivity`. Establish `h4 : (k.factorial : ℚ) ≠ 0` using `by positivity`. Establish `h5 : ((k.choose t : ℕ) : ℚ) ≠ 0` using `by exact_mod_cast (Nat.choose_pos ht').ne'`. Rewrite using `[← h1]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hE]`. Use `Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `hM t _ (hU _ (hL (k - t) y hy))`.
-/
theorem intOn_divAdj (L M : Submodule ℤ V) (e : Module.End ℚ V)
    (hL : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (e ^ k) x ∈ L)
    (hM : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (e ^ k) x ∈ M)
    (c : ℕ) (U : Module.End ℚ V) (hU : IntOn L M c U) (k : ℕ) :
    IntOn L M c (((k.factorial : ℚ)⁻¹) • (adj e ^ k) U) := by
  intro y hy
  have hE : ((c : ℕ) : ℤ) • (((k.factorial : ℚ)⁻¹ • (adj e ^ k) U) y) =
      ∑ t ∈ Finset.range (k + 1), ((-1 : ℤ) ^ (k - t)) • ((t.factorial : ℚ)⁻¹ •
        (e ^ t) (((c : ℕ) : ℤ) • U (((k - t).factorial : ℚ)⁻¹ • (e ^ (k - t)) y))) := by
    rw [LinearMap.smul_apply, adj_pow_apply, LinearMap.sum_apply, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have hch := Nat.choose_mul_factorial_mul_factorial ht'
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      LinearMap.sum_apply, Finset.smul_sum]
    congr 1
    have h1 : ((k.choose t : ℕ) : ℚ) * (t.factorial : ℚ) * ((k - t).factorial : ℚ) = (k.factorial : ℚ) := by
      exact_mod_cast hch
    have h2 : (t.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((k - t).factorial : ℚ) ≠ 0 := by positivity
    have h4 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h5 : ((k.choose t : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos ht').ne'
    rw [← h1]
    push_cast
    field_simp
  rw [hE]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
  exact hM t _ (hU _ (hL (k - t) y hy))

/- English proof (translation)
Introduce `y hy`. Simplify using `only [proj, LinearMap.sum_apply, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun k hk => ?_` and prove the remaining obligations. Establish `hkK : k ≤ K` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)`. Take `⟨m, hm⟩` from `hΛ k hkK`.

Establish `hE : ((c * Λ : ℕ) : ℤ) • ((coef j₀ k • (adj Y ^ k * adj X ^ k)) U) y = ((-1 : ℤ) ^ k * (m : ℤ)) • (((c : ℕ) : ℤ) • (((k.factorial : ℚ)⁻¹ • (adj Y ^ k) ((k.factorial : ℚ)⁻¹ • (adj X ^ k) U)) y))`. Simplify using `only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]`. Use `congr 1`. Establish `h2 : (j₀.factorial : ℚ) ≠ 0` using `by positivity`. Establish `h3 : (k.factorial : ℚ) ≠ 0` using `by positivity`.

Establish `h4 : ((j₀ + k + 1).factorial : ℚ) ≠ 0` using `by positivity`. Establish `hΛq : (Λ : ℚ) = ((j₀ + k + 1).factorial : ℚ) * (m : ℚ) / ((j₀.factorial : ℚ) * (k.factorial : ℚ))`. Rewrite using `[eq_div_iff (by positivity)]`. Conclude with `hm` after adjusting the coercions. Establish `hkj : k + j₀ + 1 = j₀ + k + 1` using `by omega`.

Simplify using `only [coef, hkj]`. Use `push_cast`. Rewrite using `[hΛq]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hE]`.

Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `intOn_divAdj L M Y hLY hMY c _ (intOn_divAdj L M X hLX hMX c U hU k) k y hy`.
-/
theorem intOn_proj (L M : Submodule ℤ V) (X Y : Module.End ℚ V)
    (hLX : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (X ^ k) x ∈ L)
    (hMX : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (X ^ k) x ∈ M)
    (hLY : ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (Y ^ k) x ∈ L)
    (hMY : ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : ℚ)⁻¹) • (Y ^ k) x ∈ M)
    (K j₀ Λ : ℕ) (hΛ : ∀ k ≤ K, (j₀ + k + 1).factorial ∣ Λ * (j₀.factorial * k.factorial))
    (c : ℕ) (U : Module.End ℚ V) (hU : IntOn L M c U) :
    IntOn L M (c * Λ) (proj K j₀ (adj X) (adj Y) U) := by
  intro y hy
  simp only [proj, LinearMap.sum_apply, Finset.smul_sum]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨m, hm⟩ := hΛ k hkK
  have hE : ((c * Λ : ℕ) : ℤ) • ((coef j₀ k • (adj Y ^ k * adj X ^ k)) U) y =
      ((-1 : ℤ) ^ k * (m : ℤ)) • (((c : ℕ) : ℤ) • (((k.factorial : ℚ)⁻¹ • (adj Y ^ k)
        ((k.factorial : ℚ)⁻¹ • (adj X ^ k) U)) y)) := by
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    have h2 : (j₀.factorial : ℚ) ≠ 0 := by positivity
    have h3 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h4 : ((j₀ + k + 1).factorial : ℚ) ≠ 0 := by positivity
    have hΛq : (Λ : ℚ) = ((j₀ + k + 1).factorial : ℚ) * (m : ℚ) / ((j₀.factorial : ℚ) * (k.factorial : ℚ)) := by
      rw [eq_div_iff (by positivity)]
      exact_mod_cast hm
    have hkj : k + j₀ + 1 = j₀ + k + 1 := by omega
    simp only [coef, hkj]
    push_cast
    rw [hΛq]
    field_simp
  rw [hE]
  refine Submodule.smul_mem _ _ ?_
  exact intOn_divAdj L M Y hLY hMY c _ (intOn_divAdj L M X hLX hMX c U hU k) k y hy

/- English proof (translation)
The claim follows from `| [], _, c, U, hU => by simpa using hU | f :: l, hf, c, U, hU => by rw [List.prod_cons, Module.End.mul_apply, List.length_cons, pow_succ, ← mul_assoc] exact hf f (List.mem_cons_self ..) _ _ (intOn_listProd L M n l (fun g hg => hf g (List.mem_cons_of_mem _ hg)) c U hU)`.
-/
theorem intOn_listProd (L M : Submodule ℤ V) (n : ℕ) :
    ∀ (l : List (Module.End ℚ (Module.End ℚ V))), (∀ f ∈ l, ∀ c U, IntOn L M c U → IntOn L M (c * n) (f U)) →
      ∀ c U, IntOn L M c U → IntOn L M (c * n ^ l.length) (l.prod U)
  | [], _, c, U, hU => by simpa using hU
  | f :: l, hf, c, U, hU => by
      rw [List.prod_cons, Module.End.mul_apply, List.length_cons, pow_succ, ← mul_assoc]
      exact hf f (List.mem_cons_self ..) _ _
        (intOn_listProd L M n l (fun g hg => hf g (List.mem_cons_of_mem _ hg)) c U hU)

end GlobalTheory.LeviCut.GridIntProof

namespace GlobalTheory.LeviCut

open GridIntProof in

/- English proof (translation)
Introduce `V _ _ a b K w Λ e L M hL hM hw hΛ c T hT`. Establish `hstep : ∀ i < a, ∀ j, a ≤ j → j < a + b → ∀ (c : ℕ) (U : Module.End ℚ V), IntOn L M c U → IntOn L M (c * Λ) (rootP (fun c d => adj (e c d)) K i j U)`. Introduce `i hi j hj1 hj2 c U hU`. Establish `hij : i ≠ j` using `by omega`. Establish `hji : j ≠ i` using `by omega`.

Conclude with `intOn_proj L M (e i j) (e j i) (fun k x hx => hL i (by omega) j hj2 hij k x hx) (fun k x hx => hM i (by omega) j hj2 hij k x hx) (fun k x hx => hL j hj2 i (by omega) hji k x hx) (fun k x hx => hM j hj2 i (by omega) hji k x hx) K (j - i - 1) Λ (fun k hk => hΛ _ _ (by omega)) c U h …`. Establish `hrow : ∀ i < a, ∀ (c : ℕ) (U : Module.End ℚ V), IntOn L M c U → IntOn L M (c * Λ ^ b) (rowP (fun c d => adj (e c d)) K i a b U)`. Introduce `i hi c U hU`. Establish `h` using `intOn_listProd L M Λ ((List.range' a b).map (rootP (fun c d => adj (e c d)) K i)) (by`. Introduce `f hf`.

Rewrite `hf` using `[List.mem_map]`. Take `⟨j, hj, rfl⟩` from `hf`. Rewrite `hj` using `[List.mem_range'_1]`. Conclude with `hstep i hi j hj.1 hj.2) c U hU`. Simplify `h` using `[rowP]`.

Establish `h` using `intOn_listProd L M (Λ ^ b) ((List.range a).reverse.map fun i => rowP (fun c d => adj (e c d)) K i a b) (by`. Introduce `f hf`. Rewrite `hf` using `[List.mem_map]`. Take `⟨i, hi, rfl⟩` from `hf`. Rewrite `hi` using `[List.mem_reverse, List.mem_range]`.

Conclude with `hrow i hi) c T hT`. Establish `e1 : (Λ ^ b) ^ ((List.range a).reverse.map fun i => rowP (fun c d => adj (e c d)) K i a b).length = Λ ^ (a * b)`. Simplify using `[← pow_mul, mul_comm]`. Rewrite `h` using `[e1]`. Conclude with `h`.
-/
theorem gridInt_holds : GridInt := by
  intro V _ _ a b K w Λ e L M hL hM hw hΛ c T hT
  have hstep : ∀ i < a, ∀ j, a ≤ j → j < a + b → ∀ (c : ℕ) (U : Module.End ℚ V), IntOn L M c U →
      IntOn L M (c * Λ) (rootP (fun c d => adj (e c d)) K i j U) := by
    intro i hi j hj1 hj2 c U hU
    have hij : i ≠ j := by omega
    have hji : j ≠ i := by omega
    exact intOn_proj L M (e i j) (e j i) (fun k x hx => hL i (by omega) j hj2 hij k x hx)
      (fun k x hx => hM i (by omega) j hj2 hij k x hx) (fun k x hx => hL j hj2 i (by omega) hji k x hx)
      (fun k x hx => hM j hj2 i (by omega) hji k x hx) K (j - i - 1) Λ (fun k hk => hΛ _ _ (by omega)) c U hU
  have hrow : ∀ i < a, ∀ (c : ℕ) (U : Module.End ℚ V), IntOn L M c U →
      IntOn L M (c * Λ ^ b) (rowP (fun c d => adj (e c d)) K i a b U) := by
    intro i hi c U hU
    have h := intOn_listProd L M Λ ((List.range' a b).map (rootP (fun c d => adj (e c d)) K i)) (by
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      rw [List.mem_range'_1] at hj
      exact hstep i hi j hj.1 hj.2) c U hU
    simpa [rowP] using h
  have h := intOn_listProd L M (Λ ^ b) ((List.range a).reverse.map fun i => rowP (fun c d => adj (e c d)) K i a b)
    (by
      intro f hf
      rw [List.mem_map] at hf
      obtain ⟨i, hi, rfl⟩ := hf
      rw [List.mem_reverse, List.mem_range] at hi
      exact hrow i hi) c T hT
  have e1 : (Λ ^ b) ^ ((List.range a).reverse.map fun i => rowP (fun c d => adj (e c d)) K i a b).length =
      Λ ^ (a * b) := by
    simp [← pow_mul, mul_comm]
  rw [e1] at h
  exact h

end GlobalTheory.LeviCut

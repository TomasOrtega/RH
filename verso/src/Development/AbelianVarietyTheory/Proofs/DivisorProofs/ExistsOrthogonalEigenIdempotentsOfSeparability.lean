import Mathlib
open scoped TensorProduct

namespace GlobalTheory.LieIdempotents

/- English proof (translation)
Establish `hB : ∀ (r : ℤ) (m n : K), B (r • m) n = B m (r • n)`. Introduce `r m n`. Rewrite using `[map_zsmul, map_zsmul]`. Both sides reduce to the same expression. Use `congrArg (TensorProduct.liftAddHom B hB) (hyp c)` as an intermediate fact.

Simplify `this` using `[map_sum, TensorProduct.liftAddHom_tmul]`.
-/
theorem balanced_apply {K : Type} {M : Type*} [CommRing K] [AddCommGroup M] (k : ℕ) (u v : Fin k → K)
    (hyp : ∀ c : K, ∑ j, (c * u j) ⊗ₜ[ℤ] v j = ∑ j, u j ⊗ₜ[ℤ] (v j * c))
    (B : K →+ K →+ M) (c : K) : ∑ j, B (c * u j) (v j) = ∑ j, B (u j) (v j * c) := by
  have hB : ∀ (r : ℤ) (m n : K), B (r • m) n = B m (r • n) := by
    intro r m n; rw [map_zsmul, map_zsmul]; rfl
  have := congrArg (TensorProduct.liftAddHom B hB) (hyp c)
  simpa [map_sum, TensorProduct.liftAddHom_tmul] using this

end GlobalTheory.LieIdempotents

open GlobalTheory.LieIdempotents in
/- English proof (translation)
Introduce `R C K _ _ _ tR a t hcom N k u v huv hyp hN H _ _ ρF`. Use `set n : C := ((hN.unit⁻¹ : Cˣ) : C) with hn`. Establish `hnN : n * (N : C) = 1` using `hN.val_inv_mul`. Establish `hS : ∀ p q, ∑ j, t p (u j) * t q (v j) = if p = q then (N : R) else 0`. Introduce `p q`.

Use `split_ifs with hpq`. Substitute `hpq` using the available equality. Simplify using `only [← map_mul, ← map_sum, huv, map_intCast]`. Use `set S := ∑ j, t p (u j) * t q (v j) with hSdef`. Set `B : K →+ K →+ R` to `AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => t p x * t q y) (by intro y y'; simp [mul_add])) (by intro x x'; ext y; simp [add_mul])`.

Establish `hc : ∀ c, t p c * S = S * t q c`. Introduce `c`. Use `balanced_apply k u v hyp B c` as an intermediate fact. Simplify using `only [B, AddMonoidHom.mk'_apply, map_mul] at this`. Rewrite using `[hSdef, Finset.mul_sum, Finset.sum_mul]`.

Apply the tactic sequence `convert this using 2 <;> ring`. Establish `hle : Ideal.span (Set.range fun x => t p x - t q x) ≤ LinearMap.ker (LinearMap.mulLeft R S)`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply]`.

Rewrite using `[mul_sub, mul_comm S, hc, sub_self]`. Rewrite `hle` using `[hcom p q hpq]`. Establish `h1 : (1 : R) ∈ LinearMap.ker (LinearMap.mulLeft R S)` using `hle Submodule.mem_top`. Simplify using `using h1`. Establish `hSC : ∀ p q, ∑ j, tR (t p (u j)) * tR (t q (v j)) = if p = q then (N : C) else 0`.

Introduce `p q`. Use `congrArg tR (hS p q)` as an intermediate fact. Simplify using `only [map_sum, map_mul] at this`. Apply the tactic sequence `rw [this]; split_ifs <;> simp`. Establish `hnNx : ∀ x : Module.End C H, n • (N : C) • x = x`.

Introduce `x`. Rewrite using `[smul_smul, hnN, one_smul]`. Establish `heig : ∀ i c, ρF c * (n • ∑ j, tR (t i (v j)) • ρF (u j)) = tR (t i c) • (n • ∑ j, tR (t i (v j)) • ρF (u j))`. Introduce `i c`. Set `B : K →+ K →+ Module.End C H` to `AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => tR (t i y) • ρF x) (by intro y y'; simp [add_smul])) (by intro x x'; ext y : 1; simp [smul_add])`.

Establish `hb` using `balanced_apply k u v hyp B c`. Simplify using `only [B, AddMonoidHom.mk'_apply, map_mul] at hb`. Rewrite using `[mul_smul_comm, Finset.mul_sum]`. Simplify using `only [mul_smul_comm]`. Rewrite using `[hb, smul_comm (tR (t i c)) n]`.

Simplify using `only [Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[smul_smul, mul_comm]`. Use `⟨fun i => n • ∑ j, tR (t i (v j)) • ρF (u j), heig, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j`. Simplify using `only`. Generalize the expression as in `hΦ : n • ∑ l, tR (t j (v l)) • ρF (u l) = Φ at heig`. Establish `hj` using `heig j`. Rewrite `hj` using `[hΦ]`.

Rewrite using `[smul_mul_assoc, Finset.sum_mul]`. Simplify using `only [smul_mul_assoc, hj, smul_smul, ← Finset.sum_smul]`. Establish `hsum : ∑ l, tR (t i (v l)) * tR (t j (u l)) = ∑ l, tR (t j (u l)) * tR (t i (v l))` using `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Rewrite using `[hsum, hSC j i]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, hnN, one_smul]`. Conclude with `hΦ.symm`. Simplify using `[hij, Ne.symm hij]`. Introduce `g hg i`.

Simplify using `only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, hg]`. Introduce `F hF i x hx`. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply]`. Conclude with `F.smul_mem _ (F.sum_mem fun l _ => F.smul_mem _ (hF _ _ hx))`. Introduce `F hF i w hw j`.

Establish `e : (n • ∑ l, tR (t j (v l)) • ρF (u l)) w - (if j = i then w else 0) = n • ∑ l, tR (t j (v l)) • (ρF (u l) w - tR (t i (u l)) • w)`. Establish `hite : (if j = i then w else 0) = n • (∑ l, tR (t i (u l)) * tR (t j (v l))) • w`. Rewrite using `[hSC i j]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `[smul_smul, hnN]`. Simplify using `[hij, Ne.symm hij]`. Rewrite using `[hite]`. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Put the polynomial expressions in normal form. Rewrite using `[e]`. Conclude with `F.smul_mem _ (F.sum_mem fun l _ => F.smul_mem _ (hw _))`.
-/
theorem GlobalTheory.lie_idempotents : ∀ (R C K : Type) [CommRing R] [CommRing C] [CommRing K] (tR : R →+* C) (a : ℕ) (t : Fin a → (K →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∀ (N : ℤ) (k : ℕ) (u v : Fin k → K), ∑ j, u j * v j = (N : K) → (∀ c : K, ∑ j, (c * u j) ⊗ₜ[ℤ] v j = ∑ j, u j ⊗ₜ[ℤ] (v j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρF : K →+* Module.End C H), ∃ φ : Fin a → Module.End C H, (∀ i c, ρF c * φ i = tR (t i c) • φ i) ∧ (∀ i j, φ i * φ j = if i = j then φ i else 0) ∧ (∀ g : Module.End C H, (∀ c, g * ρF c = ρF c * g) → ∀ i, g * φ i = φ i * g) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i, ∀ x ∈ F, φ i x ∈ F) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i w, (∀ c, ρF c w - tR (t i c) • w ∈ F) → ∀ j, φ j w - (if j = i then w else 0) ∈ F) := by
  intro R C K _ _ _ tR a t hcom N k u v huv hyp hN H _ _ ρF
  set n : C := ((hN.unit⁻¹ : Cˣ) : C) with hn
  have hnN : n * (N : C) = 1 := hN.val_inv_mul

  have hS : ∀ p q, ∑ j, t p (u j) * t q (v j) = if p = q then (N : R) else 0 := by
    intro p q
    split_ifs with hpq
    · subst hpq
      simp only [← map_mul, ← map_sum, huv, map_intCast]
    · set S := ∑ j, t p (u j) * t q (v j) with hSdef
      let B : K →+ K →+ R := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => t p x * t q y)
        (by intro y y'; simp [mul_add])) (by intro x x'; ext y; simp [add_mul])
      have hc : ∀ c, t p c * S = S * t q c := by
        intro c
        have := balanced_apply k u v hyp B c
        simp only [B, AddMonoidHom.mk'_apply, map_mul] at this
        rw [hSdef, Finset.mul_sum, Finset.sum_mul]
        convert this using 2 <;> ring
      have hle : Ideal.span (Set.range fun x => t p x - t q x) ≤ LinearMap.ker (LinearMap.mulLeft R S) := by
        rw [Ideal.span_le]
        rintro _ ⟨x, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply]
        rw [mul_sub, mul_comm S, hc, sub_self]
      rw [hcom p q hpq] at hle
      have h1 : (1 : R) ∈ LinearMap.ker (LinearMap.mulLeft R S) := hle Submodule.mem_top
      simpa using h1
  have hSC : ∀ p q, ∑ j, tR (t p (u j)) * tR (t q (v j)) = if p = q then (N : C) else 0 := by
    intro p q
    have := congrArg tR (hS p q)
    simp only [map_sum, map_mul] at this
    rw [this]; split_ifs <;> simp
  have hnNx : ∀ x : Module.End C H, n • (N : C) • x = x := by
    intro x; rw [smul_smul, hnN, one_smul]
  have heig : ∀ i c, ρF c * (n • ∑ j, tR (t i (v j)) • ρF (u j)) = tR (t i c) • (n • ∑ j, tR (t i (v j)) • ρF (u j)) := by
    intro i c
    let B : K →+ K →+ Module.End C H := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => tR (t i y) • ρF x)
        (by intro y y'; simp [add_smul])) (by intro x x'; ext y : 1; simp [smul_add])
    have hb := balanced_apply k u v hyp B c
    simp only [B, AddMonoidHom.mk'_apply, map_mul] at hb
    rw [mul_smul_comm, Finset.mul_sum]
    simp only [mul_smul_comm]
    rw [hb, smul_comm (tR (t i c)) n]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [smul_smul, mul_comm]
  refine ⟨fun i => n • ∑ j, tR (t i (v j)) • ρF (u j), heig, ?_, ?_, ?_, ?_⟩
  ·
    intro i j
    dsimp only
    generalize hΦ : n • ∑ l, tR (t j (v l)) • ρF (u l) = Φ at heig
    have hj := heig j
    rw [hΦ] at hj
    rw [smul_mul_assoc, Finset.sum_mul]
    simp only [smul_mul_assoc, hj, smul_smul, ← Finset.sum_smul]
    have hsum : ∑ l, tR (t i (v l)) * tR (t j (u l)) = ∑ l, tR (t j (u l)) * tR (t i (v l)) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [hsum, hSC j i]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl, hnN, one_smul]; exact hΦ.symm
    · simp [hij, Ne.symm hij]
  · intro g hg i
    simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, hg]
  · intro F hF i x hx
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    exact F.smul_mem _ (F.sum_mem fun l _ => F.smul_mem _ (hF _ _ hx))
  · intro F hF i w hw j
    have e : (n • ∑ l, tR (t j (v l)) • ρF (u l)) w - (if j = i then w else 0)
        = n • ∑ l, tR (t j (v l)) • (ρF (u l) w - tR (t i (u l)) • w) := by
      have hite : (if j = i then w else 0) = n • (∑ l, tR (t i (u l)) * tR (t j (v l))) • w := by
        rw [hSC i j]; by_cases hij : i = j
        · subst hij; simp [smul_smul, hnN]
        · simp [hij, Ne.symm hij]
      rw [hite]
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, Finset.smul_sum, smul_smul]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      ring_nf
    rw [e]
    exact F.smul_mem _ (F.sum_mem fun l _ => F.smul_mem _ (hw _))

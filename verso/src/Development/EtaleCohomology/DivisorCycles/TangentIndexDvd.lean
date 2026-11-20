import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb
namespace TangentIndexDvd

section
variable {C : Type} [Field C] {N : ℕ}

/- English proof (translation)
Introduce `_ hx _ hf` and use `hf _ hx`.
-/
theorem subset_zcl (S : Set (Mat C N)) : S ⊆ Zcl S := fun _ hx _ hf => hf _ hx

/- English proof (translation)
Simplify using `only [ev, map_mul]`.
-/
theorem ev_mul (x : Mat C N) (f g : MP C N) : ev x (f * g) = ev x f * ev x g := by
  simp only [ev, map_mul]

/- English proof (translation)
Simplify using `only [ev, map_prod]`.
-/
theorem ev_prod {ι : Type} (s : Finset ι) (x : Mat C N) (q : ι → MP C N) :
    ev x (∏ c ∈ s, q c) = ∏ c ∈ s, ev x (q c) := by
  simp only [ev, map_prod]

/- English proof (translation)
Unfold `dAt`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz]`. Simplify using `only [ev, smul_eq_mul, map_add, map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dAt_mul (f g : MP C N) (x Y : Mat C N) :
    dAt (f * g) x Y = ev x f * dAt g x Y + ev x g * dAt f x Y := by
  unfold dAt
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Derivation.leibniz]
  simp only [ev, smul_eq_mul, map_add, map_mul]
  ring

/- English proof (translation)
Simplify using `[img, Submonoid.mem_map]`.
-/
theorem mem_img {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (U : Subgroup Γ) (x : Mat C N) :
    x ∈ img ρ U ↔ ∃ u ∈ U, ((ρ u : GL (Fin N) C) : Mat C N) = x := by
  simp [img, Submonoid.mem_map]

/- English proof (translation)
Distinguish the cases in `h : ∃ q : MP C N, ev 1 q ≠ 0 ∧ ∀ γ : Γ, (γ : Γ ⧸ U) = (g : Γ ⧸ U) → ev ((ρ γ : GL (Fin N) C) : Mat C N) q = 0`. Take `⟨q, hq1, hq⟩` from `h`. Conclude with `⟨q, hq1, fun γ hγ => by rw [ev_mul, hq γ hγ, mul_zero]⟩`. Establish `h' : ∀ q : MP C N, (∀ γ : Γ, (γ : Γ ⧸ U) = (g : Γ ⧸ U) → ev ((ρ γ : GL (Fin N) C) : Mat C N) q = 0) → ev 1 q = 0` using `fun q hq => by`. Assume the negation of the conclusion as `hne`.

Conclude with `h ⟨q, hne, hq⟩`. Establish `hinv : ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ∈ Zcl (img ρ U : Set (Mat C N))`. Introduce `h0 hh0`. Take `⟨h1, hev, -⟩` from `hChain C N N (LinearMap.mulLeft C ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) h0`. Establish `key` using `h' h1 (fun γ hγ => by`.

Rewrite using `[hev, LinearMap.mulLeft_apply]`. Apply `hh0` to reduce the goal to its premises. Rewrite using `[SetLike.mem_coe, mem_img]`. Use `⟨g⁻¹ * γ, QuotientGroup.eq.mp hγ.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Units.val_mul])`.

Rewrite `key` using `[hev, LinearMap.mulLeft_apply, mul_one]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨k, hk, hkU⟩ : ∃ k : ℕ, 0 < k ∧ g ^ k ∈ U := by`. Establish `: Finite (Γ ⧸ U)` using `Subgroup.finite_quotient_of_finiteIndex`. Use `⟨orderOf (g : Γ ⧸ U), orderOf_pos _, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]`.

Establish `hpow : ∀ m : ℕ, ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ^ m ∈ Zcl (img ρ U : Set (Mat C N))`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero]`. Conclude with `subset_zcl _ (img ρ U).one_mem`.

Consider the case `succ m ih => rw [pow_succ]`. Conclude with `hMul C N _ _ ih _ hinv`. Establish `hg : ((ρ g : GL (Fin N) C) : Mat C N) ∈ Zcl (img ρ U : Set (Mat C N))`. Establish `e : ((ρ g : GL (Fin N) C) : Mat C N) = ((ρ (g ^ k) : GL (Fin N) C) : Mat C N) * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ^ (k - 1)`. Rewrite using `[← Units.val_pow_eq_pow_val, ← Units.val_mul, ← map_pow, ← map_mul]`.

Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Use `congr 2`. Simplify using `[pow_succ', mul_assoc, inv_pow]`. Rewrite using `[e]`. Conclude with `hMul C N _ _ (subset_zcl _ ((mem_img ρ U _).2 ⟨_, hkU, rfl⟩)) _ (hpow _)`.

Use `⟨1, by simp [ev], fun γ hγ => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_one]`. Establish `hγU : g⁻¹ * γ ∈ U` using `QuotientGroup.eq.mp hγ.symm`. Establish `e : ((ρ γ : GL (Fin N) C) : Mat C N) = ((ρ g : GL (Fin N) C) : Mat C N) * ((ρ (g⁻¹ * γ) : GL (Fin N) C) : Mat C N)`. Rewrite using `[← Units.val_mul, ← map_mul, mul_inv_cancel_left]`.

Rewrite using `[e]`. Conclude with `hMul C N _ _ hg _ (subset_zcl _ ((mem_img ρ U _).2 ⟨_, hγU, rfl⟩)) f hf`.
-/
theorem coset_poly {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (U : Subgroup Γ) [U.Normal]
    [U.FiniteIndex] (hChain : Chain) (hMul : ZclMul) (f : MP C N)
    (hf : f ∈ Van (img ρ U : Set (Mat C N))) (g : Γ) :
    ∃ q : MP C N, ev 1 q ≠ 0 ∧ ∀ γ : Γ, (γ : Γ ⧸ U) = (g : Γ ⧸ U) →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) (f * q) = 0 := by
  by_cases h : ∃ q : MP C N, ev 1 q ≠ 0 ∧ ∀ γ : Γ, (γ : Γ ⧸ U) = (g : Γ ⧸ U) →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) q = 0
  · obtain ⟨q, hq1, hq⟩ := h
    exact ⟨q, hq1, fun γ hγ => by rw [ev_mul, hq γ hγ, mul_zero]⟩
  have h' : ∀ q : MP C N, (∀ γ : Γ, (γ : Γ ⧸ U) = (g : Γ ⧸ U) →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) q = 0) → ev 1 q = 0 := fun q hq => by
    by_contra hne; exact h ⟨q, hne, hq⟩
  have hinv : ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ∈ Zcl (img ρ U : Set (Mat C N)) := by
    intro h0 hh0
    obtain ⟨h1, hev, -⟩ := hChain C N N (LinearMap.mulLeft C ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) h0
    have key := h' h1 (fun γ hγ => by
      rw [hev, LinearMap.mulLeft_apply]
      apply hh0
      rw [SetLike.mem_coe, mem_img]
      refine ⟨g⁻¹ * γ, QuotientGroup.eq.mp hγ.symm, ?_⟩
      rw [map_mul, Units.val_mul])
    rwa [hev, LinearMap.mulLeft_apply, mul_one] at key
  obtain ⟨k, hk, hkU⟩ : ∃ k : ℕ, 0 < k ∧ g ^ k ∈ U := by
    have : Finite (Γ ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
    refine ⟨orderOf (g : Γ ⧸ U), orderOf_pos _, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
  have hpow : ∀ m : ℕ, ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ^ m ∈ Zcl (img ρ U : Set (Mat C N)) := by
    intro m
    induction m with
    | zero => rw [pow_zero]; exact subset_zcl _ (img ρ U).one_mem
    | succ m ih => rw [pow_succ]; exact hMul C N _ _ ih _ hinv
  have hg : ((ρ g : GL (Fin N) C) : Mat C N) ∈ Zcl (img ρ U : Set (Mat C N)) := by
    have e : ((ρ g : GL (Fin N) C) : Mat C N) = ((ρ (g ^ k) : GL (Fin N) C) : Mat C N) *
        ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ^ (k - 1) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← map_pow, ← map_mul]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      congr 2
      simp [pow_succ', mul_assoc, inv_pow]
    rw [e]
    exact hMul C N _ _ (subset_zcl _ ((mem_img ρ U _).2 ⟨_, hkU, rfl⟩)) _ (hpow _)
  refine ⟨1, by simp [ev], fun γ hγ => ?_⟩
  rw [mul_one]
  have hγU : g⁻¹ * γ ∈ U := QuotientGroup.eq.mp hγ.symm
  have e : ((ρ γ : GL (Fin N) C) : Mat C N) = ((ρ g : GL (Fin N) C) : Mat C N) *
      ((ρ (g⁻¹ * γ) : GL (Fin N) C) : Mat C N) := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  rw [e]
  exact hMul C N _ _ hg _ (subset_zcl _ ((mem_img ρ U _).2 ⟨_, hγU, rfl⟩)) f hf

end

/- English proof (translation)
Introduce `Γ C _ _ N ρ U hN hU Y hY`. Establish `: Finite (Γ ⧸ U)` using `Subgroup.finite_quotient_of_finiteIndex`. Use `haveI : Fintype (Γ ⧸ U) := Fintype.ofFinite _`. Establish `hY' : ∀ F ∈ Van (img ρ ⊤ : Set (Mat C N)), dAt F 1 Y = 0` using `hY`. Use `show ∀ f ∈ Van (img ρ U : Set (Mat C N)), dAt f 1 Y = 0`.

Introduce `f hf`. Establish `hc : ∀ c : Γ ⧸ U, ∃ q : MP C N, ev 1 q ≠ 0 ∧ ∀ γ : Γ, (γ : Γ ⧸ U) = c → ev ((ρ γ : GL (Fin N) C) : Mat C N) (f * q) = 0`. Introduce `c`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective c`. Conclude with `coset_poly ρ U hChain hMul f hf g`.

Use `choose q hq1 hq using hc`. Establish `hF : f * ∏ c, q c ∈ Van (img ρ ⊤ : Set (Mat C N))`. Introduce `x hx`. Take `⟨γ, -, rfl⟩` from `(mem_img ρ ⊤ x).1 hx`. Establish `h0` using `hq (γ : Γ ⧸ U) γ rfl`.

Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ (γ : Γ ⧸ U)), ← mul_assoc, ev_mul, h0, zero_mul]`. Establish `key` using `hY' _ hF`. Rewrite `key` using `[dAt_mul]`. Establish `hf1 : ev 1 f = 0` using `hf 1 (img ρ U).one_mem`. Establish `hG1 : ev 1 (∏ c, q c) ≠ 0`.

Rewrite using `[ev_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 fun c _ => hq1 c`. Rewrite `key` using `[hf1, zero_mul, zero_add]`. Conclude with `(mul_eq_zero.1 key).resolve_left hG1`.
-/
theorem TanIndex_of (hChain : Chain) (hMul : ZclMul) : TanIndex := by
  classical
  intro Γ C _ _ N ρ U hN hU Y hY
  have : Finite (Γ ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ U) := Fintype.ofFinite _
  have hY' : ∀ F ∈ Van (img ρ ⊤ : Set (Mat C N)), dAt F 1 Y = 0 := hY
  show ∀ f ∈ Van (img ρ U : Set (Mat C N)), dAt f 1 Y = 0
  intro f hf
  have hc : ∀ c : Γ ⧸ U, ∃ q : MP C N, ev 1 q ≠ 0 ∧ ∀ γ : Γ, (γ : Γ ⧸ U) = c →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) (f * q) = 0 := by
    intro c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    exact coset_poly ρ U hChain hMul f hf g
  choose q hq1 hq using hc
  have hF : f * ∏ c, q c ∈ Van (img ρ ⊤ : Set (Mat C N)) := by
    intro x hx
    obtain ⟨γ, -, rfl⟩ := (mem_img ρ ⊤ x).1 hx
    have h0 := hq (γ : Γ ⧸ U) γ rfl
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (γ : Γ ⧸ U)), ← mul_assoc,
      ev_mul, h0, zero_mul]
  have key := hY' _ hF
  rw [dAt_mul] at key
  have hf1 : ev 1 f = 0 := hf 1 (img ρ U).one_mem
  have hG1 : ev 1 (∏ c, q c) ≠ 0 := by
    rw [ev_prod]; exact Finset.prod_ne_zero_iff.2 fun c _ => hq1 c
  rw [hf1, zero_mul, zero_add] at key
  exact (mul_eq_zero.1 key).resolve_left hG1

end TangentIndexDvd
end LateralTheory.DivDb

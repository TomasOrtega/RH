import ReciprocityTheory.DualLattices.ExistsReductionOfCoordinateCombination

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Lift1

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)

def avgF (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H) (i : Fin U.m) (c₀ : R)
    (F : Nb p g → C) (y : Nb p g) : C :=
  ∑ γ, algebraMap R C (c₀ * U.sg i (β γ⁻¹)) * F (nbAct H (β γ) y)

/- English proof (translation)
Establish `hsum : avgF β H U i c₀ F = ∑ γ, (c₀ * U.sg i (β γ⁻¹)) • (fun y => F (nbAct H (β γ) y))`. Use function extensionality and compare the values at `y`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply]`. Simplify using `only [avgF, Algebra.smul_def]`.

Rewrite using `[hsum]`. Conclude with `Submodule.sum_mem _ fun γ _ => Submodule.smul_mem _ _ (comp_mem H _ hF)`.
-/
lemma avgF_mem {H : HodgeTateDatum p g v R O σ cp} (U : UnramData p g v R O σ cp H) (i : Fin U.m) (c₀ : R)
    {F : Nb p g → C} (hF : F ∈ H.AA.carrier) : avgF β H U i c₀ F ∈ H.AA.carrier := by
  have hsum : avgF β H U i c₀ F = ∑ γ, (c₀ * U.sg i (β γ⁻¹)) • (fun y => F (nbAct H (β γ) y)) := by
    funext y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    simp only [avgF, Algebra.smul_def]
  rw [hsum]
  exact Submodule.sum_mem _ fun γ _ => Submodule.smul_mem _ _ (comp_mem H _ hF)

/- English proof (translation)
Rewrite using `[nbAct, nbAct, nbAct, hmul, Matrix.map_mul, Matrix.mulVec_mulVec]`.
-/
lemma nbAct_mul {H : HodgeTateDatum p g v R O σ cp}
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (γ δ : G) (y : Nb p g) :
    nbAct H (β (γ * δ)) y = nbAct H (β γ) (nbAct H (β δ) y) := by
  rw [nbAct, nbAct, nbAct, hmul, Matrix.map_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Establish `hnz : NoZeroDivisors R` using `hS.integers.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)`. Assume the negation of the conclusion as `hne`. Apply `hM` to reduce the goal to its premises. Use extensionality with `k l`. Establish `h` using `congrFun (congrFun hs k) l`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h`. Break down `mul_eq_zero.mp h with h' | h'` into its components or cases. Conclude with `absurd h' hne`. Simplify using `using h'`.
-/
private lemma smul_cancel_lemma (hS : HodgeTateSetting p v R O σ cp) {M : Matrix (Ix g) (Ix g) R}
    (hM : M ≠ 0) (s : R) (hs : s • M = 0) : s = 0 := by
  have hnz : NoZeroDivisors R := hS.integers.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  by_contra hne
  apply hM
  ext k l
  have h := congrFun (congrFun hs k) l
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hne
  · simpa using h'

/- English proof (translation)
Apply `sub_eq_zero.mp` to reduce the goal to its premises. Apply `smul_cancel_lemma hS hi` to reduce the goal to its premises. Establish `e1` using `U.εT_eig (β (γ * γ')) i`. Rewrite `e1` using `[hmul, Matrix.map_mul, Matrix.mul_assoc, U.εT_eig, Matrix.mul_smul, U.εT_eig, smul_smul]`. Rewrite using `[sub_smul, ← e1, mul_comm, sub_self]`.
-/
private lemma sg_mul_lemma_2 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ'))
    {i : Fin U.m} (hi : U.εT i ≠ 0) (γ γ' : G) :
    U.sg i (β (γ * γ')) = U.sg i (β γ) * U.sg i (β γ') := by
  apply sub_eq_zero.mp
  apply smul_cancel_lemma hS hi
  have e1 := U.εT_eig (β (γ * γ')) i
  rw [hmul, Matrix.map_mul, Matrix.mul_assoc, U.εT_eig, Matrix.mul_smul, U.εT_eig, smul_smul] at e1
  rw [sub_smul, ← e1, mul_comm, sub_self]

/- English proof (translation)
Apply `sub_eq_zero.mp` to reduce the goal to its premises. Apply `smul_cancel_lemma hS hi` to reduce the goal to its premises. Establish `e1` using `U.εT_eig (β 1) i`. Rewrite `e1` using `[h1, Matrix.map_one (algebraMap ℤ_[p] R) (map_zero _) (map_one _), Matrix.one_mul]`. Rewrite using `[sub_smul, ← e1, one_smul, sub_self]`.
-/
private lemma sg_one_lemma_3 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0) : U.sg i (β 1) = 1 := by
  apply sub_eq_zero.mp
  apply smul_cancel_lemma hS hi
  have e1 := U.εT_eig (β 1) i
  rw [h1, Matrix.map_one (algebraMap ℤ_[p] R) (map_zero _) (map_one _), Matrix.one_mul] at e1
  rw [sub_smul, ← e1, one_smul, sub_self]

/- English proof (translation)
Rewrite using `[← sg_mul_lemma_2 β hS U hmul hi, mul_inv_cancel, sg_one_lemma_3 β hS U h1 hi]`.
-/
private lemma sg_inv_lemma_4 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0) (γ : G) : U.sg i (β γ) * U.sg i (β γ⁻¹) = 1 := by
  rw [← sg_mul_lemma_2 β hS U hmul hi, mul_inv_cancel, sg_one_lemma_3 β hS U h1 hi]

/- English proof (translation)
Establish `hx : ∀ γ, F (nbAct H (β γ) (nbAct H (β δ) y)) = F (nbAct H (β (γ * δ)) y)` using `fun γ => by`. Rewrite using `[nbAct_mul β hmul]`. Simplify using `only [avgF, hx]`. Rewrite using `[Finset.mul_sum]`. Use `Fintype.sum_equiv (Equiv.mulRight δ) _ _ fun γ => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.coe_mulRight]`. Rewrite using `[_root_.mul_inv_rev, sg_mul_lemma_2 β hS U hmul hi δ⁻¹ γ⁻¹, ← mul_assoc, ← map_mul]`. Use `congr 2`. Take the linear combination `(-(c₀ * U.sg i (β γ⁻¹))) * sg_inv_lemma_4 β hS U hmul h1 hi δ`.
-/
lemma avgF_eig (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0) (c₀ : R) (F : Nb p g → C) (δ : G) (y : Nb p g) :
    avgF β H U i c₀ F (nbAct H (β δ) y) =
      algebraMap R C (U.sg i (β δ)) * avgF β H U i c₀ F y := by
  have hx : ∀ γ, F (nbAct H (β γ) (nbAct H (β δ) y)) = F (nbAct H (β (γ * δ)) y) := fun γ => by
    rw [nbAct_mul β hmul]
  simp only [avgF, hx]
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight δ) _ _ fun γ => ?_
  simp only [Equiv.coe_mulRight]
  rw [_root_.mul_inv_rev, sg_mul_lemma_2 β hS U hmul hi δ⁻¹ γ⁻¹, ← mul_assoc, ← map_mul]
  congr 2
  linear_combination (-(c₀ * U.sg i (β γ⁻¹))) * sg_inv_lemma_4 β hS U hmul h1 hi δ

/- English proof (translation)
Take `⟨δ, hδ⟩` from `hnt`. Establish `he` using `avgF_eig β hS U hmul h1 hi c₀ F δ 0`. Rewrite `he` using `[show nbAct H (β δ) 0 = 0 from Matrix.mulVec_zero _]`. Establish `hne : algebraMap R C (U.sg i (β δ)) - 1 ≠ 0`. Introduce `h0`.

Rewrite `hδ` using `[map_sub, map_one, h0, map_zero]`. Conclude with `zero_ne_one hδ`. Establish `hm : (algebraMap R C (U.sg i (β δ)) - 1) * avgF β H U i c₀ F 0 = 0`. Rewrite using `[sub_mul, ← he, one_mul, sub_self]`. Conclude with `(mul_eq_zero.mp hm).resolve_left hne`.
-/
lemma avgF_zero (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0)
    (hnt : ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1) (c₀ : R) (F : Nb p g → C) :
    avgF β H U i c₀ F 0 = 0 := by
  obtain ⟨δ, hδ⟩ := hnt
  have he := avgF_eig β hS U hmul h1 hi c₀ F δ 0
  rw [show nbAct H (β δ) 0 = 0 from Matrix.mulVec_zero _] at he
  have hne : algebraMap R C (U.sg i (β δ)) - 1 ≠ 0 := by
    intro h0
    rw [map_sub, map_one, h0, map_zero] at hδ
    exact zero_ne_one hδ
  have hm : (algebraMap R C (U.sg i (β δ)) - 1) * avgF β H U i c₀ F 0 = 0 := by
    rw [sub_mul, ← he, one_mul, sub_self]
  exact (mul_eq_zero.mp hm).resolve_left hne

/- English proof (translation)
Establish `hnz : NoZeroDivisors R` using `hS.integers.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)`. Take `⟨δ, hδ⟩` from `hsep i k hi hk hik`. Establish `hne : U.sg i (β δ) - U.sg k (β δ) ≠ 0`. Introduce `h0`. Rewrite `hδ` using `[h0, map_zero, map_zero]`.

Conclude with `zero_ne_one hδ`. Establish `hA` using `sg_inv_lemma_4 β hS U hmul h1 hi δ`. Establish `hB` using `sg_inv_lemma_4 β hS U hmul h1 hk δ`. Use `set S := ∑ γ, U.sg i (β γ⁻¹) * U.sg k (β γ) with hSdef`. Establish `hshift : S = U.sg i (β δ⁻¹) * U.sg k (β δ) * S`.

Rewrite using `[hSdef, Finset.mul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft δ⁻¹) _ _ fun γ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft, _root_.mul_inv_rev, inv_inv, sg_mul_lemma_2 β hS U hmul hi, sg_mul_lemma_2 β hS U hmul hk]`. Take the linear combination `(-(U.sg i (β γ⁻¹) * U.sg k (β γ))) * hA + (-(U.sg i (β γ⁻¹) * U.sg k (β γ) * (U.sg i (β δ) * U.sg i (β δ⁻¹)))) * hB`. Establish `hm : (U.sg i (β δ) - U.sg k (β δ)) * S = 0`.

Take the linear combination `(U.sg i (β δ)) * hshift + (U.sg k (β δ) * S) * hA`. Conclude with `(mul_eq_zero.mp hm).resolve_left hne`.
-/
private lemma orth_lemma_5 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    {i k : Fin U.m} (hi : U.εT i ≠ 0) (hk : U.εT k ≠ 0) (hik : i ≠ k) :
    ∑ γ, U.sg i (β γ⁻¹) * U.sg k (β γ) = 0 := by
  have hnz : NoZeroDivisors R := hS.integers.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  obtain ⟨δ, hδ⟩ := hsep i k hi hk hik
  have hne : U.sg i (β δ) - U.sg k (β δ) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hδ
    exact zero_ne_one hδ
  have hA := sg_inv_lemma_4 β hS U hmul h1 hi δ
  have hB := sg_inv_lemma_4 β hS U hmul h1 hk δ
  set S := ∑ γ, U.sg i (β γ⁻¹) * U.sg k (β γ) with hSdef
  have hshift : S = U.sg i (β δ⁻¹) * U.sg k (β δ) * S := by
    rw [hSdef, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft δ⁻¹) _ _ fun γ => ?_
    simp only [Equiv.coe_mulLeft, _root_.mul_inv_rev, inv_inv, sg_mul_lemma_2 β hS U hmul hi,
      sg_mul_lemma_2 β hS U hmul hk]
    linear_combination (-(U.sg i (β γ⁻¹) * U.sg k (β γ))) * hA +
      (-(U.sg i (β γ⁻¹) * U.sg k (β γ) * (U.sg i (β δ) * U.sg i (β δ⁻¹)))) * hB
  have hm : (U.sg i (β δ) - U.sg k (β δ)) * S = 0 := by
    linear_combination (U.sg i (β δ)) * hshift + (U.sg k (β δ) * S) * hA
  exact (mul_eq_zero.mp hm).resolve_left hne

/- English proof (translation)
Establish `hA : ∀ γ, (H.ρ (β γ)).map (algebraMap ℤ_[p] R) = ∑ j, U.sg j (β γ) • U.εT j`. Introduce `γ`. Establish `h` using `congrArg (fun M => (H.ρ (β γ)).map (algebraMap ℤ_[p] R) * M) U.εT_sum`. Simplify using `only [Matrix.mul_one, Matrix.mul_sum] at h`. Rewrite using `[← h]`.

Conclude with `Finset.sum_congr rfl fun j _ => U.εT_eig _ j`. Repeatedly rewrite using `[hA, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm, Finset.sum_eq_single i]`. Rewrite using `[← Finset.sum_smul]`. Establish `hc : ∀ γ, U.sg i (β γ⁻¹) * U.sg i (β γ) = 1` using `fun γ => by`.

Rewrite using `[mul_comm]`. Conclude with `sg_inv_lemma_4 β hS U hmul h1 hi γ`. Establish `hsum : ∑ γ, ((hcardG.unit⁻¹ : Rˣ) : R) * U.sg i (β γ⁻¹) * U.sg i (β γ) = 1`. Repeatedly rewrite using `[mul_assoc, ← Finset.mul_sum, hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]`. Conclude with `hcardG.val_inv_mul`.

Rewrite using `[hsum, one_smul]`. Introduce `j _ hji`. Distinguish the cases in `hj : U.εT j = 0`. Simplify using `[hj]`. Rewrite using `[← Finset.sum_smul]`.

Establish `hsum : ∑ γ, ((hcardG.unit⁻¹ : Rˣ) : R) * U.sg i (β γ⁻¹) * U.sg j (β γ) = 0`. Repeatedly rewrite using `[mul_assoc, ← Finset.mul_sum]`. Rewrite using `[orth_lemma_5 β hS U hmul h1 hsep hi hj (Ne.symm hji), mul_zero]`. Rewrite using `[hsum, zero_smul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`.
-/
private lemma proj_lemma_6 (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    (hcardG : IsUnit (Fintype.card G : R)) {i : Fin U.m} (hi : U.εT i ≠ 0) :
    ∑ γ, (((hcardG.unit⁻¹ : Rˣ) : R) * U.sg i (β γ⁻¹)) • (H.ρ (β γ)).map (algebraMap ℤ_[p] R) =
      U.εT i := by
  have hA : ∀ γ, (H.ρ (β γ)).map (algebraMap ℤ_[p] R) = ∑ j, U.sg j (β γ) • U.εT j := by
    intro γ
    have h := congrArg (fun M => (H.ρ (β γ)).map (algebraMap ℤ_[p] R) * M) U.εT_sum
    simp only [Matrix.mul_one, Matrix.mul_sum] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => U.εT_eig _ j
  simp_rw [hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Finset.sum_eq_single i]
  · rw [← Finset.sum_smul]
    have hc : ∀ γ, U.sg i (β γ⁻¹) * U.sg i (β γ) = 1 := fun γ => by
      rw [mul_comm]
      exact sg_inv_lemma_4 β hS U hmul h1 hi γ
    have hsum : ∑ γ, ((hcardG.unit⁻¹ : Rˣ) : R) * U.sg i (β γ⁻¹) * U.sg i (β γ) = 1 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one]
      exact hcardG.val_inv_mul
    rw [hsum, one_smul]
  · intro j _ hji
    by_cases hj : U.εT j = 0
    · simp [hj]
    · rw [← Finset.sum_smul]
      have hsum : ∑ γ, ((hcardG.unit⁻¹ : Rˣ) : R) * U.sg i (β γ⁻¹) * U.sg j (β γ) = 0 := by
        simp_rw [mul_assoc, ← Finset.mul_sum]
        rw [orth_lemma_5 β hS U hmul h1 hsep hi hj (Ne.symm hji), mul_zero]
      rw [hsum, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Use `choose r hr using hF`. Use `set c : R := ((hcardG.unit⁻¹ : Rˣ) : R) with hc`. Use `set T : Ix g → R := algebraMap ℤ_[p] R ∘ t with hT`. Establish `hF' : ∀ γ, F (nbAct H (β γ) (red p g t)) = algebraMap R C ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T) - algebraMap R C (p * r (H.ρ (β γ) *ᵥ t))`. Introduce `γ`.

Establish `h2 : (algebraMap ℤ_[p] R ∘ (H.ρ (β γ) *ᵥ t)) = (H.ρ (β γ)).map (algebraMap ℤ_[p] R) *ᵥ T`. Use function extensionality and compare the values at `k`. Conclude with `RingHom.map_mulVec _ _ _ k`. Rewrite using `[← red_mulVec, ← Matrix.dotProduct_mulVec, ← h2]`. Take the linear combination `-(hr (H.ρ (β γ) *ᵥ t))`.

Set `L : Matrix (Ix g) (Ix g) R →ₗ[R] R` to `{ toFun := fun M => (Lr ᵥ* M) ⬝ᵥ T map_add' := fun M N => by simp only [Matrix.vecMul_add, add_dotProduct] map_smul' := fun a M => by simp only [Matrix.vecMul_smul, smul_dotProduct, RingHom.id_apply] }`. Establish `hLε : (Lr ᵥ* U.εT i) ⬝ᵥ T = ∑ γ, (c * U.sg i (β γ⁻¹)) * ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T)`. Establish `h` using `congrArg L (proj_lemma_6 β hS U hmul h1 hsep hcardG hi)`. Rewrite `h` using `[map_sum]`. Simplify using `only [map_smul, smul_eq_mul] at h`.

Conclude with `h.symm`. Use `⟨-(∑ γ, c * U.sg i (β γ⁻¹) * r (H.ρ (β γ) *ᵥ t)), ?_⟩` and prove the remaining obligations. Use `show ∑ γ, algebraMap R C (c * U.sg i (β γ⁻¹)) * F (nbAct H (β γ) (red p g t)) - _ = _`. Simplify using `only [hF']`. Rewrite using `[hLε]`.

Establish `hmap : ∑ γ, algebraMap R C (c * U.sg i (β γ⁻¹)) * (algebraMap R C ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T) - algebraMap R C (p * r (H.ρ (β γ) *ᵥ t))) = algebraMap R C (∑ γ, c * U.sg i (β γ⁻¹) * ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T - p * r (H.ρ (β γ) *ᵥ t) …`. Simplify using `only [map_sum, map_mul, map_sub]`. Rewrite using `[hmap, ← map_sub]`. Use `congr 1`. Establish `e : ∑ γ, c * U.sg i (β γ⁻¹) * (p * r (H.ρ (β γ) *ᵥ t)) = (p : R) * ∑ γ, c * U.sg i (β γ⁻¹) * r (H.ρ (β γ) *ᵥ t)`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma avgF_cong (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    (hcardG : IsUnit (Fintype.card G : R)) {i : Fin U.m} (hi : U.εT i ≠ 0) (Lr : Ix g → R)
    (F : Nb p g → C) (hF : ∀ t : TT p g, ∃ r : R,
      algebraMap R C (Lr ⬝ᵥ (algebraMap ℤ_[p] R ∘ t)) - F (red p g t) = algebraMap R C (p * r))
    (t : TT p g) : ∃ r : R, avgF β H U i (hcardG.unit⁻¹ : Rˣ) F (red p g t) -
      algebraMap R C ((Lr ᵥ* U.εT i) ⬝ᵥ (algebraMap ℤ_[p] R ∘ t)) = algebraMap R C (p * r) := by
  choose r hr using hF
  set c : R := ((hcardG.unit⁻¹ : Rˣ) : R) with hc
  set T : Ix g → R := algebraMap ℤ_[p] R ∘ t with hT
  have hF' : ∀ γ, F (nbAct H (β γ) (red p g t)) =
      algebraMap R C ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T) -
        algebraMap R C (p * r (H.ρ (β γ) *ᵥ t)) := by
    intro γ
    have h2 : (algebraMap ℤ_[p] R ∘ (H.ρ (β γ) *ᵥ t)) =
        (H.ρ (β γ)).map (algebraMap ℤ_[p] R) *ᵥ T := by
      funext k
      exact RingHom.map_mulVec _ _ _ k
    rw [← red_mulVec, ← Matrix.dotProduct_mulVec, ← h2]
    linear_combination -(hr (H.ρ (β γ) *ᵥ t))
  let L : Matrix (Ix g) (Ix g) R →ₗ[R] R :=
    { toFun := fun M => (Lr ᵥ* M) ⬝ᵥ T
      map_add' := fun M N => by simp only [Matrix.vecMul_add, add_dotProduct]
      map_smul' := fun a M => by simp only [Matrix.vecMul_smul, smul_dotProduct, RingHom.id_apply] }
  have hLε : (Lr ᵥ* U.εT i) ⬝ᵥ T =
      ∑ γ, (c * U.sg i (β γ⁻¹)) * ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T) := by
    have h := congrArg L (proj_lemma_6 β hS U hmul h1 hsep hcardG hi)
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    exact h.symm
  refine ⟨-(∑ γ, c * U.sg i (β γ⁻¹) * r (H.ρ (β γ) *ᵥ t)), ?_⟩
  show ∑ γ, algebraMap R C (c * U.sg i (β γ⁻¹)) * F (nbAct H (β γ) (red p g t)) - _ = _
  simp only [hF']
  rw [hLε]
  have hmap : ∑ γ, algebraMap R C (c * U.sg i (β γ⁻¹)) *
      (algebraMap R C ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T) -
        algebraMap R C (p * r (H.ρ (β γ) *ᵥ t))) =
      algebraMap R C (∑ γ, c * U.sg i (β γ⁻¹) *
        ((Lr ᵥ* (H.ρ (β γ)).map (algebraMap ℤ_[p] R)) ⬝ᵥ T - p * r (H.ρ (β γ) *ᵥ t))) := by
    simp only [map_sum, map_mul, map_sub]
  rw [hmap, ← map_sub]
  congr 1
  have e : ∑ γ, c * U.sg i (β γ⁻¹) * (p * r (H.ρ (β γ) *ᵥ t)) =
      (p : R) * ∑ γ, c * U.sg i (β γ⁻¹) * r (H.ρ (β γ) *ᵥ t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [e]
  ring

/- English proof (translation)
Take `⟨c', hc'⟩` from `hdiv`. Use `choose fH hfH hrH using fun k => (H.h4 k).1`. Use `choose fB hfB hrB using fun k => (H.h4 k).2`. Use `choose rH hrH' using hrH`. Use `choose rB hrB' using hrB`.

Take `⟨F, hFdef⟩ : ∃ F : Nb p g → C, F = ∑ k, wH k • fH k + ∑ k, wB k • fB k` from `⟨_, rfl⟩`. Establish `hFmem : F ∈ H.AA.carrier`. Rewrite using `[hFdef]`. Conclude with `H.AA.carrier.add_mem (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hfH k)) (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hfB k))`. Establish `hFcong : ∀ t : TT p g, ∃ r : R, algebraMap R C ((wH ᵥ* H.Ht + wB ᵥ* H.Bt) ⬝ᵥ (algebraMap ℤ_[p] R ∘ t)) - F (red p g t) = algebraMap R C (p * r)`.

Introduce `t`. Use `⟨∑ k, wH k * rH k t + ∑ k, wB k * rB k t, ?_⟩` and prove the remaining obligations. Establish `hFt : F (red p g t) = ∑ k, algebraMap R C (wH k) * fH k (red p g t) + ∑ k, algebraMap R C (wB k) * fB k (red p g t)`. Rewrite using `[hFdef, Pi.add_apply, Finset.sum_apply, Finset.sum_apply]`. Simplify using `only [Pi.smul_apply]`.

Simplify using `only [Algebra.smul_def]`. Establish `hfH'' : ∀ k, fH k (red p g t) = algebraMap R C ((H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) - algebraMap R C (p * rH k t)` using `fun k => by linear_combination -(hrH' k t)`. Establish `hfB'' : ∀ k, fB k (red p g t) = algebraMap R C ((H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) - algebraMap R C (p * rB k t)` using `fun k => by linear_combination -(hrB' k t)`. Establish `hLT : (wH ᵥ* H.Ht + wB ᵥ* H.Bt) ⬝ᵥ (algebraMap ℤ_[p] R ∘ t) = ∑ k, wH k * (H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k + ∑ k, wB k * (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k`. Rewrite using `[add_dotProduct, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec]`.

Both sides reduce to the same expression. Rewrite using `[hFt, hLT]`. Simplify using `only [hfH'', hfB'']`. Establish `hmap : (∑ k, algebraMap R C (wH k) * (algebraMap R C ((H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) - algebraMap R C (p * rH k t)) + ∑ k, algebraMap R C (wB k) * (algebraMap R C ((H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) - algebraMap R C (p * rB k t))) = algebraMap R C (∑ k, wH k * ((H.Ht *ᵥ …`. Simplify using `only [map_add, map_sum, map_mul, map_sub]`.

Rewrite using `[hmap, ← map_sub]`. Use `congr 1`. Establish `e1 : ∑ k, wH k * (p * rH k t) = (p : R) * ∑ k, wH k * rH k t`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.

Establish `e2 : ∑ k, wB k * (p * rB k t) = (p : R) * ∑ k, wB k * rB k t`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[e1, e2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hAmem : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F ∈ H.AA.carrier` using `avgF_mem β U i _ hFmem`. Establish `hA0 : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F 0 = 0` using `avgF_zero β hS U hmul h1 hi hnt _ F`. Establish `hAeig` using `avgF_eig β hS U hmul h1 hi ((hcardG.unit⁻¹ : Rˣ) : R) F`. Establish `hAcong` using `avgF_cong β hS U hmul h1 hsep hcardG hi (wH ᵥ* H.Ht + wB ᵥ* H.Bt) F hFcong`.

Establish `hp2' : 2 ≤ p` using `(Fact.out : p.Prime).two_le`. Establish `hvcp : v (algebraMap R C cp) ≠ 0`. Introduce `h0`. Apply `hS.p_ne` to reduce the goal to its premises. Rewrite using `[← hS.cp_val, h0, zero_pow (by omega)]`.

Establish `hve : v (algebraMap R C cp) ≤ v (algebraMap R C e)`. Rewrite using `[hc', map_mul, map_mul]`. Conclude with `mul_le_of_le_one_right zero_le' (hS.integers.map_le_one c')`. Establish `he0 : algebraMap R C e ≠ 0`. Introduce `h0`.

Establish `h` using `hve`. Rewrite `h` using `[h0, map_zero]`. Conclude with `hvcp (le_antisymm h zero_le')`. Establish `hcp1 : v (algebraMap R C cp) < 1`. Break down `(hS.integers.map_le_one cp).lt_or_eq with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Establish `h'` using `hS.p_lt`. Rewrite `h'` using `[← hS.cp_val, h, one_pow]`. Conclude with `lt_irrefl _ h'`.

Establish `hpe : v (algebraMap R C (p : R)) < v (algebraMap R C e)`. Rewrite using `[← hS.cp_val]`. Establish `hp3 : 2 ≤ p - 1` using `by omega`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sq]`.

Conclude with `mul_lt_of_lt_one_right (pos_iff_ne_zero.mpr hvcp) hcp1`. Use `_ ≤ _ := hve`. Establish `hsmall : ∀ r : R, v (algebraMap R C (p * r) / algebraMap R C e) < 1`. Introduce `r`. Establish `hve0 : 0 < v (algebraMap R C e)` using `pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr he0)`.

Rewrite using `[map_div₀, div_lt_one hve0, map_mul, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right zero_le' (hS.integers.map_le_one r)) hpe`. Establish `hrep : ∀ y : Nb p g, ∃ r : R, avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y / algebraMap R C e = algebraMap R C (∑ k, lam k * ((y k).val : R)) + algebraMap R C (p * r) / algebraMap R C e`. Introduce `y`. Take `⟨t, ht⟩ : ∃ t : TT p g, t = fun k => (((y k).val : ℕ) : ℤ_[p])` from `⟨_, rfl⟩`.

Establish `hy : red p g t = y`. Use function extensionality and compare the values at `k`. Simplify using `[red, ht, map_natCast, ZMod.natCast_zmod_val]`. Establish `hT : (algebraMap ℤ_[p] R ∘ t) = fun k => ((y k).val : R)`. Use function extensionality and compare the values at `k`.

Rewrite using `[ht]`. Simplify using `only [Function.comp_apply]`. Conclude with `map_natCast _ _`. Take `⟨r, hr⟩` from `hAcong t`. Use `⟨r, ?_⟩` and prove the remaining obligations.

Establish `hdot : lam ⬝ᵥ (fun k => ((y k).val : R)) = ∑ k, lam k * ((y k).val : R)` using `rfl`. Rewrite `hr` using `[hy, hrow, hT, smul_dotProduct, smul_eq_mul, hdot]`. Establish `hAy : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y = algebraMap R C e * algebraMap R C (∑ k, lam k * ((y k).val : R)) + algebraMap R C (p * r)`. Rewrite using `[← map_mul]`. Take the linear combination `hr`.

Rewrite using `[hAy, add_div, mul_div_cancel_left₀ _ he0]`. Use `⟨fun y => avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y / algebraMap R C e, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Take `⟨r, hr⟩` from `hrep y`. Simplify using `only`.

Rewrite using `[hr]`. Conclude with `le_trans (Valuation.map_add v _ _) (max_le (hS.integers.map_le_one _) (hsmall r).le)`. Introduce `y`. Take `⟨r, hr⟩` from `hrep y`. Simplify using `only`.

Rewrite using `[hr, add_sub_cancel_left]`. Conclude with `hsmall r`. Establish `hmemA : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F ∈ augIdeal H.AA.carrier` using `Submodule.mem_inf.mpr ⟨hAmem, LinearMap.mem_ker.mpr hA0⟩`. Use `hmemA using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`.

Rewrite using `[mul_div_assoc']`. Conclude with `mul_div_cancel_left₀ _ he0`. Introduce `δ t dsimp only`. Rewrite using `[red_mulVec, hAeig δ (red p g t), mul_div_assoc]`.
-/
lemma lift_one (hS : HodgeTateSetting p v R O σ cp) (hp2 : p ≠ 2) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    (hsep : ∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
      ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1)
    (hcardG : IsUnit (Fintype.card G : R)) {i : Fin U.m} (hi : U.εT i ≠ 0)
    (hnt : ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1) (e : R) (lam : Ix g → R)
    (hdiv : ∃ c, cp = e * c) (wH wB : Fin g → R)
    (hrow : (wH ᵥ* H.Ht + wB ᵥ* H.Bt) ᵥ* U.εT i = e • lam) :
    ∃ u : Nb p g → C, (∀ y, v (u y) ≤ 1) ∧
      (∀ y, v (u y - algebraMap R C (∑ k, lam k * ((y k).val : R))) < 1) ∧
      (fun y => algebraMap R C e * u y) ∈ augIdeal H.AA.carrier ∧
      (∀ δ t, u (red p g (H.ρ (β δ) *ᵥ t)) = algebraMap R C (U.sg i (β δ)) * u (red p g t)) := by
  classical
  obtain ⟨c', hc'⟩ := hdiv
  choose fH hfH hrH using fun k => (H.h4 k).1
  choose fB hfB hrB using fun k => (H.h4 k).2
  choose rH hrH' using hrH
  choose rB hrB' using hrB
  obtain ⟨F, hFdef⟩ : ∃ F : Nb p g → C, F = ∑ k, wH k • fH k + ∑ k, wB k • fB k := ⟨_, rfl⟩
  have hFmem : F ∈ H.AA.carrier := by
    rw [hFdef]
    exact H.AA.carrier.add_mem (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hfH k))
      (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hfB k))
  have hFcong : ∀ t : TT p g, ∃ r : R,
      algebraMap R C ((wH ᵥ* H.Ht + wB ᵥ* H.Bt) ⬝ᵥ (algebraMap ℤ_[p] R ∘ t)) - F (red p g t) =
        algebraMap R C (p * r) := by
    intro t
    refine ⟨∑ k, wH k * rH k t + ∑ k, wB k * rB k t, ?_⟩
    have hFt : F (red p g t) = ∑ k, algebraMap R C (wH k) * fH k (red p g t) +
        ∑ k, algebraMap R C (wB k) * fB k (red p g t) := by
      rw [hFdef, Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
      simp only [Pi.smul_apply]
      simp only [Algebra.smul_def]
    have hfH'' : ∀ k, fH k (red p g t) = algebraMap R C ((H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
        algebraMap R C (p * rH k t) := fun k => by linear_combination -(hrH' k t)
    have hfB'' : ∀ k, fB k (red p g t) = algebraMap R C ((H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
        algebraMap R C (p * rB k t) := fun k => by linear_combination -(hrB' k t)
    have hLT : (wH ᵥ* H.Ht + wB ᵥ* H.Bt) ⬝ᵥ (algebraMap ℤ_[p] R ∘ t) =
        ∑ k, wH k * (H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k +
          ∑ k, wB k * (H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k := by
      rw [add_dotProduct, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec]
      rfl
    rw [hFt, hLT]
    simp only [hfH'', hfB'']
    have hmap : (∑ k, algebraMap R C (wH k) * (algebraMap R C ((H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
          algebraMap R C (p * rH k t)) +
        ∑ k, algebraMap R C (wB k) * (algebraMap R C ((H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) -
          algebraMap R C (p * rB k t))) =
        algebraMap R C (∑ k, wH k * ((H.Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k - p * rH k t) +
          ∑ k, wB k * ((H.Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k - p * rB k t)) := by
      simp only [map_add, map_sum, map_mul, map_sub]
    rw [hmap, ← map_sub]
    congr 1
    have e1 : ∑ k, wH k * (p * rH k t) = (p : R) * ∑ k, wH k * rH k t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ k, wB k * (p * rB k t) = (p : R) * ∑ k, wB k * rB k t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e1, e2]
    ring
  have hAmem : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F ∈ H.AA.carrier :=
    avgF_mem β U i _ hFmem
  have hA0 : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F 0 = 0 :=
    avgF_zero β hS U hmul h1 hi hnt _ F
  have hAeig := avgF_eig β hS U hmul h1 hi ((hcardG.unit⁻¹ : Rˣ) : R) F
  have hAcong := avgF_cong β hS U hmul h1 hsep hcardG hi (wH ᵥ* H.Ht + wB ᵥ* H.Bt) F hFcong
  have hp2' : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hvcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    apply hS.p_ne
    rw [← hS.cp_val, h0, zero_pow (by omega)]
  have hve : v (algebraMap R C cp) ≤ v (algebraMap R C e) := by
    rw [hc', map_mul, map_mul]
    exact mul_le_of_le_one_right zero_le' (hS.integers.map_le_one c')
  have he0 : algebraMap R C e ≠ 0 := by
    intro h0
    have h := hve
    rw [h0, map_zero] at h
    exact hvcp (le_antisymm h zero_le')
  have hcp1 : v (algebraMap R C cp) < 1 := by
    rcases (hS.integers.map_le_one cp).lt_or_eq with h | h
    · exact h
    · exfalso
      have h' := hS.p_lt
      rw [← hS.cp_val, h, one_pow] at h'
      exact lt_irrefl _ h'
  have hpe : v (algebraMap R C (p : R)) < v (algebraMap R C e) := by
    rw [← hS.cp_val]
    have hp3 : 2 ≤ p - 1 := by omega
    calc v (algebraMap R C cp) ^ (p - 1) ≤ v (algebraMap R C cp) ^ 2 :=
          pow_le_pow_of_le_one zero_le' hcp1.le hp3
      _ < v (algebraMap R C cp) := by
          rw [sq]
          exact mul_lt_of_lt_one_right (pos_iff_ne_zero.mpr hvcp) hcp1
      _ ≤ _ := hve
  have hsmall : ∀ r : R, v (algebraMap R C (p * r) / algebraMap R C e) < 1 := by
    intro r
    have hve0 : 0 < v (algebraMap R C e) := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr he0)
    rw [map_div₀, div_lt_one hve0, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le' (hS.integers.map_le_one r)) hpe
  have hrep : ∀ y : Nb p g, ∃ r : R,
      avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y / algebraMap R C e =
        algebraMap R C (∑ k, lam k * ((y k).val : R)) + algebraMap R C (p * r) / algebraMap R C e := by
    intro y
    obtain ⟨t, ht⟩ : ∃ t : TT p g, t = fun k => (((y k).val : ℕ) : ℤ_[p]) := ⟨_, rfl⟩
    have hy : red p g t = y := by
      funext k
      simp [red, ht, map_natCast, ZMod.natCast_zmod_val]
    have hT : (algebraMap ℤ_[p] R ∘ t) = fun k => ((y k).val : R) := by
      funext k
      rw [ht]
      simp only [Function.comp_apply]
      exact map_natCast _ _
    obtain ⟨r, hr⟩ := hAcong t
    refine ⟨r, ?_⟩
    have hdot : lam ⬝ᵥ (fun k => ((y k).val : R)) = ∑ k, lam k * ((y k).val : R) := rfl
    rw [hy, hrow, hT, smul_dotProduct, smul_eq_mul, hdot] at hr
    have hAy : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y =
        algebraMap R C e * algebraMap R C (∑ k, lam k * ((y k).val : R)) + algebraMap R C (p * r) := by
      rw [← map_mul]
      linear_combination hr
    rw [hAy, add_div, mul_div_cancel_left₀ _ he0]
  refine ⟨fun y => avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F y / algebraMap R C e, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨r, hr⟩ := hrep y
    dsimp only
    rw [hr]
    exact le_trans (Valuation.map_add v _ _) (max_le (hS.integers.map_le_one _) (hsmall r).le)
  · intro y
    obtain ⟨r, hr⟩ := hrep y
    dsimp only
    rw [hr, add_sub_cancel_left]
    exact hsmall r
  · have hmemA : avgF β H U i ((hcardG.unit⁻¹ : Rˣ) : R) F ∈ augIdeal H.AA.carrier :=
      Submodule.mem_inf.mpr ⟨hAmem, LinearMap.mem_ker.mpr hA0⟩
    convert hmemA using 1
    funext y
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ he0
  · intro δ t
    dsimp only
    rw [red_mulVec, hAeig δ (red p g t), mul_div_assoc]

end Lift1

end ReciprocityTheory.PGsh.Up

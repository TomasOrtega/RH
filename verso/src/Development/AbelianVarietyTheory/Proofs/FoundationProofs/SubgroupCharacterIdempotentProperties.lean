import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare.EpsProj

variable {G : Type} [Group G] [Fintype G] {S : G → Prop} {χ : G → ℂ}

omit [Fintype G] in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [h1, c1]`. Consider the case `succ n ih`. Rewrite using `[pow_succ, pow_succ]`. Conclude with `⟨hm _ _ ih.1 hu, by rw [cm _ _ ih.1 hu, ih.2]⟩`.
-/
theorem pow_spec (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (n : ℕ) :
    S (u ^ n) ∧ χ (u ^ n) = χ u ^ n := by
  induction n with
  | zero => simp [h1, c1]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ⟨hm _ _ ih.1 hu, by rw [cm _ _ ih.1 hu, ih.2]⟩

/- English proof (translation)
Establish `hc : Fintype.card G ≠ 0` using `Fintype.card_ne_zero`. Establish `hi : u⁻¹ = u ^ (Fintype.card G - 1)`. Rewrite using `[inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hc), pow_card_eq_one]`. Establish `hS : S u⁻¹` using `by rw [hi]; exact (pow_spec h1 hm c1 cm hu _).1`. Use `⟨hS, ?_, ?_⟩` and prove the remaining obligations.

Use `cm _ _ hu hS` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, c1]`. Conclude with `(eq_inv_of_mul_eq_one_right this.symm)`. Use `(pow_spec h1 hm c1 cm hu (Fintype.card G)).2` as an intermediate fact. Rewrite `this` using `[pow_card_eq_one, c1]`.

Conclude with `Complex.norm_eq_one_of_pow_eq_one this.symm hc`.
-/
theorem inv_spec (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) :
    S u⁻¹ ∧ χ u⁻¹ = (χ u)⁻¹ ∧ ‖χ u‖ = 1 := by
  have hc : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hi : u⁻¹ = u ^ (Fintype.card G - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hc), pow_card_eq_one]
  have hS : S u⁻¹ := by rw [hi]; exact (pow_spec h1 hm c1 cm hu _).1
  refine ⟨hS, ?_, ?_⟩
  · have := cm _ _ hu hS
    rw [mul_inv_cancel, c1] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  · have := (pow_spec h1 hm c1 cm hu (Fintype.card G)).2
    rw [pow_card_eq_one, c1] at this
    exact Complex.norm_eq_one_of_pow_eq_one this.symm hc

/- English proof (translation)
Take `⟨hi, ci, -⟩` from `inv_spec h1 hm c1 cm hu`. Unfold `eps`. Distinguish the cases in `hy : S y`. Rewrite using `[if_pos hy, if_pos (hm _ _ hi hy), cm _ _ hi hy, ci, mul_inv, inv_inv, mul_div_assoc]`. Establish `: ¬ S (u⁻¹ * y)` using `fun h => hy (by simpa using hm _ _ hu h)`.

Rewrite using `[if_neg hy, if_neg this, mul_zero]`.
-/
theorem eps_mul (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (y : G) :
    eps S χ (u⁻¹ * y) = χ u * eps S χ y := by
  obtain ⟨hi, ci, -⟩ := inv_spec h1 hm c1 cm hu
  unfold eps
  by_cases hy : S y
  · rw [if_pos hy, if_pos (hm _ _ hi hy), cm _ _ hi hy, ci, mul_inv, inv_inv, mul_div_assoc]
  · have : ¬ S (u⁻¹ * y) := fun h => hy (by simpa using hm _ _ hu h)
    rw [if_neg hy, if_neg this, mul_zero]

omit [Group G] in
/- English proof (translation)
Rewrite using `[Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]`.
-/
theorem sum_ite_card : ∑ y, (if S y then (1 : ℂ) else 0) = (Nat.card {u // S u} : ℂ) := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

/- English proof (translation)
Use `haveI : Nonempty {u // S u} := ⟨⟨1, h1⟩⟩`. Establish `hc : (Nat.card {u // S u} : ℂ) ≠ 0` using `by exact_mod_cast Nat.card_pos.ne'`. Establish `: ∀ y, eps S χ y * χ y = (if S y then (1 : ℂ) else 0) / (Nat.card {u // S u} : ℂ)`. Introduce `y`. Unfold `eps`.

Distinguish the cases in `hy : S y`. Establish `hn : χ y ≠ 0`. Introduce `h`. Use `(inv_spec h1 hm c1 cm hy).2.2` as an intermediate fact. Rewrite `this` using `[h]`.

Simplify using `at this`. Rewrite using `[if_pos hy, if_pos hy]`. Clear the denominators using the available nonvanishing facts. Simplify using `[hy]`. Repeatedly rewrite using `[this]`.

Rewrite using `[← Finset.sum_div, sum_ite_card, div_self hc]`.
-/
theorem sum_eps_chi (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) :
    ∑ y, eps S χ y * χ y = 1 := by
  haveI : Nonempty {u // S u} := ⟨⟨1, h1⟩⟩
  have hc : (Nat.card {u // S u} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have : ∀ y, eps S χ y * χ y = (if S y then (1 : ℂ) else 0) / (Nat.card {u // S u} : ℂ) := by
    intro y
    unfold eps
    by_cases hy : S y
    · have hn : χ y ≠ 0 := by
        intro h
        have := (inv_spec h1 hm c1 cm hy).2.2
        rw [h] at this
        simp at this
      rw [if_pos hy, if_pos hy]
      field_simp
    · simp [hy]
  simp_rw [this]
  rw [← Finset.sum_div, sum_ite_card, div_self hc]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Unfold `conv`. Establish `: ∀ y, eps S χ y * eps S χ (y⁻¹ * x) = eps S χ y * χ y * eps S χ x`. Introduce `y`.

Distinguish the cases in `hy : S y`. Rewrite using `[eps_mul h1 hm c1 cm hy, mul_assoc]`. Establish `: eps S χ y = 0` using `by simp [eps, hy]`. Simplify using `[this]`. Repeatedly rewrite using `[this]`.

Rewrite using `[← Finset.sum_mul, sum_eps_chi h1 hm c1 cm, one_mul]`. Introduce `x`. Unfold `eps`. Distinguish the cases in `hx : S x`. Take `⟨hi, ci, hn⟩` from `inv_spec h1 hm c1 cm hx`.

Rewrite using `[if_pos hx, if_pos hi, ci, map_div₀, map_inv₀, map_natCast, Complex.inv_eq_conj hn]`. Establish `: ¬ S x⁻¹` using `fun h => hx (by simpa using (inv_spec h1 hm c1 cm h).1)`. Rewrite using `[if_neg hx, if_neg this, map_zero]`.
-/
theorem isProj_eps (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) : IsProj (eps S χ) := by
  refine ⟨?_, ?_⟩
  · funext x
    unfold conv
    have : ∀ y, eps S χ y * eps S χ (y⁻¹ * x) = eps S χ y * χ y * eps S χ x := by
      intro y
      by_cases hy : S y
      · rw [eps_mul h1 hm c1 cm hy, mul_assoc]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_mul, sum_eps_chi h1 hm c1 cm, one_mul]
  · intro x
    unfold eps
    by_cases hx : S x
    · obtain ⟨hi, ci, hn⟩ := inv_spec h1 hm c1 cm hx
      rw [if_pos hx, if_pos hi, ci, map_div₀, map_inv₀, map_natCast, Complex.inv_eq_conj hn]
    · have : ¬ S x⁻¹ := fun h => hx (by simpa using (inv_spec h1 hm c1 cm h).1)
      rw [if_neg hx, if_neg this, map_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩ u hu`. Simplify using `only [op, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun y => ?_` and prove the remaining obligations. Use `eps_mul h1 hm c1 cm hu (u * y)` as an intermediate fact.

Rewrite `this` using `[inv_mul_cancel_left]`. Simplify using `only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]`. Rewrite using `[← this]`. Introduce `h`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Simplify using `only [op, LinearMap.sum_apply, LinearMap.smul_apply]`. Establish `: ∀ y, eps S χ y • ρ y x = (eps S χ y * χ y) • x`. Introduce `y`. Distinguish the cases in `hy : S y`. Rewrite using `[h y hy, smul_smul]`.

Establish `: eps S χ y = 0` using `by simp [eps, hy]`. Simplify using `[this]`. Repeatedly rewrite using `[this]`. Rewrite using `[← Finset.sum_smul, sum_eps_chi h1 hm c1 cm, one_smul]`.
-/
theorem mem_range_iff {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) (x : M) :
    x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x := by
  constructor
  · rintro ⟨z, rfl⟩ u hu
    simp only [op, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun y => ?_
    have := eps_mul h1 hm c1 cm hu (u * y)
    rw [inv_mul_cancel_left] at this
    simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]
    rw [← this]
  · intro h
    refine ⟨x, ?_⟩
    simp only [op, LinearMap.sum_apply, LinearMap.smul_apply]
    have : ∀ y, eps S χ y • ρ y x = (eps S χ y * χ y) • x := by
      intro y
      by_cases hy : S y
      · rw [h y hy, smul_smul]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_smul, sum_eps_chi h1 hm c1 cm, one_smul]

/- English proof (translation)
Introduce `G _ _ M _ _ _ ρ S χ h1 hm c1 cm`. Use `⟨isProj_eps h1 hm c1 cm, ?_, mem_range_iff ρ h1 hm c1 cm, ?_⟩` and prove the remaining obligations. Simplify using `only [eps, if_pos h1, c1, inv_one, one_div]`. Introduce `n x hx h`. Establish `hmem : ∀ i, x i ∈ LinearMap.range (op ρ (eps S χ))` using `fun i => (mem_range_iff ρ h1 hm c1 cm _).2 (h i)`.

Establish `hli : LinearIndependent ℂ (fun i => (⟨x i, hmem i⟩ : LinearMap.range (op ρ (eps S χ))))` using `LinearIndependent.of_comp (LinearMap.range (op ρ (eps S χ))).subtype hx`. Simplify `hli.fintype_card_le_finrank` using `[rk]`.
-/
theorem eps_spec : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (S : G → Prop) (χ : G → ℂ), S 1 → (∀ u v, S u → S v → S (u * v)) → χ 1 = 1 → (∀ u v, S u → S v → χ (u * v) = χ u * χ v) → IsProj (eps S χ) ∧ eps S χ 1 = ((Nat.card {u // S u} : ℂ))⁻¹ ∧ (∀ x : M, x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x) ∧ ∀ (n : ℕ) (x : Fin n → M), LinearIndependent ℂ x → (∀ i u, S u → ρ u (x i) = χ u • x i) → n ≤ rk ρ (eps S χ) := by
  intro G _ _ M _ _ _ ρ S χ h1 hm c1 cm
  refine ⟨isProj_eps h1 hm c1 cm, ?_, mem_range_iff ρ h1 hm c1 cm, ?_⟩
  · simp only [eps, if_pos h1, c1, inv_one, one_div]
  · intro n x hx h
    have hmem : ∀ i, x i ∈ LinearMap.range (op ρ (eps S χ)) :=
      fun i => (mem_range_iff ρ h1 hm c1 cm _).2 (h i)
    have hli : LinearIndependent ℂ (fun i => (⟨x i, hmem i⟩ : LinearMap.range (op ρ (eps S χ)))) :=
      LinearIndependent.of_comp (LinearMap.range (op ρ (eps S χ))).subtype hx
    simpa [rk] using hli.fintype_card_le_finrank

end GlobalTheory.BadShare.EpsProj

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomFrame

open Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocF

open Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}

/- English proof (translation)
Establish `hquad : ∀ (p q : V) (m : K), h (p + m • q) (p + m • q) = h p p + m * h p q + star m * h q p + star m * m * h q q`. Introduce `p q m`. Simplify using `only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, map_smul, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨hstar, -, hunram, hprinc, -⟩` from `hS`.

Take `⟨hsm, hint, hdual, hspan⟩` from `hM`. Establish `hsym : ∀ a b : V, star (h a b) = h b a` using `fun a b => by`. Rewrite using `[← starRingEnd_apply]`. Conclude with `hs.eq a b`. Establish `hunit : ∀ a : K, IsUnitIn S a ↔ a ≠ 0 ∧ a ∈ S ∧ a⁻¹ ∈ S` using `fun a => by`.

Unfold `IsUnitIn`. Conclude with `Iff.rfl`. Take `⟨t, ht0, htM⟩` from `hspan v`. Establish `hv' : t • v ≠ 0` using `smul_ne_zero ht0 hv`. Establish `hvo' : ∀ i ∈ s, h (x i) (t • v) = 0` using `fun i hi => by`.

Rewrite using `[map_smul, hvo i hi, smul_zero]`. Take `⟨α, ⟨m0, hm0, rfl⟩, hα0, hα⟩` from `hprinc { carrier := {a | ∃ m ∈ M, h m (t • v) = a} zero_mem' := ⟨0, M.zero_mem, by simp⟩ add_mem' := by`. Introduce and unpack `_ _ ⟨m1, hm1, rfl⟩ ⟨m2, hm2, rfl⟩`. Conclude with `⟨m1 + m2, M.add_mem hm1 hm2, by simp [mul_add]⟩`. Use the proof step `neg_mem' := by`.

Introduce and unpack `_ ⟨m, hm, rfl⟩`. Conclude with `⟨-m, M.neg_mem hm, by simp⟩ }`. Use the proof step `(by`. Introduce and unpack `c hc _ ⟨m, hm, rfl⟩`. Use `⟨star c • m, hsm _ (hstar c hc) m hm, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul, RingHom.id_apply]`. Apply the tactic sequence `try ring)`. Use the proof step `⟨h (t • v) (t • v), ⟨t • v, htM, rfl⟩, fun h0 => hv' (hd _ h0)⟩`. Use the proof step `⟨1, one_ne_zero, by`. Introduce and unpack `_ ⟨m, hm, rfl⟩`.

Rewrite using `[one_mul]`. Conclude with `hint m hm _ htM⟩`. Use `set u := h m0 (t • v) with hu`. Use `set w := u⁻¹ • (t • v) with hw`. Establish `hwM : w ∈ M`.

Apply `hdual` to reduce the goal to its premises. Introduce `m hm`. Rewrite using `[hw, map_smul, smul_eq_mul, mul_comm]`. Conclude with `hα _ ⟨m, hm, rfl⟩`. Establish `hm0w : h m0 w = 1`.

Rewrite using `[hw, map_smul, smul_eq_mul, ← hu]`. Conclude with `inv_mul_cancel₀ hα0`. Establish `hwo : ∀ i ∈ s, h (x i) w = 0` using `fun i hi => by`. Rewrite using `[hw, map_smul, hvo' i hi, smul_zero]`. Use `set c : ι → K := fun i => h (x i) m0 * (h (x i) (x i))⁻¹ with hc`.

Use `set y := m0 - ∑ i ∈ s, c i • x i with hy`. Establish `hcS : ∀ i ∈ s, c i ∈ S` using `fun i hi => S.mul_mem (hint _ (hxM i hi) _ hm0) ((hunit _).mp (hxu i hi)).2.2`. Establish `hyM : y ∈ M`. Use `M.sub_mem hm0 (M.sum_mem fun i hi => ?_)` and prove the remaining obligations. Conclude with `hsm _ (hcS i hi) _ (hxM i hi)`.

Establish `hyo : ∀ j ∈ s, h (x j) y = 0`. Introduce `j hj`. Rewrite using `[hy, map_sub, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single j]`.

Establish `hne : h (x j) (x j) ≠ 0` using `((hunit _).mp (hxu j hj)).1`. Simplify using `only [hc]`. Rewrite using `[inv_mul_cancel_right₀ hne, sub_self]`. Introduce `i hi hij`. Rewrite using `[hxo j hj i hi (Ne.symm hij), mul_zero]`.

Introduce `hjs`. Conclude with `absurd hj hjs`. Establish `hyw : h y w = 1`. Rewrite using `[hy, map_sub, map_sum, LinearMap.sub_apply]`. Use `first`.

Consider the case `rw [LinearMap.sum_apply]`. Consider the case `rw [LinearMap.coe_fn_sum, Finset.sum_apply]`. Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_zero (fun i hi => by rw [hwo i hi, mul_zero]), hm0w, sub_zero]`. Establish `hwy : h w y = 1`.

Rewrite using `[← hsym, hyw, star_one]`. Take `⟨θ, hθ, hδ⟩` from `hunram`. Take `⟨hδ0, hδS, hδi⟩` from `(hunit _).mp hδ`. Use `set μ := θ * (θ - star θ)⁻¹ with hμ`. Establish `hμS : μ ∈ S` using `S.mul_mem hθ hδi`.

Establish `e1 : μ * (θ - star θ) = θ`. Rewrite using `[hμ]`. Conclude with `inv_mul_cancel_right₀ hδ0 θ`. Establish `e2 : star μ * -(θ - star θ) = star θ`. Establish `h'` using `congrArg star e1`.

Rewrite `h'` using `[star_mul', star_sub, star_star]`. Take the linear combination `h'`. Establish `hμμ : μ + star μ = 1`. Establish `: (μ + star μ) * (θ - star θ) = 1 * (θ - star θ)`. Take the linear combination `e1 - e2`.

Conclude with `mul_right_cancel₀ hδ0 this`. Distinguish the cases in `ha : IsUnitIn S (h y y)`. Conclude with `⟨y, hyM, ha, hyo⟩`. Distinguish the cases in `hb : IsUnitIn S (h w w)`. Conclude with `⟨w, hwM, hb, hwo⟩`.

Use `⟨y + μ • w, M.add_mem hyM (hsm _ hμS _ hwM), ?_, ?_⟩` and prove the remaining obligations. Establish `hzz : h (y + μ • w) (y + μ • w) = h y y + star μ * μ * h w w + 1`. Rewrite using `[hquad, hyw, hwy]`. Take the linear combination `hμμ`. Rewrite using `[hzz]`.

Establish `hwwS : h w w ∈ S` using `hint _ hwM _ hwM`. Establish `hbS : star μ * μ * h w w ∈ S` using `S.mul_mem (S.mul_mem (hstar _ hμS) hμS) hwwS`. Apply `hloc _ (hint _ hyM _ hyM) _ hbS (hsym y y)` to reduce the goal to its premises. Rewrite using `[star_mul', star_mul', star_star, hsym w w]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `ha`. Introduce `hbu`. Apply `hb` to reduce the goal to its premises. Take `⟨hb0, -, hbi⟩` from `(hunit _).mp hbu`. Establish `hww0 : h w w ≠ 0` using `fun h0 => hb0 (by rw [h0, mul_zero])`.

Establish `hμ0 : star μ * μ ≠ 0` using `fun h0 => hb0 (by rw [h0, zero_mul])`. Use `(hunit _).mpr ⟨hww0, hwwS, ?_⟩` and prove the remaining obligations. Establish `: (h w w)⁻¹ = star μ * μ * (star μ * μ * h w w)⁻¹`. Rewrite using `[mul_inv, ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]`. Rewrite using `[this]`.

Conclude with `S.mul_mem (S.mul_mem (hstar _ hμS) hμS) hbi`. Introduce `i hi`. Rewrite using `[map_add, map_smul, hyo i hi, hwo i hi, smul_zero, add_zero]`.
-/
theorem exists_next_unit (hS : IsHermSemilocal S)
    (hloc : ∀ a ∈ S, ∀ b ∈ S, star a = a → star b = b → ¬ IsUnitIn S a → ¬ IsUnitIn S b →
      IsUnitIn S (a + b + 1))
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hM : IsSelfDualMod S h M)
    {ι : Type*} [DecidableEq ι] (x : ι → V) (s : Finset ι) (hxM : ∀ i ∈ s, x i ∈ M)
    (hxo : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → h (x i) (x j) = 0)
    (hxu : ∀ i ∈ s, IsUnitIn S (h (x i) (x i)))
    (v : V) (hv : v ≠ 0) (hvo : ∀ i ∈ s, h (x i) v = 0) :
    ∃ z ∈ M, IsUnitIn S (h z z) ∧ ∀ i ∈ s, h (x i) z = 0 := by
  have hquad : ∀ (p q : V) (m : K), h (p + m • q) (p + m • q) =
      h p p + m * h p q + star m * h q p + star m * m * h q q := by
    intro p q m
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, map_smul, RingHom.id_apply]
    ring
  obtain ⟨hstar, -, hunram, hprinc, -⟩ := hS
  obtain ⟨hsm, hint, hdual, hspan⟩ := hM
  have hsym : ∀ a b : V, star (h a b) = h b a := fun a b => by
    rw [← starRingEnd_apply]
    exact hs.eq a b
  have hunit : ∀ a : K, IsUnitIn S a ↔ a ≠ 0 ∧ a ∈ S ∧ a⁻¹ ∈ S := fun a => by
    unfold IsUnitIn
    exact Iff.rfl

  obtain ⟨t, ht0, htM⟩ := hspan v
  have hv' : t • v ≠ 0 := smul_ne_zero ht0 hv
  have hvo' : ∀ i ∈ s, h (x i) (t • v) = 0 := fun i hi => by
    rw [map_smul, hvo i hi, smul_zero]

  obtain ⟨α, ⟨m0, hm0, rfl⟩, hα0, hα⟩ := hprinc
    { carrier := {a | ∃ m ∈ M, h m (t • v) = a}
      zero_mem' := ⟨0, M.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m1, hm1, rfl⟩ ⟨m2, hm2, rfl⟩
        exact ⟨m1 + m2, M.add_mem hm1 hm2, by simp [mul_add]⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, M.neg_mem hm, by simp⟩ }
    (by
      rintro c hc _ ⟨m, hm, rfl⟩
      refine ⟨star c • m, hsm _ (hstar c hc) m hm, ?_⟩
      simp only [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul,
        RingHom.id_apply]
      try ring)
    ⟨h (t • v) (t • v), ⟨t • v, htM, rfl⟩, fun h0 => hv' (hd _ h0)⟩
    ⟨1, one_ne_zero, by
      rintro _ ⟨m, hm, rfl⟩
      rw [one_mul]
      exact hint m hm _ htM⟩
  set u := h m0 (t • v) with hu

  set w := u⁻¹ • (t • v) with hw
  have hwM : w ∈ M := by
    apply hdual
    intro m hm
    rw [hw, map_smul, smul_eq_mul, mul_comm]
    exact hα _ ⟨m, hm, rfl⟩
  have hm0w : h m0 w = 1 := by
    rw [hw, map_smul, smul_eq_mul, ← hu]
    exact inv_mul_cancel₀ hα0
  have hwo : ∀ i ∈ s, h (x i) w = 0 := fun i hi => by
    rw [hw, map_smul, hvo' i hi, smul_zero]

  set c : ι → K := fun i => h (x i) m0 * (h (x i) (x i))⁻¹ with hc
  set y := m0 - ∑ i ∈ s, c i • x i with hy
  have hcS : ∀ i ∈ s, c i ∈ S := fun i hi =>
    S.mul_mem (hint _ (hxM i hi) _ hm0) ((hunit _).mp (hxu i hi)).2.2
  have hyM : y ∈ M := by
    refine M.sub_mem hm0 (M.sum_mem fun i hi => ?_)
    exact hsm _ (hcS i hi) _ (hxM i hi)
  have hyo : ∀ j ∈ s, h (x j) y = 0 := by
    intro j hj
    rw [hy, map_sub, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · have hne : h (x j) (x j) ≠ 0 := ((hunit _).mp (hxu j hj)).1
      simp only [hc]
      rw [inv_mul_cancel_right₀ hne, sub_self]
    · intro i hi hij
      rw [hxo j hj i hi (Ne.symm hij), mul_zero]
    · intro hjs
      exact absurd hj hjs
  have hyw : h y w = 1 := by
    rw [hy, map_sub, map_sum, LinearMap.sub_apply]
    first
      | rw [LinearMap.sum_apply]
      | rw [LinearMap.coe_fn_sum, Finset.sum_apply]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_zero (fun i hi => by rw [hwo i hi, mul_zero]), hm0w, sub_zero]
  have hwy : h w y = 1 := by
    rw [← hsym, hyw, star_one]

  obtain ⟨θ, hθ, hδ⟩ := hunram
  obtain ⟨hδ0, hδS, hδi⟩ := (hunit _).mp hδ
  set μ := θ * (θ - star θ)⁻¹ with hμ
  have hμS : μ ∈ S := S.mul_mem hθ hδi
  have e1 : μ * (θ - star θ) = θ := by
    rw [hμ]
    exact inv_mul_cancel_right₀ hδ0 θ
  have e2 : star μ * -(θ - star θ) = star θ := by
    have h' := congrArg star e1
    rw [star_mul', star_sub, star_star] at h'
    linear_combination h'
  have hμμ : μ + star μ = 1 := by
    have : (μ + star μ) * (θ - star θ) = 1 * (θ - star θ) := by
      linear_combination e1 - e2
    exact mul_right_cancel₀ hδ0 this
  by_cases ha : IsUnitIn S (h y y)
  · exact ⟨y, hyM, ha, hyo⟩
  by_cases hb : IsUnitIn S (h w w)
  · exact ⟨w, hwM, hb, hwo⟩
  refine ⟨y + μ • w, M.add_mem hyM (hsm _ hμS _ hwM), ?_, ?_⟩
  · have hzz : h (y + μ • w) (y + μ • w) = h y y + star μ * μ * h w w + 1 := by
      rw [hquad, hyw, hwy]
      linear_combination hμμ
    rw [hzz]
    have hwwS : h w w ∈ S := hint _ hwM _ hwM
    have hbS : star μ * μ * h w w ∈ S := S.mul_mem (S.mul_mem (hstar _ hμS) hμS) hwwS
    apply hloc _ (hint _ hyM _ hyM) _ hbS (hsym y y)
    · rw [star_mul', star_mul', star_star, hsym w w]
      ring
    · exact ha
    · intro hbu
      apply hb
      obtain ⟨hb0, -, hbi⟩ := (hunit _).mp hbu
      have hww0 : h w w ≠ 0 := fun h0 => hb0 (by rw [h0, mul_zero])
      have hμ0 : star μ * μ ≠ 0 := fun h0 => hb0 (by rw [h0, zero_mul])
      refine (hunit _).mpr ⟨hww0, hwwS, ?_⟩
      have : (h w w)⁻¹ = star μ * μ * (star μ * μ * h w w)⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]
      rw [this]
      exact S.mul_mem (S.mul_mem (hstar _ hμS) hμS) hbi
  · intro i hi
    rw [map_add, map_smul, hyo i hi, hwo i hi, smul_zero, add_zero]

/- English proof (translation)
Establish `P : ∀ k, k ≤ finrank K V → ∃ x : ℕ → V, (∀ i < k, x i ∈ M) ∧ (∀ i < k, ∀ j < k, i ≠ j → h (x i) (x j) = 0) ∧ ∀ i < k, IsUnitIn S (h (x i) (x i))`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`.

Conclude with `⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩`. Consider the case `succ k ih`. Introduce `hk`. Take `⟨x, hxM, hxo, hxu⟩` from `ih (by omega)`. Use `set W : Submodule K V := Submodule.span K (((Finset.range k).image x : Finset V) : Set V) with hW`.

Establish `hWne : W ≠ ⊤`. Introduce `htop`. Establish `h1 : finrank K W ≤ k` using `(finrank_span_finset_le_card _).trans (Finset.card_image_le.trans (by simp))`. Rewrite `h1` using `[htop, finrank_top]`. Use linear arithmetic over natural numbers and integers.

Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u, u ∉ W := by`. Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_not] at hcon`. Conclude with `hWne (eq_top_iff.mpr fun u _ => hcon u)`. Establish `hxW : ∀ i ∈ Finset.range k, x i ∈ W` using `fun i hi => Submodule.subset_span (by exact_mod_cast Finset.mem_image_of_mem x hi)`.

Establish `hsW : ∑ i ∈ Finset.range k, (h (x i) u * (h (x i) (x i))⁻¹) • x i ∈ W` using `W.sum_mem fun i hi => W.smul_mem _ (hxW i hi)`. Take `⟨z, hzM, hzu, hzo⟩` from `exists_next_unit hS hloc hs hd hM x (Finset.range k) (fun i hi => hxM i (Finset.mem_range.mp hi)) (fun i hi j hj => hxo i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)) (fun i hi => hxu i (Finset.mem_range.mp hi)) (u - ∑ i ∈ Finset.range k, (h (x i) u * (h (x i) (x i))⁻¹) • …`. Introduce `j hj`. Rewrite using `[map_sub, map_sum, Finset.sum_eq_single j]`. Rewrite using `[map_smul, smul_eq_mul, inv_mul_cancel_right₀ (hxu j (Finset.mem_range.mp hj)).1, sub_self]`.

Introduce `i hi hij`. Rewrite using `[map_smul, hxo j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi) (Ne.symm hij), smul_zero]`. Conclude with `fun hj' => absurd hj hj')`. Establish `hzo' : ∀ i < k, h z (x i) = 0` using `fun i hi => by`. Rewrite using `[← hs.eq, hzo i (Finset.mem_range.mpr hi), map_zero]`.

Use `⟨fun i => if i = k then z else x i, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Distinguish the cases in `hik : i = k`. Simplify `hzM` using `[hik]`. Simplify `hxM i (by omega)` using `[hik]`.

Introduce `i hi j hj hij`. Distinguish the cases in `hik : i = k`. Establish `hjk : j ≠ k` using `fun e => hij (hik.trans e.symm)`. Simplify `hzo' j (by omega)` using `[hik, hjk]`. Distinguish the cases in `hjk : j = k`.

Simplify `hzo i (Finset.mem_range.mpr (by omega))` using `[hik, hjk]`. Simplify `hxo i (by omega) j (by omega) hij` using `[hik, hjk]`. Introduce `i hi`. Distinguish the cases in `hik : i = k`. Simplify `hzu` using `[hik]`.

Simplify `hxu i (by omega)` using `[hik]`. Take `⟨x, h1, h2, h3⟩` from `P _ le_rfl`. Conclude with `⟨fun i => x i, fun i => h1 i i.isLt, fun i j hij => h2 i i.isLt j j.isLt (fun e => hij (Fin.ext e)), fun i => h3 i i.isLt⟩`.
-/
theorem exists_orth_unit_frame [FiniteDimensional K V] (hS : IsHermSemilocal S)
    (hloc : ∀ a ∈ S, ∀ b ∈ S, star a = a → star b = b → ¬ IsUnitIn S a → ¬ IsUnitIn S b →
      IsUnitIn S (a + b + 1))
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hM : IsSelfDualMod S h M) :
    ∃ x : Fin (finrank K V) → V, (∀ i, x i ∈ M) ∧ (∀ i j, i ≠ j → h (x i) (x j) = 0) ∧
      ∀ i, IsUnitIn S (h (x i) (x i)) := by
  classical
  have P : ∀ k, k ≤ finrank K V → ∃ x : ℕ → V, (∀ i < k, x i ∈ M) ∧
      (∀ i < k, ∀ j < k, i ≠ j → h (x i) (x j) = 0) ∧ ∀ i < k, IsUnitIn S (h (x i) (x i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hxM, hxo, hxu⟩ := ih (by omega)
      set W : Submodule K V := Submodule.span K (((Finset.range k).image x : Finset V) : Set V)
        with hW
      have hWne : W ≠ ⊤ := by
        intro htop
        have h1 : finrank K W ≤ k :=
          (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans (by simp))
        rw [htop, finrank_top] at h1
        omega
      obtain ⟨u, hu⟩ : ∃ u, u ∉ W := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        exact hWne (eq_top_iff.mpr fun u _ => hcon u)
      have hxW : ∀ i ∈ Finset.range k, x i ∈ W := fun i hi =>
        Submodule.subset_span (by exact_mod_cast Finset.mem_image_of_mem x hi)
      have hsW : ∑ i ∈ Finset.range k, (h (x i) u * (h (x i) (x i))⁻¹) • x i ∈ W :=
        W.sum_mem fun i hi => W.smul_mem _ (hxW i hi)
      obtain ⟨z, hzM, hzu, hzo⟩ := exists_next_unit hS hloc hs hd hM x (Finset.range k)
        (fun i hi => hxM i (Finset.mem_range.mp hi))
        (fun i hi j hj => hxo i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj))
        (fun i hi => hxu i (Finset.mem_range.mp hi))
        (u - ∑ i ∈ Finset.range k, (h (x i) u * (h (x i) (x i))⁻¹) • x i)
        (fun h0 => hu (by rw [sub_eq_zero.mp h0]; exact hsW))
        (by
          intro j hj
          rw [map_sub, map_sum, Finset.sum_eq_single j]
          · rw [map_smul, smul_eq_mul,
              inv_mul_cancel_right₀ (hxu j (Finset.mem_range.mp hj)).1, sub_self]
          · intro i hi hij
            rw [map_smul, hxo j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi)
              (Ne.symm hij), smul_zero]
          · exact fun hj' => absurd hj hj')
      have hzo' : ∀ i < k, h z (x i) = 0 := fun i hi => by
        rw [← hs.eq, hzo i (Finset.mem_range.mpr hi), map_zero]
      refine ⟨fun i => if i = k then z else x i, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hik : i = k
        · simpa [hik] using hzM
        · simpa [hik] using hxM i (by omega)
      · intro i hi j hj hij
        by_cases hik : i = k
        · have hjk : j ≠ k := fun e => hij (hik.trans e.symm)
          simpa [hik, hjk] using hzo' j (by omega)
        · by_cases hjk : j = k
          · simpa [hik, hjk] using hzo i (Finset.mem_range.mpr (by omega))
          · simpa [hik, hjk] using hxo i (by omega) j (by omega) hij
      · intro i hi
        by_cases hik : i = k
        · simpa [hik] using hzu
        · simpa [hik] using hxu i (by omega)
  obtain ⟨x, h1, h2, h3⟩ := P _ le_rfl
  exact ⟨fun i => x i, fun i => h1 i i.isLt,
    fun i j hij => h2 i i.isLt j j.isLt (fun e => hij (Fin.ext e)), fun i => h3 i i.isLt⟩

end Formalism.HermitianLattices.Ext.L3.LocF

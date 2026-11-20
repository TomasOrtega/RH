import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsSmoothConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedForm

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.Cells

/- English proof (translation)
Introduce `F S hS`. Use `(Set.Finite.biUnion (Finset.range (hS.toFinset.card + 1)).finite_toSet fun m _ => ((Set.Finite.pi (t := fun _ : Fin m => S) fun _ => hS).image (Sigma.mk m))).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨m, γ⟩ ⟨h1, h2⟩`. Establish `hle : m ≤ hS.toFinset.card`. Use `Fintype.card_le_of_injective (fun j : Fin m => (⟨γ j, by simpa using h1 j⟩ : hS.toFinset)) fun a b h => h2 (congrArg Subtype.val h)` as an intermediate fact.

Simplify using `using this`. Conclude with `Set.mem_biUnion (x := m) (by simp; omega) ⟨γ, fun j _ => h1 j, rfl⟩`.
-/
theorem finite_families : ∀ (F : Type) (S : Set F), S.Finite →
    {x : Σ m : ℕ, Fin m → F | (∀ j, x.2 j ∈ S) ∧ Function.Injective x.2}.Finite := by
  intro F S hS
  classical
  refine (Set.Finite.biUnion (Finset.range (hS.toFinset.card + 1)).finite_toSet fun m _ =>
    ((Set.Finite.pi (t := fun _ : Fin m => S) fun _ => hS).image (Sigma.mk m))).subset ?_
  rintro ⟨m, γ⟩ ⟨h1, h2⟩
  have hle : m ≤ hS.toFinset.card := by
    have := Fintype.card_le_of_injective (fun j : Fin m => (⟨γ j, by simpa using h1 j⟩ : hS.toFinset))
      fun a b h => h2 (congrArg Subtype.val h)
    simpa using this
  exact Set.mem_biUnion (x := m) (by simp; omega) ⟨γ, fun j _ => h1 j, rfl⟩

/- English proof (translation)
Introduce `N hN r e₁ e₂ V hV he`. Use `set δ := e₁ - e₂ with hδ`. Establish `h1 : ∀ x, ∃ z, δ x = (N : ℤ) • δ z`. Introduce `x`. Take `⟨v, hv, hvx⟩` from `hV x`.

Establish `: ∀ i, (N : ℤ) ∣ x i - v i` using `fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (hvx i)`. Use `choose z hz using this`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `hx : x = v + (N : ℤ) • z` using `funext fun i => by simp [← hz i]`. Rewrite using `[hx, map_add, map_smul]`.

Simplify using `[δ, he v hv]`. Establish `h2 : ∀ k : ℕ, ∀ x, ∃ w, δ x = ((N : ℤ) ^ k) • w`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x; exact ⟨δ x, by simp⟩`.

Consider the case `succ k ih`. Introduce `x`. Take `⟨z, hz⟩` from `h1 x`. Take `⟨w, hw⟩` from `ih z`. Conclude with `⟨w, by rw [hz, hw, smul_smul, pow_succ']⟩`.

Establish `h3 : δ = 0`. Use `LinearMap.ext fun x => funext fun i => ?_` and prove the remaining obligations. Take `⟨w, hw⟩` from `h2 (δ x i).natAbs x`. Generalize the expression as in `hk : (δ x i).natAbs = k at hw`. Establish `hd : ((N : ℤ) ^ k) ∣ δ x i` using `⟨w i, by simpa using congrFun hw i⟩`.

Assume the negation of the conclusion as `h0`. Establish `h4` using `Int.natAbs_le_of_dvd_ne_zero hd h0`. Establish `h5 : k < N ^ k` using `Nat.lt_pow_self (by omega)`. Rewrite `h4` using `[Int.natAbs_pow, Int.natAbs_natCast]`. Use linear arithmetic over natural numbers and integers.

Conclude with `sub_eq_zero.1 h3`.
-/
theorem linearMap_eq_of_eq_on_residues : ∀ (N : ℕ), 2 ≤ N → ∀ (r : ℕ) (e₁ e₂ : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) (V : Set (Fin r → ℤ)),
    (∀ x : Fin r → ℤ, ∃ v ∈ V, ∀ i, ((v i : ℤ) : ZMod N) = (x i : ZMod N)) → (∀ v ∈ V, e₁ v = e₂ v) → e₁ = e₂ := by
  intro N hN r e₁ e₂ V hV he
  set δ := e₁ - e₂ with hδ
  have h1 : ∀ x, ∃ z, δ x = (N : ℤ) • δ z := by
    intro x
    obtain ⟨v, hv, hvx⟩ := hV x
    have : ∀ i, (N : ℤ) ∣ x i - v i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (hvx i)
    choose z hz using this
    refine ⟨z, ?_⟩
    have hx : x = v + (N : ℤ) • z := funext fun i => by simp [← hz i]
    rw [hx, map_add, map_smul]
    simp [δ, he v hv]
  have h2 : ∀ k : ℕ, ∀ x, ∃ w, δ x = ((N : ℤ) ^ k) • w := by
    intro k
    induction k with
    | zero => intro x; exact ⟨δ x, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨z, hz⟩ := h1 x
      obtain ⟨w, hw⟩ := ih z
      exact ⟨w, by rw [hz, hw, smul_smul, pow_succ']⟩
  have h3 : δ = 0 := by
    refine LinearMap.ext fun x => funext fun i => ?_
    obtain ⟨w, hw⟩ := h2 (δ x i).natAbs x
    generalize hk : (δ x i).natAbs = k at hw
    have hd : ((N : ℤ) ^ k) ∣ δ x i := ⟨w i, by simpa using congrFun hw i⟩
    by_contra h0
    have h4 := Int.natAbs_le_of_dvd_ne_zero hd h0
    have h5 : k < N ^ k := Nat.lt_pow_self (by omega)
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h4
    omega
  exact sub_eq_zero.1 h3

/- English proof (translation)
Establish `: ∀ i, (N : ℤ) ∣ y i - x i` using `fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h i)`. Use `choose z hz using this`. Establish `hy : y = x + (N : ℤ) • z` using `funext fun i => by simp [← hz i]`. Rewrite using `[hy, map_add, map_smul]`. Simplify using the standard rewrite rules.
-/
theorem cong_map {N r : ℕ} (f : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) {x y : Fin r → ℤ}
    (h : ∀ i, ((x i : ℤ) : ZMod N) = (y i : ZMod N)) (i : Fin r) : ((f x i : ℤ) : ZMod N) = (f y i : ZMod N) := by
  have : ∀ i, (N : ℤ) ∣ y i - x i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h i)
  choose z hz using this
  have hy : y = x + (N : ℤ) • z := funext fun i => by simp [← hz i]
  rw [hy, map_add, map_smul]
  simp

/- English proof (translation)
Introduce `W N _ r μ hμ b e hb`. Set `lift : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)` to `fun c u i => ((c u i).val : ℤ)`. Establish `hlift : ∀ c u i, ((lift c u i : ℤ) : ZMod N) = c u i` using `fun c u i => by simp [lift]`. Set `d : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ZMod N)` to `fun c u i => ((e (lift c u) i : ℤ) : ZMod N)`. Use `⟨fun c u => e.symm (μ (d c) u), fun c u i => ?_, fun c α hα => ?_, fun c u => ⟨d c, by simp⟩⟩` and prove the remaining obligations.

Establish `h1 : ∀ i, ((μ (d c) u i : ℤ) : ZMod N) = ((e (lift c u) i : ℤ) : ZMod N)` using `fun i => hμ _ _ _`. Establish `h2` using `cong_map e.symm.toLinearMap h1 i`. Simplify using `only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2`. Rewrite using `[h2, hlift]`. Establish `h1 : qW W (pull e.toLinearMap b) (fun u => e.symm (μ (d c) u)) = qW W b (μ (d c))` using `by simp [qW]`.

Establish `h2 : qW W (pull e.toLinearMap b) α = qW W b (fun u => e (α u))` using `by simp [qW]`. Rewrite using `[h1, h2]`. Conclude with `hb _ _ fun u i => cong_map e.toLinearMap (fun i => by rw [hα, hlift]) i`.
-/
theorem exists_transport : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (N : ℕ) [NeZero N] (r : ℕ)
    (μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) →
    ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)),
    (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) →
    ∃ μ' : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) ∧
      (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) →
        qW W (pull e.toLinearMap b) (μ' c) ≤ qW W (pull e.toLinearMap b) α) ∧
      ∀ c u, ∃ d, e (μ' c u) = μ d u := by
  intro W N _ r μ hμ b e hb
  let lift : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ) := fun c u i => ((c u i).val : ℤ)
  have hlift : ∀ c u i, ((lift c u i : ℤ) : ZMod N) = c u i := fun c u i => by simp [lift]
  let d : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ZMod N) := fun c u i => ((e (lift c u) i : ℤ) : ZMod N)
  refine ⟨fun c u => e.symm (μ (d c) u), fun c u i => ?_, fun c α hα => ?_, fun c u => ⟨d c, by simp⟩⟩
  · have h1 : ∀ i, ((μ (d c) u i : ℤ) : ZMod N) = ((e (lift c u) i : ℤ) : ZMod N) := fun i => hμ _ _ _
    have h2 := cong_map e.symm.toLinearMap h1 i
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2
    rw [h2, hlift]
  · have h1 : qW W (pull e.toLinearMap b) (fun u => e.symm (μ (d c) u)) = qW W b (μ (d c)) := by simp [qW]
    have h2 : qW W (pull e.toLinearMap b) α = qW W b (fun u => e (α u)) := by simp [qW]
    rw [h1, h2]
    exact hb _ _ fun u i => cong_map e.toLinearMap (fun i => by rw [hα, hlift]) i

/- English proof (translation)
Introduce `φ r m γ hγ b' b₀ hb' hb₀ s hs hk`. Take `⟨t, bb, hbb⟩` from `hγ.basis`. Set `B' : balForms id (Fin r → ℤ)` to `⟨b', mem_balForms_int.2 hb'⟩`. Set `B₀ : balForms id (Fin r → ℤ)` to `⟨b₀, mem_balForms_int.2 hb₀⟩`. Establish `hc : ∀ n ∈ s, ∀ o, (∀ j, o ≠ Sum.inl j) → (n : ℤ) * bb.repr B' o + bb.repr B₀ o = 0`.

Introduce `n hn o ho`. Take `⟨k, cf, hk0, he⟩` from `hk n hn`. Establish `hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j)` using `Subtype.ext (by simpa [hbb, B', B₀] using he)`. Use `congrArg (fun x => bb.repr x o) hE` as an intermediate fact. Simplify using `only [map_nsmul, map_add, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, nsmul_eq_mul] at this`.

Rewrite `this` using `[Finset.sum_eq_zero fun j _ => by rw [if_neg (ho j).symm]; simp]`. Establish `hk' : (k : ℤ) ≠ 0` using `by exact_mod_cast hk0.ne'`. Move the coercions through the operations in `at this`. Conclude with `(mul_eq_zero.1 this).resolve_left hk'`. Establish `hp : ∀ n ∈ s, ∀ j, 0 ≤ (n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j)`.

Introduce `n hn j`. Take `⟨k, cf, hk0, he⟩` from `hk n hn`. Establish `hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j)` using `Subtype.ext (by simpa [hbb, B', B₀] using he)`. Use `congrArg (fun x => bb.repr x (Sum.inl j)) hE` as an intermediate fact. Simplify using `only [map_nsmul, map_add, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, nsmul_eq_mul, Sum.inl.injEq] at this`.

Simplify using `only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Establish `hk' : (0 : ℤ) < k` using `by exact_mod_cast hk0`. Establish `h2 : (0 : ℤ) ≤ k * ((n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j))`. Move the coercions through the operations in `at this ⊢`. Rewrite using `[this]`.

Check the signs of the components of the expression. Conclude with `nonneg_of_mul_nonneg_right (by linarith) hk'`. Set `M : ℕ` to `∑ o, (bb.repr B₀ o).natAbs`. Take `⟨n₁, hn₁, h₁⟩` from `hs.exists_gt M`. Take `⟨n₂, hn₂, h₂⟩` from `hs.exists_gt n₁`.

Establish `hM : ∀ o, (bb.repr B₀ o).natAbs ≤ M` using `fun o => Finset.single_le_sum (f := fun o => (bb.repr B₀ o).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ o)`. Establish `hR : ∀ o, (∀ j, o ≠ Sum.inl j) → bb.repr B' o = 0` using `fun o ho => by`. Establish `e1` using `hc n₁ hn₁ o ho`. Establish `e2` using `hc n₂ hn₂ o ho`. Establish `: ((n₂ : ℤ) - n₁) * bb.repr B' o = 0` using `by linarith`.

Conclude with `(mul_eq_zero.1 this).resolve_left (by omega)`. Establish `hL : ∀ j, 0 ≤ bb.repr B' (Sum.inl j)` using `fun j => by`. Establish `e1` using `hp n₁ hn₁ j`. Establish `e2` using `hM (Sum.inl j)`. Assume the negation of the conclusion as `hneg`.

Use `push_neg at hneg`. Establish `: (bb.repr B₀ (Sum.inl j)) ≤ M` using `by omega`. Establish `: (n₁ : ℤ) * bb.repr B' (Sum.inl j) ≤ - n₁` using `by nlinarith`. Use linear arithmetic over natural numbers and integers. Use `⟨fun j => (bb.repr B' (Sum.inl j)).toNat, ?_⟩` and prove the remaining obligations.

Establish `hsum` using `bb.sum_repr B'`. Establish `h0 : ∑ a₂ : Fin t, bb.repr B' (Sum.inr a₂) • bb (Sum.inr a₂) = 0` using `Finset.sum_eq_zero fun o _ => by rw [hR (Sum.inr o) fun j => Sum.inr_ne_inl, zero_smul]`. Rewrite `hsum` using `[Fintype.sum_sum_type, h0, add_zero]`. Use `congrArg Subtype.val hsum` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, hbb] at this`.

Rewrite using `[show b' = (B' : LinearMap.BilinForm ℤ (Fin r → ℤ)) from rfl, ← this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← natCast_zsmul, Int.toNat_of_nonneg (hL j)]`.
-/
theorem exists_nat_comb_of_infinite : ∀ (φ : InvFun ℤ) (r m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)), IsCone id φ γ →
    ∀ b' b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b' x y = b' y x) → (∀ x y, b₀ x y = b₀ y x) →
    ∀ s : Set ℕ, s.Infinite → (∀ n ∈ s, ∃ (k : ℕ) (cf : Fin m → ℕ), 0 < k ∧ k • (n • b' + b₀) = ∑ j, cf j • γ j) →
    ∃ cf : Fin m → ℕ, b' = ∑ j, cf j • γ j := by
  intro φ r m γ hγ b' b₀ hb' hb₀ s hs hk
  classical
  obtain ⟨t, bb, hbb⟩ := hγ.basis
  let B' : balForms id (Fin r → ℤ) := ⟨b', mem_balForms_int.2 hb'⟩
  let B₀ : balForms id (Fin r → ℤ) := ⟨b₀, mem_balForms_int.2 hb₀⟩
  have hc : ∀ n ∈ s, ∀ o, (∀ j, o ≠ Sum.inl j) → (n : ℤ) * bb.repr B' o + bb.repr B₀ o = 0 := by
    intro n hn o ho
    obtain ⟨k, cf, hk0, he⟩ := hk n hn
    have hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j) := Subtype.ext (by simpa [hbb, B', B₀] using he)
    have := congrArg (fun x => bb.repr x o) hE
    simp only [map_nsmul, map_add, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply,
      Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, nsmul_eq_mul] at this
    rw [Finset.sum_eq_zero fun j _ => by rw [if_neg (ho j).symm]; simp] at this
    have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
    push_cast at this
    exact (mul_eq_zero.1 this).resolve_left hk'
  have hp : ∀ n ∈ s, ∀ j, 0 ≤ (n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j) := by
    intro n hn j
    obtain ⟨k, cf, hk0, he⟩ := hk n hn
    have hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j) := Subtype.ext (by simpa [hbb, B', B₀] using he)
    have := congrArg (fun x => bb.repr x (Sum.inl j)) hE
    simp only [map_nsmul, map_add, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply,
      Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, nsmul_eq_mul, Sum.inl.injEq] at this
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    have hk' : (0 : ℤ) < k := by exact_mod_cast hk0
    have h2 : (0 : ℤ) ≤ k * ((n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j)) := by
      push_cast at this ⊢; rw [this]; positivity
    exact nonneg_of_mul_nonneg_right (by linarith) hk'
  let M : ℕ := ∑ o, (bb.repr B₀ o).natAbs
  obtain ⟨n₁, hn₁, h₁⟩ := hs.exists_gt M
  obtain ⟨n₂, hn₂, h₂⟩ := hs.exists_gt n₁
  have hM : ∀ o, (bb.repr B₀ o).natAbs ≤ M := fun o =>
    Finset.single_le_sum (f := fun o => (bb.repr B₀ o).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ o)
  have hR : ∀ o, (∀ j, o ≠ Sum.inl j) → bb.repr B' o = 0 := fun o ho => by
    have e1 := hc n₁ hn₁ o ho
    have e2 := hc n₂ hn₂ o ho
    have : ((n₂ : ℤ) - n₁) * bb.repr B' o = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (by omega)
  have hL : ∀ j, 0 ≤ bb.repr B' (Sum.inl j) := fun j => by
    have e1 := hp n₁ hn₁ j
    have e2 := hM (Sum.inl j)
    by_contra hneg
    push_neg at hneg
    have : (bb.repr B₀ (Sum.inl j)) ≤ M := by omega
    have : (n₁ : ℤ) * bb.repr B' (Sum.inl j) ≤ - n₁ := by nlinarith
    omega
  refine ⟨fun j => (bb.repr B' (Sum.inl j)).toNat, ?_⟩
  have hsum := bb.sum_repr B'
  have h0 : ∑ a₂ : Fin t, bb.repr B' (Sum.inr a₂) • bb (Sum.inr a₂) = 0 :=
    Finset.sum_eq_zero fun o _ => by rw [hR (Sum.inr o) fun j => Sum.inr_ne_inl, zero_smul]
  rw [Fintype.sum_sum_type, h0, add_zero] at hsum
  have := congrArg Subtype.val hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul, hbb] at this
  rw [show b' = (B' : LinearMap.BilinForm ℤ (Fin r → ℤ)) from rfl, ← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← natCast_zsmul, Int.toNat_of_nonneg (hL j)]

/- English proof (translation)
Simplify using `only [qW, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring`.
-/
theorem qW_nsmul_add {r : ℕ} (W : Matrix (Fin 8) (Fin 8) ℤ) (b b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ)) (n : ℕ)
    (y : Fin 8 → Fin r → ℤ) : qW W (n • b + b₀) y = n * qW W b y + qW W b₀ y := by
  simp only [qW, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring

/- English proof (translation)
Introduce `g φ hF W hW N _ hN r hr μ hμ b₀ hb₀s hb₀p hb₀m`. Establish `hFr : IsPolFanOn id φ (Fin r → ℤ)` using `hF _ (by simpa using hr)`. Set `Mn : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)) → LinearMap.BilinForm ℤ (Fin r → ℤ) → Prop` to `fun μ b => ∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α`. Set `T : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ))` to `{x | IsCone id φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) ∧ ∃ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (k : ℕ) (cf : Fin x.1 → ℕ), 0 < k ∧ (∀ j, 0 < cf j) ∧ k • b = ∑ j, cf j • x.2 j ∧ Mn μ b}`. Establish `hT : T.Finite`.

Take `⟨S, hS, hSe⟩` from `hFr.finite`. Set `TS : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ))` to `{x | (∀ j, x.2 j ∈ S) ∧ Function.Injective x.2 ∧ IsCone id φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)}`. Establish `hTS : TS.Finite` using `(finite_families _ S hS).subset fun x hx => ⟨hx.1, hx.2.1⟩`. Establish `hdick` using `fun (x : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) (h : IsCone id φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)) => GlobalTheory.T.finite_minimiser_systems_smooth_cone φ W hW N hN r x.1 x.2 h.1 h.2`. Set `Fμ : (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) → Set ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ))` to `fun x => if h : IsCone id φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) then ((hdick x h).choose : Set _) else ∅`.

Set `M` to `(⋃ x ∈ TS, Fμ x) ∩ {μ' | ∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i}`. Establish `hM : M.Finite` using `(hTS.biUnion fun x _ => by`. Simplify using `only [Fμ]`. Use `split_ifs`. Conclude with `Finset.finite_toSet _`.

Conclude with `Set.finite_empty).inter_of_left _`. Set `V : Set (Fin r → ℤ)` to `Set.range fun p : (Fin 8 → Fin r → ZMod N) × Fin 8 => μ p.1 p.2`. Set `E` to `⋃ μ' ∈ M, {e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ) | ∀ c u, e (μ' c u) ∈ V}`. Establish `hE : E.Finite` using `hM.biUnion fun μ' hμ' => by`. Set `Φ : ((Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) → (Fin 8 → Fin r → ZMod N) × Fin 8 → (Fin r → ℤ)` to `fun e p => e (μ' p.1 p.2)`.

Use `Set.Finite.of_finite_image (f := Φ) ((Set.Finite.pi (t := fun _ => V) fun _ => Set.finite_range _).subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨e, he, rfl⟩ p -`. Conclude with `he p.1 p.2`. Introduce `e₁ _ e₂ _ h`. Use `LinearEquiv.toLinearMap_injective (linearMap_eq_of_eq_on_residues N (by omega) r _ _ (Set.range fun p : (Fin 8 → Fin r → ZMod N) × Fin 8 => μ' p.1 p.2) (fun x => ⟨μ' (fun _ i => (x i : ZMod N)) 0, ⟨((fun _ i => (x i : ZMod N)), 0), rfl⟩, fun i => hμ'.2 _ _ _⟩) ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `congrFun h p`. Use `((hTS.prod hE).image fun q => (⟨q.1.1, fun j => pull q.2.symm.toLinearMap (q.1.2 j)⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ))).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨m, γ⟩ ⟨hγ, hγd, b, k, cf, hk, hcf, hkb, hbm⟩`. Take `⟨e, he⟩` from `hSe m γ hγ`.

Take `⟨μ', hμ'1, hμ'2, hμ'3⟩` from `exists_transport W N r μ hμ b e hbm`. Establish `hc'` using `hγ.pull_equiv e`. Establish `hd' : ∀ y, y ≠ 0 → 0 < ∑ j, pull e.toLinearMap (γ j) y y` using `fun y hy => by`. Simplify `hy)` using `using hγd (e y) (by simpa`. Establish `hkb' : k • pull e.toLinearMap b = ∑ j, cf j • pull e.toLinearMap (γ j)` using `LinearMap.ext₂ fun x y => by`.

Simplify `LinearMap.congr_fun₂ hkb (e x) (e y)` using `[LinearMap.sum_apply]`. Establish `hx' : (⟨m, fun j => pull e.toLinearMap (γ j)⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) ∈ TS` using `⟨he, hc'.injective, hc', hd'⟩`. Use `⟨⟨⟨m, fun j => pull e.toLinearMap (γ j)⟩, e⟩, ⟨hx', ?_⟩, ?_⟩` and prove the remaining obligations. Use `Set.mem_biUnion (x := μ') ⟨Set.mem_biUnion hx' ?_, hμ'1⟩ fun c u => ?_` and prove the remaining obligations. Use `show μ' ∈ Fμ ⟨m, fun j => pull e.toLinearMap (γ j)⟩`.

Simplify using `only [Fμ]`. Rewrite using `[dif_pos (show IsCone id φ (fun j => pull e.toLinearMap (γ j)) ∧ _ from ⟨hc', hd'⟩)]`. Conclude with `(hdick ⟨m, fun j => pull e.toLinearMap (γ j)⟩ ⟨hc', hd'⟩).choose_spec (pull e.toLinearMap b) k cf hk hcf hkb' μ' hμ'1 hμ'2`. Take `⟨d, hd⟩` from `hμ'3 c u`. Conclude with `⟨(d, u), hd.symm⟩`.

Simplify using the standard rewrite rules. Take `⟨L, hL⟩ : ∃ L : List (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)), ∀ x, x ∈ L ↔ x ∈ T` from `⟨hT.toFinset.toList, fun x => by simp⟩`. Use `⟨L.length, fun i => (L.get i).1, fun i => (L.get i).2, fun i => ((hL _).1 (List.get_mem L i)).1, ?_⟩` and prove the remaining obligations. Introduce `b' hb's hb'p hb'm`. Establish `key : ∀ n : ℕ, ∃ i : Fin L.length, ∃ (k : ℕ) (cf : Fin (L.get i).1 → ℕ), 0 < k ∧ k • (n • b' + b₀) = ∑ j, cf j • (L.get i).2 j`.

Introduce `n`. Establish `hβs : n • b' + b₀ ∈ balForms id (Fin r → ℤ)` using `mem_balForms_int.2 fun x y => by`. Simplify using `[hb's x y, hb₀s x y]`. Establish `hβp : ∀ x, x ≠ 0 → 0 < (n • b' + b₀) x x` using `fun x hx => by`. Establish `h1` using `hb'p x`.

Establish `h2` using `hb₀p x hx`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]`. Check the signs of the components of the expression. Establish `hβm : Mn μ (n • b' + b₀)` using `fun c α hα => by`. Rewrite using `[qW_nsmul_add, qW_nsmul_add]`.

Establish `h1` using `hb'm c α hα`. Establish `h2` using `hb₀m c α hα`. Establish `h3 : (n : ℤ) * qW W b' (μ c) ≤ n * qW W b' α` using `mul_le_mul_of_nonneg_left h1 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨m, γ, k, cf, hγ, hk, hcf, hkβ⟩` from `GlobalTheory.Poinc.Cover.exists_cone ℤ id φ (Fin r → ℤ) hFr _ hβs hβp`.

Establish `hγd : ∀ y, y ≠ 0 → 0 < ∑ j, γ j y y` using `fun y hy => by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `h0 : ∀ j, γ j y y = 0` using `fun j => le_antisymm ((Finset.single_le_sum (fun j _ => hγ.nonneg j y) (Finset.mem_univ j)).trans hcon) (hγ.nonneg j y)`. Establish `h1` using `LinearMap.congr_fun₂ hkβ y y`.

Establish `h2` using `hβp y hy`. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, h0, smul_zero, Finset.sum_const_zero, nsmul_eq_mul] at h1`. Establish `: (k : ℤ) * (n • b' + b₀) y y > 0` using `mul_pos (by exact_mod_cast hk) h2`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at this h1`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmem : (⟨m, γ⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) ∈ T` using `⟨hγ, hγd, _, k, cf, hk, hcf, hkβ, hβm⟩`. Take `⟨i, hi⟩` from `List.mem_iff_get.1 ((hL _).2 hmem)`. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[hi]`. Conclude with `⟨k, cf, hk, hkβ⟩`.

Use `choose f hf using key`. Take `⟨i, hi⟩` from `Finite.exists_infinite_fiber f`. Take `⟨cf, hcf⟩` from `exists_nat_comb_of_infinite φ r _ _ ((hL _).1 (List.get_mem L i)).1 b' b₀ hb's hb₀s (f ⁻¹' {i}) (Set.infinite_coe_iff.1 hi) fun n hn => by`. Use `hf n` as an intermediate fact. Rewrite `this` using `[show f n = i from hn]`.

Conclude with `this`. Conclude with `⟨i, 1, cf, one_pos, by rw [one_smul]; exact hcf⟩`.
-/
theorem exists_finite_cones : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) → (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) → ∃ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ i, IsCone id φ (γ i)) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → ∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j := by
  intro g φ hF W hW N _ hN r hr μ hμ b₀ hb₀s hb₀p hb₀m
  classical
  have hFr : IsPolFanOn id φ (Fin r → ℤ) := hF _ (by simpa using hr)
  let Mn : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)) → LinearMap.BilinForm ℤ (Fin r → ℤ) → Prop :=
    fun μ b => ∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α
  let T : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) := {x | IsCone id φ x.2 ∧
    (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) ∧ ∃ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (k : ℕ) (cf : Fin x.1 → ℕ),
      0 < k ∧ (∀ j, 0 < cf j) ∧ k • b = ∑ j, cf j • x.2 j ∧ Mn μ b}
  have hT : T.Finite := by
    obtain ⟨S, hS, hSe⟩ := hFr.finite
    let TS : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) := {x | (∀ j, x.2 j ∈ S) ∧
      Function.Injective x.2 ∧ IsCone id φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)}
    have hTS : TS.Finite := (finite_families _ S hS).subset fun x hx => ⟨hx.1, hx.2.1⟩
    have hdick := fun (x : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ))
      (h : IsCone id φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)) => GlobalTheory.T.finite_minimiser_systems_smooth_cone φ W hW N hN r x.1 x.2 h.1 h.2
    let Fμ : (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) →
        Set ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)) := fun x =>
      if h : IsCone id φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) then ((hdick x h).choose : Set _) else ∅
    let M := (⋃ x ∈ TS, Fμ x) ∩ {μ' | ∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i}
    have hM : M.Finite := (hTS.biUnion fun x _ => by
      simp only [Fμ]; split_ifs
      · exact Finset.finite_toSet _
      · exact Set.finite_empty).inter_of_left _
    let V : Set (Fin r → ℤ) := Set.range fun p : (Fin 8 → Fin r → ZMod N) × Fin 8 => μ p.1 p.2
    let E := ⋃ μ' ∈ M, {e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ) | ∀ c u, e (μ' c u) ∈ V}
    have hE : E.Finite := hM.biUnion fun μ' hμ' => by
      let Φ : ((Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) → (Fin 8 → Fin r → ZMod N) × Fin 8 → (Fin r → ℤ) :=
        fun e p => e (μ' p.1 p.2)
      refine Set.Finite.of_finite_image (f := Φ) ((Set.Finite.pi (t := fun _ => V) fun _ => Set.finite_range _).subset ?_) ?_
      · rintro _ ⟨e, he, rfl⟩ p -
        exact he p.1 p.2
      · intro e₁ _ e₂ _ h
        refine LinearEquiv.toLinearMap_injective (linearMap_eq_of_eq_on_residues N (by omega) r _ _ (Set.range fun p : (Fin 8 → Fin r → ZMod N) × Fin 8 => μ' p.1 p.2) (fun x => ⟨μ' (fun _ i => (x i : ZMod N)) 0, ⟨((fun _ i => (x i : ZMod N)), 0), rfl⟩, fun i => hμ'.2 _ _ _⟩) ?_)
        rintro _ ⟨p, rfl⟩
        exact congrFun h p
    refine ((hTS.prod hE).image fun q => (⟨q.1.1, fun j => pull q.2.symm.toLinearMap (q.1.2 j)⟩ :
      Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ))).subset ?_
    rintro ⟨m, γ⟩ ⟨hγ, hγd, b, k, cf, hk, hcf, hkb, hbm⟩
    obtain ⟨e, he⟩ := hSe m γ hγ
    obtain ⟨μ', hμ'1, hμ'2, hμ'3⟩ := exists_transport W N r μ hμ b e hbm
    have hc' := hγ.pull_equiv e
    have hd' : ∀ y, y ≠ 0 → 0 < ∑ j, pull e.toLinearMap (γ j) y y := fun y hy => by
      simpa using hγd (e y) (by simpa using hy)
    have hkb' : k • pull e.toLinearMap b = ∑ j, cf j • pull e.toLinearMap (γ j) := LinearMap.ext₂ fun x y => by
      simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hkb (e x) (e y)
    have hx' : (⟨m, fun j => pull e.toLinearMap (γ j)⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) ∈ TS :=
      ⟨he, hc'.injective, hc', hd'⟩
    refine ⟨⟨⟨m, fun j => pull e.toLinearMap (γ j)⟩, e⟩, ⟨hx', ?_⟩, ?_⟩
    · refine Set.mem_biUnion (x := μ') ⟨Set.mem_biUnion hx' ?_, hμ'1⟩ fun c u => ?_
      · show μ' ∈ Fμ ⟨m, fun j => pull e.toLinearMap (γ j)⟩
        simp only [Fμ]
        rw [dif_pos (show IsCone id φ (fun j => pull e.toLinearMap (γ j)) ∧ _ from ⟨hc', hd'⟩)]
        exact (hdick ⟨m, fun j => pull e.toLinearMap (γ j)⟩ ⟨hc', hd'⟩).choose_spec (pull e.toLinearMap b) k cf hk hcf hkb' μ' hμ'1 hμ'2
      · obtain ⟨d, hd⟩ := hμ'3 c u
        exact ⟨(d, u), hd.symm⟩
    · simp
  obtain ⟨L, hL⟩ : ∃ L : List (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)), ∀ x, x ∈ L ↔ x ∈ T :=
    ⟨hT.toFinset.toList, fun x => by simp⟩
  refine ⟨L.length, fun i => (L.get i).1, fun i => (L.get i).2, fun i => ((hL _).1 (List.get_mem L i)).1, ?_⟩
  intro b' hb's hb'p hb'm
  have key : ∀ n : ℕ, ∃ i : Fin L.length, ∃ (k : ℕ) (cf : Fin (L.get i).1 → ℕ), 0 < k ∧
      k • (n • b' + b₀) = ∑ j, cf j • (L.get i).2 j := by
    intro n
    have hβs : n • b' + b₀ ∈ balForms id (Fin r → ℤ) := mem_balForms_int.2 fun x y => by
      simp [hb's x y, hb₀s x y]
    have hβp : ∀ x, x ≠ 0 → 0 < (n • b' + b₀) x x := fun x hx => by
      have h1 := hb'p x
      have h2 := hb₀p x hx
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      positivity
    have hβm : Mn μ (n • b' + b₀) := fun c α hα => by
      rw [qW_nsmul_add, qW_nsmul_add]
      have h1 := hb'm c α hα
      have h2 := hb₀m c α hα
      have h3 : (n : ℤ) * qW W b' (μ c) ≤ n * qW W b' α := mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    obtain ⟨m, γ, k, cf, hγ, hk, hcf, hkβ⟩ := GlobalTheory.Poinc.Cover.exists_cone ℤ id φ (Fin r → ℤ) hFr _ hβs hβp
    have hγd : ∀ y, y ≠ 0 → 0 < ∑ j, γ j y y := fun y hy => by
      by_contra hcon
      push_neg at hcon
      have h0 : ∀ j, γ j y y = 0 := fun j => le_antisymm ((Finset.single_le_sum (fun j _ => hγ.nonneg j y)
        (Finset.mem_univ j)).trans hcon) (hγ.nonneg j y)
      have h1 := LinearMap.congr_fun₂ hkβ y y
      have h2 := hβp y hy
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, h0, smul_zero, Finset.sum_const_zero, nsmul_eq_mul] at h1
      have : (k : ℤ) * (n • b' + b₀) y y > 0 := mul_pos (by exact_mod_cast hk) h2
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at this h1
      linarith
    have hmem : (⟨m, γ⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) ∈ T :=
      ⟨hγ, hγd, _, k, cf, hk, hcf, hkβ, hβm⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 ((hL _).2 hmem)
    refine ⟨i, ?_⟩
    rw [hi]
    exact ⟨k, cf, hk, hkβ⟩
  choose f hf using key
  obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber f
  obtain ⟨cf, hcf⟩ := exists_nat_comb_of_infinite φ r _ _ ((hL _).1 (List.get_mem L i)).1 b' b₀ hb's hb₀s (f ⁻¹' {i})
    (Set.infinite_coe_iff.1 hi) fun n hn => by
      have := hf n
      rw [show f n = i from hn] at this
      exact this
  exact ⟨i, 1, cf, one_pos, by rw [one_smul]; exact hcf⟩

end GlobalTheory.Poinc.Cells

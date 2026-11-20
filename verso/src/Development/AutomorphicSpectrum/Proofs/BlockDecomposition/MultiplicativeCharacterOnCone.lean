import Mathlib

namespace GlobalTheory.CompanionTheory.StrictCone

/- English proof (translation)
Establish `hmem : ∀ k : ℕ, k • s₀ + s₀ ∈ S ∧ f (k • s₀ + s₀) ≠ 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using ⟨hs₀, hne⟩`. Consider the case `succ n ih`.

Establish `h1 : (n + 1) • s₀ + s₀ = (n • s₀ + s₀) + s₀` using `by rw [succ_nsmul]`. Rewrite using `[h1]`. Use `⟨hS _ ih.1 _ hs₀, ?_⟩` and prove the remaining obligations. Rewrite using `[hf _ ih.1 _ hs₀]`. Conclude with `mul_ne_zero ih.2 hne`.

Establish `hmem' : ∀ k : ℕ, 0 < k → k • s₀ ∈ S ∧ f (k • s₀) ≠ 0`. Introduce `k hk`. Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[succ_nsmul]`. Conclude with `hmem n`.

Establish `hnz : ∀ z ∈ S, f z ≠ 0`. Introduce `z hz h0`. Take `⟨k, hk, hw⟩` from `arch (-z)`. Establish `h2 : k • s₀ = z + (k • s₀ + -z)` using `by abel`. Establish `h3` using `(hmem' k hk).2`.

Rewrite `h3` using `[h2, hf _ hz _ hw, h0, zero_mul]`. Conclude with `h3 rfl`. Establish `wd : ∀ c₁ ∈ S, ∀ c₂ ∈ S, ∀ d₁ ∈ S, ∀ d₂ ∈ S, c₁ - c₂ = d₁ - d₂ → f c₁ / f c₂ = f d₁ / f d₂`. Introduce `c₁ h₁ c₂ h₂ d₁ h₃ d₂ h₄ h`. Establish `e : c₁ + d₂ = d₁ + c₂`.

Establish `: c₁ + d₂ - (d₁ + c₂) = (c₁ - c₂) - (d₁ - d₂)` using `by abel`. Rewrite using `[← sub_eq_zero, this, h, sub_self]`. Establish `e'` using `congrArg f e`. Rewrite `e'` using `[hf _ h₁ _ h₄, hf _ h₃ _ h₂]`. Rewrite using `[div_eq_div_iff (hnz _ h₂) (hnz _ h₄)]`.

Conclude with `e'`. Use `choose k hk hd using arch`. Establish `hc : ∀ g, k g • s₀ ∈ S` using `fun g => (hmem' _ (hk g)).1`. Set `φ : G → ℂˣ` to `fun g => Units.mk0 (f (k g • s₀ + g) / f (k g • s₀)) (div_ne_zero (hnz _ (hd g)) (hnz _ (hc g)))`. Use `⟨φ, ?_, ?_⟩` and prove the remaining obligations.

Introduce `g h`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [φ, Units.val_mul, Units.val_mk0]`. Use `wd _ (hd (g + h)) _ (hc (g + h)) _ (hS _ (hd g) _ (hd h)) _ (hS _ (hc g) _ (hc h)) (by abel)` as an intermediate fact. Rewrite using `[this, hf _ (hd g) _ (hd h), hf _ (hc g) _ (hc h), mul_div_mul_comm]`.

Introduce `s hs`. Simplify using `only [φ, Units.val_mk0]`. Rewrite using `[hf _ (hc s) _ hs, mul_div_cancel_left₀ _ (hnz _ (hc s))]`.
-/
theorem exists_char_of_mul_on_cone {G : Type*} [AddCommGroup G] (S : Set G)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (f : G → ℂ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x * f y) (s₀ : G) (hs₀ : s₀ ∈ S) (hne : f s₀ ≠ 0)
    (arch : ∀ g : G, ∃ k : ℕ, 0 < k ∧ k • s₀ + g ∈ S) :
    ∃ φ : G → ℂˣ, (∀ g h, φ (g + h) = φ g * φ h) ∧ ∀ s ∈ S, f s = (φ s : ℂ) := by
  have hmem : ∀ k : ℕ, k • s₀ + s₀ ∈ S ∧ f (k • s₀ + s₀) ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨hs₀, hne⟩
    | succ n ih =>
      have h1 : (n + 1) • s₀ + s₀ = (n • s₀ + s₀) + s₀ := by rw [succ_nsmul]
      rw [h1]
      refine ⟨hS _ ih.1 _ hs₀, ?_⟩
      rw [hf _ ih.1 _ hs₀]
      exact mul_ne_zero ih.2 hne
  have hmem' : ∀ k : ℕ, 0 < k → k • s₀ ∈ S ∧ f (k • s₀) ≠ 0 := by
    intro k hk
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [succ_nsmul]
    exact hmem n
  have hnz : ∀ z ∈ S, f z ≠ 0 := by
    intro z hz h0
    obtain ⟨k, hk, hw⟩ := arch (-z)
    have h2 : k • s₀ = z + (k • s₀ + -z) := by abel
    have h3 := (hmem' k hk).2
    rw [h2, hf _ hz _ hw, h0, zero_mul] at h3
    exact h3 rfl
  have wd : ∀ c₁ ∈ S, ∀ c₂ ∈ S, ∀ d₁ ∈ S, ∀ d₂ ∈ S, c₁ - c₂ = d₁ - d₂ →
      f c₁ / f c₂ = f d₁ / f d₂ := by
    intro c₁ h₁ c₂ h₂ d₁ h₃ d₂ h₄ h
    have e : c₁ + d₂ = d₁ + c₂ := by
      have : c₁ + d₂ - (d₁ + c₂) = (c₁ - c₂) - (d₁ - d₂) := by abel
      rw [← sub_eq_zero, this, h, sub_self]
    have e' := congrArg f e
    rw [hf _ h₁ _ h₄, hf _ h₃ _ h₂] at e'
    rw [div_eq_div_iff (hnz _ h₂) (hnz _ h₄)]
    exact e'
  choose k hk hd using arch
  have hc : ∀ g, k g • s₀ ∈ S := fun g => (hmem' _ (hk g)).1
  let φ : G → ℂˣ := fun g =>
    Units.mk0 (f (k g • s₀ + g) / f (k g • s₀)) (div_ne_zero (hnz _ (hd g)) (hnz _ (hc g)))
  refine ⟨φ, ?_, ?_⟩
  · intro g h
    apply Units.ext
    simp only [φ, Units.val_mul, Units.val_mk0]
    have := wd _ (hd (g + h)) _ (hc (g + h)) _ (hS _ (hd g) _ (hd h)) _ (hS _ (hc g) _ (hc h))
      (by abel)
    rw [this, hf _ (hd g) _ (hd h), hf _ (hc g) _ (hc h), mul_div_mul_comm]
  · intro s hs
    simp only [φ, Units.val_mk0]
    rw [hf _ (hc s) _ hs, mul_div_cancel_left₀ _ (hnz _ (hc s))]

/- English proof (translation)
Set `F : (Fin n → ℤ) →+ Additive ℂˣ` to `AddMonoidHom.mk' (fun g => Additive.ofMul (φ g)) (fun g g' => by rw [h]; rfl)`. Establish `hx : x = ∑ i, x i • (Pi.single i (1 : ℤ) : Fin n → ℤ)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `h2 : F x = ∑ i, x i • F (Pi.single i 1)` using `by conv_lhs => rw [hx]`.

Rewrite using `[map_sum]`. Simplify using `only [map_zsmul]`. Establish `h3` using `congrArg Additive.toMul h2`. Simplify `h3` using `[F, toMul_sum]`.
-/
theorem char_eq_prod {n : ℕ} (φ : (Fin n → ℤ) → ℂˣ) (h : ∀ g g', φ (g + g') = φ g * φ g') (x : Fin n → ℤ) :
    φ x = ∏ i, φ (Pi.single i 1) ^ x i := by
  let F : (Fin n → ℤ) →+ Additive ℂˣ :=
    AddMonoidHom.mk' (fun g => Additive.ofMul (φ g)) (fun g g' => by rw [h]; rfl)
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℤ) : Fin n → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : F x = ∑ i, x i • F (Pi.single i 1) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    simp only [map_zsmul]
  have h3 := congrArg Additive.toMul h2
  simpa [F, toMul_sum] using h3

/- English proof (translation)
Use `Finset.induction_on (Finset.univ : Finset (Fin n)) (by simp) ?_` and prove the remaining obligations. Introduce `i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]`.
-/
theorem zpow_sum_units (Q : ℂˣ) {n : ℕ} (e : Fin n → ℤ) : Q ^ (∑ i, e i) = ∏ i, Q ^ e i := by
  classical
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

/- English proof (translation)
Use `⟨fun i => φ (Pi.single i 1) * Q ^ (-c i), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[char_eq_prod φ h x, zpow_sum_units, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_zpow, ← zpow_mul, mul_left_comm, ← zpow_add]`. Simplify using the standard rewrite rules.
-/
theorem char_split {n : ℕ} (c : Fin n → ℤ) (Q : ℂˣ) (φ : (Fin n → ℤ) → ℂˣ)
    (h : ∀ g g', φ (g + g') = φ g * φ g') :
    ∃ ξ : Fin n → ℂˣ, ∀ x, φ x = Q ^ (∑ i, c i * x i) * ∏ i, ξ i ^ x i := by
  refine ⟨fun i => φ (Pi.single i 1) * Q ^ (-c i), fun x => ?_⟩
  rw [char_eq_prod φ h x, zpow_sum_units, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_zpow, ← zpow_mul, mul_left_comm, ← zpow_add]
  simp

def IsStrict {n : ℕ} (x : Fin n → ℤ) : Prop := ∀ i j, i < j → x j + 1 ≤ x i

/- English proof (translation)
Introduce `i j hij`. Use `hx i j hij` as an intermediate fact. Use `hy i j hij` as an intermediate fact. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem IsStrict.add {n : ℕ} {x y : Fin n → ℤ} (hx : IsStrict x) (hy : IsStrict y) :
    IsStrict (x + y) := by
  intro i j hij
  have := hx i j hij
  have := hy i j hij
  simp only [Pi.add_apply]
  omega

/- English proof (translation)
Use `⟨1 + ∑ i, ∑ j, (g i - g j).natAbs, fun k hk i j hij => ?_⟩` and prove the remaining obligations. Establish `h1 : (g j - g i).natAbs ≤ ∑ i, ∑ j, (g i - g j).natAbs` using `(Finset.single_le_sum (f := fun j' => (g j' - g i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans (by`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.single_le_sum (f := fun i' => ∑ j', (g j' - g i').natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))`. Establish `h2 : s j + 1 ≤ s i` using `hs i j hij`.

Establish `h3 : (k : ℤ) * (s j + 1) ≤ (k : ℤ) * s i` using `mul_le_mul_of_nonneg_left h2 (by positivity)`. Establish `h4 : (g j - g i) ≤ ((g j - g i).natAbs : ℤ)` using `by omega`. Generalize the expression as in `(∑ i, ∑ j, (g i - g j).natAbs) = T at hk h1`. Establish `h5 : (1 : ℤ) + T ≤ k` using `by exact_mod_cast hk`. Establish `h6 : ((g j - g i).natAbs : ℤ) ≤ T` using `by exact_mod_cast h1`.

Rewrite using `[Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem IsStrict.arch {n : ℕ} {s : Fin n → ℤ} (hs : IsStrict s) (g : Fin n → ℤ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → IsStrict (k • s + g) := by
  refine ⟨1 + ∑ i, ∑ j, (g i - g j).natAbs, fun k hk i j hij => ?_⟩
  have h1 : (g j - g i).natAbs ≤ ∑ i, ∑ j, (g i - g j).natAbs :=
    (Finset.single_le_sum (f := fun j' => (g j' - g i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (by
        rw [Finset.sum_comm]
        exact Finset.single_le_sum (f := fun i' => ∑ j', (g j' - g i').natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have h2 : s j + 1 ≤ s i := hs i j hij
  have h3 : (k : ℤ) * (s j + 1) ≤ (k : ℤ) * s i :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (g j - g i) ≤ ((g j - g i).natAbs : ℤ) := by omega
  generalize (∑ i, ∑ j, (g i - g j).natAbs) = T at hk h1
  have h5 : (1 : ℤ) + T ≤ k := by exact_mod_cast hk
  have h6 : ((g j - g i).natAbs : ℤ) ≤ T := by exact_mod_cast h1
  rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
  nlinarith

/- English proof (translation)
Introduce `a b q hq χ hχ ⟨x₀, y₀, hx₀, hy₀, hne⟩`. Set `S : Set ((Fin a → ℤ) × (Fin b → ℤ))` to `{z | IsStrict z.1 ∧ IsStrict z.2}`. Take `⟨φ, hφ, hfφ⟩` from `exists_char_of_mul_on_cone S (fun x hx y hy => ⟨hx.1.add hy.1, hx.2.add hy.2⟩) (fun z => χ z.1 z.2) (fun x hx y hy => hχ _ _ _ _ hx.1 hy.1 hx.2 hy.2) (x₀, y₀) ⟨hx₀, hy₀⟩ hne (fun g => by`. Take `⟨K₁, h₁⟩` from `IsStrict.arch (s := x₀) hx₀ g.1`. Take `⟨K₂, h₂⟩` from `IsStrict.arch (s := y₀) hy₀ g.2`.

Use `⟨K₁ + K₂ + 1, by omega, ?_, ?_⟩` and prove the remaining obligations. Conclude with `h₁ _ (by omega)`. Conclude with `h₂ _ (by omega))`. Set `Q : ℂˣ` to `Units.mk0 q hq`. Take `⟨ξa, ha⟩` from `char_split (fun i : Fin a => (a : ℤ) - 1 - 2 * (i : ℕ)) Q (fun x => φ (x, 0)) (fun g g' => by rw [← hφ]; simp)`.

Take `⟨ξb, hb⟩` from `char_split (fun i : Fin b => (b : ℤ) - 1 - 2 * (i : ℕ)) Q (fun y => φ (0, y)) (fun g g' => by rw [← hφ]; simp)`. Use `⟨ξa, ξb, fun x y hx hy => ?_⟩` and prove the remaining obligations. Establish `h1 : χ x y = (φ (x, y) : ℂ)` using `hfφ (x, y) ⟨hx, hy⟩`. Establish `h2 : φ (x, y) = φ (x, 0) * φ (0, y)` using `by rw [← hφ]; simp`. Rewrite using `[h1, h2, ha x, hb y]`.

Simplify using `only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Q, Units.coe_prod]`.
-/
theorem mul_on_cone_eq_delta_char : ∀ (a b : ℕ) (q : ℂ), q ≠ 0 → ∀ χ : (Fin a → ℤ) → (Fin b → ℤ) → ℂ, (∀ x x' y y', (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → x' j + 1 ≤ x' i) → (∀ i j, i < j → y j + 1 ≤ y i) → (∀ i j, i < j → y' j + 1 ≤ y' i) → χ (x + x') (y + y') = χ x y * χ x' y') → (∃ x y, (∀ i j, i < j → x j + 1 ≤ x i) ∧ (∀ i j, i < j → y j + 1 ≤ y i) ∧ χ x y ≠ 0) → ∃ (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ∀ x y, (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → y j + 1 ≤ y i) → χ x y = q ^ (∑ i : Fin a, ((a : ℤ) - 1 - 2 * (i : ℕ)) * x i) * (∏ i, ((ξa i ^ x i : ℂˣ) : ℂ)) * (q ^ (∑ i : Fin b, ((b : ℤ) - 1 - 2 * (i : ℕ)) * y i) * ∏ i, ((ξb i ^ y i : ℂˣ) : ℂ)) := by
  intro a b q hq χ hχ ⟨x₀, y₀, hx₀, hy₀, hne⟩
  let S : Set ((Fin a → ℤ) × (Fin b → ℤ)) := {z | IsStrict z.1 ∧ IsStrict z.2}
  obtain ⟨φ, hφ, hfφ⟩ := exists_char_of_mul_on_cone S
    (fun x hx y hy => ⟨hx.1.add hy.1, hx.2.add hy.2⟩) (fun z => χ z.1 z.2)
    (fun x hx y hy => hχ _ _ _ _ hx.1 hy.1 hx.2 hy.2) (x₀, y₀) ⟨hx₀, hy₀⟩ hne
    (fun g => by
      obtain ⟨K₁, h₁⟩ := IsStrict.arch (s := x₀) hx₀ g.1
      obtain ⟨K₂, h₂⟩ := IsStrict.arch (s := y₀) hy₀ g.2
      refine ⟨K₁ + K₂ + 1, by omega, ?_, ?_⟩
      · exact h₁ _ (by omega)
      · exact h₂ _ (by omega))
  let Q : ℂˣ := Units.mk0 q hq
  obtain ⟨ξa, ha⟩ := char_split (fun i : Fin a => (a : ℤ) - 1 - 2 * (i : ℕ)) Q
    (fun x => φ (x, 0)) (fun g g' => by rw [← hφ]; simp)
  obtain ⟨ξb, hb⟩ := char_split (fun i : Fin b => (b : ℤ) - 1 - 2 * (i : ℕ)) Q
    (fun y => φ (0, y)) (fun g g' => by rw [← hφ]; simp)
  refine ⟨ξa, ξb, fun x y hx hy => ?_⟩
  have h1 : χ x y = (φ (x, y) : ℂ) := hfφ (x, y) ⟨hx, hy⟩
  have h2 : φ (x, y) = φ (x, 0) * φ (0, y) := by rw [← hφ]; simp
  rw [h1, h2, ha x, hb y]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Q, Units.coe_prod]

end GlobalTheory.CompanionTheory.StrictCone

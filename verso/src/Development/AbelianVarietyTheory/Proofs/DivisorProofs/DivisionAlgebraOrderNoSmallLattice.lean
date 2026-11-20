import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨o, rfl⟩` from `hx`. Conclude with `⟨1, one_pos, o, by simp⟩`. Consider the case `zero => exact ⟨1, one_pos, 0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨n₁, hn₁, c₁, hc₁⟩` from `hx`. Take `⟨n₂, hn₂, c₂, hc₂⟩` from `hy`. Use `⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, (n₂ : O) * c₁ + (n₁ : O) * c₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, map_natCast, map_natCast, hc₁, hc₂, ← nsmul_eq_mul, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ n₂, ← Nat.cast_smul_eq_nsmul ℚ n₁, smul_smul, smul_smul, smul_add]`.

Use `push_cast`. Rewrite using `[mul_comm (n₂ : ℚ) (n₁ : ℚ)]`. Consider the case `smul q x _ hx`. Take `⟨n, hn, c, hc⟩` from `hx`. Use `⟨q.den * n, Nat.mul_pos q.den_pos hn, (q.num : O) * c, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_intCast, hc, smul_smul]`. Rewrite using `[show ((q.num : B)) = algebraMap ℚ B (q.num : ℚ) by simp, ← Algebra.smul_def, smul_smul]`. Use `congr 1`. Use `push_cast`. Rewrite using `[← Rat.mul_den_eq_num]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem divAlg_clear_denominators {B : Type} [Ring B] [Algebra ℚ B] {O : Type} [Ring O]
    (ι : O →+* B) (v : B) (hv : v ∈ Submodule.span ℚ (Set.range ι)) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : O, ι c = (n : ℚ) • v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨o, rfl⟩ := hx
    exact ⟨1, one_pos, o, by simp⟩
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, hn₁, c₁, hc₁⟩ := hx
    obtain ⟨n₂, hn₂, c₂, hc₂⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, (n₂ : O) * c₁ + (n₁ : O) * c₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_natCast, map_natCast, hc₁, hc₂, ← nsmul_eq_mul,
      ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ n₂, ← Nat.cast_smul_eq_nsmul ℚ n₁, smul_smul,
      smul_smul, smul_add]
    push_cast
    rw [mul_comm (n₂ : ℚ) (n₁ : ℚ)]
  | smul q x _ hx =>
    obtain ⟨n, hn, c, hc⟩ := hx
    refine ⟨q.den * n, Nat.mul_pos q.den_pos hn, (q.num : O) * c, ?_⟩
    rw [map_mul, map_intCast, hc, smul_smul]
    rw [show ((q.num : B)) = algebraMap ℚ B (q.num : ℚ) by simp, ← Algebra.smul_def, smul_smul]
    congr 1
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Establish `hιa : ι a ≠ 0` using `fun h => h0 (hinj (by simpa using h))`. Take `⟨u, hu⟩` from `hunit _ hιa`. Take `⟨n, hn, c, hc⟩` from `divAlg_clear_denominators ι (↑u⁻¹ : B) (by rw [hspan]; trivial)`. Establish `hca : c * a = (n : O)`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, hc, map_natCast, ← hu, Algebra.smul_mul_assoc, Units.inv_mul, Algebra.smul_def, mul_one]`. Simplify using the standard rewrite rules. Establish `h1 : ρ (c * a) x = 0` using `by rw [map_mul, Module.End.mul_apply, ha, map_zero]`. Rewrite `h1` using `[hca, map_natCast]`.

Establish `h2 : (n : ℤ) • x = 0`. Rewrite using `[natCast_zsmul]`. Simplify `h1` using `[Module.End.natCast_apply]`. Break down `smul_eq_zero.mp h2 with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers.

Conclude with `hx h`.
-/
theorem divAlg_smul_injective {B : Type} [Ring B] [Algebra ℚ B] {O : Type} [Ring O]
    (ι : O →+* B) (hunit : ∀ x : B, x ≠ 0 → IsUnit x) (hinj : Function.Injective ι)
    (hspan : Submodule.span ℚ (Set.range ι) = ⊤)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] (ρ : O →+* Module.End ℤ X)
    (x : X) (hx : x ≠ 0) (a : O) (ha : ρ a x = 0) : a = 0 := by
  by_contra h0
  have hιa : ι a ≠ 0 := fun h => h0 (hinj (by simpa using h))
  obtain ⟨u, hu⟩ := hunit _ hιa
  obtain ⟨n, hn, c, hc⟩ := divAlg_clear_denominators ι (↑u⁻¹ : B) (by rw [hspan]; trivial)
  have hca : c * a = (n : O) := by
    apply hinj
    rw [map_mul, hc, map_natCast, ← hu, Algebra.smul_mul_assoc, Units.inv_mul,
      Algebra.smul_def, mul_one]
    simp
  have h1 : ρ (c * a) x = 0 := by rw [map_mul, Module.End.mul_apply, ha, map_zero]
  rw [hca, map_natCast] at h1
  have h2 : (n : ℤ) • x = 0 := by
    rw [natCast_zsmul]
    simpa [Module.End.natCast_apply] using h1
  rcases smul_eq_zero.mp h2 with h | h
  · omega
  · exact hx h

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `B _ _ _ O _ ι hunit hinj hspan X _ _ _ ρ hlt`. Assume the negation of the conclusion as `hne`. Establish `hnt : Nontrivial X` using `Module.nontrivial_of_finrank_pos (R := ℤ) (Nat.pos_of_ne_zero hne)`. Take `⟨x, hx⟩` from `exists_ne (0 : X)`. Set `φ : O →ₗ[ℤ] X` to `(AddMonoidHom.mk' (fun a => ρ a x) (by intro a b; simp)).toIntLinearMap`.

Establish `hφ : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `a ha`. Conclude with `divAlg_smul_injective ι hunit hinj hspan ρ x hx a ha`. Set `ι' : O →ₗ[ℤ] B` to `ι.toAddMonoidHom.toIntLinearMap`.

Take `⟨b, hbsub, hbspan, hbli⟩` from `exists_linearIndependent ℚ (Set.range ι)`. Rewrite `hbspan` using `[hspan]`. Set `e` to `Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])`. Use `choose f hf using fun i : b => hbsub i.2`. Establish `li1 : LinearIndependent ℤ (fun i : b => (i : B))` using `hbli.restrict_scalars' ℤ`.

Establish `li2 : LinearIndependent ℤ f`. Apply `LinearIndependent.of_comp ι'` to reduce the goal to its premises. Use `li1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `hf i`.

Establish `li3 : LinearIndependent ℤ (φ ∘ f)` using `li2.map' φ (LinearMap.ker_eq_bot.mpr hφ)`. Establish `hc` using `li3.cardinal_le_rank`. Rewrite `hc` using `[Module.Basis.mk_eq_rank'' e, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank]`. Use `Nat.cast_le.mp hc` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem divAlg_order_no_small_lattice : ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B]
    (O : Type) [Ring O] (ι : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective ι →
    Submodule.span ℚ (Set.range ι) = ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (ρ : O →+* Module.End ℤ X), Module.finrank ℤ X < Module.finrank ℚ B →
    Module.finrank ℤ X = 0 := by
  intro B _ _ _ O _ ι hunit hinj hspan X _ _ _ ρ hlt
  by_contra hne
  have hnt : Nontrivial X := Module.nontrivial_of_finrank_pos (R := ℤ) (Nat.pos_of_ne_zero hne)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)

  let φ : O →ₗ[ℤ] X := (AddMonoidHom.mk' (fun a => ρ a x) (by intro a b; simp)).toIntLinearMap
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact divAlg_smul_injective ι hunit hinj hspan ρ x hx a ha
  let ι' : O →ₗ[ℤ] B := ι.toAddMonoidHom.toIntLinearMap
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℚ (Set.range ι)
  rw [hspan] at hbspan
  let e := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  choose f hf using fun i : b => hbsub i.2
  have li1 : LinearIndependent ℤ (fun i : b => (i : B)) := hbli.restrict_scalars' ℤ
  have li2 : LinearIndependent ℤ f := by
    apply LinearIndependent.of_comp ι'
    convert li1 using 1
    funext i
    exact hf i
  have li3 : LinearIndependent ℤ (φ ∘ f) := li2.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  have hc := li3.cardinal_le_rank
  rw [Module.Basis.mk_eq_rank'' e, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at hc
  have := Nat.cast_le.mp hc
  omega

end GlobalTheory

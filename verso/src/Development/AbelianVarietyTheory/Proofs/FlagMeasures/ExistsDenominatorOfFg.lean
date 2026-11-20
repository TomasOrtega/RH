import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Take `⟨s, hs⟩` from `Submodule.FG.map₂ B hM hM`. Use `⟨∏ a ∈ s, a.den, Finset.prod_pos fun a _ => a.den_pos, ?_⟩` and prove the remaining obligations. Establish `key : ∀ r ∈ Submodule.span ℤ (s : Set ℚ), ∃ n : ℤ, ((∏ a ∈ s, a.den : ℕ) : ℚ) * r = n`. Introduce `r hr`. Proceed by induction on `hr using Submodule.span_induction with`.

Consider the case `mem a ha`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem (fun a : ℚ => a.den) (Finset.mem_coe.mp ha)`. Use `⟨c * a.num, ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`. Use `push_cast`.

Rewrite using `[← Rat.den_mul_eq_num]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨m, hm⟩` from `ha`.

Take `⟨n, hn⟩` from `hb`. Conclude with `⟨m + n, by rw [mul_add, hm, hn]; push_cast; ring⟩`. Consider the case `smul c a _ ha`. Take `⟨m, hm⟩` from `ha`. Conclude with `⟨c * m, by rw [zsmul_eq_mul, mul_left_comm, hm]; push_cast; ring⟩`.

Introduce `x hx y hy`. Conclude with `key _ (hs ▸ Submodule.apply_mem_map₂ B hx hy)`.
-/
theorem exists_denominator_of_fg {V : Type} [AddCommGroup V] (B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ)
    (M : Submodule ℤ V) (hM : M.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, (d : ℚ) * B x y = n := by
  obtain ⟨s, hs⟩ := Submodule.FG.map₂ B hM hM
  refine ⟨∏ a ∈ s, a.den, Finset.prod_pos fun a _ => a.den_pos, ?_⟩
  have key : ∀ r ∈ Submodule.span ℤ (s : Set ℚ), ∃ n : ℤ, ((∏ a ∈ s, a.den : ℕ) : ℚ) * r = n := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a : ℚ => a.den) (Finset.mem_coe.mp ha)
      refine ⟨c * a.num, ?_⟩
      rw [hc]
      push_cast
      rw [← Rat.den_mul_eq_num]; ring
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨m, hm⟩ := ha
      obtain ⟨n, hn⟩ := hb
      exact ⟨m + n, by rw [mul_add, hm, hn]; push_cast; ring⟩
    | smul c a _ ha =>
      obtain ⟨m, hm⟩ := ha
      exact ⟨c * m, by rw [zsmul_eq_mul, mul_left_comm, hm]; push_cast; ring⟩
  intro x hx y hy
  exact key _ (hs ▸ Submodule.apply_mem_map₂ B hx hy)

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ h U X M γ g hs hXU hrad hpos hM hMU hγ hγX hg hcong`. Establish `hiso : ∀ x y, h (γ x) (γ y) = h x y` using `hγ`. Establish `hrad' : ∀ y ∈ U, ∀ x ∈ X, h y x = 0` using `fun y hy x hx => by`. Rewrite using `[← hs.eq x y, hrad x hx y hy, map_zero]`. Set `B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ` to `LinearMap.mk₂ ℤ (fun x y => Algebra.trace ℚ K (h x y)) (fun a b c => by simp) (fun c a b => by rw [map_zsmul h, LinearMap.smul_apply, map_zsmul]) (fun a b c => by simp) (fun c a b => by rw [map_zsmul (h a), map_zsmul])`.

Establish `hB : ∀ x y, B x y = Algebra.trace ℚ K (h x y)` using `fun _ _ => rfl`. Take `⟨d, hd, hden⟩` from `exists_denominator_of_fg B (M.restrictScalars ℤ) (hM.restrictScalars)`. Establish `hnn : ∀ x ∈ U, 0 ≤ B x x` using `fun x hx => by`. Distinguish the cases in `hxX : x ∈ X`. Rewrite using `[hB, hrad x hxX x hx, map_zero]`.

Conclude with `(hpos x hx hxX).le`. Establish `main : ∀ n : ℕ, ∀ x ∈ M, (d : ℚ) * B x x < n → γ x - x ∈ X`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `x hx hlt`. Use `hnn x (hMU x hx)` as an intermediate fact. Establish `: (0 : ℚ) ≤ d * B x x` using `by positivity`. Simplify using `at hlt`. Combine the linear equalities and inequalities to obtain the conclusion.

Consider the case `succ n ih`. Introduce `x hx hlt`. Distinguish the cases in `hxX : x ∈ X`. Conclude with `X.sub_mem (hγX x hxX) hxX`. Take `⟨y, hy, hu⟩` from `hcong x hx`.

Use `set u := γ x - x - (g : K) • y with hu_def`. Use `set z := γ x - x with hz_def`. Establish `hz : z = (g : K) • y + u` using `by rw [hu_def]; abel`. Establish `hxU` using `hMU x hx`. Establish `hyU` using `hMU y hy`.

Establish `hzU : z ∈ U` using `hz ▸ U.add_mem (U.smul_mem _ hyU) (hXU hu)`. Establish `hγx : γ x = x + z` using `by rw [hz_def]; abel`. Establish `hγxU : γ x ∈ U` using `hγx ▸ U.add_mem hxU hzU`. Establish `h1 : B z z = (g : ℚ) ^ 2 * B y y`. Establish `e1 : B u z = 0` using `by rw [hB, hrad u hu z hzU, map_zero]`.

Establish `e2 : B y u = 0` using `by rw [hB, hrad' y hyU u hu, map_zero]`. Establish `hz' : z = (g : ℤ) • y + u` using `by rw [hz, natCast_zsmul, Nat.cast_smul_eq_nsmul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : B z z + B (γ x + x) (γ x + x) = 4 * B x x`. Establish `e : B (γ x) (γ x) = B x x` using `by rw [hB, hB, hiso]`.

Rewrite using `[hz_def]`. Simplify using `only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, e]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `hnn _ (U.add_mem hγxU hxU)`. Establish `hxp : 0 < B x x` using `hpos x hxU hxX`.

Establish `hyn` using `hnn y hyU`. Establish `hg' : (9 : ℚ) ≤ (g : ℚ) ^ 2`. Establish `: (3 : ℚ) ≤ g` using `by exact_mod_cast hg`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlt' : B y y < B x x` using `by nlinarith`.

Establish `hd' : (0 : ℚ) < d` using `by exact_mod_cast hd`. Take `⟨a, ha⟩` from `hden x hx x hx`. Take `⟨b, hb⟩` from `hden y hy y hy`. Establish `hab : b < a`. Establish `: (b : ℚ) < a` using `by rw [← ha, ← hb]; exact mul_lt_mul_of_pos_left hlt' hd'`.

Conclude with `this` after adjusting the coercions. Establish `han : a < n + 1`. Rewrite `hlt` using `[ha]`. Conclude with `hlt` after adjusting the coercions. Establish `hyX : γ y - y ∈ X` using `ih y hy (by`.

Rewrite using `[hb]`. Establish `: b < n` using `by omega`. Conclude with `this)` after adjusting the coercions. Establish `hw : γ z - z ∈ X`. Establish `: γ z - z = (g : K) • (γ y - y) + (γ u - u)`.

Rewrite using `[hz, map_add, map_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `X.add_mem (X.smul_mem _ hyX) (X.sub_mem (hγX u hu) hu)`. Establish `hzz : h z z = 0`.

Establish `e` using `hiso x z`. Establish `e2 : h (γ x) (γ z - z) = 0` using `hrad' _ hγxU _ hw`. Rewrite `e2` using `[map_sub, e, hγx, map_add, LinearMap.add_apply]`. Take the linear combination `-e2`. Assume the negation of the conclusion as `hzX`.

Use `hpos z hzU hzX` as an intermediate fact. Rewrite `this` using `[hzz, map_zero]`. Conclude with `lt_irrefl _ this`. Introduce `x hx`. Take `⟨n, hn⟩` from `exists_nat_gt ((d : ℚ) * B x x)`.

Conclude with `main n x hx hn`.
-/
theorem isom_sub_mem_of_congr : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (U X : Submodule K V) (M : Submodule (𝓞 K) V) (γ : V ≃ₗ[K] V) (g : ℕ), h.IsSymm → X ≤ U → (∀ x ∈ X, ∀ y ∈ U, h x y = 0) → (∀ x ∈ U, x ∉ X → 0 < Algebra.trace ℚ K (h x x)) → M.FG → (∀ x ∈ M, x ∈ U) → γ ∈ Formalism.HermitianLatticesTheory.isom h → (∀ x ∈ X, γ x ∈ X) → 3 ≤ g → (∀ x ∈ M, ∃ y ∈ M, γ x - x - (g : K) • y ∈ X) → ∀ x ∈ M, γ x - x ∈ X := by
  intro K V _ _ _ _ _ _ _ _ h U X M γ g hs hXU hrad hpos hM hMU hγ hγX hg hcong
  have hiso : ∀ x y, h (γ x) (γ y) = h x y := hγ
  have hrad' : ∀ y ∈ U, ∀ x ∈ X, h y x = 0 := fun y hy x hx => by
    rw [← hs.eq x y, hrad x hx y hy, map_zero]
  let B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ := LinearMap.mk₂ ℤ (fun x y => Algebra.trace ℚ K (h x y))
    (fun a b c => by simp) (fun c a b => by rw [map_zsmul h, LinearMap.smul_apply, map_zsmul])
    (fun a b c => by simp)
    (fun c a b => by rw [map_zsmul (h a), map_zsmul])
  have hB : ∀ x y, B x y = Algebra.trace ℚ K (h x y) := fun _ _ => rfl
  obtain ⟨d, hd, hden⟩ := exists_denominator_of_fg B (M.restrictScalars ℤ) (hM.restrictScalars)
  have hnn : ∀ x ∈ U, 0 ≤ B x x := fun x hx => by
    by_cases hxX : x ∈ X
    · rw [hB, hrad x hxX x hx, map_zero]
    · exact (hpos x hx hxX).le
  have main : ∀ n : ℕ, ∀ x ∈ M, (d : ℚ) * B x x < n → γ x - x ∈ X := by
    intro n
    induction n with
    | zero =>
      intro x hx hlt
      have := hnn x (hMU x hx)
      have : (0 : ℚ) ≤ d * B x x := by positivity
      simp at hlt
      linarith
    | succ n ih =>
      intro x hx hlt
      by_cases hxX : x ∈ X
      · exact X.sub_mem (hγX x hxX) hxX
      obtain ⟨y, hy, hu⟩ := hcong x hx
      set u := γ x - x - (g : K) • y with hu_def
      set z := γ x - x with hz_def
      have hz : z = (g : K) • y + u := by rw [hu_def]; abel
      have hxU := hMU x hx
      have hyU := hMU y hy
      have hzU : z ∈ U := hz ▸ U.add_mem (U.smul_mem _ hyU) (hXU hu)
      have hγx : γ x = x + z := by rw [hz_def]; abel
      have hγxU : γ x ∈ U := hγx ▸ U.add_mem hxU hzU
      have h1 : B z z = (g : ℚ) ^ 2 * B y y := by
        have e1 : B u z = 0 := by rw [hB, hrad u hu z hzU, map_zero]
        have e2 : B y u = 0 := by rw [hB, hrad' y hyU u hu, map_zero]
        have hz' : z = (g : ℤ) • y + u := by rw [hz, natCast_zsmul, Nat.cast_smul_eq_nsmul]
        calc B z z = B ((g : ℤ) • y + u) z := by rw [← hz']
          _ = (g : ℤ) • B y z := by rw [map_add, LinearMap.add_apply, e1, map_smul]; simp
          _ = (g : ℤ) • B y ((g : ℤ) • y + u) := by rw [← hz']
          _ = _ := by rw [map_add, e2, map_smul]; simp; ring
      have h2 : B z z + B (γ x + x) (γ x + x) = 4 * B x x := by
        have e : B (γ x) (γ x) = B x x := by rw [hB, hB, hiso]
        rw [hz_def]
        simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, e]
        ring
      have h3 := hnn _ (U.add_mem hγxU hxU)
      have hxp : 0 < B x x := hpos x hxU hxX
      have hyn := hnn y hyU
      have hg' : (9 : ℚ) ≤ (g : ℚ) ^ 2 := by
        have : (3 : ℚ) ≤ g := by exact_mod_cast hg
        nlinarith
      have hlt' : B y y < B x x := by nlinarith
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      obtain ⟨a, ha⟩ := hden x hx x hx
      obtain ⟨b, hb⟩ := hden y hy y hy
      have hab : b < a := by
        have : (b : ℚ) < a := by rw [← ha, ← hb]; exact mul_lt_mul_of_pos_left hlt' hd'
        exact_mod_cast this
      have han : a < n + 1 := by
        rw [ha] at hlt
        exact_mod_cast hlt
      have hyX : γ y - y ∈ X := ih y hy (by
        rw [hb]
        have : b < n := by omega
        exact_mod_cast this)
      have hw : γ z - z ∈ X := by
        have : γ z - z = (g : K) • (γ y - y) + (γ u - u) := by
          rw [hz, map_add, map_smul, smul_sub]; abel
        rw [this]
        exact X.add_mem (X.smul_mem _ hyX) (X.sub_mem (hγX u hu) hu)
      have hzz : h z z = 0 := by
        have e := hiso x z
        have e2 : h (γ x) (γ z - z) = 0 := hrad' _ hγxU _ hw
        rw [map_sub, e, hγx, map_add, LinearMap.add_apply] at e2
        linear_combination -e2
      by_contra hzX
      have := hpos z hzU hzX
      rw [hzz, map_zero] at this
      exact lt_irrefl _ this
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ((d : ℚ) * B x x)
  exact main n x hx hn

end GlobalTheory

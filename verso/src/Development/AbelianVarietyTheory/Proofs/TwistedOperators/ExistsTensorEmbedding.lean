import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FockTensor

/- English proof (translation)
Set `S : Submodule ℂ D.U.H` to `{ carrier := {x | ∀ g, A (D.U.π g x) = B (D.U.π g x)} add_mem' := by`. Introduce `a b ha hb g`. Simplify using `only [map_add]`. Rewrite using `[ha g, hb g]`. Use the proof step `zero_mem' := by intro g; simp`.

Use the proof step `smul_mem' := by`. Introduce `c a ha g`. Simplify using `only [map_smul]`. Rewrite using `[ha g] }`. Establish `hcl : IsClosed (S : Set D.U.H)`.

Establish `: (S : Set D.U.H) = ⋂ g, {x | A (D.U.π g x) = B (D.U.π g x)}`. Use extensionality with `x`. Simplify using `only [Set.mem_iInter]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `isClosed_iInter fun g => isClosed_eq (by fun_prop) (by fun_prop)`. Establish `hinv : ∀ g, ∀ x ∈ S, D.U.π g x ∈ S`. Introduce `g x hx g'`. Use `hx (g' * g)` as an intermediate fact. Rewrite `this` using `[map_mul]`.

Conclude with `this`. Break down `D.irred S hcl hinv with h0 | h1` into its components or cases. Establish `: u ∈ S` using `h`. Rewrite `this` using `[h0]`. Conclude with `absurd ((Submodule.mem_bot ℂ).1 this) hu`.

Use extensionality with `x`. Establish `hx : x ∈ S` using `by rw [h1]; trivial`. Use `hx 1` as an intermediate fact. Rewrite `this` using `[map_one]`. Conclude with `this`.
-/
theorem ext_orbit {p q : ℕ} {T : GrpData p q} (D : DSRep T) (u : D.U.H) (hu : u ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A B : D.U.H →L[ℂ] E)
    (h : ∀ g, A (D.U.π g u) = B (D.U.π g u)) : A = B := by
  let S : Submodule ℂ D.U.H :=
    { carrier := {x | ∀ g, A (D.U.π g x) = B (D.U.π g x)}
      add_mem' := by
        intro a b ha hb g
        simp only [map_add]
        rw [ha g, hb g]
      zero_mem' := by intro g; simp
      smul_mem' := by
        intro c a ha g
        simp only [map_smul]
        rw [ha g] }
  have hcl : IsClosed (S : Set D.U.H) := by
    have : (S : Set D.U.H) = ⋂ g, {x | A (D.U.π g x) = B (D.U.π g x)} := by
      ext x; simp only [Set.mem_iInter]; rfl
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (by fun_prop) (by fun_prop)
  have hinv : ∀ g, ∀ x ∈ S, D.U.π g x ∈ S := by
    intro g x hx g'
    have := hx (g' * g)
    rw [map_mul] at this
    exact this
  rcases D.irred S hcl hinv with h0 | h1
  · have : u ∈ S := h
    rw [h0] at this
    exact absurd ((Submodule.mem_bot ℂ).1 this) hu
  · ext x
    have hx : x ∈ S := by rw [h1]; trivial
    have := hx 1
    rw [map_one] at this
    exact this

/- English proof (translation)
The claim follows from `ext_orbit D u hu A B fun g => by rw [hA, hB, h]`.
-/
theorem isHomG_ext {p q : ℕ} {T : GrpData p q} (D : DSRep T) (πU : URep T) (u : D.U.H)
    (hu : u ≠ 0) (A B : D.U.H →L[ℂ] πU.H) (hA : ∀ g x, A (D.U.π g x) = πU.π g (A x))
    (hB : ∀ g x, B (D.U.π g x) = πU.π g (B x)) (h : A u = B u) : A = B :=
  ext_orbit D u hu A B fun g => by rw [hA, hB, h]

/- English proof (translation)
Introduce `p q T D πU v hv K _ _ j hj hex`. Use `choose io hio hiov using hex`. Establish `hu : D.ι v ≠ 0`. Introduce `h`. Rewrite `hv` using `[h, norm_zero]`.

Conclude with `zero_ne_one hv`. Establish `hG : ∀ y g x, io y (D.U.π g x) = πU.π g (io y x)` using `fun y g x => congrArg (fun f : D.U.H →L[ℂ] πU.H => f x) (hio y g)`. Establish `key1 : ∀ y y' x', inner ℂ (j y) (io y' x') = inner ℂ (D.ι v) x' * inner ℂ y y'`. Introduce `y y' x'`. Use `ext_orbit D (D.ι v) hu ((innerSL ℂ (j y)).comp (io y')) ((inner ℂ y y' : ℂ) • innerSL ℂ (D.ι v)) (fun g => by show inner ℂ (j y) (io y' (D.U.π g (D.ι v))) = inner ℂ y y' * inner ℂ (D.ι v) (D.U.π g (D.ι v))` as an intermediate fact.

Rewrite using `[hG, hiov, hj, mcoef, mul_comm])`. Establish `h2` using `congrArg (fun f : D.U.H →L[ℂ] ℂ => f x') this`. Rewrite using `[mul_comm]`. Conclude with `h2`. Establish `key2 : ∀ y y' g x', inner ℂ (io y (D.U.π g (D.ι v))) (io y' x') = inner ℂ (D.U.π g (D.ι v)) x' * inner ℂ y y'`.

Introduce `y y' g x'`. Rewrite using `[hG, hiov, inner_pi_left, ← hG, key1, inner_pi_left]`. Establish `key : ∀ x x' y y', inner ℂ (io y x) (io y' x') = inner ℂ x x' * inner ℂ y y'`. Introduce `x x' y y'`. Use `ext_orbit D (D.ι v) hu ((innerSL ℂ (io y x)).comp (io y')) ((inner ℂ y y' : ℂ) • innerSL ℂ x) (fun g => by show inner ℂ (io y x) (io y' (D.U.π g (D.ι v))) = inner ℂ y y' * inner ℂ x (D.U.π g (D.ι v))` as an intermediate fact.

Rewrite using `[← inner_conj_symm, key2, map_mul, inner_conj_symm, inner_conj_symm, mul_comm])`. Establish `h2` using `congrArg (fun f : D.U.H →L[ℂ] ℂ => f x') this`. Rewrite using `[mul_comm]`. Conclude with `h2`. Establish `hnorm : ∀ x y, ‖io y x‖ ≤ 1 * ‖x‖ * ‖y‖`.

Introduce `x y`. Establish `h` using `key x x y y`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Establish `h' : ‖io y x‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2`. Rewrite using `[mul_pow]`.

Conclude with `h` after adjusting the coercions. Use `(pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'` as an intermediate fact. Rewrite using `[this, one_mul]`. Establish `hadd : ∀ y y', io (y + y') = io y + io y'` using `fun y y' => isHomG_ext D πU _ hu _ _ (hG _) (fun g x => by show io y (D.U.π g x) + io y' (D.U.π g x) = πU.π g (io y x + io y' x)`. Rewrite using `[hG, hG, map_add]) (by`.

Use `show io (y + y') (D.ι v) = io y (D.ι v) + io y' (D.ι v)`. Rewrite using `[hiov, hiov, hiov, map_add])`. Establish `hsmul : ∀ (c : ℂ) y, io (c • y) = c • io y` using `fun c y => isHomG_ext D πU _ hu _ _ (hG _) (fun g x => by show c • io y (D.U.π g x) = πU.π g (c • io y x)`. Rewrite using `[hG, map_smul]) (by`. Use `show io (c • y) (D.ι v) = c • io y (D.ι v)`.

Rewrite using `[hiov, hiov, map_smul])`. Set `L : D.U.H →ₗ[ℂ] K →ₗ[ℂ] πU.H` to `LinearMap.mk₂ ℂ (fun x y => io y x) (fun a b y => map_add _ _ _) (fun c a y => map_smul _ _ _) (fun x a b => by rw [hadd]; rfl) (fun c x a => by rw [hsmul]; rfl)`. Use `⟨LinearMap.mkContinuous₂ L 1 hnorm, key, hiov, fun g x y => (hG y g x).symm, ?_⟩` and prove the remaining obligations. Introduce `R S hR hS x y`. Use `isHomG_ext D πU _ hu (R.comp (io y)) (io (S y)) (fun g x => by show R (io y (D.U.π g x)) = πU.π g (R (io y x))` as an intermediate fact.

Rewrite using `[hG, hR]) (hG _) (by`. Use `show R (io y (D.ι v)) = _`. Rewrite using `[hiov, hiov, hS])`. Conclude with `congrArg (fun f : D.U.H →L[ℂ] πU.H => f x) this`.
-/
theorem exists_tensor_embedding :
    ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (πU : URep T) (v : D.HK.V), ‖D.ι v‖ = 1 → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (j : K →ₗᵢ[ℂ] πU.H), (∀ g y y', inner ℂ (j y) (πU.π g (j y')) = mcoef D v g * inner ℂ y y') → (∀ y, ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = j y) → ∃ Tm : D.U.H →L[ℂ] K →L[ℂ] πU.H, (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') ∧ (∀ y, Tm (D.ι v) y = j y) ∧ (∀ g x y, πU.π g (Tm x y) = Tm (D.U.π g x) y) ∧ ∀ (R : πU.H →L[ℂ] πU.H) (S : K →L[ℂ] K), (∀ g z, R (πU.π g z) = πU.π g (R z)) → (∀ y, R (j y) = j (S y)) → ∀ x y, R (Tm x y) = Tm x (S y) := by
  intro p q T D πU v hv K _ _ j hj hex
  choose io hio hiov using hex
  have hu : D.ι v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  have hG : ∀ y g x, io y (D.U.π g x) = πU.π g (io y x) := fun y g x =>
    congrArg (fun f : D.U.H →L[ℂ] πU.H => f x) (hio y g)
  have key1 : ∀ y y' x', inner ℂ (j y) (io y' x') = inner ℂ (D.ι v) x' * inner ℂ y y' := by
    intro y y' x'
    have := ext_orbit D (D.ι v) hu ((innerSL ℂ (j y)).comp (io y'))
      ((inner ℂ y y' : ℂ) • innerSL ℂ (D.ι v)) (fun g => by
        show inner ℂ (j y) (io y' (D.U.π g (D.ι v))) =
          inner ℂ y y' * inner ℂ (D.ι v) (D.U.π g (D.ι v))
        rw [hG, hiov, hj, mcoef, mul_comm])
    have h2 := congrArg (fun f : D.U.H →L[ℂ] ℂ => f x') this
    rw [mul_comm]
    exact h2
  have key2 : ∀ y y' g x', inner ℂ (io y (D.U.π g (D.ι v))) (io y' x') =
      inner ℂ (D.U.π g (D.ι v)) x' * inner ℂ y y' := by
    intro y y' g x'
    rw [hG, hiov, inner_pi_left, ← hG, key1, inner_pi_left]
  have key : ∀ x x' y y', inner ℂ (io y x) (io y' x') = inner ℂ x x' * inner ℂ y y' := by
    intro x x' y y'
    have := ext_orbit D (D.ι v) hu ((innerSL ℂ (io y x)).comp (io y'))
      ((inner ℂ y y' : ℂ) • innerSL ℂ x) (fun g => by
        show inner ℂ (io y x) (io y' (D.U.π g (D.ι v))) =
          inner ℂ y y' * inner ℂ x (D.U.π g (D.ι v))
        rw [← inner_conj_symm, key2, map_mul, inner_conj_symm, inner_conj_symm, mul_comm])
    have h2 := congrArg (fun f : D.U.H →L[ℂ] ℂ => f x') this
    rw [mul_comm]
    exact h2
  have hnorm : ∀ x y, ‖io y x‖ ≤ 1 * ‖x‖ * ‖y‖ := by
    intro x y
    have h := key x x y y
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖io y x‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
      rw [mul_pow]; exact_mod_cast h
    have := (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'
    rw [this, one_mul]
  have hadd : ∀ y y', io (y + y') = io y + io y' := fun y y' =>
    isHomG_ext D πU _ hu _ _ (hG _) (fun g x => by
      show io y (D.U.π g x) + io y' (D.U.π g x) = πU.π g (io y x + io y' x)
      rw [hG, hG, map_add]) (by
      show io (y + y') (D.ι v) = io y (D.ι v) + io y' (D.ι v)
      rw [hiov, hiov, hiov, map_add])
  have hsmul : ∀ (c : ℂ) y, io (c • y) = c • io y := fun c y =>
    isHomG_ext D πU _ hu _ _ (hG _) (fun g x => by
      show c • io y (D.U.π g x) = πU.π g (c • io y x)
      rw [hG, map_smul]) (by
      show io (c • y) (D.ι v) = c • io y (D.ι v)
      rw [hiov, hiov, map_smul])
  let L : D.U.H →ₗ[ℂ] K →ₗ[ℂ] πU.H := LinearMap.mk₂ ℂ (fun x y => io y x)
    (fun a b y => map_add _ _ _) (fun c a y => map_smul _ _ _)
    (fun x a b => by rw [hadd]; rfl) (fun c x a => by rw [hsmul]; rfl)
  refine ⟨LinearMap.mkContinuous₂ L 1 hnorm, key, hiov, fun g x y => (hG y g x).symm, ?_⟩
  intro R S hR hS x y
  have := isHomG_ext D πU _ hu (R.comp (io y)) (io (S y)) (fun g x => by
      show R (io y (D.U.π g x)) = πU.π g (R (io y x))
      rw [hG, hR]) (hG _) (by
      show R (io y (D.ι v)) = _
      rw [hiov, hiov, hS])
  exact congrArg (fun f : D.U.H →L[ℂ] πU.H => f x) this

end GlobalTheory.FockTensor

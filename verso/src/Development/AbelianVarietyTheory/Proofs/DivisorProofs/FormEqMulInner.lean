import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwise

open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.ConjLiftUnique

/- English proof (translation)
Set `f : E → E` to `fun x => (InnerProductSpace.toDual ℂ E).symm (LinearMap.toContinuousLinearMap (b x))`. Establish `hf : ∀ x y, ⟪f x, y⟫_ℂ = b x y`. Introduce `x y`. Simplify using `only [f, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']`. Use `⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, fun x y => (hf x y).symm⟩` and prove the remaining obligations.

Introduce `x x'`. Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `y`. Simplify using `[hf, inner_add_left]`. Introduce `c x`.

Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `y`. Simplify using `[hf, inner_smul_left]`.
-/
private lemma exists_linearMap_sesqForm_eq_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) : ∃ A : E →ₗ[ℂ] E, ∀ x y, b x y = ⟪A x, y⟫_ℂ := by
  let f : E → E := fun x => (InnerProductSpace.toDual ℂ E).symm (LinearMap.toContinuousLinearMap (b x))
  have hf : ∀ x y, ⟪f x, y⟫_ℂ = b x y := by
    intro x y
    simp only [f, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, fun x y => (hf x y).symm⟩
  · intro x x'
    apply ext_inner_right ℂ
    intro y
    simp [hf, inner_add_left]
  · intro c x
    apply ext_inner_right ℂ
    intro y
    simp [hf, inner_smul_left]

/- English proof (translation)
Take `⟨A, hA⟩` from `exists_linearMap_sesqForm_eq_inner b`. Establish `hinj : ∀ k, Function.Injective (g k)`. Introduce `k`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `x hx`.

Establish `h0 : ⟪x, x⟫_ℂ = 0` using `by rw [← hu k x x, LinearMap.mem_ker.mp hx, inner_zero_left]`. Conclude with `inner_self_eq_zero.mp h0`. Establish `hsurj : ∀ k, Function.Surjective (g k)` using `fun k => LinearMap.injective_iff_surjective.mp (hinj k)`. Establish `hcomm : ∀ k x, A (g k x) = g k (A x)`. Introduce `k x`.

Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `y`. Take `⟨z, rfl⟩` from `hsurj k y`. Rewrite using `[← hA, hb, hu, hA]`. Break down `subsingleton_or_nontrivial E with hE | hE` into its components or cases.

Conclude with `⟨0, fun x y => by simp [Subsingleton.elim x 0]⟩`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue A`. Establish `hinv : ∀ k, ∀ x ∈ Module.End.eigenspace A c, g k x ∈ Module.End.eigenspace A c`. Introduce `k x hx`. Rewrite `hx`, the goal using `[Module.End.mem_eigenspace_iff]`.

Rewrite using `[hcomm, hx, map_smul]`. Break down `hirr _ hinv with h | h` into its components or cases. Conclude with `absurd h (Module.End.hasEigenvalue_iff.mp hc)`. Use `⟨conj c, fun x y => ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ Module.End.eigenspace A c` using `h ▸ Submodule.mem_top`.

Rewrite `hx` using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[hA, hx, inner_smul_left]`.
-/
theorem form_eq_mul_inner {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (g : I → E →ₗ[ℂ] E) (hu : ∀ k x y, ⟪g k x, g k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hirr : ∀ U : Submodule ℂ E, (∀ k, ∀ x ∈ U, g k x ∈ U) → U = ⊥ ∨ U = ⊤)
    (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (hb : ∀ k x y, b (g k x) (g k y) = b x y) : ∃ c : ℂ, ∀ x y, b x y = c * ⟪x, y⟫_ℂ := by
  obtain ⟨A, hA⟩ := exists_linearMap_sesqForm_eq_inner b
  have hinj : ∀ k, Function.Injective (g k) := by
    intro k
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h0 : ⟪x, x⟫_ℂ = 0 := by rw [← hu k x x, LinearMap.mem_ker.mp hx, inner_zero_left]
    exact inner_self_eq_zero.mp h0
  have hsurj : ∀ k, Function.Surjective (g k) := fun k => LinearMap.injective_iff_surjective.mp (hinj k)
  have hcomm : ∀ k x, A (g k x) = g k (A x) := by
    intro k x
    apply ext_inner_right ℂ
    intro y
    obtain ⟨z, rfl⟩ := hsurj k y
    rw [← hA, hb, hu, hA]
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨0, fun x y => by simp [Subsingleton.elim x 0]⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  have hinv : ∀ k, ∀ x ∈ Module.End.eigenspace A c, g k x ∈ Module.End.eigenspace A c := by
    intro k x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hcomm, hx, map_smul]
  rcases hirr _ hinv with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.mp hc)
  · refine ⟨conj c, fun x y => ?_⟩
    have hx : x ∈ Module.End.eigenspace A c := h ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [hA, hx, inner_smul_left]

/- English proof (translation)
Rewrite using `[inner_self_eq_norm_sq_to_K, hu]`. Simplify using the standard rewrite rules.
-/
private lemma inner_self_eq_one_of_norm_eq_one' {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {u : F}
    (hu : ‖u‖ = 1) : ⟪u, u⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hu]; simp

variable {ι : Type} [Fintype ι] [DecidableEq ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/- English proof (translation)
Distinguish the cases in `hall : ∀ i, Nontrivial (E i)`. Establish `he : ∀ i, ∃ e : E i, ‖e‖ = 1` using `fun i => by haveI := hall i`. Conclude with `exists_norm_eq (E i) zero_le_one`. Use `choose e he using he`. Establish `hee : ∀ i, ⟪e i, e i⟫_ℂ = 1` using `fun i => inner_self_eq_one_of_norm_eq_one' (he i)`.

Establish `hw : ∀ v v' w w', B v w v' w' = B v w₀ v' w₀ * ⟪w, w'⟫_ℂ`. Introduce `v v' w w'`. Take `⟨c, hc⟩` from `h2 v v'`. Rewrite using `[hc, hc w₀ w₀, inner_self_eq_one_of_norm_eq_one' h₀, mul_one]`. Establish `hs : ∀ s : Finset ι, ∀ v v' : ∀ i, E i, (∀ i ∉ s, v i = e i) → (∀ i ∉ s, v' i = e i) → B v w₀ v' w₀ = B e w₀ e w₀ * ∏ i ∈ s, ⟪v i, v' i⟫_ℂ`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `v v' hv hv'`. Establish `e1 : v = e` using `funext fun i => hv i (by simp)`.

Establish `e2 : v' = e` using `funext fun i => hv' i (by simp)`. Substitute `e1 e2` using the available equality. Simplify using the standard rewrite rules. Consider the case `insert j s hj ih`. Introduce `v v' hv hv'`.

Take `⟨c, hc⟩` from `h1 w₀ w₀ j v v'`. Establish `k1` using `hc (v j) (v' j)`. Establish `k2` using `hc (e j) (e j)`. Rewrite `k1` using `[Function.update_eq_self, Function.update_eq_self]`. Rewrite `k2` using `[hee, mul_one]`.

Establish `ih'` using `ih (Function.update v j (e j)) (Function.update v' j (e j)) ?_ ?_`. Rewrite using `[k1, ← k2, ih', Finset.prod_insert hj]`. Establish `hcg : ∀ i ∈ s, ⟪Function.update v j (e j) i, Function.update v' j (e j) i⟫_ℂ = ⟪v i, v' i⟫_ℂ`. Introduce `i hi`. Establish `hij : i ≠ j` using `fun h => hj (h ▸ hi)`.

Rewrite using `[Function.update_of_ne hij, Function.update_of_ne hij]`. Rewrite using `[Finset.prod_congr rfl hcg]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i hi`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hij]`. Conclude with `hv i (by simp [hij, hi])`. Introduce `i hi`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hij]`. Conclude with `hv' i (by simp [hij, hi])`.

Use `⟨B e w₀ e w₀, fun v w v' w' => ?_⟩` and prove the remaining obligations. Rewrite using `[hw, hs Finset.univ v v' (by simp) (by simp)]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨i, hi⟩` from `not_forall.mp hall haveI : Subsingleton (E i) := not_nontrivial_iff_subsingleton.mp hi`. Use `⟨0, fun v w v' w' => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `h1 w w' i v v'`. Establish `k` using `hc (v i) (v' i)`. Rewrite `k` using `[Function.update_eq_self, Function.update_eq_self, Subsingleton.elim (v i) 0, inner_zero_left, mul_zero]`. Rewrite using `[k, zero_mul]`.
-/
theorem exists_const (B : (∀ i, E i) → W → (∀ i, E i) → W → ℂ) (w₀ : W) (h₀ : ‖w₀‖ = 1)
    (h1 : ∀ w w' i v v', ∃ c : ℂ, ∀ a a' : E i,
      B (Function.update v i a) w (Function.update v' i a') w' = c * ⟪a, a'⟫_ℂ)
    (h2 : ∀ v v', ∃ c : ℂ, ∀ w w', B v w v' w' = c * ⟪w, w'⟫_ℂ) :
    ∃ c : ℂ, ∀ v w v' w', B v w v' w' = c * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ) := by
  by_cases hall : ∀ i, Nontrivial (E i)
  · have he : ∀ i, ∃ e : E i, ‖e‖ = 1 := fun i => by
      haveI := hall i
      exact exists_norm_eq (E i) zero_le_one
    choose e he using he
    have hee : ∀ i, ⟪e i, e i⟫_ℂ = 1 := fun i => inner_self_eq_one_of_norm_eq_one' (he i)
    have hw : ∀ v v' w w', B v w v' w' = B v w₀ v' w₀ * ⟪w, w'⟫_ℂ := by
      intro v v' w w'
      obtain ⟨c, hc⟩ := h2 v v'
      rw [hc, hc w₀ w₀, inner_self_eq_one_of_norm_eq_one' h₀, mul_one]
    have hs : ∀ s : Finset ι, ∀ v v' : ∀ i, E i, (∀ i ∉ s, v i = e i) → (∀ i ∉ s, v' i = e i) →
        B v w₀ v' w₀ = B e w₀ e w₀ * ∏ i ∈ s, ⟪v i, v' i⟫_ℂ := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro v v' hv hv'
        have e1 : v = e := funext fun i => hv i (by simp)
        have e2 : v' = e := funext fun i => hv' i (by simp)
        subst e1 e2
        simp
      | insert j s hj ih =>
        intro v v' hv hv'
        obtain ⟨c, hc⟩ := h1 w₀ w₀ j v v'
        have k1 := hc (v j) (v' j)
        have k2 := hc (e j) (e j)
        rw [Function.update_eq_self, Function.update_eq_self] at k1
        rw [hee, mul_one] at k2
        have ih' := ih (Function.update v j (e j)) (Function.update v' j (e j)) ?_ ?_
        · rw [k1, ← k2, ih', Finset.prod_insert hj]
          have hcg : ∀ i ∈ s, ⟪Function.update v j (e j) i, Function.update v' j (e j) i⟫_ℂ = ⟪v i, v' i⟫_ℂ := by
            intro i hi
            have hij : i ≠ j := fun h => hj (h ▸ hi)
            rw [Function.update_of_ne hij, Function.update_of_ne hij]
          rw [Finset.prod_congr rfl hcg]
          ring
        · intro i hi
          by_cases hij : i = j
          · subst hij
            simp
          · rw [Function.update_of_ne hij]
            exact hv i (by simp [hij, hi])
        · intro i hi
          by_cases hij : i = j
          · subst hij
            simp
          · rw [Function.update_of_ne hij]
            exact hv' i (by simp [hij, hi])
    refine ⟨B e w₀ e w₀, fun v w v' w' => ?_⟩
    rw [hw, hs Finset.univ v v' (by simp) (by simp)]
    ring
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    haveI : Subsingleton (E i) := not_nontrivial_iff_subsingleton.mp hi
    refine ⟨0, fun v w v' w' => ?_⟩
    obtain ⟨c, hc⟩ := h1 w w' i v v'
    have k := hc (v i) (v' i)
    rw [Function.update_eq_self, Function.update_eq_self, Subsingleton.elim (v i) 0, inner_zero_left,
      mul_zero] at k
    rw [k, zero_mul]

/- English proof (translation)
Rewrite using `[inner_self_eq_norm_sq_to_K, hu]`. Simplify using the standard rewrite rules.
-/
private lemma inner_self_eq_one_of_unit_norm {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {u : F}
    (hu : ‖u‖ = 1) : ⟪u, u⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hu]; simp

/- English proof (translation)
Establish `hyx : b y x = conj κ * b x x`. Rewrite using `[hs x y, hxy, map_mul, ← hs x x]`. Rewrite using `[← sub_eq_zero]`. Apply `hd` to reduce the goal to its premises. Simplify using `only [map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]`.

Take the linear combination `hyy - κ * hyx - conj κ * hxy - b x x * hk`.
-/
private lemma eq_smul_of_form_eq_of_unit_modulus {Y : Type} [AddCommGroup Y] [Module ℂ Y] (b : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ)
    (hs : ∀ x y, b y x = conj (b x y)) (hd : ∀ x, b x x = 0 → x = 0)
    {x y : Y} {κ : ℂ} (hk : conj κ * κ = 1) (hyy : b y y = b x x) (hxy : b x y = κ * b x x) :
    y = κ • x := by
  have hyx : b y x = conj κ * b x x := by
    rw [hs x y, hxy, map_mul, ← hs x x]
  rw [← sub_eq_zero]
  apply hd
  simp only [map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
  linear_combination hyy - κ * hyx - conj κ * hxy - b x x * hk

/- English proof (translation)
Establish `P1 : (∏ i, ⟪v₀ i, v₀ i⟫_ℂ) * ⟪w₀, w₀⟫_ℂ = 1`. Rewrite using `[Finset.prod_eq_one (fun i _ => inner_self_eq_one_of_unit_norm (n1 i)), inner_self_eq_one_of_unit_norm n3, one_mul]`. Establish `P2 : (∏ i, ⟪v₀' i, v₀' i⟫_ℂ) * ⟪w₀', w₀'⟫_ℂ = 1`. Rewrite using `[Finset.prod_eq_one (fun i _ => inner_self_eq_one_of_unit_norm (n2 i)), inner_self_eq_one_of_unit_norm n4, one_mul]`. Establish `hl1 : conj l * l = 1`.

Rewrite using `[Complex.conj_mul', hl]`. Simplify using the standard rewrite rules. Establish `e1 : b (F v₀ w₀) (F v₀ w₀) = c₁` using `by rw [h1, P1, mul_one]`. Establish `e2 : b (F' v₀' w₀') (F' v₀' w₀') = c₂` using `by rw [h2, P2, mul_one]`. Establish `hc : c₁ = c₂`.

Rewrite using `[← e1, ← e2, hm]`. Simplify using `only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul]`. Take the linear combination `b (F' v₀' w₀') (F' v₀' w₀') * hl1`. Establish `hA : c₃ * ((∏ i, ⟪v₀ i, v₀' i⟫_ℂ) * ⟪w₀, w₀'⟫_ℂ) = conj l * c₁`. Establish `t` using `h3 v₀ w₀ v₀' w₀'`.

Rewrite `t` using `[hm]`. Simplify using `only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at t`. Rewrite `t` using `[e2, ← hc]`. Conclude with `t.symm`. Establish `hB : c₃ = conj l * c₁ * ((∏ i, ⟪v₀' i, v₀ i⟫_ℂ) * ⟪w₀', w₀⟫_ℂ)`.

Establish `t1` using `h3 v₀ w₀ v₀ w₀`. Establish `t2` using `h2 v₀' w₀' v₀ w₀`. Rewrite `t1` using `[P1, mul_one, hm]`. Simplify using `only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at t1`. Rewrite `t1` using `[t2]`.

Rewrite using `[← t1, hc]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `h0 : c₁ = 0`. Use `⟨1, by simp, fun v w => ?_⟩` and prove the remaining obligations. Establish `a1 : F v w = 0` using `hd _ (by rw [h1, h0, zero_mul])`.

Establish `a2 : F' v w = 0` using `hd _ (by rw [h2, ← hc, h0, zero_mul])`. Rewrite using `[a1, a2, smul_zero]`. Use `set p := (∏ i, ⟪v₀ i, v₀' i⟫_ℂ) * ⟪w₀, w₀'⟫_ℂ with hp set q := (∏ i, ⟪v₀' i, v₀ i⟫_ℂ) * ⟪w₀', w₀⟫_ℂ with hq`. Establish `hqp : q = conj p`. Rewrite using `[hp, hq]`.

Simplify using `[map_prod]`. Establish `hl0 : conj l ≠ 0`. Introduce `h`. Rewrite `h` using `[map_eq_zero]`. Rewrite `hl` using `[h, norm_zero]`.

Conclude with `zero_ne_one hl`. Establish `hqp1 : q * p = 1`. Establish `hz : conj l * c₁ * (q * p - 1) = 0` using `by linear_combination hA - p * hB`. Break down `mul_eq_zero.mp hz with h | h` into its components or cases. Conclude with `absurd h (mul_ne_zero hl0 h0)`.

Conclude with `sub_eq_zero.mp h`. Establish `hq1 : ‖q‖ = 1`. Establish `h` using `congrArg norm hqp1`. Rewrite `h` using `[norm_mul, norm_one]`. Establish `e : ‖p‖ = ‖q‖` using `by rw [hqp, Complex.norm_conj]`.

Rewrite `h` using `[e]`. Break down `mul_self_eq_one_iff.mp h with h | h` into its components or cases. Conclude with `h`. Combine the linear relations using `[norm_nonneg q]`. Establish `hκ : ‖conj l * q‖ = 1` using `by rw [norm_mul, Complex.norm_conj, hl, hq1, one_mul]`.

Use `⟨conj l * q, hκ, fun v w => ?_⟩` and prove the remaining obligations. Apply `eq_smul_of_form_eq_of_unit_modulus b hs hd` to reduce the goal to its premises. Rewrite using `[Complex.conj_mul', hκ]`. Simplify using the standard rewrite rules. Rewrite using `[h2, h1, hc]`.

Rewrite using `[h3, h1, hB]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_phase {Y : Type} [AddCommGroup Y] [Module ℂ Y] (b : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ)
    (hs : ∀ x y, b y x = conj (b x y)) (hp : ∀ x, 0 ≤ (b x x).re) (hd : ∀ x, b x x = 0 → x = 0)
    (F F' : (∀ i, E i) → W → Y) {c₁ c₂ c₃ : ℂ}
    (h1 : ∀ v w v' w', b (F v w) (F v' w') = c₁ * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ))
    (h2 : ∀ v w v' w', b (F' v w) (F' v' w') = c₂ * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ))
    (h3 : ∀ v w v' w', b (F v w) (F' v' w') = c₃ * ((∏ i, ⟪v i, v' i⟫_ℂ) * ⟪w, w'⟫_ℂ))
    {v₀ v₀' : ∀ i, E i} {w₀ w₀' : W} (n1 : ∀ i, ‖v₀ i‖ = 1) (n2 : ∀ i, ‖v₀' i‖ = 1) (n3 : ‖w₀‖ = 1) (n4 : ‖w₀'‖ = 1)
    {l : ℂ} (hl : ‖l‖ = 1) (hm : F v₀ w₀ = l • F' v₀' w₀') :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ v w, F' v w = κ • F v w := by
  have P1 : (∏ i, ⟪v₀ i, v₀ i⟫_ℂ) * ⟪w₀, w₀⟫_ℂ = 1 := by
    rw [Finset.prod_eq_one (fun i _ => inner_self_eq_one_of_unit_norm (n1 i)), inner_self_eq_one_of_unit_norm n3, one_mul]
  have P2 : (∏ i, ⟪v₀' i, v₀' i⟫_ℂ) * ⟪w₀', w₀'⟫_ℂ = 1 := by
    rw [Finset.prod_eq_one (fun i _ => inner_self_eq_one_of_unit_norm (n2 i)), inner_self_eq_one_of_unit_norm n4, one_mul]
  have hl1 : conj l * l = 1 := by
    rw [Complex.conj_mul', hl]
    simp
  have e1 : b (F v₀ w₀) (F v₀ w₀) = c₁ := by rw [h1, P1, mul_one]
  have e2 : b (F' v₀' w₀') (F' v₀' w₀') = c₂ := by rw [h2, P2, mul_one]
  have hc : c₁ = c₂ := by
    rw [← e1, ← e2, hm]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul]
    linear_combination b (F' v₀' w₀') (F' v₀' w₀') * hl1
  have hA : c₃ * ((∏ i, ⟪v₀ i, v₀' i⟫_ℂ) * ⟪w₀, w₀'⟫_ℂ) = conj l * c₁ := by
    have t := h3 v₀ w₀ v₀' w₀'
    rw [hm] at t
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at t
    rw [e2, ← hc] at t
    exact t.symm
  have hB : c₃ = conj l * c₁ * ((∏ i, ⟪v₀' i, v₀ i⟫_ℂ) * ⟪w₀', w₀⟫_ℂ) := by
    have t1 := h3 v₀ w₀ v₀ w₀
    have t2 := h2 v₀' w₀' v₀ w₀
    rw [P1, mul_one, hm] at t1
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at t1
    rw [t2] at t1
    rw [← t1, hc]
    ring
  by_cases h0 : c₁ = 0
  · refine ⟨1, by simp, fun v w => ?_⟩
    have a1 : F v w = 0 := hd _ (by rw [h1, h0, zero_mul])
    have a2 : F' v w = 0 := hd _ (by rw [h2, ← hc, h0, zero_mul])
    rw [a1, a2, smul_zero]
  · set p := (∏ i, ⟪v₀ i, v₀' i⟫_ℂ) * ⟪w₀, w₀'⟫_ℂ with hp
    set q := (∏ i, ⟪v₀' i, v₀ i⟫_ℂ) * ⟪w₀', w₀⟫_ℂ with hq
    have hqp : q = conj p := by
      rw [hp, hq]
      simp [map_prod]
    have hl0 : conj l ≠ 0 := by
      intro h
      rw [map_eq_zero] at h
      rw [h, norm_zero] at hl
      exact zero_ne_one hl
    have hqp1 : q * p = 1 := by
      have hz : conj l * c₁ * (q * p - 1) = 0 := by linear_combination hA - p * hB
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (mul_ne_zero hl0 h0)
      · exact sub_eq_zero.mp h
    have hq1 : ‖q‖ = 1 := by
      have h := congrArg norm hqp1
      rw [norm_mul, norm_one] at h
      have e : ‖p‖ = ‖q‖ := by rw [hqp, Complex.norm_conj]
      rw [e] at h
      rcases mul_self_eq_one_iff.mp h with h | h
      · exact h
      · linarith [norm_nonneg q]
    have hκ : ‖conj l * q‖ = 1 := by rw [norm_mul, Complex.norm_conj, hl, hq1, one_mul]
    refine ⟨conj l * q, hκ, fun v w => ?_⟩
    apply eq_smul_of_form_eq_of_unit_modulus b hs hd
    · rw [Complex.conj_mul', hκ]
      simp
    · rw [h2, h1, hc]
    · rw [h3, h1, hB]
      ring

end GlobalTheory.ConjLiftUnique

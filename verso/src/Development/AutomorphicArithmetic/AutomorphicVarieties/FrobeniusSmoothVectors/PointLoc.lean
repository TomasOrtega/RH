import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgVring
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClSub

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Take `⟨k, hk⟩` from `Ideal.exists_pow_inf_eq_pow_smul I (Submodule.span S (Set.range a))`. Use `set M := Submodule.span S (Set.range a)`. Set `φ : Γ → C ⧸ J ^ (N + k)` to `fun g => Ideal.Quotient.mk (J ^ (N + k)) (a g)`. Set `f : Γ → C ⧸ (I ^ N • M)` to `fun g => (I ^ N • M).mkQ (a g)`. Establish `key : ∀ g g', φ g = φ g' → f g = f g'`.

Introduce `g g' hgg`. Establish `h1 : a g - a g' ∈ J ^ (N + k)` using `Ideal.Quotient.eq.1 hgg`. Establish `h2 : a g - a g' ∈ (I ^ (N + k) • ⊤ : Submodule S C) ⊓ M` using `⟨h _ _ h1, M.sub_mem (Submodule.subset_span ⟨g, rfl⟩) (Submodule.subset_span ⟨g', rfl⟩)⟩`. Rewrite `h2` using `[hk (N + k) (by omega), Nat.add_sub_cancel]`. Establish `h3 : a g - a g' ∈ I ^ N • M` using `Submodule.smul_mono le_rfl inf_le_right h2`.

Conclude with `(Submodule.Quotient.eq _).2 h3`. Establish `hf : f = (fun x => if hx : ∃ g, φ g = x then f hx.choose else 0) ∘ φ`. Use function extensionality and compare the values at `g`. Establish `hx : ∃ g', φ g' = φ g` using `⟨g, rfl⟩`. Simplify using `only [Function.comp_apply, dif_pos hx]`.

Conclude with `key _ _ hx.choose_spec.symm`. Express the relevant statement in the definitionally equal form `IsLocallyConstant f`. Rewrite using `[hf]`. Conclude with `(ha (N + k)).comp _`.
-/
private theorem cont_sub {Γ S C : Type} [TopologicalSpace Γ] [CommRing S] [IsNoetherianRing S] [CommRing C]
    [Algebra S C] [Module.Finite S C] (I : Ideal S) (J : Ideal C)
    (h : ∀ N, ∀ c ∈ J ^ N, c ∈ (I ^ N • ⊤ : Submodule S C)) (a : Γ → C) (ha : AdicCont J a) (N : ℕ) :
    IsLocallyConstant fun g => (I ^ N • Submodule.span S (Set.range a)).mkQ (a g) := by
  classical
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (Submodule.span S (Set.range a))
  set M := Submodule.span S (Set.range a)
  let φ : Γ → C ⧸ J ^ (N + k) := fun g => Ideal.Quotient.mk (J ^ (N + k)) (a g)
  let f : Γ → C ⧸ (I ^ N • M) := fun g => (I ^ N • M).mkQ (a g)
  have key : ∀ g g', φ g = φ g' → f g = f g' := by
    intro g g' hgg
    have h1 : a g - a g' ∈ J ^ (N + k) := Ideal.Quotient.eq.1 hgg
    have h2 : a g - a g' ∈ (I ^ (N + k) • ⊤ : Submodule S C) ⊓ M :=
      ⟨h _ _ h1, M.sub_mem (Submodule.subset_span ⟨g, rfl⟩) (Submodule.subset_span ⟨g', rfl⟩)⟩
    rw [hk (N + k) (by omega), Nat.add_sub_cancel] at h2
    have h3 : a g - a g' ∈ I ^ N • M := Submodule.smul_mono le_rfl inf_le_right h2
    exact (Submodule.Quotient.eq _).2 h3
  have hf : f = (fun x => if hx : ∃ g, φ g = x then f hx.choose else 0) ∘ φ := by
    funext g
    have hx : ∃ g', φ g' = φ g := ⟨g, rfl⟩
    simp only [Function.comp_apply, dif_pos hx]
    exact key _ _ hx.choose_spec.symm
  change IsLocallyConstant f
  rw [hf]
  exact (ha (N + k)).comp _

/- English proof (translation)
Establish `hy : y = -x` using `by linear_combination h1`. Substitute `hy` using the available equality. Establish `hx : (s - t) * x = 0` using `by linear_combination h2`. Break down `mul_eq_zero.1 hx with h3 | h3` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h3) h`.

Conclude with `⟨h3, by simp [h3]⟩`.
-/
private theorem two_zero {K : Type} [Field K] {x y s t : K} (h : s ≠ t) (h1 : x + y = 0) (h2 : s * x + t * y = 0) :
    x = 0 ∧ y = 0 := by
  have hy : y = -x := by linear_combination h1
  subst hy
  have hx : (s - t) * x = 0 := by linear_combination h2
  rcases mul_eq_zero.1 hx with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) h
  · exact ⟨h3, by simp [h3]⟩

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨⟨g, hg⟩, ⟨g', hg'⟩⟩` from `hc`. Conclude with `mul_ne_zero hg hg' (h g g')`.
-/
private theorem or_zero {G K : Type} [Field K] {a b : G → K} (h : ∀ g g', a g * b g' = 0) :
    (∀ g, a g = 0) ∨ ∀ g, b g = 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩ := hc
  exact mul_ne_zero hg hg' (h g g')

/- English proof (translation)
Establish `hst` using `UpperTheory.V.Fr.star hF`. Establish `hd : ∀ g h : F.G0, ∀ i, ρ.r (g * h) i i = ρ.r g i i * ρ.r h i i`. Introduce `g h i`. Rewrite using `[hρ.1, hρ.1, hρ.1]`. Simplify using `[mul_zpow, map_mul]`.

Break down `hn with rfl | rfl` into its components or cases. Establish `hE : ∀ g h : F.G0, ρ.r g 0 1 * ρ.r h 1 0 = 0`. Introduce `g h`. Establish `e` using `hd g h 0`. Rewrite `e` using `[map_mul, Matrix.mul_apply, Fin.sum_univ_two]`.

Take the linear combination `e`. Break down `or_zero hE with h01 | h10` into its components or cases. Use `right`. Introduce `g i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at hij`.

Conclude with `h01 g`. Use `left`. Introduce `g i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at hij`. Conclude with `h10 g`.

Use `set X := ρ.r F.g0 - ρ.r (F.star F.g0) with hXdef`. Establish `hX : ∀ a b : Fin 3, a ≠ b → X a b = 0` using `fun a b hab => ρ.diag a b hab`. Establish `hXm : ∀ g h : F.G0, ρ.r (g * F.g0 * h) - ρ.r (g * F.star F.g0 * h) = ρ.r g * X * ρ.r h`. Introduce `g h`. Simplify using `only [map_mul, hXdef, Matrix.mul_sub, Matrix.sub_mul]`.

Establish `hT : ∀ g h : F.G0, ∀ i : Fin 3, (ρ.r g * X * ρ.r h) i i = ρ.r g i i * X i i * ρ.r h i i`. Introduce `g h i`. Rewrite using `[← hXm, Matrix.sub_apply, hd, hd, hd, hd, hXdef, Matrix.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hE : ∀ g h : F.G0, ∀ i : Fin 3, (ρ.r g * ρ.r h) i i = ρ.r g i i * ρ.r h i i`.

Introduce `g h i`. Rewrite using `[← map_mul, hd]`. Establish `hp : (F.Ψ ↑F.g0 : kˣ) ^ 2 ≠ 1` using `hF.baseSubgroup_spec`. Use `set p := F.Ψ ↑F.g0 with hpdef`. Establish `hw0 : w 3 0 = 1` using `by simp [w]`.

Establish `hw1 : w 3 1 = 0` using `by simp [w]`. Establish `hw2 : w 3 2 = -1` using `by simp [w]`. Establish `hs : F.Ψ ↑(F.star F.g0) = p⁻¹` using `hst.2.2.1 F.g0`. Establish `hX0 : X 0 0 = f ↑p - f ↑p⁻¹`. Rewrite using `[hXdef, Matrix.sub_apply, hρ.1, hρ.1, hw0, hs]`.

Simplify using `[← hpdef]`. Establish `hX1 : X 1 1 = 0`. Rewrite using `[hXdef, Matrix.sub_apply, hρ.1, hρ.1, hw1]`. Simplify using the standard rewrite rules. Establish `hX2 : X 2 2 = f ↑p⁻¹ - f ↑p`.

Rewrite using `[hXdef, Matrix.sub_apply, hρ.1, hρ.1, hw2, hs]`. Simplify using `[← hpdef]`. Establish `hq : f ↑p - f ↑p⁻¹ ≠ 0`. Introduce `e`. Apply `hp` to reduce the goal to its premises.

Establish `e2 : f ((p : k) * p) = f ((p : k) * ↑p⁻¹)`. Rewrite using `[map_mul, map_mul, sub_eq_zero.1 e]`. Rewrite `e2` using `[Units.mul_inv]`. Establish `e3 : (p : k) * p = 1` using `f.injective (by rw [e2, map_one])`. Use `ext`.

Simplify `e3` using `[pow_two]`. Establish `h2 : (2 : K) ≠ 0`. Establish `hk2 : (2 : k) ≠ 0`. Introduce `e`. Establish `: (l : ℕ) ∣ 2`.

Use `(CharP.cast_eq_zero_iff k l 2).1 (by exact_mod_cast e)` as an intermediate fact. Conclude with `this`. Establish `hl` using `(Fact.out : l.Prime)`. Break down `(Nat.le_of_dvd (by norm_num) this).lt_or_eq with h | h` into its components or cases. Use `hl.two_le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `hF.l_odd h`. Introduce `e`. Apply `hk2` to reduce the goal to its premises. Apply `f.injective` to reduce the goal to its premises.

Rewrite using `[map_ofNat, e, map_zero]`. Establish `hA : ∀ g h : F.G0, ρ.r g 0 1 * ρ.r h 1 0 = 0 ∧ ρ.r g 0 2 * ρ.r h 2 0 = 0`. Introduce `g h`. Establish `e1` using `hE g h 0`. Establish `e2` using `hT g h 0`.

Simplify using `only [Matrix.mul_apply, Fin.sum_univ_three, hX 0 1 (by decide), hX 0 2 (by decide), hX 1 0 (by decide), hX 1 2 (by decide), hX 2 0 (by decide), hX 2 1 (by decide)] at e1 e2`. Use `two_zero (s := X 1 1) (t := X 2 2) ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hX1, hX2]`. Introduce `e`. Conclude with `hq (by linear_combination e)`.

Take the linear combination `e1`. Take the linear combination `e2`. Establish `hB : ∀ g h : F.G0, ρ.r g 1 0 * ρ.r h 0 1 = 0 ∧ ρ.r g 1 2 * ρ.r h 2 1 = 0`. Introduce `g h`. Establish `e1` using `hE g h 1`.

Establish `e2` using `hT g h 1`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_three, hX 0 1 (by decide), hX 0 2 (by decide), hX 1 0 (by decide), hX 1 2 (by decide), hX 2 0 (by decide), hX 2 1 (by decide)] at e1 e2`. Use `two_zero (s := X 0 0) (t := X 2 2) ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hX0, hX2]`. Introduce `e`.

Apply `h2` to reduce the goal to its premises. Establish `: (2 : K) * (f ↑p - f ↑p⁻¹) = 0` using `by linear_combination e`. Conclude with `(mul_eq_zero.1 this).resolve_right hq`. Take the linear combination `e1`. Take the linear combination `e2`.

Establish `s01 : ∀ g, ρ.r (F.star g) 0 1 = ρ.r g 1 2` using `fun g => hst.2.2.2.2 ρ g 0 1`. Establish `s10 : ∀ g, ρ.r (F.star g) 1 0 = ρ.r g 2 1` using `fun g => hst.2.2.2.2 ρ g 1 0`. Establish `t12 : (∀ g : F.G0, ρ.r g 0 1 = 0) → ∀ g : F.G0, ρ.r g 1 2 = 0` using `fun h g => by`. Rewrite using `[← s01]`. Conclude with `h _`.

Establish `t21 : (∀ g : F.G0, ρ.r g 1 0 = 0) → ∀ g : F.G0, ρ.r g 2 1 = 0` using `fun h g => by`. Rewrite using `[← s10]`. Conclude with `h _`. Establish `t10 : (∀ g : F.G0, ρ.r g 2 1 = 0) → ∀ g : F.G0, ρ.r g 1 0 = 0` using `fun h g => by`. Rewrite using `[← hst.1 g, s10]`.

Conclude with `h _`. Establish `hP : ∀ g h : F.G0, (ρ.r g * ρ.r h) = ρ.r (g * h)` using `fun g h => (map_mul _ _ _).symm`. Establish `hL : (∀ g : F.G0, ρ.r g 1 0 = 0) → (∀ g : F.G0, ρ.r g 2 0 = 0) → (∀ g : F.G0, ρ.r g 2 1 = 0) → (∀ (g : F.G0) (i j : Fin 3), j < i → ρ.r g i j = 0)`. Introduce `a b c g i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at hij`.

Conclude with `a g`. Conclude with `b g`. Conclude with `c g`. Establish `hR : (∀ g : F.G0, ρ.r g 0 1 = 0) → (∀ g : F.G0, ρ.r g 0 2 = 0) → (∀ g : F.G0, ρ.r g 1 2 = 0) → (∀ (g : F.G0) (i j : Fin 3), i < j → ρ.r g i j = 0)`. Introduce `a b c g i j hij`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at hij`. Conclude with `a g`. Conclude with `b g`. Conclude with `c g`. Break down `or_zero (fun g h => (hA g h).1) with a01 | a10` into its components or cases.

Establish `a12` using `t12 a01`. Break down `or_zero (fun g h => (hA g h).2) with a02 | a20` into its components or cases. Conclude with `Or.inr (hR a01 a02 a12)`. Establish `hC : ∀ g h : F.G0, ρ.r g 0 2 * ρ.r h 2 1 = 0`. Introduce `g h`.

Establish `e` using `congrFun (congrFun (hP g h) 0) 1`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_three, a01, a01 h] at e`. Take the linear combination `e`. Break down `or_zero hC with a02 | a21` into its components or cases. Conclude with `Or.inr (hR a01 a02 a12)`.

Conclude with `Or.inl (hL (t10 a21) a20 a21)`. Establish `a21` using `t21 a10`. Break down `or_zero (fun g h => (hA g h).2) with a02 | a20` into its components or cases. Establish `hC : ∀ g h : F.G0, ρ.r g 2 0 * ρ.r h 0 1 = 0`. Introduce `g h`.

Establish `e` using `congrFun (congrFun (hP g h) 2) 1`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_three, a21, a21 h] at e`. Take the linear combination `e`. Break down `or_zero hC with a20 | a01` into its components or cases. Conclude with `Or.inl (hL a10 a20 a21)`.

Conclude with `Or.inr (hR a01 a02 (t12 a01))`. Conclude with `Or.inl (hL a10 a20 a21)`.
-/
private theorem tri_of_bar {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}
    (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) {K : Type} [Field K] (f : k →+* K) (ρ : NRep F n K) (hρ : ρ.IsBar f) :
    (∀ g i j, j < i → ρ.r g i j = 0) ∨ ∀ g i j, i < j → ρ.r g i j = 0 := by
  have hst := UpperTheory.V.Fr.star hF
  have hd : ∀ g h : F.G0, ∀ i, ρ.r (g * h) i i = ρ.r g i i * ρ.r h i i := by
    intro g h i
    rw [hρ.1, hρ.1, hρ.1]
    simp [mul_zpow, map_mul]
  rcases hn with rfl | rfl
  · have hE : ∀ g h : F.G0, ρ.r g 0 1 * ρ.r h 1 0 = 0 := by
      intro g h
      have e := hd g h 0
      rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two] at e
      linear_combination e
    rcases or_zero hE with h01 | h10
    · right
      intro g i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      exact h01 g
    · left
      intro g i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      exact h10 g
  · set X := ρ.r F.g0 - ρ.r (F.star F.g0) with hXdef
    have hX : ∀ a b : Fin 3, a ≠ b → X a b = 0 := fun a b hab => ρ.diag a b hab
    have hXm : ∀ g h : F.G0, ρ.r (g * F.g0 * h) - ρ.r (g * F.star F.g0 * h) = ρ.r g * X * ρ.r h := by
      intro g h
      simp only [map_mul, hXdef, Matrix.mul_sub, Matrix.sub_mul]
    have hT : ∀ g h : F.G0, ∀ i : Fin 3, (ρ.r g * X * ρ.r h) i i = ρ.r g i i * X i i * ρ.r h i i := by
      intro g h i
      rw [← hXm, Matrix.sub_apply, hd, hd, hd, hd, hXdef, Matrix.sub_apply]
      ring
    have hE : ∀ g h : F.G0, ∀ i : Fin 3, (ρ.r g * ρ.r h) i i = ρ.r g i i * ρ.r h i i := by
      intro g h i
      rw [← map_mul, hd]
    have hp : (F.Ψ ↑F.g0 : kˣ) ^ 2 ≠ 1 := hF.baseSubgroup_spec
    set p := F.Ψ ↑F.g0 with hpdef
    have hw0 : w 3 0 = 1 := by simp [w]
    have hw1 : w 3 1 = 0 := by simp [w]
    have hw2 : w 3 2 = -1 := by simp [w]
    have hs : F.Ψ ↑(F.star F.g0) = p⁻¹ := hst.2.2.1 F.g0
    have hX0 : X 0 0 = f ↑p - f ↑p⁻¹ := by
      rw [hXdef, Matrix.sub_apply, hρ.1, hρ.1, hw0, hs]
      simp [← hpdef]
    have hX1 : X 1 1 = 0 := by
      rw [hXdef, Matrix.sub_apply, hρ.1, hρ.1, hw1]
      simp
    have hX2 : X 2 2 = f ↑p⁻¹ - f ↑p := by
      rw [hXdef, Matrix.sub_apply, hρ.1, hρ.1, hw2, hs]
      simp [← hpdef]
    have hq : f ↑p - f ↑p⁻¹ ≠ 0 := by
      intro e
      apply hp
      have e2 : f ((p : k) * p) = f ((p : k) * ↑p⁻¹) := by
        rw [map_mul, map_mul, sub_eq_zero.1 e]
      rw [Units.mul_inv] at e2
      have e3 : (p : k) * p = 1 := f.injective (by rw [e2, map_one])
      ext
      simpa [pow_two] using e3
    have h2 : (2 : K) ≠ 0 := by
      have hk2 : (2 : k) ≠ 0 := by
        intro e
        have : (l : ℕ) ∣ 2 := by
          have := (CharP.cast_eq_zero_iff k l 2).1 (by exact_mod_cast e)
          exact this
        have hl := (Fact.out : l.Prime)
        rcases (Nat.le_of_dvd (by norm_num) this).lt_or_eq with h | h
        · have := hl.two_le
          omega
        · exact hF.l_odd h
      intro e
      apply hk2
      apply f.injective
      rw [map_ofNat, e, map_zero]
    have hA : ∀ g h : F.G0, ρ.r g 0 1 * ρ.r h 1 0 = 0 ∧ ρ.r g 0 2 * ρ.r h 2 0 = 0 := by
      intro g h
      have e1 := hE g h 0
      have e2 := hT g h 0
      simp only [Matrix.mul_apply, Fin.sum_univ_three, hX 0 1 (by decide), hX 0 2 (by decide),
        hX 1 0 (by decide), hX 1 2 (by decide), hX 2 0 (by decide), hX 2 1 (by decide)] at e1 e2
      refine two_zero (s := X 1 1) (t := X 2 2) ?_ ?_ ?_
      · rw [hX1, hX2]
        intro e
        exact hq (by linear_combination e)
      · linear_combination e1
      · linear_combination e2
    have hB : ∀ g h : F.G0, ρ.r g 1 0 * ρ.r h 0 1 = 0 ∧ ρ.r g 1 2 * ρ.r h 2 1 = 0 := by
      intro g h
      have e1 := hE g h 1
      have e2 := hT g h 1
      simp only [Matrix.mul_apply, Fin.sum_univ_three, hX 0 1 (by decide), hX 0 2 (by decide),
        hX 1 0 (by decide), hX 1 2 (by decide), hX 2 0 (by decide), hX 2 1 (by decide)] at e1 e2
      refine two_zero (s := X 0 0) (t := X 2 2) ?_ ?_ ?_
      · rw [hX0, hX2]
        intro e
        apply h2
        have : (2 : K) * (f ↑p - f ↑p⁻¹) = 0 := by linear_combination e
        exact (mul_eq_zero.1 this).resolve_right hq
      · linear_combination e1
      · linear_combination e2
    have s01 : ∀ g, ρ.r (F.star g) 0 1 = ρ.r g 1 2 := fun g => hst.2.2.2.2 ρ g 0 1
    have s10 : ∀ g, ρ.r (F.star g) 1 0 = ρ.r g 2 1 := fun g => hst.2.2.2.2 ρ g 1 0
    have t12 : (∀ g : F.G0, ρ.r g 0 1 = 0) → ∀ g : F.G0, ρ.r g 1 2 = 0 := fun h g => by
      rw [← s01]; exact h _
    have t21 : (∀ g : F.G0, ρ.r g 1 0 = 0) → ∀ g : F.G0, ρ.r g 2 1 = 0 := fun h g => by
      rw [← s10]; exact h _
    have t10 : (∀ g : F.G0, ρ.r g 2 1 = 0) → ∀ g : F.G0, ρ.r g 1 0 = 0 := fun h g => by
      rw [← hst.1 g, s10]; exact h _
    have hP : ∀ g h : F.G0, (ρ.r g * ρ.r h) = ρ.r (g * h) := fun g h => (map_mul _ _ _).symm
    have hL : (∀ g : F.G0, ρ.r g 1 0 = 0) → (∀ g : F.G0, ρ.r g 2 0 = 0) → (∀ g : F.G0, ρ.r g 2 1 = 0) →
        (∀ (g : F.G0) (i j : Fin 3), j < i → ρ.r g i j = 0) := by
      intro a b c g i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      · exact a g
      · exact b g
      · exact c g
    have hR : (∀ g : F.G0, ρ.r g 0 1 = 0) → (∀ g : F.G0, ρ.r g 0 2 = 0) → (∀ g : F.G0, ρ.r g 1 2 = 0) →
        (∀ (g : F.G0) (i j : Fin 3), i < j → ρ.r g i j = 0) := by
      intro a b c g i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      · exact a g
      · exact b g
      · exact c g
    rcases or_zero (fun g h => (hA g h).1) with a01 | a10
    · have a12 := t12 a01
      rcases or_zero (fun g h => (hA g h).2) with a02 | a20
      · exact Or.inr (hR a01 a02 a12)
      · have hC : ∀ g h : F.G0, ρ.r g 0 2 * ρ.r h 2 1 = 0 := by
          intro g h
          have e := congrFun (congrFun (hP g h) 0) 1
          simp only [Matrix.mul_apply, Fin.sum_univ_three, a01, a01 h] at e
          linear_combination e
        rcases or_zero hC with a02 | a21
        · exact Or.inr (hR a01 a02 a12)
        · exact Or.inl (hL (t10 a21) a20 a21)
    · have a21 := t21 a10
      rcases or_zero (fun g h => (hA g h).2) with a02 | a20
      · have hC : ∀ g h : F.G0, ρ.r g 2 0 * ρ.r h 0 1 = 0 := by
          intro g h
          have e := congrFun (congrFun (hP g h) 2) 1
          simp only [Matrix.mul_apply, Fin.sum_univ_three, a21, a21 h] at e
          linear_combination e
        rcases or_zero hC with a20 | a01
        · exact Or.inl (hL a10 a20 a21)
        · exact Or.inr (hR a01 a02 (t12 a01))
      · exact Or.inl (hL a10 a20 a21)

/- English proof (translation)
Establish `hw : ∀ i j : Fin n, i ≤ j → 0 ≤ w n i - w n j ∧ (w n i - w n j = 0 → i = j)`. Introduce `i j hij`. Establish `hij' : (i : ℕ) ≤ j` using `hij`. Break down `hn with rfl | rfl` into its components or cases. Simplify using `only [w]`.

Use `⟨by norm_num; omega, fun e => Fin.ext ?_⟩` and prove the remaining obligations. Evaluate the numerical expressions using `at e`. Use linear arithmetic over natural numbers and integers. Simplify using `only [w]`. Use `⟨by norm_num; omega, fun e => Fin.ext ?_⟩` and prove the remaining obligations.

Evaluate the numerical expressions using `at e`. Use linear arithmetic over natural numbers and integers. Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons s L ih`.

Introduce `s' hs'`. Establish `hs` using `hw s.2.1 s.2.2 (h s (List.mem_cons_self ..))`. Establish `hL : ∀ t ∈ L, t.2.1 ≤ t.2.2` using `fun t ht => h t (List.mem_cons_of_mem _ ht)`. Establish `hnn : 0 ≤ (L.map fun s => w n s.2.1 - w n s.2.2).sum`. Apply `List.sum_nonneg` to reduce the goal to its premises.

Introduce `x hx`. Take `⟨t, ht, rfl⟩` from `List.mem_map.1 hx`. Conclude with `(hw _ _ (hL t ht)).1`. Rewrite `h0` using `[List.map_cons, List.sum_cons]`. Establish `e1 : w n s.2.1 - w n s.2.2 = 0` using `by linarith [hs.1]`.

Establish `e2 : (L.map fun s => w n s.2.1 - w n s.2.2).sum = 0` using `by linarith [hs.1]`. Break down `List.mem_cons.1 hs' with rfl | hs'` into its components or cases. Conclude with `hs.2 e1`. Conclude with `ih hL e2 s' hs'`.
-/
private theorem wsum {G : Type} {n : ℕ} (hn : n = 2 ∨ n = 3) (L : List (G × Fin n × Fin n))
    (h : ∀ s ∈ L, s.2.1 ≤ s.2.2) (h0 : (L.map fun s => w n s.2.1 - w n s.2.2).sum = 0) : ∀ s ∈ L, s.2.1 = s.2.2 := by
  have hw : ∀ i j : Fin n, i ≤ j → 0 ≤ w n i - w n j ∧ (w n i - w n j = 0 → i = j) := by
    intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    rcases hn with rfl | rfl
    · simp only [w]
      refine ⟨by norm_num; omega, fun e => Fin.ext ?_⟩
      norm_num at e
      omega
    · simp only [w]
      refine ⟨by norm_num; omega, fun e => Fin.ext ?_⟩
      norm_num at e
      omega
  induction L with
  | nil => simp
  | cons s L ih =>
    intro s' hs'
    have hs := hw s.2.1 s.2.2 (h s (List.mem_cons_self ..))
    have hL : ∀ t ∈ L, t.2.1 ≤ t.2.2 := fun t ht => h t (List.mem_cons_of_mem _ ht)
    have hnn : 0 ≤ (L.map fun s => w n s.2.1 - w n s.2.2).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      exact (hw _ _ (hL t ht)).1
    rw [List.map_cons, List.sum_cons] at h0
    have e1 : w n s.2.1 - w n s.2.2 = 0 := by linarith [hs.1]
    have e2 : (L.map fun s => w n s.2.1 - w n s.2.2).sum = 0 := by linarith [hs.1]
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact hs.2 e1
    · exact ih hL e2 s' hs'

/- English proof (translation)
Establish `hr : ∀ g i j, (ρ.map (residue C)).r g i j = residue C (ρ.r g i j)` using `fun _ _ _ => rfl`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_list_prod, List.map_map]`. Apply `List.prod_eq_zero` to reduce the goal to its premises. Break down `tri_of_bar hF hn f (ρ.map (residue C)) hρ with ht | ht` into its components or cases. Distinguish the cases in `hex : ∃ s ∈ L, s.2.2 < s.2.1`.

Take `⟨s, hs, hlt⟩` from `hex`. Use `List.mem_map.2 ⟨s, hs, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[← hr]`. Conclude with `ht _ _ _ hlt`.

Use `push_neg at hex`. It suffices to derive a contradiction. Take `⟨s, hs, hne⟩` from `h1`. Conclude with `hne (wsum hn L hex h0 s hs)`. Distinguish the cases in `hex : ∃ s ∈ L, s.2.1 < s.2.2`.

Take `⟨s, hs, hlt⟩` from `hex`. Use `List.mem_map.2 ⟨s, hs, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[← hr]`. Conclude with `ht _ _ _ hlt`.

Use `push_neg at hex`. It suffices to derive a contradiction. Take `⟨s, hs, hne⟩` from `h1`. Establish `hL' : ∀ t ∈ L.map (fun s => (s.1, s.2.2, s.2.1)), t.2.1 ≤ t.2.2`. Introduce `t ht`.

Take `⟨s, hs, rfl⟩` from `List.mem_map.1 ht`. Conclude with `hex s hs`. Establish `h0' : ((L.map (fun s => (s.1, s.2.2, s.2.1))).map fun s => w n s.2.1 - w n s.2.2).sum = 0`. Establish `e : ((L.map (fun s => (s.1, s.2.2, s.2.1))).map fun s => w n s.2.1 - w n s.2.2) = (L.map fun s => w n s.2.1 - w n s.2.2).map Neg.neg`. Simplify using `[List.map_map, Function.comp_def]`.

Establish `hneg : ∀ m : List ℤ, (m.map Neg.neg).sum = -m.sum`. Introduce `m`. Proceed by induction on `m with`. Consider the case `nil => simp`. Consider the case `cons a m ih => simp only [List.map_cons, List.sum_cons, ih]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hneg, h0, neg_zero]`. Conclude with `hne (wsum hn _ hL' h0' (s.1, s.2.2, s.2.1) (List.mem_map.2 ⟨s, hs, rfl⟩)).symm`.
-/
private theorem cyc_mem {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}
    (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) {C : Type} [CommRing C] [IsLocalRing C] (f : k →+* ResidueField C)
    (ρ : NRep F n C) (hρ : (ρ.map (residue C)).IsBar f) (L : List (F.G0 × Fin n × Fin n))
    (h0 : (L.map fun s => w n s.2.1 - w n s.2.2).sum = 0) (h1 : ∃ s ∈ L, s.2.1 ≠ s.2.2) :
    (L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod ∈ maximalIdeal C := by
  have hr : ∀ g i j, (ρ.map (residue C)).r g i j = residue C (ρ.r g i j) := fun _ _ _ => rfl
  rw [← IsLocalRing.residue_eq_zero_iff, map_list_prod, List.map_map]
  apply List.prod_eq_zero
  rcases tri_of_bar hF hn f (ρ.map (residue C)) hρ with ht | ht
  · by_cases hex : ∃ s ∈ L, s.2.2 < s.2.1
    · obtain ⟨s, hs, hlt⟩ := hex
      refine List.mem_map.2 ⟨s, hs, ?_⟩
      simp only [Function.comp_apply]
      rw [← hr]
      exact ht _ _ _ hlt
    · push_neg at hex
      exfalso
      obtain ⟨s, hs, hne⟩ := h1
      exact hne (wsum hn L hex h0 s hs)
  · by_cases hex : ∃ s ∈ L, s.2.1 < s.2.2
    · obtain ⟨s, hs, hlt⟩ := hex
      refine List.mem_map.2 ⟨s, hs, ?_⟩
      simp only [Function.comp_apply]
      rw [← hr]
      exact ht _ _ _ hlt
    · push_neg at hex
      exfalso
      obtain ⟨s, hs, hne⟩ := h1
      have hL' : ∀ t ∈ L.map (fun s => (s.1, s.2.2, s.2.1)), t.2.1 ≤ t.2.2 := by
        intro t ht
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
        exact hex s hs
      have h0' : ((L.map (fun s => (s.1, s.2.2, s.2.1))).map fun s => w n s.2.1 - w n s.2.2).sum = 0 := by
        have e : ((L.map (fun s => (s.1, s.2.2, s.2.1))).map fun s => w n s.2.1 - w n s.2.2) =
            (L.map fun s => w n s.2.1 - w n s.2.2).map Neg.neg := by
          simp [List.map_map, Function.comp_def]
        have hneg : ∀ m : List ℤ, (m.map Neg.neg).sum = -m.sum := by
          intro m
          induction m with
          | nil => simp
          | cons a m ih => simp only [List.map_cons, List.sum_cons, ih]; ring
        rw [e, hneg, h0, neg_zero]
      exact hne (wsum hn _ hL' h0' (s.1, s.2.2, s.2.1) (List.mem_map.2 ⟨s, hs, rfl⟩)).symm

/- English proof (translation)
Break down `isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩` into its components or cases. Conclude with `IsLocallyConstant.of_constant _ (fun x => (hX.false x).elim)`. Establish `e : g = (fun a => if ha : ∃ x, φ x = a then g ha.choose else g x₀) ∘ φ`. Use function extensionality and compare the values at `x`. Establish `ha : ∃ y, φ y = φ x` using `⟨x, rfl⟩`.

Simplify using `only [Function.comp_apply, dif_pos ha]`. Conclude with `h _ _ ha.choose_spec.symm`. Rewrite using `[e]`. Conclude with `hφ.comp _`.
-/
private theorem lc_lemma {X A B : Type} [TopologicalSpace X] (φ : X → A) (g : X → B)
    (hφ : IsLocallyConstant φ) (h : ∀ x y, φ x = φ y → g x = g y) : IsLocallyConstant g := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact IsLocallyConstant.of_constant _ (fun x => (hX.false x).elim)
  have e : g = (fun a => if ha : ∃ x, φ x = a then g ha.choose else g x₀) ∘ φ := by
    funext x
    have ha : ∃ y, φ y = φ x := ⟨x, rfl⟩
    simp only [Function.comp_apply, dif_pos ha]
    exact h _ _ ha.choose_spec.symm
  rw [e]
  exact hφ.comp _

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ hCL f hf ρ hρc hρ`. Take `⟨S', hmem, hfin, hCO, hpow⟩` from `UpperTheory.V.CA.cl_sub O C hCL`. Take `⟨hBco, hmB⟩` from `co_B hF hn S`. Establish `hJ : ∀ c ∈ maximalIdeal C, c ∈ S'` using `fun c hc => (hmem c).2 ⟨0, by simpa using hc⟩`. Establish `hmax : ∀ c : S', c ∈ maximalIdeal S' ↔ (c : C) ∈ maximalIdeal C`.

Introduce `c`. Simplify using `using hpow 1 c`. Establish `hin : ∀ (c : C) (t : ResidueField O), residue C c = f t → c ∈ S'`. Introduce `c t h`. Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective t`.

Use `(hmem c).2 ⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, h, hf a, sub_self]`. Establish `hres : ∀ (c : S') (t : ResidueField O), residue C (c : C) = f t → res O S' c = t`. Introduce `c t h`. Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective t`.

Establish `d : c - algebraMap O S' a ∈ maximalIdeal S'`. Rewrite using `[hmax]`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff]`. Simplify using `only [Subalgebra.coe_sub, Subalgebra.coe_algebraMap, map_sub, h, hf a, sub_self]`. Establish `d2` using `(res_eq_zero_iff O S' _).2 d`.

Rewrite `d2` using `[map_sub, AlgHom.commutes, sub_eq_zero]`. Rewrite using `[d2, IsLocalRing.ResidueField.algebraMap_eq]`. Establish `hJN : ∀ N, ∀ c ∈ maximalIdeal C ^ N, c ∈ ((maximalIdeal S' ^ N • ⊤ : Submodule S' C))`. Introduce `N c hc`. Establish `hle : maximalIdeal C ≤ Ideal.map (algebraMap S' C) (maximalIdeal S')`.

Introduce `c hc`. Conclude with `Ideal.mem_map_of_mem (algebraMap S' C) ((hmax ⟨c, hJ c hc⟩).2 hc)`. Establish `hc'` using `Ideal.pow_right_mono hle N hc`. Rewrite `hc'` using `[← Ideal.map_pow]`. Rewrite using `[Ideal.smul_top_eq_map]`.

Conclude with `hc'`. Establish `cone : Cone O S' ρ`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g i`. Conclude with `⟨⟨ρ.r g i i, hin _ _ (hρ.1 g i)⟩, rfl, hres ⟨ρ.r g i i, hin _ _ (hρ.1 g i)⟩ _ (hρ.1 g i)⟩`.

Introduce `L h0 h1`. Establish `hp` using `cyc_mem hF hn f ρ hρ L h0 h1`. Conclude with `⟨⟨_, hJ _ hp⟩, (hmax _).2 hp, rfl⟩`. Introduce `i j haveI : IsNoetherian S' C := isNoetherian_of_isNoetherianRing_of_finite S' C`. Conclude with `IsNoetherian.noetherian _`.

Introduce `i j N`. Conclude with `cont_sub (maximalIdeal S') (maximalIdeal C) hJN (fun g => ρ.r g i j) (hρc.1 i j) N`. Use `⟨fun v i g => ⟨((ρ.ψ v i g : Cˣ) : C), hin _ _ (hρ.2 v i g)⟩, ?_, fun v i g => rfl⟩` and prove the remaining obligations. Introduce `v i`. Use `⟨?_, fun g => hres _ _ (hρ.2 v i g)⟩` and prove the remaining obligations.

Introduce `N`. Use `lc_lemma _ _ (hρc.2 v i N) ?_` and prove the remaining obligations. Introduce `x y hxy`. Apply `Ideal.Quotient.eq.2` to reduce the goal to its premises. Rewrite using `[hpow]`.

Conclude with `Ideal.Quotient.eq.1 hxy`. Take `⟨ξ, β, h1, h2⟩` from `alg hF hn S S' C Subtype.val_injective ρ cone`. Use `⟨ξ, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[Space.x0, Ideal.map_le_iff_le_comap]`. Introduce `b hb`.

Rewrite `hb` using `[← hmB]`. Use `show ξ (S.inc b) ∈ maximalIdeal C`. Rewrite using `[h2]`. Apply `(hmax _).1` to reduce the goal to its premises. Rewrite using `[← res_eq_zero_iff O S', res_map]`.

Conclude with `(res_eq_zero_iff O S.B b).2 hb`.
-/
theorem UpperTheory.V.Fr.point_loc :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [IsLocalRing C] [Algebra O C], UpperTheory.V.CA.IsCL O C → ∀ (f : ResidueField O →+* ResidueField C), IsResMap O C f → ∀ ρ : NRep F n C, ρ.Cont (maximalIdeal C) → (ρ.map (residue C)).IsBar f → ∃ ξ : S.A →ₐ[O] C, S.u.map (ξ : S.A →+* C) = ρ ∧ S.x0 ≤ (maximalIdeal C).comap (ξ : S.A →+* C) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ hCL f hf ρ hρc hρ
  obtain ⟨S', hmem, hfin, hCO, hpow⟩ := UpperTheory.V.CA.cl_sub O C hCL
  obtain ⟨hBco, hmB⟩ := co_B hF hn S
  have hJ : ∀ c ∈ maximalIdeal C, c ∈ S' := fun c hc => (hmem c).2 ⟨0, by simpa using hc⟩
  have hmax : ∀ c : S', c ∈ maximalIdeal S' ↔ (c : C) ∈ maximalIdeal C := by
    intro c
    simpa using hpow 1 c
  have hin : ∀ (c : C) (t : ResidueField O), residue C c = f t → c ∈ S' := by
    intro c t h
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective t
    refine (hmem c).2 ⟨a, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, hf a, sub_self]
  have hres : ∀ (c : S') (t : ResidueField O), residue C (c : C) = f t → res O S' c = t := by
    intro c t h
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective t
    have d : c - algebraMap O S' a ∈ maximalIdeal S' := by
      rw [hmax]
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp only [Subalgebra.coe_sub, Subalgebra.coe_algebraMap, map_sub, h, hf a, sub_self]
    have d2 := (res_eq_zero_iff O S' _).2 d
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at d2
    rw [d2, IsLocalRing.ResidueField.algebraMap_eq]
  have hJN : ∀ N, ∀ c ∈ maximalIdeal C ^ N, c ∈ ((maximalIdeal S' ^ N • ⊤ : Submodule S' C)) := by
    intro N c hc
    have hle : maximalIdeal C ≤ Ideal.map (algebraMap S' C) (maximalIdeal S') := by
      intro c hc
      exact Ideal.mem_map_of_mem (algebraMap S' C) ((hmax ⟨c, hJ c hc⟩).2 hc)
    have hc' := Ideal.pow_right_mono hle N hc
    rw [← Ideal.map_pow] at hc'
    rw [Ideal.smul_top_eq_map]
    exact hc'
  have cone : Cone O S' ρ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro g i
      exact ⟨⟨ρ.r g i i, hin _ _ (hρ.1 g i)⟩, rfl, hres ⟨ρ.r g i i, hin _ _ (hρ.1 g i)⟩ _ (hρ.1 g i)⟩
    · intro L h0 h1
      have hp := cyc_mem hF hn f ρ hρ L h0 h1
      exact ⟨⟨_, hJ _ hp⟩, (hmax _).2 hp, rfl⟩
    · intro i j
      haveI : IsNoetherian S' C := isNoetherian_of_isNoetherianRing_of_finite S' C
      exact IsNoetherian.noetherian _
    · intro i j N
      exact cont_sub (maximalIdeal S') (maximalIdeal C) hJN (fun g => ρ.r g i j) (hρc.1 i j) N
    · refine ⟨fun v i g => ⟨((ρ.ψ v i g : Cˣ) : C), hin _ _ (hρ.2 v i g)⟩, ?_, fun v i g => rfl⟩
      intro v i
      refine ⟨?_, fun g => hres _ _ (hρ.2 v i g)⟩
      intro N
      refine lc_lemma _ _ (hρc.2 v i N) ?_
      intro x y hxy
      apply Ideal.Quotient.eq.2
      rw [hpow]
      exact Ideal.Quotient.eq.1 hxy
  obtain ⟨ξ, β, h1, h2⟩ := alg hF hn S S' C Subtype.val_injective ρ cone
  refine ⟨ξ, h1, ?_⟩
  rw [Space.x0, Ideal.map_le_iff_le_comap]
  intro b hb
  rw [← hmB] at hb
  show ξ (S.inc b) ∈ maximalIdeal C
  rw [h2]
  apply (hmax _).1
  rw [← res_eq_zero_iff O S', res_map]
  exact (res_eq_zero_iff O S.B b).2 hb

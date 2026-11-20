import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF

noncomputable section

namespace PI.VolStabSW.FFHS

open Module

variable {K : Type} [Field K] {σ : K →+* K}

structure IsSq {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) :
    Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (c : K) x y, h x (c • y) = c * h x y
  herm : ∀ x y, h y x = σ (h x y)

structure IsHS {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) : Prop
    extends IsSq σ h where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

section basic

variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

def IsSq.lin (hs : IsSq σ h) (x : V) : V →ₗ[K] K where
  toFun := h x
  map_add' := hs.add_right x
  map_smul' c y := by simp [hs.smul_right]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem IsSq.lin_apply (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl

/- English proof (translation)
Rewrite using `[hs.herm z (x + y), hs.add_right, map_add, ← hs.herm, ← hs.herm]`.
-/
theorem IsSq.add_left (hs : IsSq σ h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hs.herm z (x + y), hs.add_right, map_add, ← hs.herm, ← hs.herm]

/- English proof (translation)
Rewrite using `[hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm]`.
-/
theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm]

/- English proof (translation)
Establish `h0` using `hs.smul_right 0 x 0`. Simplify using `using h0`.
-/
theorem IsSq.zero_right (hs : IsSq σ h) (x : V) : h x 0 = 0 := by
  have h0 := hs.smul_right 0 x 0
  simpa using h0

/- English proof (translation)
Rewrite using `[hs.herm y 0, hs.zero_right, map_zero]`.
-/
theorem IsSq.zero_left (hs : IsSq σ h) (y : V) : h 0 y = 0 := by
  rw [hs.herm y 0, hs.zero_right, map_zero]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, hs.add_right, ← neg_one_smul K z, hs.smul_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z := by
  rw [sub_eq_add_neg, hs.add_right, ← neg_one_smul K z, hs.smul_right]
  ring

/- English proof (translation)
Conclude with `(hs.herm x x).symm`.
-/
theorem IsSq.self_fixed (hs : IsSq σ h) (x : V) : σ (h x x) = h x x := by
  exact (hs.herm x x).symm

/- English proof (translation)
Establish `h1 : ∀ i y, h (b i) y = h' (b i) y`. Introduce `i y`. Establish `e` using `b.ext (f₁ := hs.lin (b i)) (f₂ := hs'.lin (b i)) (fun j => hb i j)`. Conclude with `LinearMap.congr_fun e y`. Establish `h3 : ∀ x y, h y x = h' y x`.

Introduce `x y`. Establish `e` using `b.ext (f₁ := hs.lin y) (f₂ := hs'.lin y) (fun i => by`. Simplify using `only [IsSq.lin_apply]`. Rewrite using `[hs.herm (b i) y, hs'.herm (b i) y, h1])`. Conclude with `LinearMap.congr_fun e x`.

Conclude with `h3 y x`.
-/
theorem IsSq.ext_basis {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have h1 : ∀ i y, h (b i) y = h' (b i) y := by
    intro i y
    have e := b.ext (f₁ := hs.lin (b i)) (f₂ := hs'.lin (b i)) (fun j => hb i j)
    exact LinearMap.congr_fun e y
  have h3 : ∀ x y, h y x = h' y x := by
    intro x y
    have e := b.ext (f₁ := hs.lin y) (f₂ := hs'.lin y) (fun i => by
      simp only [IsSq.lin_apply]
      rw [hs.herm (b i) y, hs'.herm (b i) y, h1])
    exact LinearMap.congr_fun e x
  exact h3 y x

/- English proof (translation)
Assume the negation of the conclusion as `H`. Use `push_neg at H`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by`. Assume the negation of the conclusion as `H'`. Use `push_neg at H'`.

Conclude with `hx (hs.nondeg x H')`. Establish `key : ∀ c : K, c * h x y + σ (c * h x y) = 0`. Introduce `c`. Establish `e1 : h (x + c • y) (x + c • y) = h x x + h x (c • y) + (h (c • y) x + h (c • y) (c • y))`. Rewrite using `[hs.add_right, IsSq.add_left hs.toIsSq, IsSq.add_left hs.toIsSq]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `e1` using `[H, H, H, hs.herm x (c • y), hs.smul_right]`. Take the linear combination `-e1`. Establish `ha : h x y + σ (h x y) = 0` using `by simpa using key 1`. Distinguish the cases in `hσ : ∃ c, σ c ≠ c`.

Take `⟨c, hc⟩` from `hσ`. Establish `e2` using `key c`. Rewrite `e2` using `[map_mul]`. Establish `hsa : σ (h x y) = -(h x y)` using `by linear_combination ha`. Rewrite `e2` using `[hsa]`.

Establish `e3 : (c - σ c) * h x y = 0` using `by linear_combination e2`. Break down `mul_eq_zero.1 e3 with h0 | h0` into its components or cases. Conclude with `hc (by linear_combination -h0)`. Conclude with `hy h0`. Use `push_neg at hσ`.

Rewrite `ha` using `[hσ]`. Establish `e3 : (2 : K) * h x y = 0` using `by linear_combination ha`. Break down `mul_eq_zero.1 e3 with h0 | h0` into its components or cases. Conclude with `h2 h0`. Conclude with `hy h0`.
-/
theorem exists_aniso (h2 : (2 : K) ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by
  by_contra H
  push_neg at H
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra H'
    push_neg at H'
    exact hx (hs.nondeg x H')
  have key : ∀ c : K, c * h x y + σ (c * h x y) = 0 := by
    intro c
    have e1 : h (x + c • y) (x + c • y) = h x x + h x (c • y) + (h (c • y) x + h (c • y) (c • y)) := by
      rw [hs.add_right, IsSq.add_left hs.toIsSq, IsSq.add_left hs.toIsSq]
      ring
    rw [H, H, H, hs.herm x (c • y), hs.smul_right] at e1
    linear_combination -e1
  have ha : h x y + σ (h x y) = 0 := by simpa using key 1
  by_cases hσ : ∃ c, σ c ≠ c
  · obtain ⟨c, hc⟩ := hσ
    have e2 := key c
    rw [map_mul] at e2
    have hsa : σ (h x y) = -(h x y) := by linear_combination ha
    rw [hsa] at e2
    have e3 : (c - σ c) * h x y = 0 := by linear_combination e2
    rcases mul_eq_zero.1 e3 with h0 | h0
    · exact hc (by linear_combination -h0)
    · exact hy h0
  · push_neg at hσ
    rw [hσ] at ha
    have e3 : (2 : K) * h x y = 0 := by linear_combination ha
    rcases mul_eq_zero.1 e3 with h0 | h0
    · exact h2 h0
    · exact hy h0

def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)

/- English proof (translation)
Conclude with `LinearMap.mem_ker`.
-/
theorem mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := by
  exact LinearMap.mem_ker

/- English proof (translation)
The claim follows from `hs.add_right x y z smul_right c x y := hs.smul_right c x y herm x y := hs.herm x y nondeg w hw := by have hq := hs.toIsSq apply Subtype.ext apply hs.nondeg intro y have hm : y - ((h e e)⁻¹ * h e y) • e ∈ perp hq e := by have : (h e e)⁻¹ * h e y * h e e = h e y := by rw [mul_comm, …`.
-/
theorem perp_isHS (hs : IsHS σ h) (e : V) (he : h e e ≠ 0) :
    IsHS σ (fun w w' : perp hs.toIsSq e => h w w') where
  add_right x y z := hs.add_right x y z
  smul_right c x y := hs.smul_right c x y
  herm x y := hs.herm x y
  nondeg w hw := by
    have hq := hs.toIsSq
    apply Subtype.ext
    apply hs.nondeg
    intro y
    have hm : y - ((h e e)⁻¹ * h e y) • e ∈ perp hq e := by
      have : (h e e)⁻¹ * h e y * h e e = h e y := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
      rw [mem_perp, hq.sub_right, hq.smul_right, this, sub_self]
    have h1 := hw ⟨_, hm⟩
    have hwe : h w e = 0 := by rw [hq.herm e w, (mem_perp hq e w).1 w.2, map_zero]
    calc h w y = h w (((h e e)⁻¹ * h e y) • e + (y - ((h e e)⁻¹ * h e y) • e)) := by
          rw [add_sub_cancel]
      _ = ((h e e)⁻¹ * h e y) * h w e + h w (y - ((h e e)⁻¹ * h e y) • e) := by
          rw [hq.add_right, hq.smul_right]
      _ = 0 := by rw [hwe, h1]; ring

/- English proof (translation)
Establish `hsurj : LinearMap.range (hs.lin e) = ⊤`. Rewrite using `[LinearMap.range_eq_top]`. Introduce `c`. Use `⟨(c / h e e) • e, ?_⟩` and prove the remaining obligations. Rewrite using `[IsSq.lin_apply, hs.smul_right, div_mul_cancel₀ _ he]`.

Establish `e1` using `LinearMap.finrank_range_add_finrank_ker (hs.lin e)`. Rewrite `e1` using `[hsurj, finrank_top, Module.finrank_self]`. Unfold `perp`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_perp [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : LinearMap.range (hs.lin e) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨(c / h e e) • e, ?_⟩
    rw [IsSq.lin_apply, hs.smul_right, div_mul_cancel₀ _ he]
  have e1 := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [hsurj, finrank_top, Module.finrank_self] at e1
  unfold perp
  omega

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `e1` using `congrArg (hs.lin (f i)) hg`. Rewrite `e1` using `[map_sum, map_zero]`. Simplify using `only [map_smul, IsSq.lin_apply, smul_eq_mul] at e1`.

Rewrite `e1` using `[Finset.sum_eq_single i]`. Conclude with `(mul_eq_zero.1 e1).resolve_right (h2 i)`. Introduce `j _ hji`. Rewrite using `[h1 i j (Ne.symm hji), mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem linIndep_orth (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have e1 := congrArg (hs.lin (f i)) hg
  rw [map_sum, map_zero] at e1
  simp only [map_smul, IsSq.lin_apply, smul_eq_mul] at e1
  rw [Finset.sum_eq_single i] at e1
  · exact (mul_eq_zero.1 e1).resolve_right (h2 i)
  · intro j _ hji
    rw [h1 i j (Ne.symm hji), mul_zero]
  · simp

/- English proof (translation)
Establish `hwe : h w e = 0` using `by rw [hs.herm e w, hw, map_zero]`. Rewrite using `[hs.add_right, IsSq.add_left hs, IsSq.add_left hs, IsSq.smul_left hs, IsSq.smul_left hs, hs.smul_right, hs.smul_right, hw, hwe]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem decomp_val (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  have hwe : h w e = 0 := by rw [hs.herm e w, hw, map_zero]
  rw [hs.add_right, IsSq.add_left hs, IsSq.add_left hs, IsSq.smul_left hs, IsSq.smul_left hs, hs.smul_right,
    hs.smul_right, hw, hwe]
  ring

end basic

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `V _ _ _ h hs hm`. Conclude with `⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩`.

Consider the case `succ n ih`. Introduce `V _ _ _ h hs hm`. Take `⟨x, hx⟩` from `Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank K V)`. Take `⟨e, he⟩` from `exists_aniso h2 hs x hx`. Establish `hp` using `perp_isHS hs e he`.

Establish `hr` using `finrank_perp hs.toIsSq e he`. Take `⟨g, hg1, hg2⟩` from `ih (perp hs.toIsSq e) (fun w w' => h w w') hp (by omega)`. Use `⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Apply the tactic sequence `induction i using Fin.cases <;> induction j using Fin.cases`.

Conclude with `absurd rfl hij`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Conclude with `(mem_perp hs.toIsSq e _).1 (g _).2`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[hs.herm e, (mem_perp hs.toIsSq e _).1 (g _).2, map_zero]`.

Simplify using `only [Fin.cons_succ]`. Conclude with `hg1 _ _ (fun h' => hij (by rw [h']))`. Introduce `i`. Proceed by induction on `i using Fin.cases`. Simplify using `using he`.

Simplify using `using hg2 _`.
-/
theorem exists_orth (h2 : (2 : K) ≠ 0) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hs hm
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro V _ _ _ h hs hm
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank K V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hp := perp_isHS hs e he
    have hr := finrank_perp hs.toIsSq e he
    obtain ⟨g, hg1, hg2⟩ := ih (perp hs.toIsSq e) (fun w w' => h w w') hp (by omega)
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases <;> induction j using Fin.cases
      · exact absurd rfl hij
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact (mem_perp hs.toIsSq e _).1 (g _).2
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hs.herm e, (mem_perp hs.toIsSq e _).1 (g _).2, map_zero]
      · simp only [Fin.cons_succ]
        exact hg1 _ _ (fun h' => hij (by rw [h']))
    · intro i
      induction i using Fin.cases
      · simpa using he
      · simpa using hg2 _

end PI.VolStabSW.FFHS

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFF

noncomputable section

namespace PI.VolStabS.FFHS

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
Rewrite using `[hs.herm z (x + y), hs.add_right, map_add, ← hs.herm z x, ← hs.herm z y]`.
-/
theorem IsSq.add_left (hs : IsSq σ h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hs.herm z (x + y), hs.add_right, map_add, ← hs.herm z x, ← hs.herm z y]

/- English proof (translation)
Rewrite using `[hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm y x]`.
-/
theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm y x]

/- English proof (translation)
Simplify using `using hs.add_right x 0 0`.
-/
theorem IsSq.zero_right (hs : IsSq σ h) (x : V) : h x 0 = 0 := by
  simpa using hs.add_right x 0 0

/- English proof (translation)
Rewrite using `[hs.herm y 0, hs.zero_right, map_zero]`.
-/
theorem IsSq.zero_left (hs : IsSq σ h) (y : V) : h 0 y = 0 := by
  rw [hs.herm y 0, hs.zero_right, map_zero]

/- English proof (translation)
The claim follows from `(hs.lin x).map_sub y z`.
-/
theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z :=
  (hs.lin x).map_sub y z

/- English proof (translation)
The claim follows from `(hs.herm x x).symm`.
-/
theorem IsSq.self_fixed (hs : IsSq σ h) (x : V) : σ (h x x) = h x x := (hs.herm x x).symm

/- English proof (translation)
Establish `step1 : ∀ i y, h (b i) y = h' (b i) y` using `fun i y => by`. Establish `: hs.lin (b i) = hs'.lin (b i)` using `b.ext (fun j => hb i j)`. Conclude with `LinearMap.congr_fun this y`. Establish `step2 : ∀ x, hs.lin x = hs'.lin x` using `fun x => b.ext (fun i => by`. Simplify using `only [IsSq.lin_apply]`.

Rewrite using `[hs.herm (b i) x, hs'.herm (b i) x, step1])`. Conclude with `LinearMap.congr_fun (step2 x) y`.
-/
theorem IsSq.ext_basis {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have step1 : ∀ i y, h (b i) y = h' (b i) y := fun i y => by
    have : hs.lin (b i) = hs'.lin (b i) := b.ext (fun j => hb i j)
    exact LinearMap.congr_fun this y
  have step2 : ∀ x, hs.lin x = hs'.lin x := fun x => b.ext (fun i => by
    simp only [IsSq.lin_apply]
    rw [hs.herm (b i) x, hs'.herm (b i) x, step1])
  exact LinearMap.congr_fun (step2 x) y

/- English proof (translation)
Establish `hq` using `hs.toIsSq`. Assume the negation of the conclusion as `H`. Use `push_neg at H`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by`. Assume the negation of the conclusion as `H'`.

Use `push_neg at H'`. Conclude with `hx (hs.nondeg x H')`. Establish `key` using `H (x + (h x y)⁻¹ • y)`. Simplify using `only [hq.add_right, hq.add_left, hq.smul_right, hq.smul_left, H x, H y, hq.herm x y] at key`. Establish `e1 : σ (h x y)⁻¹ * σ (h x y) = 1`.

Rewrite using `[← map_mul, inv_mul_cancel₀ hy, map_one]`. Establish `e2 : (h x y)⁻¹ * h x y = 1` using `inv_mul_cancel₀ hy`. Conclude with `h2 (by linear_combination key - e1 - e2)`.
-/
theorem exists_aniso (h2 : (2 : K) ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by
  have hq := hs.toIsSq
  by_contra H
  push_neg at H
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra H'
    push_neg at H'
    exact hx (hs.nondeg x H')
  have key := H (x + (h x y)⁻¹ • y)
  simp only [hq.add_right, hq.add_left, hq.smul_right, hq.smul_left, H x, H y,
    hq.herm x y] at key
  have e1 : σ (h x y)⁻¹ * σ (h x y) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hy, map_one]
  have e2 : (h x y)⁻¹ * h x y = 1 := inv_mul_cancel₀ hy
  exact h2 (by linear_combination key - e1 - e2)

def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)

/- English proof (translation)
The claim follows from `LinearMap.mem_ker`.
-/
theorem mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := LinearMap.mem_ker

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
Establish `hsurj : Function.Surjective (hs.lin e)` using `fun c => ⟨(c * (h e e)⁻¹) • e, by rw [IsSq.lin_apply, hs.smul_right, mul_assoc, inv_mul_cancel₀ he, mul_one]⟩`. Use `LinearMap.finrank_range_add_finrank_ker (hs.lin e)` as an intermediate fact. Rewrite `this` using `[LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_self]`. Unfold `perp`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_perp [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : Function.Surjective (hs.lin e) := fun c =>
    ⟨(c * (h e e)⁻¹) • e, by rw [IsSq.lin_apply, hs.smul_right, mul_assoc, inv_mul_cancel₀ he,
      mul_one]⟩
  have := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_self] at this
  unfold perp
  omega

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Use `congrArg (hs.lin (f i)) hg` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero, Finset.sum_eq_single i]`. Rewrite `this` using `[map_smul, IsSq.lin_apply, smul_eq_mul]`.

Conclude with `(mul_eq_zero.1 this).resolve_right (h2 i)`. Introduce `j _ hji`. Rewrite using `[map_smul, IsSq.lin_apply, h1 i j (Ne.symm hji), smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem linIndep_orth (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have := congrArg (hs.lin (f i)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single i] at this
  · rw [map_smul, IsSq.lin_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (h2 i)
  · intro j _ hji
    rw [map_smul, IsSq.lin_apply, h1 i j (Ne.symm hji), smul_zero]
  · simp

/- English proof (translation)
Simplify using `only [hs.add_right, hs.add_left, hs.smul_right, hs.smul_left, hw, hs.herm e w, map_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem decomp_val (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  simp only [hs.add_right, hs.add_left, hs.smul_right, hs.smul_left, hw, hs.herm e w, map_zero]
  ring

end basic

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro V _ _ _ h _ _`. Conclude with `⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩`. Consider the case `succ m ih`.

Introduce `V _ _ _ h hs hm`. Establish `: Nontrivial V` using `Module.nontrivial_of_finrank_eq_succ hm`. Take `⟨x, hx⟩` from `exists_ne (0 : V)`. Take `⟨e, he⟩` from `exists_aniso h2 hs x hx`. Establish `hq` using `hs.toIsSq`.

Establish `hfr : finrank K (perp hq e) = m` using `by have := finrank_perp hq e he; omega`. Take `⟨g, hg1, hg2⟩` from `ih (perp hq e) (fun w w' => h w w') (perp_isHS hs e he) hfr`. Use `⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Proceed by induction on `i using Fin.cases with`.

Consider the case `zero`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact absurd rfl hij`. Consider the case `succ j => simpa using (mem_perp hq e (g j)).1 (g j).2`. Consider the case `succ i`.

Proceed by induction on `j using Fin.cases with`. Consider the case `zero`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[hq.herm e, (mem_perp hq e (g i)).1 (g i).2, map_zero]`. Consider the case `succ j`.

Simplify using `only [Fin.cons_succ]`. Conclude with `hg1 i j (fun hh => hij (by rw [hh]))`. Introduce `i`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simpa using he`.

Consider the case `succ i => simpa using hg2 i`.
-/
theorem exists_orth (h2 : (2 : K) ≠ 0) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero => intro V _ _ _ h _ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro V _ _ _ h hs hm
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hq := hs.toIsSq
    have hfr : finrank K (perp hq e) = m := by have := finrank_perp hq e he; omega
    obtain ⟨g, hg1, hg2⟩ := ih (perp hq e) (fun w w' => h w w') (perp_isHS hs e he) hfr
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (mem_perp hq e (g j)).1 (g j).2
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hq.herm e, (mem_perp hq e (g i)).1 (g i).2, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hg1 i j (fun hh => hij (by rw [hh]))
    · intro i
      induction i using Fin.cases with
      | zero => simpa using he
      | succ i => simpa using hg2 i

end PI.VolStabS.FFHS

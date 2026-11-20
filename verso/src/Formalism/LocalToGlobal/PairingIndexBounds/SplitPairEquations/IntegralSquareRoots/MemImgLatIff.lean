import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume

noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.L2.Th1.H

variable {ι : Type} [Fintype ι] {V V₁ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁]

structure Copies (e : V ≃ₗ[ℂ] (ι → V₁)) (H : Sesq V) (H₁ : Sesq V₁) (α : V → ℂ) (α₁ : V₁ → ℂ)
    (Λ : AddSubgroup V) (Λ₁ : AddSubgroup V₁) (δ Ae : V ≃ₗ[ℂ] V) (δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁) : Prop where
  form : ∀ x y, H x y = ∑ i, H₁ (e x i) (e y i)
  char : ∀ x ∈ Λ, α x = ∏ i, α₁ (e x i)
  lat : ∀ x, x ∈ Λ ↔ ∀ i, e x i ∈ Λ₁
  map : ∀ x i, e (δ x) i = δ₁ (e x i)
  cay : ∀ x i, e (Ae x) i = Ae₁ (e x i)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩ show g.symm (g y) ∈ M`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Conclude with `hy`. Introduce `h`.

Conclude with `⟨g.symm x, h, g.apply_symm_apply x⟩`.
-/
theorem mem_imgLat_iff {W : Type} [AddCommGroup W] [Module ℂ W] (g : W ≃ₗ[ℂ] W) (M : AddSubgroup W) (x : W) :
    x ∈ imgLat (g : W →ₗ[ℂ] W) M ↔ g.symm x ∈ M := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show g.symm (g y) ∈ M
    rw [LinearEquiv.symm_apply_apply]; exact hy
  · intro h
    exact ⟨g.symm x, h, g.apply_symm_apply x⟩

/- English proof (translation)
Use `h (g.symm x) i` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[this, LinearEquiv.symm_apply_apply]`.
-/
theorem symm_coord (e : V ≃ₗ[ℂ] (ι → V₁)) (g : V ≃ₗ[ℂ] V) (g₁ : V₁ ≃ₗ[ℂ] V₁) (h : ∀ x i, e (g x) i = g₁ (e x i))
    (x : V) (i : ι) : e (g.symm x) i = g₁.symm (e x i) := by
  have := h (g.symm x) i
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this, LinearEquiv.symm_apply_apply]

variable {e : V ≃ₗ[ℂ] (ι → V₁)} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ} {α₁ : V₁ → ℂ}
  {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}

/- English proof (translation)
Unfold `latA`. Simplify using `only [mem_imgLat_iff, AddSubgroup.mem_inf, c.lat, symm_coord e Ae Ae₁ c.cay, symm_coord e δ δ₁ c.map]`. Conclude with `forall_and.symm`.
-/
theorem Copies.mem_latA (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (x : V) :
    x ∈ latA Λ δ Ae ↔ ∀ i, e x i ∈ latA Λ₁ δ₁ Ae₁ := by
  unfold latA
  simp only [mem_imgLat_iff, AddSubgroup.mem_inf, c.lat, symm_coord e Ae Ae₁ c.cay, symm_coord e δ δ₁ c.map]
  exact forall_and.symm

def prodReps (e : V ≃ₗ[ℂ] (ι → V₁)) (S₁ : Finset V₁) : Finset V :=
  (Fintype.piFinset fun _ : ι => S₁).image e.symm

/- English proof (translation)
Unfold `prodReps`. Rewrite using `[Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, rfl⟩ i`. Rewrite using `[LinearEquiv.apply_symm_apply]`.

Conclude with `Fintype.mem_piFinset.mp hp i`. Introduce `h`. Conclude with `⟨e x, Fintype.mem_piFinset.mpr h, e.symm_apply_apply x⟩`.
-/
theorem mem_prodReps (S₁ : Finset V₁) (x : V) : x ∈ prodReps e S₁ ↔ ∀ i, e x i ∈ S₁ := by
  unfold prodReps
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩ i
    rw [LinearEquiv.apply_symm_apply]
    exact Fintype.mem_piFinset.mp hp i
  · intro h
    exact ⟨e x, Fintype.mem_piFinset.mpr h, e.symm_apply_apply x⟩

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hS`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Conclude with `(c.lat x).2 fun i => h1 _ ((mem_prodReps S₁ x).1 hx i)`. Introduce `x hx y hy hxy`.

Apply `e.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `h2 _ ((mem_prodReps S₁ x).1 hx i) _ ((mem_prodReps S₁ y).1 hy i) ?_` and prove the remaining obligations. Use `(c.mem_latA (x - y)).1 hxy i` as an intermediate fact. Rewrite `this` using `[map_sub]`. Then use the resulting hypothesis.

Introduce `y hy`. Establish `hy'` using `(c.lat y).1 hy`. Use `choose s hs hs' using fun i => h3 (e y i) (hy' i)`. Use `⟨e.symm s, (mem_prodReps S₁ _).2 fun i => by rw [LinearEquiv.apply_symm_apply]; exact hs i, ?_⟩` and prove the remaining obligations. Use `(c.mem_latA _).2 fun i => ?_` and prove the remaining obligations.

Rewrite using `[map_sub, LinearEquiv.apply_symm_apply]`. Conclude with `hs' i`.
-/
theorem Copies.reps (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) {S₁ : Finset V₁}
    (hS : IsReps (latA Λ₁ δ₁ Ae₁) Λ₁ S₁) : IsReps (latA Λ δ Ae) Λ (prodReps e S₁) := by
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (c.lat x).2 fun i => h1 _ ((mem_prodReps S₁ x).1 hx i)
  · intro x hx y hy hxy
    apply e.injective
    funext i
    refine h2 _ ((mem_prodReps S₁ x).1 hx i) _ ((mem_prodReps S₁ y).1 hy i) ?_
    have := (c.mem_latA (x - y)).1 hxy i
    rwa [map_sub] at this
  · intro y hy
    have hy' := (c.lat y).1 hy
    choose s hs hs' using fun i => h3 (e y i) (hy' i)
    refine ⟨e.symm s, (mem_prodReps S₁ _).2 fun i => by rw [LinearEquiv.apply_symm_apply]; exact hs i, ?_⟩
    refine (c.mem_latA _).2 fun i => ?_
    rw [map_sub, LinearEquiv.apply_symm_apply]
    exact hs' i

/- English proof (translation)
Unfold `phiC`. Rewrite using `[Finset.prod_mul_distrib, c.char x hx, ← Complex.exp_sum, c.form, Finset.mul_sum]`. Use `congr 2`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 2`.

Unfold `cayC`. Rewrite using `[map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, symm_coord e Ae Ae₁ c.cay]`.
-/
theorem Copies.phi (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) {x : V} (hx : x ∈ Λ) :
    phiC H α Ae x = ∏ i, phiC H₁ α₁ Ae₁ (e x i) := by
  unfold phiC
  rw [Finset.prod_mul_distrib, c.char x hx, ← Complex.exp_sum, c.form, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  unfold cayC
  rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, symm_coord e Ae Ae₁ c.cay]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg ha n), ih]`.
-/
theorem sqrt_pow' (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : Real.sqrt (a ^ n) = Real.sqrt a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg ha n), ih]

/- English proof (translation)
Unfold `gaussC`. Establish `hcard : (prodReps e S₁).card = S₁.card ^ Fintype.card ι`. Unfold `prodReps`. Rewrite using `[Finset.card_image_of_injective _ e.symm.injective, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]`. Establish `hsum : ∑ x ∈ prodReps e S₁, phiC H α Ae x = (∑ x ∈ S₁, phiC H₁ α₁ Ae₁ x) ^ Fintype.card ι`.

Unfold `prodReps`. Rewrite using `[Finset.sum_image (fun x _ y _ h => e.symm.injective h), ← Finset.card_univ, ← Finset.prod_const, Finset.prod_univ_sum]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hp'` using `Fintype.mem_piFinset.mp hp`. Rewrite using `[c.phi ((c.lat _).2 fun i => by rw [LinearEquiv.apply_symm_apply]; exact hS _ (hp' i))]`.

Simplify using `only [LinearEquiv.apply_symm_apply]`. Rewrite using `[hcard, hsum, mul_pow, Nat.cast_pow, sqrt_pow' _ (Nat.cast_nonneg _), Complex.ofReal_pow, inv_pow]`.
-/
theorem Copies.gauss (c : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) {S₁ : Finset V₁} (hS : ∀ x ∈ S₁, x ∈ Λ₁) :
    gaussC H α Ae (prodReps e S₁) = gaussC H₁ α₁ Ae₁ S₁ ^ Fintype.card ι := by
  unfold gaussC
  have hcard : (prodReps e S₁).card = S₁.card ^ Fintype.card ι := by
    unfold prodReps
    rw [Finset.card_image_of_injective _ e.symm.injective, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]
  have hsum : ∑ x ∈ prodReps e S₁, phiC H α Ae x = (∑ x ∈ S₁, phiC H₁ α₁ Ae₁ x) ^ Fintype.card ι := by
    unfold prodReps
    rw [Finset.sum_image (fun x _ y _ h => e.symm.injective h), ← Finset.card_univ, ← Finset.prod_const,
      Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Fintype.mem_piFinset.mp hp
    rw [c.phi ((c.lat _).2 fun i => by rw [LinearEquiv.apply_symm_apply]; exact hS _ (hp' i))]
    simp only [LinearEquiv.apply_symm_apply]
  rw [hcard, hsum, mul_pow, Nat.cast_pow, sqrt_pow' _ (Nat.cast_nonneg _), Complex.ofReal_pow, inv_pow]

/- English proof (translation)
Rewrite using `[← LinearMap.det_conj g e, ← Finset.card_univ, ← Finset.prod_const, ← LinearMap.det_pi]`. Use `congr 1`. Use extensionality with `x i`. Simplify using `[h]`.
-/
theorem det_copies [FiniteDimensional ℂ V₁] (e : V ≃ₗ[ℂ] (ι → V₁)) (g : V →ₗ[ℂ] V) (g₁ : V₁ →ₗ[ℂ] V₁)
    (h : ∀ x i, e (g x) i = g₁ (e x i)) : LinearMap.det g = LinearMap.det g₁ ^ Fintype.card ι := by
  rw [← LinearMap.det_conj g e, ← Finset.card_univ, ← Finset.prod_const, ← LinearMap.det_pi]
  congr 1
  ext x i
  simp [h]

end Formalism.L2.PairingIndexBounds.Eq.J

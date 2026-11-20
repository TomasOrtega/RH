import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.Meet

/- English proof (translation)
Establish `hconj` using `h.conj`. Take `⟨n, ρ, hi, hρ⟩` from `h`. Set `j` to `algebraMap K (AlgebraicClosure K)`. Establish `hj : Function.Injective j` using `j.injective`. Use `set T : Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K) := ∑ g : G, ρ (g * y * g⁻¹) with hTdef`.

Establish `hT : ∀ a v, T (ρ a v) = ρ a (T v)`. Introduce `a v`. Simplify using `only [hTdef, LinearMap.sum_apply, map_sum]`. Rewrite using `[← Equiv.sum_comp (Equiv.mulLeft a)]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Simplify using `[mul_assoc]`. Take `⟨c, hc⟩` from `schur_scalar ρ T hT`. Establish `h1 : ∀ u : G, ∑ g : G, ρ.character (g * y * g⁻¹ * u) = c * ρ.character u`. Introduce `u`.

Establish `: LinearMap.trace _ _ (T * ρ u) = c * ρ.character u`. Rewrite using `[hc]`. Simplify using `[Representation.character, Module.End.mul_eq_comp]`. Rewrite using `[← this, hTdef, Finset.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[Representation.character, map_mul]`. Establish `h2 : j ((Fintype.card G : K) * χ y) = c * j (χ 1)`. Use `h1 1` as an intermediate fact. Simplify using `only [mul_one, hρ, hconj] at this`. Rewrite using `[← this]`.

Simplify using `[j]`. Establish `h3 : j (∑ g : G, χ (g * y * g⁻¹ * s)) = c * j (χ s)`. Use `h1 s` as an intermediate fact. Simplify using `only [hρ] at this`. Rewrite using `[map_sum, this]`.

Apply `hj` to reduce the goal to its premises. Rewrite using `[map_mul, h3, map_mul _ _ (χ s), h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_char_conj_mul {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] {χ : G → K}
    (h : IsAbsIrrChar χ) (y s : G) :
    (∑ g : G, χ (g * y * g⁻¹ * s)) * χ 1 = (Fintype.card G : K) * χ y * χ s := by
  classical
  have hconj := h.conj
  obtain ⟨n, ρ, hi, hρ⟩ := h
  let j := algebraMap K (AlgebraicClosure K)
  have hj : Function.Injective j := j.injective
  set T : Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K) := ∑ g : G, ρ (g * y * g⁻¹) with hTdef
  have hT : ∀ a v, T (ρ a v) = ρ a (T v) := by
    intro a v
    simp only [hTdef, LinearMap.sum_apply, map_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft a)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  obtain ⟨c, hc⟩ := schur_scalar ρ T hT
  have h1 : ∀ u : G, ∑ g : G, ρ.character (g * y * g⁻¹ * u) = c * ρ.character u := by
    intro u
    have : LinearMap.trace _ _ (T * ρ u) = c * ρ.character u := by
      rw [hc]; simp [Representation.character, Module.End.mul_eq_comp]
    rw [← this, hTdef, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Representation.character, map_mul]
  have h2 : j ((Fintype.card G : K) * χ y) = c * j (χ 1) := by
    have := h1 1
    simp only [mul_one, hρ, hconj] at this
    rw [← this]
    simp [j]
  have h3 : j (∑ g : G, χ (g * y * g⁻¹ * s)) = c * j (χ s) := by
    have := h1 s
    simp only [hρ] at this
    rw [map_sum, this]
  apply hj
  rw [map_mul, h3, map_mul _ _ (χ s), h2]
  ring

section Op

variable {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
  (σ : K →+* ℂ) (ρ : Representation ℂ G W)

/- English proof (translation)
Establish `hN : ((Fintype.card G : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `e1 : ∀ g : G, ρ (g * y * g⁻¹) (∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u) = ∑ s : G, σ ((chiIdem χ).coeff ((g * y * g⁻¹)⁻¹ * s)) • ρ s u`. Introduce `g`. Rewrite using `[map_sum, ← Equiv.sum_comp (Equiv.mulLeft (g * y * g⁻¹)⁻¹)]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, ← Module.End.mul_apply, ← map_mul]`. Simplify using `[mul_assoc]`. Simplify using `only [e1]`. Rewrite using `[Finset.sum_comm, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_smul, ← map_sum, smul_smul, ← map_mul]`. Use `congr 2`. Establish `e2 : ∀ g : G, (chiIdem χ).coeff ((g * y * g⁻¹)⁻¹ * s) = χ 1 / (Fintype.card G : K) * χ (g * y * g⁻¹ * s⁻¹)`. Introduce `g`. Rewrite using `[coeff_chiIdem]`.

Use `congr 1`. Use `h.conj s (s⁻¹ * (g * y * g⁻¹))` as an intermediate fact. Rewrite using `[_root_.mul_inv_rev, inv_inv, ← this]`. Use `congr 1`. Use `group`.

Simplify using `only [e2]`. Rewrite using `[← Finset.mul_sum, coeff_chiIdem]`. Use `sum_char_conj_mul h y s⁻¹` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Take the linear combination `this`.
-/
theorem class_sum_apply {χ : G → K} (h : IsAbsIrrChar χ) (h1 : χ 1 ≠ 0) (y : G) (u : W) :
    ∑ g : G, ρ (g * y * g⁻¹) (∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u) =
      σ ((Fintype.card G : K) * χ y / χ 1) • ∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u := by
  classical
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have e1 : ∀ g : G, ρ (g * y * g⁻¹) (∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u) =
      ∑ s : G, σ ((chiIdem χ).coeff ((g * y * g⁻¹)⁻¹ * s)) • ρ s u := by
    intro g
    rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft (g * y * g⁻¹)⁻¹)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  simp only [e1]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_smul, ← map_sum, smul_smul, ← map_mul]
  congr 2
  have e2 : ∀ g : G, (chiIdem χ).coeff ((g * y * g⁻¹)⁻¹ * s) =
      χ 1 / (Fintype.card G : K) * χ (g * y * g⁻¹ * s⁻¹) := by
    intro g
    rw [coeff_chiIdem]
    congr 1
    have := h.conj s (s⁻¹ * (g * y * g⁻¹))
    rw [_root_.mul_inv_rev, inv_inv, ← this]
    congr 1
    group
  simp only [e2]
  rw [← Finset.mul_sum, coeff_chiIdem]
  have := sum_char_conj_mul h y s⁻¹
  field_simp
  linear_combination this

end Op

def lvlCoef {K G : Type} [Field K] [Group G] (P : Subgroup G) (ψ : P →* Kˣ) (h : P) : K :=
  (Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)

open Classical in

/- English proof (translation)
Unfold `lvlIdem`. Rewrite using `[Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[MonoidAlgebra.coeff_mul_single_apply, coeff_chiIdem]`. Simplify using `only [lvlCoef, _root_.mul_inv_rev, inv_inv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_chiIdem_mul_lvlIdem {K G : Type} [Field K] [Group G] [Fintype G] (χ : G → K) (P : Subgroup G)
    (ψ : P →* Kˣ) (t : G) :
    (chiIdem χ * lvlIdem P ψ).coeff t =
      χ 1 / (Fintype.card G : K) * ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹) := by
  classical
  unfold lvlIdem
  rw [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [MonoidAlgebra.coeff_mul_single_apply, coeff_chiIdem]
  simp only [lvlCoef, _root_.mul_inv_rev, inv_inv]
  ring

end GlobalTheory.Hk3.Meet

namespace GlobalTheory.Hk3

open GlobalTheory.Hk3.Meet in

/- English proof (translation)
Introduce `K G W _ _ _ _ _ _ _ σ X P ψ ρ U hX hne hst hbot hid`. Establish `hmem : ∀ g, ∀ u ∈ U, ρ g u ∈ U` using `fun g u hu => hst g (Submodule.mem_map_of_mem hu)`. Take `⟨u₀, hu₀, hu₀ne⟩` from `(Submodule.ne_bot_iff U).1 hbot`. Establish `hsplit : ∑ χ ∈ X, ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ = u₀`. Use `Eq.trans ?_ (hid u₀ hu₀)` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Establish `e : (idemOf X).coeff g = ∑ φ ∈ X, (chiIdem φ).coeff g`. Unfold `idemOf`. Simplify using the standard rewrite rules.

Rewrite using `[← Finset.sum_smul, ← map_sum, e]`. Choose the witnesses or unpack the hypotheses as in `⟨χ, hχ, hw⟩ : ∃ χ ∈ X, ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hu₀ne (by rw [← hsplit]; exact Finset.sum_eq_zero hcon)`.

Use `set w₀ := ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ with hw₀`. Establish `hw₀U : w₀ ∈ U` using `Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hmem g _ hu₀)`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, (chiIdem χ * lvlIdem P ψ).coeff t ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Conclude with `hne χ hχ (by`. Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `t`. Simplify using `using hcon t)`. Rewrite `ht` using `[coeff_chiIdem_mul_lvlIdem]`.

Establish `h1 : χ 1 ≠ 0` using `fun e => ht (by simp [e])`. Establish `hc : ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹) ≠ 0` using `right_ne_zero_of_mul ht`. Establish `hN : ((Fintype.card G : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Use `set L : W → W := fun w => ∑ h : P, σ (lvlCoef P ψ h) • ρ (h : G) w with hL`. Establish `hLU : ∀ w ∈ U, L w ∈ U` using `fun w hw => Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (hmem _ _ hw)`.

Establish `hLe : ∀ (p : P) w, ρ p (L w) = σ (ψ p : K) • L w`. Introduce `p w`. Simplify using `only [hL, map_sum, map_smul, Finset.smul_sum]`. Use `(Equiv.sum_comp (Equiv.mulLeft p⁻¹) _).symm.trans (Finset.sum_congr rfl fun h _ => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft]`.

Establish `e1 : lvlCoef P ψ (p⁻¹ * h) = (ψ p : K) * lvlCoef P ψ h`. Simplify using `only [lvlCoef, _root_.mul_inv_rev, inv_inv, map_mul, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ρ (p : G) (ρ ((p⁻¹ * h : P) : G) w) = ρ (h : G) w`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[e1, e2, map_mul, mul_smul]`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hL0 : ∀ w ∈ U, L w = 0`.

Introduce `w hw`. Assume the negation of the conclusion as `hLw`. Take `⟨p, hp⟩` from `hno _ (hLU w hw) hLw`. Conclude with `hp (hLe p w)`. Establish `hz : ∑ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) = 0` using `Finset.sum_eq_zero fun g _ => by rw [hL0 _ (hmem _ _ hw₀U), map_zero]`.

Establish `hz2 : ∑ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) = σ ((Fintype.card G : K) / χ 1 * ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹)) • w₀`. Establish `e : ∀ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) = ∑ h : P, σ (lvlCoef P ψ h) • ρ (g * ((h : G) * t⁻¹) * g⁻¹) w₀`. Introduce `g`. Simplify using `only [hL, map_sum, map_smul]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations.

Rewrite using `[← Module.End.mul_apply (ρ (h : G)), ← map_mul, ← Module.End.mul_apply (ρ g), ← map_mul]`. Simplify using `[mul_assoc]`. Simplify using `only [e]`. Rewrite using `[Finset.sum_comm]`. Establish `e2 : ∀ h : P, ∑ g : G, σ (lvlCoef P ψ h) • ρ (g * ((h : G) * t⁻¹) * g⁻¹) w₀ = σ (lvlCoef P ψ h * ((Fintype.card G : K) * χ ((h : G) * t⁻¹) / χ 1)) • w₀`.

Introduce `h`. Rewrite using `[← Finset.smul_sum, map_mul, mul_smul]`. Use `congr 1`. Conclude with `class_sum_apply σ ρ (hX χ hχ) h1 _ u₀`. Simplify using `only [e2]`.

Rewrite using `[← Finset.sum_smul, ← map_sum, Finset.mul_sum]`. Use `congr 2`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite `hz` using `[hz2]`.

Break down `smul_eq_zero.1 hz with h0 | h0` into its components or cases. Conclude with `(mul_ne_zero (div_ne_zero hN h1) hc) ((map_eq_zero σ).1 h0)`. Conclude with `hw h0`.
-/
theorem exists_level_vector : ∀ {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : K →+* ℂ) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) (ρ : Representation ℂ G W)
    (U : Submodule ℂ W), (∀ χ ∈ X, IsAbsIrrChar χ) → (∀ χ ∈ X, chiIdem χ * lvlIdem P ψ ≠ 0) → (∀ g, U.map (ρ g) ≤ U) →
    U ≠ ⊥ → (∀ u ∈ U, ∑ g, σ ((idemOf X).coeff g) • ρ g u = u) →
    ∃ u ∈ U, u ≠ 0 ∧ ∀ p : P, ρ p u = σ (ψ p : K) • u := by
  intro K G W _ _ _ _ _ _ _ σ X P ψ ρ U hX hne hst hbot hid
  classical
  have hmem : ∀ g, ∀ u ∈ U, ρ g u ∈ U := fun g u hu => hst g (Submodule.mem_map_of_mem hu)

  obtain ⟨u₀, hu₀, hu₀ne⟩ := (Submodule.ne_bot_iff U).1 hbot
  have hsplit : ∑ χ ∈ X, ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ = u₀ := by
    refine Eq.trans ?_ (hid u₀ hu₀)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : (idemOf X).coeff g = ∑ φ ∈ X, (chiIdem φ).coeff g := by
      unfold idemOf
      simp
    rw [← Finset.sum_smul, ← map_sum, e]
  obtain ⟨χ, hχ, hw⟩ : ∃ χ ∈ X, ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hu₀ne (by rw [← hsplit]; exact Finset.sum_eq_zero hcon)
  set w₀ := ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ with hw₀
  have hw₀U : w₀ ∈ U := Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hmem g _ hu₀)

  obtain ⟨t, ht⟩ : ∃ t, (chiIdem χ * lvlIdem P ψ).coeff t ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne χ hχ (by
      apply MonoidAlgebra.ext
      ext t
      simpa using hcon t)
  rw [coeff_chiIdem_mul_lvlIdem] at ht
  have h1 : χ 1 ≠ 0 := fun e => ht (by simp [e])
  have hc : ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹) ≠ 0 := right_ne_zero_of_mul ht
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

  set L : W → W := fun w => ∑ h : P, σ (lvlCoef P ψ h) • ρ (h : G) w with hL
  have hLU : ∀ w ∈ U, L w ∈ U := fun w hw => Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (hmem _ _ hw)
  have hLe : ∀ (p : P) w, ρ p (L w) = σ (ψ p : K) • L w := by
    intro p w
    simp only [hL, map_sum, map_smul, Finset.smul_sum]
    refine (Equiv.sum_comp (Equiv.mulLeft p⁻¹) _).symm.trans (Finset.sum_congr rfl fun h _ => ?_)
    simp only [Equiv.coe_mulLeft]
    have e1 : lvlCoef P ψ (p⁻¹ * h) = (ψ p : K) * lvlCoef P ψ h := by
      simp only [lvlCoef, _root_.mul_inv_rev, inv_inv, map_mul, Units.val_mul]
      ring
    have e2 : ρ (p : G) (ρ ((p⁻¹ * h : P) : G) w) = ρ (h : G) w := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [e1, e2, map_mul, mul_smul]
  by_contra hno
  push_neg at hno
  have hL0 : ∀ w ∈ U, L w = 0 := by
    intro w hw
    by_contra hLw
    obtain ⟨p, hp⟩ := hno _ (hLU w hw) hLw
    exact hp (hLe p w)
  have hz : ∑ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) = 0 :=
    Finset.sum_eq_zero fun g _ => by rw [hL0 _ (hmem _ _ hw₀U), map_zero]
  have hz2 : ∑ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) =
      σ ((Fintype.card G : K) / χ 1 * ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹)) • w₀ := by
    have e : ∀ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) =
        ∑ h : P, σ (lvlCoef P ψ h) • ρ (g * ((h : G) * t⁻¹) * g⁻¹) w₀ := by
      intro g
      simp only [hL, map_sum, map_smul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← Module.End.mul_apply (ρ (h : G)), ← map_mul, ← Module.End.mul_apply (ρ g), ← map_mul]
      simp [mul_assoc]
    simp only [e]
    rw [Finset.sum_comm]
    have e2 : ∀ h : P, ∑ g : G, σ (lvlCoef P ψ h) • ρ (g * ((h : G) * t⁻¹) * g⁻¹) w₀ =
        σ (lvlCoef P ψ h * ((Fintype.card G : K) * χ ((h : G) * t⁻¹) / χ 1)) • w₀ := by
      intro h
      rw [← Finset.smul_sum, map_mul, mul_smul]
      congr 1
      exact class_sum_apply σ ρ (hX χ hχ) h1 _ u₀
    simp only [e2]
    rw [← Finset.sum_smul, ← map_sum, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  rw [hz2] at hz
  rcases smul_eq_zero.1 hz with h0 | h0
  · exact (mul_ne_zero (div_ne_zero hN h1) hc) ((map_eq_zero σ).1 h0)
  · exact hw h0

end GlobalTheory.Hk3

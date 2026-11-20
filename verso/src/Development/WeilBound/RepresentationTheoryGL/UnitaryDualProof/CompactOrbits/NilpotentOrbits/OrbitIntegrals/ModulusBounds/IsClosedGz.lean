import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
import GroundTheory.AutomorphicForms.GLnLocal

noncomputable section

open Matrix Module ValuativeRel GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Establish `: (Gz Z : Set (GL (Fin n) k)) = ⋂ a ∈ Z, {g : GL (Fin n) k | a * g.val = g.val * a}`. Use extensionality with `g`. Simplify using `[Gz]`. Rewrite using `[this]`. Conclude with `isClosed_biInter fun a _ => isClosed_eq (continuous_const.matrix_mul Units.continuous_val) (Units.continuous_val.matrix_mul continuous_const)`.
-/
theorem isClosed_Gz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (Gz Z : Set (GL (Fin n) k)) := by
  have : (Gz Z : Set (GL (Fin n) k)) = ⋂ a ∈ Z, {g : GL (Fin n) k | a * g.val = g.val * a} := by
    ext g; simp [Gz]
  rw [this]
  exact isClosed_biInter fun a _ => isClosed_eq (continuous_const.matrix_mul Units.continuous_val)
    (Units.continuous_val.matrix_mul continuous_const)

/- English proof (translation)
Distinguish the cases in `ha : valuation k a ≤ 1`. Conclude with `⟨0, by rw [pow_zero, one_mul]; exact ha⟩`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `ha (by rw [map_zero]; exact zero_le')`.

Establish `hinv : valuation k a⁻¹ ≤ 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ (le_of_lt (not_le.mp ha))`. Use `set b : 𝒪[k] := ⟨a⁻¹, hinv⟩ with hb`. Establish `hb0 : b ≠ 0`.

Introduce `h`. Establish `h' : (b : k) = 0` using `by rw [h]; rfl`. Conclude with `inv_ne_zero ha0 h'`. Establish `hirr : Irreducible (GroundTheory.Automorphic.GLnLocal.uniformizer k)`. Rewrite using `[IsDiscreteValuationRing.irreducible_iff_uniformizer]`.

Establish `h` using `maximalIdeal_pow_eq k 1`. Rewrite `h` using `[pow_one, pow_one]`. Conclude with `h`. Take `⟨e, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hb0 hirr`. Use `⟨e, ?_⟩` and prove the remaining obligations.

Establish `h1 : valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ e ≤ valuation k a⁻¹`. Establish `h2 : (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ e = a⁻¹ * ((u : 𝒪[k]) : k)`. Establish `h3` using `congrArg (fun z : 𝒪[k] => (z : k)) hu`. Simplify `h3.symm` using `[hb]`. Rewrite using `[← map_pow, h2, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem exists_uniformizer_pow_mul_valuation_le_one (a : k) : ∃ e : ℕ,
    valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ e * valuation k a ≤ 1 := by
  by_cases ha : valuation k a ≤ 1
  · exact ⟨0, by rw [pow_zero, one_mul]; exact ha⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (by rw [map_zero]; exact zero_le')
  have hinv : valuation k a⁻¹ ≤ 1 := by
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp ha))
  set b : 𝒪[k] := ⟨a⁻¹, hinv⟩ with hb
  have hb0 : b ≠ 0 := by
    intro h
    have h' : (b : k) = 0 := by rw [h]; rfl
    exact inv_ne_zero ha0 h'
  have hirr : Irreducible (GroundTheory.Automorphic.GLnLocal.uniformizer k) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    have h := maximalIdeal_pow_eq k 1
    rw [pow_one, pow_one] at h
    exact h
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hirr
  refine ⟨e, ?_⟩
  have h1 : valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ e ≤ valuation k a⁻¹ := by
    have h2 : (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ e = a⁻¹ * ((u : 𝒪[k]) : k) := by
      have h3 := congrArg (fun z : 𝒪[k] => (z : k)) hu
      simpa [hb] using h3.symm
    rw [← map_pow, h2, map_mul]
    calc _ ≤ valuation k a⁻¹ * 1 := mul_le_mul_right (u : 𝒪[k]).2 _
      _ = _ := mul_one _
  calc _ ≤ valuation k a⁻¹ * valuation k a := mul_le_mul_left h1 _
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ ha0, map_one]

/- English proof (translation)
Use `set c := valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E with hc`. Rewrite using `[Matrix.mul_apply]`. Use `sum_mem fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`. Use `sum_mem fun a _ => ?_` and prove the remaining obligations.

Use `show valuation k (P i a * y a b * Q b j) ≤ 1`. Rewrite using `[map_mul, map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mul_mul_apply_mem_integers_of_valuation_bounds (E : ℕ) (P Q y : Matrix (Fin n) (Fin n) k)
    (hP : ∀ i j, valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E * valuation k (P i j) ≤ 1)
    (hQ : ∀ i j, valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E * valuation k (Q i j) ≤ 1)
    (hy : ∀ i j, valuation k (y i j) ≤ valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E *
      valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E)
    (i j : Fin n) : (P * y * Q) i j ∈ 𝒪[k] := by
  set c := valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E with hc
  rw [Matrix.mul_apply]
  refine sum_mem fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine sum_mem fun a _ => ?_
  show valuation k (P i a * y a b * Q b j) ≤ 1
  rw [map_mul, map_mul]
  calc valuation k (P i a) * valuation k (y a b) * valuation k (Q b j)
      ≤ valuation k (P i a) * (c * c) * valuation k (Q b j) :=
        mul_le_mul_left (mul_le_mul_right (hy a b) _) _
    _ = (c * valuation k (P i a)) * (c * valuation k (Q b j)) := by ac_rfl
    _ ≤ 1 * 1 := mul_le_mul' (hP i a) (hQ b j)
    _ = 1 := one_mul 1

/- English proof (translation)
Use `choose e he using fun a : k => exists_uniformizer_pow_mul_valuation_le_one (k := k) a`. Use `set A : Matrix (Fin n) (Fin n) k := (g : Matrix (Fin n) (Fin n) k) with hA`. Use `set B : Matrix (Fin n) (Fin n) k := ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hB`. Use `set E : ℕ := ∑ i, ∑ j, (e (A i j) + e (B i j)) with hE`. Establish `hπ1 : valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ≤ 1` using `(GroundTheory.Automorphic.GLnLocal.uniformizer k).2`.

Establish `hbound : ∀ a : k, e a ≤ E → valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E * valuation k a ≤ 1`. Introduce `a ha`. Conclude with `le_trans (mul_le_mul_left (pow_le_pow_right_of_le_one' hπ1 ha) _) (he a)`. Establish `hrow : ∀ i j, e (A i j) + e (B i j) ≤ E`. Introduce `i j`.

Combine the equalities or inequalities in the displayed calculation. Establish `heA : ∀ i j, e (A i j) ≤ E` using `fun i j => le_trans (Nat.le_add_right _ _) (hrow i j)`. Establish `heB : ∀ i j, e (B i j) ≤ E` using `fun i j => le_trans (Nat.le_add_left _ _) (hrow i j)`. Establish `hBA : B * A = 1` using `Units.inv_mul g`. Establish `hAB : A * B = 1` using `Units.mul_inv g`.

Establish `h1 : ∀ i j, (1 : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k]`. Introduce `i j`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Use `⟨2 * E + 1, by omega, ?_⟩` and prove the remaining obligations. Establish `hconj : ∀ w ∈ congruenceSubgroup k n (2 * E + 1), ∀ i j, ((g⁻¹ * w * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] ∧ ((g * w * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k]`. Introduce `w hw i j`. Rewrite `hw` using `[mem_congruenceSubgroup_iff]`.

Use `set y : Matrix (Fin n) (Fin n) k := (w : Matrix (Fin n) (Fin n) k) - 1 with hy`. Establish `hw' : (w : Matrix (Fin n) (Fin n) k) = 1 + y` using `by rw [hy]; abel`. Establish `hyb : ∀ a b, valuation k (y a b) ≤ valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E * valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E`. Introduce `a b`. Rewrite using `[← pow_add]`.

Conclude with `le_trans (hw.2 a b) (pow_le_pow_right_of_le_one' hπ1 (by omega))`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Units.val_mul, Units.val_mul, ← hB, ← hA, hw', Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBA, Matrix.add_apply]`. Conclude with `add_mem (h1 i j) (mul_mul_apply_mem_integers_of_valuation_bounds E B A y (fun i j => hbound _ (heB i j)) (fun i j => hbound _ (heA i j)) hyb i j)`. Rewrite using `[Units.val_mul, Units.val_mul, ← hB, ← hA, hw', Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAB, Matrix.add_apply]`.

Conclude with `add_mem (h1 i j) (mul_mul_apply_mem_integers_of_valuation_bounds E A B y (fun i j => hbound _ (heA i j)) (fun i j => hbound _ (heB i j)) hyb i j)`. Introduce `u hu`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_integralGL_iff]`. Use `⟨fun i j => (hconj u hu i j).1, fun i j => ?_⟩` and prove the remaining obligations.

Establish `hinv : (g⁻¹ * u * g)⁻¹ = g⁻¹ * u⁻¹ * g` using `by group`. Rewrite using `[hinv]`. Conclude with `(hconj u⁻¹ (inv_mem hu) i j).1`. Rewrite using `[mem_integralGL_iff]`. Use `⟨fun i j => (hconj u hu i j).2, fun i j => ?_⟩` and prove the remaining obligations.

Establish `hinv : (g * u * g⁻¹)⁻¹ = g * u⁻¹ * g⁻¹` using `by group`. Rewrite using `[hinv]`. Conclude with `(hconj u⁻¹ (inv_mem hu) i j).2`.
-/
theorem exists_level (g : GL (Fin n) k) : ∃ m : ℕ, 1 ≤ m ∧ ∀ u ∈ congruenceSubgroup k n m,
    g⁻¹ * u * g ∈ integralGL k n ∧ g * u * g⁻¹ ∈ integralGL k n := by
  classical
  choose e he using fun a : k => exists_uniformizer_pow_mul_valuation_le_one (k := k) a
  set A : Matrix (Fin n) (Fin n) k := (g : Matrix (Fin n) (Fin n) k) with hA
  set B : Matrix (Fin n) (Fin n) k := ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hB
  set E : ℕ := ∑ i, ∑ j, (e (A i j) + e (B i j)) with hE
  have hπ1 : valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ≤ 1 :=
    (GroundTheory.Automorphic.GLnLocal.uniformizer k).2
  have hbound : ∀ a : k, e a ≤ E →
      valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E * valuation k a ≤ 1 := by
    intro a ha
    exact le_trans (mul_le_mul_left (pow_le_pow_right_of_le_one' hπ1 ha) _) (he a)
  have hrow : ∀ i j, e (A i j) + e (B i j) ≤ E := by
    intro i j
    calc e (A i j) + e (B i j) ≤ ∑ j', (e (A i j') + e (B i j')) :=
          Finset.single_le_sum (f := fun j' => e (A i j') + e (B i j'))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ ≤ E := Finset.single_le_sum (f := fun i' => ∑ j', (e (A i' j') + e (B i' j')))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have heA : ∀ i j, e (A i j) ≤ E := fun i j => le_trans (Nat.le_add_right _ _) (hrow i j)
  have heB : ∀ i j, e (B i j) ≤ E := fun i j => le_trans (Nat.le_add_left _ _) (hrow i j)
  have hBA : B * A = 1 := Units.inv_mul g
  have hAB : A * B = 1 := Units.mul_inv g
  have h1 : ∀ i j, (1 : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨2 * E + 1, by omega, ?_⟩
  have hconj : ∀ w ∈ congruenceSubgroup k n (2 * E + 1), ∀ i j,
      ((g⁻¹ * w * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] ∧
      ((g * w * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    intro w hw i j
    rw [mem_congruenceSubgroup_iff] at hw
    set y : Matrix (Fin n) (Fin n) k := (w : Matrix (Fin n) (Fin n) k) - 1 with hy
    have hw' : (w : Matrix (Fin n) (Fin n) k) = 1 + y := by rw [hy]; abel
    have hyb : ∀ a b, valuation k (y a b) ≤
        valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E *
          valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ^ E := by
      intro a b
      rw [← pow_add]
      exact le_trans (hw.2 a b) (pow_le_pow_right_of_le_one' hπ1 (by omega))
    constructor
    · rw [Units.val_mul, Units.val_mul, ← hB, ← hA, hw', Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, hBA, Matrix.add_apply]
      exact add_mem (h1 i j) (mul_mul_apply_mem_integers_of_valuation_bounds E B A y (fun i j => hbound _ (heB i j))
        (fun i j => hbound _ (heA i j)) hyb i j)
    · rw [Units.val_mul, Units.val_mul, ← hB, ← hA, hw', Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, hAB, Matrix.add_apply]
      exact add_mem (h1 i j) (mul_mul_apply_mem_integers_of_valuation_bounds E A B y (fun i j => hbound _ (heA i j))
        (fun i j => hbound _ (heB i j)) hyb i j)
  intro u hu
  refine ⟨?_, ?_⟩
  · rw [mem_integralGL_iff]
    refine ⟨fun i j => (hconj u hu i j).1, fun i j => ?_⟩
    have hinv : (g⁻¹ * u * g)⁻¹ = g⁻¹ * u⁻¹ * g := by group
    rw [hinv]
    exact (hconj u⁻¹ (inv_mem hu) i j).1
  · rw [mem_integralGL_iff]
    refine ⟨fun i j => (hconj u hu i j).2, fun i j => ?_⟩
    have hinv : (g * u * g⁻¹)⁻¹ = g * u⁻¹ * g⁻¹ := by group
    rw [hinv]
    exact (hconj u⁻¹ (inv_mem hu) i j).2

/- English proof (translation)
Use `set π := GroundTheory.Automorphic.GLnLocal.uniformizer k with hπ`. Establish `hπm : π ∈ 𝓂[k]`. Establish `h` using `maximalIdeal_pow_eq k 1`. Rewrite `h` using `[pow_one, pow_one]`. Rewrite using `[h]`.

Conclude with `Ideal.subset_span rfl`. Establish `hπ1 : valuation k (π : k) < 1`. Rewrite `hπm` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hπm`. Establish `hle : ∀ i j, valuation k (x i j) < 1` using `fun i j => lt_of_le_of_lt (hx i j) (pow_lt_one₀ zero_le' hπ1 (by omega))`.

Set `X : Matrix (Fin n) (Fin n) 𝒪[k]` to `fun i j => ⟨x i j, (hle i j).le⟩`. Establish `hXm : ∀ i j, X i j ∈ 𝓂[k]` using `fun i j => by`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr (hle i j)`. Establish `hdet : IsUnit (1 + X).det`.

Establish `h1 : (IsLocalRing.residue 𝒪[k]) (1 + X).det = 1`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h0 : X.map (IsLocalRing.residue 𝒪[k]) = 0`. Use extensionality with `i j`. Simplify `hXm i j` using `[IsLocalRing.residue_eq_zero_iff]`.

Rewrite using `[h0, add_zero, Matrix.det_one]`. Assume the negation of the conclusion as `h`. Establish `hm : (1 + X).det ∈ IsLocalRing.maximalIdeal 𝒪[k]` using `h`. Rewrite `hm` using `[← IsLocalRing.residue_eq_zero_iff]`. Rewrite `h1` using `[hm]`.

Conclude with `zero_ne_one h1`. Establish `hU : IsUnit (1 + X)` using `(Matrix.isUnit_iff_isUnit_det _).mpr hdet`. Apply the tactic sequence `have hentry : ∀ i j, (((1 + X) i j : 𝒪[k]) : k) = (1 : Matrix (Fin n) (Fin n) k) i j + x i j := by`. Introduce `i j`. Use `show (((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j : 𝒪[k]) : k) + x i j = _`.

Use `congr 1`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use `⟨integralGLHom k n hU.unit, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_congruenceSubgroup_iff]`.

Use `⟨⟨hU.unit, rfl⟩, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[integralGLHom_apply, IsUnit.unit_spec, hentry, add_sub_cancel_left]`. Conclude with `hx i j`. Use extensionality with `i j`. Rewrite using `[integralGLHom_apply, IsUnit.unit_spec, hentry, Matrix.add_apply]`.
-/
theorem exists_unit (m : ℕ) (hm : 1 ≤ m) (x : Matrix (Fin n) (Fin n) k)
    (hx : ∀ i j, valuation k (x i j) ≤ valuation k (uniformizer k : k) ^ m) :
    ∃ u ∈ congruenceSubgroup k n m, u.val = 1 + x := by
  classical
  set π := GroundTheory.Automorphic.GLnLocal.uniformizer k with hπ
  have hπm : π ∈ 𝓂[k] := by
    have h := maximalIdeal_pow_eq k 1
    rw [pow_one, pow_one] at h
    rw [h]
    exact Ideal.subset_span rfl
  have hπ1 : valuation k (π : k) < 1 := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hπm
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hπm
  have hle : ∀ i j, valuation k (x i j) < 1 := fun i j =>
    lt_of_le_of_lt (hx i j) (pow_lt_one₀ zero_le' hπ1 (by omega))
  let X : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨x i j, (hle i j).le⟩
  have hXm : ∀ i j, X i j ∈ 𝓂[k] := fun i j => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr (hle i j)
  have hdet : IsUnit (1 + X).det := by
    have h1 : (IsLocalRing.residue 𝒪[k]) (1 + X).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add _),
        Matrix.map_one _ (map_zero _) (map_one _)]
      have h0 : X.map (IsLocalRing.residue 𝒪[k]) = 0 := by
        ext i j
        simpa [IsLocalRing.residue_eq_zero_iff] using hXm i j
      rw [h0, add_zero, Matrix.det_one]
    by_contra h
    have hm : (1 + X).det ∈ IsLocalRing.maximalIdeal 𝒪[k] := h
    rw [← IsLocalRing.residue_eq_zero_iff] at hm
    rw [hm] at h1
    exact zero_ne_one h1
  have hU : IsUnit (1 + X) := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hentry : ∀ i j, (((1 + X) i j : 𝒪[k]) : k) = (1 : Matrix (Fin n) (Fin n) k) i j + x i j := by
    intro i j
    show (((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j : 𝒪[k]) : k) + x i j = _
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨integralGLHom k n hU.unit, ?_, ?_⟩
  · rw [mem_congruenceSubgroup_iff]
    refine ⟨⟨hU.unit, rfl⟩, fun i j => ?_⟩
    rw [integralGLHom_apply, IsUnit.unit_spec, hentry, add_sub_cancel_left]
    exact hx i j
  · ext i j
    rw [integralGLHom_apply, IsUnit.unit_spec, hentry, Matrix.add_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BModbound

import Mathlib
import GroundTheory.FunctionField.PlaceDefs
import GroundTheory.FunctionField.PlaceBasic
import GroundTheory.FunctionField.Approximation
import GroundTheory.FunctionField.Divisor
import GroundTheory.FunctionField.DivisorDegree
import GroundTheory.FunctionField.Repartition
import GroundTheory.FunctionField.ExistsBoundDegSubFinrankL

namespace GroundTheory.FunctionField

open Module Repartition

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

namespace Divisor

/- English proof (translation)
Introduce `v`. Rewrite using `[Repartition.mul_apply, map_mul, v.valuation_eq_exp_neg_ord hx]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← WithZero.exp_add, Finsupp.coe_sub, Pi.sub_apply, divisor_apply]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_mem_A {x : K} (hx : x ≠ 0) {E : Divisor k K} {a : Repartition k K} (ha : a ∈ A E) :
    Repartition.mul x a ∈ A (E - divisor x) := by
  intro v
  rw [Repartition.mul_apply, map_mul, v.valuation_eq_exp_neg_ord hx]
  calc WithZero.exp (-v.ord x) * v.valuation (a v)
      ≤ WithZero.exp (-v.ord x) * WithZero.exp (E v) := mul_le_mul' le_rfl (ha v)
    _ = WithZero.exp ((E - divisor x : Divisor k K) v) := by
      rw [← WithZero.exp_add, Finsupp.coe_sub, Pi.sub_apply, divisor_apply]
      congr 1
      ring

/- English proof (translation)
Introduce `a ha`. Set `f : Place k K → K` to `fun v => if E v ≤ D v then a v else 0`. Establish `hf : {v : Place k K | f v ∉ v.ring}.Finite` using `a.finite_not_mem.subset fun v (hv : f v ∉ v.ring) => by show a v ∉ v.ring`. Introduce `h`. Apply `hv` to reduce the goal to its premises.

Simplify using `only [f]`. Use `split_ifs`. Conclude with `h`. Conclude with `v.ring.zero_mem`. Set `b` to `Repartition.mk f hf`.

Establish `hb : b ∈ A D`. Introduce `v`. Express the relevant statement in the definitionally equal form `v.valuation (f v) ≤ _`. Simplify using `only [f]`. Use `split_ifs with h`.

Use `ha v` as an intermediate fact. Rewrite `this` using `[Finsupp.sup_apply, sup_of_le_left h]`. Then use the resulting hypothesis. Rewrite using `[map_zero]`. Conclude with `zero_le`. Establish `hc : a - b ∈ A E`.

Introduce `v`. Rewrite using `[Repartition.sub_apply]`. Express the relevant statement in the definitionally equal form `v.valuation (a v - f v) ≤ _`. Simplify using `only [f]`. Use `split_ifs with h`.

Rewrite using `[sub_self, map_zero]`. Conclude with `zero_le`. Rewrite using `[sub_zero]`. Use `ha v` as an intermediate fact. Rewrite `this` using `[Finsupp.sup_apply, sup_of_le_right (not_le.1 h).le]`. Then use the resulting hypothesis.

Establish `: a = b + (a - b)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup hb hc`.
-/
theorem A_sup_le (D E : Divisor k K) : A (D ⊔ E) ≤ A D ⊔ A E := by
  classical
  intro a ha
  let f : Place k K → K := fun v => if E v ≤ D v then a v else 0
  have hf : {v : Place k K | f v ∉ v.ring}.Finite :=
    a.finite_not_mem.subset fun v (hv : f v ∉ v.ring) => by
      show a v ∉ v.ring
      intro h
      apply hv
      simp only [f]
      split_ifs
      · exact h
      · exact v.ring.zero_mem
  let b := Repartition.mk f hf
  have hb : b ∈ A D := by
    intro v
    change v.valuation (f v) ≤ _
    simp only [f]
    split_ifs with h
    · have := ha v
      rwa [Finsupp.sup_apply, sup_of_le_left h] at this
    · rw [map_zero]; exact zero_le
  have hc : a - b ∈ A E := by
    intro v
    rw [Repartition.sub_apply]
    change v.valuation (a v - f v) ≤ _
    simp only [f]
    split_ifs with h
    · rw [sub_self, map_zero]; exact zero_le
    · rw [sub_zero]
      have := ha v
      rwa [Finsupp.sup_apply, sup_of_le_right (not_le.1 h).le] at this
  have : a = b + (a - b) := by abel
  rw [this]
  exact Submodule.add_mem_sup hb hc

noncomputable def weilSpace (D : Divisor k K) : Submodule k (Module.Dual k (Repartition k K)) :=
  (A D ⊔ principal k K).dualAnnihilator

/- English proof (translation)
Rewrite using `[weilSpace, Submodule.mem_dualAnnihilator]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨fun a ha => h a (Submodule.mem_sup_left ha), fun x => h _ (Submodule.mem_sup_right (diag_mem_principal x))⟩`. Introduce and unpack `⟨h1, h2⟩ a ha`.

Take `⟨b, hb, c, ⟨x, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 ha`. Rewrite using `[map_add, h1 b hb, h2 x, add_zero]`.
-/
theorem mem_weilSpace {D : Divisor k K} {ω : Module.Dual k (Repartition k K)} :
    ω ∈ weilSpace D ↔ (∀ a ∈ A D, ω a = 0) ∧ ∀ x : K, ω (diag x) = 0 := by
  rw [weilSpace, Submodule.mem_dualAnnihilator]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Submodule.mem_sup_left ha),
      fun x => h _ (Submodule.mem_sup_right (diag_mem_principal x))⟩
  · rintro ⟨h1, h2⟩ a ha
    obtain ⟨b, hb, c, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ha
    rw [map_add, h1 b hb, h2 x, add_zero]

/- English proof (translation)
The claim follows from `Submodule.dualAnnihilator_anti (sup_le_sup_right (A_mono h) _)`.
-/
theorem weilSpace_anti {D E : Divisor k K} (h : D ≤ E) : weilSpace E ≤ weilSpace D :=
  Submodule.dualAnnihilator_anti (sup_le_sup_right (A_mono h) _)

/- English proof (translation)
Rewrite `hD`, `hE`, the goal using `[mem_weilSpace]`. Use `⟨fun a ha => ?_, hD.2⟩` and prove the remaining obligations. Take `⟨b, hb, c, hc, rfl⟩` from `Submodule.mem_sup.1 (A_sup_le D E ha)`. Rewrite using `[map_add, hD.1 b hb, hE.1 c hc, add_zero]`.
-/
theorem weilSpace_sup {D E : Divisor k K} {ω : Module.Dual k (Repartition k K)}
    (hD : ω ∈ weilSpace D) (hE : ω ∈ weilSpace E) : ω ∈ weilSpace (D ⊔ E) := by
  rw [mem_weilSpace] at hD hE ⊢
  refine ⟨fun a ha => ?_, hD.2⟩
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 (A_sup_le D E ha)
  rw [map_add, hD.1 b hb, hE.1 c hc, add_zero]

instance (D : Divisor k K) : FiniteDimensional k (weilSpace D) :=
  Module.Finite.equiv (Submodule.dualQuotEquivDualAnnihilator (A D ⊔ principal k K))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `finrank k (A D ⊔ principal k K).dualAnnihilator = _`. Rewrite using `[indexOfSpeciality, ← (Submodule.dualQuotEquivDualAnnihilator (A D ⊔ principal k K)).finrank_eq, Subspace.dual_finrank_eq]`.
-/
theorem finrank_weilSpace (D : Divisor k K) : finrank k (weilSpace D) = indexOfSpeciality D := by
  change finrank k (A D ⊔ principal k K).dualAnnihilator = _
  rw [indexOfSpeciality,
    ← (Submodule.dualQuotEquivDualAnnihilator (A D ⊔ principal k K)).finrank_eq,
    Subspace.dual_finrank_eq]

/- English proof (translation)
Take `⟨E₀, hE₀⟩` from `exists_eq_genusInt (k := k) (K := K)`. Use `⟨deg E₀ + genusInt k K, fun D hD => ?_⟩` and prove the remaining obligations. Establish `h1` using `le_genusInt (D - E₀)`. Rewrite `h1` using `[map_sub]`. Establish `hpos : 0 < finrank k (L (D - E₀))`.

Establish `: (0 : ℤ) < finrank k (L (D - E₀))` using `by linarith`. Conclude with `this` after adjusting the coercions. Take `⟨z, hz⟩` from `finrank_pos_iff_exists_ne_zero.1 hpos`. Establish `hz0 : (z : K) ≠ 0` using `fun h => hz (Subtype.ext h)`. Establish `hzL` using `(mem_L_iff_le hz0).1 z.2`.

Establish `hle : E₀ ≤ D + divisor (z : K)`. Rewrite using `[← sub_nonneg]`. Use `hzL using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Establish `hD'` using `eq_genusInt_of_le hE₀ hle`.

Rewrite `hD'` using `[finrank_L_add_divisor D hz0, map_add, deg_divisor, add_zero]`. Establish `hi` using `indexOfSpeciality_eq_genusInt D`. Establish `: (indexOfSpeciality D : ℤ) = 0` using `by linarith`. Conclude with `this` after adjusting the coercions.
-/
theorem exists_indexOfSpeciality_eq_zero :
    ∃ c : ℤ, ∀ D : Divisor k K, c ≤ deg D → indexOfSpeciality D = 0 := by
  obtain ⟨E₀, hE₀⟩ := exists_eq_genusInt (k := k) (K := K)
  refine ⟨deg E₀ + genusInt k K, fun D hD => ?_⟩
  have h1 := le_genusInt (D - E₀)
  rw [map_sub] at h1
  have hpos : 0 < finrank k (L (D - E₀)) := by
    have : (0 : ℤ) < finrank k (L (D - E₀)) := by linarith
    exact_mod_cast this
  obtain ⟨z, hz⟩ := finrank_pos_iff_exists_ne_zero.1 hpos
  have hz0 : (z : K) ≠ 0 := fun h => hz (Subtype.ext h)
  have hzL := (mem_L_iff_le hz0).1 z.2
  have hle : E₀ ≤ D + divisor (z : K) := by
    rw [← sub_nonneg]
    convert hzL using 1
    abel
  have hD' := eq_genusInt_of_le hE₀ hle
  rw [finrank_L_add_divisor D hz0, map_add, deg_divisor, add_zero] at hD'
  have hi := indexOfSpeciality_eq_genusInt D
  have : (indexOfSpeciality D : ℤ) = 0 := by linarith
  exact_mod_cast this

/- English proof (translation)
Take `⟨P⟩` from `Place.nonempty (k := k) (K := K)`. Use `set N : ℕ := (2 - genusInt k K).toNat with hN`. Use `⟨-(N • Finsupp.single P 1), ?_⟩` and prove the remaining obligations. Establish `h` using `indexOfSpeciality_eq_genusInt (-(N • Finsupp.single P 1) : Divisor k K)`. Establish `hdeg : deg (-(N • Finsupp.single P 1) : Divisor k K) = -(N * P.deg)`.

Rewrite using `[map_neg, map_nsmul, deg_single, nsmul_eq_mul, one_mul]`. Establish `hP : (1 : ℤ) ≤ P.deg` using `by exact_mod_cast P.deg_pos`. Establish `hN' : (2 : ℤ) - genusInt k K ≤ N` using `Int.self_le_toNat _`. Establish `hl : (0 : ℤ) ≤ finrank k (L (-(N • Finsupp.single P 1) : Divisor k K))` using `Nat.cast_nonneg _`. Establish `hN0 : (0 : ℤ) ≤ N` using `Nat.cast_nonneg _`.

Establish `: (1 : ℤ) ≤ indexOfSpeciality (-(N • Finsupp.single P 1) : Divisor k K)`. Rewrite using `[h, hdeg]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `this` after adjusting the coercions.
-/
theorem exists_indexOfSpeciality_pos : ∃ D : Divisor k K, 0 < indexOfSpeciality D := by
  obtain ⟨P⟩ := Place.nonempty (k := k) (K := K)
  set N : ℕ := (2 - genusInt k K).toNat with hN
  refine ⟨-(N • Finsupp.single P 1), ?_⟩
  have h := indexOfSpeciality_eq_genusInt (-(N • Finsupp.single P 1) : Divisor k K)
  have hdeg : deg (-(N • Finsupp.single P 1) : Divisor k K) = -(N * P.deg) := by
    rw [map_neg, map_nsmul, deg_single, nsmul_eq_mul, one_mul]
  have hP : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  have hN' : (2 : ℤ) - genusInt k K ≤ N := Int.self_le_toNat _
  have hl : (0 : ℤ) ≤ finrank k (L (-(N • Finsupp.single P 1) : Divisor k K)) := Nat.cast_nonneg _
  have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg _
  have : (1 : ℤ) ≤ indexOfSpeciality (-(N • Finsupp.single P 1) : Divisor k K) := by
    rw [h, hdeg]
    nlinarith
  exact_mod_cast this

end Divisor

open Divisor

variable (k K) in

def weilDifferentials : Submodule k (Module.Dual k (Repartition k K)) where
  carrier := {ω | ∃ D : Divisor k K, ω ∈ weilSpace D}
  add_mem' := by
    rintro ω₁ ω₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    exact ⟨D₁ ⊓ D₂, add_mem (weilSpace_anti inf_le_left h₁) (weilSpace_anti inf_le_right h₂)⟩
  zero_mem' := ⟨0, zero_mem _⟩
  smul_mem' := by
    rintro c ω ⟨D, h⟩
    exact ⟨D, Submodule.smul_mem _ c h⟩

variable (k K) in

def WeilDifferential : Type _ := weilDifferentials k K

namespace WeilDifferential

instance : AddCommGroup (WeilDifferential k K) :=
  inferInstanceAs (AddCommGroup (weilDifferentials k K))

instance : Module k (WeilDifferential k K) := inferInstanceAs (Module k (weilDifferentials k K))

def toDual : WeilDifferential k K →ₗ[k] Module.Dual k (Repartition k K) :=
  (weilDifferentials k K).subtype

/- English proof (translation)
The claim follows from `Subtype.val_injective`.
-/
theorem toDual_injective : Function.Injective (toDual (k := k) (K := K)) :=
  Subtype.val_injective

def mk (ω : Module.Dual k (Repartition k K)) (h : ∃ D : Divisor k K, ω ∈ weilSpace D) :
    WeilDifferential k K :=
  (⟨ω, h⟩ : weilDifferentials k K)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toDual_mk (ω : Module.Dual k (Repartition k K)) (h : ∃ D : Divisor k K, ω ∈ weilSpace D) :
    toDual (mk ω h) = ω :=
  rfl

/- English proof (translation)
The claim follows from `(show weilDifferentials k K from ω).2`.
-/
theorem exists_mem (ω : WeilDifferential k K) : ∃ D : Divisor k K, toDual ω ∈ weilSpace D :=
  (show weilDifferentials k K from ω).2

/- English proof (translation)
Take `⟨D, hD⟩` from `ω.exists_mem`. Distinguish the cases in `hx : x = 0`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `: Repartition.mul (0 : K) = (0 : Repartition k K →ₗ[k] Repartition k K)`. Use extensionality with `a v`.

Simplify using the standard rewrite rules. Rewrite using `[hx, this, LinearMap.comp_zero]`. Conclude with `zero_mem _`. Use `⟨D + divisor x, ?_⟩` and prove the remaining obligations. Rewrite `hD`, the goal using `[mem_weilSpace]`.

Use `⟨fun a ha => ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply]`. Apply `hD.1` to reduce the goal to its premises. Use `mul_mem_A hx ha` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Then use the resulting hypothesis.

Rewrite using `[LinearMap.comp_apply, Repartition.mul_diag]`. Conclude with `hD.2 _`.
-/
theorem exists_comp_mul_mem (ω : WeilDifferential k K) (x : K) :
    ∃ D : Divisor k K, toDual ω ∘ₗ Repartition.mul x ∈ weilSpace D := by
  obtain ⟨D, hD⟩ := ω.exists_mem
  by_cases hx : x = 0
  · refine ⟨0, ?_⟩
    have : Repartition.mul (0 : K) = (0 : Repartition k K →ₗ[k] Repartition k K) := by
      ext a v
      simp
    rw [hx, this, LinearMap.comp_zero]
    exact zero_mem _
  · refine ⟨D + divisor x, ?_⟩
    rw [mem_weilSpace] at hD ⊢
    refine ⟨fun a ha => ?_, fun y => ?_⟩
    · rw [LinearMap.comp_apply]
      apply hD.1
      have := mul_mem_A hx ha
      rwa [add_sub_cancel_right] at this
    · rw [LinearMap.comp_apply, Repartition.mul_diag]
      exact hD.2 _

noncomputable instance : SMul K (WeilDifferential k K) :=
  ⟨fun x ω => mk (toDual ω ∘ₗ Repartition.mul x) (exists_comp_mul_mem ω x)⟩

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toDual_smul_apply (x : K) (ω : WeilDifferential k K) (a : Repartition k K) :
    toDual (x • ω) a = toDual ω (Repartition.mul x a) :=
  rfl

/- English proof (translation)
Use extensionality with `v`. Simplify using `[add_mul]`.
-/
theorem mul_add_left (x y : K) (a : Repartition k K) :
    Repartition.mul (x + y) a = Repartition.mul x a + Repartition.mul y a := by
  ext v
  simp [add_mul]

noncomputable instance : Module K (WeilDifferential k K) :=
  Module.ofMinimalAxioms
    (fun x ω₁ ω₂ => toDual_injective <| LinearMap.ext fun a => by simp)
    (fun x y ω => toDual_injective <| LinearMap.ext fun a => by simp [mul_add_left])
    (fun x y ω => toDual_injective <| LinearMap.ext fun a => by
      simp only [toDual_smul_apply]
      rw [mul_comm x y, Repartition.mul_mul])
    (fun ω => toDual_injective <| LinearMap.ext fun a => by
      simp only [toDual_smul_apply]
      rw [Repartition.mul_one'])

/- English proof (translation)
Apply `toDual_injective` to reduce the goal to its premises. Use extensionality with `a`. Rewrite using `[toDual_smul_apply, map_smul, LinearMap.smul_apply, ← map_smul]`. Use `congr 1`. Use extensionality with `v`.

Simplify using the standard rewrite rules.
-/
theorem algebraMap_smul (c : k) (ω : WeilDifferential k K) : algebraMap k K c • ω = c • ω := by
  apply toDual_injective
  ext a
  rw [toDual_smul_apply, map_smul, LinearMap.smul_apply, ← map_smul]
  congr 1
  ext v
  simp

/- English proof (translation)
Rewrite using `[Algebra.smul_def, mul_smul, algebraMap_smul]`.
-/
theorem smul_smul_scalar (c : k) (y : K) (ω : WeilDifferential k K) :
    (c • y) • ω = c • (y • ω) := by
  rw [Algebra.smul_def, mul_smul, algebraMap_smul]

noncomputable def weilMap (ω : WeilDifferential k K) : K →ₗ[k] Module.Dual k (Repartition k K) where
  toFun y := toDual (y • ω)
  map_add' y z := by rw [add_smul, map_add]
  map_smul' c y := by rw [smul_smul_scalar, map_smul, RingHom.id_apply]

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem weilMap_apply (ω : WeilDifferential k K) (y : K) : weilMap ω y = toDual (y • ω) :=
  rfl

/- English proof (translation)
Rewrite using `[mem_weilSpace, mem_weilSpace]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun b hb => ?_, fun y => ?_⟩` and prove the remaining obligations. Establish `hb' : Repartition.mul x⁻¹ b ∈ A D`.

Use `mul_mem_A (inv_ne_zero hx) hb` as an intermediate fact. Rewrite `this` using `[divisor_inv, sub_neg_eq_add, sub_add_cancel]`. Then use the resulting hypothesis. Use `h1 _ hb'` as an intermediate fact. Rewrite `this` using `[toDual_smul_apply, ← Repartition.mul_mul, mul_inv_cancel₀ hx, Repartition.mul_one']`. Then use the resulting hypothesis. Use `h2 (x⁻¹ * y)` as an intermediate fact.

Rewrite `this` using `[toDual_smul_apply, Repartition.mul_diag, ← _root_.mul_assoc, mul_inv_cancel₀ hx, one_mul]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun a ha => ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[toDual_smul_apply]`. Conclude with `h1 _ (mul_mem_A hx ha)`.

Rewrite using `[toDual_smul_apply, Repartition.mul_diag]`. Conclude with `h2 _`.
-/
theorem smul_mem_weilSpace_iff {x : K} (hx : x ≠ 0) (ω : WeilDifferential k K) (D : Divisor k K) :
    toDual (x • ω) ∈ weilSpace D ↔ toDual ω ∈ weilSpace (D - divisor x) := by
  rw [mem_weilSpace, mem_weilSpace]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, fun y => ?_⟩
    · have hb' : Repartition.mul x⁻¹ b ∈ A D := by
        have := mul_mem_A (inv_ne_zero hx) hb
        rwa [divisor_inv, sub_neg_eq_add, sub_add_cancel] at this
      have := h1 _ hb'
      rwa [toDual_smul_apply, ← Repartition.mul_mul, mul_inv_cancel₀ hx,
        Repartition.mul_one'] at this
    · have := h2 (x⁻¹ * y)
      rwa [toDual_smul_apply, Repartition.mul_diag, ← _root_.mul_assoc, mul_inv_cancel₀ hx,
        one_mul] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun a ha => ?_, fun y => ?_⟩
    · rw [toDual_smul_apply]
      exact h1 _ (mul_mem_A hx ha)
    · rw [toDual_smul_apply, Repartition.mul_diag]
      exact h2 _

/- English proof (translation)
Take `⟨D, hD⟩` from `exists_indexOfSpeciality_pos (k := k) (K := K)`. Rewrite `hD` using `[← finrank_weilSpace]`. Establish `hne : weilSpace D ≠ ⊥`. Introduce `h`. Rewrite `hD` using `[h]`.

Simplify using `at hD`. Take `⟨φ, hφmem, hφ⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Use `⟨mk φ ⟨D, hφmem⟩, fun h => hφ ?_⟩` and prove the remaining obligations. Use `congrArg toDual h` as an intermediate fact. Rewrite `this` using `[toDual_mk, map_zero]`. Then use the resulting hypothesis.
-/
theorem exists_ne_zero : ∃ ω : WeilDifferential k K, ω ≠ 0 := by
  obtain ⟨D, hD⟩ := exists_indexOfSpeciality_pos (k := k) (K := K)
  rw [← finrank_weilSpace] at hD
  have hne : weilSpace D ≠ ⊥ := by
    intro h
    rw [h] at hD
    simp at hD
  obtain ⟨φ, hφmem, hφ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨mk φ ⟨D, hφmem⟩, fun h => hφ ?_⟩
  have := congrArg toDual h
  rwa [toDual_mk, map_zero] at this

noncomputable def toQuotDual (D : Divisor k K) :
    weilSpace D ≃ₗ[k] Module.Dual k (Repartition k K ⧸ (A D ⊔ principal k K)) :=
  (Submodule.dualQuotEquivDualAnnihilator (A D ⊔ principal k K)).symm

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨D₁, hD₁⟩` from `ω₁.exists_mem`. Take `⟨D₂, hD₂⟩` from `ω₂.exists_mem`. Take `⟨P⟩` from `Place.nonempty (k := k) (K := K)`.

Use `set s := genusInt k K with hs`. Use `set N : ℕ := (3 * s - deg D₁ - deg D₂).toNat + 1 with hN`. Use `set B : Divisor k K := N • Finsupp.single P 1 with hB`. Establish `hmem : ∀ {ω : WeilDifferential k K} {D : Divisor k K}, toDual ω ∈ weilSpace D → ∀ y ∈ L (B + D), weilMap ω y ∈ weilSpace (-B)`. Introduce `ω D hD y hy`.

Rewrite using `[weilMap_apply]`. Distinguish the cases in `hy0 : y = 0`. Rewrite using `[hy0, zero_smul, map_zero]`. Conclude with `zero_mem _`. Rewrite using `[smul_mem_weilSpace_iff hy0]`.

Use `weilSpace_anti ?_ hD` and prove the remaining obligations. Use `(mem_L_iff_le hy0).1 hy` as an intermediate fact. Rewrite using `[← sub_nonneg]`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.

Set `Φ₀ : L (B + D₁) × L (B + D₂) →ₗ[k] Module.Dual k (Repartition k K)` to `((weilMap ω₁) ∘ₗ (L (B + D₁)).subtype).coprod ((weilMap ω₂) ∘ₗ (L (B + D₂)).subtype)`. Establish `hΦ₀ : ∀ p, Φ₀ p ∈ weilSpace (-B)` using `fun p => add_mem (hmem hD₁ _ p.1.2) (hmem hD₂ _ p.2.2)`. Establish `hΦ₀inj : Function.Injective Φ₀`. Use `(injective_iff_map_eq_zero Φ₀).2 ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨y, hy⟩, ⟨z, hz⟩⟩ hp`.

Establish `hsum : y • ω₁ + z • ω₂ = 0`. Apply `toDual_injective` to reduce the goal to its premises. Rewrite using `[map_add, map_zero]`. Conclude with `hp`. Distinguish the cases in `hz0 : z = 0`.

Substitute `hz0` using the available equality. Rewrite `hsum` using `[zero_smul, add_zero, smul_eq_zero]`. Break down `hsum with rfl | h` into its components or cases. Both sides reduce to the same expression. Conclude with `absurd h h₁`.

It suffices to derive a contradiction. Apply `hcon (-(y / z))` to reduce the goal to its premises. Establish `h' : z • ω₂ = -(y • ω₁)` using `eq_neg_of_add_eq_zero_right hsum`. Establish `e : (-(y / z)) • ω₁ = z⁻¹ • (z • ω₂)`. Rewrite using `[h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]`.

Rewrite using `[e, smul_smul, inv_mul_cancel₀ hz0, one_smul]`. Set `Φ` to `(toQuotDual (-B)).toLinearMap ∘ₗ LinearMap.codRestrict (weilSpace (-B)) Φ₀ hΦ₀`. Establish `hΦ : Function.Injective Φ` using `(toQuotDual (-B)).injective.comp fun p q h => hΦ₀inj (congrArg Subtype.val h)`. Establish `hfin` using `LinearMap.finrank_le_finrank_of_injective hΦ`. Rewrite `hfin` using `[Module.finrank_prod, Subspace.dual_finrank_eq]`.

Express the relevant statement in the definitionally equal form `_ ≤ indexOfSpeciality (-B) at hfin`. Establish `hi` using `indexOfSpeciality_eq_genusInt (-B)`. Establish `hP : (1 : ℤ) ≤ P.deg` using `by exact_mod_cast P.deg_pos`. Establish `hdegB : deg B = N * P.deg` using `by rw [hB, map_nsmul, deg_single, nsmul_eq_mul, one_mul]`. Establish `hNb : 3 * s - deg D₁ - deg D₂ + 1 ≤ (N : ℤ)`.

Use `Int.self_le_toNat (3 * s - deg D₁ - deg D₂)` as an intermediate fact. Rewrite using `[hN]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN0 : (0 : ℤ) ≤ N` using `Nat.cast_nonneg _`.

Establish `hBN : (N : ℤ) ≤ deg B` using `by rw [hdegB]; nlinarith`. Establish `hl0 : finrank k (L (-B)) = 0`. Rewrite using `[L_eq_bot_of_deg_neg (by rw [map_neg]; linarith)]`. Simplify using the standard rewrite rules. Establish `h1` using `le_genusInt (B + D₁)`.

Establish `h2` using `le_genusInt (B + D₂)`. Rewrite `h1`, `h2` using `[map_add]`. Rewrite `hi` using `[hl0, map_neg]`. Establish `: ((finrank k (L (B + D₁)) + finrank k (L (B + D₂)) : ℕ) : ℤ) ≤ indexOfSpeciality (-B)` using `by exact_mod_cast hfin`. Move the coercions through the operations in `at this hi`.

Rewrite `h1`, `h2`, `hi` using `[← hs]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_smul_eq {ω₁ : WeilDifferential k K} (h₁ : ω₁ ≠ 0) (ω₂ : WeilDifferential k K) :
    ∃ x : K, x • ω₁ = ω₂ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨D₁, hD₁⟩ := ω₁.exists_mem
  obtain ⟨D₂, hD₂⟩ := ω₂.exists_mem
  obtain ⟨P⟩ := Place.nonempty (k := k) (K := K)
  set s := genusInt k K with hs
  set N : ℕ := (3 * s - deg D₁ - deg D₂).toNat + 1 with hN
  set B : Divisor k K := N • Finsupp.single P 1 with hB
  have hmem : ∀ {ω : WeilDifferential k K} {D : Divisor k K}, toDual ω ∈ weilSpace D →
      ∀ y ∈ L (B + D), weilMap ω y ∈ weilSpace (-B) := by
    intro ω D hD y hy
    rw [weilMap_apply]
    by_cases hy0 : y = 0
    · rw [hy0, zero_smul, map_zero]
      exact zero_mem _
    rw [smul_mem_weilSpace_iff hy0]
    refine weilSpace_anti ?_ hD
    have := (mem_L_iff_le hy0).1 hy
    rw [← sub_nonneg]
    convert this using 1
    abel
  let Φ₀ : L (B + D₁) × L (B + D₂) →ₗ[k] Module.Dual k (Repartition k K) :=
    ((weilMap ω₁) ∘ₗ (L (B + D₁)).subtype).coprod ((weilMap ω₂) ∘ₗ (L (B + D₂)).subtype)
  have hΦ₀ : ∀ p, Φ₀ p ∈ weilSpace (-B) := fun p =>
    add_mem (hmem hD₁ _ p.1.2) (hmem hD₂ _ p.2.2)
  have hΦ₀inj : Function.Injective Φ₀ := by
    refine (injective_iff_map_eq_zero Φ₀).2 ?_
    rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ hp
    have hsum : y • ω₁ + z • ω₂ = 0 := by
      apply toDual_injective
      rw [map_add, map_zero]
      exact hp
    by_cases hz0 : z = 0
    · subst hz0
      rw [zero_smul, add_zero, smul_eq_zero] at hsum
      rcases hsum with rfl | h
      · rfl
      · exact absurd h h₁
    · exfalso
      apply hcon (-(y / z))
      have h' : z • ω₂ = -(y • ω₁) := eq_neg_of_add_eq_zero_right hsum
      have e : (-(y / z)) • ω₁ = z⁻¹ • (z • ω₂) := by
        rw [h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      rw [e, smul_smul, inv_mul_cancel₀ hz0, one_smul]
  let Φ := (toQuotDual (-B)).toLinearMap ∘ₗ LinearMap.codRestrict (weilSpace (-B)) Φ₀ hΦ₀
  have hΦ : Function.Injective Φ :=
    (toQuotDual (-B)).injective.comp fun p q h => hΦ₀inj (congrArg Subtype.val h)
  have hfin := LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Module.finrank_prod, Subspace.dual_finrank_eq] at hfin
  change _ ≤ indexOfSpeciality (-B) at hfin
  have hi := indexOfSpeciality_eq_genusInt (-B)
  have hP : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  have hdegB : deg B = N * P.deg := by rw [hB, map_nsmul, deg_single, nsmul_eq_mul, one_mul]
  have hNb : 3 * s - deg D₁ - deg D₂ + 1 ≤ (N : ℤ) := by
    have := Int.self_le_toNat (3 * s - deg D₁ - deg D₂)
    rw [hN]
    push_cast
    linarith
  have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg _
  have hBN : (N : ℤ) ≤ deg B := by rw [hdegB]; nlinarith
  have hl0 : finrank k (L (-B)) = 0 := by
    rw [L_eq_bot_of_deg_neg (by rw [map_neg]; linarith)]
    simp
  have h1 := le_genusInt (B + D₁)
  have h2 := le_genusInt (B + D₂)
  rw [map_add] at h1 h2
  rw [hl0, map_neg] at hi
  have : ((finrank k (L (B + D₁)) + finrank k (L (B + D₂)) : ℕ) : ℤ) ≤
      indexOfSpeciality (-B) := by exact_mod_cast hfin
  push_cast at this hi
  rw [← hs] at h1 h2 hi
  linarith

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_indexOfSpeciality_eq_zero (k := k) (K := K)`. Use `⟨c, fun D hD => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hle`. Use `push Not at hle`. Establish `h0 : finrank k (Repartition k K ⧸ (A D ⊔ principal k K)) = 0` using `hc D hle`.

Establish `hsub : Subsingleton (Repartition k K ⧸ (A D ⊔ principal k K))` using `Module.finrank_zero_iff.1 h0`. Establish `h1 : toQuotDual D ⟨toDual ω, hD⟩ = 0` using `LinearMap.ext fun q => by simp [Subsingleton.elim q 0]`. Establish `h2 : (⟨toDual ω, hD⟩ : weilSpace D) = 0` using `(toQuotDual D).injective (by rw [h1, map_zero])`. Conclude with `hω (toDual_injective (by rw [map_zero]; exact congrArg Subtype.val h2))`.
-/
theorem exists_deg_lt {ω : WeilDifferential k K} (hω : ω ≠ 0) :
    ∃ c : ℤ, ∀ D : Divisor k K, toDual ω ∈ weilSpace D → deg D < c := by
  obtain ⟨c, hc⟩ := exists_indexOfSpeciality_eq_zero (k := k) (K := K)
  refine ⟨c, fun D hD => ?_⟩
  by_contra hle
  push Not at hle
  have h0 : finrank k (Repartition k K ⧸ (A D ⊔ principal k K)) = 0 := hc D hle
  have hsub : Subsingleton (Repartition k K ⧸ (A D ⊔ principal k K)) :=
    Module.finrank_zero_iff.1 h0
  have h1 : toQuotDual D ⟨toDual ω, hD⟩ = 0 :=
    LinearMap.ext fun q => by simp [Subsingleton.elim q 0]
  have h2 : (⟨toDual ω, hD⟩ : weilSpace D) = 0 :=
    (toQuotDual D).injective (by rw [h1, map_zero])
  exact hω (toDual_injective (by rw [map_zero]; exact congrArg Subtype.val h2))

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_deg_lt hω`. Take `⟨D₀, hD₀⟩` from `ω.exists_mem`. Take `⟨n, ⟨W, hW, rfl⟩, hmax⟩` from `Int.exists_greatest_of_bdd (P := fun n => ∃ D, toDual ω ∈ weilSpace D ∧ deg D = n) ⟨c, fun n ⟨D, hD, hn⟩ => hn ▸ (hc D hD).le⟩ ⟨deg D₀, D₀, hD₀, rfl⟩`. Use `⟨W, fun D => ⟨fun hD => ?_, fun h => weilSpace_anti h hW⟩⟩` and prove the remaining obligations. Establish `hsup` using `weilSpace_sup hD hW`.

Establish `h1` using `hmax _ ⟨_, hsup, rfl⟩`. Establish `h2 : 0 ≤ (D ⊔ W) - W` using `sub_nonneg.2 le_sup_right`. Establish `h3 : deg ((D ⊔ W) - W) = 0`. Use `deg_nonneg h2` as an intermediate fact. Rewrite `this`, the goal using `[map_sub]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4` using `eq_zero_of_deg_eq_zero h2 h3`. Establish `: D ⊔ W = W` using `sub_eq_zero.1 h4`. Rewrite using `[← this]`. Conclude with `le_sup_left`.
-/
theorem exists_divisor {ω : WeilDifferential k K} (hω : ω ≠ 0) :
    ∃ W : Divisor k K, ∀ D : Divisor k K, toDual ω ∈ weilSpace D ↔ D ≤ W := by
  classical
  obtain ⟨c, hc⟩ := exists_deg_lt hω
  obtain ⟨D₀, hD₀⟩ := ω.exists_mem
  obtain ⟨n, ⟨W, hW, rfl⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd (P := fun n => ∃ D, toDual ω ∈ weilSpace D ∧ deg D = n)
      ⟨c, fun n ⟨D, hD, hn⟩ => hn ▸ (hc D hD).le⟩ ⟨deg D₀, D₀, hD₀, rfl⟩
  refine ⟨W, fun D => ⟨fun hD => ?_, fun h => weilSpace_anti h hW⟩⟩
  have hsup := weilSpace_sup hD hW
  have h1 := hmax _ ⟨_, hsup, rfl⟩
  have h2 : 0 ≤ (D ⊔ W) - W := sub_nonneg.2 le_sup_right
  have h3 : deg ((D ⊔ W) - W) = 0 := by
    have := deg_nonneg h2
    rw [map_sub] at this ⊢
    linarith
  have h4 := eq_zero_of_deg_eq_zero h2 h3
  have : D ⊔ W = W := sub_eq_zero.1 h4
  rw [← this]
  exact le_sup_left

open Classical in

noncomputable def divisor (ω : WeilDifferential k K) : Divisor k K :=
  if h : ω = 0 then 0 else Classical.choose (exists_divisor h)

/- English proof (translation)
Rewrite using `[divisor, dif_neg hω]`. Conclude with `Classical.choose_spec (exists_divisor hω) D`.
-/
theorem mem_weilSpace_iff_le_divisor {ω : WeilDifferential k K} (hω : ω ≠ 0) (D : Divisor k K) :
    toDual ω ∈ weilSpace D ↔ D ≤ ω.divisor := by
  rw [divisor, dif_neg hω]
  exact Classical.choose_spec (exists_divisor hω) D

/- English proof (translation)
Distinguish the cases in `hy : y = 0`. Rewrite using `[hy, zero_smul, map_zero]`. Conclude with `⟨fun _ => zero_mem _, fun _ => zero_mem _⟩`. Rewrite using `[smul_mem_weilSpace_iff hy, mem_weilSpace_iff_le_divisor hω, mem_L_iff_le hy, ← sub_nonneg]`. Apply the tactic sequence `constructor <;> intro h <;> convert h using 1 <;> abel`.
-/
theorem smul_mem_weilSpace_iff_mem_L {ω : WeilDifferential k K} (hω : ω ≠ 0) (D : Divisor k K)
    (y : K) : toDual (y • ω) ∈ weilSpace D ↔ y ∈ L (ω.divisor - D) := by
  by_cases hy : y = 0
  · rw [hy, zero_smul, map_zero]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  rw [smul_mem_weilSpace_iff hy, mem_weilSpace_iff_le_divisor hω, mem_L_iff_le hy,
    ← sub_nonneg]
  constructor <;> intro h <;> convert h using 1 <;> abel

noncomputable def dualityEquiv {ω : WeilDifferential k K} (hω : ω ≠ 0) (D : Divisor k K) :
    L (ω.divisor - D) ≃ₗ[k] Module.Dual k (Repartition k K ⧸ (A D ⊔ principal k K)) :=
  LinearEquiv.ofBijective
    ((toQuotDual D).toLinearMap ∘ₗ LinearMap.codRestrict (weilSpace D)
      ((weilMap ω) ∘ₗ (L (ω.divisor - D)).subtype)
      (fun y => (smul_mem_weilSpace_iff_mem_L hω D y).2 y.2))
    ⟨(toQuotDual D).injective.comp fun y z h => by
        have h' : toDual ((y : K) • ω) = toDual ((z : K) • ω) := by
          have := congrArg Subtype.val h
          exact this
        exact Subtype.ext (smul_left_injective K hω (toDual_injective h')),
      fun f => by
        set φ := (toQuotDual D).symm f with hφ
        obtain ⟨y, hy⟩ := exists_smul_eq hω (mk (φ : Module.Dual k (Repartition k K)) ⟨D, φ.2⟩)
        have hyD : toDual (y • ω) = φ := by rw [hy, toDual_mk]
        have hyL : y ∈ L (ω.divisor - D) :=
          (smul_mem_weilSpace_iff_mem_L hω D y).1 (hyD ▸ φ.2)
        refine ⟨⟨y, hyL⟩, ?_⟩
        have : LinearMap.codRestrict (weilSpace D) ((weilMap ω) ∘ₗ (L (ω.divisor - D)).subtype)
            (fun y => (smul_mem_weilSpace_iff_mem_L hω D y).2 y.2) ⟨y, hyL⟩ = φ :=
          Subtype.ext hyD
        rw [LinearMap.comp_apply, this, hφ, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]⟩

end WeilDifferential

end GroundTheory.FunctionField

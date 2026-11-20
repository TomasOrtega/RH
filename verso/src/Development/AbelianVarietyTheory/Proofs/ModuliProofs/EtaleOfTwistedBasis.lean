import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme

namespace GlobalTheory.CocycleSplit

section SquareZero

variable {B : Type} [CommRing B] {I : Ideal B}

/- English proof (translation)
Establish `h : s * t ∈ I ^ 2`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul hs ht`. Rewrite `h` using `[hI]`. Conclude with `(Submodule.mem_bot B).1 h`.
-/
private lemma mul_eq_zero_of_mem_of_sq_eq_bot (hI : I ^ 2 = ⊥) {s t : B} (hs : s ∈ I) (ht : t ∈ I) :
    s * t = 0 := by
  have h : s * t ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hs ht
  rw [hI] at h
  exact (Submodule.mem_bot B).1 h

/- English proof (translation)
Establish `hsq : (u - 1) * (u - 1) = 0` using `mul_eq_zero_of_mem_of_sq_eq_bot hI hu hu`. Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, ih]`.

Use `push_cast`. Take the linear combination `(↑n : B) * hsq`.
-/
theorem pow_eq_of_sub_one_mem (hI : I ^ 2 = ⊥) {u : B} (hu : u - 1 ∈ I) (N : ℕ) :
    u ^ N = 1 + N * (u - 1) := by
  have hsq : (u - 1) * (u - 1) = 0 := mul_eq_zero_of_mem_of_sq_eq_bot hI hu hu
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (↑n : B) * hsq

/- English proof (translation)
Rewrite `h` using `[pow_eq_of_sub_one_mem hI hu N, pow_eq_of_sub_one_mem hI hv N]`. Establish `h3 : (N : B) * (u - 1) = N * (v - 1)` using `add_left_cancel h`. Establish `h4` using `hN.mul_left_cancel h3`. Take the linear combination `h4`.
-/
theorem eq_of_pow_eq (hI : I ^ 2 = ⊥) {N : ℕ} (hN : IsUnit (N : B)) {u v : B} (hu : u - 1 ∈ I)
    (hv : v - 1 ∈ I) (h : u ^ N = v ^ N) : u = v := by
  rw [pow_eq_of_sub_one_mem hI hu N, pow_eq_of_sub_one_mem hI hv N] at h
  have h3 : (N : B) * (u - 1) = N * (v - 1) := add_left_cancel h
  have h4 := hN.mul_left_cancel h3
  linear_combination h4

/- English proof (translation)
Take `⟨v, hv⟩` from `h.exists_right_inv`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective v`. Establish `hm : a * w - 1 ∈ I` using `Ideal.Quotient.eq.1 (by rw [map_mul, map_one]; exact hv)`. Establish `hsq : (a * w - 1) * (a * w - 1) = 0` using `mul_eq_zero_of_mem_of_sq_eq_bot hI hm hm`. Establish `h : a * (w * (2 - a * w)) = 1` using `by linear_combination (-1 : B) * hsq`.

Conclude with `⟨⟨a, w * (2 - a * w), h, by rw [mul_comm]; exact h⟩, rfl⟩`.
-/
private lemma isUnit_of_isUnit_quotient_of_sq_eq_bot (hI : I ^ 2 = ⊥) {a : B} (h : IsUnit (Ideal.Quotient.mk I a)) :
    IsUnit a := by
  obtain ⟨v, hv⟩ := h.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hm : a * w - 1 ∈ I := Ideal.Quotient.eq.1 (by rw [map_mul, map_one]; exact hv)
  have hsq : (a * w - 1) * (a * w - 1) = 0 := mul_eq_zero_of_mem_of_sq_eq_bot hI hm hm
  have h : a * (w * (2 - a * w)) = 1 := by linear_combination (-1 : B) * hsq
  exact ⟨⟨a, w * (2 - a * w), h, by rw [mul_comm]; exact h⟩, rfl⟩

/- English proof (translation)
Use `Fintype.ofFinite C` as an intermediate fact. Rewrite `hN` using `[Nat.card_eq_fintype_card]`. Use `choose a₀ ha₀ using fun x => Ideal.Quotient.mk_surjective (b x)`. Establish `hu : ∀ x, IsUnit (a₀ x)` using `fun x => isUnit_of_isUnit_quotient_of_sq_eq_bot hI (by rw [ha₀]; exact hb x)`. Use `set δ : C → C → B := fun x y => ((c x y : B) * a₀ (x * y) - a₀ x * a₀ y) * ↑(hu x).unit⁻¹ * ↑(hu y).unit⁻¹ with hδeq`.

Establish `hδI : ∀ x y, δ x y ∈ I`. Introduce `x y`. Use `I.mul_mem_right _ (I.mul_mem_right _ (Ideal.Quotient.eq.1 ?_))` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ha₀, ha₀, ha₀]`. Conclude with `hbc x y`.

Establish `hδ : ∀ x y, (c x y : B) * a₀ (x * y) = a₀ x * a₀ y + a₀ x * a₀ y * δ x y`. Introduce `x y`. Establish `h1` using `(hu x).mul_val_inv`. Establish `h2` using `(hu y).mul_val_inv`. Simplify using `only [hδeq]`.

Take the linear combination `(-((c x y : B) * a₀ (x * y) - a₀ x * a₀ y) * (a₀ y * ↑(hu y).unit⁻¹)) * h1 - ((c x y : B) * a₀ (x * y) - a₀ x * a₀ y) * h2`. Establish `hco : ∀ x y z, δ x y + δ (x * y) z = δ y z + δ x (y * z)`. Introduce `x y z`. Establish `hP : IsUnit (a₀ x * a₀ y * a₀ z)` using `((hu x).mul (hu y)).mul (hu z)`. Establish `E : (c x y : B) * c (x * y) z = c y z * c x (y * z)`.

Use `congrArg (fun t : Bˣ => (t : B)) (hc x y z)` as an intermediate fact. Simplify using `using this`. Establish `h12` using `mul_eq_zero_of_mem_of_sq_eq_bot hI (hδI x y) (hδI (x * y) z)`. Establish `h34` using `mul_eq_zero_of_mem_of_sq_eq_bot hI (hδI y z) (hδI x (y * z))`. Establish `A` using `hδ x y`.

Establish `Bq` using `hδ (x * y) z`. Establish `Cq` using `hδ y z`. Establish `D` using `hδ x (y * z)`. Rewrite `Bq` using `[mul_assoc x y z]`. Establish `key : a₀ x * a₀ y * a₀ z * (δ x y + δ (x * y) z - (δ y z + δ x (y * z))) = 0`.

Take the linear combination `a₀ (x * (y * z)) * E - (c x y : B) * Bq - a₀ z * (1 + δ (x * y) z) * A + (c y z : B) * D + a₀ x * (1 + δ x (y * z)) * Cq - a₀ x * a₀ y * a₀ z * h12 + a₀ x * a₀ y * a₀ z * h34`. Rewrite `key` using `[hP.mul_right_eq_zero, sub_eq_zero]`. Conclude with `key`. Use `set F : C → B := fun x => ∑ z, δ x z with hFeq`. Establish `hF : ∀ x y, (Fintype.card C : B) * δ x y + F (x * y) = F y + F x`.

Introduce `x y`. Establish `hs` using `Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) => hco x y z)`. Rewrite `hs` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `hre : ∑ z, δ x (y * z) = ∑ z, δ x z` using `Fintype.sum_equiv (Equiv.mulLeft y) _ _ (fun z => rfl)`. Rewrite `hs` using `[hre]`.

Simplify `hs` using `[hFeq]`. Use `set ν : B := ↑hN.unit⁻¹ with hνeq`. Establish `hνN : ν * (Fintype.card C : B) = 1` using `hN.val_inv_mul`. Use `set η : C → B := fun x => ν * F x with hηeq`. Establish `hηI : ∀ x, η x ∈ I` using `fun x => I.mul_mem_left _ (I.sum_mem fun z _ => hδI x z)`.

Establish `hsum : ∀ x y, δ x y = η x + η y - η (x * y)`. Introduce `x y`. Simplify using `only [hηeq]`. Take the linear combination `ν * hF x y - δ x y * hνN`. Use `⟨fun x => a₀ x * (1 + η x), fun x => ?_, fun x y => ?_⟩` and prove the remaining obligations.

Establish `h0 : Ideal.Quotient.mk I (η x) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (hηI x)`. Simplify using `[ha₀, h0]`. Establish `h1` using `mul_eq_zero_of_mem_of_sq_eq_bot hI (hδI x y) (hηI (x * y))`. Establish `h2` using `mul_eq_zero_of_mem_of_sq_eq_bot hI (hηI x) (hηI y)`. Take the linear combination `(1 + η (x * y)) * hδ x y + a₀ x * a₀ y * (hsum x y + h1 - h2)`.
-/
theorem exists_lift_splitting (hI : I ^ 2 = ⊥) {C : Type} [CommGroup C] [Finite C]
    (hN : IsUnit ((Nat.card C : ℕ) : B)) (c : C → C → Bˣ)
    (hc : ∀ x y z, c x y * c (x * y) z = c y z * c x (y * z)) (b : C → B ⧸ I)
    (hb : ∀ x, IsUnit (b x))
    (hbc : ∀ x y, Ideal.Quotient.mk I (c x y) * b (x * y) = b x * b y) :
    ∃ a : C → B, (∀ x, Ideal.Quotient.mk I (a x) = b x) ∧ ∀ x y, c x y * a (x * y) = a x * a y := by
  classical
  have := Fintype.ofFinite C
  rw [Nat.card_eq_fintype_card] at hN
  choose a₀ ha₀ using fun x => Ideal.Quotient.mk_surjective (b x)
  have hu : ∀ x, IsUnit (a₀ x) := fun x => isUnit_of_isUnit_quotient_of_sq_eq_bot hI (by rw [ha₀]; exact hb x)
  set δ : C → C → B := fun x y =>
    ((c x y : B) * a₀ (x * y) - a₀ x * a₀ y) * ↑(hu x).unit⁻¹ * ↑(hu y).unit⁻¹ with hδeq
  have hδI : ∀ x y, δ x y ∈ I := by
    intro x y
    refine I.mul_mem_right _ (I.mul_mem_right _ (Ideal.Quotient.eq.1 ?_))
    rw [map_mul, map_mul, ha₀, ha₀, ha₀]
    exact hbc x y
  have hδ : ∀ x y, (c x y : B) * a₀ (x * y) = a₀ x * a₀ y + a₀ x * a₀ y * δ x y := by
    intro x y
    have h1 := (hu x).mul_val_inv
    have h2 := (hu y).mul_val_inv
    simp only [hδeq]
    linear_combination (-((c x y : B) * a₀ (x * y) - a₀ x * a₀ y) * (a₀ y * ↑(hu y).unit⁻¹)) * h1
      - ((c x y : B) * a₀ (x * y) - a₀ x * a₀ y) * h2
  have hco : ∀ x y z, δ x y + δ (x * y) z = δ y z + δ x (y * z) := by
    intro x y z
    have hP : IsUnit (a₀ x * a₀ y * a₀ z) := ((hu x).mul (hu y)).mul (hu z)
    have E : (c x y : B) * c (x * y) z = c y z * c x (y * z) := by
      have := congrArg (fun t : Bˣ => (t : B)) (hc x y z)
      simpa using this
    have h12 := mul_eq_zero_of_mem_of_sq_eq_bot hI (hδI x y) (hδI (x * y) z)
    have h34 := mul_eq_zero_of_mem_of_sq_eq_bot hI (hδI y z) (hδI x (y * z))
    have A := hδ x y
    have Bq := hδ (x * y) z
    have Cq := hδ y z
    have D := hδ x (y * z)
    rw [mul_assoc x y z] at Bq
    have key : a₀ x * a₀ y * a₀ z * (δ x y + δ (x * y) z - (δ y z + δ x (y * z))) = 0 := by
      linear_combination a₀ (x * (y * z)) * E - (c x y : B) * Bq
        - a₀ z * (1 + δ (x * y) z) * A + (c y z : B) * D + a₀ x * (1 + δ x (y * z)) * Cq
        - a₀ x * a₀ y * a₀ z * h12 + a₀ x * a₀ y * a₀ z * h34
    rw [hP.mul_right_eq_zero, sub_eq_zero] at key
    exact key
  set F : C → B := fun x => ∑ z, δ x z with hFeq
  have hF : ∀ x y, (Fintype.card C : B) * δ x y + F (x * y) = F y + F x := by
    intro x y
    have hs := Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) => hco x y z)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hs
    have hre : ∑ z, δ x (y * z) = ∑ z, δ x z :=
      Fintype.sum_equiv (Equiv.mulLeft y) _ _ (fun z => rfl)
    rw [hre] at hs
    simpa [hFeq] using hs
  set ν : B := ↑hN.unit⁻¹ with hνeq
  have hνN : ν * (Fintype.card C : B) = 1 := hN.val_inv_mul
  set η : C → B := fun x => ν * F x with hηeq
  have hηI : ∀ x, η x ∈ I := fun x => I.mul_mem_left _ (I.sum_mem fun z _ => hδI x z)
  have hsum : ∀ x y, δ x y = η x + η y - η (x * y) := by
    intro x y
    simp only [hηeq]
    linear_combination ν * hF x y - δ x y * hνN
  refine ⟨fun x => a₀ x * (1 + η x), fun x => ?_, fun x y => ?_⟩
  · have h0 : Ideal.Quotient.mk I (η x) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hηI x)
    simp [ha₀, h0]
  · have h1 := mul_eq_zero_of_mem_of_sq_eq_bot hI (hδI x y) (hηI (x * y))
    have h2 := mul_eq_zero_of_mem_of_sq_eq_bot hI (hηI x) (hηI y)
    linear_combination (1 + η (x * y)) * hδ x y + a₀ x * a₀ y * (hsum x y + h1 - h2)

end SquareZero

/- English proof (translation)
Use `set T : C → Module.End R (C →₀ R) := fun x => Finsupp.linearCombination R (fun y => Finsupp.single (x * y) (c x y : R)) with hTeq`. Establish `hTs : ∀ x y (r : R), T x (Finsupp.single y r) = Finsupp.single (x * y) (r * c x y)`. Introduce `x y r`. Simplify using `[hTeq, Finsupp.linearCombination_single, Finsupp.smul_single]`. Establish `hcR : ∀ x y z, (c x y : R) * c (x * y) z = c y z * c x (y * z)`.

Introduce `x y z`. Use `congrArg (fun t : Rˣ => (t : R)) (hc x y z)` as an intermediate fact. Simplify using `using this`. Establish `hc1 : ∀ z, c 1 z = c 1 1`. Introduce `z`.

Establish `h` using `hc 1 1 z`. Simplify using `only [one_mul] at h`. Conclude with `(mul_right_cancel h).symm`. Establish `hT1 : T 1 = (c 1 1 : R) • 1`. Apply `Finsupp.lhom_ext` to reduce the goal to its premises.

Introduce `z r`. Rewrite using `[hTs, LinearMap.smul_apply, Module.End.one_apply, Finsupp.smul_single, hc1, one_mul, smul_eq_mul, mul_comm]`. Establish `hTmul : ∀ x y, T x * T y = (c x y : R) • T (x * y)`. Introduce `x y`. Apply `Finsupp.lhom_ext` to reduce the goal to its premises.

Introduce `z r`. Rewrite using `[Module.End.mul_apply, hTs, hTs, LinearMap.smul_apply, hTs, Finsupp.smul_single, mul_assoc, smul_eq_mul, mul_assoc x y z]`. Use `congr 1`. Take the linear combination `(-r) * hcR x y z`. Establish `hcomm : ∀ a ∈ Set.range T, ∀ b ∈ Set.range T, a * b = b * a`.

Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨y, rfl⟩`. Rewrite using `[hTmul, hTmul, hs, mul_comm x y]`. Establish `hAc` using `Algebra.isMulCommutative_adjoin R hcomm`. Use `set S := Algebra.adjoin R (Set.range T) with hSeq`. Set `hA : CommRing S` to `{ (inferInstance : Ring S) with mul_comm := fun a b => hAc.is_comm.comm a b }`.

Set `f : R →+* S` to `{ toFun := fun r => ⟨algebraMap R (Module.End R (C →₀ R)) r, S.algebraMap_mem r⟩ map_one' := Subtype.ext (map_one _) map_mul' := fun r s => Subtype.ext (map_mul _ r s) map_zero' := Subtype.ext (map_zero _) map_add' := fun r s => Subtype.ext (map_add _ r s) }`. Set `alg : Algebra R S` to `f.toAlgebra`. Set `V : S →ₗ[R] Module.End R (C →₀ R)` to `{ toFun := fun a => (a : Module.End R (C →₀ R)) map_add' := fun _ _ => rfl map_smul' := fun r a => by show algebraMap R _ r * (a : Module.End R (C →₀ R)) = r • (a : Module.End R (C →₀ R))`. Rewrite using `[Algebra.smul_def] }`. Set `e : C → S` to `fun x => ⟨T x, Algebra.subset_adjoin ⟨x, rfl⟩⟩`.

Establish `hliT : LinearIndependent R T`. Establish `h0` using `(Finsupp.basisSingleOne : Module.Basis C R (C →₀ R)).linearIndependent.units_smul (fun x => c x 1)`. Apply `LinearIndependent.of_comp (LinearMap.applyₗ (Finsupp.single (1 : C) (1 : R)))` to reduce the goal to its premises. Use `h0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Simplify using `[hTs, Units.smul_def, Finsupp.smul_single]`. Establish `hli : LinearIndependent R e` using `LinearIndependent.of_comp V hliT`. Establish `hone : (1 : Module.End R (C →₀ R)) = ((c 1 1)⁻¹ : Rˣ) • T 1`. Rewrite using `[hT1, Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`. Establish `hle : Algebra.adjoin R (Set.range T) ≤ (Submodule.span R (Set.range T)).toSubalgebra (by rw [hone]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)) (by`.

Introduce `a b ha hb`. Establish `hm` using `Submodule.mul_mem_mul ha hb`. Rewrite `hm` using `[Submodule.span_mul_span]`. Use `Submodule.span_le.2 ?_ hm` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩`.

Use `beta_reduce`. Rewrite using `[hTmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) :=`. Use the proof step `Algebra.adjoin_le (fun _ h => Submodule.subset_span h)`. Establish `hsp : ⊤ ≤ Submodule.span R (Set.range e)`.

Introduce `y _`. Establish `hy : (y : Module.End R (C →₀ R)) ∈ Submodule.span R (Set.range T)` using `hle y.2`. Establish `hr : Set.range T = V '' Set.range e`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite `hy` using `[hr, ← Submodule.map_span]`. Take `⟨z, hz, hzy⟩` from `hy`. Establish `hzy' : z = y` using `Subtype.ext hzy`. Conclude with `hzy' ▸ hz`. Use `⟨S, hA, alg, Module.Basis.mk hli hsp, fun x y => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Module.Basis.mk_apply, Module.Basis.mk_apply, Module.Basis.mk_apply]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show T x * T y = algebraMap R (Module.End R (C →₀ R)) (c x y : R) * T (x * y)`. Rewrite using `[hTmul, Algebra.smul_def]`. Rewrite using `[Module.Basis.mk_apply]`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show T 1 = algebraMap R (Module.End R (C →₀ R)) (c 1 1 : R)`. Rewrite using `[hT1, Algebra.algebraMap_eq_smul_one]`.
-/
theorem exists_twisted_algebra (R : Type) [CommRing R] (C : Type) [CommGroup C] (c : C → C → Rˣ)
    (hs : ∀ x y, c x y = c y x) (hc : ∀ x y z, c x y * c (x * y) z = c y z * c x (y * z)) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (e : Module.Basis C R A),
      (∀ x y, e x * e y = (c x y : R) • e (x * y)) ∧ e 1 = algebraMap R A (c 1 1) := by
  classical
  set T : C → Module.End R (C →₀ R) := fun x =>
    Finsupp.linearCombination R (fun y => Finsupp.single (x * y) (c x y : R)) with hTeq
  have hTs : ∀ x y (r : R), T x (Finsupp.single y r) = Finsupp.single (x * y) (r * c x y) := by
    intro x y r
    simp [hTeq, Finsupp.linearCombination_single, Finsupp.smul_single]
  have hcR : ∀ x y z, (c x y : R) * c (x * y) z = c y z * c x (y * z) := by
    intro x y z
    have := congrArg (fun t : Rˣ => (t : R)) (hc x y z)
    simpa using this
  have hc1 : ∀ z, c 1 z = c 1 1 := by
    intro z
    have h := hc 1 1 z
    simp only [one_mul] at h
    exact (mul_right_cancel h).symm
  have hT1 : T 1 = (c 1 1 : R) • 1 := by
    apply Finsupp.lhom_ext
    intro z r
    rw [hTs, LinearMap.smul_apply, Module.End.one_apply, Finsupp.smul_single, hc1, one_mul,
      smul_eq_mul, mul_comm]
  have hTmul : ∀ x y, T x * T y = (c x y : R) • T (x * y) := by
    intro x y
    apply Finsupp.lhom_ext
    intro z r
    rw [Module.End.mul_apply, hTs, hTs, LinearMap.smul_apply, hTs, Finsupp.smul_single, mul_assoc,
      smul_eq_mul, mul_assoc x y z]
    congr 1
    linear_combination (-r) * hcR x y z
  have hcomm : ∀ a ∈ Set.range T, ∀ b ∈ Set.range T, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hTmul, hTmul, hs, mul_comm x y]
  have hAc := Algebra.isMulCommutative_adjoin R hcomm
  set S := Algebra.adjoin R (Set.range T) with hSeq
  let hA : CommRing S :=
    { (inferInstance : Ring S) with mul_comm := fun a b => hAc.is_comm.comm a b }
  let f : R →+* S :=
    { toFun := fun r => ⟨algebraMap R (Module.End R (C →₀ R)) r, S.algebraMap_mem r⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun r s => Subtype.ext (map_mul _ r s)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun r s => Subtype.ext (map_add _ r s) }
  let alg : Algebra R S := f.toAlgebra
  let V : S →ₗ[R] Module.End R (C →₀ R) :=
    { toFun := fun a => (a : Module.End R (C →₀ R))
      map_add' := fun _ _ => rfl
      map_smul' := fun r a => by
        show algebraMap R _ r * (a : Module.End R (C →₀ R)) = r • (a : Module.End R (C →₀ R))
        rw [Algebra.smul_def] }
  let e : C → S := fun x => ⟨T x, Algebra.subset_adjoin ⟨x, rfl⟩⟩
  have hliT : LinearIndependent R T := by
    have h0 := (Finsupp.basisSingleOne : Module.Basis C R (C →₀ R)).linearIndependent.units_smul
      (fun x => c x 1)
    apply LinearIndependent.of_comp (LinearMap.applyₗ (Finsupp.single (1 : C) (1 : R)))
    convert h0 using 1
    funext x
    simp [hTs, Units.smul_def, Finsupp.smul_single]
  have hli : LinearIndependent R e := LinearIndependent.of_comp V hliT
  have hone : (1 : Module.End R (C →₀ R)) = ((c 1 1)⁻¹ : Rˣ) • T 1 := by
    rw [hT1, Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hle : Algebra.adjoin R (Set.range T) ≤ (Submodule.span R (Set.range T)).toSubalgebra
      (by rw [hone]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
      (by
        intro a b ha hb
        have hm := Submodule.mul_mem_mul ha hb
        rw [Submodule.span_mul_span] at hm
        refine Submodule.span_le.2 ?_ hm
        rintro _ ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩
        beta_reduce
        rw [hTmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) :=
    Algebra.adjoin_le (fun _ h => Submodule.subset_span h)
  have hsp : ⊤ ≤ Submodule.span R (Set.range e) := by
    intro y _
    have hy : (y : Module.End R (C →₀ R)) ∈ Submodule.span R (Set.range T) := hle y.2
    have hr : Set.range T = V '' Set.range e := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← Submodule.map_span] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : z = y := Subtype.ext hzy
    exact hzy' ▸ hz
  refine ⟨S, hA, alg, Module.Basis.mk hli hsp, fun x y => ?_, ?_⟩
  · rw [Module.Basis.mk_apply, Module.Basis.mk_apply, Module.Basis.mk_apply]
    apply Subtype.ext
    show T x * T y = algebraMap R (Module.End R (C →₀ R)) (c x y : R) * T (x * y)
    rw [hTmul, Algebra.smul_def]
  · rw [Module.Basis.mk_apply]
    apply Subtype.ext
    show T 1 = algebraMap R (Module.End R (C →₀ R)) (c 1 1 : R)
    rw [hT1, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Establish `hfree : Module.Free R A` using `Module.Free.of_basis e`. Establish `hfin : Module.Finite R A` using `Module.Finite.of_basis e`. Establish `hfp : Module.FinitePresentation R A` using `Module.finitePresentation_of_projective R A`. Establish `hafp : Algebra.FinitePresentation R A` using `Algebra.FinitePresentation.of_finitePresentation R A`. Establish `hcR : ∀ x y z, (c x y : R) * c (x * y) z = c y z * c x (y * z)`.

Introduce `x y z`. Use `congrArg (fun t : Rˣ => (t : R)) (hc x y z)` as an intermediate fact. Simplify using `using this`. Establish `hmap : ∀ {T : Type} [CommRing T] [Algebra R T] (g : A →ₐ[R] T) (x y : C), algebraMap R T (c x y) * g (e (x * y)) = g (e x) * g (e y)`. Introduce `T _ _ g x y`.

Rewrite using `[← map_mul, he, map_smul, Algebra.smul_def]`. Establish `hone : (1 : A) = (↑(c 1 1)⁻¹ : R) • e 1`. Rewrite using `[h1, Algebra.smul_def, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]`. Use `{ formallyEtale := ?_, finitePresentation := hafp }` and prove the remaining obligations. Rewrite using `[Algebra.FormallyEtale.iff_comp_bijective]`.

Introduce `B _ _ I hI`. Establish `hN' : IsUnit ((Nat.card C : ℕ) : B)`. Use `hN.map (algebraMap R B)` as an intermediate fact. Simplify using `using this`. Prove the components needed by the constructor for the conclusion.

Introduce `g₁ g₂ hg`. Apply `AlgHom.toLinearMap_injective` to reduce the goal to its premises. Apply `e.ext` to reduce the goal to its premises. Introduce `x`. Use `show g₁ (e x) = g₂ (e x)`.

Establish `hq : ∀ x, Ideal.Quotient.mk I (g₂ (e x)) = Ideal.Quotient.mk I (g₁ (e x))`. Introduce `x`. Use `congrArg (fun g : A →ₐ[R] B ⧸ I => g (e x)) hg` as an intermediate fact. Simplify using `using this.symm`. Use `set v : C → B := fun x => ↑((hu x).map g₁).unit⁻¹ with hveq`.

Establish `hinv : ∀ x, g₁ (e x) * v x = 1` using `fun x => ((hu x).map g₁).mul_val_inv`. Use `set w : C → B := fun x => g₂ (e x) * v x with hweq`. Establish `hw1 : ∀ x, w x - 1 ∈ I`. Introduce `x`. Establish `h : w x - 1 = (g₂ (e x) - g₁ (e x)) * v x`.

Simplify using `only [hweq]`. Take the linear combination `hinv x`. Rewrite using `[h]`. Conclude with `I.mul_mem_right _ (Ideal.Quotient.eq.1 (hq x))`. Establish `hwmul : ∀ x y, w (x * y) = w x * w y`.

Introduce `x y`. Establish `k : algebraMap R B (c x y) * v x * v y = v (x * y)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hinv, mul_one]`. Use `_ = (algebraMap R B (c x y) * g₁ (e (x * y))) * v x * v y * v (x * y) := by ring`.

Use `_ = (g₁ (e x) * v x) * (g₁ (e y) * v y) * v (x * y) := by rw [hmap]; ring`. Use `_ = v (x * y) := by rw [hinv, hinv]; ring`. Simplify using `only [hweq]`. Rewrite using `[← k]`. Take the linear combination `v x * v y * hmap g₂ x y`.

Establish `hw1' : w 1 = 1`. Establish `hm` using `hwmul 1 1`. Rewrite `hm` using `[one_mul]`. Establish `hsq` using `mul_eq_zero_of_mem_of_sq_eq_bot hI (hw1 1) (hw1 1)`. Take the linear combination `(-1 : B) * hm - hsq`.

Establish `hpow : ∀ k : ℕ, w x ^ k = w (x ^ k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [hw1']`. Consider the case `succ k ih => rw [pow_succ, ih, ← hwmul, pow_succ]`.

Establish `hx1 : w x = 1`. Use `eq_of_pow_eq hI hN' (hw1 x) (by simp) ?_` and prove the remaining obligations. Rewrite using `[hpow, pow_card_eq_one', hw1', one_pow]`. Establish `hx1' : g₂ (e x) * v x = 1` using `hx1`. Take the linear combination `g₂ (e x) * hinv x - g₁ (e x) * hx1'`.

Introduce `f set c' : C → C → Bˣ := fun x y => Units.map (algebraMap R B).toMonoidHom (c x y) with hcpeq`. Establish `hc' : ∀ x y z, c' x y * c' (x * y) z = c' y z * c' x (y * z)`. Introduce `x y z`. Use `congrArg (Units.map (algebraMap R B).toMonoidHom) (hc x y z)` as an intermediate fact. Simplify `this` using `[hcpeq]`.

Establish `hbc : ∀ x y, Ideal.Quotient.mk I (c' x y : B) * f (e (x * y)) = f (e x) * f (e y)`. Introduce `x y`. Use `hmap f x y` as an intermediate fact. Simplify `this` using `[hcpeq]`. Take `⟨a, ha, hac⟩` from `exists_lift_splitting hI hN' c' hc' (fun x => f (e x)) (fun x => (hu x).map f) hbc`.

Establish `ha1u : IsUnit (a 1)` using `isUnit_of_isUnit_quotient_of_sq_eq_bot hI (by rw [ha]; exact (hu 1).map f)`. Establish `ha1 : a 1 = algebraMap R B (c 1 1)`. Establish `h` using `hac 1 1`. Rewrite `h` using `[one_mul]`. Establish `h' : (c' 1 1 : B) * a 1 = a 1 * a 1` using `h`.

Conclude with `((ha1u.mul_left_inj).1 h').symm`. Use `set L : A →ₗ[R] B := e.constr R a with hLeq`. Establish `hLe : ∀ x, L (e x) = a x` using `fun x => e.constr_basis R a x`. Establish `hL1 : L 1 = 1`. Rewrite using `[hone, L.map_smul, hLe, ha1, Algebra.smul_def, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]`.

Establish `hbil : (LinearMap.mul R B).compl₁₂ L L = (LinearMap.mul R A).compr₂ L`. Apply `e.ext` to reduce the goal to its premises. Introduce `x`. Apply `e.ext` to reduce the goal to its premises. Introduce `y`.

Establish `h` using `hac x y`. Simplify using `only [LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.compr₂_apply, hLe, he]`. Rewrite using `[L.map_smul, hLe, Algebra.smul_def, ← h]`. Both sides reduce to the same expression. Establish `hLmul : ∀ p q, L (p * q) = L p * L q`.

Introduce `p q`. Use `LinearMap.congr_fun (LinearMap.congr_fun hbil p) q` as an intermediate fact. Simplify using `using this.symm`. Use `⟨AlgHom.ofLinearMap L hL1 hLmul, ?_⟩` and prove the remaining obligations. Apply `AlgHom.toLinearMap_injective` to reduce the goal to its premises.

Apply `e.ext` to reduce the goal to its premises. Introduce `x`. Use `show Ideal.Quotient.mk I (L (e x)) = f (e x)`. Rewrite using `[hLe, ha]`.
-/
theorem etale_of_twisted_basis {R : Type} [CommRing R] {C : Type} [CommGroup C] [Finite C]
    (c : C → C → Rˣ) (hc : ∀ x y z, c x y * c (x * y) z = c y z * c x (y * z))
    (hN : IsUnit ((Nat.card C : ℕ) : R)) {A : Type} [CommRing A] [Algebra R A]
    (e : Module.Basis C R A) (he : ∀ x y, e x * e y = (c x y : R) • e (x * y))
    (h1 : e 1 = algebraMap R A (c 1 1)) (hu : ∀ x, IsUnit (e x)) : Algebra.Etale R A := by
  classical
  have hfree : Module.Free R A := Module.Free.of_basis e
  have hfin : Module.Finite R A := Module.Finite.of_basis e
  have hfp : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  have hafp : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finitePresentation R A
  have hcR : ∀ x y z, (c x y : R) * c (x * y) z = c y z * c x (y * z) := by
    intro x y z
    have := congrArg (fun t : Rˣ => (t : R)) (hc x y z)
    simpa using this
  have hmap : ∀ {T : Type} [CommRing T] [Algebra R T] (g : A →ₐ[R] T) (x y : C),
      algebraMap R T (c x y) * g (e (x * y)) = g (e x) * g (e y) := by
    intro T _ _ g x y
    rw [← map_mul, he, map_smul, Algebra.smul_def]
  have hone : (1 : A) = (↑(c 1 1)⁻¹ : R) • e 1 := by
    rw [h1, Algebra.smul_def, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  refine { formallyEtale := ?_, finitePresentation := hafp }
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  intro B _ _ I hI
  have hN' : IsUnit ((Nat.card C : ℕ) : B) := by
    have := hN.map (algebraMap R B)
    simpa using this
  constructor
  · intro g₁ g₂ hg
    apply AlgHom.toLinearMap_injective
    apply e.ext
    intro x
    show g₁ (e x) = g₂ (e x)
    have hq : ∀ x, Ideal.Quotient.mk I (g₂ (e x)) = Ideal.Quotient.mk I (g₁ (e x)) := by
      intro x
      have := congrArg (fun g : A →ₐ[R] B ⧸ I => g (e x)) hg
      simpa using this.symm
    set v : C → B := fun x => ↑((hu x).map g₁).unit⁻¹ with hveq
    have hinv : ∀ x, g₁ (e x) * v x = 1 := fun x => ((hu x).map g₁).mul_val_inv
    set w : C → B := fun x => g₂ (e x) * v x with hweq
    have hw1 : ∀ x, w x - 1 ∈ I := by
      intro x
      have h : w x - 1 = (g₂ (e x) - g₁ (e x)) * v x := by
        simp only [hweq]
        linear_combination hinv x
      rw [h]
      exact I.mul_mem_right _ (Ideal.Quotient.eq.1 (hq x))
    have hwmul : ∀ x y, w (x * y) = w x * w y := by
      intro x y
      have k : algebraMap R B (c x y) * v x * v y = v (x * y) := by
        calc algebraMap R B (c x y) * v x * v y
            = algebraMap R B (c x y) * v x * v y * (g₁ (e (x * y)) * v (x * y)) := by
              rw [hinv, mul_one]
          _ = (algebraMap R B (c x y) * g₁ (e (x * y))) * v x * v y * v (x * y) := by ring
          _ = (g₁ (e x) * v x) * (g₁ (e y) * v y) * v (x * y) := by rw [hmap]; ring
          _ = v (x * y) := by rw [hinv, hinv]; ring
      simp only [hweq]
      rw [← k]
      linear_combination v x * v y * hmap g₂ x y
    have hw1' : w 1 = 1 := by
      have hm := hwmul 1 1
      rw [one_mul] at hm
      have hsq := mul_eq_zero_of_mem_of_sq_eq_bot hI (hw1 1) (hw1 1)
      linear_combination (-1 : B) * hm - hsq
    have hpow : ∀ k : ℕ, w x ^ k = w (x ^ k) := by
      intro k
      induction k with
      | zero => simp [hw1']
      | succ k ih => rw [pow_succ, ih, ← hwmul, pow_succ]
    have hx1 : w x = 1 := by
      refine eq_of_pow_eq hI hN' (hw1 x) (by simp) ?_
      rw [hpow, pow_card_eq_one', hw1', one_pow]
    have hx1' : g₂ (e x) * v x = 1 := hx1
    linear_combination g₂ (e x) * hinv x - g₁ (e x) * hx1'
  · intro f
    set c' : C → C → Bˣ := fun x y => Units.map (algebraMap R B).toMonoidHom (c x y) with hcpeq
    have hc' : ∀ x y z, c' x y * c' (x * y) z = c' y z * c' x (y * z) := by
      intro x y z
      have := congrArg (Units.map (algebraMap R B).toMonoidHom) (hc x y z)
      simpa [hcpeq] using this
    have hbc : ∀ x y, Ideal.Quotient.mk I (c' x y : B) * f (e (x * y)) = f (e x) * f (e y) := by
      intro x y
      have := hmap f x y
      simpa [hcpeq] using this
    obtain ⟨a, ha, hac⟩ := exists_lift_splitting hI hN' c' hc' (fun x => f (e x))
      (fun x => (hu x).map f) hbc
    have ha1u : IsUnit (a 1) := isUnit_of_isUnit_quotient_of_sq_eq_bot hI (by rw [ha]; exact (hu 1).map f)
    have ha1 : a 1 = algebraMap R B (c 1 1) := by
      have h := hac 1 1
      rw [one_mul] at h
      have h' : (c' 1 1 : B) * a 1 = a 1 * a 1 := h
      exact ((ha1u.mul_left_inj).1 h').symm
    set L : A →ₗ[R] B := e.constr R a with hLeq
    have hLe : ∀ x, L (e x) = a x := fun x => e.constr_basis R a x
    have hL1 : L 1 = 1 := by
      rw [hone, L.map_smul, hLe, ha1, Algebra.smul_def, ← map_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, map_one]
    have hbil : (LinearMap.mul R B).compl₁₂ L L = (LinearMap.mul R A).compr₂ L := by
      apply e.ext
      intro x
      apply e.ext
      intro y
      have h := hac x y
      simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.compr₂_apply, hLe, he]
      rw [L.map_smul, hLe, Algebra.smul_def, ← h]
      rfl
    have hLmul : ∀ p q, L (p * q) = L p * L q := by
      intro p q
      have := LinearMap.congr_fun (LinearMap.congr_fun hbil p) q
      simpa using this.symm
    refine ⟨AlgHom.ofLinearMap L hL1 hLmul, ?_⟩
    apply AlgHom.toLinearMap_injective
    apply e.ext
    intro x
    show Ideal.Quotient.mk I (L (e x)) = f (e x)
    rw [hLe, ha]

/- English proof (translation)
Introduce `R _ n C _ _ c hn hn0 hexp hs hc`. Take `⟨A, hA, hAlg, e, he, h1⟩` from `exists_twisted_algebra R C c hs hc`. Establish `hone : (1 : A) = (↑(c 1 1)⁻¹ : R) • e 1`. Rewrite using `[h1, Algebra.smul_def, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]`. Establish `hpow : ∀ x (k : ℕ), ∃ r : Rˣ, e x ^ k = (r : R) • e (x ^ k)`.

Introduce `x k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨(c 1 1)⁻¹, by rw [pow_zero, pow_zero, hone]⟩`. Consider the case `succ k ih`. Take `⟨r, hr⟩` from `ih`.

Use `⟨r * c (x ^ k) x, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, hr, smul_mul_assoc, he, smul_smul, pow_succ, Units.val_mul]`. Establish `hu : ∀ x, IsUnit (e x)`. Introduce `x`. Take `⟨r, hr⟩` from `hpow x n`.

Rewrite `hr` using `[hexp, h1, Algebra.smul_def, ← map_mul]`. Establish `hun : IsUnit (e x ^ n)`. Rewrite using `[hr]`. Conclude with `(r.isUnit.mul (c 1 1).isUnit).map (algebraMap R A)`. Conclude with `(isUnit_pow_iff (Nat.pos_iff_ne_zero.1 hn0)).1 hun`.

Establish `hN : IsUnit ((Nat.card C : ℕ) : R)`. Take `⟨m, hm⟩` from `card_dvd_exponent_pow_rank' (G := C) hexp`. Establish `hun : IsUnit ((n ^ Group.rank C : ℕ) : R)`. Rewrite using `[Nat.cast_pow]`. Conclude with `hn.pow _`.

Rewrite `hun` using `[hm, Nat.cast_mul]`. Conclude with `isUnit_of_mul_isUnit_left hun`. Establish `hfree : Module.Free R A` using `Module.Free.of_basis e`. Use `⟨A, hA, hAlg, etale_of_twisted_basis c hc hN e he h1 hu, Module.Finite.of_basis e, ?_, fun x => (hu x).unit, fun x y => ?_⟩` and prove the remaining obligations. Break down `subsingleton_or_nontrivial R with hR | hR` into its components or cases.

Conclude with `{ submodule_ne_top := fun m hm => (hm.ne_top (Subsingleton.elim _ _)).elim }`. Establish `hnt : Nontrivial A` using `nontrivial_of_ne (e 1) 0 (e.ne_zero 1) infer_instance`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, Units.coe_map, IsUnit.unit_spec]`. Rewrite using `[he, Algebra.smul_def]`.

Both sides reduce to the same expression.
-/
theorem exists_etale_splitting :
    ∀ (R : Type) [CommRing R] (n : ℕ) (C : Type) [CommGroup C] [Finite C] (c : C → C → Rˣ), IsUnit (n : R) → 0 < n → (∀ x : C, x ^ n = 1) → (∀ x y, c x y = c y x) → (∀ x y z, c x y * c (x * y) z = c y z * c x (y * z)) → ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R'), Algebra.Etale R R' ∧ Module.Finite R R' ∧ Module.FaithfullyFlat R R' ∧ ∃ b : C → R'ˣ, ∀ x y, Units.map (algebraMap R R').toMonoidHom (c x y) * b (x * y) = b x * b y := by
  intro R _ n C _ _ c hn hn0 hexp hs hc
  obtain ⟨A, hA, hAlg, e, he, h1⟩ := exists_twisted_algebra R C c hs hc
  have hone : (1 : A) = (↑(c 1 1)⁻¹ : R) • e 1 := by
    rw [h1, Algebra.smul_def, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have hpow : ∀ x (k : ℕ), ∃ r : Rˣ, e x ^ k = (r : R) • e (x ^ k) := by
    intro x k
    induction k with
    | zero => exact ⟨(c 1 1)⁻¹, by rw [pow_zero, pow_zero, hone]⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * c (x ^ k) x, ?_⟩
      rw [pow_succ, hr, smul_mul_assoc, he, smul_smul, pow_succ, Units.val_mul]
  have hu : ∀ x, IsUnit (e x) := by
    intro x
    obtain ⟨r, hr⟩ := hpow x n
    rw [hexp, h1, Algebra.smul_def, ← map_mul] at hr
    have hun : IsUnit (e x ^ n) := by
      rw [hr]
      exact (r.isUnit.mul (c 1 1).isUnit).map (algebraMap R A)
    exact (isUnit_pow_iff (Nat.pos_iff_ne_zero.1 hn0)).1 hun
  have hN : IsUnit ((Nat.card C : ℕ) : R) := by
    obtain ⟨m, hm⟩ := card_dvd_exponent_pow_rank' (G := C) hexp
    have hun : IsUnit ((n ^ Group.rank C : ℕ) : R) := by
      rw [Nat.cast_pow]
      exact hn.pow _
    rw [hm, Nat.cast_mul] at hun
    exact isUnit_of_mul_isUnit_left hun
  have hfree : Module.Free R A := Module.Free.of_basis e
  refine ⟨A, hA, hAlg, etale_of_twisted_basis c hc hN e he h1 hu, Module.Finite.of_basis e, ?_,
    fun x => (hu x).unit, fun x y => ?_⟩
  · rcases subsingleton_or_nontrivial R with hR | hR
    · exact { submodule_ne_top := fun m hm => (hm.ne_top (Subsingleton.elim _ _)).elim }
    · have hnt : Nontrivial A := nontrivial_of_ne (e 1) 0 (e.ne_zero 1)
      infer_instance
  · apply Units.ext
    simp only [Units.val_mul, Units.coe_map, IsUnit.unit_spec]
    rw [he, Algebra.smul_def]
    rfl

end GlobalTheory.CocycleSplit

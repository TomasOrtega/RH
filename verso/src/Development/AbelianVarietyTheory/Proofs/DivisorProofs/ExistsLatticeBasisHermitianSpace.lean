import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPrincipalIdealRingLoc
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatMulIntegral

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatAdelicBasis

open NumberField IsDedekindDomain
open scoped TensorProduct Matrix

/- English proof (translation)
Establish `key : ∀ P Q : Matrix (Fin n) (Fin n) R, P * Q = 1 → (e • P + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (e • Q + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) = 1`. Introduce `P Q h`. Establish `a1 : e * (1 - e) = 0` using `by rw [mul_sub, hee, mul_one, sub_self]`. Establish `a2 : (1 - e) * e = 0` using `by rw [mul_comm, a1]`. Establish `a3 : (1 - e) * (1 - e) = 1 - e` using `by rw [mul_sub, a2, mul_one, sub_zero]`.

Simplify using `only [add_mul, mul_add, smul_mul_smul_comm, h, hee, a1, a2, a3, zero_smul, add_zero, zero_add, mul_one]`. Rewrite using `[← add_smul, add_sub_cancel, one_smul]`. Establish `hPQ : γ.val.map φ * (γ⁻¹).val.map φ = 1`. Rewrite using `[← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero φ) (map_one φ)]`. Establish `hQP : (γ⁻¹).val.map φ * γ.val.map φ = 1`.

Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero φ) (map_one φ)]`. Set `β : GL (Fin n) R` to `⟨_, _, key _ _ hPQ, key _ _ hQP⟩`. Use `⟨β, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩` and prove the remaining obligations. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨x, hx, rfl⟩` from `hy`. Introduce `i`. Take `⟨o, ho⟩` from `h2 x hx i`. Take `⟨p, hp⟩` from `h4 x hx i`. Establish `hm : ((γ⁻¹).val.map φ *ᵥ fun i => φ (x i)) i = φ (((γ⁻¹).val *ᵥ x) i)` using `(RingHom.map_mulVec φ _ x i).symm`.

Establish `ho'` using `congrArg φ ho`. Establish `hp'` using `congrArg φ hp`. Rewrite `ho'`, `hp'` using `[map_mul, map_natCast]`. Establish `: ((β⁻¹).val *ᵥ fun i => φ (x i)) i = e * u * φ (algebraMap O E p) + f * φ (algebraMap O E o)`. Express the relevant statement in the definitionally equal form `((e • (γ⁻¹).val.map φ + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) *ᵥ fun i => φ (x i)) i = _`.

Rewrite using `[Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hm, smul_eq_mul, smul_eq_mul, ← ho', ← hp', hef]`. Take the linear combination `(-φ (((γ⁻¹).val *ᵥ x) i)) * heu`. Rewrite using `[this]`. Conclude with `add_mem (mul_mem (mul_mem he hu) (hO p)) (mul_mem hf (hO o))`. Consider the case `zero => intro i`.

Rewrite using `[Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add y w _ _ hy hw => intro i`. Rewrite using `[Matrix.mulVec_add]`. Conclude with `add_mem (hy i) (hw i)`.

Consider the case `smul a y _ hy`. Introduce `i`. Rewrite using `[Subring.smul_def, Matrix.mulVec_smul]`. Conclude with `mul_mem a.2 (hy i)`. Establish `hz' : z = ∑ j, (⟨_, hz j⟩ : S) • ((⟨e, he⟩ : S) • (fun i => φ (γ.val i j)) + (⟨f, hf⟩ : S) • fun i => φ (((N : E) • (Pi.single j 1 : Fin n → E)) i))`.

Establish `: z = β.val *ᵥ ((β⁻¹).val *ᵥ z)`. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Use `conv_lhs => rw [this]`. Generalize the expression as in `(β⁻¹).val *ᵥ z = w at hz`. Use function extensionality and compare the values at `i`.

Simplify using `only [Finset.sum_apply, Subring.smul_def, Pi.smul_apply, Pi.add_apply, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `∑ j, (e • γ.val.map φ + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) i j * w j = _`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hef]`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, Matrix.one_apply, Pi.single_apply] <;> ring`.

Rewrite using `[hz']`. Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (add_mem ?_ ?_)` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h3 j, rfl⟩)`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h1 j, rfl⟩)`.
-/
theorem exists_glued {O E R : Type} [CommRing O] [Field E] [Algebra O E] [CommRing R] (φ : E →+* R) (S : Subring R)
    (hO : ∀ o : O, φ (algebraMap O E o) ∈ S) {n : ℕ} (L : Submodule O (Fin n → E)) (N k : ℕ) (γ : GL (Fin n) E)
    (h1 : ∀ j, (N : E) • (Pi.single j 1 : Fin n → E) ∈ L)
    (h2 : ∀ x ∈ L, ∀ i, ∃ o : O, (N : E) * x i = algebraMap O E o)
    (h3 : ∀ j, (fun i => γ.val i j) ∈ L)
    (h4 : ∀ x ∈ L, ∀ i, ∃ o : O, (k : E) * ((γ⁻¹).val *ᵥ x) i = algebraMap O E o)
    (e f u : R) (he : e ∈ S) (hf : f ∈ S) (hu : u ∈ S) (hee : e * e = e) (hef : 1 - e = N * f)
    (heu : e * k * u = e) :
    ∃ β : GL (Fin n) R, ∀ z : Fin n → R,
      z ∈ Submodule.span S ((fun x : Fin n → E => fun i => φ (x i)) '' (L : Set (Fin n → E))) ↔
        ∀ i, ((β⁻¹).val *ᵥ z) i ∈ S := by
  classical
  have key : ∀ P Q : Matrix (Fin n) (Fin n) R, P * Q = 1 →
      (e • P + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (e • Q + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
    intro P Q h
    have a1 : e * (1 - e) = 0 := by rw [mul_sub, hee, mul_one, sub_self]
    have a2 : (1 - e) * e = 0 := by rw [mul_comm, a1]
    have a3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, a2, mul_one, sub_zero]
    simp only [add_mul, mul_add, smul_mul_smul_comm, h, hee, a1, a2, a3, zero_smul, add_zero, zero_add, mul_one]
    rw [← add_smul, add_sub_cancel, one_smul]
  have hPQ : γ.val.map φ * (γ⁻¹).val.map φ = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hQP : (γ⁻¹).val.map φ * γ.val.map φ = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero φ) (map_one φ)]
  let β : GL (Fin n) R := ⟨_, _, key _ _ hPQ, key _ _ hQP⟩
  refine ⟨β, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      intro i
      obtain ⟨o, ho⟩ := h2 x hx i
      obtain ⟨p, hp⟩ := h4 x hx i
      have hm : ((γ⁻¹).val.map φ *ᵥ fun i => φ (x i)) i = φ (((γ⁻¹).val *ᵥ x) i) :=
        (RingHom.map_mulVec φ _ x i).symm
      have ho' := congrArg φ ho
      have hp' := congrArg φ hp
      rw [map_mul, map_natCast] at ho' hp'
      have : ((β⁻¹).val *ᵥ fun i => φ (x i)) i = e * u * φ (algebraMap O E p) + f * φ (algebraMap O E o) := by
        change ((e • (γ⁻¹).val.map φ + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) *ᵥ fun i => φ (x i)) i = _
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply,
          Pi.smul_apply, Pi.smul_apply, hm, smul_eq_mul, smul_eq_mul, ← ho', ← hp', hef]
        linear_combination (-φ (((γ⁻¹).val *ᵥ x) i)) * heu
      rw [this]
      exact add_mem (mul_mem (mul_mem he hu) (hO p)) (mul_mem hf (hO o))
    | zero => intro i; rw [Matrix.mulVec_zero]; exact zero_mem _
    | add y w _ _ hy hw => intro i; rw [Matrix.mulVec_add]; exact add_mem (hy i) (hw i)
    | smul a y _ hy =>
      intro i
      rw [Subring.smul_def, Matrix.mulVec_smul]
      exact mul_mem a.2 (hy i)
  · have hz' : z = ∑ j, (⟨_, hz j⟩ : S) • ((⟨e, he⟩ : S) • (fun i => φ (γ.val i j)) +
        (⟨f, hf⟩ : S) • fun i => φ (((N : E) • (Pi.single j 1 : Fin n → E)) i)) := by
      have : z = β.val *ᵥ ((β⁻¹).val *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      conv_lhs => rw [this]
      generalize (β⁻¹).val *ᵥ z = w at hz
      funext i
      simp only [Finset.sum_apply, Subring.smul_def, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      change ∑ j, (e • γ.val.map φ + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) i j * w j = _
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hef]
      by_cases h : i = j <;> simp [h, Matrix.one_apply, Pi.single_apply] <;> ring
    rw [hz']
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (add_mem ?_ ?_)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h3 j, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h1 j, rfl⟩)

/- English proof (translation)
Take `⟨y, hy, h⟩` from `exists_integral_multiples ℤ ℚ s`. Use `⟨(y * y).toNat, by have := mul_self_pos.2 hy; omega, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩ : ∃ p : 𝓞 E, algebraMap (𝓞 E) E p = y • x` from `⟨⟨y • x, h x hx⟩, rfl⟩`. Use `⟨(y : 𝓞 E) * p, ?_⟩` and prove the remaining obligations. Establish `: (((y * y).toNat : ℕ) : E) = (y : E) * y`.

Establish `h0 : (((y * y).toNat : ℕ) : ℤ) = y * y` using `Int.toNat_of_nonneg (mul_self_nonneg y)`. Rewrite using `[← Int.cast_natCast, h0, Int.cast_mul]`. Rewrite using `[this, map_mul, map_intCast, hp, zsmul_eq_mul, mul_assoc]`.
-/
theorem exists_nat_multiples {E : Type} [Field E] [NumberField E] (s : Finset E) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ s, ∃ o : 𝓞 E, (N : E) * x = algebraMap (𝓞 E) E o := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨(y * y).toNat, by have := mul_self_pos.2 hy; omega, fun x hx => ?_⟩
  obtain ⟨p, hp⟩ : ∃ p : 𝓞 E, algebraMap (𝓞 E) E p = y • x := ⟨⟨y • x, h x hx⟩, rfl⟩
  refine ⟨(y : 𝓞 E) * p, ?_⟩
  have : (((y * y).toNat : ℕ) : E) = (y : E) * y := by
    have h0 : (((y * y).toNat : ℕ) : ℤ) = y * y := Int.toNat_of_nonneg (mul_self_nonneg y)
    rw [← Int.cast_natCast, h0, Int.cast_mul]
  rw [this, map_mul, map_intCast, hp, zsmul_eq_mul, mul_assoc]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CoordinateBasisBounds.main`. Consider the case `exact _root_.GlobalTheory.CoordinateBasisBounds.main`. Consider the case `(apply _root_.GlobalTheory.CoordinateBasisBounds.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CoordinateBasisBounds.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CoordinateBasisBounds.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CoordinateBasisBounds.main ..)`.
-/
theorem exists_level {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ (∀ j, (N : E) • (Pi.single j 1 : Fin n → E) ∈ L) ∧
      ∀ x ∈ L, ∀ i, ∃ o : 𝓞 E, (N : E) * x i = algebraMap (𝓞 E) E o := by
  first
  | exact @_root_.GlobalTheory.CoordinateBasisBounds.main
  | exact _root_.GlobalTheory.CoordinateBasisBounds.main
  | (apply _root_.GlobalTheory.CoordinateBasisBounds.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoordinateBasisBounds.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoordinateBasisBounds.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoordinateBasisBounds.main ..)

/- English proof (translation)
Establish `hS : GlobalTheory.PlaceInt.LocBasis.primeTo (𝓞 E) N ≤ nonZeroDivisors (𝓞 E)`. Introduce and unpack `_ ⟨k, hk, -, rfl⟩`. Conclude with `mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk)`. Set `A` to `Localization.subalgebra E (GlobalTheory.PlaceInt.LocBasis.primeTo (𝓞 E) N) hS`. Establish `: IsPrincipalIdealRing A` using `GlobalTheory.PlaceInt.LocBasis.isPrincipalIdealRing_loc E N hN hS A`.

Take `⟨⟨_, k, hk0, hk, rfl⟩, b, hli, hb, hw⟩` from `GlobalTheory.PlaceInt.LocBasis.exists_basis_up_to (A := A) (GlobalTheory.PlaceInt.LocBasis.primeTo (𝓞 E) N) L hfg hsp`. Set `g : Matrix (Fin n) (Fin n) E` to `Matrix.of fun i j => b j i`. Establish `hunit : IsUnit g` using `Matrix.linearIndependent_cols_iff_isUnit.1 hli`. Use `⟨k, hunit.unit, hk, hb, fun x hx i => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 (hw x hx)`.

Use `⟨a i, ?_⟩` and prove the remaining obligations. Establish `h1 : hunit.unit.val *ᵥ (fun j => algebraMap (𝓞 E) E (a j)) = (k : E) • x`. Establish `: (k : E) • x = (k : 𝓞 E) • x` using `by rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`. Rewrite using `[this]`. Use `Eq.trans ?_ ha` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `only [IsUnit.unit_spec, Matrix.mulVec, dotProduct, g, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`. Establish `h2` using `congrArg (fun w => ((hunit.unit⁻¹).val *ᵥ w) i) h1`.

Simplify using `only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h2`. Conclude with `h2.symm`.
-/
theorem exists_gl {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (N : ℕ) (hN : 0 < N) :
    ∃ (k : ℕ) (γ : GL (Fin n) E), Nat.Coprime k N ∧ (∀ j, (fun i => γ.val i j) ∈ L) ∧
      ∀ x ∈ L, ∀ i, ∃ o : 𝓞 E, (k : E) * ((γ⁻¹).val *ᵥ x) i = algebraMap (𝓞 E) E o := by
  classical
  have hS : GlobalTheory.PlaceInt.LocBasis.primeTo (𝓞 E) N ≤ nonZeroDivisors (𝓞 E) := by
    rintro _ ⟨k, hk, -, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk)
  let A := Localization.subalgebra E (GlobalTheory.PlaceInt.LocBasis.primeTo (𝓞 E) N) hS
  have : IsPrincipalIdealRing A := GlobalTheory.PlaceInt.LocBasis.isPrincipalIdealRing_loc E N hN hS A
  obtain ⟨⟨_, k, hk0, hk, rfl⟩, b, hli, hb, hw⟩ :=
    GlobalTheory.PlaceInt.LocBasis.exists_basis_up_to (A := A) (GlobalTheory.PlaceInt.LocBasis.primeTo (𝓞 E) N) L hfg hsp
  let g : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => b j i
  have hunit : IsUnit g := Matrix.linearIndependent_cols_iff_isUnit.1 hli
  refine ⟨k, hunit.unit, hk, hb, fun x hx i => ?_⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hw x hx)
  refine ⟨a i, ?_⟩
  have h1 : hunit.unit.val *ᵥ (fun j => algebraMap (𝓞 E) E (a j)) = (k : E) • x := by
    have : (k : E) • x = (k : 𝓞 E) • x := by rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [this]
    refine Eq.trans ?_ ha
    funext i
    simp only [IsUnit.unit_spec, Matrix.mulVec, dotProduct, g, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have h2 := congrArg (fun w => ((hunit.unit⁻¹).val *ᵥ w) i) h1
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_smul, Pi.smul_apply,
    smul_eq_mul] at h2
  exact h2.symm

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inl ⟨⟨_, o, rfl⟩, rfl⟩)`.
-/
theorem left_mem (o : 𝓞 E) :
    (algebraMap (𝓞 E) E o) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) ∈ Formalism.L2.Herm.intAf F E :=
  Subring.subset_closure (Or.inl ⟨⟨_, o, rfl⟩, rfl⟩)

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)`.
-/
theorem right_mem (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

/- English proof (translation)
Use `set c := Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E with hc`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`.

Take `⟨a, ha, x, hx, rfl⟩` from `hy`. Use `Submodule.smul_mem _ (⟨_, right_mem F E a ha⟩ : Formalism.L2.Herm.intAf F E) (Submodule.subset_span (R := Formalism.L2.Herm.intAf F E) (Set.mem_image_of_mem (fun x : Fin n → E => fun i => (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F) (x i)) hx) …` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[hc, Subring.smul_def]`.

Consider the case `zero`. Use `Submodule.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Consider the case `add y w _ _ hy hw`.

Use `Submodule.add_mem _ hy hw using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Consider the case `neg y _ hy`. Use `Submodule.neg_mem _ hy using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `gen : ∀ r : GlobalTheory.AdLat.RA F E, (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x ∈ L, r • (fun i => a ⊗ₜ[F] x i) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) → ∀ w ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), r • w ∈ GlobalTheory.AdLa …`. Introduce `r hr w hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`.

Consider the case `mem y hy`. Take `⟨a, ha, x, hx, rfl⟩` from `hy`. Conclude with `hr a ha x hx`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`.

Consider the case `add y w _ _ hy hw => rw [smul_add]`. Conclude with `add_mem hy hw`. Consider the case `neg y _ hy => rw [smul_neg]`. Conclude with `neg_mem hy`. Establish `stab : ∀ s ∈ Formalism.L2.Herm.intAf F E, ∀ w ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), c.symm s • w ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E))`.

Introduce `s hs`. Proceed by induction on `hs using Subring.closure_induction with`. Consider the case `mem s hs`. Break down `hs with ⟨⟨_, o, rfl⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩` into its components or cases. Use `gen _ fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, o • x, L.smul_mem o hx, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `[hc, Algebra.smul_def]`. Use `gen _ fun a ha x hx => AddSubgroup.subset_closure ⟨b * a, fun v => (v.adicCompletionIntegers F).mul_mem _ _ (hb v) (ha v), x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[hc]`.

Consider the case `zero => intro w _`. Rewrite using `[map_zero, zero_smul]`. Conclude with `zero_mem _`. Consider the case `one => intro w hw`. Rewrite using `[map_one, one_smul]`.

Conclude with `hw`. Consider the case `add s t _ _ hs ht => intro w hw`. Rewrite using `[map_add, add_smul]`. Conclude with `add_mem (hs w hw) (ht w hw)`. Consider the case `neg s _ hs => intro w hw`.

Rewrite using `[map_neg, neg_smul]`. Conclude with `neg_mem (hs w hw)`. Consider the case `mul s t _ _ hs ht => intro w hw`. Rewrite using `[map_mul, mul_smul]`. Conclude with `hs _ (ht w hw)`.

Establish `main : ∀ y ∈ Submodule.span (Formalism.L2.Herm.intAf F E) ((fun x : Fin n → E => fun i => (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F) (x i)) '' (L : Set (Fin n → E))), (fun i => c.symm (y i)) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E))`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`.

Conclude with `AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩`. Consider the case `zero`. Use `AddSubgroup.zero_mem _ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Consider the case `add y w _ _ hy hw`. Use `AddSubgroup.add_mem _ hy hw using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Consider the case `smul s y _ hy`.

Use `stab s.1 s.2 _ hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[Subring.smul_def]`. Introduce `hz`. Simplify using `using main _ hz`.
-/
theorem mem_hat_iff {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → GlobalTheory.AdLat.RA F E) :
    z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (z i)) ∈
        Submodule.span (Formalism.L2.Herm.intAf F E)
          ((fun x : Fin n → E => fun i =>
            (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F) (x i)) ''
            (L : Set (Fin n → E))) := by
  set c := Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E with hc
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have := Submodule.smul_mem _ (⟨_, right_mem F E a ha⟩ : Formalism.L2.Herm.intAf F E)
        (Submodule.subset_span (R := Formalism.L2.Herm.intAf F E) (Set.mem_image_of_mem (fun x : Fin n → E => fun i =>
            (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F) (x i)) hx))
      convert this using 1
      funext i
      simp [hc, Subring.smul_def]
    | zero =>
      convert Submodule.zero_mem _ using 1
      funext i; simp
    | add y w _ _ hy hw =>
      convert Submodule.add_mem _ hy hw using 1
      funext i; simp
    | neg y _ hy =>
      convert Submodule.neg_mem _ hy using 1
      funext i; simp
  · have gen : ∀ r : GlobalTheory.AdLat.RA F E, (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) →
        ∀ x ∈ L, r • (fun i => a ⊗ₜ[F] x i) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) →
        ∀ w ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), r • w ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
      intro r hr w hw
      induction hw using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hy
        exact hr a ha x hx
      | zero => rw [smul_zero]; exact zero_mem _
      | add y w _ _ hy hw => rw [smul_add]; exact add_mem hy hw
      | neg y _ hy => rw [smul_neg]; exact neg_mem hy
    have stab : ∀ s ∈ Formalism.L2.Herm.intAf F E, ∀ w ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
        c.symm s • w ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
      intro s hs
      induction hs using Subring.closure_induction with
      | mem s hs =>
        rcases hs with ⟨⟨_, o, rfl⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
        · refine gen _ fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, o • x, L.smul_mem o hx, ?_⟩
          funext i
          simp [hc, Algebra.smul_def]
        · refine gen _ fun a ha x hx => AddSubgroup.subset_closure
            ⟨b * a, fun v => (v.adicCompletionIntegers F).mul_mem _ _ (hb v) (ha v), x, hx, ?_⟩
          funext i
          simp [hc]
      | zero => intro w _; rw [map_zero, zero_smul]; exact zero_mem _
      | one => intro w hw; rw [map_one, one_smul]; exact hw
      | add s t _ _ hs ht => intro w hw; rw [map_add, add_smul]; exact add_mem (hs w hw) (ht w hw)
      | neg s _ hs => intro w hw; rw [map_neg, neg_smul]; exact neg_mem (hs w hw)
      | mul s t _ _ hs ht => intro w hw; rw [map_mul, mul_smul]; exact hs _ (ht w hw)
    have main : ∀ y ∈ Submodule.span (Formalism.L2.Herm.intAf F E)
          ((fun x : Fin n → E => fun i =>
            (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F) (x i)) ''
            (L : Set (Fin n → E))), (fun i => c.symm (y i)) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩
      | zero =>
        convert AddSubgroup.zero_mem _ using 1
        funext i; simp
      | add y w _ _ hy hw =>
        convert AddSubgroup.add_mem _ hy hw using 1
        funext i; simp
      | smul s y _ hy =>
        convert stab s.1 s.2 _ hy using 1
        funext i; simp [Subring.smul_def]
    intro hz
    simpa using main _ hz

/- English proof (translation)
Take `⟨N, hN, h1, h2⟩` from `exists_level L hfg hsp`. Take `⟨k, γ, hk, h3, h4⟩` from `exists_gl L hfg hsp N hN`. Take `⟨e, f, hee, hef, hun⟩` from `GlobalTheory.AdLat.RootNear.exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) N`. Take `⟨a, b, hab⟩ : IsCoprime (k : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) N` from `Nat.Coprime.cast hk`. Take `⟨w, hw⟩` from `(hun (-b)).exists_right_inv`.

Establish `heu : e * k * (a * w) = e`. Take the linear combination `e * w * hab + e * hw + N * b * w * hee`. Set `ψ : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F` to `(Algebra.TensorProduct.includeRight : FiniteAdeleRing (𝓞 F) F →ₐ[F] _).toRingHom.comp (GlobalTheory.AdLat.RootNear.incl F)`. Establish `hψ : ∀ t, ψ t ∈ Formalism.L2.Herm.intAf F E` using `fun t => right_mem F E (GlobalTheory.AdLat.RootNear.incl F t) fun v => (t v).2`. Take `⟨β, hβ⟩` from `exists_glued (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F) (Formalism.L2.Herm.intAf F E) (left_mem F E) L N k γ h1 h2 h3 h4 (ψ e) (ψ f) (ψ (a * w)) (hψ _) (hψ _) (hψ _) (by rw [← map_mul, hee]) (by rw [← map_natCast ψ, ← map_mul, ← hef, map_sub …`.

Conclude with `⟨β, fun z => (mem_hat_iff F E L z).trans (hβ _)⟩`.
-/
theorem exists_basis_hat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), ∀ z : Fin n → GlobalTheory.AdLat.RA F E,
      z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) ↔
        ∀ i, ((β⁻¹).val *ᵥ fun a => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (z a)) i ∈
          Formalism.L2.Herm.intAf F E := by
  obtain ⟨N, hN, h1, h2⟩ := exists_level L hfg hsp
  obtain ⟨k, γ, hk, h3, h4⟩ := exists_gl L hfg hsp N hN
  obtain ⟨e, f, hee, hef, hun⟩ :=
    GlobalTheory.AdLat.RootNear.exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) N
  obtain ⟨a, b, hab⟩ : IsCoprime (k : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) N :=
    Nat.Coprime.cast hk
  obtain ⟨w, hw⟩ := (hun (-b)).exists_right_inv
  have heu : e * k * (a * w) = e := by
    linear_combination e * w * hab + e * hw + N * b * w * hee
  let ψ : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
    (Algebra.TensorProduct.includeRight : FiniteAdeleRing (𝓞 F) F →ₐ[F] _).toRingHom.comp
      (GlobalTheory.AdLat.RootNear.incl F)
  have hψ : ∀ t, ψ t ∈ Formalism.L2.Herm.intAf F E := fun t =>
    right_mem F E (GlobalTheory.AdLat.RootNear.incl F t) fun v => (t v).2
  obtain ⟨β, hβ⟩ := exists_glued
    (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F) (Formalism.L2.Herm.intAf F E)
    (left_mem F E) L N k γ h1 h2 h3 h4 (ψ e) (ψ f) (ψ (a * w)) (hψ _) (hψ _) (hψ _)
    (by rw [← map_mul, hee]) (by rw [← map_natCast ψ, ← map_mul, ← hef, map_sub, map_one])
    (by rw [← map_natCast ψ, ← map_mul, ← map_mul, heu])
  exact ⟨β, fun z => (mem_hat_iff F E L z).trans (hβ _)⟩

end GlobalTheory.LatAdelicBasis

namespace GlobalTheory.LatAdelicBasis

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D V r hr`. Substitute `hr` using the available equality. Take `⟨h, -, hfg, hsp, -⟩` from `GlobalTheory.Member.latHat_eq_hat_and_gram D V`. Take `⟨β, hβ⟩` from `exists_basis_hat D.host.F D.host.E _ hfg hsp`. Use `⟨β, fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[h]`. Conclude with `hβ z`.
-/
theorem exists_isLatBasis : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r),
    ∃ β : GL (Fin r) (EAf D), LatticeBasisLifts.IsLatBasis V hr β := by
  intro D V r hr
  subst hr
  obtain ⟨h, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨β, hβ⟩ := exists_basis_hat D.host.F D.host.E _ hfg hsp
  refine ⟨β, fun z => ?_⟩
  rw [h]
  exact hβ z

end GlobalTheory.LatAdelicBasis

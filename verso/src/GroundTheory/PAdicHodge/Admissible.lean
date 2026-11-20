import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open TensorProduct Module

section Defs

variable (G F B : Type*) [Group G] [Field F] [CommRing B] [Algebra F B]
  [MulSemiringAction G B] [SMulCommClass G F B]

abbrev invariantRing : Subalgebra F B := FixedPoints.subalgebra F B G

variable {G F B} in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_invariantRing {b : B} : b ∈ invariantRing G F B ↔ ∀ g : G, g • b = b := Iff.rfl

structure IsRegular [IsDomain B] : Prop where

  image_fixedPoints :
    letI := IsFractionRing.mulSemiringAction G B (FractionRing B)
    algebraMap B (FractionRing B) '' MulAction.fixedPoints G B =
      MulAction.fixedPoints G (FractionRing B)

  isUnit_of_mem_span : ∀ b : B, b ≠ 0 → (∀ g : G, g • b ∈ Submodule.span F {b}) → IsUnit b

variable {G F} {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)

noncomputable abbrev baseChangeRep : Representation F G (B ⊗[F] V) :=
  (Representation.ofDistribMulAction F G B).tprod ρ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem baseChangeRep_tmul (g : G) (b : B) (v : V) :
    baseChangeRep B ρ g (b ⊗ₜ v) = (g • b) ⊗ₜ ρ g v := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c v`. Rewrite using `[TensorProduct.smul_tmul', baseChangeRep_tmul, baseChangeRep_tmul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, smul_mul']`. Consider the case `add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]`.
-/
theorem baseChangeRep_smul (g : G) (b : B) (x : B ⊗[F] V) :
    baseChangeRep B ρ g (b • x) = (g • b) • baseChangeRep B ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [TensorProduct.smul_tmul', baseChangeRep_tmul, baseChangeRep_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, smul_mul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/- English proof (translation)
The claim follows from `(algebraMap_smul B e x).symm`.
-/
theorem invariantRing_smul_eq (e : invariantRing G F B) (x : B ⊗[F] V) :
    e • x = (e : B) • x :=
  (algebraMap_smul B e x).symm

def DB : Submodule (invariantRing G F B) (B ⊗[F] V) where
  carrier := {x | ∀ g : G, baseChangeRep B ρ g x = x}
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  zero_mem' g := map_zero _
  smul_mem' e x hx g := by
    rw [invariantRing_smul_eq, baseChangeRep_smul, hx g, (mem_invariantRing.1 e.2) g]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_DB {x : B ⊗[F] V} : x ∈ DB B ρ ↔ ∀ g : G, baseChangeRep B ρ g x = x := Iff.rfl

noncomputable def comparison : B ⊗[invariantRing G F B] DB B ρ →ₗ[B] B ⊗[F] V :=
  (DB B ρ).subtype.liftBaseChange B

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem comparison_tmul (b : B) (d : DB B ρ) :
    comparison B ρ (b ⊗ₜ d) = b • (d : B ⊗[F] V) := rfl

def IsAdmissible : Prop := finrank (invariantRing G F B) (DB B ρ) = finrank F V

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b w`. Rewrite using `[baseChangeRep_tmul]`. Simplify using `only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, smul_mul', smul_algebraMap]`.

Rewrite using `[← LinearMap.toMatrix_mulVec_repr v v (ρ g) w]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy`.

Simplify using `only [map_add, Finsupp.add_apply, hx, hy, smul_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem repr_baseChangeRep {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Basis ι F V) (g : G)
    (x : B ⊗[F] V) (k : ι) :
    (Algebra.TensorProduct.basis B v).repr (baseChangeRep B ρ g x) k =
      ∑ i, algebraMap F B (LinearMap.toMatrix v v (ρ g) k i) *
        (g • (Algebra.TensorProduct.basis B v).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b w =>
    rw [baseChangeRep_tmul]
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, smul_mul', smul_algebraMap]
    rw [← LinearMap.toMatrix_mulVec_repr v v (ρ g) w]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy, smul_add, mul_add, Finset.sum_add_distrib]

end Defs

namespace IsRegular

variable {G F B : Type*} [Group G] [Field F] [CommRing B] [IsDomain B] [Algebra F B]
  [MulSemiringAction G B] [SMulCommClass G F B] (h : IsRegular G F B)
include h

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 1, zero_ne_one⟩ mul_comm := mul_comm mul_inv_cancel := fun {e} he => by have he' : (e : B) ≠ 0 := fun h0 => he (Subtype.ext h0) have hfix := mem_invariantRing.1 e.2 obtain ⟨u, hu⟩ := h.isUnit_of_mem_span (e : B) he' fun g => by rw [hfix g]; exact Submodule.mem_span_singleton_ …`.
-/
theorem isField : IsField (invariantRing G F B) where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel := fun {e} he => by
    have he' : (e : B) ≠ 0 := fun h0 => he (Subtype.ext h0)
    have hfix := mem_invariantRing.1 e.2
    obtain ⟨u, hu⟩ := h.isUnit_of_mem_span (e : B) he' fun g => by
      rw [hfix g]; exact Submodule.mem_span_singleton_self _
    have hinv : ∀ g : G, g • (↑u⁻¹ : B) = ↑u⁻¹ := by
      intro g
      have h1 : (e : B) * (g • (↑u⁻¹ : B)) = 1 := by
        have := congrArg (g • ·) u.mul_inv
        simp only [smul_mul', smul_one] at this
        rwa [hu, hfix g] at this
      calc g • (↑u⁻¹ : B) = (↑u⁻¹ * (e : B)) * g • ↑u⁻¹ := by rw [← hu, u.inv_mul, one_mul]
        _ = ↑u⁻¹ := by rw [mul_assoc, h1, mul_one]
    refine ⟨⟨(↑u⁻¹ : B), mem_invariantRing.2 hinv⟩, Subtype.ext ?_⟩
    change (e : B) * ↑u⁻¹ = 1
    rw [← hu, u.mul_inv]

noncomputable abbrev field : Field (invariantRing G F B) where
  toCommRing := inferInstance
  __ := h.isField.toSemifield
  qsmul := _
  qsmul_def := fun _ _ => rfl

/- English proof (translation)
Use `letI := IsFractionRing.mulSemiringAction G B (FractionRing B)`. Establish `hinj` using `IsFractionRing.injective B (FractionRing B)`. Establish `hmap : ∀ (g : G) (b : B), g • algebraMap B (FractionRing B) b = algebraMap B (FractionRing B) (g • b)` using `fun g b => IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b`. Establish `hc₀' : algebraMap B (FractionRing B) c₀ ≠ 0` using `(map_ne_zero_iff _ hinj).2 hc₀`. Establish `hx : algebraMap B (FractionRing B) c / algebraMap B (FractionRing B) c₀ ∈ MulAction.fixedPoints G (FractionRing B)`.

Introduce `g`. Establish `hgc₀ : g • c₀ ≠ 0`. Introduce `h0`. Apply `hc₀` to reduce the goal to its premises. Simplify using `using congrArg (g⁻¹ • ·) h0`.

Establish `hgc₀' : algebraMap B (FractionRing B) (g • c₀) ≠ 0` using `(map_ne_zero_iff _ hinj).2 hgc₀`. Rewrite using `[smul_div₀', hmap, hmap, div_eq_div_iff hgc₀' hc₀', ← map_mul, ← map_mul]`. Use `congr 1`. Take the linear combination `-(hg g)`. Establish `himg : algebraMap B (FractionRing B) '' MulAction.fixedPoints G B = MulAction.fixedPoints G (FractionRing B)` using `h.image_fixedPoints`.

Rewrite `hx` using `[← himg]`. Take `⟨e, he, hxe⟩` from `hx`. Use `⟨e, he, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hxe, div_mul_cancel₀ _ hc₀']`.
-/
theorem exists_eq_mul {c₀ c : B} (hc₀ : c₀ ≠ 0)
    (hg : ∀ g : G, (g • c₀) * c = c₀ * (g • c)) :
    ∃ e ∈ invariantRing G F B, c = e * c₀ := by
  letI := IsFractionRing.mulSemiringAction G B (FractionRing B)
  have hinj := IsFractionRing.injective B (FractionRing B)
  have hmap : ∀ (g : G) (b : B), g • algebraMap B (FractionRing B) b =
      algebraMap B (FractionRing B) (g • b) := fun g b =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
  have hc₀' : algebraMap B (FractionRing B) c₀ ≠ 0 := (map_ne_zero_iff _ hinj).2 hc₀
  have hx : algebraMap B (FractionRing B) c / algebraMap B (FractionRing B) c₀ ∈
      MulAction.fixedPoints G (FractionRing B) := by
    intro g
    have hgc₀ : g • c₀ ≠ 0 := by
      intro h0
      apply hc₀
      simpa using congrArg (g⁻¹ • ·) h0
    have hgc₀' : algebraMap B (FractionRing B) (g • c₀) ≠ 0 := (map_ne_zero_iff _ hinj).2 hgc₀
    rw [smul_div₀', hmap, hmap, div_eq_div_iff hgc₀' hc₀', ← map_mul, ← map_mul]
    congr 1
    linear_combination -(hg g)
  have himg : algebraMap B (FractionRing B) '' MulAction.fixedPoints G B =
      MulAction.fixedPoints G (FractionRing B) := h.image_fixedPoints
  rw [← himg] at hx
  obtain ⟨e, he, hxe⟩ := hx
  refine ⟨e, he, hinj ?_⟩
  rw [map_mul, hxe, div_mul_cancel₀ _ hc₀']

variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s`. Proceed by induction on `s using Finset.strongInduction with`. Consider the case `H s ih`. Introduce `c hc`.

Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨i₀, hi₀, hci₀⟩` from `hne`. Establish `hgsum : ∀ g : G, ∑ i ∈ s, (g • c i) • (d i : B ⊗[F] V) = 0`. Introduce `g`.

Use `congrArg (baseChangeRep B ρ g) hc` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[baseChangeRep_smul, (mem_DB B ρ).1 (d i).2 g]`.

Establish `hrel : ∀ g : G, ∀ i ∈ s, (g • c i₀) * c i = c i₀ * (g • c i)`. Introduce `g`. Establish `e1 : ∑ i ∈ s, ((g • c i₀) * c i - c i₀ * (g • c i)) • (d i : B ⊗[F] V) = (g • c i₀) • ∑ i ∈ s, c i • (d i : B ⊗[F] V) - c i₀ • ∑ i ∈ s, (g • c i) • (d i : B ⊗[F] V)`. Rewrite using `[Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by module`.

Establish `hsub : ∑ i ∈ s.erase i₀, ((g • c i₀) * c i - c i₀ * (g • c i)) • (d i : B ⊗[F] V) = 0`. Rewrite using `[Finset.sum_erase _ (by rw [mul_comm, sub_self, zero_smul]), e1, hc, hgsum g, smul_zero, smul_zero, sub_zero]`. Use `ih (s.erase i₀) (Finset.erase_ssubset hi₀) _ hsub` as an intermediate fact. Introduce `i hi`. Distinguish the cases in `hii : i = i₀`.

Substitute `hii` using the available equality. Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.1 (this i (Finset.mem_erase.2 ⟨hii, hi⟩))`. Use `choose! e he hce using fun i (hi : i ∈ s) => h.exists_eq_mul hci₀ fun g => hrel g i hi`. Set `e' : ι → invariantRing G F B` to `fun i => if hi : i ∈ s then ⟨e i, he i hi⟩ else 0`.

Establish `he' : ∀ i ∈ s, ((e' i : invariantRing G F B) : B) = e i` using `fun i hi => by simp [e', hi]`. Establish `hsumB : ∑ i ∈ s, ((e' i : invariantRing G F B) : B) • (d i : B ⊗[F] V) = 0`. Apply `(smul_right_injective (B ⊗[F] V) hci₀)` to reduce the goal to its premises. Simplify using `only [smul_zero, Finset.smul_sum]`. Rewrite using `[← hc]`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[← mul_smul, he' i hi, hce i hi, mul_comm]`. Establish `hsumE : ∑ i ∈ s, e' i • d i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, invariantRing_smul_eq, Submodule.coe_zero]`.

Conclude with `hsumB`. Use `linearIndependent_iff'ₛ.1 hd s e' 0 (by rw [hsumE]; exact (Finset.sum_eq_zero fun i _ => zero_smul _ _).symm) i₀ hi₀` as an intermediate fact. Apply `hci₀` to reduce the goal to its premises. Rewrite using `[hce i₀ hi₀, ← he' i₀ hi₀, this]`. Simplify using the standard rewrite rules.
-/
theorem linearIndependent {ι : Type*} {d : ι → DB B ρ}
    (hd : LinearIndependent (invariantRing G F B) d) :
    LinearIndependent B (fun i => (d i : B ⊗[F] V)) := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀, hci₀⟩ := hne
  have hgsum : ∀ g : G, ∑ i ∈ s, (g • c i) • (d i : B ⊗[F] V) = 0 := by
    intro g
    have := congrArg (baseChangeRep B ρ g) hc
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [baseChangeRep_smul, (mem_DB B ρ).1 (d i).2 g]
  have hrel : ∀ g : G, ∀ i ∈ s, (g • c i₀) * c i = c i₀ * (g • c i) := by
    intro g
    have e1 : ∑ i ∈ s, ((g • c i₀) * c i - c i₀ * (g • c i)) • (d i : B ⊗[F] V) =
        (g • c i₀) • ∑ i ∈ s, c i • (d i : B ⊗[F] V) -
          c i₀ • ∑ i ∈ s, (g • c i) • (d i : B ⊗[F] V) := by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by module
    have hsub : ∑ i ∈ s.erase i₀, ((g • c i₀) * c i - c i₀ * (g • c i)) •
        (d i : B ⊗[F] V) = 0 := by
      rw [Finset.sum_erase _ (by rw [mul_comm, sub_self, zero_smul]), e1, hc, hgsum g, smul_zero,
        smul_zero, sub_zero]
    have := ih (s.erase i₀) (Finset.erase_ssubset hi₀) _ hsub
    intro i hi
    by_cases hii : i = i₀
    · subst hii; ring
    · exact sub_eq_zero.1 (this i (Finset.mem_erase.2 ⟨hii, hi⟩))
  choose! e he hce using fun i (hi : i ∈ s) => h.exists_eq_mul hci₀ fun g => hrel g i hi
  let e' : ι → invariantRing G F B := fun i => if hi : i ∈ s then ⟨e i, he i hi⟩ else 0
  have he' : ∀ i ∈ s, ((e' i : invariantRing G F B) : B) = e i := fun i hi => by simp [e', hi]
  have hsumB : ∑ i ∈ s, ((e' i : invariantRing G F B) : B) • (d i : B ⊗[F] V) = 0 := by
    apply (smul_right_injective (B ⊗[F] V) hci₀)
    simp only [smul_zero, Finset.smul_sum]
    rw [← hc]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← mul_smul, he' i hi, hce i hi, mul_comm]
  have hsumE : ∑ i ∈ s, e' i • d i = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, invariantRing_smul_eq, Submodule.coe_zero]
    exact hsumB
  have := linearIndependent_iff'ₛ.1 hd s e' 0
    (by rw [hsumE]; exact (Finset.sum_eq_zero fun i _ => zero_smul _ _).symm) i₀ hi₀
  apply hci₀
  rw [hce i₀ hi₀, ← he' i₀ hi₀, this]
  simp

/- English proof (translation)
Use `letI := h.field`. Conclude with `Module.Free.of_divisionRing (invariantRing G F B) (DB B ρ)`.
-/
theorem free : Module.Free (invariantRing G F B) (DB B ρ) := by
  letI := h.field
  exact Module.Free.of_divisionRing (invariantRing G F B) (DB B ρ)

/- English proof (translation)
Use `letI := h.field`. Use `haveI := h.free ρ`. Establish `key : ∀ s : Finset (DB B ρ), LinearIndependent (invariantRing G F B) (fun i : s => (i : DB B ρ)) → s.card ≤ finrank F V`. Introduce `s hs`. Use `(h.linearIndependent ρ hs).fintype_card_le_finrank` as an intermediate fact.

Rewrite `this` using `[Module.finrank_baseChange, Fintype.card_coe]`. Then use the resulting hypothesis. Establish `hrk` using `rank_le key`. Conclude with `⟨Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt hrk Cardinal.natCast_lt_aleph0), finrank_le_of_rank_le hrk⟩`.
-/
theorem finite_and_finrank_le [FiniteDimensional F V] :
    Module.Finite (invariantRing G F B) (DB B ρ) ∧
      finrank (invariantRing G F B) (DB B ρ) ≤ finrank F V := by
  letI := h.field
  haveI := h.free ρ
  have key : ∀ s : Finset (DB B ρ),
      LinearIndependent (invariantRing G F B) (fun i : s => (i : DB B ρ)) →
        s.card ≤ finrank F V := by
    intro s hs
    have := (h.linearIndependent ρ hs).fintype_card_le_finrank
    rwa [Module.finrank_baseChange, Fintype.card_coe] at this
  have hrk := rank_le key
  exact ⟨Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt hrk Cardinal.natCast_lt_aleph0),
    finrank_le_of_rank_le hrk⟩

/- English proof (translation)
The claim follows from `(h.finite_and_finrank_le ρ).1`.
-/
theorem finite [FiniteDimensional F V] : Module.Finite (invariantRing G F B) (DB B ρ) :=
  (h.finite_and_finrank_le ρ).1

/- English proof (translation)
The claim follows from `(h.finite_and_finrank_le ρ).2`.
-/
theorem finrank_le [FiniteDimensional F V] :
    finrank (invariantRing G F B) (DB B ρ) ≤ finrank F V :=
  (h.finite_and_finrank_le ρ).2

/- English proof (translation)
Use `letI := h.field`. Use `haveI := h.free ρ`. Use `haveI := h.finite ρ`. Set `b` to `Module.Free.chooseBasis (invariantRing G F B) (DB B ρ)`. Set `bB` to `Algebra.TensorProduct.basis B b`.

Establish `hli` using `h.linearIndependent ρ b.linearIndependent`. Establish `hcomp : comparison B ρ = (Finsupp.linearCombination B (fun i => (b i : B ⊗[F] V))) ∘ₗ bB.repr.toLinearMap`. Use `bB.ext fun i => ?_` and prove the remaining obligations. Simplify using `[bB, comparison_tmul]`. Introduce `x y hxy`.

Rewrite `hxy` using `[hcomp]`. Conclude with `bB.repr.injective (hli hxy)`.
-/
theorem comparison_injective [FiniteDimensional F V] : Function.Injective (comparison B ρ) := by
  letI := h.field
  haveI := h.free ρ
  haveI := h.finite ρ
  let b := Module.Free.chooseBasis (invariantRing G F B) (DB B ρ)
  let bB := Algebra.TensorProduct.basis B b
  have hli := h.linearIndependent ρ b.linearIndependent
  have hcomp : comparison B ρ = (Finsupp.linearCombination B (fun i => (b i : B ⊗[F] V))) ∘ₗ
      bB.repr.toLinearMap := by
    refine bB.ext fun i => ?_
    simp [bB, comparison_tmul]
  intro x y hxy
  rw [hcomp] at hxy
  exact bB.repr.injective (hli hxy)

/- English proof (translation)
Use `letI := h.field`. Use `haveI := h.free ρ`. Use `haveI := h.finite ρ`. Set `b : Basis (Fin (finrank F V)) (invariantRing G F B) (DB B ρ)` to `Module.finBasisOfFinrankEq _ _ hadm`. Set `v : Basis (Fin (finrank F V)) F V` to `Module.finBasisOfFinrankEq F V rfl`.

Set `e` to `Algebra.TensorProduct.basis B v`. Set `x : Fin (finrank F V) → B ⊗[F] V` to `fun j => (b j : B ⊗[F] V)`. Establish `hli : LinearIndependent B x` using `h.linearIndependent ρ b.linearIndependent`. Set `a` to `e.toMatrix x`. Establish `hinv : ∀ g : G, a = (LinearMap.toMatrix v v (ρ g)).map (algebraMap F B) * a.map (g • ·)`.

Introduce `g`. Use extensionality with `k j`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [a, Basis.toMatrix_apply, Matrix.map_apply]`. Establish `hxj : x j = baseChangeRep B ρ g (x j)` using `((mem_DB B ρ).1 (b j).2 g).symm`.

Use `conv_lhs => rw [hxj]`. Conclude with `repr_baseChangeRep B ρ v g _ k`. Establish `hdet : ∀ g : G, a.det = algebraMap F B (LinearMap.toMatrix v v (ρ g)).det * (g • a.det)`. Introduce `g`. Establish `h1` using `(algebraMap F B).map_det (LinearMap.toMatrix v v (ρ g))`.

Establish `h2` using `(MulSemiringAction.toRingHom G B g).map_det a`. Rewrite `h1`, `h2` using `[RingHom.mapMatrix_apply]`. Use `conv_lhs => rw [hinv g]`. Rewrite using `[Matrix.det_mul, h1]`. Use `congr 1`.

Rewrite `h2` using `[MulSemiringAction.toRingHom_apply]`. Rewrite using `[h2]`. Both sides reduce to the same expression. Establish `hne : a.det ≠ 0`. Introduce `h0`.

Take `⟨w, hw, hw0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hw` to reduce the goal to its premises. Establish `hsum : ∑ j, w j • x j = 0`. Apply `e.repr.injective` to reduce the goal to its premises. Use extensionality with `k`.

Establish `hk` using `congrFun hw0 k`. Rewrite `hk` using `[Pi.zero_apply]`. Rewrite using `[map_zero, Finsupp.zero_apply, map_sum, ← hk]`. Simplify using `only [Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, a, Basis.toMatrix_apply, mul_comm]`. Conclude with `funext fun j => Fintype.linearIndependent_iff.1 hli w hsum j`.

Establish `hunit : IsUnit a.det` using `h.isUnit_of_mem_span _ hne fun g => by`. Rewrite using `[Submodule.mem_span_singleton]`. Use `⟨(LinearMap.toMatrix v v (ρ g⁻¹)).det, ?_⟩` and prove the remaining obligations. Use `congrArg (g • ·) (hdet g⁻¹)` as an intermediate fact. Simplify using `only [smul_mul', smul_algebraMap, smul_inv_smul] at this`.

Rewrite using `[Algebra.smul_def, ← this]`. Establish `hspan : Submodule.span B (Set.range x) = ⊤` using `((e.is_basis_iff_det).2 (by rwa [Basis.det_apply])).2`. Introduce `y`. Establish `hy : y ∈ Submodule.span B (Set.range x)` using `hspan ▸ Submodule.mem_top`. Establish `hle : Submodule.span B (Set.range x) ≤ LinearMap.range (comparison B ρ)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨1 ⊗ₜ b j, by simp [comparison_tmul, x]⟩`. Conclude with `hle hy`.
-/
theorem comparison_surjective [FiniteDimensional F V] (hadm : IsAdmissible B ρ) :
    Function.Surjective (comparison B ρ) := by
  classical
  letI := h.field
  haveI := h.free ρ
  haveI := h.finite ρ
  let b : Basis (Fin (finrank F V)) (invariantRing G F B) (DB B ρ) :=
    Module.finBasisOfFinrankEq _ _ hadm
  let v : Basis (Fin (finrank F V)) F V := Module.finBasisOfFinrankEq F V rfl
  let e := Algebra.TensorProduct.basis B v
  let x : Fin (finrank F V) → B ⊗[F] V := fun j => (b j : B ⊗[F] V)
  have hli : LinearIndependent B x := h.linearIndependent ρ b.linearIndependent
  let a := e.toMatrix x
  have hinv : ∀ g : G,
      a = (LinearMap.toMatrix v v (ρ g)).map (algebraMap F B) * a.map (g • ·) := by
    intro g
    ext k j
    rw [Matrix.mul_apply]
    simp only [a, Basis.toMatrix_apply, Matrix.map_apply]
    have hxj : x j = baseChangeRep B ρ g (x j) := ((mem_DB B ρ).1 (b j).2 g).symm
    conv_lhs => rw [hxj]
    exact repr_baseChangeRep B ρ v g _ k
  have hdet : ∀ g : G,
      a.det = algebraMap F B (LinearMap.toMatrix v v (ρ g)).det * (g • a.det) := by
    intro g
    have h1 := (algebraMap F B).map_det (LinearMap.toMatrix v v (ρ g))
    have h2 := (MulSemiringAction.toRingHom G B g).map_det a
    rw [RingHom.mapMatrix_apply] at h1 h2
    conv_lhs => rw [hinv g]
    rw [Matrix.det_mul, h1]
    congr 1
    rw [MulSemiringAction.toRingHom_apply] at h2
    rw [h2]
    rfl
  have hne : a.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw, hw0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hw
    have hsum : ∑ j, w j • x j = 0 := by
      apply e.repr.injective
      ext k
      have hk := congrFun hw0 k
      rw [Pi.zero_apply] at hk
      rw [map_zero, Finsupp.zero_apply, map_sum, ← hk]
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, map_smul, Finsupp.smul_apply,
        smul_eq_mul, Matrix.mulVec, dotProduct, a, Basis.toMatrix_apply, mul_comm]
    exact funext fun j => Fintype.linearIndependent_iff.1 hli w hsum j
  have hunit : IsUnit a.det := h.isUnit_of_mem_span _ hne fun g => by
    rw [Submodule.mem_span_singleton]
    refine ⟨(LinearMap.toMatrix v v (ρ g⁻¹)).det, ?_⟩
    have := congrArg (g • ·) (hdet g⁻¹)
    simp only [smul_mul', smul_algebraMap, smul_inv_smul] at this
    rw [Algebra.smul_def, ← this]
  have hspan : Submodule.span B (Set.range x) = ⊤ :=
    ((e.is_basis_iff_det).2 (by rwa [Basis.det_apply])).2
  intro y
  have hy : y ∈ Submodule.span B (Set.range x) := hspan ▸ Submodule.mem_top
  have hle : Submodule.span B (Set.range x) ≤ LinearMap.range (comparison B ρ) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨1 ⊗ₜ b j, by simp [comparison_tmul, x]⟩
  exact hle hy

/- English proof (translation)
Use `letI := h.field`. Use `haveI := h.free ρ`. Use `haveI := h.finite ρ`. Use `⟨fun hadm => ⟨h.comparison_injective ρ, h.comparison_surjective ρ hadm⟩, fun hbij => ?_⟩` and prove the remaining obligations. Use `(LinearEquiv.ofBijective (comparison B ρ) hbij).finrank_eq` as an intermediate fact.

Rewrite `this` using `[Module.finrank_baseChange, Module.finrank_baseChange]`. Then use the resulting hypothesis.
-/
theorem isAdmissible_iff_bijective [FiniteDimensional F V] :
    IsAdmissible B ρ ↔ Function.Bijective (comparison B ρ) := by
  letI := h.field
  haveI := h.free ρ
  haveI := h.finite ρ
  refine ⟨fun hadm => ⟨h.comparison_injective ρ, h.comparison_surjective ρ hadm⟩, fun hbij => ?_⟩
  have := (LinearEquiv.ofBijective (comparison B ρ) hbij).finrank_eq
  rwa [Module.finrank_baseChange, Module.finrank_baseChange] at this

/- English proof (translation)
Use `letI := h.field`. Use `haveI := h.free ρ`. Use `haveI := h.finite ρ`. Establish `hE : LinearIndependent (invariantRing G F B) x` using `LinearIndependent.of_comp (DB B ρ).subtype (hx.restrict_scalars' (invariantRing G F B))`. Conclude with `le_antisymm (h.finrank_le ρ) (hcard.trans hE.fintype_card_le_finrank)`.
-/
theorem isAdmissible_of_linearIndependent [FiniteDimensional F V] {ι : Type*} [Fintype ι]
    {x : ι → DB B ρ} (hx : LinearIndependent B (fun i => (x i : B ⊗[F] V)))
    (hcard : finrank F V ≤ Fintype.card ι) : IsAdmissible B ρ := by
  letI := h.field
  haveI := h.free ρ
  haveI := h.finite ρ
  have hE : LinearIndependent (invariantRing G F B) x :=
    LinearIndependent.of_comp (DB B ρ).subtype (hx.restrict_scalars' (invariantRing G F B))
  exact le_antisymm (h.finrank_le ρ) (hcard.trans hE.fintype_card_le_finrank)

noncomputable def basisOfIsAdmissible [FiniteDimensional F V] (hadm : IsAdmissible B ρ)
    {ι : Type*} [Fintype ι] (b : Basis ι (invariantRing G F B) (DB B ρ)) :
    Basis ι B (B ⊗[F] V) :=
  Basis.mk (h.linearIndependent ρ b.linearIndependent) (by
    have hsub : ∀ d : DB B ρ, (d : B ⊗[F] V) ∈
        Submodule.span B (Set.range fun i => (b i : B ⊗[F] V)) := by
      intro d
      rw [← b.sum_repr d, Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul, invariantRing_smul_eq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rintro y -
    obtain ⟨z, rfl⟩ := h.comparison_surjective ρ hadm y
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c d => rw [comparison_tmul]; exact Submodule.smul_mem _ c (hsub d)
    | add z z' hz hz' => rw [map_add]; exact Submodule.add_mem _ hz hz')

@[simp]
/- English proof (translation)
The claim follows from `Basis.coe_mk _ _`.
-/
theorem coe_basisOfIsAdmissible [FiniteDimensional F V] (hadm : IsAdmissible B ρ)
    {ι : Type*} [Fintype ι] (b : Basis ι (invariantRing G F B) (DB B ρ)) :
    ⇑(h.basisOfIsAdmissible ρ hadm b) = fun i => (b i : B ⊗[F] V) :=
  Basis.coe_mk _ _

end IsRegular

end GroundTheory.PAdicHodge

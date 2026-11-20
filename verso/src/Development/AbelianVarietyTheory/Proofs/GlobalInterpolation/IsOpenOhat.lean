import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DifferentiableAtChart

open NumberField IsDedekindDomain GlobalTheory.CuspNF Matrix Topology

namespace GlobalTheory.CuspNF.KprOpen

/- English proof (translation)
Set `P : Matrix n n S` to `Matrix.of fun i j => ⟨_, h1 i j⟩`. Set `Q : Matrix n n S` to `Matrix.of fun i j => ⟨_, h2 i j⟩`. Establish `hinj : Function.Injective (S.subtype.mapMatrix : Matrix n n S →+* Matrix n n A)` using `fun x y h => by`. Use extensionality with `i j`. Conclude with `congrFun (congrFun h i) j`.

Establish `hP : S.subtype.mapMatrix P = (g : Matrix n n A)` using `rfl`. Establish `hQ : S.subtype.mapMatrix Q = ((g⁻¹ : GL n A) : Matrix n n A)` using `rfl`. Set `u : GL n S` to `⟨P, Q, hinj (by rw [map_mul, hP, hQ, map_one, Units.mul_inv]), hinj (by rw [map_mul, hP, hQ, map_one, Units.inv_mul])⟩`. Use `⟨u, ?_, Units.ext rfl⟩` and prove the remaining obligations. Use `Units.ext ?_` and prove the remaining obligations.

Use extensionality with `i j`. Take `⟨y, hy, e⟩` from `h3 i j`. Establish `key : Ideal.Quotient.mk (Ideal.span {m}) (P i j) = Ideal.Quotient.mk (Ideal.span {m}) ((1 : Matrix n n S) i j)`. Use `Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨⟨y, hy⟩, Subtype.ext ?_⟩)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y * (m : A) = (g : Matrix n n A) i j - _`.

Rewrite using `[e]`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {m}) (P i j) = (1 : Matrix n n _) i j`. Rewrite using `[key]`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`.
-/
theorem mem_map_ker {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n] (S : Subring A) (m : S) (g : GL n A)
    (h1 : ∀ i j, (g : Matrix n n A) i j ∈ S) (h2 : ∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ S)
    (h3 : ∀ i j, ∃ y ∈ S, y * (m : A) = (g : Matrix n n A) i j - (1 : Matrix n n A) i j) :
    g ∈ (GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {m}))).ker.map (GeneralLinearGroup.map S.subtype) := by
  let P : Matrix n n S := Matrix.of fun i j => ⟨_, h1 i j⟩
  let Q : Matrix n n S := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hinj : Function.Injective (S.subtype.mapMatrix : Matrix n n S →+* Matrix n n A) := fun x y h => by
    ext i j
    exact congrFun (congrFun h i) j
  have hP : S.subtype.mapMatrix P = (g : Matrix n n A) := rfl
  have hQ : S.subtype.mapMatrix Q = ((g⁻¹ : GL n A) : Matrix n n A) := rfl
  let u : GL n S := ⟨P, Q, hinj (by rw [map_mul, hP, hQ, map_one, Units.mul_inv]),
    hinj (by rw [map_mul, hP, hQ, map_one, Units.inv_mul])⟩
  refine ⟨u, ?_, Units.ext rfl⟩
  refine Units.ext ?_
  ext i j
  obtain ⟨y, hy, e⟩ := h3 i j
  have key : Ideal.Quotient.mk (Ideal.span {m}) (P i j) = Ideal.Quotient.mk (Ideal.span {m}) ((1 : Matrix n n S) i j) := by
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨⟨y, hy⟩, Subtype.ext ?_⟩)
    change y * (m : A) = (g : Matrix n n A) i j - _
    rw [e]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  change Ideal.Quotient.mk (Ideal.span {m}) (P i j) = (1 : Matrix n n _) i j
  rw [key]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/- English proof (translation)
Establish `h : IsOpen {x : FiniteAdeleRing (𝓞 E) E | ∀ v, x v ∈ v.adicCompletionIntegers E}` using `RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `only [Ohat, SetLike.mem_coe, Subring.mem_iInf, Subring.mem_comap, Set.mem_ofPred_eq]`. Both sides reduce to the same expression.
-/
theorem isOpen_Ohat (E : Type) [Field E] [NumberField E] : IsOpen (Ohat E : Set (GlobalTheory.CuspRep.Af E)) := by
  have h : IsOpen {x : FiniteAdeleRing (𝓞 E) E | ∀ v, x v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  convert h using 1
  ext x
  simp only [Ohat, SetLike.mem_coe, Subring.mem_iInf, Subring.mem_comap, Set.mem_ofPred_eq]
  rfl

/- English proof (translation)
Introduce `E _ _ a M hM`. Establish `hO` using `isOpen_Ohat E`. Use `set c : GlobalTheory.CuspRep.Af E := algebraMap E (GlobalTheory.CuspRep.Af E) (M : E)⁻¹ with hc`. Establish `hcM : c * (M : GlobalTheory.CuspRep.Af E) = 1`. Rewrite using `[hc, ← map_natCast (algebraMap E (GlobalTheory.CuspRep.Af E)), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM.ne'), map_one]`.

Establish `c1 : ∀ i j, Continuous fun g : GL (Fin a) (GlobalTheory.CuspRep.Af E) => (g : Matrix (Fin a) (Fin a) (GlobalTheory.CuspRep.Af E)) i j` using `fun i j => Units.continuous_val.matrix_elem i j`. Establish `c2 : ∀ i j, Continuous fun g : GL (Fin a) (GlobalTheory.CuspRep.Af E) => ((g⁻¹ : GL (Fin a) (GlobalTheory.CuspRep.Af E)) : Matrix (Fin a) (Fin a) (GlobalTheory.CuspRep.Af E)) i j` using `fun i j => Units.continuous_coe_inv.matrix_elem i j`. Set `U : Set (GL (Fin a) (GlobalTheory.CuspRep.Af E))` to `⋂ i, ⋂ j, ((fun g : GL (Fin a) (GlobalTheory.CuspRep.Af E) => (g : Matrix (Fin a) (Fin a) (GlobalTheory.CuspRep.Af E)) i j) ⁻¹' (Ohat E) ∩ (fun g : GL (Fin a) (GlobalTheory.CuspRep.Af E) => ((g⁻¹ : GL (Fin a) (GlobalTheory.CuspRep.Af E)) : Matrix (Fin a) (Fin a) (GlobalTheory.Cus …`. Establish `hU : IsOpen U` using `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ((hO.preimage (c1 i j)).inter (hO.preimage (c2 i j))).inter (hO.preimage (((c1 i j).sub continuous_const).mul continuous_const))`. Establish `h1U : (1 : GL (Fin a) (GlobalTheory.CuspRep.Af E)) ∈ U`.

Establish `h1 : ∀ i j, (1 : Matrix (Fin a) (Fin a) (GlobalTheory.CuspRep.Af E)) i j ∈ Ohat E` using `fun i j => by`. Distinguish the cases in `h : i = j`. Rewrite using `[h, Matrix.one_apply_eq]`. Conclude with `one_mem _`. Rewrite using `[Matrix.one_apply_ne h]`.

Conclude with `zero_mem _`. Use `Set.mem_iInter₂.2 fun i j => ⟨⟨h1 i j, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `using h1 i j`. Simplify using the standard rewrite rules. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds h1U) fun g hg => ?_)` and prove the remaining obligations.

Establish `hg'` using `Set.mem_iInter₂.1 hg`. Use `mem_map_ker (Ohat E) (M : Ohat E) g (fun i j => (hg' i j).1.1) (fun i j => (hg' i j).1.2) fun i j => ⟨_, (hg' i j).2, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, Subring.coe_natCast, hcM, mul_one]`.
-/
theorem isOpen_Kpr : ∀ (E : Type) [Field E] [NumberField E] (a M : ℕ), 0 < M →
    IsOpen (GlobalTheory.CuspNF.Kpr E a M : Set (GL (Fin a) (GlobalTheory.CuspRep.Af E))) := by
  intro E _ _ a M hM
  have hO := isOpen_Ohat E
  set c : GlobalTheory.CuspRep.Af E := algebraMap E (GlobalTheory.CuspRep.Af E) (M : E)⁻¹ with hc
  have hcM : c * (M : GlobalTheory.CuspRep.Af E) = 1 := by
    rw [hc, ← map_natCast (algebraMap E (GlobalTheory.CuspRep.Af E)), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM.ne'), map_one]
  have c1 : ∀ i j, Continuous fun g : GL (Fin a) (GlobalTheory.CuspRep.Af E) => (g : Matrix (Fin a) (Fin a) (GlobalTheory.CuspRep.Af E)) i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have c2 : ∀ i j, Continuous fun g : GL (Fin a) (GlobalTheory.CuspRep.Af E) => ((g⁻¹ : GL (Fin a) (GlobalTheory.CuspRep.Af E)) : Matrix (Fin a) (Fin a) (GlobalTheory.CuspRep.Af E)) i j := fun i j =>
    Units.continuous_coe_inv.matrix_elem i j
  let U : Set (GL (Fin a) (GlobalTheory.CuspRep.Af E)) := ⋂ i, ⋂ j,
    ((fun g : GL (Fin a) (GlobalTheory.CuspRep.Af E) => (g : Matrix (Fin a) (Fin a) (GlobalTheory.CuspRep.Af E)) i j) ⁻¹' (Ohat E) ∩
      (fun g : GL (Fin a) (GlobalTheory.CuspRep.Af E) => ((g⁻¹ : GL (Fin a) (GlobalTheory.CuspRep.Af E)) : Matrix (Fin a) (Fin a) (GlobalTheory.CuspRep.Af E)) i j) ⁻¹' (Ohat E) ∩
      (fun g : GL (Fin a) (GlobalTheory.CuspRep.Af E) => ((g : Matrix (Fin a) (Fin a) (GlobalTheory.CuspRep.Af E)) i j - (1 : Matrix (Fin a) (Fin a) (GlobalTheory.CuspRep.Af E)) i j) * c) ⁻¹' (Ohat E))
  have hU : IsOpen U := isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    ((hO.preimage (c1 i j)).inter (hO.preimage (c2 i j))).inter
      (hO.preimage (((c1 i j).sub continuous_const).mul continuous_const))
  have h1U : (1 : GL (Fin a) (GlobalTheory.CuspRep.Af E)) ∈ U := by
    have h1 : ∀ i j, (1 : Matrix (Fin a) (Fin a) (GlobalTheory.CuspRep.Af E)) i j ∈ Ohat E := fun i j => by
      by_cases h : i = j
      · rw [h, Matrix.one_apply_eq]; exact one_mem _
      · rw [Matrix.one_apply_ne h]; exact zero_mem _
    refine Set.mem_iInter₂.2 fun i j => ⟨⟨h1 i j, ?_⟩, ?_⟩
    · simpa using h1 i j
    · simp
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds h1U) fun g hg => ?_)
  have hg' := Set.mem_iInter₂.1 hg
  refine mem_map_ker (Ohat E) (M : Ohat E) g (fun i j => (hg' i j).1.1) (fun i j => (hg' i j).1.2)
    fun i j => ⟨_, (hg' i j).2, ?_⟩
  rw [mul_assoc, Subring.coe_natCast, hcM, mul_one]

end GlobalTheory.CuspNF.KprOpen

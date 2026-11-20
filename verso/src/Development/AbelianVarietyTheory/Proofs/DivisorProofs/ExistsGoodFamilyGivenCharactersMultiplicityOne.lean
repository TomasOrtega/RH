import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxPass
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSet

noncomputable section

open Formalism.L2.DIV NumberField

namespace GlobalTheory.GoodFamilyOfChars

/- English proof (translation)
Establish `e : Formalism.IndefR.IndefiniteEpsilonOperator.epOp (T.tau s) ⟨P0, ψ0⟩ = (T.tau s).asAlgebraHom (Formalism.MainNotions.PrimeDegreeVariant.eps ⟨P0, ψ0⟩)`. Rewrite using `[Formalism.MainNotions.PrimeDegreeVariant.eps, map_smul, map_sum, Formalism.IndefR.IndefiniteEpsilonOperator.epOp]`. Use `congr 1`. Establish `hsub : (Finset.univ.map (Function.Embedding.subtype (· ∈ P0))) ⊆ Finset.univ` using `Finset.subset_univ _`. Rewrite using `[← Finset.sum_subset hsub (fun x _ hx => by`.

Establish `: x ∉ P0` using `fun h => hx (Finset.mem_map.2 ⟨⟨x, h⟩, Finset.mem_univ _, rfl⟩)`. Simplify using `[this]), Finset.sum_map]`. Simplify using `only [Function.Embedding.subtype_apply]`. Use `Finset.sum_congr (by convert rfl) fun h _ => ?_` and prove the remaining obligations. Simplify using `[h.2, Representation.asAlgebraHom_of, map_inv]`.

Unfold `Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp Formalism.MainNotions.PrimeDegreeVariant.nS`. Rewrite using `[e]`.
-/
theorem nOf_eq_nS {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (P0 : Subgroup G)
    [Fintype P0] (ψ0 : P0 →* Kˣ) (s : T.S) :
    Formalism.IndefR.IndefiniteEpsilonOperator.nOf (T.tau s) ⟨P0, ψ0⟩ = Formalism.MainNotions.PrimeDegreeVariant.nS T ⟨P0, ψ0⟩ s := by
  classical
  have e : Formalism.IndefR.IndefiniteEpsilonOperator.epOp (T.tau s) ⟨P0, ψ0⟩ = (T.tau s).asAlgebraHom (Formalism.MainNotions.PrimeDegreeVariant.eps ⟨P0, ψ0⟩) := by
    rw [Formalism.MainNotions.PrimeDegreeVariant.eps, map_smul, map_sum, Formalism.IndefR.IndefiniteEpsilonOperator.epOp]
    congr 1
    have hsub : (Finset.univ.map (Function.Embedding.subtype (· ∈ P0))) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_subset hsub (fun x _ hx => by
      have : x ∉ P0 := fun h => hx (Finset.mem_map.2 ⟨⟨x, h⟩, Finset.mem_univ _, rfl⟩)
      simp [this]), Finset.sum_map]
    simp only [Function.Embedding.subtype_apply]
    refine Finset.sum_congr (by convert rfl) fun h _ => ?_
    simp [h.2, Representation.asAlgebraHom_of, map_inv]
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp Formalism.MainNotions.PrimeDegreeVariant.nS
  rw [e]

variable {K : Type} [Field K] {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module K W]

/- English proof (translation)
Proceed by induction on `a using MonoidAlgebra.induction_on with`. Consider the case `of g => intro w hw`. Simplify `hU g w hw` using `[Representation.asAlgebraHom_of]`. Consider the case `add a b ha hb => intro w hw`. Simplify using `using U.add_mem (ha w hw) (hb w hw)`.

Consider the case `smul r a ha => intro w hw`. Simplify using `using U.smul_mem r (ha w hw)`.
-/
theorem asAlg_mem (τ : Representation K G W) (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U)
    (a : MonoidAlgebra K G) : ∀ w ∈ U, τ.asAlgebraHom a w ∈ U := by
  induction a using MonoidAlgebra.induction_on with
  | of g => intro w hw; simpa [Representation.asAlgebraHom_of] using hU g w hw
  | add a b ha hb => intro w hw; simpa using U.add_mem (ha w hw) (hb w hw)
  | smul r a ha => intro w hw; simpa using U.smul_mem r (ha w hw)

/- English proof (translation)
Proceed by induction on `a using MonoidAlgebra.induction_on with`. Consider the case `of g => simpa [Representation.asAlgebraHom_of, Module.End.mul_eq_comp] using hf g`. Consider the case `add a b ha hb => simp [map_add, mul_add, add_mul, ha, hb]`. Consider the case `smul r a ha => simp [map_smul, ha]`.
-/
theorem asAlg_comm (τ : Representation K G W) (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f)
    (a : MonoidAlgebra K G) : f * τ.asAlgebraHom a = τ.asAlgebraHom a * f := by
  induction a using MonoidAlgebra.induction_on with
  | of g => simpa [Representation.asAlgebraHom_of, Module.End.mul_eq_comp] using hf g
  | add a b ha hb => simp [map_add, mul_add, add_mul, ha, hb]
  | smul r a ha => simp [map_smul, ha]

/- English proof (translation)
Distinguish the cases in `h : U = ⊥`. Conclude with `Or.inl h`. Use `right`. Take `⟨w, hw, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ w ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hc)`. Rewrite using `[eq_top_iff]`. Introduce `v _`.

Take `⟨a, ha⟩` from `hs ((φ w)⁻¹ • φ.smulRight v)`. Use `asAlg_mem τ U hU a w hw` as an intermediate fact. Rewrite `this` using `[ha]`. Simplify `this` using `[hφ]`.
-/
theorem irr_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hc)
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha⟩ := hs ((φ w)⁻¹ • φ.smulRight v)
  have := asAlg_mem τ U hU a w hw
  rw [ha] at this
  simpa [hφ] using this

/- English proof (translation)
Establish `hc : f ∈ Set.center (Module.End K W)`. Rewrite using `[Semigroup.mem_center_iff]`. Introduce `e`. Take `⟨a, rfl⟩` from `hs e`. Conclude with `(asAlg_comm τ f hf a).symm`.

Take `⟨α, hα, rfl⟩` from `Module.End.mem_center_iff.1 hc`. Conclude with `⟨α, by ext x; simp⟩`.
-/
theorem scalar_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f) : ∃ c : K, f = c • LinearMap.id := by
  have hc : f ∈ Set.center (Module.End K W) := by
    rw [Semigroup.mem_center_iff]
    intro e
    obtain ⟨a, rfl⟩ := hs e
    exact (asAlg_comm τ f hf a).symm
  obtain ⟨α, hα, rfl⟩ := Module.End.mem_center_iff.1 hc
  exact ⟨α, by ext x; simp⟩

/- English proof (translation)
Introduce `K _ _ G _ _ X hX P0 _ ψ0 h1`. Take `⟨T, hT, hM, -⟩` from `GlobalTheory.GoodSetOfChars.exists_goodSet K G X hX ⟨P0, ψ0⟩ h1`. Establish `hch : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) = fun g => LinearMap.trace K (T.W s) (T.tau s g)` using `fun s => rfl`. Establish `hmem : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) ∈ X` using `fun s => (hT _).2 ⟨s, (hch s)⟩`. Use `⟨T.S, inferInstance, T.W, inferInstance, inferInstance, inferInstance, T.tau, ⟨fun s => inferInstance, fun s U hU => irr_of_surj (T.tau s) (T.irr s) U hU, fun s f hf => scalar_of_surj (T.tau s) (T.irr s) f hf, fun s t h => T.inj h⟩, fun χ => ⟨fun h => ?_, ?_⟩, fun s => ?_⟩` and prove the remaining obligations.

Take `⟨s, hs⟩` from `(hT χ).1 h`. Conclude with `⟨s, hs.symm⟩`. Introduce and unpack `⟨s, rfl⟩`. Conclude with `hmem s`. Rewrite using `[nOf_eq_nS]`.

Conclude with `hM s`.
-/
theorem exists_goodFamily : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P0 : Subgroup G) [Fintype P0] (ψ0 : P0 →* Kˣ), (∀ χ ∈ X, ∑ h : P0, χ (h : G) * (((ψ0 h)⁻¹ : Kˣ) : K) = (Fintype.card P0 : K)) → ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module K (Ws s)) (_ : ∀ s, FiniteDimensional K (Ws s)) (τ : ∀ s, Representation K G (Ws s)), Formalism.IndefR.TransferLatticeStatement.IsGood τ ∧ (∀ χ : G → K, χ ∈ X ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ) ∧ Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ := by
  intro K _ _ G _ _ X hX P0 _ ψ0 h1
  obtain ⟨T, hT, hM, -⟩ := GlobalTheory.GoodSetOfChars.exists_goodSet K G X hX ⟨P0, ψ0⟩ h1
  have hch : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) = fun g => LinearMap.trace K (T.W s) (T.tau s g) := fun s => rfl
  have hmem : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) ∈ X := fun s => (hT _).2 ⟨s, (hch s)⟩
  refine ⟨T.S, inferInstance, T.W, inferInstance, inferInstance, inferInstance, T.tau,
    ⟨fun s => inferInstance, fun s U hU => irr_of_surj (T.tau s) (T.irr s) U hU,
     fun s f hf => scalar_of_surj (T.tau s) (T.irr s) f hf, fun s t h => T.inj h⟩,
    fun χ => ⟨fun h => ?_, ?_⟩, fun s => ?_⟩
  · obtain ⟨s, hs⟩ := (hT χ).1 h
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact hmem s
  · rw [nOf_eq_nS]
    exact hM s

end GlobalTheory.GoodFamilyOfChars

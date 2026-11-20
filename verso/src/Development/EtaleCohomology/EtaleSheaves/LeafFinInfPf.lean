import Development.EtaleCohomology.EtaleSheaves.LeafOrdInfLocalPf

namespace LateralTheory.E.E4

open Polynomial

/- English proof (translation)
Establish `h : (aeval (algebraMap B L (g X)) : Polynomial k →ₐ[k] L) = (IsScalarTower.toAlgHom k B L).comp g`. Apply `Polynomial.algHom_ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem finInf_comm {k B L : Type} [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]
    [Algebra B L] [IsScalarTower k B L] (g : Polynomial k →ₐ[k] B) (p : Polynomial k) :
    aeval (algebraMap B L (g X)) p = algebraMap B L (g p) := by
  have h : (aeval (algebraMap B L (g X)) : Polynomial k →ₐ[k] L) =
      (IsScalarTower.toAlgHom k B L).comp g := by
    apply Polynomial.algHom_ext
    simp
  rw [h]; rfl

/- English proof (translation)
Establish `hi : g.toRingHom.IsIntegral` using `RingHom.IsIntegral.of_finite hf`. Take `⟨p, hp, hpb⟩` from `hi b`. Set `φ : Polynomial k →ₐ[k] K` to `aeval (⟨_, hT⟩ : K)`. Establish `hc : (algebraMap K L).comp φ.toRingHom = (algebraMap B L).comp g.toRingHom`. Use `RingHom.ext fun q => ?_` and prove the remaining obligations.

Establish `h1` using `finInf_comm (L := L) g q`. Establish `h2` using `Polynomial.aeval_algebraMap_apply L (⟨_, hT⟩ : K) q`. Conclude with `h2.symm.trans h1`. Use `⟨p.map φ.toRingHom, hp.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[eval₂_map, hc, ← Polynomial.hom_eval₂, hpb, map_zero]`.
-/
theorem finInf_integral {k B L : Type} [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]
    [Algebra B L] [IsScalarTower k B L] (g : Polynomial k →ₐ[k] B) (hf : g.Finite)
    (K : IntermediateField k L) (hT : algebraMap B L (g X) ∈ K) (b : B) :
    IsIntegral K (algebraMap B L b) := by
  have hi : g.toRingHom.IsIntegral := RingHom.IsIntegral.of_finite hf
  obtain ⟨p, hp, hpb⟩ := hi b
  let φ : Polynomial k →ₐ[k] K := aeval (⟨_, hT⟩ : K)
  have hc : (algebraMap K L).comp φ.toRingHom = (algebraMap B L).comp g.toRingHom := by
    refine RingHom.ext fun q => ?_
    have h1 := finInf_comm (L := L) g q
    have h2 := Polynomial.aeval_algebraMap_apply L (⟨_, hT⟩ : K) q
    exact h2.symm.trans h1
  refine ⟨p.map φ.toRingHom, hp.map _, ?_⟩
  rw [eval₂_map, hc, ← Polynomial.hom_eval₂, hpb, map_zero]

/- English proof (translation)
Introduce `k B _ _ _ _ _ hft g hg hf`. Establish `hinj : Function.Injective (algebraMap B (FractionRing B))` using `IsFractionRing.injective B _`. Establish `htr : Transcendental k (algebraMap B (FractionRing B) (g X))`. Rewrite using `[transcendental_iff]`. Introduce `p hp`.

Rewrite `hp` using `[finInf_comm]`. Apply `hg` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Simplify using `using hp`. Use `⟨fun h => htr (IsAlgebraic.inv_iff.mp h), ?_⟩` and prove the remaining obligations.

Use `set K := IntermediateField.adjoin k {(algebraMap B (FractionRing B) (g X))⁻¹} with hK`. Establish `hT : algebraMap B (FractionRing B) (g X) ∈ K`. Establish `: (algebraMap B (FractionRing B) (g X))⁻¹ ∈ K` using `IntermediateField.subset_adjoin k _ (Set.mem_singleton _)`. Simplify using `using K.inv_mem this`. Take `⟨S, hS⟩` from `hft.out`.

Set `S' : Set (FractionRing B)` to `algebraMap B (FractionRing B) '' (S : Set B)`. Establish `: Finite S'` using `(S.finite_toSet.image _).to_subtype`. Establish `hfd : FiniteDimensional K (IntermediateField.adjoin K S')` using `IntermediateField.finiteDimensional_adjoin (by`. Introduce and unpack `_ ⟨b, -, rfl⟩`. Conclude with `finInf_integral g hf K hT b)`.

Establish `hB : ∀ b : B, algebraMap B (FractionRing B) b ∈ IntermediateField.adjoin K S'`. Introduce `b`. Establish `hb : b ∈ Algebra.adjoin k (S : Set B)` using `hS ▸ Algebra.mem_top`. Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact IntermediateField.subset_adjoin K S' ⟨x, hx, rfl⟩`.

Consider the case `algebraMap r`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k K (FractionRing B)]`. Conclude with `IntermediateField.algebraMap_mem _ _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`. Establish `htop : IntermediateField.adjoin K S' = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := B) x`. Conclude with `div_mem (hB a) (hB b)`. Rewrite `hfd` using `[htop]`. Conclude with `IntermediateField.topEquiv.toLinearEquiv.finiteDimensional`.
-/
theorem LeafFinInf_of : LeafFinInf := by
  intro k B _ _ _ _ _ hft g hg hf
  have hinj : Function.Injective (algebraMap B (FractionRing B)) := IsFractionRing.injective B _
  have htr : Transcendental k (algebraMap B (FractionRing B) (g X)) := by
    rw [transcendental_iff]
    intro p hp
    rw [finInf_comm] at hp
    apply hg
    apply hinj
    simpa using hp
  refine ⟨fun h => htr (IsAlgebraic.inv_iff.mp h), ?_⟩
  set K := IntermediateField.adjoin k {(algebraMap B (FractionRing B) (g X))⁻¹} with hK
  have hT : algebraMap B (FractionRing B) (g X) ∈ K := by
    have : (algebraMap B (FractionRing B) (g X))⁻¹ ∈ K :=
      IntermediateField.subset_adjoin k _ (Set.mem_singleton _)
    simpa using K.inv_mem this
  obtain ⟨S, hS⟩ := hft.out
  let S' : Set (FractionRing B) := algebraMap B (FractionRing B) '' (S : Set B)
  have : Finite S' := (S.finite_toSet.image _).to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K S') :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact finInf_integral g hf K hT b)
  have hB : ∀ b : B, algebraMap B (FractionRing B) b ∈ IntermediateField.adjoin K S' := by
    intro b
    have hb : b ∈ Algebra.adjoin k (S : Set B) := hS ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K S' ⟨x, hx, rfl⟩
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k K (FractionRing B)]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop : IntermediateField.adjoin K S' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact div_mem (hB a) (hB b)
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end LateralTheory.E.E4

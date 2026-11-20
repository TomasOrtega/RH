import Mathlib

noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[algebraMap_adicCompletion]`. Simplify using `[valuedAdicCompletion_eq_valuation']`.
-/
theorem val_algebraMap_F (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    Valued.v (algebraMap F (v.adicCompletion F) t) = v.valuation F t := by
  rw [algebraMap_adicCompletion]
  simp [valuedAdicCompletion_eq_valuation']

/- English proof (translation)
Establish `hnhds : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ 𝓝 x`. Rewrite using `[Valued.mem_nhds]`. Conclude with `⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩`. Take `⟨_, hy, ⟨k, rfl⟩⟩` from `mem_closure_iff_nhds.mp ((denseRange_algebraMap (K := F) (v := v)) x) _ hnhds`. Simplify using `only [Set.mem_ofPred_eq] at hy`.

Establish `hk : v.valuation F k ≤ 1`. Rewrite using `[← val_algebraMap_F]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨a, ha⟩` from `exists_valuation_sub_lt_of_integer v hk 1`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `h2 : Valued.v (algebraMap F (v.adicCompletion F) k - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1`. Rewrite using `[← map_sub, val_algebraMap_F, ← Valuation.map_neg, neg_sub]`. Simplify using `using ha`. Combine the equalities or inequalities in the displayed calculation. Use `max_lt ?_ h2` and prove the remaining obligations.

Rewrite using `[← Valuation.map_neg, neg_sub]`. Conclude with `hy`.
-/
theorem exists_int_near (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
  have hnhds : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ 𝓝 x := by
    rw [Valued.mem_nhds]
    exact ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨_, hy, ⟨k, rfl⟩⟩ :=
    mem_closure_iff_nhds.mp ((denseRange_algebraMap (K := F) (v := v)) x) _ hnhds
  simp only [Set.mem_ofPred_eq] at hy
  have hk : v.valuation F k ≤ 1 := by
    rw [← val_algebraMap_F]
    calc Valued.v (algebraMap F (v.adicCompletion F) k)
        = Valued.v ((algebraMap F (v.adicCompletion F) k - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap F (v.adicCompletion F) k - x)) (Valued.v x) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := max_le hy.le hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hk 1
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) k -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
    rw [← map_sub, val_algebraMap_F, ← Valuation.map_neg, neg_sub]
    simpa using ha
  calc Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
      = Valued.v ((x - algebraMap F (v.adicCompletion F) k) + (algebraMap F (v.adicCompletion F) k -
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < 1 := by
      refine max_lt ?_ h2
      rw [← Valuation.map_neg, neg_sub]; exact hy

def toOv (v : HeightOneSpectrum (𝓞 F)) : 𝓞 F →+* Valued.integer (v.adicCompletion F) :=
  ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict _ (fun a => by
    show Valued.v (_ : v.adicCompletion F) ≤ 1
    simp only [RingHom.comp_apply]
    rw [val_algebraMap_F, valuation_of_algebraMap]
    exact intValuation_le_one v a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toOv_coe (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    ((toOv v a : Valued.integer (v.adicCompletion F)) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl

/- English proof (translation)
The claim follows from `(Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one`.
-/
theorem isUnit_integer_iff (v : HeightOneSpectrum (𝓞 F)) (x : Valued.integer (v.adicCompletion F)) :
    IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 :=
  (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one

/- English proof (translation)
Establish `hfin : Finite (𝓞 F ⧸ v.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot`. Set `φ : 𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F))` to `(IsLocalRing.residue _).comp (toOv v)`. Establish `hker : ∀ a ∈ v.asIdeal, φ a = 0`. Introduce `a ha`. Simplify using `only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_iff, toOv_coe, val_algebraMap_F, valuation_of_algebraMap]`.

Conclude with `((intValuation_lt_one_iff_mem v a).mpr ha).ne`. Set `ψ` to `Ideal.Quotient.lift v.asIdeal φ hker`. Use `Finite.of_surjective ψ ?_` and prove the remaining obligations. Introduce `z`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective z`.

Take `⟨a, ha⟩` from `exists_int_near v (x : v.adicCompletion F) x.2`. Use `⟨Ideal.Quotient.mk _ a, ?_⟩` and prove the remaining obligations. Simplify using `only [ψ, Ideal.Quotient.lift_mk, φ, RingHom.comp_apply]`. Rewrite using `[eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_iff]`. Move the coercions through the operations in `[toOv_coe]`.

Conclude with `ha.ne`.
-/
theorem finite_residue (v : HeightOneSpectrum (𝓞 F)) :
    Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F))) := by
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F)) :=
    (IsLocalRing.residue _).comp (toOv v)
  have hker : ∀ a ∈ v.asIdeal, φ a = 0 := by
    intro a ha
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, isUnit_integer_iff, toOv_coe, val_algebraMap_F, valuation_of_algebraMap]
    exact ((intValuation_lt_one_iff_mem v a).mpr ha).ne
  let ψ := Ideal.Quotient.lift v.asIdeal φ hker
  refine Finite.of_surjective ψ ?_
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := exists_int_near v (x : v.adicCompletion F) x.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  simp only [ψ, Ideal.Quotient.lift_mk, φ, RingHom.comp_apply]
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, isUnit_integer_iff]
  push_cast [toOv_coe]
  exact ha.ne

/- English proof (translation)
Rewrite using `[Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]`. Use `⟨?_, ?_, finite_residue v⟩` and prove the remaining obligations. Conclude with `(Valued.isClosed_integer (R := v.adicCompletion F)).completeSpace_coe`. Conclude with `inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))`.
-/
theorem compactSpace_integer (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (Valued.integer (v.adicCompletion F)) := by
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  refine ⟨?_, ?_, finite_residue v⟩
  · exact (Valued.isClosed_integer (R := v.adicCompletion F)).completeSpace_coe
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))

/- English proof (translation)
Use `compactSpace_integer v` as an intermediate fact. Conclude with `isCompact_iff_compactSpace.mpr this`.
-/
theorem isCompact_Ov (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have := compactSpace_integer v
  exact isCompact_iff_compactSpace.mpr this

instance compactSpace_Ov (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
  isCompact_iff_compactSpace.mp (isCompact_Ov v)

def Ohat (F : Type) [Field F] [NumberField F] : Set (FiniteAdeleRing (𝓞 F) F) :=
  {a | ∀ v, a v ∈ v.adicCompletionIntegers F}

/- English proof (translation)
The claim follows from `RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun _ ↦ Valued.isOpen_valuationSubring _)`.
-/
theorem isOpen_Ohat : IsOpen (Ohat F) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ ↦ Valued.isOpen_valuationSubring _)

instance compactSpace_Ov' (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  isCompact_iff_compactSpace.mp (isCompact_Ov v)

/- English proof (translation)
Establish `hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite)` using `RestrictedProduct.isEmbedding_structureMap.continuous`. Establish `: Ohat F = Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite)`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce `ha`.

Conclude with `⟨fun v => ⟨a v, ha v⟩, rfl⟩`. Introduce and unpack `⟨x, rfl⟩ v`. Conclude with `(x v).2`. Rewrite using `[this]`. Conclude with `isCompact_range hc`.
-/
theorem isCompact_Ohat : IsCompact (Ohat F) := by
  have hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have : Ohat F = Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, rfl⟩
    · rintro ⟨x, rfl⟩ v
      exact (x v).2
  rw [this]
  exact isCompact_range hc

instance t2Space_finiteAdeleRing_alt : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

end PI.WAU

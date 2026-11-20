import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

universe u

section Places

variable {F L : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem placesOver_finite {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S.Finite) :
    (placesOver S : Set (HeightOneSpectrum (𝓞 L))).Finite := by
  have hfin : ∀ v ∈ S, {w : HeightOneSpectrum (𝓞 L) | w.asIdeal.LiesOver v.asIdeal}.Finite := by
    intro v _
    have h := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)
    refine (h.preimage (f := fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal)
      fun a _ b _ hab => HeightOneSpectrum.ext hab).subset ?_
    intro w hw
    exact ⟨w.isPrime, hw⟩
  refine (hS.biUnion hfin).subset ?_
  rintro w ⟨v, hv, hwv⟩
  exact Set.mem_biUnion hv hwv

omit [NumberField F] [NumberField L] in

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_placesOver_of_natCast_mem {S : Set (HeightOneSpectrum (𝓞 F))} {n : ℕ}
    (hn : ∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    {w : HeightOneSpectrum (𝓞 L)} (hw : ((n : ℕ) : 𝓞 L) ∈ w.asIdeal) : w ∈ placesOver S := by
  refine (mem_placesOver_iff (F := F) (L := L)).2 (hn _ ?_)
  change ((n : ℕ) : 𝓞 F) ∈ Ideal.comap (algebraMap (𝓞 F) (𝓞 L)) w.asIdeal
  rw [Ideal.mem_comap, map_natCast (algebraMap (𝓞 F) (𝓞 L))]
  exact hw

omit [NumberField F] [NumberField L] in

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem natCast_not_mem_of_not_mem_placesOver {S : Set (HeightOneSpectrum (𝓞 F))} {n : ℕ}
    (hn : ∀ v : HeightOneSpectrum (𝓞 F), ((n : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) :
    ∀ w ∉ (placesOver S : Set (HeightOneSpectrum (𝓞 L))), ((n : ℕ) : 𝓞 L) ∉ w.asIdeal :=
  fun _ hw hmem => hw (mem_placesOver_of_natCast_mem hn hmem)

end Places

section OpenSubgroups

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem mem_gsOpenSubgroup_iff_of_image {L : FiniteSubfield} [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (T : Set (maxUnramifiedOutside K.1 ℚ̄ S)) (hT : ∀ x : L.1, gsEmbedding hL x ∈ T)
    (hT' : ∀ y ∈ T, ∃ x : L.1, gsEmbedding hL x = y) (σ : galUnramifiedOutside K.1 ℚ̄ S) :
    σ ∈ gsOpenSubgroup S hL ↔ ∀ y ∈ T, σ y = y := by
  rw [mem_gsOpenSubgroup_iff]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hT' y hy
    exact h x
  · intro h x
    exact h _ (hT x)

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_gsOpenSubgroup_eq (V : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) :
    ∃ (L : FiniteSubfield) (_ : Fact (K ≤ L))
      (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      gsOpenSubgroup S hL = V := by
  let KS := maxUnramifiedOutside K.1 ℚ̄ S
  let H : ClosedSubgroup Gal(KS/K.1) := ⟨(V : Subgroup Gal(KS/K.1)), V.isClosed⟩
  let E : IntermediateField K.1 KS := IntermediateField.fixedField (H : Subgroup Gal(KS/K.1))
  have hEV : E.fixingSubgroup = (V : Subgroup Gal(KS/K.1)) :=
    InfiniteGalois.fixingSubgroup_fixedField H
  have hEfin : FiniteDimensional K.1 E := by
    rw [← InfiniteGalois.isOpen_iff_finite E, hEV]
    exact V.isOpen
  let E' : IntermediateField K.1 ℚ̄ := E.map KS.val
  have hE'fin : FiniteDimensional K.1 E' :=
    LinearEquiv.finiteDimensional (E.equivMap KS.val).toLinearEquiv
  have hE'Q₀ : FiniteDimensional ℚ E' := FiniteDimensional.trans ℚ K.1 E'
  have hE'Q : FiniteDimensional ℚ (E'.restrictScalars ℚ) := hE'Q₀
  have hKL : K ≤ ⟨E'.restrictScalars ℚ, hE'Q⟩ := by
    intro x hx
    change x ∈ E'
    have : algebraMap K.1 ℚ̄ ⟨x, hx⟩ ∈ E' := E'.algebraMap_mem _
    exact this
  have hKS : ∀ x : (⟨E'.restrictScalars ℚ, hE'Q⟩ : FiniteSubfield).1,
      algebraMap (⟨E'.restrictScalars ℚ, hE'Q⟩ : FiniteSubfield).1 ℚ̄ x ∈ KS := by
    intro x
    obtain ⟨y, -, hy⟩ := (x.2 : (x : ℚ̄) ∈ E')
    change (x : ℚ̄) ∈ KS
    rw [← hy]
    exact y.2
  have : Fact (K ≤ ⟨E'.restrictScalars ℚ, hE'Q⟩) := ⟨hKL⟩
  refine ⟨⟨E'.restrictScalars ℚ, hE'Q⟩, inferInstance, hKS, ?_⟩
  ext σ
  rw [mem_gsOpenSubgroup_iff_of_image K S hKS (E : Set KS)]
  · change _ ↔ σ ∈ (V : Subgroup Gal(KS/K.1))
    rw [← hEV, IntermediateField.mem_fixingSubgroup_iff]
    rfl
  · intro x
    obtain ⟨y, hy, hyx⟩ := (x.2 : (x : ℚ̄) ∈ E')
    have hy' : y ∈ (E : Set KS) := hy
    convert hy' using 1
    apply Subtype.ext
    exact hyx.symm
  · intro y hy
    exact ⟨⟨(y : ℚ̄), ⟨y, hy, rfl⟩⟩, Subtype.ext rfl⟩

end OpenSubgroups

end

end GroundTheory.ProfCoh

import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import ReciprocityTheory.SemistableReduction.ExistsDualDerivations

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial DerivationAlgebraicIndependence

/- English proof (translation)
Use `haveI : FaithfulSMul K Ω := (faithfulSMul_iff_algebraMap_injective K Ω).2 (algebraMap K Ω).injective`. Use `haveI : FaithfulSMul Ω (MvPolynomial (SVars D m) Ω) := (faithfulSMul_iff_algebraMap_injective Ω _).2 (MvPolynomial.C_injective _ _)`. Use `haveI : FaithfulSMul (MvPolynomial (SVars D m) Ω) (SField Ω D m) := (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective (MvPolynomial (SVars D m) Ω) (SField Ω D m))`. Establish `h1` using `trdeg_add_eq K (MvPolynomial (SVars D m) Ω) (A := SField Ω D m)`. Establish `h2` using `trdeg_add_eq K Ω (A := MvPolynomial (SVars D m) Ω)`.

Establish `h3 : Algebra.trdeg (MvPolynomial (SVars D m) Ω) (SField Ω D m) = 0` using `trdeg_eq_zero_iff.2 (IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (SVars D m) Ω)))`. Establish `h4 : Algebra.trdeg Ω (MvPolynomial (SVars D m) Ω) = ((1 + (D + 1) * m : ℕ) : Cardinal)`. Rewrite using `[MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]`. Use `congr 1`. Simplify using `[SVars, Fintype.card_sum, Fintype.card_prod]`.

Rewrite using `[← h1, h3, add_zero, ← h2, h4]`.
-/
theorem trdeg_sField {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ) :
    Algebra.trdeg K (SField Ω D m) = Algebra.trdeg K Ω + ((1 + (D + 1) * m : ℕ) : Cardinal) := by
  classical
  haveI : FaithfulSMul K Ω :=
    (faithfulSMul_iff_algebraMap_injective K Ω).2 (algebraMap K Ω).injective
  haveI : FaithfulSMul Ω (MvPolynomial (SVars D m) Ω) :=
    (faithfulSMul_iff_algebraMap_injective Ω _).2 (MvPolynomial.C_injective _ _)
  haveI : FaithfulSMul (MvPolynomial (SVars D m) Ω) (SField Ω D m) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (IsFractionRing.injective (MvPolynomial (SVars D m) Ω) (SField Ω D m))
  have h1 := trdeg_add_eq K (MvPolynomial (SVars D m) Ω) (A := SField Ω D m)
  have h2 := trdeg_add_eq K Ω (A := MvPolynomial (SVars D m) Ω)
  have h3 : Algebra.trdeg (MvPolynomial (SVars D m) Ω) (SField Ω D m) = 0 :=
    trdeg_eq_zero_iff.2
      (IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (SVars D m) Ω)))
  have h4 : Algebra.trdeg Ω (MvPolynomial (SVars D m) Ω) =
      ((1 + (D + 1) * m : ℕ) : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
    congr 1
    simp [SVars, Fintype.card_sum, Fintype.card_prod]
  rw [← h1, h3, add_zero, ← h2, h4]

/- English proof (translation)
Unfold `FieldOfSStatement`. Introduce `K Ω _ _ _ _ D m x hfg htr hJ`. Take `⟨J, hJ⟩` from `hJ`. Use `set v : Fin D → KaehlerDifferential K Ω := fun a => KaehlerDifferential.D K Ω (x (J a)) with hv`. Establish `hli : LinearIndependent Ω v` using `hJ`.

Establish `hφ : ∀ a : Fin D, ∃ φ : KaehlerDifferential K Ω →ₗ[Ω] Ω, ∀ b, φ (v b) = if a = b then 1 else 0`. Introduce `a`. Take `⟨g, hg⟩` from `LinearMap.exists_extend ((Finsupp.lapply a).comp hli.repr)`. Use `⟨g, fun b => ?_⟩` and prove the remaining obligations. Establish `hb : v b ∈ Submodule.span Ω (Set.range v)` using `Submodule.subset_span ⟨b, rfl⟩`.

Establish `h` using `congrArg (fun f => f ⟨v b, hb⟩) hg`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply] at h`. Rewrite using `[h, Finsupp.lapply_apply, hli.repr_eq_single b ⟨v b, hb⟩ rfl, Finsupp.single_apply]`. Simplify using `[eq_comm]`. Use `choose φ hφ using hφ`.

Set `δ : Fin D → Derivation K Ω Ω` to `fun a => (φ a).compDer (KaehlerDifferential.D K Ω)`. Establish `hδ : ∀ a b, δ a (x (J b)) = if a = b then 1 else 0` using `fun a b => hφ a b`. Establish `hg` using `DerivationAlgebraicIndependence.gFam_indep (K := K) x J δ hδ`. Establish `hind : AlgebraicIndependent K (sImage (D` using `D) x) := by`. Establish `h1` using `hg.comp _ (DerivationAlgebraicIndependence.eIdx_injective D m)`.

Establish `h2` using `h1.map' (f := IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m)) (IsFractionRing.injective _ _)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[DerivationAlgebraicIndependence.sImage_eq]`. Use `⟨hind, ?_⟩` and prove the remaining obligations.

Establish `htrS : Algebra.trdeg K (SField Ω D m) = (((D + 1) * (m + 1) : ℕ) : Cardinal)`. Rewrite using `[trdeg_sField, htr, ← Nat.cast_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hTB : IsTranscendenceBasis K (sImage (D` using `D) x) := by`.

Use `hind.isTranscendenceBasis_of_lift_trdeg_le ?_ ?_` and prove the remaining obligations. Rewrite using `[htrS]`. Conclude with `Cardinal.nat_lt_aleph0 _`. Rewrite using `[htrS]`. Simplify using the standard rewrite rules.

Establish `halg` using `hTB.isAlgebraic_field`. Use `set E := IntermediateField.adjoin K (Set.range (sImage (D := D) x))`. Take `⟨s, hs⟩` from `hfg`. Set `f : Ω →ₐ[K] SField Ω D m` to `(IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m)).comp (IsScalarTower.toAlgHom K Ω (MvPolynomial (SVars D m) Ω))`. Set `S : Set (SField Ω D m)` to `f '' (s : Set Ω) ∪ Set.range (fun i => algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (MvPolynomial.X i))`.

Establish `hSfin : S.Finite` using `(s.finite_toSet.image _).union (Set.finite_range _)`. Use `haveI : Finite S := hSfin.to_subtype`. Set `L` to `IntermediateField.adjoin E S`. Establish `hK : IntermediateField.adjoin K (f '' (s : Set Ω)) ≤ L.restrictScalars K`. Rewrite using `[IntermediateField.adjoin_le_iff]`.

Introduce `z hz`. Conclude with `IntermediateField.subset_adjoin E S (Or.inl hz)`. Establish `hω : ∀ ω : Ω, f ω ∈ L`. Introduce `ω`. Establish `h1 : f ω ∈ (IntermediateField.adjoin K (s : Set Ω)).map f` using `(IntermediateField.mem_map _).2 ⟨ω, by rw [hs]; trivial, rfl⟩`.

Rewrite `h1` using `[IntermediateField.adjoin_map]`. Conclude with `hK h1`. Establish `hP : ∀ p : MvPolynomial (SVars D m) Ω, algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) p ∈ L`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`.

Consider the case `C a`. Establish `h` using `hω a`. Simplify `h` using `[f, MvPolynomial.algebraMap_eq]`. Consider the case `add p q hp hq`. Rewrite using `[map_add]`.

Conclude with `L.add_mem hp hq`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul]`. Conclude with `L.mul_mem hp (IntermediateField.subset_adjoin E S (Or.inr ⟨i, rfl⟩))`. Establish `htop : L = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `z _`. Take `⟨a, b, _, rfl⟩` from `IsFractionRing.div_surjective (A := MvPolynomial (SVars D m) Ω) z`. Conclude with `L.div_mem (hP a) (hP b)`. Establish `hfd : FiniteDimensional E L` using `IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral`.

Rewrite `hfd` using `[htop]`. Conclude with `IntermediateField.topEquiv.toLinearEquiv.finiteDimensional`.
-/
theorem genericImageFinite : FieldOfSStatement := by
  classical
  unfold FieldOfSStatement
  intro K Ω _ _ _ _ D m x hfg htr hJ
  obtain ⟨J, hJ⟩ := hJ
  set v : Fin D → KaehlerDifferential K Ω := fun a => KaehlerDifferential.D K Ω (x (J a)) with hv
  have hli : LinearIndependent Ω v := hJ
  have hφ : ∀ a : Fin D, ∃ φ : KaehlerDifferential K Ω →ₗ[Ω] Ω,
      ∀ b, φ (v b) = if a = b then 1 else 0 := by
    intro a
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply a).comp hli.repr)
    refine ⟨g, fun b => ?_⟩
    have hb : v b ∈ Submodule.span Ω (Set.range v) := Submodule.subset_span ⟨b, rfl⟩
    have h := congrArg (fun f => f ⟨v b, hb⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h, Finsupp.lapply_apply, hli.repr_eq_single b ⟨v b, hb⟩ rfl, Finsupp.single_apply]
    simp [eq_comm]
  choose φ hφ using hφ
  let δ : Fin D → Derivation K Ω Ω := fun a => (φ a).compDer (KaehlerDifferential.D K Ω)
  have hδ : ∀ a b, δ a (x (J b)) = if a = b then 1 else 0 := fun a b => hφ a b
  have hg := DerivationAlgebraicIndependence.gFam_indep (K := K) x J δ hδ
  have hind : AlgebraicIndependent K (sImage (D := D) x) := by
    have h1 := hg.comp _ (DerivationAlgebraicIndependence.eIdx_injective D m)
    have h2 := h1.map'
      (f := IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m))
      (IsFractionRing.injective _ _)
    convert h2 using 1
    funext p
    simp [DerivationAlgebraicIndependence.sImage_eq]
  refine ⟨hind, ?_⟩
  have htrS : Algebra.trdeg K (SField Ω D m) = (((D + 1) * (m + 1) : ℕ) : Cardinal) := by
    rw [trdeg_sField, htr, ← Nat.cast_add]
    congr 1
    ring
  have hTB : IsTranscendenceBasis K (sImage (D := D) x) := by
    refine hind.isTranscendenceBasis_of_lift_trdeg_le ?_ ?_
    · rw [htrS]
      exact Cardinal.nat_lt_aleph0 _
    · rw [htrS]
      simp
  have halg := hTB.isAlgebraic_field
  set E := IntermediateField.adjoin K (Set.range (sImage (D := D) x))
  obtain ⟨s, hs⟩ := hfg
  let f : Ω →ₐ[K] SField Ω D m :=
    (IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m)).comp
      (IsScalarTower.toAlgHom K Ω (MvPolynomial (SVars D m) Ω))
  let S : Set (SField Ω D m) := f '' (s : Set Ω) ∪
    Set.range (fun i => algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (MvPolynomial.X i))
  have hSfin : S.Finite := (s.finite_toSet.image _).union (Set.finite_range _)
  haveI : Finite S := hSfin.to_subtype
  let L := IntermediateField.adjoin E S
  have hK : IntermediateField.adjoin K (f '' (s : Set Ω)) ≤ L.restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact IntermediateField.subset_adjoin E S (Or.inl hz)
  have hω : ∀ ω : Ω, f ω ∈ L := by
    intro ω
    have h1 : f ω ∈ (IntermediateField.adjoin K (s : Set Ω)).map f :=
      (IntermediateField.mem_map _).2 ⟨ω, by rw [hs]; trivial, rfl⟩
    rw [IntermediateField.adjoin_map] at h1
    exact hK h1
  have hP : ∀ p : MvPolynomial (SVars D m) Ω,
      algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) p ∈ L := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h := hω a
      simpa [f, MvPolynomial.algebraMap_eq] using h
    | add p q hp hq =>
      rw [map_add]
      exact L.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact L.mul_mem hp (IntermediateField.subset_adjoin E S (Or.inr ⟨i, rfl⟩))
  have htop : L = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (SVars D m) Ω) z
    exact L.div_mem (hP a) (hP b)
  have hfd : FiniteDimensional E L :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end ReciprocityTheory.MultiplicativeHeights

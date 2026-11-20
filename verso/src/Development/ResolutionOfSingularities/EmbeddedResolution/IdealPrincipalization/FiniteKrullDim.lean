import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u v

open TopologicalSpace AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
A homeomorphism identifies the posets of irreducible closed sets and preserves the lengths of their strict chains. The two topological Krull dimensions are therefore equal, so finiteness transfers.
-/
private theorem topologicalKrullDim_lt_top_of_homeomorph {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (h : topologicalKrullDim B < ⊤) :
    topologicalKrullDim A < ⊤ := by
  rw [topologicalKrullDim_eq_of_homeomorph e]
  exact h

/- English proof (authored)
Take a point of the preirreducible set and any open neighborhood of it. That neighborhood meets the set, and so does the given open by hypothesis. Preirreducibility gives a point of the set in both opens. Thus every such neighborhood meets the intersection with the given open, proving the closure assertion.
-/
private theorem subset_closure_inter_of_isPreirreducible {X : Type u} [TopologicalSpace X]
    {S V : Set X} (hS : IsPreirreducible S) (hV : IsOpen V) (hne : (S ∩ V).Nonempty) :
    S ⊆ closure (S ∩ V) := by
  intro s hs
  rw [mem_closure_iff]
  intro W hW hsW
  obtain ⟨y, hyS, hyW, hyV⟩ := hS W V hW hV ⟨s, hs, hsW⟩ hne
  exact ⟨y, hyW, hyS, hyV⟩

/- English proof (authored)
The two closed sets have equal intersections with the open. The intersection with the larger irreducible set is nonempty because the smaller set meets it. This intersection is dense in the larger set and is contained in the smaller closed set. Thus the larger set lies in the smaller one, giving equality.
-/
private theorem eq_of_preimage_val_eq {X : Type u} [TopologicalSpace X] {W : Set X}
    (hW : IsOpen W) {C D : Set X} (hC : IsClosed C) (hD : IsIrreducible D) (hCsubD : C ⊆ D)
    (hne : (C ∩ W).Nonempty)
    (heq : (Subtype.val ⁻¹' C : Set ↥W) = (Subtype.val ⁻¹' D : Set ↥W)) : C = D := by
  refine subset_antisymm hCsubD ?_
  have h1 : D ∩ W ⊆ C := by
    rintro y ⟨hyD, hyW⟩
    have hy : (⟨y, hyW⟩ : ↥W) ∈ (Subtype.val ⁻¹' D : Set ↥W) := hyD
    rw [← heq] at hy
    exact hy
  obtain ⟨z, hzC, hzW⟩ := hne
  have h2 : (D ∩ W).Nonempty := ⟨z, hCsubD hzC, hzW⟩
  calc D ⊆ closure (D ∩ W) := subset_closure_inter_of_isPreirreducible hD.2 hW h2
    _ ⊆ closure C := closure_mono h1
    _ = C := hC.closure_eq

/- English proof (authored)
Take any finite strict chain of irreducible closed subsets. A point of its smallest member lies in some covering open, and this same point lies in every member. Intersect the chain with that open. Each intersection is nonempty, irreducible and closed in the open. The inclusions remain strict because equality of consecutive intersections would, by density in the irreducible sets, identify the two original closed subsets. Thus there is a chain of the same length in that covering open, whose dimension is bounded by the given bound. Taking the supremum over all original chains gives the result.
-/
private theorem topologicalKrullDim_le_of_iUnion_eq_univ {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)
    (c : WithBot ℕ∞) (h : ∀ i, topologicalKrullDim ↥(U i) ≤ c) :
    topologicalKrullDim X ≤ c := by
  refine iSup_le ?_
  intro p
  obtain ⟨x, hx⟩ := (p 0).isIrreducible.1
  have hxU : x ∈ ⋃ i, U i := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
  have hoe := (hU i).isOpenEmbedding_subtypeVal
  have hsub : ∀ j : Fin (p.length + 1),
      ((p 0 : IrreducibleCloseds X) : Set X) ⊆ ((p j : IrreducibleCloseds X) : Set X) :=
    fun j => SetLike.coe_subset_coe.mpr (LTSeries.monotone p (Fin.zero_le j))
  let V : Fin (p.length + 1) → IrreducibleCloseds ↥(U i) := fun j =>
    ⟨Subtype.val ⁻¹' ((p j : IrreducibleCloseds X) : Set X),
      ⟨⟨⟨x, hi⟩, hsub j hx⟩, (p j).isIrreducible.2.preimage hoe⟩,
      (p j).isClosed.preimage continuous_subtype_val⟩
  have hstep : ∀ j : Fin p.length, V j.castSucc < V j.succ := by
    intro j
    have hlt : p j.castSucc < p j.succ := p.step j
    have hsubset : ((p j.castSucc : IrreducibleCloseds X) : Set X)
        ⊆ ((p j.succ : IrreducibleCloseds X) : Set X) :=
      SetLike.coe_subset_coe.mpr hlt.le
    have hle : V j.castSucc ≤ V j.succ := by
      refine SetLike.coe_subset_coe.mp ?_
      intro z hz
      exact hsubset hz
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hcar : (Subtype.val ⁻¹' ((p j.castSucc : IrreducibleCloseds X) : Set X) : Set ↥(U i))
        = (Subtype.val ⁻¹' ((p j.succ : IrreducibleCloseds X) : Set X) : Set ↥(U i)) :=
      congrArg (fun s : IrreducibleCloseds ↥(U i) => (s : Set ↥(U i))) hEq
    have hCsubD : ((p j.castSucc : IrreducibleCloseds X) : Set X)
        = ((p j.succ : IrreducibleCloseds X) : Set X) :=
      eq_of_preimage_val_eq (hU i) (p j.castSucc).isClosed (p j.succ).isIrreducible hsubset
        ⟨x, hsub _ hx, hi⟩ hcar
    exact absurd (IrreducibleCloseds.ext hCsubD) hlt.ne
  let q : LTSeries (IrreducibleCloseds ↥(U i)) := ⟨p.length, V, hstep⟩
  have hq : ((q.length : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥(U i) :=
    Order.LTSeries.length_le_krullDim q
  exact le_trans hq (h i)

/- English proof (authored)
Apply the open-cover chain bound with the embedded natural number as the common bound for the dimensions of the open sets.
-/
theorem topologicalKrullDim_le_natCast_of_isOpenCover {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) (n : ℕ)
    (h : ∀ i, topologicalKrullDim ↥(U i) ≤ (n : WithBot ℕ∞)) :
    topologicalKrullDim X ≤ (n : WithBot ℕ∞) :=
  topologicalKrullDim_le_of_iUnion_eq_univ U hU hcov _ h

/- English proof (authored)
A natural number is finite in the extended natural numbers. Adjoining a bottom element preserves the distinction between that finite number and the top element.
-/
private theorem natCast_withBot_ne_top (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) ≠ ⊤ := by
  intro hcontra
  have h2 : ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_natCast]
    exact hcontra
  have h3 : (n : ℕ∞) = ⊤ := WithBot.coe_injective h2
  simp at h3

/- English proof (authored)
The embedded natural number is below top and distinct from it, so it is strictly below top.
-/
private theorem natCast_withBot_lt_top (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) < ⊤ :=
  lt_top_iff_ne_top.mpr (natCast_withBot_ne_top n)

/- English proof (authored)
An element below top in this ordered set is either bottom or an embedded natural number. In the first case zero bounds it, and in the second the corresponding natural number bounds it by equality.
-/
private theorem exists_le_natCast_of_lt_top {a : WithBot ℕ∞} (h : a < ⊤) :
    ∃ n : ℕ, a ≤ ((n : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact ⟨0, bot_le⟩
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd h (lt_irrefl _)
    | coe n => exact ⟨n, le_rfl⟩

/- English proof (authored)
Choose a natural upper bound for the dimension of each covering open. Their finite supremum is still a natural number and bounds every open's dimension. By the chain bound for open covers it bounds the dimension of the whole space. It lies strictly below top, as required.
-/
theorem topologicalKrullDim_lt_top_of_finite_isOpenCover {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Finite ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = Set.univ) (h : ∀ i, topologicalKrullDim ↥(U i) < ⊤) :
    topologicalKrullDim X < ⊤ := by
  classical
  choose N hN using fun i => exists_le_natCast_of_lt_top (h i)
  have : Fintype ι := Fintype.ofFinite ι
  have hle : topologicalKrullDim X ≤ (((Finset.univ.sup N : ℕ) : ℕ) : WithBot ℕ∞) := by
    refine topologicalKrullDim_le_natCast_of_isOpenCover U hU hcov _ ?_
    intro i
    exact le_trans (hN i) (Nat.mono_cast (Finset.le_sup (Finset.mem_univ i)))
  exact lt_of_le_of_lt hle (natCast_withBot_lt_top _)

/- English proof (authored)
Two and zero are distinct natural numbers. Both embeddings into the extended naturals and then into the order with a bottom element are injective, so their images remain distinct.
-/
private theorem two_ne_zero_withBotENat : (2 : WithBot ℕ∞) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ∞) : WithBot ℕ∞) = ((0 : ℕ∞) : WithBot ℕ∞) := h
  have h2 : (2 : ℕ∞) = 0 := WithBot.coe_injective h'
  simp at h2

/- English proof (authored)
For embedded finite numbers, multiplication and addition agree with multiplication and addition of natural numbers before embedding. This gives the equality for twice the given number plus one.
-/
private theorem two_mul_natCast_add_one (m : ℕ) :
    (2 : WithBot ℕ∞) * ((m : ℕ∞) : WithBot ℕ∞) + 1 = (((2 * m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have e2 : (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := rfl
  have e1 : (1 : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := rfl
  rw [e2, e1, ← WithBot.coe_mul, ← WithBot.coe_add]
  congr 1

/- English proof (authored)
Since the element is distinct from top, it is bottom or an embedded natural number. In the bottom case multiplying by the nonzero element two and adding one still gives bottom. In the finite case the result is the embedded natural number given by twice the number plus one. Both are strictly below top.
-/
private theorem two_mul_add_one_lt_top {a : WithBot ℕ∞} (h : a ≠ ⊤) : 2 * a + 1 < ⊤ := by
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.mul_bot two_ne_zero_withBotENat, WithBot.bot_add]
    exact bot_lt_top
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd rfl h
    | coe m =>
      refine lt_of_eq_of_lt ?_ (natCast_withBot_lt_top (2 * m + 1))
      exact two_mul_natCast_add_one m

/- English proof (authored)
Induct on the number of variables. With no variables the polynomial ring is the coefficient field and has dimension zero. With one more variable it is a univariate polynomial ring over the preceding multivariate polynomial ring. The polynomial-ring dimension bound is twice the preceding dimension plus one. By induction the preceding dimension is below top, so this bound is still below top.
-/
private theorem ringKrullDim_mvPolynomial_lt_top (k : Type u) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) < ⊤ := by
  induction n with
  | zero =>
    have h0 : ((0 : ℕ) : WithBot ℕ∞) = 0 := Nat.cast_zero
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)),
      ringKrullDim_eq_zero_of_field k, ← h0]
    exact natCast_withBot_lt_top 0
  | succ m ih =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.finSuccEquiv k m).toRingEquiv]
    exact lt_of_le_of_lt Polynomial.ringKrullDim_le (two_mul_add_one_lt_top (ne_of_lt ih))

/- English proof (authored)
A finite-type algebra over the field is a quotient of a polynomial ring in finitely many variables. A surjection does not increase Krull dimension, since it identifies prime ideals of the quotient with prime ideals containing the kernel. The polynomial ring has finite dimension by the preceding result, so the quotient does as well.
-/
theorem ringKrullDim_lt_top_of_finiteType (k : Type u) [Field k] (A : Type v) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : ringKrullDim A < ⊤ := by
  obtain ⟨n, φ, hφ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k A›
  refine lt_of_le_of_lt (ringKrullDim_le_of_surjective φ.toRingHom hφ) ?_
  exact ringKrullDim_mvPolynomial_lt_top k n

/- English proof (authored)
Topological Krull dimension of a prime spectrum equals the ring's Krull dimension. Apply the finite-type algebra bound.
-/
theorem topologicalKrullDim_primeSpectrum_lt_top (k : Type u) [Field k] (A : Type v) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : topologicalKrullDim (PrimeSpectrum A) < ⊤ := by
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_lt_top_of_finiteType k A

/- English proof (authored)
The underlying space of the affine scheme is the prime spectrum of its coordinate ring. The dimension bound for spectra of finite-type algebras therefore applies.
-/
theorem topologicalKrullDim_spec_lt_top (k : Type u) [Field k] (R : CommRingCat.{v})
    [Algebra k R] [Algebra.FiniteType k R] : topologicalKrullDim ↥(Spec R) < ⊤ :=
  topologicalKrullDim_primeSpectrum_lt_top k R

/- English proof (authored)
Local finite type of the structural map gives a finite-type map from the sections on the field spectrum to the sections on the affine open. The former ring identifies with the field, so the affine open's coordinate ring is a finite-type algebra over that field. The affine open is homeomorphic to the spectrum of this coordinate ring, whose dimension is finite.
-/
private theorem topologicalKrullDim_affineOpen_lt_top {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (hft : LocallyOfFiniteType f) {U : X.Opens}
    (hU : IsAffineOpen U) : topologicalKrullDim ↥((U : Set ↥X)) < ⊤ := by
  have hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) := le_top
  have hQ : RingHom.FiniteType ((f.appLE ⊤ U hle).hom) :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f hft
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of k))⟩ ⟨U, hU⟩ hle
  have hsurj : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom := by
    intro y
    refine ⟨((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom y, ?_⟩
    have hid := (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) y) hid
  let _ : Algebra k Γ(X, U) :=
    RingHom.toAlgebra (((f.appLE ⊤ U hle).hom).comp
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom)
  have : Algebra.FiniteType k Γ(X, U) :=
    hQ.comp (RingHom.FiniteType.of_surjective _ hsurj)
  have e : ↥((U : Set ↥X)) ≃ₜ ↥(Spec Γ(X, U)) := Scheme.homeoOfIso hU.isoSpec
  exact topologicalKrullDim_lt_top_of_homeomorph e (topologicalKrullDim_spec_lt_top k Γ(X, U))

/- English proof (authored)
The field spectrum is quasi-compact, and the inverse image of its whole space is quasi-compact by the given property of the structural map. Hence the affine opens admit a finite subcover of the scheme. Every member has finite dimension by local finite type and the affine-open result. The finite-cover dimension bound then gives finite dimension of the whole scheme.
-/
theorem topologicalKrullDim_lt_top_of_finiteType {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (hft : LocallyOfFiniteType f) (hqc : QuasiCompact f) :
    topologicalKrullDim ↥X < ⊤ := by
  classical
  have hcompact : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of k))) := by
    simp
  have : CompactSpace ↥X := by
    constructor
    have h := hqc.isCompact_preimage Set.univ isOpen_univ hcompact
    simpa using h
  have hcov : ⋃ i : X.affineOpens, ((i : X.Opens) : Set ↥X) = Set.univ := by
    rw [← Opens.coe_iSup, iSup_affineOpens_eq_top X, Opens.coe_top]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : X.affineOpens => ((i : X.Opens) : Set ↥X))
    (fun i => ((i : X.Opens)).isOpen) hcov.ge
  refine topologicalKrullDim_lt_top_of_finite_isOpenCover
    (ι := {i : X.affineOpens // i ∈ t})
    (fun i => ((i.1 : X.Opens) : Set ↥X)) (fun i => ((i.1 : X.Opens)).isOpen) ?_ ?_
  · refine Set.eq_univ_of_univ_subset ?_
    intro x _
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  · intro i
    exact topologicalKrullDim_affineOpen_lt_top f hft i.1.2

/- English proof (authored)
Admissibility gives a locally finite-type and quasi-compact structural map to the base field. The finite-dimension result for schemes with those properties applies to the marked ideal's ambient scheme.
-/
theorem MarkedIdealWithBoundary.IsAdmissible.topologicalKrullDim_lt_top {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) :
    topologicalKrullDim ↥T.scheme < ⊤ :=
  topologicalKrullDim_lt_top_of_finiteType T.structMap hT.locallyOfFiniteType hT.quasiCompact

end FunctorialResolution.EmbeddedResolution

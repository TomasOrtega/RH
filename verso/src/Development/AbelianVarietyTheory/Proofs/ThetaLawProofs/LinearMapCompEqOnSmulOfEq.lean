import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopologicalKrullDimLeOfFiniteCommonZeros
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignInsert
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SectionsSeparatePointsAndTangents
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIntegralOfIsIntegralOfIsAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open TopologicalSpace

namespace GlobalTheory.LineFinite

/- English proof (translation)
Set `e : W → IrreducibleCloseds W` to `fun p => ⟨closure {p}, isIrreducible_singleton.closure, isClosed_closure⟩`. Establish `he : ∀ p q : W, e p ≤ e q ↔ q.1 ⤳ p.1` using `fun p q => (specializes_iff_closure_subset (x := q) (y := p)).symm.trans (subtype_specializes_iff q p)`. Break down `Order.krullDim_le_one_iff.1 h (e ⟨b, hb⟩) with h' | h'` into its components or cases. Conclude with `Or.inr (hbc.antisymm ((he _ _).1 (h' ((he ⟨c, hc⟩ ⟨b, hb⟩).2 hbc)))).eq`. Conclude with `Or.inl (hab.antisymm ((he _ _).1 (h' ((he ⟨b, hb⟩ ⟨a, ha⟩).2 hab)))).eq`.
-/
theorem eq_or_eq_of_dim_le_one {T : Type*} [TopologicalSpace T] [T0Space T] {W : Set T}
    (h : topologicalKrullDim W ≤ 1) {a b c : T} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hab : a ⤳ b) (hbc : b ⤳ c) :
    a = b ∨ b = c := by
  let e : W → IrreducibleCloseds W := fun p => ⟨closure {p}, isIrreducible_singleton.closure, isClosed_closure⟩
  have he : ∀ p q : W, e p ≤ e q ↔ q.1 ⤳ p.1 := fun p q =>
    (specializes_iff_closure_subset (x := q) (y := p)).symm.trans (subtype_specializes_iff q p)
  rcases Order.krullDim_le_one_iff.1 h (e ⟨b, hb⟩) with h' | h'
  · exact Or.inr (hbc.antisymm ((he _ _).1 (h' ((he ⟨c, hc⟩ ⟨b, hb⟩).2 hbc)))).eq
  · exact Or.inl (hab.antisymm ((he _ _).1 (h' ((he ⟨b, hb⟩ ⟨a, ha⟩).2 hab)))).eq

/- English proof (translation)
Take `⟨S, hS, hc, hirr, rfl⟩` from `NoetherianSpace.exists_finite_set_isClosed_irreducible hZ`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Use `hi (hS.sUnion fun C hC => ?_)` and prove the remaining obligations. Take `⟨p, hp⟩` from `QuasiSober.sober (hirr C hC) (hc C hC)`.

Establish `: IsClosed ({p} : Set T)` using `hn p ⟨C, hC, hp.mem⟩`. Rewrite using `[← hp.def, this.closure_eq]`. Conclude with `Set.finite_singleton p`.
-/
theorem exists_not_isClosed {T : Type*} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T] {Z : Set T}
    (hZ : IsClosed Z) (hi : Z.Infinite) : ∃ p ∈ Z, ¬ IsClosed ({p} : Set T) := by
  obtain ⟨S, hS, hc, hirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  by_contra hn
  push Not at hn
  refine hi (hS.sUnion fun C hC => ?_)
  obtain ⟨p, hp⟩ := QuasiSober.sober (hirr C hC) (hc C hC)
  have : IsClosed ({p} : Set T) := hn p ⟨C, hC, hp.mem⟩
  rw [← hp.def, this.closure_eq]
  exact Set.finite_singleton p

/- English proof (translation)
Introduce `h`. Establish `hc : IsClosed (closure {p} ∩ closedPoints T)`. Rewrite using `[← Set.biUnion_of_singleton (closure {p} ∩ closedPoints T)]`. Conclude with `h.isClosed_biUnion fun x hx => hx.2`. Establish `e` using `JacobsonSpace.closure_inter_closedPoints (isClosed_closure (s := ({p} : Set T)))`.

Rewrite `e` using `[hc.closure_eq]`. Conclude with `hp (e.ge (subset_closure rfl)).2`.
-/
theorem infinite_closure_inter {T : Type*} [TopologicalSpace T] [JacobsonSpace T] {p : T}
    (hp : ¬ IsClosed ({p} : Set T)) : (closure {p} ∩ closedPoints T).Infinite := by
  intro h
  have hc : IsClosed (closure {p} ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (closure {p} ∩ closedPoints T)]
    exact h.isClosed_biUnion fun x hx => hx.2
  have e := JacobsonSpace.closure_inter_closedPoints (isClosed_closure (s := ({p} : Set T)))
  rw [hc.closure_eq] at e
  exact hp (e.ge (subset_closure rfl)).2

/- English proof (translation)
Take `⟨p, hp, hpc⟩` from `exists_not_isClosed hZ' hi`. Establish `hq : ¬ IsClosed ({φ p} : Set A)` using `fun h => hpc (by`. Use `h.preimage hφ` as an intermediate fact. Rewrite using `[(hfib _ h).eq_singleton_of_mem (show p ∈ φ ⁻¹' {φ p} from rfl)] at this)` and apply the resulting hypothesis. Establish `hWX : closure {φ p} ⊆ X` using `closure_minimal (Set.singleton_subset_iff.2 (hle hp)) hX`.

Take `⟨ζ, hζ⟩` from `QuasiSober.sober (hirr _ isClosed_closure (isIrreducible_singleton (x := φ p)).closure) (isClosed_closure.preimage hφ)`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc, hcp⟩ : ∃ c, p ⤳ c ∧ p ≠ c := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Use `hpc (closure_subset_iff_isClosed.1 fun c hc => ?_)` and prove the remaining obligations.

Conclude with `(hn c (specializes_iff_mem_closure.2 hc)).symm`. Establish `e : ζ = p` using `(eq_or_eq_of_dim_le_one hd (hWX hζ.mem) (hle hp) (hle (hc.mem_closed hZ' hp)) (hζ.specializes (subset_closure (s := {φ p}) rfl)) hc).resolve_right hcp`. Substitute `e` using the available equality. Establish `hsub : ∀ y ∈ closure {φ ζ}, φ ⁻¹' {y} ⊆ Z'` using `fun y hy a ha => (hζ.specializes (show φ a ∈ closure {φ ζ} from (show φ a = y from ha) ▸ hy)).mem_closed hZ' hp`. Take `⟨y₁, h₁, y₂, h₂, hne⟩` from `((infinite_closure_inter hq).sdiff hZ).nontrivial`.

Conclude with `⟨y₁, y₂, hne, h₁.1.2, h₂.1.2, hWX h₁.1.1, h₁.2, hsub _ h₁.1.1, hsub _ h₂.1.1⟩`.
-/
theorem exists_two_fibres {A A' : Type*} [TopologicalSpace A] [TopologicalSpace A'] [NoetherianSpace A']
    [QuasiSober A'] [T0Space A'] [JacobsonSpace A] {φ : A' → A} (hφ : Continuous φ)
    (hirr : ∀ W : Set A, IsClosed W → IsIrreducible W → IsIrreducible (φ ⁻¹' W))
    (hfib : ∀ y : A, IsClosed ({y} : Set A) → (φ ⁻¹' {y}).Subsingleton) {X Z : Set A} (hX : IsClosed X)
    (hZ : Z.Finite) (hd : topologicalKrullDim (φ ⁻¹' X) ≤ 1) {Z' : Set A'} (hZ' : IsClosed Z') (hle : Z' ⊆ φ ⁻¹' X)
    (hi : Z'.Infinite) : ∃ y₁ y₂ : A, y₁ ≠ y₂ ∧ IsClosed ({y₁} : Set A) ∧ IsClosed ({y₂} : Set A) ∧ y₁ ∈ X ∧ y₁ ∉ Z ∧
      φ ⁻¹' {y₁} ⊆ Z' ∧ φ ⁻¹' {y₂} ⊆ Z' := by
  obtain ⟨p, hp, hpc⟩ := exists_not_isClosed hZ' hi
  have hq : ¬ IsClosed ({φ p} : Set A) := fun h => hpc (by
    have := h.preimage hφ
    rwa [(hfib _ h).eq_singleton_of_mem (show p ∈ φ ⁻¹' {φ p} from rfl)] at this)
  have hWX : closure {φ p} ⊆ X := closure_minimal (Set.singleton_subset_iff.2 (hle hp)) hX
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hirr _ isClosed_closure (isIrreducible_singleton (x := φ p)).closure)
    (isClosed_closure.preimage hφ)
  obtain ⟨c, hc, hcp⟩ : ∃ c, p ⤳ c ∧ p ≠ c := by
    by_contra hn
    push Not at hn
    refine hpc (closure_subset_iff_isClosed.1 fun c hc => ?_)
    exact (hn c (specializes_iff_mem_closure.2 hc)).symm
  have e : ζ = p := (eq_or_eq_of_dim_le_one hd (hWX hζ.mem) (hle hp) (hle (hc.mem_closed hZ' hp))
    (hζ.specializes (subset_closure (s := {φ p}) rfl)) hc).resolve_right hcp
  subst e
  have hsub : ∀ y ∈ closure {φ ζ}, φ ⁻¹' {y} ⊆ Z' := fun y hy a ha =>
    (hζ.specializes (show φ a ∈ closure {φ ζ} from (show φ a = y from ha) ▸ hy)).mem_closed hZ' hp
  obtain ⟨y₁, h₁, y₂, h₂, hne⟩ := ((infinite_closure_inter hq).sdiff hZ).nontrivial
  exact ⟨y₁, y₂, hne, h₁.1.2, h₂.1.2, hWX h₁.1.1, h₁.2, hsub _ h₁.1.1, hsub _ h₂.1.1⟩

/- English proof (translation)
Set `I` to `Scheme.IdealSheafData.vanishingIdeal (X := A) ⟨W, hW⟩`. Establish `hI : Set.range I.subschemeι = W`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Both sides reduce to the same expression. Establish `: IrreducibleSpace I.subscheme`.

Use `Subtype.irreducibleSpace hi` as an intermediate fact. Establish `e : I.subscheme ≃ₜ W` using `(I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hI)`. Conclude with `e.irreducibleSpace_iff.2 this`. Establish `hg` using `GlobalTheory.geometricallyIrreducible_of_isAlgClosed (I.subschemeι ≫ p)`. Establish `: IrreducibleSpace ↥(pullback I.subschemeι φ)` using `hg.1 f (pullback.fst _ _) (pullback.snd _ _ ≫ p') ((IsPullback.of_hasPullback I.subschemeι φ).paste_vert h)`.

Rewrite using `[← hI, ← Scheme.Pullback.range_snd, ← Set.image_univ]`. Conclude with `(IrreducibleSpace.isIrreducible_univ _).image _ (pullback.snd I.subschemeι φ).continuous.continuousOn`.
-/
theorem isIrreducible_preimage {k K : Type} [Field k] [IsAlgClosed k] [Field K] {A A' : Scheme.{0}} {φ : A' ⟶ A}
    {p : A ⟶ Sp k} {p' : A' ⟶ Sp K} {f : Sp K ⟶ Sp k} [LocallyOfFiniteType p] (h : IsPullback φ p' p f)
    (W : Set A) (hW : IsClosed W) (hi : IsIrreducible W) : IsIrreducible (φ ⁻¹' W) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (X := A) ⟨W, hW⟩
  have hI : Set.range I.subschemeι = W := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have : IrreducibleSpace I.subscheme := by
    have := Subtype.irreducibleSpace hi
    have e : I.subscheme ≃ₜ W := (I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hI)
    exact e.irreducibleSpace_iff.2 this
  have hg := GlobalTheory.geometricallyIrreducible_of_isAlgClosed (I.subschemeι ≫ p)
  have : IrreducibleSpace ↥(pullback I.subschemeι φ) := hg.1 f (pullback.fst _ _) (pullback.snd _ _ ≫ p')
    ((IsPullback.of_hasPullback I.subschemeι φ).paste_vert h)
  rw [← hI, ← Scheme.Pullback.range_snd, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (pullback.snd I.subschemeι φ).continuous.continuousOn

/- English proof (translation)
Establish `e₁ : w q ∈ Out.nonzeroLocus s ↔ w q ∈ X.basicOpen (s.f c)`. Rewrite using `[← GlobalTheory.nonzeroLocus_inf_chart s c]`. Conclude with `⟨fun h' => ⟨h', h (show q ∈ ⊤ from trivial)⟩, fun h' => h'.1⟩`. Establish `e₂` using `Scheme.basicOpen_appLE w ⊤ (M.U c) h (s.f c)`. Rewrite `e₂` using `[basicOpen_eq_of_affine', top_inf_eq]`.

Rewrite using `[e₁, EtBaseChange.valT_eq _ _ h]`. Express the relevant statement in the definitionally equal form `q ∈ w ⁻¹ᵁ X.basicOpen (s.f c) ↔ _`. Rewrite using `[← e₂]`. Express the relevant statement in the definitionally equal form `EtBaseChange.valH w (M.U c) h (s.f c) ∉ q.asIdeal ↔ _`. Rewrite using `[show q.asIdeal = ⊥ from congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum K) q ⊥), Ideal.mem_bot]`.
-/
theorem mem_nonzeroLocus_iff {K : Type} [Field K] {X : Scheme.{0}} {M : LB X} (s : LB.Sec M) (w : Sp K ⟶ X) (c : M.ι)
    (h : ⊤ ≤ w ⁻¹ᵁ M.U c) (q : Sp K) : w q ∈ Out.nonzeroLocus s ↔ valT w (M.U c) (s.f c) ≠ 0 := by
  have e₁ : w q ∈ Out.nonzeroLocus s ↔ w q ∈ X.basicOpen (s.f c) := by
    rw [← GlobalTheory.nonzeroLocus_inf_chart s c]
    exact ⟨fun h' => ⟨h', h (show q ∈ ⊤ from trivial)⟩, fun h' => h'.1⟩
  have e₂ := Scheme.basicOpen_appLE w ⊤ (M.U c) h (s.f c)
  rw [basicOpen_eq_of_affine', top_inf_eq] at e₂
  rw [e₁, EtBaseChange.valT_eq _ _ h]
  change q ∈ w ⁻¹ᵁ X.basicOpen (s.f c) ↔ _
  rw [← e₂]
  change EtBaseChange.valH w (M.U c) h (s.f c) ∉ q.asIdeal ↔ _
  rw [show q.asIdeal = ⊥ from congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum K) q ⊥), Ideal.mem_bot]

/- English proof (translation)
Establish `ht : t ≠ 0`. Introduce and unpack `rfl`. Simplify using `[ha] at h₁`. Establish `h₃ : ∑ j, (a₂ * β₁ j - a₁ * β₂ j) • T j = 0`. Establish `: ∑ j, (a₂ * β₁ j - a₁ * β₂ j) • T j = algebraMap k K a₂ * ∑ j, T j * algebraMap k K (β₁ j) - algebraMap k K a₁ * ∑ j, T j * algebraMap k K (β₂ j)`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_sub, map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Use `mul_left_cancel₀ ht ?_` and prove the remaining obligations. Take the linear combination `algebraMap k K a₂ * h₁ - algebraMap k K a₁ * h₂`. Establish `h₄` using `Fintype.linearIndependent_iff.1 hT _ h₃`. Use `mul_left_cancel₀ ha ?_` and prove the remaining obligations. Establish `: a₁ * ∑ j, c j * β₂ j = a₂ * ∑ j, c j * β₁ j`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Take the linear combination `(-c j) * h₄ j`. Rewrite using `[this, hc]`. Simplify using the standard rewrite rules.
-/
theorem linearMap_comp_eq_on_smul_of_eq {k K : Type} [Field k] [Field K] [Algebra k K] {N : ℕ} {T : Fin N → K} (hT : LinearIndependent k T)
    (t : K) (a₁ a₂ : k) (β₁ β₂ c : Fin N → k) (ha : a₁ ≠ 0)
    (h₁ : (1 - t) * algebraMap k K a₁ + t * ∑ j, T j * algebraMap k K (β₁ j) = 0)
    (h₂ : (1 - t) * algebraMap k K a₂ + t * ∑ j, T j * algebraMap k K (β₂ j) = 0)
    (hc : ∑ j, c j * β₁ j = 0) : ∑ j, c j * β₂ j = 0 := by
  have ht : t ≠ 0 := by
    rintro rfl
    simp [ha] at h₁
  have h₃ : ∑ j, (a₂ * β₁ j - a₁ * β₂ j) • T j = 0 := by
    have : ∑ j, (a₂ * β₁ j - a₁ * β₂ j) • T j = algebraMap k K a₂ * ∑ j, T j * algebraMap k K (β₁ j) -
        algebraMap k K a₁ * ∑ j, T j * algebraMap k K (β₂ j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, map_sub, map_mul, map_mul]
      ring
    rw [this]
    refine mul_left_cancel₀ ht ?_
    linear_combination algebraMap k K a₂ * h₁ - algebraMap k K a₁ * h₂
  have h₄ := Fintype.linearIndependent_iff.1 hT _ h₃
  refine mul_left_cancel₀ ha ?_
  have : a₁ * ∑ j, c j * β₂ j = a₂ * ∑ j, c j * β₁ j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (-c j) * h₄ j
  rw [this, hc]
  simp

/- English proof (translation)
Rewrite using `[hc i]`. Use `(EtBaseChange.valT_eq (T := R) z.left _ h _).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun j _ => ?_))` and prove the remaining obligations. Use `(map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (EtBaseChange.valT_eq (T := R) z.left _ h _).symm)` and prove the remaining obligations. Conclude with `(EtBaseChange.valT_eq (T := R) z.left _ h _).symm.trans (KoszulCx.valH_cst x z _ h _)`.
-/
theorem valT_coords {R : Type} [CommRing R] {x : KeyIn R} {l N : ℕ} {b : Fin N → RR x l} {c : Fin N → R}
    {f : ∀ i, Γ(x.P.A.left, x.P.L.U i)} (hc : Coords x b c f) (z : Pt x) (i : x.P.L.ι)
    (h : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U i) :
    valT (T := R) z.left (x.P.L.U i) (f i) = ∑ j, c j * valT (T := R) z.left (x.P.L.U i) ((b j).f i) := by
  rw [hc i]
  refine (EtBaseChange.valT_eq (T := R) z.left _ h _).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun j _ => ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (EtBaseChange.valT_eq (T := R) z.left _ h _).symm)
  exact (EtBaseChange.valT_eq (T := R) z.left _ h _).symm.trans (KoszulCx.valH_cst x z _ h _)

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_chart x.P.isLB (z.left (IsLocalRing.closedPoint K))`. Conclude with `⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map z.left.continuous).mem_open (x.P.L.U i).isOpen hi⟩`.
-/
theorem exists_chart_pt {K : Type} [Field K] (x : KeyIn K) (z : Pt x) : ∃ i, ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U i := by
  obtain ⟨i, hi⟩ := exists_chart x.P.isLB (z.left (IsLocalRing.closedPoint K))
  exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map z.left.continuous).mem_open (x.P.L.U i).isOpen hi⟩

section Via
variable {k K : Type} [Field k] [Field K] {x : KeyIn k} {x' : KeyIn K} {f : k →+* K} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}

/- English proof (translation)
Use `x.P.isAb.proper` as an intermediate fact. Set `z : Pt x` to `Over.homMk (pointOfClosedPoint x.P.A.hom y hy) (pointOfClosedPoint_comp x.P.A.hom y hy)`. Establish `hz : ∀ q : Sp k, z.left q = y` using `fun q => pointOfClosedPoint_apply x.P.A.hom y hy q`. Establish `hw : (spMap f ≫ z.left) ≫ x.P.A.hom = 𝟙 _ ≫ spMap f` using `(Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (Over.w z)).trans ((Category.comp_id _).trans (Category.id_comp _).symm))`. Set `z' : Pt x'` to `Over.homMk (hp.lift (spMap f ≫ z.left) (𝟙 _) hw) (hp.lift_snd _ _ _)`.

Establish `hz' : z'.left ≫ φ = spMap f ≫ z.left` using `hp.lift_fst _ _ _`. Use `⟨z, z', hz, hz', fun a ha => ?_⟩` and prove the remaining obligations. Establish `sq : IsPullback (spMap f) z'.left z.left φ`. Use `IsPullback.of_bot (t := hp) ?_ hz'.symm` and prove the remaining obligations. Establish `e₁ : z'.left ≫ x'.P.A.hom = 𝟙 _` using `Over.w z'`.

Establish `e₂ : z.left ≫ x.P.A.hom = 𝟙 _` using `Over.w z`. Rewrite using `[e₁, e₂]`. Conclude with `IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp K)) (f := 𝟙 (Sp k)) (g := spMap f) ⟨by simp⟩`. Take `⟨q, -, hq⟩` from `Scheme.exists_preimage_of_isPullback sq (IsLocalRing.closedPoint k) a ((hz _).trans ha.symm)`. Conclude with `⟨q, hq⟩`.
-/
theorem exists_pt [IsAlgClosed k] (hp : IsPullback φ x'.P.A.hom x.P.A.hom (spMap f)) (y : x.P.A.left)
    (hy : IsClosed ({y} : Set x.P.A.left)) : ∃ (z : Pt x) (z' : Pt x'), (∀ q : Sp k, z.left q = y) ∧
      z'.left ≫ φ = spMap f ≫ z.left ∧ ∀ a, φ a = y → ∃ q : Sp K, z'.left q = a := by
  have := x.P.isAb.proper
  let z : Pt x := Over.homMk (pointOfClosedPoint x.P.A.hom y hy) (pointOfClosedPoint_comp x.P.A.hom y hy)
  have hz : ∀ q : Sp k, z.left q = y := fun q => pointOfClosedPoint_apply x.P.A.hom y hy q
  have hw : (spMap f ≫ z.left) ≫ x.P.A.hom = 𝟙 _ ≫ spMap f :=
    (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (Over.w z)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  let z' : Pt x' := Over.homMk (hp.lift (spMap f ≫ z.left) (𝟙 _) hw) (hp.lift_snd _ _ _)
  have hz' : z'.left ≫ φ = spMap f ≫ z.left := hp.lift_fst _ _ _
  refine ⟨z, z', hz, hz', fun a ha => ?_⟩
  have sq : IsPullback (spMap f) z'.left z.left φ := by
    refine IsPullback.of_bot (t := hp) ?_ hz'.symm
    have e₁ : z'.left ≫ x'.P.A.hom = 𝟙 _ := Over.w z'
    have e₂ : z.left ≫ x.P.A.hom = 𝟙 _ := Over.w z
    rw [e₁, e₂]
    exact IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp K)) (f := 𝟙 (Sp k)) (g := spMap f) ⟨by simp⟩
  obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback sq (IsLocalRing.closedPoint k) a ((hz _).trans ha.symm)
  exact ⟨q, hq⟩

/- English proof (translation)
Establish `hφ : ⊤ ≤ (z'.left ≫ φ) ⁻¹ᵁ x.P.L.U c` using `fun p _ => by`. Rewrite using `[hz]`. Conclude with `h (show spMap f p ∈ ⊤ from trivial)`. Use `⟨_, fun s s' hs => Eq.trans ?_ (EtBaseChange.valT_via (T := K) hs z'.left c c' hφ h')⟩` and prove the remaining obligations. Conclude with `((congrArg (fun q => valT (T := K) q (x.P.L.U c) (s.f c)) hz).trans (EtBaseChange.valT_spMap f z.left h _)).symm`.
-/
theorem exists_unit (z : Pt x) (z' : Pt x') (hz : z'.left ≫ φ = spMap f ≫ z.left) (c : x.P.L.ι) (c' : x'.P.L.ι)
    (h : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ z'.left ⁻¹ᵁ x'.P.L.U c') (l : ℕ) :
    ∃ u : K, ∀ (s : RR x l) (s' : RR x' l), SecVia x' x φ w s' s →
      f (valT (T := k) z.left (x.P.L.U c) (s.f c)) = u * valT (T := K) z'.left (x'.P.L.U c') (s'.f c') := by
  have hφ : ⊤ ≤ (z'.left ≫ φ) ⁻¹ᵁ x.P.L.U c := fun p _ => by
    rw [hz]
    exact h (show spMap f p ∈ ⊤ from trivial)
  refine ⟨_, fun s s' hs => Eq.trans ?_ (EtBaseChange.valT_via (T := K) hs z'.left c c' hφ h')⟩
  exact ((congrArg (fun q => valT (T := K) q (x.P.L.U c) (s.f c)) hz).trans
    (EtBaseChange.valT_spMap f z.left h _)).symm

/- English proof (translation)
Take `⟨c', h'⟩` from `exists_chart_pt x' z'`. Take `⟨u, hu⟩` from `exists_unit (w := w) z z' hz c c' h h' n`. Establish `e₀ : valT (T` using `K) z'.left (x'.P.L.U c') (σ.f c') = 0 := not_not.1 fun e => h0 ((mem_nonzeroLocus_iff σ z'.left c' h' q).2 e)`. Establish `e₁ : valT (T` using `K) z'.left (x'.P.L.U c') (σ.f c') = (1 - t) * valT (T := K) z'.left (x'.P.L.U c') (s₀.f c') + t * valT (T := K) z'.left (x'.P.L.U c') (s₁.f c') := by`. Establish `v` using `EtBaseChange.valT_eq (T := K) z'.left _ h'`.

Use `(congrArg (valT (T := K) z'.left (x'.P.L.U c')) (hσ c')).trans ((v _).trans ((map_add _ _ _).trans ?_))` and prove the remaining obligations. Use `congrArg₂ (· + ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (v _).symm)) ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (v _).symm))` and prove the remaining obligations. Conclude with `(v _).symm.trans (KoszulCx.valH_cst x' z' _ h' _)`. Conclude with `(v _).symm.trans (KoszulCx.valH_cst x' z' _ h' _)`. Establish `e₂` using `valT_coords hT z' c' h'`.

Establish `e₃ : ∑ j, T j * f (valT (T` using `k) z.left (x.P.L.U c) ((b j).f c)) = u * valT (T := K) z'.left (x'.P.L.U c') (s₁.f c') := by`. Rewrite using `[e₂, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => (congrArg (T j * ·) (hu _ _ (hb j))).trans (mul_left_comm _ _ _)`. Rewrite using `[e₃, hu _ _ hs]`. Take the linear combination `u * (e₁.symm.trans e₀)`.
-/
theorem relation {n N : ℕ} {b : Fin N → RR x n} {b' : Fin N → RR x' n} (hb : ∀ j, SecVia x' x φ w (b' j) (b j))
    {s : RR x n} {σ s₀ s₁ : RR x' n} (hs : SecVia x' x φ w s₀ s) {T : Fin N → K} (hT : Coords x' b' T s₁.f) {t : K}
    (hσ : ∀ c, (show Γ(x'.P.A.left, x'.P.L.U c) from σ.f c) =
      AbLaw.cst x'.P.A.hom _ (1 - t) * (show Γ(x'.P.A.left, x'.P.L.U c) from s₀.f c) +
        AbLaw.cst x'.P.A.hom _ t * (show Γ(x'.P.A.left, x'.P.L.U c) from s₁.f c))
    (z : Pt x) (z' : Pt x') (hz : z'.left ≫ φ = spMap f ≫ z.left) (c : x.P.L.ι) (h : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c)
    (q : Sp K) (h0 : z'.left q ∉ Out.nonzeroLocus σ) :
    (1 - t) * f (valT (T := k) z.left (x.P.L.U c) (s.f c)) +
      t * ∑ j, T j * f (valT (T := k) z.left (x.P.L.U c) ((b j).f c)) = 0 := by
  obtain ⟨c', h'⟩ := exists_chart_pt x' z'
  obtain ⟨u, hu⟩ := exists_unit (w := w) z z' hz c c' h h' n
  have e₀ : valT (T := K) z'.left (x'.P.L.U c') (σ.f c') = 0 :=
    not_not.1 fun e => h0 ((mem_nonzeroLocus_iff σ z'.left c' h' q).2 e)
  have e₁ : valT (T := K) z'.left (x'.P.L.U c') (σ.f c') =
      (1 - t) * valT (T := K) z'.left (x'.P.L.U c') (s₀.f c') + t * valT (T := K) z'.left (x'.P.L.U c') (s₁.f c') := by
    have v := EtBaseChange.valT_eq (T := K) z'.left _ h'
    refine (congrArg (valT (T := K) z'.left (x'.P.L.U c')) (hσ c')).trans ((v _).trans ((map_add _ _ _).trans ?_))
    refine congrArg₂ (· + ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (v _).symm))
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (v _).symm))
    · exact (v _).symm.trans (KoszulCx.valH_cst x' z' _ h' _)
    · exact (v _).symm.trans (KoszulCx.valH_cst x' z' _ h' _)
  have e₂ := valT_coords hT z' c' h'
  have e₃ : ∑ j, T j * f (valT (T := k) z.left (x.P.L.U c) ((b j).f c)) =
      u * valT (T := K) z'.left (x'.P.L.U c') (s₁.f c') := by
    rw [e₂, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (congrArg (T j * ·) (hu _ _ (hb j))).trans (mul_left_comm _ _ _)
  rw [e₃, hu _ _ hs]
  linear_combination u * (e₁.symm.trans e₀)

end Via

end GlobalTheory.LineFinite

open GlobalTheory.LineFinite in

/- English proof (translation)
Introduce `hL k K _ _ _ _ _ x x' φ w n b b' r s s' i₀ s₀ s₁ T t hn ⟨_, _, _, hp, _⟩ hb hb' hs hT hs' hs₀ hs₁ hσ`. Use `x.P.isAb.proper` as an intermediate fact. Use `x'.P.isAb.proper` as an intermediate fact. Use `LocallyOfFiniteType.jacobsonSpace x.P.A.hom` as an intermediate fact. Use `LocallyOfFiniteType.isLocallyNoetherian x'.P.A.hom` as an intermediate fact.

Establish `: CompactSpace x'.P.A.left` using `QuasiCompact.compactSpace_of_compactSpace x'.P.A.hom`. Establish `: IsNoetherian x'.P.A.left` using `{}`. Establish `cl : ∀ {Y : Scheme.{0}} {J : Type} (P : J → Prop) (D : J → Y.Opens), IsClosed {y : Y | ∀ i, P i → y ∉ D i}` using `fun P D => by`. Simplify using `only [Set.ofPred_forall]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun _ => (D i).isOpen.isClosed_compl`.

Establish `hfib : ∀ y : x.P.A.left, IsClosed ({y} : Set x.P.A.left) → (φ ⁻¹' {y}).Subsingleton` using `fun y hy a ha a' ha' => by`. Take `⟨z, z', -, -, h⟩` from `exists_pt hp.1 y hy`. Take `⟨q, rfl⟩` from `h a ha`. Take `⟨q', rfl⟩` from `h a' ha'`. Conclude with `congrArg z'.left (Subsingleton.elim (α := PrimeSpectrum K) q q')`.

Set `X : Set x.P.A.left` to `{y | ∀ i, i ≠ i₀ → y ∉ Out.nonzeroLocus (s i)}`. Set `Z : Set x.P.A.left` to `{y | ∀ i, y ∉ Out.nonzeroLocus (s i)}`. Set `Z' : Set x'.P.A.left` to `{y | ∀ i, y ∉ Out.nonzeroLocus (s' i)}`. Establish `hX : IsClosed X` using `cl _ _`. Establish `hZ : IsClosed Z` using `by simpa using cl (fun _ => True) fun i => Out.nonzeroLocus (s i)`.

Establish `hZ' : IsClosed Z'` using `by simpa using cl (fun _ => True) fun i => Out.nonzeroLocus (s' i)`. Establish `hle : Z' ⊆ φ ⁻¹' X` using `fun y hy i hi h => hy i (EtBaseChange.mem_nonzeroLocus_via (hs' i hi) y h)`. Assume the negation of the conclusion as `hi`. Establish `hi' : Z'.Infinite` using `hi`. Establish `hfin : (φ ⁻¹' Z).Finite` using `Set.Finite.preimage' hs fun y hy => (hfib y (GlobalTheory.DimCut.isClosed_singleton_of_finite hZ hs hy)).finite`.

Establish `hd : topologicalKrullDim (φ ⁻¹' X) ≤ 1`. Use `GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros hL K x' n 1 (fun _ => s₀) (φ ⁻¹' X) (by omega) (hX.preimage φ.continuous) (hi'.nonempty.mono hle) (hfin.subset fun y hy i h => by` as an intermediate fact. Distinguish the cases in `e : i = i₀`. Substitute `e` using the available equality. Conclude with `hy.2 0 (EtBaseChange.mem_nonzeroLocus_via hs₀ y h)`.

Conclude with `hy.1 i e h)`. Conclude with `this` after adjusting the coercions. Take `⟨y₁, y₂, hne, c₁, c₂, hX₁, hZ₁, l₁, l₂⟩` from `exists_two_fibres φ.continuous (isIrreducible_preimage hp.1) hfib hX (Z := Z) hs hd hZ' hle hi'`. Take `⟨z₁, z₁', p₁, e₁, -⟩` from `exists_pt hp.1 y₁ c₁`. Take `⟨z₂, z₂', p₂, e₂, -⟩` from `exists_pt hp.1 y₂ c₂`.

Take `⟨d₁, h₁⟩` from `exists_chart_pt x z₁`. Take `⟨d₂, h₂⟩` from `exists_chart_pt x z₂`. Set `q : Sp K` to `IsLocalRing.closedPoint K`. Set `q₀ : Sp k` to `IsLocalRing.closedPoint k`. Establish `r₁` using `relation hb' hs₀ hs₁ hσ z₁ z₁' e₁ d₁ h₁ q (l₁ (show φ (z₁'.left q) = y₁ from (congrArg (fun m => m q) e₁).trans (p₁ _)) i₀)`.

Establish `r₂` using `relation hb' hs₀ hs₁ hσ z₂ z₂' e₂ d₂ h₂ q (l₂ (show φ (z₂'.left q) = y₂ from (congrArg (fun m => m q) e₂).trans (p₂ _)) i₀)`. Establish `ha : valT (T` using `k) z₁.left (x.P.L.U d₁) ((s i₀).f d₁) ≠ 0 := by`. Use `(mem_nonzeroLocus_iff (s i₀) z₁.left d₁ h₁ q₀).1 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `hZ₁ fun i => ?_` and prove the remaining obligations.

Distinguish the cases in `e : i = i₀`. Rewrite using `[e, ← p₁ q₀]`. Conclude with `h`. Conclude with `hX₁ i e`. Take `⟨σ, hσ₁, hσ₂⟩` from `(GlobalTheory.KeyKa.sections_separate_points_and_tangents hL k x n hn).2 z₁ z₂ d₁ d₂ (fun e => hne ((p₁ q₀).symm.trans (e ▸ p₂ q₀))) h₁ h₂`.

Take `⟨c, hc, -⟩` from `hb σ`. Conclude with `hσ₂ ((valT_coords hc z₂ d₂ h₂).trans (linearMap_comp_eq_on_smul_of_eq hT.linearIndependent t _ _ _ _ c ha r₁ r₂ ((valT_coords hc z₁ d₁ h₁).symm.trans hσ₁)))`.
-/
theorem GlobalTheory.KeyKa.finZ_of_line_towards_generic : Out.Laws → ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n : ℕ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (r : ℕ) (s : Fin r → RR x n) (s' : Fin r → RR x' n) (i₀ : Fin r) (s₀ s₁ : RR x' n) (T : Fin (n ^ x.P.g) → K) (t : K), 4 ≤ n → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → FinZ x s → AlgebraicIndependent k T → (∀ i, i ≠ i₀ → SecVia x' x φ w (s' i) (s i)) → SecVia x' x φ w s₀ (s i₀) → Coords x' b' T s₁.f → (∀ c, (show Γ(x'.P.A.left, x'.P.L.U c) from (s' i₀).f c) = AbLaw.cst x'.P.A.hom _ (1 - t) * (show Γ(x'.P.A.left, x'.P.L.U c) from s₀.f c) + AbLaw.cst x'.P.A.hom _ t * (show Γ(x'.P.A.left, x'.P.L.U c) from s₁.f c)) → FinZ x' s' := by
  intro hL k K _ _ _ _ _ x x' φ w n b b' r s s' i₀ s₀ s₁ T t hn ⟨_, _, _, hp, _⟩ hb hb' hs hT hs' hs₀ hs₁ hσ
  have := x.P.isAb.proper
  have := x'.P.isAb.proper
  have := LocallyOfFiniteType.jacobsonSpace x.P.A.hom
  have := LocallyOfFiniteType.isLocallyNoetherian x'.P.A.hom
  have : CompactSpace x'.P.A.left := QuasiCompact.compactSpace_of_compactSpace x'.P.A.hom
  have : IsNoetherian x'.P.A.left := {}
  have cl : ∀ {Y : Scheme.{0}} {J : Type} (P : J → Prop) (D : J → Y.Opens), IsClosed {y : Y | ∀ i, P i → y ∉ D i} :=
    fun P D => by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => (D i).isOpen.isClosed_compl
  have hfib : ∀ y : x.P.A.left, IsClosed ({y} : Set x.P.A.left) → (φ ⁻¹' {y}).Subsingleton := fun y hy a ha a' ha' => by
    obtain ⟨z, z', -, -, h⟩ := exists_pt hp.1 y hy
    obtain ⟨q, rfl⟩ := h a ha
    obtain ⟨q', rfl⟩ := h a' ha'
    exact congrArg z'.left (Subsingleton.elim (α := PrimeSpectrum K) q q')
  let X : Set x.P.A.left := {y | ∀ i, i ≠ i₀ → y ∉ Out.nonzeroLocus (s i)}
  let Z : Set x.P.A.left := {y | ∀ i, y ∉ Out.nonzeroLocus (s i)}
  let Z' : Set x'.P.A.left := {y | ∀ i, y ∉ Out.nonzeroLocus (s' i)}
  have hX : IsClosed X := cl _ _
  have hZ : IsClosed Z := by simpa using cl (fun _ => True) fun i => Out.nonzeroLocus (s i)
  have hZ' : IsClosed Z' := by simpa using cl (fun _ => True) fun i => Out.nonzeroLocus (s' i)
  have hle : Z' ⊆ φ ⁻¹' X := fun y hy i hi h => hy i (EtBaseChange.mem_nonzeroLocus_via (hs' i hi) y h)
  by_contra hi
  have hi' : Z'.Infinite := hi
  have hfin : (φ ⁻¹' Z).Finite := Set.Finite.preimage' hs fun y hy =>
    (hfib y (GlobalTheory.DimCut.isClosed_singleton_of_finite hZ hs hy)).finite
  have hd : topologicalKrullDim (φ ⁻¹' X) ≤ 1 := by
    have := GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros hL K x' n 1 (fun _ => s₀) (φ ⁻¹' X) (by omega)
      (hX.preimage φ.continuous) (hi'.nonempty.mono hle) (hfin.subset fun y hy i h => by
        by_cases e : i = i₀
        · subst e
          exact hy.2 0 (EtBaseChange.mem_nonzeroLocus_via hs₀ y h)
        · exact hy.1 i e h)
    exact_mod_cast this
  obtain ⟨y₁, y₂, hne, c₁, c₂, hX₁, hZ₁, l₁, l₂⟩ := exists_two_fibres φ.continuous (isIrreducible_preimage hp.1) hfib
    hX (Z := Z) hs hd hZ' hle hi'
  obtain ⟨z₁, z₁', p₁, e₁, -⟩ := exists_pt hp.1 y₁ c₁
  obtain ⟨z₂, z₂', p₂, e₂, -⟩ := exists_pt hp.1 y₂ c₂
  obtain ⟨d₁, h₁⟩ := exists_chart_pt x z₁
  obtain ⟨d₂, h₂⟩ := exists_chart_pt x z₂
  let q : Sp K := IsLocalRing.closedPoint K
  let q₀ : Sp k := IsLocalRing.closedPoint k
  have r₁ := relation hb' hs₀ hs₁ hσ z₁ z₁' e₁ d₁ h₁ q
    (l₁ (show φ (z₁'.left q) = y₁ from (congrArg (fun m => m q) e₁).trans (p₁ _)) i₀)
  have r₂ := relation hb' hs₀ hs₁ hσ z₂ z₂' e₂ d₂ h₂ q
    (l₂ (show φ (z₂'.left q) = y₂ from (congrArg (fun m => m q) e₂).trans (p₂ _)) i₀)
  have ha : valT (T := k) z₁.left (x.P.L.U d₁) ((s i₀).f d₁) ≠ 0 := by
    refine (mem_nonzeroLocus_iff (s i₀) z₁.left d₁ h₁ q₀).1 ?_
    by_contra h
    refine hZ₁ fun i => ?_
    by_cases e : i = i₀
    · rw [e, ← p₁ q₀]
      exact h
    · exact hX₁ i e
  obtain ⟨σ, hσ₁, hσ₂⟩ := (GlobalTheory.KeyKa.sections_separate_points_and_tangents hL k x n hn).2 z₁ z₂ d₁ d₂
    (fun e => hne ((p₁ q₀).symm.trans (e ▸ p₂ q₀))) h₁ h₂
  obtain ⟨c, hc, -⟩ := hb σ
  exact hσ₂ ((valT_coords hc z₂ d₂ h₂).trans (linearMap_comp_eq_on_smul_of_eq hT.linearIndependent t _ _ _ _ c ha r₁ r₂
    ((valT_coords hc z₁ d₁ h₁).symm.trans hσ₁)))

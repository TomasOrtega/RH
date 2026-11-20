import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePlacesLgNeZero

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.HtTwist

/- English proof (translation)
Use `isClosed_singleton_iff_isClosedImmersion.1 hx` as an intermediate fact. Take `⟨φ, hφ⟩` from `Spec.map_surjective (X.fromSpecResidueField x ≫ s)`. Establish `hfin : IsFinite (Spec.map φ)`. Rewrite using `[hφ]`. Conclude with `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance`.

Use `letI : Algebra k (X.residueField x) := φ.hom.toAlgebra`. Use `haveI : Module.Finite k (X.residueField x) := (IsFinite.SpecMap_iff φ).1 hfin`. Use `⟨Module.finrank k (X.residueField x), Module.finrank_pos.ne', fun K _ _ σ => ?_⟩` and prove the remaining obligations. Use `letI : Algebra k K := σ.toAlgebra`. Establish `hP (ψ : X.residueField x →ₐ[k] K) : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x) ≫ s = spMap σ`.

Establish `h : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom σ` using `CommRingCat.hom_ext ψ.comp_algebraMap`. Rewrite using `[Category.assoc, ← hφ, ← Spec.map_comp]`. Conclude with `congrArg Spec.map h`. Set `P : (X.residueField x →ₐ[k] K) → {y : {y : Sp K ⟶ X // y ≫ s = spMap σ} // below y.1 = x}` to `fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, hP ψ⟩, ExtConj.below_comp x _⟩`. Establish `hb : Function.Bijective P`.

Use `⟨fun a b h => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ X.fromSpecResidueField x = Spec.map (CommRingCat.ofHom b.toRingHom) ≫ X.fromSpecResidueField x` using `congrArg (fun t => t.1.1) h`. Establish `h2` using `congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h1))`. Conclude with `AlgHom.coe_ringHom_injective h2`. Introduce and unpack `⟨⟨y, hy⟩, hyx⟩`.

Take `⟨ψ, h⟩` from `ExtConj.factor y x hyx`. Establish `h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom σ)`. Rewrite using `[Spec.map_comp, hφ, ← Category.assoc, h]`. Conclude with `hy`. Establish `h3` using `Spec.map_injective h2`.

Conclude with `⟨⟨ψ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext (Subtype.ext h)⟩`. Rewrite using `[← Nat.card_congr (Equiv.ofBijective P hb), Nat.card_eq_fintype_card, AlgHom.card]`.
-/
theorem exists_card {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} (s : X ⟶ Sp k)
    [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (σ : k →+* K),
      Nat.card {y : {y : Sp K ⟶ X // y ≫ s = spMap σ} // below y.1 = x} = N := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ s)
  have hfin : IsFinite (Spec.map φ) := by
    rw [hφ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra k (X.residueField x) := φ.hom.toAlgebra
  haveI : Module.Finite k (X.residueField x) := (IsFinite.SpecMap_iff φ).1 hfin
  refine ⟨Module.finrank k (X.residueField x), Module.finrank_pos.ne', fun K _ _ σ => ?_⟩
  letI : Algebra k K := σ.toAlgebra
  have hP (ψ : X.residueField x →ₐ[k] K) :
      (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x) ≫ s = spMap σ := by
    have h : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom σ :=
      CommRingCat.hom_ext ψ.comp_algebraMap
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact congrArg Spec.map h
  let P : (X.residueField x →ₐ[k] K) → {y : {y : Sp K ⟶ X // y ≫ s = spMap σ} // below y.1 = x} :=
    fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, hP ψ⟩,
      ExtConj.below_comp x _⟩
  have hb : Function.Bijective P := by
    refine ⟨fun a b h => ?_, ?_⟩
    · have h1 : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ X.fromSpecResidueField x =
          Spec.map (CommRingCat.ofHom b.toRingHom) ≫ X.fromSpecResidueField x := congrArg (fun t => t.1.1) h
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h1))
      exact AlgHom.coe_ringHom_injective h2
    · rintro ⟨⟨y, hy⟩, hyx⟩
      obtain ⟨ψ, h⟩ := ExtConj.factor y x hyx
      have h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom σ) := by
        rw [Spec.map_comp, hφ, ← Category.assoc, h]
        exact hy
      have h3 := Spec.map_injective h2
      exact ⟨⟨ψ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext (Subtype.ext h)⟩
  rw [← Nat.card_congr (Equiv.ofBijective P hb), Nat.card_eq_fintype_card, AlgHom.card]

/- English proof (translation)
Establish `: Finite {y // p y}` using `Nat.finite_of_card_ne_zero (h ▸ hN)`. Use `letI := Fintype.ofFinite {y // p y}`. Rewrite using `[← finsum_subtype_eq_finsum_cond, ← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, ← h, Nat.card_eq_fintype_card]`. Simplify using the standard rewrite rules.
-/
theorem finsum_sub_const {α : Type} (p : α → Prop) {N : ℕ} (hN : N ≠ 0) (h : Nat.card {y // p y} = N)
    (f : α → ℝ) (c : ℝ) : ∑ᶠ (y) (_ : p y), (f y - c) = (∑ᶠ (y) (_ : p y), f y) - N * c := by
  have : Finite {y // p y} := Nat.finite_of_card_ne_zero (h ▸ hN)
  letI := Fintype.ofFinite {y // p y}
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, ← h, Nat.card_eq_fintype_card]
  simp

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise Finset.univ (fun σ : F →+* ℂ => InfinitePlace.mk σ)]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ => c v) fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2], Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]`.
-/
theorem sum_mk {F : Type} [Field F] [NumberField F] (c : InfinitePlace F → ℝ) :
    ∑ σ : F →+* ℂ, c (InfinitePlace.mk σ) = ∑ v : InfinitePlace F, (v.mult : ℝ) * c v := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : F →+* ℂ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => c v) fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2], Finset.sum_const,
    InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

/- English proof (translation)
Introduce `F _ _ C Y A ci cf ⟨M, L, k, c₀, hI⟩ hcf x hx`. Take `⟨N, hN, hc⟩` from `exists_card Y.str x hx`. Establish `hA : Nat.card {y : AlgPt Y // below y.1 = x} = N` using `hc _ _`. Establish `hfin : Finite {y : AlgPt Y // below y.1 = x}` using `(ExtConj.pts Y x hx).2`. Establish `h₁ (σ : F →+* ℂ) (f : Pts Y σ → ℝ) : ∑ᶠ (z : Pts Y σ) (_ : under z = x), (f z - (A.n : ℕ) * (A.ci + ci) (InfinitePlace.mk σ)) = (∑ᶠ (z : Pts Y σ) (_ : under z = x), (f z - (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) - N * ((A.n : ℕ) * ci (InfinitePlace.mk σ))`.

Rewrite using `[← finsum_sub_const (fun z : Pts Y σ => under z = x) hN (hc ℂ σ)]`. Simplify using `only [Pi.add_apply, mul_add, sub_sub]`. Establish `hs : (Function.support fun v : HeightOneSpectrum (𝓞 F) => ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v (Ext.instNonempty v).some y).Finite`. Use `(Set.finite_iUnion fun y : {y : AlgPt Y // below y.1 = x} => finite_places_lg_ne_zero F C Y A M L k c₀ hI y.1).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not, ne_eq] at h`. Use `hv ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← finsum_subtype_eq_finsum_cond]`. Simplify using `[h]`.

Establish `h₂ : ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), (A.lg v (Ext.instNonempty v).some y - (A.n : ℕ) * cf v) = (∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v (Ext.instNonempty v).some y) - N * ((A.n : ℕ) * ∑ᶠ v, cf v)`. Rewrite using `[mul_finsum, mul_finsum, ← finsum_sub_distrib hs (hcf.subset fun v hv h0 => hv (by simp [h0]))]`. Conclude with `finsum_congr fun v => finsum_sub_const _ hN hA _ _`. Establish `hN' : (N : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hN`. Establish `hF : (Module.finrank ℚ F : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`.

Establish `hn : ((A.n : ℕ) : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 A.n.ne_zero`. Simplify using `only [Adl.ht, Adl.twist, dif_pos (Ext.instNonempty _), h₁, h₂, hA, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_mk]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (ci : InfinitePlace F → ℝ) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.IsModel → (Function.support cf).Finite → ∀ x : Y.X, IsClosed ({x} : Set Y.X) → (A.twist ci cf).ht x = A.ht x + ((∑ v : InfinitePlace F, (v.mult : ℝ) * ci v) + ∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ) := by
  intro F _ _ C Y A ci cf ⟨M, L, k, c₀, hI⟩ hcf x hx
  obtain ⟨N, hN, hc⟩ := exists_card Y.str x hx
  have hA : Nat.card {y : AlgPt Y // below y.1 = x} = N := hc _ _
  have hfin : Finite {y : AlgPt Y // below y.1 = x} := (ExtConj.pts Y x hx).2
  have h₁ (σ : F →+* ℂ) (f : Pts Y σ → ℝ) : ∑ᶠ (z : Pts Y σ) (_ : under z = x),
      (f z - (A.n : ℕ) * (A.ci + ci) (InfinitePlace.mk σ)) = (∑ᶠ (z : Pts Y σ) (_ : under z = x),
      (f z - (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) - N * ((A.n : ℕ) * ci (InfinitePlace.mk σ)) := by
    rw [← finsum_sub_const (fun z : Pts Y σ => under z = x) hN (hc ℂ σ)]
    simp only [Pi.add_apply, mul_add, sub_sub]
  have hs : (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v (Ext.instNonempty v).some y).Finite := by
    refine (Set.finite_iUnion fun y : {y : AlgPt Y // below y.1 = x} =>
      finite_places_lg_ne_zero F C Y A M L k c₀ hI y.1).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not, ne_eq] at h
    refine hv ?_
    simp only
    rw [← finsum_subtype_eq_finsum_cond]
    simp [h]
  have h₂ : ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x),
      (A.lg v (Ext.instNonempty v).some y - (A.n : ℕ) * cf v) =
      (∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v (Ext.instNonempty v).some y) -
        N * ((A.n : ℕ) * ∑ᶠ v, cf v) := by
    rw [mul_finsum, mul_finsum, ← finsum_sub_distrib hs
      (hcf.subset fun v hv h0 => hv (by simp [h0]))]
    exact finsum_congr fun v => finsum_sub_const _ hN hA _ _
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 A.n.ne_zero
  simp only [Adl.ht, Adl.twist, dif_pos (Ext.instNonempty _), h₁, h₂, hA, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_mk]
  field_simp
  ring

end GlobalTheory.TrueGeo.HtTwist

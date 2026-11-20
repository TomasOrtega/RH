import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BlochKatoGeneratorBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SecondTwistSmallIffExactlyAtAndFinClause
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IotaInjOfTensorInj
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.H1fGeneratorsBis
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraTer

noncomputable section

namespace GlobalTheory.H1fGeneratorBoundAlt

open Module

section Algebra

variable {O : Type} [CommRing O]

/- English proof (translation)
Use `haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (Ideal.IsMaximal.ne_top inferInstance)`. Use `haveI : Nontrivial O := (Ideal.Quotient.mk I).domain_nontrivial`. Establish `e` using `(TensorProduct.quotTensorEquivQuotSMul N I).extendScalarsOfSurjective (S := O ⧸ I) Ideal.Quotient.mk_surjective`. Rewrite using `[← e.finrank_eq, Module.finrank_baseChange]`.
-/
theorem finrank_quot_smul_top (I : Ideal O) [I.IsMaximal] (N : Type) [AddCommGroup N] [Module O N]
    [Module.Free O N] [Module.Finite O N] :
    finrank (O ⧸ I) (N ⧸ (I • (⊤ : Submodule O N))) = finrank O N := by
  haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (Ideal.IsMaximal.ne_top inferInstance)
  haveI : Nontrivial O := (Ideal.Quotient.mk I).domain_nontrivial
  have e := (TensorProduct.quotTensorEquivQuotSMul N I).extendScalarsOfSurjective
    (S := O ⧸ I) Ideal.Quotient.mk_surjective
  rw [← e.finrank_eq, Module.finrank_baseChange]

def redMap (I : Ideal O) {N N' : Type} [AddCommGroup N] [Module O N] [AddCommGroup N'] [Module O N']
    (f : N →ₗ[O] N') :
    (N ⧸ (I • (⊤ : Submodule O N))) →ₗ[O ⧸ I] (N' ⧸ (I • (⊤ : Submodule O N'))) :=
  (Submodule.mapQ _ _ f (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem redMap_mk (I : Ideal O) {N N' : Type} [AddCommGroup N] [Module O N] [AddCommGroup N']
    [Module O N'] (f : N →ₗ[O] N') (x : N) :
    redMap I f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

/- English proof (translation)
Use `letI : Field (O ⧸ I) := Ideal.Quotient.field I`. Use `haveI : Module.Finite (O ⧸ I) (N ⧸ (I • (⊤ : Submodule O N))) := Module.Finite.of_restrictScalars_finite O _ _`. Use `haveI : Module.Finite (O ⧸ I) (Z ⧸ (I • (⊤ : Submodule O Z))) := Module.Finite.of_restrictScalars_finite O _ _`. Use `set R := LinearMap.range (redMap I f) with hR`. Set `Q` to `(Z ⧸ (I • (⊤ : Submodule O Z))) ⧸ R`.

Set `b` to `Module.finBasis (O ⧸ I) Q`. Set `π : Z →ₗ[O] Q` to `(R.mkQ.restrictScalars O).comp (Submodule.mkQ _)`. Establish `hπ : Function.Surjective π` using `(Submodule.mkQ_surjective R).comp (Submodule.mkQ_surjective _)`. Use `choose z hz using fun i => hπ (b i)`. Use `⟨_, z, ?_, ?_⟩` and prove the remaining obligations.

Establish `hJ : I ≤ Ideal.jacobson ⊥`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, IsLocalRing.eq_maximalIdeal hI]`. Use `top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ ?_)` and prove the remaining obligations. Introduce `x _`. Use `choose c hc using fun i => Ideal.Quotient.mk_surjective (b.repr (π x) i)`.

Establish `h0 : π (x - ∑ i, c i • z i) = 0`. Rewrite using `[map_sub, map_sum, sub_eq_zero, ← b.sum_repr (π x)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hz, ← hc]`. Both sides reduce to the same expression.

Take `⟨y, hy⟩ : Submodule.Quotient.mk (x - ∑ i, c i • z i) ∈ R` from `(Submodule.Quotient.mk_eq_zero R).1 h0`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite `hy` using `[redMap_mk, eq_comm, Submodule.Quotient.eq]`. Establish `: x = (∑ i, c i • z i + f y) + (x - ∑ i, c i • z i - f y)` using `by abel`. Rewrite using `[this]`.

Use `Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ⟨y, rfl⟩) hy` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `h1` using `R.finrank_quotient_add_finrank`. Establish `h2` using `(redMap I f).finrank_range_add_finrank_ker`. Rewrite `h1`, `h2` using `[finrank_quot_smul_top]`.

Express the relevant statement in the definitionally equal form `finrank (O ⧸ I) Q + _ = _ at h1`. Rewrite `h2` using `[← hR]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_generators [IsLocalRing O] (I : Ideal O) [hI : I.IsMaximal] {N Z : Type}
    [AddCommGroup N] [Module O N] [Module.Free O N] [Module.Finite O N]
    [AddCommGroup Z] [Module O Z] [Module.Free O Z] [Module.Finite O Z] (f : N →ₗ[O] Z) :
    ∃ (m : ℕ) (z : Fin m → Z), Submodule.span O (Set.range z) ⊔ LinearMap.range f = ⊤ ∧
      m + finrank O N = finrank O Z + finrank (O ⧸ I) ↥(LinearMap.ker (redMap I f)) := by
  letI : Field (O ⧸ I) := Ideal.Quotient.field I
  haveI : Module.Finite (O ⧸ I) (N ⧸ (I • (⊤ : Submodule O N))) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Module.Finite (O ⧸ I) (Z ⧸ (I • (⊤ : Submodule O Z))) :=
    Module.Finite.of_restrictScalars_finite O _ _
  set R := LinearMap.range (redMap I f) with hR
  let Q := (Z ⧸ (I • (⊤ : Submodule O Z))) ⧸ R
  let b := Module.finBasis (O ⧸ I) Q
  let π : Z →ₗ[O] Q := (R.mkQ.restrictScalars O).comp (Submodule.mkQ _)
  have hπ : Function.Surjective π :=
    (Submodule.mkQ_surjective R).comp (Submodule.mkQ_surjective _)
  choose z hz using fun i => hπ (b i)
  refine ⟨_, z, ?_, ?_⟩
  · have hJ : I ≤ Ideal.jacobson ⊥ := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, IsLocalRing.eq_maximalIdeal hI]
    refine top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ ?_)
    intro x _
    choose c hc using fun i => Ideal.Quotient.mk_surjective (b.repr (π x) i)
    have h0 : π (x - ∑ i, c i • z i) = 0 := by
      rw [map_sub, map_sum, sub_eq_zero, ← b.sum_repr (π x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hz, ← hc]
      rfl
    obtain ⟨y, hy⟩ : Submodule.Quotient.mk (x - ∑ i, c i • z i) ∈ R :=
      (Submodule.Quotient.mk_eq_zero R).1 h0
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [redMap_mk, eq_comm, Submodule.Quotient.eq] at hy
    have : x = (∑ i, c i • z i + f y) + (x - ∑ i, c i • z i - f y) := by abel
    rw [this]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ⟨y, rfl⟩) hy
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have h1 := R.finrank_quotient_add_finrank
    have h2 := (redMap I f).finrank_range_add_finrank_ker
    rw [finrank_quot_smul_top] at h1 h2
    change finrank (O ⧸ I) Q + _ = _ at h1
    rw [← hR] at h2
    omega

/- English proof (translation)
Establish `h` using `((Module.finBasis O N).linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf))`. Establish `h'` using `(LinearIndependent.iff_fractionRing O LL).1 h`. Simplify using `using h'.fintype_card_le_finrank`.
-/
theorem finrank_le_of_injective {LL : Type} [Field LL] [Algebra O LL] [IsDomain O]
    [IsFractionRing O LL] {N W : Type} [AddCommGroup N] [Module O N] [Module.Free O N]
    [Module.Finite O N] [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
    [FiniteDimensional LL W] (f : N →ₗ[O] W) (hf : Function.Injective f) :
    finrank O N ≤ finrank LL W := by
  have h := ((Module.finBasis O N).linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf))
  have h' := (LinearIndependent.iff_fractionRing O LL).1 h
  simpa using h'.fintype_card_le_finrank

/- English proof (translation)
Use `haveI : ∀ i, Module.Finite LL ↥(p i) := fun i => Submodule.finiteDimensional_of_le (hU i)`. Establish `hinj` using `hp.dfinsupp_lsum_injective`. Rewrite using `[← Module.finrank_directSum]`. Use `LinearMap.finrank_le_finrank_of_injective (f := ((DFinsupp.lsum ℕ (M := fun i => ↥(p i)) fun i => (p i).subtype)).codRestrict U ?_) ?_` and prove the remaining obligations. Introduce `x`.

Rewrite using `[DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]`. Conclude with `Submodule.sum_mem _ fun i _ => hU i (x i).2`. Introduce `x y h`. Conclude with `hinj (congrArg Subtype.val h)`.
-/
theorem sum_finrank_le {LL W ι : Type} [Field LL] [AddCommGroup W] [Module LL W] [Fintype ι]
    (p : ι → Submodule LL W) (hp : iSupIndep p) (U : Submodule LL W) [Module.Finite LL ↥U]
    (hU : ∀ i, p i ≤ U) : ∑ i, finrank LL ↥(p i) ≤ finrank LL ↥U := by
  classical
  haveI : ∀ i, Module.Finite LL ↥(p i) := fun i => Submodule.finiteDimensional_of_le (hU i)
  have hinj := hp.dfinsupp_lsum_injective
  rw [← Module.finrank_directSum]
  refine LinearMap.finrank_le_finrank_of_injective
    (f := ((DFinsupp.lsum ℕ (M := fun i => ↥(p i)) fun i => (p i).subtype)).codRestrict U ?_) ?_
  · intro x
    rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
    exact Submodule.sum_mem _ fun i _ => hU i (x i).2
  · intro x y h
    exact hinj (congrArg Subtype.val h)

end Algebra

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions TensorProduct

section Lattice

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  [IsDomain O] [IsFractionRing O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Ue16.exists_smul_mem L x`.
-/
theorem exists_smul_mem (L : Lattice (O := O) ρ) (x : V) : ∃ a : O, a ≠ 0 ∧ a • x ∈ L.T :=
  _root_.UpperTheory.Reformulated.B.Ue16.exists_smul_mem L x

/- English proof (translation)
Use `haveI := L.free`. Use `haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg`. Use `le_antisymm (finrank_le_of_injective L.T.subtype L.T.injective_subtype) ?_` and prove the remaining obligations. Set `b` to `Module.finBasis O ↥L.T`. Establish `h : Submodule.span LL (Set.range fun i => (b i : V)) = ⊤`.

Rewrite using `[← L.span, ← Submodule.span_span_of_tower O LL]`. Use `congr 2`. Use `congrArg (Submodule.map L.T.subtype) b.span_eq` as an intermediate fact. Rewrite `this` using `[Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]`. Then use the resulting hypothesis. Simplify using `using finrank_le_of_span_eq_top h`.
-/
theorem finrank_lattice [FiniteDimensional LL V] (L : Lattice (O := O) ρ) :
    finrank O ↥L.T = finrank LL V := by
  haveI := L.free
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  refine le_antisymm (finrank_le_of_injective L.T.subtype L.T.injective_subtype) ?_
  let b := Module.finBasis O ↥L.T
  have h : Submodule.span LL (Set.range fun i => (b i : V)) = ⊤ := by
    rw [← L.span, ← Submodule.span_span_of_tower O LL]
    congr 2
    have := congrArg (Submodule.map L.T.subtype) b.span_eq
    rwa [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at this
  simpa using finrank_le_of_span_eq_top h

variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

/- English proof (translation)
Set `U : {a : O // a ≠ 0} → Set G` to `fun a => {g | a.1 • c g ∈ L.T}`. Establish `hU : ∀ a, IsOpen (U a)` using `fun a => by`. Establish `: Continuous fun g => a.1 • c g`. Simplify using `only [← algebraMap_smul LL a.1]`. Conclude with `hc.const_smul _`.

Conclude with `hT.preimage this`. Take `⟨s, hs⟩` from `isCompact_univ.elim_finite_subcover U hU fun g _ => by`. Take `⟨a, ha, h⟩` from `exists_smul_mem L (c g)`. Conclude with `Set.mem_iUnion.2 ⟨⟨a, ha⟩, h⟩`. Use `⟨∏ a ∈ s, a.1, Finset.prod_ne_zero_iff.2 fun a _ => a.2, fun g => ?_⟩` and prove the remaining obligations.

Take `⟨a, ha, h⟩` from `Set.mem_iUnion₂.1 (hs (Set.mem_univ g))`. Rewrite using `[← Finset.prod_erase_mul s _ ha, mul_smul]`. Conclude with `L.T.smul_mem _ h`.
-/
theorem exists_smul_fun_mem [CompactSpace G] (L : Lattice (O := O) ρ) (hT : IsOpen (L.T : Set V))
    (c : G → V) (hc : Continuous c) : ∃ a : O, a ≠ 0 ∧ ∀ g, a • c g ∈ L.T := by
  classical
  let U : {a : O // a ≠ 0} → Set G := fun a => {g | a.1 • c g ∈ L.T}
  have hU : ∀ a, IsOpen (U a) := fun a => by
    have : Continuous fun g => a.1 • c g := by
      simp only [← algebraMap_smul LL a.1]
      exact hc.const_smul _
    exact hT.preimage this
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU fun g _ => by
    obtain ⟨a, ha, h⟩ := exists_smul_mem L (c g)
    exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, h⟩
  refine ⟨∏ a ∈ s, a.1, Finset.prod_ne_zero_iff.2 fun a _ => a.2, fun g => ?_⟩
  obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ g))
  rw [← Finset.prod_erase_mul s _ ha, mul_smul]
  exact L.T.smul_mem _ h

end Lattice

section Cohomology

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}

/- English proof (translation)
Use `haveI := PD.finK`. Use `sum_finrank_le _ ?_ _ fun τ => inf_le_left` and prove the remaining obligations. Set `pb` to `Field.powerBasisOfFiniteOfSeparable Qp K`. Establish `hinj : Function.Injective fun τ : K →ₐ[Qp] LL => τ pb.gen` using `fun τ τ' h => pb.algHom_ext h`. Use `((Module.End.eigenspaces_iSupIndep (mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL) pb.gen)).comp hinj).mono fun τ x hx => ?_` and prove the remaining obligations.

Use `(Submodule.mem_iInf _).1 hx.2 pb.gen` as an intermediate fact. Rewrite using `[Function.comp_apply, Module.End.mem_eigenspace_iff]`. Simplify `this` using `[sub_eq_zero]`.
-/
theorem sum_finrank_DdRE_le [CharZero Qp] [Fintype (K →ₐ[Qp] LL)] [Module.Finite LL ↥(DdR PD ρ)] :
    ∑ τ : K →ₐ[Qp] LL, finrank LL ↥(DdRE PD ρ τ) ≤ finrank LL ↥(DdR PD ρ) := by
  haveI := PD.finK
  refine sum_finrank_le _ ?_ _ fun τ => inf_le_left
  let pb := Field.powerBasisOfFiniteOfSeparable Qp K
  have hinj : Function.Injective fun τ : K →ₐ[Qp] LL => τ pb.gen := fun τ τ' h => pb.algHom_ext h
  refine ((Module.End.eigenspaces_iSupIndep
    (mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL) pb.gen)).comp hinj).mono fun τ x hx => ?_
  have := (Submodule.mem_iInf _).1 hx.2 pb.gen
  rw [Function.comp_apply, Module.End.mem_eigenspace_iff]
  simpa [sub_eq_zero] using this

variable [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]

/- English proof (translation)
Use `⟨⟨(hρ x).sub continuous_const, fun g h => ?_⟩, x ⊗ₜ 1, fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ρ (g * h) x - x = ρ g x - x + ρ g (ρ h x - x)`. Rewrite using `[map_mul, map_sub, Module.End.mul_apply]`. Normalize the expressions using the abelian group laws. Express the relevant statement in the definitionally equal form `(ρ g x - x) ⊗ₜ[Qp] (1 : B) = _`.

Simplify using `[actVB, sub_tmul]`.
-/
theorem coboundary_mem_blochKatoCocycles (hρ : ∀ x, Continuous fun g => ρ g x) (x : V) : cob ρ x ∈ finiteCocycles PD ρ := by
  refine ⟨⟨(hρ x).sub continuous_const, fun g h => ?_⟩, x ⊗ₜ 1, fun g => ?_⟩
  · change ρ (g * h) x - x = ρ g x - x + ρ g (ρ h x - x)
    rw [map_mul, map_sub, Module.End.mul_apply]
    abel
  · change (ρ g x - x) ⊗ₜ[Qp] (1 : B) = _
    simp [actVB, sub_tmul]

/- English proof (translation)
Establish `hle : B1 ρ ≤ finiteCocycles PD ρ`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `coboundary_mem_blochKatoCocycles PD hρ x`. Establish `h1` using `((B1 ρ).comap (finiteCocycles PD ρ).subtype).finrank_quotient_add_finrank`. Establish `h2` using `(cob ρ).finrank_range_add_finrank_ker`.

Establish `h3 : LinearMap.ker (cob ρ) = H0V ρ`. Rewrite using `[cob, LinearMap.ker_pi, H0V]`. Establish `h4` using `(Submodule.comapSubtypeEquivOfLe hle).finrank_eq`. Rewrite `h2` using `[h3]`. Express the relevant statement in the definitionally equal form `finrank LL ↥(B1 ρ) + _ = _ at h2`.

Express the relevant statement in the definitionally equal form `finrank LL (FiniteCohomology PD ρ) + _ = _ at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_bloch_kato_cocycles [FiniteDimensional LL V] (hρ : ∀ x, Continuous fun g => ρ g x)
    [Module.Finite LL ↥(finiteCocycles PD ρ)] :
    finrank LL ↥(finiteCocycles PD ρ) + finrank LL ↥(H0V ρ) = finrank LL (FiniteCohomology PD ρ) + finrank LL V := by
  have hle : B1 ρ ≤ finiteCocycles PD ρ := by
    rintro _ ⟨x, rfl⟩
    exact coboundary_mem_blochKatoCocycles PD hρ x
  have h1 := ((B1 ρ).comap (finiteCocycles PD ρ).subtype).finrank_quotient_add_finrank
  have h2 := (cob ρ).finrank_range_add_finrank_ker
  have h3 : LinearMap.ker (cob ρ) = H0V ρ := by
    rw [cob, LinearMap.ker_pi, H0V]
  have h4 := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  rw [h3] at h2
  change finrank LL ↥(B1 ρ) + _ = _ at h2
  change finrank LL (FiniteCohomology PD ρ) + _ = _ at h1
  omega

variable {O : Type} [CommRing O] [Algebra O LL] [IsDomain O] [IsDiscreteValuationRing O]
  [IsFractionRing O LL] [Module O V] [IsScalarTower O LL V]

def cobT (L : Lattice (O := O) ρ) (hρ : ∀ x, Continuous fun g => ρ g x) :
    ↥L.T →ₗ[O] ↥(latticeFiniteCocycles PD L) :=
  (((cob ρ).restrictScalars O).comp L.T.subtype).codRestrict _ fun x =>
    ⟨⟨(coboundary_mem_blochKatoCocycles PD hρ x).1, fun g _ => L.T.sub_mem (L.stable g x x.2) x.2⟩, coboundary_mem_blochKatoCocycles PD hρ x⟩

def classT (L : Lattice (O := O) ρ) : ↥(latticeFiniteCocycles PD L) →ₗ[O] LatticeCohomology L :=
  (Submodule.mkQ _).comp (Submodule.inclusion inf_le_left)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] in
/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨_, c.2, rfl⟩`. Introduce and unpack `⟨c, hc, rfl⟩`.

Conclude with `⟨⟨c, hc⟩, rfl⟩`.
-/
theorem range_classT (L : Lattice (O := O) ρ) : LinearMap.range (classT PD L) = latticeFiniteCohomology PD L := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, c.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] in
/- English proof (translation)
Use extensionality with `c`. Rewrite using `[LinearMap.mem_ker]`. Use `(Submodule.Quotient.mk_eq_zero _).trans ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨x, hx, h⟩`. Conclude with `⟨⟨x, hx⟩, Subtype.ext h⟩`.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x, x.2, rfl⟩`.
-/
theorem ker_classT (L : Lattice (O := O) ρ) (hρ : ∀ x, Continuous fun g => ρ g x) :
    LinearMap.ker (classT PD L) = LinearMap.range (cobT PD L hρ) := by
  ext c
  rw [LinearMap.mem_ker]
  refine (Submodule.Quotient.mk_eq_zero _).trans ⟨?_, ?_⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨⟨x, hx⟩, Subtype.ext h⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩

omit [IsFractionRing O LL] in
/- English proof (translation)
Use `haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg`. Use `⟨Submodule.fg_of_fg_map_of_fg_inf_ker (classT PD L) (IsNoetherian.noetherian _) ?_⟩` and prove the remaining obligations. Rewrite using `[top_inf_eq, ker_classT PD L hρ]`. Conclude with `Submodule.fg_range _`.
-/
theorem finite_Z1fT (L : Lattice (O := O) ρ) (hρ : ∀ x, Continuous fun g => ρ g x)
    [Module.Finite O (LatticeCohomology L)] : Module.Finite O ↥(latticeFiniteCocycles PD L) := by
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (classT PD L) (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, ker_classT PD L hρ]
  exact Submodule.fg_range _

/- English proof (translation)
Take `⟨s, hs⟩ : (latticeFiniteCocycles PD L).FG` from `Module.Finite.iff_fg.1 inferInstance`. Use `haveI := FiniteDimensional.span_finset LL s`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span LL (s : Set (G → V))) fun c hc => ?_` and prove the remaining obligations. Take `⟨a, ha, h⟩` from `exists_smul_fun_mem L hT c hc.1.1`. Establish `h1 : a • c ∈ (finiteCocycles PD ρ).restrictScalars O` using `Submodule.smul_mem ((finiteCocycles PD ρ).restrictScalars O) a hc`.

Establish `h2 : a • c ∈ latticeFiniteCocycles PD L` using `⟨⟨h1.1, fun g _ => h g⟩, h1⟩`. Rewrite `h2` using `[← hs]`. Establish `h3` using `Submodule.span_subset_span O LL _ h2`. Establish `ha' : algebraMap O LL a ≠ 0` using `by simpa using ha`. Rewrite `h3` using `[← algebraMap_smul LL a]`.

Conclude with `(Submodule.smul_mem_iff _ ha').1 h3`.
-/
theorem finite_bloch_kato_cocycles [CompactSpace G] (L : Lattice (O := O) ρ) (hT : IsOpen (L.T : Set V))
    [Module.Finite O ↥(latticeFiniteCocycles PD L)] : Module.Finite LL ↥(finiteCocycles PD ρ) := by
  obtain ⟨s, hs⟩ : (latticeFiniteCocycles PD L).FG := Module.Finite.iff_fg.1 inferInstance
  haveI := FiniteDimensional.span_finset LL s
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span LL (s : Set (G → V))) fun c hc => ?_
  obtain ⟨a, ha, h⟩ := exists_smul_fun_mem L hT c hc.1.1
  have h1 : a • c ∈ (finiteCocycles PD ρ).restrictScalars O :=
    Submodule.smul_mem ((finiteCocycles PD ρ).restrictScalars O) a hc
  have h2 : a • c ∈ latticeFiniteCocycles PD L := ⟨⟨h1.1, fun g _ => h g⟩, h1⟩
  rw [← hs] at h2
  have h3 := Submodule.span_subset_span O LL _ h2
  have ha' : algebraMap O LL a ≠ 0 := by simpa using ha
  rw [← algebraMap_smul LL a] at h3
  exact (Submodule.smul_mem_iff _ ha').1 h3

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] in

/- English proof (translation)
Introduce `y hy`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite `hy` using `[LinearMap.mem_ker, redMap_mk, Submodule.Quotient.mk_eq_zero]`. Use `(mk_mem_H0Mod L I x).2 fun g => ?_` and prove the remaining obligations. Set `ev : ↥(latticeFiniteCocycles PD L) →ₗ[O] ↥L.T` to `((LinearMap.proj g).comp (latticeFiniteCocycles PD L).subtype).codRestrict _ fun c => c.2.1.2 g (Set.mem_univ g)`.

Establish `h` using `Submodule.mem_map_of_mem (f := ev) hy`. Rewrite `h` using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top h`.
-/
theorem ker_redMap_le (L : Lattice (O := O) ρ) (hρ : ∀ x, Continuous fun g => ρ g x) (I : Ideal O) :
    LinearMap.ker (redMap I (cobT PD L hρ)) ≤ galoisLatticeModIdealInvariants L I := by
  intro y hy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.mem_ker, redMap_mk, Submodule.Quotient.mk_eq_zero] at hy
  refine (mk_mem_H0Mod L I x).2 fun g => ?_
  let ev : ↥(latticeFiniteCocycles PD L) →ₗ[O] ↥L.T :=
    ((LinearMap.proj g).comp (latticeFiniteCocycles PD L).subtype).codRestrict _ fun c => c.2.1.2 g (Set.mem_univ g)
  have h := Submodule.mem_map_of_mem (f := ev) hy
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

/- English proof (translation)
Use `haveI hI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ`. Use `letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _`. Use `haveI := L.free`. Use `haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg`. Use `haveI := finite_Z1fT PD L hρ`.

Use `haveI := finite_bloch_kato_cocycles PD L hT`. Use `haveI : Module.IsTorsionFree O LL := inferInstance`. Use `haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans LL`. Use `haveI : Module.Free O ↥(latticeFiniteCocycles PD L) := inferInstance`. Take `⟨m, z, hz, hm⟩` from `exists_generators (Ideal.span {ϖ}) (cobT PD L hρ)`.

Use `⟨m, ⟨Finset.univ.image fun i => classT PD L (z i), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `congrArg (Submodule.map (classT PD L)) hz` as an intermediate fact. Rewrite `this` using `[Submodule.map_sup, ← ker_classT, Submodule.map_top, range_classT, (Submodule.map_le_iff_le_comap.2 le_rfl : (LinearMap.ker (classT PD L)).map (classT PD L) ≤ ⊥).antisymm bot_le, sup_bot_eq, Submodule.map_span, ← Set.range_comp]`. Rewrite using `[← this, Finset.coe_image, Finset.coe_univ, Set.image_univ]`. Both sides reduce to the same expression.

Simplify using `using Finset.card_image_le (s := Finset.univ) (f := fun i => classT PD L (z i))`. Use `haveI := finite_latMod L (Ideal.span {ϖ})`. Establish `h1` using `Submodule.finrank_mono (ker_redMap_le PD L hρ (Ideal.span {ϖ}))`. Establish `h2` using `finrank_bloch_kato_cocycles PD hρ`. Establish `h3` using `finrank_lattice L`.

Establish `h4 : finrank O ↥(latticeFiniteCocycles PD L) ≤ finrank LL ↥(finiteCocycles PD ρ)` using `finrank_le_of_injective (W := ↥(finiteCocycles PD ρ)) { toFun := fun c => ⟨c, c.2.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl } fun _ _ h => Subtype.ext (congrArg (fun c : ↥(finiteCocycles PD ρ) => (c : G → V)) h)`. Establish `h5 : finrank (O ⧸ Ideal.span {ϖ}) ↥(LinearMap.ker (redMap (Ideal.span {ϖ}) (cobT PD L hρ))) ≤ h0ModResidueDim L ϖ` using `h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_generators_H1fT [CompactSpace G] [FiniteDimensional LL V] (L : Lattice (O := O) ρ)
    (hρ : ∀ x, Continuous fun g => ρ g x) (hT : IsOpen (L.T : Set V)) [Module.Finite O (LatticeCohomology L)]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ m : ℕ, GeneratedByAtMost (latticeFiniteCohomology PD L) m ∧
      m + finrank LL ↥(H0V ρ) ≤ finrank LL (FiniteCohomology PD ρ) + h0ModResidueDim L ϖ := by
  classical
  haveI hI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  haveI := L.free
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  haveI := finite_Z1fT PD L hρ
  haveI := finite_bloch_kato_cocycles PD L hT
  haveI : Module.IsTorsionFree O LL := inferInstance
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans LL
  haveI : Module.Free O ↥(latticeFiniteCocycles PD L) := inferInstance
  obtain ⟨m, z, hz, hm⟩ := exists_generators (Ideal.span {ϖ}) (cobT PD L hρ)
  refine ⟨m, ⟨Finset.univ.image fun i => classT PD L (z i), ?_, ?_⟩, ?_⟩
  · have := congrArg (Submodule.map (classT PD L)) hz
    rw [Submodule.map_sup, ← ker_classT, Submodule.map_top, range_classT,
      (Submodule.map_le_iff_le_comap.2 le_rfl : (LinearMap.ker (classT PD L)).map (classT PD L) ≤ ⊥).antisymm bot_le,
      sup_bot_eq, Submodule.map_span, ← Set.range_comp] at this
    rw [← this, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  · simpa using Finset.card_image_le (s := Finset.univ) (f := fun i => classT PD L (z i))
  · haveI := finite_latMod L (Ideal.span {ϖ})
    have h1 := Submodule.finrank_mono (ker_redMap_le PD L hρ (Ideal.span {ϖ}))
    have h2 := finrank_bloch_kato_cocycles PD hρ
    have h3 := finrank_lattice L
    have h4 : finrank O ↥(latticeFiniteCocycles PD L) ≤ finrank LL ↥(finiteCocycles PD ρ) :=
      finrank_le_of_injective (W := ↥(finiteCocycles PD ρ))
        { toFun := fun c => ⟨c, c.2.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl } fun _ _ h =>
          Subtype.ext (congrArg (fun c : ↥(finiteCocycles PD ρ) => (c : G → V)) h)
    have h5 : finrank (O ⧸ Ideal.span {ϖ}) ↥(LinearMap.ker (redMap (Ideal.span {ϖ}) (cobT PD L hρ))) ≤
      h0ModResidueDim L ϖ := h1
    omega

omit [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
  [IsFractionRing O LL] in

/- English proof (translation)
Use `haveI hI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ`. Use `letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _`. Use `haveI := L.free`. Use `haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg`. Use `haveI := finite_latMod L (Ideal.span {ϖ})`.

Rewrite using `[← finrank_quot_smul_top (Ideal.span {ϖ})]`. Conclude with `Submodule.finrank_le _`.
-/
theorem h0_mod_uniformizer_le_rank (L : Lattice (O := O) ρ) {ϖ : O} (hϖ : Irreducible ϖ) :
    h0ModResidueDim L ϖ ≤ finrank O ↥L.T := by
  haveI hI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  haveI := L.free
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  haveI := finite_latMod L (Ideal.span {ϖ})
  rw [← finrank_quot_smul_top (Ideal.span {ϖ})]
  exact Submodule.finrank_le _

end Cohomology

section FieldPeriods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Use `letI : Field BdR := hF.toField`. Use `haveI := PD.finK`. Use `haveI : Module.Finite Qp V := Module.Finite.trans LL V`. Use `⟨GlobalTheory.Cmp.SmallJumps.finite_ddR_of_isField PD hF ρ, ?_⟩` and prove the remaining obligations. Set `σ : G → BdR ⊗[Qp] V →ₗ[Qp] BdR ⊗[Qp] V` to `fun g => TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)`.

Establish `hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w`. Introduce `g b w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c v => simp [σ, TensorProduct.smul_tmul']`.

Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`. Set `U : Submodule K (BdR ⊗[Qp] V)` to `{ carrier := {x | ∀ g, σ g x = x} zero_mem' := fun g => map_zero _ add_mem' := fun hx hy g => by rw [map_add, hx g, hy g] smul_mem' := fun c x hx g => by`. Rewrite using `[← algebraMap_smul BdR c x, hσ, hx g, AlgEquiv.commutes] }`. Use `haveI : Module.Finite K U := GlobalTheory.Cmp.SmallJumps.finite_of_invariant (F := BdR) (fun g b => PD.actdR g b) (fun g => (σ g).toAddMonoidHom) hσ PD.invdR U fun _ hx => hx`. Use `haveI : Module.Finite Qp U := Module.Finite.trans K U`.

Establish `hU : finrank K U ≤ finrank Qp V`. Set `b` to `Module.finBasis K U`. Establish `h1 : LinearIndependent K fun i => (b i : BdR ⊗[Qp] V)` using `b.linearIndependent.map' U.subtype U.ker_subtype`. Establish `h2` using `GlobalTheory.Cmp.SmallJumps.linearIndepOn_of_invariant (F := BdR) (fun g b => PD.actdR g b) (fun g => (σ g).toAddMonoidHom) hσ PD.invdR (fun i => (b i : BdR ⊗[Qp] V)) (fun g i => (b i).2 g) Finset.univ (h1.linearIndepOn _)`. Simplify using `using LinearIndependent.fintype_card_le_finrank h2`.

Establish `hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) = TensorProduct.comm Qp V BdR (actVdR PD ρ g x)`. Introduce `g x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c v => simp [σ, actVdR]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Set `f : DdR PD ρ →ₗ[Qp] U` to `{ toFun := fun x => ⟨TensorProduct.comm Qp V BdR x, fun g => by`. Use `x.2` as an intermediate fact. Simplify using `only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this`. Rewrite using `[hc, this g]⟩`.

Use the proof step `map_add' := fun x y => Subtype.ext (map_add _ _ _)`. Use the proof step `map_smul' := fun c x => Subtype.ext (map_smul (TensorProduct.comm Qp V BdR) c _) }`. Establish `h1 : finrank Qp ↥(DdR PD ρ) ≤ finrank Qp U` using `LinearMap.finrank_le_finrank_of_injective (f := f) fun x y h => Subtype.ext ((TensorProduct.comm Qp V BdR).injective (congrArg Subtype.val h))`. Rewrite `h1` using `[← finrank_mul_finrank Qp LL ↥(DdR PD ρ), ← finrank_mul_finrank Qp K U]`. Rewrite `hU` using `[← finrank_mul_finrank Qp LL V]`.

Use `Nat.le_of_mul_le_mul_left (h1.trans ?_) (finrank_pos (R := Qp) (M := LL))` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem finrank_DdR_le_of_isField (hF : IsField BdR) [FiniteDimensional Qp LL]
    [FiniteDimensional LL V] (ρ : Representation LL G V) :
    Module.Finite LL ↥(DdR PD ρ) ∧ finrank LL ↥(DdR PD ρ) ≤ finrank Qp K * finrank LL V := by
  letI : Field BdR := hF.toField
  haveI := PD.finK
  haveI : Module.Finite Qp V := Module.Finite.trans LL V
  refine ⟨GlobalTheory.Cmp.SmallJumps.finite_ddR_of_isField PD hF ρ, ?_⟩
  let σ : G → BdR ⊗[Qp] V →ₗ[Qp] BdR ⊗[Qp] V := fun g =>
    TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  let U : Submodule K (BdR ⊗[Qp] V) :=
    { carrier := {x | ∀ g, σ g x = x}
      zero_mem' := fun g => map_zero _
      add_mem' := fun hx hy g => by rw [map_add, hx g, hy g]
      smul_mem' := fun c x hx g => by
        rw [← algebraMap_smul BdR c x, hσ, hx g, AlgEquiv.commutes] }
  haveI : Module.Finite K U := GlobalTheory.Cmp.SmallJumps.finite_of_invariant (F := BdR)
    (fun g b => PD.actdR g b) (fun g => (σ g).toAddMonoidHom) hσ PD.invdR U fun _ hx => hx
  haveI : Module.Finite Qp U := Module.Finite.trans K U
  have hU : finrank K U ≤ finrank Qp V := by
    let b := Module.finBasis K U
    have h1 : LinearIndependent K fun i => (b i : BdR ⊗[Qp] V) :=
      b.linearIndependent.map' U.subtype U.ker_subtype
    have h2 := GlobalTheory.Cmp.SmallJumps.linearIndepOn_of_invariant (F := BdR) (fun g b => PD.actdR g b)
      (fun g => (σ g).toAddMonoidHom) hσ PD.invdR (fun i => (b i : BdR ⊗[Qp] V))
      (fun g i => (b i).2 g) Finset.univ (h1.linearIndepOn _)
    simpa using LinearIndependent.fintype_card_le_finrank h2
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, actVdR]
    | add x y hx hy => simp only [map_add, hx, hy]
  let f : DdR PD ρ →ₗ[Qp] U :=
    { toFun := fun x => ⟨TensorProduct.comm Qp V BdR x, fun g => by
        have := x.2
        simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero] at this
        rw [hc, this g]⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul (TensorProduct.comm Qp V BdR) c _) }
  have h1 : finrank Qp ↥(DdR PD ρ) ≤ finrank Qp U :=
    LinearMap.finrank_le_finrank_of_injective (f := f) fun x y h =>
      Subtype.ext ((TensorProduct.comm Qp V BdR).injective (congrArg Subtype.val h))
  rw [← finrank_mul_finrank Qp LL ↥(DdR PD ρ), ← finrank_mul_finrank Qp K U] at h1
  rw [← finrank_mul_finrank Qp LL V] at hU
  refine Nat.le_of_mul_le_mul_left (h1.trans ?_) (finrank_pos (R := Qp) (M := LL))
  calc _ ≤ finrank Qp K * (finrank Qp LL * finrank LL V) := Nat.mul_le_mul_left _ hU
    _ = _ := by ring

end FieldPeriods

def toGRep {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O) :
    GRep G Qp LL O where
  V := T.V
  ρ := T.ρ
  cont := T.cont

section Bound

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

/- English proof (translation)
Take `⟨hD, hDVR, hF⟩` from `hO.1`. Use `haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V`. Use `haveI : Module.Finite O (LatticeCohomology T.L) := hfin _ _ hO (toGRep T) T.L`. Take `⟨m, ⟨s, hs', hc⟩, hm⟩` from `exists_generators_H1fT PD T.L T.cont (GlobalTheory.Cyc.locLat_isOpen hO T) hϖ`. Establish `h1` using `hBK hs T.V T.ρ T.cont hT`.

Establish `h3` using `sum_finrank_DdRE_le PD (ρ := T.ρ)`. Establish `h4 : ∑ τ : K →ₐ[Qp] LL, ((finrank LL ↥(DdRE PD T.ρ τ) : ℤ) - finrank LL ↥(FildR PD T.ρ τ 0)) ≤ ((∑ τ : K →ₐ[Qp] LL, finrank LL ↥(DdRE PD T.ρ τ) : ℕ) : ℤ)`. Rewrite using `[Nat.cast_sum]`. Conclude with `Finset.sum_le_sum fun τ _ => sub_le_self _ (Nat.cast_nonneg _)`. Establish `h5` using `h0_mod_uniformizer_le_rank T.L hϖ`.

Rewrite `h2` using `[← finrank_lattice T.L]`. Use `⟨⟨s, hs', ?_⟩, ?_⟩` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers. Rewrite using `[add_mul, one_mul]`. Use linear arithmetic over natural numbers and integers.
-/
theorem generatorBound_of [CharZero Qp] [CompactSpace G] [Fintype (K →ₐ[Qp] LL)]
    (hO : GoodO (Qp := Qp) LL O) (hs : Splits (Qp := Qp) (K := K) LL) (hBK : BlochKatoDim PD LL)
    (hfin : TateFiniteness PD) {ϖ : O} (hϖ : Irreducible ϖ) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (hfd : Module.Finite LL ↥(DdR PD T.ρ))
    (h2 : finrank LL ↥(DdR PD T.ρ) ≤ finrank Qp K * finrank LL T.V) : GeneratorBound PD T ϖ := by
  obtain ⟨hD, hDVR, hF⟩ := hO.1
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V
  haveI : Module.Finite O (LatticeCohomology T.L) := hfin _ _ hO (toGRep T) T.L
  obtain ⟨m, ⟨s, hs', hc⟩, hm⟩ :=
    exists_generators_H1fT PD T.L T.cont (GlobalTheory.Cyc.locLat_isOpen hO T) hϖ
  have h1 := hBK hs T.V T.ρ T.cont hT
  have h3 := sum_finrank_DdRE_le PD (ρ := T.ρ)
  have h4 : ∑ τ : K →ₐ[Qp] LL, ((finrank LL ↥(DdRE PD T.ρ τ) : ℤ) - finrank LL ↥(FildR PD T.ρ τ 0)) ≤
      ((∑ τ : K →ₐ[Qp] LL, finrank LL ↥(DdRE PD T.ρ τ) : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum fun τ _ => sub_le_self _ (Nat.cast_nonneg _)
  have h5 := h0_mod_uniformizer_le_rank T.L hϖ
  rw [← finrank_lattice T.L] at h2
  refine ⟨⟨s, hs', ?_⟩, ?_⟩
  · omega
  · rw [add_mul, one_mul]
    omega

end Bound

section Local

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use `haveI := K.2`. Establish `h : IsClosed ((GK K : Subgroup (GQ l)) : Set (GQ l))` using `IntermediateField.fixingSubgroup_isClosed K.1`. Conclude with `isCompact_iff_compactSpace.1 h.isCompact`.
-/
theorem compactSpace_GK (K : FinExt l) : CompactSpace ↥(GK K) := by
  haveI := K.2
  have h : IsClosed ((GK K : Subgroup (GQ l)) : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed K.1
  exact isCompact_iff_compactSpace.1 h.isCompact

/- English proof (translation)
Use `haveI := K.2`. Use `⟨LL.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← AlgHom.card ℚ_[l] ↥K.1 (Om l)]`. Use `Fintype.card_of_bijective (f := fun τ => LL.1.val.comp τ) ⟨fun τ τ' hτ => ?_, fun σ => ?_⟩` and prove the remaining obligations. Conclude with `AlgHom.ext fun x => Subtype.ext (DFunLike.congr_fun hτ x)`.

Establish `hσ : ∀ x, σ x ∈ LL.1`. Introduce `x`. Use `letI : Algebra ↥K.1 ↥(Ks K s) := (IntermediateField.inclusion h.2.2.1).toAlgebra`. Use `haveI : IsScalarTower ℚ_[l] ↥K.1 ↥(Ks K s) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : Algebra.IsAlgebraic ↥K.1 ↥(Ks K s) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _`.

Take `⟨τ, hτ⟩` from `IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := ℚ_[l]) (L := ↥K.1) (E := ↥(Ks K s)) (M := Om l) σ`. Rewrite using `[← hτ]`. Conclude with `h.2.2.2 τ _`. Conclude with `⟨σ.codRestrict LL.1.toSubalgebra hσ, AlgHom.ext fun _ => rfl⟩`.
-/
theorem splits_of_good {K LL : FinExt l} {s : ℕ} (h : Good K s LL)
    [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] : Splits (Qp := ℚ_[l]) (K := ↥K.1) ↥LL.1 := by
  haveI := K.2
  refine ⟨LL.2, ?_⟩
  rw [← AlgHom.card ℚ_[l] ↥K.1 (Om l)]
  refine Fintype.card_of_bijective (f := fun τ => LL.1.val.comp τ) ⟨fun τ τ' hτ => ?_, fun σ => ?_⟩
  · exact AlgHom.ext fun x => Subtype.ext (DFunLike.congr_fun hτ x)
  · have hσ : ∀ x, σ x ∈ LL.1 := by
      intro x
      letI : Algebra ↥K.1 ↥(Ks K s) := (IntermediateField.inclusion h.2.2.1).toAlgebra
      haveI : IsScalarTower ℚ_[l] ↥K.1 ↥(Ks K s) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      haveI : Algebra.IsAlgebraic ↥K.1 ↥(Ks K s) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
      obtain ⟨τ, hτ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
        (K := ℚ_[l]) (L := ↥K.1) (E := ↥(Ks K s)) (M := Om l) σ
      rw [← hτ]
      exact h.2.2.2 τ _
    exact ⟨σ.codRestrict LL.1.toSubalgebra hσ, AlgHom.ext fun _ => rfl⟩

def BlochKatoAt (P : LocPrime l) : Prop :=
  ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)], BlochKatoDim (P.PD K) ↥LL.1

def TateFiniteAt (P : LocPrime l) : Prop := ∀ K : FinExt l, TateFiniteness (P.PD K)

def DeRhamLeAt (P : LocPrime l) : Prop :=
  ∀ (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    Module.Finite ↥LL.1 ↥(DdR (P.PD K) T.ρ) ∧
      finrank ↥LL.1 ↥(DdR (P.PD K) T.ρ) ≤ finrank ℚ_[l] ↥K.1 * finrank ↥LL.1 T.V

/- English proof (translation)
Introduce `K LL T` and use `(h K _ _ (GlobalTheory.LocalIntegers.good_integers l LL).1 (toGRep T)).2.1`.
-/
theorem deRhamLeAt_of_fontCore (P : LocPrime l) (h : ∀ K : FinExt l, fontCore (P.PD K)) :
    DeRhamLeAt P := fun K LL T =>
  (h K _ _ (GlobalTheory.LocalIntegers.good_integers l LL).1 (toGRep T)).2.1

/- English proof (translation)
Introduce `K LL T` and use `haveI := LL.2 finrank_DdR_le_of_isField (P.PD K) h T.ρ`.
-/
theorem deRhamLeAt_of_isField (P : LocPrime l) (h : IsField P.R.BdR) : DeRhamLeAt P := fun K LL T =>
  haveI := LL.2
  finrank_DdR_le_of_isField (P.PD K) h T.ρ

/- English proof (translation)
Introduce `K LL hA ϖ hϖ T hT`. Use `haveI := K.2`. Use `haveI := compactSpace_GK K`. Conclude with `generatorBound_of (P.PD K) (GlobalTheory.LocalIntegers.good_integers l LL).1 (splits_of_good hA.2.2) (hBK K LL) (hfin K) hϖ T hT (hdR K LL T).1 (hdR K LL T).2`.
-/
theorem h1fGeneratorsAt_of (P : LocPrime l) (hBK : BlochKatoAt P) (hfin : TateFiniteAt P)
    (hdR : DeRhamLeAt P) : H1fGeneratorBoundAt P := by
  intro K LL hA ϖ hϖ T hT
  haveI := K.2
  haveI := compactSpace_GK K
  exact generatorBound_of (P.PD K) (GlobalTheory.LocalIntegers.good_integers l LL).1 (splits_of_good hA.2.2)
    (hBK K LL) (hfin K) hϖ T hT (hdR K LL T).1 (hdR K LL T).2

/- English proof (translation)
The claim follows from `h1fGeneratorsAt_of P hBK hfin (deRhamLeAt_of_isField P hF)`.
-/
theorem h1fGeneratorsAt_of_isField (P : LocPrime l) (hF : IsField P.R.BdR) (hBK : BlochKatoAt P)
    (hfin : TateFiniteAt P) : H1fGeneratorBoundAt P :=
  h1fGeneratorsAt_of P hBK hfin (deRhamLeAt_of_isField P hF)

/- English proof (translation)
The claim follows from `h1fGeneratorsAt_of_isField P (GlobalTheory.MemLoc.RingsModel.isField_of_isStd h) hBK hfin`.
-/
theorem h1fGeneratorsAt_of_isStd (P : LocPrime l) (AI : LocAinf l P) (h : GlobalTheory.Per.IsStd P AI)
    (hBK : BlochKatoAt P) (hfin : TateFiniteAt P) : H1fGeneratorBoundAt P :=
  h1fGeneratorsAt_of_isField P (GlobalTheory.MemLoc.RingsModel.isField_of_isStd h) hBK hfin

end Local

/- English proof (translation)
The claim follows from `h1fGeneratorsAt_of P`.
-/
theorem h1fGenerators_pointwise (l : ℕ) [Fact l.Prime] (P : LocPrime l) :
    BlochKatoAt P → TateFiniteAt P → DeRhamLeAt P → H1fGeneratorBoundAt P :=
  h1fGeneratorsAt_of P

/- English proof (translation)
Introduce `l _ P` and use `h1fGeneratorsAt_of P (hBK l P) (hfin l P) (hdR l P)`.
-/
theorem h1fGenerators_of (hBK : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), BlochKatoAt P)
    (hfin : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), TateFiniteAt P)
    (hdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), DeRhamLeAt P) : H1fGeneratorBoundAlt :=
  fun l _ P => h1fGeneratorsAt_of P (hBK l P) (hfin l P) (hdR l P)

/- English proof (translation)
Introduce `_ _ P AI h` and use `h1fGeneratorsAt_of_isStd P AI h`.
-/
theorem h1fGenerators_std_pointwise : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    GlobalTheory.Per.IsStd P AI → BlochKatoAt P → TateFiniteAt P → H1fGeneratorBoundAt P :=
  fun _ _ P AI h => h1fGeneratorsAt_of_isStd P AI h

/- English proof (translation)
The claim follows from `h1fGeneratorsAt_of_isStd P AI ⟨T⟩ hBK hfin`.
-/
theorem h1fGenerators_tied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (hBK : BlochKatoAt P) (hfin : TateFiniteAt P) : H1fGeneratorBoundAt P :=
  h1fGeneratorsAt_of_isStd P AI ⟨T⟩ hBK hfin

/- English proof (translation)
Introduce `l _ P AI h` and use `h1fGeneratorsAt_of_isStd P AI h (hBK l P AI h) (hfin l P AI h)`.
-/
theorem h1fGeneratorsStd_of
    (hBK : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), GlobalTheory.Per.IsStd P AI →
      BlochKatoAt P)
    (hfin : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), GlobalTheory.Per.IsStd P AI →
      TateFiniteAt P) : GlobalTheory.Survey.H1fGeneratorsBis.H1fGeneratorsStandard :=
  fun l _ P AI h => h1fGeneratorsAt_of_isStd P AI h (hBK l P AI h) (hfin l P AI h)

end GlobalTheory.H1fGeneratorBoundAlt

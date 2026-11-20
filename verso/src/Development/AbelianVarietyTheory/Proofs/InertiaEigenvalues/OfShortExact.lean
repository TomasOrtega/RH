import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRingsStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.FontCmp

namespace GlobalTheory.Per.CrysSubQuot

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V₀ : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

/- English proof (translation)
Take `⟨e1, e2⟩` from `GlobalTheory.RegularRing.left_exact PD hi hp h1 h2 h3`. Establish `h4` using `(DcrisMap PD hp).finrank_range_add_finrank_ker`. Rewrite `h4` using `[e2.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1]`. Establish `h5` using `p.finrank_range_add_finrank_ker`. Rewrite `h5` using `[h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top]`.

Establish `h6` using `(LinearMap.range (DcrisMap PD hp)).finrank_le`. Unfold `IsCrys at h ⊢`. Rewrite `h` using `[← h5, mul_add]`. Use `⟨by omega, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.range_eq_top]`.

Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
theorem of_shortExact [FiniteDimensional LL V]
    {ρ₀ : Representation LL G V₀} {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    {i : V₀ →ₗ[LL] V} {p : V →ₗ[LL] V'} (hi : IsEquivariant ρ₀ ρ i) (hp : IsEquivariant ρ ρ' p)
    (h1 : Function.Injective i) (h2 : Function.Exact i p) (h3 : Function.Surjective p)
    [Module.Finite LL ↥(Dcris PD ρ)] [Module.Finite LL ↥(Dcris PD ρ')]
    (a : finrank LL ↥(Dcris PD ρ₀) ≤ finrank Qp K₀ * finrank LL V₀)
    (c : finrank LL ↥(Dcris PD ρ') ≤ finrank Qp K₀ * finrank LL V')
    (h : IsCrys PD ρ) :
    IsCrys PD ρ₀ ∧ IsCrys PD ρ' ∧ Function.Surjective (DcrisMap PD hp) := by
  obtain ⟨e1, e2⟩ := GlobalTheory.RegularRing.left_exact PD hi hp h1 h2 h3
  have h4 := (DcrisMap PD hp).finrank_range_add_finrank_ker
  rw [e2.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1] at h4
  have h5 := p.finrank_range_add_finrank_ker
  rw [h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top] at h5
  have h6 := (LinearMap.range (DcrisMap PD hp)).finrank_le
  unfold IsCrys at h ⊢
  rw [← h5, mul_add] at h
  refine ⟨by omega, by omega, ?_⟩
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  omega

end Generic

/- English proof (translation)
Introduce `l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f hf`. Take `⟨hle, hfin⟩` from `GlobalTheory.T.fontaine_inequality_dcris_finite_concrete_rings l P AI T K LL`. Establish `he : IsEquivariant ρ ρ' f` using `hf`. Use `hfin V ρ` as an intermediate fact. Use `hfin V' ρ'` as an intermediate fact.

Use `⟨fun hi h => ?_, fun hs h => ?_⟩` and prove the remaining obligations. Establish `hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ' g)`. Introduce and unpack `g _ ⟨v, rfl⟩`. Conclude with `⟨ρ g v, hf g v⟩`. Establish `hq : IsEquivariant ρ' (ρ'.quotient (LinearMap.range f) hst) (LinearMap.range f).mkQ` using `fun g v => rfl`.

Use `hfin _ (ρ'.quotient (LinearMap.range f) hst)` as an intermediate fact. Conclude with `(of_shortExact (P.PD K) he hq hi (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective (hle V ρ) (hle _ _) h).1`. Establish `hst : ∀ g, LinearMap.ker f ≤ (LinearMap.ker f).comap (ρ g)`. Introduce `g v hv`. Rewrite using `[Submodule.mem_comap, LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]`.

Establish `hq : IsEquivariant (ρ.subrepresentation (LinearMap.ker f) hst) ρ (LinearMap.ker f).subtype` using `fun g v => rfl`. Take `⟨-, h1, h2⟩` from `of_shortExact (P.PD K) hq he (LinearMap.ker f).injective_subtype (LinearMap.exact_subtype_ker_map f) hs (hle _ _) (hle V' ρ') h`. Use `⟨h1, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `h2 ⟨y, hy⟩`. Conclude with `⟨x.1, x.2, congrArg Subtype.val hx⟩`.
-/
theorem crys_sub_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (f : V →ₗ[↥LL.1] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → IsCrys (P.PD K) ρ' → IsCrys (P.PD K) ρ) ∧ (Function.Surjective f → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' ∧ ∀ y ∈ Dcris (P.PD K) ρ', ∃ x ∈ Dcris (P.PD K) ρ, AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x = y) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f hf
  obtain ⟨hle, hfin⟩ := GlobalTheory.T.fontaine_inequality_dcris_finite_concrete_rings l P AI T K LL
  have he : IsEquivariant ρ ρ' f := hf
  have := hfin V ρ
  have := hfin V' ρ'
  refine ⟨fun hi h => ?_, fun hs h => ?_⟩
  · have hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ' g) := by
      rintro g _ ⟨v, rfl⟩
      exact ⟨ρ g v, hf g v⟩
    have hq : IsEquivariant ρ' (ρ'.quotient (LinearMap.range f) hst) (LinearMap.range f).mkQ :=
      fun g v => rfl
    have := hfin _ (ρ'.quotient (LinearMap.range f) hst)
    exact (of_shortExact (P.PD K) he hq hi (LinearMap.exact_map_mkQ_range f)
      (LinearMap.range f).mkQ_surjective (hle V ρ) (hle _ _) h).1
  · have hst : ∀ g, LinearMap.ker f ≤ (LinearMap.ker f).comap (ρ g) := by
      intro g v hv
      rw [Submodule.mem_comap, LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]
    have hq : IsEquivariant (ρ.subrepresentation (LinearMap.ker f) hst) ρ (LinearMap.ker f).subtype :=
      fun g v => rfl
    obtain ⟨-, h1, h2⟩ := of_shortExact (P.PD K) hq he (LinearMap.ker f).injective_subtype
      (LinearMap.exact_subtype_ker_map f) hs (hle _ _) (hle V' ρ') h
    refine ⟨h1, fun y hy => ?_⟩
    obtain ⟨x, hx⟩ := h2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

end GlobalTheory.Per.CrysSubQuot

import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPointsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqBotOrEqTopOfInvariant
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertHeckeEigen

open Formalism.UG GlobalTheory.PRep

section Abstract

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def quotMap (p : G →* H) (K : Subgroup H) : G ⧸ K.comap p → H ⧸ K :=
  Quotient.map' p fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact hab

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotMap_mk (p : G →* H) (K : Subgroup H) (a : G) :
    quotMap p K (a : G ⧸ K.comap p) = (p a : H ⧸ K) := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective x`. Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective y`. Rewrite `hxy` using `[quotMap_mk, quotMap_mk, QuotientGroup.eq]`.

Rewrite using `[QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]`. Conclude with `hxy`. Introduce `d`. Take `⟨y, rfl⟩` from `QuotientGroup.mk_surjective d`. Take `⟨a, rfl⟩` from `hp y`.

Conclude with `⟨a, rfl⟩`.
-/
theorem quotMap_bijective (p : G →* H) (hp : Function.Surjective p) (K : Subgroup H) :
    Function.Bijective (quotMap p K) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [quotMap_mk, quotMap_mk, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact hxy
  · intro d
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective d
    obtain ⟨a, rfl⟩ := hp y
    exact ⟨a, rfl⟩

/- English proof (translation)
Set `e` to `Equiv.ofBijective _ (quotMap_bijective p hp K)`. Rewrite using `[GlobalTheory.LFun.heckeVec_eq_of_section hh hv (fun d => p (e.symm d).out) fun d => ?_]`. Rewrite using `[← finsum_comp_equiv e (f := fun d => h (p (e.symm d).out) • ρ (p (e.symm d).out) v)]`. Simplify using `only [Equiv.symm_apply_apply]`. Both sides reduce to the same expression.

Rewrite using `[← quotMap_mk, QuotientGroup.out_eq']`. Conclude with `e.apply_symm_apply d`.
-/
theorem heckeVec_comp_surj (p : G →* H) (hp : Function.Surjective p) {K : Subgroup H} {h : H → ℂ}
    (hh : IsBiInv K h) (ρ : Representation ℂ H V) {v : V} (hv : v ∈ fixed ρ K) :
    GlobalTheory.LFun.heckeVec (ρ.comp p) (K.comap p) (fun x => h (p x)) v = GlobalTheory.LFun.heckeVec ρ K h v := by
  let e := Equiv.ofBijective _ (quotMap_bijective p hp K)
  rw [GlobalTheory.LFun.heckeVec_eq_of_section hh hv (fun d => p (e.symm d).out) fun d => ?_]
  · rw [← finsum_comp_equiv e (f := fun d => h (p (e.symm d).out) • ρ (p (e.symm d).out) v)]
    simp only [Equiv.symm_apply_apply]
    rfl
  · rw [← quotMap_mk, QuotientGroup.out_eq']
    exact e.apply_symm_apply d

/- English proof (translation)
Use `(hf.preimage (quotMap_bijective p hp K).1.injOn).subset fun c hc => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq] at hc ⊢`. Establish `hk : (quotMap p K c).out⁻¹ * p c.out ∈ K`. Rewrite using `[← QuotientGroup.eq, QuotientGroup.out_eq', ← quotMap_mk, QuotientGroup.out_eq']`. Establish `e1` using `hh 1 ⟨_, hk⟩ (quotMap p K c).out`.

Simplify using `only [OneMemClass.coe_one, one_mul, mul_inv_cancel_left] at e1`. Rewrite `hc` using `[e1]`. Then use the resulting hypothesis.
-/
theorem finite_support_comp (p : G →* H) (hp : Function.Surjective p) {K : Subgroup H} {h : H → ℂ}
    (hh : IsBiInv K h) (hf : {d : H ⧸ K | h d.out ≠ 0}.Finite) :
    {c : G ⧸ K.comap p | h (p c.out) ≠ 0}.Finite := by
  refine (hf.preimage (quotMap_bijective p hp K).1.injOn).subset fun c hc => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hc ⊢
  have hk : (quotMap p K c).out⁻¹ * p c.out ∈ K := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← quotMap_mk, QuotientGroup.out_eq']
  have e1 := hh 1 ⟨_, hk⟩ (quotMap p K c).out
  simp only [OneMemClass.coe_one, one_mul, mul_inv_cancel_left] at e1
  rwa [e1] at hc

/- English proof (translation)
Use `finsum_eq_sum_of_support_subset _ fun c hc => hS c fun h0 => hc ?_` and prove the remaining obligations. Simplify using `[h0]`.
-/
theorem heckeVec_eq_sum (ρ : Representation ℂ G V) (K : Subgroup G) (h : G → ℂ) (S : Finset (G ⧸ K))
    (hS : ∀ c : G ⧸ K, h c.out ≠ 0 → c ∈ S) (x : V) :
    GlobalTheory.LFun.heckeVec ρ K h x = ∑ c ∈ S, h c.out • ρ c.out x := by
  refine finsum_eq_sum_of_support_subset _ fun c hc => hS c fun h0 => hc ?_
  simp [h0]

/- English proof (translation)
Use `first`. Consider the case `(rename_i h_3 h_4 h_5 h_6 h_7; revert G V W h_3 h_4 h_5 h_6 h_7 ι ρ σ hσ f hf K Z hZ hZK φ hK hφ; exact @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range)`. Consider the case `exact @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range`. Consider the case `exact _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range`. Consider the case `(apply _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> assumption)`.

Consider the case `(intros; apply _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> assumption)`. Consider the case `(intros; apply @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range ..)`.
-/
theorem mem_of_mem_iSup {ι : Type} (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hσ : σ.IsIrreducible)
    (f : ι → W →ₗ[ℂ] V) (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (Z : Submodule ℂ V)
    (hZ : ∀ i v, (∀ k ∈ K, σ k v = v) → f i v ∈ Z) (hZK : ∀ z ∈ Z, ∀ k ∈ K, ρ k z = z) (φ : V)
    (hK : ∀ k ∈ K, ρ k φ = φ) (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : φ ∈ Z := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7; revert G V W h_3 h_4 h_5 h_6 h_7 ι ρ σ hσ f hf K Z hZ hZK φ hK hφ; exact @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range)
  | exact @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range
  | exact _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range
  | (apply _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range ..)

end Abstract

end GlobalTheory.InertHeckeEigen

open GlobalTheory.InertHeckeEigen Formalism.UG GlobalTheory.PRep GlobalTheory.DefU in

/- English proof (translation)
Introduce `L _ _ _ n U hU w s ϖ q hq p hp σ hcomp α0 hsat φ hφ hfix h hh`. Establish `hfin : {c : locU n w ⧸ (KU s n).comap p | h (p c.out) ≠ 0}.Finite` using `finite_support_comp p hp hh.1 (Formalism.UG.P.finite_support_cosets (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hq n) hh.2)`. Establish `hS : ∀ c : locU n w ⧸ (KU s n).comap p, (fun x => h (p x)) c.out ≠ 0 → c ∈ hfin.toFinset` using `fun c hc => hfin.mem_toFinset.2 hc`. Set `T : (UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ)` to `∑ c ∈ hfin.toFinset, h (p c.out) • (RU L n) (c.out : UA L n)`. Establish `hT : ∀ x, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((KU s n).comap p) (fun x => h (p x)) x = T x` using `fun x => by`.

Rewrite using `[heckeVec_eq_sum _ _ _ _ hS x]`. Simplify using `[T, LinearMap.sum_apply]`. Set `lam` to `SatU ϖ q h (fun i => (α0 i : ℂ))`. Set `Z : Submodule ℂ (UA L n → ℂ)` to `fixed ((RU L n).comp (locU n w).subtype) ((KU s n).comap p) ⊓ LinearMap.ker (T - lam • LinearMap.id)`. Establish `hZ' : ∀ x, x ∈ Z ↔ (∀ k ∈ (KU s n).comap p, RU L n (k : UA L n) x = x) ∧ T x = lam • x` using `fun x => by`.

Simplify using `only [Z, Submodule.mem_inf, GlobalTheory.LGrp.mem_fixed, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Both sides reduce to the same expression. Set `π : AutSub L n` to `⟨U, hU⟩`. Take `⟨hσirr, f, hf0, hfm, hf⟩` from `hcomp`. Establish `hirr : Representation.IsIrreducible (σ.ρ.comp p)`.

Take `⟨h0, h1⟩` from `(GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr`. Use `(GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hp g`. Conclude with `hY x v hv`. Set `F : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype)` to `⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩`.

Establish `hF0 : F ≠ 0` using `fun h => hf0 (LinearMap.ext fun v => by`. Use `congrArg Subtype.val (DFunLike.congr_fun h v)` as an intermediate fact. Conclude with `this)`. Take `⟨r, -, -, hr⟩` from `GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints L n w`. Establish `htop` using `(GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA L n) (locU n w) π.V σ.V σ.V π.rep (locU n w).subtype (σ.ρ.comp p) (σ.ρ.comp p) π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1`.

Set `fi : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) → σ.V →ₗ[ℂ] (UA L n → ℂ)` to `fun i => U.subtype ∘ₗ i.toLinearMap`. Establish `hfi : ∀ i g u, fi i ((σ.ρ.comp p) g u) = (RU L n).comp (locU n w).subtype g (fi i u)` using `fun i g u => congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) i g u)`. Establish `hmem : φ ∈ ⨆ i, LinearMap.range (fi i)`. Establish `: φ ∈ (⨆ i : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype), LinearMap.range i.toLinearMap).map U.subtype`. Rewrite using `[htop]`.

Conclude with `⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩`. Simplify using `only [fi, LinearMap.range_comp]`. Rewrite `this` using `[Submodule.map_iSup]`. Then use the resulting hypothesis. Establish `hZ : ∀ i v, (∀ k ∈ ((KU s n).comap p : Set (locU n w)), (σ.ρ.comp p) k v = v) → fi i v ∈ Z`. Introduce `i v hv`.

Distinguish the cases in `hv0 : v = 0`. Rewrite using `[hv0, map_zero]`. Conclude with `Z.zero_mem`. Establish `hvK : v ∈ fixed σ.ρ (KU s n)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => by`. Take `⟨x, rfl⟩` from `hp k`.

Conclude with `hv x hk`. Use `(hZ' _).2 ⟨fun k hk => (hfi i k v).symm.trans (congrArg (fi i) (hv k hk)), ?_⟩` and prove the remaining obligations. Establish `e2` using `heckeVec_comp_surj p hp hh.1 σ.ρ hvK`. Rewrite `e2` using `[heckeVec_eq_sum _ _ _ _ hS]`. Rewrite `e2` using `[((hsat.2 v hvK hv0).2.2 h hh)]`.

Rewrite using `[← hT (fi i v), heckeVec_eq_sum _ _ _ _ hS]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hfi]`.

Use `_ = lam • fi i v := by rw [e2, map_smul]`. Establish `hZK : ∀ z ∈ Z, ∀ k ∈ ((KU s n).comap p : Set (locU n w)), (RU L n).comp (locU n w).subtype k z = z` using `fun z hz k hk => ((hZ' z).1 hz).1 k hk`. Establish `hφZ` using `mem_of_mem_iSup ((RU L n).comp (locU n w).subtype) (σ.ρ.comp p) hirr fi hfi _ Z hZ hZK φ (fun k hk => hfix k hk) hmem`. Rewrite using `[hT]`. Conclude with `((hZ' φ).1 hφZ).2`.
-/
theorem GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)) (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), Formalism.UG.IsUnramInv ϖ s q → ∀ p : locU n w →* Formalism.UG.GU s n, Function.Surjective p → ∀ σ : SmIrr (Formalism.UG.GU s n), IsCompAlong U (locU n w) p σ.ρ → ∀ α0 : Fin (n / 2) → ℂˣ, GlobalTheory.LFun.HasSatU ϖ q σ.ρ α0 → ∀ φ ∈ U, (∀ x : locU n w, p x ∈ Formalism.UG.KU s n → RU L n x.val φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU s n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU s n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU ϖ q h (fun i => (α0 i : ℂ)) • φ := by
  intro L _ _ _ n U hU w s ϖ q hq p hp σ hcomp α0 hsat φ hφ hfix h hh
  have hfin : {c : locU n w ⧸ (KU s n).comap p | h (p c.out) ≠ 0}.Finite :=
    finite_support_comp p hp hh.1 (Formalism.UG.P.finite_support_cosets (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hq n) hh.2)
  have hS : ∀ c : locU n w ⧸ (KU s n).comap p, (fun x => h (p x)) c.out ≠ 0 → c ∈ hfin.toFinset :=
    fun c hc => hfin.mem_toFinset.2 hc
  let T : (UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    ∑ c ∈ hfin.toFinset, h (p c.out) • (RU L n) (c.out : UA L n)
  have hT : ∀ x, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((KU s n).comap p) (fun x => h (p x)) x
      = T x := fun x => by
    rw [heckeVec_eq_sum _ _ _ _ hS x]
    simp [T, LinearMap.sum_apply]
  let lam := SatU ϖ q h (fun i => (α0 i : ℂ))
  let Z : Submodule ℂ (UA L n → ℂ) :=
    fixed ((RU L n).comp (locU n w).subtype) ((KU s n).comap p) ⊓ LinearMap.ker (T - lam • LinearMap.id)
  have hZ' : ∀ x, x ∈ Z ↔ (∀ k ∈ (KU s n).comap p, RU L n (k : UA L n) x = x) ∧ T x = lam • x := fun x => by
    simp only [Z, Submodule.mem_inf, GlobalTheory.LGrp.mem_fixed, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl

  let π : AutSub L n := ⟨U, hU⟩
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hcomp
  have hirr : Representation.IsIrreducible (σ.ρ.comp p) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints L n w
  have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA L n) (locU n w) π.V σ.V σ.V π.rep (locU n w).subtype (σ.ρ.comp p) (σ.ρ.comp p)
    π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) → σ.V →ₗ[ℂ] (UA L n → ℂ) :=
    fun i => U.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.ρ.comp p) g u) = (RU L n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype),
        LinearMap.range i.toLinearMap).map U.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this

  have hZ : ∀ i v, (∀ k ∈ ((KU s n).comap p : Set (locU n w)), (σ.ρ.comp p) k v = v) → fi i v ∈ Z := by
    intro i v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]; exact Z.zero_mem
    have hvK : v ∈ fixed σ.ρ (KU s n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
      obtain ⟨x, rfl⟩ := hp k
      exact hv x hk
    refine (hZ' _).2 ⟨fun k hk => (hfi i k v).symm.trans (congrArg (fi i) (hv k hk)), ?_⟩
    have e2 := heckeVec_comp_surj p hp hh.1 σ.ρ hvK
    rw [heckeVec_eq_sum _ _ _ _ hS] at e2
    rw [((hsat.2 v hvK hv0).2.2 h hh)] at e2
    rw [← hT (fi i v), heckeVec_eq_sum _ _ _ _ hS]
    calc _ = fi i (∑ c ∈ hfin.toFinset, h (p c.out) • (σ.ρ.comp p) c.out v) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_smul, hfi]
      _ = lam • fi i v := by rw [e2, map_smul]
  have hZK : ∀ z ∈ Z, ∀ k ∈ ((KU s n).comap p : Set (locU n w)), (RU L n).comp (locU n w).subtype k z = z :=
    fun z hz k hk => ((hZ' z).1 hz).1 k hk
  have hφZ := mem_of_mem_iSup ((RU L n).comp (locU n w).subtype) (σ.ρ.comp p) hirr fi hfi _ Z hZ hZK φ
    (fun k hk => hfix k hk) hmem
  rw [hT]
  exact ((hZ' φ).1 hφZ).2

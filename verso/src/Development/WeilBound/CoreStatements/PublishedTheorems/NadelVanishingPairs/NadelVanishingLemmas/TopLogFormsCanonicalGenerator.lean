import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsEqChartForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemChartFormsIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTop

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogDR
open TopForm
variable {k K : Type} [CommRing k] [Field K]

def absDer (α : k →+* K) (hk : Function.Surjective (Int.castRingHom k)) :
    letI := α.toAlgebra; letI : Module k Ω[K⁄ℤ] := Module.compHom _ α; Derivation k K Ω[K⁄ℤ] :=
  letI := α.toAlgebra
  letI : Module k Ω[K⁄ℤ] := Module.compHom _ α
  { toFun := KaehlerDifferential.D ℤ K
    map_add' := map_add _
    map_smul' := fun c a => by
      obtain ⟨n, rfl⟩ := hk c
      rw [Algebra.smul_def, Derivation.leibniz]
      have : algebraMap k K (Int.castRingHom k n) = algebraMap ℤ K n := by simp
      rw [this, Derivation.map_algebraMap, smul_zero, add_zero, RingHom.id_apply]
      exact congrArg (· • KaehlerDifferential.D ℤ K a) this.symm
    map_one_eq_zero' := Derivation.map_one_eq_zero _
    leibniz' := fun a b => Derivation.leibniz _ a b }

/- English proof (translation)
Introduce `a` and use `ZMod.intCast_surjective a`.
-/
theorem intCast_surj (p : ℕ) : Function.Surjective (Int.castRingHom (ZMod p)) :=
  fun a => ZMod.intCast_surjective a

def omegaToAbs (α : k →+* K) (hk : Function.Surjective (Int.castRingHom k)) :
    Omega α →ₗ[K] Ω[K⁄ℤ] :=
  letI := α.toAlgebra
  letI : Module k Ω[K⁄ℤ] := Module.compHom _ α
  letI tw : IsScalarTower k K Ω[K⁄ℤ] := ⟨fun c a m => mul_smul (α c) a m⟩
  @Derivation.liftKaehlerDifferential k K _ _ _ _ _ _ _ tw (absDer α hk)

/- English proof (translation)
Use `letI := α.toAlgebra`. Use `letI : Module k Ω[K⁄ℤ] := Module.compHom _ α`. Use `letI tw : IsScalarTower k K Ω[K⁄ℤ] := ⟨fun c a m => mul_smul (α c) a m⟩`. Conclude with `@Derivation.liftKaehlerDifferential_comp_D k K _ _ _ _ _ _ _ tw (absDer α hk) f`.
-/
@[simp] theorem omegaToAbs_dFun (α : k →+* K) (hk : Function.Surjective (Int.castRingHom k)) (f : K) :
    omegaToAbs α hk (dFun α f) = dK f := by
  letI := α.toAlgebra
  letI : Module k Ω[K⁄ℤ] := Module.compHom _ α
  letI tw : IsScalarTower k K Ω[K⁄ℤ] := ⟨fun c a m => mul_smul (α c) a m⟩
  exact @Derivation.liftKaehlerDifferential_comp_D k K _ _ _ _ _ _ _ tw (absDer α hk) f

def formsToLam (α : k →+* K) (hk : Function.Surjective (Int.castRingHom k)) (D : ℕ) :
    Forms α D →ₗ[K] abelian₂ K :=
  (⋀[K]^D Ω[K⁄ℤ]).subtype ∘ₗ exteriorPower.map D (omegaToAbs α hk)

/- English proof (translation)
Simplify using `only [formsToLam, dForm, dWedge, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti, Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe, Function.comp_def]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `omegaToAbs_dFun α hk (f i)`.
-/
theorem formsToLam_dForm (α : k →+* K) (hk : Function.Surjective (Int.castRingHom k)) {D : ℕ}
    (f : Fin D → K) :
    formsToLam α hk D (dForm α f) = ExteriorAlgebra.ιMulti K D fun i => dK (f i) := by
  simp only [formsToLam, dForm, dWedge, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
    Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe, Function.comp_def]
  congr 1
  funext i
  exact omegaToAbs_dFun α hk (f i)

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR
open TopForm GlobalTheory.Cartier.CartierDiv

/- English proof (translation)
Take `⟨e, he_inj, hJ, hE⟩` from `h`. Establish `key : ∀ S : Finset C, (∑ c ∈ S, E c).IsEqn y (∏ c ∈ S, (e c).elim 1 x)`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using isEqn_zero y`.

Consider the case `insert a S ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `(hE a y hy).add ih`. Establish `hprod : (∏ c, (e c).elim 1 x) = ∏ j ∈ J, x j`. Establish `s1 : ∀ c, (e c).elim 1 x = ∏ j ∈ J, (if e c = some j then x j else 1)`.

Introduce `c`. Consider the cases of `hc : e c with`. Consider the case `none => simp`. Consider the case `some j0`. Establish `hj0 : j0 ∈ J` using `(hJ j0).2 ⟨c, hc⟩`.

Simplify using `[hj0]`. Establish `s2 : ∀ j ∈ J, (∏ c, (if e c = some j then x j else 1)) = x j`. Introduce `j hj`. Take `⟨c0, hc0⟩` from `(hJ j).1 hj`. Establish `hiff : ∀ c, (e c = some j ↔ c0 = c)` using `fun c => ⟨fun h => he_inj c0 c j hc0 h, fun h => h ▸ hc0⟩`.

Simplify using `only [hiff]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_congr rfl (fun c _ => s1 c), Finset.prod_comm]`. Conclude with `Finset.prod_congr rfl s2`. Use `key Finset.univ` as an intermediate fact.

Rewrite `this` using `[hprod]`. Then use the resulting hypothesis.
-/
theorem isEqn_sum_of_isSncOn {X : Scheme.{0}} [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X)
    (U : X.Opens) {n : ℕ} (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (h : IsSncOn E U x J)
    (y : X) (hy : y ∈ U) : (∑ c, E c).IsEqn y (∏ j ∈ J, x j) := by
  classical
  obtain ⟨e, he_inj, hJ, hE⟩ := h
  have key : ∀ S : Finset C, (∑ c ∈ S, E c).IsEqn y (∏ c ∈ S, (e c).elim 1 x) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using isEqn_zero y
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact (hE a y hy).add ih
  have hprod : (∏ c, (e c).elim 1 x) = ∏ j ∈ J, x j := by
    have s1 : ∀ c, (e c).elim 1 x = ∏ j ∈ J, (if e c = some j then x j else 1) := by
      intro c
      cases hc : e c with
      | none => simp
      | some j0 =>
        have hj0 : j0 ∈ J := (hJ j0).2 ⟨c, hc⟩
        simp [hj0]
    have s2 : ∀ j ∈ J, (∏ c, (if e c = some j then x j else 1)) = x j := by
      intro j hj
      obtain ⟨c0, hc0⟩ := (hJ j).1 hj
      have hiff : ∀ c, (e c = some j ↔ c0 = c) := fun c =>
        ⟨fun h => he_inj c0 c j hc0 h, fun h => h ▸ hc0⟩
      simp only [hiff]
      simp
    rw [Finset.prod_congr rfl (fun c _ => s1 c), Finset.prod_comm]
    exact Finset.prod_congr rfl s2
  have := key Finset.univ
  rwa [hprod] at this

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR
open TopForm GlobalTheory.Cartier.CartierDiv
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `A.sum_mem fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Conclude with `A.zsmul_mem (A.prod_mem fun i _ => hc _ _) _`.
-/
theorem det_mem_subring {K : Type} [Field K] (A : Subring K) {n : ℕ} (c : Matrix (Fin n) (Fin n) K)
    (hc : ∀ i k, c i k ∈ A) : c.det ∈ A := by
  rw [Matrix.det_apply]
  refine A.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact A.zsmul_mem (A.prod_mem fun i _ => hc _ _) _

/- English proof (translation)
Use `letI := α.toAlgebra`. Establish `hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A d))`. Rewrite using `[exteriorPower.ιMulti_span]`. Discharge the goal by the elementary cases of `trivial`. Use `Submodule.span_induction (fun x hx => ?_) P.zero_mem (fun _ _ _ _ => P.add_mem) (fun a _ _ => P.smul_mem a) hω` and prove the remaining obligations.

Take `⟨w, rfl⟩` from `hx`. Establish `hw : ∀ i, ∃ c : A →₀ A, (c.sum fun a r => r • KaehlerDifferential.D k A a) = w i` using `fun i => (Finsupp.mem_span_range_iff_exists_finsupp).1 (by rw [KaehlerDifferential.span_range_derivation]; trivial)`. Use `choose c hc using hw`. Establish `hw' : w = fun i => ∑ a ∈ (c i).support, c i a • KaehlerDifferential.D k A a`. Use function extensionality and compare the values at `fun i => (hc i).symm`.

Rewrite using `[hw']`. Rewrite using `[← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum_finset]`. Use `P.sum_mem fun r _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ, AlternatingMap.coe_multilinearMap]`. Conclude with `P.smul_mem _ (hgen r)`.
-/
private theorem forms_mem_lemma {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) (d : ℕ)
    (P : Submodule A (Forms α d)) (hgen : ∀ f : Fin d → A, dForm α f ∈ P) (ω : Forms α d) : ω ∈ P := by
  letI := α.toAlgebra
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A d)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  refine Submodule.span_induction (fun x hx => ?_) P.zero_mem (fun _ _ _ _ => P.add_mem)
    (fun a _ _ => P.smul_mem a) hω
  obtain ⟨w, rfl⟩ := hx
  have hw : ∀ i, ∃ c : A →₀ A, (c.sum fun a r => r • KaehlerDifferential.D k A a) = w i := fun i =>
    (Finsupp.mem_span_range_iff_exists_finsupp).1
      (by rw [KaehlerDifferential.span_range_derivation]; trivial)
  choose c hc using hw
  have hw' : w = fun i => ∑ a ∈ (c i).support, c i a • KaehlerDifferential.D k A a :=
    funext fun i => (hc i).symm
  rw [hw']
  rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum_finset]
  refine P.sum_mem fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, AlternatingMap.coe_multilinearMap]
  exact P.smul_mem _ (hgen r)

/- English proof (translation)
Use `set b := Module.Basis.mk hx.1 (le_of_eq hx.2.symm) with hbdef`. Establish `hb : (fun j => dK (x j : K)) = ⇑b` using `(Module.Basis.coe_mk _ _).symm`. Rewrite using `[hb, ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]`. Introduce `φ`. Establish `h1` using `congrArg (fun g => g v) (AlternatingMap.eq_smul_basis_det b (φ.compAlternatingMap (ExteriorAlgebra.ιMulti K n)))`.

Simplify using `only [AlternatingMap.smul_apply, LinearMap.compAlternatingMap_apply, smul_eq_mul] at h1`. Rewrite using `[map_sub, map_smul, h1, smul_eq_mul, mul_comm, sub_self]`.
-/
private theorem ιMulti_eq_det_lemma_2 {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x)
    (v : Fin n → Ω[K⁄ℤ]) :
    ExteriorAlgebra.ιMulti K n v = (Module.Basis.mk hx.1 (le_of_eq hx.2.symm)).det v •
      ExteriorAlgebra.ιMulti K n (fun j => dK (x j : K)) := by
  classical
  set b := Module.Basis.mk hx.1 (le_of_eq hx.2.symm) with hbdef
  have hb : (fun j => dK (x j : K)) = ⇑b := (Module.Basis.coe_mk _ _).symm
  rw [hb, ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  have h1 := congrArg (fun g => g v)
    (AlternatingMap.eq_smul_basis_det b (φ.compAlternatingMap (ExteriorAlgebra.ιMulti K n)))
  simp only [AlternatingMap.smul_apply, LinearMap.compAlternatingMap_apply, smul_eq_mul] at h1
  rw [map_sub, map_smul, h1, smul_eq_mul, mul_comm, sub_self]

/- English proof (translation)
Establish `hxc` using `hx.coord`. Use `set b := Module.Basis.mk hxc.1 (le_of_eq hxc.2.symm) with hbdef`. Establish `hbi : ∀ i, b i = dK (x i : X.functionField)` using `fun i => Module.Basis.mk_apply _ _ _`. Establish `hrep : ∀ g ∈ locRing y, ∀ j, b.repr (dK g) j ∈ locRing y`. Introduce `g hg j`.

Take `⟨c, hc, hd⟩` from `hx.deriv g hg`. Establish `hs : dK g = ∑ i, c i • b i`. Rewrite using `[hd]`. Simplify using `only [hbi]`. Rewrite using `[hs, Module.Basis.repr_sum_self]`.

Conclude with `hc j`. Set `W` to `ExteriorAlgebra.ιMulti X.functionField d (fun j => dK (x j : X.functionField))`. Set `P : Submodule (Γ(X, U)) (FormsOn f d U)` to `{ carrier := {ω | ∃ u, RegAt y u ∧ formsToLam (constFn f) (intCast_surj p) d (formOf U (gen_mem hy) ω) = u • W} add_mem' := by`. Introduce and unpack `a c ⟨u1, h1, e1⟩ ⟨u2, h2, e2⟩`. Conclude with `⟨u1 + u2, h1.add h2, by rw [map_add, map_add, e1, e2, add_smul]⟩`.

Use the proof step `zero_mem' := ⟨0, regAt_zero y, by rw [map_zero, map_zero, zero_smul]⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `a c ⟨u, hu, e⟩`. Use `⟨fnOf U (gen_mem hy) a * u, (regAt_fnOf hy _ a).mul hu, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, map_smul, e, mul_smul] }`.

Establish `hgen : ∀ g : Fin d → Γ(X, U), dForm (algX f U) g ∈ P`. Introduce `g`. Use `⟨b.det (fun j => dK (fnOf U (gen_mem hy) (g j))), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← mem_locRing, Module.Basis.det_apply]`. Use `det_mem_subring _ _ fun i j => ?_` and prove the remaining obligations.

Rewrite using `[Module.Basis.toMatrix_apply]`. Conclude with `hrep _ (mem_locRing.2 (regAt_fnOf hy _ _)) i`. Simplify using `only [formOf, formMap_dForm, formsToLam_dForm]`. Conclude with `ιMulti_eq_det_lemma_2 x hxc _`. Conclude with `forms_mem_lemma (algX f U) d P hgen ω`.
-/
theorem formOf_eq_regAt_smul (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp (ZMod p))
    (d : ℕ) {U : X.Opens} (ω : FormsOn f d U) (y : X) (hy : y ∈ U) (x : Fin d → X.functionFieldˣ)
    (hx : AlgChart (locRing y) x) :
    ∃ u : X.functionField, RegAt y u ∧
      formsToLam (constFn f) (intCast_surj p) d (formOf U (gen_mem hy) ω) =
        u • ExteriorAlgebra.ιMulti _ d fun j => dK (x j : X.functionField) := by
  classical
  have hxc := hx.coord
  set b := Module.Basis.mk hxc.1 (le_of_eq hxc.2.symm) with hbdef
  have hbi : ∀ i, b i = dK (x i : X.functionField) := fun i => Module.Basis.mk_apply _ _ _
  have hrep : ∀ g ∈ locRing y, ∀ j, b.repr (dK g) j ∈ locRing y := by
    intro g hg j
    obtain ⟨c, hc, hd⟩ := hx.deriv g hg
    have hs : dK g = ∑ i, c i • b i := by
      rw [hd]
      simp only [hbi]
    rw [hs, Module.Basis.repr_sum_self]
    exact hc j
  let W := ExteriorAlgebra.ιMulti X.functionField d (fun j => dK (x j : X.functionField))
  let P : Submodule (Γ(X, U)) (FormsOn f d U) :=
    { carrier := {ω | ∃ u, RegAt y u ∧
        formsToLam (constFn f) (intCast_surj p) d (formOf U (gen_mem hy) ω) = u • W}
      add_mem' := by
        rintro a c ⟨u1, h1, e1⟩ ⟨u2, h2, e2⟩
        exact ⟨u1 + u2, h1.add h2, by rw [map_add, map_add, e1, e2, add_smul]⟩
      zero_mem' := ⟨0, regAt_zero y, by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro a c ⟨u, hu, e⟩
        refine ⟨fnOf U (gen_mem hy) a * u, (regAt_fnOf hy _ a).mul hu, ?_⟩
        rw [LinearMap.map_smulₛₗ, map_smul, e, mul_smul] }
  have hgen : ∀ g : Fin d → Γ(X, U), dForm (algX f U) g ∈ P := by
    intro g
    refine ⟨b.det (fun j => dK (fnOf U (gen_mem hy) (g j))), ?_, ?_⟩
    · rw [← mem_locRing, Module.Basis.det_apply]
      refine det_mem_subring _ _ fun i j => ?_
      rw [Module.Basis.toMatrix_apply]
      exact hrep _ (mem_locRing.2 (regAt_fnOf hy _ _)) i
    · simp only [formOf, formMap_dForm, formsToLam_dForm]
      exact ιMulti_eq_det_lemma_2 x hxc _
  exact forms_mem_lemma (algX f U) d P hgen ω

/- English proof (translation)
Use `choose Uj hyj aj haj using fun j => RegAt.exists_fnOf (hx j)`. Establish `hS : (U : Set X) ∩ ⋂ j, (Uj j : Set X) ∈ nhds y` using `Filter.inter_mem (U.isOpen.mem_nhds hy) (Filter.iInter_mem.2 fun j => (Uj j).isOpen.mem_nhds (hyj j))`. Set `O : X.Opens` to `⟨interior ((U : Set X) ∩ ⋂ j, (Uj j : Set X)), isOpen_interior⟩`. Establish `hyO : y ∈ O` using `mem_interior_iff_mem_nhds.2 hS`. Take `⟨W, hWa, hyW, hWO⟩` from `(Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)) hyO`.

Establish `hWU : W ≤ U` using `fun z hz => (interior_subset (hWO hz)).1`. Establish `hWj : ∀ j, W ≤ Uj j` using `fun j z hz => Set.mem_iInter.1 (interior_subset (hWO hz)).2 j`. Establish `hg : genericPoint X ∈ W` using `gen_mem hyW`. Establish `hgx : ∀ j, fnOf W hg (resG X (hWj j) (aj j)) = (x j : X.functionField)`. Introduce `j`.

Rewrite using `[fnOf_resG]`. Conclude with `haj j`. Take `⟨c, hc⟩` from `hω.exists_coeff hWU (dForm (algX f W) fun j => resG X (hWj j) (aj j))`. Establish `hc'` using `hc W hWa le_rfl`. Establish `e1 : formOf W hg (resForm le_rfl (dForm (algX f W) fun j => resG X (hWj j) (aj j))) = formOf W hg (dForm (algX f W) fun j => resG X (hWj j) (aj j))` using `formOf_resForm le_rfl hg _`.

Establish `e2 : formOf W hg (resForm hWU ω) = formOf U (gen_mem hy) ω` using `formOf_resForm hWU hg ω`. Establish `e3 : formsToLam (constFn f) (intCast_surj p) d (formOf W hg (dForm (algX f W) fun j => resG X (hWj j) (aj j))) = ExteriorAlgebra.ιMulti _ d (fun j => dK (x j : X.functionField))`. Simplify using `only [formOf, formMap_dForm, formsToLam_dForm]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Rewrite using `[← hgx j]`. Use `⟨fnOf W hg (resG X le_rfl c), regAt_fnOf hyW hg _, ?_⟩` and prove the remaining obligations. Rewrite using `[← e3, ← e1, hc', LinearMap.map_smulₛₗ, map_smul, e2]`.
-/
theorem coordForm_eq_regAt_smul (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp (ZMod p))
    (d : ℕ) {U : X.Opens} (ω : FormsOn f d U) (hω : IsFrame ω) (y : X) (hy : y ∈ U)
    (x : Fin d → X.functionFieldˣ) (hx : ∀ j, RegAt y (x j : X.functionField)) :
    ∃ v : X.functionField, RegAt y v ∧
      ExteriorAlgebra.ιMulti _ d (fun j => dK (x j : X.functionField)) =
        v • formsToLam (constFn f) (intCast_surj p) d (formOf U (gen_mem hy) ω) := by
  classical
  choose Uj hyj aj haj using fun j => RegAt.exists_fnOf (hx j)
  have hS : (U : Set X) ∩ ⋂ j, (Uj j : Set X) ∈ nhds y :=
    Filter.inter_mem (U.isOpen.mem_nhds hy)
      (Filter.iInter_mem.2 fun j => (Uj j).isOpen.mem_nhds (hyj j))
  let O : X.Opens := ⟨interior ((U : Set X) ∩ ⋂ j, (Uj j : Set X)), isOpen_interior⟩
  have hyO : y ∈ O := mem_interior_iff_mem_nhds.2 hS
  obtain ⟨W, hWa, hyW, hWO⟩ := (Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)) hyO
  have hWU : W ≤ U := fun z hz => (interior_subset (hWO hz)).1
  have hWj : ∀ j, W ≤ Uj j := fun j z hz => Set.mem_iInter.1 (interior_subset (hWO hz)).2 j
  have hg : genericPoint X ∈ W := gen_mem hyW
  have hgx : ∀ j, fnOf W hg (resG X (hWj j) (aj j)) = (x j : X.functionField) := by
    intro j
    rw [fnOf_resG]
    exact haj j
  obtain ⟨c, hc⟩ := hω.exists_coeff hWU (dForm (algX f W) fun j => resG X (hWj j) (aj j))
  have hc' := hc W hWa le_rfl
  have e1 : formOf W hg (resForm le_rfl (dForm (algX f W) fun j => resG X (hWj j) (aj j))) =
      formOf W hg (dForm (algX f W) fun j => resG X (hWj j) (aj j)) :=
    formOf_resForm le_rfl hg _
  have e2 : formOf W hg (resForm hWU ω) = formOf U (gen_mem hy) ω := formOf_resForm hWU hg ω
  have e3 : formsToLam (constFn f) (intCast_surj p) d
      (formOf W hg (dForm (algX f W) fun j => resG X (hWj j) (aj j))) =
      ExteriorAlgebra.ιMulti _ d (fun j => dK (x j : X.functionField)) := by
    simp only [formOf, formMap_dForm, formsToLam_dForm]
    congr 1
    funext j
    rw [← hgx j]
  refine ⟨fnOf W hg (resG X le_rfl c), regAt_fnOf hyW hg _, ?_⟩
  rw [← e3, ← e1, hc', LinearMap.map_smulₛₗ, map_smul, e2]

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR
open TopForm GlobalTheory.Cartier.CartierDiv

/- English proof (translation)
Take `⟨hli, hsp⟩` from `hx`. Set `b` to `Module.Basis.mk hli (le_of_eq hsp.symm)`. Introduce `h0`. Establish `hb : (fun j => dK (x j : K)) = ⇑b` using `(Module.Basis.coe_mk _ _).symm`. Establish `hc : (Finset.univ : Finset (Fin n)).card = n` using `by simp`.

Establish `he : ∀ e : Fin n ↪o Fin n, ⇑e = id`. Introduce `e`. Establish `h1` using `Finset.orderEmbOfFin_unique' hc (f := e) (fun _ => Finset.mem_univ _)`. Establish `h2` using `Finset.orderEmbOfFin_unique' hc (f := (OrderIso.refl (Fin n)).toOrderEmbedding) (fun _ => Finset.mem_univ _)`. Rewrite using `[h1, ← h2]`.

Both sides reduce to the same expression. Set `s : Set.powersetCard (Fin n) n` to `⟨Finset.univ, by simp⟩`. Establish `hne` using `(exteriorPower.ιMulti_family_linearIndependent_ofBasis K n b).ne_zero s`. Apply `hne` to reduce the goal to its premises. Rewrite using `[exteriorPower.ιMulti_family, he, Function.comp_id, ← hb]`.

Conclude with `Subtype.ext (by simpa using h0)`.
-/
theorem ιMulti_coord_ne_zero {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    ExteriorAlgebra.ιMulti K n (fun j => dK (x j : K)) ≠ 0 := by
  classical
  obtain ⟨hli, hsp⟩ := hx
  let b := Module.Basis.mk hli (le_of_eq hsp.symm)
  intro h0
  have hb : (fun j => dK (x j : K)) = ⇑b := (Module.Basis.coe_mk _ _).symm
  have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
  have he : ∀ e : Fin n ↪o Fin n, ⇑e = id := by
    intro e
    have h1 := Finset.orderEmbOfFin_unique' hc (f := e) (fun _ => Finset.mem_univ _)
    have h2 := Finset.orderEmbOfFin_unique' hc
      (f := (OrderIso.refl (Fin n)).toOrderEmbedding) (fun _ => Finset.mem_univ _)
    rw [h1, ← h2]
    rfl
  let s : Set.powersetCard (Fin n) n := ⟨Finset.univ, by simp⟩
  have hne := (exteriorPower.ιMulti_family_linearIndependent_ofBasis K n b).ne_zero s
  apply hne
  rw [exteriorPower.ιMulti_family, he, Function.comp_id, ← hb]
  exact Subtype.ext (by simpa using h0)

/- English proof (translation)
Use `set L := CanonLB.all f d with hL`. Establish `hcov : y ∈ ⨆ i, L.bundle.U i`. Rewrite using `[L.isLB.cover]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hcov`.

Establish `hω : IsFrame (L.om i)` using `L.isFrame i`. Establish `hgU : genericPoint X ∈ L.bundle.U i` using `gen_mem hi`. Take `⟨u0, hu0, e0⟩` from `formOf_eq_regAt_smul p f d (L.om i) y hi x hx`. Take `⟨v, hv, ev⟩` from `coordForm_eq_regAt_smul p f d (L.om i) hω y hi x (fun j => mem_locRing.1 (hx.mem j))`. Establish `hW : ExteriorAlgebra.ιMulti X.functionField d (fun j => dK (x j : X.functionField)) ≠ 0` using `ιMulti_coord_ne_zero x hx.coord`.

Establish `hvu : v * u0 = 1`. Establish `h0 : (v * u0 - 1) • ExteriorAlgebra.ιMulti X.functionField d (fun j => dK (x j : X.functionField)) = 0`. Rewrite using `[sub_smul, mul_smul, ← e0, ← ev, one_smul, sub_self]`. Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hW)`. Establish `hu0ne : u0 ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hvu`. Establish `hUu0 : UnitAt y u0`. Use `(unitAt_iff hu0ne).2 ⟨hu0, ?_⟩` and prove the remaining obligations. Rewrite using `[← eq_inv_of_mul_eq_one_left hvu]`.

Conclude with `hv`. Establish `hB` using `isFrame_baseFrame f d`. Establish `hr` using `formOf_eq_ratio_smul (gen_mem_baseOpen f d) hgU hB hω`. Use `set t := fnOf (baseOpen f d ⊓ L.bundle.U i) (by exact ⟨gen_mem_baseOpen f d, hgU⟩) (↑(hB.ratio hω) : Γ(X, baseOpen f d ⊓ L.bundle.U i)) with ht`. Establish `htne : t ≠ 0` using `((hB.ratio hω).isUnit.map _).ne_zero`.

Establish `hbf : baseForm f d = ((Units.mk0 t⁻¹ (inv_ne_zero htne) : X.functionFieldˣ) : X.functionField) • formOf (L.bundle.U i) hgU (L.om i)`. Rewrite using `[Units.val_mk0, hr, smul_smul, inv_mul_cancel₀ htne, one_smul]`. Both sides reduce to the same expression. Use `⟨Units.mk0 t⁻¹ (inv_ne_zero htne), u0, isDivOfForm_canonical f d _ (L.om i) hω y hi _ hbf, hUu0, ?_⟩` and prove the remaining obligations. Rewrite using `[hbf, map_smul, e0, smul_smul]`.
-/
theorem exists_baseForm_eq (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp (ZMod p))
    (d : ℕ) [SmoothOfRelativeDimension d f] (y : X) (x : Fin d → X.functionFieldˣ)
    (hx : AlgChart (locRing y) x) :
    ∃ (g : X.functionFieldˣ) (u : X.functionField), (canonical f d).IsEqn y g ∧ UnitAt y u ∧
      formsToLam (constFn f) (intCast_surj p) d (baseForm f d) =
        ((g : X.functionField) * u) • ExteriorAlgebra.ιMulti _ d fun j => dK (x j : X.functionField) := by
  classical
  set L := CanonLB.all f d with hL
  have hcov : y ∈ ⨆ i, L.bundle.U i := by
    rw [L.isLB.cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  have hω : IsFrame (L.om i) := L.isFrame i
  have hgU : genericPoint X ∈ L.bundle.U i := gen_mem hi
  obtain ⟨u0, hu0, e0⟩ := formOf_eq_regAt_smul p f d (L.om i) y hi x hx
  obtain ⟨v, hv, ev⟩ := coordForm_eq_regAt_smul p f d (L.om i) hω y hi x
    (fun j => mem_locRing.1 (hx.mem j))
  have hW : ExteriorAlgebra.ιMulti X.functionField d (fun j => dK (x j : X.functionField)) ≠ 0 :=
    ιMulti_coord_ne_zero x hx.coord
  have hvu : v * u0 = 1 := by
    have h0 : (v * u0 - 1) •
        ExteriorAlgebra.ιMulti X.functionField d (fun j => dK (x j : X.functionField)) = 0 := by
      rw [sub_smul, mul_smul, ← e0, ← ev, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hW)
  have hu0ne : u0 ≠ 0 := by
    rintro rfl
    simp at hvu
  have hUu0 : UnitAt y u0 := by
    refine (unitAt_iff hu0ne).2 ⟨hu0, ?_⟩
    rw [← eq_inv_of_mul_eq_one_left hvu]
    exact hv
  have hB := isFrame_baseFrame f d
  have hr := formOf_eq_ratio_smul (gen_mem_baseOpen f d) hgU hB hω
  set t := fnOf (baseOpen f d ⊓ L.bundle.U i) (by exact ⟨gen_mem_baseOpen f d, hgU⟩)
    (↑(hB.ratio hω) : Γ(X, baseOpen f d ⊓ L.bundle.U i)) with ht
  have htne : t ≠ 0 := ((hB.ratio hω).isUnit.map _).ne_zero
  have hbf : baseForm f d = ((Units.mk0 t⁻¹ (inv_ne_zero htne) : X.functionFieldˣ) : X.functionField) •
      formOf (L.bundle.U i) hgU (L.om i) := by
    rw [Units.val_mk0, hr, smul_smul, inv_mul_cancel₀ htne, one_smul]
    rfl
  refine ⟨Units.mk0 t⁻¹ (inv_ne_zero htne), u0,
    isDivOfForm_canonical f d _ (L.om i) hω y hi _ hbf, hUu0, ?_⟩
  rw [hbf, map_smul, e0, smul_smul]

/- English proof (translation)
Establish `hg` using `g.ne_zero`. Establish `hh` using `h.ne_zero`. Simplify using `only [dlog, dK, Units.val_mul, Units.val_inv_eq_inv_val, Derivation.leibniz, smul_add, smul_smul]`. Rewrite using `[show ((g : K) * h)⁻¹ * g = (h : K)⁻¹ by field_simp, show ((g : K) * h)⁻¹ * h = (g : K)⁻¹ by field_simp, add_comm]`.
-/
private theorem dlog_mul_lemma_3 {K : Type} [Field K] (g h : Kˣ) : dlog (g * h) = dlog g + dlog h := by
  have hg := g.ne_zero
  have hh := h.ne_zero
  simp only [dlog, dK, Units.val_mul, Units.val_inv_eq_inv_val, Derivation.leibniz, smul_add, smul_smul]
  rw [show ((g : K) * h)⁻¹ * g = (h : K)⁻¹ by field_simp,
    show ((g : K) * h)⁻¹ * h = (g : K)⁻¹ by field_simp, add_comm]

/- English proof (translation)
Set `φ : Kˣ →* Multiplicative Ω[K⁄ℤ]` to `{ toFun := fun g => Multiplicative.ofAdd (dlog g) map_one' := by simp [dlog, dK] map_mul' := fun g h => by rw [dlog_mul_lemma_3]; rfl }`. Establish `h` using `congrArg Multiplicative.toAdd (map_mul φ u (∏ j ∈ J, x j ^ m j))`. Rewrite `h` using `[map_prod]`. Simplify `h` using `only [map_zpow, toAdd_mul, toAdd_prod, toAdd_zpow, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, φ]`.
-/
private theorem dlog_prod_lemma_4 {K : Type} [Field K] {n : ℕ} (u : Kˣ) (x : Fin n → Kˣ) (J : Finset (Fin n))
    (m : Fin n → ℤ) : dlog (u * ∏ j ∈ J, x j ^ m j) = dlog u + ∑ j ∈ J, m j • dlog (x j) := by
  let φ : Kˣ →* Multiplicative Ω[K⁄ℤ] :=
    { toFun := fun g => Multiplicative.ofAdd (dlog g)
      map_one' := by simp [dlog, dK]
      map_mul' := fun g h => by rw [dlog_mul_lemma_3]; rfl }
  have h := congrArg Multiplicative.toAdd (map_mul φ u (∏ j ∈ J, x j ^ m j))
  rw [map_prod] at h
  simpa only [map_zpow, toAdd_mul, toAdd_prod, toAdd_zpow, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, φ] using h

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h1 : ZeroAt y f` using `zeroAt_iff.2 ⟨hf, h.1⟩`. Establish `hr1 : RegAt y (1 : X.functionField)` using `(unitAt_one y).regAt`. Establish `h2 : ZeroAt y (f + 1)` using `zeroAt_iff.2 ⟨hf.add hr1, h.2⟩`.

Establish `hm : RegAt y (-1 : X.functionField)` using `mem_locRing.1 (neg_mem (mem_locRing.2 hr1))`. Establish `h3` using `h2.add (h1.mul hm)`. Establish `h4 : f + 1 + f * -1 = (1 : X.functionField)` using `by ring`. Rewrite `h3` using `[h4]`. Conclude with `(zeroAt_iff.1 h3).2 (unitAt_one y)`.
-/
private theorem unit_or_succ_lemma_5 {X : Scheme} [IsIntegral X] {y : X} {f : X.functionField}
    (hf : RegAt y f) : UnitAt y f ∨ UnitAt y (f + 1) := by
  by_contra h
  push_neg at h
  have h1 : ZeroAt y f := zeroAt_iff.2 ⟨hf, h.1⟩
  have hr1 : RegAt y (1 : X.functionField) := (unitAt_one y).regAt
  have h2 : ZeroAt y (f + 1) := zeroAt_iff.2 ⟨hf.add hr1, h.2⟩
  have hm : RegAt y (-1 : X.functionField) := mem_locRing.1 (neg_mem (mem_locRing.2 hr1))
  have h3 := h2.add (h1.mul hm)
  have h4 : f + 1 + f * -1 = (1 : X.functionField) := by ring
  rw [h4] at h3
  exact (zeroAt_iff.1 h3).2 (unitAt_one y)

/- English proof (translation)
Establish `hxc` using `hch.coord`. Use `set b := Module.Basis.mk hxc.1 (le_of_eq hxc.2.symm) with hbdef`. Establish `hbi : ∀ i, b i = dK (x i : X.functionField)` using `fun i => Module.Basis.mk_apply _ _ _`. Use `set W := ExteriorAlgebra.ιMulti X.functionField n (fun j => dK (x j : X.functionField)) with hW`. Use `set e : X.functionField := ∏ j ∈ J, (x j : X.functionField) with he`.

Establish `hene : e ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => (x j).ne_zero`. Set `s : Fin n → X.functionField` to `fun i => if i ∈ J then (x i : X.functionField) else 1`. Establish `hs_prod : ∏ i, s i = e`. Simplify using `only [s]`. Rewrite using `[Finset.prod_ite_mem, Finset.univ_inter]`.

Establish `hsA : ∀ i, s i ∈ locRing y` using `fun i => by`. Simplify using `only [s]`. Use `split_ifs`. Conclude with `hch.mem i`. Conclude with `one_mem _`.

Establish `hrep : ∀ g ∈ locRing y, ∀ j, b.repr (dK g) j ∈ locRing y`. Introduce `g hg j`. Take `⟨c, hc, hd⟩` from `hch.deriv g hg`. Establish `hs : dK g = ∑ i, c i • b i`. Rewrite using `[hd]`.

Simplify using `only [hbi]`. Rewrite using `[hs, Module.Basis.repr_sum_self]`. Conclude with `hc j`. Establish `hcoord : ∀ g : X.functionFieldˣ, LogUnit Z y g → ∀ i, s i * b.repr (dlog g) i ∈ locRing y`. Introduce `g hg i`.

Take `⟨u, m, hu, rfl⟩` from `(hlog g).1 hg`. Rewrite using `[dlog_prod_lemma_4]`. Simplify using `only [map_add, map_sum, Finsupp.add_apply, Finsupp.finset_sum_apply, mul_add, Finset.mul_sum]`. Use `add_mem ?_ (sum_mem fun j hj => ?_)` and prove the remaining obligations. Rewrite using `[show dlog u = ((u⁻¹ : X.functionFieldˣ) : X.functionField) • dK (u : X.functionField) from rfl, map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Use `mul_mem (hsA i) (mul_mem ?_ (hrep _ (mem_locRing.2 hu.regAt) i))` and prove the remaining obligations. Rewrite using `[Units.val_inv_eq_inv_val]`. Conclude with `mem_locRing.2 hu.inv.regAt`. Rewrite using `[map_zsmul, Finsupp.smul_apply, mul_smul_comm]`. Use `zsmul_mem ?_ _` and prove the remaining obligations.

Establish `hdx : dlog (x j) = ((x j : X.functionField))⁻¹ • b j`. Rewrite using `[hbi]`. Simplify using `[dlog, Units.val_inv_eq_inv_val]`. Rewrite using `[hdx, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]`. Distinguish the cases in `hij : j = i`.

Substitute `hij` using the available equality. Simplify using `only [s, hj, if_true, mul_one]`. Rewrite using `[mul_inv_cancel₀ (x j).ne_zero]`. Conclude with `one_mem _`. Rewrite using `[if_neg hij, mul_zero, mul_zero]`.

Conclude with `zero_mem _`. Prove the components needed by the constructor for the conclusion. Introduce `hη`. Set `S : AddSubgroup (abelian₂ X.functionField)` to `{ carrier := {η | ∃ a : X.functionField, RegAt y (a * gG) ∧ η = (a * e⁻¹) • W} add_mem' := by`. Introduce and unpack `_ _ ⟨a1, h1, rfl⟩ ⟨a2, h2, rfl⟩`.

Conclude with `⟨a1 + a2, by rw [add_mul]; exact h1.add h2, by rw [add_mul, add_smul]⟩`. Use the proof step `zero_mem' := ⟨0, by rw [zero_mul]; exact regAt_zero y, by rw [zero_mul, zero_smul]⟩`. Use the proof step `neg_mem' := by`. Introduce and unpack `_ ⟨a, h, rfl⟩`. Conclude with `⟨-a, by rw [neg_mul]; exact mem_locRing.1 (neg_mem (mem_locRing.2 h)), by rw [neg_mul, neg_smul]⟩ }`.

Establish `hle : logAt Z G n y ≤ S`. Rewrite using `[logAt, spanForms, AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨c, hc, v, hv, rfl⟩`. Use `choose g hg hgv using hv`. Establish `hdet : b.det v * e ∈ locRing y`.

Rewrite using `[Module.Basis.det_apply, ← hs_prod, mul_comm, ← Matrix.det_mul_column]`. Use `det_mem_subring _ _ fun i k => ?_` and prove the remaining obligations. Rewrite using `[Matrix.of_apply, Module.Basis.toMatrix_apply, ← hgv k]`. Conclude with `hcoord (g k) (hg k) i`. Use `⟨(b.det v * e) * c, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_assoc]`. Conclude with `RegAt.mul (mem_locRing.1 hdet) ((hG.regularAt_iff).1 hc)`. Rewrite using `[ιMulti_eq_det_lemma_2 x hxc v, smul_smul]`. Use `congr 1`. Rewrite using `[mul_right_comm (b.det v) e c, mul_assoc _ e, mul_inv_cancel₀ hene, mul_one, mul_comm]`.

Conclude with `hle hη`. Introduce and unpack `⟨a, ha, rfl⟩`. Establish `hreg : ∀ i, RegAt y (x i : X.functionField)` using `fun i => mem_locRing.1 (hch.mem i)`. Establish `hq : ∀ i, ∃ q : X.functionFieldˣ, LogUnit Z y q ∧ dK (q : X.functionField) = dK (x i : X.functionField) ∧ (q : X.functionField) = s i * (if i ∈ J then 1 else (q : X.functionField)) ∧ RegAt y (if i ∈ J then 1 else (q : X.functionField))`. Introduce `i`.

Distinguish the cases in `hi : i ∈ J`. Use `⟨x i, (hlog _).2 ⟨1, Pi.single i 1, unitAt_one y, ?_⟩, rfl, by simp [s, hi], ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul, Finset.prod_eq_single i (fun j _ hji => by simp [Pi.single_apply, hji]) (fun h => absurd hi h)]`. Simplify using the standard rewrite rules. Simplify `(unitAt_one y).regAt` using `[hi]`.

Break down `unit_or_succ_lemma_5 (hreg i) with h | h` into its components or cases. Conclude with `⟨x i, (hlog _).2 ⟨x i, 0, h, by simp⟩, rfl, by simp [s, hi], by simpa [hi] using hreg i⟩`. Establish `hne : (x i : X.functionField) + 1 ≠ 0` using `h.ne_zero`. Use `⟨Units.mk0 _ hne, (hlog _).2 ⟨Units.mk0 _ hne, 0, by simpa using h, by simp⟩, ?_, by simp [s, hi], ?_⟩` and prove the remaining obligations. Simplify using `[dK]`.

Simplify `h.regAt` using `[hi]`. Use `choose q hqlog hqd hqs hqr using hq`. Set `v : Fin n → Ω[X.functionField⁄ℤ]` to `fun i => dlog (q i)`. Establish `hv : ExteriorAlgebra.ιMulti X.functionField n v = (∏ i, ((q i : X.functionField))⁻¹) • W`. Establish `hv' : v = fun i => ((q i : X.functionField))⁻¹ • dK (x i : X.functionField)`.

Use function extensionality and compare the values at `i`. Simplify using `only [v, dlog, Units.val_inv_eq_inv_val, hqd]`. Rewrite using `[hv', AlternatingMap.map_smul_univ]`. Set `r : Fin n → X.functionField` to `fun i => if i ∈ J then 1 else (q i : X.functionField)`. Establish `hqprod : ∏ i, (q i : X.functionField) = e * ∏ i, r i`.

Rewrite using `[← hs_prod, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun i _ => hqs i`. Establish `hqne : ∏ i, (q i : X.functionField) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => (q i).ne_zero`. Establish `hrne : ∏ i, r i ≠ 0`. Introduce `h0`.

Apply `hqne` to reduce the goal to its premises. Rewrite using `[hqprod, h0, mul_zero]`. Establish `hrA : RegAt y (∏ i, r i)` using `mem_locRing.1 (prod_mem fun i _ => mem_locRing.2 (hqr i))`. Establish `hcoef : G.RegularAt y (a * ∏ i, r i)`. Rewrite using `[hG.regularAt_iff, mul_right_comm]`.

Conclude with `RegAt.mul ha hrA`. Establish `hmem : (a * ∏ i, r i) • ExteriorAlgebra.ιMulti X.functionField n v ∈ logAt Z G n y`. Rewrite using `[logAt, spanForms]`. Conclude with `AddSubgroup.subset_closure ⟨a * ∏ i, r i, hcoef, v, fun i => ⟨q i, hqlog i, rfl⟩, rfl⟩`. Use `hmem using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[hv, smul_smul]`. Use `congr 1`. Rewrite using `[Finset.prod_inv_distrib, hqprod]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem logAt_top_lemma_6 {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (G : CartierDiv X) (y : X)
    {n : ℕ} (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (hch : AlgChart (locRing y) x)
    (hlog : ∀ g : X.functionFieldˣ, LogUnit Z y g ↔
      ∃ (u : X.functionFieldˣ) (m : Fin n → ℤ), UnitAt y ↑u ∧ g = u * ∏ j ∈ J, x j ^ m j)
    (gG : X.functionFieldˣ) (hG : G.IsEqn y gG) (η : abelian₂ X.functionField) :
    η ∈ logAt Z G n y ↔ ∃ a : X.functionField, RegAt y (a * gG) ∧
      η = (a * (∏ j ∈ J, (x j : X.functionField))⁻¹) •
        ExteriorAlgebra.ιMulti _ n (fun j => dK (x j : X.functionField)) := by
  classical
  have hxc := hch.coord
  set b := Module.Basis.mk hxc.1 (le_of_eq hxc.2.symm) with hbdef
  have hbi : ∀ i, b i = dK (x i : X.functionField) := fun i => Module.Basis.mk_apply _ _ _
  set W := ExteriorAlgebra.ιMulti X.functionField n (fun j => dK (x j : X.functionField)) with hW
  set e : X.functionField := ∏ j ∈ J, (x j : X.functionField) with he
  have hene : e ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (x j).ne_zero
  let s : Fin n → X.functionField := fun i => if i ∈ J then (x i : X.functionField) else 1
  have hs_prod : ∏ i, s i = e := by
    simp only [s]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  have hsA : ∀ i, s i ∈ locRing y := fun i => by
    simp only [s]
    split_ifs
    · exact hch.mem i
    · exact one_mem _
  have hrep : ∀ g ∈ locRing y, ∀ j, b.repr (dK g) j ∈ locRing y := by
    intro g hg j
    obtain ⟨c, hc, hd⟩ := hch.deriv g hg
    have hs : dK g = ∑ i, c i • b i := by
      rw [hd]
      simp only [hbi]
    rw [hs, Module.Basis.repr_sum_self]
    exact hc j
  have hcoord : ∀ g : X.functionFieldˣ, LogUnit Z y g → ∀ i, s i * b.repr (dlog g) i ∈ locRing y := by
    intro g hg i
    obtain ⟨u, m, hu, rfl⟩ := (hlog g).1 hg
    rw [dlog_prod_lemma_4]
    simp only [map_add, map_sum, Finsupp.add_apply, Finsupp.finset_sum_apply, mul_add, Finset.mul_sum]
    refine add_mem ?_ (sum_mem fun j hj => ?_)
    · rw [show dlog u = ((u⁻¹ : X.functionFieldˣ) : X.functionField) • dK (u : X.functionField) from rfl,
        map_smul, Finsupp.smul_apply, smul_eq_mul]
      refine mul_mem (hsA i) (mul_mem ?_ (hrep _ (mem_locRing.2 hu.regAt) i))
      rw [Units.val_inv_eq_inv_val]
      exact mem_locRing.2 hu.inv.regAt
    · rw [map_zsmul, Finsupp.smul_apply, mul_smul_comm]
      refine zsmul_mem ?_ _
      have hdx : dlog (x j) = ((x j : X.functionField))⁻¹ • b j := by
        rw [hbi]
        simp [dlog, Units.val_inv_eq_inv_val]
      rw [hdx, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases hij : j = i
      · subst hij
        simp only [s, hj, if_true, mul_one]
        rw [mul_inv_cancel₀ (x j).ne_zero]
        exact one_mem _
      · rw [if_neg hij, mul_zero, mul_zero]
        exact zero_mem _
  constructor
  · intro hη
    let S : AddSubgroup (abelian₂ X.functionField) :=
      { carrier := {η | ∃ a : X.functionField, RegAt y (a * gG) ∧ η = (a * e⁻¹) • W}
        add_mem' := by
          rintro _ _ ⟨a1, h1, rfl⟩ ⟨a2, h2, rfl⟩
          exact ⟨a1 + a2, by rw [add_mul]; exact h1.add h2, by rw [add_mul, add_smul]⟩
        zero_mem' := ⟨0, by rw [zero_mul]; exact regAt_zero y, by rw [zero_mul, zero_smul]⟩
        neg_mem' := by
          rintro _ ⟨a, h, rfl⟩
          exact ⟨-a, by rw [neg_mul]; exact mem_locRing.1 (neg_mem (mem_locRing.2 h)),
            by rw [neg_mul, neg_smul]⟩ }
    have hle : logAt Z G n y ≤ S := by
      rw [logAt, spanForms, AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      choose g hg hgv using hv
      have hdet : b.det v * e ∈ locRing y := by
        rw [Module.Basis.det_apply, ← hs_prod, mul_comm, ← Matrix.det_mul_column]
        refine det_mem_subring _ _ fun i k => ?_
        rw [Matrix.of_apply, Module.Basis.toMatrix_apply, ← hgv k]
        exact hcoord (g k) (hg k) i
      refine ⟨(b.det v * e) * c, ?_, ?_⟩
      · rw [mul_assoc]
        exact RegAt.mul (mem_locRing.1 hdet) ((hG.regularAt_iff).1 hc)
      · rw [ιMulti_eq_det_lemma_2 x hxc v, smul_smul]
        congr 1
        rw [mul_right_comm (b.det v) e c, mul_assoc _ e, mul_inv_cancel₀ hene, mul_one, mul_comm]
    exact hle hη
  · rintro ⟨a, ha, rfl⟩
    have hreg : ∀ i, RegAt y (x i : X.functionField) := fun i => mem_locRing.1 (hch.mem i)
    have hq : ∀ i, ∃ q : X.functionFieldˣ, LogUnit Z y q ∧
        dK (q : X.functionField) = dK (x i : X.functionField) ∧
        (q : X.functionField) = s i * (if i ∈ J then 1 else (q : X.functionField)) ∧
        RegAt y (if i ∈ J then 1 else (q : X.functionField)) := by
      intro i
      by_cases hi : i ∈ J
      · refine ⟨x i, (hlog _).2 ⟨1, Pi.single i 1, unitAt_one y, ?_⟩, rfl, by simp [s, hi], ?_⟩
        · rw [one_mul, Finset.prod_eq_single i (fun j _ hji => by simp [Pi.single_apply, hji])
            (fun h => absurd hi h)]
          simp
        · simpa [hi] using (unitAt_one y).regAt
      · rcases unit_or_succ_lemma_5 (hreg i) with h | h
        · exact ⟨x i, (hlog _).2 ⟨x i, 0, h, by simp⟩, rfl, by simp [s, hi], by simpa [hi] using hreg i⟩
        · have hne : (x i : X.functionField) + 1 ≠ 0 := h.ne_zero
          refine ⟨Units.mk0 _ hne, (hlog _).2 ⟨Units.mk0 _ hne, 0, by simpa using h, by simp⟩, ?_,
            by simp [s, hi], ?_⟩
          · simp [dK]
          · simpa [hi] using h.regAt
    choose q hqlog hqd hqs hqr using hq
    let v : Fin n → Ω[X.functionField⁄ℤ] := fun i => dlog (q i)
    have hv : ExteriorAlgebra.ιMulti X.functionField n v = (∏ i, ((q i : X.functionField))⁻¹) • W := by
      have hv' : v = fun i => ((q i : X.functionField))⁻¹ • dK (x i : X.functionField) := by
        funext i
        simp only [v, dlog, Units.val_inv_eq_inv_val, hqd]
      rw [hv', AlternatingMap.map_smul_univ]
    let r : Fin n → X.functionField := fun i => if i ∈ J then 1 else (q i : X.functionField)
    have hqprod : ∏ i, (q i : X.functionField) = e * ∏ i, r i := by
      rw [← hs_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => hqs i
    have hqne : ∏ i, (q i : X.functionField) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (q i).ne_zero
    have hrne : ∏ i, r i ≠ 0 := by
      intro h0
      apply hqne
      rw [hqprod, h0, mul_zero]
    have hrA : RegAt y (∏ i, r i) := mem_locRing.1 (prod_mem fun i _ => mem_locRing.2 (hqr i))
    have hcoef : G.RegularAt y (a * ∏ i, r i) := by
      rw [hG.regularAt_iff, mul_right_comm]
      exact RegAt.mul ha hrA
    have hmem : (a * ∏ i, r i) • ExteriorAlgebra.ιMulti X.functionField n v ∈ logAt Z G n y := by
      rw [logAt, spanForms]
      exact AddSubgroup.subset_closure ⟨a * ∏ i, r i, hcoef, v, fun i => ⟨q i, hqlog i, rfl⟩, rfl⟩
    convert hmem using 1
    rw [hv, smul_smul]
    congr 1
    rw [Finset.prod_inv_distrib, hqprod]
    field_simp

/- English proof (translation)
Introduce `p _ X _ f d _ C _ E ι 𝒜`. Use `⟨formsToLam (constFn f) (intCast_surj p) d (baseForm f d), ?_, ?_⟩` and prove the remaining obligations. Establish `hg0 : genericPoint X ∈ ⨆ i, 𝒜.U i`. Rewrite using `[𝒜.cover]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hg0`. Take `⟨g, u, -, hu, e⟩` from `exists_baseForm_eq p X f d _ (𝒜.x i) ((𝒜.chart i).chart _ hi)`. Rewrite using `[e]`. Conclude with `smul_ne_zero (mul_ne_zero g.ne_zero hu.ne_zero) (ιMulti_coord_ne_zero _ ((𝒜.chart i).chart _ hi).coord)`. Introduce `G y η`.

Establish `hy0 : y ∈ ⨆ i, 𝒜.U i`. Rewrite using `[𝒜.cover]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hy0`. Establish `hch` using `(𝒜.chart i).chart y hi`.

Take `⟨gK, u, hgK, hu, hω⟩` from `exists_baseForm_eq p X f d y (𝒜.x i) hch`. Establish `hE` using `isEqn_sum_of_isSncOn E (𝒜.U i) (𝒜.x i) (𝒜.J i) (𝒜.snc i) y hi`. Take `⟨gG, hG⟩` from `CartierDiv.exists_isEqn G y`. Establish `hT` using `(hgK.add hE).add hG`. Rewrite using `[logAt_top_lemma_6 (suppAll E) G y (𝒜.x i) (𝒜.J i) hch ((𝒜.chart i).logUnit y hi) gG hG η, hω]`.

Establish `hune : (u : X.functionField) ≠ 0` using `hu.ne_zero`. Establish `hgne : (gK : X.functionField) ≠ 0` using `gK.ne_zero`. Establish `hene : (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun j _ => (𝒜.x i j).ne_zero`. Simplify using `only [hT.regularAt_iff, Units.val_mul, Units.coe_prod]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, rfl⟩`. Use `⟨a * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField)))⁻¹ * ((gK : X.functionField) * u)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Establish `hh : a * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField)))⁻¹ * ((gK : X.functionField) * u)⁻¹ * ((gK : X.functionField) * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) * gG) = (a * gG) * (u : X.functionField)⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hh]`.

Conclude with `ha.mul hu.inv.regAt`. Rewrite using `[smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨c, hc, rfl⟩`.

Use `⟨c * gK * u * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))), ?_, ?_⟩` and prove the remaining obligations. Establish `hh : c * gK * u * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) * gG = (c * ((gK : X.functionField) * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) * gG)) * u`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hh]`. Conclude with `hc.mul hu.regAt`.

Rewrite using `[smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem logAt_top_eq_canonical : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp (ZMod p)) (d : ℕ) [SmoothOfRelativeDimension d f] {C : Type} [Fintype C] (E : C → CartierDiv X) {ι : Type} (𝒜 : SncAtlas E d ι), ∃ ω₀ : abelian₂ X.functionField, ω₀ ≠ 0 ∧ ∀ (G : CartierDiv X) (y : X) (η : abelian₂ X.functionField), η ∈ logAt (suppAll E) G d y ↔ ∃ c : X.functionField, (canonical f d + ∑ c, E c + G).RegularAt y c ∧ η = c • ω₀ := by
  intro p _ X _ f d _ C _ E ι 𝒜
  classical
  refine ⟨formsToLam (constFn f) (intCast_surj p) d (baseForm f d), ?_, ?_⟩
  · have hg0 : genericPoint X ∈ ⨆ i, 𝒜.U i := by
      rw [𝒜.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hg0
    obtain ⟨g, u, -, hu, e⟩ := exists_baseForm_eq p X f d _ (𝒜.x i) ((𝒜.chart i).chart _ hi)
    rw [e]
    exact smul_ne_zero (mul_ne_zero g.ne_zero hu.ne_zero)
      (ιMulti_coord_ne_zero _ ((𝒜.chart i).chart _ hi).coord)
  · intro G y η
    have hy0 : y ∈ ⨆ i, 𝒜.U i := by
      rw [𝒜.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy0
    have hch := (𝒜.chart i).chart y hi
    obtain ⟨gK, u, hgK, hu, hω⟩ := exists_baseForm_eq p X f d y (𝒜.x i) hch
    have hE := isEqn_sum_of_isSncOn E (𝒜.U i) (𝒜.x i) (𝒜.J i) (𝒜.snc i) y hi
    obtain ⟨gG, hG⟩ := CartierDiv.exists_isEqn G y
    have hT := (hgK.add hE).add hG
    rw [logAt_top_lemma_6 (suppAll E) G y (𝒜.x i) (𝒜.J i) hch ((𝒜.chart i).logUnit y hi) gG hG η, hω]
    have hune : (u : X.functionField) ≠ 0 := hu.ne_zero
    have hgne : (gK : X.functionField) ≠ 0 := gK.ne_zero
    have hene : (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => (𝒜.x i j).ne_zero
    simp only [hT.regularAt_iff, Units.val_mul, Units.coe_prod]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField)))⁻¹ * ((gK : X.functionField) * u)⁻¹, ?_, ?_⟩
      · have hh : a * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField)))⁻¹ * ((gK : X.functionField) * u)⁻¹ *
            ((gK : X.functionField) * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) * gG) =
            (a * gG) * (u : X.functionField)⁻¹ := by
          field_simp
        rw [hh]
        exact ha.mul hu.inv.regAt
      · rw [smul_smul]
        congr 1
        field_simp
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c * gK * u * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))), ?_, ?_⟩
      · have hh : c * gK * u * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) * gG =
            (c * ((gK : X.functionField) * (∏ j ∈ 𝒜.J i, ((𝒜.x i j : X.functionField))) * gG)) * u := by
          ring
        rw [hh]
        exact hc.mul hu.regAt
      · rw [smul_smul]
        congr 1
        field_simp

end GlobalTheory.LogDR

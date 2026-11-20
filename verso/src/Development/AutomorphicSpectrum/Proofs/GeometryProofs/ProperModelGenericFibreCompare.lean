import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineLatticeGenericSectionsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgClosedTensorIsDomainStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.Ar.Flat.Descend

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

noncomputable def val (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hU : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (ξ.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hU).ge ≫
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom

/- English proof (translation)
Establish `e : X.presheaf.germ U (ξ (IsLocalRing.closedPoint (CommRingCat.of Ω))) hU ≫ Scheme.stalkClosedPointTo ξ = ξ.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hU).ge ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom`. Rewrite using `[Scheme.germ_stalkClosedPointTo]`. Simplify using `[Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]`. Conclude with `congrArg (fun φ => φ.hom g) e`.
-/
theorem germ_closedPoint (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hU : genPt ξ ∈ U) (g : Γ(X, U)) :
    (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hU g) = val ξ U hU g := by
  have e : X.presheaf.germ U (ξ (IsLocalRing.closedPoint (CommRingCat.of Ω))) hU ≫ Scheme.stalkClosedPointTo ξ =
      ξ.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hU).ge ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  exact congrArg (fun φ => φ.hom g) e

/- English proof (translation)
The claim follows from `(congrArg (Scheme.stalkClosedPointTo ξ).hom (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hp p.2 g)).trans (germ_closedPoint ξ U _ g)`.
-/
theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (p : Cpt ξ) (hp : p.1 ∈ U) (g : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp g) = val ξ U (p.2.mem_open U.isOpen hp) g :=
  (congrArg (Scheme.stalkClosedPointTo ξ).hom
    (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hp p.2 g)).trans (germ_closedPoint ξ U _ g)

/- English proof (translation)
Establish `e' : (Spec.map φ).appLE ⊤ ⊤ e = (Spec.map φ).appTop`. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Use `congr 1`. Rewrite using `[e']`. Conclude with `Scheme.ΓSpecIso_naturality _`.
-/
theorem appLE_top_spec {R S : CommRingCat.{0}} (φ : R ⟶ S) (e) :
    (Spec.map φ).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso S).hom = (Scheme.ΓSpecIso R).hom ≫ φ := by
  have e' : (Spec.map φ).appLE ⊤ ⊤ e = (Spec.map φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  rw [e']
  exact Scheme.ΓSpecIso_naturality _

/- English proof (translation)
Establish `key : ∀ (g : Spec (CommRingCat.of Ω') ⟶ X) (_ : g = Spec.map (CommRingCat.ofHom i) ≫ ξ) (e), g.appLE W ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom = ξ.appLE W ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hne).ge ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom …`. Introduce `g hg e`. Substitute `hg` using the available equality. Rewrite using `[← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom i)) ξ W ⊤ ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hne).ge le_top, Category.assoc, appLE_top_spec]`. Establish `e2 : f.appLE W W' hle ≫ ξ'.appLE W' ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ' hne').ge ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom = ξ.appLE W ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hne).ge ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom i`.

Rewrite using `[← Category.assoc, Scheme.Hom.appLE_comp_appLE]`. Conclude with `key _ hD _`. Conclude with `congrArg (fun φ => φ.hom b) e2`.
-/
theorem val_pull {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} (hD : Dominates ξ' ξ f i)
    (W : X.Opens) (W' : X'.Opens) (hle : W' ≤ f ⁻¹ᵁ W) (hne : genPt ξ ∈ W) (hne' : genPt ξ' ∈ W') (b : Γ(X, W)) :
    val ξ' W' hne' ((f.appLE W W' hle).hom b) = i (val ξ W hne b) := by
  have key : ∀ (g : Spec (CommRingCat.of Ω') ⟶ X) (_ : g = Spec.map (CommRingCat.ofHom i) ≫ ξ) (e),
      g.appLE W ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom =
        ξ.appLE W ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hne).ge ≫
          (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom i := by
    intro g hg e
    subst hg
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom i)) ξ W ⊤ ⊤
      (Scheme.preimage_eq_top_of_closedPoint_mem ξ hne).ge le_top, Category.assoc, appLE_top_spec]
  have e2 : f.appLE W W' hle ≫ ξ'.appLE W' ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ' hne').ge ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom =
        ξ.appLE W ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hne).ge ≫
          (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom i := by
    rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE]
    exact key _ hD _
  exact congrArg (fun φ => φ.hom b) e2

/- English proof (translation)
Establish `key : ∀ (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) (_ : g = Spec.map (CommRingCat.ofHom (algebraMap R Ω))) (e), g.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (algebraMap R Ω)`. Introduce `g hg e`. Substitute `hg` using the available equality. Conclude with `appLE_top_spec _ _`. Establish `e2 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appLE ⊤ U (by simp) ≫ ξ.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hU).ge ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap R Ω)`.

Establish `e3` using `Scheme.Hom.appLE_comp_appLE ξ s ⊤ U ⊤ (by simp) (Scheme.preimage_eq_top_of_closedPoint_mem ξ hU).ge`. Rewrite using `[reassoc_of% e3, key _ h, Iso.inv_hom_id_assoc]`. Conclude with `congrArg (fun φ => φ.hom r) e2`.
-/
theorem val_algX {R : Type} [CommRing R] [Algebra R Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {s : X ⟶ Spec (CommRingCat.of R)} (h : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
    (U : X.Opens) (hU : genPt ξ ∈ U) (r : R) : val ξ U hU (algX s U r) = algebraMap R Ω r := by
  have key : ∀ (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R))
      (_ : g = Spec.map (CommRingCat.ofHom (algebraMap R Ω))) (e),
      g.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom =
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (algebraMap R Ω) := by
    intro g hg e
    subst hg
    exact appLE_top_spec _ _
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appLE ⊤ U (by simp) ≫
      ξ.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hU).ge ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap R Ω) := by
    have e3 := Scheme.Hom.appLE_comp_appLE ξ s ⊤ U ⊤ (by simp)
      (Scheme.preimage_eq_top_of_closedPoint_mem ξ hU).ge
    rw [reassoc_of% e3, key _ h, Iso.inv_hom_id_assoc]
  exact congrArg (fun φ => φ.hom r) e2

end Val

/- English proof (translation)
Introduce `o ho`. Set `p : Cpt ξ` to `⟨f q', h⟩`. Set `r : Γ(Spec (CommRingCat.of O), ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o`. Set `g : Γ(X, s ⁻¹ᵁ ⊤)` to `(s.app ⊤).hom r`. Establish `hgX : g = algX s (s ⁻¹ᵁ ⊤) o`.

Simplify using `only [g, r, algX, RingHom.comp_apply, Scheme.Hom.app_eq_appLE]`. Establish `hpt : (s (f q')) ∈ (Spec (CommRingCat.of O)).basicOpen r`. Establish `e1 : s (f q') = Spec.map (CommRingCat.ofHom (algebraMap O C)) (s' q')`. Use `congrArg (fun m : X' ⟶ Spec (CommRingCat.of O) => m q') hw` as an intermediate fact. Simplify using `using this`.

Rewrite using `[e1]`. Establish `e2 : (Spec (CommRingCat.of O)).basicOpen r = PrimeSpectrum.basicOpen (R` using `O) o := basicOpen_eq_of_affine (R := CommRingCat.of O) o`. Rewrite using `[e2]`. Use `show o ∉ (PrimeSpectrum.comap (algebraMap O C) (s' q')).asIdeal`. Introduce `hm`.

Establish `hm' : algebraMap O C o ∈ (show PrimeSpectrum C from s' q').asIdeal` using `hm`. Rewrite `hm'` using `[Ideal.eq_bot_of_prime (show PrimeSpectrum C from s' q').asIdeal]`. Conclude with `ho (hC (by simpa using hm'))`. Establish `hpb : f q' ∈ X.basicOpen g`. Use `Scheme.preimage_basicOpen s r` as an intermediate fact.

Rewrite using `[← this]`. Conclude with `hpt`. Establish `hmem : f q' ∈ s ⁻¹ᵁ ⊤` using `trivial`. Establish `hu : IsUnit (X.presheaf.germ (s ⁻¹ᵁ ⊤) (f q') hmem g)` using `(X.mem_basicOpen g (f q') hmem).1 hpb`. Establish `hv : genMap ξ p (X.presheaf.germ (s ⁻¹ᵁ ⊤) (f q') hmem g) = algebraMap O Ω o` using `(genMap_germ ξ _ p hmem g).trans (by rw [hgX, val_algX h1])`.

Take `⟨w, hw'⟩` from `hu.exists_right_inv`. Establish `h0 : algebraMap O Ω o ≠ 0`. Rewrite using `[← hv]`. Conclude with `(hu.map (genMap ξ p)).ne_zero`. Use `⟨h0, ⟨_, hv⟩, ⟨w, ?_⟩⟩` and prove the remaining obligations.

Use `congrArg (genMap ξ p) hw'` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, hv]`. Conclude with `eq_inv_of_mul_eq_one_right this`.
-/
theorem genFibre_of_field_point (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (h1 : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)))
    (X' : Scheme.{0}) (C : Type) [Field C] [Algebra O C] (s' : X' ⟶ Spec (CommRingCat.of C)) (f : X' ⟶ X)
    (hC : Function.Injective (algebraMap O C))
    (hw : f ≫ s = s' ≫ Spec.map (CommRingCat.ofHom (algebraMap O C)))
    (q' : X') (h : genPt ξ ⤳ f q') : (⟨f q', h⟩ : Cpt ξ) ∈ genFibre O ξ := by
  intro o ho
  let p : Cpt ξ := ⟨f q', h⟩
  let r : Γ(Spec (CommRingCat.of O), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o
  let g : Γ(X, s ⁻¹ᵁ ⊤) := (s.app ⊤).hom r
  have hgX : g = algX s (s ⁻¹ᵁ ⊤) o := by
    simp only [g, r, algX, RingHom.comp_apply, Scheme.Hom.app_eq_appLE]
  have hpt : (s (f q')) ∈ (Spec (CommRingCat.of O)).basicOpen r := by
    have e1 : s (f q') = Spec.map (CommRingCat.ofHom (algebraMap O C)) (s' q') := by
      have := congrArg (fun m : X' ⟶ Spec (CommRingCat.of O) => m q') hw
      simpa using this
    rw [e1]
    have e2 : (Spec (CommRingCat.of O)).basicOpen r = PrimeSpectrum.basicOpen (R := O) o :=
      basicOpen_eq_of_affine (R := CommRingCat.of O) o
    rw [e2]
    show o ∉ (PrimeSpectrum.comap (algebraMap O C) (s' q')).asIdeal
    intro hm
    have hm' : algebraMap O C o ∈ (show PrimeSpectrum C from s' q').asIdeal := hm
    rw [Ideal.eq_bot_of_prime (show PrimeSpectrum C from s' q').asIdeal] at hm'
    exact ho (hC (by simpa using hm'))
  have hpb : f q' ∈ X.basicOpen g := by
    have := Scheme.preimage_basicOpen s r
    rw [← this]
    exact hpt
  have hmem : f q' ∈ s ⁻¹ᵁ ⊤ := trivial
  have hu : IsUnit (X.presheaf.germ (s ⁻¹ᵁ ⊤) (f q') hmem g) := (X.mem_basicOpen g (f q') hmem).1 hpb
  have hv : genMap ξ p (X.presheaf.germ (s ⁻¹ᵁ ⊤) (f q') hmem g) = algebraMap O Ω o :=
    (genMap_germ ξ _ p hmem g).trans (by rw [hgX, val_algX h1])
  obtain ⟨w, hw'⟩ := hu.exists_right_inv
  have h0 : algebraMap O Ω o ≠ 0 := by
    rw [← hv]
    exact (hu.map (genMap ξ p)).ne_zero
  refine ⟨h0, ⟨_, hv⟩, ⟨w, ?_⟩⟩
  have := congrArg (genMap ξ p) hw'
  rw [map_mul, map_one, hv] at this
  exact eq_inv_of_mul_eq_one_right this

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace K C`. Set `B` to `Algebra.TensorProduct.basis Ω b`. Establish `hcoord : ∀ p z, z ∈ AddSubmonoid.closure {z : Ω ⊗[K] C | ∃ a ∈ S p, ∃ c : C, z = a ⊗ₜ[K] c} → ∀ j, B.repr z j ∈ S p`. Introduce `p z hz j`. Proceed by induction on `hz using AddSubmonoid.closure_induction with`.

Consider the case `mem z hz`. Take `⟨a, ha, c, rfl⟩` from `hz`. Rewrite using `[Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]`. Conclude with `mul_mem ha (hK p _)`.

Consider the case `zero => simp [zero_mem]`. Consider the case `add u v _ _ hu hv`. Rewrite using `[map_add, Finsupp.add_apply]`. Conclude with `add_mem hu hv`. Establish `hτ0 : τ ≠ 0` using `fun h => one_ne_zero (by rw [← hτυ, h, zero_mul] : (1 : Ω ⊗[K] C) = 0)`.

Establish `hυ0 : υ ≠ 0` using `fun h => one_ne_zero (by rw [← hτυ, h, mul_zero] : (1 : Ω ⊗[K] C) = 0)`. Establish `hne : ∀ z : Ω ⊗[K] C, z ≠ 0 → ∃ j, B.repr z j ≠ 0`. Introduce `z hz`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hz (B.repr.map_eq_zero_iff.1 (Finsupp.ext h))`. Take `⟨j, hj⟩` from `hne τ hτ0`. Take `⟨k, hk⟩` from `hne υ hυ0`. Establish `ht : ∀ l p, B.repr τ l / e p ∈ S p`. Introduce `l p`.

Establish `: B.repr τ l / e p = B.repr (x p) l`. Rewrite using `[hτ p, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ (he p)]`. Rewrite using `[this]`. Conclude with `hcoord p _ (hx p) l`. Establish `hu : ∀ l p, e p * B.repr υ l ∈ S p`.

Introduce `l p`. Establish `: e p * B.repr υ l = B.repr (y p) l`. Rewrite using `[← hυ p, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Rewrite using `[this]`. Conclude with `hcoord p _ (hy p) l`.

Use `set t := B.repr τ j with ht_def`. Use `set u := B.repr υ k with hu_def`. Establish `hm : ∀ p, t * u ∈ S p`. Introduce `p`. Establish `h` using `mul_mem (ht j p) (hu k p)`.

Establish `e1 : B.repr τ j / e p * (e p * B.repr υ k) = t * u`. Rewrite using `[← ht_def, ← hu_def]`. Clear denominators, using `[he p]` for the nonvanishing conditions. Rewrite `h` using `[e1]`. Then use the resulting hypothesis. Take `⟨κ, hκ⟩` from `H1 (t * u) (mul_ne_zero hj hk) hm`.

Establish `hκ0 : algebraMap K Ω κ ≠ 0`. Rewrite using `[← hκ]`. Conclude with `mul_ne_zero hj hk`. Establish `hr : ∀ p, t / e p ∈ S p ∧ e p / t ∈ S p`. Introduce `p`.

Use `⟨ht j p, ?_⟩` and prove the remaining obligations. Establish `e1 : e p / t = (e p * u) * algebraMap K Ω κ⁻¹`. Rewrite using `[map_inv₀, ← hκ]`. Clear denominators, using `[he p, hj, hk]` for the nonvanishing conditions. Rewrite using `[e1]`.

Conclude with `mul_mem (hu k p) (hK p _)`. Establish `hl : ∀ l, ∃ c : K, B.repr τ l = algebraMap K Ω c * t` using `fun l => H2 t hj hr _ fun p => ht l p`. Use `choose c hc using hl`. Use `⟨t, ∑ l ∈ (B.repr τ).support, c l • b l, hj, hr, ?_⟩` and prove the remaining obligations. Establish `hsum : τ = ∑ l ∈ (B.repr τ).support, B.repr τ l • B l` using `by conv_lhs => rw [← B.linearCombination_repr τ]`.

Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum]`. Rewrite using `[TensorProduct.tmul_sum]`. Use `hsum.trans (Finset.sum_congr rfl fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[hc l, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]`.
-/
theorem descent_core {K Ω C : Type} [Field K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C]
    [Nontrivial (Ω ⊗[K] C)] {ι : Type} (S : ι → Subring Ω) (hK : ∀ p k, algebraMap K Ω k ∈ S p)
    (e : ι → Ω) (he : ∀ p, e p ≠ 0) (τ υ : Ω ⊗[K] C) (hτυ : τ * υ = 1) (x y : ι → Ω ⊗[K] C)
    (hx : ∀ p, x p ∈ AddSubmonoid.closure {z : Ω ⊗[K] C | ∃ a ∈ S p, ∃ c : C, z = a ⊗ₜ[K] c})
    (hy : ∀ p, y p ∈ AddSubmonoid.closure {z : Ω ⊗[K] C | ∃ a ∈ S p, ∃ c : C, z = a ⊗ₜ[K] c})
    (hτ : ∀ p, τ = e p • x p) (hυ : ∀ p, e p • υ = y p)
    (H1 : ∀ a : Ω, a ≠ 0 → (∀ p, a ∈ S p) → ∃ k : K, a = algebraMap K Ω k)
    (H2 : ∀ t : Ω, t ≠ 0 → (∀ p, t / e p ∈ S p ∧ e p / t ∈ S p) → ∀ u : Ω, (∀ p, u / e p ∈ S p) →
      ∃ k : K, u = algebraMap K Ω k * t) :
    ∃ (t : Ω) (c : C), t ≠ 0 ∧ (∀ p, t / e p ∈ S p ∧ e p / t ∈ S p) ∧ τ = t ⊗ₜ[K] c := by
  classical
  let b := Module.Basis.ofVectorSpace K C
  let B := Algebra.TensorProduct.basis Ω b
  have hcoord : ∀ p z, z ∈ AddSubmonoid.closure {z : Ω ⊗[K] C | ∃ a ∈ S p, ∃ c : C, z = a ⊗ₜ[K] c} →
      ∀ j, B.repr z j ∈ S p := by
    intro p z hz j
    induction hz using AddSubmonoid.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, c, rfl⟩ := hz
      rw [Algebra.TensorProduct.basis_repr_tmul]
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      exact mul_mem ha (hK p _)
    | zero => simp [zero_mem]
    | add u v _ _ hu hv =>
      rw [map_add, Finsupp.add_apply]
      exact add_mem hu hv
  have hτ0 : τ ≠ 0 := fun h => one_ne_zero (by rw [← hτυ, h, zero_mul] : (1 : Ω ⊗[K] C) = 0)
  have hυ0 : υ ≠ 0 := fun h => one_ne_zero (by rw [← hτυ, h, mul_zero] : (1 : Ω ⊗[K] C) = 0)
  have hne : ∀ z : Ω ⊗[K] C, z ≠ 0 → ∃ j, B.repr z j ≠ 0 := by
    intro z hz
    by_contra h
    push_neg at h
    exact hz (B.repr.map_eq_zero_iff.1 (Finsupp.ext h))
  obtain ⟨j, hj⟩ := hne τ hτ0
  obtain ⟨k, hk⟩ := hne υ hυ0
  have ht : ∀ l p, B.repr τ l / e p ∈ S p := by
    intro l p
    have : B.repr τ l / e p = B.repr (x p) l := by
      rw [hτ p, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ (he p)]
    rw [this]
    exact hcoord p _ (hx p) l
  have hu : ∀ l p, e p * B.repr υ l ∈ S p := by
    intro l p
    have : e p * B.repr υ l = B.repr (y p) l := by
      rw [← hυ p, map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [this]
    exact hcoord p _ (hy p) l
  set t := B.repr τ j with ht_def
  set u := B.repr υ k with hu_def
  have hm : ∀ p, t * u ∈ S p := by
    intro p
    have h := mul_mem (ht j p) (hu k p)
    have e1 : B.repr τ j / e p * (e p * B.repr υ k) = t * u := by
      rw [← ht_def, ← hu_def]
      field_simp [he p]
    rwa [e1] at h
  obtain ⟨κ, hκ⟩ := H1 (t * u) (mul_ne_zero hj hk) hm
  have hκ0 : algebraMap K Ω κ ≠ 0 := by
    rw [← hκ]
    exact mul_ne_zero hj hk
  have hr : ∀ p, t / e p ∈ S p ∧ e p / t ∈ S p := by
    intro p
    refine ⟨ht j p, ?_⟩
    have e1 : e p / t = (e p * u) * algebraMap K Ω κ⁻¹ := by
      rw [map_inv₀, ← hκ]
      field_simp [he p, hj, hk]
    rw [e1]
    exact mul_mem (hu k p) (hK p _)
  have hl : ∀ l, ∃ c : K, B.repr τ l = algebraMap K Ω c * t := fun l => H2 t hj hr _ fun p => ht l p
  choose c hc using hl
  refine ⟨t, ∑ l ∈ (B.repr τ).support, c l • b l, hj, hr, ?_⟩
  have hsum : τ = ∑ l ∈ (B.repr τ).support, B.repr τ l • B l := by
    conv_lhs => rw [← B.linearCombination_repr τ]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [TensorProduct.tmul_sum]
  refine hsum.trans (Finset.sum_congr rfl fun l _ => ?_)
  rw [hc l, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]

/- English proof (translation)
Use `haveI : Module.Flat O K := IsLocalization.flat K (nonZeroDivisors O)`. Use `haveI : Module.Flat O C := Module.Flat.trans O K C`. Establish `hcs` using `IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors O) K Ω C`. Set `e` to `TensorProduct.equivOfCompatibleSMul O K Ω Ω C`. Use `letI : Algebra O (Ω ⊗[K] C) := ((algebraMap K (Ω ⊗[K] C)).comp (algebraMap O K)).toAlgebra`.

Set `g1 : B →ₐ[O] Ω ⊗[K] C` to `{ toRingHom := (Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[K] C).comp ev.toRingHom commutes' := fun o => by show (ev (algebraMap O B o)) ⊗ₜ[K] (1 : C) = algebraMap K (Ω ⊗[K] C) (algebraMap O K o)`. Rewrite using `[ev.commutes, Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply] }`. Set `g2 : C →ₐ[O] Ω ⊗[K] C` to `{ toRingHom := (Algebra.TensorProduct.includeRight : C →ₐ[K] Ω ⊗[K] C).toRingHom commutes' := fun o => by show (Algebra.TensorProduct.includeRight : C →ₐ[K] Ω ⊗[K] C) (algebraMap O C o) = algebraMap K (Ω ⊗[K] C) (algebraMap O K o)`. Rewrite using `[IsScalarTower.algebraMap_apply O K C, AlgHom.commutes] }`. Set `ι : B ⊗[O] C →+* Ω ⊗[K] C` to `(Algebra.TensorProduct.productMap g1 g2).toRingHom`.

Establish `hι : ∀ b c, ι (b ⊗ₜ[O] c) = ev b ⊗ₜ[K] c`. Introduce `b c`. Use `show g1 b * g2 c = _`. Use `show (ev b ⊗ₜ[K] (1 : C)) * ((1 : Ω) ⊗ₜ[K] c) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.

Use `⟨ι, ?_, hι⟩` and prove the remaining obligations. Establish `hE : ∀ z, e (ι z) = (ev.toLinearMap.rTensor C) z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul b c => rw [hι]`. Both sides reduce to the same expression. Consider the case `add u v hu hv => rw [map_add, map_add, hu, hv, map_add]`. Introduce `a b hab`. Establish `h` using `congrArg e hab`.

Rewrite `h` using `[hE, hE]`. Conclude with `Module.Flat.rTensor_preserves_injective_linearMap _ hev h`.
-/
theorem tensor_inj {O K Ω C B : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field Ω] [Algebra O Ω] [Algebra K Ω] [IsScalarTower O K Ω] [Field C] [Algebra O C] [Algebra K C]
    [IsScalarTower O K C] [CommRing B] [Algebra O B] (ev : B →ₐ[O] Ω) (hev : Function.Injective ev) :
    ∃ ι : B ⊗[O] C →+* Ω ⊗[K] C, Function.Injective ι ∧ ∀ b c, ι (b ⊗ₜ[O] c) = ev b ⊗ₜ[K] c := by
  classical
  haveI : Module.Flat O K := IsLocalization.flat K (nonZeroDivisors O)
  haveI : Module.Flat O C := Module.Flat.trans O K C
  have hcs := IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors O) K Ω C
  let e := TensorProduct.equivOfCompatibleSMul O K Ω Ω C
  letI : Algebra O (Ω ⊗[K] C) := ((algebraMap K (Ω ⊗[K] C)).comp (algebraMap O K)).toAlgebra
  let g1 : B →ₐ[O] Ω ⊗[K] C :=
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[K] C).comp ev.toRingHom
      commutes' := fun o => by
        show (ev (algebraMap O B o)) ⊗ₜ[K] (1 : C) = algebraMap K (Ω ⊗[K] C) (algebraMap O K o)
        rw [ev.commutes, Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply] }
  let g2 : C →ₐ[O] Ω ⊗[K] C :=
    { toRingHom := (Algebra.TensorProduct.includeRight : C →ₐ[K] Ω ⊗[K] C).toRingHom
      commutes' := fun o => by
        show (Algebra.TensorProduct.includeRight : C →ₐ[K] Ω ⊗[K] C) (algebraMap O C o) =
          algebraMap K (Ω ⊗[K] C) (algebraMap O K o)
        rw [IsScalarTower.algebraMap_apply O K C, AlgHom.commutes] }
  let ι : B ⊗[O] C →+* Ω ⊗[K] C := (Algebra.TensorProduct.productMap g1 g2).toRingHom
  have hι : ∀ b c, ι (b ⊗ₜ[O] c) = ev b ⊗ₜ[K] c := by
    intro b c
    show g1 b * g2 c = _
    show (ev b ⊗ₜ[K] (1 : C)) * ((1 : Ω) ⊗ₜ[K] c) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine ⟨ι, ?_, hι⟩
  have hE : ∀ z, e (ι z) = (ev.toLinearMap.rTensor C) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => rw [hι]; rfl
    | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]
  intro a b hab
  have h := congrArg e hab
  rw [hE, hE] at h
  exact Module.Flat.rTensor_preserves_injective_linearMap _ hev h

section Affine

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Set `x : W` to `⟨genPt ξ, hne⟩`. Use `letI := X.presheaf.algebra_section_stalk x`. Use `haveI hloc := hW.isLocalization_stalk x`. Establish `hinj : Function.Injective (algebraMap Γ(X, W) (X.presheaf.stalk x.1))` using `IsLocalization.injective _ (hW.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors`. Establish `hfac : ∀ g, val ξ W hne g = (Scheme.stalkClosedPointTo ξ).hom (algebraMap Γ(X, W) (X.presheaf.stalk x.1) g)` using `fun g => (germ_closedPoint ξ W hne g).symm`.

Establish `hP : (hW.primeIdealOf x).asIdeal = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `a ha`. Assume the negation of the conclusion as `ha0`. Establish `ha0' : a ≠ 0` using `fun h => ha0 (by simp [h])`.

Establish `h1 : algebraMap Γ(X, W) (X.presheaf.stalk x.1) a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff _ (hW.primeIdealOf x).asIdeal a).2 ha`. Establish `hz : algebraMap Γ(X, W) (X.presheaf.stalk x.1) a ≠ 0` using `fun h => ha0' (hinj (h.trans (map_zero _).symm))`. Use `set z := algebraMap Γ(X, W) (X.presheaf.stalk x.1) a`. Set `φ : X.presheaf.stalk x.1 →+* Ω` to `(Scheme.stalkClosedPointTo ξ).hom`. Establish `hφ : Function.Bijective φ` using `hg.bij`.

Establish `hy : φ z ≠ 0` using `fun h => hz (hφ.1 (h.trans (map_zero _).symm))`. Take `⟨w, hw⟩` from `hφ.2 (φ z)⁻¹`. Establish `hzw : z * w = 1` using `hφ.1 (by rw [map_mul, map_one, hw, mul_inv_cancel₀ hy])`. Conclude with `h1 (IsUnit.of_mul_eq_one w hzw)`. Use `⟨fun q hq => ?_, fun a b hab => ?_⟩` and prove the remaining obligations.

Set `y : W` to `⟨q, hq⟩`. Establish `h1 : hW.primeIdealOf x ⤳ hW.primeIdealOf y` using `(PrimeSpectrum.le_iff_specializes _ _).1 (by show (hW.primeIdealOf x).asIdeal ≤ (hW.primeIdealOf y).asIdeal`. Rewrite using `[hP]`. Conclude with `bot_le)`. Establish `h2` using `h1.map hW.fromSpec.continuous`.

Rewrite `h2` using `[IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_primeIdealOf]`. Then use the resulting hypothesis. Rewrite `hab` using `[hfac, hfac]`. Conclude with `hinj (hg.bij.1 hab)`.
-/
theorem affine_domain_gen (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hg : IsCptGen ξ) (W : X.Opens)
    (hW : IsAffineOpen W) (hne : genPt ξ ∈ W) [IsDomain Γ(X, W)] :
    (∀ q ∈ W, genPt ξ ⤳ q) ∧ Function.Injective (val ξ W hne) := by
  let x : W := ⟨genPt ξ, hne⟩
  letI := X.presheaf.algebra_section_stalk x
  haveI hloc := hW.isLocalization_stalk x
  have hinj : Function.Injective (algebraMap Γ(X, W) (X.presheaf.stalk x.1)) :=
    IsLocalization.injective _ (hW.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors
  have hfac : ∀ g, val ξ W hne g =
      (Scheme.stalkClosedPointTo ξ).hom (algebraMap Γ(X, W) (X.presheaf.stalk x.1) g) :=
    fun g => (germ_closedPoint ξ W hne g).symm
  have hP : (hW.primeIdealOf x).asIdeal = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    by_contra ha0
    have ha0' : a ≠ 0 := fun h => ha0 (by simp [h])
    have h1 : algebraMap Γ(X, W) (X.presheaf.stalk x.1) a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x.1) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (hW.primeIdealOf x).asIdeal a).2 ha
    have hz : algebraMap Γ(X, W) (X.presheaf.stalk x.1) a ≠ 0 := fun h =>
      ha0' (hinj (h.trans (map_zero _).symm))
    set z := algebraMap Γ(X, W) (X.presheaf.stalk x.1) a
    let φ : X.presheaf.stalk x.1 →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
    have hφ : Function.Bijective φ := hg.bij
    have hy : φ z ≠ 0 := fun h => hz (hφ.1 (h.trans (map_zero _).symm))
    obtain ⟨w, hw⟩ := hφ.2 (φ z)⁻¹
    have hzw : z * w = 1 := hφ.1 (by rw [map_mul, map_one, hw, mul_inv_cancel₀ hy])
    exact h1 (IsUnit.of_mul_eq_one w hzw)
  refine ⟨fun q hq => ?_, fun a b hab => ?_⟩
  · let y : W := ⟨q, hq⟩
    have h1 : hW.primeIdealOf x ⤳ hW.primeIdealOf y :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (by
        show (hW.primeIdealOf x).asIdeal ≤ (hW.primeIdealOf y).asIdeal
        rw [hP]
        exact bot_le)
    have h2 := h1.map hW.fromSpec.continuous
    rwa [IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_primeIdealOf] at h2
  · rw [hfac, hfac] at hab
    exact hinj (hg.bij.1 hab)

/- English proof (translation)
Set `x : W` to `⟨genPt ξ, hne⟩`. Use `letI := X.presheaf.algebra_section_stalk x`. Use `haveI hloc := hW.isLocalization_stalk x`. Establish `hfac : ∀ g, val ξ W hne g = (Scheme.stalkClosedPointTo ξ).hom (algebraMap Γ(X, W) (X.presheaf.stalk x.1) g)` using `fun g => (germ_closedPoint ξ W hne g).symm`. Take `⟨z, rfl⟩` from `hg.bij.2 ω`.

Take `⟨⟨a, r⟩, h⟩` from `IsLocalization.surj (S := X.presheaf.stalk x.1) (hW.primeIdealOf x).asIdeal.primeCompl z`. Use `⟨a, r, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfac]`. Conclude with `((IsLocalization.map_units (X.presheaf.stalk x.1) r).map (Scheme.stalkClosedPointTo ξ).hom).ne_zero`. Rewrite using `[hfac, hfac, ← map_mul]`.

Conclude with `congrArg _ h`.
-/
theorem exists_frac (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hg : IsCptGen ξ) (W : X.Opens)
    (hW : IsAffineOpen W) (hne : genPt ξ ∈ W) (ω : Ω) :
    ∃ b₁ b₂ : Γ(X, W), val ξ W hne b₂ ≠ 0 ∧ ω * val ξ W hne b₂ = val ξ W hne b₁ := by
  let x : W := ⟨genPt ξ, hne⟩
  letI := X.presheaf.algebra_section_stalk x
  haveI hloc := hW.isLocalization_stalk x
  have hfac : ∀ g, val ξ W hne g =
      (Scheme.stalkClosedPointTo ξ).hom (algebraMap Γ(X, W) (X.presheaf.stalk x.1) g) :=
    fun g => (germ_closedPoint ξ W hne g).symm
  obtain ⟨z, rfl⟩ := hg.bij.2 ω
  obtain ⟨⟨a, r⟩, h⟩ := IsLocalization.surj (S := X.presheaf.stalk x.1) (hW.primeIdealOf x).asIdeal.primeCompl z
  refine ⟨a, r, ?_, ?_⟩
  · rw [hfac]
    exact ((IsLocalization.map_units (X.presheaf.stalk x.1) r).map
      (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  · rw [hfac, hfac, ← map_mul]
    exact congrArg _ h

end Affine

/- English proof (translation)
Establish `hd : ξ' ≫ f = Spec.map (CommRingCat.ofHom i) ≫ ξ` using `hdom`. Establish `e : Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom (algebraMap O Ω)) = Spec.map (CommRingCat.ofHom (algebraMap C Ω')) ≫ Spec.map (CommRingCat.ofHom (algebraMap O C))`. Rewrite using `[← h1, ← h2, Category.assoc, ← hw, ← Category.assoc, ← hd, Category.assoc]`. Rewrite `e` using `[← Spec.map_comp, ← Spec.map_comp]`. Establish `e'` using `Spec.map_injective e`.

Conclude with `congrArg (fun g => g.hom o) e'`.
-/
theorem compat_base {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {O : Type} [CommRing O] [Algebra O Ω] {s : X ⟶ Spec (CommRingCat.of O)}
    {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} {C : Type} [Field C] [Algebra O C] [Algebra C Ω'] {s' : X' ⟶ Spec (CommRingCat.of C)}
    (h1 : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)))
    (hw : f ≫ s = s' ≫ Spec.map (CommRingCat.ofHom (algebraMap O C)))
    (h2 : ξ' ≫ s' = Spec.map (CommRingCat.ofHom (algebraMap C Ω')))
    (hdom : Dominates ξ' ξ f i) (o : O) :
    i (algebraMap O Ω o) = algebraMap C Ω' (algebraMap O C o) := by
  have hd : ξ' ≫ f = Spec.map (CommRingCat.ofHom i) ≫ ξ := hdom
  have e : Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom (algebraMap O Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap C Ω')) ≫ Spec.map (CommRingCat.ofHom (algebraMap O C)) := by
    rw [← h1, ← h2, Category.assoc, ← hw, ← Category.assoc, ← hd, Category.assoc]
  rw [← Spec.map_comp, ← Spec.map_comp] at e
  have e' := Spec.map_injective e
  exact congrArg (fun g => g.hom o) e'

/- English proof (translation)
Use `letI : Algebra O Γ(X, W) := (algX s W).toAlgebra`. Set `W' : X'.Opens` to `f ⁻¹ᵁ W ⊓ s' ⁻¹ᵁ ⊤`. Establish `hmemW' : ∀ q' : X', q' ∈ W' ↔ f q' ∈ W` using `fun q' => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩`. Establish `hWW' : W' = f ⁻¹ᵁ W`. Use extensionality with `q'`.

Conclude with `(hmemW' q').trans Iff.rfl`. Use `haveI : IsAffineHom f := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance`. Establish `hW' : IsAffineOpen W'`. Rewrite using `[hWW']`. Conclude with `hW.preimage f`.

Establish `hne' : genPt ξ' ∈ W'`. Rewrite using `[hmemW']`. Establish `: f (genPt ξ') = genPt ξ` using `hdom.map_genPt`. Rewrite using `[this]`. Conclude with `hne`.

Establish `hvinj : Function.Injective (val ξ W hne)`. Introduce `a b hab`. Use `RegSection.section_eq hg W hWZ a b fun q hq => ?_` and prove the remaining obligations. Rewrite using `[genMap_germ ξ W ⟨q, hWZ q hq⟩ hq, genMap_germ ξ W ⟨q, hWZ q hq⟩ hq]`. Conclude with `hab`.

Set `evA : Γ(X, W) →ₐ[O] Ω` to `{ toRingHom := val ξ W hne commutes' := fun o => val_algX h1 W hne o }`. Take `⟨ι, hιinj, hι⟩` from `tensor_inj (K := K) (C := C) evA hvinj`. Set `E` to `eTens s s' f hpb W hW`. Use `haveI : IsDomain (Γ(X, W) ⊗[O] C) := hιinj.isDomain ι`. Use `haveI : IsDomain Γ(X', W') := E.symm.injective.isDomain (E.symm : Γ(X', W') →+* Γ(X, W) ⊗[O] C)`.

Take `⟨hspec, hvinj'⟩` from `affine_domain_gen ξ' hg' W' hW' hne'`. Establish `hvE : ∀ z : Γ(X, W) ⊗[O] C, val ξ' W' hne' (E z) = φ (ι z)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero E, map_zero (val ξ' W' hne'), map_zero ι, map_zero φ]`.

Consider the case `tmul b c`. Rewrite using `[hι, hφ, show E (b ⊗ₜ[O] c) = _ from eTens_tmul s s' f hpb W hW b c, map_mul, val_pull hdom W W' inf_le_left hne hne', val_algX h2]`. Both sides reduce to the same expression. Consider the case `add u v hu hv => simp only [map_add, hu, hv]`. Establish `hφs : ∀ (a : Ω) (z : Ω ⊗[K] C), φ (a • z) = i a * φ z`.

Introduce `a z`. Rewrite using `[Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, hφ]`. Simplify using the standard rewrite rules. Establish `hcl : ∀ z, ι z ∈ AddSubmonoid.closure {z : Ω ⊗[K] C | ∃ (a : Ω) (c : C), (∀ p : Cpt ξ, p.1 ∈ W → a ∈ regAt ξ p) ∧ z = a ⊗ₜ[K] c}`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `tmul b c`. Use `AddSubmonoid.subset_closure ⟨val ξ W hne b, c, fun p hp => ?_, hι b c⟩` and prove the remaining obligations.

Conclude with `⟨_, genMap_germ ξ W p hp b⟩`. Consider the case `add u v hu hv => rw [map_add]`. Conclude with `add_mem hu hv`. Use `⟨fun q' hq => hspec q' ((hmemW' q').2 hq), ?_, fun a' ha' => ?_⟩` and prove the remaining obligations. Establish `key : ∀ x : Ω ⊗[K] C, ∃ b : Γ(X, W), val ξ W hne b ≠ 0 ∧ ∃ z, ι z = val ξ W hne b • x`.

Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, by simp, 0, by simp⟩`. Consider the case `tmul a c`. Take `⟨b₁, b₂, h0, h⟩` from `exists_frac ξ hg W hW hne a`.

Use `⟨b₂, h0, b₁ ⊗ₜ[O] c, ?_⟩` and prove the remaining obligations. Rewrite using `[hι, TensorProduct.smul_tmul', smul_eq_mul, mul_comm, h]`. Both sides reduce to the same expression. Consider the case `add u v hu hv`. Take `⟨b₁, h₁, z₁, e₁⟩` from `hu`.

Take `⟨b₂, h₂, z₂, e₂⟩` from `hv`. Use `⟨b₁ * b₂, by simpa [h₁, h₂] using mul_ne_zero h₁ h₂, (b₂ ⊗ₜ[O] (1 : C)) * z₁ + (b₁ ⊗ₜ[O] (1 : C)) * z₂, ?_⟩` and prove the remaining obligations. Establish `hb : ∀ (b : Γ(X, W)) (z), ι ((b ⊗ₜ[O] (1 : C)) * z) = val ξ W hne b • ι z`. Introduce `b z`. Rewrite using `[map_mul, hι, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]`.

Both sides reduce to the same expression. Rewrite using `[map_add, hb, hb, e₁, e₂, map_mul, smul_add, smul_smul, smul_smul, mul_comm (val ξ W hne b₁)]`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨b, hb, z, hz⟩` from `key x`.

Establish `h0 : val ξ' W' hne' (E z) = val ξ' W' hne' 0`. Rewrite using `[hvE, hz, hφs, hx, mul_zero, map_zero]`. Establish `hz0 : z = 0` using `E.injective ((hvinj' h0).trans (map_zero E).symm)`. Rewrite `hz` using `[hz0, map_zero]`. Conclude with `(smul_eq_zero.1 hz.symm).resolve_left hb`.

Establish `hU : ∀ q ∈ W', genPt ξ' ⤳ q` using `hspec`. Take `⟨g, hg₁, -⟩` from `RegSection.existsUnique_section X' Ω' ξ' hg' W' hU a' ⟨_, hne'⟩ (fun q hq => ha' ⟨q, hU q hq⟩ ((hmemW' q).1 hq))`. Take `⟨z, rfl⟩` from `E.surjective g`. Use `⟨ι z, ?_, hcl z⟩` and prove the remaining obligations. Rewrite using `[← hvE, ← hg₁ _ hne', genMap_germ ξ' W' ⟨genPt ξ', hU _ hne'⟩ hne']`.
-/
theorem chart (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (X' : Scheme.{0}) [IsLocallyNoetherian X'] (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X)
    (i : Ω →+* Ω') (C : Type) [Field C] [Algebra O C] [Algebra C Ω'] (s' : X' ⟶ Spec (CommRingCat.of C))
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra K Ω] [IsScalarTower O K Ω]
    [Algebra K C] [IsScalarTower O K C] [IsDomain (Ω ⊗[K] C)]
    (h1 : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)))
    (hpb : IsPullback f s' s (Spec.map (CommRingCat.ofHom (algebraMap O C))))
    (h2 : ξ' ≫ s' = Spec.map (CommRingCat.ofHom (algebraMap C Ω')))
    (hdom : Dominates ξ' ξ f i) (hg : IsCptGen ξ) (hg' : IsCptGen ξ')
    (φ : Ω ⊗[K] C →+* Ω') (hφ : ∀ a c, φ (a ⊗ₜ[K] c) = i a * algebraMap C Ω' c)
    (W : X.Opens) (hW : IsAffineOpen W) (hWZ : ∀ q ∈ W, genPt ξ ⤳ q) (hne : genPt ξ ∈ W) :
    (∀ q' : X', f q' ∈ W → genPt ξ' ⤳ q') ∧ Function.Injective φ ∧
      ∀ a' : Ω', (∀ q' : Cpt ξ', f q'.1 ∈ W → a' ∈ regAt ξ' q') → ∃ x : Ω ⊗[K] C, φ x = a' ∧
        x ∈ AddSubmonoid.closure {z : Ω ⊗[K] C | ∃ (a : Ω) (c : C),
          (∀ p : Cpt ξ, p.1 ∈ W → a ∈ regAt ξ p) ∧ z = a ⊗ₜ[K] c} := by
  classical
  letI : Algebra O Γ(X, W) := (algX s W).toAlgebra
  let W' : X'.Opens := f ⁻¹ᵁ W ⊓ s' ⁻¹ᵁ ⊤
  have hmemW' : ∀ q' : X', q' ∈ W' ↔ f q' ∈ W := fun q' => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
  have hWW' : W' = f ⁻¹ᵁ W := by
    ext q'
    exact (hmemW' q').trans Iff.rfl
  haveI : IsAffineHom f :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hW' : IsAffineOpen W' := by
    rw [hWW']
    exact hW.preimage f
  have hne' : genPt ξ' ∈ W' := by
    rw [hmemW']
    have : f (genPt ξ') = genPt ξ := hdom.map_genPt
    rw [this]
    exact hne
  have hvinj : Function.Injective (val ξ W hne) := by
    intro a b hab
    refine RegSection.section_eq hg W hWZ a b fun q hq => ?_
    rw [genMap_germ ξ W ⟨q, hWZ q hq⟩ hq, genMap_germ ξ W ⟨q, hWZ q hq⟩ hq]
    exact hab
  let evA : Γ(X, W) →ₐ[O] Ω :=
    { toRingHom := val ξ W hne
      commutes' := fun o => val_algX h1 W hne o }
  obtain ⟨ι, hιinj, hι⟩ := tensor_inj (K := K) (C := C) evA hvinj
  let E := eTens s s' f hpb W hW
  haveI : IsDomain (Γ(X, W) ⊗[O] C) := hιinj.isDomain ι
  haveI : IsDomain Γ(X', W') := E.symm.injective.isDomain (E.symm : Γ(X', W') →+* Γ(X, W) ⊗[O] C)
  obtain ⟨hspec, hvinj'⟩ := affine_domain_gen ξ' hg' W' hW' hne'
  have hvE : ∀ z : Γ(X, W) ⊗[O] C, val ξ' W' hne' (E z) = φ (ι z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero E, map_zero (val ξ' W' hne'), map_zero ι, map_zero φ]
    | tmul b c =>
      rw [hι, hφ, show E (b ⊗ₜ[O] c) = _ from eTens_tmul s s' f hpb W hW b c, map_mul,
        val_pull hdom W W' inf_le_left hne hne', val_algX h2]
      rfl
    | add u v hu hv => simp only [map_add, hu, hv]
  have hφs : ∀ (a : Ω) (z : Ω ⊗[K] C), φ (a • z) = i a * φ z := by
    intro a z
    rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, hφ]
    simp
  have hcl : ∀ z, ι z ∈ AddSubmonoid.closure {z : Ω ⊗[K] C | ∃ (a : Ω) (c : C),
      (∀ p : Cpt ξ, p.1 ∈ W → a ∈ regAt ξ p) ∧ z = a ⊗ₜ[K] c} := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul b c =>
      refine AddSubmonoid.subset_closure ⟨val ξ W hne b, c, fun p hp => ?_, hι b c⟩
      exact ⟨_, genMap_germ ξ W p hp b⟩
    | add u v hu hv => rw [map_add]; exact add_mem hu hv
  refine ⟨fun q' hq => hspec q' ((hmemW' q').2 hq), ?_, fun a' ha' => ?_⟩
  · have key : ∀ x : Ω ⊗[K] C, ∃ b : Γ(X, W), val ξ W hne b ≠ 0 ∧ ∃ z, ι z = val ξ W hne b • x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨1, by simp, 0, by simp⟩
      | tmul a c =>
        obtain ⟨b₁, b₂, h0, h⟩ := exists_frac ξ hg W hW hne a
        refine ⟨b₂, h0, b₁ ⊗ₜ[O] c, ?_⟩
        rw [hι, TensorProduct.smul_tmul', smul_eq_mul, mul_comm, h]
        rfl
      | add u v hu hv =>
        obtain ⟨b₁, h₁, z₁, e₁⟩ := hu
        obtain ⟨b₂, h₂, z₂, e₂⟩ := hv
        refine ⟨b₁ * b₂, by simpa [h₁, h₂] using mul_ne_zero h₁ h₂, (b₂ ⊗ₜ[O] (1 : C)) * z₁ + (b₁ ⊗ₜ[O] (1 : C)) * z₂, ?_⟩
        have hb : ∀ (b : Γ(X, W)) (z), ι ((b ⊗ₜ[O] (1 : C)) * z) = val ξ W hne b • ι z := by
          intro b z
          rw [map_mul, hι, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
          rfl
        rw [map_add, hb, hb, e₁, e₂, map_mul, smul_add, smul_smul, smul_smul, mul_comm (val ξ W hne b₁)]
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, hb, z, hz⟩ := key x
    have h0 : val ξ' W' hne' (E z) = val ξ' W' hne' 0 := by
      rw [hvE, hz, hφs, hx, mul_zero, map_zero]
    have hz0 : z = 0 := E.injective ((hvinj' h0).trans (map_zero E).symm)
    rw [hz0, map_zero] at hz
    exact (smul_eq_zero.1 hz.symm).resolve_left hb
  · have hU : ∀ q ∈ W', genPt ξ' ⤳ q := hspec
    obtain ⟨g, hg₁, -⟩ := RegSection.existsUnique_section X' Ω' ξ' hg' W' hU a' ⟨_, hne'⟩
      (fun q hq => ha' ⟨q, hU q hq⟩ ((hmemW' q).1 hq))
    obtain ⟨z, rfl⟩ := E.surjective g
    refine ⟨ι z, ?_, hcl z⟩
    rw [← hvE, ← hg₁ _ hne', genMap_germ ξ' W' ⟨genPt ξ', hU _ hne'⟩ hne']

/- English proof (translation)
Establish `hcomp0` using `compat_base h1 hpb.w h2 hdom`. Establish `hcomp : ∀ k : K, i (algebraMap K Ω k) = algebraMap C Ω' (algebraMap K C k)`. Introduce `k`. Establish `: i.comp (algebraMap K Ω) = (algebraMap C Ω').comp (algebraMap K C)`. Apply `IsLocalization.ringHom_ext (nonZeroDivisors O)` to reduce the goal to its premises.

Use extensionality with `o`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply O K Ω, ← IsScalarTower.algebraMap_apply O K C]`. Conclude with `hcomp0 o`. Conclude with `congrArg (fun g => g k) this`.

Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Ω ⊗[K] C →+* Ω', ∀ a c, φ (a ⊗ₜ[K] c) = i a * algebraMap C Ω' c := by`. Use `letI : Algebra K Ω' := ((algebraMap C Ω').comp (algebraMap K C)).toAlgebra`. Set `fΩ : Ω →ₐ[K] Ω'` to `{ i with commutes' := fun k => hcomp k }`. Set `fC : C →ₐ[K] Ω'` to `{ algebraMap C Ω' with commutes' := fun k => rfl }`. Conclude with `⟨(Algebra.TensorProduct.productMap fΩ fC).toRingHom, fun a c => by simp [fΩ, fC]⟩`.

Use `haveI : CharZero K := ((algebraMap K Ω).charZero_iff (algebraMap K Ω).injective).2 inferInstance`. Establish `hfrac : ∀ (x y : O) (a b : Ω), y ≠ 0 → a * algebraMap O Ω y = algebraMap O Ω x * b → a = algebraMap K Ω (algebraMap O K x / algebraMap O K y) * b`. Introduce `x y a b hy e`. Establish `hy' : algebraMap O Ω y ≠ 0` using `fun h => hy (hO (h.trans (map_zero _).symm))`. Rewrite using `[map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_mul_eq_mul_div, eq_div_iff hy', e]`.

Use `haveI hT : IsDomain (Ω ⊗[K] C) := GlobalTheory.T.alg_closed_tensor_isDomain K Ω C (fun a ha => by`. Take `⟨x, y, hy, e⟩` from `hcc a ((IsFractionRing.isAlgebraic_iff O K Ω).2 ha)`. Conclude with `⟨algebraMap O K x / algebraMap O K y, by`. Use `hfrac x y a 1 hy (by rw [e, mul_one])` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Conclude with `this.symm⟩)`. Use `haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s`. Use `haveI : LocallyOfFiniteType s' := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance`. Use `haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian s'`. Take `⟨Z, hZ, -, -⟩` from `cpt_open_integral X Ω ξ hg`.

Establish `hfib : ∀ (q' : X') (h : genPt ξ ⤳ f q'), (⟨f q', h⟩ : Cpt ξ) ∈ genFibre O ξ` using `genFibre_of_field_point X Ω ξ O s h1 X' C s' f hOC hpb.w`. Establish `hchart : ∀ p : {p : Cpt ξ // p ∈ genFibre O ξ}, ∃ (e : Ω) (W : X.Opens), e ≠ 0 ∧ IsAffineOpen W ∧ p.1.1 ∈ W ∧ (∀ q ∈ W, genPt ξ ⤳ q) ∧ (∀ q ∈ genFibre O ξ, q.1 ∈ W → L.IsGenAt q e)`. Introduce and unpack `⟨p, hp⟩`. Take `⟨U, hU, b, -, hb⟩` from `hVB p hp`. Establish `hm : p.1 ∈ U ⊓ Z` using `⟨hU, (hZ p.1).2 p.2⟩`.

Take `⟨W, hW, hpW, hWle⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hm`. Establish `hr : Set.range b = {b 0}`. Use extensionality with `x`. Simplify using `[Fin.exists_fin_one, eq_comm]`. Use `⟨b 0, W, (hb p hp hU).1.ne_zero 0, hW, hpW, fun q hq => (hZ q).1 (hWle hq).2, fun q hq hqW => ?_⟩` and prove the remaining obligations.

Establish `hf` using `hb q hq (hWle hqW).1`. Conclude with `⟨hf.1.ne_zero 0, by rw [hf.2, hr]⟩`. Use `choose e W he hW hpW hWZ hWL using hchart`. Establish `hne : ∀ p, genPt ξ ∈ W p` using `fun p => p.1.2.mem_open (W p).isOpen (hpW p)`. Establish `hcharts` using `fun p => chart X Ω ξ O s X' Ω' ξ' f i C s' K h1 hpb h2 hdom hg hg' φ hφ (W p) (hW p) (hWZ p) (hne p)`.

Establish `hgen_e : ∀ p (q' : Cpt ξ'), f q'.1 ∈ W p → (L.pull ξ' f i.toAddMonoidHom).IsGenAt q' (i (e p))`. Introduce `p q' hq`. Take `⟨h, -, H⟩` from `pull_reg_and_gen X Ω ξ X' Ω' ξ' f i hdom q'`. Conclude with `H L (e p) (hWL p _ (hfib q'.1 h) hq)`. Establish `ht0 : t' ≠ 0` using `(hgen ⟨genPt ξ', specializes_rfl⟩).1`.

Establish `hei : ∀ p, i (e p) ≠ 0` using `fun p => (map_ne_zero i).2 (he p)`. Establish `hunit : ∀ p (q' : Cpt ξ'), f q'.1 ∈ W p → unitAt ξ' q' (t' / i (e p))`. Introduce `p q' hq`. Establish `a` using `hgen q'`. Establish `b` using `hgen_e p q' hq`.

Take `⟨u, hu, hut⟩` from `ZUnit.exists_of_span_eq a.1 (a.2.symm.trans b.2)`. Establish `e1 : t' / i (e p) = u`. Rewrite using `[hut, smul_eq_mul, mul_div_cancel_right₀ _ (hei p)]`. Rewrite using `[e1]`. Conclude with `hu`.

Establish `hx` using `fun p => (hcharts p).2.2 (t' / i (e p)) (fun q' hq => (hunit p q' hq).2.1)`. Establish `hy` using `fun p => (hcharts p).2.2 (i (e p) / t') (fun q' hq => by`. Use `(hunit p q' hq).2.2` as an intermediate fact. Rewrite using `[inv_div] at this)` and apply the resulting hypothesis. Use `choose x hxφ hxm using hx`.

Use `choose y hyφ hym using hy`. Establish `hφs : ∀ (a : Ω) (z : Ω ⊗[K] C), φ (a • z) = i a * φ z`. Introduce `a z`. Rewrite using `[Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, hφ]`. Simplify using the standard rewrite rules.

Establish `hfg : f (genPt ξ') = genPt ξ` using `hdom.map_genPt`. Set `p₀ : {p : Cpt ξ // p ∈ genFibre O ξ}` to `⟨⟨f (genPt ξ'), by rw [hfg]⟩, hfib _ _⟩`. Establish `hinj : Function.Injective φ` using `(hcharts p₀).2.1`. Establish `hτφ : φ (e p₀ • x p₀) = t'`. Rewrite using `[hφs, hxφ]`.

Clear denominators, using `[hei p₀]` for the nonvanishing conditions. Establish `hυφ : φ ((e p₀)⁻¹ • y p₀) = t'⁻¹`. Rewrite using `[hφs, hyφ, map_inv₀]`. Clear denominators, using `[hei p₀, ht0]` for the nonvanishing conditions. Establish `hK : ∀ (p : {p : Cpt ξ // p ∈ genFibre O ξ}) k, algebraMap K Ω k ∈ regAt ξ p.1`.

Introduce `p k`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := O) k`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hreg : ∀ o : O, algebraMap O Ω o ∈ regAt ξ p.1`. Introduce `o`.

Distinguish the cases in `ho : o = 0`. Rewrite using `[ho, map_zero]`. Conclude with `zero_mem _`. Conclude with `(p.2 o ho).2.1`. Rewrite using `[map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_eq_mul_inv]`.

Conclude with `mul_mem (hreg a) (p.2 b hb0).2.2`. Establish `hLt : ∀ (t : Ω), t ≠ 0 → (∀ p : {p : Cpt ξ // p ∈ genFibre O ξ}, t / e p ∈ regAt ξ p.1 ∧ e p / t ∈ regAt ξ p.1) → ∀ p ∈ genFibre O ξ, L.IsGenAt p t`. Introduce `t ht hr p hp`. Establish `hpe` using `hWL ⟨p, hp⟩ p hp (hpW ⟨p, hp⟩)`. Use `⟨ht, hpe.2.trans ?_⟩` and prove the remaining obligations.

Take `⟨r1, r2⟩` from `hr ⟨p, hp⟩`. Establish `he'` using `he ⟨p, hp⟩`. Apply the tactic sequence `apply le_antisymm <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]`. Conclude with `⟨⟨_, r2⟩, by show e ⟨p, hp⟩ / t * t = _; field_simp⟩`. Conclude with `⟨⟨_, r1⟩, by show t / e ⟨p, hp⟩ * e ⟨p, hp⟩ = _; field_simp⟩`.

Take `⟨t, c, ht, hr, hτ⟩` from `descent_core (K := K) (C := C) (fun p : {p : Cpt ξ // p ∈ genFibre O ξ} => regAt ξ p.1) hK e he (e p₀ • x p₀) ((e p₀)⁻¹ • y p₀) (hinj (by rw [map_mul, hτφ, hυφ, map_one, mul_inv_cancel₀ ht0])) x y (fun p => AddSubmonoid.closure_mono (by`. Introduce and unpack `_ ⟨a, c, ha, rfl⟩`. Conclude with `⟨a, ha p.1 (hpW p), c, rfl⟩) (hxm p))`. Use the proof step `(fun p => AddSubmonoid.closure_mono (by`. Introduce and unpack `_ ⟨a, c, ha, rfl⟩`.

Conclude with `⟨a, ha p.1 (hpW p), c, rfl⟩) (hym p))`. Use the proof step `(fun p => hinj (by rw [hτφ, hφs, hxφ]; field_simp [hei p]))`. Use the proof step `(fun p => hinj (by rw [hφs, hυφ, hyφ]; field_simp [hei p, ht0]))`. Use the proof step `(fun a ha hreg => by`. Take `⟨u, v, hv, ee⟩` from `(GlobalTheory.T.line_lattice_generic_sections X Ω ξ O s h1 hO hg hcc (fun p => Submodule.span (regAt ξ p) {1}) 1 (fun p _ => ⟨one_ne_zero, rfl⟩) a).1 (fun p hp => Submodule.mem_span_singleton.2 ⟨⟨a, hreg ⟨p, hp⟩⟩, mul_one a⟩)`.

Use `hfrac u v a 1 hv ee` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `⟨_, this⟩)`. Use the proof step `(fun t ht hr u hu => by`. Establish `hLt'` using `hLt t ht hr`.

Take `⟨a, b, hb, ee⟩` from `(GlobalTheory.T.line_lattice_generic_sections X Ω ξ O s h1 hO hg hcc L t hLt' u).1 (fun p hp => by`. Establish `hpe` using `hWL ⟨p, hp⟩ p hp (hpW ⟨p, hp⟩)`. Rewrite using `[hpe.2]`. Conclude with `Submodule.mem_span_singleton.2 ⟨⟨_, hu ⟨p, hp⟩⟩, by show u / e ⟨p, hp⟩ * e ⟨p, hp⟩ = u`. Clear denominators, using `[he ⟨p, hp⟩]⟩)` for the nonvanishing conditions.

Conclude with `⟨_, hfrac a b u t hb ee⟩)`. Use `⟨t, c, hLt t ht hr, ?_⟩` and prove the remaining obligations. Use `congrArg φ hτ` as an intermediate fact. Rewrite `this` using `[hτφ, hφ]`. Rewrite using `[this, mul_comm]`.
-/
theorem finiteRing_sq_sub_mul_sq_eq_of_card (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω]
    (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    [IsNoetherianRing O] [IsProper s]
    (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X)
    (i : Ω →+* Ω') (C : Type) [Field C] [Algebra O C] [Algebra C Ω'] (s' : X' ⟶ Spec (CommRingCat.of C))
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra K Ω] [IsScalarTower O K Ω]
    [Algebra K C] [IsScalarTower O K C]
    (h1 : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)))
    (hO : Function.Injective (algebraMap O Ω))
    (hOC : Function.Injective (algebraMap O C))
    (hpb : IsPullback f s' s (Spec.map (CommRingCat.ofHom (algebraMap O C))))
    (h2 : ξ' ≫ s' = Spec.map (CommRingCat.ofHom (algebraMap C Ω')))
    (hdom : Dominates ξ' ξ f i) (hg : IsCptGen ξ) (hg' : IsCptGen ξ') (hcc : ConstClosed O Ω)
    (L : Lat ξ Ω) (t' : Ω') (hVB : L.IsVBOn (genFibre O ξ) 1 ⊤)
    (hgen : ∀ p' : Cpt ξ', (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' t') :
    ∃ (t : Ω) (c : C), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) ∧ t' = algebraMap C Ω' c * i t := by
  classical
  have hcomp0 := compat_base h1 hpb.w h2 hdom
  have hcomp : ∀ k : K, i (algebraMap K Ω k) = algebraMap C Ω' (algebraMap K C k) := by
    intro k
    have : i.comp (algebraMap K Ω) = (algebraMap C Ω').comp (algebraMap K C) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors O)
      ext o
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply O K Ω, ← IsScalarTower.algebraMap_apply O K C]
      exact hcomp0 o
    exact congrArg (fun g => g k) this
  obtain ⟨φ, hφ⟩ : ∃ φ : Ω ⊗[K] C →+* Ω', ∀ a c, φ (a ⊗ₜ[K] c) = i a * algebraMap C Ω' c := by
    letI : Algebra K Ω' := ((algebraMap C Ω').comp (algebraMap K C)).toAlgebra
    let fΩ : Ω →ₐ[K] Ω' := { i with commutes' := fun k => hcomp k }
    let fC : C →ₐ[K] Ω' := { algebraMap C Ω' with commutes' := fun k => rfl }
    exact ⟨(Algebra.TensorProduct.productMap fΩ fC).toRingHom, fun a c => by simp [fΩ, fC]⟩
  haveI : CharZero K := ((algebraMap K Ω).charZero_iff (algebraMap K Ω).injective).2 inferInstance

  have hfrac : ∀ (x y : O) (a b : Ω), y ≠ 0 → a * algebraMap O Ω y = algebraMap O Ω x * b →
      a = algebraMap K Ω (algebraMap O K x / algebraMap O K y) * b := by
    intro x y a b hy e
    have hy' : algebraMap O Ω y ≠ 0 := fun h => hy (hO (h.trans (map_zero _).symm))
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_mul_eq_mul_div,
      eq_div_iff hy', e]
  haveI hT : IsDomain (Ω ⊗[K] C) := GlobalTheory.T.alg_closed_tensor_isDomain K Ω C (fun a ha => by
    obtain ⟨x, y, hy, e⟩ := hcc a ((IsFractionRing.isAlgebraic_iff O K Ω).2 ha)
    exact ⟨algebraMap O K x / algebraMap O K y, by
      have := hfrac x y a 1 hy (by rw [e, mul_one])
      rw [mul_one] at this
      exact this.symm⟩)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : LocallyOfFiniteType s' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian s'
  obtain ⟨Z, hZ, -, -⟩ := cpt_open_integral X Ω ξ hg
  have hfib : ∀ (q' : X') (h : genPt ξ ⤳ f q'), (⟨f q', h⟩ : Cpt ξ) ∈ genFibre O ξ :=
    genFibre_of_field_point X Ω ξ O s h1 X' C s' f hOC hpb.w
  have hchart : ∀ p : {p : Cpt ξ // p ∈ genFibre O ξ}, ∃ (e : Ω) (W : X.Opens), e ≠ 0 ∧ IsAffineOpen W ∧
      p.1.1 ∈ W ∧ (∀ q ∈ W, genPt ξ ⤳ q) ∧ (∀ q ∈ genFibre O ξ, q.1 ∈ W → L.IsGenAt q e) := by
    rintro ⟨p, hp⟩
    obtain ⟨U, hU, b, -, hb⟩ := hVB p hp
    have hm : p.1 ∈ U ⊓ Z := ⟨hU, (hZ p.1).2 p.2⟩
    obtain ⟨W, hW, hpW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hm
    have hr : Set.range b = {b 0} := by
      ext x
      simp [Fin.exists_fin_one, eq_comm]
    refine ⟨b 0, W, (hb p hp hU).1.ne_zero 0, hW, hpW, fun q hq => (hZ q).1 (hWle hq).2, fun q hq hqW => ?_⟩
    have hf := hb q hq (hWle hqW).1
    exact ⟨hf.1.ne_zero 0, by rw [hf.2, hr]⟩
  choose e W he hW hpW hWZ hWL using hchart
  have hne : ∀ p, genPt ξ ∈ W p := fun p => p.1.2.mem_open (W p).isOpen (hpW p)
  have hcharts := fun p => chart X Ω ξ O s X' Ω' ξ' f i C s' K h1 hpb h2 hdom hg hg' φ hφ (W p) (hW p)
    (hWZ p) (hne p)
  have hgen_e : ∀ p (q' : Cpt ξ'), f q'.1 ∈ W p → (L.pull ξ' f i.toAddMonoidHom).IsGenAt q' (i (e p)) := by
    intro p q' hq
    obtain ⟨h, -, H⟩ := pull_reg_and_gen X Ω ξ X' Ω' ξ' f i hdom q'
    exact H L (e p) (hWL p _ (hfib q'.1 h) hq)
  have ht0 : t' ≠ 0 := (hgen ⟨genPt ξ', specializes_rfl⟩).1
  have hei : ∀ p, i (e p) ≠ 0 := fun p => (map_ne_zero i).2 (he p)
  have hunit : ∀ p (q' : Cpt ξ'), f q'.1 ∈ W p → unitAt ξ' q' (t' / i (e p)) := by
    intro p q' hq
    have a := hgen q'
    have b := hgen_e p q' hq
    obtain ⟨u, hu, hut⟩ := ZUnit.exists_of_span_eq a.1 (a.2.symm.trans b.2)
    have e1 : t' / i (e p) = u := by
      rw [hut, smul_eq_mul, mul_div_cancel_right₀ _ (hei p)]
    rw [e1]
    exact hu
  have hx := fun p => (hcharts p).2.2 (t' / i (e p)) (fun q' hq => (hunit p q' hq).2.1)
  have hy := fun p => (hcharts p).2.2 (i (e p) / t') (fun q' hq => by
    have := (hunit p q' hq).2.2
    rwa [inv_div] at this)
  choose x hxφ hxm using hx
  choose y hyφ hym using hy
  have hφs : ∀ (a : Ω) (z : Ω ⊗[K] C), φ (a • z) = i a * φ z := by
    intro a z
    rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, hφ]
    simp
  have hfg : f (genPt ξ') = genPt ξ := hdom.map_genPt
  let p₀ : {p : Cpt ξ // p ∈ genFibre O ξ} := ⟨⟨f (genPt ξ'), by rw [hfg]⟩, hfib _ _⟩
  have hinj : Function.Injective φ := (hcharts p₀).2.1
  have hτφ : φ (e p₀ • x p₀) = t' := by
    rw [hφs, hxφ]
    field_simp [hei p₀]
  have hυφ : φ ((e p₀)⁻¹ • y p₀) = t'⁻¹ := by
    rw [hφs, hyφ, map_inv₀]
    field_simp [hei p₀, ht0]
  have hK : ∀ (p : {p : Cpt ξ // p ∈ genFibre O ξ}) k, algebraMap K Ω k ∈ regAt ξ p.1 := by
    intro p k
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) k
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hreg : ∀ o : O, algebraMap O Ω o ∈ regAt ξ p.1 := by
      intro o
      by_cases ho : o = 0
      · rw [ho, map_zero]; exact zero_mem _
      · exact (p.2 o ho).2.1
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_eq_mul_inv]
    exact mul_mem (hreg a) (p.2 b hb0).2.2
  have hLt : ∀ (t : Ω), t ≠ 0 → (∀ p : {p : Cpt ξ // p ∈ genFibre O ξ}, t / e p ∈ regAt ξ p.1 ∧ e p / t ∈ regAt ξ p.1) →
      ∀ p ∈ genFibre O ξ, L.IsGenAt p t := by
    intro t ht hr p hp
    have hpe := hWL ⟨p, hp⟩ p hp (hpW ⟨p, hp⟩)
    refine ⟨ht, hpe.2.trans ?_⟩
    obtain ⟨r1, r2⟩ := hr ⟨p, hp⟩
    have he' := he ⟨p, hp⟩
    apply le_antisymm <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    · exact ⟨⟨_, r2⟩, by show e ⟨p, hp⟩ / t * t = _; field_simp⟩
    · exact ⟨⟨_, r1⟩, by show t / e ⟨p, hp⟩ * e ⟨p, hp⟩ = _; field_simp⟩
  obtain ⟨t, c, ht, hr, hτ⟩ := descent_core (K := K) (C := C) (fun p : {p : Cpt ξ // p ∈ genFibre O ξ} => regAt ξ p.1)
    hK e he (e p₀ • x p₀) ((e p₀)⁻¹ • y p₀) (hinj (by rw [map_mul, hτφ, hυφ, map_one, mul_inv_cancel₀ ht0]))
    x y
    (fun p => AddSubmonoid.closure_mono (by
      rintro _ ⟨a, c, ha, rfl⟩
      exact ⟨a, ha p.1 (hpW p), c, rfl⟩) (hxm p))
    (fun p => AddSubmonoid.closure_mono (by
      rintro _ ⟨a, c, ha, rfl⟩
      exact ⟨a, ha p.1 (hpW p), c, rfl⟩) (hym p))
    (fun p => hinj (by rw [hτφ, hφs, hxφ]; field_simp [hei p]))
    (fun p => hinj (by rw [hφs, hυφ, hyφ]; field_simp [hei p, ht0]))
    (fun a ha hreg => by
      obtain ⟨u, v, hv, ee⟩ := (GlobalTheory.T.line_lattice_generic_sections X Ω ξ O s h1 hO hg hcc
        (fun p => Submodule.span (regAt ξ p) {1}) 1 (fun p _ => ⟨one_ne_zero, rfl⟩) a).1
        (fun p hp => Submodule.mem_span_singleton.2 ⟨⟨a, hreg ⟨p, hp⟩⟩, mul_one a⟩)
      have := hfrac u v a 1 hv ee
      rw [mul_one] at this
      exact ⟨_, this⟩)
    (fun t ht hr u hu => by
      have hLt' := hLt t ht hr
      obtain ⟨a, b, hb, ee⟩ := (GlobalTheory.T.line_lattice_generic_sections X Ω ξ O s h1 hO hg hcc L t hLt' u).1 (fun p hp => by
        have hpe := hWL ⟨p, hp⟩ p hp (hpW ⟨p, hp⟩)
        rw [hpe.2]
        exact Submodule.mem_span_singleton.2 ⟨⟨_, hu ⟨p, hp⟩⟩, by
          show u / e ⟨p, hp⟩ * e ⟨p, hp⟩ = u
          field_simp [he ⟨p, hp⟩]⟩)
      exact ⟨_, hfrac a b u t hb ee⟩)
  refine ⟨t, c, hLt t ht hr, ?_⟩
  have := congrArg φ hτ
  rw [hτφ, hφ] at this
  rw [this, mul_comm]

end GlobalTheory.CompanionTheory.Ar.Flat.Descend

open GlobalTheory.CompanionTheory.Ar.Flat.Descend in

/- English proof (translation)
Introduce `X Ω _ ξ _ O _ _ _ s _ _ X' Ω' _ ξ' f i C _ _ _ s' h1 hO hOC hpb h2 hdom hg hg' hcc L t' hVB hgen`. Use `haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hO`. Use `haveI : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).2 hOC`. Use `letI : Algebra (FractionRing O) Ω := FractionRing.liftAlgebra O Ω`. Use `letI : Algebra (FractionRing O) C := FractionRing.liftAlgebra O C`.

Conclude with `finiteRing_sq_sub_mul_sq_eq_of_card X Ω ξ O s X' Ω' ξ' f i C s' (FractionRing O) h1 hO hOC hpb h2 hdom hg hg' hcc L t' hVB hgen`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_extension : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [IsProper s] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (C : Type) [Field C] [Algebra O C] [Algebra C Ω'] (s' : X' ⟶ Spec (CommRingCat.of C)), ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → Function.Injective (algebraMap O C) → IsPullback f s' s (Spec.map (CommRingCat.ofHom (algebraMap O C))) → ξ' ≫ s' = Spec.map (CommRingCat.ofHom (algebraMap C Ω')) → Dominates ξ' ξ f i → IsCptGen ξ → IsCptGen ξ' → ConstClosed O Ω → ∀ (L : Lat ξ Ω) (t' : Ω'), L.IsVBOn (genFibre O ξ) 1 ⊤ → (∀ p' : Cpt ξ', (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' t') → ∃ (t : Ω) (c : C), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) ∧ t' = algebraMap C Ω' c * i t := by
  intro X Ω _ ξ _ O _ _ _ s _ _ X' Ω' _ ξ' f i C _ _ _ s' h1 hO hOC hpb h2 hdom hg hg' hcc L t' hVB hgen
  haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hO
  haveI : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).2 hOC
  letI : Algebra (FractionRing O) Ω := FractionRing.liftAlgebra O Ω
  letI : Algebra (FractionRing O) C := FractionRing.liftAlgebra O C
  exact finiteRing_sq_sub_mul_sq_eq_of_card X Ω ξ O s X' Ω' ξ' f i C s' (FractionRing O) h1 hO hOC hpb h2 hdom hg hg' hcc L t' hVB hgen

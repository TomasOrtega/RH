import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisIntegralChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsUniversalBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDominantSpMapOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth GlobalTheory.LieMet

namespace GlobalTheory.LatDRSpan

section Alg

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Set `x : Fin n → K` to `Matrix.vecMul c M⁻¹`. Establish `hx : c = ∑ j, x j • M j`. Rewrite using `[← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hM), Matrix.vecMul_one]`. Take `⟨⟨d, hd⟩, hdi⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) x`. Use `choose a ha using hdi`.

Establish `hd0 : Ideal.span {d} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `nonZeroDivisors.ne_zero hd`. Establish `hP0 : P ≠ ⊥` using `fun h => hr0 (by simpa [h] using hr)`. Establish `hm : P.IsMaximal` using `hP.isMaximal hP0`.

Take `⟨Q, hQ, hI⟩` from `Ideal.eq_prime_pow_mul_coprime hd0 P`. Generalize the expression as in `Multiset.count P _ = k at hI`. Establish `: ¬ Q ≤ P` using `fun h => hP.ne_top (by rw [← hQ]; exact (sup_eq_left.2 h).symm)`. Take `⟨s, hsQ, hsP⟩` from `SetLike.not_le_iff_exists.1 this`. Establish `hmem` using `Ideal.mul_mem_mul (Ideal.pow_mem_pow hr k) hsQ`.

Rewrite `hmem` using `[← hI, Ideal.mem_span_singleton']`. Take `⟨e, he⟩` from `hmem`. Use `⟨s, hsP, k, fun j => e * a j, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, ← he, hx, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `h1 : algebraMap (𝓞 K) K (a j) = d • x j` using `ha j`. Rewrite using `[mul_smul, mul_smul, ← smul_assoc d, ← h1, algebraMap_smul]`.
-/
theorem exists_mul_pow_mem (P : Ideal (𝓞 K)) [hP : P.IsPrime] {r : 𝓞 K} (hr : r ∈ P) (hr0 : r ≠ 0)
    (M : Matrix (Fin n) (Fin n) K) (hM : M.det ≠ 0) (c : Fin n → K) :
    ∃ s, s ∉ P ∧ ∃ (k : ℕ) (a : Fin n → 𝓞 K), r ^ k • s • c = ∑ j, a j • M j := by
  classical
  let x : Fin n → K := Matrix.vecMul c M⁻¹
  have hx : c = ∑ j, x j • M j := by
    rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hM), Matrix.vecMul_one]
  obtain ⟨⟨d, hd⟩, hdi⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) x
  choose a ha using hdi
  have hd0 : Ideal.span {d} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero hd
  have hP0 : P ≠ ⊥ := fun h => hr0 (by simpa [h] using hr)
  have hm : P.IsMaximal := hP.isMaximal hP0
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime hd0 P
  generalize Multiset.count P _ = k at hI
  have : ¬ Q ≤ P := fun h => hP.ne_top (by rw [← hQ]; exact (sup_eq_left.2 h).symm)
  obtain ⟨s, hsQ, hsP⟩ := SetLike.not_le_iff_exists.1 this
  have hmem := Ideal.mul_mem_mul (Ideal.pow_mem_pow hr k) hsQ
  rw [← hI, Ideal.mem_span_singleton'] at hmem
  obtain ⟨e, he⟩ := hmem
  refine ⟨s, hsP, k, fun j => e * a j, ?_⟩
  rw [smul_smul, ← he, hx, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : algebraMap (𝓞 K) K (a j) = d • x j := ha j
  rw [mul_smul, mul_smul, ← smul_assoc d, ← h1, algebraMap_smul]

/- English proof (translation)
Take `⟨⟨d, hd⟩, hdi⟩` from `IsLocalization.exist_integer_multiples_of_finite P.primeCompl x`. Use `choose a ha using hdi`. Use `⟨d, hd, a, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `h1 : algebraMap (𝓞 K) _ (a j) = d • x j` using `ha j`. Establish `h2` using `congrArg κ h1`. Rewrite `h2` using `[Algebra.smul_def, map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply κ (algebraMap _ _) d, hκ]`. Rewrite using `[← algebraMap_smul K (a j), h2, mul_smul, algebraMap_smul]`.
-/
theorem exists_mul_mem (P : Ideal (𝓞 K)) [hP : P.IsPrime] (κ : Localization.AtPrime P →+* K)
    (hκ : κ.comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K) (M : Matrix (Fin n) (Fin n) K)
    (x : Fin n → Localization.AtPrime P) :
    ∃ s, s ∉ P ∧ ∃ a : Fin n → 𝓞 K, s • ∑ j, κ (x j) • M j = ∑ j, a j • M j := by
  obtain ⟨⟨d, hd⟩, hdi⟩ := IsLocalization.exist_integer_multiples_of_finite P.primeCompl x
  choose a ha using hdi
  refine ⟨d, hd, a, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : algebraMap (𝓞 K) _ (a j) = d • x j := ha j
  have h2 := congrArg κ h1
  rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply κ (algebraMap _ _) d, hκ] at h2
  rw [← algebraMap_smul K (a j), h2, mul_smul, algebraMap_smul]

/- English proof (translation)
Use `⟨(j.comp (algebraMap (𝓞 K) K)).codRestrict (intO C) fun a => ?_, rfl⟩` and prove the remaining obligations. Establish `hx` using `map_isIntegral_int j a.isIntegral_coe`. Establish `h : j a ∈ (NormedField.valuation (K` using `C)).integer := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top`. Rewrite `h` using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Use `show ‖j a‖ ≤ 1`.

Conclude with `h` after adjusting the coercions.
-/
theorem exists_int_hom {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (j : K →+* C) :
    ∃ ψ : 𝓞 K →+* ↥(intO C), (intO C).subtype.comp ψ = j.comp (algebraMap (𝓞 K) K) := by
  refine ⟨(j.comp (algebraMap (𝓞 K) K)).codRestrict (intO C) fun a => ?_, rfl⟩
  have hx := map_isIntegral_int j a.isIntegral_coe
  have h : j a ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  show ‖j a‖ ≤ 1
  exact_mod_cast h

end Alg

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

/- English proof (translation)
Substitute `hχ` using the available equality. Apply `tan_ext` to reduce the goal to its premises. Rewrite using `[left_bcTan, left_bcTan, left_bcTan, ← GlobalTheory.LatDRCrd.dualMap_comp', ← spMap_comp', Category.assoc]`.
-/
theorem bcTan_bcTan {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    {χ : S →+* S''} (hχ : ψ.comp φ = χ) {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    {x'' : Sp S'' ⟶ X} (e : spMap φ ≫ x = x') (e' : spMap ψ ≫ x' = x'') (e'' : spMap χ ≫ x = x'')
    (v : TanM x t.G) : bcTan ψ e' (bcTan φ e v) = bcTan χ e'' v := by
  subst hχ
  apply tan_ext
  rw [left_bcTan, left_bcTan, left_bcTan, ← GlobalTheory.LatDRCrd.dualMap_comp', ← spMap_comp', Category.assoc]

variable {K : Type} [Field K] [NumberField K] {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X}
  (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) {n : ℕ} (b : Fin n → TanM xK t.G)

/- English proof (translation)
Take `⟨m, r, M, -, h2, h3, h4⟩` from `GlobalTheory.T.tangent_basis_integral_change t hx b hb`. Establish `key : ∀ i, ∃ s, s ∉ P ∧ ∃ (k : ℕ) (a : Fin n → 𝓞 K), r i ^ k • s • c = ∑ j, a j • M i j` using `fun i => by`. Distinguish the cases in `hi : r i ∈ P`. Conclude with `exists_mul_pow_mem P hi (h2 i).1 _ (h2 i).2 c`. Establish `h1 : spMap (RingHom.id K) ≫ xK = xK`.

Rewrite using `[show spMap (RingHom.id K) = 𝟙 _ from Spec.map_id _, Category.id_comp]`. Take `⟨a, ha⟩` from `h4 i _ (algebraMap (𝓞 K) (Localization.AtPrime P)) (IsLocalization.map_units _ (⟨r i, hi⟩ : P.primeCompl)) K κ (RingHom.id K) hκ xK h1 _ (isTan_tv v)`. Establish `hid : (fun q => bcTan (RingHom.id K) h1 (b q)) = b` using `funext fun q => tan_ext (by`. Rewrite using `[left_bcTan]`. Establish `: dualMap (RingHom.id K) = RingHom.id _`.

Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [dualMap]`. Rewrite using `[this, show spMap (RingHom.id (DualNumber K)) = 𝟙 _ from Spec.map_id _, Category.id_comp])`. Rewrite `ha` using `[hid]`. Establish `h5` using `hc.symm.trans (tan_ext (v := bcTan κ e v) ha)`.

Establish `h6 : c = ∑ s, κ (a s) • M i s` using `funext (Fintype.linearIndependent_iffₛ.1 hb.1 _ _ h5)`. Take `⟨s, hs, a', ha'⟩` from `exists_mul_mem P κ hκ (M i) a`. Conclude with `⟨s, hs, 0, a', by rw [pow_zero, one_smul, h6, ha']⟩`. Use `choose s hs k a ha using key`. Use `⟨∏ i, s i, P.primeCompl.prod_mem fun i _ => hs i, (h3 _).2 fun i => ?_⟩` and prove the remaining obligations.

Use `⟨k i, fun j => (∏ i' ∈ Finset.univ.erase i, s i') * a i j, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, smul_comm, ha, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => (mul_smul _ _ _).symm`.
-/
theorem exists_smul_mem_lieCoordLat (hb : TanBasis t b) (P : Ideal (𝓞 K)) [hP : P.IsPrime]
    (κ : Localization.AtPrime P →+* K) (hκ : κ.comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K)
    (e : spMap κ ≫ spMap (algebraMap (𝓞 K) (Localization.AtPrime P)) ≫ xO = xK)
    (v : TanM (spMap (algebraMap (𝓞 K) (Localization.AtPrime P)) ≫ xO) t.G) (c : Fin n → K)
    (hc : bcTan κ e v = ∑ i, c i • b i) : ∃ s, s ∉ P ∧ s • c ∈ lieCoordLat t hx b := by
  obtain ⟨m, r, M, -, h2, h3, h4⟩ := GlobalTheory.T.tangent_basis_integral_change t hx b hb
  have key : ∀ i, ∃ s, s ∉ P ∧ ∃ (k : ℕ) (a : Fin n → 𝓞 K), r i ^ k • s • c = ∑ j, a j • M i j := fun i => by
    by_cases hi : r i ∈ P
    · exact exists_mul_pow_mem P hi (h2 i).1 _ (h2 i).2 c
    · have h1 : spMap (RingHom.id K) ≫ xK = xK := by
        rw [show spMap (RingHom.id K) = 𝟙 _ from Spec.map_id _, Category.id_comp]
      obtain ⟨a, ha⟩ := h4 i _ (algebraMap (𝓞 K) (Localization.AtPrime P))
        (IsLocalization.map_units _ (⟨r i, hi⟩ : P.primeCompl)) K κ (RingHom.id K) hκ xK h1 _ (isTan_tv v)
      have hid : (fun q => bcTan (RingHom.id K) h1 (b q)) = b := funext fun q => tan_ext (by
        rw [left_bcTan]
        have : dualMap (RingHom.id K) = RingHom.id _ := by
          refine RingHom.ext fun z => ?_
          ext <;> simp [dualMap]
        rw [this, show spMap (RingHom.id (DualNumber K)) = 𝟙 _ from Spec.map_id _, Category.id_comp])
      rw [hid] at ha
      have h5 := hc.symm.trans (tan_ext (v := bcTan κ e v) ha)
      have h6 : c = ∑ s, κ (a s) • M i s := funext (Fintype.linearIndependent_iffₛ.1 hb.1 _ _ h5)
      obtain ⟨s, hs, a', ha'⟩ := exists_mul_mem P κ hκ (M i) a
      exact ⟨s, hs, 0, a', by rw [pow_zero, one_smul, h6, ha']⟩
  choose s hs k a ha using key
  refine ⟨∏ i, s i, P.primeCompl.prod_mem fun i _ => hs i, (h3 _).2 fun i => ?_⟩
  classical
  refine ⟨k i, fun j => (∏ i' ∈ Finset.univ.erase i, s i') * a i j, ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, smul_comm, ha, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => (mul_smul _ _ _).symm

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (j : K →+* C) {xC : Sp C ⟶ X}
  (hC : spMap j ≫ xK = xC)

/- English proof (translation)
Take `⟨b', hb'⟩` from `GlobalTheory.DRFlag.exists_basis_tanPull j hC (Module.Basis.mk hb.1 hb.2.ge)`. Establish `: (fun i => bcTan j hC (b i)) = b'` using `funext fun i => by`. Rewrite using `[hb', Module.Basis.mk_apply]`. Conclude with `tan_ext rfl`. Rewrite using `[TanIndep, this]`.

Conclude with `b'.linearIndependent`.
-/
theorem indep (hb : TanBasis t b) : TanIndep t (fun i => bcTan j hC (b i)) := by
  obtain ⟨b', hb'⟩ := GlobalTheory.DRFlag.exists_basis_tanPull j hC (Module.Basis.mk hb.1 hb.2.ge)
  have : (fun i => bcTan j hC (b i)) = b' := funext fun i => by
    rw [hb', Module.Basis.mk_apply]
    exact tan_ext rfl
  rw [TanIndep, this]
  exact b'.linearIndependent

/- English proof (translation)
Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => map_smulₛₗ _ _ _`.
-/
theorem bc_comb (c : Fin n → K) : bcTan j hC (∑ i, c i • b i) = ∑ i, j (c i) • bcTan j hC (b i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smulₛₗ _ _ _

/- English proof (translation)
Take `⟨ψ, hψ⟩` from `exists_int_hom j`. Establish `e : spMap (intO C).subtype ≫ spMap ψ ≫ xO = xC`. Rewrite using `[← Category.assoc, spMap_comp', hψ, ← spMap_comp', Category.assoc, hx, hC]`. Establish `key : ∃ v : TanM (spMap ψ ≫ xO) t.G, bcTan (intO C).subtype e v = ∑ i, d i • bcTan j hC (b i)`. Proceed by induction on `hd using Submodule.span_induction with`.

Consider the case `mem _ h`. Take `⟨c, ⟨w, hw⟩, rfl⟩` from `h`. Establish `e' : spMap (j.comp (algebraMap (𝓞 K) K)) ≫ xO = xC` using `by rw [← spMap_comp', Category.assoc, hx, hC]`. Use `⟨bcTan ψ rfl w, ?_⟩` and prove the remaining obligations. Establish `h1` using `bcTan_bcTan t _ _ hψ rfl e e' w`.

Establish `h2` using `bcTan_bcTan t _ _ rfl hx hC e' w`. Rewrite `h2` using `[hw, bc_comb]`. Conclude with `h1.trans h2.symm`. Consider the case `zero => exact ⟨0, by simp only [map_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero]⟩`. Consider the case `add _ _ _ _ h h'`.

Take `⟨v, hv⟩` from `h`. Take `⟨v', hv'⟩` from `h'`. Use `⟨v + v', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hv, hv', ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm`.

Consider the case `smul a _ _ h`. Take `⟨v, hv⟩` from `h`. Use `⟨a • v, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, hv, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => (mul_smul (a : C) _ _).symm`.

Take `⟨v, hv⟩` from `key`. Establish `h : spMap (dualMap (intO C).subtype) ≫ (tv v).left = combLeft t (fun i => bcTan j hC (b i)) d` using `(left_bcTan _ e v).symm.trans (congrArg (fun z => (tv z).left) hv)`. Conclude with `⟨spMap ψ ≫ xO, e, (tv v).left, isTan_tv v, h⟩`.
-/
theorem mem_of_latC {d : Fin n → C} (hd : d ∈ latC j (lieCoordLat t hx b)) :
    combLeft t (fun i => bcTan j hC (b i)) d ∈ latDR t xC := by
  obtain ⟨ψ, hψ⟩ := exists_int_hom j
  have e : spMap (intO C).subtype ≫ spMap ψ ≫ xO = xC := by
    rw [← Category.assoc, spMap_comp', hψ, ← spMap_comp', Category.assoc, hx, hC]
  have key : ∃ v : TanM (spMap ψ ≫ xO) t.G, bcTan (intO C).subtype e v = ∑ i, d i • bcTan j hC (b i) := by
    induction hd using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨c, ⟨w, hw⟩, rfl⟩ := h
      have e' : spMap (j.comp (algebraMap (𝓞 K) K)) ≫ xO = xC := by rw [← spMap_comp', Category.assoc, hx, hC]
      refine ⟨bcTan ψ rfl w, ?_⟩
      have h1 := bcTan_bcTan t _ _ hψ rfl e e' w
      have h2 := bcTan_bcTan t _ _ rfl hx hC e' w
      rw [hw, bc_comb] at h2
      exact h1.trans h2.symm
    | zero => exact ⟨0, by simp only [map_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero]⟩
    | add _ _ _ _ h h' =>
      obtain ⟨v, hv⟩ := h
      obtain ⟨v', hv'⟩ := h'
      refine ⟨v + v', ?_⟩
      rw [map_add, hv, hv', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm
    | smul a _ _ h =>
      obtain ⟨v, hv⟩ := h
      refine ⟨a • v, ?_⟩
      rw [map_smulₛₗ, hv, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (mul_smul (a : C) _ _).symm
  obtain ⟨v, hv⟩ := key
  have h : spMap (dualMap (intO C).subtype) ≫ (tv v).left = combLeft t (fun i => bcTan j hC (b i)) d :=
    (left_bcTan _ e v).symm.trans (congrArg (fun z => (tv z).left) hv)
  exact ⟨spMap ψ ≫ xO, e, (tv v).left, isTan_tv v, h⟩

/- English proof (translation)
Take `⟨ψ, hψ⟩` from `exists_int_hom j`. Use `haveI := GlobalTheory.LatDRFree.intO_isLocalRing C`. Set `P : Ideal (𝓞 K)` to `(IsLocalRing.maximalIdeal ↥(intO C)).comap ψ`. Establish `hu : ∀ s, s ∉ P → IsUnit (ψ s)` using `fun s hs => by`. Assume the negation of the conclusion as `h`.

Conclude with `hs h`. Set `χ : Localization.AtPrime P →+* ↥(intO C)` to `IsLocalization.lift (M := P.primeCompl) fun y => hu y.1 y.2`. Establish `hχ : χ.comp (algebraMap (𝓞 K) _) = ψ` using `IsLocalization.lift_comp _`. Set `κ : Localization.AtPrime P →+* K` to `IsLocalization.lift (M := P.primeCompl) (g := algebraMap (𝓞 K) K) fun y => Ne.isUnit fun h => y.2 (by`. Establish `: y.1 = 0` using `(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 h`.

Rewrite using `[this]`. Conclude with `P.zero_mem)`. Establish `hκ : κ.comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K` using `IsLocalization.lift_comp _`. Establish `hc : (intO C).subtype.comp χ = j.comp κ` using `IsLocalization.ringHom_ext P.primeCompl (by`. Rewrite using `[RingHom.comp_assoc, RingHom.comp_assoc, hχ, hκ, hψ])`.

Establish `eK : spMap κ ≫ spMap (algebraMap (𝓞 K) (Localization.AtPrime P)) ≫ xO = xK`. Rewrite using `[← Category.assoc, spMap_comp', hκ, hx]`. Establish `e' : spMap (j.comp κ) ≫ spMap (algebraMap (𝓞 K) (Localization.AtPrime P)) ≫ xO = xC`. Rewrite using `[← spMap_comp', Category.assoc, eK, hC]`. Establish `e : spMap (intO C).subtype ≫ spMap χ ≫ spMap (algebraMap (𝓞 K) (Localization.AtPrime P)) ≫ xO = xC`.

Rewrite using `[← Category.assoc, spMap_comp', hc, e']`. Take `⟨xO', hxO', vO, hv, rfl⟩` from `hw`. Use `GlobalTheory.LatDRCrd.isDominant_spMap_of_injective (intO C).subtype Subtype.val_injective` as an intermediate fact. Take `rfl : xO' = _` from `ext_of_isDominant (spMap (intO C).subtype) (hxO'.trans e.symm)`. Take `⟨m, D, hD, hbas⟩` from `GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t (Localization.AtPrime P) (spMap (algebraMap (𝓞 K) (Localization.AtPrime P)) ≫ xO)`.

Take `⟨a, ha, -⟩` from `hbas _ χ vO hv`. Establish `h1 : tanOf hv = ∑ q, a q • bcTan χ rfl (tanOf (hD q))` using `(GlobalTheory.LieMet.isComb_iff (fun q => bcTan χ rfl (tanOf (hD q))) a (tanOf hv)).1 ha`. Establish `h2 : ∀ q, ∃ c : Fin n → K, ∑ i, c i • b i = bcTan κ eK (tanOf (hD q))` using `fun q => (Submodule.mem_span_range_iff_exists_fun K).1 (hb.2.ge Submodule.mem_top)`. Use `choose c hcq using h2`. Use `⟨∑ q, a q • fun i => j (c q i), Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_, ?_⟩` and prove the remaining obligations.

Take `⟨s, hs, hm⟩` from `exists_smul_mem_lieCoordLat t hx b hb P κ hκ eK _ _ (hcq q).symm`. Take `⟨u, hu'⟩` from `(hu s hs).exists_left_inv`. Establish `h3 : (fun i => j (c q i)) = u • fun i => j ((s • c q) i)` using `funext fun i => by`. Establish `h4 : j (algebraMap (𝓞 K) K s) = (ψ s : C)` using `(RingHom.congr_fun hψ s).symm`. Establish `h5 : (u : C) * (ψ s : C) = 1` using `congrArg Subtype.val hu'`.

Use `show _ = (u : C) * j (s • c q i)`. Rewrite using `[Algebra.smul_def, map_mul, h4, ← _root_.mul_assoc, h5, _root_.one_mul]`. Rewrite using `[h3]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm, rfl⟩)`. Establish `h6 : bcTan (intO C).subtype e (tanOf hv) = ∑ i, (∑ q, a q • fun i => j (c q i)) i • bcTan j hC (b i)`.

Rewrite using `[h1, map_sum]`. Simplify using `only [Finset.sum_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, bcTan_bcTan t _ _ hc _ _ e', ← bcTan_bcTan t _ _ rfl eK hC e', ← hcq, bc_comb, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => (mul_smul _ _ _).symm`. Conclude with `congrArg (fun z => (tv z).left) h6`.
-/
theorem exists_latC [X.IsSeparated] (hb : TanBasis t b) {w : Sp (DualNumber C) ⟶ t.G.left} (hw : w ∈ latDR t xC) :
    ∃ d ∈ latC j (lieCoordLat t hx b), w = combLeft t (fun i => bcTan j hC (b i)) d := by
  obtain ⟨ψ, hψ⟩ := exists_int_hom j
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing C
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal ↥(intO C)).comap ψ
  have hu : ∀ s, s ∉ P → IsUnit (ψ s) := fun s hs => by
    by_contra h
    exact hs h
  let χ : Localization.AtPrime P →+* ↥(intO C) := IsLocalization.lift (M := P.primeCompl) fun y => hu y.1 y.2
  have hχ : χ.comp (algebraMap (𝓞 K) _) = ψ := IsLocalization.lift_comp _
  let κ : Localization.AtPrime P →+* K := IsLocalization.lift (M := P.primeCompl) (g := algebraMap (𝓞 K) K) fun y =>
    Ne.isUnit fun h => y.2 (by
      have : y.1 = 0 := (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 h
      rw [this]; exact P.zero_mem)
  have hκ : κ.comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K := IsLocalization.lift_comp _
  have hc : (intO C).subtype.comp χ = j.comp κ := IsLocalization.ringHom_ext P.primeCompl (by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hχ, hκ, hψ])
  have eK : spMap κ ≫ spMap (algebraMap (𝓞 K) (Localization.AtPrime P)) ≫ xO = xK := by
    rw [← Category.assoc, spMap_comp', hκ, hx]
  have e' : spMap (j.comp κ) ≫ spMap (algebraMap (𝓞 K) (Localization.AtPrime P)) ≫ xO = xC := by
    rw [← spMap_comp', Category.assoc, eK, hC]
  have e : spMap (intO C).subtype ≫ spMap χ ≫ spMap (algebraMap (𝓞 K) (Localization.AtPrime P)) ≫ xO = xC := by
    rw [← Category.assoc, spMap_comp', hc, e']
  obtain ⟨xO', hxO', vO, hv, rfl⟩ := hw
  have := GlobalTheory.LatDRCrd.isDominant_spMap_of_injective (intO C).subtype Subtype.val_injective
  obtain rfl : xO' = _ := ext_of_isDominant (spMap (intO C).subtype) (hxO'.trans e.symm)
  obtain ⟨m, D, hD, hbas⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t (Localization.AtPrime P)
    (spMap (algebraMap (𝓞 K) (Localization.AtPrime P)) ≫ xO)
  obtain ⟨a, ha, -⟩ := hbas _ χ vO hv
  have h1 : tanOf hv = ∑ q, a q • bcTan χ rfl (tanOf (hD q)) := (GlobalTheory.LieMet.isComb_iff (fun q => bcTan χ rfl (tanOf (hD q))) a (tanOf hv)).1 ha
  have h2 : ∀ q, ∃ c : Fin n → K, ∑ i, c i • b i = bcTan κ eK (tanOf (hD q)) := fun q =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hb.2.ge Submodule.mem_top)
  choose c hcq using h2
  refine ⟨∑ q, a q • fun i => j (c q i), Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_, ?_⟩
  · obtain ⟨s, hs, hm⟩ := exists_smul_mem_lieCoordLat t hx b hb P κ hκ eK _ _ (hcq q).symm
    obtain ⟨u, hu'⟩ := (hu s hs).exists_left_inv
    have h3 : (fun i => j (c q i)) = u • fun i => j ((s • c q) i) := funext fun i => by
      have h4 : j (algebraMap (𝓞 K) K s) = (ψ s : C) := (RingHom.congr_fun hψ s).symm
      have h5 : (u : C) * (ψ s : C) = 1 := congrArg Subtype.val hu'
      show _ = (u : C) * j (s • c q i)
      rw [Algebra.smul_def, map_mul, h4, ← _root_.mul_assoc, h5, _root_.one_mul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm, rfl⟩)
  · have h6 : bcTan (intO C).subtype e (tanOf hv) =
        ∑ i, (∑ q, a q • fun i => j (c q i)) i • bcTan j hC (b i) := by
      rw [h1, map_sum]
      simp only [Finset.sum_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smulₛₗ, bcTan_bcTan t _ _ hc _ _ e', ← bcTan_bcTan t _ _ rfl eK hC e', ← hcq, bc_comb, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (mul_smul _ _ _).symm
    exact congrArg (fun z => (tv z).left) h6

/- English proof (translation)
Introduce `E _ _ _ H X _ t K _ _ xO xK hx n b hb C _ _ j xC hC`. Use `⟨indep t b j hC hb, fun w => ⟨exists_latC t hx b j hC hb, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨d, hd, rfl⟩`. Conclude with `mem_of_latC t hx b j hC hd`.
-/
theorem latDR_eq_latC : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} [X.IsSeparated] (t : SAB H X) {K : Type} [Field K] [NumberField K] {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X} (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) {n : ℕ} (b : Fin n → TanM xK t.G), TanBasis t b → ∀ {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (j : K →+* C) {xC : Sp C ⟶ X} (hC : spMap j ≫ xK = xC), TanIndep t (fun i => bcTan j hC (b i)) ∧ ∀ w, w ∈ latDR t xC ↔ ∃ d ∈ latC j (lieCoordLat t hx b), w = combLeft t (fun i => bcTan j hC (b i)) d := by
  intro E _ _ _ H X _ t K _ _ xO xK hx n b hb C _ _ j xC hC
  refine ⟨indep t b j hC hb, fun w => ⟨exists_latC t hx b j hC hb, ?_⟩⟩
  rintro ⟨d, hd, rfl⟩
  exact mem_of_latC t hx b j hC hd

end GlobalTheory.LatDRSpan

end

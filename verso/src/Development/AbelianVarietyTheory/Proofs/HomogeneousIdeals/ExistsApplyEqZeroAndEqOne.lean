import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.PowCardLeNormProd

namespace GlobalTheory.AffinePoints

open Topology Filter Set Polynomial

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

/- English proof (translation)
Use `letI : Algebra A B := φ.toRingHom.toAlgebra`. Use `haveI : Algebra.IsIntegral A B := ⟨hφ⟩`. Establish `hsurj : Function.Surjective p` using `fun c => ⟨algebraMap K A c, by simp⟩`. Use `haveI : (RingHom.ker p).IsMaximal := RingHom.ker_isMaximal_of_surjective p hsurj`. Take `⟨Q, hQ, hQp⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) (RingHom.ker p) hp`.

Establish `hcomp : ∀ a, Ideal.Quotient.mk Q (φ a) = algebraMap K (B ⧸ Q) (p a)`. Introduce `a`. Establish `: a - algebraMap K A (p a) ∈ Q.comap (algebraMap A B)`. Rewrite using `[hQp]`. Simplify using `[RingHom.mem_ker]`.

Establish `h2 : φ (a - algebraMap K A (p a)) ∈ Q` using `this`. Rewrite `h2` using `[map_sub, AlgHom.commutes]`. Conclude with `Ideal.Quotient.eq.2 h2`. Use `haveI : Algebra.IsIntegral K (B ⧸ Q) := ⟨fun x => by`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Take `⟨h, hm, hb⟩` from `hφ b`. Use `⟨h.map p.toRingHom, hm.map _, ?_⟩` and prove the remaining obligations. Establish `: (algebraMap K (B ⧸ Q)).comp p.toRingHom = (Ideal.Quotient.mk Q).comp φ.toRingHom`. Use extensionality with `a`. Conclude with `(hcomp a).symm`.

Rewrite using `[eval₂_map, this, ← hom_eval₂, hb, map_zero]⟩`. Set `e : K ≃ₐ[K] (B ⧸ Q)` to `AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ Q)) IsAlgClosed.algebraMap_bijective_of_isIntegral`. Use `⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K Q), ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `e.symm (Ideal.Quotient.mk Q (φ a)) = p a`.

Rewrite using `[hcomp, AlgEquiv.commutes]`. Both sides reduce to the same expression.
-/
theorem exists_comap_eq_of_isIntegral {K A B : Type*} [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (φ : A →ₐ[K] B) (hφ : φ.toRingHom.IsIntegral)
    (p : A →ₐ[K] K) (hp : ∀ a, φ a = 0 → p a = 0) : ∃ q : B →ₐ[K] K, comap φ q = p := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  have hsurj : Function.Surjective p := fun c => ⟨algebraMap K A c, by simp⟩
  haveI : (RingHom.ker p).IsMaximal := RingHom.ker_isMaximal_of_surjective p hsurj
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) (RingHom.ker p) hp
  have hcomp : ∀ a, Ideal.Quotient.mk Q (φ a) = algebraMap K (B ⧸ Q) (p a) := by
    intro a
    have : a - algebraMap K A (p a) ∈ Q.comap (algebraMap A B) := by
      rw [hQp]; simp [RingHom.mem_ker]
    have h2 : φ (a - algebraMap K A (p a)) ∈ Q := this
    rw [map_sub, AlgHom.commutes] at h2
    exact Ideal.Quotient.eq.2 h2
  haveI : Algebra.IsIntegral K (B ⧸ Q) := ⟨fun x => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨h, hm, hb⟩ := hφ b
    refine ⟨h.map p.toRingHom, hm.map _, ?_⟩
    have : (algebraMap K (B ⧸ Q)).comp p.toRingHom = (Ideal.Quotient.mk Q).comp φ.toRingHom := by
      ext a; exact (hcomp a).symm
    rw [eval₂_map, this, ← hom_eval₂, hb, map_zero]⟩
  let e : K ≃ₐ[K] (B ⧸ Q) := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ Q))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K Q), ?_⟩
  ext a
  change e.symm (Ideal.Quotient.mk Q (φ a)) = p a
  rw [hcomp, AlgEquiv.commutes]; rfl

/- English proof (translation)
Introduce `p` and use `exists_comap_eq_of_isIntegral φ hφ p fun a ha => by rw [(injective_iff_map_eq_zero φ).1 hinj a ha, map_zero]`.
-/
theorem surjective_comap_of_isIntegral {K A B : Type*} [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (φ : A →ₐ[K] B) (hφ : φ.toRingHom.IsIntegral)
    (hinj : Function.Injective φ) :
    Function.Surjective (comap φ : (B →ₐ[K] K) → (A →ₐ[K] K)) := fun p =>
  exists_comap_eq_of_isIntegral φ hφ p fun a ha => by
    rw [(injective_iff_map_eq_zero φ).1 hinj a ha, map_zero]

/- English proof (translation)
Use `letI : Algebra A B := φ.toRingHom.toAlgebra`. Use `letI : Algebra A K := p.toRingHom.toAlgebra`. Use `haveI : Module.Finite A B := hφ`. Set `F : ((comap φ : (B →ₐ[R] K) → (A →ₐ[R] K)) ⁻¹' {p}) → (B →ₐ[A] K)` to `fun q => { q.1.toRingHom with commutes' := fun a => DFunLike.congr_fun q.2 a }`. Use `Set.finite_coe_iff.1 (Finite.of_injective F fun q q' h => ?_)` and prove the remaining obligations.

Use extensionality with `b`. Conclude with `DFunLike.congr_fun h b`.
-/
theorem finite_fiber_comap {R A B K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [Field K] [Algebra R K] (φ : A →ₐ[R] B) (hφ : φ.Finite) (p : A →ₐ[R] K) :
    ((comap φ : (B →ₐ[R] K) → (A →ₐ[R] K)) ⁻¹' {p}).Finite := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Algebra A K := p.toRingHom.toAlgebra
  haveI : Module.Finite A B := hφ
  let F : ((comap φ : (B →ₐ[R] K) → (A →ₐ[R] K)) ⁻¹' {p}) → (B →ₐ[A] K) := fun q =>
    { q.1.toRingHom with commutes' := fun a => DFunLike.congr_fun q.2 a }
  refine Set.finite_coe_iff.1 (Finite.of_injective F fun q q' h => ?_)
  ext b
  exact DFunLike.congr_fun h b

/- English proof (translation)
Establish `h1` using `ht.norm_lt_cauchyBound hm.ne_zero`. Establish `h2 : h.cauchyBound ≤ ∑ i ∈ Finset.range h.natDegree, ‖h.coeff i‖₊ + 1`. Simplify using `only [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, add_le_add_iff_right]`. Conclude with `Finset.sup_le fun i hi => Finset.single_le_sum (f := fun i => ‖h.coeff i‖₊) (fun _ _ => zero_le) hi`. Establish `h3` using `h1.le.trans h2`.

Simplify `NNReal.coe_le_coe.2 h3` using `[NNReal.coe_sum]`.
-/
theorem norm_le_of_isRoot_monic {h : ℂ[X]} (hm : h.Monic) {t : ℂ} (ht : h.IsRoot t) :
    ‖t‖ ≤ ∑ i ∈ Finset.range h.natDegree, ‖h.coeff i‖ + 1 := by
  have h1 := ht.norm_lt_cauchyBound hm.ne_zero
  have h2 : h.cauchyBound ≤ ∑ i ∈ Finset.range h.natDegree, ‖h.coeff i‖₊ + 1 := by
    simp only [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, add_le_add_iff_right]
    exact Finset.sup_le fun i hi =>
      Finset.single_le_sum (f := fun i => ‖h.coeff i‖₊) (fun _ _ => zero_le) hi
  have h3 := h1.le.trans h2
  simpa [NNReal.coe_sum] using NNReal.coe_le_coe.2 h3

/- English proof (translation)
Use `isProperMap_iff_ultrafilter_of_t2.2 ⟨continuous_comap φ, fun 𝒰 p hp => ?_⟩` and prove the remaining obligations. Establish `hlim : ∀ b : B, ∃ t : ℂ, Tendsto (fun q : B →ₐ[ℂ] ℂ => q b) 𝒰 (𝓝 t)`. Introduce `b`. Take `⟨h, hm, hb⟩` from `hφ b`. Set `M : (A →ₐ[ℂ] ℂ) → ℝ` to `fun r => ∑ i ∈ Finset.range h.natDegree, ‖r (h.coeff i)‖ + 1`.

Establish `hM : Continuous M` using `(continuous_finset_sum _ fun i _ => (continuous_eval _).norm).add continuous_const`. Establish `hbd : ∀ q : B →ₐ[ℂ] ℂ, ‖q b‖ ≤ M (comap φ q)`. Introduce `q`. Establish `hr : (h.map (comap φ q).toRingHom).IsRoot (q b)`. Establish `: (comap φ q).toRingHom = q.toRingHom.comp φ.toRingHom` using `rfl`.

Rewrite using `[IsRoot, eval_map, this]`. Express the relevant statement in the definitionally equal form `eval₂ _ (q.toRingHom b) h = 0`. Rewrite using `[← hom_eval₂, hb, map_zero]`. Use `norm_le_of_isRoot_monic (hm.map _) hr` as an intermediate fact. Simplify `this` using `[hm.natDegree_map, M]`.

Establish `hev : ∀ᶠ q in (𝒰 : Filter (B →ₐ[ℂ] ℂ)), q b ∈ Metric.closedBall (0 : ℂ) (M p + 1)` using `by filter_upwards [((hM.tendsto p).comp hp).eventually (gt_mem_nhds (lt_add_one (M p)))] with q hq`. Conclude with `mem_closedBall_zero_iff.2 ((hbd q).trans hq.le)`. Take `⟨t, -, ht⟩` from `(isCompact_closedBall (0 : ℂ) (M p + 1)).ultrafilter_le_nhds (𝒰.map fun q : B →ₐ[ℂ] ℂ => q b) (le_principal_iff.2 hev)`. Conclude with `⟨t, ht⟩`. Use `choose u hu using hlim`.

Establish `hu' : Tendsto (fun q : B →ₐ[ℂ] ℂ => (q : B → ℂ)) 𝒰 (𝓝 u)` using `tendsto_pi_nhds.2 hu`. Take `⟨q, hq⟩` from `(isClosedEmbedding_coe (R := ℂ) (A := B) (C := ℂ)).isClosed_range.mem_of_tendsto hu' (Eventually.of_forall fun q => ⟨q, rfl⟩)`. Use `⟨q, ?_⟩` and prove the remaining obligations. Rewrite using `[← tendsto_id', tendsto_nhds_iff]`. Introduce `b`.

Rewrite using `[show q b = u b from congrFun hq b]`. Conclude with `hu b`.
-/
theorem isProperMap_comap (φ : A →ₐ[ℂ] B) (hφ : φ.toRingHom.IsIntegral) :
    IsProperMap (comap φ : (B →ₐ[ℂ] ℂ) → (A →ₐ[ℂ] ℂ)) := by
  refine isProperMap_iff_ultrafilter_of_t2.2 ⟨continuous_comap φ, fun 𝒰 p hp => ?_⟩
  have hlim : ∀ b : B, ∃ t : ℂ, Tendsto (fun q : B →ₐ[ℂ] ℂ => q b) 𝒰 (𝓝 t) := by
    intro b
    obtain ⟨h, hm, hb⟩ := hφ b
    let M : (A →ₐ[ℂ] ℂ) → ℝ := fun r => ∑ i ∈ Finset.range h.natDegree, ‖r (h.coeff i)‖ + 1
    have hM : Continuous M :=
      (continuous_finset_sum _ fun i _ => (continuous_eval _).norm).add continuous_const
    have hbd : ∀ q : B →ₐ[ℂ] ℂ, ‖q b‖ ≤ M (comap φ q) := by
      intro q
      have hr : (h.map (comap φ q).toRingHom).IsRoot (q b) := by
        have : (comap φ q).toRingHom = q.toRingHom.comp φ.toRingHom := rfl
        rw [IsRoot, eval_map, this]
        change eval₂ _ (q.toRingHom b) h = 0
        rw [← hom_eval₂, hb, map_zero]
      have := norm_le_of_isRoot_monic (hm.map _) hr
      simpa [hm.natDegree_map, M] using this
    have hev : ∀ᶠ q in (𝒰 : Filter (B →ₐ[ℂ] ℂ)), q b ∈ Metric.closedBall (0 : ℂ) (M p + 1) := by
      filter_upwards [((hM.tendsto p).comp hp).eventually (gt_mem_nhds (lt_add_one (M p)))]
        with q hq
      exact mem_closedBall_zero_iff.2 ((hbd q).trans hq.le)
    obtain ⟨t, -, ht⟩ := (isCompact_closedBall (0 : ℂ) (M p + 1)).ultrafilter_le_nhds
      (𝒰.map fun q : B →ₐ[ℂ] ℂ => q b) (le_principal_iff.2 hev)
    exact ⟨t, ht⟩
  choose u hu using hlim
  have hu' : Tendsto (fun q : B →ₐ[ℂ] ℂ => (q : B → ℂ)) 𝒰 (𝓝 u) := tendsto_pi_nhds.2 hu
  obtain ⟨q, hq⟩ := (isClosedEmbedding_coe (R := ℂ) (A := B) (C := ℂ)).isClosed_range.mem_of_tendsto
    hu' (Eventually.of_forall fun q => ⟨q, rfl⟩)
  refine ⟨q, ?_⟩
  rw [← tendsto_id', tendsto_nhds_iff]
  intro b
  rw [show q b = u b from congrFun hq b]
  exact hu b

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.RootNormBound.exists_root_norm_lt`. Consider the case `exact _root_.GlobalTheory.RootNormBound.exists_root_norm_lt`. Consider the case `(apply _root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.RootNormBound.exists_root_norm_lt ..)`.
-/
theorem exists_isRoot_norm_lt {h : ℂ[X]} (hm : h.Monic) {ε : ℝ} (hε : 0 ≤ ε)
    (h0 : ‖h.coeff 0‖ < ε ^ h.natDegree) : ∃ t, h.IsRoot t ∧ ‖t‖ < ε := by
  first
  | exact @_root_.GlobalTheory.RootNormBound.exists_root_norm_lt
  | exact _root_.GlobalTheory.RootNormBound.exists_root_norm_lt
  | (apply _root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootNormBound.exists_root_norm_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootNormBound.exists_root_norm_lt ..)

/- English proof (translation)
Establish `: ∀ q ∈ S, ∃ e : A, p e = 1 ∧ q e = 0`. Introduce `q hq`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, p b ≠ q b := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hp (by rwa [AlgHom.ext h])`. Use `⟨(p b - q b)⁻¹ • (b - algebraMap K A (q b)), ?_, by simp⟩` and prove the remaining obligations. Simplify using `[inv_mul_cancel₀ (sub_ne_zero.2 hb)]`. Use `choose! e he using this`. Use `⟨1 - ∏ q ∈ hS.toFinset, e q, ?_, fun q hq => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, map_one, map_prod, Finset.prod_eq_one fun q hq => (he q (by simpa using hq)).1, sub_self]`. Rewrite using `[map_sub, map_one, map_prod, Finset.prod_eq_zero (i := q) (by simpa using hq) (he q hq).2, sub_zero]`.
-/
theorem exists_apply_eq_zero_and_eq_one {K : Type*} [Field K] [Algebra K A] (p : A →ₐ[K] K)
    {S : Set (A →ₐ[K] K)} (hS : S.Finite) (hp : p ∉ S) :
    ∃ a : A, p a = 0 ∧ ∀ q ∈ S, q a = 1 := by
  classical
  have : ∀ q ∈ S, ∃ e : A, p e = 1 ∧ q e = 0 := by
    intro q hq
    obtain ⟨b, hb⟩ : ∃ b, p b ≠ q b := by
      by_contra h
      push Not at h
      exact hp (by rwa [AlgHom.ext h])
    refine ⟨(p b - q b)⁻¹ • (b - algebraMap K A (q b)), ?_, by simp⟩
    simp [inv_mul_cancel₀ (sub_ne_zero.2 hb)]
  choose! e he using this
  refine ⟨1 - ∏ q ∈ hS.toFinset, e q, ?_, fun q hq => ?_⟩
  · rw [map_sub, map_one, map_prod, Finset.prod_eq_one fun q hq => (he q (by simpa using hq)).1,
      sub_self]
  · rw [map_sub, map_one, map_prod, Finset.prod_eq_zero (i := q) (by simpa using hq) (he q hq).2,
      sub_zero]

/- English proof (translation)
Establish `hint : φ.toRingHom.IsIntegral` using `RingHom.Finite.to_isIntegral hφ`. Use `letI : Algebra A B := φ.toRingHom.toAlgebra`. Use `haveI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm`. Use `haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj`. Introduce `U hU`.

Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `_ ⟨p, hpU, rfl⟩`. Take `⟨a, hpa, ha⟩` from `exists_apply_eq_zero_and_eq_one p ((finite_fiber_comap φ hφ (comap φ p)).diff (t := U)) (fun h => h.2 hpU)`. Establish `hai : IsIntegral A a` using `hint a`. Establish `hm` using `minpoly.monic hai`.

Establish `hK : IsClosed (comap φ '' (Uᶜ ∩ {q : B →ₐ[ℂ] ℂ | ‖q a‖ ≤ 1 / 2}))` using `(isProperMap_comap φ hint).isClosedMap _ (hU.isClosed_compl.inter (isClosed_le (continuous_eval a).norm continuous_const))`. Establish `hW : IsOpen {r : A →ₐ[ℂ] ℂ | ‖r ((minpoly A a).coeff 0)‖ < (1 / 2) ^ (minpoly A a).natDegree}` using `isOpen_lt (continuous_eval _).norm continuous_const`. Use `mem_of_superset ((hK.isOpen_compl.inter hW).mem_nhds ⟨?_, ?_⟩) ?_` and prove the remaining obligations. Introduce and unpack `⟨q, ⟨hqU, hqa⟩, hq⟩`. Rewrite `hqa` using `[mem_setOf_eq, ha q ⟨hq, hqU⟩]`.

Evaluate the numerical expressions using `at hqa`. Establish `h1 : p (φ ((minpoly A a).coeff 0)) = 0`. Establish `h2 : p.toRingHom (eval₂ φ.toRingHom a (minpoly A a)) = 0`. Rewrite using `[show eval₂ φ.toRingHom a (minpoly A a) = 0 from minpoly.aeval A a, map_zero]`. Rewrite `h2` using `[hom_eval₂, show p.toRingHom a = 0 from hpa, eval₂_at_zero]`.

Conclude with `h2`. Rewrite using `[mem_setOf_eq, comap_apply, h1, norm_zero]`. Check the signs of the components of the expression. Introduce and unpack `r ⟨hrK, hrW⟩`. Take `⟨t, ht, htn⟩` from `exists_isRoot_norm_lt (h := (minpoly A a).map r.toRingHom) (hm.map _) (ε := 1 / 2) (by norm_num) (by simpa [hm.natDegree_map] using hrW)`.

Set `χ : A[X] →ₐ[ℂ] B` to `(aeval a).restrictScalars ℂ`. Establish `hχ : χ.toRingHom.IsIntegral`. Use `RingHom.IsIntegral.tower_top (C : A →+* A[X]) χ.toRingHom ?_` and prove the remaining obligations. Use `hint` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Simplify using `[χ, RingHom.algebraMap_toAlgebra]`. Take `⟨q, hq⟩` from `exists_comap_eq_of_isIntegral χ hχ (aevalTower r t) fun f hf => by`. Take `⟨k, rfl⟩` from `minpoly.isIntegrallyClosed_dvd hai (p := f) hf`. Establish `: aevalTower r t (minpoly A a) = 0`. Rewrite `ht` using `[IsRoot, eval_map]`.

Conclude with `ht`. Rewrite using `[map_mul, this, zero_mul]`. Establish `hqr : comap φ q = r`. Use extensionality with `x`. Simplify `DFunLike.congr_fun hq (C x)` using `[χ, RingHom.algebraMap_toAlgebra]`.

Establish `hqa : q a = t` using `by simpa [χ] using DFunLike.congr_fun hq X`. Use `⟨q, ?_, hqr⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hqU`. Conclude with `hrK ⟨q, ⟨hqU, by rw [mem_setOf_eq, hqa]; exact htn.le⟩, hqr⟩`.
-/
theorem isOpenMap_comap [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] (φ : A →ₐ[ℂ] B)
    (hφ : φ.Finite) (hinj : Function.Injective φ) :
    IsOpenMap (comap φ : (B →ₐ[ℂ] ℂ) → (A →ₐ[ℂ] ℂ)) := by
  have hint : φ.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hφ
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨p, hpU, rfl⟩
  obtain ⟨a, hpa, ha⟩ := exists_apply_eq_zero_and_eq_one p
    ((finite_fiber_comap φ hφ (comap φ p)).diff (t := U)) (fun h => h.2 hpU)
  have hai : IsIntegral A a := hint a
  have hm := minpoly.monic hai
  have hK : IsClosed (comap φ '' (Uᶜ ∩ {q : B →ₐ[ℂ] ℂ | ‖q a‖ ≤ 1 / 2})) :=
    (isProperMap_comap φ hint).isClosedMap _ (hU.isClosed_compl.inter
      (isClosed_le (continuous_eval a).norm continuous_const))
  have hW : IsOpen {r : A →ₐ[ℂ] ℂ |
      ‖r ((minpoly A a).coeff 0)‖ < (1 / 2) ^ (minpoly A a).natDegree} :=
    isOpen_lt (continuous_eval _).norm continuous_const
  refine mem_of_superset ((hK.isOpen_compl.inter hW).mem_nhds ⟨?_, ?_⟩) ?_
  · rintro ⟨q, ⟨hqU, hqa⟩, hq⟩
    rw [mem_setOf_eq, ha q ⟨hq, hqU⟩] at hqa
    norm_num at hqa
  · have h1 : p (φ ((minpoly A a).coeff 0)) = 0 := by
      have h2 : p.toRingHom (eval₂ φ.toRingHom a (minpoly A a)) = 0 := by
        rw [show eval₂ φ.toRingHom a (minpoly A a) = 0 from minpoly.aeval A a, map_zero]
      rw [hom_eval₂, show p.toRingHom a = 0 from hpa, eval₂_at_zero] at h2
      exact h2
    rw [mem_setOf_eq, comap_apply, h1, norm_zero]
    positivity
  · rintro r ⟨hrK, hrW⟩
    obtain ⟨t, ht, htn⟩ := exists_isRoot_norm_lt (h := (minpoly A a).map r.toRingHom) (hm.map _)
      (ε := 1 / 2) (by norm_num) (by simpa [hm.natDegree_map] using hrW)
    let χ : A[X] →ₐ[ℂ] B := (aeval a).restrictScalars ℂ
    have hχ : χ.toRingHom.IsIntegral := by
      refine RingHom.IsIntegral.tower_top (C : A →+* A[X]) χ.toRingHom ?_
      convert hint
      ext x
      simp [χ, RingHom.algebraMap_toAlgebra]
    obtain ⟨q, hq⟩ := exists_comap_eq_of_isIntegral χ hχ (aevalTower r t) fun f hf => by
      obtain ⟨k, rfl⟩ := minpoly.isIntegrallyClosed_dvd hai (p := f) hf
      have : aevalTower r t (minpoly A a) = 0 := by
        rw [IsRoot, eval_map] at ht
        exact ht
      rw [map_mul, this, zero_mul]
    have hqr : comap φ q = r := by
      ext x
      simpa [χ, RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun hq (C x)
    have hqa : q a = t := by simpa [χ] using DFunLike.congr_fun hq X
    refine ⟨q, ?_, hqr⟩
    by_contra hqU
    exact hrK ⟨q, ⟨hqU, by rw [mem_setOf_eq, hqa]; exact htn.le⟩, hqr⟩

end GlobalTheory.AffinePoints

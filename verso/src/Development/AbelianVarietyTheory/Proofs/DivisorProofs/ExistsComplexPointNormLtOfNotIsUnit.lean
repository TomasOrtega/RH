import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SpecialisationNumberFieldAndCountableValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCardLeNormProd

open Polynomial Filter Topology

namespace GlobalTheory

namespace SmallPoint

/- English proof (translation)
Use `haveI := RingHom.ker_isPrime φ`. Take `⟨Q, -, hQ, hQP⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (RingHom.ker φ) ⊥ h`. Use `haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩`. Use `letI : Algebra (R ⧸ RingHom.ker φ) Ω := (RingHom.kerLift φ).toAlgebra`. Use `haveI : FaithfulSMul (R ⧸ RingHom.ker φ) Ω := (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ)`.

Use `haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) Ω := FaithfulSMul.to_isTorsionFree _ _`. Use `haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) (B ⧸ Q) := FaithfulSMul.to_isTorsionFree _ _`. Use `haveI : Algebra.IsIntegral (R ⧸ RingHom.ker φ) (B ⧸ Q) := Algebra.IsIntegral.tower_top (R := R)`. Use `haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker φ) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic`. Set `σ : (B ⧸ Q) →ₐ[R ⧸ RingHom.ker φ] Ω` to `IsAlgClosed.lift`.

Use `⟨σ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun r => ?_⟩` and prove the remaining obligations. Conclude with `(σ.commutes (Ideal.Quotient.mk _ r)).trans (RingHom.kerLift_mk φ r)`.
-/
theorem exists_extend_of_ker_le {R B Ω : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.IsIntegral R B] [Field Ω] [IsAlgClosed Ω]
    (φ : R →+* Ω) (h : RingHom.ker (algebraMap R B) ≤ RingHom.ker φ) :
    ∃ ψ : B →+* Ω, ψ.comp (algebraMap R B) = φ := by
  haveI := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    (RingHom.ker φ) ⊥ h
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩
  letI : Algebra (R ⧸ RingHom.ker φ) Ω := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker φ) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ)
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) Ω := FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) (B ⧸ Q) := FaithfulSMul.to_isTorsionFree _ _
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker φ) (B ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := R)
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker φ) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let σ : (B ⧸ Q) →ₐ[R ⧸ RingHom.ker φ] Ω := IsAlgClosed.lift
  refine ⟨σ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun r => ?_⟩
  exact (σ.commutes (Ideal.Quotient.mk _ r)).trans (RingHom.kerLift_mk φ r)

/- English proof (translation)
Use `letI : Algebra R[X] B := (aeval u : R[X] →ₐ[R] B).toRingHom.toAlgebra`. Use `haveI : IsScalarTower R R[X] B := IsScalarTower.of_algebraMap_eq fun x => ((aeval u : R[X] →ₐ[R] B).commutes x).symm`. Use `haveI : Algebra.IsIntegral R[X] B := Algebra.IsIntegral.tower_top (R := R)`. Take `⟨φ, hφ⟩` from `exists_extend_of_ker_le (B := B) (eval₂RingHom ψ t) (fun f hf => by`. Take `⟨g, rfl⟩` from `minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral (R := R) u) (p := f) hf`.

Rewrite using `[RingHom.mem_ker, map_mul, coe_eval₂RingHom, ht, zero_mul])`. Establish `h : ∀ f : R[X], φ (aeval u f) = f.eval₂ ψ t` using `fun f => DFunLike.congr_fun hφ f`. Use `⟨φ, RingHom.ext fun r => ?_, ?_⟩` and prove the remaining obligations. Simplify using `using h (C r)`. Simplify using `using h X`.
-/
theorem exists_extend_apply_eq {R B Ω : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B]
    [Field Ω] [IsAlgClosed Ω] (ψ : R →+* Ω) (u : B) (t : Ω)
    (ht : (minpoly R u).eval₂ ψ t = 0) :
    ∃ φ : B →+* Ω, φ.comp (algebraMap R B) = ψ ∧ φ u = t := by
  letI : Algebra R[X] B := (aeval u : R[X] →ₐ[R] B).toRingHom.toAlgebra
  haveI : IsScalarTower R R[X] B :=
    IsScalarTower.of_algebraMap_eq fun x => ((aeval u : R[X] →ₐ[R] B).commutes x).symm
  haveI : Algebra.IsIntegral R[X] B := Algebra.IsIntegral.tower_top (R := R)
  obtain ⟨φ, hφ⟩ := exists_extend_of_ker_le (B := B) (eval₂RingHom ψ t) (fun f hf => by
    obtain ⟨g, rfl⟩ := minpoly.isIntegrallyClosed_dvd
      (Algebra.IsIntegral.isIntegral (R := R) u) (p := f) hf
    rw [RingHom.mem_ker, map_mul, coe_eval₂RingHom, ht, zero_mul])
  have h : ∀ f : R[X], φ (aeval u f) = f.eval₂ ψ t := fun f => DFunLike.congr_fun hφ f
  refine ⟨φ, RingHom.ext fun r => ?_, ?_⟩
  · simpa using h (C r)
  · simpa using h X

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt`. Consider the case `exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt`. Consider the case `(apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt ..)`.
-/
theorem exists_root_norm_lt {F : ℂ[X]} (hF : F.Monic) {ε : ℝ} (hε : 0 < ε)
    (h : ‖F.coeff 0‖ < ε ^ F.natDegree) : ∃ t, F.IsRoot t ∧ ‖t‖ < ε := by
  first
  | exact @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt
  | exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt
  | (apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt ..)

/- English proof (translation)
Take `⟨G, hG, hGb⟩` from `hb`. Establish `h1 : ∀ i : ℕ, ∀ᶠ s in 𝓝 (0 : ℂ), ‖(Ψ (G.coeff i)).eval s‖ < ‖(Ψ (G.coeff i)).eval 0‖ + 1` using `fun i => ((Ψ (G.coeff i)).continuous.norm.tendsto 0).eventually (gt_mem_nhds (lt_add_one _))`. Use `⟨∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖ + 1) + 1, ?_⟩` and prove the remaining obligations. Use `filter_upwards [(Finset.range G.natDegree).eventually_all.2 fun i _ => h1 i] with s hs φ hφ`. Establish `hm : (G.map ((evalRingHom s).comp Ψ)).Monic` using `hG.map _`.

Establish `hr : (G.map ((evalRingHom s).comp Ψ)).IsRoot (φ b)`. Rewrite using `[IsRoot, eval_map, ← hφ, ← hom_eval₂, hGb, map_zero]`. Establish `h2` using `hr.norm_lt_cauchyBound hm.ne_zero`. Rewrite `h2` using `[cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hG.natDegree_map]`. Establish `h3 : ((Finset.range G.natDegree).sup (fun i => ‖(G.map ((evalRingHom s).comp Ψ)).coeff i‖₊) : NNReal) ≤ ∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖₊ + 1)`.

Use `Finset.sup_le fun i hi => ?_` and prove the remaining obligations. Use `le_trans ?_ (Finset.single_le_sum (f := fun i => ‖(Ψ (G.coeff i)).eval 0‖₊ + 1) (fun _ _ => zero_le) hi)` and prove the remaining obligations. Rewrite using `[coeff_map]`. Conclude with `(hs i hi).le` after adjusting the coercions. Establish `h4` using `h2.le.trans (add_le_add_left h3 1)`.

Establish `h5` using `NNReal.coe_le_coe.2 h4`. Move the coercions through the operations in `at h5`. Conclude with `h5`.
-/
theorem exists_eventually_norm_le {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (Ψ : R →+* ℂ[X]) {b : B} (hb : IsIntegral R b) :
    ∃ M : ℝ, ∀ᶠ s in 𝓝 (0 : ℂ), ∀ φ : B →+* ℂ,
      φ.comp (algebraMap R B) = (evalRingHom s).comp Ψ → ‖φ b‖ ≤ M := by
  obtain ⟨G, hG, hGb⟩ := hb
  have h1 : ∀ i : ℕ, ∀ᶠ s in 𝓝 (0 : ℂ),
      ‖(Ψ (G.coeff i)).eval s‖ < ‖(Ψ (G.coeff i)).eval 0‖ + 1 := fun i =>
    ((Ψ (G.coeff i)).continuous.norm.tendsto 0).eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖ + 1) + 1, ?_⟩
  filter_upwards [(Finset.range G.natDegree).eventually_all.2 fun i _ => h1 i] with s hs φ hφ
  have hm : (G.map ((evalRingHom s).comp Ψ)).Monic := hG.map _
  have hr : (G.map ((evalRingHom s).comp Ψ)).IsRoot (φ b) := by
    rw [IsRoot, eval_map, ← hφ, ← hom_eval₂, hGb, map_zero]
  have h2 := hr.norm_lt_cauchyBound hm.ne_zero
  rw [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hG.natDegree_map] at h2
  have h3 : ((Finset.range G.natDegree).sup
      (fun i => ‖(G.map ((evalRingHom s).comp Ψ)).coeff i‖₊) : NNReal) ≤
      ∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖₊ + 1) := by
    refine Finset.sup_le fun i hi => ?_
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ‖(Ψ (G.coeff i)).eval 0‖₊ + 1) (fun _ _ => zero_le) hi)
    rw [coeff_map]
    exact_mod_cast (hs i hi).le
  have h4 := h2.le.trans (add_le_add_left h3 1)
  have h5 := NNReal.coe_le_coe.2 h4
  push_cast at h5
  exact h5

/- English proof (translation)
Use `choose M hM using fun i => exists_eventually_norm_le Ψ (Algebra.IsIntegral.isIntegral (R := R) (w i))`. Use `⟨∑ i, |M i|, fun ε hε => ?_⟩` and prove the remaining obligations. Establish `hint` using `Algebra.IsIntegral.isIntegral (R := R) u`. Establish `hF` using `minpoly.monic hint`. Establish `h0 : (Ψ ((minpoly R u).coeff 0)).eval 0 = 0`.

Establish `h` using `congrArg p (minpoly.aeval R u)`. Rewrite `h` using `[aeval_def, hom_eval₂, hu, eval₂_at_zero, hp, map_zero]`. Conclude with `h`. Establish `h1 : ∀ᶠ s in 𝓝 (0 : ℂ), ‖(Ψ ((minpoly R u).coeff 0)).eval s‖ < ε ^ (minpoly R u).natDegree` using `((Ψ _).continuous.norm.tendsto 0).eventually (gt_mem_nhds (by`. Simplify using `only [h0, norm_zero]`.

Use the proof step `positivity))`. Establish `h2 : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ¬ (Ψ r).IsRoot s` using `nhdsNE_le_cofinite _ (eventually_cofinite.2 (by`. Simplify using `using (Ψ r).finite_setOf_isRoot hr))`. Take `⟨s, hs2, hs1, hs3⟩` from `(h2.and ((h1.and (eventually_all.2 hM)).filter_mono nhdsWithin_le_nhds)).exists`. Take `⟨t, ht, htε⟩` from `exists_root_norm_lt (hF.map ((evalRingHom s).comp Ψ)) hε (by`.

Rewrite using `[coeff_map, hF.natDegree_map]`. Conclude with `hs1)`. Take `⟨φ, hφ, hφu⟩` from `exists_extend_apply_eq ((evalRingHom s).comp Ψ) u t (by`. Rewrite using `[IsRoot, eval_map] at ht)` and apply the resulting hypothesis. Use `⟨s, φ, hφ, hs2, hφu ▸ htε, fun i => (hs3 i φ hφ).trans ((le_abs_self _).trans ?_)⟩` and prove the remaining obligations.

Conclude with `Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)`.
-/
theorem exists_small_of_curve {R B : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B]
    (Ψ : R →+* ℂ[X]) (p : B →+* ℂ) (hp : p.comp (algebraMap R B) = (evalRingHom 0).comp Ψ)
    {n : ℕ} (w : Fin n → B) {u : B} (hu : p u = 0) {r : R} (hr : Ψ r ≠ 0) :
    ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ (s : ℂ) (φ : B →+* ℂ),
      φ.comp (algebraMap R B) = (evalRingHom s).comp Ψ ∧ (Ψ r).eval s ≠ 0 ∧ ‖φ u‖ < ε ∧
        ∀ i, ‖φ (w i)‖ ≤ M := by
  choose M hM using fun i => exists_eventually_norm_le Ψ
    (Algebra.IsIntegral.isIntegral (R := R) (w i))
  refine ⟨∑ i, |M i|, fun ε hε => ?_⟩
  have hint := Algebra.IsIntegral.isIntegral (R := R) u
  have hF := minpoly.monic hint
  have h0 : (Ψ ((minpoly R u).coeff 0)).eval 0 = 0 := by
    have h := congrArg p (minpoly.aeval R u)
    rw [aeval_def, hom_eval₂, hu, eval₂_at_zero, hp, map_zero] at h
    exact h
  have h1 : ∀ᶠ s in 𝓝 (0 : ℂ),
      ‖(Ψ ((minpoly R u).coeff 0)).eval s‖ < ε ^ (minpoly R u).natDegree :=
    ((Ψ _).continuous.norm.tendsto 0).eventually (gt_mem_nhds (by
      simp only [h0, norm_zero]
      positivity))
  have h2 : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ¬ (Ψ r).IsRoot s :=
    nhdsNE_le_cofinite _ (eventually_cofinite.2 (by
      simpa using (Ψ r).finite_setOf_isRoot hr))
  obtain ⟨s, hs2, hs1, hs3⟩ := (h2.and
    ((h1.and (eventually_all.2 hM)).filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨t, ht, htε⟩ := exists_root_norm_lt (hF.map ((evalRingHom s).comp Ψ)) hε (by
    rw [coeff_map, hF.natDegree_map]
    exact hs1)
  obtain ⟨φ, hφ, hφu⟩ := exists_extend_apply_eq ((evalRingHom s).comp Ψ) u t (by
    rwa [IsRoot, eval_map] at ht)
  refine ⟨s, φ, hφ, hs2, hφu ▸ htε, fun i => (hs3 i φ hφ).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

end SmallPoint

/- English proof (translation)
Introduce `K B _ _ _ _ _ σ n w u q hu hq`. Take `⟨d, g, hinj, hint⟩` from `exists_integral_inj_algHom_of_fg K B`. Use `letI := g.toRingHom.toAlgebra`. Use `haveI : Algebra.IsIntegral (MvPolynomial (Fin d) K) B := ⟨hint⟩`. Use `haveI : FaithfulSMul (MvPolynomial (Fin d) K) B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj`.

Use `haveI : Nontrivial (B ⧸ Ideal.span {u}) := Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])`. Take `⟨p₀, hp₀⟩` from `exists_ringHom_extend_of_finiteType K (B ⧸ Ideal.span {u}) ℂ σ`. Set `p : B →+* ℂ` to `p₀.comp (Ideal.Quotient.mk _)`. Establish `hpu : p u = 0`. Express the relevant statement in the definitionally equal form `p₀ (Ideal.Quotient.mk _ u) = 0`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self u), map_zero]`. Take `⟨r, hr, c, hc⟩` from `(Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) K) q).isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hq)`. Take `⟨z, hz⟩ : ∃ z : Fin d → ℂ, MvPolynomial.eval z (MvPolynomial.map σ r) ≠ 0` from `by by_contra! h`. Conclude with `hr (MvPolynomial.map_injective σ σ.injective (MvPolynomial.funext (by simpa using h)))`. Set `Ψ : MvPolynomial (Fin d) K →+* ℂ[X]` to `MvPolynomial.eval₂Hom (C.comp σ) fun j => C (p (g (MvPolynomial.X j))) + X * C (z j - p (g (MvPolynomial.X j)))`.

Establish `hΨ0 : p.comp (algebraMap (MvPolynomial (Fin d) K) B) = (evalRingHom 0).comp Ψ`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)` and prove the remaining obligations. Establish `: p (g (MvPolynomial.C a)) = σ a`. Rewrite using `[MvPolynomial.algHom_C]`. Conclude with `hp₀ a`.

Conclude with `this.trans (by simp [Ψ])`. Simplify using `[Ψ]`. Both sides reduce to the same expression. Establish `hΨ1 : (evalRingHom 1).comp Ψ = (MvPolynomial.eval z).comp (MvPolynomial.map σ)`. Apply the tactic sequence `refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_) <;> simp [Ψ]`.

Establish `hΨr : Ψ r ≠ 0` using `fun h => hz (by`. Use `DFunLike.congr_fun hΨ1 r` as an intermediate fact. Simplify `this.symm)` using `[h]`. Take `⟨M, hM⟩` from `SmallPoint.exists_small_of_curve Ψ p hΨ0 w hpu hΨr`. Use `⟨M, fun ε hε => ?_⟩` and prove the remaining obligations.

Take `⟨s, φ, hφ, h1, h2, h3⟩` from `hM ε hε`. Use `⟨φ, RingHom.ext fun a => ?_, fun h => h1 ?_, h2, h3⟩` and prove the remaining obligations. Use `DFunLike.congr_fun hφ (MvPolynomial.C a)` as an intermediate fact. Rewrite using `[RingHom.comp_apply, ← MvPolynomial.algHom_C g]`. Conclude with `this.trans (by simp [Ψ])`.

Use `DFunLike.congr_fun hφ r` as an intermediate fact. Rewrite `this` using `[RingHom.comp_apply, hc, map_mul, h, zero_mul]`. Conclude with `this.symm`.
-/
theorem exists_complex_point_norm_lt_of_not_isUnit :
    ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
      (σ : K →+* ℂ) (n : ℕ) (w : Fin n → B) (u q : B), ¬ IsUnit u → q ≠ 0 →
      ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ φ : B →+* ℂ, φ.comp (algebraMap K B) = σ ∧ φ q ≠ 0 ∧
        ‖φ u‖ < ε ∧ ∀ i, ‖φ (w i)‖ ≤ M := by
  intro K B _ _ _ _ _ σ n w u q hu hq
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K B
  letI := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) K) B := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin d) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Nontrivial (B ⧸ Ideal.span {u}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨p₀, hp₀⟩ := exists_ringHom_extend_of_finiteType K (B ⧸ Ideal.span {u}) ℂ σ
  let p : B →+* ℂ := p₀.comp (Ideal.Quotient.mk _)
  have hpu : p u = 0 := by
    change p₀ (Ideal.Quotient.mk _ u) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self u), map_zero]
  obtain ⟨r, hr, c, hc⟩ :=
    (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) K) q).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hq)
  obtain ⟨z, hz⟩ : ∃ z : Fin d → ℂ, MvPolynomial.eval z (MvPolynomial.map σ r) ≠ 0 := by
    by_contra! h
    exact hr (MvPolynomial.map_injective σ σ.injective
      (MvPolynomial.funext (by simpa using h)))
  let Ψ : MvPolynomial (Fin d) K →+* ℂ[X] := MvPolynomial.eval₂Hom (C.comp σ)
    fun j => C (p (g (MvPolynomial.X j))) + X * C (z j - p (g (MvPolynomial.X j)))
  have hΨ0 : p.comp (algebraMap (MvPolynomial (Fin d) K) B) = (evalRingHom 0).comp Ψ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · have : p (g (MvPolynomial.C a)) = σ a := by
        rw [MvPolynomial.algHom_C]
        exact hp₀ a
      exact this.trans (by simp [Ψ])
    · simp [Ψ]
      rfl
  have hΨ1 : (evalRingHom 1).comp Ψ = (MvPolynomial.eval z).comp (MvPolynomial.map σ) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_) <;> simp [Ψ]
  have hΨr : Ψ r ≠ 0 := fun h => hz (by
    have := DFunLike.congr_fun hΨ1 r
    simpa [h] using this.symm)
  obtain ⟨M, hM⟩ := SmallPoint.exists_small_of_curve Ψ p hΨ0 w hpu hΨr
  refine ⟨M, fun ε hε => ?_⟩
  obtain ⟨s, φ, hφ, h1, h2, h3⟩ := hM ε hε
  refine ⟨φ, RingHom.ext fun a => ?_, fun h => h1 ?_, h2, h3⟩
  · have := DFunLike.congr_fun hφ (MvPolynomial.C a)
    rw [RingHom.comp_apply, ← MvPolynomial.algHom_C g]
    exact this.trans (by simp [Ψ])
  · have := DFunLike.congr_fun hφ r
    rw [RingHom.comp_apply, hc, map_mul, h, zero_mul] at this
    exact this.symm

end GlobalTheory

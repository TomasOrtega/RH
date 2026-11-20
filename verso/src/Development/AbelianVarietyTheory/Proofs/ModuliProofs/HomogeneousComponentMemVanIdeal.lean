import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjectiveCokerOfIsLocallyConstantFinrankRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open scoped TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.FamAlg
open Module MvPolynomial GlobalTheory.Semicont

/- English proof (translation)
Establish `key : ∀ q : PrimeSpectrum R, (finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) : ℚ) = r`. Introduce `q`. Take `⟨_, ⟨f, rfl⟩, hqf, hf⟩` from `(PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1 (eventually_finrank_fiber_le (M := M) q)`. Take `⟨p, hp, hpp, hqp, hfp⟩` from `hP q.asIdeal f q.isPrime hqf`. Rewrite using `[← h ⟨p, hpp⟩ hp]`.

Use `congr 1`. Use `le_antisymm ?_ (hf (show (⟨p, hpp⟩ : PrimeSpectrum R) ∈ _ from hfp))` and prove the remaining obligations. Establish `hs : q ⤳ (⟨p, hpp⟩ : PrimeSpectrum R)` using `(PrimeSpectrum.le_iff_specializes _ _).1 hqp`. Conclude with `(hs.nhds_le_nhds.trans' (pure_le_nhds q)) (eventually_finrank_fiber_le (M := M) ⟨p, hpp⟩)`. Use `projective_of_finite_of_isLocallyConstant_finrank_fiber (IsLocallyConstant.of_constant _ fun p q => ?_)` and prove the remaining obligations.

Conclude with `(key p).trans (key q).symm` after adjusting the coercions.
-/
theorem projective_of_veryDense {R : Type} [CommRing R] [IsReduced R] {P : Set (Ideal R)} (hP : VeryDense P)
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (r : ℚ)
    (h : ∀ q : PrimeSpectrum R, q.asIdeal ∈ P →
      (finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) : ℚ) = r) :
    Module.Projective R M := by
  have key : ∀ q : PrimeSpectrum R,
      (finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) : ℚ) = r := by
    intro q
    obtain ⟨_, ⟨f, rfl⟩, hqf, hf⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1
      (eventually_finrank_fiber_le (M := M) q)
    obtain ⟨p, hp, hpp, hqp, hfp⟩ := hP q.asIdeal f q.isPrime hqf
    rw [← h ⟨p, hpp⟩ hp]
    congr 1
    refine le_antisymm ?_ (hf (show (⟨p, hpp⟩ : PrimeSpectrum R) ∈ _ from hfp))
    have hs : q ⤳ (⟨p, hpp⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hqp
    exact (hs.nhds_le_nhds.trans' (pure_le_nhds q)) (eventually_finrank_fiber_le (M := M) ⟨p, hpp⟩)
  refine projective_of_finite_of_isLocallyConstant_finrank_fiber
    (IsLocallyConstant.of_constant _ fun p q => ?_)
  exact_mod_cast (key p).trans (key q).symm

/- English proof (translation)
Rewrite using `[homogeneousSubmodule_eq_finsupp_supported]`. Conclude with `⟨basisRestrictSupport R _, fun F i => rfl⟩`.
-/
theorem exists_basis (σ R : Type) [CommRing R] (e : ℕ) :
    ∃ b : Basis {u : σ →₀ ℕ | u.degree = e} R (homogeneousSubmodule σ R e),
      ∀ F i, b.repr F i = coeff i.1 F.1 := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact ⟨basisRestrictSupport R _, fun F i => rfl⟩

/- English proof (translation)
Take `⟨b, -⟩` from `exists_basis σ K e`. Conclude with `finrank_eq_nat_card_basis b`.
-/
theorem finrank_forms (σ K : Type) [Field K] (e : ℕ) :
    finrank K (homogeneousSubmodule σ K e) = Nat.card {u : σ →₀ ℕ | u.degree = e} := by
  obtain ⟨b, -⟩ := exists_basis σ K e
  exact finrank_eq_nat_card_basis b

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_basis σ R e`. Take `⟨c, hc⟩` from `exists_basis σ K e`. Use `⟨(b.baseChange K).repr ≪≫ₗ c.repr.symm, fun F => ?_⟩` and prove the remaining obligations. Establish `: (b.baseChange K).repr (1 ⊗ₜ F) = c.repr ⟨map (algebraMap R K) F.1, IsHomogeneous.map F.2 _⟩`. Use extensionality with `i`.

Rewrite using `[Basis.baseChange_repr_tmul, hb, hc, coeff_map, Algebra.smul_def, mul_one]`. Rewrite using `[LinearEquiv.trans_apply, this, LinearEquiv.symm_apply_apply]`.
-/
theorem exists_equiv (σ R K : Type) [CommRing R] [CommRing K] [Algebra R K] (e : ℕ) :
    ∃ θ : K ⊗[R] homogeneousSubmodule σ R e ≃ₗ[K] homogeneousSubmodule σ K e,
      ∀ F, (θ (1 ⊗ₜ F)).1 = map (algebraMap R K) F.1 := by
  obtain ⟨b, hb⟩ := exists_basis σ R e
  obtain ⟨c, hc⟩ := exists_basis σ K e
  refine ⟨(b.baseChange K).repr ≪≫ₗ c.repr.symm, fun F => ?_⟩
  have : (b.baseChange K).repr (1 ⊗ₜ F) = c.repr ⟨map (algebraMap R K) F.1, IsHomogeneous.map F.2 _⟩ := by
    ext i
    rw [Basis.baseChange_repr_tmul, hb, hc, coeff_map, Algebra.smul_def, mul_one]
  rw [LinearEquiv.trans_apply, this, LinearEquiv.symm_apply_apply]

/- English proof (translation)
Use extensionality with `u`. Simplify using `only [coeff_homogeneousComponent, coeff_map]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_homogeneousComponent {σ R K : Type} [CommRing R] [CommRing K] (x : R →+* K) (e : ℕ)
    (F : MvPolynomial σ R) : homogeneousComponent e (map x F) = map x (homogeneousComponent e F) := by
  ext u
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

/- English proof (translation)
Use `Submodule.span_induction (fun G hG => Submodule.subset_span hG) (zero_mem _) (fun _ _ _ _ => add_mem) (fun a G _ hG => ?_) hF` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`. Proceed by induction on `a using MvPolynomial.induction_on' with`. Consider the case `add a b ha hb => rw [add_mul]`. Conclude with `add_mem ha hb`.

Consider the case `monomial u c`. Establish `: monomial u c = c • map x (monomial u 1)` using `by simp [smul_monomial]`. Rewrite using `[this, smul_mul_assoc]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `Submodule.span_induction ?_ (by simp) (fun _ _ _ _ h1 h2 => ?_) (fun s _ _ h1 => ?_) hG` and prove the remaining obligations.

Introduce and unpack `_ ⟨H, hH, rfl⟩`. Conclude with `Submodule.subset_span ⟨_, J.mul_mem_left (monomial u 1) hH, map_mul _ _ _⟩`. Rewrite using `[mul_add]`. Conclude with `add_mem h1 h2`. Rewrite using `[mul_smul_comm]`.

Conclude with `Submodule.smul_mem _ _ h1`.
-/
theorem mem_span_of_mem_map {σ R K : Type} [CommRing R] [CommRing K] (x : R →+* K)
    (J : Ideal (MvPolynomial σ R)) {F : MvPolynomial σ K} (hF : F ∈ J.map (map x)) :
    F ∈ Submodule.span K (map x '' (J : Set (MvPolynomial σ R))) := by
  refine Submodule.span_induction (fun G hG => Submodule.subset_span hG) (zero_mem _)
    (fun _ _ _ _ => add_mem) (fun a G _ hG => ?_) hF
  rw [smul_eq_mul]
  induction a using MvPolynomial.induction_on' with
  | add a b ha hb => rw [add_mul]; exact add_mem ha hb
  | monomial u c =>
    have : monomial u c = c • map x (monomial u 1) := by simp [smul_monomial]
    rw [this, smul_mul_assoc]
    refine Submodule.smul_mem _ _ ?_
    refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ h1 h2 => ?_) (fun s _ _ h1 => ?_) hG
    · rintro _ ⟨H, hH, rfl⟩
      exact Submodule.subset_span ⟨_, J.mul_mem_left (monomial u 1) hH, map_mul _ _ _⟩
    · rw [mul_add]; exact add_mem h1 h2
    · rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h1

attribute [local instance] MvPolynomial.gradedAlgebra in
/- English proof (translation)
The claim follows from `homogeneousComponent_mem_of_mem (Ideal.homogeneous_span _ _ fun _ hG => ⟨d, hG.1⟩) hF e`.
-/
theorem homogeneousComponent_mem_vanIdeal {σ R Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    {F : MvPolynomial σ R} (hF : F ∈ vanIdeal d p) (e : ℕ) : homogeneousComponent e F ∈ vanIdeal d p :=
  homogeneousComponent_mem_of_mem (Ideal.homogeneous_span _ _ fun _ hG => ⟨d, hG.1⟩) hF e

/- English proof (translation)
The claim follows from `(Ideal.span_le (I := RingHom.ker (eval (p h)))).2 (fun _ hG => hG.2 h) hF`.
-/
theorem eval_eq_zero_of_mem_vanIdeal {σ R Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    {F : MvPolynomial σ R} (hF : F ∈ vanIdeal d p) (h : Hh) : eval (p h) F = 0 :=
  (Ideal.span_le (I := RingHom.ker (eval (p h)))).2 (fun _ hG => hG.2 h) hF

noncomputable abbrev part {σ R : Type} [CommRing R] (J : Ideal (MvPolynomial σ R)) (e : ℕ) :
    Submodule R (homogeneousSubmodule σ R e) :=
  (J.restrictScalars R).comap (homogeneousSubmodule σ R e).subtype

noncomputable def ev {σ R Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R) :
    homogeneousSubmodule σ R d →ₗ[R] (Hh → R) :=
  LinearMap.pi fun h => (aeval (p h)).toLinearMap ∘ₗ (homogeneousSubmodule σ R d).subtype

/- English proof (translation)
Rewrite using `[← coe_aeval_eq_eval]`. Both sides reduce to the same expression.
-/
theorem ev_apply {σ R Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R) (F) (h : Hh) :
    ev d p F h = eval (p h) F.1 := by
  rw [← coe_aeval_eq_eval]
  rfl

/- English proof (translation)
Use extensionality with `F`. Prove the components needed by the constructor for the conclusion. Introduce `hF`. Conclude with `Ideal.subset_span ⟨F.2, fun h => (ev_apply d p F h).symm.trans (congrFun (LinearMap.mem_ker.1 hF) h)⟩`. Introduce `hF`.

Establish `hF' : F.1 ∈ vanIdeal d p` using `hF`. Rewrite using `[LinearMap.mem_ker]`. Use extensionality with `h`. Rewrite using `[ev_apply, eval_eq_zero_of_mem_vanIdeal d p hF' h, Pi.zero_apply]`.
-/
theorem ker_ev {σ R Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R) :
    LinearMap.ker (ev d p) = part (vanIdeal d p) d := by
  ext F
  constructor
  · intro hF
    exact Ideal.subset_span ⟨F.2, fun h => (ev_apply d p F h).symm.trans (congrFun (LinearMap.mem_ker.1 hF) h)⟩
  · intro hF
    have hF' : F.1 ∈ vanIdeal d p := hF
    rw [LinearMap.mem_ker]
    ext h
    rw [ev_apply, eval_eq_zero_of_mem_vanIdeal d p hF' h, Pi.zero_apply]

/- English proof (translation)
Establish `h1 : part (vanIdeal d p) e = part I e`. Use extensionality with `F`. Conclude with `((h e he).2 F.1 F.2).symm`. Rewrite using `[← (h e he).1, h1, dimDeg, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]`.
-/
theorem finrank_part {σ K Hh : Type} [Field K] {I : Ideal (MvPolynomial σ K)} {Q : Polynomial ℚ} {d : ℕ}
    {p : Hh → σ → K} (h : CutBy I Q d p) {e : ℕ} (he : e ≥ d) :
    (finrank K (part (vanIdeal d p) e) : ℚ) = Q.eval (e : ℚ) := by
  have h1 : part (vanIdeal d p) e = part I e := by
    ext F
    exact ((h e he).2 F.1 F.2).symm
  rw [← (h e he).1, h1, dimDeg, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

/- English proof (translation)
Use `letI := Fintype.ofFinite Hh`. Establish `key : ∀ z, ev d (fun h i => algebraMap R K (p h i)) (θ z) = TensorProduct.piScalarRight R K K Hh ((ev d p).baseChange K z)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a F`. Establish `: a ⊗ₜ[R] F = a • (1 : K) ⊗ₜ[R] F` using `by simp [TensorProduct.smul_tmul']`. Rewrite using `[this, map_smul, map_smul, map_smul, map_smul]`. Use `congr 1`.

Use extensionality with `h`. Rewrite using `[ev_apply, hθ, eval_map]`. Establish `h2` using `eval₂_comp_left (algebraMap R K) (RingHom.id R) (p h) F.1`. Rewrite using `[LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]`. Use `beta_reduce`.

Rewrite using `[ev_apply, Algebra.smul_def, mul_one]`. Conclude with `h2.symm`. Rewrite using `[← ker_ev, Submodule.map_equiv_eq_comap_symm]`. Use extensionality with `F`. Simplify using `only [Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_coe]`.

Rewrite using `[← (TensorProduct.piScalarRight R K K Hh).map_eq_zero_iff, ← key, LinearEquiv.apply_symm_apply]`.
-/
theorem map_ker_baseChange {σ R Hh : Type} (K : Type) [CommRing R] [CommRing K] [Algebra R K] [Finite Hh]
    (d : ℕ) (p : Hh → σ → R) (θ : K ⊗[R] homogeneousSubmodule σ R d ≃ₗ[K] homogeneousSubmodule σ K d)
    (hθ : ∀ F, (θ (1 ⊗ₜ F)).1 = map (algebraMap R K) F.1) :
    (LinearMap.ker ((ev d p).baseChange K)).map θ.toLinearMap =
      part (vanIdeal d fun h i => algebraMap R K (p h i)) d := by
  classical
  letI := Fintype.ofFinite Hh
  have key : ∀ z, ev d (fun h i => algebraMap R K (p h i)) (θ z) =
      TensorProduct.piScalarRight R K K Hh ((ev d p).baseChange K z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a F =>
      have : a ⊗ₜ[R] F = a • (1 : K) ⊗ₜ[R] F := by simp [TensorProduct.smul_tmul']
      rw [this, map_smul, map_smul, map_smul, map_smul]
      congr 1
      ext h
      rw [ev_apply, hθ, eval_map]
      have h2 := eval₂_comp_left (algebraMap R K) (RingHom.id R) (p h) F.1
      rw [LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
      beta_reduce
      rw [ev_apply, Algebra.smul_def, mul_one]
      exact h2.symm
  rw [← ker_ev, Submodule.map_equiv_eq_comap_symm]
  ext F
  simp only [Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_coe]
  rw [← (TensorProduct.piScalarRight R K K Hh).map_eq_zero_iff, ← key, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.baseChange_eq_span, Submodule.map_span_le]`. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Use `show (θ (1 ⊗ₜ F)).1 ∈ J.map _`. Rewrite using `[hθ]`.

Conclude with `Ideal.mem_map_of_mem _ hF`. Introduce `F hF`. Establish `h1` using `mem_span_of_mem_map _ J hF`. Establish `h2 : ∀ G ∈ Submodule.span K (map (algebraMap R K) '' (J : Set (MvPolynomial σ R))), (homogeneousComponent e).codRestrict _ (homogeneousComponent_mem e) G ∈ ((part J e).baseChange K).map θ.toLinearMap`. Introduce `G hG`.

Use `Submodule.span_le (p := (((part J e).baseChange K).map θ.toLinearMap).comap ((homogeneousComponent e).codRestrict _ (homogeneousComponent_mem e))) |>.2 ?_ hG` and prove the remaining obligations. Introduce and unpack `_ ⟨H, hH, rfl⟩`. Use `⟨1 ⊗ₜ ⟨_, homogeneousComponent_mem e H⟩, Submodule.tmul_mem_baseChange_of_mem _ (hJ H hH), Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `(hθ _).trans (map_homogeneousComponent _ _ _).symm`. Use `h2 _ h1` and compare the differences between its conclusion and the goal.

Conclude with `Subtype.ext (by simp [homogeneousComponent_of_mem F.2])`.
-/
theorem map_part_baseChange {σ R : Type} (K : Type) [CommRing R] [CommRing K] [Algebra R K]
    (J : Ideal (MvPolynomial σ R)) (e : ℕ) (hJ : ∀ F ∈ J, homogeneousComponent e F ∈ J)
    (θ : K ⊗[R] homogeneousSubmodule σ R e ≃ₗ[K] homogeneousSubmodule σ K e)
    (hθ : ∀ F, (θ (1 ⊗ₜ F)).1 = map (algebraMap R K) F.1) :
    ((part J e).baseChange K).map θ.toLinearMap = part (J.map (map (algebraMap R K))) e := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span, Submodule.map_span_le]
    rintro _ ⟨F, hF, rfl⟩
    show (θ (1 ⊗ₜ F)).1 ∈ J.map _
    rw [hθ]
    exact Ideal.mem_map_of_mem _ hF
  · intro F hF
    have h1 := mem_span_of_mem_map _ J hF
    have h2 : ∀ G ∈ Submodule.span K (map (algebraMap R K) '' (J : Set (MvPolynomial σ R))),
        (homogeneousComponent e).codRestrict _ (homogeneousComponent_mem e) G ∈
          ((part J e).baseChange K).map θ.toLinearMap := by
      intro G hG
      refine Submodule.span_le (p := (((part J e).baseChange K).map θ.toLinearMap).comap
        ((homogeneousComponent e).codRestrict _ (homogeneousComponent_mem e))) |>.2 ?_ hG
      rintro _ ⟨H, hH, rfl⟩
      refine ⟨1 ⊗ₜ ⟨_, homogeneousComponent_mem e H⟩,
        Submodule.tmul_mem_baseChange_of_mem _ (hJ H hH), Subtype.ext ?_⟩
      exact (hθ _).trans (map_homogeneousComponent _ _ _).symm
    convert h2 _ h1
    exact Subtype.ext (by simp [homogeneousComponent_of_mem F.2])

/- English proof (translation)
Introduce `R _ _ σ Hh _ _ p Q d P hP hcut`. Establish `hfin : ∀ e, Module.Finite R (homogeneousSubmodule σ R e)` using `fun e => Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ R e)`. Establish `hcoker : Module.Projective R ((Hh → R) ⧸ LinearMap.range (ev d p))`. Use `projective_of_veryDense hP _ ((Nat.card Hh : ℚ) - (Nat.card {u : σ →₀ ℕ | u.degree = d} - Q.eval (d : ℚ))) fun q hq => ?_` and prove the remaining obligations. Take `⟨K, _, x, I, hx, hI⟩` from `hcut _ hq`.

Use `letI := x.toAlgebra`. Use `letI := Fintype.ofFinite Hh`. Take `⟨θ, hθ⟩` from `exists_equiv σ R K d`. Establish `h1` using `finrank_baseChange_coker_add_finrank_range K (ev d p)`. Establish `h2` using `((ev d p).baseChange K).finrank_range_add_finrank_ker`.

Establish `h3 : (finrank K (LinearMap.ker ((ev d p).baseChange K)) : ℚ) = Q.eval (d : ℚ)`. Rewrite using `[← finrank_part hI le_rfl, ← θ.finrank_map_eq, map_ker_baseChange K d p θ hθ]`. Both sides reduce to the same expression. Rewrite `h2` using `[θ.finrank_eq, finrank_forms]`. Rewrite `h1` using `[(TensorProduct.piScalarRight R K K Hh).finrank_eq, finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card]`.

Rewrite using `[← finrank_tensorProduct_eq_finrank_fiber K q hx.symm, ← h1, ← h2, ← h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨s, hs⟩` from `exists_comp_comp_eq_of_projective (ev d p)`. Establish `hmap : ∀ (K : Type) [Field K] (x : R →+* K), (vanIdeal d p).map (MvPolynomial.map x) = vanIdeal d (fun h i => x (p h i))`.

Introduce `K _ x`. Use `letI := x.toAlgebra`. Take `⟨θ, hθ⟩` from `exists_equiv σ R K d`. Establish `h1` using `map_ker_baseChange K d p θ hθ`. Rewrite `h1` using `[← baseChange_ker_of_comp_comp_eq _ s hs, ker_ev, map_part_baseChange K _ d (fun F hF => homogeneousComponent_mem_vanIdeal d p hF d) θ hθ]`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Use `Ideal.span_le.2 fun F hF => ?_` and prove the remaining obligations. Conclude with `(SetLike.ext_iff.1 h1 ⟨map x F, hF.1.map x⟩).1 (Ideal.mem_map_of_mem _ (Ideal.subset_span hF))`. Use `Ideal.span_le.2 fun F hF => ?_` and prove the remaining obligations.

Conclude with `(SetLike.ext_iff.1 h1 ⟨F, hF.1⟩).2 (Ideal.subset_span hF)`. Use `⟨fun e he => ?_, ?_, hmap⟩` and prove the remaining obligations. Use `projective_of_veryDense hP _ ((Nat.card {u : σ →₀ ℕ | u.degree = e} : ℚ) - Q.eval (e : ℚ)) fun q hq => ?_` and prove the remaining obligations. Take `⟨K, _, x, I, hx, hI⟩` from `hcut _ hq`. Use `letI := x.toAlgebra`.

Take `⟨θ, hθ⟩` from `exists_equiv σ R K e`. Establish `h1` using `Submodule.finrank_quotient_add_finrank ((part (vanIdeal d p) e).baseChange K)`. Establish `h3 : (finrank K ((part (vanIdeal d p) e).baseChange K) : ℚ) = Q.eval (e : ℚ)`. Rewrite using `[← finrank_part hI he, ← θ.finrank_map_eq, map_part_baseChange K _ e (fun F hF => homogeneousComponent_mem_vanIdeal d p hF e) θ hθ, ← hmap K x]`. Both sides reduce to the same expression.

Rewrite `h1` using `[θ.finrank_eq, finrank_forms, ← (baseChangeQuotEquiv K _).finrank_eq]`. Rewrite using `[← finrank_tensorProduct_eq_finrank_fiber K q hx.symm, ← h1, ← h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨t, ht⟩` from `exists_retraction_ker_of_generalizedInverse _ s hs`.

Establish `h2 : Module.Finite R (LinearMap.ker (ev d p))` using `Module.Finite.of_surjective t (Function.RightInverse.surjective (g := (LinearMap.ker (ev d p)).subtype) (LinearMap.congr_fun ht))`. Take `⟨T, hT⟩` from `(Module.Finite.iff_fg.1 h2).map (homogeneousSubmodule σ R d).subtype`. Use `⟨T, le_antisymm (Ideal.span_le.2 fun F hF => ?_) (Ideal.span_le.2 fun F hF => ?_)⟩` and prove the remaining obligations. Establish `: F ∈ (LinearMap.ker (ev d p)).map (homogeneousSubmodule σ R d).subtype` using `hT ▸ Submodule.subset_span hF`. Take `⟨G, hG, rfl⟩` from `this`.

Conclude with `(ker_ev d p).le hG`. Establish `: F ∈ Submodule.span R (T : Set (MvPolynomial σ R))` using `hT ▸ ⟨⟨F, hF.1⟩, (ker_ev d p).ge (Ideal.subset_span hF), rfl⟩`. Conclude with `Submodule.span_le_restrictScalars R _ _ this`.
-/
theorem forms_through_points : ∀ (R : Type) [CommRing R] [IsReduced R] (σ Hh : Type) [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (P : Set (Ideal R)), VeryDense P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : Ideal (MvPolynomial σ K)), RingHom.ker x = q ∧ CutBy I Q d (fun h i => x (p h i))) → (∀ e ≥ d, Module.Projective R (↥(MvPolynomial.homogeneousSubmodule σ R e) ⧸ ((vanIdeal d p).restrictScalars R).comap (MvPolynomial.homogeneousSubmodule σ R e).subtype)) ∧ (vanIdeal d p).FG ∧ ∀ (K : Type) [Field K] (x : R →+* K), (vanIdeal d p).map (MvPolynomial.map x) = vanIdeal d (fun h i => x (p h i)) := by
  intro R _ _ σ Hh _ _ p Q d P hP hcut
  have hfin : ∀ e, Module.Finite R (homogeneousSubmodule σ R e) := fun e =>
    Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ R e)
  have hcoker : Module.Projective R ((Hh → R) ⧸ LinearMap.range (ev d p)) := by
    refine projective_of_veryDense hP _
      ((Nat.card Hh : ℚ) - (Nat.card {u : σ →₀ ℕ | u.degree = d} - Q.eval (d : ℚ))) fun q hq => ?_
    obtain ⟨K, _, x, I, hx, hI⟩ := hcut _ hq
    letI := x.toAlgebra
    classical
    letI := Fintype.ofFinite Hh
    obtain ⟨θ, hθ⟩ := exists_equiv σ R K d
    have h1 := finrank_baseChange_coker_add_finrank_range K (ev d p)
    have h2 := ((ev d p).baseChange K).finrank_range_add_finrank_ker
    have h3 : (finrank K (LinearMap.ker ((ev d p).baseChange K)) : ℚ) = Q.eval (d : ℚ) := by
      rw [← finrank_part hI le_rfl, ← θ.finrank_map_eq, map_ker_baseChange K d p θ hθ]
      rfl
    rw [θ.finrank_eq, finrank_forms] at h2
    rw [(TensorProduct.piScalarRight R K K Hh).finrank_eq, finrank_fintype_fun_eq_card,
      ← Nat.card_eq_fintype_card] at h1
    rw [← finrank_tensorProduct_eq_finrank_fiber K q hx.symm, ← h1, ← h2, ← h3]
    push_cast
    ring
  obtain ⟨s, hs⟩ := exists_comp_comp_eq_of_projective (ev d p)
  have hmap : ∀ (K : Type) [Field K] (x : R →+* K),
      (vanIdeal d p).map (MvPolynomial.map x) = vanIdeal d (fun h i => x (p h i)) := by
    intro K _ x
    letI := x.toAlgebra
    obtain ⟨θ, hθ⟩ := exists_equiv σ R K d
    have h1 := map_ker_baseChange K d p θ hθ
    rw [← baseChange_ker_of_comp_comp_eq _ s hs, ker_ev, map_part_baseChange K _ d
      (fun F hF => homogeneousComponent_mem_vanIdeal d p hF d) θ hθ] at h1
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      refine Ideal.span_le.2 fun F hF => ?_
      exact (SetLike.ext_iff.1 h1 ⟨map x F, hF.1.map x⟩).1 (Ideal.mem_map_of_mem _ (Ideal.subset_span hF))
    · refine Ideal.span_le.2 fun F hF => ?_
      exact (SetLike.ext_iff.1 h1 ⟨F, hF.1⟩).2 (Ideal.subset_span hF)
  refine ⟨fun e he => ?_, ?_, hmap⟩
  · refine projective_of_veryDense hP _
      ((Nat.card {u : σ →₀ ℕ | u.degree = e} : ℚ) - Q.eval (e : ℚ)) fun q hq => ?_
    obtain ⟨K, _, x, I, hx, hI⟩ := hcut _ hq
    letI := x.toAlgebra
    obtain ⟨θ, hθ⟩ := exists_equiv σ R K e
    have h1 := Submodule.finrank_quotient_add_finrank ((part (vanIdeal d p) e).baseChange K)
    have h3 : (finrank K ((part (vanIdeal d p) e).baseChange K) : ℚ) = Q.eval (e : ℚ) := by
      rw [← finrank_part hI he, ← θ.finrank_map_eq, map_part_baseChange K _ e
        (fun F hF => homogeneousComponent_mem_vanIdeal d p hF e) θ hθ, ← hmap K x]
      rfl
    rw [θ.finrank_eq, finrank_forms, ← (baseChangeQuotEquiv K _).finrank_eq] at h1
    rw [← finrank_tensorProduct_eq_finrank_fiber K q hx.symm, ← h1, ← h3]
    push_cast
    ring
  · obtain ⟨t, ht⟩ := exists_retraction_ker_of_generalizedInverse _ s hs
    have h2 : Module.Finite R (LinearMap.ker (ev d p)) := Module.Finite.of_surjective t
      (Function.RightInverse.surjective (g := (LinearMap.ker (ev d p)).subtype) (LinearMap.congr_fun ht))
    obtain ⟨T, hT⟩ := (Module.Finite.iff_fg.1 h2).map (homogeneousSubmodule σ R d).subtype
    refine ⟨T, le_antisymm (Ideal.span_le.2 fun F hF => ?_) (Ideal.span_le.2 fun F hF => ?_)⟩
    · have : F ∈ (LinearMap.ker (ev d p)).map (homogeneousSubmodule σ R d).subtype :=
        hT ▸ Submodule.subset_span hF
      obtain ⟨G, hG, rfl⟩ := this
      exact (ker_ev d p).le hG
    · have : F ∈ Submodule.span R (T : Set (MvPolynomial σ R)) :=
        hT ▸ ⟨⟨F, hF.1⟩, (ker_ev d p).ge (Ideal.subset_span hF), rfl⟩
      exact Submodule.span_le_restrictScalars R _ _ this

end GlobalTheory.FamAlg

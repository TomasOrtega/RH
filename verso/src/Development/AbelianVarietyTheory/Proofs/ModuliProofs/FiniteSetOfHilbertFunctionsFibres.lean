import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open scoped TensorProduct

namespace GlobalTheory

namespace HilbertFamily

open MvPolynomial

/- English proof (translation)
Set `p : Ideal A` to `RingHom.ker (algebraMap A K)`. Use `haveI : p.IsPrime := RingHom.ker_isPrime _`. Set `B` to `Localization.AtPrime p`. Use `haveI : Module.Free B (B ⊗[A] M) := ha B (IsLocalization.map_units B (⟨a, hK⟩ : p.primeCompl))`. Use `haveI : Module.Flat B (B ⊗[A] N) := Module.Flat.of_retract (i.baseChange B) (r.baseChange B) (by`.

Rewrite using `[← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id])`. Use `haveI : Module.Free B (B ⊗[A] N) := Module.free_of_flat_of_isLocalRing`. Establish `key : ∀ (L : Type) [Field L] [Algebra A L], (∀ y : p.primeCompl, IsUnit (algebraMap A L y)) → Module.finrank L (L ⊗[A] N) = Module.finrank B (B ⊗[A] N)`. Introduce `L _ _ hL`. Use `letI : Algebra B L := (IsLocalization.lift (M := p.primeCompl) hL).toAlgebra`.

Use `haveI : IsScalarTower A B L := .of_algebraMap_eq fun y => (IsLocalization.lift_eq (M := p.primeCompl) hL y).symm`. Rewrite using `[← Module.finrank_baseChange (R := L) (S := B) (M' := B ⊗[A] N)]`. Conclude with `(TensorProduct.AlgebraTensorModule.cancelBaseChange A B L L N).finrank_eq.symm`. Rewrite using `[key K fun y => isUnit_iff_ne_zero.2 y.2, key (FractionRing A) fun y => ?_]`. Use `isUnit_iff_ne_zero.2 ?_` and prove the remaining obligations.

Rewrite using `[Ne, FaithfulSMul.algebraMap_eq_zero_iff]`. Introduce `h`. Conclude with `y.2 (h ▸ p.zero_mem)`.
-/
theorem finrank_tensor_eq_of_retract {A M N : Type} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module.Finite A N]
    (i : N →ₗ[A] M) (r : M →ₗ[A] N) (hri : r ∘ₗ i = LinearMap.id) (a : A)
    (ha : ∀ (B : Type) [CommRing B] [Algebra A B], IsUnit (algebraMap A B a) →
      Module.Free B (B ⊗[A] M))
    (K : Type) [Field K] [Algebra A K] (hK : algebraMap A K a ≠ 0) :
    Module.finrank K (K ⊗[A] N) =
      Module.finrank (FractionRing A) (FractionRing A ⊗[A] N) := by
  let p : Ideal A := RingHom.ker (algebraMap A K)
  haveI : p.IsPrime := RingHom.ker_isPrime _
  let B := Localization.AtPrime p
  haveI : Module.Free B (B ⊗[A] M) :=
    ha B (IsLocalization.map_units B (⟨a, hK⟩ : p.primeCompl))
  haveI : Module.Flat B (B ⊗[A] N) :=
    Module.Flat.of_retract (i.baseChange B) (r.baseChange B) (by
      rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id])
  haveI : Module.Free B (B ⊗[A] N) := Module.free_of_flat_of_isLocalRing
  have key : ∀ (L : Type) [Field L] [Algebra A L],
      (∀ y : p.primeCompl, IsUnit (algebraMap A L y)) →
      Module.finrank L (L ⊗[A] N) = Module.finrank B (B ⊗[A] N) := by
    intro L _ _ hL
    letI : Algebra B L := (IsLocalization.lift (M := p.primeCompl) hL).toAlgebra
    haveI : IsScalarTower A B L :=
      .of_algebraMap_eq fun y => (IsLocalization.lift_eq (M := p.primeCompl) hL y).symm
    rw [← Module.finrank_baseChange (R := L) (S := B) (M' := B ⊗[A] N)]
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A B L L N).finrank_eq.symm
  rw [key K fun y => isUnit_iff_ne_zero.2 y.2, key (FractionRing A) fun y => ?_]
  refine isUnit_iff_ne_zero.2 ?_
  rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  intro h
  exact y.2 (h ▸ p.zero_mem)

noncomputable def piece {A σ : Type} [CommRing A] (I : Ideal (MvPolynomial σ A)) (e : ℕ) :
    Submodule A (MvPolynomial σ A ⧸ I) :=
  (homogeneousSubmodule σ A e).map (Ideal.Quotient.mkₐ A I).toLinearMap

instance {A σ : Type} [CommRing A] [Finite σ] (I : Ideal (MvPolynomial σ A)) (e : ℕ) :
    Module.Finite A (piece I e) :=
  Module.Finite.iff_fg.2 ((homogeneousSubmodule_fg σ A e).map _)

/- English proof (translation)
Set `f : MvPolynomial σ A →ₗ[A] piece I e` to `LinearMap.codRestrict (piece I e) ((Ideal.Quotient.mkₐ A I).toLinearMap ∘ₗ homogeneousComponent e) fun F => ⟨_, homogeneousComponent_mem e F, rfl⟩`. Establish `hf : I.restrictScalars A ≤ LinearMap.ker f` using `fun F hF => Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (hI F hF e))`. Use `⟨((I.restrictScalars A).liftQ f hf) ∘ₗ (Submodule.Quotient.restrictScalarsEquiv A I).symm.toLinearMap, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨_, F, hF, rfl⟩`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (homogeneousComponent e F) = Ideal.Quotient.mk I F`.

Rewrite using `[homogeneousComponent_of_mem hF, if_pos rfl]`.
-/
theorem exists_retract {A σ : Type} [CommRing A] (I : Ideal (MvPolynomial σ A))
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) (e : ℕ) :
    ∃ r : (MvPolynomial σ A ⧸ I) →ₗ[A] piece I e, r ∘ₗ (piece I e).subtype = LinearMap.id := by
  let f : MvPolynomial σ A →ₗ[A] piece I e :=
    LinearMap.codRestrict (piece I e)
      ((Ideal.Quotient.mkₐ A I).toLinearMap ∘ₗ homogeneousComponent e)
      fun F => ⟨_, homogeneousComponent_mem e F, rfl⟩
  have hf : I.restrictScalars A ≤ LinearMap.ker f := fun F hF =>
    Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (hI F hF e))
  refine ⟨((I.restrictScalars A).liftQ f hf) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv A I).symm.toLinearMap, ?_⟩
  ext ⟨_, F, hF, rfl⟩
  change Ideal.Quotient.mk I (homogeneousComponent e F) = Ideal.Quotient.mk I F
  rw [homogeneousComponent_of_mem hF, if_pos rfl]

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_retract I hI e`. Establish `hinj : Function.Injective ((piece I e).subtype.baseChange K)`. Apply `Function.LeftInverse.injective (g := r.baseChange K)` to reduce the goal to its premises. Introduce `z`. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id, LinearMap.id_apply]`.

Set `ε` to `algebraTensorAlgEquiv (σ := σ) A K`. Set `ψ : MvPolynomial σ K →ₗ[K] K ⊗[A] (MvPolynomial σ A ⧸ I)` to `(Ideal.Quotient.mkₐ A I).toLinearMap.baseChange K ∘ₗ ε.symm.toLinearMap`. Establish `hψ : ∀ F : MvPolynomial σ A, ψ (map (algebraMap A K) F) = 1 ⊗ₜ Ideal.Quotient.mk I F`. Introduce `F`. Establish `: ε.symm (map (algebraMap A K) F) = 1 ⊗ₜ F`.

Rewrite using `[AlgEquiv.symm_apply_eq, algebraTensorAlgEquiv_tmul, one_smul]`. Express the relevant statement in the definitionally equal form `(Ideal.Quotient.mkₐ A I).toLinearMap.baseChange K (ε.symm _) = _`. Rewrite using `[this]`. Both sides reduce to the same expression. Establish `hker : ∀ G, ψ G = 0 ↔ G ∈ I.map (map (algebraMap A K))`.

Introduce `G`. Establish `h1` using `Algebra.TensorProduct.lTensor_ker (A := K) (Ideal.Quotient.mkₐ A I) (Ideal.Quotient.mkₐ_surjective A I)`. Establish `h2 : RingHom.ker (Ideal.Quotient.mkₐ A I) = I` using `Ideal.Quotient.mkₐ_ker A I`. Rewrite `h1` using `[h2]`. Establish `h3 : (map (algebraMap A K) : MvPolynomial σ A →+* MvPolynomial σ K) = (ε.toRingEquiv : _ →+* _).comp (Algebra.TensorProduct.includeRight (R` using `A) (A := K) (B := MvPolynomial σ A)).toRingHom := by`.

Use `RingHom.ext fun F => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = ε (1 ⊗ₜ F)`. Rewrite using `[algebraTensorAlgEquiv_tmul, one_smul]`. Establish `h4 : I.map (Algebra.TensorProduct.includeRight (R` using `A) (A := K) (B := MvPolynomial σ A)).toRingHom = _ := h1.symm`. Rewrite using `[h3, ← Ideal.map_map, h4, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingHom.mem_ker]`.

Both sides reduce to the same expression. Establish `hrange : (homogeneousSubmodule σ K e).map ψ = (piece I e).baseChange K`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨G, hG, rfl⟩`. Rewrite using `[G.as_sum, map_sum]`.

Use `Submodule.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Establish `hd' : d.degree = e`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `hG (mem_support_iff.1 hd)`. Establish `: (monomial d (coeff d G) : MvPolynomial σ K) = coeff d G • map (algebraMap A K) (monomial d 1)`.

Simplify using `[smul_monomial]`. Rewrite using `[this, map_smul, hψ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.tmul_mem_baseChange_of_mem _ ⟨_, isHomogeneous_monomial 1 hd', rfl⟩)`. Introduce and unpack `_ ⟨z, rfl⟩`. Proceed by induction on `z with`.

Consider the case `zero => simp`. Consider the case `add z w hz hw => rw [map_add]`. Conclude with `add_mem hz hw`. Consider the case `tmul c n`. Take `⟨_, F, hF, rfl⟩` from `n`.

Use `⟨c • map (algebraMap A K) F, Submodule.smul_mem _ _ (IsHomogeneous.map hF _), ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hψ, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Both sides reduce to the same expression. Use `haveI : Module.Finite K (homogeneousSubmodule σ K e) := Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ K e)`. Establish `h` using `LinearMap.finrank_range_add_finrank_ker (ψ ∘ₗ (homogeneousSubmodule σ K e).subtype)`.

Rewrite `h` using `[LinearMap.range_comp, Submodule.range_subtype, hrange, Submodule.baseChange, LinearMap.finrank_range_of_inj hinj, LinearMap.ker_comp, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]`. Establish `hk : LinearMap.ker ψ = (I.map (map (algebraMap A K))).restrictScalars K` using `Submodule.ext hker`. Rewrite `h` using `[hk]`. Use `h.trans ?_` and prove the remaining obligations. Rewrite using `[homogeneousSubmodule_eq_finsupp_supported]`.

Conclude with `Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)`.
-/
theorem dimDeg_add_finrank {A σ : Type} [CommRing A] [Finite σ] (I : Ideal (MvPolynomial σ A))
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) (e : ℕ)
    (K : Type) [Field K] [Algebra A K] :
    Module.finrank K (K ⊗[A] piece I e) + ZM.dimDeg (I.map (map (algebraMap A K))) e =
      Nat.card {d : σ →₀ ℕ | d.degree = e} := by
  obtain ⟨r, hr⟩ := exists_retract I hI e
  have hinj : Function.Injective ((piece I e).subtype.baseChange K) := by
    apply Function.LeftInverse.injective (g := r.baseChange K)
    intro z
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id,
      LinearMap.id_apply]
  let ε := algebraTensorAlgEquiv (σ := σ) A K
  let ψ : MvPolynomial σ K →ₗ[K] K ⊗[A] (MvPolynomial σ A ⧸ I) :=
    (Ideal.Quotient.mkₐ A I).toLinearMap.baseChange K ∘ₗ ε.symm.toLinearMap
  have hψ : ∀ F : MvPolynomial σ A, ψ (map (algebraMap A K) F) = 1 ⊗ₜ Ideal.Quotient.mk I F := by
    intro F
    have : ε.symm (map (algebraMap A K) F) = 1 ⊗ₜ F := by
      rw [AlgEquiv.symm_apply_eq, algebraTensorAlgEquiv_tmul, one_smul]
    change (Ideal.Quotient.mkₐ A I).toLinearMap.baseChange K (ε.symm _) = _
    rw [this]
    rfl
  have hker : ∀ G, ψ G = 0 ↔ G ∈ I.map (map (algebraMap A K)) := by
    intro G
    have h1 := Algebra.TensorProduct.lTensor_ker (A := K) (Ideal.Quotient.mkₐ A I)
      (Ideal.Quotient.mkₐ_surjective A I)
    have h2 : RingHom.ker (Ideal.Quotient.mkₐ A I) = I := Ideal.Quotient.mkₐ_ker A I
    rw [h2] at h1
    have h3 : (map (algebraMap A K) : MvPolynomial σ A →+* MvPolynomial σ K) =
        (ε.toRingEquiv : _ →+* _).comp
          (Algebra.TensorProduct.includeRight (R := A) (A := K)
            (B := MvPolynomial σ A)).toRingHom := by
      refine RingHom.ext fun F => ?_
      change _ = ε (1 ⊗ₜ F)
      rw [algebraTensorAlgEquiv_tmul, one_smul]
    have h4 : I.map (Algebra.TensorProduct.includeRight (R := A) (A := K)
        (B := MvPolynomial σ A)).toRingHom = _ := h1.symm
    rw [h3, ← Ideal.map_map, h4, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingHom.mem_ker]
    rfl
  have hrange : (homogeneousSubmodule σ K e).map ψ = (piece I e).baseChange K := by
    apply le_antisymm
    · rintro _ ⟨G, hG, rfl⟩
      rw [G.as_sum, map_sum]
      refine Submodule.sum_mem _ fun d hd => ?_
      have hd' : d.degree = e := by
        rw [Finsupp.degree_eq_weight_one]
        exact hG (mem_support_iff.1 hd)
      have : (monomial d (coeff d G) : MvPolynomial σ K) =
          coeff d G • map (algebraMap A K) (monomial d 1) := by
        simp [smul_monomial]
      rw [this, map_smul, hψ]
      exact Submodule.smul_mem _ _ (Submodule.tmul_mem_baseChange_of_mem _
        ⟨_, isHomogeneous_monomial 1 hd', rfl⟩)
    · rintro _ ⟨z, rfl⟩
      induction z with
      | zero => simp
      | add z w hz hw => rw [map_add]; exact add_mem hz hw
      | tmul c n =>
        obtain ⟨_, F, hF, rfl⟩ := n
        refine ⟨c • map (algebraMap A K) F,
          Submodule.smul_mem _ _ (IsHomogeneous.map hF _), ?_⟩
        rw [map_smul, hψ, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rfl
  haveI : Module.Finite K (homogeneousSubmodule σ K e) :=
    Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ K e)
  have h := LinearMap.finrank_range_add_finrank_ker (ψ ∘ₗ (homogeneousSubmodule σ K e).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, hrange, Submodule.baseChange,
    LinearMap.finrank_range_of_inj hinj, LinearMap.ker_comp,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at h
  have hk : LinearMap.ker ψ = (I.map (map (algebraMap A K))).restrictScalars K :=
    Submodule.ext hker
  rw [hk] at h
  refine h.trans ?_
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)

/- English proof (translation)
Take `⟨a, ha0, ha⟩` from `exists_free_tensor_of_isUnit.{0} A (MvPolynomial σ A) (MvPolynomial σ A ⧸ I)`. Use `⟨a, ha0, ZM.dimDeg (I.map (map (algebraMap A (FractionRing A)))), fun K _ x hx => ?_⟩` and prove the remaining obligations. Use `letI : Algebra A K := x.toAlgebra`. Use function extensionality and compare the values at `e`. Take `⟨r, hr⟩` from `exists_retract I hI e`.

Establish `h1` using `finrank_tensor_eq_of_retract _ r hr a ha K hx`. Establish `h2` using `dimDeg_add_finrank I hI e K`. Establish `h3` using `dimDeg_add_finrank I hI e (FractionRing A)`. Express the relevant statement in the definitionally equal form `ZM.dimDeg (I.map (map (algebraMap A K))) e = _`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_const_of_isDomain {A σ : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Finite σ] (I : Ideal (MvPolynomial σ A))
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) :
    ∃ a : A, a ≠ 0 ∧ ∃ φ : ℕ → ℕ, ∀ (K : Type) [Field K] (x : A →+* K), x a ≠ 0 →
      ZM.dimDeg (I.map (map x)) = φ := by
  obtain ⟨a, ha0, ha⟩ := exists_free_tensor_of_isUnit.{0} A (MvPolynomial σ A)
    (MvPolynomial σ A ⧸ I)
  refine ⟨a, ha0, ZM.dimDeg (I.map (map (algebraMap A (FractionRing A)))), fun K _ x hx => ?_⟩
  letI : Algebra A K := x.toAlgebra
  funext e
  obtain ⟨r, hr⟩ := exists_retract I hI e
  have h1 := finrank_tensor_eq_of_retract _ r hr a ha K hx
  have h2 := dimDeg_add_finrank I hI e K
  have h3 := dimDeg_add_finrank I hI e (FractionRing A)
  change ZM.dimDeg (I.map (map (algebraMap A K))) e = _
  omega

/- English proof (translation)
Proceed by induction on `J using IsNoetherian.induction with`. Consider the case `_ J ih`. Establish `hlt : ∀ b, b ∉ J → J < J ⊔ Ideal.span {b}` using `fun b hb => lt_of_le_of_ne le_sup_left fun h => hb (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))`. Establish `hle : ∀ (K : Type) [Field K] (x : R →+* K) (b : R), J ≤ RingHom.ker x → x b = 0 → J ⊔ Ideal.span {b} ≤ RingHom.ker x` using `fun K _ x b h hb => sup_le h ((Ideal.span_singleton_le_iff_mem _).2 hb)`. Distinguish the cases in `hJ : Ideal.IsPrime J`.

Establish `hsurj : Function.Surjective (map (σ` using `σ) (Ideal.Quotient.mk J)) := map_surjective _ Ideal.Quotient.mk_surjective`. Take `⟨a, ha0, φ₀, h⟩` from `exists_const_of_isDomain (I.map (map (Ideal.Quotient.mk J))) (by`. Introduce `F hF e`. Take `⟨G, hG, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ hsurj).1 hF`. Establish `: homogeneousComponent e (map (Ideal.Quotient.mk J) G) = map (Ideal.Quotient.mk J) (homogeneousComponent e G)`.

Use extensionality with `d`. Simplify using `only [coeff_homogeneousComponent, coeff_map]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[this]`. Conclude with `Ideal.mem_map_of_mem _ (hI G hG e))`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `haJ : a ∉ J` using `fun h => ha0 (Ideal.Quotient.eq_zero_iff_mem.2 h)`. Use `((ih _ (hlt a haJ)).insert φ₀).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨K, _, x, hx, rfl⟩`. Distinguish the cases in `hxa : x a = 0`.

Conclude with `Or.inr ⟨K, _, x, hle K x a hx hxa, rfl⟩`. Use `left`. Rewrite using `[← h K (Ideal.Quotient.lift J x hx) hxa, Ideal.map_map]`. Use `congr 2`. Use `RingHom.ext fun F => ?_` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, map_map]`. Both sides reduce to the same expression. Break down `Ideal.not_isPrime_iff.1 hJ with rfl | ⟨b, hb, c, hc, hbc⟩` into its components or cases. Use `Set.finite_empty.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨K, _, x, hx, rfl⟩`.

Establish `: x 1 = 0` using `hx Submodule.mem_top`. Simplify using `at this`. Use `((ih _ (hlt b hb)).union (ih _ (hlt c hc))).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨K, _, x, hx, rfl⟩`. Establish `: x b * x c = 0` using `by rw [← map_mul]; exact hx hbc`.

Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `Or.inl ⟨K, _, x, hle K x b hx h, rfl⟩`. Conclude with `Or.inr ⟨K, _, x, hle K x c hx h, rfl⟩`.
-/
theorem finite_of_le_ker {R σ : Type} [CommRing R] [IsNoetherianRing R] [Finite σ]
    (I : Ideal (MvPolynomial σ R)) (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (J : Ideal R) :
    {φ : ℕ → ℕ | ∃ (K : Type) (_ : Field K) (x : R →+* K), J ≤ RingHom.ker x ∧
      φ = ZM.dimDeg (I.map (map x))}.Finite := by
  induction J using IsNoetherian.induction with
  | _ J ih =>
  have hlt : ∀ b, b ∉ J → J < J ⊔ Ideal.span {b} := fun b hb =>
    lt_of_le_of_ne le_sup_left fun h =>
      hb (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
  have hle : ∀ (K : Type) [Field K] (x : R →+* K) (b : R), J ≤ RingHom.ker x → x b = 0 →
      J ⊔ Ideal.span {b} ≤ RingHom.ker x := fun K _ x b h hb =>
    sup_le h ((Ideal.span_singleton_le_iff_mem _).2 hb)
  by_cases hJ : Ideal.IsPrime J
  · have hsurj : Function.Surjective (map (σ := σ) (Ideal.Quotient.mk J)) :=
      map_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨a, ha0, φ₀, h⟩ := exists_const_of_isDomain (I.map (map (Ideal.Quotient.mk J))) (by
      intro F hF e
      obtain ⟨G, hG, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hF
      have : homogeneousComponent e (map (Ideal.Quotient.mk J) G) =
          map (Ideal.Quotient.mk J) (homogeneousComponent e G) := by
        ext d
        simp only [coeff_homogeneousComponent, coeff_map]
        split_ifs <;> simp
      rw [this]
      exact Ideal.mem_map_of_mem _ (hI G hG e))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have haJ : a ∉ J := fun h => ha0 (Ideal.Quotient.eq_zero_iff_mem.2 h)
    refine ((ih _ (hlt a haJ)).insert φ₀).subset ?_
    rintro _ ⟨K, _, x, hx, rfl⟩
    by_cases hxa : x a = 0
    · exact Or.inr ⟨K, _, x, hle K x a hx hxa, rfl⟩
    · left
      rw [← h K (Ideal.Quotient.lift J x hx) hxa, Ideal.map_map]
      congr 2
      refine RingHom.ext fun F => ?_
      rw [RingHom.comp_apply, map_map]
      rfl
  · rcases Ideal.not_isPrime_iff.1 hJ with rfl | ⟨b, hb, c, hc, hbc⟩
    · refine Set.finite_empty.subset ?_
      rintro _ ⟨K, _, x, hx, rfl⟩
      have : x 1 = 0 := hx Submodule.mem_top
      simp at this
    · refine ((ih _ (hlt b hb)).union (ih _ (hlt c hc))).subset ?_
      rintro _ ⟨K, _, x, hx, rfl⟩
      have : x b * x c = 0 := by rw [← map_mul]; exact hx hbc
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl ⟨K, _, x, hle K x b hx h, rfl⟩
      · exact Or.inr ⟨K, _, x, hle K x c hx h, rfl⟩

end HilbertFamily

open GlobalTheory.ZM in

/- English proof (translation)
Introduce `R σ _ _ _ I hI`. Use `(HilbertFamily.finite_of_le_ker I hI ⊥).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨K, _, x, rfl⟩`. Conclude with `⟨K, _, x, bot_le, rfl⟩`.
-/
theorem finite_setOf_dimDeg_map : ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → {φ : ℕ → ℕ | ∃ (K : Type) (_ : Field K) (x : R →+* K), φ = dimDeg (I.map (MvPolynomial.map x))}.Finite := by
  intro R σ _ _ _ I hI
  refine (HilbertFamily.finite_of_le_ker I hI ⊥).subset ?_
  rintro _ ⟨K, _, x, rfl⟩
  exact ⟨K, _, x, bot_le, rfl⟩

end GlobalTheory

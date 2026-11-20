import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplIs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplUniq
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.AdditiveValuation.UnramExtY

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Take `⟨α, hα⟩` from `Field.exists_primitive_element k K`. Establish `hint : IsIntegral k α` using `Algebra.IsIntegral.isIntegral α`. Conclude with `⟨minpoly k α, minpoly.monic hint, minpoly.irreducible hint, ⟨(IntermediateField.adjoinRootEquivAdjoin k hint).trans ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)⟩⟩`.
-/
private theorem prim_ex (k K : Type) [Field k] [Field K] [Finite K] [Algebra k K] :
    ∃ g : Polynomial k, g.Monic ∧ Irreducible g ∧ Nonempty (AdjoinRoot g ≃ₐ[k] K) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k K
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  exact ⟨minpoly k α, minpoly.monic hint, minpoly.irreducible hint,
    ⟨(IntermediateField.adjoinRootEquivAdjoin k hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)⟩⟩

/- English proof (translation)
Use `letI : Algebra (ResidueField O) K := (Ideal.Quotient.lift (maximalIdeal O) (algebraMap O K) hK).toAlgebra`. Use `haveI : IsScalarTower O (ResidueField O) K := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Take `⟨g, hg, hgi, ⟨e⟩⟩` from `prim_ex (ResidueField O) K`. Take `⟨f, hf1, -, hf⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic (f := residue O) (p := g) (Polynomial.mem_lifts_of_surjective residue_surjective _) hg`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`.

Take `⟨hd, hv, hi, hc⟩` from `KStar.Binom.adjoinRoot_unramified hϖ hf (hf1 ▸ hgi)`. Use `haveI : Module.Finite O (AdjoinRoot f) := hf.finite_adjoinRoot`. Establish `hm : (maximalIdeal O).map (algebraMap O (AdjoinRoot f)) = maximalIdeal (AdjoinRoot f)`. Rewrite using `[hϖ.maximalIdeal_eq, hi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Use `haveI hl : IsLocalHom (algebraMap O (AdjoinRoot f)) := ((local_hom_TFAE _).out 0 2).2 hm.le`.

Establish `hcl : UpperTheory.V.CA.IsCL O (AdjoinRoot f)` using `UpperTheory.V.CA.cl_fin O O (AdjoinRoot f) (UpperTheory.V.CA.IsCL.of_isCO O O)`. Establish `hfin : Finite (ResidueField (AdjoinRoot f))` using `Nat.finite_of_card_ne_zero (by`. Rewrite using `[hc]`. Conclude with `pow_ne_zero _ Nat.card_pos.ne')`. Establish `hch : CharP (ResidueField (AdjoinRoot f)) l` using `charP_of_injective_ringHom (ResidueField.map (algebraMap O (AdjoinRoot f))).injective l`.

Use `⟨AdjoinRoot f, inferInstance, hd, hv, ⟨hcl.complete, hfin, hch⟩, inferInstance, inferInstance, hm, ?_⟩` and prove the remaining obligations. Establish `h0 : Polynomial.aeval (residue (AdjoinRoot f) (AdjoinRoot.root f)) g = 0`. Rewrite using `[← hf1]`. Establish `h1 : Polynomial.aeval (residue (AdjoinRoot f) (AdjoinRoot.root f)) f = 0`. Use `Polynomial.aeval_algebraMap_apply (ResidueField (AdjoinRoot f)) (AdjoinRoot.root f) f` as an intermediate fact.

Rewrite `this` using `[AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]`. Conclude with `this`. Conclude with `(Polynomial.aeval_map_algebraMap (ResidueField O) _ f).trans h1`. Conclude with `⟨((AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) _ h0).comp e.symm.toAlgHom).restrictScalars O⟩`.
-/
private theorem unr_ex {l : ℕ} (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (K : Type) [Field K] [Finite K] [Algebra O K] (hK : ∀ a ∈ maximalIdeal O, algebraMap O K a = 0) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : IsCoef l O')
      (_ : Algebra O O') (_ : Module.Finite O O'), (maximalIdeal O).map (algebraMap O O') = maximalIdeal O' ∧
      Nonempty (K →ₐ[O] ResidueField O') := by
  letI : Algebra (ResidueField O) K := (Ideal.Quotient.lift (maximalIdeal O) (algebraMap O K) hK).toAlgebra
  haveI : IsScalarTower O (ResidueField O) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨g, hg, hgi, ⟨e⟩⟩ := prim_ex (ResidueField O) K
  obtain ⟨f, hf1, -, hf⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (f := residue O) (p := g) (Polynomial.mem_lifts_of_surjective residue_surjective _) hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hd, hv, hi, hc⟩ := KStar.Binom.adjoinRoot_unramified hϖ hf (hf1 ▸ hgi)
  haveI : Module.Finite O (AdjoinRoot f) := hf.finite_adjoinRoot
  have hm : (maximalIdeal O).map (algebraMap O (AdjoinRoot f)) = maximalIdeal (AdjoinRoot f) := by
    rw [hϖ.maximalIdeal_eq, hi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  haveI hl : IsLocalHom (algebraMap O (AdjoinRoot f)) := ((local_hom_TFAE _).out 0 2).2 hm.le
  have hcl : UpperTheory.V.CA.IsCL O (AdjoinRoot f) := UpperTheory.V.CA.cl_fin O O (AdjoinRoot f) (UpperTheory.V.CA.IsCL.of_isCO O O)
  have hfin : Finite (ResidueField (AdjoinRoot f)) := Nat.finite_of_card_ne_zero (by
    rw [hc]; exact pow_ne_zero _ Nat.card_pos.ne')
  have hch : CharP (ResidueField (AdjoinRoot f)) l :=
    charP_of_injective_ringHom (ResidueField.map (algebraMap O (AdjoinRoot f))).injective l
  refine ⟨AdjoinRoot f, inferInstance, hd, hv, ⟨hcl.complete, hfin, hch⟩, inferInstance, inferInstance, hm, ?_⟩
  have h0 : Polynomial.aeval (residue (AdjoinRoot f) (AdjoinRoot.root f)) g = 0 := by
    rw [← hf1]
    have h1 : Polynomial.aeval (residue (AdjoinRoot f) (AdjoinRoot.root f)) f = 0 := by
      have := Polynomial.aeval_algebraMap_apply (ResidueField (AdjoinRoot f)) (AdjoinRoot.root f) f
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero] at this
      exact this
    exact (Polynomial.aeval_map_algebraMap (ResidueField O) _ f).trans h1
  exact ⟨((AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) _ h0).comp e.symm.toAlgHom).restrictScalars O⟩

/- English proof (translation)
Use `(res_eq_zero_iff O R _).2 h` as an intermediate fact. Rewrite `this` using `[map_sub, AlgHom.commutes, sub_eq_zero]`. Then use the resulting hypothesis.
-/
private theorem res_eq_of {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    {x : R} {a : O} (h : x - algebraMap O R a ∈ maximalIdeal R) : res O R x = algebraMap O _ a := by
  have := (res_eq_zero_iff O R _).2 h
  rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this

/- English proof (translation)
Establish `hy : ∀ d : D, algebraMap D R d ∈ maximalIdeal R ↔ φ d = 0` using `fun d => by`. Use `hc.comap_pow 1` as an intermediate fact. Rewrite `this` using `[pow_one, pow_one]`. Rewrite using `[← Ideal.mem_comap, this]`. Both sides reduce to the same expression.

Establish `hs : ∀ d : D, ∃ a : O, φ d = algebraMap O _ a ∧ algebraMap D R d - algebraMap O R a ∈ maximalIdeal R` using `fun d => by`. Take `⟨a, ha⟩` from `residue_surjective (φ d)`. Use `⟨a, ha.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply O D R, ← map_sub, hy, map_sub, AlgHom.commutes, sub_eq_zero]`. Conclude with `ha.symm`.

Use `haveI := hc.noeth`. Establish `hco : IsCO O R` using `{ complete := hc.complete isLocalHom := ⟨fun a ha => by`. Assume the negation of the conclusion as `hn`. Establish `h1 : algebraMap D R (algebraMap O D a) ∈ maximalIdeal R`. Rewrite using `[hy, AlgHom.commutes]`.

Conclude with `(residue_eq_zero_iff a).2 hn`. Rewrite `h1` using `[← IsScalarTower.algebraMap_apply]`. Conclude with `h1 ha⟩`. Use `res_surj := fun r => by`. Take `⟨d, hd⟩` from `hc.dense 1 r`.

Take `⟨a, -, ha⟩` from `hs d`. Rewrite `hd` using `[pow_one]`. Conclude with `⟨a, by simpa using add_mem hd ha⟩ }`. Use `⟨hco, fun d => ?_, fun C _ _ _ f hf => ?_⟩` and prove the remaining obligations. Take `⟨a, h1, h2⟩` from `hs d`.

Rewrite using `[h1, res_eq_of h2]`. Take `⟨G, ⟨h1, h2⟩, hu⟩` from `(UpperTheory.V.CA.cpl_uniq _ hc).1 C (maximalIdeal C) f.toRingHom fun d hd => by`. Rewrite using `[Ideal.mem_comap, ← res_eq_zero_iff O]`. Conclude with `(hf d).trans hd`. Establish `h3 : ∀ d, G (algebraMap D R d) = f d` using `fun d => DFunLike.congr_fun h1 d`.

Use `⟨{ G with commutes' := fun a => ?_ }, h3, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply O D R]`. Conclude with `(h3 _).trans (f.commutes a)`. Use `hu g.toRingHom ⟨RingHom.ext hg, fun z hz => by` as an intermediate fact. Rewrite using `[Ideal.mem_comap, ← res_eq_zero_iff O]`.

Conclude with `(res_map g z).trans ((res_eq_zero_iff O R z).2 hz)⟩`. Conclude with `AlgHom.ext fun z => DFunLike.congr_fun this z`.
-/
private theorem cpl_univ (O D R : Type) [CommRing O] [IsLocalRing O] [CommRing D] [Algebra O D] [IsNoetherianRing D]
    (φ : D →ₐ[O] ResidueField O) [CommRing R] [IsLocalRing R] [Algebra D R] [Algebra O R] [IsScalarTower O D R]
    [(RingHom.ker φ.toRingHom).IsMaximal] (hc : UpperTheory.V.CA.IsCplAt (RingHom.ker φ.toRingHom) R) :
    ∃ (_ : IsCO O R), (∀ a, res O R (algebraMap D R a) = φ a) ∧
      ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : D →ₐ[O] C),
        (∀ a, res O C (f a) = φ a) → ∃! g : R →ₐ[O] C, ∀ a, g (algebraMap D R a) = f a := by
  have hy : ∀ d : D, algebraMap D R d ∈ maximalIdeal R ↔ φ d = 0 := fun d => by
    have := hc.comap_pow 1
    rw [pow_one, pow_one] at this
    rw [← Ideal.mem_comap, this]
    rfl
  have hs : ∀ d : D, ∃ a : O, φ d = algebraMap O _ a ∧ algebraMap D R d - algebraMap O R a ∈ maximalIdeal R :=
    fun d => by
      obtain ⟨a, ha⟩ := residue_surjective (φ d)
      refine ⟨a, ha.symm, ?_⟩
      rw [IsScalarTower.algebraMap_apply O D R, ← map_sub, hy, map_sub, AlgHom.commutes, sub_eq_zero]
      exact ha.symm
  haveI := hc.noeth
  have hco : IsCO O R :=
    { complete := hc.complete
      isLocalHom := ⟨fun a ha => by
        by_contra hn
        have h1 : algebraMap D R (algebraMap O D a) ∈ maximalIdeal R := by
          rw [hy, AlgHom.commutes]
          exact (residue_eq_zero_iff a).2 hn
        rw [← IsScalarTower.algebraMap_apply] at h1
        exact h1 ha⟩
      res_surj := fun r => by
        obtain ⟨d, hd⟩ := hc.dense 1 r
        obtain ⟨a, -, ha⟩ := hs d
        rw [pow_one] at hd
        exact ⟨a, by simpa using add_mem hd ha⟩ }
  refine ⟨hco, fun d => ?_, fun C _ _ _ f hf => ?_⟩
  · obtain ⟨a, h1, h2⟩ := hs d
    rw [h1, res_eq_of h2]
  · obtain ⟨G, ⟨h1, h2⟩, hu⟩ := (UpperTheory.V.CA.cpl_uniq _ hc).1 C (maximalIdeal C) f.toRingHom fun d hd => by
      rw [Ideal.mem_comap, ← res_eq_zero_iff O]
      exact (hf d).trans hd
    have h3 : ∀ d, G (algebraMap D R d) = f d := fun d => DFunLike.congr_fun h1 d
    refine ⟨{ G with commutes' := fun a => ?_ }, h3, fun g hg => ?_⟩
    · rw [IsScalarTower.algebraMap_apply O D R]
      exact (h3 _).trans (f.commutes a)
    · have := hu g.toRingHom ⟨RingHom.ext hg, fun z hz => by
        rw [Ideal.mem_comap, ← res_eq_zero_iff O]
        exact (res_map g z).trans ((res_eq_zero_iff O R z).2 hz)⟩
      exact AlgHom.ext fun z => DFunLike.congr_fun this z

/- English proof (translation)
Use `haveI hm : (RingHom.ker φ.toRingHom).IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun z => by`. Take `⟨a, rfl⟩` from `residue_surjective z`. Conclude with `⟨algebraMap O D a, φ.commutes a⟩`. Establish `key : ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : Algebra D R), UpperTheory.V.CA.IsCplAt (RingHom.ker φ.toRingHom) R`. Take `⟨hloc, hc⟩` from `UpperTheory.V.CA.cpl_is D (RingHom.ker φ.toRingHom)`.

Conclude with `⟨_, _, hloc, _, hc⟩`. Take `⟨R, _, _, _, hc⟩` from `key`. Use `letI : Algebra O R := ((algebraMap D R).comp (algebraMap O D)).toAlgebra`. Use `haveI : IsScalarTower O D R := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Take `⟨hco, h1, h2⟩` from `cpl_univ O D R φ hc`.

Conclude with `⟨R, _, _, hco, IsScalarTower.toAlgHom O D R, h1, h2⟩`.
-/
private theorem cpl_ex (O D : Type) [CommRing O] [IsLocalRing O] [CommRing D] [Algebra O D] [IsNoetherianRing D]
    (φ : D →ₐ[O] ResidueField O) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (j : D →ₐ[O] R), (∀ a, res O R (j a) = φ a) ∧
      ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : D →ₐ[O] C),
        (∀ a, res O C (f a) = φ a) → ∃! g : R →ₐ[O] C, ∀ a, g (j a) = f a := by
  haveI hm : (RingHom.ker φ.toRingHom).IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun z => by
    obtain ⟨a, rfl⟩ := residue_surjective z
    exact ⟨algebraMap O D a, φ.commutes a⟩
  have key : ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : Algebra D R),
      UpperTheory.V.CA.IsCplAt (RingHom.ker φ.toRingHom) R := by
    obtain ⟨hloc, hc⟩ := UpperTheory.V.CA.cpl_is D (RingHom.ker φ.toRingHom)
    exact ⟨_, _, hloc, _, hc⟩
  obtain ⟨R, _, _, _, hc⟩ := key
  letI : Algebra O R := ((algebraMap D R).comp (algebraMap O D)).toAlgebra
  haveI : IsScalarTower O D R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hco, h1, h2⟩ := cpl_univ O D R φ hc
  exact ⟨R, _, _, hco, IsScalarTower.toAlgHom O D R, h1, h2⟩

/- English proof (translation)
Use `letI := Ideal.Quotient.field x`. Use `haveI : Finite (ResidueField B) := Finite.of_surjective _ (resMap_bijective O B).2`. Use `letI : Algebra (ResidueField B) (A ⧸ x) := (Ideal.Quotient.lift (maximalIdeal B) (algebraMap B (A ⧸ x)) fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hx ha)).toAlgebra`. Use `haveI : IsScalarTower B (ResidueField B) (A ⧸ x) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : Algebra.FiniteType (ResidueField B) (A ⧸ x) := Algebra.FiniteType.of_restrictScalars_finiteType B _ _`.

Use `haveI : Module.Finite (ResidueField B) (A ⧸ x) := finite_of_finite_type_of_isJacobsonRing _ _`. Conclude with `Module.finite_of_finite (ResidueField B)`.
-/
private theorem res_fin (O B A : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing B] [Algebra O B]
    [IsCO O B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A] (x : Ideal A) [x.IsMaximal]
    (hx : maximalIdeal B ≤ x.comap (algebraMap B A)) : Finite (A ⧸ x) := by
  letI := Ideal.Quotient.field x
  haveI : Finite (ResidueField B) := Finite.of_surjective _ (resMap_bijective O B).2
  letI : Algebra (ResidueField B) (A ⧸ x) := (Ideal.Quotient.lift (maximalIdeal B) (algebraMap B (A ⧸ x))
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hx ha)).toAlgebra
  haveI : IsScalarTower B (ResidueField B) (A ⧸ x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType (ResidueField B) (A ⧸ x) := Algebra.FiniteType.of_restrictScalars_finiteType B _ _
  haveI : Module.Finite (ResidueField B) (A ⧸ x) := finite_of_finite_type_of_isJacobsonRing _ _
  exact Module.finite_of_finite (ResidueField B)

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn S x hx hB`. Establish `hA : IsNoetherianRing S.A` using `(gr_A hF hn S).2.2.2.2.2.1`. Establish `hT : Algebra.FiniteType S.B S.A` using `(gr_A hF hn S).2.2.2.2.1`. Take `⟨hco, hm⟩` from `co_B hF hn S`. Rewrite `hB` using `[← hm]`.

Use `haveI : Finite (S.A ⧸ x) := res_fin O S.B S.A x hB`. Use `letI := Ideal.Quotient.field x`. Take `⟨O', _, _, _, _, _, _, hu, ⟨e⟩⟩` from `unr_ex (l := l) O (S.A ⧸ x) fun a ha => by`. Establish `h1 : algebraMap O S.B a ∈ maximalIdeal S.B` using `fun h => ha (IsLocalHom.map_nonunit a h)`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hB h1)`.

Establish `hD : IsNoetherianRing (TensorProduct O O' S.A)`. Establish `h1 : IsNoetherianRing (TensorProduct O S.A O')` using `Algebra.FiniteType.isNoetherianRing S.A _`. Conclude with `isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm O S.A O').toRingEquiv`. Set `φ : TensorProduct O O' S.A →ₐ[O'] ResidueField O'` to `Algebra.TensorProduct.lift (Algebra.ofId _ _) (e.comp (Ideal.Quotient.mkₐ O x)) fun _ _ => Commute.all _ _`. Take `⟨R, _, _, _, j, h1, h2⟩` from `cpl_ex O' _ φ`.

Use `letI : Algebra O R := ((algebraMap O' R).comp (algebraMap O O')).toAlgebra`. Use `haveI : IsScalarTower O O' R := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hφ : ∀ a : S.A, φ (1 ⊗ₜ a) = e (Ideal.Quotient.mk x a)` using `fun a => by simp [φ]`. Use `⟨{ O' := O' unr := hu R := R ι := (j.restrictScalars O).comp Algebra.TensorProduct.includeRight lies := ?_ univ := fun C _ _ _ _ _ f hf => ?_ }⟩` and prove the remaining obligations. Use extensionality with `a`.

Rewrite using `[Ideal.mem_comap, ← res_eq_zero_iff O', ← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff e e.toRingHom.injective, ← hφ, ← h1]`. Both sides reduce to the same expression. Set `f' : TensorProduct O O' S.A →ₐ[O'] C` to `Algebra.TensorProduct.lift (Algebra.ofId _ _) f fun _ _ => Commute.all _ _`. Establish `hf' : ∀ a : S.A, f' (1 ⊗ₜ a) = f a` using `fun a => by simp [f']`. Establish `e1 : (res O' C).comp f' = φ` using `Algebra.TensorProduct.ext (by ext) (by`.

Use extensionality with `a`. Use `show res O' C (f' (1 ⊗ₜ a)) = φ (1 ⊗ₜ a)`. Rewrite using `[hf', hf, ← h1]`. Use the proof step `rfl)`. Take `⟨g, hg, hu⟩` from `h2 C f' fun a => DFunLike.congr_fun e1 a`.

Use `⟨g, fun a => (hg _).trans (hf' a), fun g' hg' => hu g' fun a => ?_⟩` and prove the remaining obligations. Establish `e2 : g'.comp j = f'` using `Algebra.TensorProduct.ext (by ext) (by`. Use extensionality with `a`. Use `show g' (j (1 ⊗ₜ a)) = f' (1 ⊗ₜ a)`. Rewrite using `[hf']`.

Conclude with `hg' a)`. Conclude with `DFunLike.congr_fun e2 a`.
-/
theorem UpperTheory.V.Fr.loc_ex :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ x : Ideal S.A, x.IsMaximal → S.mB ≤ S.π x → Nonempty (S.Loc x) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x hx hB
  have hA : IsNoetherianRing S.A := (gr_A hF hn S).2.2.2.2.2.1
  have hT : Algebra.FiniteType S.B S.A := (gr_A hF hn S).2.2.2.2.1
  obtain ⟨hco, hm⟩ := co_B hF hn S
  rw [← hm] at hB
  haveI : Finite (S.A ⧸ x) := res_fin O S.B S.A x hB
  letI := Ideal.Quotient.field x
  obtain ⟨O', _, _, _, _, _, _, hu, ⟨e⟩⟩ := unr_ex (l := l) O (S.A ⧸ x) fun a ha => by
    have h1 : algebraMap O S.B a ∈ maximalIdeal S.B := fun h => ha (IsLocalHom.map_nonunit a h)
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hB h1)
  have hD : IsNoetherianRing (TensorProduct O O' S.A) := by
    have h1 : IsNoetherianRing (TensorProduct O S.A O') :=
      Algebra.FiniteType.isNoetherianRing S.A _
    exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm O S.A O').toRingEquiv
  let φ : TensorProduct O O' S.A →ₐ[O'] ResidueField O' :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) (e.comp (Ideal.Quotient.mkₐ O x)) fun _ _ => Commute.all _ _
  obtain ⟨R, _, _, _, j, h1, h2⟩ := cpl_ex O' _ φ
  letI : Algebra O R := ((algebraMap O' R).comp (algebraMap O O')).toAlgebra
  haveI : IsScalarTower O O' R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hφ : ∀ a : S.A, φ (1 ⊗ₜ a) = e (Ideal.Quotient.mk x a) := fun a => by simp [φ]
  refine ⟨{
    O' := O'
    unr := hu
    R := R
    ι := (j.restrictScalars O).comp Algebra.TensorProduct.includeRight
    lies := ?_
    univ := fun C _ _ _ _ _ f hf => ?_ }⟩
  · ext a
    rw [Ideal.mem_comap, ← res_eq_zero_iff O', ← Ideal.Quotient.eq_zero_iff_mem,
      ← map_eq_zero_iff e e.toRingHom.injective, ← hφ, ← h1]
    rfl
  · let f' : TensorProduct O O' S.A →ₐ[O'] C :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) f fun _ _ => Commute.all _ _
    have hf' : ∀ a : S.A, f' (1 ⊗ₜ a) = f a := fun a => by simp [f']
    have e1 : (res O' C).comp f' = φ := Algebra.TensorProduct.ext (by ext) (by
      ext a
      show res O' C (f' (1 ⊗ₜ a)) = φ (1 ⊗ₜ a)
      rw [hf', hf, ← h1]; rfl)
    obtain ⟨g, hg, hu⟩ := h2 C f' fun a => DFunLike.congr_fun e1 a
    refine ⟨g, fun a => (hg _).trans (hf' a), fun g' hg' => hu g' fun a => ?_⟩
    have e2 : g'.comp j = f' := Algebra.TensorProduct.ext (by ext) (by
      ext a
      show g' (j (1 ⊗ₜ a)) = f' (1 ⊗ₜ a)
      rw [hf']; exact hg' a)
    exact DFunLike.congr_fun e2 a

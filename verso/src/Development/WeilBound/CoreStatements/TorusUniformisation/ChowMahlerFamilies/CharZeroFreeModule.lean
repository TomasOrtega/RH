import Mathlib
open NumberField

namespace PositivityTheory.Xgn.CharZeroFreeModule
open Polynomial

section chi
variable (k : Type) [Field k]

noncomputable def chi (M : Type) [AddCommGroup M] [Module k M] [Module k[X] M]
    [IsScalarTower k k[X] M] [FiniteDimensional k M] : k[X] :=
  (Algebra.lsmul k k M (X : k[X])).charpoly

variable {k}
variable {M N : Type} [AddCommGroup M] [Module k M] [Module k[X] M]
    [IsScalarTower k k[X] M] [FiniteDimensional k M]
    [AddCommGroup N] [Module k N] [Module k[X] N]
    [IsScalarTower k k[X] N] [FiniteDimensional k N]

/- English proof (translation)
The claim follows from `LinearMap.charpoly_monic _`.
-/
theorem chi_monic : (chi k M).Monic := LinearMap.charpoly_monic _

/- English proof (translation)
The claim follows from `LinearMap.charpoly_natDegree _`.
-/
theorem chi_natDegree : (chi k M).natDegree = Module.finrank k M :=
  LinearMap.charpoly_natDegree _

/- English proof (translation)
Establish `h` using `LinearMap.aeval_self_charpoly (Algebra.lsmul k k M (X : k[X]))`. Rewrite `h` using `[Polynomial.aeval_algHom_apply, aeval_X_left_apply]`. Conclude with `congrArg (fun f => f m) h`.
-/
theorem chi_smul (m : M) : chi k M • m = 0 := by
  have h := LinearMap.aeval_self_charpoly (Algebra.lsmul k k M (X : k[X]))
  rw [Polynomial.aeval_algHom_apply, aeval_X_left_apply] at h
  exact congrArg (fun f => f m) h

/- English proof (translation)
Unfold `chi`. Rewrite using `[← LinearEquiv.charpoly_conj (e.restrictScalars k)]`. Use `congr 1`. Use extensionality with `n`. Simplify using `[LinearEquiv.conj_apply]`.
-/
theorem chi_equiv (e : M ≃ₗ[k[X]] N) : chi k M = chi k N := by
  unfold chi
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k)]
  congr 1
  ext n
  simp [LinearEquiv.conj_apply]

/- English proof (translation)
Unfold `chi`. Rewrite using `[← LinearMap.charpoly_prodMap]`. Use `congr 1`.
-/
theorem chi_prod : chi k (M × N) = chi k M * chi k N := by
  unfold chi
  rw [← LinearMap.charpoly_prodMap]
  congr 1

/- English proof (translation)
Take `⟨I, hI, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule k[X] M›`. Take `⟨q, rfl⟩ : ∃ q, I = Ideal.span {q}` from `⟨_, (Ideal.span_singleton_generator I).symm⟩`. Establish `hd : q ∣ chi k M`. Establish `h` using `congrArg e (chi_smul (k := k) (e.symm 1))`. Rewrite `h` using `[map_smul, e.apply_symm_apply, map_zero, Algebra.smul_def, mul_one]`.

Conclude with `Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)`. Establish `h0 : chi k M ≠ 0` using `chi_monic.ne_zero`. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`. Conclude with `h0 (zero_dvd_iff.mp hd)`.

Establish `hdeg : (chi k M).natDegree = q.natDegree`. Rewrite using `[chi_natDegree, (e.restrictScalars k).finrank_eq, finrank_quotient_span_eq_natDegree]`. Establish `ha : Associated q (chi k M)` using `associated_of_dvd_of_natDegree_le hd h0 hdeg.le`. Establish `hp : Prime q` using `(Ideal.span_singleton_prime hq0).mp hI.isPrime`. Use `⟨ha.irreducible hp.irreducible, ⟨e.trans (Submodule.quotEquivOfEq _ _ ?_)⟩⟩` and prove the remaining obligations.

Conclude with `Ideal.span_singleton_eq_span_singleton.mpr ha`.
-/
theorem chi_simple [IsSimpleModule k[X] M] :
    Irreducible (chi k M) ∧ Nonempty (M ≃ₗ[k[X]] k[X] ⧸ Ideal.span {chi k M}) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule k[X] M›
  obtain ⟨q, rfl⟩ : ∃ q, I = Ideal.span {q} := ⟨_, (Ideal.span_singleton_generator I).symm⟩
  have hd : q ∣ chi k M := by
    have h := congrArg e (chi_smul (k := k) (e.symm 1))
    rw [map_smul, e.apply_symm_apply, map_zero, Algebra.smul_def, mul_one] at h
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h0 : chi k M ≠ 0 := chi_monic.ne_zero
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact h0 (zero_dvd_iff.mp hd)
  have hdeg : (chi k M).natDegree = q.natDegree := by
    rw [chi_natDegree, (e.restrictScalars k).finrank_eq, finrank_quotient_span_eq_natDegree]
  have ha : Associated q (chi k M) :=
    associated_of_dvd_of_natDegree_le hd h0 hdeg.le
  have hp : Prime q := (Ideal.span_singleton_prime hq0).mp hI.isPrime
  refine ⟨ha.irreducible hp.irreducible, ⟨e.trans (Submodule.quotEquivOfEq _ _ ?_)⟩⟩
  exact Ideal.span_singleton_eq_span_singleton.mpr ha

instance subFin (T : Submodule k[X] M) : FiniteDimensional k T :=
  Module.Finite.of_injective (T.subtype.restrictScalars k) T.injective_subtype

omit [Module k M] [IsScalarTower k k[X] M] [FiniteDimensional k M] in
/- English proof (translation)
Take `⟨T', h⟩` from `exists_isCompl T`. Conclude with `⟨T', ⟨(Submodule.prodEquivOfIsCompl _ _ h).symm⟩⟩`.
-/
theorem exists_split [IsSemisimpleModule k[X] M] (T : Submodule k[X] M) :
    ∃ T' : Submodule k[X] M, Nonempty (M ≃ₗ[k[X]] T × T') := by
  obtain ⟨T', h⟩ := exists_isCompl T
  exact ⟨T', ⟨(Submodule.prodEquivOfIsCompl _ _ h).symm⟩⟩

/- English proof (translation)
Use `haveI : Nontrivial S := IsSimpleModule.nontrivial k[X] S`. Rewrite using `[(e.restrictScalars k).finrank_eq, Module.finrank_prod]`. Establish `: 0 < Module.finrank k S` using `Module.finrank_pos`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_lt_of_split {S T : Submodule k[X] M} [IsSimpleModule k[X] S]
    (e : M ≃ₗ[k[X]] S × T) : Module.finrank k T < Module.finrank k M := by
  haveI : Nontrivial S := IsSimpleModule.nontrivial k[X] S
  rw [(e.restrictScalars k).finrank_eq, Module.finrank_prod]
  have : 0 < Module.finrank k S := Module.finrank_pos
  omega

end chi

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `M _ _ _ _ _ _ hn hd`. Break down `subsingleton_or_nontrivial M with hM | hM` into its components or cases. It suffices to derive a contradiction.

Establish `h1 : chi k M = 1`. Rewrite using `[← chi_monic.natDegree_eq_zero, chi_natDegree]`. Conclude with `Module.finrank_zero_of_subsingleton`. Rewrite `hd` using `[h1]`. Conclude with `hp.not_isUnit (isUnit_of_dvd_one hd)`.

Take `⟨S, hS⟩` from `IsSemisimpleModule.exists_simple_submodule k[X] M`. Take `⟨T, ⟨e⟩⟩` from `exists_split S`. Rewrite `hd` using `[chi_equiv e, chi_prod]`. Break down `hp.prime.dvd_or_dvd hd with h | h` into its components or cases. Conclude with `⟨S, hS, (eq_of_monic_of_associated hm chi_monic (hp.associated_of_dvd chi_simple.1 h)).symm⟩`.

Take `⟨U, hU, hc⟩` from `ih _ (hn ▸ finrank_lt_of_split e) T rfl h`. Establish `e'` using `U.equivMapOfInjective T.subtype T.injective_subtype`. Conclude with `⟨U.map T.subtype, IsSimpleModule.congr e'.symm, (chi_equiv e').symm.trans hc⟩`.
-/
theorem exists_simple_of_dvd {k : Type} [Field k] (p : k[X]) (hp : Irreducible p) (hm : p.Monic)
    (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module k M] [Module k[X] M]
    [IsScalarTower k k[X] M] [FiniteDimensional k M] [IsSemisimpleModule k[X] M],
    Module.finrank k M = n → p ∣ chi k M →
    ∃ T : Submodule k[X] M, IsSimpleModule k[X] T ∧ chi k T = p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ _ hn hd
  rcases subsingleton_or_nontrivial M with hM | hM
  · exfalso
    have h1 : chi k M = 1 := by
      rw [← chi_monic.natDegree_eq_zero, chi_natDegree]
      exact Module.finrank_zero_of_subsingleton
    rw [h1] at hd
    exact hp.not_isUnit (isUnit_of_dvd_one hd)
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule k[X] M
  obtain ⟨T, ⟨e⟩⟩ := exists_split S
  rw [chi_equiv e, chi_prod] at hd
  rcases hp.prime.dvd_or_dvd hd with h | h
  · exact ⟨S, hS, (eq_of_monic_of_associated hm chi_monic
      (hp.associated_of_dvd chi_simple.1 h)).symm⟩
  · obtain ⟨U, hU, hc⟩ := ih _ (hn ▸ finrank_lt_of_split e) T rfl h
    have e' := U.equivMapOfInjective T.subtype T.injective_subtype
    exact ⟨U.map T.subtype, IsSimpleModule.congr e'.symm, (chi_equiv e').symm.trans hc⟩

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `M N _ _ _ _ _ _ _ _ _ _ _ _ hn hc`. Break down `subsingleton_or_nontrivial M with hM | hM` into its components or cases. Establish `h : Module.finrank k N = 0`.

Rewrite using `[← chi_natDegree, ← hc, chi_natDegree]`. Conclude with `Module.finrank_zero_of_subsingleton`. Use `haveI : Subsingleton N := Module.finrank_zero_iff.mp h`. Conclude with `⟨LinearEquiv.ofSubsingleton _ _⟩`. Take `⟨S, hS⟩` from `IsSemisimpleModule.exists_simple_submodule k[X] M`.

Take `⟨T, ⟨e⟩⟩` from `exists_split S`. Establish `h1 : chi k M = chi k S * chi k T` using `by rw [chi_equiv e, chi_prod]`. Take `⟨S', hS', hc'⟩` from `exists_simple_of_dvd (chi k S) chi_simple.1 chi_monic _ N rfl ⟨_, hc.symm.trans h1⟩`. Take `⟨T', ⟨e'⟩⟩` from `exists_split S'`. Establish `h2 : chi k N = chi k S' * chi k T'` using `by rw [chi_equiv e', chi_prod]`.

Establish `h3 : chi k T = chi k T'`. Rewrite `hc` using `[h1, h2, hc']`. Conclude with `mul_left_cancel₀ chi_monic.ne_zero hc`. Take `⟨f⟩` from `ih _ (hn ▸ finrank_lt_of_split e) T T' rfl h3`. Take `⟨g⟩` from `(chi_simple (k := k) (M := S)).2`.

Take `⟨g'⟩` from `(chi_simple (k := k) (M := S')).2`. Rewrite `g'` using `[hc']`. Conclude with `⟨e.trans (((g.trans g'.symm).prodCongr f).trans e'.symm)⟩`.
-/
theorem equiv_of_chi_eq {k : Type} [Field k]
    (n : ℕ) : ∀ (M N : Type) [AddCommGroup M] [Module k M] [Module k[X] M]
    [IsScalarTower k k[X] M] [FiniteDimensional k M] [IsSemisimpleModule k[X] M]
    [AddCommGroup N] [Module k N] [Module k[X] N]
    [IsScalarTower k k[X] N] [FiniteDimensional k N] [IsSemisimpleModule k[X] N],
    Module.finrank k M = n → chi k M = chi k N → Nonempty (M ≃ₗ[k[X]] N) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M N _ _ _ _ _ _ _ _ _ _ _ _ hn hc
  rcases subsingleton_or_nontrivial M with hM | hM
  · have h : Module.finrank k N = 0 := by
      rw [← chi_natDegree, ← hc, chi_natDegree]
      exact Module.finrank_zero_of_subsingleton
    haveI : Subsingleton N := Module.finrank_zero_iff.mp h
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule k[X] M
  obtain ⟨T, ⟨e⟩⟩ := exists_split S
  have h1 : chi k M = chi k S * chi k T := by rw [chi_equiv e, chi_prod]
  obtain ⟨S', hS', hc'⟩ := exists_simple_of_dvd (chi k S) chi_simple.1 chi_monic _ N rfl
    ⟨_, hc.symm.trans h1⟩
  obtain ⟨T', ⟨e'⟩⟩ := exists_split S'
  have h2 : chi k N = chi k S' * chi k T' := by rw [chi_equiv e', chi_prod]
  have h3 : chi k T = chi k T' := by
    rw [h1, h2, hc'] at hc
    exact mul_left_cancel₀ chi_monic.ne_zero hc
  obtain ⟨f⟩ := ih _ (hn ▸ finrank_lt_of_split e) T T' rfl h3
  obtain ⟨g⟩ := (chi_simple (k := k) (M := S)).2
  obtain ⟨g'⟩ := (chi_simple (k := k) (M := S')).2
  rw [hc'] at g'
  exact ⟨e.trans (((g.trans g'.symm).prodCongr f).trans e'.symm)⟩

/- English proof (translation)
Unfold `chi`. Rewrite using `[← LinearEquiv.charpoly_conj (Module.AEval'.of f) f]`. Use `congr 1`. Use extensionality with `v`. Take `⟨v, rfl⟩` from `(Module.AEval'.of f).surjective v`.

Simplify using `[LinearEquiv.conj_apply, Module.AEval'.X_smul_of]`.
-/
theorem chi_aeval {k V : Type} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : Module.End k V) : chi k (Module.AEval' f) = f.charpoly := by
  unfold chi
  rw [← LinearEquiv.charpoly_conj (Module.AEval'.of f) f]
  congr 1
  ext v
  obtain ⟨v, rfl⟩ := (Module.AEval'.of f).surjective v
  simp [LinearEquiv.conj_apply, Module.AEval'.X_smul_of]

/- English proof (translation)
Use `haveI : IsSemisimpleModule k[X] (Module.AEval' f) := hf`. Use `haveI : IsSemisimpleModule k[X] (Module.AEval' g) := hg`. Take `⟨e⟩` from `equiv_of_chi_eq (k := k) _ (Module.AEval' f) (Module.AEval' g) rfl (by rw [chi_aeval, chi_aeval, h])`. Use `⟨(Module.AEval'.of f).trans ((e.restrictScalars k).trans (Module.AEval'.of g).symm), fun v => ?_⟩` and prove the remaining obligations. Apply `(Module.AEval'.of g).injective` to reduce the goal to its premises.

Simplify using `only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.restrictScalars_apply]`. Rewrite using `[← Module.AEval'.X_smul_of, ← Module.AEval'.X_smul_of, map_smul, LinearEquiv.apply_symm_apply]`.
-/
theorem conj_of_charpoly_eq {k V W : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (f : Module.End k V) (g : Module.End k W) (hf : f.IsSemisimple) (hg : g.IsSemisimple)
    (h : f.charpoly = g.charpoly) : ∃ e : V ≃ₗ[k] W, ∀ v, e (f v) = g (e v) := by
  haveI : IsSemisimpleModule k[X] (Module.AEval' f) := hf
  haveI : IsSemisimpleModule k[X] (Module.AEval' g) := hg
  obtain ⟨e⟩ := equiv_of_chi_eq (k := k) _ (Module.AEval' f) (Module.AEval' g) rfl
    (by rw [chi_aeval, chi_aeval, h])
  refine ⟨(Module.AEval'.of f).trans ((e.restrictScalars k).trans (Module.AEval'.of g).symm),
    fun v => ?_⟩
  apply (Module.AEval'.of g).injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.restrictScalars_apply]
  rw [← Module.AEval'.X_smul_of, ← Module.AEval'.X_smul_of, map_smul,
    LinearEquiv.apply_symm_apply]

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Rewrite using `[pow_zero, ← (LinearMap.charpoly_monic _).natDegree_eq_zero, LinearMap.charpoly_natDegree]`. Conclude with `Module.finrank_zero_of_subsingleton`. Consider the case `succ r ih`.

Rewrite using `[pow_succ', ← ih, ← LinearMap.charpoly_prodMap, ← LinearEquiv.charpoly_conj (Fin.consLinearEquiv k (fun _ : Fin (r + 1) => V))]`. Use `congr 1`. Use `LinearMap.ext fun v => funext fun i => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[LinearEquiv.conj_apply]`.

Simplify using `[LinearEquiv.conj_apply, Fin.tail]`.
-/
theorem charpoly_compLeft {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : Module.End k V) (r : ℕ) :
    LinearMap.charpoly (f.compLeft (Fin r)) = f.charpoly ^ r := by
  induction r with
  | zero =>
    rw [pow_zero, ← (LinearMap.charpoly_monic _).natDegree_eq_zero, LinearMap.charpoly_natDegree]
    exact Module.finrank_zero_of_subsingleton
  | succ r ih =>
    rw [pow_succ', ← ih, ← LinearMap.charpoly_prodMap,
      ← LinearEquiv.charpoly_conj (Fin.consLinearEquiv k (fun _ : Fin (r + 1) => V))]
    congr 1
    refine LinearMap.ext fun v => funext fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [LinearEquiv.conj_apply]
    · simp [LinearEquiv.conj_apply, Fin.tail]

/- English proof (translation)
Establish `h` using `Polynomial.aeval_algHom_apply ρ.toIntAlgHom a P`. Establish `h2` using `Polynomial.aeval_map_algebraMap k (ρ a) P`. Conclude with `h2.trans h`.
-/
theorem aeval_rho {R k W : Type} [CommRing R] [Field k] [AddCommGroup W] [Module k W]
    (ρ : R →+* Module.End k W) (a : R) (P : ℤ[X]) :
    aeval (ρ a) (P.map (Int.castRingHom k)) = ρ (aeval a P) := by
  have h := Polynomial.aeval_algHom_apply ρ.toIntAlgHom a P
  have h2 := Polynomial.aeval_map_algebraMap k (ρ a) P
  exact h2.trans h

/- English proof (translation)
Establish `hi : IsIntegral ℤ a` using `Algebra.IsIntegral.isIntegral a`. Establish `h1 : minpoly ℚ (algebraMap (𝓞 E) E a) = (minpoly ℤ a).map (algebraMap ℤ ℚ)` using `minpoly.isIntegrallyClosed_eq_field_fractions ℚ E hi`. Establish `h2 : ((minpoly ℤ a).map (algebraMap ℤ ℚ)).Separable`. Rewrite using `[← h1]`. Conclude with `(minpoly.irreducible (Algebra.IsIntegral.isIntegral _)).separable`.

Establish `h3 : ((minpoly ℤ a).map (Int.castRingHom k)).Separable`. Use `h2.map (f := algebraMap ℚ k)` as an intermediate fact. Rewrite `this` using `[Polynomial.map_map]`. Rewrite `this` using `[RingHom.eq_intCast' ((algebraMap ℚ k).comp (algebraMap ℤ ℚ))]`. Then use the resulting hypothesis. Use `Module.End.isSemisimple_of_squarefree_aeval_eq_zero h3.squarefree ?_` and prove the remaining obligations.

Rewrite using `[aeval_rho, minpoly.aeval, map_zero]`.
-/
theorem rho_semisimple {E : Type} [Field E] [NumberField E] {k W : Type} [Field k] [CharZero k]
    [AddCommGroup W] [Module k W] (ρ : 𝓞 E →+* Module.End k W) (a : 𝓞 E) :
    (ρ a).IsSemisimple := by
  have hi : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
  have h1 : minpoly ℚ (algebraMap (𝓞 E) E a) = (minpoly ℤ a).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ E hi
  have h2 : ((minpoly ℤ a).map (algebraMap ℤ ℚ)).Separable := by
    rw [← h1]
    exact (minpoly.irreducible (Algebra.IsIntegral.isIntegral _)).separable
  have h3 : ((minpoly ℤ a).map (Int.castRingHom k)).Separable := by
    have := h2.map (f := algebraMap ℚ k)
    rw [Polynomial.map_map] at this
    rwa [RingHom.eq_intCast' ((algebraMap ℚ k).comp (algebraMap ℤ ℚ))] at this
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero h3.squarefree ?_
  rw [aeval_rho, minpoly.aeval, map_zero]

/- English proof (translation)
Take `⟨α, hα⟩` from `Field.exists_primitive_element ℚ E`. Establish `halg : IsAlgebraic ℤ α` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic α)`. Take `⟨y, hy, hint⟩` from `halg.exists_integral_multiple`. Take `⟨a, ha⟩ : ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = y • α` from `⟨⟨y • α, hint⟩, rfl⟩`. Use `⟨a, fun b => ?_⟩` and prove the remaining obligations.

Establish `hb : (b : E) ∈ Algebra.adjoin ℚ {α}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic α), hα]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `hb` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨Q, hQ⟩` from `hb`.

Establish `hQ' : aeval (y • α) (Q.comp (C (y : ℚ)⁻¹ * X)) = (b : E)`. Establish `hy' : (y : E) ≠ 0` using `Int.cast_ne_zero.mpr hy`. Rewrite using `[aeval_comp]`. Simplify using `only [map_mul, aeval_C, aeval_X, map_inv₀, map_intCast, zsmul_eq_mul]`. Rewrite using `[inv_mul_cancel_left₀ hy']`.

Conclude with `hQ`. Take `⟨N, hN, hs⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (Q.comp (C (y : ℚ)⁻¹ * X))`. Use `⟨N, IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q.comp (C (y : ℚ)⁻¹ * X)), nonZeroDivisors.ne_zero hN, ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Rewrite using `[← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap ℚ, hs, ha]`.

Simplify using `only [map_zsmul]`. Use `congr 1`. Conclude with `hQ'.symm`.
-/
theorem exists_gen (E : Type) [Field E] [NumberField E] :
    ∃ a : 𝓞 E, ∀ b : 𝓞 E, ∃ (N : ℤ) (P : ℤ[X]), N ≠ 0 ∧ N • b = aeval a P := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  have halg : IsAlgebraic ℤ α :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = y • α := ⟨⟨y • α, hint⟩, rfl⟩
  refine ⟨a, fun b => ?_⟩
  have hb : (b : E) ∈ Algebra.adjoin ℚ {α} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α), hα]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
  obtain ⟨Q, hQ⟩ := hb
  have hQ' : aeval (y • α) (Q.comp (C (y : ℚ)⁻¹ * X)) = (b : E) := by
    have hy' : (y : E) ≠ 0 := Int.cast_ne_zero.mpr hy
    rw [aeval_comp]
    simp only [map_mul, aeval_C, aeval_X, map_inv₀, map_intCast, zsmul_eq_mul]
    rw [inv_mul_cancel_left₀ hy']
    exact hQ
  obtain ⟨N, hN, hs⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ)
    (Q.comp (C (y : ℚ)⁻¹ * X))
  refine ⟨N, IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q.comp (C (y : ℚ)⁻¹ * X)),
    nonZeroDivisors.ne_zero hN, ?_⟩
  apply RingOfIntegers.coe_injective
  rw [← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap ℚ, hs, ha]
  simp only [map_zsmul]
  congr 1
  exact hQ'.symm

end PositivityTheory.Xgn.CharZeroFreeModule

open PositivityTheory.Xgn.CharZeroFreeModule in
/- English proof (translation)
Introduce `E _ _ k W _ _ _ _ _ r ρ hρ`. Take `⟨a, ha⟩` from `exists_gen E`. Set `ρ0 : 𝓞 E →+* Module.End k (Fin r → TensorProduct ℤ k (𝓞 E))` to `(Algebra.lsmul k k (Fin r → TensorProduct ℤ k (𝓞 E)) : TensorProduct ℤ k (𝓞 E) →ₐ[k] _).toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := k) (B := 𝓞 E)).toRingHom`. Establish `hρ0 : ∀ b v i, ρ0 b v i = ((1 : k) ⊗ₜ[ℤ] b) * v i` using `fun _ _ _ => rfl`. Establish `hc : (ρ0 a).charpoly = (ρ a).charpoly`.

Establish `h1 : ρ0 a = LinearMap.compLeft (LinearMap.baseChange k (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E))) (Fin r)`. Rewrite using `[Algebra.baseChange_lmul]`. Both sides reduce to the same expression. Rewrite using `[hρ a, h1, charpoly_compLeft, LinearMap.charpoly_baseChange]`. Both sides reduce to the same expression.

Take `⟨e, he⟩` from `conj_of_charpoly_eq _ _ (rho_semisimple ρ0 a) (rho_semisimple ρ a) hc`. Establish `hp : ∀ (P : Polynomial ℤ) v, e (ρ0 (Polynomial.aeval a P) v) = ρ (Polynomial.aeval a P) (e v)`. Introduce `P`. Proceed by induction on `P using Polynomial.induction_on with`. Consider the case `C c`.

Introduce `v`. Rewrite using `[Polynomial.aeval_C, eq_intCast, map_intCast, map_intCast, Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul]`. Consider the case `add p q hp hq => intro v`. Simplify using `[hp, hq]`. Consider the case `monomial n c h`.

Introduce `v`. Rewrite using `[pow_succ, ← mul_assoc, map_mul (Polynomial.aeval a), Polynomial.aeval_X, map_mul ρ0, map_mul ρ, Module.End.mul_apply, Module.End.mul_apply, h, he]`. Establish `hb : ∀ b v, e (ρ0 b v) = ρ b (e v)`. Introduce `b v`. Take `⟨N, P, hN, h⟩` from `ha b`.

Use `hp P v` as an intermediate fact. Rewrite `this` using `[← h, map_zsmul, map_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul, ← Int.cast_smul_eq_zsmul k, ← Int.cast_smul_eq_zsmul k]`. Conclude with `smul_right_injective W (Int.cast_ne_zero.mpr hN) this`. Set `B` to `((Pi.basis fun _ : Fin r => (RingOfIntegers.basis E).baseChange k).reindex (Equiv.sigmaEquivProd _ _)).map e`. Establish `hB : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (e (Pi.single q.1 1))) = B`.

Use function extensionality and compare the values at `⟨i, j⟩`. Simplify using `only [B, Module.Basis.map_apply, Module.Basis.reindex_apply]`. Rewrite using `[← hb]`. Use `congr 1`. Use function extensionality and compare the values at `l`.

Rewrite using `[hρ0]`. Simplify using `only [Equiv.sigmaEquivProd_symm_apply, Pi.basis_apply, Module.Basis.baseChange_apply]`. Distinguish the cases in `h : l = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`. Use `⟨fun i => e (Pi.single i 1), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hB]`. Conclude with `B.linearIndependent`. Rewrite using `[hB]`.

Conclude with `B.span_eq`.
-/
theorem PositivityTheory.Xgn.char_zero_free_module : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [CharZero k] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  intro E _ _ k W _ _ _ _ _ r ρ hρ
  obtain ⟨a, ha⟩ := exists_gen E
  let ρ0 : 𝓞 E →+* Module.End k (Fin r → TensorProduct ℤ k (𝓞 E)) :=
    (Algebra.lsmul k k (Fin r → TensorProduct ℤ k (𝓞 E)) :
      TensorProduct ℤ k (𝓞 E) →ₐ[k] _).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := k) (B := 𝓞 E)).toRingHom
  have hρ0 : ∀ b v i, ρ0 b v i = ((1 : k) ⊗ₜ[ℤ] b) * v i := fun _ _ _ => rfl
  have hc : (ρ0 a).charpoly = (ρ a).charpoly := by
    have h1 : ρ0 a = LinearMap.compLeft
        (LinearMap.baseChange k (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E))) (Fin r) := by
      rw [Algebra.baseChange_lmul]
      rfl
    rw [hρ a, h1, charpoly_compLeft, LinearMap.charpoly_baseChange]
    rfl
  obtain ⟨e, he⟩ := conj_of_charpoly_eq _ _ (rho_semisimple ρ0 a) (rho_semisimple ρ a) hc
  have hp : ∀ (P : Polynomial ℤ) v, e (ρ0 (Polynomial.aeval a P) v) =
      ρ (Polynomial.aeval a P) (e v) := by
    intro P
    induction P using Polynomial.induction_on with
    | C c =>
      intro v
      rw [Polynomial.aeval_C, eq_intCast, map_intCast, map_intCast, Module.End.intCast_apply,
        Module.End.intCast_apply, map_zsmul]
    | add p q hp hq => intro v; simp [hp, hq]
    | monomial n c h =>
      intro v
      rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval a), Polynomial.aeval_X, map_mul ρ0,
        map_mul ρ, Module.End.mul_apply, Module.End.mul_apply, h, he]
  have hb : ∀ b v, e (ρ0 b v) = ρ b (e v) := by
    intro b v
    obtain ⟨N, P, hN, h⟩ := ha b
    have := hp P v
    rw [← h, map_zsmul, map_zsmul, LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul,
      ← Int.cast_smul_eq_zsmul k, ← Int.cast_smul_eq_zsmul k] at this
    exact smul_right_injective W (Int.cast_ne_zero.mpr hN) this
  let B := ((Pi.basis fun _ : Fin r => (RingOfIntegers.basis E).baseChange k).reindex
    (Equiv.sigmaEquivProd _ _)).map e
  have hB : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      ρ (RingOfIntegers.basis E q.2) (e (Pi.single q.1 1))) = B := by
    funext ⟨i, j⟩
    simp only [B, Module.Basis.map_apply, Module.Basis.reindex_apply]
    rw [← hb]
    congr 1
    funext l
    rw [hρ0]
    simp only [Equiv.sigmaEquivProd_symm_apply, Pi.basis_apply, Module.Basis.baseChange_apply]
    by_cases h : l = i
    · subst h; simp
    · simp [h]
  refine ⟨fun i => e (Pi.single i 1), ?_, ?_⟩
  · rw [hB]; exact B.linearIndependent
  · rw [hB]; exact B.span_eq

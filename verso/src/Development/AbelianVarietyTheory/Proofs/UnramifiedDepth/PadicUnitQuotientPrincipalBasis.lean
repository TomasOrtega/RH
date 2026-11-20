import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Formalism.LocalToGlobal.ProjectiveLattices.AvMono
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueMaximalAbovePlace
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DifferentPowerUnramifiedIff

noncomputable section

namespace GlobalTheory.PlaceMono

section SlopeTestRemainingChoices

open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

/- English proof (translation)
Establish `hkrull : ⨅ i : ℕ, (IsLocalRing.maximalIdeal A) ^ i = ⊥` using `Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top`. Establish `hfac : ∀ a : A, a ≠ 0 → ∃ (k : ℕ) (u : A), IsUnit u ∧ a = π ^ k * u`. Introduce `a ha`. Establish `hex : ∃ n : ℕ, a ∉ (IsLocalRing.maximalIdeal A) ^ n`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `ha` to reduce the goal to its premises. Establish `hmem : a ∈ ⨅ i : ℕ, (IsLocalRing.maximalIdeal A) ^ i` using `Submodule.mem_iInf _ |>.2 h`. Rewrite `hmem` using `[hkrull, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `hn : a ∉ (IsLocalRing.maximalIdeal A) ^ Nat.find hex` using `Nat.find_spec hex`.

Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by`. Use `Nat.exists_eq_succ_of_ne_zero fun h0 => hn ?_` and prove the remaining obligations. Rewrite using `[h0, pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`. Establish `hak : a ∈ (IsLocalRing.maximalIdeal A) ^ k`.

Assume the negation of the conclusion as `h`. Conclude with `Nat.find_min hex (by omega) h`. Rewrite `hak` using `[hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Take `⟨u, hu⟩` from `hak`. Use `⟨k, u, ?_, by rw [← hu, mul_comm]⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hu'`. Apply `hn` to reduce the goal to its premises. Establish `hum : u ∈ IsLocalRing.maximalIdeal A` using `(IsLocalRing.mem_maximalIdeal u).2 hu'`. Rewrite `hum` using `[hπ, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `hum`.

Rewrite using `[hk, hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Conclude with `⟨c, by rw [← hu, ← hc, pow_succ]; ring⟩`. Establish `hnzd : NoZeroDivisors A`. Use `⟨fun {a b} hab => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Take `⟨k, u, hu, rfl⟩` from `hfac a h.1`. Take `⟨l, v, hv, rfl⟩` from `hfac b h.2`. Establish `h1 : (u * v) * π ^ (k + l) = 0` using `by rw [← hab]; ring`. Establish `h2 : u * v = 0` using `(mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hreg (k + l))).1 h1`.

Conclude with `(hu.mul hv).ne_zero h2`. Conclude with `NoZeroDivisors.to_isDomain A`.
-/
private theorem isDomain_of_span {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {π : A} (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (hreg : π ∈ nonZeroDivisors A) :
    IsDomain A := by
  classical
  have hkrull : ⨅ i : ℕ, (IsLocalRing.maximalIdeal A) ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top

  have hfac : ∀ a : A, a ≠ 0 → ∃ (k : ℕ) (u : A), IsUnit u ∧ a = π ^ k * u := by
    intro a ha
    have hex : ∃ n : ℕ, a ∉ (IsLocalRing.maximalIdeal A) ^ n := by
      by_contra h
      push_neg at h
      apply ha
      have hmem : a ∈ ⨅ i : ℕ, (IsLocalRing.maximalIdeal A) ^ i := Submodule.mem_iInf _ |>.2 h
      rwa [hkrull, Ideal.mem_bot] at hmem
    have hn : a ∉ (IsLocalRing.maximalIdeal A) ^ Nat.find hex := Nat.find_spec hex
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero fun h0 => hn ?_
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    have hak : a ∈ (IsLocalRing.maximalIdeal A) ^ k := by
      by_contra h
      exact Nat.find_min hex (by omega) h
    rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hak
    obtain ⟨u, hu⟩ := hak
    refine ⟨k, u, ?_, by rw [← hu, mul_comm]⟩
    by_contra hu'
    apply hn
    have hum : u ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal u).2 hu'
    rw [hπ, Ideal.mem_span_singleton'] at hum
    obtain ⟨c, hc⟩ := hum
    rw [hk, hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨c, by rw [← hu, ← hc, pow_succ]; ring⟩
  have hnzd : NoZeroDivisors A := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨k, u, hu, rfl⟩ := hfac a h.1
    obtain ⟨l, v, hv, rfl⟩ := hfac b h.2
    have h1 : (u * v) * π ^ (k + l) = 0 := by rw [← hab]; ring
    have h2 : u * v = 0 :=
      (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hreg (k + l))).1 h1
    exact (hu.mul hv).ne_zero h2
  exact NoZeroDivisors.to_isDomain A

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

/- English proof (translation)
Use `GlobalTheory.OnePrime.nontrivial_Ow w` as an intermediate fact. Take `⟨P, hP, hpP, hm, hQ⟩` from `GlobalTheory.OnePrime.exists_prime_under p R w`. Establish `: IsLocalRing w.Ow` using `IsLocalRing.of_unique_max_ideal ⟨_, hm, fun N hN => GlobalTheory.OnePrime.maximal_unique w _ N hm hN⟩`. Establish `: IsNoetherianRing w.Ow` using `IsNoetherianRing.of_finite ℤ_[p] w.Ow`. Establish `hM : IsLocalRing.maximalIdeal w.Ow = P.map w.toOw` using `(IsLocalRing.eq_maximalIdeal hm).symm`.

Establish `hp0 : (p : R) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero`. Establish `hP0 : P ≠ ⊥` using `fun h => hp0 (by rwa [h, Ideal.mem_bot] at hpP)`. Establish `hpow : ∀ a : R, a ≠ 0 → ∃ (k : ℕ) (Q : Ideal R), Ideal.span {a} = P ^ k * Q ∧ P ⊔ Q = ⊤ ∧ Ideal.span {w.toOw a} = P.map w.toOw ^ k`. Introduce `a ha`. Establish `ha0 : Ideal.span {a} ≠ ⊥` using `by simpa using ha`.

Take `⟨Q, hPQ, hQe⟩` from `Ideal.eq_prime_pow_mul_coprime ha0 P`. Generalize the expression as in `Multiset.count P _ = e at hQe`. Establish `hQ0 : Q ≠ ⊥` using `by rintro rfl; exact ha0 (by simpa using hQe)`. Use `⟨e, Q, hQe, hPQ, ?_⟩` and prove the remaining obligations. Use `congrArg (Ideal.map w.toOw) hQe` as an intermediate fact.

Rewrite `this` using `[Ideal.map_span, Set.image_singleton, Ideal.map_mul, Ideal.map_pow, GlobalTheory.Proof.different_power_unramified_iff.map_eq_top_of_coprime _ P hP hQ Q hQ0 hPQ, Ideal.mul_top]`. Then use the resulting hypothesis. Take `⟨a, ha1, ha2⟩` from `Ideal.exists_mem_pow_notMem_pow_succ P hP0 hP.ne_top 1`. Establish `ha0 : a ≠ 0` using `by rintro rfl; exact ha2 (zero_mem _)`. Establish `hπ : IsLocalRing.maximalIdeal w.Ow = Ideal.span {w.toOw a}`. Take `⟨k, Q, h1, h2, h3⟩` from `hpow a ha0`.

Rewrite `ha1` using `[pow_one]`. Establish `hk : k ≤ 1`. Assume the negation of the conclusion as `hk`. Apply `ha2` to reduce the goal to its premises. Use `(Ideal.span_singleton_le_iff_mem _).1 ?_` and prove the remaining obligations.

Rewrite using `[h1]`. Conclude with `Ideal.mul_le_left.trans (Ideal.pow_le_pow_right (Nat.succ_le_of_lt (not_le.1 hk)))`. Rewrite using `[hM]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[h3] conv_lhs => rw [← pow_one (P.map w.toOw)]`.

Conclude with `Ideal.pow_le_pow_right hk`. Conclude with `(Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_map_of_mem _ ha1)`. Establish `hpM : (p : w.Ow) ∈ IsLocalRing.maximalIdeal w.Ow`. Rewrite using `[hM, ← map_natCast w.toOw]`. Conclude with `Ideal.mem_map_of_mem _ hpP`.

Establish `hpreg : (p : w.Ow) ∈ nonZeroDivisors w.Ow` using `mem_nonZeroDivisors_iff_left.2 (GlobalTheory.Proof.different_power_unramified_iff.ow_p_torsionFree p R w)`. Establish `hreg : w.toOw a ∈ nonZeroDivisors w.Ow`. Establish `h` using `hpM`. Rewrite `h` using `[hπ, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `h`.

Rewrite `hpreg` using `[hc]`. Conclude with `(mul_mem_nonZeroDivisors.1 hpreg).1`. Establish `hd` using `isDomain_of_span hπ hreg`. Use `⟨hd, ?_⟩` and prove the remaining obligations. Establish `hnf : ¬ IsField w.Ow`.

Rewrite using `[IsLocalRing.isField_iff_maximalIdeal_eq]`. Introduce `h`. Rewrite `hpM` using `[h, Ideal.mem_bot]`. Conclude with `nonZeroDivisors.ne_zero hpreg hpM`. Establish `hpr : (IsLocalRing.maximalIdeal w.Ow).IsPrincipal` using `⟨_, hπ⟩`.

Conclude with `((IsDiscreteValuationRing.TFAE w.Ow hnf).out 0 4).2 hpr`.
-/
private theorem exists_dvr [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R]
    (w : Place p R) : ∃ _ : IsDomain w.Ow, IsDiscreteValuationRing w.Ow := by
  classical
  have := GlobalTheory.OnePrime.nontrivial_Ow w
  obtain ⟨P, hP, hpP, hm, hQ⟩ := GlobalTheory.OnePrime.exists_prime_under p R w
  have : IsLocalRing w.Ow :=
    IsLocalRing.of_unique_max_ideal ⟨_, hm, fun N hN => GlobalTheory.OnePrime.maximal_unique w _ N hm hN⟩
  have : IsNoetherianRing w.Ow := IsNoetherianRing.of_finite ℤ_[p] w.Ow
  have hM : IsLocalRing.maximalIdeal w.Ow = P.map w.toOw := (IsLocalRing.eq_maximalIdeal hm).symm
  have hp0 : (p : R) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hP0 : P ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hpP)
  have hpow : ∀ a : R, a ≠ 0 → ∃ (k : ℕ) (Q : Ideal R), Ideal.span {a} = P ^ k * Q ∧ P ⊔ Q = ⊤ ∧
      Ideal.span {w.toOw a} = P.map w.toOw ^ k := by
    intro a ha
    have ha0 : Ideal.span {a} ≠ ⊥ := by simpa using ha
    obtain ⟨Q, hPQ, hQe⟩ := Ideal.eq_prime_pow_mul_coprime ha0 P
    generalize Multiset.count P _ = e at hQe
    have hQ0 : Q ≠ ⊥ := by rintro rfl; exact ha0 (by simpa using hQe)
    refine ⟨e, Q, hQe, hPQ, ?_⟩
    have := congrArg (Ideal.map w.toOw) hQe
    rwa [Ideal.map_span, Set.image_singleton, Ideal.map_mul, Ideal.map_pow,
      GlobalTheory.Proof.different_power_unramified_iff.map_eq_top_of_coprime _ P hP hQ Q hQ0 hPQ, Ideal.mul_top] at this
  obtain ⟨a, ha1, ha2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P hP0 hP.ne_top 1
  have ha0 : a ≠ 0 := by rintro rfl; exact ha2 (zero_mem _)
  have hπ : IsLocalRing.maximalIdeal w.Ow = Ideal.span {w.toOw a} := by
    obtain ⟨k, Q, h1, h2, h3⟩ := hpow a ha0
    rw [pow_one] at ha1
    have hk : k ≤ 1 := by
      by_contra hk
      apply ha2
      refine (Ideal.span_singleton_le_iff_mem _).1 ?_
      rw [h1]
      exact Ideal.mul_le_left.trans (Ideal.pow_le_pow_right (Nat.succ_le_of_lt (not_le.1 hk)))
    rw [hM]
    apply le_antisymm
    · rw [h3]
      conv_lhs => rw [← pow_one (P.map w.toOw)]
      exact Ideal.pow_le_pow_right hk
    · exact (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_map_of_mem _ ha1)
  have hpM : (p : w.Ow) ∈ IsLocalRing.maximalIdeal w.Ow := by
    rw [hM, ← map_natCast w.toOw]; exact Ideal.mem_map_of_mem _ hpP
  have hpreg : (p : w.Ow) ∈ nonZeroDivisors w.Ow :=
    mem_nonZeroDivisors_iff_left.2 (GlobalTheory.Proof.different_power_unramified_iff.ow_p_torsionFree p R w)
  have hreg : w.toOw a ∈ nonZeroDivisors w.Ow := by
    have h := hpM
    rw [hπ, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    rw [hc] at hpreg
    exact (mul_mem_nonZeroDivisors.1 hpreg).1
  have hd := isDomain_of_span hπ hreg
  refine ⟨hd, ?_⟩
  have hnf : ¬ IsField w.Ow := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    intro h
    rw [h, Ideal.mem_bot] at hpM
    exact nonZeroDivisors.ne_zero hpreg hpM
  have hpr : (IsLocalRing.maximalIdeal w.Ow).IsPrincipal := ⟨_, hπ⟩
  exact ((IsDiscreteValuationRing.TFAE w.Ow hnf).out 0 4).2 hpr

private def cutEquiv (w : Place p R) :
    LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e) ≃ₗ[ℤ_[p]] w.Ow :=
  LinearEquiv.ofBijective
    ((Ideal.Quotient.mkₐ ℤ_[p] (Ideal.span {1 - w.e})).toLinearMap ∘ₗ
      (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)).subtype) (by
      constructor
      · rw [injective_iff_map_eq_zero]
        rintro ⟨_, a, rfl⟩ ha
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 ha)
        have hc' : c * (1 - w.e) = w.e * a := hc
        apply Subtype.ext
        show w.e * a = 0
        linear_combination (-w.e) * hc' - (a + c) * w.idem.eq
      · intro s
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
        refine ⟨⟨w.e * a, a, rfl⟩, Ideal.Quotient.eq.2 ?_⟩
        exact Ideal.mem_span_singleton'.2 ⟨-a, by
          show -a * (1 - w.e) = w.e * a - a
          ring⟩)

/- English proof (translation)
Establish `: (cutEquiv w).symm (Ideal.Quotient.mk _ a) = ⟨w.e * a, a, rfl⟩`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Use `Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨a, ?_⟩)` and prove the remaining obligations. Use `show a * (1 - w.e) = a - w.e * a`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`.
-/
private theorem cutEquiv_symm (w : Place p R) (a : Op p R) :
    ((cutEquiv w).symm (Ideal.Quotient.mk _ a) : Op p R) = w.e * a := by
  have : (cutEquiv w).symm (Ideal.Quotient.mk _ a) = ⟨w.e * a, a, rfl⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨a, ?_⟩)
    show a * (1 - w.e) = a - w.e * a
    ring
  rw [this]

/- English proof (translation)
Take `⟨_, _⟩` from `exists_dvr w`. Establish `: Module.Free ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))` using `inferInstance`. Establish `: Module.Free ℤ_[p] w.Ow` using `Module.Free.of_equiv (cutEquiv w)`. Establish `: IsLocalHom (algebraMap ℤ_[p] w.Ow)` using `Algebra.IsIntegral.isLocalHom _ _`. Establish `: Finite (IsLocalRing.ResidueField ℤ_[p])` using `Finite.of_equiv _ (PadicInt.residueField (p := p)).toEquiv.symm`.

Take `⟨θ, hθ⟩ : ∃ θ : w.Ow, Algebra.adjoin ℤ_[p] {θ} = ⊤` from `Formalism.L2.Pj.AvAlg.exists_adjoin_eq_top (FaithfulSMul.algebraMap_injective _ _)`. Take `⟨α, rfl⟩` from `Ideal.Quotient.mk_surjective θ`. Set `pb` to `PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral _) hθ`. Establish `hg : pb.gen = Ideal.Quotient.mk _ α` using `by simp [pb]`. Establish `hn : pb.dim = Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))`.

Rewrite using `[(cutEquiv w).finrank_eq, pb.finrank]`. Use `⟨α, (pb.basis.map (cutEquiv w).symm).reindex (finCongr hn), fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.reindex_apply, Module.Basis.map_apply, pb.basis_eq_pow, hg, ← map_pow, cutEquiv_symm]`. Both sides reduce to the same expression.
-/
private theorem exists_basis [IsDedekindDomain R] [CharZero R] [Module.Free ℤ R]
    [Module.Finite ℤ R] (w : Place p R) :
    ∃ (α : Op p R) (b : Module.Basis
      (Fin (Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)))) ℤ_[p]
      (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))), ∀ k, (b k : Op p R) = w.e * α ^ (k : ℕ) := by
  obtain ⟨_, _⟩ := exists_dvr w
  have : Module.Free ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) := inferInstance
  have : Module.Free ℤ_[p] w.Ow := Module.Free.of_equiv (cutEquiv w)
  have : IsLocalHom (algebraMap ℤ_[p] w.Ow) := Algebra.IsIntegral.isLocalHom _ _
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := p)).toEquiv.symm
  obtain ⟨θ, hθ⟩ : ∃ θ : w.Ow, Algebra.adjoin ℤ_[p] {θ} = ⊤ :=
    Formalism.L2.Pj.AvAlg.exists_adjoin_eq_top (FaithfulSMul.algebraMap_injective _ _)
  obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective θ
  let pb := PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral _) hθ
  have hg : pb.gen = Ideal.Quotient.mk _ α := by simp [pb]
  have hn : pb.dim = Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) := by
    rw [(cutEquiv w).finrank_eq, pb.finrank]
  refine ⟨α, (pb.basis.map (cutEquiv w).symm).reindex (finCongr hn), fun k => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply, pb.basis_eq_pow, hg, ← map_pow,
    cutEquiv_symm]
  rfl

end SlopeTestRemainingChoices

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

/- English proof (translation)
Introduce `p _ OE _ _ _ _ _ w`. Set `w' : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p OE` to `⟨w.e, w.idem, w.ne_zero, w.prim⟩`. Take `⟨h1, h2⟩` from `exists_dvr w'`. Conclude with `⟨h1, h2.toIsPrincipalIdealRing, exists_basis w'⟩`.
-/
theorem place_monogenic : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE), IsDomain ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ IsPrincipalIdealRing ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ ∃ (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))), ∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ) := by
  intro p _ OE _ _ _ _ _ w
  let w' : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p OE := ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  obtain ⟨h1, h2⟩ := exists_dvr w'
  exact ⟨h1, h2.toIsPrincipalIdealRing, exists_basis w'⟩

end GlobalTheory.PlaceMono

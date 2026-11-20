import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonicDvdXPowCardSubOneExistsRootStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionResiduePowAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIntegersUnramifiedInvolutionExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinPrimitiveRootEqIntegersUnramifiedQuadraticStatement

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial IsLocalRing

/- English proof (translation)
Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hn`. Establish `key : (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) * (y₁ - y₂) = 0`. Rewrite using `[Commute.geom_sum₂_mul (Commute.all _ _), h₁, h₂, sub_self]`.

Establish `hr : residue S (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) = (n : ResidueField S) * residue S y₂ ^ (n - 1)`. Rewrite using `[map_sum]`. Simplify using `only [map_mul, map_pow, h]`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => residue S y₂ ^ (n - 1)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Introduce `i hi`.

Rewrite using `[← pow_add]`. Use `congr 1`. Use `Finset.mem_range.1 hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hu : IsUnit (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i))`.

Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, hr]`. Use `mul_ne_zero ?_ (pow_ne_zero _ ?_)` and prove the remaining obligations. Simplify using `using (hn.map (residue S)).ne_zero`. Introduce `h0`. Use `congrArg (residue S) h₂` as an intermediate fact.

Rewrite `this` using `[map_pow, h0, zero_pow hn0, map_one]`. Conclude with `zero_ne_one this`. Use `(hu.mul_right_eq_zero).1 key` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
theorem pow_eq_one_eq_of_residue {S : Type*} [CommRing S] [IsLocalRing S] {n : ℕ} (hn : IsUnit (n : S))
    {y₁ y₂ : S} (h₁ : y₁ ^ n = 1) (h₂ : y₂ ^ n = 1) (h : residue S y₁ = residue S y₂) : y₁ = y₂ := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have key : (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) * (y₁ - y₂) = 0 := by
    rw [Commute.geom_sum₂_mul (Commute.all _ _), h₁, h₂, sub_self]
  have hr : residue S (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) =
      (n : ResidueField S) * residue S y₂ ^ (n - 1) := by
    rw [map_sum]
    simp only [map_mul, map_pow, h]
    rw [Finset.sum_congr rfl (g := fun _ => residue S y₂ ^ (n - 1)), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    intro i hi
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.1 hi
    omega
  have hu : IsUnit (∑ i ∈ Finset.range n, y₁ ^ i * y₂ ^ (n - 1 - i)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hr]
    refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
    · simpa using (hn.map (residue S)).ne_zero
    · intro h0
      have := congrArg (residue S) h₂
      rw [map_pow, h0, zero_pow hn0, map_one] at this
      exact zero_ne_one this
  have := (hu.mul_right_eq_zero).1 key
  exact sub_eq_zero.1 this

/- English proof (translation)
Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_sub Nat.card_pos, Nat.cast_one]`. Use `haveI := Fintype.ofFinite (ResidueField S)`. Rewrite using `[Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]`. Simplify using the standard rewrite rules.
-/
theorem card_sub_one_isUnit (S : Type*) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] :
    IsUnit ((Nat.card (ResidueField S) - 1 : ℕ) : S) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_sub Nat.card_pos, Nat.cast_one]
  haveI := Fintype.ofFinite (ResidueField S)
  rw [Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
  simp

/- English proof (translation)
Introduce `K _ B hu _ hi hl d hcard K' φ hU hz`. Take `⟨z, hzp, hzadj⟩` from `hz`. Use `set R := Algebra.adjoin K.O ({B.g} : Set B.A) with hR`. Establish `hq0 : K.q ≠ 0`. Introduce `h0`.

Establish `: 0 < Nat.card (ResidueField K.O)` using `Nat.card_pos`. Rewrite `this` using `[K.card_res, h0]`. Simplify using `at this`. Establish `hq' : K'.q = K.q ^ d` using `hU.1`. Use `set N := K'.q ^ 2 - 1 with hNdef`.

Establish `hcardR : Nat.card (ResidueField R) = K'.q ^ 2` using `by rw [hcard, hq', ← pow_mul, mul_comm]`. Establish `hd : d ≠ 0`. Introduce and unpack `rfl`. Rewrite `hq'` using `[pow_zero]`. Rewrite `hcardR` using `[hq', one_pow]`.

Establish `: Subsingleton (ResidueField R)` using `(Nat.card_eq_one_iff_unique.1 hcardR).1`. Conclude with `not_subsingleton (ResidueField R) this`. Use `haveI : Finite (ResidueField R) := Nat.finite_of_card_ne_zero (by rw [hcardR, hq']; exact pow_ne_zero _ (pow_ne_zero _ hq0))`. Use `haveI : Module.Finite K.O R := Algebra.finite_adjoin_simple_of_isIntegral hi`. Use `haveI : HenselianLocalRing K.O := GlobalTheory.henselianLocalRing_of_henselianRing K.O`.

Use `haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_finite K.O R`. Establish `h1q : 1 < K'.q ^ 2` using `by rw [← K'.card_res]; exact Finite.one_lt_card`. Establish `hN : N ≠ 0` using `by omega`. Establish `hNR : IsUnit (N : R)`. Use `card_sub_one_isUnit R` as an intermediate fact.

Rewrite `this` using `[hcardR]`. Then use the resulting hypothesis. Use `letI : Algebra K.E K'.E := φ.toAlgebra`. Use `letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra`. Use `haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : FaithfulSMul K.O K'.E := (faithfulSMul_iff_algebraMap_injective _ _).2 (φ.injective.comp (IsFractionRing.injective K.O K.E))`.

Establish `hzN : z ^ N = 1` using `hzp.pow_eq_one`. Establish `hzint : IsIntegral K.O z` using `⟨_, monic_X_pow_sub_C (1 : K.O) hN, by rw [← aeval_def]; simp [hzN]⟩`. Establish `hmdvd : minpoly K.O z ∣ X ^ N - C 1` using `minpoly.isIntegrallyClosed_dvd hzint (by simp [hzN])`. Take `⟨yR, hyR⟩` from `GlobalTheory.T.exists_root_of_monic_dvd_X_pow_card_sub_one R ((minpoly K.O z).map (algebraMap K.O R)) ((minpoly.monic hzint).map _) (by rw [(minpoly.monic hzint).natDegree_map]; exact (minpoly.natDegree_pos hzint).ne') (by`. Rewrite using `[hcardR]`.

Use `Polynomial.map_dvd (algebraMap K.O R) hmdvd` as an intermediate fact. Simplify using `using this)`. Establish `hyN : yR ^ N = 1`. Take `⟨h, hh⟩` from `hmdvd`. Use `congrArg (fun p => (p.map (algebraMap K.O R)).eval yR) hh` as an intermediate fact.

Simplify using `only [Polynomial.map_mul, eval_mul, hyR, zero_mul] at this`. Simplify `this` using `[sub_eq_zero]`. Establish `hzE : IsIntegral K.E z` using `hzint.tower_top`. Set `pb` to `PowerBasis.ofAdjoinEqTop hzE hzadj`. Establish `hgen : pb.gen = z` using `rfl`.

Establish `hy : aeval (yR : B.A) (minpoly K.E pb.gen) = 0`. Rewrite using `[hgen, minpoly.isIntegrallyClosed_eq_field_fractions' K.E hzint, aeval_map_algebraMap, ← Polynomial.aeval_subalgebra_coe, aeval_def, ← eval_map, hyR]`. Both sides reduce to the same expression. Set `ψ : K'.E →+* B.A` to `(pb.lift (yR : B.A) hy).toRingHom`. Establish `hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e` using `fun e => (pb.lift (yR : B.A) hy).commutes e`.

Establish `hψz : ψ z = yR` using `pb.lift_gen _ hy`. Use `haveI : Nontrivial B.A := nontrivial_of_ne (0 : B.A) 1 fun h => zero_ne_one (Subtype.ext h : (0 : R) = 1)`. Establish `hψi : Function.Injective ψ` using `ψ.injective`. Set `τR : R →+* R` to `(B.σ : B.A →+* B.A).restrict R R fun x hx => Orbit.adjoin_stable B hu hi hx`. Establish `hτR : ∀ x : R, (τR x : B.A) = B.σ x` using `fun x => rfl`.

Establish `hτ2 : ∀ x, τR (τR x) = x` using `fun x => Subtype.ext (B.σ_σ x)`. Take `⟨a, b, hab, hres⟩` from `K.c_res`. Establish `hτa : τR (algebraMap K.O R a) = algebraMap K.O R b`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hτR]`.

Express the relevant statement in the definitionally equal form `B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A b`. Rewrite using `[IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hab, ← IsScalarTower.algebraMap_apply]`. Establish `hne : residue R (τR (algebraMap K.O R a)) ≠ residue R (algebraMap K.O R a)`. Rewrite using `[hτa]`. Introduce `h`.

Establish `h2 : residue R (algebraMap K.O R (a - b)) = 0` using `by rw [map_sub, map_sub, h, sub_self]`. Rewrite `h2` using `[IsLocalRing.residue_eq_zero_iff]`. Establish `hu' : IsUnit (a - b)`. Assume the negation of the conclusion as `hc`. Conclude with `hres ((IsLocalRing.mem_maximalIdeal _).2 hc)`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h2 (hu'.map _)`. Take `⟨hfr1, hfr2⟩` from `GlobalTheory.T.involution_residue_pow_and_roots_of_unity R K'.q hcardR τR hτ2 ⟨_, hne⟩`. Use `choose τ' hτ' using K'.c_int`. Establish `hinj' : Function.Injective (algebraMap K'.O K'.E)` using `IsFractionRing.injective _ _`. Set `cO : K'.O →+* K'.O` to `{ toFun := τ' map_one' := hinj' (by rw [← hτ']; simp) map_mul' := fun a b => hinj' (by simp [← hτ']) map_zero' := hinj' (by rw [← hτ']; simp) map_add' := fun a b => hinj' (by simp [← hτ']) }`.

Establish `hcO : ∀ x, algebraMap K'.O K'.E (cO x) = K'.c (algebraMap K'.O K'.E x)` using `fun x => (hτ' x).symm`. Establish `hc2 : ∀ x, cO (cO x) = x` using `fun x => hinj' (by rw [hcO, hcO, K'.c_c])`. Take `⟨a', b', hab', hres'⟩` from `K'.c_res`. Establish `hne' : residue K'.O (cO a') ≠ residue K'.O a'`. Establish `: cO a' = b'` using `hinj' (by rw [hcO, hab'])`.

Rewrite using `[this]`. Introduce `h`. Apply `hres'` to reduce the goal to its premises. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]`. Take `⟨-, hfc⟩` from `GlobalTheory.T.involution_residue_pow_and_roots_of_unity K'.O K'.q K'.card_res cO hc2 ⟨_, hne'⟩`.

Take `⟨zO, hzO⟩ : ∃ zO : K'.O, algebraMap K'.O K'.E zO = z` from `IsIntegrallyClosed.isIntegral_iff.1 ⟨_, monic_X_pow_sub_C (1 : K'.O) hN, by rw [← aeval_def]; simp [hzN]⟩`. Establish `hzON : zO ^ N = 1` using `hinj' (by rw [map_pow, hzO, hzN, map_one])`. Establish `hcz : K'.c z = z ^ K'.q`. Rewrite using `[← hzO, ← hcO, hfc zO hzON, map_pow]`. Establish `hσz : B.σ (ψ z) = ψ (K'.c z)`.

Rewrite using `[hψz, ← hτR, hfr2 yR hyN, hcz, map_pow, hψz]`. Both sides reduce to the same expression. Establish `hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)`. Introduce `e`. Establish `he : e ∈ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z}` using `hzadj ▸ Algebra.mem_top`.

Proceed by induction on `he using Algebra.adjoin_induction with`. Consider the case `mem x hx => rw [Set.mem_singleton_iff.1 hx]`. Conclude with `hσz`. Consider the case `algebraMap e`. Express the relevant statement in the definitionally equal form `B.σ (ψ (φ e)) = ψ (K'.c (φ e))`.

Rewrite using `[← hU.2.1, hψ, hψ, B.σ_alg]`. Consider the case `add x y _ _ hx hy => simp only [map_add, hx, hy]`. Consider the case `mul x y _ _ hx hy => simp only [map_mul, hx, hy]`. Establish `hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ R`. Introduce `y`.

Establish `hadj` using `GlobalTheory.T.adjoin_primitiveRoot_eq_integers_unramifiedQuadratic K K' d φ hU hd z hzp hzadj _ (GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt K K' d φ hU hd y)`. Generalize the expression as in `algebraMap K'.O K'.E y = x at hadj ⊢`. Proceed by induction on `hadj using Algebra.adjoin_induction with`. Consider the case `mem x hx => rw [Set.mem_singleton_iff.1 hx, hψz]`. Conclude with `yR.2`.

Consider the case `algebraMap a`. Express the relevant statement in the definitionally equal form `ψ (φ (algebraMap K.O K.E a)) ∈ R`. Rewrite using `[hψ, ← IsScalarTower.algebraMap_apply]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`. Use `⟨ψ, hψ, hσ, hO, ?_⟩` and prove the remaining obligations. Use `haveI : NeZero N := ⟨hN⟩`.

Establish `hcoe : ∀ n : ℕ, ((yR ^ n : R) : B.A) = ψ (z ^ n)` using `fun n => by rw [map_pow, hψz]; rfl`. Establish `hwp : IsPrimitiveRoot (residue R yR) N`. Use `⟨by rw [← map_pow, hyN, map_one], fun l hl => hzp.dvd_of_pow_eq_one l ?_⟩` and prove the remaining obligations. Establish `h1 : yR ^ l = 1` using `pow_eq_one_eq_of_residue hNR (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [map_pow, hl, map_one])`. Apply `hψi` to reduce the goal to its premises.

Rewrite using `[← hcoe, h1, map_one]`. Both sides reduce to the same expression. Use `set gR : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ with hgR`. Establish `hgu : gR * τR gR = 1` using `Subtype.ext hu`. Establish `hg0 : residue R gR ≠ 0` using `(IsUnit.map (residue R) (⟨⟨gR, τR gR, hgu, by rw [mul_comm]; exact hgu⟩, rfl⟩ : IsUnit gR)).ne_zero`.

Establish `hgN : residue R gR ^ N = 1` using `by haveI := Fintype.ofFinite (ResidueField R)`. Use `FiniteField.pow_card_sub_one_eq_one _ hg0` as an intermediate fact. Rewrite `this` using `[← Nat.card_eq_fintype_card, hcardR]`. Then use the resulting hypothesis. Take `⟨j, -, hj⟩` from `hwp.eq_pow_of_pow_eq_one hgN`. Set `zOu : K'.Oˣ` to `Units.ofPowEqOne zO N hzON hN`.

Establish `hs : algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O) = z ^ j`. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, Units.val_ofPowEqOne, hzO]`. Use `⟨zOu ^ j, ?_, ?_⟩` and prove the remaining obligations. Use `set e := j + j * K'.q with he`. Establish `hres : residue R (yR ^ e) = 1`.

Rewrite using `[map_pow, he, pow_add, pow_mul, hj, ← hfr1 gR, ← map_mul, hgu, map_one]`. Establish `hye : yR ^ e = 1` using `pow_eq_one_eq_of_residue hNR (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [hres, map_one])`. Rewrite using `[hs, map_pow, hcz, ← pow_mul, ← pow_add, mul_comm K'.q j, ← he]`. Apply `hψi` to reduce the goal to its premises. Rewrite using `[← hcoe, hye, map_one]`.

Both sides reduce to the same expression. Establish `: (⟨ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)), hO _⟩ : R) = yR ^ j` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)) = ((yR ^ j : R) : B.A)`. Rewrite using `[hs, hcoe])`. Rewrite using `[this, map_pow, hj]`.
-/
theorem exists_unr_embedding : ∀ (K : UQ), K.Odd → ∀ B : InvAlg K, B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) (d : ℕ), Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) → ∀ (K' : UQ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → (∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤) → ∃ (ψ : K'.E →+* B.A) (_ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (_ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)), ∃ s : K'.Oˣ, algebraMap K'.O K'.E s * K'.c (algebraMap K'.O K'.E s) = 1 ∧ @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ := by
  intro K _ B hu _ hi hl d hcard K' φ hU hz
  obtain ⟨z, hzp, hzadj⟩ := hz
  set R := Algebra.adjoin K.O ({B.g} : Set B.A) with hR
  have hq0 : K.q ≠ 0 := by
    intro h0
    have : 0 < Nat.card (ResidueField K.O) := Nat.card_pos
    rw [K.card_res, h0] at this
    simp at this
  have hq' : K'.q = K.q ^ d := hU.1
  set N := K'.q ^ 2 - 1 with hNdef
  have hcardR : Nat.card (ResidueField R) = K'.q ^ 2 := by rw [hcard, hq', ← pow_mul, mul_comm]
  have hd : d ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq'
    rw [hq', one_pow] at hcardR
    have : Subsingleton (ResidueField R) := (Nat.card_eq_one_iff_unique.1 hcardR).1
    exact not_subsingleton (ResidueField R) this
  haveI : Finite (ResidueField R) := Nat.finite_of_card_ne_zero (by rw [hcardR, hq']; exact pow_ne_zero _ (pow_ne_zero _ hq0))

  haveI : Module.Finite K.O R := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : HenselianLocalRing K.O := GlobalTheory.henselianLocalRing_of_henselianRing K.O
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_finite K.O R
  have h1q : 1 < K'.q ^ 2 := by rw [← K'.card_res]; exact Finite.one_lt_card
  have hN : N ≠ 0 := by omega
  have hNR : IsUnit (N : R) := by
    have := card_sub_one_isUnit R
    rwa [hcardR] at this
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul K.O K'.E := (faithfulSMul_iff_algebraMap_injective _ _).2
    (φ.injective.comp (IsFractionRing.injective K.O K.E))
  have hzN : z ^ N = 1 := hzp.pow_eq_one
  have hzint : IsIntegral K.O z :=
    ⟨_, monic_X_pow_sub_C (1 : K.O) hN, by rw [← aeval_def]; simp [hzN]⟩
  have hmdvd : minpoly K.O z ∣ X ^ N - C 1 := minpoly.isIntegrallyClosed_dvd hzint (by simp [hzN])
  obtain ⟨yR, hyR⟩ := GlobalTheory.T.exists_root_of_monic_dvd_X_pow_card_sub_one R ((minpoly K.O z).map (algebraMap K.O R))
    ((minpoly.monic hzint).map _)
    (by rw [(minpoly.monic hzint).natDegree_map]; exact (minpoly.natDegree_pos hzint).ne')
    (by
      rw [hcardR]
      have := Polynomial.map_dvd (algebraMap K.O R) hmdvd
      simpa using this)
  have hyN : yR ^ N = 1 := by
    obtain ⟨h, hh⟩ := hmdvd
    have := congrArg (fun p => (p.map (algebraMap K.O R)).eval yR) hh
    simp only [Polynomial.map_mul, eval_mul, hyR, zero_mul] at this
    simpa [sub_eq_zero] using this

  have hzE : IsIntegral K.E z := hzint.tower_top
  let pb := PowerBasis.ofAdjoinEqTop hzE hzadj
  have hgen : pb.gen = z := rfl
  have hy : aeval (yR : B.A) (minpoly K.E pb.gen) = 0 := by
    rw [hgen, minpoly.isIntegrallyClosed_eq_field_fractions' K.E hzint, aeval_map_algebraMap,
      ← Polynomial.aeval_subalgebra_coe, aeval_def, ← eval_map, hyR]
    rfl
  let ψ : K'.E →+* B.A := (pb.lift (yR : B.A) hy).toRingHom
  have hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e := fun e => (pb.lift (yR : B.A) hy).commutes e
  have hψz : ψ z = yR := pb.lift_gen _ hy
  haveI : Nontrivial B.A := nontrivial_of_ne (0 : B.A) 1 fun h => zero_ne_one (Subtype.ext h : (0 : R) = 1)
  have hψi : Function.Injective ψ := ψ.injective

  let τR : R →+* R := (B.σ : B.A →+* B.A).restrict R R fun x hx => Orbit.adjoin_stable B hu hi hx
  have hτR : ∀ x : R, (τR x : B.A) = B.σ x := fun x => rfl
  have hτ2 : ∀ x, τR (τR x) = x := fun x => Subtype.ext (B.σ_σ x)
  obtain ⟨a, b, hab, hres⟩ := K.c_res
  have hτa : τR (algebraMap K.O R a) = algebraMap K.O R b := by
    apply Subtype.ext
    rw [hτR]
    change B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A b
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hab, ← IsScalarTower.algebraMap_apply]
  have hne : residue R (τR (algebraMap K.O R a)) ≠ residue R (algebraMap K.O R a) := by
    rw [hτa]
    intro h
    have h2 : residue R (algebraMap K.O R (a - b)) = 0 := by rw [map_sub, map_sub, h, sub_self]
    rw [IsLocalRing.residue_eq_zero_iff] at h2
    have hu' : IsUnit (a - b) := by
      by_contra hc
      exact hres ((IsLocalRing.mem_maximalIdeal _).2 hc)
    exact (IsLocalRing.mem_maximalIdeal _).1 h2 (hu'.map _)
  obtain ⟨hfr1, hfr2⟩ := GlobalTheory.T.involution_residue_pow_and_roots_of_unity R K'.q hcardR τR hτ2 ⟨_, hne⟩
  choose τ' hτ' using K'.c_int
  have hinj' : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective _ _
  let cO : K'.O →+* K'.O :=
    { toFun := τ'
      map_one' := hinj' (by rw [← hτ']; simp)
      map_mul' := fun a b => hinj' (by simp [← hτ'])
      map_zero' := hinj' (by rw [← hτ']; simp)
      map_add' := fun a b => hinj' (by simp [← hτ']) }
  have hcO : ∀ x, algebraMap K'.O K'.E (cO x) = K'.c (algebraMap K'.O K'.E x) := fun x => (hτ' x).symm
  have hc2 : ∀ x, cO (cO x) = x := fun x => hinj' (by rw [hcO, hcO, K'.c_c])
  obtain ⟨a', b', hab', hres'⟩ := K'.c_res
  have hne' : residue K'.O (cO a') ≠ residue K'.O a' := by
    have : cO a' = b' := hinj' (by rw [hcO, hab'])
    rw [this]
    intro h
    apply hres'
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  obtain ⟨-, hfc⟩ := GlobalTheory.T.involution_residue_pow_and_roots_of_unity K'.O K'.q K'.card_res cO hc2 ⟨_, hne'⟩
  obtain ⟨zO, hzO⟩ : ∃ zO : K'.O, algebraMap K'.O K'.E zO = z :=
    IsIntegrallyClosed.isIntegral_iff.1
      ⟨_, monic_X_pow_sub_C (1 : K'.O) hN, by rw [← aeval_def]; simp [hzN]⟩
  have hzON : zO ^ N = 1 := hinj' (by rw [map_pow, hzO, hzN, map_one])
  have hcz : K'.c z = z ^ K'.q := by
    rw [← hzO, ← hcO, hfc zO hzON, map_pow]
  have hσz : B.σ (ψ z) = ψ (K'.c z) := by
    rw [hψz, ← hτR, hfr2 yR hyN, hcz, map_pow, hψz]
    rfl
  have hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e) := by
    intro e
    have he : e ∈ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} := hzadj ▸ Algebra.mem_top
    induction he using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hσz
    | algebraMap e =>
      change B.σ (ψ (φ e)) = ψ (K'.c (φ e))
      rw [← hU.2.1, hψ, hψ, B.σ_alg]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | mul x y _ _ hx hy => simp only [map_mul, hx, hy]

  have hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ R := by
    intro y
    have hadj := GlobalTheory.T.adjoin_primitiveRoot_eq_integers_unramifiedQuadratic K K' d φ hU hd z hzp hzadj _ (GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt K K' d φ hU hd y)
    generalize algebraMap K'.O K'.E y = x at hadj ⊢
    induction hadj using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx, hψz]; exact yR.2
    | algebraMap a =>
      change ψ (φ (algebraMap K.O K.E a)) ∈ R
      rw [hψ, ← IsScalarTower.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨ψ, hψ, hσ, hO, ?_⟩
  haveI : NeZero N := ⟨hN⟩
  have hcoe : ∀ n : ℕ, ((yR ^ n : R) : B.A) = ψ (z ^ n) := fun n => by rw [map_pow, hψz]; rfl
  have hwp : IsPrimitiveRoot (residue R yR) N := by
    refine ⟨by rw [← map_pow, hyN, map_one], fun l hl => hzp.dvd_of_pow_eq_one l ?_⟩
    have h1 : yR ^ l = 1 := pow_eq_one_eq_of_residue hNR
      (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [map_pow, hl, map_one])
    apply hψi
    rw [← hcoe, h1, map_one]
    rfl
  set gR : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ with hgR
  have hgu : gR * τR gR = 1 := Subtype.ext hu
  have hg0 : residue R gR ≠ 0 := (IsUnit.map (residue R) (⟨⟨gR, τR gR, hgu, by rw [mul_comm]; exact hgu⟩, rfl⟩ : IsUnit gR)).ne_zero
  have hgN : residue R gR ^ N = 1 := by
    haveI := Fintype.ofFinite (ResidueField R)
    have := FiniteField.pow_card_sub_one_eq_one _ hg0
    rwa [← Nat.card_eq_fintype_card, hcardR] at this
  obtain ⟨j, -, hj⟩ := hwp.eq_pow_of_pow_eq_one hgN
  let zOu : K'.Oˣ := Units.ofPowEqOne zO N hzON hN
  have hs : algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O) = z ^ j := by
    rw [Units.val_pow_eq_pow_val, map_pow, Units.val_ofPowEqOne, hzO]
  refine ⟨zOu ^ j, ?_, ?_⟩
  · set e := j + j * K'.q with he
    have hres : residue R (yR ^ e) = 1 := by
      rw [map_pow, he, pow_add, pow_mul, hj, ← hfr1 gR, ← map_mul, hgu, map_one]
    have hye : yR ^ e = 1 := pow_eq_one_eq_of_residue hNR
      (by rw [← pow_mul, mul_comm, pow_mul, hyN, one_pow]) (one_pow N) (by rw [hres, map_one])
    rw [hs, map_pow, hcz, ← pow_mul, ← pow_add, mul_comm K'.q j, ← he]
    apply hψi
    rw [← hcoe, hye, map_one]
    rfl
  · have : (⟨ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)), hO _⟩ : R) = yR ^ j :=
      Subtype.ext (by
        change ψ (algebraMap K'.O K'.E ((zOu ^ j : K'.Oˣ) : K'.O)) = ((yR ^ j : R) : B.A)
        rw [hs, hcoe])
    rw [this, map_pow, hj]

end GlobalTheory.UnitLemma.Unr

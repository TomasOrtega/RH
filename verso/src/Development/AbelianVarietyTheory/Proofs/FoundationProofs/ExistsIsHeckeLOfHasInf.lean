import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlacesBelowSplitCoprimeConductorOfAdmissible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedEqOneOfLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom

namespace GlobalTheory.ToricDistribution

open Classical in

def ToricSumFormula : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E)
      (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (Λ : ℂ → ℂ), UnramFin E → 1 ≤ s → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q →
      IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → IsHeckeL χ Λ →
      IsToricSum φ s κ (condQ 𝔣 Q) χ
        (Λ s * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), Formalism.PairingDivisionLocalBalance.eq (Ideal.absNorm q.asIdeal) s (val χ (Pq q) : ℂ))

section Pic

open GlobalTheory.Mem.TupHecke

variable {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {n : ℕ}

/- English proof (translation)
Establish `hn0 : (n : E) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Establish `key` using `GlobalTheory.IntDense.mem_of_isClosed E (C := {α | algebraMap E (Af E) n * α ∈ hatO c}) ((Subring.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)) (fun a => by show _ ∈ hatO c`. Rewrite using `[← map_mul]`. Use `algebraMap_mem_hatO (mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) n * a, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc), ?_⟩)` and prove the remaining obligations. Use the proof step `simp) (algebraMap E (Af E) (n : E)⁻¹ * (z - 1)) fun P => by`.

Establish `h0` using `GlobalTheory.AdLat.valued_natCast_ne_zero P hn`. Use `show Valued.v (algebraMap E (P.adicCompletion E) (n : E)⁻¹ * (z P - 1)) ≤ 1`. Rewrite using `[map_mul, map_inv₀, map_inv₀, map_natCast, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]`. Conclude with `hz P`. Establish `e : z = algebraMap E (Af E) n * (algebraMap E (Af E) (n : E)⁻¹ * (z - 1)) + 1`.

Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul, sub_add_cancel]`. Rewrite using `[e]`. Conclude with `add_mem key (one_mem _)`.
-/
theorem mem_hatO_of_cong (hn : 0 < n) (hc : (n : OF E) ∈ c) {z : Af E}
    (hz : ∀ P, Valued.v (z P - 1) ≤ Valued.v (n : P.adicCompletion E)) : z ∈ hatO c := by
  have hn0 : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have key := GlobalTheory.IntDense.mem_of_isClosed E (C := {α | algebraMap E (Af E) n * α ∈ hatO c})
    ((Subring.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)) (fun a => by
      show _ ∈ hatO c
      rw [← map_mul]
      refine algebraMap_mem_hatO (mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) n * a,
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc), ?_⟩)
      simp) (algebraMap E (Af E) (n : E)⁻¹ * (z - 1)) fun P => by
      have h0 := GlobalTheory.AdLat.valued_natCast_ne_zero P hn
      show Valued.v (algebraMap E (P.adicCompletion E) (n : E)⁻¹ * (z P - 1)) ≤ 1
      rw [map_mul, map_inv₀, map_inv₀, map_natCast, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]
      exact hz P
  have e : z = algebraMap E (Af E) n * (algebraMap E (Af E) (n : E)⁻¹ * (z - 1)) + 1 := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul, sub_add_cancel]
  rw [e]
  exact add_mem key (one_mem _)

/- English proof (translation)
Use `mem_hatOUnits.2 ⟨mem_hatO_of_cong hn hc fun P => (hu P).2, mem_hatO_of_cong hn hc fun P => ?_⟩` and prove the remaining obligations. Establish `h1 : Valued.v (cmp P u : P.adicCompletion E) = 1` using `(hu P).1`. Establish `e : (↑u⁻¹ : Af E) P - 1 = -((cmp P u : P.adicCompletion E)⁻¹ * (cmp P u - 1))`. Rewrite using `[← cmp_val, map_inv, Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ (cmp P u).ne_zero]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, Valuation.map_neg, map_mul, map_inv₀, h1, inv_one, one_mul]`. Conclude with `(hu P).2`.
-/
theorem mem_hatOUnits_of_cong (hn : 0 < n) (hc : (n : OF E) ∈ c) {u : (Af E)ˣ} (hu : Cong n u) : u ∈ hatOUnits c := by
  refine mem_hatOUnits.2 ⟨mem_hatO_of_cong hn hc fun P => (hu P).2, mem_hatO_of_cong hn hc fun P => ?_⟩
  have h1 : Valued.v (cmp P u : P.adicCompletion E) = 1 := (hu P).1
  have e : (↑u⁻¹ : Af E) P - 1 = -((cmp P u : P.adicCompletion E)⁻¹ * (cmp P u - 1)) := by
    rw [← cmp_val, map_inv, Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ (cmp P u).ne_zero]
    ring
  rw [e, Valuation.map_neg, map_mul, map_inv₀, h1, inv_one, one_mul]
  exact (hu P).2

/- English proof (translation)
Establish `hn : 0 < Ideal.absNorm c` using `Nat.pos_of_ne_zero fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `hk : ∀ u, Cong (Ideal.absNorm c) u → θ.comp (QuotientGroup.mk' _) u = 1` using `fun u hu => by show θ (QuotientGroup.mk u) = 1`. Rewrite using `[(QuotientGroup.eq_one_iff u).2 (Subgroup.mem_sup_right (mem_hatOUnits_of_cong hn (Ideal.absNorm_mem c) hu)), map_one]`. Set `η : HChar E` to `⟨(θ.comp (QuotientGroup.mk' _)).comp (finP E), continuous_finP hn _ hk, fun k => by show θ (QuotientGroup.mk (Units.map (algebraMap E (Af E)).toMonoidHom k)) = 1`. Rewrite using `[(QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_left (show _ ∈ princ from ⟨k, rfl⟩)), map_one]⟩`.

Establish `key` using `GlobalTheory.FrobDense.eq_one_of_away (η * ξ⁻¹).1 (η * ξ⁻¹).2.1 (η * ξ⁻¹).2.2 (S ∪ (finite_nat (L := E) hn).toFinset) fun P hP => by`. Rewrite `hP` using `[Finset.mem_union, not_or]`. Establish `hP2 : Valued.v ((Ideal.absNorm c : ℕ) : P.adicCompletion E) = 1` using `by simpa using hP.2`. Establish `hη : η.UnrAt P` using `fun x hx => hk _ (cong_sing hx (by`. Rewrite using `[hP2]`.

Conclude with `Valuation.map_sub_le _ (le_of_eq hx) (by simp)))`. Use `GlobalTheory.FrobDense.eq_one_of_unif ((η * ξ⁻¹).loc P) fun x hx => ?_` and prove the remaining obligations. Rewrite using `[Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, η.val_eq hη x hx, ξ.val_eq (h P hP.1).1 x hx, ← (h P hP.1).2]`. Conclude with `mul_inv_cancel _`. Conclude with `mul_inv_eq_one.1 (DFunLike.congr_fun key (finIdele E y))`.
-/
theorem pic_char_eq_finPart (hc : c ≠ ⊥) (θ : PicO c →* ℂˣ) (ξ : HChar E) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ P ∉ S, ξ.UnrAt P ∧ θ (QuotientGroup.mk (unifAt P)) = ξ.val P) (y : (Af E)ˣ) :
    θ (QuotientGroup.mk y) = finPart ξ y := by
  classical
  have hn : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  have hk : ∀ u, Cong (Ideal.absNorm c) u → θ.comp (QuotientGroup.mk' _) u = 1 := fun u hu => by
    show θ (QuotientGroup.mk u) = 1
    rw [(QuotientGroup.eq_one_iff u).2 (Subgroup.mem_sup_right (mem_hatOUnits_of_cong hn (Ideal.absNorm_mem c) hu)),
      map_one]
  let η : HChar E := ⟨(θ.comp (QuotientGroup.mk' _)).comp (finP E), continuous_finP hn _ hk, fun k => by
    show θ (QuotientGroup.mk (Units.map (algebraMap E (Af E)).toMonoidHom k)) = 1
    rw [(QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_left (show _ ∈ princ from ⟨k, rfl⟩)), map_one]⟩
  have key := GlobalTheory.FrobDense.eq_one_of_away (η * ξ⁻¹).1 (η * ξ⁻¹).2.1 (η * ξ⁻¹).2.2
    (S ∪ (finite_nat (L := E) hn).toFinset) fun P hP => by
      rw [Finset.mem_union, not_or] at hP
      have hP2 : Valued.v ((Ideal.absNorm c : ℕ) : P.adicCompletion E) = 1 := by simpa using hP.2
      have hη : η.UnrAt P := fun x hx => hk _ (cong_sing hx (by
        rw [hP2]
        exact Valuation.map_sub_le _ (le_of_eq hx) (by simp)))
      refine GlobalTheory.FrobDense.eq_one_of_unif ((η * ξ⁻¹).loc P) fun x hx => ?_
      rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, η.val_eq hη x hx, ξ.val_eq (h P hP.1).1 x hx,
        ← (h P hP.1).2]
      exact mul_inv_cancel _
  exact mul_inv_eq_one.1 (DFunLike.congr_fun key (finIdele E y))

end Pic

section Roots

/- English proof (translation)
Establish `: NeZero m` using `⟨hm⟩`. Establish `hζ` using `Complex.isPrimitiveRoot_exp m hm`. Establish `h1 : ∀ x, ∃ z : ℂˣ, ι z = ψ x` using `fun x => by`. Take `⟨i, -, hi⟩` from `(hζ.map_of_injective ι.injective).eq_pow_of_pow_eq_one (ξ := (ψ x : K)) (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one])`. Conclude with `⟨Units.mk0 _ (pow_ne_zero i (hζ.ne_zero hm)), by rw [Units.val_mk0, map_pow, hi]⟩`.

Use `choose f hf using h1`. Conclude with `⟨MonoidHom.mk' f fun x y => Units.ext (ι.injective (by`. Rewrite using `[Units.val_mul, map_mul ι, hf, hf, hf, map_mul, Units.val_mul])), hf⟩`.
-/
theorem exists_complex_char {Γ K : Type} [Group Γ] [Field K] (ι : ℂ →+* K) (ψ : Γ →* Kˣ) {m : ℕ} (hm : m ≠ 0)
    (h : ∀ x, ψ x ^ m = 1) : ∃ r : Γ →* ℂˣ, ∀ x, ι (r x) = ψ x := by
  have : NeZero m := ⟨hm⟩
  have hζ := Complex.isPrimitiveRoot_exp m hm
  have h1 : ∀ x, ∃ z : ℂˣ, ι z = ψ x := fun x => by
    obtain ⟨i, -, hi⟩ := (hζ.map_of_injective ι.injective).eq_pow_of_pow_eq_one (ξ := (ψ x : K))
      (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one])
    exact ⟨Units.mk0 _ (pow_ne_zero i (hζ.ne_zero hm)), by rw [Units.val_mk0, map_pow, hi]⟩
  choose f hf using h1
  exact ⟨MonoidHom.mk' f fun x y => Units.ext (ι.injective (by
    rw [Units.val_mul, map_mul ι, hf, hf, hf, map_mul, Units.val_mul])), hf⟩

/- English proof (translation)
Simplify using `[BlochKatoReduction.Gen.eq']`.
-/
theorem map_eq {K L : Type} [Field K] [Field L] (f : K →+* L) (Y t : K) (q : ℕ) :
    f (BlochKatoReduction.Gen.eq' Y t q) = BlochKatoReduction.Gen.eq' (f Y) (f t) q := by
  simp [BlochKatoReduction.Gen.eq']

/- English proof (translation)
Rewrite using `[Formalism.PairingDivisionLocalBalance.eq, BlochKatoReduction.Gen.eq', zpow_neg, zpow_natCast, inv_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eq_inv {K : Type} [Field K] (q s : ℕ) (Y : K) :
    Formalism.PairingDivisionLocalBalance.eq q s Y⁻¹ = BlochKatoReduction.Gen.eq' Y ((q : K) ^ (-(s : ℤ))) q := by
  rw [Formalism.PairingDivisionLocalBalance.eq, BlochKatoReduction.Gen.eq', zpow_neg, zpow_natCast, inv_inv]
  ring

end Roots

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

/- English proof (translation)
The claim follows from `GlobalTheory.BaseChangeExistsCompare.unram_of_cm D (GlobalTheory.Mem.host_cmData D.R D.host) P`.
-/
theorem host_unram (P : HeightOneSpectrum (𝓞 D.host.E)) : Algebra.IsUnramifiedAt (OF D.host.E) P.asIdeal :=
  GlobalTheory.BaseChangeExistsCompare.unram_of_cm D (GlobalTheory.Mem.host_cmData D.R D.host) P

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ h`. Establish `h0 : M ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)`. Conclude with `not_dvd_differentIdeal_iff.2 (host_unram ⟨M, hM.isPrime, h0⟩) (Ideal.dvd_iff_le.2 hle)`.
-/
theorem host_unramFin : UnramFin D.host.E := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  have h0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)
  exact not_dvd_differentIdeal_iff.2 (host_unram ⟨M, hM.isPrime, h0⟩) (Ideal.dvd_iff_le.2 hle)

/- English proof (translation)
Use `X.Ok_fin i k` as an intermediate fact. Establish `: FaithfulSMul (X.O i) (X.Ok i k)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)`. Establish `: FaithfulSMul (X.O i) (Kbar X i)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (by`. Rewrite using `[IsScalarTower.algebraMap_eq (X.O i) (FractionRing (X.O i)) (Kbar X i)]`. Conclude with `(algebraMap (FractionRing (X.O i)) (Kbar X i)).injective.comp (IsFractionRing.injective _ _))`.

Set `J0 : X.Ok i k →ₐ[X.O i] Kbar X i` to `IsAlgClosed.lift`. Establish `hJ : Function.Injective J0.toRingHom`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Use `Ideal.eq_bot_of_comap_eq_bot (R := X.O i) ?_` and prove the remaining obligations. Rewrite using `[RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]`.

Introduce `a b hab`. Conclude with `FaithfulSMul.algebraMap_injective (X.O i) (Kbar X i) ((J0.commutes a).symm.trans (Eq.trans hab (J0.commutes b)))`. Use `⟨IsFractionRing.lift hJ, fun x => ?_⟩` and prove the remaining obligations. Use `DFunLike.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors (X.O i)) (j := (IsFractionRing.lift hJ : FractionRing (X.Ok i k) →+* Kbar X i).comp (BlochKatoReduction.Gen.kMap X i k)) (k := algebraMap (FractionRing (X.O i)) (Kbar X i)) (RingHom.ext fun a => ?_)) x` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, BlochKatoReduction.Gen.kMap, IsFractionRing.lift_algebraMap]`.

Conclude with `(J0.commutes a).trans (IsScalarTower.algebraMap_apply _ _ _ a)`.
-/
theorem exists_emb (i : X.Tw) (k : ℕ) : ∃ J : FractionRing (X.Ok i k) →+* Kbar X i,
    ∀ x, J (BlochKatoReduction.Gen.kMap X i k x) = algebraMap (FractionRing (X.O i)) (Kbar X i) x := by
  have := X.Ok_fin i k
  have : FaithfulSMul (X.O i) (X.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)
  have : FaithfulSMul (X.O i) (Kbar X i) := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    rw [IsScalarTower.algebraMap_eq (X.O i) (FractionRing (X.O i)) (Kbar X i)]
    exact (algebraMap (FractionRing (X.O i)) (Kbar X i)).injective.comp (IsFractionRing.injective _ _))
  let J0 : X.Ok i k →ₐ[X.O i] Kbar X i := IsAlgClosed.lift
  have hJ : Function.Injective J0.toRingHom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := X.O i) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    intro a b hab
    exact FaithfulSMul.algebraMap_injective (X.O i) (Kbar X i)
      ((J0.commutes a).symm.trans (Eq.trans hab (J0.commutes b)))
  refine ⟨IsFractionRing.lift hJ, fun x => ?_⟩
  refine DFunLike.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors (X.O i))
    (j := (IsFractionRing.lift hJ : FractionRing (X.Ok i k) →+* Kbar X i).comp (BlochKatoReduction.Gen.kMap X i k))
    (k := algebraMap (FractionRing (X.O i)) (Kbar X i)) (RingHom.ext fun a => ?_)) x
  simp only [RingHom.comp_apply, BlochKatoReduction.Gen.kMap, IsFractionRing.lift_algebraMap]
  exact (J0.commutes a).trans (IsScalarTower.algebraMap_apply _ _ _ a)

/- English proof (translation)
Use `choose n hn using X.RCG_l i Q`. Use `⟨Finset.univ.sup n, fun x => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le (Finset.le_sup (f := n) (Finset.mem_univ x))`. Rewrite using `[hk, pow_add, pow_mul, hn, one_pow]`.
-/
theorem exists_exponent (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    ∃ n : ℕ, ∀ x : X.RCG i Q, x ^ (X.l i ^ n) = 1 := by
  choose n hn using X.RCG_l i Q
  refine ⟨Finset.univ.sup n, fun x => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) (Finset.mem_univ x))
  rw [hk, pow_add, pow_mul, hn, one_pow]

variable {X} {i : X.Tw} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}
  {art : Ideles D.host.E →* Gab D.host.E N.Om} {r : X.RCG i Q →* ℂˣ} {ξ : HChar D.host.E}

/- English proof (translation)
The claim follows from `h.unr ha (N.plOm.2 P) fun σ hσ => by rw [MonoidHom.comp_apply, X.art_unr i Q P hP _ (N.plOm.2 P) σ hσ, map_one]`.
-/
theorem unrAt_of_corr (ha : IsGlobalArtin art) (h : Corr art (r.comp (X.art i Q)) ξ) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : P ∉ Q) : ξ.UnrAt P :=
  h.unr ha (N.plOm.2 P) fun σ hσ => by rw [MonoidHom.comp_apply, X.art_unr i Q P hP _ (N.plOm.2 P) σ hσ, map_one]

/- English proof (translation)
Establish `: IsCMField D.host.E` using `D.host.isCMField_hostE`. Take `⟨n, hn⟩` from `exists_exponent X i Q`. Establish `hp` using `h.pow (m := X.l i ^ n) fun σ => by rw [MonoidHom.comp_apply, ← map_pow, hn, map_one]`. Take `⟨j, hj⟩` from `X.cc_cm.1`. Use `⟨resFin_of_anti (IsCMField.complexConj D.host.E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one _) host_unram (cc := X.cc) (fun x => j.injective ?_) (fun x => j.injective ?_) ha h (fun g g' hg => ?_), fun w k => ?_⟩` and prove the remaining obligations.

Rewrite using `[hj]`. Conclude with `(IsCMField.complexEmbedding_complexConj D.host.E (j.comp (algebraMap D.host.E N.Om)) x).symm`. Rewrite using `[hj, hj, Complex.conj_conj]`. Rewrite using `[MonoidHom.comp_apply, X.art_anti i Q g g' hg, map_inv, MonoidHom.comp_apply]`. Rewrite using `[Formalism.L2.Host.HChar.resInf_apply]`.

Conclude with `Finset.prod_eq_one fun w' _ => locInf_of_pow (pow_ne_zero _ (X.lPrime i).out.ne_zero) hp w' _`.
-/
theorem trivOnF_of_corr (ha : IsGlobalArtin art) (h : Corr art (r.comp (X.art i Q)) ξ) : TrivOnF ξ := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨n, hn⟩ := exists_exponent X i Q
  have hp := h.pow (m := X.l i ^ n) fun σ => by rw [MonoidHom.comp_apply, ← map_pow, hn, map_one]
  obtain ⟨j, hj⟩ := X.cc_cm.1
  refine ⟨resFin_of_anti (IsCMField.complexConj D.host.E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    (IsCMField.complexConj_ne_one _) host_unram (cc := X.cc) (fun x => j.injective ?_) (fun x => j.injective ?_) ha h
    (fun g g' hg => ?_), fun w k => ?_⟩
  · rw [hj]
    exact (IsCMField.complexEmbedding_complexConj D.host.E (j.comp (algebraMap D.host.E N.Om)) x).symm
  · rw [hj, hj, Complex.conj_conj]
  · rw [MonoidHom.comp_apply, X.art_anti i Q g g' hg, map_inv, MonoidHom.comp_apply]
  · rw [Formalism.L2.Host.HChar.resInf_apply]
    exact Finset.prod_eq_one fun w' _ => locInf_of_pow (pow_ne_zero _ (X.lPrime i).out.ne_zero) hp w' _

/- English proof (translation)
Establish `: IsCMField D.host.E` using `D.host.isCMField_hostE`. Take `⟨n, hn⟩` from `exists_exponent X i Q`. Establish `hp` using `h.pow (m := X.l i ^ n) fun σ => by rw [MonoidHom.comp_apply, ← map_pow, hn, map_one]`. Establish `hl` using `pow_ne_zero n (X.lPrime i).out.ne_zero`. Take `⟨h1, h2⟩` from `placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣`.

Use `⟨hχ.1.mul (isUnitary_of_pow hl hp), hχ.2.1.mul (trivOnF_of_corr ha h), fun k => ?_, fun v P hP => ⟨fun hv => ?_, fun hv m => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Formalism.L2.Host.HChar.inf_mul, inf_of_pow hl hp, mul_one]`. Conclude with `hχ.2.2.1 k`. Establish `e` using `(hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)`. Rewrite `e` using `[expIn, multiplicity_eq_zero.2 (h1 v hv).2, expAt_zero_iff]`.

Establish `hPl : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal` using `fun hm => h2 v hv (by`. Rewrite using `[← hP, Ideal.mem_comap, map_natCast]`. Conclude with `hm)`. Introduce `x hx hx1`. Rewrite using `[Formalism.L2.Host.HChar.loc_mul, e x hx, levelLe_one_of_pow (X.lPrime i).out hp hPl x hx hx1, one_mul]`.

Establish `hu : ξ.UnrAt P` using `unrAt_of_corr ha h fun hm => hv (Finset.mem_image.2 ⟨P, hm, HeightOneSpectrum.ext hP⟩)`. Rewrite using `[← (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v) m]`. Use `forall_congr' fun x => forall_congr' fun hx => ?_` and prove the remaining obligations. Rewrite using `[Formalism.L2.Host.HChar.loc_mul, hu x hx, mul_one]`.
-/
theorem isValChar_mul (ha : IsGlobalArtin art) (h : Corr art (r.comp (X.art i Q)) ξ) (hQ : BlochKatoReduction.Gen.QOk X i Q)
    {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF D.host.E)} {χ : HChar D.host.E}
    (h𝔣 : ∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) (hχ : IsValChar φ s κ 𝔣 ∅ χ) :
    IsValChar φ s κ 𝔣 (belowSet Q) (χ * ξ) := by
  classical
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨n, hn⟩ := exists_exponent X i Q
  have hp := h.pow (m := X.l i ^ n) fun σ => by rw [MonoidHom.comp_apply, ← map_pow, hn, map_one]
  have hl := pow_ne_zero n (X.lPrime i).out.ne_zero
  obtain ⟨h1, h2⟩ := placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣
  refine ⟨hχ.1.mul (isUnitary_of_pow hl hp), hχ.2.1.mul (trivOnF_of_corr ha h), fun k => ?_, fun v P hP => ⟨fun hv => ?_,
    fun hv m => ?_⟩⟩
  · rw [Formalism.L2.Host.HChar.inf_mul, inf_of_pow hl hp, mul_one]
    exact hχ.2.2.1 k
  · have e := (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)
    rw [expIn, multiplicity_eq_zero.2 (h1 v hv).2, expAt_zero_iff] at e
    have hPl : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun hm => h2 v hv (by
      rw [← hP, Ideal.mem_comap, map_natCast]
      exact hm)
    intro x hx hx1
    rw [Formalism.L2.Host.HChar.loc_mul, e x hx, levelLe_one_of_pow (X.lPrime i).out hp hPl x hx hx1, one_mul]
  · have hu : ξ.UnrAt P := unrAt_of_corr ha h fun hm =>
      hv (Finset.mem_image.2 ⟨P, hm, HeightOneSpectrum.ext hP⟩)
    rw [← (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v) m]
    refine forall_congr' fun x => forall_congr' fun hx => ?_
    rw [Formalism.L2.Host.HChar.loc_mul, hu x hx, mul_one]

/- English proof (translation)
Use `GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 fun ⟨t, ht⟩ => ?_` and prove the remaining obligations. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hb.2.1`. Set `v : HeightOneSpectrum (OF E)` to `⟨M, hM.isPrime, fun h => hb.1 (le_bot_iff.1 (h ▸ hle))⟩`. Establish `hv : v.asIdeal ∣ 𝔣` using `Ideal.dvd_iff_le.2 hle`. Take `⟨P, -, -, hP, -⟩` from `(hb.2.2 v hv).1`.

Use `((hχ.2.2.2 v P hP).2 fun hm => (hT v hm).2 hv).not_unrAt (multiplicity_ne_zero.2 hv) ?_` and prove the remaining obligations. Rewrite using `[(GlobalTheory.HeckeOne.isNormPow_iff _ _).1 ht]`. Conclude with `GlobalTheory.HeckeOne.unrAt_normChar t P`.
-/
theorem exists_isHeckeL {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {T : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hb : IsBaseCond 𝔣) (hT : IsFinSetSplitPlacesCoprimeConductor 𝔣 T)
    (hχ : IsValChar φ s κ 𝔣 T χ) : ∃ Λ, IsHeckeL χ Λ := by
  refine GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 fun ⟨t, ht⟩ => ?_
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hb.2.1
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, fun h => hb.1 (le_bot_iff.1 (h ▸ hle))⟩
  have hv : v.asIdeal ∣ 𝔣 := Ideal.dvd_iff_le.2 hle
  obtain ⟨P, -, -, hP, -⟩ := (hb.2.2 v hv).1
  refine ((hχ.2.2.2 v P hP).2 fun hm => (hT v hm).2 hv).not_unrAt (multiplicity_ne_zero.2 hv) ?_
  rw [(GlobalTheory.HeckeOne.isNormPow_iff _ _).1 ht]
  exact GlobalTheory.HeckeOne.unrAt_normChar t P

/- English proof (translation)
Use `Fintype.ofFinite (PicO c)` as an intermediate fact. Establish `hfin : ∀ q : PicO c, r (π q) = finPart ξ q.out` using `fun q => by`. Rewrite using `[← pic_char_eq_finPart hc (r.comp π) ξ (X.S0 i ∪ Q) (fun P hP => ?_), QuotientGroup.out_eq', MonoidHom.comp_apply]`. Rewrite `hP` using `[Finset.mem_union, not_or]`. Take `⟨σ, hσ⟩` from `exists_isFrob (N.plOm.2 P)`.

Establish `hu` using `unrAt_of_corr ha h hP.2`. Conclude with `⟨hu, by rw [h.val ha (N.plOm.2 P) hu hσ, MonoidHom.comp_apply, hπ P hP.1 hP.2 σ hσ, map_inv, MonoidHom.comp_apply]⟩`. Establish `e : t = ∑ q, T q * (r (π q⁻¹) : ℂ)`. Use `ht.unique ((isToricSum_iff _ _ _ _ _ _).2 ⟨inferInstance, fun q => T q * (r (π q⁻¹) : ℂ), fun q => ?_, (finsum_eq_sum_of_fintype _).symm⟩)` and prove the remaining obligations. Take `⟨S, hS, hTq⟩` from `hT q`.

Use `⟨S, hS, ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[hTq, map_inv, map_inv, hfin, finPart_mul, Units.val_mul, Units.val_inv_eq_inv_val]`. Simplify using `only [mul_inv]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹), map_sum, Finset.mul_sum, BlochKatoReduction.Gen.thEval, map_sum]`. Use `Finset.sum_congr rfl fun δ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hJ, hδ, ← hr, mul_assoc, ← map_mul]`. Use `congr 2`. Rewrite using `[show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.1 hq).2]`.
-/
theorem thEval_eq (ha : IsGlobalArtin art) (h : Corr art (r.comp (X.art i Q)) ξ) {k : ℕ} {ψ : X.RCG i Q →* (X.Ok i k)ˣ}
    {ι : ℂ →+* Kbar X i} {J : FractionRing (X.Ok i k) →+* Kbar X i}
    (hJ : ∀ x, J (BlochKatoReduction.Gen.kMap X i k x) = algebraMap (FractionRing (X.O i)) (Kbar X i) x)
    (hr : ∀ x, ι (r x) = J (algebraMap (X.Ok i k) _ (ψ x : X.Ok i k)))
    {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF D.host.E)} (hc : c ≠ ⊥)
    {χ : HChar D.host.E} {lam : X.abelian₂ i} {u : Kbar X i} [Finite (PicO c)] {π : PicO c →* X.RCG i Q} {T : PicO c → ℂ}
    (hπ : IsRecMap X i Q π) (hT : ∀ q, IsClassTerm φ s κ c χ q.out (T q))
    (hδ : ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q))
    {t : ℂ} (ht : IsToricSum φ s κ c (χ * ξ) t) : J (BlochKatoReduction.Gen.thEval X i Q lam k ψ) = u * ι t := by
  classical
  have := Fintype.ofFinite (PicO c)
  have hfin : ∀ q : PicO c, r (π q) = finPart ξ q.out := fun q => by
    rw [← pic_char_eq_finPart hc (r.comp π) ξ (X.S0 i ∪ Q) (fun P hP => ?_), QuotientGroup.out_eq', MonoidHom.comp_apply]
    rw [Finset.mem_union, not_or] at hP
    obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 P)
    have hu := unrAt_of_corr ha h hP.2
    exact ⟨hu, by rw [h.val ha (N.plOm.2 P) hu hσ, MonoidHom.comp_apply, hπ P hP.1 hP.2 σ hσ, map_inv,
      MonoidHom.comp_apply]⟩
  have e : t = ∑ q, T q * (r (π q⁻¹) : ℂ) := by
    refine ht.unique ((isToricSum_iff _ _ _ _ _ _).2 ⟨inferInstance, fun q => T q * (r (π q⁻¹) : ℂ), fun q => ?_,
      (finsum_eq_sum_of_fintype _).symm⟩)
    obtain ⟨S, hS, hTq⟩ := hT q
    refine ⟨S, hS, ?_⟩
    beta_reduce
    rw [hTq, map_inv, map_inv, hfin, finPart_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    simp only [mul_inv]
    ring
  rw [e, ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹), map_sum, Finset.mul_sum, BlochKatoReduction.Gen.thEval, map_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [map_mul, hJ, hδ, ← hr, mul_assoc, ← map_mul]
  congr 2
  rw [show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.1 hq).2]

end Record

section Entire

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm) in

/- English proof (translation)
Use `GlobalTheory.HeckeOne.entire_of_not_normPow hu fun ⟨t, ht⟩ => ?_` and prove the remaining obligations. Establish `hn : ∀ k : Eˣ, ideleNorm (infDiag k) = ∏ w : InfinitePlace E, w (k : E) ^ w.mult` using `fun k => by`. Rewrite using `[infDiag_eq]`. Express the relevant statement in the definitionally equal form `(∏ v : InfinitePlace E, ‖algebraMap E v.Completion k‖ ^ v.mult) * (∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(1 : v.adicCompletion E)‖) = _`. Simplify using `only [GlobalTheory.FrobDense.norm_inf, norm_one, finprod_one, mul_one]`.

Establish `h1 : Function.Injective φ` using `fun i j h => (hφ (φ i)).unique (Or.inl rfl) (Or.inl h)`. Establish `h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j)` using `fun i j h => by`. Take `rfl : i = j` from `(hφ (φ i)).unique (Or.inl rfl) (Or.inr h)`. Conclude with `IsTotallyComplex.complexEmbedding_not_isReal (φ i) h.symm`. Establish `key` using `GlobalTheory.HalfIntChars.hasInf_unique φ h1 h2 hm (n' := fun i => -(2 * m i)) fun k => by`.

Set `k' : Eˣ` to `Units.map (IsCMField.complexConj E).toRingEquiv.toMonoidHom k`. Establish `hk : ∀ σ : E →+* ℂ, σ (k' : E) = starRingEnd ℂ (σ k)` using `fun σ => IsCMField.complexEmbedding_complexConj E σ k`. Establish `e : ((χ.inf k : ℂˣ) : ℂ) = χ.inf k'`. Use `(ht _).trans (Eq.trans ?_ (ht _).symm)` and prove the remaining obligations. Rewrite using `[hn, hn]`.

Simplify using `only [← InfinitePlace.norm_embedding_eq, hk, Complex.norm_conj]`. Rewrite using `[e, hm k']`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hz : φ i k ≠ 0` using `by simp`. Establish `hz' : ((‖φ i k‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hz`.

Rewrite using `[hk, Complex.norm_conj, zpow_neg, ← inv_zpow, inv_div]`. Use `congr 1`. Rewrite using `[div_eq_div_iff hz' hz, mul_comm, Complex.mul_conj', sq]`. Take `⟨i, hi⟩` from `h0`. Use `congrFun key i` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_isHeckeL_of_hasInf (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (m : I → ℤ) (χ : HChar E) (hφ : IsCMType φ) (hu : IsUnitary χ) (hm : HasInf χ φ m) (h0 : ∃ i, m i ≠ 0) :
    ∃ Λ, IsHeckeL χ Λ := by
  refine GlobalTheory.HeckeOne.entire_of_not_normPow hu fun ⟨t, ht⟩ => ?_
  have hn : ∀ k : Eˣ, ideleNorm (infDiag k) = ∏ w : InfinitePlace E, w (k : E) ^ w.mult := fun k => by
    rw [infDiag_eq]
    change (∏ v : InfinitePlace E, ‖algebraMap E v.Completion k‖ ^ v.mult) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(1 : v.adicCompletion E)‖) = _
    simp only [GlobalTheory.FrobDense.norm_inf, norm_one, finprod_one, mul_one]
  have h1 : Function.Injective φ := fun i j h => (hφ (φ i)).unique (Or.inl rfl) (Or.inl h)
  have h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j) := fun i j h => by
    obtain rfl : i = j := (hφ (φ i)).unique (Or.inl rfl) (Or.inr h)
    exact IsTotallyComplex.complexEmbedding_not_isReal (φ i) h.symm
  have key := GlobalTheory.HalfIntChars.hasInf_unique φ h1 h2 hm (n' := fun i => -(2 * m i)) fun k => by
    let k' : Eˣ := Units.map (IsCMField.complexConj E).toRingEquiv.toMonoidHom k
    have hk : ∀ σ : E →+* ℂ, σ (k' : E) = starRingEnd ℂ (σ k) := fun σ =>
      IsCMField.complexEmbedding_complexConj E σ k
    have e : ((χ.inf k : ℂˣ) : ℂ) = χ.inf k' := by
      refine (ht _).trans (Eq.trans ?_ (ht _).symm)
      rw [hn, hn]
      simp only [← InfinitePlace.norm_embedding_eq, hk, Complex.norm_conj]
    rw [e, hm k']
    refine Finset.prod_congr rfl fun i _ => ?_
    have hz : φ i k ≠ 0 := by simp
    have hz' : ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
    rw [hk, Complex.norm_conj, zpow_neg, ← inv_zpow, inv_div]
    congr 1
    rw [div_eq_div_iff hz' hz, mul_comm, Complex.mul_conj', sq]
  obtain ⟨i, hi⟩ := h0
  have := congrFun key i
  omega

end Entire

section Main

open GlobalTheory.Mem.Chr

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

/- English proof (translation)
Establish `e : ∀ z, (IsCMField.complexConj D.host.E).toRingEquiv z = D.host.conj z` using `fun z => by`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Conclude with `(IsCMField.complexEmbedding_complexConj _ _ z).trans (Formalism.HC.HostAx.conjE_apply _ _ z).symm`. Rewrite using `[conjPl_iff_mem]`. Simplify using `only [e]`.

Both sides reduce to the same expression.
-/
theorem conjPl_iff [IsCMField D.host.E] (P P' : HeightOneSpectrum (𝓞 D.host.E)) :
    ConjPl (IsCMField.complexConj D.host.E).toRingEquiv P P' ↔ IsConjPl D.host P P' := by
  have e : ∀ z, (IsCMField.complexConj D.host.E).toRingEquiv z = D.host.conj z := fun z => by
    apply D.host.φ₀.injective
    exact (IsCMField.complexEmbedding_complexConj _ _ z).trans (Formalism.HC.HostAx.conjE_apply _ _ z).symm
  rw [conjPl_iff_mem]
  simp only [e]
  rfl

/- English proof (translation)
Establish `: IsCMField D.host.E` using `D.host.isCMField_hostE`. Establish `e` using `aboveF_under (IsCMField.complexConj D.host.E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one _) ((conjPl_iff P Pb).2 h)`. Use `mem_aboveF.symm.trans ?_` and prove the remaining obligations. Rewrite using `[below, e, Finset.mem_insert, Finset.mem_singleton]`.
-/
theorem below_eq_iff {P Pb : HeightOneSpectrum (𝓞 D.host.E)} (h : IsConjPl D.host P Pb) (P' : HeightOneSpectrum (𝓞 D.host.E)) :
    below P' = below P ↔ P' = P ∨ P' = Pb := by
  classical
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have e := aboveF_under (IsCMField.complexConj D.host.E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    (IsCMField.complexConj_ne_one _) ((conjPl_iff P Pb).2 h)
  refine mem_aboveF.symm.trans ?_
  rw [below, e, Finset.mem_insert, Finset.mem_singleton]

open Classical in

/- English proof (translation)
Introduce `i hi Q hQ lam s hs P Pb hP hPb hne hconj k ψ σ hσ`. Establish `: IsCMField D.host.E` using `D.host.isCMField_hostE`. Take `⟨s, rfl⟩` from `Int.eq_ofNat_of_zero_le (le_trans zero_le_one hs.2.1)`. Take `⟨ι₀, -, hι⟩` from `ht i hi`. Take `⟨I, _, φ, κ, 𝔣, χ, u, hD, h𝔣, hX, -, hth⟩` from `hι lam s hs`.

Generalize the expression as in `atSide X (X.sideL i lam) ι₀ = ι at hX hth`. Take `⟨art, ha⟩` from `hA D.host.E N.Om`. Establish `hmem : ∀ v, v ∈ (Q.erase P).erase Pb ↔ v ∈ Q ∧ below v ≠ below P` using `fun v => by`. Rewrite using `[Finset.mem_erase, Finset.mem_erase, Ne, Ne, Ne, below_eq_iff hconj]`. The claim follows by propositional logic.

Use `generalize_proofs _ hsub`. Generalize the expression as in `(Q.erase P).erase Pb = Q' at *`. Establish `hQ' : BlochKatoReduction.Gen.QOk X i Q'` using `⟨fun v hv => hQ.1 v (hsub hv), hQ.2.1.mono_left hsub, fun v hv v' h => (hmem v').2 ⟨hQ.2.2 v (hsub hv) v' h, by`. Rewrite using `[(below_eq_iff h v').2 (Or.inr rfl)]`. Conclude with `((hmem v).1 hv).2⟩⟩`.

Establish `hnot : below P ∉ belowSet Q'` using `fun h => by`. Take `⟨v, hv, e⟩` from `Finset.mem_image.1 h`. Conclude with `((hmem v).1 hv).2 e`. Establish `hins : belowSet Q = insert (below P) (belowSet Q')`. Use extensionality with `v`.

Simplify using `only [belowSet, Finset.mem_insert, Finset.mem_image, hmem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Distinguish the cases in `e : below w = below P`. Conclude with `Or.inl e`.

Conclude with `Or.inr ⟨w, ⟨hw, e⟩, rfl⟩`. Introduce and unpack `(rfl | ⟨w, hw, rfl⟩)`. Conclude with `⟨P, hP, rfl⟩`. Conclude with `⟨w, hw.1, rfl⟩`. Take `⟨J, hJ⟩` from `exists_emb X i k`.

Take `⟨n, hn⟩` from `exists_exponent X i Q'`. Take `⟨r, hr⟩` from `exists_complex_char ι ((Units.map (J.comp (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)))).toMonoidHom).comp ψ) (pow_ne_zero n (X.lPrime i).out.ne_zero) fun x => by rw [← map_pow, hn, map_one]`. Take `⟨ξ, hξ'⟩` from `exists_corr (r := r.comp (X.art i Q')) ha (Subgroup.isOpen_mono (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hg, map_one]) (X.art_cont i Q'))`. Establish `hξ : Corr art ((r.comp (X.res i Q Q' hsub)).comp (X.art i Q)) ξ`. Rewrite using `[MonoidHom.comp_assoc, X.res_art]` and apply the resulting hypothesis.

Establish `hv` using `isValChar_mul ha hξ hQ h𝔣 hD.2.2.2.2.2`. Establish `hv'` using `isValChar_mul ha hξ' hQ' h𝔣 hD.2.2.2.2.2`. Establish `hb` using `hD.2.2.2.2.1`. Take `⟨Λ, hΛ⟩` from `exists_isHeckeL hb (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1 hv`. Choose the witnesses or unpack the hypotheses as in `⟨Pq, hPq, hPP⟩ : ∃ Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E), (∀ q ∈ belowSet Q, Over (Pq q) q) ∧ Pq (below P) = P := by`.

Establish `: ∀ q : HeightOneSpectrum (OF D.host.E), ∃ w, (q ∈ belowSet Q → Over w q) ∧ (q = below P → w = P)` using `fun q => by`. Distinguish the cases in `e : q = below P`. Conclude with `⟨P, fun _ => e ▸ over_below P, fun _ => rfl⟩`. Distinguish the cases in `e' : q ∈ belowSet Q`. Take `⟨w, -, rfl⟩` from `Finset.mem_image.1 e'`.

Conclude with `⟨w, fun _ => over_below w, fun h => absurd h e⟩`. Conclude with `⟨P, fun h => absurd h e', fun _ => rfl⟩`. Use `choose Pq h1 h2 using this`. Conclude with `⟨Pq, h1, h2 _ rfl⟩`. Establish `hc : ∀ T, condQ 𝔣 T ≠ ⊥` using `fun T => mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)`.

Establish `t1` using `hL _ I φ hD.1 s κ 𝔣 _ _ Pq Λ host_unramFin hD.2.2.1 hb (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1 hv hPq hΛ`. Establish `t2` using `hL _ I φ hD.1 s κ 𝔣 _ _ Pq Λ host_unramFin hD.2.2.1 hb (placesBelow_splitCoprimeConductor_of_admissible hQ' h𝔣).1 hv' (fun q hq => hPq q (hins ▸ Finset.mem_insert_of_mem hq)) hΛ`. Take `⟨_, π, T, hπ, hT, hδ⟩` from `hth Q hQ`. Take `⟨_, π', T', hπ', hT', hδ'⟩` from `hth Q' hQ'`. Establish `e1` using `thEval_eq ha hξ (ψ := ψ.comp (X.res i Q Q' hsub)) hJ (fun x => hr _) (hc _) hπ hT hδ t1`.

Establish `e2` using `thEval_eq ha hξ' (ψ := ψ) hJ hr (hc _) hπ' hT' hδ' t2`. Establish `hPS : P ∉ X.S0 i` using `Finset.disjoint_left.1 hQ.2.1 hP`. Establish `huξ : ξ.UnrAt P` using `unrAt_of_corr ha hξ' fun h => ((hmem P).1 h).2 rfl`. Establish `huχ : χ.UnrAt P`. Establish `e` using `(hD.2.2.2.2.2.2.2.2 _ P (over_below P)).2 (Finset.notMem_empty _)`.

Rewrite `e` using `[expIn, multiplicity_eq_zero.2 fun h => hPS (h𝔣 P h), expAt_zero_iff]`. Then use the resulting hypothesis. Establish `hN : Ideal.absNorm (below P).asIdeal = normV P` using `((normV_eq P).trans (absNorm_split (IsCMField.complexConj D.host.E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one _) host_unram ((conjPl_iff P Pb).2 hconj) hne)).symm`. Apply `J.injective` to reduce the goal to its premises. Rewrite using `[map_mul, e1, e2, hins, Finset.filter_insert, if_pos (hPP.symm ▸ huχ.mul huξ), Finset.prod_insert fun h => hnot (Finset.mem_filter.1 h).1, hPP, hN, ← inv_inv (val (χ * ξ) P : ℂ), eq_inv, map_eq, map_mul J, hJ, ← IsScalarTower.algebraMap_apply, map_zpow₀, map_natCast, mul_left_com …`. Use `congr 2`.

Rewrite using `[Formalism.L2.Host.HChar.val_mul, hξ'.val ha (N.plOm.2 P) huξ hσ, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv, inv_inv, map_mul, map_inv₀, eq_inv_of_mul_eq_one_left (hX P hPS)]`. Conclude with `congrArg _ (hr _)`.
-/
theorem gen_relation (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hL : ToricSumFormula) (ht : IsToricElt X) : BlochKatoReduction.Gen.adm10 X := by
  intro i hi Q hQ lam s hs P Pb hP hPb hne hconj k ψ σ hσ
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans zero_le_one hs.2.1)
  obtain ⟨ι₀, -, hι⟩ := ht i hi
  obtain ⟨I, _, φ, κ, 𝔣, χ, u, hD, h𝔣, hX, -, hth⟩ := hι lam s hs
  generalize atSide X (X.sideL i lam) ι₀ = ι at hX hth
  obtain ⟨art, ha⟩ := hA D.host.E N.Om
  have hmem : ∀ v, v ∈ (Q.erase P).erase Pb ↔ v ∈ Q ∧ below v ≠ below P := fun v => by
    rw [Finset.mem_erase, Finset.mem_erase, Ne, Ne, Ne, below_eq_iff hconj]
    tauto
  generalize_proofs _ hsub
  generalize (Q.erase P).erase Pb = Q' at *
  have hQ' : BlochKatoReduction.Gen.QOk X i Q' := ⟨fun v hv => hQ.1 v (hsub hv), hQ.2.1.mono_left hsub, fun v hv v' h =>
    (hmem v').2 ⟨hQ.2.2 v (hsub hv) v' h, by
      rw [(below_eq_iff h v').2 (Or.inr rfl)]
      exact ((hmem v).1 hv).2⟩⟩
  have hnot : below P ∉ belowSet Q' := fun h => by
    obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
    exact ((hmem v).1 hv).2 e
  have hins : belowSet Q = insert (below P) (belowSet Q') := by
    ext v
    simp only [belowSet, Finset.mem_insert, Finset.mem_image, hmem]
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases e : below w = below P
      · exact Or.inl e
      · exact Or.inr ⟨w, ⟨hw, e⟩, rfl⟩
    · rintro (rfl | ⟨w, hw, rfl⟩)
      · exact ⟨P, hP, rfl⟩
      · exact ⟨w, hw.1, rfl⟩
  obtain ⟨J, hJ⟩ := exists_emb X i k
  obtain ⟨n, hn⟩ := exists_exponent X i Q'
  obtain ⟨r, hr⟩ := exists_complex_char ι
    ((Units.map (J.comp (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)))).toMonoidHom).comp ψ)
    (pow_ne_zero n (X.lPrime i).out.ne_zero) fun x => by rw [← map_pow, hn, map_one]
  obtain ⟨ξ, hξ'⟩ := exists_corr (r := r.comp (X.art i Q')) ha
    (Subgroup.isOpen_mono (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hg, map_one]) (X.art_cont i Q'))
  have hξ : Corr art ((r.comp (X.res i Q Q' hsub)).comp (X.art i Q)) ξ := by
    rwa [MonoidHom.comp_assoc, X.res_art]
  have hv := isValChar_mul ha hξ hQ h𝔣 hD.2.2.2.2.2
  have hv' := isValChar_mul ha hξ' hQ' h𝔣 hD.2.2.2.2.2
  have hb := hD.2.2.2.2.1
  obtain ⟨Λ, hΛ⟩ := exists_isHeckeL hb (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1 hv
  obtain ⟨Pq, hPq, hPP⟩ : ∃ Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E),
      (∀ q ∈ belowSet Q, Over (Pq q) q) ∧ Pq (below P) = P := by
    have : ∀ q : HeightOneSpectrum (OF D.host.E), ∃ w, (q ∈ belowSet Q → Over w q) ∧ (q = below P → w = P) := fun q => by
      by_cases e : q = below P
      · exact ⟨P, fun _ => e ▸ over_below P, fun _ => rfl⟩
      · by_cases e' : q ∈ belowSet Q
        · obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 e'
          exact ⟨w, fun _ => over_below w, fun h => absurd h e⟩
        · exact ⟨P, fun h => absurd h e', fun _ => rfl⟩
    choose Pq h1 h2 using this
    exact ⟨Pq, h1, h2 _ rfl⟩
  have hc : ∀ T, condQ 𝔣 T ≠ ⊥ := fun T => mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have t1 := hL _ I φ hD.1 s κ 𝔣 _ _ Pq Λ host_unramFin hD.2.2.1 hb (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1 hv hPq hΛ
  have t2 := hL _ I φ hD.1 s κ 𝔣 _ _ Pq Λ host_unramFin hD.2.2.1 hb (placesBelow_splitCoprimeConductor_of_admissible hQ' h𝔣).1 hv'
    (fun q hq => hPq q (hins ▸ Finset.mem_insert_of_mem hq)) hΛ
  obtain ⟨_, π, T, hπ, hT, hδ⟩ := hth Q hQ
  obtain ⟨_, π', T', hπ', hT', hδ'⟩ := hth Q' hQ'
  have e1 := thEval_eq ha hξ (ψ := ψ.comp (X.res i Q Q' hsub)) hJ (fun x => hr _) (hc _) hπ hT hδ t1
  have e2 := thEval_eq ha hξ' (ψ := ψ) hJ hr (hc _) hπ' hT' hδ' t2
  have hPS : P ∉ X.S0 i := Finset.disjoint_left.1 hQ.2.1 hP
  have huξ : ξ.UnrAt P := unrAt_of_corr ha hξ' fun h => ((hmem P).1 h).2 rfl
  have huχ : χ.UnrAt P := by
    have e := (hD.2.2.2.2.2.2.2.2 _ P (over_below P)).2 (Finset.notMem_empty _)
    rwa [expIn, multiplicity_eq_zero.2 fun h => hPS (h𝔣 P h), expAt_zero_iff] at e
  have hN : Ideal.absNorm (below P).asIdeal = normV P :=
    ((normV_eq P).trans (absNorm_split (IsCMField.complexConj D.host.E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
      (IsCMField.complexConj_ne_one _) host_unram ((conjPl_iff P Pb).2 hconj) hne)).symm
  apply J.injective
  rw [map_mul, e1, e2, hins, Finset.filter_insert, if_pos (hPP.symm ▸ huχ.mul huξ),
    Finset.prod_insert fun h => hnot (Finset.mem_filter.1 h).1, hPP, hN, ← inv_inv (val (χ * ξ) P : ℂ), eq_inv,
    map_eq, map_mul J, hJ, ← IsScalarTower.algebraMap_apply, map_zpow₀, map_natCast, mul_left_comm (Λ s), map_mul ι,
    map_eq, map_zpow₀, map_natCast, mul_left_comm u]
  congr 2
  rw [Formalism.L2.Host.HChar.val_mul, hξ'.val ha (N.plOm.2 P) huξ hσ, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv, inv_inv,
    map_mul, map_inv₀, eq_inv_of_mul_eq_one_left (hX P hPS)]
  exact congrArg _ (hr _)

end Main

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ ht => gen_relation hA hL ht, fun _ ht => gen_relation hA hL ht⟩`.
-/
theorem distribution_relation (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hL : ToricSumFormula) :
    (∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N), IsToricElt X → BlochKatoReduction.Gen.adm10 X) ∧
    ∀ D : D7, IsToricElt D.ntw → BlochKatoReduction.adm10 D :=
  ⟨fun _ _ _ ht => gen_relation hA hL ht, fun _ ht => gen_relation hA hL ht⟩

end GlobalTheory.ToricDistribution

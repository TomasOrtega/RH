import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedCmTypeHeckeCharOnHost
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveCharacterOfIsCyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAl
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostDeltaCharacterInertialOrderFifteenExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPowClassNumber
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfInfOfVal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.Inhab

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Chr
open scoped Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem loc_pow {L : Type} [Field L] [NumberField L] (χ : HChar L) (n : ℕ) (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ) : (χ ^ n).loc v x = χ.loc v x ^ n := rfl

/- English proof (translation)
Establish `hx : ∀ x, (χ.1 x) ^ n = 1` using `fun x => congrArg (fun ξ : HChar L => ξ.1 x) h`. Establish `hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.locInf w y = 1`. Introduce `w y`. Set `e` to `InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn`.

Establish `hz' : (e.symm z) ^ n = y` using `by rw [← map_pow, hz]; simp`. Establish `hz0 : e.symm z ≠ 0`. Introduce `h0`. Rewrite `hz'` using `[h0, zero_pow hn.ne']`. Conclude with `y.ne_zero hz'.symm`.

Establish `: y = (Units.mk0 _ hz0) ^ n` using `Units.ext (by simp [hz'])`. Rewrite using `[this, map_pow]`. Conclude with `hx _`. Use `show χ.1 (infDiag k) = 1`. Unfold `infDiag`.

Rewrite using `[MonoidHom.finset_prod_apply, map_prod]`. Conclude with `Finset.prod_eq_one fun w _ => hw w _`.
-/
theorem inf_eq_one {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.locInf w y = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow]
    exact hx _
  show χ.1 (infDiag k) = 1
  unfold infDiag
  rw [MonoidHom.finset_prod_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

/- English proof (translation)
Establish `: IsTotallyComplex H.E`. Use `H.isCMField_hostE` as an intermediate fact. Use `infer_instance`. Take `⟨n, hn, ho⟩` from `h.fin`. Establish `hu : ∀ v, (χ ^ 15).UnrAt v` using `fun v x hx => by`.

Rewrite using `[loc_pow]`. Distinguish the cases in `hv : OverP H p v`. Conclude with `(h.ine v hv 15).2 dvd_rfl x hx`. Rewrite using `[h.unr v hv x hx, one_pow]`. Establish `hi : ∀ k, (χ ^ 15).inf k = 1` using `fun k => by`.

Express the relevant statement in the definitionally equal form `χ.inf k ^ 15 = 1`. Rewrite using `[inf_eq_one hn ho k, one_pow]`. Unfold `HChar.OrderDvd`. Rewrite using `[pow_mul]`. Use `GlobalTheory.HeckeUnrTrivial.eq_one_of_val_eq_one _ fun v _ => ?_` and prove the remaining obligations.

Conclude with `GlobalTheory.Mem.ChiVal.val_pow_classNumber _ hu hi v`.
-/
theorem isDelta_orderDvd {R : Ranks} {H : Formalism.BasicNotions.Host R} {p : ℕ} {χ : HChar H.E} (h : IsDelta (H := H) p χ) :
    χ.OrderDvd (15 * classNumber H.E) := by
  have : IsTotallyComplex H.E := by
    have := H.isCMField_hostE
    infer_instance
  obtain ⟨n, hn, ho⟩ := h.fin
  have hu : ∀ v, (χ ^ 15).UnrAt v := fun v x hx => by
    rw [loc_pow]
    by_cases hv : OverP H p v
    · exact (h.ine v hv 15).2 dvd_rfl x hx
    · rw [h.unr v hv x hx, one_pow]
  have hi : ∀ k, (χ ^ 15).inf k = 1 := fun k => by
    change χ.inf k ^ 15 = 1
    rw [inf_eq_one hn ho k, one_pow]
  unfold HChar.OrderDvd
  rw [pow_mul]
  refine GlobalTheory.HeckeUnrTrivial.eq_one_of_val_eq_one _ fun v _ => ?_
  exact GlobalTheory.Mem.ChiVal.val_pow_classNumber _ hu hi v

/- English proof (translation)
Use `GlobalTheory.NormOneChar.mem_of_pow_eq_one (Nat.mul_pos (by norm_num) (classNumber_pos _)) hz ?_` and prove the remaining obligations. Establish `h1 : (χ.1 x) ^ (15 * classNumber H.E) = 1` using `congrArg (fun ξ : HChar H.E => ξ.1 x) (isDelta_orderDvd h)`. Rewrite using `[← Units.val_pow_eq_pow_val, h1, Units.val_one]`.
-/
theorem isDelta_mem {R : Ranks} {H : Formalism.BasicNotions.Host R} {p : ℕ} {χ : HChar H.E} (h : IsDelta (H := H) p χ)
    {M : IntermediateField ℚ ℂ} (hz : ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (15 * classNumber H.E) ∈ M) (x) :
    ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  refine GlobalTheory.NormOneChar.mem_of_pow_eq_one (Nat.mul_pos (by norm_num) (classNumber_pos _)) hz ?_
  have h1 : (χ.1 x) ^ (15 * classNumber H.E) = 1 := congrArg (fun ξ : HChar H.E => ξ.1 x) (isDelta_orderDvd h)
  rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]

variable {D : D7}

/- English proof (translation)
Take `⟨-, ⟨W⟩⟩` from `GlobalTheory.nonempty_piBar_and_omg D.R D.host`. Establish `hmu : ∀ j : Fin D.R.m, ∃ χ : HChar D.host.E, IsMu0 P W (eExp D j) j.1 χ` using `fun j => GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes D.R D.host P W (eExp D j) j.1 D.nd.g_split (fun τ => (D.hc _).e_int j) (by`. Use `(UpperTheory.MUQ.equiv_iff D.eTau).1 ?_` and prove the remaining obligations. Simplify `he j)` using `only [embPsi, eExp, Equiv.symm_apply_apply]`. Use `choose mu hmu using hmu`.

Take `⟨eta, heta⟩` from `GlobalTheory.Mem.EtaT.etaT_exists D.R D.host`. Take `⟨chi, hchi⟩` from `GlobalTheory.Mem.ChiPsiExist.exists_chiPsi D.R D.host`. Take `⟨d, hd⟩` from `GlobalTheory.Mem.DeltaZero.delta_exists D.R D.host _ D.host.pde_prime D.host.pde_mod.1 h₁`. Take `⟨d', hd'⟩` from `GlobalTheory.Mem.DeltaZero.delta_exists D.R D.host _ D.host.pde'_prime D.host.pde_mod.2 h₂`. Conclude with `⟨⟨P, W, mu, eta, chi, d, d', hmu, heta, hchi, hd, hd'⟩, rfl⟩`.
-/
theorem exists_charFrame (D : D7) (P : PiBar D.host) (h₁ : SplitsC D.host.E D.host.pde) (h₂ : SplitsC D.host.E D.host.pde')
    (he : ∀ j : Fin D.R.m, UpperTheory.MUQ (fun τ => D.host.emb (D.eTau τ : D.R.GG)) (fun τ => (D.hc τ).e j)) : ∃ C : CharFrame D, C.P = P := by
  obtain ⟨-, ⟨W⟩⟩ := GlobalTheory.nonempty_piBar_and_omg D.R D.host
  have hmu : ∀ j : Fin D.R.m, ∃ χ : HChar D.host.E, IsMu0 P W (eExp D j) j.1 χ := fun j =>
    GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes D.R D.host P W (eExp D j) j.1 D.nd.g_split (fun τ => (D.hc _).e_int j) (by
      refine (UpperTheory.MUQ.equiv_iff D.eTau).1 ?_
      simpa only [embPsi, eExp, Equiv.symm_apply_apply] using he j)
  choose mu hmu using hmu
  obtain ⟨eta, heta⟩ := GlobalTheory.Mem.EtaT.etaT_exists D.R D.host
  obtain ⟨chi, hchi⟩ := GlobalTheory.Mem.ChiPsiExist.exists_chiPsi D.R D.host
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.DeltaZero.delta_exists D.R D.host _ D.host.pde_prime D.host.pde_mod.1 h₁
  obtain ⟨d', hd'⟩ := GlobalTheory.Mem.DeltaZero.delta_exists D.R D.host _ D.host.pde'_prime D.host.pde_mod.2 h₂
  exact ⟨⟨P, W, mu, eta, chi, d, d', hmu, heta, hchi, hd, hd'⟩, rfl⟩

/- English proof (translation)
Rewrite using `[conjPl_iff_smul]`. Prove the components needed by the constructor for the conclusion. Introduce `hc`. Establish `hle : D.host.conj • w.asIdeal ≤ w'.asIdeal`. Introduce `y hy`.

Rewrite `hy` using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Take `⟨z, hz, hzv⟩` from `hc _ hy`. Establish `e : z = y` using `RingOfIntegers.ext ((hzv.trans (bridge_star_holds D.R D.host _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))`. Conclude with `e ▸ hz`. Take `⟨v, hv, -⟩` from `existsUnique_conjPl D.host.conj.toRingEquiv w`.

Establish `hv'` using `(conjPl_iff_smul D.host.conj w v).1 hv`. Establish `hvw : v = w'` using `HeightOneSpectrum.ext (v.isMaximal.eq_of_le w'.isPrime.ne_top (hv' ▸ hle))`. Conclude with `hvw ▸ hv'`. Introduce `h c hc`. Conclude with `⟨D.host.conj • c, h ▸ Ideal.smul_mem_pointwise_smul _ _ _ hc, (bridge_star_holds D.R D.host _).symm⟩`.
-/
theorem isConjPl_iff_conjPl {w w' : HeightOneSpectrum (𝓞 D.host.E)} :
    Lev.IsConjPl w w' ↔ ConjPl D.host.conj.toRingEquiv w w' := by
  rw [conjPl_iff_smul]
  constructor
  · intro hc
    have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
      intro y hy
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
      obtain ⟨z, hz, hzv⟩ := hc _ hy
      have e : z = y := RingOfIntegers.ext
        ((hzv.trans (bridge_star_holds D.R D.host _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
      exact e ▸ hz
    obtain ⟨v, hv, -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv w
    have hv' := (conjPl_iff_smul D.host.conj w v).1 hv
    have hvw : v = w' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le w'.isPrime.ne_top (hv' ▸ hle))
    exact hvw ▸ hv'
  · intro h c hc
    exact ⟨D.host.conj • c, h ▸ Ideal.smul_mem_pointwise_smul _ _ _ hc, (bridge_star_holds D.R D.host _).symm⟩

/- English proof (translation)
Simplify using `[aboveF]`.
-/
theorem mem_aboveK {P : HeightOneSpectrum (𝓞 D.host.K)} {w : HeightOneSpectrum (𝓞 D.host.E)} :
    w ∈ aboveF (L := D.host.E) D.host.K P ↔ w.under (𝓞 D.host.K) = P := by
  simp [aboveF]

/- English proof (translation)
Substitute `h` using the available equality. Establish `h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((p : ℕ) : 𝓞 D.host.K) ∈ w.asIdeal` using `hP`. Rewrite `h2` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem overP_of_under {p : ℕ} {P : HeightOneSpectrum (𝓞 D.host.K)} (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.K) = P) : OverP D.host p w := by
  subst h
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((p : ℕ) : 𝓞 D.host.K) ∈ w.asIdeal := hP
  rwa [map_natCast] at h2

/- English proof (translation)
Use `P.isPrime` as an intermediate fact. Take `⟨⟨W, hW, hWv⟩⟩` from `(inferInstance : Nonempty (P.asIdeal.primesOver (𝓞 D.host.E)))`. Conclude with `⟨⟨W, hW, Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot W⟩, mem_aboveK.2 (HeightOneSpectrum.ext hWv.over.symm)⟩`.
-/
theorem aboveK_nonempty (P : HeightOneSpectrum (𝓞 D.host.K)) : (aboveF (L := D.host.E) D.host.K P).Nonempty := by
  have := P.isPrime
  obtain ⟨⟨W, hW, hWv⟩⟩ := (inferInstance : Nonempty (P.asIdeal.primesOver (𝓞 D.host.E)))
  exact ⟨⟨W, hW, Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot W⟩, mem_aboveK.2 (HeightOneSpectrum.ext hWv.over.symm)⟩

section One

variable {p : ℕ} (hp : p.Prime) (hs : SplitsC D.host.E p) {P : HeightOneSpectrum (𝓞 D.host.K)}
  (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal)
include hp hs hP

/- English proof (translation)
Introduce `w hw`. Take `⟨h1, h2, -, h4⟩` from `splitsC_main D.R D.host p hp hs w (overP_of_under hP (mem_aboveK.1 hw))`. Use `⟨⟨p, hp, ?_, h2, hg⟩, fun w' hw' hc => ?_⟩` and prove the remaining obligations. Rewrite using `[← h1, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `(h4 P hP w' (isConjPl_iff_conjPl.1 hc)).2.1 (mem_aboveK.1 hw) (mem_aboveK.1 hw')`.
-/
theorem isTwistPlaces_aboveK (hg : ∀ i, p ≠ D.host.g i) : Lev.IsTwistPlaces D.host.g (aboveF (L := D.host.E) D.host.K P) := by
  intro w hw
  obtain ⟨h1, h2, -, h4⟩ := splitsC_main D.R D.host p hp hs w (overP_of_under hP (mem_aboveK.1 hw))
  refine ⟨⟨p, hp, ?_, h2, hg⟩, fun w' hw' hc => ?_⟩
  · rw [← h1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · exact (h4 P hP w' (isConjPl_iff_conjPl.1 hc)).2.1 (mem_aboveK.1 hw) (mem_aboveK.1 hw')

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hw`. Distinguish the cases in `h : w.under (𝓞 D.host.K) = P`. Conclude with `Or.inl (mem_aboveK.2 h)`. Take `⟨w', hw', -⟩` from `existsUnique_conjPl D.host.conj.toRingEquiv.symm w`.

Establish `hc : ConjPl D.host.conj.toRingEquiv w' w` using `fun x => by`. Use `hw' (D.host.conj.toRingEquiv x)` as an intermediate fact. Rewrite `this` using `[RingEquiv.symm_apply_apply]`. Conclude with `this.symm`. Establish `ho : OverP D.host p w'` using `((conjPl_iff_mem _ w' w).1 hc _ _ (by simp)).2 hw`.

Conclude with `Or.inr ⟨w', mem_aboveK.2 (((splitsC_main D.R D.host p hp hs w' ho).2.2.2 P hP w hc).2.2 h), isConjPl_iff_conjPl.2 hc⟩`. Introduce and unpack `(h | ⟨w', h, hc⟩)`. Conclude with `overP_of_under hP (mem_aboveK.1 h)`. Conclude with `((splitsC_main D.R D.host p hp hs w' (overP_of_under hP (mem_aboveK.1 h))).2.2.2 P hP w (isConjPl_iff_conjPl.1 hc)).1`.
-/
theorem overP_iff (w : HeightOneSpectrum (𝓞 D.host.E)) : OverP D.host p w ↔
    w ∈ aboveF (L := D.host.E) D.host.K P ∨ ∃ w' ∈ aboveF (L := D.host.E) D.host.K P, Lev.IsConjPl w' w := by
  constructor
  · intro hw
    by_cases h : w.under (𝓞 D.host.K) = P
    · exact Or.inl (mem_aboveK.2 h)
    · obtain ⟨w', hw', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv.symm w
      have hc : ConjPl D.host.conj.toRingEquiv w' w := fun x => by
        have := hw' (D.host.conj.toRingEquiv x)
        rw [RingEquiv.symm_apply_apply] at this
        exact this.symm
      have ho : OverP D.host p w' := ((conjPl_iff_mem _ w' w).1 hc _ _ (by simp)).2 hw
      exact Or.inr ⟨w', mem_aboveK.2 (((splitsC_main D.R D.host p hp hs w' ho).2.2.2 P hP w hc).2.2 h),
        isConjPl_iff_conjPl.2 hc⟩
  · rintro (h | ⟨w', h, hc⟩)
    · exact overP_of_under hP (mem_aboveK.1 h)
    · exact ((splitsC_main D.R D.host p hp hs w' (overP_of_under hP (mem_aboveK.1 h))).2.2.2 P hP w
        (isConjPl_iff_conjPl.1 hc)).1

end One

/- English proof (translation)
Use `⟨fun hn => by_contra fun hw => hn (h.unr w hw), fun hw hu => ?_⟩` and prove the remaining obligations. Use `(h.ine w hw 1).1 fun x hx => by rw [hu x hx, one_pow]` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem not_unrAt_iff {p : ℕ} {χ : HChar D.host.E} (h : IsDelta (H := D.host) p χ) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ¬ χ.UnrAt w ↔ OverP D.host p w := by
  refine ⟨fun hn => by_contra fun hw => hn (h.unr w hw), fun hw hu => ?_⟩
  have := (h.ine w hw 1).1 fun x hx => by rw [hu x hx, one_pow]
  omega

/- English proof (translation)
Establish `hpp : p.Prime`. Break down `hp with rfl | rfl` into its components or cases. Use `exacts [D.host.pde_prime, D.host.pde'_prime]`. Establish `hT : ∀ u, Nat.Coprime p (D.mem u).A.T` using `fun u => (Nat.coprime_primes hpp (D.mem u).A.T_prime).2 (by`. Break down `hp with rfl | rfl` into its components or cases.

Use `exacts [(D.T_ne_pde u).1.symm, (D.T_ne_pde u).2.symm])`. Establish `h3 : p ∉ D.host.small ∧ p ≠ D.host.q ∧ p ≠ D.host.d`. Unfold `Formalism.BasicNotions.Host.cls primeClass at hc`. Use `split_ifs at hc`. Conclude with `⟨‹_›, ‹_›, ‹_›⟩`.

Use `⟨GlobalTheory.CoverHalf.not_mem_of_coprime w.isPrime.ne_top ?_ hw, fun u => GlobalTheory.CoverHalf.not_mem_of_coprime w.isPrime.ne_top (hT u) hw⟩` and prove the remaining obligations. Rewrite using `[D.sp_T]`. Conclude with `(UpperTheory.Ram.coprime_condN D.host hpp h3.1 h3.2.1 h3.2.2).symm.mul_right (hT _)`.
-/
theorem off_special {p : ℕ} (hp : p = D.host.pde ∨ p = D.host.pde') (hc : D.host.cls p = PrimeClass.splitK)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : OverP D.host p w) :
    ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧
      ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  have hpp : p.Prime := by
    rcases hp with rfl | rfl
    exacts [D.host.pde_prime, D.host.pde'_prime]
  have hT : ∀ u, Nat.Coprime p (D.mem u).A.T := fun u => (Nat.coprime_primes hpp (D.mem u).A.T_prime).2 (by
    rcases hp with rfl | rfl
    exacts [(D.T_ne_pde u).1.symm, (D.T_ne_pde u).2.symm])
  have h3 : p ∉ D.host.small ∧ p ≠ D.host.q ∧ p ≠ D.host.d := by
    unfold Formalism.BasicNotions.Host.cls primeClass at hc
    split_ifs at hc
    exact ⟨‹_›, ‹_›, ‹_›⟩
  refine ⟨GlobalTheory.CoverHalf.not_mem_of_coprime w.isPrime.ne_top ?_ hw,
    fun u => GlobalTheory.CoverHalf.not_mem_of_coprime w.isPrime.ne_top (hT u) hw⟩
  rw [D.sp_T]
  exact (UpperTheory.Ram.coprime_condN D.host hpp h3.1 h3.2.1 h3.2.2).symm.mul_right (hT _)

/- English proof (translation)
Set `p : Bool → ℕ` to `fun b => cond b D.host.pde' D.host.pde`. Set `P : Bool → HeightOneSpectrum (𝓞 D.host.K)` to `fun b => cond b P₂ P₁`. Set `δ : Bool → HChar D.host.E` to `fun b => cond b C.del' C.del`. Establish `hpp : ∀ b, (p b).Prime` using `fun b => by cases b; exacts [D.host.pde_prime, D.host.pde'_prime]`. Establish `hs : ∀ b, SplitsC D.host.E (p b)` using `fun b => by cases b; exacts [h₁, h₂]`.

Establish `hP : ∀ b, ((p b : ℕ) : 𝓞 D.host.K) ∈ (P b).asIdeal` using `fun b => by cases b; exacts [hP₁, hP₂]`. Establish `hδ : ∀ b, IsDelta (H` using `D.host) (p b) (δ b) := fun b => by cases b; exacts [C.isDel, C.isDel']`. Establish `hown : ∀ b, p b = D.host.pde ∨ p b = D.host.pde'` using `fun b => by cases b; exacts [Or.inl rfl, Or.inr rfl]`. Establish `hc : ∀ b, D.host.cls (p b) = PrimeClass.splitK` using `fun b => by cases b; exacts [c₁, c₂]`. Establish `hg : ∀ b i, p b ≠ D.host.g i` using `fun b i => by cases b; exacts [(D.host.pde_ne_g i).1, (D.host.pde_ne_g i).2]`.

Establish `hsame : ∀ b b' (w : HeightOneSpectrum (𝓞 D.host.E)), OverP D.host (p b) w → OverP D.host (p b') w → b = b'`. Introduce `b b' w h h'`. Assume the negation of the conclusion as `hne`. Use `GlobalTheory.CoverHalf.not_mem_of_coprime w.isPrime.ne_top ((Nat.coprime_primes (hpp b) (hpp b')).2 ?_) h h'` and prove the remaining obligations. Apply the tactic sequence `cases b <;> cases b'`.

Use `exacts [absurd rfl hne, D.host.pde_ne, D.host.pde_ne.symm, absurd rfl hne]`. Establish `hex : ∀ b, ∃ w, OverP D.host (p b) w` using `fun b =>`. Set `⟨w, hw⟩` to `aboveK_nonempty (P b)`. Use the proof step `⟨w, overP_of_under (hP b) (mem_aboveK.1 hw)⟩`. Establish `hone : ∀ w, (1 : HChar D.host.E).UnrAt w` using `fun _ _ _ => rfl`.

Take `⟨Lc, a1, a2, a3, -, a5⟩` from `GlobalTheory.LevelChoices.exists_levCh D C (Option Bool) none (fun t => t.elim 1 δ) (fun t => t.elim ∅ fun b => aboveF (L := D.host.E) D.host.K (P b)) (by`. Introduce and unpack `(_ | b) (_ | b') h`. Both sides reduce to the same expression. Take `⟨w, hw⟩` from `hex b'`. Conclude with `absurd ((show (1 : HChar D.host.E) = δ b' from h) ▸ hone w) ((not_unrAt_iff (hδ b') w).2 hw)`.

Take `⟨w, hw⟩` from `hex b`. Conclude with `absurd ((show δ b = (1 : HChar D.host.E) from h) ▸ hone w) ((not_unrAt_iff (hδ b) w).2 hw)`. Take `⟨w, hw⟩` from `hex b`. Establish `h1` using `(not_unrAt_iff (hδ b) w).2 hw`. Rewrite `h1` using `[show δ b = δ b' from h]`.

Rewrite using `[hsame b b' w hw ((not_unrAt_iff (hδ b') w).1 h1)])`. Both sides reduce to the same expression. Use the proof step `(by`. Introduce and unpack `(_ | b)`. Use `exacts [⟨1, one_pos, one_pow 1⟩, (hδ b).fin])`.

Use the proof step `(by`. Introduce and unpack `(_ | b)`. Use `exacts [(isPsi_one (H := D.host) 2).triv, (hδ b).triv])`. Use the proof step `(by`. Introduce and unpack `(_ | b)`.

Use `exacts [fun _ _ _ _ => rfl, (hδ b).tame])`. Use the proof step `(by`. Introduce and unpack `(_ | b)`. Use `exacts [fun _ h => absurd h (Finset.notMem_empty _), isTwistPlaces_aboveK (hpp b) (hs b) (hP b) (hg b)])`. Use the proof step `(by`.

Introduce and unpack `(_ | b) w hw`. Use `exacts [absurd hw (Finset.notMem_empty _), off_special (hown b) (hc b) (overP_of_under (hP b) (mem_aboveK.1 hw))])`. Use the proof step `(by`. Introduce `q hq`. Choose the witnesses or unpack the hypotheses as in `⟨b, rfl⟩ : ∃ b, q = p b := by`.

Break down `hq with h | h` into its components or cases. Use `exacts [⟨false, h⟩, ⟨true, h⟩]`. Use `⟨P b, ?_⟩` and prove the remaining obligations. Introduce and unpack `(_ | b') w hw h`. Conclude with `absurd hw (Finset.notMem_empty _)`.

Rewrite using `[hsame b b' w h (overP_of_under (hP b') (mem_aboveK.1 hw))]`. Conclude with `mem_aboveK.1 hw)`. Use the proof step `(by`. Introduce and unpack `(_ | b) w`. Conclude with `iff_of_false (fun h => h (hone w)) (by simp)`.

Conclude with `(not_unrAt_iff (hδ b) w).trans (overP_iff (hpp b) (hs b) (hP b) w))`. Conclude with `⟨Lc, a1, a5, by rw [a2]; rfl, by rw [a2]; rfl, by rw [a3]; rfl, by rw [a3]; rfl⟩`.
-/
theorem exists_levCh_twisted (C : CharFrame D) (h₁ : SplitsC D.host.E D.host.pde) (h₂ : SplitsC D.host.E D.host.pde')
    (c₁ : D.host.cls D.host.pde = PrimeClass.splitK) (c₂ : D.host.cls D.host.pde' = PrimeClass.splitK)
    (P₁ P₂ : HeightOneSpectrum (𝓞 D.host.K)) (hP₁ : ((D.host.pde : ℕ) : 𝓞 D.host.K) ∈ P₁.asIdeal)
    (hP₂ : ((D.host.pde' : ℕ) : 𝓞 D.host.K) ∈ P₂.asIdeal) :
    ∃ Lc : LevCh D (Option Bool), Lc.C = C ∧ Lc.Is none ∧ Lc.xiH (some false) = C.del ∧ Lc.xiH (some true) = C.del' ∧
      Lc.Q (some false) = aboveF (L := D.host.E) D.host.K P₁ ∧ Lc.Q (some true) = aboveF (L := D.host.E) D.host.K P₂ := by
  let p : Bool → ℕ := fun b => cond b D.host.pde' D.host.pde
  let P : Bool → HeightOneSpectrum (𝓞 D.host.K) := fun b => cond b P₂ P₁
  let δ : Bool → HChar D.host.E := fun b => cond b C.del' C.del
  have hpp : ∀ b, (p b).Prime := fun b => by cases b; exacts [D.host.pde_prime, D.host.pde'_prime]
  have hs : ∀ b, SplitsC D.host.E (p b) := fun b => by cases b; exacts [h₁, h₂]
  have hP : ∀ b, ((p b : ℕ) : 𝓞 D.host.K) ∈ (P b).asIdeal := fun b => by cases b; exacts [hP₁, hP₂]
  have hδ : ∀ b, IsDelta (H := D.host) (p b) (δ b) := fun b => by cases b; exacts [C.isDel, C.isDel']
  have hown : ∀ b, p b = D.host.pde ∨ p b = D.host.pde' := fun b => by cases b; exacts [Or.inl rfl, Or.inr rfl]
  have hc : ∀ b, D.host.cls (p b) = PrimeClass.splitK := fun b => by cases b; exacts [c₁, c₂]
  have hg : ∀ b i, p b ≠ D.host.g i := fun b i => by cases b; exacts [(D.host.pde_ne_g i).1, (D.host.pde_ne_g i).2]
  have hsame : ∀ b b' (w : HeightOneSpectrum (𝓞 D.host.E)), OverP D.host (p b) w → OverP D.host (p b') w → b = b' := by
    intro b b' w h h'
    by_contra hne
    refine GlobalTheory.CoverHalf.not_mem_of_coprime w.isPrime.ne_top ((Nat.coprime_primes (hpp b) (hpp b')).2 ?_) h h'
    cases b <;> cases b'
    exacts [absurd rfl hne, D.host.pde_ne, D.host.pde_ne.symm, absurd rfl hne]
  have hex : ∀ b, ∃ w, OverP D.host (p b) w := fun b =>
    let ⟨w, hw⟩ := aboveK_nonempty (P b)
    ⟨w, overP_of_under (hP b) (mem_aboveK.1 hw)⟩
  have hone : ∀ w, (1 : HChar D.host.E).UnrAt w := fun _ _ _ => rfl
  obtain ⟨Lc, a1, a2, a3, -, a5⟩ := GlobalTheory.LevelChoices.exists_levCh D C (Option Bool) none (fun t => t.elim 1 δ)
    (fun t => t.elim ∅ fun b => aboveF (L := D.host.E) D.host.K (P b))
    (by
      rintro (_ | b) (_ | b') h
      · rfl
      · obtain ⟨w, hw⟩ := hex b'
        exact absurd ((show (1 : HChar D.host.E) = δ b' from h) ▸ hone w) ((not_unrAt_iff (hδ b') w).2 hw)
      · obtain ⟨w, hw⟩ := hex b
        exact absurd ((show δ b = (1 : HChar D.host.E) from h) ▸ hone w) ((not_unrAt_iff (hδ b) w).2 hw)
      · obtain ⟨w, hw⟩ := hex b
        have h1 := (not_unrAt_iff (hδ b) w).2 hw
        rw [show δ b = δ b' from h] at h1
        rw [hsame b b' w hw ((not_unrAt_iff (hδ b') w).1 h1)])
    rfl
    (by
      rintro (_ | b)
      exacts [⟨1, one_pos, one_pow 1⟩, (hδ b).fin])
    (by
      rintro (_ | b)
      exacts [(isPsi_one (H := D.host) 2).triv, (hδ b).triv])
    (by
      rintro (_ | b)
      exacts [fun _ _ _ _ => rfl, (hδ b).tame])
    (by
      rintro (_ | b)
      exacts [fun _ h => absurd h (Finset.notMem_empty _), isTwistPlaces_aboveK (hpp b) (hs b) (hP b) (hg b)])
    (by
      rintro (_ | b) w hw
      exacts [absurd hw (Finset.notMem_empty _), off_special (hown b) (hc b) (overP_of_under (hP b) (mem_aboveK.1 hw))])
    (by
      intro q hq
      obtain ⟨b, rfl⟩ : ∃ b, q = p b := by
        rcases hq with h | h
        exacts [⟨false, h⟩, ⟨true, h⟩]
      refine ⟨P b, ?_⟩
      rintro (_ | b') w hw h
      · exact absurd hw (Finset.notMem_empty _)
      · rw [hsame b b' w h (overP_of_under (hP b') (mem_aboveK.1 hw))]
        exact mem_aboveK.1 hw)
    (by
      rintro (_ | b) w
      · exact iff_of_false (fun h => h (hone w)) (by simp)
      · exact (not_unrAt_iff (hδ b) w).trans (overP_iff (hpp b) (hs b) (hP b) w))
  exact ⟨Lc, a1, a5, by rw [a2]; rfl, by rw [a2]; rfl, by rw [a3]; rfl, by rw [a3]; rfl⟩

end GlobalTheory.BigOn.Inhab

end

import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ExistsBaseRingOfConjugationFixedTensor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharTameAtOfFactorsThroughResidue
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatMMemOfLeHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TameConjPlace

open GlobalTheory.ExportSeries Formalism.L2.JoinChr

section Density

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hone : ∀ k : Eˣ, PP.valuation E ((k : E) - 1) < 1 → H.locK PP k = 1`. Introduce `k hk`. Establish `hv1 : PP.valuation E (k : E) = 1`. Establish `e : (k : E) = 1 + ((k : E) - 1)` using `by ring`. Establish `h1 : PP.valuation E ((k : E) - 1) < PP.valuation E 1` using `by rwa [map_one]`.

Rewrite using `[e]`. Use `first`. Consider the case `rw [Valuation.map_add_eq_of_lt_right _ h1, map_one]`. Consider the case `rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]`. Consider the case `rw [add_comm, Valuation.map_add_eq_of_lt_right _ h1, map_one]`.

Consider the case `rw [add_comm, Valuation.map_add_eq_of_lt_left _ h1, map_one]`. Take `⟨a, s, h⟩` from `PP.exists_primeCompl_mul_eq_of_integer (k : E) hv1.le`. Establish `hs : (s : 𝓞 E) ∉ PP.asIdeal` using `s.2`. Establish `hsv` using `GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem PP _ hs`. Establish `hav : PP.valuation E (algebraMap (𝓞 E) E a) = 1`.

Rewrite using `[← h, map_mul, hv1, hsv, one_mul]`. Establish `ha : a ∉ PP.asIdeal`. Introduce `hm`. Establish `hlt : PP.valuation E (algebraMap (𝓞 E) E a) < 1` using `(PP.valuation_lt_one_iff_mem (K := E) a).mpr hm`. Conclude with `absurd hav (ne_of_lt hlt)`.

Establish `hs0 : algebraMap (𝓞 E) E s ≠ 0` using `fun h0 => by`. Rewrite `hsv` using `[h0, map_zero]`. Conclude with `zero_ne_one hsv`. Establish `ha0 : algebraMap (𝓞 E) E a ≠ 0` using `fun h0 => by`. Rewrite `hav` using `[h0, map_zero]`.

Conclude with `zero_ne_one hav`. Establish `hdiff : a - (s : 𝓞 E) ∈ PP.asIdeal`. Apply `(PP.valuation_lt_one_iff_mem (K := E) _).mp` to reduce the goal to its premises. Use `show PP.valuation E (algebraMap (𝓞 E) E (a - (s : 𝓞 E))) < 1`. Rewrite using `[map_sub, ← h, ← sub_one_mul, map_mul, hsv, mul_one]`.

Conclude with `hk`. Set `ka : Eˣ` to `Units.mk0 _ ha0`. Set `ks : Eˣ` to `Units.mk0 _ hs0`. Establish `e1 : H.locK PP ka = H.locK PP ks` using `hc a (s : 𝓞 E) ka ks rfl rfl ha hdiff`. Establish `hk' : k = ka * ks⁻¹`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ka, ks]`. Rewrite using `[← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]`. Rewrite using `[hk', map_mul, map_inv, e1, mul_inv_cancel]`. Unfold `Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe`.

Introduce `x _ hx1`. Assume the negation of the conclusion as `hne`. Establish `hcont : Continuous (H.loc PP)` using `H.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele PP)`. Establish `hW : IsOpen {y : (PP.adicCompletion E)ˣ | H.loc PP y ≠ 1}` using `isOpen_ne_fun hcont continuous_const`. Take `⟨T, hT, hTe⟩` from `Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hW`.

Establish `hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1`. Rewrite using `[← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)`. Establish `hxT : (x : PP.adicCompletion E) ∈ T ∩ {z | Valued.v (z - 1) < 1}`. Use `⟨?_, lt_of_le_of_lt hx1 hlt⟩` and prove the remaining obligations. Establish `: x ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion E)ˣ)` using `by rw [hTe]; exact hne`.

Conclude with `this`. Establish `hU : IsOpen (T ∩ {z : PP.adicCompletion E | Valued.v (z - 1) < 1})` using `hT.inter ((GlobalTheory.ChainOnto.TameRes.isOpen_ltOne PP).preimage (continuous_sub_right 1))`. Take `⟨k, hk⟩` from `(HeightOneSpectrum.denseRange_algebraMap E PP).exists_mem_open hU ⟨_, hxT⟩`. Establish `hk1 : PP.valuation E (k - 1) < 1`. Rewrite using `[← GlobalTheory.ChainOnto.TameRes.val_alg, map_sub, map_one]`.

Conclude with `hk.2`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hk1`. Establish `hloc` using `hone (Units.mk0 k hk0) hk1`.

Establish `hmem : Formalism.L2.Host.atFin PP (Units.mk0 k hk0) ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion E)ˣ)` using `hk.1`. Rewrite `hmem` using `[hTe]`. Conclude with `hmem hloc`.
-/
theorem tameAt_of_congr (H : Formalism.L2.Host.HChar E) (PP : HeightOneSpectrum (𝓞 E))
    (hc : ∀ (a b : 𝓞 E) (ka kb : Eˣ), (ka : E) = (a : E) → (kb : E) = (b : E) → a ∉ PP.asIdeal →
      a - b ∈ PP.asIdeal → H.locK PP ka = H.locK PP kb) : H.TameAt PP := by
  have hone : ∀ k : Eˣ, PP.valuation E ((k : E) - 1) < 1 → H.locK PP k = 1 := by
    intro k hk
    have hv1 : PP.valuation E (k : E) = 1 := by
      have e : (k : E) = 1 + ((k : E) - 1) := by ring
      have h1 : PP.valuation E ((k : E) - 1) < PP.valuation E 1 := by rwa [map_one]
      rw [e]
      first
        | rw [Valuation.map_add_eq_of_lt_right _ h1, map_one]
        | rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]
        | rw [add_comm, Valuation.map_add_eq_of_lt_right _ h1, map_one]
        | rw [add_comm, Valuation.map_add_eq_of_lt_left _ h1, map_one]
    obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer (k : E) hv1.le
    have hs : (s : 𝓞 E) ∉ PP.asIdeal := s.2
    have hsv := GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem PP _ hs
    have hav : PP.valuation E (algebraMap (𝓞 E) E a) = 1 := by
      rw [← h, map_mul, hv1, hsv, one_mul]
    have ha : a ∉ PP.asIdeal := by
      intro hm
      have hlt : PP.valuation E (algebraMap (𝓞 E) E a) < 1 :=
        (PP.valuation_lt_one_iff_mem (K := E) a).mpr hm
      exact absurd hav (ne_of_lt hlt)
    have hs0 : algebraMap (𝓞 E) E s ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hsv; exact zero_ne_one hsv
    have ha0 : algebraMap (𝓞 E) E a ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hav; exact zero_ne_one hav
    have hdiff : a - (s : 𝓞 E) ∈ PP.asIdeal := by
      apply (PP.valuation_lt_one_iff_mem (K := E) _).mp
      show PP.valuation E (algebraMap (𝓞 E) E (a - (s : 𝓞 E))) < 1
      rw [map_sub, ← h, ← sub_one_mul, map_mul, hsv, mul_one]
      exact hk
    let ka : Eˣ := Units.mk0 _ ha0
    let ks : Eˣ := Units.mk0 _ hs0
    have e1 : H.locK PP ka = H.locK PP ks := hc a (s : 𝓞 E) ka ks rfl rfl ha hdiff
    have hk' : k = ka * ks⁻¹ := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ka, ks]
      rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
    rw [hk', map_mul, map_inv, e1, mul_inv_cancel]
  unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
  intro x _ hx1
  by_contra hne
  have hcont : Continuous (H.loc PP) := H.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele PP)
  have hW : IsOpen {y : (PP.adicCompletion E)ˣ | H.loc PP y ≠ 1} := isOpen_ne_fun hcont continuous_const
  obtain ⟨T, hT, hTe⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hW
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hxT : (x : PP.adicCompletion E) ∈ T ∩ {z | Valued.v (z - 1) < 1} := by
    refine ⟨?_, lt_of_le_of_lt hx1 hlt⟩
    have : x ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion E)ˣ) := by rw [hTe]; exact hne
    exact this
  have hU : IsOpen (T ∩ {z : PP.adicCompletion E | Valued.v (z - 1) < 1}) :=
    hT.inter ((GlobalTheory.ChainOnto.TameRes.isOpen_ltOne PP).preimage (continuous_sub_right 1))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap E PP).exists_mem_open hU ⟨_, hxT⟩
  have hk1 : PP.valuation E (k - 1) < 1 := by
    rw [← GlobalTheory.ChainOnto.TameRes.val_alg, map_sub, map_one]; exact hk.2
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk1
  have hloc := hone (Units.mk0 k hk0) hk1
  have hmem : Formalism.L2.Host.atFin PP (Units.mk0 k hk0) ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion E)ˣ) := hk.1
  rw [hTe] at hmem
  exact hmem hloc

end Density

variable {D : D7}

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `he` using `hδ.split.isIdemAt hPP`. Establish `hee : idemAt PP * idemAt PP = idemAt PP` using `he.1.1`. Take `⟨hi, h1⟩` from `GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he`. Use `haveI : PP.asIdeal.IsMaximal := PP.isMaximal`. Establish `hma : (Ideal.Quotient.mk PP.asIdeal a : kP PP) ≠ 0`.

Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `ha`. Set `u : (kP PP)ˣ` to `Units.mk0 _ hma`. Establish `key : ∀ (c : 𝓞 D.host.E) (z : (AE D)ˣ), (z : AE D) = 1 + idemAt PP * (incA D (c : D.host.E) - 1) → Ideal.Quotient.mk PP.asIdeal c = (u : kP PP) → δ.chi z = δ.res PP u`. Introduce `c z hz hcu`.

Establish `hv : Formalism.IndefR.Datum.toEAf D (z : AE D) = ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E c - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D)`. Establish `hb : Formalism.IndefR.Datum.toEAf D (incA D (c : D.host.E)) = ((oToS D.host.F D.host.E c : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D)` using `rfl`. Rewrite using `[hz, GlobalTheory.ConjTwist.map_loc, hb]`. Both sides reduce to the same expression. Establish `hzi : Formalism.IndefR.Datum.toEAf D (z : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`.

Rewrite using `[hv]`. Conclude with `Subtype.property _`. Use `hδ.res PP hPP z ?_ hzi u ?_` and prove the remaining obligations. Rewrite using `[hz]`. Take the linear combination `(1 - incA D (c : D.host.E)) * hee`.

Establish `e2 : (⟨_, hzi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E c - 1)` using `Subtype.ext hv`. Rewrite using `[e2, GlobalTheory.ConjTwist.map_loc, h1, resS_oToS, hcu]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : Ideal.Quotient.mk PP.asIdeal b = (u : kP PP)` using `by show Ideal.Quotient.mk PP.asIdeal b = Ideal.Quotient.mk PP.asIdeal a`. Conclude with `(Ideal.Quotient.eq.mpr hab).symm`.

Rewrite using `[key a x hx rfl, key b y hy hb]`.
-/
theorem chi_locE_congr (δ : Twist D Circle) (hδ : δ.Good) {PP : Pl D.host.E} (hPP : PP ∈ δ.Q) (a b : 𝓞 D.host.E)
    (ha : a ∉ PP.asIdeal) (hab : a - b ∈ PP.asIdeal) (x y : (AE D)ˣ)
    (hx : (x : AE D) = 1 + idemAt PP * (incA D (a : D.host.E) - 1))
    (hy : (y : AE D) = 1 + idemAt PP * (incA D (b : D.host.E) - 1)) : δ.chi x = δ.chi y := by
  have he := hδ.split.isIdemAt hPP
  have hee : idemAt PP * idemAt PP = idemAt PP := he.1.1
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP he
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have hma : (Ideal.Quotient.mk PP.asIdeal a : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact ha
  let u : (kP PP)ˣ := Units.mk0 _ hma
  have key : ∀ (c : 𝓞 D.host.E) (z : (AE D)ˣ), (z : AE D) = 1 + idemAt PP * (incA D (c : D.host.E) - 1) →
      Ideal.Quotient.mk PP.asIdeal c = (u : kP PP) → δ.chi z = δ.res PP u := by
    intro c z hz hcu
    have hv : Formalism.IndefR.Datum.toEAf D (z : AE D) =
        ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E c - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) := by
      have hb : Formalism.IndefR.Datum.toEAf D (incA D (c : D.host.E)) =
          ((oToS D.host.F D.host.E c : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D) := rfl
      rw [hz, GlobalTheory.ConjTwist.map_loc, hb]
      rfl
    have hzi : Formalism.IndefR.Datum.toEAf D (z : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [hv]; exact Subtype.property _
    refine hδ.res PP hPP z ?_ hzi u ?_
    · rw [hz]; linear_combination (1 - incA D (c : D.host.E)) * hee
    · have e2 : (⟨_, hzi⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E c - 1) :=
        Subtype.ext hv
      rw [e2, GlobalTheory.ConjTwist.map_loc, h1, resS_oToS, hcu]
      ring
  have hb : Ideal.Quotient.mk PP.asIdeal b = (u : kP PP) := by
    show Ideal.Quotient.mk PP.asIdeal b = Ideal.Quotient.mk PP.asIdeal a
    exact (Ideal.Quotient.eq.mpr hab).symm
  rw [key a x hx rfl, key b y hy hb]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `he'` using `hδ.split.isIdemAt hP'`. Establish `he : Formalism.L2.NTheta.IsIdemAt (cA D (idemAt P')) P` using `(GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.2 P' _ _ he' hPP`. Establish `hee : cA D (idemAt P') * cA D (idemAt P') = cA D (idemAt P')` using `he.1.1`. Establish `hcc : cA D (cA D (idemAt P')) = idemAt P'` using `GlobalTheory.MovedIdem.cA_cA _`. Establish `step : ∀ (k : D.host.Eˣ) (c : 𝓞 D.host.E), (k : D.host.E) = star (c : D.host.E) → ∀ z : (AE D)ˣ, (z : AE D) = 1 + idemAt P' * (incA D (c : D.host.E) - 1) → ((χ.locK P k : ℂˣ) : ℂ) = ((δ.chi z : Circle) : ℂ)⁻¹`.

Introduce `k c hk z hz`. Set `x` to `locU hee k`. Establish `h1 : ((δ.chi x : Circle) : ℂ) = ((χ.locK P k : ℂˣ) : ℂ)` using `hc.2 P _ (GlobalTheory.HeckeDetChar.isPlIdem he) k x (locU_val hee k)`. Establish `hxz : cA D (x : AE D) = (z : AE D)`. Rewrite using `[locU_val, locE, hz, RingHom.map_add, RingHom.map_one, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hcc, GlobalTheory.MovedIdem.cA_incA, hk, star_star]`.

Establish `hfix : cA D ((x * z : (AE D)ˣ) : AE D) = ((x * z : (AE D)ˣ) : AE D)`. Rewrite using `[Units.val_mul, RingHom.map_mul, hxz, ← hxz, GlobalTheory.MovedIdem.cA_cA, mul_comm]`. Take `⟨α, hα⟩` from `(GlobalTheory.DetRootRows.fixed_iff_idF (x * z)).1 hfix`. Establish `h2 : δ.chi x * δ.chi z = 1` using `by rw [← map_mul, ← hα, hδ.real]`. Rewrite using `[← h1]`.

Establish `h3 : ((δ.chi x : Circle) : ℂ) * ((δ.chi z : Circle) : ℂ) = 1`. Rewrite using `[← Circle.coe_mul, h2, Circle.coe_one]`. Conclude with `eq_inv_of_mul_eq_one_left h3`. Establish `hsym` using `GlobalTheory.ParahoricLift.isConjPl_symm hPP`. Establish `hca : Formalism.L2.Col.cO _ a ∉ P'.asIdeal`.

Introduce `hm`. Take `⟨c', hc', hc'e⟩` from `hPP _ hm`. Apply `ha` to reduce the goal to its premises. Establish `: c' = a` using `RingOfIntegers.ext (by rw [hc'e]; exact star_star (a : D.host.E))`. Rewrite using `[← this]` and apply the resulting hypothesis.

Establish `hcab : Formalism.L2.Col.cO _ a - Formalism.L2.Col.cO _ b ∈ P'.asIdeal`. Take `⟨c', hc', hc'e⟩` from `hsym _ hab`. Establish `: c' = Formalism.L2.Col.cO _ a - Formalism.L2.Col.cO _ b` using `RingOfIntegers.ext (by`. Rewrite using `[hc'e]`. Use `show star (((a - b : 𝓞 D.host.E)) : D.host.E) = star (a : D.host.E) - star (b : D.host.E)`.

Use `push_cast`. Conclude with `star_sub _ _)`. Rewrite using `[← this]` and apply the resulting hypothesis. Establish `hcne : ∀ c : 𝓞 D.host.E, c ∉ P'.asIdeal → (c : D.host.E) ≠ 0` using `fun c hc0 h0 => hc0 (by rw [show c = 0 from RingOfIntegers.ext h0]; exact zero_mem _)`. Establish `hcb : Formalism.L2.Col.cO _ b ∉ P'.asIdeal` using `fun hm => hca (by`.

Use `add_mem hcab hm` as an intermediate fact. Rewrite using `[sub_add_cancel] at this)` and apply the resulting hypothesis. Establish `he'e : idemAt P' * idemAt P' = idemAt P'` using `he'.1.1`. Set `za` to `locU he'e (Units.mk0 _ (hcne _ hca))`. Set `zb` to `locU he'e (Units.mk0 _ (hcne _ hcb))`.

Establish `hza` using `step ka (Formalism.L2.Col.cO _ a) (by rw [hka]; exact (star_star (a : D.host.E)).symm) za (locU_val he'e _)`. Establish `hzb` using `step kb (Formalism.L2.Col.cO _ b) (by rw [hkb]; exact (star_star (b : D.host.E)).symm) zb (locU_val he'e _)`. Establish `heq` using `chi_locE_congr δ hδ hP' _ _ hca hcab za zb (locU_val he'e _) (locU_val he'e _)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hza, hzb, heq]`.
-/
theorem locK_congr_conj (δ : Twist D Circle) (hδ : δ.Good) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq δ.chi χ)
    {P' : Pl D.host.E} (hP' : P' ∈ δ.Q) {P : Pl D.host.E} (hPP : Formalism.IndefR.Lev.IsConjPl P' P)
    (a b : 𝓞 D.host.E) (ka kb : D.host.Eˣ) (hka : (ka : D.host.E) = (a : D.host.E)) (hkb : (kb : D.host.E) = (b : D.host.E))
    (ha : a ∉ P.asIdeal) (hab : a - b ∈ P.asIdeal) : χ.locK P ka = χ.locK P kb := by
  have he' := hδ.split.isIdemAt hP'
  have he : Formalism.L2.NTheta.IsIdemAt (cA D (idemAt P')) P :=
    (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.2 P' _ _ he' hPP
  have hee : cA D (idemAt P') * cA D (idemAt P') = cA D (idemAt P') := he.1.1
  have hcc : cA D (cA D (idemAt P')) = idemAt P' := GlobalTheory.MovedIdem.cA_cA _

  have step : ∀ (k : D.host.Eˣ) (c : 𝓞 D.host.E), (k : D.host.E) = star (c : D.host.E) →
      ∀ z : (AE D)ˣ, (z : AE D) = 1 + idemAt P' * (incA D (c : D.host.E) - 1) →
      ((χ.locK P k : ℂˣ) : ℂ) = ((δ.chi z : Circle) : ℂ)⁻¹ := by
    intro k c hk z hz
    let x := locU hee k
    have h1 : ((δ.chi x : Circle) : ℂ) = ((χ.locK P k : ℂˣ) : ℂ) :=
      hc.2 P _ (GlobalTheory.HeckeDetChar.isPlIdem he) k x (locU_val hee k)
    have hxz : cA D (x : AE D) = (z : AE D) := by
      rw [locU_val, locE, hz, RingHom.map_add, RingHom.map_one, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hcc,
        GlobalTheory.MovedIdem.cA_incA, hk, star_star]
    have hfix : cA D ((x * z : (AE D)ˣ) : AE D) = ((x * z : (AE D)ˣ) : AE D) := by
      rw [Units.val_mul, RingHom.map_mul, hxz, ← hxz, GlobalTheory.MovedIdem.cA_cA, mul_comm]
    obtain ⟨α, hα⟩ := (GlobalTheory.DetRootRows.fixed_iff_idF (x * z)).1 hfix
    have h2 : δ.chi x * δ.chi z = 1 := by rw [← map_mul, ← hα, hδ.real]
    rw [← h1]
    have h3 : ((δ.chi x : Circle) : ℂ) * ((δ.chi z : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, h2, Circle.coe_one]
    exact eq_inv_of_mul_eq_one_left h3
  have hsym := GlobalTheory.ParahoricLift.isConjPl_symm hPP

  have hca : Formalism.L2.Col.cO _ a ∉ P'.asIdeal := by
    intro hm
    obtain ⟨c', hc', hc'e⟩ := hPP _ hm
    apply ha
    have : c' = a := RingOfIntegers.ext (by rw [hc'e]; exact star_star (a : D.host.E))
    rwa [← this]
  have hcab : Formalism.L2.Col.cO _ a - Formalism.L2.Col.cO _ b ∈ P'.asIdeal := by
    obtain ⟨c', hc', hc'e⟩ := hsym _ hab
    have : c' = Formalism.L2.Col.cO _ a - Formalism.L2.Col.cO _ b := RingOfIntegers.ext (by
      rw [hc'e]
      show star (((a - b : 𝓞 D.host.E)) : D.host.E) = star (a : D.host.E) - star (b : D.host.E)
      push_cast
      exact star_sub _ _)
    rwa [← this]
  have hcne : ∀ c : 𝓞 D.host.E, c ∉ P'.asIdeal → (c : D.host.E) ≠ 0 := fun c hc0 h0 =>
    hc0 (by rw [show c = 0 from RingOfIntegers.ext h0]; exact zero_mem _)
  have hcb : Formalism.L2.Col.cO _ b ∉ P'.asIdeal := fun hm => hca (by
    have := add_mem hcab hm
    rwa [sub_add_cancel] at this)
  have he'e : idemAt P' * idemAt P' = idemAt P' := he'.1.1
  let za := locU he'e (Units.mk0 _ (hcne _ hca))
  let zb := locU he'e (Units.mk0 _ (hcne _ hcb))
  have hza := step ka (Formalism.L2.Col.cO _ a) (by rw [hka]; exact (star_star (a : D.host.E)).symm) za (locU_val he'e _)
  have hzb := step kb (Formalism.L2.Col.cO _ b) (by rw [hkb]; exact (star_star (b : D.host.E)).symm) zb (locU_val he'e _)
  have heq := chi_locE_congr δ hδ hP' _ _ hca hcab za zb (locU_val he'e _) (locU_val he'e _)
  apply Units.ext
  rw [hza, hzb, heq]

/- English proof (translation)
Introduce `D δ hδ χ hc P' hP' P hPP`. Conclude with `tameAt_of_congr χ P fun a b ka kb hka hkb ha hab => locK_congr_conj δ hδ χ hc hP' hPP a b ka kb hka hkb ha hab`.
-/
theorem tameAt_conj : ∀ (D : D7) (δ : GlobalTheory.ExportSeries.Twist D Circle), δ.Good → ∀ (χ : Formalism.L2.Host.HChar D.host.E),
    ChrEq δ.chi χ → ∀ P' ∈ δ.Q, ∀ P : Pl D.host.E, Formalism.IndefR.Lev.IsConjPl P' P → χ.TameAt P := by
  intro D δ hδ χ hc P' hP' P hPP
  exact tameAt_of_congr χ P fun a b ka kb hka hkb ha hab =>
    locK_congr_conj δ hδ χ hc hP' hPP a b ka kb hka hkb ha hab

end GlobalTheory.TameConjPlace

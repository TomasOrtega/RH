import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelope
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorDvdOfSaturatedIdealStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonSubOneDvdAinfCoeffZeroOfThetaVanishingStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.MuOfEps

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Apply `(frobeniusEquiv (OCb l) l).injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply, ← h]`. Both sides reduce to the same expression.
-/
theorem root_eq {ε δ : OCb l} (h : δ ^ l = ε) : δ = (frobeniusEquiv (OCb l) l).symm ε := by
  apply (frobeniusEquiv (OCb l) l).injective
  rw [RingEquiv.apply_symm_apply, ← h]
  rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `WittVector.constantCoeff (WittVector.teichmuller l x - 1) = x - 1`. Rewrite using `[map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`.
-/
theorem coeff_zero_muOf (x : OCb l) : (muOf x).coeff 0 = x - 1 := by
  change WittVector.constantCoeff (WittVector.teichmuller l x - 1) = x - 1
  rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', ih, muOf, muOf, map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, ← pow_mul, pow_succ]`.
-/
theorem frob_iterate_muOf (x : OCb l) (n : ℕ) :
    WittVector.frobenius^[n] (muOf x) = muOf (x ^ (l ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, muOf, muOf, map_sub, map_one,
      WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, ← pow_mul, pow_succ]

/- English proof (translation)
Rewrite using `[muOf, map_sub, map_one, WittVector.fontaineTheta_teichmuller]`.
-/
theorem theta_muOf (x : OCb l) : Per.θ l (muOf x) = x.untilt - 1 := by
  rw [muOf, map_sub, map_one, WittVector.fontaineTheta_teichmuller]

variable (l) in

def kerAll : Ideal (Ainf l) := ⨅ n : ℕ, RingHom.ker ((Per.θ l).comp (WittVector.frobenius ^ n))

/- English proof (translation)
Simplify using `only [kerAll, Ideal.mem_iInf, RingHom.mem_ker, RingHom.comp_apply, RingHom.coe_pow]`.
-/
theorem mem_kerAll (a : Ainf l) : a ∈ kerAll l ↔ ∀ n : ℕ, Per.θ l (WittVector.frobenius^[n] a) = 0 := by
  simp only [kerAll, Ideal.mem_iInf, RingHom.mem_ker, RingHom.comp_apply, RingHom.coe_pow]

/- English proof (translation)
Rewrite using `[mem_kerAll]`. Introduce `n`. Rewrite using `[frob_iterate_muOf, theta_muOf, map_pow, hx, one_pow, sub_self]`.
-/
theorem muOf_mem_kerAll {x : OCb l} (hx : x.untilt = 1) : muOf x ∈ kerAll l := by
  rw [mem_kerAll]
  intro n
  rw [frob_iterate_muOf, theta_muOf, map_pow, hx, one_pow, sub_self]

/- English proof (translation)
Rewrite `h`, the goal using `[mem_kerAll]`. Introduce `n`. Establish `h1` using `h n`. Rewrite `h1` using `[← RingHom.coe_pow, map_mul, map_natCast, map_mul, map_natCast, RingHom.coe_pow]`. Conclude with `(mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hl.out.ne_zero)`.
-/
theorem kerAll_sat (a : Ainf l) (h : (l : Ainf l) * a ∈ kerAll l) : a ∈ kerAll l := by
  rw [mem_kerAll] at h ⊢
  intro n
  have h1 := h n
  rw [← RingHom.coe_pow, map_mul, map_natCast, map_mul, map_natCast, RingHom.coe_pow] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hl.out.ne_zero)

/- English proof (translation)
Take `⟨h1, δ, hδ, hδ1⟩` from `hε`. Conclude with `⟨h1, by rw [← root_eq hδ]; exact hδ1⟩`.
-/
theorem isEps_mem {ε : OCb l} (hε : IsEps ε) :
    GlobalTheory.MemLoc.IsEps ε := by
  obtain ⟨h1, δ, hδ, hδ1⟩ := hε
  exact ⟨h1, by rw [← root_eq hδ]; exact hδ1⟩

/- English proof (translation)
Take `⟨-, δ, hδ, hδ1⟩` from `hε`. Introduce and unpack `rfl`. Establish `: δ = 1` using `by rw [root_eq hδ, map_one]`. Conclude with `hδ1 (by rw [this, map_one])`.
-/
theorem ne_one {ε : OCb l} (hε : IsEps ε) : ε ≠ 1 := by
  obtain ⟨-, δ, hδ, hδ1⟩ := hε
  rintro rfl
  have : δ = 1 := by rw [root_eq hδ, map_one]
  exact hδ1 (by rw [this, map_one])

/- English proof (translation)
The claim follows from `GlobalTheory.T.wittVector_dvd_of_mem_saturated_ideal l (OCb l) (kerAll l) (muOf ε) (muOf_mem_kerAll hε.1) kerAll_sat (fun a ha => by rw [coeff_zero_muOf]; exact GlobalTheory.T.epsilon_sub_one_dvd_ainf_coeff_zero_of_theta_vanishing l ε hε a ((mem_kerAll a).1 ha)) _ (muOf_mem_kerAl …`.
-/
theorem muOf_dvd {ε : OCb l} (hε : IsEps ε) {x : OCb l} (hx : x.untilt = 1) : muOf ε ∣ muOf x :=
  GlobalTheory.T.wittVector_dvd_of_mem_saturated_ideal l (OCb l) (kerAll l) (muOf ε) (muOf_mem_kerAll hε.1) kerAll_sat
    (fun a ha => by rw [coeff_zero_muOf]; exact GlobalTheory.T.epsilon_sub_one_dvd_ainf_coeff_zero_of_theta_vanishing l ε hε a ((mem_kerAll a).1 ha)) _ (muOf_mem_kerAll hx)

/- English proof (translation)
Introduce `h` and use `by have := congrArg (fun y : Ainf l => y.coeff 0) h simp only [coeff_zero_muOf, WittVector.zero_coeff] at this exact ne_one hε (sub_eq_zero.1 this)`.
-/
theorem muOf_ne_zero {ε : OCb l} (hε : IsEps ε) : muOf ε ≠ 0 := fun h => by
  have := congrArg (fun y : Ainf l => y.coeff 0) h
  simp only [coeff_zero_muOf, WittVector.zero_coeff] at this
  exact ne_one hε (sub_eq_zero.1 this)

/- English proof (translation)
Rewrite using `[muOf, muOf, map_sub, map_one, GlobalTheory.RingIface.sigA_teich]`.
-/
theorem σA_muOf (g : GQ l) (x : OCb l) : Per.σA g (muOf x) = muOf (Per.σF g x) := by
  rw [muOf, muOf, map_sub, map_one, GlobalTheory.RingIface.sigA_teich]

/- English proof (translation)
Rewrite using `[GlobalTheory.RingBasics.untilt_σF, hx, map_one]`.
-/
theorem untilt_σF_eq {x : OCb l} (hx : x.untilt = 1) (g : GQ l) : (Per.σF g x).untilt = 1 := by
  rw [GlobalTheory.RingBasics.untilt_σF, hx, map_one]

end GlobalTheory.MuOfEps

namespace GlobalTheory.MuOfEps

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Take `⟨ζ, e, h0, -, h1, hr⟩` from `GlobalTheory.MemLoc.exists_zeta_eps l`. Establish `he : e.untilt = 1` using `Subtype.ext (by`. Use `hr 0` as an intermediate fact. Rewrite `this` using `[h0, map_one]`. Conclude with `this)`.

Establish `hE : GlobalTheory.MemLoc.IsEps e` using `⟨he, fun hh => h1 (by`. Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises. Rewrite using `[← hr 1, map_one]`. Conclude with `congrArg Subtype.val hh)⟩`. Conclude with `⟨e, he, _, frobeniusEquiv_symm_pow_p (OCb l) l e, hE.2⟩`.
-/
theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ ε : OCb l, IsEps ε := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  exact ⟨e, he, _, frobeniusEquiv_symm_pow_p (OCb l) l e, hE.2⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `muOf_dvd hε (untilt_σF_eq hε.1 g)`. Take `⟨b, hb⟩` from `muOf_dvd hε (untilt_σF_eq hε.1 g⁻¹)`. Rewrite `ha`, `hb` using `[← σA_muOf]`. Establish `h : muOf ε = Per.σA g b * a * muOf ε`. Use `congrArg (Per.σA g) hb` as an intermediate fact.

Rewrite `this` using `[← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one, map_mul, ha]`. Take the linear combination `this`. Establish `h1 : Per.σA g b * a = 1`. Establish `h2 : (Per.σA g b * a - 1) * muOf ε = 0` using `by linear_combination -h`. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (muOf_ne_zero hε))`.

Use `⟨⟨a, Per.σA g b, by rw [mul_comm]; exact h1, h1⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[ha, mul_comm]`.
-/
theorem units_σA {ε : OCb l} (hε : IsEps ε) (g : GQ l) :
    ∃ u : (Ainf l)ˣ, Per.σA g (muOf ε) = u * muOf ε := by
  obtain ⟨a, ha⟩ := muOf_dvd hε (untilt_σF_eq hε.1 g)
  obtain ⟨b, hb⟩ := muOf_dvd hε (untilt_σF_eq hε.1 g⁻¹)
  rw [← σA_muOf] at ha hb
  have h : muOf ε = Per.σA g b * a * muOf ε := by
    have := congrArg (Per.σA g) hb
    rw [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one, map_mul, ha] at this
    linear_combination this
  have h1 : Per.σA g b * a = 1 := by
    have h2 : (Per.σA g b * a - 1) * muOf ε = 0 := by linear_combination -h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (muOf_ne_zero hε))
  refine ⟨⟨a, Per.σA g b, by rw [mul_comm]; exact h1, h1⟩, ?_⟩
  rw [ha, mul_comm]

/- English proof (translation)
Introduce `l _`. Use `⟨exists_isEps l, fun ε δ hε hδ => ?_⟩` and prove the remaining obligations. Establish `hr` using `root_eq hδ`. Establish `hE` using `isEps_mem hε`. Use `⟨⟨GlobalTheory.MemLoc.xi ε, (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE).symm, ?_⟩, ?_, ?_, ?_, ?_, units_σA hε, fun x hx => muOf_dvd hε hx⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.MemLoc.xi, ← hr, muOf, muOf, geom_sum_mul, ← map_pow, hδ]`. Rewrite using `[muOf, muOf, map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, hδ]`. Rewrite using `[theta_muOf, sub_ne_zero]`. Take `⟨-, δ', hδ', hδ'1⟩` from `hε`. Rewrite `hδ'1` using `[root_eq hδ', ← hr]`. Then use the resulting hypothesis.

Conclude with `GlobalTheory.CrisLoc.unit_of_root l ε hε.1 (ne_one hε)`. Use `WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => ?_` and prove the remaining obligations. Establish `h0 : (muOf ε).coeff 0 = 0` using `IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm)`. Rewrite `h0` using `[coeff_zero_muOf]`. Conclude with `ne_one hε (sub_eq_zero.1 h0)`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime], (∃ ε : OCb l, IsEps ε) ∧ ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → (∃ ξ : Ainf l, Ideal.span {ξ} = RingHom.ker (Per.θ l) ∧ muOf ε = ξ * muOf δ) ∧ WittVector.frobenius (muOf δ) = muOf ε ∧ Per.θ l (muOf δ) ≠ 0 ∧ IsUnit (acrisToBcris l (ainfToAcris l (muOf ε))) ∧ IsUnit (inclW l (muOf ε)) ∧ (∀ g : GQ l, ∃ u : (Ainf l)ˣ, Per.σA g (muOf ε) = u * muOf ε) ∧ ∀ x : OCb l, x.untilt = 1 → muOf ε ∣ muOf x := by
  intro l _
  refine ⟨exists_isEps l, fun ε δ hε hδ => ?_⟩
  have hr := root_eq hδ
  have hE := isEps_mem hε
  refine ⟨⟨GlobalTheory.MemLoc.xi ε, (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE).symm, ?_⟩, ?_, ?_, ?_, ?_, units_σA hε,
    fun x hx => muOf_dvd hε hx⟩
  · rw [GlobalTheory.MemLoc.xi, ← hr, muOf, muOf, geom_sum_mul, ← map_pow, hδ]
  · rw [muOf, muOf, map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      frobenius_def, hδ]
  · rw [theta_muOf, sub_ne_zero]
    obtain ⟨-, δ', hδ', hδ'1⟩ := hε
    rwa [root_eq hδ', ← hr] at hδ'1
  · exact GlobalTheory.CrisLoc.unit_of_root l ε hε.1 (ne_one hε)
  · refine WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => ?_
    have h0 : (muOf ε).coeff 0 = 0 :=
      IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm)
    rw [coeff_zero_muOf] at h0
    exact ne_one hε (sub_eq_zero.1 h0)

end GlobalTheory.MuOfEps

end

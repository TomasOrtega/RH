import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import GroundTheory.GlobalFields.TateThesis.AdelePoisson
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.HalfOut

section SlopeTestRemainingChoices

open Formalism.L2.DIV GlobalTheory.StdFrames ValuativeRel
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
Introduce and unpack `rfl`. Establish `h` using `Nat.mod_mod_of_dvd p hk`. Rewrite `h` using `[hp, Nat.mod_self, Nat.mod_eq_of_lt hk1]`. Conclude with `one_ne_zero h`.
-/
theorem ne_of_mod_eq_one {p M k : ℕ} (hp : p % M = 1) (hk : k ∣ M) (hk1 : 1 < k) : p ≠ k := by
  rintro rfl
  have h := Nat.mod_mod_of_dvd p hk
  rw [hp, Nat.mod_self, Nat.mod_eq_of_lt hk1] at h
  exact one_ne_zero h

/- English proof (translation)
Use `Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)` and prove the remaining obligations. Break down `(Nat.Prime.dvd_mul hp).1 h with h | h` into its components or cases. Conclude with `h2 (Nat.mem_primeFactors.2 ⟨hp, h, D.host.QS_pos.ne'⟩)`. Conclude with `hq ((Nat.prime_dvd_prime_iff_eq hp D.host.hyp.1).1 h)`.
-/
theorem coprime_two_q {p : ℕ} (hp : p.Prime) (h2 : p ∉ D.host.small) (hq : p ≠ D.host.q) : Nat.Coprime (D.host.QS * D.host.q) p := by
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact h2 (Nat.mem_primeFactors.2 ⟨hp, h, D.host.QS_pos.ne'⟩)
  · exact hq ((Nat.prime_dvd_prime_iff_eq hp D.host.hyp.1).1 h)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = w := by`. Unfold `Places.W0 at hw`. Use `Finset.mem_image.1 hw` and compare the differences between its conclusion and the goal. Establish `hoff : ∀ p : ℕ, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) → p ∉ D.host.small ∧ p ≠ D.host.q` using `fun p hp hc => ⟨fun hs => (Nat.Prime.coprime_iff_not_dvd hp).1 hc ((Nat.dvd_of_mem_primeFactors hs).mul_right _), fun e => (Nat.Prime.coprime_iff_not_dvd hp).1 hc (e ▸ dvd_mul_left _ _)⟩`. Establish `hN : 1 < D.host.QS * D.host.q * D.host.d` using `lt_of_lt_of_le D.host.hyp.2.1.one_lt (Nat.le_mul_of_pos_left _ (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos))`.

Establish `hq : D.host.q ∣ D.host.QS * D.host.q * D.host.d` using `Dvd.dvd.mul_right (dvd_mul_left _ _) _`. Establish `hq1 : 1 < D.host.q` using `D.host.hyp.1.one_lt`. Establish `key : ∃ p : ℕ, p.Prime ∧ p ∉ D.host.small ∧ p ≠ D.host.q ∧ ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal`. Break down `G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1` into its components or cases. Establish `h0` using `(GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).2.1`.

Conclude with `⟨_, (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1, UpperTheory.Small.not_mem_of_mod D.host (by`. Establish `h1` using `Nat.mod_mod_of_dvd (q0 D) (dvd_mul_left (D.host.QS * D.host.q * D.host.d) (Formalism.MainNotions.rPrAv D))`. Conclude with `h1.symm.trans ((congrArg (· % (D.host.QS * D.host.q * D.host.d)) h0).trans (Nat.mod_eq_of_lt hN))),`. Use `ne_of_mod_eq_one h0 (dvd_trans hq (dvd_mul_left _ _)) hq1, G.pl.basePlace_over_qZero⟩`. Break down `(GlobalTheory.ChiGrid.S1_mem_OmF D).1 hv1 with h | h | h | h` into its components or cases.

Conclude with `⟨_, D.host.g_prime 0, UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond 0), ne_of_mod_eq_one (D.ntypes.g_cond 0) hq hq1, h⟩`. Conclude with `⟨_, D.host.g_prime 1, UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond 1), ne_of_mod_eq_one (D.ntypes.g_cond 1) hq hq1, h⟩`. Conclude with `⟨_, D.host.pde_prime, (hoff _ D.host.pde_prime hO.1).1, (hoff _ D.host.pde_prime hO.1).2, h⟩`. Conclude with `⟨_, D.host.pde'_prime, (hoff _ D.host.pde'_prime hO.2).1, (hoff _ D.host.pde'_prime hO.2).2, h⟩`. Take `⟨p, hp, hp2, hpq, hpv⟩` from `key`.

Establish `hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal`. Rewrite `hpv` using `[← G.pl.under_w hv]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ (G.pl.w v).asIdeal at hpv`. Rewrite `hpv` using `[map_natCast]`. Then use the resulting hypothesis. Conclude with `GlobalTheory.AAUnit.natCast_notMem_of_coprime _ (coprime_two_q hp hp2 hpq) hpw`.
-/
theorem two_q_notMem (hO : OffQ D) (G : GridData L sc) {w : Pl D.host.E} (hw : w ∈ G.pl.W0) :
    ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  classical
  obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = w := by
    unfold Places.W0 at hw
    convert Finset.mem_image.1 hw
  have hoff : ∀ p : ℕ, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) → p ∉ D.host.small ∧ p ≠ D.host.q := fun p hp hc =>
    ⟨fun hs => (Nat.Prime.coprime_iff_not_dvd hp).1 hc ((Nat.dvd_of_mem_primeFactors hs).mul_right _),
      fun e => (Nat.Prime.coprime_iff_not_dvd hp).1 hc (e ▸ dvd_mul_left _ _)⟩
  have hN : 1 < D.host.QS * D.host.q * D.host.d :=
    lt_of_lt_of_le D.host.hyp.2.1.one_lt (Nat.le_mul_of_pos_left _ (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos))
  have hq : D.host.q ∣ D.host.QS * D.host.q * D.host.d := Dvd.dvd.mul_right (dvd_mul_left _ _) _
  have hq1 : 1 < D.host.q := D.host.hyp.1.one_lt
  have key : ∃ p : ℕ, p.Prime ∧ p ∉ D.host.small ∧ p ≠ D.host.q ∧ ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
    · have h0 := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
      exact ⟨_, (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1, UpperTheory.Small.not_mem_of_mod D.host (by
          have h1 := Nat.mod_mod_of_dvd (q0 D) (dvd_mul_left (D.host.QS * D.host.q * D.host.d) (Formalism.MainNotions.rPrAv D))
          exact h1.symm.trans ((congrArg (· % (D.host.QS * D.host.q * D.host.d)) h0).trans (Nat.mod_eq_of_lt hN))),
        ne_of_mod_eq_one h0 (dvd_trans hq (dvd_mul_left _ _)) hq1, G.pl.basePlace_over_qZero⟩
    · rcases (GlobalTheory.ChiGrid.S1_mem_OmF D).1 hv1 with h | h | h | h
      · exact ⟨_, D.host.g_prime 0, UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond 0),
          ne_of_mod_eq_one (D.ntypes.g_cond 0) hq hq1, h⟩
      · exact ⟨_, D.host.g_prime 1, UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond 1),
          ne_of_mod_eq_one (D.ntypes.g_cond 1) hq hq1, h⟩
      · exact ⟨_, D.host.pde_prime, (hoff _ D.host.pde_prime hO.1).1, (hoff _ D.host.pde_prime hO.1).2, h⟩
      · exact ⟨_, D.host.pde'_prime, (hoff _ D.host.pde'_prime hO.2).1, (hoff _ D.host.pde'_prime hO.2).2, h⟩
  obtain ⟨p, hp, hp2, hpq, hpv⟩ := key
  have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
    rw [← G.pl.under_w hv] at hpv
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ (G.pl.w v).asIdeal at hpv
    rwa [map_natCast] at hpv
  exact GlobalTheory.AAUnit.natCast_notMem_of_coprime _ (coprime_two_q hp hp2 hpq) hpw

/- English proof (translation)
Rewrite using `[GlobalTheory.FunObj.Good.valued_alg]`. Conclude with `GlobalTheory.FunObj.Good.valuation_le_one_of_mem (two_q_notMem hO G hw) (Or.inl ha)`.
-/
theorem aa_le_one (hO : OffQ D) (G : GridData L sc) {w : Pl D.host.E} (hw : w ∈ G.pl.W0) {a : D.host.E}
    (ha : a ∈ D.host.AA) : Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1 := by
  rw [GlobalTheory.FunObj.Good.valued_alg]
  exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem (two_q_notMem hO G hw) (Or.inl ha)

/- English proof (translation)
Rewrite using `[GlobalTheory.FunObj.Good.valued_alg]`. Establish `h1 : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `G.pl.modul_ne_bot sc`. Establish `hb : G.pl.modulBar sc ≠ ⊥`.

Unfold `Places.modulBar`. Introduce `h`. Apply `G.pl.modul_ne_bot sc` to reduce the goal to its premises. Use `congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h` as an intermediate fact. Simplify `this` using `[smul_smul]`.

Establish `h2 : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `hb`. Establish `hc : FractionalIdeal.count D.host.E w (shiftId G) = cosExp G w`. Unfold `shiftId`.

Rewrite using `[FractionalIdeal.count_mul D.host.E w h1 (inv_ne_zero h2), FractionalIdeal.count_inv, count_modul, count_modulBar G (t := t) ((GlobalTheory.FunObj.GivenAdm.mem_locPl).2 (Or.inl hw)), neg_zero, add_zero]`. Use `GroundTheory.Global.valuation_le_of_mem_fractionalIdeal w hσ` as an intermediate fact. Rewrite `this` using `[hc]`. Then use the resulting hypothesis.
-/
theorem shift_le (G : GridData L sc) (t : T) {w : Pl D.host.E} (hw : w ∈ G.pl.W0) {σ : D.host.E} (hσ : σ ∈ shiftId G) :
    Valued.v (algebraMap D.host.E (Kw w) σ) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  rw [GlobalTheory.FunObj.Good.valued_alg]
  have h1 : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hb : G.pl.modulBar sc ≠ ⊥ := by
    unfold Places.modulBar
    intro h
    apply G.pl.modul_ne_bot sc
    have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
    simpa [smul_smul] using this
  have h2 : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hb
  have hc : FractionalIdeal.count D.host.E w (shiftId G) = cosExp G w := by
    unfold shiftId
    rw [FractionalIdeal.count_mul D.host.E w h1 (inv_ne_zero h2), FractionalIdeal.count_inv, count_modul,
      count_modulBar G (t := t) ((GlobalTheory.FunObj.GivenAdm.mem_locPl).2 (Or.inl hw)), neg_zero, add_zero]
  have := GroundTheory.Global.valuation_le_of_mem_fractionalIdeal w hσ
  rwa [hc] at this

end SlopeTestRemainingChoices

end GlobalTheory.HalfOut

namespace GlobalTheory.HalfOut

section Local

open Formalism.L2.DIV GlobalTheory.StdFrames ValuativeRel GlobalTheory.RowLatChi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem genMap_add (S T : HSp D) (s : Fin S.rank → D.host.E) (t t' : Fin T.rank → D.host.E) :
    GlobalTheory.LatVac.genMap S T 1 s (t + t') = GlobalTheory.LatVac.genMap S T 1 s t + GlobalTheory.LatVac.genMap S T 1 s t' := by
  ext p q; simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; ring

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem genMap_smul (S T : HSp D) (s : Fin S.rank → D.host.E) (c : D.host.E) (t : Fin T.rank → D.host.E) :
    GlobalTheory.LatVac.genMap S T 1 s (c • t) = c • GlobalTheory.LatVac.genMap S T 1 s t := by
  ext p q; simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Use extensionality with `p q`. Simplify using `[GlobalTheory.LatVac.genMap]`.
-/
theorem genMap_zero (S T : HSp D) (s : Fin S.rank → D.host.E) :
    GlobalTheory.LatVac.genMap S T 1 s (0 : Fin T.rank → D.host.E) = 0 := by
  ext p q; simp [GlobalTheory.LatVac.genMap]

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]`.
-/
theorem map_smul_eToEAf {m n : ℕ} (c : D.host.E) (Y : Matrix (Fin m) (Fin n) D.host.E) :
    (c • Y).map (eToEAf D) = eToEAf D c • Y.map (eToEAf D) := by
  ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Apply the tactic sequence `have hS : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) := (G.isV (X := .grid (i + 1) 0) (by show _ ∧ _; constructor <;> omega) (by intro j hj; injection hj with h2; omega)).sd`. Establish `hβS` using `B.isFrame_β hL (i := i + 1) hi (Nat.zero_le _)`. Establish `hβT` using `B.isFrame_β hL (i := i) hi.le (Nat.zero_le _)`. Use `set κ : WithZero (Multiplicative ℤ) := WithZero.exp (-(cosExp G w : ℤ)) with hκ`. Set `p : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) → Prop` to `fun u => ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) (u.map (toEAf D)) a b)) ≤ κ`.

Establish `hadd : ∀ x y, p x → p y → p (x + y)` using `fun x y hx hy a b => by`. Rewrite using `[Matrix.map_add _ (toEAf D).map_add, Comparison₂.fr_add, Matrix.add_apply, RingHom.map_add]`. Conclude with `Valuation.map_add_le _ (hx a b) (hy a b)`. Establish `hneg : ∀ x, p x → p (-x)` using `fun x hx a b => by`. Rewrite using `[Matrix.map_neg _ (toEAf D).map_neg, fr_neg, Matrix.neg_apply, RingHom.map_neg, Valuation.map_neg]`.

Conclude with `hx a b`. Establish `hzero : p 0` using `fun a b => by`. Rewrite using `[Matrix.map_zero _ (toEAf D).map_zero, show Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) (0 : Matrix (Fin (G.V (.grid i 0)).rank) (Fin (G.V (.grid (i + 1) 0)).rank) (EAf D)) = 0 by`. Rewrite using `[Comparison₂.fr, Matrix.mul_zero, Matrix.zero_mul]]`. Simplify using the standard rewrite rules.

Establish `hY : ∀ s ∈ G.Λ (.grid (i + 1) 0), ∀ t ∈ idLat (shiftId G) (G.Λ (.grid i 0)), ∀ a b, Valued.v (cpt (D` using `D) w (Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) ((GlobalTheory.LatVac.genMap (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) 1 s t).map (eToEAf D)) a b)) ≤ κ := by`. Introduce `s hs t ht`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨σ, hσ, y, hy, rfl⟩` from `hx`.

Introduce `a b`. Take `⟨s', -, hs'⟩` from `Comparison₂.fr_mem_idS hβS hβT (𝔪 := ⊤) (by rw [Submodule.top_smul]; exact genMap_one_mem_homLat hS hs hy) a b`. Rewrite using `[genMap_smul, map_smul_eToEAf, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, Valuation.map_mul]`. Establish `h1 : Valued.v (cpt (D` using `D) w (eToEAf D σ)) ≤ κ := by`. Rewrite using `[show cpt (D := D) w (eToEAf D σ) = algebraMap D.host.E (Kw w) σ from Comparison₂.cpt_tmul w σ]`.

Conclude with `shift_le G μ₀ hw hσ`. Establish `h2` using `(mem_OA_iff _).1 s'.2 w`. Rewrite `h2` using `[hs']`. Combine the equalities or inequalities in the displayed calculation. Consider the case `zero`.

Introduce `a b`. Rewrite using `[genMap_zero, Matrix.map_zero _ (eToEAf D).map_zero, show Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) (0 : Matrix (Fin (G.V (.grid i 0)).rank) (Fin (G.V (.grid (i + 1) 0)).rank) (EAf D)) = 0 by`. Rewrite using `[Comparison₂.fr, Matrix.mul_zero, Matrix.zero_mul]]`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`.

Introduce `a b`. Rewrite using `[genMap_add, Matrix.map_add _ (eToEAf D).map_add, Comparison₂.fr_add, Matrix.add_apply, RingHom.map_add]`. Conclude with `Valuation.map_add_le _ (hx a b) (hy a b)`. Consider the case `smul r x _ hx`. Introduce `a b`.

Rewrite using `[← algebraMap_smul D.host.E r x, genMap_smul, map_smul_eToEAf, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, Valuation.map_mul]`. Establish `h1 : Valued.v (cpt (D` using `D) w (eToEAf D (algebraMap (𝓞 D.host.E) D.host.E r))) ≤ 1 := by`. Rewrite using `[show cpt (D := D) w (eToEAf D (algebraMap (𝓞 D.host.E) D.host.E r)) = algebraMap D.host.E (Kw w) (algebraMap (𝓞 D.host.E) D.host.E r) from Comparison₂.cpt_tmul w _, GlobalTheory.FunObj.Good.valued_alg]`. Conclude with `w.valuation_le_one r`. Combine the equalities or inequalities in the displayed calculation.

Use `GlobalTheory.LatVac.latO_induction (p := p) (fun α hα M hM => ?_) hzero hadd hneg hu a b` and prove the remaining obligations. Proceed by induction on `hM using AddSubgroup.closure_induction with`. Consider the case `mem M hM`. Take `⟨c, hc, s, hs, t, ht, rfl⟩` from `hM`. Use `set Y := GlobalTheory.LatVac.genMap (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) 1 s t`.

Establish `e1 : (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) c s t) : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))).map (toEAf D) = toEAf D ((pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D c) • Y.map (eToEAf D)`. Use extensionality with `p q`. Simplify using `only [GlobalTheory.LatVac.finTens, Y, GlobalTheory.LatVac.genMap, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[show c * t p * ∑ k, star (s k) * HSpace.gram (G.V (.grid (i + 1) 0)) k q = c * (1 * t p * ∑ k, star (s k) * HSpace.gram (G.V (.grid (i + 1) 0)) k q) by ring, tmul_eq, RingHom.map_mul]`. Both sides reduce to the same expression.

Introduce `a b`. Rewrite using `[e1, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul, RingHom.map_mul, Valuation.map_mul]`. Establish `h1 : Valued.v (cpt (D` using `D) w (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)))) ≤ 1 := by`. Establish `hi : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D` using `AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩`. Conclude with `((comp_toAd D).int (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E))).1 hi w`.

Establish `h2 : Valued.v (cpt (D` using `D) w (toEAf D (incA D c))) ≤ 1 := by`. Rewrite using `[show cpt (D := D) w (toEAf D (incA D c)) = algebraMap D.host.E (Kw w) c from Comparison₂.cpt_tmul w c]`. Conclude with `aa_le_one hO G hw hc`. Combine the equalities or inequalities in the displayed calculation. Consider the case `zero => rw [GlobalTheory.LatVac.finTens_zero]`.

Conclude with `hzero`. Consider the case `add x y _ _ hx hy => rw [GlobalTheory.LatVac.finTens_add]`. Conclude with `hadd _ _ hx hy`. Consider the case `neg x _ hx => rw [GlobalTheory.LatVac.finTens_neg]`. Conclude with `hneg _ hx`.
-/
theorem local_le {μ₀ : T} (hL : L.Is μ₀) (hO : OffQ D) (G : GridData L sc) (B : GlobalTheory.FunObj.Frames G) {i : ℕ} (hi : i < D.R.m)
    {w : Pl D.host.E} (hw : w ∈ G.pl.W0) {u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))} (hu : u ∈ latBig G i)
    (a : Fin (G.V (.grid i 0)).rank) (b : Fin (G.V (.grid (i + 1) 0)).rank) :
    Valued.v (cpt (D := D) w (Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) (u.map (toEAf D)) a b)) ≤
      WithZero.exp (-(cosExp G w : ℤ)) := by
  have hS : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) :=
    (G.isV (X := .grid (i + 1) 0) (by show _ ∧ _; constructor <;> omega) (by intro j hj; injection hj with h2; omega)).sd
  have hβS := B.isFrame_β hL (i := i + 1) hi (Nat.zero_le _)
  have hβT := B.isFrame_β hL (i := i) hi.le (Nat.zero_le _)
  set κ : WithZero (Multiplicative ℤ) := WithZero.exp (-(cosExp G w : ℤ)) with hκ
  let p : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) → Prop := fun u => ∀ a b,
    Valued.v (cpt (D := D) w (Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) (u.map (toEAf D)) a b)) ≤ κ
  have hadd : ∀ x y, p x → p y → p (x + y) := fun x y hx hy a b => by
    rw [Matrix.map_add _ (toEAf D).map_add, Comparison₂.fr_add, Matrix.add_apply, RingHom.map_add]
    exact Valuation.map_add_le _ (hx a b) (hy a b)
  have hneg : ∀ x, p x → p (-x) := fun x hx a b => by
    rw [Matrix.map_neg _ (toEAf D).map_neg, fr_neg, Matrix.neg_apply, RingHom.map_neg, Valuation.map_neg]
    exact hx a b
  have hzero : p 0 := fun a b => by
    rw [Matrix.map_zero _ (toEAf D).map_zero, show Comparison₂.fr (B.β i 0) (B.β (i + 1) 0)
      (0 : Matrix (Fin (G.V (.grid i 0)).rank) (Fin (G.V (.grid (i + 1) 0)).rank) (EAf D)) = 0 by
      rw [Comparison₂.fr, Matrix.mul_zero, Matrix.zero_mul]]
    simp
  have hY : ∀ s ∈ G.Λ (.grid (i + 1) 0), ∀ t ∈ idLat (shiftId G) (G.Λ (.grid i 0)), ∀ a b,
      Valued.v (cpt (D := D) w (Comparison₂.fr (B.β i 0) (B.β (i + 1) 0)
        ((GlobalTheory.LatVac.genMap (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) 1 s t).map (eToEAf D)) a b)) ≤ κ := by
    intro s hs t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨σ, hσ, y, hy, rfl⟩ := hx
      intro a b
      obtain ⟨s', -, hs'⟩ := Comparison₂.fr_mem_idS hβS hβT (𝔪 := ⊤)
        (by rw [Submodule.top_smul]; exact genMap_one_mem_homLat hS hs hy) a b
      rw [genMap_smul, map_smul_eToEAf, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, Valuation.map_mul]
      have h1 : Valued.v (cpt (D := D) w (eToEAf D σ)) ≤ κ := by
        rw [show cpt (D := D) w (eToEAf D σ) = algebraMap D.host.E (Kw w) σ from Comparison₂.cpt_tmul w σ]
        exact shift_le G μ₀ hw hσ
      have h2 := (mem_OA_iff _).1 s'.2 w
      rw [hs'] at h2
      calc _ ≤ κ * 1 := mul_le_mul' h1 h2
        _ = κ := mul_one κ
    | zero =>
      intro a b
      rw [genMap_zero, Matrix.map_zero _ (eToEAf D).map_zero, show Comparison₂.fr (B.β i 0) (B.β (i + 1) 0)
        (0 : Matrix (Fin (G.V (.grid i 0)).rank) (Fin (G.V (.grid (i + 1) 0)).rank) (EAf D)) = 0 by
        rw [Comparison₂.fr, Matrix.mul_zero, Matrix.zero_mul]]
      simp
    | add x y _ _ hx hy =>
      intro a b
      rw [genMap_add, Matrix.map_add _ (eToEAf D).map_add, Comparison₂.fr_add, Matrix.add_apply, RingHom.map_add]
      exact Valuation.map_add_le _ (hx a b) (hy a b)
    | smul r x _ hx =>
      intro a b
      rw [← algebraMap_smul D.host.E r x, genMap_smul, map_smul_eToEAf, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul,
        RingHom.map_mul, Valuation.map_mul]
      have h1 : Valued.v (cpt (D := D) w (eToEAf D (algebraMap (𝓞 D.host.E) D.host.E r))) ≤ 1 := by
        rw [show cpt (D := D) w (eToEAf D (algebraMap (𝓞 D.host.E) D.host.E r)) =
          algebraMap D.host.E (Kw w) (algebraMap (𝓞 D.host.E) D.host.E r) from Comparison₂.cpt_tmul w _,
          GlobalTheory.FunObj.Good.valued_alg]
        exact w.valuation_le_one r
      calc _ ≤ 1 * κ := mul_le_mul' h1 (hx a b)
        _ = κ := one_mul κ
  refine GlobalTheory.LatVac.latO_induction (p := p) (fun α hα M hM => ?_) hzero hadd hneg hu a b
  induction hM using AddSubgroup.closure_induction with
  | mem M hM =>
    obtain ⟨c, hc, s, hs, t, ht, rfl⟩ := hM
    set Y := GlobalTheory.LatVac.genMap (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) 1 s t
    have e1 : (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) c s t) :
        WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))).map (toEAf D) =
        toEAf D ((pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D c) • Y.map (eToEAf D) := by
      ext p q
      simp only [GlobalTheory.LatVac.finTens, Y, GlobalTheory.LatVac.genMap, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul]
      rw [show c * t p * ∑ k, star (s k) * HSpace.gram (G.V (.grid (i + 1) 0)) k q =
          c * (1 * t p * ∑ k, star (s k) * HSpace.gram (G.V (.grid (i + 1) 0)) k q) by ring,
        tmul_eq, RingHom.map_mul]
      rfl
    intro a b
    rw [e1, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul,
      RingHom.map_mul, Valuation.map_mul]
    have h1 : Valued.v (cpt (D := D) w (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)))) ≤ 1 := by
      have hi : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩
      exact ((comp_toAd D).int (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E))).1 hi w
    have h2 : Valued.v (cpt (D := D) w (toEAf D (incA D c))) ≤ 1 := by
      rw [show cpt (D := D) w (toEAf D (incA D c)) = algebraMap D.host.E (Kw w) c from Comparison₂.cpt_tmul w c]
      exact aa_le_one hO G hw hc
    calc _ ≤ 1 * 1 * κ := mul_le_mul' (mul_le_mul' h1 h2) (hY s hs t ht a b)
      _ = κ := by rw [one_mul, one_mul]
  | zero => rw [GlobalTheory.LatVac.finTens_zero]; exact hzero
  | add x y _ _ hx hy => rw [GlobalTheory.LatVac.finTens_add]; exact hadd _ _ hx hy
  | neg x _ hx => rw [GlobalTheory.LatVac.finTens_neg]; exact hneg _ hx

end Local

end GlobalTheory.HalfOut

section Main
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

/- English proof (translation)
Introduce `D T L sc μ₀ hL hO G i hi e he u hu`. Take `⟨B⟩` from `(inferInstance : Nonempty (GlobalTheory.FunObj.Frames G))`. Establish `hβS` using `B.isFrame_β hL (i := i + 1) hi (Nat.zero_le _)`. Establish `hβT` using `B.isFrame_β hL (i := i) hi.le (Nat.zero_le _)`. Take `⟨e0, e1, e2⟩` from `Comparison₂.cpt_idemSum he`.

Rewrite using `[Comparison₂.mem_hatMx_iff hβS hβT]`. Use `⟨fun a b => ?_, fun a b => ?_⟩` and prove the remaining obligations. Use `show infPart D (e * u a b) = 0`. Rewrite using `[RingHom.map_mul, e0, zero_mul]`. Use `set z := toEAf D e * Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) (u.map (toEAf D)) a b with hzdef`.

Establish `hz : Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) ((e • u).map (toEAf D)) a b = z`. Establish `: (e • u).map (toEAf D) = toEAf D e • u.map (toEAf D)` using `Matrix.ext fun p q => by`. Rewrite using `[Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]`. Both sides reduce to the same expression. Rewrite using `[this, Comparison₂.fr_smul]`.

Both sides reduce to the same expression. Establish `hloc : ∀ w ∈ G.pl.W0, Valued.v (GlobalTheory.StdFrames.cpt (D` using `D) w z) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by`. Introduce `w hw`. Rewrite using `[hzdef, RingHom.map_mul, e1 w hw, one_mul]`. Conclude with `GlobalTheory.HalfOut.local_le hL hO G B hi hw hu a b`.

Use `⟨⟨z, (GlobalTheory.StdFrames.mem_OA_iff _).2 fun Q => ?_⟩, (Comparison₂.mem_idS_modul G _).2 hloc, hz.symm⟩` and prove the remaining obligations. Distinguish the cases in `hQ : Q ∈ G.pl.W0`. Conclude with `(hloc Q hQ).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)`. Conclude with `Comparison₂.cpt_mul_mem hzdef (e2 Q hQ)`.
-/
theorem GlobalTheory.HalfOut.smul_mem_hatMx_of_mem_latBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latBig G i, e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := by
  intro D T L sc μ₀ hL hO G i hi e he u hu
  obtain ⟨B⟩ := (inferInstance : Nonempty (GlobalTheory.FunObj.Frames G))
  have hβS := B.isFrame_β hL (i := i + 1) hi (Nat.zero_le _)
  have hβT := B.isFrame_β hL (i := i) hi.le (Nat.zero_le _)
  obtain ⟨e0, e1, e2⟩ := Comparison₂.cpt_idemSum he
  rw [Comparison₂.mem_hatMx_iff hβS hβT]
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · show infPart D (e * u a b) = 0
    rw [RingHom.map_mul, e0, zero_mul]
  · set z := toEAf D e * Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) (u.map (toEAf D)) a b with hzdef
    have hz : Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) ((e • u).map (toEAf D)) a b = z := by
      have : (e • u).map (toEAf D) = toEAf D e • u.map (toEAf D) := Matrix.ext fun p q => by
        rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]; rfl
      rw [this, Comparison₂.fr_smul]; rfl
    have hloc : ∀ w ∈ G.pl.W0, Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
      intro w hw
      rw [hzdef, RingHom.map_mul, e1 w hw, one_mul]
      exact GlobalTheory.HalfOut.local_le hL hO G B hi hw hu a b
    refine ⟨⟨z, (GlobalTheory.StdFrames.mem_OA_iff _).2 fun Q => ?_⟩, (Comparison₂.mem_idS_modul G _).2 hloc, hz.symm⟩
    by_cases hQ : Q ∈ G.pl.W0
    · exact (hloc Q hQ).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
    · exact Comparison₂.cpt_mul_mem hzdef (e2 Q hQ)

end Main

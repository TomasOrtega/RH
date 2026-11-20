import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatMMemOfLeHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open GlobalTheory.ExportSeries

namespace GlobalTheory.OnePlaceCong

def locU {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) : Rˣ where
  val := 1 - g + g * x
  inv := 1 - g + g * (x⁻¹ : Rˣ)
  val_inv := by
    have h := x.mul_inv
    linear_combination (-((x : R) + (x⁻¹ : Rˣ) - 2)) * hg + g * g * h
  inv_val := by
    have h := x.inv_mul
    linear_combination (-((x : R) + (x⁻¹ : Rˣ) - 2)) * hg + g * g * h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_locU {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) :
    ((locU g hg x : Rˣ) : R) = 1 - g + g * x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem locU_inv {R : Type} [CommRing R] (g : R) (hg : g * g = g) (x : Rˣ) :
    (locU g hg x)⁻¹ = locU g hg x⁻¹ := rfl

variable {D : D7}

/- English proof (translation)
Establish `h1 : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D` using `GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1)`. Establish `hfg : finPart D g ∈ intAE D` using `GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hg])`. Rewrite using `[coe_locU, RingHom.map_add, RingHom.map_sub, RingHom.map_one, RingHom.map_mul]`. Conclude with `add_mem (sub_mem h1 hfg) (GlobalTheory.HeckeConj.mul_mem_intAE D hfg hz)`.
-/
theorem finPart_locU_mem {g : AE D} (hg : g * g = g) {z : (AE D)ˣ} (hz : finPart D (z : AE D) ∈ intAE D) :
    finPart D ((locU g hg z : (AE D)ˣ) : AE D) ∈ intAE D := by
  have h1 : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1)
  have hfg : finPart D g ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hg])
  rw [coe_locU, RingHom.map_add, RingHom.map_sub, RingHom.map_one, RingHom.map_mul]
  exact add_mem (sub_mem h1 hfg) (GlobalTheory.HeckeConj.mul_mem_intAE D hfg hz)

/- English proof (translation)
Establish `he : idemAt PP * idemAt PP = idemAt PP` using `hI.1.1`. Establish `hfa` using `finPart_locU_mem he hx`. Establish `hxa` using `GlobalTheory.IdemRes.toEAf_mem_of_finPart hfa`. Take `⟨hE, hres⟩` from `GlobalTheory.IdemRes.resS_idem_eq_one D (idemAt PP) PP hI`. Take `⟨w, rfl⟩` from `GlobalTheory.SplitDualLat.finPart_surjective (D := D) y`.

Establish `hX` using `GlobalTheory.IdemRes.toEAf_mem_of_finPart hx`. Establish `hW` using `GlobalTheory.IdemRes.toEAf_mem_of_finPart hy`. Establish `key0 : Formalism.IndefR.Datum.toEAf D ((x : AE D) - 1 - N • w) = 0`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D _) = 0`. Rewrite using `[RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul, hxy, sub_self, map_zero]`.

Establish `key : Formalism.IndefR.Datum.toEAf D (x : AE D) = 1 + N • Formalism.IndefR.Datum.toEAf D w`. Rewrite `key0` using `[RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul]`. Take the linear combination `key0`. Establish `ha : (⟨Formalism.IndefR.Datum.toEAf D (locU (idemAt PP) he x : AE D), hxa⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 - ⟨_, hE⟩ + ⟨_, hE⟩ * (1 + N • ⟨_, hW⟩)`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `Formalism.IndefR.Datum.toEAf D (1 - idemAt PP + idemAt PP * (x : AE D)) = 1 - Formalism.IndefR.Datum.toEAf D (idemAt PP) + Formalism.IndefR.Datum.toEAf D (idemAt PP) * (1 + N • Formalism.IndefR.Datum.toEAf D w)`. Rewrite using `[RingHom.map_add, RingHom.map_sub, RingHom.map_one, RingHom.map_mul, key]`. Establish `hN0 : ((N : ℕ) : kP PP) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk PP.asIdeal)]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hN`.

Use `(hχ _ ?_ hxa 1 ?_).trans (map_one c)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 - idemAt PP) * (1 - idemAt PP + idemAt PP * (x : AE D)) = 1 - idemAt PP`. Take the linear combination `(-((x : AE D) - 1)) * he`. Rewrite using `[ha, map_add, map_sub, map_one, map_mul, hres, map_add, map_one, map_nsmul, nsmul_eq_mul, hN0]`. Simplify using the standard rewrite rules.
-/
theorem res_locU_eq_one {A : Type} [CommGroup A] {PP : Pl D.host.E} {χ : (AE D)ˣ →* A} {c : (kP PP)ˣ →* A}
    (hχ : IsResAt χ PP c) (hI : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) (N : ℕ)
    (hN : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (x : (AE D)ˣ) (hx : finPart D (x : AE D) ∈ intAE D)
    (y : Af D.host.F ⊗[D.host.F] D.host.E) (hy : y ∈ intAE D) (hxy : finPart D (x : AE D) - 1 = N • y) :
    χ (locU (idemAt PP) hI.1.1 x) = 1 := by
  have he : idemAt PP * idemAt PP = idemAt PP := hI.1.1
  have hfa := finPart_locU_mem he hx
  have hxa := GlobalTheory.IdemRes.toEAf_mem_of_finPart hfa
  obtain ⟨hE, hres⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (idemAt PP) PP hI
  obtain ⟨w, rfl⟩ := GlobalTheory.SplitDualLat.finPart_surjective (D := D) y
  have hX := GlobalTheory.IdemRes.toEAf_mem_of_finPart hx
  have hW := GlobalTheory.IdemRes.toEAf_mem_of_finPart hy
  have key0 : Formalism.IndefR.Datum.toEAf D ((x : AE D) - 1 - N • w) = 0 := by
    change Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D _) = 0
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul, hxy, sub_self, map_zero]
  have key : Formalism.IndefR.Datum.toEAf D (x : AE D) = 1 + N • Formalism.IndefR.Datum.toEAf D w := by
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_nsmul] at key0
    linear_combination key0
  have ha : (⟨Formalism.IndefR.Datum.toEAf D (locU (idemAt PP) he x : AE D), hxa⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      1 - ⟨_, hE⟩ + ⟨_, hE⟩ * (1 + N • ⟨_, hW⟩) := by
    apply Subtype.ext
    change Formalism.IndefR.Datum.toEAf D (1 - idemAt PP + idemAt PP * (x : AE D)) =
      1 - Formalism.IndefR.Datum.toEAf D (idemAt PP) + Formalism.IndefR.Datum.toEAf D (idemAt PP) *
        (1 + N • Formalism.IndefR.Datum.toEAf D w)
    rw [RingHom.map_add, RingHom.map_sub, RingHom.map_one, RingHom.map_mul, key]
  have hN0 : ((N : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hN
  refine (hχ _ ?_ hxa 1 ?_).trans (map_one c)
  · change (1 - idemAt PP) * (1 - idemAt PP + idemAt PP * (x : AE D)) = 1 - idemAt PP
    linear_combination (-((x : AE D) - 1)) * he
  · rw [ha, map_add, map_sub, map_one, map_mul, hres, map_add, map_one, map_nsmul, nsmul_eq_mul, hN0]
    simp

/- English proof (translation)
Introduce `D A _ PP χ κ ht N hN x hx hxy`. Take `⟨y, hy, hxy⟩` from `hxy`. Establish `hPP : PP ∈ ({PP} : Finset (Pl D.host.E))` using `Finset.mem_singleton_self PP`. Establish `hsp : SplitSet ({PP} : Finset (Pl D.host.E))` using `ht.split`. Establish `hI` using `hsp.isIdemAt hPP`.

Establish `he : idemAt PP * idemAt PP = idemAt PP` using `hI.1.1`. Establish `h0 : idemAt PP * cA D (idemAt PP) = 0` using `hsp.mul_conj hPP hPP`. Establish `hc : cA D (idemAt PP) * cA D (idemAt PP) = cA D (idemAt PP)` using `by rw [← RingHom.map_mul, he]`. Establish `hg : (1 - idemAt PP - cA D (idemAt PP)) * (1 - idemAt PP - cA D (idemAt PP)) = 1 - idemAt PP - cA D (idemAt PP)`. Take the linear combination `he + hc + 2 * h0`.

Establish `hres` using `ht.res PP hPP`. Establish `hx_eq : x = locU (idemAt PP) he x * locU (cA D (idemAt PP)) hc x * locU (1 - idemAt PP - cA D (idemAt PP)) hg x`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, coe_locU]`. Take the linear combination `((x : AE D) - 1) ^ 2 * he + ((x : AE D) - 1) ^ 2 * hc + (((x : AE D) - 1) ^ 2 - (1 - idemAt PP - cA D (idemAt PP)) * ((x : AE D) - 1) ^ 3) * h0`.

Establish `hA : χ (locU (idemAt PP) he x) = 1` using `res_locU_eq_one hres hI N hN x hx.2.1 y hy hxy`. Establish `hB : χ (locU (cA D (idemAt PP)) hc x) = 1`. Establish `hcb : Units.map (cA D).toMonoidHom (locU (cA D (idemAt PP)) hc x) = locU (idemAt PP) he (Units.map (cA D).toMonoidHom x)`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `cA D (1 - cA D (idemAt PP) + cA D (idemAt PP) * (x : AE D)) = 1 - idemAt PP + idemAt PP * cA D (x : AE D)`.

Rewrite using `[RingHom.map_add, RingHom.map_sub, RingHom.map_one, RingHom.map_mul, Formalism.L2.Theta.cA_cA]`. Establish `h1 : χ (locU (idemAt PP) he (Units.map (cA D).toMonoidHom x)) = 1`. Use `res_locU_eq_one hres hI N hN _ ?_ (sigR (Af D.host.F) D.sp.cm.sig y) (GlobalTheory.SplitDualLat.sigR_mem_intAE hy) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `finPart D (cA D (x : AE D)) ∈ intAE D`. Rewrite using `[GlobalTheory.SplitDualLat.finPart_cA]`.

Conclude with `GlobalTheory.SplitDualLat.sigR_mem_intAE hx.2.1`. Express the relevant statement in the definitionally equal form `finPart D (cA D (x : AE D)) - 1 = _`. Rewrite using `[GlobalTheory.SplitDualLat.finPart_cA, ← RingHom.map_one (sigR (Af D.host.F) D.sp.cm.sig), ← RingHom.map_sub, hxy, map_nsmul]`. Establish `hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x` using `fun x => star_star x`. Establish `htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x`.

Introduce `x`. Apply `(D.sp.cm.fixed _).1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `D.sp.cm.sig _ = _`. Rewrite using `[map_add, hσ, add_comm]`. Use `set b := locU (cA D (idemAt PP)) hc x with hb`.

Establish `hz : sigR (AF D.host.F) D.sp.cm.sig ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D) = ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D)`. Express the relevant statement in the definitionally equal form `cA D ((b : AE D) * cA D (b : AE D)) = (b : AE D) * cA D (b : AE D)`. Rewrite using `[RingHom.map_mul, Formalism.L2.Theta.cA_cA, mul_comm]`. Take `⟨a, ha⟩` from `GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr _ hz`. Establish `hr : χ (idF D a) = 1` using `ht.real a`.

Establish `ha' : idF D a = b * Units.map (cA D).toMonoidHom b` using `ha`. Rewrite `hr` using `[ha', map_mul, hcb, h1, mul_one]`. Conclude with `hr`. Establish `hC : χ (locU (1 - idemAt PP - cA D (idemAt PP)) hg x) = 1`. Establish `hi0 : infPart D (idemAt PP) = 0` using `SpecGood.infPart_eq_zero_of_isIdemAt D PP _ hI`.

Establish `hi1 : infPart D (cA D (idemAt PP)) = 0`. Rewrite using `[GlobalTheory.PlaceIdem.infPart_cA, hi0, RingHom.map_zero]`. Establish `hidem : idem ({PP} : Finset (Pl D.host.E)) = idemAt PP` using `Finset.sum_singleton _ _`. Use `ht.unram _ ?_ (finPart_locU_mem hg hx.2.1) ?_ ?_` and prove the remaining obligations. Rewrite using `[coe_locU, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_sub, RingHom.map_one, hi0, hi1, hx.1]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[locU_inv]`. Conclude with `finPart_locU_mem hg hx.2.2`. Express the relevant statement in the definitionally equal form `(idem ({PP} : Finset (Pl D.host.E)) + cA D (idem ({PP} : Finset (Pl D.host.E)))) * (1 - (1 - idemAt PP - cA D (idemAt PP)) + (1 - idemAt PP - cA D (idemAt PP)) * (x : AE D)) = _`. Rewrite using `[hidem]`.

Take the linear combination `(-((x : AE D) - 1)) * he + (-((x : AE D) - 1)) * hc + (-2 * ((x : AE D) - 1)) * h0`. Rewrite using `[hx_eq, map_mul, map_mul, hA, hB, hC, mul_one, mul_one]`.
-/
theorem chi_eq_one_of_cong : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := by
  intro D A _ PP χ κ ht N hN x hx hxy
  obtain ⟨y, hy, hxy⟩ := hxy
  have hPP : PP ∈ ({PP} : Finset (Pl D.host.E)) := Finset.mem_singleton_self PP
  have hsp : SplitSet ({PP} : Finset (Pl D.host.E)) := ht.split
  have hI := hsp.isIdemAt hPP
  have he : idemAt PP * idemAt PP = idemAt PP := hI.1.1
  have h0 : idemAt PP * cA D (idemAt PP) = 0 := hsp.mul_conj hPP hPP
  have hc : cA D (idemAt PP) * cA D (idemAt PP) = cA D (idemAt PP) := by rw [← RingHom.map_mul, he]
  have hg : (1 - idemAt PP - cA D (idemAt PP)) * (1 - idemAt PP - cA D (idemAt PP)) =
      1 - idemAt PP - cA D (idemAt PP) := by
    linear_combination he + hc + 2 * h0
  have hres := ht.res PP hPP

  have hx_eq : x = locU (idemAt PP) he x * locU (cA D (idemAt PP)) hc x *
      locU (1 - idemAt PP - cA D (idemAt PP)) hg x := by
    apply Units.ext
    simp only [Units.val_mul, coe_locU]
    linear_combination ((x : AE D) - 1) ^ 2 * he + ((x : AE D) - 1) ^ 2 * hc +
      (((x : AE D) - 1) ^ 2 - (1 - idemAt PP - cA D (idemAt PP)) * ((x : AE D) - 1) ^ 3) * h0

  have hA : χ (locU (idemAt PP) he x) = 1 := res_locU_eq_one hres hI N hN x hx.2.1 y hy hxy

  have hB : χ (locU (cA D (idemAt PP)) hc x) = 1 := by
    have hcb : Units.map (cA D).toMonoidHom (locU (cA D (idemAt PP)) hc x) =
        locU (idemAt PP) he (Units.map (cA D).toMonoidHom x) := by
      apply Units.ext
      change cA D (1 - cA D (idemAt PP) + cA D (idemAt PP) * (x : AE D)) = 1 - idemAt PP + idemAt PP * cA D (x : AE D)
      rw [RingHom.map_add, RingHom.map_sub, RingHom.map_one, RingHom.map_mul, Formalism.L2.Theta.cA_cA]
    have h1 : χ (locU (idemAt PP) he (Units.map (cA D).toMonoidHom x)) = 1 := by
      refine res_locU_eq_one hres hI N hN _ ?_ (sigR (Af D.host.F) D.sp.cm.sig y)
        (GlobalTheory.SplitDualLat.sigR_mem_intAE hy) ?_
      · change finPart D (cA D (x : AE D)) ∈ intAE D
        rw [GlobalTheory.SplitDualLat.finPart_cA]
        exact GlobalTheory.SplitDualLat.sigR_mem_intAE hx.2.1
      · change finPart D (cA D (x : AE D)) - 1 = _
        rw [GlobalTheory.SplitDualLat.finPart_cA, ← RingHom.map_one (sigR (Af D.host.F) D.sp.cm.sig), ← RingHom.map_sub, hxy,
          map_nsmul]
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      intro x
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add, hσ, add_comm]
    set b := locU (cA D (idemAt PP)) hc x with hb
    have hz : sigR (AF D.host.F) D.sp.cm.sig ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D) =
        ((b * Units.map (cA D).toMonoidHom b : (AE D)ˣ) : AE D) := by
      change cA D ((b : AE D) * cA D (b : AE D)) = (b : AE D) * cA D (b : AE D)
      rw [RingHom.map_mul, Formalism.L2.Theta.cA_cA, mul_comm]
    obtain ⟨a, ha⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr _ hz
    have hr : χ (idF D a) = 1 := ht.real a
    have ha' : idF D a = b * Units.map (cA D).toMonoidHom b := ha
    rw [ha', map_mul, hcb, h1, mul_one] at hr
    exact hr

  have hC : χ (locU (1 - idemAt PP - cA D (idemAt PP)) hg x) = 1 := by
    have hi0 : infPart D (idemAt PP) = 0 := SpecGood.infPart_eq_zero_of_isIdemAt D PP _ hI
    have hi1 : infPart D (cA D (idemAt PP)) = 0 := by
      rw [GlobalTheory.PlaceIdem.infPart_cA, hi0, RingHom.map_zero]
    have hidem : idem ({PP} : Finset (Pl D.host.E)) = idemAt PP := Finset.sum_singleton _ _
    refine ht.unram _ ?_ (finPart_locU_mem hg hx.2.1) ?_ ?_
    · rw [coe_locU, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_sub,
        RingHom.map_one, hi0, hi1, hx.1]
      ring
    · rw [locU_inv]
      exact finPart_locU_mem hg hx.2.2
    · change (idem ({PP} : Finset (Pl D.host.E)) + cA D (idem ({PP} : Finset (Pl D.host.E)))) *
        (1 - (1 - idemAt PP - cA D (idemAt PP)) + (1 - idemAt PP - cA D (idemAt PP)) * (x : AE D)) = _
      rw [hidem]
      linear_combination (-((x : AE D) - 1)) * he + (-((x : AE D) - 1)) * hc + (-2 * ((x : AE D) - 1)) * h0
  rw [hx_eq, map_mul, map_mul, hA, hB, hC, mul_one, mul_one]

end GlobalTheory.OnePlaceCong

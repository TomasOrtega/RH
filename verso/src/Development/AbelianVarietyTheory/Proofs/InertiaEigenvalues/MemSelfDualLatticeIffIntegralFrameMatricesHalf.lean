import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelOneClassEqClassicalShortSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeOfFrameMatrixIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivCoefNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.LatHalf

open GlobalTheory.ExportSeries
open Formalism.L2.DIV (Pl)

variable {D : D7}

/- English proof (translation)
Introduce `c hc`. Use `⟨Formalism.L2.DIV.starO c, ?_, Formalism.L2.DIV.starO_coe c⟩` and prove the remaining obligations. Use `show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO c) ∈ P.asIdeal`. Rewrite using `[Formalism.L2.DIV.starO_starO]`. Conclude with `hc`.
-/
theorem levConj_conjPl (P : Formalism.L2.DIV.Pl D.host.E) : Formalism.IndefR.Lev.IsConjPl P (Formalism.L2.DIV.conjPl P) := by
  intro c hc
  refine ⟨Formalism.L2.DIV.starO c, ?_, Formalism.L2.DIV.starO_coe c⟩
  show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO c) ∈ P.asIdeal
  rw [Formalism.L2.DIV.starO_starO]
  exact hc

/- English proof (translation)
Use `(HeightOneSpectrum.ext ?_).symm` and prove the remaining obligations. Use `Ideal.IsMaximal.eq_of_le (Formalism.L2.DIV.conjPl A).isMaximal B.isPrime.ne_top fun b hb => ?_` and prove the remaining obligations. Take `⟨c', hc', e⟩` from `h (Formalism.L2.DIV.starO b) hb`. Establish `: c' = b` using `RingOfIntegers.ext (by rw [e, Formalism.L2.DIV.starO_coe, star_star])`. Conclude with `this ▸ hc'`.
-/
theorem eq_conjPl_of_levConj {A B : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl A B) :
    B = Formalism.L2.DIV.conjPl A := by
  refine (HeightOneSpectrum.ext ?_).symm
  refine Ideal.IsMaximal.eq_of_le (Formalism.L2.DIV.conjPl A).isMaximal B.isPrime.ne_top fun b hb => ?_
  obtain ⟨c', hc', e⟩ := h (Formalism.L2.DIV.starO b) hb
  have : c' = b := RingOfIntegers.ext (by rw [e, Formalism.L2.DIV.starO_coe, star_star])
  exact this ▸ hc'

/- English proof (translation)
The claim follows from `GlobalTheory.MovedIdem.isIdemAt_conj h fun x => by rw [show Formalism.L2.Col.cO D.host.E x = Formalism.L2.DIV.starO x from RingOfIntegers.ext (by rw [Formalism.L2.DIV.starO_coe]; rfl)] rfl`.
-/
theorem isIdemAt_conjPl {e : AE D} {P : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e P) :
    Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.L2.DIV.conjPl P) :=
  GlobalTheory.MovedIdem.isIdemAt_conj h fun x => by
    rw [show Formalism.L2.Col.cO D.host.E x = Formalism.L2.DIV.starO x from RingOfIntegers.ext (by rw [Formalism.L2.DIV.starO_coe]; rfl)]
    rfl

/- English proof (translation)
Take `⟨P, h1, -, hP⟩` from `h.split`. Establish `hS` using `hP.mono h1`. Establish `hinj : Set.InjOn Formalism.L2.DIV.conjPl (Pg : Set (Pl D.host.E))` using `fun a _ b _ hab => by`. Rewrite using `[← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl]`. Establish `hc : ∀ PP ∈ Pg, idemAt (Formalism.L2.DIV.conjPl PP) = cA D (idemAt PP)` using `fun PP hPP => idemAt_eq (isIdemAt_conjPl (hS.isIdemAt hPP))`.

Establish `he : idem (Pg.image Formalism.L2.DIV.conjPl) = cA D (idem Pg)`. Rewrite using `[idem, Finset.sum_image hinj, idem, map_sum]`. Conclude with `Finset.sum_congr rfl hc`. Use `⟨he, ⟨⟨Pg.image Formalism.L2.DIV.conjPl, Finset.empty_subset _, le_rfl, ⟨idem (Pg.image Formalism.L2.DIV.conjPl), ⟨idemAt, ?_, rfl⟩, ?_⟩⟩, Finset.disjoint_empty_left _, ?_⟩⟩` and prove the remaining obligations. Introduce `PP hPP`.

Take `⟨P0, hP0, rfl⟩` from `Finset.mem_image.1 hPP`. Rewrite using `[hc P0 hP0]`. Conclude with `isIdemAt_conjPl (hS.isIdemAt hP0)`. Rewrite using `[he, GlobalTheory.DualPairCheck.cA_cA, mul_comm]`. Conclude with `hS.isIdemSum.2`.

Introduce `PP hPP PP' hPP'`. Take `⟨P0, hP0, rfl⟩` from `Finset.mem_image.1 (hPP.resolve_left (Finset.notMem_empty PP))`. Break down `hPP' with rfl | hc'` into its components or cases. Conclude with `h.prime P0 (Or.inl hP0) _ (Or.inr (levConj_conjPl P0))`. Rewrite using `[eq_conjPl_of_levConj hc', Formalism.L2.DIV.conjPl_conjPl]`.

Conclude with `h.prime P0 (Or.inl hP0) P0 (Or.inl rfl)`.
-/
theorem conj_placesOK {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) :
    idem (Pg.image Formalism.L2.DIV.conjPl) = cA D (idem Pg) ∧ PlacesOK ∅ (Pg.image Formalism.L2.DIV.conjPl) := by
  obtain ⟨P, h1, -, hP⟩ := h.split
  have hS := hP.mono h1
  have hinj : Set.InjOn Formalism.L2.DIV.conjPl (Pg : Set (Pl D.host.E)) := fun a _ b _ hab => by
    rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl]
  have hc : ∀ PP ∈ Pg, idemAt (Formalism.L2.DIV.conjPl PP) = cA D (idemAt PP) := fun PP hPP =>
    idemAt_eq (isIdemAt_conjPl (hS.isIdemAt hPP))
  have he : idem (Pg.image Formalism.L2.DIV.conjPl) = cA D (idem Pg) := by
    rw [idem, Finset.sum_image hinj, idem, map_sum]
    exact Finset.sum_congr rfl hc
  refine ⟨he, ⟨⟨Pg.image Formalism.L2.DIV.conjPl, Finset.empty_subset _, le_rfl,
    ⟨idem (Pg.image Formalism.L2.DIV.conjPl), ⟨idemAt, ?_, rfl⟩, ?_⟩⟩, Finset.disjoint_empty_left _, ?_⟩⟩
  · intro PP hPP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hPP
    rw [hc P0 hP0]
    exact isIdemAt_conjPl (hS.isIdemAt hP0)
  · rw [he, GlobalTheory.DualPairCheck.cA_cA, mul_comm]
    exact hS.isIdemSum.2
  · intro PP hPP PP' hPP'
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 (hPP.resolve_left (Finset.notMem_empty PP))
    rcases hPP' with rfl | hc'
    · exact h.prime P0 (Or.inl hP0) _ (Or.inr (levConj_conjPl P0))
    · rw [eq_conjPl_of_levConj hc', Formalism.L2.DIV.conjPl_conjPl]
      exact h.prime P0 (Or.inl hP0) P0 (Or.inl rfl)

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.split.imp fun _ hP => ⟨Finset.empty_subset _, hP.2.1, hP.2.2⟩, Finset.disjoint_empty_left _, fun PP hPP => h.prime PP (Or.inr (hPP.resolve_left (Finset.notMem_empty PP)))⟩`.
-/
theorem goodPosition_auxiliaryPlaces_alone {Pg Q : Finset (Pl D.host.E)} (h : PlacesOK Pg Q) : PlacesOK ∅ Q :=
  ⟨h.split.imp fun _ hP => ⟨Finset.empty_subset _, hP.2.1, hP.2.2⟩, Finset.disjoint_empty_left _,
    fun PP hPP => h.prime PP (Or.inr (hPP.resolve_left (Finset.notMem_empty PP)))⟩

/- English proof (translation)
Use `h.isOrthSum.1.idem` as an intermediate fact. Rewrite `this` using `[halfIdem, idem_empty, map_zero, zero_add]`. Then use the resulting hypothesis.
-/
theorem idem_sq {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) : idem R * idem R = idem R := by
  have := h.isOrthSum.1.idem
  rwa [halfIdem, idem_empty, map_zero, zero_add] at this

/- English proof (translation)
Take `⟨P, -, h2, hP⟩` from `h.split`. Use `GlobalTheory.DatumFourier.idem_div_int (hP.mono h2).isIdemSum one_ne_zero fun PP _ hPP => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hPP))` as an intermediate fact. Simplify using `using this`.
-/
theorem toEAf_idem_int {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) :
    toEAf D (idem R) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, -, h2, hP⟩ := h.split
  have := GlobalTheory.DatumFourier.idem_div_int (hP.mono h2).isIdemSum one_ne_zero fun PP _ hPP =>
    PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hPP))
  simpa using this

/- English proof (translation)
Unfold `frMapO`. Rewrite using `[Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]`.
-/
theorem frMapO_add {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
Unfold `frMapO`. Establish `: (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D)` using `Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]`. Rewrite using `[this, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem frMapO_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T) :
    frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Introduce `i j` and use `by show e * (e * x i j) = e * x i j rw [← mul_assoc, he]`.
-/
theorem isHalf_smul {m n : ℕ} {e : AE D} (he : e * e = e) (x : Mx D m n) : IsHalf e (e • x) := fun i j => by
  show e * (e * x i j) = e * x i j
  rw [← mul_assoc, he]

/- English proof (translation)
Use `GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral hF hR (isHalf_smul (idem_sq hR) x) ?_` and prove the remaining obligations. Rewrite using `[frMapO_smul]`. Conclude with `fun i j => by`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Conclude with `mul_mem (toEAf_idem_int hR) (hi i j)`.
-/
theorem mem_lat_piece {S T : HSp D} {F : Frame S T} (hF : F.Good) {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R)
    (x : WO S T) (hi : IsIntM (frMapO S T F.βS F.βT x)) : idem R • x ∈ F.lat := by
  refine GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral hF hR (isHalf_smul (idem_sq hR) x) ?_
  rw [frMapO_smul]
  exact fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (toEAf_idem_int hR) (hi i j)

/- English proof (translation)
Introduce `D S T F hF Pg Q h _ x hx`. Take `⟨hR1, hR⟩` from `conj_placesOK h`. Establish `hQ` using `goodPosition_auxiliaryPlaces_alone h`. Establish `hxe : x = idem (Pg.image Formalism.L2.DIV.conjPl) • x + idem Q • x`. Rewrite using `[← add_smul, hR1]`.

Conclude with `(Matrix.ext fun i j => hx i j).symm`. Prove the components needed by the constructor for the conclusion. Introduce `hl`. Take `⟨o1, a1⟩` from `GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hR (isHalf_smul (idem_sq hR) x) (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hR) hl)`. Take `⟨o2, a2⟩` from `GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hQ (isHalf_smul (idem_sq hQ) x) (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hQ) hl)`.

Rewrite using `[hxe, GlobalTheory.PlaceVec.frMapAdj_add, frMapO_add]`. Conclude with `⟨fun i j => add_mem (a1 i j) (a2 i j), fun i j => add_mem (o1 i j) (o2 i j)⟩`. Introduce and unpack `⟨-, hi⟩`. Rewrite using `[hxe]`. Conclude with `add_mem (mem_lat_piece hF hR x hi) (mem_lat_piece hF hQ x hi)`.
-/
theorem mem_lat_iff_isIntM_halfIdem : ∀ {D : D7} {S T : HSp D} {F : GlobalTheory.ExportSeries.Frame S T}, F.Good →
    ∀ {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}, GlobalTheory.ExportSeries.PlacesOK Pg Q →
    (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) →
    ∀ {x : WO S T}, IsHalf (GlobalTheory.ExportSeries.halfIdem Pg Q) x →
      (x ∈ F.lat ↔ IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)) := by
  intro D S T F hF Pg Q h _ x hx
  obtain ⟨hR1, hR⟩ := conj_placesOK h
  have hQ := goodPosition_auxiliaryPlaces_alone h
  have hxe : x = idem (Pg.image Formalism.L2.DIV.conjPl) • x + idem Q • x := by
    rw [← add_smul, hR1]
    exact (Matrix.ext fun i j => hx i j).symm
  constructor
  · intro hl
    obtain ⟨o1, a1⟩ := GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hR (isHalf_smul (idem_sq hR) x)
      (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hR) hl)
    obtain ⟨o2, a2⟩ := GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hQ (isHalf_smul (idem_sq hQ) x)
      (GlobalTheory.PlaceModelSum.idem_smul_latO (idem_sq hQ) hl)
    rw [hxe, GlobalTheory.PlaceVec.frMapAdj_add, frMapO_add]
    exact ⟨fun i j => add_mem (a1 i j) (a2 i j), fun i j => add_mem (o1 i j) (o2 i j)⟩
  · rintro ⟨-, hi⟩
    rw [hxe]
    exact add_mem (mem_lat_piece hF hR x hi) (mem_lat_piece hF hQ x hi)

end GlobalTheory.ExportSeries.LatHalf

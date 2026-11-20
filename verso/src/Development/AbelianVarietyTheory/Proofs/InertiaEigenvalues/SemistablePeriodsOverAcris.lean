import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EcoefQNormLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPeriodMatrixOverAcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFactsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.CrisPeriods

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus (I := Ideal.span {(l : R)}) inferInstance _ fun n => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton.1 (PadicInt.appr_spec n z)`. Establish `hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * y` using `by rw [← hy]; ring`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Use `⟨f y - g y, ?_⟩` and prove the remaining obligations. Establish `hf` using `congrArg f hz`. Establish `hg` using `congrArg g hz`. Rewrite `hf`, `hg` using `[map_add, map_mul, map_pow, map_natCast, map_natCast]`. Rewrite using `[hf, hg]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem padicInt_hom_ext {R : Type} [CommRing R] [IsHausdorff (Ideal.span {(l : R)}) R]
    (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {(l : R)}) inferInstance _ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n z)
  have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * y := by rw [← hy]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨f y - g y, ?_⟩
  have hf := congrArg f hz
  have hg := congrArg g hz
  rw [map_add, map_mul, map_pow, map_natCast, map_natCast] at hf hg
  rw [hf, hg]
  ring

/- English proof (translation)
The claim follows from `haveI : IsHausdorff (Ideal.span {(l : Ainf l)}) (Ainf l) := (WittVector.isAdicCompleteIdealSpanP (p := l) (k := Per.Fl l)).toIsHausdorff padicInt_hom_ext (R := Ainf l) (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) z`.
-/
private theorem zA_eq_alg (z : ℤ_[l]) : Per.zA l z = algebraMap ℤ_[l] (Ainf l) z :=
  haveI : IsHausdorff (Ideal.span {(l : Ainf l)}) (Ainf l) :=
    (WittVector.isAdicCompleteIdealSpanP (p := l) (k := Per.Fl l)).toIsHausdorff
  padicInt_hom_ext (R := Ainf l) (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) z

/- English proof (translation)
Rewrite using `[GlobalTheory.MemLoc.ULaws.alg_acris, C.j_cris.on0]`. Both sides reduce to the same expression.
-/
private theorem j_alg (C : Core l) (a : Ainf l) : C.j (algebraMap (Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [GlobalTheory.MemLoc.ULaws.alg_acris, C.j_cris.on0]
  rfl

/- English proof (translation)
Apply `GlobalTheory.MemLoc.ULaws.iota_injective C` to reduce the goal to its premises. Rewrite using `[C.ι_j, j_alg, GlobalTheory.MemLoc.ULaws.iota_aB]`.
-/
private theorem alg_alg_eq_aB (C : Core l) (a : Ainf l) :
    algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Ainf l) (Per.Acris l) a) = Per.aB l a := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [C.ι_j, j_alg, GlobalTheory.MemLoc.ULaws.iota_aB]

/- English proof (translation)
Apply `GlobalTheory.MemLoc.ULaws.iota_injective C` to reduce the goal to its premises. Rewrite using `[← GlobalTheory.MemLoc.ULaws.u_padicInt C, GlobalTheory.MemLoc.ULaws.iota_aB, C.ι_u, ← C.o_sec.z]`. Both sides reduce to the same expression.
-/
private theorem aB_zA (C : Core l) (z : ℤ_[l]) : Per.aB l (Per.zA l z) = Per.zB l z := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [← GlobalTheory.MemLoc.ULaws.u_padicInt C, GlobalTheory.MemLoc.ULaws.iota_aB, C.ι_u, ← C.o_sec.z]
  rfl

/- English proof (translation)
Establish `hz : ∀ w : ℤ_[l], algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Ainf l) (Per.Acris l) (Per.zA l w)) = Per.zB l w` using `fun w => (alg_alg_eq_aB C _).trans (aB_zA C w)`. Establish `hM : (Mn.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map (algebraMap (Per.Acris l) (Per.Bcris l)) = Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]`. Conclude with `alg_alg_eq_aB C _`.

Establish `he : ∀ i ∈ Finset.range d, Per.zB l (GlobalTheory.SstPer.ecoef l k₀ k i) = (l : Per.Bcris l) ^ k₀ * C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹)`. Introduce `i hi`. Rewrite using `[← (GlobalTheory.MemLoc.ULaws.u_laws l C).2.2.1, GlobalTheory.SstPer.ecoef_val (hn i (Finset.mem_range.1 hi))]`. Use `show C.qB _ = _`. Rewrite using `[GlobalTheory.SstPer.ecoefQ, map_mul, map_pow, map_natCast]`.

Unfold `GlobalTheory.SstPer.kap`. Rewrite using `[← RingHom.mapMatrix_apply, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[RingHom.mapMatrix_apply, map_smul_ring, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply, hM, smul_smul]`. Use `congr 1`.

Rewrite using `[map_mul, map_pow, map_mul, hz, hz, he i hi, Core.tB]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kap_map (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a))
    (z : ℤ_[l]) (hn : ∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) :
    (GlobalTheory.SstPer.kap C bk k₀ k Mn z).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
      (l : Per.Bcris l) ^ k₀ • ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) *
        (Per.zB l z * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i := by
  have hz : ∀ w : ℤ_[l], algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Ainf l) (Per.Acris l) (Per.zA l w)) =
      Per.zB l w := fun w => (alg_alg_eq_aB C _).trans (aB_zA C w)
  have hM : (Mn.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map
      (algebraMap (Per.Acris l) (Per.Bcris l)) = Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
    ext i j
    simp only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]
    exact alg_alg_eq_aB C _
  have he : ∀ i ∈ Finset.range d, Per.zB l (GlobalTheory.SstPer.ecoef l k₀ k i) =
      (l : Per.Bcris l) ^ k₀ * C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) := by
    intro i hi
    rw [← (GlobalTheory.MemLoc.ULaws.u_laws l C).2.2.1, GlobalTheory.SstPer.ecoef_val (hn i (Finset.mem_range.1 hi))]
    show C.qB _ = _
    rw [GlobalTheory.SstPer.ecoefQ, map_mul, map_pow, map_natCast]
  unfold GlobalTheory.SstPer.kap
  rw [← RingHom.mapMatrix_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [RingHom.mapMatrix_apply, map_smul_ring, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply, hM,
    smul_smul]
  congr 1
  rw [map_mul, map_pow, map_mul, hz, hz, he i hi, Core.tB]
  ring

end GlobalTheory.CrisPeriods

namespace GlobalTheory.CrisPeriods

/- English proof (translation)
Introduce `l _ K bk P AI T C _hFits d ρ U U' hUU' c₁ F hφ k k₀ Mn c hn hgal`. Establish `hA` using `(GlobalTheory.MemLoc.AwayT.away_and_inj l C).1`. Take `⟨_, _, -, -, -, hFilt, -⟩` from `GlobalTheory.MemLoc.BdRDVR.core_dvr l C`. Take `⟨-, hmul, -, hiff, -, -, hinj⟩` from `GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (xi C.ε) C.ker_theta.symm`. Establish `AL` using `GlobalTheory.MemLoc.ActLaws.act_laws l`.

Take `⟨N₁, h₁⟩` from `exists_lift C hA U`. Take `⟨N₂, h₂⟩` from `exists_lift C hA U'`. Use `⟨max N₁ N₂, fun N hN X X' hX hX' => ?_⟩` and prove the remaining obligations. Take `⟨Z, hZ⟩` from `h₁ N (le_of_max_le_left hN)`. Take `⟨Z', hZ'⟩` from `h₂ N (le_of_max_le_right hN)`.

Establish `hmi : Function.Injective (fun M : Matrix (Fin d) (Fin d) (Per.Acris l) => M.map (algebraMap (Per.Acris l) (Per.Bcris l)))` using `Matrix.map_injective hinj`. Establish `hXm : ∀ Y : Matrix (Fin d) (Fin d) bk.S, ((Y.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))).map C.ι = Y.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))`. Introduce `Y`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, RingHom.comp_apply]`.

Rewrite using `[C.ι_j]`. Use `congr 1`. Conclude with `j_alg C _`. Establish `htN : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ^ N ∈ Per.FilD l N`. Rewrite using `[C.ι_j, ← map_pow, hiff, hFilt]`.

Conclude with `Ideal.mem_span_singleton_self _`. Use `⟨Z, Z', ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `hmi` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Matrix.map_mul, hZ, hZ', map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), smul_mul_smul_comm, hUU', map_pow, ← pow_add, two_mul]`.

Apply `hmi` to reduce the goal to its premises. Simplify using `only`. Establish `hZφ : (Z.map (phiA l)).map (algebraMap (Per.Acris l) (Per.Bcris l)) = (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.φB l)`. Use extensionality with `i j`. Conclude with `(AL.2.2.2.2.2.2.2.2.2.2.2.2 (Z i j)).symm`.

Establish `hFm : (F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map (algebraMap (Per.Acris l) (Per.Bcris l)) = F.map ((Per.aB l).comp (wA l bk.a).toRingHom)`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]`. Conclude with `alg_alg_eq_aB C _`. Establish `ht : algebraMap (Per.Acris l) (Per.Bcris l) (phiA l C.t) = Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) C.t)` using `(AL.2.2.2.2.2.2.2.2.2.2.2.2 C.t).symm`.

Rewrite using `[map_smul_ring, hZφ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hFm, hZ, map_pow, map_pow, ht, Matrix.smul_mul, ← hφ]`. Simplify using `only [map_mul, map_pow, map_natCast, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Introduce `g`.

Apply `hmi` to reduce the goal to its premises. Simplify using `only`. Establish `hZσ : (Z.map (sigA (g : GQ l))).map (algebraMap (Per.Acris l) (Per.Bcris l)) = (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.σB (g : GQ l))`. Use extensionality with `i j`. Conclude with `(AL.2.2.2.2.2.2.2.2.2.2.2.1 _ (Z i j)).symm`.

Establish `hρ : ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))).map (algebraMap (Per.Acris l) (Per.Bcris l)) = (ρ g).map (Per.zB l)`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, RingHom.comp_apply]`. Rewrite using `[alg_alg_eq_aB C, ← zA_eq_alg, aB_zA C]`. Establish `ht : algebraMap (Per.Acris l) (Per.Bcris l) (sigA (g : GQ l) C.t) = Per.σB (g : GQ l) (algebraMap (Per.Acris l) (Per.Bcris l) C.t)` using `(AL.2.2.2.2.2.2.2.2.2.2.2.1 _ C.t).symm`.

Rewrite using `[map_smul_ring, Matrix.map_mul, hρ, hZσ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hZ, kap_map C bk k₀ k Mn (c g) hn]`. Simplify using `only [map_pow, map_mul, map_natCast, ht]`. Rewrite using `[Matrix.mul_smul, hgal g, Matrix.smul_mul, Matrix.mul_smul]`. Simplify using `only [smul_smul, Core.tB]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Introduce `i j`. Rewrite using `[← hiff, ← C.ι_j]`. Establish `e : algebraMap (Per.Acris l) (Per.Bcris l) ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) = ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))) i j`. Both sides reduce to the same expression.

Rewrite using `[e, Matrix.map_mul, hZ, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]`. Establish `e2 : C.ι ((U * (X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))) i j) = (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j`. Rewrite using `[← hXm]`. Conclude with `congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j`. Rewrite using `[e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]`.

Conclude with `hmul _ _ _ _ htN (hX i j)`. Introduce `i j`. Rewrite using `[← hiff, ← C.ι_j]`. Establish `e : algebraMap (Per.Acris l) (Per.Bcris l) ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) = ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z').map (algebraMap (Per.Acris l) (Per.Bcris l))) i j`. Both sides reduce to the same expression.

Rewrite using `[e, Matrix.map_mul, hZ', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]`. Establish `e2 : C.ι (((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l)) * U') i j) = (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j`. Rewrite using `[← hXm]`. Conclude with `congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j`. Rewrite using `[e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]`.

Conclude with `hmul _ _ _ _ htN (hX' i j)`.
-/
theorem periods_over_Acris_sst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) → ∀ (k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * GlobalTheory.SstPer.kap C bk k₀ k Mn (c g))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) := by
  intro l _ K bk P AI T C _hFits d ρ U U' hUU' c₁ F hφ k k₀ Mn c hn hgal
  have hA := (GlobalTheory.MemLoc.AwayT.away_and_inj l C).1
  obtain ⟨_, _, -, -, -, hFilt, -⟩ := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
  obtain ⟨-, hmul, -, hiff, -, -, hinj⟩ := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (xi C.ε) C.ker_theta.symm
  have AL := GlobalTheory.MemLoc.ActLaws.act_laws l
  obtain ⟨N₁, h₁⟩ := exists_lift C hA U
  obtain ⟨N₂, h₂⟩ := exists_lift C hA U'
  refine ⟨max N₁ N₂, fun N hN X X' hX hX' => ?_⟩
  obtain ⟨Z, hZ⟩ := h₁ N (le_of_max_le_left hN)
  obtain ⟨Z', hZ'⟩ := h₂ N (le_of_max_le_right hN)
  have hmi : Function.Injective
      (fun M : Matrix (Fin d) (Fin d) (Per.Acris l) => M.map (algebraMap (Per.Acris l) (Per.Bcris l))) :=
    Matrix.map_injective hinj
  have hXm : ∀ Y : Matrix (Fin d) (Fin d) bk.S,
      ((Y.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))).map C.ι =
        Y.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) := by
    intro Y
    ext i j
    simp only [Matrix.map_apply, RingHom.comp_apply]
    rw [C.ι_j]
    congr 1
    exact j_alg C _
  have htN : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ^ N ∈ Per.FilD l N := by
    rw [C.ι_j, ← map_pow, hiff, hFilt]
    exact Ideal.mem_span_singleton_self _
  refine ⟨Z, Z', ?_, ?_, ?_, ?_, ?_⟩
  · apply hmi
    simp only
    rw [Matrix.map_mul, hZ, hZ', map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), smul_mul_smul_comm,
      hUU', map_pow, ← pow_add, two_mul]
  · apply hmi
    simp only
    have hZφ : (Z.map (phiA l)).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
        (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.φB l) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.2 (Z i j)).symm
    have hFm : (F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) = F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]
      exact alg_alg_eq_aB C _
    have ht : algebraMap (Per.Acris l) (Per.Bcris l) (phiA l C.t) =
        Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.2 C.t).symm
    rw [map_smul_ring, hZφ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hFm, hZ, map_pow, map_pow, ht,
      Matrix.smul_mul, ← hφ]
    simp only [map_mul, map_pow, map_natCast, smul_smul]
    congr 1
    ring
  · intro g
    apply hmi
    simp only
    have hZσ : (Z.map (sigA (g : GQ l))).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
        (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.σB (g : GQ l)) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ (Z i j)).symm
    have hρ : ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) = (ρ g).map (Per.zB l) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply]
      rw [alg_alg_eq_aB C, ← zA_eq_alg, aB_zA C]
    have ht : algebraMap (Per.Acris l) (Per.Bcris l) (sigA (g : GQ l) C.t) =
        Per.σB (g : GQ l) (algebraMap (Per.Acris l) (Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ C.t).symm
    rw [map_smul_ring, Matrix.map_mul, hρ, hZσ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hZ,
      kap_map C bk k₀ k Mn (c g) hn]
    simp only [map_pow, map_mul, map_natCast, ht]
    rw [Matrix.mul_smul, hgal g, Matrix.smul_mul, Matrix.mul_smul]
    simp only [smul_smul, Core.tB]
    congr 1
    ring
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (Per.Acris l) (Per.Bcris l) ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) =
        ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι ((U * (X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map
        (algebraMap (Per.Acris l) (Per.Bcris l))) i j) =
        (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX i j)
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (Per.Acris l) (Per.Bcris l) ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) =
        ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z').map (algebraMap (Per.Acris l) (Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι (((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) * U') i j) =
        (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX' i j)

end GlobalTheory.CrisPeriods

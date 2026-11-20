import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsModificationOfFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKTwist
variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Take `⟨-, h2, h3, -, -⟩` from `GlobalTheory.MemLoc.thetaD_props l`. Establish `hmap : A.map (Per.θD l) = ((l : Per.BdRp l) ^ k • Λ₀).map (Per.θD l)`. Use extensionality with `i j`. Use `(h2 _).2 (hD i j)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`.

Simplify using `using this`. Establish `hl : Per.θD l (l : Per.BdRp l) ≠ 0`. Rewrite using `[map_natCast]`. Conclude with `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Establish `hdet` using `congrArg (fun M => Per.θD l M.det) hAA`.

Simplify using `only [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, map_mul, map_pow] at hdet`. Establish `hA : Per.θD l A.det ≠ 0`. Introduce `h0`. Rewrite `hdet` using `[h0, zero_mul]`. Conclude with `pow_ne_zero _ (pow_ne_zero _ hl) hdet.symm`.

Establish `e1 : Per.θD l A.det = Per.θD l (((l : Per.BdRp l) ^ k • Λ₀).det)`. Rewrite using `[RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hmap]`. Rewrite `hA` using `[e1, Matrix.det_smul, map_mul]`. Conclude with `h3 _ (right_ne_zero_of_mul hA)`.
-/
theorem isUnit_det_of_approx {d : ℕ} (Λ₀ A A' : Matrix (Fin d) (Fin d) (Per.BdRp l)) (k : ℕ)
    (hAA : A * A' = ((l : Per.BdRp l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)))
    (hD : ∀ i j, (A - (l : Per.BdRp l) ^ k • Λ₀) i j ∈ Per.FilP l 1) : IsUnit Λ₀.det := by
  obtain ⟨-, h2, h3, -, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  have hmap : A.map (Per.θD l) = ((l : Per.BdRp l) ^ k • Λ₀).map (Per.θD l) := by
    ext i j
    have := (h2 _).2 (hD i j)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    simpa using this
  have hl : Per.θD l (l : Per.BdRp l) ≠ 0 := by
    rw [map_natCast]; exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hdet := congrArg (fun M => Per.θD l M.det) hAA
  simp only [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, map_mul, map_pow] at hdet
  have hA : Per.θD l A.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero _ (pow_ne_zero _ hl) hdet.symm
  have e1 : Per.θD l A.det = Per.θD l (((l : Per.BdRp l) ^ k • Λ₀).det) := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hmap]
  rw [e1, Matrix.det_smul, map_mul] at hA
  exact h3 _ (right_ne_zero_of_mul hA)

/- English proof (translation)
Rewrite using `[PadicInt.unitCoeff_spec hy, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]`. Conclude with `((PadicInt.unitCoeff hy).isUnit.map _).map _ |>.mul ((isUnit_l_BdRp l).pow _)`.
-/
theorem isUnit_aDp_zA' {y : ℤ_[l]} (hy : y ≠ 0) : IsUnit (aDp l (Per.zA l y)) := by
  rw [PadicInt.unitCoeff_spec hy, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
  exact ((PadicInt.unitCoeff hy).isUnit.map _).map _ |>.mul ((isUnit_l_BdRp l).pow _)

/- English proof (translation)
Rewrite using `[map_mul]`. Use `congr 1`. Simplify using `only [Core.oD, RingHom.comp_apply, C.o_sec.z]`.
-/
theorem oD_int' (C : Core l) (y : ℤ_[l]) (x : Om l) :
    C.oD (algebraMap ℚ_[l] (Om l) (y : ℚ_[l]) * x) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * C.oD x := by
  rw [map_mul]
  congr 1
  simp only [Core.oD, RingHom.comp_apply, C.o_sec.z]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Ideal.sum_mem _ fun t _ => Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (hB s t)`.
-/
theorem mul_mem_ideal {R : Type} [CommRing R] {d : ℕ} (I : Ideal R) (A B C : Matrix (Fin d) (Fin d) R)
    (hB : ∀ i j, B i j ∈ I) (i j : Fin d) : (A * B * C) i j ∈ I := by
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun t _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (hB s t)

end GlobalTheory.BKTwist

namespace GlobalTheory.BKTwist

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `l _ K bk C hI d ρ H U U' Λ₀ hUU' hinv happ N₀`. Take `⟨hFilP, hmul, hanti, hP, hbd, hxi, -⟩` from `GlobalTheory.MemLoc.seed_fil l C (bk.ev bk.E) bk.span_ev`. Establish `hmap0 : ∀ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l 0`. Introduce `z`. Use `(hP 0 z).2 (by rw [hFilP 0, pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top)` as an intermediate fact.

Simplify using `using this`. Take `⟨k1, Λ1, Λ1', h1, hD1⟩` from `happ 1`. Establish `hdet : IsUnit Λ₀.det`. Use `isUnit_det_of_approx Λ₀ (Λ1.map ((aDp l).comp bk.ev)) (Λ1'.map ((aDp l).comp bk.ev)) k1 ?_ hD1` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, h1, GlobalTheory.BKModif.map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _)]`.

Simplify using the standard rewrite rules. Establish `hΛ : Λ₀ * Λ₀⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hdet`. Take `⟨Q₀, hQ₀⟩ : ∃ Q : Matrix (Fin d) (Fin d) (Per.BdR l), Q = U * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))` from `⟨_, rfl⟩`. Take `⟨Q₀', hQ₀'⟩ : ∃ Q : Matrix (Fin d) (Fin d) (Per.BdR l), Q = Λ₀⁻¹.map (algebraMap (Per.BdRp l) (Per.BdR l)) * U'` from `⟨_, rfl⟩`. Establish `hQQ : Q₀ * Q₀' = 1`.

Rewrite using `[hQ₀, hQ₀', Matrix.mul_assoc, ← Matrix.mul_assoc (Λ₀.map _), ← Matrix.map_mul, hΛ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, hUU']`. Establish `hQQ' : Q₀' * Q₀ = 1` using `mul_eq_one_comm.1 hQQ`. Establish `hinvQ₀ : ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q₀.map (Per.σD (g : GQ l)) = Q₀` using `fun g => by`. Rewrite using `[hQ₀]`. Conclude with `hinv g`.

Establish `hρ : ∀ g : ↥(GK K), ((ρ g).map (zOm l)).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) = (ρ g).map (Per.zD l)`. Introduce `g`. Use extensionality with `i j`. Simplify using `[zOm, GlobalTheory.RingIface.zD_alg, C.o_sec.z, aDp]`. Establish `hinvQ : ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * H.Q.map (Per.σD (g : GQ l)) = H.Q` using `fun g => by`.

Rewrite using `[← hρ g]`. Conclude with `H.inv g g.2`. Take `⟨c, hc⟩ : ∃ c : Matrix (Fin d) (Fin d) (Per.BdR l), c = Q₀' * H.Q` from `⟨_, rfl⟩`. Establish `hcσ : ∀ g : ↥(GK K), c.map (Per.σD (g : GQ l)) = c`. Introduce `g`.

Establish `hσ1 : Q₀.map (Per.σD (g : GQ l)) * Q₀'.map (Per.σD (g : GQ l)) = 1`. Rewrite using `[← Matrix.map_mul, hQQ, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `key : Q₀ * c.map (Per.σD (g : GQ l)) = H.Q`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Establish `hx : ∀ i j, ∃ x ∈ K.1, C.oD x = c i j` using `fun i j => hI K (c i j) (fun g hg => by`. Use `congrFun (congrFun (hcσ ⟨g, hg⟩) i) j` as an intermediate fact. Simplify using `using this)`. Use `choose x hxK hxc using hx`. Use `haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2`.

Take `⟨y, hy0, hint⟩` from `exists_integral_multiples ℤ_[l] ℚ_[l] (Finset.univ.image fun p : Fin d × Fin d => (⟨x p.1 p.2, hxK p.1 p.2⟩ : ↥K.1))`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z : Matrix (Fin d) (Fin d) ↥(OL K), ∀ i j, z.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) i j = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * c i j := by`. Use `⟨fun i j => ⟨y • ⟨x i j, hxK i j⟩, hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))⟩, fun i j => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `C.oD (K.1.val.toRingHom ((OL K).val.toRingHom _)) = _`. Rewrite using `[← hxc, ← oD_int']`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `((y • (⟨x i j, hxK i j⟩ : ↥K.1) : ↥K.1) : Om l) = _`. Rewrite using `[← algebraMap_smul ℚ_[l] y, Algebra.smul_def]`. Simplify using the standard rewrite rules. Establish `hu` using `isUnit_aDp_zA' hy0`.

Take `⟨w, hw⟩` from `hu.exists_right_inv`. Establish `hξ : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)))`. Establish `hk : Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)}` using `ker_localizedTheta_eq_span_of_dvd l (bk.ev bk.E) fun a => by`. Rewrite using `[← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]`. Establish `hun` using `GlobalTheory.RingIface.isUnit_of_generator l hk`.

Rewrite `hun` using `[GlobalTheory.RingIface.pD_eq_alg]`. Simplify `hun` using `only [aDp, RingHom.comp_apply]`. Take `⟨ξi, hξi⟩` from `hξ.exists_right_inv`. Establish `hQform : H.Q = H.V.map (algebraMap (Per.BdRp l) (Per.BdR l)) * Matrix.diagonal (fun j => ξi ^ H.q * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p j)`. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_diagonal, Matrix.map_apply]`. Use `H.Q_eq i j` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_pow, mul_comm ξi, hξi, one_pow, one_mul]`. Use `_ = ξi ^ H.q * (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * H.Q i j) := by ring`.

Use `_ = _ := by rw [this, map_mul, map_pow]; ring`. Establish `hVdet : IsUnit H.V.det` using `(Matrix.isUnit_iff_isUnit_det H.V).1 H.unit`. Take `⟨Qi, hQi⟩ : ∃ Qi : Matrix (Fin d) (Fin d) (Per.BdR l), Qi = Matrix.diagonal (fun i => algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * ξi ^ H.p i) * H.V⁻¹.map (algebraMap (Per.BdRp l) (Per.BdR l))` from `⟨_, rfl⟩`. Establish `hQQi : H.Q * Qi = 1`. Rewrite using `[hQform, hQi, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]`.

Establish `: (fun j => ξi ^ H.q * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p j * (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * ξi ^ H.p j)) = fun _ => 1`. Use function extensionality and compare the values at `j`. Rewrite using `[show ξi ^ H.q * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p j * (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * ξi ^ H.p j) = (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * ξi) ^ H.q * (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l …`. Rewrite using `[this, Matrix.diagonal_one, Matrix.one_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hVdet, Matrix.map_one _ (map_zero _) (map_one _)]`. Take `⟨β, hβ⟩ : ∃ β : Matrix (Fin d) (Fin d) (Per.BdR l), β = algebraMap (Per.BdRp l) (Per.BdR l) w • Qi` from `⟨_, rfl⟩`.

Take `⟨kk, hkk⟩ : ∃ kk : Fin d → ℤ, kk = fun i => (H.p i : ℤ) - H.q` from `⟨_, rfl⟩`. Establish `hcmap : z.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) • c`. Use extensionality with `i j`. Rewrite using `[hz, Matrix.smul_apply, smul_eq_mul]`. Establish `hQ₀c : Q₀ * z.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) • H.Q`.

Rewrite using `[hcmap, Matrix.mul_smul, hc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]`. Establish `hprod : Q₀ * z.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1`. Rewrite using `[hQ₀c, hβ, Matrix.smul_mul, Matrix.mul_smul, hQQi, smul_smul, ← map_mul, hw, map_one, one_smul]`. Establish `hQmem : ∀ r i, H.Q r i ∈ Per.FilD l (kk i)`. Introduce `r i`.

Use `(hxi (kk i) H.q (H.Q r i)).1 ?_` and prove the remaining obligations. Rewrite using `[H.Q_eq r i, show kk i + (H.q : ℤ) = ((H.p i : ℕ) : ℤ) by rw [hkk]; ring]`. Use `(hP _ _).2 ?_` and prove the remaining obligations. Rewrite using `[hFilP]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.

Establish `hQ₀cmem : ∀ r i, (Q₀ * z.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (kk i)`. Introduce `r i`. Rewrite using `[hQ₀c, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ (hQmem r i)`. Establish `hβmem : ∀ i j, β i j ∈ Per.FilD l (-kk i)`.

Introduce `i j`. Rewrite using `[hβ, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def]`. Use `Submodule.smul_mem _ _ ((hxi (-kk i) (H.p i) (Qi i j)).1 ?_)` and prove the remaining obligations. Establish `e : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p i * Qi i j = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E) ^ H.q * H.V⁻¹ i j)`. Rewrite using `[hQi, Matrix.diagonal_mul, Matrix.map_apply, map_mul, map_pow]`.

Rewrite using `[show algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p i * (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * ξi ^ H.p i * algebraMap (Per.BdRp l) (Per.BdR l) (H.V⁻¹ i j)) = (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * ξi) ^ H.p i * (al …`. Rewrite using `[e, show -kk i + (H.p i : ℤ) = ((H.q : ℕ) : ℤ) by rw [hkk]; ring]`. Use `(hP _ _).2 ?_` and prove the remaining obligations. Rewrite using `[hFilP]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.

Use `choose nb hnb using hbd`. Take `⟨M, hMU, hMU'⟩ : ∃ M : ℕ, (∀ r s, nb (U r s) ≤ M) ∧ ∀ r s, nb (U' r s) ≤ M` from `⟨Finset.univ.sup (fun q : Fin d × Fin d => max (nb (U q.1 q.2)) (nb (U' q.1 q.2))), fun r s => le_trans (le_max_left _ _) (Finset.le_sup (f := fun q : Fin d × Fin d => max (nb (U q.1 q.2)) (nb (U' q.1 q.2))) (Finset.mem_univ (r, s))), fun r s => le_trans (le_max_right _ _) (Finse …`. Establish `hU : ∀ r s, U r s ∈ Per.FilD l (-(M : ℤ))` using `fun r s => hanti _ _ (by have := hMU r s; omega) (hnb _)`. Establish `hU' : ∀ r s, U' r s ∈ Per.FilD l (-(M : ℤ))` using `fun r s => hanti _ _ (by have := hMU' r s; omega) (hnb _)`. Take `⟨N, hN₀, hNk, hNQ⟩ : ∃ N : ℕ, N₀ ≤ N ∧ (∀ i, (kk i).natAbs ≤ N) ∧ ∀ r s, nb (Q₀ r s) ≤ N` from `⟨max N₀ (max (Finset.univ.sup fun i => (kk i).natAbs) (Finset.univ.sup fun q : Fin d × Fin d => nb (Q₀ q.1 q.2))), le_max_left _ _, fun i => le_trans (Finset.le_sup (f := fun i => (kk i).natAbs) (Finset.mem_univ i)) (le_trans (le_max_left _ _) (le_max_right _ _)), fun r s => le_t …`.

Establish `hk : ∀ i, |kk i| ≤ N` using `fun i => by rw [Int.abs_eq_natAbs]; exact_mod_cast hNk i`. Establish `hQ₀N : ∀ r s, Q₀ r s ∈ Per.FilD l (-(N : ℤ))` using `fun r s => hanti _ _ (by have := hNQ r s; omega) (hnb _)`. Take `⟨c₂, X₀, X₀', hX₀, -, hQX, hXQ⟩` from `GlobalTheory.BKModif.exists_modification_of_filtration l K bk C d Q₀ Q₀' hQQ N d kk z β hk hQ₀N hQ₀cmem hβmem hprod`. Take `⟨k, Λ, Λ', hΛΛ, hΛD⟩` from `happ (N + M)`. Establish `hφψ : ∀ A : Matrix (Fin d) (Fin d) bk.S, A.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) = (A.map ((aDp l).comp bk.ev)).map (algebraMap (Per.BdRp l) (Per.BdR l))` using `fun A => by ext; rfl`.

Establish `hφ0 : ∀ s : bk.S, ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) s ∈ Per.FilD l 0` using `fun s => hmap0 _`. Take `⟨D, hD⟩ : ∃ D : Matrix (Fin d) (Fin d) (Per.BdRp l), D = Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀` from `⟨_, rfl⟩`. Establish `hDm : ∀ i j, (D.map (algebraMap (Per.BdRp l) (Per.BdR l))) i j ∈ Per.FilD l ((N + M : ℕ) : ℤ)` using `fun i j => (hP _ _).2 (by rw [hD]; exact hΛD i j)`. Establish `hΛsplit : Λ.map ((aDp l).comp bk.ev) = (l : Per.BdRp l) ^ k • Λ₀ + D` using `by rw [hD]; abel`. Use `⟨N, c₂ + 2 * k, Λ * X₀, X₀' * Λ', hN₀, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc X₀, hX₀, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hΛΛ, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e : U * (Λ * X₀).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) = algebraMap (Per.BdRp l) (Per.BdR l) ((l : Per.BdRp l) ^ k) • (Q₀ * X₀.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) + U * D.map (algebraMap (Per.BdRp l) (Per.BdR l)) …`. Rewrite using `[Matrix.map_mul, hφψ Λ, hΛsplit, Matrix.map_add _ (map_add _), GlobalTheory.BKModif.map_smul_ringHom, hQ₀]`.

Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]`. Introduce `r j`. Rewrite using `[e, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def]`. Use `add_mem (Submodule.smul_mem _ _ (hQX r j)) ?_` and prove the remaining obligations. Establish `h1 : ∀ r t, (U * D.map (algebraMap (Per.BdRp l) (Per.BdR l))) r t ∈ Per.FilD l N` using `fun r t => GlobalTheory.BKModif.mulFil hmul hanti U _ (fun _ _ => -(M : ℤ)) (fun _ _ => ((N + M : ℕ) : ℤ)) (fun _ _ => (N : ℤ)) hU hDm (fun _ _ _ => by push_cast; omega) r t`.

Conclude with `GlobalTheory.BKModif.mulFil hmul hanti _ _ (fun _ _ => (N : ℤ)) (fun _ _ => 0) (fun _ _ => (N : ℤ)) h1 (fun _ _ => hφ0 _) (fun _ _ _ => by simp) r j`. Establish `hl0` using `GlobalTheory.BKModif.l_ne_zero bk`. Establish `hΛ'Λ : Λ' * Λ = ((l : bk.S) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) bk.S)` using `GlobalTheory.BKModif.mul_comm_of_scalar Λ Λ' _ (pow_ne_zero _ hl0) hΛΛ`. Establish `hA'A : Λ'.map ((aDp l).comp bk.ev) * Λ.map ((aDp l).comp bk.ev) = ((l : Per.BdRp l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l))`. Rewrite using `[← Matrix.map_mul, hΛ'Λ, GlobalTheory.BKModif.map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _)]`.

Simplify using the standard rewrite rules. Establish `key : (l : Per.BdRp l) ^ k • Λ'.map ((aDp l).comp bk.ev) = (l : Per.BdRp l) ^ (2 * k) • Λ₀⁻¹ - Λ'.map ((aDp l).comp bk.ev) * D * Λ₀⁻¹`. Rewrite using `[hD, Matrix.mul_sub, Matrix.mul_smul, hA'A, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc (Λ'.map _) Λ₀, hΛ, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Establish `hE : ∀ i j, (Λ'.map ((aDp l).comp bk.ev) * D * Λ₀⁻¹) i j ∈ Per.FilP l (N + M)` using `mul_mem_ideal _ _ _ _ (fun i j => by rw [hD]; exact hΛD i j)`.

Establish `hEm : ∀ i j, ((Λ'.map ((aDp l).comp bk.ev) * D * Λ₀⁻¹).map (algebraMap (Per.BdRp l) (Per.BdR l))) i j ∈ Per.FilD l ((N + M : ℕ) : ℤ)` using `fun i j => (hP _ _).2 (hE i j)`. Establish `e : algebraMap (Per.BdRp l) (Per.BdR l) ((l : Per.BdRp l) ^ k) • ((X₀' * Λ').map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U') = algebraMap (Per.BdRp l) (Per.BdR l) ((l : Per.BdRp l) ^ (2 * k)) • (X₀'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp …`. Rewrite using `[Matrix.map_mul, hφψ Λ', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_smul, ← Matrix.smul_mul, ← GlobalTheory.BKModif.map_smul_ringHom, key, Matrix.map_sub _ (map_sub _), GlobalTheory.BKModif.map_smul_ringHom, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, …`. Introduce `r j`. Establish `hfin : algebraMap (Per.BdRp l) (Per.BdR l) ((l : Per.BdRp l) ^ k) * ((X₀' * Λ').map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U') r j ∈ Per.FilD l N`.

Use `congrFun (congrFun e r) j` as an intermediate fact. Rewrite `this` using `[Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[this, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def]`. Use `sub_mem (Submodule.smul_mem _ _ (hXQ r j)) ?_` and prove the remaining obligations. Establish `h1 : ∀ r t, (X₀'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * (Λ'.map ((aDp l).comp bk.ev) * D * Λ₀⁻¹).map (algebraMap (Per.BdRp l) (Per.BdR l))) r t ∈ Per.FilD l ((N + M : ℕ) : ℤ)` using `fun r t => GlobalTheory.BKModif.mulFil hmul hanti _ _ (fun _ _ => 0) (fun _ _ => ((N + M : ℕ) : ℤ)) (fun _ _ => ((N + M : ℕ) : ℤ)) (fun _ _ => hφ0 _) hEm (fun _ _ _ => by simp) r t`.

Conclude with `GlobalTheory.BKModif.mulFil hmul hanti _ _ (fun _ _ => ((N + M : ℕ) : ℤ)) (fun _ _ => -(M : ℤ)) (fun _ _ => (N : ℤ)) h1 hU' (fun _ _ _ => by push_cast; omega) r j`. Take `⟨v, hv⟩` from `((isUnit_l_BdRp l).pow k).exists_left_inv`. Establish `key2` using `Submodule.smul_mem _ v hfin`. Rewrite `key2` using `[Algebra.smul_def, ← mul_assoc, ← map_mul, hv, map_one, one_mul]`. Conclude with `key2`.
-/
theorem exists_twisted_modification : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K) (U U' : Matrix (Fin d) (Fin d) (Per.BdR l)) (Λ₀ : Matrix (Fin d) (Fin d) (Per.BdRp l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * (U * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))).map (Per.σD (g : GQ l)) = U * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))) → (∀ m : ℕ, ∃ (k : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) (bk.S)), Λ * Λ' = (l : bk.S) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ ∀ i j, (Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀) i j ∈ Per.FilP l m) → ∀ N₀ : ℕ, ∃ (N c₂ : ℕ) (X X' : Matrix (Fin d) (Fin d) (bk.S)), N₀ ≤ N ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ (∀ i j, (U * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) ∧ ∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U') i j ∈ Per.FilD l N := by
  intro l _ K bk C hI d ρ H U U' Λ₀ hUU' hinv happ N₀
  obtain ⟨hFilP, hmul, hanti, hP, hbd, hxi, -⟩ := GlobalTheory.MemLoc.seed_fil l C (bk.ev bk.E) bk.span_ev
  have hmap0 : ∀ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l 0 := by
    intro z
    have := (hP 0 z).2 (by rw [hFilP 0, pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top)
    simpa using this

  obtain ⟨k1, Λ1, Λ1', h1, hD1⟩ := happ 1
  have hdet : IsUnit Λ₀.det := by
    refine isUnit_det_of_approx Λ₀ (Λ1.map ((aDp l).comp bk.ev)) (Λ1'.map ((aDp l).comp bk.ev)) k1 ?_ hD1
    rw [← Matrix.map_mul, h1, GlobalTheory.BKModif.map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _)]
    simp
  have hΛ : Λ₀ * Λ₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet

  obtain ⟨Q₀, hQ₀⟩ : ∃ Q : Matrix (Fin d) (Fin d) (Per.BdR l), Q = U * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l)) := ⟨_, rfl⟩
  obtain ⟨Q₀', hQ₀'⟩ : ∃ Q : Matrix (Fin d) (Fin d) (Per.BdR l), Q = Λ₀⁻¹.map (algebraMap (Per.BdRp l) (Per.BdR l)) * U' := ⟨_, rfl⟩
  have hQQ : Q₀ * Q₀' = 1 := by
    rw [hQ₀, hQ₀', Matrix.mul_assoc, ← Matrix.mul_assoc (Λ₀.map _), ← Matrix.map_mul, hΛ,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, hUU']
  have hQQ' : Q₀' * Q₀ = 1 := mul_eq_one_comm.1 hQQ
  have hinvQ₀ : ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q₀.map (Per.σD (g : GQ l)) = Q₀ := fun g => by
    rw [hQ₀]; exact hinv g
  have hρ : ∀ g : ↥(GK K), ((ρ g).map (zOm l)).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) =
      (ρ g).map (Per.zD l) := by
    intro g; ext i j; simp [zOm, GlobalTheory.RingIface.zD_alg, C.o_sec.z, aDp]
  have hinvQ : ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * H.Q.map (Per.σD (g : GQ l)) = H.Q := fun g => by
    rw [← hρ g]; exact H.inv g g.2

  obtain ⟨c, hc⟩ : ∃ c : Matrix (Fin d) (Fin d) (Per.BdR l), c = Q₀' * H.Q := ⟨_, rfl⟩
  have hcσ : ∀ g : ↥(GK K), c.map (Per.σD (g : GQ l)) = c := by
    intro g
    have hσ1 : Q₀.map (Per.σD (g : GQ l)) * Q₀'.map (Per.σD (g : GQ l)) = 1 := by
      rw [← Matrix.map_mul, hQQ, Matrix.map_one _ (map_zero _) (map_one _)]
    have key : Q₀ * c.map (Per.σD (g : GQ l)) = H.Q := by
      calc Q₀ * c.map (Per.σD (g : GQ l)) = ((ρ g).map (Per.zD l) * Q₀.map (Per.σD (g : GQ l))) *
            (Q₀'.map (Per.σD (g : GQ l)) * H.Q.map (Per.σD (g : GQ l))) := by rw [hinvQ₀ g, hc, Matrix.map_mul]
        _ = (ρ g).map (Per.zD l) * (Q₀.map (Per.σD (g : GQ l)) * Q₀'.map (Per.σD (g : GQ l))) *
            H.Q.map (Per.σD (g : GQ l)) := by simp only [Matrix.mul_assoc]
        _ = H.Q := by rw [hσ1, Matrix.mul_one, hinvQ g]
    calc c.map (Per.σD (g : GQ l)) = (Q₀' * Q₀) * c.map (Per.σD (g : GQ l)) := by rw [hQQ', Matrix.one_mul]
      _ = Q₀' * (Q₀ * c.map (Per.σD (g : GQ l))) := Matrix.mul_assoc _ _ _
      _ = c := by rw [key, hc]

  have hx : ∀ i j, ∃ x ∈ K.1, C.oD x = c i j := fun i j => hI K (c i j) (fun g hg => by
    have := congrFun (congrFun (hcσ ⟨g, hg⟩) i) j
    simpa using this)
  choose x hxK hxc using hx
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  classical
  obtain ⟨y, hy0, hint⟩ := exists_integral_multiples ℤ_[l] ℚ_[l]
    (Finset.univ.image fun p : Fin d × Fin d => (⟨x p.1 p.2, hxK p.1 p.2⟩ : ↥K.1))
  obtain ⟨z, hz⟩ : ∃ z : Matrix (Fin d) (Fin d) ↥(OL K), ∀ i j,
      z.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) i j =
        algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * c i j := by
    refine ⟨fun i j => ⟨y • ⟨x i j, hxK i j⟩, hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))⟩,
      fun i j => ?_⟩
    change C.oD (K.1.val.toRingHom ((OL K).val.toRingHom _)) = _
    rw [← hxc, ← oD_int']
    congr 1
    change ((y • (⟨x i j, hxK i j⟩ : ↥K.1) : ↥K.1) : Om l) = _
    rw [← algebraMap_smul ℚ_[l] y, Algebra.smul_def]
    simp
  have hu := isUnit_aDp_zA' hy0
  obtain ⟨w, hw⟩ := hu.exists_right_inv

  have hξ : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E))) := by
    have hk : Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)} :=
      ker_localizedTheta_eq_span_of_dvd l (bk.ev bk.E) fun a => by
        rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]
    have hun := GlobalTheory.RingIface.isUnit_of_generator l hk
    rw [GlobalTheory.RingIface.pD_eq_alg] at hun
    simpa only [aDp, RingHom.comp_apply] using hun
  obtain ⟨ξi, hξi⟩ := hξ.exists_right_inv

  have hQform : H.Q = H.V.map (algebraMap (Per.BdRp l) (Per.BdR l)) *
      Matrix.diagonal (fun j => ξi ^ H.q * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p j) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.map_apply]
    have := H.Q_eq i j
    calc H.Q i j = (ξi ^ H.q * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q) * H.Q i j := by
          rw [← mul_pow, mul_comm ξi, hξi, one_pow, one_mul]
      _ = ξi ^ H.q * (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * H.Q i j) := by ring
      _ = _ := by rw [this, map_mul, map_pow]; ring
  have hVdet : IsUnit H.V.det := (Matrix.isUnit_iff_isUnit_det H.V).1 H.unit
  obtain ⟨Qi, hQi⟩ : ∃ Qi : Matrix (Fin d) (Fin d) (Per.BdR l), Qi =
      Matrix.diagonal (fun i => algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * ξi ^ H.p i) *
        H.V⁻¹.map (algebraMap (Per.BdRp l) (Per.BdR l)) := ⟨_, rfl⟩
  have hQQi : H.Q * Qi = 1 := by
    rw [hQform, hQi, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    have : (fun j => ξi ^ H.q * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p j *
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * ξi ^ H.p j)) = fun _ => 1 := by
      funext j
      rw [show ξi ^ H.q * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p j *
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * ξi ^ H.p j) =
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * ξi) ^ H.q *
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * ξi) ^ H.p j by ring, hξi, one_pow, one_pow, mul_one]
    rw [this, Matrix.diagonal_one, Matrix.one_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hVdet,
      Matrix.map_one _ (map_zero _) (map_one _)]

  obtain ⟨β, hβ⟩ : ∃ β : Matrix (Fin d) (Fin d) (Per.BdR l), β = algebraMap (Per.BdRp l) (Per.BdR l) w • Qi := ⟨_, rfl⟩
  obtain ⟨kk, hkk⟩ : ∃ kk : Fin d → ℤ, kk = fun i => (H.p i : ℤ) - H.q := ⟨_, rfl⟩
  have hcmap : z.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) • c := by
    ext i j; rw [hz, Matrix.smul_apply, smul_eq_mul]
  have hQ₀c : Q₀ * z.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) • H.Q := by
    rw [hcmap, Matrix.mul_smul, hc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have hprod : Q₀ * z.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 := by
    rw [hQ₀c, hβ, Matrix.smul_mul, Matrix.mul_smul, hQQi, smul_smul, ← map_mul, hw, map_one, one_smul]
  have hQmem : ∀ r i, H.Q r i ∈ Per.FilD l (kk i) := by
    intro r i
    refine (hxi (kk i) H.q (H.Q r i)).1 ?_
    rw [H.Q_eq r i, show kk i + (H.q : ℤ) = ((H.p i : ℕ) : ℤ) by rw [hkk]; ring]
    refine (hP _ _).2 ?_
    rw [hFilP]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hQ₀cmem : ∀ r i, (Q₀ * z.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈
      Per.FilD l (kk i) := by
    intro r i
    rw [hQ₀c, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hQmem r i)
  have hβmem : ∀ i j, β i j ∈ Per.FilD l (-kk i) := by
    intro i j
    rw [hβ, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ((hxi (-kk i) (H.p i) (Qi i j)).1 ?_)
    have e : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p i * Qi i j =
        algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E) ^ H.q * H.V⁻¹ i j) := by
      rw [hQi, Matrix.diagonal_mul, Matrix.map_apply, map_mul, map_pow]
      rw [show algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p i *
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * ξi ^ H.p i *
          algebraMap (Per.BdRp l) (Per.BdR l) (H.V⁻¹ i j)) =
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * ξi) ^ H.p i *
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q *
          algebraMap (Per.BdRp l) (Per.BdR l) (H.V⁻¹ i j)) by ring, hξi, one_pow, one_mul]
    rw [e, show -kk i + (H.p i : ℤ) = ((H.q : ℕ) : ℤ) by rw [hkk]; ring]
    refine (hP _ _).2 ?_
    rw [hFilP]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

  choose nb hnb using hbd
  obtain ⟨M, hMU, hMU'⟩ : ∃ M : ℕ, (∀ r s, nb (U r s) ≤ M) ∧ ∀ r s, nb (U' r s) ≤ M :=
    ⟨Finset.univ.sup (fun q : Fin d × Fin d => max (nb (U q.1 q.2)) (nb (U' q.1 q.2))),
      fun r s => le_trans (le_max_left _ _)
        (Finset.le_sup (f := fun q : Fin d × Fin d => max (nb (U q.1 q.2)) (nb (U' q.1 q.2))) (Finset.mem_univ (r, s))),
      fun r s => le_trans (le_max_right _ _)
        (Finset.le_sup (f := fun q : Fin d × Fin d => max (nb (U q.1 q.2)) (nb (U' q.1 q.2))) (Finset.mem_univ (r, s)))⟩
  have hU : ∀ r s, U r s ∈ Per.FilD l (-(M : ℤ)) := fun r s =>
    hanti _ _ (by have := hMU r s; omega) (hnb _)
  have hU' : ∀ r s, U' r s ∈ Per.FilD l (-(M : ℤ)) := fun r s =>
    hanti _ _ (by have := hMU' r s; omega) (hnb _)
  obtain ⟨N, hN₀, hNk, hNQ⟩ : ∃ N : ℕ, N₀ ≤ N ∧ (∀ i, (kk i).natAbs ≤ N) ∧ ∀ r s, nb (Q₀ r s) ≤ N :=
    ⟨max N₀ (max (Finset.univ.sup fun i => (kk i).natAbs) (Finset.univ.sup fun q : Fin d × Fin d => nb (Q₀ q.1 q.2))),
      le_max_left _ _,
      fun i => le_trans (Finset.le_sup (f := fun i => (kk i).natAbs) (Finset.mem_univ i))
        (le_trans (le_max_left _ _) (le_max_right _ _)),
      fun r s => le_trans (Finset.le_sup (f := fun q : Fin d × Fin d => nb (Q₀ q.1 q.2)) (Finset.mem_univ (r, s)))
        (le_trans (le_max_right _ _) (le_max_right _ _))⟩
  have hk : ∀ i, |kk i| ≤ N := fun i => by rw [Int.abs_eq_natAbs]; exact_mod_cast hNk i
  have hQ₀N : ∀ r s, Q₀ r s ∈ Per.FilD l (-(N : ℤ)) := fun r s =>
    hanti _ _ (by have := hNQ r s; omega) (hnb _)
  obtain ⟨c₂, X₀, X₀', hX₀, -, hQX, hXQ⟩ := GlobalTheory.BKModif.exists_modification_of_filtration l K bk C d Q₀ Q₀' hQQ
    N d kk z β hk hQ₀N hQ₀cmem hβmem hprod

  obtain ⟨k, Λ, Λ', hΛΛ, hΛD⟩ := happ (N + M)
  have hφψ : ∀ A : Matrix (Fin d) (Fin d) bk.S, A.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) =
      (A.map ((aDp l).comp bk.ev)).map (algebraMap (Per.BdRp l) (Per.BdR l)) := fun A => by ext; rfl
  have hφ0 : ∀ s : bk.S, ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) s ∈ Per.FilD l 0 :=
    fun s => hmap0 _
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin d) (Fin d) (Per.BdRp l),
      D = Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀ := ⟨_, rfl⟩
  have hDm : ∀ i j, (D.map (algebraMap (Per.BdRp l) (Per.BdR l))) i j ∈ Per.FilD l ((N + M : ℕ) : ℤ) :=
    fun i j => (hP _ _).2 (by rw [hD]; exact hΛD i j)
  have hΛsplit : Λ.map ((aDp l).comp bk.ev) = (l : Per.BdRp l) ^ k • Λ₀ + D := by rw [hD]; abel
  refine ⟨N, c₂ + 2 * k, Λ * X₀, X₀' * Λ', hN₀, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc X₀, hX₀, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hΛΛ,
      smul_smul]
    congr 1
    ring
  · have e : U * (Λ * X₀).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) =
        algebraMap (Per.BdRp l) (Per.BdR l) ((l : Per.BdRp l) ^ k) •
          (Q₀ * X₀.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) +
        U * D.map (algebraMap (Per.BdRp l) (Per.BdR l)) *
          X₀.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) := by
      rw [Matrix.map_mul, hφψ Λ, hΛsplit, Matrix.map_add _ (map_add _), GlobalTheory.BKModif.map_smul_ringHom, hQ₀]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    intro r j
    rw [e, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def]
    refine add_mem (Submodule.smul_mem _ _ (hQX r j)) ?_
    have h1 : ∀ r t, (U * D.map (algebraMap (Per.BdRp l) (Per.BdR l))) r t ∈ Per.FilD l N :=
      fun r t => GlobalTheory.BKModif.mulFil hmul hanti U _ (fun _ _ => -(M : ℤ)) (fun _ _ => ((N + M : ℕ) : ℤ))
        (fun _ _ => (N : ℤ)) hU hDm (fun _ _ _ => by push_cast; omega) r t
    exact GlobalTheory.BKModif.mulFil hmul hanti _ _ (fun _ _ => (N : ℤ)) (fun _ _ => 0) (fun _ _ => (N : ℤ)) h1
      (fun _ _ => hφ0 _) (fun _ _ _ => by simp) r j
  · have hl0 := GlobalTheory.BKModif.l_ne_zero bk
    have hΛ'Λ : Λ' * Λ = ((l : bk.S) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) bk.S) :=
      GlobalTheory.BKModif.mul_comm_of_scalar Λ Λ' _ (pow_ne_zero _ hl0) hΛΛ
    have hA'A : Λ'.map ((aDp l).comp bk.ev) * Λ.map ((aDp l).comp bk.ev) =
        ((l : Per.BdRp l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)) := by
      rw [← Matrix.map_mul, hΛ'Λ, GlobalTheory.BKModif.map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _)]
      simp
    have key : (l : Per.BdRp l) ^ k • Λ'.map ((aDp l).comp bk.ev) =
        (l : Per.BdRp l) ^ (2 * k) • Λ₀⁻¹ - Λ'.map ((aDp l).comp bk.ev) * D * Λ₀⁻¹ := by
      rw [hD, Matrix.mul_sub, Matrix.mul_smul, hA'A, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_assoc (Λ'.map _) Λ₀, hΛ, Matrix.mul_one]
      abel
    have hE : ∀ i j, (Λ'.map ((aDp l).comp bk.ev) * D * Λ₀⁻¹) i j ∈ Per.FilP l (N + M) :=
      mul_mem_ideal _ _ _ _ (fun i j => by rw [hD]; exact hΛD i j)
    have hEm : ∀ i j, ((Λ'.map ((aDp l).comp bk.ev) * D * Λ₀⁻¹).map (algebraMap (Per.BdRp l) (Per.BdR l))) i j ∈
        Per.FilD l ((N + M : ℕ) : ℤ) := fun i j => (hP _ _).2 (hE i j)
    have e : algebraMap (Per.BdRp l) (Per.BdR l) ((l : Per.BdRp l) ^ k) •
        ((X₀' * Λ').map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U') =
        algebraMap (Per.BdRp l) (Per.BdR l) ((l : Per.BdRp l) ^ (2 * k)) •
          (X₀'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * Q₀') -
        X₀'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) *
          (Λ'.map ((aDp l).comp bk.ev) * D * Λ₀⁻¹).map (algebraMap (Per.BdRp l) (Per.BdR l)) * U' := by
      rw [Matrix.map_mul, hφψ Λ', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_smul, ← Matrix.smul_mul,
        ← GlobalTheory.BKModif.map_smul_ringHom, key, Matrix.map_sub _ (map_sub _), GlobalTheory.BKModif.map_smul_ringHom, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hQ₀']
    intro r j
    have hfin : algebraMap (Per.BdRp l) (Per.BdR l) ((l : Per.BdRp l) ^ k) *
        ((X₀' * Λ').map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U') r j ∈ Per.FilD l N := by
      have := congrFun (congrFun e r) j
      rw [Matrix.smul_apply, smul_eq_mul] at this
      rw [this, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def]
      refine sub_mem (Submodule.smul_mem _ _ (hXQ r j)) ?_
      have h1 : ∀ r t, (X₀'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) *
          (Λ'.map ((aDp l).comp bk.ev) * D * Λ₀⁻¹).map (algebraMap (Per.BdRp l) (Per.BdR l))) r t ∈
            Per.FilD l ((N + M : ℕ) : ℤ) :=
        fun r t => GlobalTheory.BKModif.mulFil hmul hanti _ _ (fun _ _ => 0) (fun _ _ => ((N + M : ℕ) : ℤ))
          (fun _ _ => ((N + M : ℕ) : ℤ)) (fun _ _ => hφ0 _) hEm (fun _ _ _ => by simp) r t
      exact GlobalTheory.BKModif.mulFil hmul hanti _ _ (fun _ _ => ((N + M : ℕ) : ℤ)) (fun _ _ => -(M : ℤ))
        (fun _ _ => (N : ℤ)) h1 hU' (fun _ _ _ => by push_cast; omega) r j
    obtain ⟨v, hv⟩ := ((isUnit_l_BdRp l).pow k).exists_left_inv
    have key2 := Submodule.smul_mem _ v hfin
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, hv, map_one, one_mul] at key2
    exact key2

end GlobalTheory.BKTwist

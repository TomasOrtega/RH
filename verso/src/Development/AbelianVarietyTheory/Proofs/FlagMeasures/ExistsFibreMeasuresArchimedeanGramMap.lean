import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.GramDensityRealCoordinates
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Assembly
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacterStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.GramMapFibreExistence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibDis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfSS

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ArchGramFibre

open Formalism.L2.SG.Sub PI.VolFromSW PI.AdicCompletionValuation PI.VolStabS

/- English proof (translation)
Establish `: IsTotallyReal F` using `hCM.1`. Take `⟨k, eK, hK⟩` from `exists_coord_tens F E`. Take `⟨k1, e1, h1⟩` from `exists_coord_pi eK hK (Fin M)`. Take `⟨n, eV, hV⟩` from `exists_coord_pi e1 h1 (Fin a)`. Take `⟨k2, e2, h2⟩` from `exists_coord_pi eK hK (Fin a)`.

Take `⟨N, eM, hM⟩` from `exists_coord_pi e2 h2 (Fin a)`. Establish `hdiv : ∀ n : ℕ, 0 < n → ∀ S ∈ HermR (Ainf F) σ a, ∃ T ∈ HermR (Ainf F) σ a, n • T = S`. Introduce `n hn S hS`. Set `c : Ainf F ⊗[F] E` to `algebraMap F (Ainf F ⊗[F] E) (1 / n)`. Establish `hsc : sigR (Ainf F) σ c = c` using `(Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _`.

Use `⟨c • S, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, map_mul, hsc]`. Rewrite using `[hS i j]`. Establish `hc1 : (n : Ainf F ⊗[F] E) * c = 1`.

Simplify using `only [c]`. Rewrite using `[← map_natCast (algebraMap F (Ainf F ⊗[F] E)) n, ← map_mul]`. Establish `: (n : F) ≠ 0` using `by exact_mod_cast hn.ne'`. Rewrite using `[mul_one_div_cancel this, map_one]`. Use extensionality with `i j`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, ← mul_assoc, hc1, one_mul]`. Take `⟨m, eH, hH⟩` from `exists_coord_sub (X := Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) eM hM (HermR (Ainf F) σ a) (isClosed_HermR (Ainf F) σ a) hdiv`. Conclude with `⟨n, m, eV, eH, hV, hH⟩`.
-/
theorem exists_real_coords (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ) :
    ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
      (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)),
      (∀ x y, eV (x + y) = eV x + eV y) ∧ ∀ x y, eH (x + y) = eH x + eH y := by
  have : IsTotallyReal F := hCM.1
  obtain ⟨k, eK, hK⟩ := exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := exists_coord_pi eK hK (Fin M)
  obtain ⟨n, eV, hV⟩ := exists_coord_pi e1 h1 (Fin a)
  obtain ⟨k2, e2, h2⟩ := exists_coord_pi eK hK (Fin a)
  obtain ⟨N, eM, hM⟩ := exists_coord_pi e2 h2 (Fin a)
  have hdiv : ∀ n : ℕ, 0 < n → ∀ S ∈ HermR (Ainf F) σ a, ∃ T ∈ HermR (Ainf F) σ a, n • T = S := by
    intro n hn S hS
    let c : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1 / n)
    have hsc : sigR (Ainf F) σ c = c :=
      (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
    refine ⟨c • S, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hsc]
      rw [hS i j]
    · have hc1 : (n : Ainf F ⊗[F] E) * c = 1 := by
        simp only [c]
        rw [← map_natCast (algebraMap F (Ainf F ⊗[F] E)) n, ← map_mul]
        have : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
        rw [mul_one_div_cancel this, map_one]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, ← mul_assoc, hc1, one_mul]
  obtain ⟨m, eH, hH⟩ := exists_coord_sub (X := Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) eM hM
    (HermR (Ainf F) σ a) (isClosed_HermR (Ainf F) σ a) hdiv
  exact ⟨n, m, eV, eH, hV, hH⟩

/- English proof (translation)
Introduce `X hX S`. Use `semisimpleTens_holds F E σ hCM` as an intermediate fact. Establish `hσ : ∀ x, σ (σ x) = x` using `PI.VolStabS.sigma_invol σ hCM.2.2.2`. Set `s` to `sigR (Ainf F) σ`. Set `Z : Fin a → Fin M → Ainf F ⊗[F] E` to `fun i => Matrix.vecMul (fun l => s (X i l)) (JR (F := F) (Ainf F) J)`.

Establish `hZh : ∀ i y, hR (Ainf F) σ J (X i) y = ∑ k, Z i k * y k`. Introduce `i y`. Simplify using `only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `hJu : IsUnit (JR (F` using `F) (Ainf F) J).det := by`.

Establish `e` using `RingHom.map_det (inclR (F := F) (E := E) (Ainf F)) J`. Rewrite `e` using `[RingHom.mapMatrix_apply]`. Use `show IsUnit (J.map (inclR (Ainf F))).det`. Rewrite using `[← e]`. Conclude with `(isUnit_iff_ne_zero.2 hJ.2).map _`.

Establish `hZ : LinearIndependent (Ainf F ⊗[F] E) Z`. Use `Fintype.linearIndependent_iff.2 fun g hg i => ?_` and prove the remaining obligations. Set `v : Fin M → Ainf F ⊗[F] E` to `fun l => ∑ i, g i * s (X i l)`. Establish `hv0 : Matrix.vecMul v (JR (F` using `F) (Ainf F) J) = 0 := by`. Use function extensionality and compare the values at `j`.

Use `congrFun hg j` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct, Finset.mul_sum, Pi.zero_apply] at this`. Simplify using `only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[← this]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring`. Establish `hv : v = 0`. Use `congrArg (fun u => Matrix.vecMul u (JR (F := F) (Ainf F) J)⁻¹) hv0` as an intermediate fact. Simplify using `only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one, Matrix.zero_vecMul] at this`. Conclude with `this`.

Establish `hX0 : ∑ i, s (g i) • X i = 0`. Use function extensionality and compare the values at `l`. Use `congrArg s (congrFun hv l)` as an intermediate fact. Simplify using `only [v, map_sum, map_mul, s, sigR_invol (Ainf F) σ hσ, Pi.zero_apply, map_zero] at this`. Simplify `this` using `[Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Use `Fintype.linearIndependent_iff.1 hX _ hX0 i` as an intermediate fact. Establish `e2` using `congrArg s this`. Simplify using `only [s, sigR_invol (Ainf F) σ hσ, map_zero] at e2`. Conclude with `e2`. Set `half : Ainf F ⊗[F] E` to `algebraMap F (Ainf F ⊗[F] E) (1/2)`.

Establish `hh : half + half = 1`. Simplify using `only [half, ← map_add]`. Evaluate the numerical expressions. Apply the tactic sequence `first | rfl | exact Algebra.TensorProduct.one_def.symm`. Establish `hsh : s half = half` using `(Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _`.

Establish `hw : ∀ j, ∃ w : Fin M → Ainf F ⊗[F] E, ∀ i, ∑ k, Z i k * w k = half * (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) i j` using `fun j => exists_dual_of_linIndep Z hZ _`. Use `choose Y hY using hw`. Use `⟨Y, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Establish `h1 : hR (Ainf F) σ J (X i) (Y j) = half * (S : Matrix _ _ _) i j` using `by rw [hZh]; exact hY j i`.

Establish `h2 : hR (Ainf F) σ J (Y i) (X j) = half * (S : Matrix _ _ _) i j`. Rewrite using `[← hR_herm (Ainf F) σ hσ J hJ.1 (X j) (Y i), hZh, hY i j]`. Simplify using `only [map_mul]`. Rewrite using `[show sigR (Ainf F) σ half = half from hsh, S.2 i j]`. Use `show hR (Ainf F) σ J (X i) (Y j) + hR (Ainf F) σ J (Y i) (X j) = _`.

Rewrite using `[h1, h2, ← add_mul, hh, one_mul]`.
-/
theorem gramB_surj_of_free (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    ∀ X : Fin a → Fin M → Ainf F ⊗[F] E, LinearIndependent (Ainf F ⊗[F] E) X →
      ∀ S : HermR (Ainf F) σ a, ∃ Y, gramB (Ainf F) σ J X Y = S := by
  intro X hX S
  have := semisimpleTens_holds F E σ hCM
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  let s := sigR (Ainf F) σ
  let Z : Fin a → Fin M → Ainf F ⊗[F] E :=
    fun i => Matrix.vecMul (fun l => s (X i l)) (JR (F := F) (Ainf F) J)
  have hZh : ∀ i y, hR (Ainf F) σ J (X i) y = ∑ k, Z i k * y k := by
    intro i y
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hJu : IsUnit (JR (F := F) (Ainf F) J).det := by
    have e := RingHom.map_det (inclR (F := F) (E := E) (Ainf F)) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR (Ainf F))).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hJ.2).map _
  have hZ : LinearIndependent (Ainf F ⊗[F] E) Z := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let v : Fin M → Ainf F ⊗[F] E := fun l => ∑ i, g i * s (X i l)
    have hv0 : Matrix.vecMul v (JR (F := F) (Ainf F) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : v = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Ainf F) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • X i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      simp only [v, map_sum, map_mul, s, sigR_invol (Ainf F) σ hσ, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hX _ hX0 i
    have e2 := congrArg s this
    simp only [s, sigR_invol (Ainf F) σ hσ, map_zero] at e2
    exact e2
  let half : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1/2)
  have hh : half + half = 1 := by
    simp only [half, ← map_add]; norm_num
    first | rfl | exact Algebra.TensorProduct.one_def.symm
  have hsh : s half = half := (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
  have hw : ∀ j, ∃ w : Fin M → Ainf F ⊗[F] E, ∀ i, ∑ k, Z i k * w k =
      half * (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) i j :=
    fun j => exists_dual_of_linIndep Z hZ _
  choose Y hY using hw
  refine ⟨Y, ?_⟩
  funext i j
  have h1 : hR (Ainf F) σ J (X i) (Y j) = half * (S : Matrix _ _ _) i j := by rw [hZh]; exact hY j i
  have h2 : hR (Ainf F) σ J (Y i) (X j) = half * (S : Matrix _ _ _) i j := by
    rw [← hR_herm (Ainf F) σ hσ J hJ.1 (X j) (Y i), hZh, hY i j]
    simp only [map_mul]
    rw [show sigR (Ainf F) σ half = half from hsh, S.2 i j]
  show hR (Ainf F) σ J (X i) (Y j) + hR (Ainf F) σ J (Y i) (X j) = _
  rw [h1, h2, ← add_mul, hh, one_mul]

/- English proof (translation)
Take `⟨n, m, eV, eH, hV, hH⟩` from `exists_real_coords F E σ hCM M a`. Establish `hσ : ∀ x, σ (σ x) = x` using `PI.VolStabS.sigma_invol σ hCM.2.2.2`. Set `Q : (Fin a → Fin M → Ainf F ⊗[F] E) → HermR (Ainf F) σ a` to `gramH (Ainf F) σ hσ J hJ.1`. Set `β : (Fin a → Fin M → Ainf F ⊗[F] E) → (Fin a → Fin M → Ainf F ⊗[F] E) → HermR (Ainf F) σ a` to `fun X Y => ⟨gramB (Ainf F) σ J X Y, gramB_mem (Ainf F) σ hσ J hJ.1 X Y⟩`. Establish `hβc : Continuous (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) => β p.1 p.2)`.

Conclude with `(continuous_gramB (Ainf F) σ J).subtype_mk _`. Establish `hβa : ∀ x y z, β (x + y) z = β x z + β y z`. Introduce `x y z`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`.

Use `show gramB (Ainf F) σ J (x + y) z i j = gramB (Ainf F) σ J x z i j + gramB (Ainf F) σ J y z i j`. Simplify using `only [gramB, Pi.add_apply, PI.VolStabS.hR_add_left, PI.VolStabS.hR_add_right]`. Normalize the expressions using the abelian group laws. Establish `hβs : ∀ x y, β x y = β y x`. Introduce `x y`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Simplify using `only [β, gramB]`. Conclude with `add_comm _ _`. Establish `hQ : ∀ x, β x x = Q x + Q x`.

Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Both sides reduce to the same expression. Take `⟨hC, hD⟩` from `quadCoord_holds _ _ n m eV eH Q β hV hH hβc hβa hβs hQ`.

Use `⟨n, m, eV, eH, fun y => eH (Q (eV.symm y)), hV, hH, hC, fun X => ?_, fun X hX => ?_⟩` and prove the remaining obligations. Simplify using `[Q, gramH]`. Introduce `t`. Take `⟨Y, hY⟩` from `gramB_surj_of_free F E σ hCM M a J hJ X hX (eH.symm t)`. Use `⟨eV Y, ?_⟩` and prove the remaining obligations.

Rewrite using `[hD X Y]`. Establish `: β X Y = eH.symm t` using `Subtype.ext hY`. Rewrite using `[this, Homeomorph.apply_symm_apply]`.
-/
theorem exists_submersion_coords (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
      (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)) (f' : (Fin n → ℝ) → (Fin m → ℝ)),
      (∀ x y, eV (x + y) = eV x + eV y) ∧ (∀ x y, eH (x + y) = eH x + eH y) ∧ ContDiff ℝ 1 f' ∧
      (∀ X, ((eH.symm (f' (eV X)) : HermR (Ainf F) σ a) : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) =
        gramR (Ainf F) σ J X) ∧
      ∀ X, LinearIndependent (Ainf F ⊗[F] E) X → Function.Surjective (fderiv ℝ f' (eV X)) := by
  obtain ⟨n, m, eV, eH, hV, hH⟩ := exists_real_coords F E σ hCM M a
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  let Q : (Fin a → Fin M → Ainf F ⊗[F] E) → HermR (Ainf F) σ a := gramH (Ainf F) σ hσ J hJ.1
  let β : (Fin a → Fin M → Ainf F ⊗[F] E) → (Fin a → Fin M → Ainf F ⊗[F] E) →
      HermR (Ainf F) σ a := fun X Y => ⟨gramB (Ainf F) σ J X Y, gramB_mem (Ainf F) σ hσ J hJ.1 X Y⟩
  have hβc : Continuous (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (Fin a → Fin M → Ainf F ⊗[F] E) => β p.1 p.2) := by
    exact (continuous_gramB (Ainf F) σ J).subtype_mk _
  have hβa : ∀ x y z, β (x + y) z = β x z + β y z := by
    intro x y z; apply Subtype.ext; funext i j
    show gramB (Ainf F) σ J (x + y) z i j = gramB (Ainf F) σ J x z i j + gramB (Ainf F) σ J y z i j
    simp only [gramB, Pi.add_apply, PI.VolStabS.hR_add_left, PI.VolStabS.hR_add_right]
    abel
  have hβs : ∀ x y, β x y = β y x := by
    intro x y; apply Subtype.ext; funext i j
    simp only [β, gramB]; exact add_comm _ _
  have hQ : ∀ x, β x x = Q x + Q x := by
    intro x; apply Subtype.ext; funext i j; rfl
  obtain ⟨hC, hD⟩ := quadCoord_holds _ _ n m eV eH Q β hV hH hβc hβa hβs hQ
  refine ⟨n, m, eV, eH, fun y => eH (Q (eV.symm y)), hV, hH, hC, fun X => ?_, fun X hX => ?_⟩
  · simp [Q, gramH]
  · intro t
    obtain ⟨Y, hY⟩ := gramB_surj_of_free F E σ hCM M a J hJ X hX (eH.symm t)
    refine ⟨eV Y, ?_⟩
    rw [hD X Y]
    have : β X Y = eH.symm t := Subtype.ext hY
    rw [this, Homeomorph.apply_symm_apply]

/- English proof (translation)
Take `⟨n, m, eV, eH, f', hV, hH, hC, hG, hS⟩` from `exists_submersion_coords F E σ hCM M a J hJ`. Establish `: ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E)` using `⟨by`. Establish `e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) => p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2)`. Use function extensionality and compare the values at `p`. Rewrite using `[← hV, Homeomorph.symm_apply_apply]`.

Rewrite using `[e]`. Use the proof step `fun_prop⟩`. Establish `: ContinuousAdd (HermR (Ainf F) σ a)` using `⟨by`. Establish `e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) = fun p => eH.symm (eH p.1 + eH p.2)`. Use function extensionality and compare the values at `p`.

Rewrite using `[← hH, Homeomorph.symm_apply_apply]`. Rewrite using `[e]`. Use the proof step `fun_prop⟩`. Establish `hμ' : (μ.map eV).IsAddHaarMeasure` using `Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective (eV.map_cocompact).le`. Establish `hν' : (ν.map eH).IsAddHaarMeasure` using `Measure.isAddHaarMeasure_map ν (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective (eH.map_cocompact).le`.

Establish `hD` using `submDens_holds n m _ _ hμ' hν' f' hC`. Use `densAll_transport μ ν (gramR (Ainf F) σ J) Subtype.val _ eV eH f' Subtype.val_injective (fun X => hG X) (densAll_mono hD ?_)` and prove the remaining obligations. Introduce and unpack `y ⟨X, hX, rfl⟩`. Conclude with `hS X hX`.
-/
theorem gram_densities (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) :
    DensAll μ (gramR (Ainf F) σ J) Subtype.val ν {X | LinearIndependent (Ainf F ⊗[F] E) X} := by
  obtain ⟨n, m, eV, eH, f', hV, hH, hC, hG, hS⟩ := exists_submersion_coords F E σ hCM M a J hJ
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μ.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (ν.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map ν (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hD := submDens_holds n m _ _ hμ' hν' f' hC
  refine densAll_transport μ ν (gramR (Ainf F) σ J) Subtype.val _ eV eH f'
    Subtype.val_injective (fun X => hG X) (densAll_mono hD ?_)
  rintro y ⟨X, hX, rfl⟩
  exact hS X hX

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M a J hJ μ ν hμ hν`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Establish `hσ : ∀ x, σ (σ x) = x` using `PI.VolStabS.sigma_invol σ hCM.2.2.2`. Conclude with `fib_of_tens PI.VolStabS.DiscreteGroups.fibOfDens_holds (tensFacts_of σ hσ J hJ.1 a (Ainf F) (isOpen_units_Ainf F) (lip_ainf F)) μ ν hμ hν (gram_densities F E σ hCM M a J hJ μ ν hμ hν)`.
-/
theorem exists_fibreFamily : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M a : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J →
    ∀ (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a)),
      μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
      ∃ fib : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib := by
  intro F E _ _ _ _ _ σ hCM M a J hJ μ ν hμ hν
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  exact fib_of_tens PI.VolStabS.DiscreteGroups.fibOfDens_holds
    (tensFacts_of σ hσ J hJ.1 a (Ainf F) (isOpen_units_Ainf F) (lip_ainf F)) μ ν hμ hν
    (gram_densities F E σ hCM M a J hJ μ ν hμ hν)

end GlobalTheory.ArchGramFibre

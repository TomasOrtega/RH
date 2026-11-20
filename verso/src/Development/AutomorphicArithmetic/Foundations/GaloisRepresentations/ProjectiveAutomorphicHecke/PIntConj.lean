import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

/- English proof (translation)
Establish `h` using `congrArg (RingHom.mapMatrix (pLoc E u)) (mem_Sim.1 k.2)`. Rewrite `h` using `[map_mul]`. Use `Eq.trans ?_ (h.trans ?_)` and prove the remaining obligations. Both sides reduce to the same expression. Use extensionality with `i j`.

Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]`.
-/
private theorem comp_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := congrArg (RingHom.mapMatrix (pLoc E u)) (mem_Sim.1 k.2)
  rw [map_mul] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

/- English proof (translation)
Use `show Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ) u) = 1`. Rewrite using `[GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply, GroundTheory.Global.SemiLocal.valued_completionMap, hk (GroundTheory.Global.AdeleBaseChange.below ℚ u), one_pow]`.
-/
private theorem val_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (hk : sim k ∈ ZU) (u : Plc E) :
    Valued.v (pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ))) = 1 := by
  show Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ) u) = 1
  rw [GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply, GroundTheory.Global.SemiLocal.valued_completionMap,
    hk (GroundTheory.Global.AdeleBaseChange.below ℚ u), one_pow]

/- English proof (translation)
Introduce `E _ _ _ n k w hs ha`. Rewrite using `[← GlobalTheory.CompanionTheory.LFixDPf.mem_KGL_map_conj w]`. Use `set s := pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) with hsdef`. Establish `hv : Valued.v s = 1` using `val_sim k hs w`. Establish `hs0 : s ≠ 0`.

Introduce `h0`. Rewrite `hv` using `[h0, map_zero]`. Conclude with `zero_ne_one hv`. Use `set a := comp w k with hadef`. Use `set G := Matrix.GeneralLinearGroup.map (n := Fin n) (conjLoc (GlobalTheory.SplitPts.conjE E) w) (comp (cj w) k) with hG`.

Establish `hrel : (G.val)ᵀ * a.val = s • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))` using `comp_rel k w`. Establish `hGt : (G.val)ᵀ = s • (a⁻¹).val`. Combine the equalities or inequalities in the displayed calculation. Establish `hGi : (G⁻¹).val = s⁻¹ • (a.val)ᵀ`. Establish `h1 : G.val * (s⁻¹ • (a.val)ᵀ) = 1`.

Establish `h2 : a.val * (G.val)ᵀ = s • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))`. Rewrite using `[hGt, Matrix.mul_smul, Units.mul_inv]`. Establish `h3` using `congrArg Matrix.transpose h2`. Rewrite `h3` using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one]`. Rewrite using `[Matrix.mul_smul, h3, smul_smul, inv_mul_cancel₀ hs0, one_smul]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨ha1, ha2⟩` from `(GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w a).1 ha`. Use `(GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w G).2 ⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (congrFun hGt j) i`. Rewrite `h` using `[Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]`.

Rewrite using `[h, map_mul, hv, one_mul]`. Conclude with `ha2 j i`. Rewrite using `[hGi, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hv, inv_one, one_mul, Matrix.transpose_apply]`. Conclude with `ha1 j i`.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pIntConj_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj := by
  intro E _ _ _ n k w hs ha
  rw [← GlobalTheory.CompanionTheory.LFixDPf.mem_KGL_map_conj w]
  set s := pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) with hsdef
  have hv : Valued.v s = 1 := val_sim k hs w
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  set a := comp w k with hadef
  set G := Matrix.GeneralLinearGroup.map (n := Fin n) (conjLoc (GlobalTheory.SplitPts.conjE E) w) (comp (cj w) k) with hG
  have hrel : (G.val)ᵀ * a.val = s • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := comp_rel k w
  have hGt : (G.val)ᵀ = s • (a⁻¹).val := by
    calc (G.val)ᵀ = (G.val)ᵀ * (a.val * (a⁻¹).val) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = ((G.val)ᵀ * a.val) * (a⁻¹).val := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hrel, smul_mul_assoc, Matrix.one_mul]
  have hGi : (G⁻¹).val = s⁻¹ • (a.val)ᵀ := by
    have h1 : G.val * (s⁻¹ • (a.val)ᵀ) = 1 := by
      have h2 : a.val * (G.val)ᵀ = s • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
        rw [hGt, Matrix.mul_smul, Units.mul_inv]
      have h3 := congrArg Matrix.transpose h2
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at h3
      rw [Matrix.mul_smul, h3, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    calc (G⁻¹).val = (G⁻¹).val * (G.val * (s⁻¹ • (a.val)ᵀ)) := by rw [h1, Matrix.mul_one]
      _ = ((G⁻¹).val * G.val) * (s⁻¹ • (a.val)ᵀ) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.one_mul]
  obtain ⟨ha1, ha2⟩ := (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w a).1 ha
  refine (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w G).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · have h := congrFun (congrFun hGt j) i
    rw [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [h, map_mul, hv, one_mul]
    exact ha2 j i
  · rw [hGi, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hv, inv_one, one_mul, Matrix.transpose_apply]
    exact ha1 j i

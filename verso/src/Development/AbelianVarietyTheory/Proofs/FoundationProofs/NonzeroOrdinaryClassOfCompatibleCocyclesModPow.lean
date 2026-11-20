import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallNormLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralLimitCompatibleModPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitOfApproximateCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDotProductEqOfPrimePowApproxQbarLStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoefRingInvertPrimeInvOfMemNeZeroStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

/- English proof (translation)
Introduce `l _ Ω _ _ _ S A W c hWc hWint hg a N ha hcoc hloc hstep hker hine hdec hN hGZ`. Take `⟨z0, hz0O, hz0⟩` from `GlobalTheory.T.exists_integral_limit_compatible_modPrimePow l c (G ℚ Ω × Fin 2) (fun n p => a n p.1 p.2) (fun n p => ha n p.1 p.2) (fun n p => hstep n p.1 p.2)`. Set `z : G ℚ Ω → Fin 2 → Qbar l` to `fun s i => z0 (s, i)`. Establish `hzO : ∀ s i, z s i ∈ c.O` using `fun s i => hz0O (s, i)`. Establish `hza : ∀ n s, Cv n (z s) (a n s)` using `fun n s i => hz0 n (s, i)`.

Establish `hZ : z ∈ Z1 (Loc.colRep W)` using `GlobalTheory.T.limit_of_approximate_cocycles l Ω W c hWint a z hcoc hloc hza`. Establish `hcol : ∀ s (v : Fin 2 → Qbar l), Loc.colRep W s v = mat W s *ᵥ v` using `fun s v => by`. Simplify using `[Loc.colRep, Matrix.toLin'_apply]`. Establish `hrow : ∀ s (y : Fin 2 → Qbar l) i, (fun j => (mat W s - 1) i j) ⬝ᵥ y = (mat W s *ᵥ y - y) i`. Introduce `s y i`.

Use `show ((mat W s - 1) *ᵥ y) i = _`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Establish `hzker : ∀ b ∈ (toGS Ω (S : Set Pl)).ker, z b = 0`. Introduce `b hb`. Use function extensionality and compare the values at `i`.

Use `eq_zero_of_forall_norm_le _ fun n => ?_` and prove the remaining obligations. Establish `h` using `cg_trans (hza n b i) (hker n b hb i)`. Simplify using `only [Cg, Pi.zero_apply, sub_zero] at h`. Conclude with `h`. Establish `hexact : ∀ H : Subgroup (G ℚ Ω), (∀ n, ∃ y : Fin 2 → Qbar l, ∀ s ∈ H, Cv n (a n s) (mat W s *ᵥ y - y)) → ∃ x : Fin 2 → Qbar l, ∀ s ∈ H, z s = mat W s *ᵥ x - x`.

Introduce `H hH`. Take `⟨x, hx⟩` from `GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL l (↥H × Fin 2) 2 (fun p j => (mat W p.1 - 1) p.2 j) (fun p => z p.1 p.2) (fun n => by`. Take `⟨y, hy⟩` from `hH n`. Use `⟨y, fun p => ?_⟩` and prove the remaining obligations. Establish `h` using `cg_trans (hza n p.1 p.2) (hy p.1 p.1.2 p.2)`.

Rewrite `h` using `[← hrow]`. Conclude with `h)`. Conclude with `⟨x, fun s hs => funext fun i => by rw [← hrow]; exact hx (⟨s, hs⟩, i)⟩`. Establish `hUnr : Unr W z`. Introduce `w hw`.

Use `⟨placeOf Ω w, isPlaceOver_placeOf Ω w, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hwS : w ∈ S`. Conclude with `hexact (Ine (F := ℚ) (placeOf Ω w)) fun n => by`. Take `⟨y, -, hy⟩` from `hine n w hwS hw _ (isPlaceOver_placeOf Ω w)`. Conclude with `⟨y, hy⟩`.

Use `⟨0, fun s hs => ?_⟩` and prove the remaining obligations. Establish `hsN : s ∈ (toGS Ω (S : Set Pl)).ker` using `by show s ∈ (QuotientGroup.mk' (NS Ω (S : Set Pl))).ker`. Rewrite using `[QuotientGroup.ker_mk']`. Apply `Subgroup.le_topologicalClosure` to reduce the goal to its premises. Apply `Subgroup.subset_normalClosure` to reduce the goal to its premises.

Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨w, by simpa using hwS, placeOf Ω w, isPlaceOver_placeOf Ω w, hs⟩`. Rewrite using `[hzker s hsN]`. Simplify using the standard rewrite rules. Establish `hGr : Gr W A z`.

Take `⟨y, hy⟩` from `GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL l (↥(Dec (F := ℚ) A)) 1 (fun s _ => mat W s 1 1 - 1) (fun s => z s 1) (fun n => by`. Take `⟨y, -, hy⟩` from `hdec n`. Use `⟨fun _ => y, fun s => ?_⟩` and prove the remaining obligations. Establish `h` using `cg_trans (hza n s 1) (hy s s.2)`. Establish `e : (fun _ : Fin 1 => mat W s 1 1 - 1) ⬝ᵥ (fun _ => y) = mat W s 1 1 * y - y`.

Simplify using `[dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h)`. Use `⟨y 0, fun s hs => ?_⟩` and prove the remaining obligations.

Establish `h` using `hy ⟨s, hs⟩`. Rewrite using `[h]`. Simplify using `[dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨x, hx⟩` from `(mem_coboundaries1 _ _).1 (hGZ z hZ hUnr hGr)`.

Take `⟨g, hdg⟩` from `hg`. Establish `hMO : ∀ i j, (mat W g - 1) i j ∈ c.O`. Introduce `i j`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply]`. Use `split_ifs`.

Conclude with `c.O.sub_mem (hWint g i j) c.O.one_mem`. Conclude with `c.O.sub_mem (hWint g i j) c.O.zero_mem`. Establish `hdO : (mat W g - 1).det ∈ c.O`. Rewrite using `[Matrix.det_fin_two]`. Conclude with `c.O.sub_mem (c.O.mul_mem (hMO 0 0) (hMO 1 1)) (c.O.mul_mem (hMO 0 1) (hMO 1 0))`.

Establish `hadjO : ∀ i j, (mat W g - 1).adjugate i j ∈ c.O`. Introduce `i j`. Rewrite using `[Matrix.adjugate_fin_two]`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `hMO 1 1`.

Conclude with `c.O.neg_mem (hMO 0 1)`. Conclude with `c.O.neg_mem (hMO 1 0)`. Conclude with `hMO 0 0`. Establish `hMx : (mat W g - 1) *ᵥ x = z g` using `by rw [hx g, hcol, Matrix.sub_mulVec, Matrix.one_mulVec]`. Establish `hdx : (mat W g - 1).det • x = (mat W g - 1).adjugate *ᵥ z g`.

Rewrite using `[← hMx, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]`. Take `⟨k, hk⟩` from `GlobalTheory.T.memCoefRingInvertPrime_inv_of_mem_ne_zero l c _ hdO hdg`. Establish `hxE : VecE c x` using `⟨k, fun i => by`. Establish `e : x i = ((mat W g - 1).det)⁻¹ * ((mat W g - 1).adjugate *ᵥ z g) i`. Rewrite using `[← hdx, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdg, one_mul]`.

Rewrite using `[e, ← mul_assoc]`. Use `c.O.mul_mem hk ?_` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Conclude with `c.O.add_mem (c.O.mul_mem (hadjO i 0) (hzO g 0)) (c.O.mul_mem (hadjO i 1) (hzO g 1))⟩`. Use `hN ⟨x, hxE, fun s => ?_⟩` and prove the remaining obligations.

Establish `h` using `hza N s`. Rewrite `h` using `[hx s, hcol]`. Conclude with `cv_symm h`.
-/
theorem limit_nonzero_ordinary_class : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (N : ℕ), (∀ n s i, a n s i ∈ c.O) → (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (a (n + 1) s) (a n s)) → (∀ n, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cv n (a n b) 0) → (∀ n, ∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, Cv n (a n s) (mat W s *ᵥ y - y)) → (∀ n, ∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, Cg n (a n s 1) (mat W s 1 1 * y - y)) → (¬ ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s, Cv N (a N s) (mat W s *ᵥ y - y)) → ¬ GrZero W A := by
  intro l _ Ω _ _ _ S A W c hWc hWint hg a N ha hcoc hloc hstep hker hine hdec hN hGZ
  obtain ⟨z0, hz0O, hz0⟩ := GlobalTheory.T.exists_integral_limit_compatible_modPrimePow l c (G ℚ Ω × Fin 2) (fun n p => a n p.1 p.2) (fun n p => ha n p.1 p.2)
    (fun n p => hstep n p.1 p.2)
  let z : G ℚ Ω → Fin 2 → Qbar l := fun s i => z0 (s, i)
  have hzO : ∀ s i, z s i ∈ c.O := fun s i => hz0O (s, i)
  have hza : ∀ n s, Cv n (z s) (a n s) := fun n s i => hz0 n (s, i)
  have hZ : z ∈ Z1 (Loc.colRep W) := GlobalTheory.T.limit_of_approximate_cocycles l Ω W c hWint a z hcoc hloc hza
  have hcol : ∀ s (v : Fin 2 → Qbar l), Loc.colRep W s v = mat W s *ᵥ v := fun s v => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  have hrow : ∀ s (y : Fin 2 → Qbar l) i, (fun j => (mat W s - 1) i j) ⬝ᵥ y = (mat W s *ᵥ y - y) i := by
    intro s y i
    show ((mat W s - 1) *ᵥ y) i = _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hzker : ∀ b ∈ (toGS Ω (S : Set Pl)).ker, z b = 0 := by
    intro b hb
    funext i
    refine eq_zero_of_forall_norm_le _ fun n => ?_
    have h := cg_trans (hza n b i) (hker n b hb i)
    simp only [Cg, Pi.zero_apply, sub_zero] at h
    exact h
  have hexact : ∀ H : Subgroup (G ℚ Ω), (∀ n, ∃ y : Fin 2 → Qbar l, ∀ s ∈ H, Cv n (a n s) (mat W s *ᵥ y - y)) →
      ∃ x : Fin 2 → Qbar l, ∀ s ∈ H, z s = mat W s *ᵥ x - x := by
    intro H hH
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL l (↥H × Fin 2) 2 (fun p j => (mat W p.1 - 1) p.2 j) (fun p => z p.1 p.2) (fun n => by
      obtain ⟨y, hy⟩ := hH n
      refine ⟨y, fun p => ?_⟩
      have h := cg_trans (hza n p.1 p.2) (hy p.1 p.1.2 p.2)
      rw [← hrow] at h
      exact h)
    exact ⟨x, fun s hs => funext fun i => by rw [← hrow]; exact hx (⟨s, hs⟩, i)⟩
  have hUnr : Unr W z := by
    intro w hw
    refine ⟨placeOf Ω w, isPlaceOver_placeOf Ω w, ?_⟩
    by_cases hwS : w ∈ S
    · exact hexact (Ine (F := ℚ) (placeOf Ω w)) fun n => by
        obtain ⟨y, -, hy⟩ := hine n w hwS hw _ (isPlaceOver_placeOf Ω w)
        exact ⟨y, hy⟩
    · refine ⟨0, fun s hs => ?_⟩
      have hsN : s ∈ (toGS Ω (S : Set Pl)).ker := by
        show s ∈ (QuotientGroup.mk' (NS Ω (S : Set Pl))).ker
        rw [QuotientGroup.ker_mk']
        apply Subgroup.le_topologicalClosure
        apply Subgroup.subset_normalClosure
        simp only [Set.mem_iUnion]
        exact ⟨w, by simpa using hwS, placeOf Ω w, isPlaceOver_placeOf Ω w, hs⟩
      rw [hzker s hsN]
      simp
  have hGr : Gr W A z := by
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL l (↥(Dec (F := ℚ) A)) 1 (fun s _ => mat W s 1 1 - 1) (fun s => z s 1) (fun n => by
      obtain ⟨y, -, hy⟩ := hdec n
      refine ⟨fun _ => y, fun s => ?_⟩
      have h := cg_trans (hza n s 1) (hy s s.2)
      have e : (fun _ : Fin 1 => mat W s 1 1 - 1) ⬝ᵥ (fun _ => y) = mat W s 1 1 * y - y := by
        simp [dotProduct]; ring
      rw [e]; exact h)
    refine ⟨y 0, fun s hs => ?_⟩
    have h := hy ⟨s, hs⟩
    rw [h]
    simp [dotProduct]
    ring
  obtain ⟨x, hx⟩ := (mem_coboundaries1 _ _).1 (hGZ z hZ hUnr hGr)
  obtain ⟨g, hdg⟩ := hg
  have hMO : ∀ i j, (mat W g - 1) i j ∈ c.O := by
    intro i j
    rw [Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact c.O.sub_mem (hWint g i j) c.O.one_mem
    · exact c.O.sub_mem (hWint g i j) c.O.zero_mem
  have hdO : (mat W g - 1).det ∈ c.O := by
    rw [Matrix.det_fin_two]
    exact c.O.sub_mem (c.O.mul_mem (hMO 0 0) (hMO 1 1)) (c.O.mul_mem (hMO 0 1) (hMO 1 0))
  have hadjO : ∀ i j, (mat W g - 1).adjugate i j ∈ c.O := by
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · exact hMO 1 1
    · exact c.O.neg_mem (hMO 0 1)
    · exact c.O.neg_mem (hMO 1 0)
    · exact hMO 0 0
  have hMx : (mat W g - 1) *ᵥ x = z g := by rw [hx g, hcol, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hdx : (mat W g - 1).det • x = (mat W g - 1).adjugate *ᵥ z g := by
    rw [← hMx, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨k, hk⟩ := GlobalTheory.T.memCoefRingInvertPrime_inv_of_mem_ne_zero l c _ hdO hdg
  have hxE : VecE c x := ⟨k, fun i => by
    have e : x i = ((mat W g - 1).det)⁻¹ * ((mat W g - 1).adjugate *ᵥ z g) i := by
      rw [← hdx, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdg, one_mul]
    rw [e, ← mul_assoc]
    refine c.O.mul_mem hk ?_
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hadjO i 0) (hzO g 0)) (c.O.mul_mem (hadjO i 1) (hzO g 1))⟩
  refine hN ⟨x, hxE, fun s => ?_⟩
  have h := hza N s
  rw [hx s, hcol] at h
  exact cv_symm h

end GlobalTheory.Ord2

end

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountTopSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleDimSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleDegreeSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Sections

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨q, hq, a, ha, by rw [smul_eq_mul, mul_comm]⟩`.
-/
theorem mul_mem_pow_succ (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) : a * q ∈ (Q.pow (m + 1)).sub I :=
  Submodule.subset_span ⟨q, hq, a, ha, by rw [smul_eq_mul, mul_comm]⟩

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using ha`. Consider the case `succ j ih`. Rewrite using `[pow_succ, ← mul_assoc, ← add_assoc]`. Conclude with `mul_mem_pow_succ Q I ih hq`.
-/
theorem mul_pow_mem_pow (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) (j : ℕ) : a * q ^ j ∈ (Q.pow (m + j)).sub I := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact mul_mem_pow_succ Q I ih hq

/- English proof (translation)
Establish `hI : ∀ l, h l ∈ Q.sub I` using `fun l => (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp (hh l) I)`. Establish `hprod : ∀ (α : Fin (r + 1) →₀ ℕ) (s : Finset (Fin (r + 1))), ∏ i ∈ s, h i ^ α i ∈ (Q.pow (∑ i ∈ s, α i)).sub I`. Introduce `α s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Rewrite using `[Finset.prod_empty, Finset.sum_empty]`. Conclude with `one_mem_twistMod_zero (S := k) I`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, mul_comm, add_comm]`. Conclude with `mul_pow_mem_pow Q I ih (hI j) (α j)`.

Rewrite using `[f.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun α hα => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial]`. Establish `hdeg : ∑ i ∈ α.support, α i = n`. Use `hf (mem_support_iff.mp hα)` as an intermediate fact.

Rewrite `this` using `[Finsupp.weight_apply, Finsupp.sum]`. Simplify using `using this`. Establish `hmem` using `hprod α α.support`. Rewrite `hmem` using `[hdeg]`. Rewrite using `[Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]`.

Conclude with `Submodule.smul_of_tower_mem _ _ hmem`.
-/
theorem aeval_mem_pow (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (I : Chart x) {f : MvPolynomial (Fin (r + 1)) k} {n : ℕ} (hf : f.IsHomogeneous n) :
    aeval h f ∈ (Q.pow n).sub I := by
  have hI : ∀ l, h l ∈ Q.sub I := fun l =>
    (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp (hh l) I)
  have hprod : ∀ (α : Fin (r + 1) →₀ ℕ) (s : Finset (Fin (r + 1))),
      ∏ i ∈ s, h i ^ α i ∈ (Q.pow (∑ i ∈ s, α i)).sub I := by
    intro α s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact one_mem_twistMod_zero (S := k) I
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, mul_comm, add_comm]
      exact mul_pow_mem_pow Q I ih (hI j) (α j)
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [aeval_monomial]
  have hdeg : ∑ i ∈ α.support, α i = n := by
    have := hf (mem_support_iff.mp hα)
    rw [Finsupp.weight_apply, Finsupp.sum] at this
    simpa using this
  have hmem := hprod α α.support
  rw [hdeg] at hmem
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact Submodule.smul_of_tower_mem _ _ hmem

/- English proof (translation)
Rewrite using `[twistMul, SubSystem.twist_twistSys_zero]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, e, hf, he, rfl⟩`. Establish `hen : e = n` using `by exact_mod_cast he`. Substitute `hen` using the available equality.

Conclude with `(Submodule.mem_iInf _).mpr fun I => (Submodule.restrictScalars_mem k _ _).mpr (aeval_mem_pow Q hh I hf)`.
-/
theorem coordGraded_le_secs (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (n : ℕ) : (coordGraded k h).piece (n : ℤ) ≤ (twistMul Q n 0).secs := by
  rw [twistMul, SubSystem.twist_twistSys_zero]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, e, hf, he, rfl⟩
  have hen : e = n := by exact_mod_cast he
  subst hen
  exact (Submodule.mem_iInf _).mpr fun I =>
    (Submodule.restrictScalars_mem k _ _).mpr (aeval_mem_pow Q hh I hf)

/- English proof (translation)
Take `⟨m, deg, gen, -, hspan⟩` from `hTF k Ω N x (twistBundle k x 0) Nb r h hx hV.mem_secs hV.generates`. Establish `e1 : (twistBundle k x 0).toSubSystem.twist (Nb.toSubSystem.pow n) = twistMul Nb.toSubSystem n 0`. Rewrite using `[twistMul, SubSystem.twist_twistSys_zero]`. Conclude with `twistSys_zero_twist _`. Establish `hle` using `hspan n`.

Rewrite `hle` using `[e1]`. Set `T : Submodule k Ω` to `⨆ j : Fin m, (homogeneousSubmodule (Fin (r + 1)) k (n - deg j)).map ((LinearMap.mulRight k (gen j)).comp (aeval h).toLinearMap)`. Establish `hT : T.FG` using `Submodule.fg_iSup _ fun j => (homogeneousSubmodule_fg (Fin (r + 1)) k (n - deg j)).map _`. Establish `hle' : Submodule.span k {z | ∃ (j : Fin m) (f : MvPolynomial (Fin (r + 1)) k) (e : ℕ), f.IsHomogeneous e ∧ e + deg j = n ∧ z = aeval h f * gen j} ≤ T`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨j, f, e, hf, hed, rfl⟩`. Use `Submodule.mem_iSup_of_mem j ⟨f, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, mem_homogeneousSubmodule]`. Use `hf using 1` and compare the differences between its conclusion and the goal. Use linear arithmetic over natural numbers and integers.

Establish `: FiniteDimensional k T` using `Module.Finite.iff_fg.mpr hT`. Conclude with `Submodule.finiteDimensional_of_le (hle.trans hle')`.
-/
theorem finite_secs_twistMul (hTF : TwistFinite.Statement.{u, w}) (Nb : LineBundle k x) {r : ℕ}
    {h : Fin (r + 1) → Ω} (hx : x ≠ 0) (hV : IsVeryAmpleBy Nb.toSubSystem h) (n : ℕ) :
    Module.Finite k (twistMul Nb.toSubSystem n 0).secs := by
  obtain ⟨m, deg, gen, -, hspan⟩ :=
    hTF k Ω N x (twistBundle k x 0) Nb r h hx hV.mem_secs hV.generates
  have e1 : (twistBundle k x 0).toSubSystem.twist (Nb.toSubSystem.pow n) =
      twistMul Nb.toSubSystem n 0 := by
    rw [twistMul, SubSystem.twist_twistSys_zero]
    exact twistSys_zero_twist _
  have hle := hspan n
  rw [e1] at hle
  let T : Submodule k Ω := ⨆ j : Fin m, (homogeneousSubmodule (Fin (r + 1)) k (n - deg j)).map
    ((LinearMap.mulRight k (gen j)).comp (aeval h).toLinearMap)
  have hT : T.FG := Submodule.fg_iSup _ fun j => (homogeneousSubmodule_fg (Fin (r + 1)) k (n - deg j)).map _
  have hle' : Submodule.span k {z | ∃ (j : Fin m) (f : MvPolynomial (Fin (r + 1)) k) (e : ℕ),
      f.IsHomogeneous e ∧ e + deg j = n ∧ z = aeval h f * gen j} ≤ T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, f, e, hf, hed, rfl⟩
    refine Submodule.mem_iSup_of_mem j ⟨f, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_homogeneousSubmodule]
    convert hf using 1
    omega
  have : FiniteDimensional k T := Module.Finite.iff_fg.mpr hT
  exact Submodule.finiteDimensional_of_le (hle.trans hle')

end Sections

/- English proof (translation)
Introduce `k _ Ω _ _ N x d Nb hZ hN`. Take `⟨r, h, hV⟩` from `hN`. Establish `hx : x ≠ 0`. Introduce and unpack `rfl`. Take `⟨i, hi⟩` from `hZ.relevant`.

Conclude with `hi ((mem_primeOf_of_isHomogeneous _ (isHomogeneous_X k i)).mpr (by simp))`. Establish `hZh` using `hDim k Ω N x (d + 1) Nb r h hZ hV`. Take `⟨⟨C, hC⟩, -, -⟩` from `hHP k Ω r h (d + 1) (Nat.le_add_left 1 d) hZh`. Establish `hnum : interNum (primeOf (S` using `k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) = NumbersDVR.intNum k (primeOfOne (S := k) h) (fun _ : Fin (d + 1) => fun _ : Unit => (1 : ℤ)) := by`. Rewrite using `[hDeg k Ω N x (d + 1) Nb r h hZ hV]`.

Conclude with `hTie k Ω r h (d + 1) (primeOf (S := k) h) (fun _ => 1) hZh`. Use `⟨C, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hC] with n hn`. Establish `hle : (Module.finrank k ((coordGraded k h).piece (n : ℤ)) : ℝ) ≤ (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ)`. Use `finite_secs_twistMul hTF Nb hx hV n` as an intermediate fact.

Conclude with `Submodule.finrank_mono (coordGraded_le_secs Nb.toSubSystem hV.mem_secs n)` after adjusting the coercions. Rewrite using `[hnum]`. Rewrite `hn` using `[Nat.add_sub_cancel]`. Use `(abs_le.mp hn).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem SectionCount.Top.proof (hHP : HilbertPositive.Statement.{u, w})
    (hTie : InterNumTie.Statement.{u, w}) (hTF : TwistFinite.Statement.{u, w})
    (hDim : VeryAmpleDim.Statement.{u, w}) (hDeg : VeryAmpleDegree.Statement.{u, w}) :
    SectionCount.Top.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb hZ hN
  obtain ⟨r, h, hV⟩ := hN
  have hx : x ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hZ.relevant
    exact hi ((mem_primeOf_of_isHomogeneous _ (isHomogeneous_X k i)).mpr (by simp))
  have hZh := hDim k Ω N x (d + 1) Nb r h hZ hV
  obtain ⟨⟨C, hC⟩, -, -⟩ := hHP k Ω r h (d + 1) (Nat.le_add_left 1 d) hZh
  have hnum : interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) =
      NumbersDVR.intNum k (primeOfOne (S := k) h) (fun _ : Fin (d + 1) => fun _ : Unit => (1 : ℤ)) := by
    rw [hDeg k Ω N x (d + 1) Nb r h hZ hV]
    exact hTie k Ω r h (d + 1) (primeOf (S := k) h) (fun _ => 1) hZh
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  have hle : (Module.finrank k ((coordGraded k h).piece (n : ℤ)) : ℝ) ≤
      (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ) := by
    have := finite_secs_twistMul hTF Nb hx hV n
    exact_mod_cast Submodule.finrank_mono (coordGraded_le_secs Nb.toSubSystem hV.mem_secs n)
  rw [hnum]
  rw [Nat.add_sub_cancel] at hn
  have := (abs_le.mp hn).1
  linarith

end

end GroundTheory.Heights₂.Heights.Kleiman

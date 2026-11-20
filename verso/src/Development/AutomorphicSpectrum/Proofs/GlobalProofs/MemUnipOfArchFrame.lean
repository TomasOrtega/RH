import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompInfRTensorInlA
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

noncomputable section
open Matrix
namespace GlobalTheory.CompanionTheory.GoodPos

open GlobalTheory.StdPar GlobalTheory.StdPar.UnipArch

section Lin

variable {A : Type} [CommRing A] {r : ℕ}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `i j h`. Rewrite `h` using `[zero_add, pow_one]`. Use `hQ i j h` as an intermediate fact.

Conclude with `⟨this, by have := hPlt i j this; rw [Fin.lt_def] at this; omega⟩`. Consider the case `succ k ih`. Introduce `i j h`. Rewrite `h` using `[pow_succ, Matrix.mul_apply]`. Take `⟨l, -, hl⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`.

Establish `h1` using `ih i l (left_ne_zero_of_mul hl)`. Establish `h2` using `hQ l j (right_ne_zero_of_mul hl)`. Use `⟨hPt i l j h1.1 h2, ?_⟩` and prove the remaining obligations. Use `hPlt l j h2` as an intermediate fact. Rewrite `this` using `[Fin.lt_def]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem pow_support (P : Fin r → Fin r → Prop) (hPt : ∀ i l j, P i l → P l j → P i j) (hPlt : ∀ i l, P i l → i < l)
    (Q : Matrix (Fin r) (Fin r) A) (hQ : ∀ i l, Q i l ≠ 0 → P i l) (k : ℕ) :
    ∀ i j, (Q ^ (k + 1)) i j ≠ 0 → P i j ∧ i.val + k + 1 ≤ j.val := by
  induction k with
  | zero =>
    intro i j h
    rw [zero_add, pow_one] at h
    have := hQ i j h
    exact ⟨this, by have := hPlt i j this; rw [Fin.lt_def] at this; omega⟩
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := ih i l (left_ne_zero_of_mul hl)
    have h2 := hQ l j (right_ne_zero_of_mul hl)
    refine ⟨hPt i l j h1.1 h2, ?_⟩
    have := hPlt l j h2
    rw [Fin.lt_def] at this
    omega

/- English proof (translation)
Establish `hQn : ∀ i l, (-Q) i l ≠ 0 → P i l` using `fun i l h => hQ i l (by simpa using h)`. Establish `hnil : (-Q) ^ (r + 1) = 0`. Use extensionality with `i j`. Assume the negation of the conclusion as `h`. Use `(pow_support P hPt hPlt (-Q) hQn r i j h).2` as an intermediate fact.

Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨∑ t ∈ Finset.range r, (-Q) ^ (t + 1), fun i l h => ?_, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[Matrix.sum_apply]`. Take `⟨t, -, ht⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`.

Conclude with `(pow_support P hPt hPlt (-Q) hQn t i l ht).1`. Establish `e` using `mul_neg_geom_sum (-Q) (r + 1)`. Rewrite `e` using `[hnil, sub_zero, sub_neg_eq_add, Finset.sum_range_succ', pow_zero, add_comm _ (1 : Matrix _ _ _)]`. Conclude with `e`.
-/
theorem exists_inv_pattern (P : Fin r → Fin r → Prop) (hPt : ∀ i l j, P i l → P l j → P i j) (hPlt : ∀ i l, P i l → i < l)
    (Q : Matrix (Fin r) (Fin r) A) (hQ : ∀ i l, Q i l ≠ 0 → P i l) :
    ∃ Q' : Matrix (Fin r) (Fin r) A, (∀ i l, Q' i l ≠ 0 → P i l) ∧ (1 + Q) * (1 + Q') = 1 := by
  have hQn : ∀ i l, (-Q) i l ≠ 0 → P i l := fun i l h => hQ i l (by simpa using h)
  have hnil : (-Q) ^ (r + 1) = 0 := by
    ext i j
    by_contra h
    have := (pow_support P hPt hPlt (-Q) hQn r i j h).2
    have := j.2
    omega
  refine ⟨∑ t ∈ Finset.range r, (-Q) ^ (t + 1), fun i l h => ?_, ?_⟩
  · rw [Matrix.sum_apply] at h
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact (pow_support P hPt hPlt (-Q) hQn t i l ht).1
  · have e := mul_neg_geom_sum (-Q) (r + 1)
    rw [hnil, sub_zero, sub_neg_eq_add, Finset.sum_range_succ', pow_zero, add_comm _ (1 : Matrix _ _ _)] at e
    exact e

end Lin

section Main

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r Xf S u hu hN`. Use `choose Nw hM hQw hPw using hN`. Set `ψ : AF F ⊗[F] E →+* Af F ⊗[F] E` to `(Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom`. Set `N : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)` to `Matrix.of fun i v => glueInf F E (fun w => Nw w i v)`. Establish `hcN : ∀ w, N.map (compInf F E w) = Nw w` using `fun w => Matrix.ext fun i v => compInf_glueInf _ w`.

Establish `hsN : N.map ψ = 0` using `Matrix.ext fun i v => sndA_glueInf _`. Establish `hcZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E) (w : InfinitePlace F), (adMat F Z).map (compInf F E w) = Z.map (inclR (F` using `F) w.Completion) := fun Z w => Matrix.ext fun i j => by show compInf F E w ((1 : AF F) ⊗ₜ[F] Z i j) = (1 : w.Completion) ⊗ₜ[F] Z i j`. Simplify using `[compInf]`. Use `set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J u).1 with hMdef`. Establish `hcM : ∀ w, M.map (compInf F E w) = (matHom _ σ J (projArch σ J w u)).1` using `fun w => Matrix.ext fun a b => by rw [matHom_projArch]; rfl`.

Establish `hsM : M.map ψ = 1` using `Matrix.ext fun a b => congrArg (fun g => (g : GL (Fin n) _).1 a b) hu`. Use `set C := adMat F Xf with hC`. Establish `hMat : M * C = C + C * N`. Use extensionality with `a b`. Apply `tens_ext` to reduce the goal to its premises.

Introduce `w`. Establish `e1 : compInf F E w ((M * C) a b) = ((M * C).map (compInf F E w)) a b` using `rfl`. Establish `e2 : compInf F E w ((C + C * N) a b) = ((C + C * N).map (compInf F E w)) a b` using `rfl`. Rewrite using `[e1, e2, Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hcM, hcN, hC, hcZ, hM w]`. Use `show ψ _ = ψ _`.

Establish `e1 : ψ ((M * C) a b) = ((M * C).map ψ) a b` using `rfl`. Establish `e2 : ψ ((C + C * N) a b) = ((C + C * N).map ψ) a b` using `rfl`. Rewrite using `[e1, e2, Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hsM, hsN, Matrix.one_mul, Matrix.mul_zero, add_zero]`. Set `P : Fin r → Fin r → Prop` to `fun i j => ∃ k ∈ S, i ≤ k ∧ k < j`. Establish `hPt : ∀ i l j, P i l → P l j → P i j` using `fun i l j ⟨k, hk, h1, h2⟩ ⟨k', hk', h1', h2'⟩ => ⟨k', hk', h1.trans (h2.le.trans h1'), h2'⟩`.

Establish `hPlt : ∀ i l, P i l → i < l` using `fun i l ⟨k, _, h1, h2⟩ => lt_of_le_of_lt h1 h2`. Establish `hQ : ∀ i l, N i l ≠ 0 → P i l`. Introduce `i l h`. Assume the negation of the conclusion as `hc`. Apply `h` to reduce the goal to its premises.

Establish `: (fun w => Nw w i l) = fun _ => 0` using `funext fun w => by`. Assume the negation of the conclusion as `h'`. Conclude with `hc (hQw w i l h')`. Use `show glueInf F E _ = 0`. Rewrite using `[this, glueInf_zero]`.

Take `⟨N', hQ', hinv⟩` from `exists_inv_pattern P hPt hPlt N hQ`. Use `set M' : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J u⁻¹).1 with hM'def`. Establish `hM'M : M' * M = 1`. Rewrite using `[hM'def, hMdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Establish `hMC : M * C = C * (1 + N)` using `by rw [hMat, Matrix.mul_add, Matrix.mul_one]`.

Establish `hM'C : M' * C = C * (1 + N')`. Combine the equalities or inequalities in the displayed calculation. Establish `hsupp : ∀ (D : Set (Fin r)) (Q : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)), (∀ i l, Q i l ≠ 0 → P i l) → (∀ i l, P i l → l ∈ D → i ∈ D) → ∀ a : Fin r → AF F ⊗[F] E, (∀ l, l ∉ D → a l = 0) → ∀ l, l ∉ D → ((1 + Q) *ᵥ a) l = 0`. Introduce `D Q hq hD a ha i hi`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, ha i hi, zero_add]`.

Use `show ∑ l, Q i l * a l = 0`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : Q i l = 0`. Rewrite using `[h, zero_mul]`. Rewrite using `[ha l (fun hl => hi (hD i l (hq i l h) hl)), mul_zero]`.

Establish `hstab : ∀ D : Set (Fin r), (∀ i l, P i l → l ∈ D → i ∈ D) → ∀ y, y ∈ colSpan F Xf D ↔ M *ᵥ y ∈ colSpan F Xf D`. Introduce `D hD y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨a, ha, rfl⟩` from `(mem_span_cols_iff C D y).1 hy`.

Use `(mem_span_cols_iff C D _).2 ⟨(1 + N) *ᵥ a, hsupp D N hQ hD a ha, ?_⟩` and prove the remaining obligations. Rewrite using `[mulVec_mulVec, mulVec_mulVec, hMC]`. Introduce `hy`. Take `⟨a, ha, hay⟩` from `(mem_span_cols_iff C D _).1 hy`. Use `(mem_span_cols_iff C D _).2 ⟨(1 + N') *ᵥ a, hsupp D N' hQ' hD a ha, ?_⟩` and prove the remaining obligations.

Rewrite using `[mulVec_mulVec, ← hM'C, ← mulVec_mulVec, hay, mulVec_mulVec, hM'M, one_mulVec]`. Use `⟨Subgroup.mem_iInf.2 fun j => ⟨fun y => hstab _ (fun i l h hl => hPt i l j h hl) y, fun y hy => ?_⟩, hstab _ (fun i l ⟨k, hk, h1, _⟩ _ => ⟨k, hk, h1⟩), fun y hy => ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[colSpan, Set.image_singleton, Submodule.mem_span_singleton]`. Take `⟨a, rfl⟩` from `hy`. Use `show M *ᵥ _ - _ ∈ _`.

Rewrite using `[mulVec_smul, ← smul_sub]`. Use `Submodule.smul_mem _ _ ((mem_span_cols_iff C _ _).2 ⟨fun i => N i j, fun l hl => ?_, ?_⟩)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hl (hQ l j h)`. Establish `e : M *ᵥ Cᵀ j = fun i => (M * C) i j`.

Use function extensionality and compare the values at `i`. Simplify using `[mulVec, dotProduct, mul_apply]`. Rewrite using `[e, hMat]`. Use function extensionality and compare the values at `i`. Use `show (C *ᵥ fun i => N i j) i = (C + C * N) i j - C i j`.

Rewrite using `[Matrix.add_apply, add_sub_cancel_left]`. Both sides reduce to the same expression. Establish `hy' : ∀ i : Fin r, (∃ k ∈ S, i ≤ k) → (adMat F (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ y) i = 0` using `fun i hi => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hy i) hi`. Establish `hyw : ∀ w : InfinitePlace F, ∀ i : Fin r, (∃ k ∈ S, i ≤ k) → ((Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F` using `F) w.Completion) *ᵥ (compInf F E w ∘ y)) i = 0 := by`. Introduce `w i hi`.

Use `congrArg (compInf F E w) (hy' i hi)` as an intermediate fact. Rewrite `this` using `[RingHom.map_mulVec, hcZ, map_zero]`. Then use the resulting hypothesis. Use `choose a ha hA using fun w => hPw w (compInf F E w ∘ y) (hyw w)`. Set `A : Fin r → AF F ⊗[F] E` to `fun i => glueInf F E (fun w => a w i)`. Establish `hcA : ∀ w, compInf F E w ∘ A = a w` using `fun w => funext fun i => compInf_glueInf _ w`.

Establish `hsA : ψ ∘ A = 0` using `funext fun i => sndA_glueInf _`. Use `(mem_span_cols_iff C _ _).2 ⟨A, fun l hl => ?_, ?_⟩` and prove the remaining obligations. Establish `: (fun w => a w l) = fun _ => 0` using `funext fun w => by`. Assume the negation of the conclusion as `h'`. Conclude with `hl (ha w l h')`.

Use `show glueInf F E _ = 0`. Rewrite using `[this, glueInf_zero]`. Use function extensionality and compare the values at `i`. Apply `tens_ext` to reduce the goal to its premises. Introduce `w`.

Establish `e1 : compInf F E w ((M *ᵥ y - y) i) = ((matHom _ σ J (projArch σ J w u)).1 *ᵥ (compInf F E w ∘ y) - compInf F E w ∘ y) i`. Rewrite using `[Pi.sub_apply, map_sub, RingHom.map_mulVec, hcM]`. Both sides reduce to the same expression. Rewrite using `[e1, congrFun (hA w) i, RingHom.map_mulVec, hC, hcZ, hcA]`. Use `show ψ _ = ψ _`.

Rewrite using `[Pi.sub_apply, map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hsM, one_mulVec, hsA, mulVec_zero]`. Simplify using the standard rewrite rules.
-/
theorem mem_unip_of_arch_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (Xf : Matrix (Fin n) (Fin r) E)
    (S : Finset (Fin r)) (u : GAd σ J), u ∈ infPts σ J →
    (∀ w : InfinitePlace F, ∃ N : Matrix (Fin r) (Fin r) (w.Completion ⊗[F] E),
      (matHom _ σ J (projArch σ J w u)).1 * Xf.map (inclR (F := F) w.Completion) =
        Xf.map (inclR (F := F) w.Completion) + Xf.map (inclR (F := F) w.Completion) * N ∧
      (∀ i j, N i j ≠ 0 → ∃ k ∈ S, i ≤ k ∧ k < j) ∧
      (∀ v : Fin n → w.Completion ⊗[F] E,
        (∀ i : Fin r, (∃ k ∈ S, i ≤ k) → ((Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F := F) w.Completion) *ᵥ v) i = 0) →
        ∃ a : Fin r → w.Completion ⊗[F] E, (∀ i, a i ≠ 0 → ∃ k ∈ S, i ≤ k) ∧
          (matHom _ σ J (projArch σ J w u)).1 *ᵥ v - v = Xf.map (inclR (F := F) w.Completion) *ᵥ a)) →
    u ∈ GlobalTheory.StdPar.unip σ J Xf S := by
  intro F E _ _ _ _ _ σ n J r Xf S u hu hN
  classical
  choose Nw hM hQw hPw using hN
  let ψ : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  let N : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := Matrix.of fun i v => glueInf F E (fun w => Nw w i v)
  have hcN : ∀ w, N.map (compInf F E w) = Nw w := fun w => Matrix.ext fun i v => compInf_glueInf _ w
  have hsN : N.map ψ = 0 := Matrix.ext fun i v => sndA_glueInf _
  have hcZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E) (w : InfinitePlace F),
      (adMat F Z).map (compInf F E w) = Z.map (inclR (F := F) w.Completion) := fun Z w =>
    Matrix.ext fun i j => by
      show compInf F E w ((1 : AF F) ⊗ₜ[F] Z i j) = (1 : w.Completion) ⊗ₜ[F] Z i j
      simp [compInf]
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J u).1 with hMdef
  have hcM : ∀ w, M.map (compInf F E w) = (matHom _ σ J (projArch σ J w u)).1 := fun w =>
    Matrix.ext fun a b => by rw [matHom_projArch]; rfl
  have hsM : M.map ψ = 1 := Matrix.ext fun a b =>
    congrArg (fun g => (g : GL (Fin n) _).1 a b) hu
  set C := adMat F Xf with hC
  have hMat : M * C = C + C * N := by
    ext a b
    apply tens_ext
    · intro w
      have e1 : compInf F E w ((M * C) a b) = ((M * C).map (compInf F E w)) a b := rfl
      have e2 : compInf F E w ((C + C * N) a b) = ((C + C * N).map (compInf F E w)) a b := rfl
      rw [e1, e2, Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hcM, hcN, hC, hcZ, hM w]
    · show ψ _ = ψ _
      have e1 : ψ ((M * C) a b) = ((M * C).map ψ) a b := rfl
      have e2 : ψ ((C + C * N) a b) = ((C + C * N).map ψ) a b := rfl
      rw [e1, e2, Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hsM, hsN, Matrix.one_mul,
        Matrix.mul_zero, add_zero]
  let P : Fin r → Fin r → Prop := fun i j => ∃ k ∈ S, i ≤ k ∧ k < j
  have hPt : ∀ i l j, P i l → P l j → P i j := fun i l j ⟨k, hk, h1, h2⟩ ⟨k', hk', h1', h2'⟩ =>
    ⟨k', hk', h1.trans (h2.le.trans h1'), h2'⟩
  have hPlt : ∀ i l, P i l → i < l := fun i l ⟨k, _, h1, h2⟩ => lt_of_le_of_lt h1 h2
  have hQ : ∀ i l, N i l ≠ 0 → P i l := by
    intro i l h
    by_contra hc
    apply h
    have : (fun w => Nw w i l) = fun _ => 0 := funext fun w => by
      by_contra h'
      exact hc (hQw w i l h')
    show glueInf F E _ = 0
    rw [this, glueInf_zero]
  obtain ⟨N', hQ', hinv⟩ := exists_inv_pattern P hPt hPlt N hQ
  set M' : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J u⁻¹).1 with hM'def
  have hM'M : M' * M = 1 := by
    rw [hM'def, hMdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hMC : M * C = C * (1 + N) := by rw [hMat, Matrix.mul_add, Matrix.mul_one]
  have hM'C : M' * C = C * (1 + N') := by
    calc M' * C = M' * (C * ((1 + N) * (1 + N'))) := by rw [hinv, Matrix.mul_one]
      _ = M' * (M * C) * (1 + N') := by rw [hMC]; simp only [Matrix.mul_assoc]
      _ = C * (1 + N') := by rw [← Matrix.mul_assoc, hM'M, Matrix.one_mul]
  have hsupp : ∀ (D : Set (Fin r)) (Q : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)), (∀ i l, Q i l ≠ 0 → P i l) →
      (∀ i l, P i l → l ∈ D → i ∈ D) → ∀ a : Fin r → AF F ⊗[F] E, (∀ l, l ∉ D → a l = 0) →
      ∀ l, l ∉ D → ((1 + Q) *ᵥ a) l = 0 := by
    intro D Q hq hD a ha i hi
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, ha i hi, zero_add]
    show ∑ l, Q i l * a l = 0
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h : Q i l = 0
    · rw [h, zero_mul]
    · rw [ha l (fun hl => hi (hD i l (hq i l h) hl)), mul_zero]
  have hstab : ∀ D : Set (Fin r), (∀ i l, P i l → l ∈ D → i ∈ D) →
      ∀ y, y ∈ colSpan F Xf D ↔ M *ᵥ y ∈ colSpan F Xf D := by
    intro D hD y
    constructor
    · intro hy
      obtain ⟨a, ha, rfl⟩ := (mem_span_cols_iff C D y).1 hy
      refine (mem_span_cols_iff C D _).2 ⟨(1 + N) *ᵥ a, hsupp D N hQ hD a ha, ?_⟩
      rw [mulVec_mulVec, mulVec_mulVec, hMC]
    · intro hy
      obtain ⟨a, ha, hay⟩ := (mem_span_cols_iff C D _).1 hy
      refine (mem_span_cols_iff C D _).2 ⟨(1 + N') *ᵥ a, hsupp D N' hQ' hD a ha, ?_⟩
      rw [mulVec_mulVec, ← hM'C, ← mulVec_mulVec, hay, mulVec_mulVec, hM'M, one_mulVec]
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨fun y => hstab _ (fun i l h hl => hPt i l j h hl) y, fun y hy => ?_⟩,
    hstab _ (fun i l ⟨k, hk, h1, _⟩ _ => ⟨k, hk, h1⟩), fun y hy => ?_⟩
  · rw [colSpan, Set.image_singleton, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    show M *ᵥ _ - _ ∈ _
    rw [mulVec_smul, ← smul_sub]
    refine Submodule.smul_mem _ _ ((mem_span_cols_iff C _ _).2 ⟨fun i => N i j, fun l hl => ?_, ?_⟩)
    · by_contra h
      exact hl (hQ l j h)
    · have e : M *ᵥ Cᵀ j = fun i => (M * C) i j := by
        funext i
        simp [mulVec, dotProduct, mul_apply]
      rw [e, hMat]
      funext i
      show (C *ᵥ fun i => N i j) i = (C + C * N) i j - C i j
      rw [Matrix.add_apply, add_sub_cancel_left]
      rfl
  · have hy' : ∀ i : Fin r, (∃ k ∈ S, i ≤ k) → (adMat F (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ y) i = 0 := fun i hi =>
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hy i) hi
    have hyw : ∀ w : InfinitePlace F, ∀ i : Fin r, (∃ k ∈ S, i ≤ k) →
        ((Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F := F) w.Completion) *ᵥ (compInf F E w ∘ y)) i = 0 := by
      intro w i hi
      have := congrArg (compInf F E w) (hy' i hi)
      rwa [RingHom.map_mulVec, hcZ, map_zero] at this
    choose a ha hA using fun w => hPw w (compInf F E w ∘ y) (hyw w)
    let A : Fin r → AF F ⊗[F] E := fun i => glueInf F E (fun w => a w i)
    have hcA : ∀ w, compInf F E w ∘ A = a w := fun w => funext fun i => compInf_glueInf _ w
    have hsA : ψ ∘ A = 0 := funext fun i => sndA_glueInf _
    refine (mem_span_cols_iff C _ _).2 ⟨A, fun l hl => ?_, ?_⟩
    · have : (fun w => a w l) = fun _ => 0 := funext fun w => by
        by_contra h'
        exact hl (ha w l h')
      show glueInf F E _ = 0
      rw [this, glueInf_zero]
    · funext i
      apply tens_ext
      · intro w
        have e1 : compInf F E w ((M *ᵥ y - y) i) =
            ((matHom _ σ J (projArch σ J w u)).1 *ᵥ (compInf F E w ∘ y) - compInf F E w ∘ y) i := by
          rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, hcM]
          rfl
        rw [e1, congrFun (hA w) i, RingHom.map_mulVec, hC, hcZ, hcA]
      · show ψ _ = ψ _
        rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hsM, one_mulVec, hsA, mulVec_zero]
        simp

end Main

end GlobalTheory.CompanionTheory.GoodPos

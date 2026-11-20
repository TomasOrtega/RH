import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliPolynomialCoefficientsIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliOperatorsCommute
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum

open Polynomial

namespace GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks

open GlobalTheory.CompanionTheory.Dblock.CentreBlocks

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _ _ i hi`. Simplify using `at hi`. Consider the case `insert a s ha ih`. Introduce `hm h`.

Use `set Q : A[X] := ∏ i ∈ s, (P i).comp (X + C (algebraMap ℂ A (c i))) with hQ`. Establish `hQm : Q.Monic` using `monic_prod_of_monic _ _ fun i hi => (hm i (Finset.mem_insert_of_mem hi)).comp_X_add_C _`. Establish `hQe : ∀ t : ℂ, Q.eval (algebraMap ℂ A t) = ∏ i ∈ s, (P i).eval (algebraMap ℂ A (t + c i))`. Introduce `t`. Rewrite using `[hQ, eval_prod]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[eval_comp, map_add]`. Establish `key` using `GlobalTheory.T.monic_factor_coefficients_integral A (P a) Q (c a) 0 (hm a (Finset.mem_insert_self a s)) hQm (fun u => by`. Rewrite using `[add_zero, hQe]`. Use `h u` as an intermediate fact.

Rewrite using `[Finset.prod_insert ha] at this)` and apply the resulting hypothesis. Introduce `i hi k`. Break down `Finset.mem_insert.1 hi with rfl | hi'` into its components or cases. Conclude with `(key k).1`. Use `ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)) (fun u => ?_) i hi' k` and prove the remaining obligations.

Rewrite using `[← hQe]`. Conclude with `isIntegral_eval Q (fun k => (key k).2) _ isIntegral_algebraMap`.
-/
theorem isIntegral_coeff_of_shifted_prod {ι : Type} [DecidableEq ι] {A : Type} [CommRing A]
    [Algebra ℂ A] (P : ι → A[X]) (c : ι → ℂ) (s : Finset ι) :
    (∀ i ∈ s, (P i).Monic) →
    (∀ u : ℂ, IsIntegral ℂ (∏ i ∈ s, (P i).eval (algebraMap ℂ A (u + c i)))) →
    ∀ i ∈ s, ∀ k, IsIntegral ℂ ((P i).coeff k) := by
  induction s using Finset.induction_on with
  | empty => intro _ _ i hi; simp at hi
  | insert a s ha ih =>
    intro hm h
    set Q : A[X] := ∏ i ∈ s, (P i).comp (X + C (algebraMap ℂ A (c i))) with hQ
    have hQm : Q.Monic := monic_prod_of_monic _ _ fun i hi =>
      (hm i (Finset.mem_insert_of_mem hi)).comp_X_add_C _
    have hQe : ∀ t : ℂ, Q.eval (algebraMap ℂ A t) =
        ∏ i ∈ s, (P i).eval (algebraMap ℂ A (t + c i)) := by
      intro t
      rw [hQ, eval_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [eval_comp, map_add]
    have key := GlobalTheory.T.monic_factor_coefficients_integral A (P a) Q (c a) 0 (hm a (Finset.mem_insert_self a s)) hQm (fun u => by
      rw [add_zero, hQe]
      have := h u
      rwa [Finset.prod_insert ha] at this)
    intro i hi k
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · exact (key k).1
    · refine ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)) (fun u => ?_) i hi' k
      rw [← hQe]
      exact isIntegral_eval Q (fun k => (key k).2) _ isIntegral_algebraMap

/- English proof (translation)
Set `s : Set (Module.End ℂ V)` to `Set.range fun p : Fin c × ℂ => R p.1 p.2`. Establish `hcs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x`. Introduce and unpack `_ ⟨p, rfl⟩ _ ⟨q, rfl⟩`. Conclude with `(hcomm _ _ _ _).eq`. Use `letI : CommRing (Algebra.adjoin ℂ s) := Algebra.adjoinCommRingOfComm ℂ hcs`.

Establish `hpres : Algebra.adjoin ℂ s ≤ preserving I`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `hI p.1 p.2`. Set `Y : Ideal (Algebra.adjoin ℂ s)` to `{ carrier := {x | ∀ F ∈ W₀, (x : Module.End ℂ V) F ∈ I} add_mem' := fun {x y} hx hy F hF => by`.

Simplify using `using I.add_mem (hx F hF) (hy F hF)`. Use the proof step `zero_mem' := fun F _ => by simp`. Use the proof step `smul_mem' := fun c x hx F hF => by show ((c * x : Algebra.adjoin ℂ s) : Module.End ℂ V) F ∈ I`. Rewrite using `[Subalgebra.coe_mul, Module.End.mul_apply]`. Conclude with `hpres c.2 _ (hx F hF) }`.

Set `π` to `Ideal.Quotient.mkₐ ℂ Y`. Establish `hRmem : ∀ i u, R i u ∈ Algebra.adjoin ℂ s` using `fun i u => Algebra.subset_adjoin ⟨(i, u), rfl⟩`. Establish `hamem : ∀ i k, a i k ∈ Algebra.adjoin ℂ s` using `fun i k => (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin ℂ s))).mpr (by rintro x ⟨u, rfl⟩; exact hRmem i u) (haspan i k)`. Set `P : Fin c → (Algebra.adjoin ℂ s ⧸ Y)[X]` to `fun i => sumPoly (fun k => π ⟨a i k, hamem i k⟩) (d i)`. Establish `hPm : ∀ i, (P i).Monic` using `fun i => sumPoly_monic _ _ (by`.

Establish `: (⟨a i (d i), hamem i (d i)⟩ : Algebra.adjoin ℂ s) = 1` using `Subtype.ext (ha1 i)`. Simplify using `only [this, map_one])`. Establish `hPev : ∀ i (t : ℂ), (P i).eval (algebraMap ℂ _ t) = π ⟨R i t, hRmem i t⟩`. Introduce `i t`. Establish `: (⟨R i t, hRmem i t⟩ : Algebra.adjoin ℂ s) = ∑ k ∈ Finset.range (d i + 1), t ^ k • (⟨a i k, hamem i k⟩ : Algebra.adjoin ℂ s)`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hform i t]`. Rewrite using `[this, map_sum, sumPoly_eval]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, map_pow, mul_comm]`.

Set `φ : Algebra.adjoin ℂ s →* Module.End ℂ V` to `{ toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl }`. Establish `hprod : ∀ u : ℂ, IsIntegral ℂ (∏ i ∈ Finset.univ, (P i).eval (algebraMap ℂ (Algebra.adjoin ℂ s ⧸ Y) (u + sh i)))`. Introduce `u`. Take `⟨z, hz⟩` from `hB u`. Establish `hcoe : φ (∏ i, (⟨R i (u + sh i), hRmem i _⟩ : Algebra.adjoin ℂ s)) = (List.ofFn fun i => R i (u + sh i)).prod`.

Rewrite using `[← List.prod_ofFn, map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression. Establish `hval : ∏ i ∈ Finset.univ, (P i).eval (algebraMap ℂ (Algebra.adjoin ℂ s ⧸ Y) (u + sh i)) = algebraMap ℂ _ z`. Repeatedly rewrite using `[hPev]`. Rewrite using `[← map_prod, ← AlgHom.commutes π z, ← sub_eq_zero, ← map_sub, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`.

Introduce `F hF`. Establish `h1` using `hz F hF`. Rewrite `h1` using `[← hcoe]`. Simplify `h1` using `[φ, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[hval]`.

Conclude with `isIntegral_algebraMap`. Establish `hcoef` using `isIntegral_coeff_of_shifted_prod P sh Finset.univ (fun i _ => hPm i) hprod`. Introduce `i w`. Establish `hint : IsIntegral ℂ (π ⟨R i w, hRmem i w⟩)`. Rewrite using `[← hPev]`.

Conclude with `isIntegral_eval (P i) (fun k => hcoef i (Finset.mem_univ i) k) _ isIntegral_algebraMap`. Take `⟨q, hqm, hq0⟩` from `hint`. Use `⟨q, hqm, fun F hF => ?_⟩` and prove the remaining obligations. Rewrite `hq0` using `[← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`. Use `hq0 F hF` as an intermediate fact.

Rewrite `this` using `[Polynomial.aeval_subalgebra_coe]`. Then use the resulting hypothesis.
-/
theorem monic_of_shifted_prod {V : Type} [AddCommGroup V] [Module ℂ V] {c : ℕ} (d : Fin c → ℕ)
    (R : Fin c → ℂ → Module.End ℂ V) (a : Fin c → ℕ → Module.End ℂ V)
    (I : Submodule ℂ V) (W₀ : Set V) (sh : Fin c → ℂ)
    (hcomm : ∀ i j u v, Commute (R i u) (R j v))
    (hI : ∀ i u, ∀ F ∈ I, R i u F ∈ I)
    (ha1 : ∀ i, a i (d i) = 1)
    (haspan : ∀ i k, a i k ∈ Submodule.span ℂ (Set.range (R i)))
    (hform : ∀ i u, R i u = ∑ k ∈ Finset.range (d i + 1), u ^ k • a i k)
    (hB : ∀ u : ℂ, ∃ s : ℂ, ∀ F ∈ W₀,
      (List.ofFn fun i => R i (u + sh i)).prod F - s • F ∈ I) :
    ∀ i w, ∃ q : ℂ[X], q.Monic ∧ ∀ F ∈ W₀, aeval (R i w) q F ∈ I := by
  let s : Set (Module.End ℂ V) := Set.range fun p : Fin c × ℂ => R p.1 p.2
  have hcs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact (hcomm _ _ _ _).eq
  letI : CommRing (Algebra.adjoin ℂ s) := Algebra.adjoinCommRingOfComm ℂ hcs
  have hpres : Algebra.adjoin ℂ s ≤ preserving I := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    exact hI p.1 p.2
  let Y : Ideal (Algebra.adjoin ℂ s) :=
    { carrier := {x | ∀ F ∈ W₀, (x : Module.End ℂ V) F ∈ I}
      add_mem' := fun {x y} hx hy F hF => by
        simpa using I.add_mem (hx F hF) (hy F hF)
      zero_mem' := fun F _ => by simp
      smul_mem' := fun c x hx F hF => by
        show ((c * x : Algebra.adjoin ℂ s) : Module.End ℂ V) F ∈ I
        rw [Subalgebra.coe_mul, Module.End.mul_apply]
        exact hpres c.2 _ (hx F hF) }
  let π := Ideal.Quotient.mkₐ ℂ Y
  have hRmem : ∀ i u, R i u ∈ Algebra.adjoin ℂ s := fun i u =>
    Algebra.subset_adjoin ⟨(i, u), rfl⟩
  have hamem : ∀ i k, a i k ∈ Algebra.adjoin ℂ s := fun i k =>
    (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin ℂ s))).mpr
      (by rintro x ⟨u, rfl⟩; exact hRmem i u) (haspan i k)
  let P : Fin c → (Algebra.adjoin ℂ s ⧸ Y)[X] := fun i =>
    sumPoly (fun k => π ⟨a i k, hamem i k⟩) (d i)
  have hPm : ∀ i, (P i).Monic := fun i => sumPoly_monic _ _ (by
    have : (⟨a i (d i), hamem i (d i)⟩ : Algebra.adjoin ℂ s) = 1 := Subtype.ext (ha1 i)
    simp only [this, map_one])
  have hPev : ∀ i (t : ℂ), (P i).eval (algebraMap ℂ _ t) = π ⟨R i t, hRmem i t⟩ := by
    intro i t
    have : (⟨R i t, hRmem i t⟩ : Algebra.adjoin ℂ s)
        = ∑ k ∈ Finset.range (d i + 1), t ^ k • (⟨a i k, hamem i k⟩ : Algebra.adjoin ℂ s) := by
      apply Subtype.ext; simp [hform i t]
    rw [this, map_sum, sumPoly_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Algebra.smul_def, map_pow, mul_comm]
  let φ : Algebra.adjoin ℂ s →* Module.End ℂ V :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hprod : ∀ u : ℂ, IsIntegral ℂ
      (∏ i ∈ Finset.univ, (P i).eval (algebraMap ℂ (Algebra.adjoin ℂ s ⧸ Y) (u + sh i))) := by
    intro u
    obtain ⟨z, hz⟩ := hB u
    have hcoe : φ (∏ i, (⟨R i (u + sh i), hRmem i _⟩ : Algebra.adjoin ℂ s)) =
        (List.ofFn fun i => R i (u + sh i)).prod := by
      rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
      rfl
    have hval : ∏ i ∈ Finset.univ, (P i).eval (algebraMap ℂ (Algebra.adjoin ℂ s ⧸ Y) (u + sh i)) =
        algebraMap ℂ _ z := by
      simp_rw [hPev]
      rw [← map_prod, ← AlgHom.commutes π z, ← sub_eq_zero, ← map_sub, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      intro F hF
      have h1 := hz F hF
      rw [← hcoe] at h1
      simpa [φ, Algebra.algebraMap_eq_smul_one] using h1
    rw [hval]
    exact isIntegral_algebraMap
  have hcoef := isIntegral_coeff_of_shifted_prod P sh Finset.univ (fun i _ => hPm i) hprod
  intro i w
  have hint : IsIntegral ℂ (π ⟨R i w, hRmem i w⟩) := by
    rw [← hPev]
    exact isIntegral_eval (P i) (fun k => hcoef i (Finset.mem_univ i) k) _ isIntegral_algebraMap
  obtain ⟨q, hqm, hq0⟩ := hint
  refine ⟨q, hqm, fun F hF => ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hq0
  have := hq0 F hF
  rwa [Polynomial.aeval_subalgebra_coe] at this

/- English proof (translation)
Establish `hle : Algebra.adjoin ℂ T ≤ Subalgebra.centralizer ℂ ({x} : Set A)`. Use `Algebra.adjoin_le fun t ht => ?_` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_centralizer_iff]`. Introduce and unpack `_ rfl`. Conclude with `(h t ht).symm.eq`.

Establish `: Commute x w` using `(Subalgebra.mem_centralizer_iff ℂ).1 (hle hw) x rfl`. Conclude with `this.symm`.
-/
theorem commute_of_mem_adjoin {A : Type} [Ring A] [Algebra ℂ A] {T : Set A} {x w : A}
    (h : ∀ t ∈ T, Commute t x) (hw : w ∈ Algebra.adjoin ℂ T) : Commute w x := by
  have hle : Algebra.adjoin ℂ T ≤ Subalgebra.centralizer ℂ ({x} : Set A) := by
    refine Algebra.adjoin_le fun t ht => ?_
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact (h t ht).symm.eq
  have : Commute x w := (Subalgebra.mem_centralizer_iff ℂ).1 (hle hw) x rfl
  exact this.symm

/- English proof (translation)
Set `S : Subalgebra ℂ (Module.End ℂ W)` to `Algebra.adjoin ℂ (Set.range fun pq : Fin N × Fin N => Xf pq.1 pq.2)`. Establish `hSE : ∀ p q, Xf p q ∈ S` using `fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩`. Establish `hSW : S ≤ preserving Wn` using `Algebra.adjoin_le (by rintro _ ⟨pq, rfl⟩; exact hWn pq.1 pq.2)`. Set `Xs : Fin N → Fin N → S` to `fun p q => ⟨Xf p q, hSE p q⟩`. Establish `hXr : Formalism.REAL.GlRel Xs` using `fun a b c' d => Subtype.ext (by`.

Use `hX a b c' d` as an intermediate fact. Apply the tactic sequence `split_ifs at this ⊢ <;> simpa [Xs] using this)`. Establish `key` using `GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal S n h Xs hXr u`. Set `Lm : S →ₗ[ℂ] Q` to `{ toFun := fun w => L ((w : Module.End ℂ W) G) map_add' := fun a b => by simp map_smul' := fun r a => by simp }`. Establish `hker : Submodule.span ℂ {y : S | ∃ (p q : Fin N) (w : S), GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q ∧ y = Xs p q * w} ≤ LinearMap.ker Lm`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, q, w, hpq, rfl⟩`. Express the relevant statement in the definitionally equal form `L (Xf p q ((w : Module.End ℂ W) G)) = 0`. Conclude with `hL p q hpq _ (hSW w.2 G hG)`. Establish `h1` using `hker key`.

Rewrite `h1` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Establish `hLv : ∀ w : S, Lm w = L ((S.val w) G)` using `fun _ => rfl`. Rewrite `h1` using `[hLv, hLv, map_list_prod, List.map_ofFn, GlobalTheory.CuspRep.map_qdet]`. Simplify using `only [Function.comp_def, GlobalTheory.CuspRep.map_qdet] at h1`. Conclude with `h1`.
-/
theorem map_qdet_eq_map_blocks {W Q : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup Q]
    [Module ℂ Q] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (Xf : Fin N → Fin N → Module.End ℂ W) (hX : Formalism.REAL.GlRel Xf) (Wn : Submodule ℂ W)
    (hWn : ∀ p q, ∀ F ∈ Wn, Xf p q F ∈ Wn) (L : W →ₗ[ℂ] Q)
    (hL : ∀ p q, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q →
      ∀ F ∈ Wn, L (Xf p q F) = 0) (u : ℂ) (G : W) (hG : G ∈ Wn) :
    L (Formalism.REAL.qdet Xf (u + ((N : ℂ) - 1) / 2) G) =
      L ((List.ofFn fun i : Fin c => Formalism.REAL.qdet
        (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩))
        (u + ((n i : ℂ) - 1) / 2 - (GlobalTheory.SmGL.modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod G) := by
  let S : Subalgebra ℂ (Module.End ℂ W) :=
    Algebra.adjoin ℂ (Set.range fun pq : Fin N × Fin N => Xf pq.1 pq.2)
  have hSE : ∀ p q, Xf p q ∈ S := fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩
  have hSW : S ≤ preserving Wn :=
    Algebra.adjoin_le (by rintro _ ⟨pq, rfl⟩; exact hWn pq.1 pq.2)
  let Xs : Fin N → Fin N → S := fun p q => ⟨Xf p q, hSE p q⟩
  have hXr : Formalism.REAL.GlRel Xs := fun a b c' d => Subtype.ext (by
    have := hX a b c' d
    split_ifs at this ⊢ <;> simpa [Xs] using this)
  have key := GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal S n h Xs hXr u
  let Lm : S →ₗ[ℂ] Q :=
    { toFun := fun w => L ((w : Module.End ℂ W) G)
      map_add' := fun a b => by simp
      map_smul' := fun r a => by simp }
  have hker : Submodule.span ℂ {y : S | ∃ (p q : Fin N) (w : S),
      GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q ∧
        y = Xs p q * w} ≤ LinearMap.ker Lm := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, q, w, hpq, rfl⟩
    change L (Xf p q ((w : Module.End ℂ W) G)) = 0
    exact hL p q hpq _ (hSW w.2 G hG)
  have h1 := hker key
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
  have hLv : ∀ w : S, Lm w = L ((S.val w) G) := fun _ => rfl
  rw [hLv, hLv, map_list_prod, List.map_ofFn, GlobalTheory.CuspRep.map_qdet] at h1
  simp only [Function.comp_def, GlobalTheory.CuspRep.map_qdet] at h1
  exact h1

/- English proof (translation)
Introduce `W Q _ _ _ _ c N n h Xf hX Wn hWn L hL W₀ hW0 hs i₀ w₀`. Set `Rr : Fin c → ℂ → Module.End ℂ W` to `fun i u => Formalism.REAL.qdet (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) u`. Set `T : Set (Module.End ℂ W)` to `{x | ∃ (i : Fin c) (p q : Fin (n i)), x = Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)}`. Set `Sm : Subalgebra ℂ (Module.End ℂ W)` to `Algebra.adjoin ℂ T`. Establish `hTmem : ∀ (i : Fin c) (p q : Fin (n i)), Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩) ∈ Sm` using `fun i p q => Algebra.subset_adjoin ⟨i, p, q, rfl⟩`.

Establish `hSmW : Sm ≤ preserving Wn` using `Algebra.adjoin_le (by rintro _ ⟨i, p, q, rfl⟩; exact hWn _ _)`. Establish `hinj : ∀ i : Fin c, Function.Injective fun p : Fin (n i) => GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩` using `fun i => (GlobalTheory.SmGL.stdBlocks n h).injective.comp sigma_mk_injective`. Establish `hne : ∀ (i j : Fin c) (p : Fin (n i)) (r : Fin (n j)), i ≠ j → GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩ ≠ GlobalTheory.SmGL.stdBlocks n h ⟨j, r⟩`. Introduce `i j p r hij e`. Conclude with `hij (congrArg Sigma.fst ((GlobalTheory.SmGL.stdBlocks n h).injective e))`.

Establish `hglr : ∀ i : Fin c, Formalism.REAL.GlRel (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩))` using `fun i => GlobalTheory.CapHC.glRel_restrict hX _ (hinj i)`. Establish `hTR : ∀ i u, ∀ t ∈ T, Commute t (Rr i u)`. Introduce and unpack `i u _ ⟨j, p, q, rfl⟩`. Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality.

Conclude with `Commute.symm (Formalism.REAL.qDetCentral _ _ _ (hglr j) u p q)`. Use `GlobalTheory.CompanionTheory.CTFin.CapComm.commute_qdet_of (fun a b => ?_) u` and prove the remaining obligations. Use `hX (GlobalTheory.SmGL.stdBlocks n h ⟨j, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨j, q⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, a⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, b⟩)` as an intermediate fact. Rewrite `this` using `[if_neg (hne _ _ _ _ hji), if_neg (hne _ _ _ _ (Ne.symm hji)), sub_self]`. Conclude with `sub_eq_zero.1 this`.

Establish `hSR : ∀ x ∈ Sm, ∀ i u, Commute x (Rr i u)` using `fun x hx i u => commute_of_mem_adjoin (hTR i u) hx`. Establish `hRSm : ∀ i u, Rr i u ∈ Sm` using `fun i u => GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem Sm _ (fun p q => hTmem i p q) u`. Establish `hRR : ∀ i j u v, Commute (Rr i u) (Rr j v)` using `fun i j u v => hSR _ (hRSm i u) j v`. Establish `hSD : ∀ x ∈ Sm, ∀ v, Commute x (Formalism.REAL.qdet Xf v)` using `fun x hx v => commute_of_mem_adjoin (by`. Introduce and unpack `_ ⟨i, p, q, rfl⟩`.

Conclude with `Commute.symm (Formalism.REAL.qDetCentral _ _ _ hX v _ _)) hx`. Set `sh : Fin c → ℂ` to `fun i => ((n i : ℂ) - 1) / 2 - (GlobalTheory.SmGL.modExp (fun i => Fin (n i)) i : ℂ) / 2`. Establish `hSB : ∀ x ∈ Sm, ∀ u, Commute x (List.ofFn fun i => Rr i (u + sh i)).prod` using `fun x hx u => Commute.list_prod_right _ _ (fun y hy => by`. Take `⟨i, rfl⟩` from `List.mem_ofFn.mp hy`. Conclude with `hSR x hx _ _)`.

Set `I : Submodule ℂ W` to `{ carrier := {F | ∀ x ∈ Sm, L (x F) = 0} add_mem' := fun {a b} ha hb x hx => by`. Rewrite using `[map_add, map_add, ha x hx, hb x hx, add_zero]`. Use the proof step `zero_mem' := fun x _ => by simp`. Use the proof step `smul_mem' := fun r a ha x hx => by`. Rewrite using `[map_smul, map_smul, ha x hx, smul_zero] }`.

Establish `hIR : ∀ i u, ∀ F ∈ I, Rr i u F ∈ I` using `fun i u F hF x hx => by`. Use `hF (x * Rr i u) (Sm.mul_mem hx (hRSm i u))` as an intermediate fact. Simplify using `using this`. Establish `hDB : ∀ u, ∀ F ∈ Wn, Formalism.REAL.qdet Xf (u + ((N : ℂ) - 1) / 2) F - (List.ofFn fun i => Rr i (u + sh i)).prod F ∈ I`. Introduce `u F hF x hx`.

Establish `h1` using `map_qdet_eq_map_blocks n h Xf hX Wn hWn L hL u (x F) (hSmW hx F hF)`. Simplify using `only [add_sub_assoc] at h1`. Establish `e1 : x (Formalism.REAL.qdet Xf (u + ((N : ℂ) - 1) / 2) F) = Formalism.REAL.qdet Xf (u + ((N : ℂ) - 1) / 2) (x F)` using `LinearMap.congr_fun (hSD x hx _).eq F`. Establish `e2 : x ((List.ofFn fun i => Rr i (u + sh i)).prod F) = (List.ofFn fun i => Rr i (u + sh i)).prod (x F)` using `LinearMap.congr_fun (hSB x hx u).eq F`. Rewrite using `[map_sub, map_sub, sub_eq_zero, e1, e2]`.

Conclude with `h1`. Establish `hBs : ∀ u : ℂ, ∃ s : ℂ, ∀ F ∈ W₀, (List.ofFn fun i => Rr i (u + sh i)).prod F - s • F ∈ I`. Introduce `u`. Take `⟨s, hs'⟩` from `hs (u + ((N : ℂ) - 1) / 2)`. Use `⟨s, fun F hF => ?_⟩` and prove the remaining obligations.

Use `I.neg_mem (hDB u F (hW0 hF))` as an intermediate fact. Rewrite `this` using `[hs' F hF, neg_sub]`. Conclude with `this`. Use `choose a ha1 haspan hform using fun i : Fin c => GlobalTheory.CompanionTheory.CTFin.QdetCoeff.qdet_shift_coeff (Module.End ℂ W) (n i) (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) 0`. Simplify using `only [add_zero] at haspan hform`.

Take `⟨q, hqm, hq⟩` from `monic_of_shifted_prod n Rr a I W₀ sh hRR hIR ha1 haspan hform hBs i₀ w₀`. Use `⟨q, hqm, fun F hF => ?_⟩` and prove the remaining obligations. Use `hq F hF 1 Sm.one_mem` as an intermediate fact. Simplify using `using this`.
-/
theorem monic_relations_along_block : ∀ (W Q : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup Q] [Module ℂ Q] (c N : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (Xf : Fin N → Fin N → Module.End ℂ W), Formalism.REAL.GlRel Xf → ∀ Wn : Submodule ℂ W, (∀ p q, ∀ F ∈ Wn, Xf p q F ∈ Wn) →
    ∀ L : W →ₗ[ℂ] Q, (∀ p q, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q → ∀ F ∈ Wn, L (Xf p q F) = 0) →
    ∀ W₀ : Set W, W₀ ⊆ Wn → (∀ v : ℂ, ∃ s : ℂ, ∀ F ∈ W₀, Formalism.REAL.qdet Xf v F = s • F) →
    ∀ (i : Fin c) (w : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀,
      L (Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) w) q F) = 0 := by
  intro W Q _ _ _ _ c N n h Xf hX Wn hWn L hL W₀ hW0 hs i₀ w₀
  let Rr : Fin c → ℂ → Module.End ℂ W := fun i u => Formalism.REAL.qdet
    (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) u
  let T : Set (Module.End ℂ W) := {x | ∃ (i : Fin c) (p q : Fin (n i)),
    x = Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)}
  let Sm : Subalgebra ℂ (Module.End ℂ W) := Algebra.adjoin ℂ T
  have hTmem : ∀ (i : Fin c) (p q : Fin (n i)),
      Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩) ∈ Sm :=
    fun i p q => Algebra.subset_adjoin ⟨i, p, q, rfl⟩
  have hSmW : Sm ≤ preserving Wn :=
    Algebra.adjoin_le (by rintro _ ⟨i, p, q, rfl⟩; exact hWn _ _)
  have hinj : ∀ i : Fin c, Function.Injective fun p : Fin (n i) => GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩ :=
    fun i => (GlobalTheory.SmGL.stdBlocks n h).injective.comp sigma_mk_injective
  have hne : ∀ (i j : Fin c) (p : Fin (n i)) (r : Fin (n j)), i ≠ j →
      GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩ ≠ GlobalTheory.SmGL.stdBlocks n h ⟨j, r⟩ := by
    intro i j p r hij e
    exact hij (congrArg Sigma.fst ((GlobalTheory.SmGL.stdBlocks n h).injective e))
  have hglr : ∀ i : Fin c, Formalism.REAL.GlRel
      (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) :=
    fun i => GlobalTheory.CapHC.glRel_restrict hX _ (hinj i)
  have hTR : ∀ i u, ∀ t ∈ T, Commute t (Rr i u) := by
    rintro i u _ ⟨j, p, q, rfl⟩
    by_cases hji : j = i
    · subst hji
      exact Commute.symm (Formalism.REAL.qDetCentral _ _ _ (hglr j) u p q)
    · refine GlobalTheory.CompanionTheory.CTFin.CapComm.commute_qdet_of (fun a b => ?_) u
      have := hX (GlobalTheory.SmGL.stdBlocks n h ⟨j, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨j, q⟩)
        (GlobalTheory.SmGL.stdBlocks n h ⟨i, a⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, b⟩)
      rw [if_neg (hne _ _ _ _ hji), if_neg (hne _ _ _ _ (Ne.symm hji)), sub_self] at this
      exact sub_eq_zero.1 this
  have hSR : ∀ x ∈ Sm, ∀ i u, Commute x (Rr i u) := fun x hx i u =>
    commute_of_mem_adjoin (hTR i u) hx
  have hRSm : ∀ i u, Rr i u ∈ Sm := fun i u =>
    GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem Sm _ (fun p q => hTmem i p q) u
  have hRR : ∀ i j u v, Commute (Rr i u) (Rr j v) := fun i j u v => hSR _ (hRSm i u) j v
  have hSD : ∀ x ∈ Sm, ∀ v, Commute x (Formalism.REAL.qdet Xf v) := fun x hx v =>
    commute_of_mem_adjoin (by
      rintro _ ⟨i, p, q, rfl⟩
      exact Commute.symm (Formalism.REAL.qDetCentral _ _ _ hX v _ _)) hx
  let sh : Fin c → ℂ := fun i =>
    ((n i : ℂ) - 1) / 2 - (GlobalTheory.SmGL.modExp (fun i => Fin (n i)) i : ℂ) / 2
  have hSB : ∀ x ∈ Sm, ∀ u, Commute x (List.ofFn fun i => Rr i (u + sh i)).prod :=
    fun x hx u => Commute.list_prod_right _ _ (fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact hSR x hx _ _)
  let I : Submodule ℂ W :=
    { carrier := {F | ∀ x ∈ Sm, L (x F) = 0}
      add_mem' := fun {a b} ha hb x hx => by
        rw [map_add, map_add, ha x hx, hb x hx, add_zero]
      zero_mem' := fun x _ => by simp
      smul_mem' := fun r a ha x hx => by
        rw [map_smul, map_smul, ha x hx, smul_zero] }
  have hIR : ∀ i u, ∀ F ∈ I, Rr i u F ∈ I := fun i u F hF x hx => by
    have := hF (x * Rr i u) (Sm.mul_mem hx (hRSm i u))
    simpa using this
  have hDB : ∀ u, ∀ F ∈ Wn, Formalism.REAL.qdet Xf (u + ((N : ℂ) - 1) / 2) F -
      (List.ofFn fun i => Rr i (u + sh i)).prod F ∈ I := by
    intro u F hF x hx
    have h1 := map_qdet_eq_map_blocks n h Xf hX Wn hWn L hL u (x F) (hSmW hx F hF)
    simp only [add_sub_assoc] at h1
    have e1 : x (Formalism.REAL.qdet Xf (u + ((N : ℂ) - 1) / 2) F) =
        Formalism.REAL.qdet Xf (u + ((N : ℂ) - 1) / 2) (x F) :=
      LinearMap.congr_fun (hSD x hx _).eq F
    have e2 : x ((List.ofFn fun i => Rr i (u + sh i)).prod F) =
        (List.ofFn fun i => Rr i (u + sh i)).prod (x F) :=
      LinearMap.congr_fun (hSB x hx u).eq F
    rw [map_sub, map_sub, sub_eq_zero, e1, e2]
    exact h1
  have hBs : ∀ u : ℂ, ∃ s : ℂ, ∀ F ∈ W₀,
      (List.ofFn fun i => Rr i (u + sh i)).prod F - s • F ∈ I := by
    intro u
    obtain ⟨s, hs'⟩ := hs (u + ((N : ℂ) - 1) / 2)
    refine ⟨s, fun F hF => ?_⟩
    have := I.neg_mem (hDB u F (hW0 hF))
    rw [hs' F hF, neg_sub] at this
    exact this
  choose a ha1 haspan hform using fun i : Fin c =>
    GlobalTheory.CompanionTheory.CTFin.QdetCoeff.qdet_shift_coeff (Module.End ℂ W) (n i)
      (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) 0
  simp only [add_zero] at haspan hform
  obtain ⟨q, hqm, hq⟩ := monic_of_shifted_prod n Rr a I W₀ sh hRR hIR ha1 haspan hform hBs i₀ w₀
  refine ⟨q, hqm, fun F hF => ?_⟩
  have := hq F hF 1 Sm.one_mem
  simpa using this

end GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks

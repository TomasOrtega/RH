import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GradedSeriesContinuationDominatedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumHeckeEigenvalueGeneratingSeriesGLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGLStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeVectorHeckeEigenvalueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCardCosetsDiagonalDoubleCosetGLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaGL

/- English proof (translation)
Establish `hm` using `mem_Ov_of_isUnifV hϖ`. Take `⟨a, ha, k₁, hk₁, k₂, hk₂, e⟩` from `Formalism.UG.Final.CartanDecomp E w r ϖ hm hϖ g`. Establish `hg : g = k₁ * T a * k₂` using `Units.ext (by rw [e, Units.val_mul, Units.val_mul, hT]; rfl)`. Use `⟨⟨a, ha⟩, DoubleCoset.mem_doubleCoset.2 ⟨k₁, hk₁, k₂, hk₂, hg⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨a', ha'⟩ h`.

Take `⟨k₁', hk₁', k₂', hk₂', e'⟩` from `DoubleCoset.mem_doubleCoset.1 h`. Rewrite `e'` using `[hg]`. Establish `e2 : T a' = (k₁'⁻¹ * k₁) * T a * (k₂ * k₂'⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Establish `e3` using `congrArg Units.val e2`.

Rewrite `e3` using `[Units.val_mul, Units.val_mul, hT, hT]`. Conclude with `Subtype.ext (Formalism.UG.Final.CartanUnique E w r ϖ hm hϖ a a' ha ha' _ (mul_mem (inv_mem hk₁') hk₁) _ (mul_mem hk₂ (inv_mem hk₂')) e3.symm).symm`.
-/
theorem cartan_existsUnique (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E))
    (hT : ∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) (g : GL (Fin r) (w.adicCompletion E)) :
    ∃! d : {d : Fin r → ℤ // Antitone d},
      g ∈ DoubleCoset.doubleCoset (T d.1) (KGL w r : Set (GL (Fin r) (w.adicCompletion E))) (KGL w r) := by
  have hm := mem_Ov_of_isUnifV hϖ
  obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w r ϖ hm hϖ g
  have hg : g = k₁ * T a * k₂ := Units.ext (by rw [e, Units.val_mul, Units.val_mul, hT]; rfl)
  refine ⟨⟨a, ha⟩, DoubleCoset.mem_doubleCoset.2 ⟨k₁, hk₁, k₂, hk₂, hg⟩, ?_⟩
  rintro ⟨a', ha'⟩ h
  obtain ⟨k₁', hk₁', k₂', hk₂', e'⟩ := DoubleCoset.mem_doubleCoset.1 h
  rw [hg] at e'
  have e2 : T a' = (k₁'⁻¹ * k₁) * T a * (k₂ * k₂'⁻¹) := by
    calc T a' = k₁'⁻¹ * (k₁' * T a' * k₂') * k₂'⁻¹ := by group
      _ = _ := by rw [← e']; group
  have e3 := congrArg Units.val e2
  rw [Units.val_mul, Units.val_mul, hT, hT] at e3
  exact Subtype.ext (Formalism.UG.Final.CartanUnique E w r ϖ hm hϖ a a' ha ha' _ (mul_mem (inv_mem hk₁') hk₁) _
    (mul_mem hk₂ (inv_mem hk₂')) e3.symm).symm

/- English proof (translation)
Proceed by induction on `B using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons b B ih`. Simplify using `only [eulerPoly_cons]`. Conclude with `(by fun_prop : Differentiable ℂ fun X : ℂ => 1 - (b : ℂ) * (a * X)).mul ih`.
-/
theorem differentiable_eulerPoly (B : Multiset ℂˣ) (a : ℂ) : Differentiable ℂ fun X : ℂ => eulerPoly B (a * X) := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih =>
    simp only [eulerPoly_cons]
    exact (by fun_prop : Differentiable ℂ fun X : ℂ => 1 - (b : ℂ) * (a * X)).mul ih

/- English proof (translation)
Introduce `X hX` and use `((differentiable_eulerPoly B a X).inv (eulerPoly_ne_zero fun b hb => h b hb X (by simpa using hX))).differentiableWithinAt`.
-/
theorem differentiableOn_eulerFac (B : Multiset ℂˣ) (a : ℂ) (R : ℝ)
    (h : ∀ b ∈ B, ∀ X : ℂ, ‖X‖ < R → ‖(b : ℂ) * (a * X)‖ < 1) :
    DifferentiableOn ℂ (fun X => eulerFac B (a * X)) (Metric.ball 0 R) := fun X hX =>
  ((differentiable_eulerPoly B a X).inv
    (eulerPoly_ne_zero fun b hb => h b hb X (by simpa using hX))).differentiableWithinAt

end GlobalTheory.ZetaGL

namespace GlobalTheory.ZetaGL

/- English proof (translation)
Introduce `H E _ _ w r t hrt z φ hz hφ V _ _ ρ x B hx hB ℓ hℓ`. Take `⟨Cℓ, hC⟩` from `hℓ`. Take `⟨ϖ, hϖ⟩` from `exists_isUnifV w`. Establish `h0 : ϖ ≠ 0` using `SatCompare.ne_zero_of_isUnifV hϖ`. Set `T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E)` to `fun d => GlobalTheory.WeylGL.tor h0 d`.

Establish `hTv : ∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i` using `fun d => rfl`. Establish `hK : IsCommensurated (KGL w r)` using `Formalism.UG.Final.GLintComm E w r`. Establish `hmem : ∀ g, dosetInd ℂ (KGL w r) g ∈ Hecke ℂ (KGL w r)` using `fun g => Formalism.UG.Final.DosetIndMem _ _ ℂ g`. Use `choose c hc using fun d => SatCompare.exists_eigenvalue_GL hx hx _ (hmem (T d))`. Set `S : (Fin r → ℤ) → Set (GL (Fin r) (w.adicCompletion E) ⧸ KGL w r)` to `fun d => {a | a.out ∈ DoubleCoset.doubleCoset (T d) (KGL w r : Set (GL (Fin r) (w.adicCompletion E))) (KGL w r)}`.

Establish `hSfin : ∀ d, (S d).Finite` using `fun d => (Formalism.UG.P.finite_support_cosets hK (hmem (T d)).2).subset fun a ha => by`. Simplify using `only [Set.mem_setOf_eq, dosetInd]`. Rewrite using `[Set.indicator_of_mem (s := DoubleCoset.doubleCoset _ _ _) ha]`. Conclude with `one_ne_zero`. Establish `hsumS : ∀ d, ∑ᶠ a ∈ S d, ρ a.out x = c d • x` using `fun d => by`.

Rewrite using `[← (hc d).1, heckeVec, finsum_mem_def]`. Use `finsum_congr fun a => ?_` and prove the remaining obligations. Distinguish the cases in `ha : a ∈ S d`. Rewrite using `[Set.indicator_of_mem ha, dosetInd, Set.indicator_of_mem (s := DoubleCoset.doubleCoset _ _ _) ha]`. Simplify using the standard rewrite rules.

Rewrite using `[Set.indicator_of_notMem ha, dosetInd, Set.indicator_of_notMem (s := DoubleCoset.doubleCoset _ _ _) ha]`. Simplify using the standard rewrite rules. Establish `hU` using `fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r => cartan_existsUnique E w r hϖ T hTv a.out`. Use `choose D hD using fun a => (hU a).exists`. Establish `hDu : ∀ (d : {d : Fin r → ℤ // Antitone d}) (a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r), a ∈ S d.1 → D a = d` using `fun d a ha => (hU a).unique (hD a) ha`.

Set `e : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r ≃ Σ d : {d : Fin r → ℤ // Antitone d}, S d.1` to `{ toFun := fun a => ⟨D a, a, hD a⟩ invFun := fun p => p.2.1 left_inv := fun a => rfl right_inv := fun ⟨d, a, ha⟩ => by`. Establish `h1 : D a = d` using `hDu d a ha`. Substitute `h1` using the available equality. Use `rfl }`. Use `haveI : ∀ d, Fintype (S d) := fun d => (hSfin d).fintype`.

Establish `hsumF : ∀ d, ∑ a : S d, ρ (a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out x = c d • x` using `fun d => by`. Rewrite using `[← hsumS d, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]`. Use `set q : ℝ := (qV E w : ℝ) with hqdef`. Establish `hq1 : (1 : ℝ) < q` using `by show (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ); exact_mod_cast one_lt_absNorm w`. Establish `hq0 : (0 : ℝ) < q` using `by linarith`.

Use `set M : ℝ := q ^ (((r : ℝ) - 1) / 2) with hM`. Use `set ρ₀ : ℝ := q ^ (-((r : ℝ) - 1)) with hρ₀`. Establish `hM0 : 0 < M` using `Real.rpow_pos_of_pos hq0 _`. Establish `hMM : M * M * ρ₀ = 1`. Rewrite using `[hM, hρ₀, ← Real.rpow_add hq0, ← Real.rpow_add hq0, show ((r : ℝ) - 1) / 2 + ((r : ℝ) - 1) / 2 + -((r : ℝ) - 1) = 0 by ring, Real.rpow_zero]`.

Use `set cq : ℂ := (qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) with hcq`. Establish `hcqn : ‖cq‖ = M`. Rewrite using `[hcq, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (qV_ne_zero w))]`. Use `congr 1`. Simplify using the standard rewrite rules.

Establish `hsmall : ∀ β : ℂ, ‖β‖ ≤ M → ∀ X : ℂ, ‖X‖ < ρ₀ → ‖β * (cq * X)‖ < 1` using `fun β hβ X hX => by`. Rewrite using `[norm_mul, norm_mul, hcqn]`. Combine the equalities or inequalities in the displayed calculation. Use `set X₀ : ℝ := q ^ (-(((r : ℝ) + t) / 2)) with hX₀`. Establish `hX₀pos : 0 < X₀` using `Real.rpow_pos_of_pos hq0 _`.

Establish `hX₀ρ : X₀ < ρ₀` using `Real.rpow_lt_rpow_of_exponent_lt hq1 (by`. Establish `: (r : ℝ) ≤ t` using `by exact_mod_cast hrt`. Use the proof step `linarith)`. Establish `hX₀c : ((X₀ : ℝ) : ℂ) = (qV E w : ℂ) ^ (-(((r : ℂ) + t) / 2))`. Rewrite using `[hX₀, Complex.ofReal_cpow hq0.le]`.

Use `push_cast`. Both sides reduce to the same expression. Set `deg : {d : Fin r → ℤ // Antitone d} → ℕ` to `fun d => (∑ i, |d.1 i|).toNat`. Establish `hdeg : ∀ k, {d | deg d = k}.Finite` using `fun k => by`. Establish `hfin : (Set.pi Set.univ fun _ : Fin r => Set.Icc (-(k : ℤ)) k).Finite` using `Set.Finite.pi fun _ => Set.finite_Icc _ _`.

Use `(hfin.preimage Subtype.val_injective.injOn).subset fun d hd => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, deg] at hd`. Simplify using `only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]`. Introduce `i`. Establish `h1 : |d.1 i| ≤ ∑ j, |d.1 j|` using `Finset.single_le_sum (fun j _ => abs_nonneg (d.1 j)) (Finset.mem_univ i)`.

Establish `h2 : ∑ j, |d.1 j| = k` using `by rw [← hd, Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]`. Prove the components needed by the constructor for the conclusion. Combine the linear relations using `[neg_abs_le (d.1 i)]`. Combine the linear relations using `[le_abs_self (d.1 i)]`. Take `⟨δ₁, hδ₁, hs₁⟩` from `GlobalTheory.T.satake_vector_hecke_eigenvalue H E w r V ρ x B hx z ϖ hϖ T hTv c (fun d => (hc d).1)`.

Take `⟨B₀, hB₀, δ₂, hδ₂, hs₂⟩` from `GlobalTheory.T.hasSum_card_cosets_diagonalDoubleCoset_GL H E w r ϖ hϖ T hTv`. Set `a : {d : Fin r → ℤ // Antitone d} → ℂ` to `fun d => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * ℓ x`. Set `b : {d : Fin r → ℤ // Antitone d} → ℝ` to `fun d => (Nat.card (S d.1) : ℝ)`. Set `P : ℂ → ℂ` to `fun X => eulerFac (B.map (z * ·)) (cq * X) * eulerFac (B.map fun β => (z * β)⁻¹) (cq * X) * (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)) * ℓ x`. Set `P' : ℂ → ℂ` to `fun X => eulerFac B₀ (cq * X) * eulerFac (B₀.map (·⁻¹)) (cq * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)`.

Establish `hC0 : 0 ≤ Cℓ` using `(norm_nonneg _).trans (hC 1)`. Establish `hab : ∀ d, ‖a d‖ ≤ Cℓ * b d` using `fun d => by`. Establish `e1 : c d.1 * ℓ x = ∑ y : S d.1, ℓ (ρ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out x)`. Rewrite using `[← map_sum, hsumF, map_smul, smul_eq_mul]`. Establish `hz' : ‖(z : ℂ) ^ (∑ i, d.1 i)‖ = 1` using `by rw [norm_zpow, hz, _root_.one_zpow]`.

Simplify using `only [a, b]`. Rewrite using `[mul_assoc, norm_mul, hz', one_mul, e1]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Use `(Finset.sum_le_sum fun y _ => hC _).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, mul_comm]`.

Establish `hbnd : ∀ β ∈ B.map (z * ·), ‖(β : ℂ)‖ ≤ M`. Introduce `β hβ`. Take `⟨b, hb, rfl⟩` from `Multiset.mem_map.1 hβ`. Simplify `(hB b hb).1` using `[norm_mul, hz]`. Establish `hbnd' : ∀ β ∈ B.map fun β => (z * β)⁻¹, ‖(β : ℂ)‖ ≤ M`.

Introduce `β hβ`. Take `⟨b, hb, rfl⟩` from `Multiset.mem_map.1 hβ`. Simplify `(hB b hb).2` using `[norm_mul, hz, Units.val_inv_eq_inv_val]`. Establish `hbnd₀ : ∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ M` using `fun β hβ => (hB₀ β hβ).1`. Establish `hbnd₀' : ∀ β ∈ B₀.map (·⁻¹), ‖(β : ℂ)‖ ≤ M`.

Introduce `β hβ`. Take `⟨b, hb, rfl⟩` from `Multiset.mem_map.1 hβ`. Conclude with `(hB₀ b hb).2`. Establish `hpoly : Differentiable ℂ fun X : ℂ => ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)` using `by fun_prop`. Establish `hE1` using `differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd β hβ) X hX`.

Establish `hE2` using `differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd' β hβ) X hX`. Establish `hE3` using `differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd₀ β hβ) X hX`. Establish `hE4` using `differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd₀' β hβ) X hX`. Establish `hP : DifferentiableOn ℂ P (Metric.ball 0 ρ₀)` using `(((hE1.mul hE2).mul hpoly.differentiableOn).mul_const (ℓ x)).congr fun X _ => by simp only [P, Pi.mul_apply]`. Establish `hP' : DifferentiableOn ℂ P' (Metric.ball 0 ρ₀)` using `((hE3.mul hE4).mul hpoly.differentiableOn).congr fun X _ => rfl`.

Establish `hser : ∀ X : ℝ, 0 < X → X < min δ₁ δ₂ → HasSum (fun d => a d * (X : ℂ) ^ deg d) (P X) ∧ HasSum (fun d => (b d : ℂ) * (X : ℂ) ^ deg d) (P' X)` using `fun X hX h => ⟨by`. Establish `h1` using `(hs₁ X hX (lt_of_lt_of_le h (min_le_left _ _))).mul_right (ℓ x)`. Rewrite using `[show (fun d => a d * (X : ℂ) ^ deg d) = fun d : {d : Fin r → ℤ // Antitone d} => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat * ℓ x from funext fun d => by`. Simplify using `only [a, deg]`. Use the proof step `ring]`.

Conclude with `h1,`. Use `hs₂ X hX (lt_of_lt_of_le h (min_le_right _ _))⟩`. Take `⟨hA, hBs⟩` from `GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval deg hdeg a b Cℓ (min δ₁ δ₂) ρ₀ P P' (lt_min hδ₁ hδ₂) (fun d => Nat.cast_nonneg _) hab hP hP' hser (X₀ : ℂ) (by rw [Complex.norm_real, Real.norm_of_nonneg hX₀pos.le]; exact hX₀ρ)`. Establish `hφv : ∀ a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r, φ a.out = (z : ℂ) ^ (∑ i, (D a).1 i) * (X₀ : ℂ) ^ deg (D a)` using `fun a => by`. Take `⟨k₁, hk₁, k₂, hk₂, e1⟩` from `DoubleCoset.mem_doubleCoset.1 (hD a)`.

Rewrite using `[e1, hφ ϖ hϖ (D a).1 (T (D a).1) (hTv _) k₁ hk₁ k₂ hk₂]`. Use `congr 1`. Establish `hn : ((∑ i, |(D a).1 i| : ℤ) : ℂ) = ((deg (D a) : ℕ) : ℂ)`. Simplify using `only [deg]`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]`.

Rewrite using `[hn, hX₀c, ← Complex.cpow_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Set `f : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r → ℂ` to `fun a => φ a.out * ℓ (ρ a.out x)`.

Set `u : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r → ℝ` to `fun a => Cℓ * X₀ ^ deg (D a)`. Establish `hfu : ∀ a, ‖f a‖ ≤ u a` using `fun a => by`. Simplify using `only [f, u]`. Rewrite using `[hφv, norm_mul, norm_mul, norm_zpow, hz, _root_.one_zpow, one_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hX₀pos.le, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right (hC _) (pow_nonneg hX₀pos.le _)`.

Establish `hu : Summable u`. Rewrite using `[← e.symm.summable_iff]`. Use `(summable_sigma_of_nonneg fun p => mul_nonneg hC0 (pow_nonneg hX₀pos.le _)).2 ⟨fun d => Summable.of_finite, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ d : {d : Fin r → ℤ // Antitone d}, Cℓ * (b d * ‖(X₀ : ℂ)‖ ^ deg d) = ∑' y : S d.1, (u ∘ e.symm) ⟨d, y⟩` using `fun d => by`. Establish `h2 : ∀ y : S d.1, (u ∘ e.symm) ⟨d, y⟩ = Cℓ * X₀ ^ deg d` using `fun y => by show Cℓ * X₀ ^ deg (D y.1) = _`.

Rewrite using `[hDu d y.1 y.2]`. Repeatedly rewrite using `[h2]`. Rewrite using `[tsum_const, nsmul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hX₀pos.le]`. Simplify using `only [b]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `(hBs.mul_left Cℓ).congr h1`. Establish `hf : Summable f` using `Summable.of_norm_bounded hu hfu`. Establish `hfib : ∀ d : {d : Fin r → ℤ // Antitone d}, HasSum (fun y : S d.1 => (f ∘ e.symm) ⟨d, y⟩) (a d * (X₀ : ℂ) ^ deg d)` using `fun d => by`. Establish `h2 : ∀ y : S d.1, (f ∘ e.symm) ⟨d, y⟩ = (z : ℂ) ^ (∑ i, d.1 i) * (X₀ : ℂ) ^ deg d * ℓ (ρ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out x)` using `fun y => by show φ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out * _ = _`. Rewrite using `[hφv, hDu d y.1 y.2]`.

Both sides reduce to the same expression. Establish `h3 : ∑ y : S d.1, (f ∘ e.symm) ⟨d, y⟩ = a d * (X₀ : ℂ) ^ deg d`. Rewrite using `[Finset.sum_congr rfl fun y _ => h2 y, ← Finset.mul_sum, ← map_sum, hsumF, map_smul, smul_eq_mul]`. Simplify using `only [a]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h3 ▸ hasSum_fintype _`. Establish `heq : ∑' a, f a = P X₀` using `(((e.symm.hasSum_iff).2 hf.hasSum).sigma hfib).unique hA`. Establish `hfin` using `hf.hasSum`. Rewrite `hfin` using `[heq]`. Establish `hcX : cq * (X₀ : ℂ) = npow w (-((1 + (t : ℂ)) / 2))`.

Establish `hqC : (qV E w : ℂ) ≠ 0` using `by exact_mod_cast qV_ne_zero w`. Rewrite using `[hcq, hX₀c, ← Complex.cpow_add _ _ hqC]`. Use `show ((qV E w : ℕ) : ℂ) ^ _ = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hX2 : (X₀ : ℂ) ^ 2 = ((qV E w : ℂ) ^ (r + t))⁻¹`. Rewrite using `[hX₀c, ← Complex.cpow_nat_mul, show ((2 : ℕ) : ℂ) * -(((r : ℂ) + t) / 2) = -(((r + t : ℕ) : ℂ)) by push_cast; ring, Complex.cpow_neg, Complex.cpow_natCast]`. Establish `hprod : ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X₀ : ℂ) ^ 2) = ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)`. Establish `hqC : (qV E w : ℂ) ≠ 0` using `by exact_mod_cast qV_ne_zero w`. Use `Finset.prod_nbij' (fun i => r + t - i) (fun j => r + t - j) (fun i hi => ?_) (fun j hj => ?_) (fun i hi => ?_) (fun j hj => ?_) (fun i hi => ?_)` and prove the remaining obligations.

Simplify using `only [Finset.mem_range, Finset.mem_Ioc, Finset.mem_coe] at hi ⊢`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Finset.mem_range, Finset.mem_Ioc, Finset.mem_coe] at hj ⊢`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Finset.mem_range, Finset.mem_coe] at hi`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [Finset.mem_Ioc, Finset.mem_coe] at hj`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Finset.mem_range, Finset.mem_coe] at hi`. Establish `hp : (qV E w : ℂ) ^ (r + t) = (qV E w : ℂ) ^ (r + t - i) * (qV E w : ℂ) ^ i`.

Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hX2, hp]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Establish `hval : P X₀ = eulerFac (B.map (z * ·)) (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => (z * β)⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * (∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) * ℓ x`. Simplify using `only [P]`. Rewrite using `[hcX, hprod]`. Rewrite `hfin` using `[hval]`.

Conclude with `hfin`.
-/
theorem zeta_sum_GL : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r => φ a.out * ℓ (ρ a.out x)) (eulerFac (B.map (z * ·)) (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => (z * β)⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * (∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) * ℓ x) := by
  intro H E _ _ w r t hrt z φ hz hφ V _ _ ρ x B hx hB ℓ hℓ
  obtain ⟨Cℓ, hC⟩ := hℓ
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
  have h0 : ϖ ≠ 0 := SatCompare.ne_zero_of_isUnifV hϖ
  let T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E) := fun d => GlobalTheory.WeylGL.tor h0 d
  have hTv : ∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i := fun d => rfl
  have hK : IsCommensurated (KGL w r) := Formalism.UG.Final.GLintComm E w r
  have hmem : ∀ g, dosetInd ℂ (KGL w r) g ∈ Hecke ℂ (KGL w r) := fun g => Formalism.UG.Final.DosetIndMem _ _ ℂ g
  choose c hc using fun d => SatCompare.exists_eigenvalue_GL hx hx _ (hmem (T d))
  let S : (Fin r → ℤ) → Set (GL (Fin r) (w.adicCompletion E) ⧸ KGL w r) := fun d =>
    {a | a.out ∈ DoubleCoset.doubleCoset (T d) (KGL w r : Set (GL (Fin r) (w.adicCompletion E))) (KGL w r)}
  have hSfin : ∀ d, (S d).Finite := fun d =>
    (Formalism.UG.P.finite_support_cosets hK (hmem (T d)).2).subset fun a ha => by
      simp only [Set.mem_setOf_eq, dosetInd]; rw [Set.indicator_of_mem (s := DoubleCoset.doubleCoset _ _ _) ha]; exact one_ne_zero
  have hsumS : ∀ d, ∑ᶠ a ∈ S d, ρ a.out x = c d • x := fun d => by
    rw [← (hc d).1, heckeVec, finsum_mem_def]
    refine finsum_congr fun a => ?_
    by_cases ha : a ∈ S d
    · rw [Set.indicator_of_mem ha, dosetInd, Set.indicator_of_mem (s := DoubleCoset.doubleCoset _ _ _) ha]; simp
    · rw [Set.indicator_of_notMem ha, dosetInd, Set.indicator_of_notMem (s := DoubleCoset.doubleCoset _ _ _) ha]; simp

  have hU := fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r => cartan_existsUnique E w r hϖ T hTv a.out
  choose D hD using fun a => (hU a).exists
  have hDu : ∀ (d : {d : Fin r → ℤ // Antitone d}) (a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r), a ∈ S d.1 → D a = d :=
    fun d a ha => (hU a).unique (hD a) ha
  let e : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r ≃ Σ d : {d : Fin r → ℤ // Antitone d}, S d.1 :=
    { toFun := fun a => ⟨D a, a, hD a⟩
      invFun := fun p => p.2.1
      left_inv := fun a => rfl
      right_inv := fun ⟨d, a, ha⟩ => by
        have h1 : D a = d := hDu d a ha
        subst h1
        rfl }
  haveI : ∀ d, Fintype (S d) := fun d => (hSfin d).fintype
  have hsumF : ∀ d, ∑ a : S d, ρ (a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out x = c d • x := fun d => by
    rw [← hsumS d, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]

  set q : ℝ := (qV E w : ℝ) with hqdef
  have hq1 : (1 : ℝ) < q := by
    show (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ); exact_mod_cast one_lt_absNorm w
  have hq0 : (0 : ℝ) < q := by linarith
  set M : ℝ := q ^ (((r : ℝ) - 1) / 2) with hM
  set ρ₀ : ℝ := q ^ (-((r : ℝ) - 1)) with hρ₀
  have hM0 : 0 < M := Real.rpow_pos_of_pos hq0 _
  have hMM : M * M * ρ₀ = 1 := by
    rw [hM, hρ₀, ← Real.rpow_add hq0, ← Real.rpow_add hq0,
      show ((r : ℝ) - 1) / 2 + ((r : ℝ) - 1) / 2 + -((r : ℝ) - 1) = 0 by ring, Real.rpow_zero]
  set cq : ℂ := (qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) with hcq
  have hcqn : ‖cq‖ = M := by
    rw [hcq, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (qV_ne_zero w))]
    congr 1; simp
  have hsmall : ∀ β : ℂ, ‖β‖ ≤ M → ∀ X : ℂ, ‖X‖ < ρ₀ → ‖β * (cq * X)‖ < 1 := fun β hβ X hX => by
    rw [norm_mul, norm_mul, hcqn]
    calc ‖β‖ * (M * ‖X‖) ≤ M * (M * ‖X‖) := mul_le_mul_of_nonneg_right hβ (by positivity)
      _ < M * (M * ρ₀) := by gcongr
      _ = 1 := by rw [← mul_assoc, hMM]
  set X₀ : ℝ := q ^ (-(((r : ℝ) + t) / 2)) with hX₀
  have hX₀pos : 0 < X₀ := Real.rpow_pos_of_pos hq0 _
  have hX₀ρ : X₀ < ρ₀ := Real.rpow_lt_rpow_of_exponent_lt hq1 (by
    have : (r : ℝ) ≤ t := by exact_mod_cast hrt
    linarith)
  have hX₀c : ((X₀ : ℝ) : ℂ) = (qV E w : ℂ) ^ (-(((r : ℂ) + t) / 2)) := by
    rw [hX₀, Complex.ofReal_cpow hq0.le]; push_cast; rfl

  let deg : {d : Fin r → ℤ // Antitone d} → ℕ := fun d => (∑ i, |d.1 i|).toNat
  have hdeg : ∀ k, {d | deg d = k}.Finite := fun k => by
    have hfin : (Set.pi Set.univ fun _ : Fin r => Set.Icc (-(k : ℤ)) k).Finite :=
      Set.Finite.pi fun _ => Set.finite_Icc _ _
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun d hd => ?_
    simp only [Set.mem_setOf_eq, deg] at hd
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    intro i
    have h1 : |d.1 i| ≤ ∑ j, |d.1 j| := Finset.single_le_sum (fun j _ => abs_nonneg (d.1 j)) (Finset.mem_univ i)
    have h2 : ∑ j, |d.1 j| = k := by rw [← hd, Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    constructor
    · linarith [neg_abs_le (d.1 i)]
    · linarith [le_abs_self (d.1 i)]

  obtain ⟨δ₁, hδ₁, hs₁⟩ := GlobalTheory.T.satake_vector_hecke_eigenvalue H E w r V ρ x B hx z ϖ hϖ T hTv c (fun d => (hc d).1)
  obtain ⟨B₀, hB₀, δ₂, hδ₂, hs₂⟩ := GlobalTheory.T.hasSum_card_cosets_diagonalDoubleCoset_GL H E w r ϖ hϖ T hTv
  let a : {d : Fin r → ℤ // Antitone d} → ℂ := fun d => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * ℓ x
  let b : {d : Fin r → ℤ // Antitone d} → ℝ := fun d => (Nat.card (S d.1) : ℝ)
  let P : ℂ → ℂ := fun X => eulerFac (B.map (z * ·)) (cq * X) * eulerFac (B.map fun β => (z * β)⁻¹) (cq * X) *
    (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)) * ℓ x
  let P' : ℂ → ℂ := fun X => eulerFac B₀ (cq * X) * eulerFac (B₀.map (·⁻¹)) (cq * X) *
    ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2)
  have hC0 : 0 ≤ Cℓ := (norm_nonneg _).trans (hC 1)
  have hab : ∀ d, ‖a d‖ ≤ Cℓ * b d := fun d => by
    have e1 : c d.1 * ℓ x = ∑ y : S d.1, ℓ (ρ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out x) := by
      rw [← map_sum, hsumF, map_smul, smul_eq_mul]
    have hz' : ‖(z : ℂ) ^ (∑ i, d.1 i)‖ = 1 := by rw [norm_zpow, hz, _root_.one_zpow]
    simp only [a, b]
    rw [mul_assoc, norm_mul, hz', one_mul, e1]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun y _ => hC _).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card, mul_comm]
  have hbnd : ∀ β ∈ B.map (z * ·), ‖(β : ℂ)‖ ≤ M := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
    simpa [norm_mul, hz] using (hB b hb).1
  have hbnd' : ∀ β ∈ B.map fun β => (z * β)⁻¹, ‖(β : ℂ)‖ ≤ M := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
    simpa [norm_mul, hz, Units.val_inv_eq_inv_val] using (hB b hb).2
  have hbnd₀ : ∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ M := fun β hβ => (hB₀ β hβ).1
  have hbnd₀' : ∀ β ∈ B₀.map (·⁻¹), ‖(β : ℂ)‖ ≤ M := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
    exact (hB₀ b hb).2
  have hpoly : Differentiable ℂ fun X : ℂ => ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * X ^ 2) := by fun_prop
  have hE1 := differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd β hβ) X hX
  have hE2 := differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd' β hβ) X hX
  have hE3 := differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd₀ β hβ) X hX
  have hE4 := differentiableOn_eulerFac _ cq ρ₀ fun β hβ X hX => hsmall _ (hbnd₀' β hβ) X hX
  have hP : DifferentiableOn ℂ P (Metric.ball 0 ρ₀) :=
    (((hE1.mul hE2).mul hpoly.differentiableOn).mul_const (ℓ x)).congr fun X _ => by simp only [P, Pi.mul_apply]
  have hP' : DifferentiableOn ℂ P' (Metric.ball 0 ρ₀) :=
    ((hE3.mul hE4).mul hpoly.differentiableOn).congr fun X _ => rfl
  have hser : ∀ X : ℝ, 0 < X → X < min δ₁ δ₂ → HasSum (fun d => a d * (X : ℂ) ^ deg d) (P X) ∧
      HasSum (fun d => (b d : ℂ) * (X : ℂ) ^ deg d) (P' X) := fun X hX h =>
    ⟨by
      have h1 := (hs₁ X hX (lt_of_lt_of_le h (min_le_left _ _))).mul_right (ℓ x)
      rw [show (fun d => a d * (X : ℂ) ^ deg d) = fun d : {d : Fin r → ℤ // Antitone d} =>
        (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat * ℓ x from funext fun d => by
          simp only [a, deg]; ring]
      exact h1,
    hs₂ X hX (lt_of_lt_of_le h (min_le_right _ _))⟩
  obtain ⟨hA, hBs⟩ := GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval deg hdeg a b Cℓ (min δ₁ δ₂) ρ₀ P P' (lt_min hδ₁ hδ₂) (fun d => Nat.cast_nonneg _)
    hab hP hP' hser (X₀ : ℂ) (by rw [Complex.norm_real, Real.norm_of_nonneg hX₀pos.le]; exact hX₀ρ)

  have hφv : ∀ a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r,
      φ a.out = (z : ℂ) ^ (∑ i, (D a).1 i) * (X₀ : ℂ) ^ deg (D a) := fun a => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := DoubleCoset.mem_doubleCoset.1 (hD a)
    rw [e1, hφ ϖ hϖ (D a).1 (T (D a).1) (hTv _) k₁ hk₁ k₂ hk₂]
    congr 1
    have hn : ((∑ i, |(D a).1 i| : ℤ) : ℂ) = ((deg (D a) : ℕ) : ℂ) := by
      simp only [deg]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    rw [hn, hX₀c, ← Complex.cpow_nat_mul]
    congr 1
    push_cast
    ring

  let f : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r → ℂ := fun a => φ a.out * ℓ (ρ a.out x)
  let u : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r → ℝ := fun a => Cℓ * X₀ ^ deg (D a)
  have hfu : ∀ a, ‖f a‖ ≤ u a := fun a => by
    simp only [f, u]
    rw [hφv, norm_mul, norm_mul, norm_zpow, hz, _root_.one_zpow, one_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hX₀pos.le, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (pow_nonneg hX₀pos.le _)
  have hu : Summable u := by
    rw [← e.symm.summable_iff]
    refine (summable_sigma_of_nonneg fun p => mul_nonneg hC0 (pow_nonneg hX₀pos.le _)).2
      ⟨fun d => Summable.of_finite, ?_⟩
    have h1 : ∀ d : {d : Fin r → ℤ // Antitone d},
        Cℓ * (b d * ‖(X₀ : ℂ)‖ ^ deg d) = ∑' y : S d.1, (u ∘ e.symm) ⟨d, y⟩ := fun d => by
      have h2 : ∀ y : S d.1, (u ∘ e.symm) ⟨d, y⟩ = Cℓ * X₀ ^ deg d := fun y => by
        show Cℓ * X₀ ^ deg (D y.1) = _
        rw [hDu d y.1 y.2]
      simp_rw [h2]
      rw [tsum_const, nsmul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hX₀pos.le]
      simp only [b]
      ring
    exact (hBs.mul_left Cℓ).congr h1
  have hf : Summable f := Summable.of_norm_bounded hu hfu
  have hfib : ∀ d : {d : Fin r → ℤ // Antitone d},
      HasSum (fun y : S d.1 => (f ∘ e.symm) ⟨d, y⟩) (a d * (X₀ : ℂ) ^ deg d) := fun d => by
    have h2 : ∀ y : S d.1, (f ∘ e.symm) ⟨d, y⟩ =
        (z : ℂ) ^ (∑ i, d.1 i) * (X₀ : ℂ) ^ deg d * ℓ (ρ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out x) :=
      fun y => by
        show φ (y : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r).out * _ = _
        rw [hφv, hDu d y.1 y.2]
        rfl
    have h3 : ∑ y : S d.1, (f ∘ e.symm) ⟨d, y⟩ = a d * (X₀ : ℂ) ^ deg d := by
      rw [Finset.sum_congr rfl fun y _ => h2 y, ← Finset.mul_sum, ← map_sum, hsumF, map_smul, smul_eq_mul]
      simp only [a]
      ring
    exact h3 ▸ hasSum_fintype _
  have heq : ∑' a, f a = P X₀ := (((e.symm.hasSum_iff).2 hf.hasSum).sigma hfib).unique hA
  have hfin := hf.hasSum
  rw [heq] at hfin

  have hcX : cq * (X₀ : ℂ) = npow w (-((1 + (t : ℂ)) / 2)) := by
    have hqC : (qV E w : ℂ) ≠ 0 := by exact_mod_cast qV_ne_zero w
    rw [hcq, hX₀c, ← Complex.cpow_add _ _ hqC]
    show ((qV E w : ℕ) : ℂ) ^ _ = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _
    congr 1
    ring
  have hX2 : (X₀ : ℂ) ^ 2 = ((qV E w : ℂ) ^ (r + t))⁻¹ := by
    rw [hX₀c, ← Complex.cpow_nat_mul, show ((2 : ℕ) : ℂ) * -(((r : ℂ) + t) / 2) = -(((r + t : ℕ) : ℂ)) by push_cast; ring,
      Complex.cpow_neg, Complex.cpow_natCast]
  have hprod : ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X₀ : ℂ) ^ 2) =
      ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹) := by
    have hqC : (qV E w : ℂ) ≠ 0 := by exact_mod_cast qV_ne_zero w
    refine Finset.prod_nbij' (fun i => r + t - i) (fun j => r + t - j) (fun i hi => ?_) (fun j hj => ?_)
      (fun i hi => ?_) (fun j hj => ?_) (fun i hi => ?_)
    · simp only [Finset.mem_range, Finset.mem_Ioc, Finset.mem_coe] at hi ⊢; omega
    · simp only [Finset.mem_range, Finset.mem_Ioc, Finset.mem_coe] at hj ⊢; omega
    · simp only [Finset.mem_range, Finset.mem_coe] at hi; omega
    · simp only [Finset.mem_Ioc, Finset.mem_coe] at hj; omega
    · simp only [Finset.mem_range, Finset.mem_coe] at hi
      have hp : (qV E w : ℂ) ^ (r + t) = (qV E w : ℂ) ^ (r + t - i) * (qV E w : ℂ) ^ i := by
        rw [← pow_add]; congr 1; omega
      rw [hX2, hp]
      congr 1
      field_simp
  have hval : P X₀ = eulerFac (B.map (z * ·)) (npow w (-((1 + (t : ℂ)) / 2))) *
      eulerFac (B.map fun β => (z * β)⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) *
      (∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) * ℓ x := by
    simp only [P]
    rw [hcX, hprod]
  rw [hval] at hfin
  exact hfin

end GlobalTheory.ZetaGL

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH
open scoped Classical

noncomputable section

namespace GlobalTheory.KFixIrr

/- English proof (translation)
Unfold `Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq`. Rewrite using `[← Matrix.fromBlocks_diagonal]`. Simplify using `only [Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases h : i = j <;> simp [h, Matrix.diagonal_apply]`.
-/
theorem jm_eq_diagonal (p q : ℕ) :
    Formalism.BasicNotions.TH.Jm p q = Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)) := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [← Matrix.fromBlocks_diagonal]
  simp only [Matrix.diagonal_one]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.diagonal_apply]

/- English proof (translation)
Apply the tactic sequence `rcases a with i | i <;> rcases b with j | j <;> simp_all [Formalism.BasicNotions.TH.sameBlock]`.
-/
theorem not_sameBlock_symm {p q : ℕ} {a b : Formalism.BasicNotions.TH.Ix p q} (h : ¬ Formalism.BasicNotions.TH.sameBlock a b) :
    ¬ Formalism.BasicNotions.TH.sameBlock b a := by
  rcases a with i | i <;> rcases b with j | j <;> simp_all [Formalism.BasicNotions.TH.sameBlock]

/- English proof (translation)
Rewrite using `[jm_eq_diagonal]`. Use extensionality with `a b`. Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `h : Formalism.BasicNotions.TH.sameBlock a b`. Apply the tactic sequence `rcases a with i | i <;> rcases b with j | j <;> simp_all [Formalism.BasicNotions.TH.sameBlock]`.

Rewrite using `[hX a b h]`. Simplify using the standard rewrite rules.
-/
theorem commute_jm {p q : ℕ} (X : Formalism.BasicNotions.TH.Mat p q) (hX : Formalism.BasicNotions.TH.IsKC X) :
    Commute X (Formalism.BasicNotions.TH.Jm p q) := by
  rw [jm_eq_diagonal]
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : Formalism.BasicNotions.TH.sameBlock a b
  · rcases a with i | i <;> rcases b with j | j <;> simp_all [Formalism.BasicNotions.TH.sameBlock]
  · rw [hX a b h]; simp

/- English proof (translation)
Use `show Yᴴ * Formalism.BasicNotions.TH.Jm p q + Formalism.BasicNotions.TH.Jm p q * Y = 0`. Rewrite using `[hs, Matrix.neg_mul, (commute_jm Y hY).eq, neg_add_cancel]`.
-/
theorem mem_upq_of_skew {p q : ℕ} (Y : Formalism.BasicNotions.TH.Mat p q) (hY : Formalism.BasicNotions.TH.IsKC Y) (hs : Yᴴ = -Y) :
    Y ∈ Formalism.BasicNotions.TH.upq p q := by
  show Yᴴ * Formalism.BasicNotions.TH.Jm p q + Formalism.BasicNotions.TH.Jm p q * Y = 0
  rw [hs, Matrix.neg_mul, (commute_jm Y hY).eq, neg_add_cancel]

/- English proof (translation)
Establish `hXH : Formalism.BasicNotions.TH.IsKC Xᴴ`. Introduce `a b h`. Rewrite using `[Matrix.conjTranspose_apply, hX b a (not_sameBlock_symm h), star_zero]`. Establish `k1 : Formalism.BasicNotions.TH.IsKC ((1 / 2 : ℂ) • (X - Xᴴ))`. Introduce `a b h`.

Rewrite using `[Matrix.smul_apply, Matrix.sub_apply, hX a b h, hXH a b h]`. Simplify using the standard rewrite rules. Establish `k2 : Formalism.BasicNotions.TH.IsKC ((-(Complex.I / 2)) • (X + Xᴴ))`. Introduce `a b h`. Rewrite using `[Matrix.smul_apply, Matrix.add_apply, hX a b h, hXH a b h]`.

Simplify using the standard rewrite rules. Use `⟨(1 / 2 : ℂ) • (X - Xᴴ), (-(Complex.I / 2)) • (X + Xᴴ), mem_upq_of_skew _ k1 ?_, k1, mem_upq_of_skew _ k2 ?_, k2, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Simplify using `[Matrix.conjTranspose_apply]`. Expand and normalize the polynomial expressions, which then agree.

Use extensionality with `a b`. Simplify using `[Matrix.conjTranspose_apply]`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`.

Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isKC_decomp {p q : ℕ} (X : Formalism.BasicNotions.TH.Mat p q) (hX : Formalism.BasicNotions.TH.IsKC X) :
    ∃ Y₁ Y₂ : Formalism.BasicNotions.TH.Mat p q, Y₁ ∈ Formalism.BasicNotions.TH.upq p q ∧ Formalism.BasicNotions.TH.IsKC Y₁ ∧ Y₂ ∈ Formalism.BasicNotions.TH.upq p q ∧
      Formalism.BasicNotions.TH.IsKC Y₂ ∧ X = Y₁ + Complex.I • Y₂ := by
  have hXH : Formalism.BasicNotions.TH.IsKC Xᴴ := by
    intro a b h
    rw [Matrix.conjTranspose_apply, hX b a (not_sameBlock_symm h), star_zero]
  have k1 : Formalism.BasicNotions.TH.IsKC ((1 / 2 : ℂ) • (X - Xᴴ)) := by
    intro a b h
    rw [Matrix.smul_apply, Matrix.sub_apply, hX a b h, hXH a b h]; simp
  have k2 : Formalism.BasicNotions.TH.IsKC ((-(Complex.I / 2)) • (X + Xᴴ)) := by
    intro a b h
    rw [Matrix.smul_apply, Matrix.add_apply, hX a b h, hXH a b h]; simp
  refine ⟨(1 / 2 : ℂ) • (X - Xᴴ), (-(Complex.I / 2)) • (X + Xᴴ), mem_upq_of_skew _ k1 ?_, k1,
    mem_upq_of_skew _ k2 ?_, k2, ?_⟩
  · ext a b
    simp [Matrix.conjTranspose_apply]
    ring
  · ext a b
    simp [Matrix.conjTranspose_apply]
    ring
  · ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring

/- English proof (translation)
Establish `h1 : g * θ * A = θ * g * A`. Combine the equalities or inequalities in the displayed calculation. Use `show g * θ = θ * g`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem commute_of_frame {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {g θ : Matrix (Fin n) (Fin n) ℂ}
    {A : Matrix (Fin n) ι ℂ} {A' : Matrix ι (Fin n) ℂ} {e j : Matrix ι ι ℂ} (hA : A * A' = 1) (hg : g * A = A * e)
    (hθ : θ * A = A * j) (hej : Commute e j) : Commute g θ := by
  have h1 : g * θ * A = θ * g * A := by
    calc g * θ * A = g * A * j := by rw [Matrix.mul_assoc, hθ, ← Matrix.mul_assoc]
      _ = A * (e * j) := by rw [hg, Matrix.mul_assoc]
      _ = A * j * e := by rw [hej.eq, ← Matrix.mul_assoc]
      _ = θ * g * A := by rw [← hθ, Matrix.mul_assoc, ← hg, ← Matrix.mul_assoc]
  show g * θ = θ * g
  calc g * θ = g * θ * (A * A') := by rw [hA, Matrix.mul_one]
    _ = θ * g * (A * A') := by rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
    _ = θ * g := by rw [hA, Matrix.mul_one]

/- English proof (translation)
Introduce `v` and use `by obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem s hy)⟩`.
-/
theorem locFin_fockAct1 {P Q R S : ℕ} (Y : Formalism.BasicNotions.TH.Mat P Q) (hY : Formalism.BasicNotions.TH.IsKC Y) (s : ℂ) :
    LocFin (Formalism.BasicNotions.TH.fockAct1 P Q R S Y + s • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem s hy)⟩

/- English proof (translation)
Simplify using `using GlobalTheory.TensIrr.atPl_smul (V := V) w (0 : ℂ) 0`.
-/
theorem atPl_zero' {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (w : ι) : atPl (V := V) w 0 = 0 := by
  simpa using GlobalTheory.TensIrr.atPl_smul (V := V) w (0 : ℂ) 0

/- English proof (translation)
Rewrite using `[GlobalTheory.TensIrr.atPl_add, GlobalTheory.TensIrr.atPl_smul, GlobalTheory.TensIrr.atPl_one]`. Both sides reduce to the same expression.
-/
theorem atPl_shift_apply {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (w : ι) (L : Module.End ℂ (V w)) (s : ℂ) (T : ⨂[ℂ] i, V i) :
    atPl (V := V) w (L + s • 1) T = atPl (V := V) w L T + s • T := by
  rw [GlobalTheory.TensIrr.atPl_add, GlobalTheory.TensIrr.atPl_smul, GlobalTheory.TensIrr.atPl_one]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[pureA]`.
-/
theorem pureA_zero' {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : pureA F (⇑(0 : SInf F κ)) g = 0 := by
  funext x; simp [pureA]

end GlobalTheory.KFixIrr

namespace GlobalTheory.KFixIrr

/- English proof (translation)
Introduce `hLaws hLine hK F E _ _ _ _ _ σ B n d P Q R S X W om A Φ c hCM hFr hθ hinj hAB hadm T`. Prove the components needed by the constructor for the conclusion. Introduce `hfix`. Rewrite using `[mem_chiPart]`. Establish `key : ∀ w (Y : Formalism.BasicNotions.TH.Mat P Q), Y ∈ Formalism.BasicNotions.TH.upq P Q → Formalism.BasicNotions.TH.IsKC Y → atPl (V` using `fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct1 P Q R S Y) T = ((c w : ℂ) * Y.trace) • T := by`.

Introduce `w Y hY hYK`. Use `set Y' : InfinitePlace F → Formalism.BasicNotions.TH.Mat P Q := Function.update 0 w Y with hY'`. Establish `hY'K : ∀ w', Formalism.BasicNotions.TH.IsKC (Y' w')`. Introduce `w'`. Distinguish the cases in `h : w' = w`.

Substitute `h` using the available equality. Simplify `hYK` using `[hY']`. Rewrite using `[hY', Function.update_of_ne h]`. Introduce `a b _`. Both sides reduce to the same expression.

Establish `hY'u : ∀ w', Y' w' ∈ Formalism.BasicNotions.TH.upq P Q`. Introduce `w'`. Distinguish the cases in `h : w' = w`. Substitute `h` using the available equality. Simplify `hY` using `[hY']`.

Rewrite using `[hY', Function.update_of_ne h]`. Use `show (0 : Formalism.BasicNotions.TH.Mat P Q)ᴴ * _ + _ * 0 = 0`. Simplify using the standard rewrite rules. Take `⟨γ, hγ, hgen⟩` from `hLine F E σ (Fin n) P Q B.emb (incM F X.J) 1 A hCM hFr Y' hY'u`. Establish `hkin : ∀ t : ℝ, γ (Multiplicative.ofAdd t) ∈ KInf σ X B.emb`.

Introduce `t`. Use `⟨hγ.2 _, fun w' => ?_⟩` and prove the remaining obligations. Take `⟨A', hA'⟩` from `(hFr w').2`. Conclude with `commute_of_frame hA' (hgen t w') (hθ w') (((commute_jm _ (hY'K w')).smul_left t).exp_left)`. Establish `hSD0 : SD (fun t => (om.comp (MonoidHom.inl _ _)) (γ (Multiplicative.ofAdd t))) (Φ T) (Φ 0)`.

Introduce `g hg l hl`. Establish `hc : (fun t : ℝ => l ((om.comp (MonoidHom.inl _ _)) (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) = fun _ => l (pureA F (Φ T) g)`. Use function extensionality and compare the values at `t`. Use `GlobalTheory.KInfPol.sa_of_acts (hfix _ (hkin t)) g hg` as an intermediate fact. Simplify using `only [MonoidHom.comp_apply, MonoidHom.inl_apply]`.

Rewrite using `[this]`. Rewrite using `[hc, map_zero, pureA_zero', map_zero]`. Conclude with `hasDerivAt_const _ _`. Establish `h2` using `hAB γ hγ Y' hgen T`. Establish `hz` using `hinj ((hLaws F (Fin n × Fin d) (Φ T) _ _).2.2.2.2 _ h2 hSD0)`.

Establish `hsum : sumPl (V` using `fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) (fun w' => Formalism.BasicNotions.TH.fockAct1 P Q R S (Y' w') + ((-((c w' : ℚ) : ℂ)) * (Y' w').trace) • 1) = atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH …`. Unfold `sumPl`. Rewrite using `[Finset.sum_eq_single w]`. Simplify using `[hY']`. Introduce `w' _ hne`.

Simplify using `only [hY', Function.update_of_ne hne, Pi.zero_apply, map_zero, Matrix.trace_zero, mul_zero, zero_smul, add_zero]`. Conclude with `atPl_zero' w'`. Introduce `h`. Conclude with `absurd (Finset.mem_univ w) h`. Rewrite `hz` using `[hsum, atPl_shift_apply]`.

Rewrite using `[eq_neg_of_add_eq_zero_left hz, ← neg_smul, neg_mul, neg_neg]`. Introduce `w Xm hXm`. Take `⟨Y₁, Y₂, h1u, h1k, h2u, h2k, rfl⟩` from `isKC_decomp Xm hXm`. Rewrite using `[map_add, map_smul, GlobalTheory.TensIrr.atPl_add, GlobalTheory.TensIrr.atPl_smul, LinearMap.add_apply, LinearMap.smul_apply, key w Y₁ h1u h1k, key w Y₂ h2u h2k, Matrix.trace_add, Matrix.trace_smul, smul_smul, ← add_smul]`. Use `congr 1`.

Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `hT k hk`. Rewrite `hT` using `[mem_chiPart]`. Take `⟨γ, hγ, Y, hgen, hYK, hγ1⟩` from `hK F E σ (Fin n) P Q B.emb (incM F X.J) 1 A X.θ hCM hFr hθ k hk.1 hk.2`.

Use `set L := sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) (fun w => Formalism.BasicNotions.TH.fockAct1 P Q R S (Y w) + ((-((c w : ℚ) : ℂ)) * (Y w).trace) • 1) with hL`. Establish `hLT : L T = 0`. Rewrite using `[hL]`. Unfold `sumPl`. Rewrite using `[LinearMap.sum_apply]`.

Use `Finset.sum_eq_zero fun w _ => ?_` and prove the remaining obligations. Rewrite using `[atPl_shift_apply, hT w (Y w) (hYK w), ← add_smul]`. Simplify using the standard rewrite rules. Establish `hLF : LocFin L` using `GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => locFin_fockAct1 (Y w) (hYK w) _`. Take `⟨U, hU, hSA⟩` from `GlobalTheory.ExpAct.expAct_fock F (Fin n × Fin d) (Tens F P Q R S) Φ L ((om.comp (MonoidHom.inl _ _)).comp γ) hLF (fun t l hl => hadm _ l hl) (fun T' => hAB γ hγ Y hgen T')`.

Establish `hUT : U T = T` using `GlobalTheory.ExpAct.eq_of_forms fun l => by`. Establish `h2` using `hasSum_single (f := fun m : ℕ => ((m.factorial : ℂ))⁻¹ * l ((L ^ m) T)) 0 (by`. Introduce `m hm`. Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hm`. Simplify using `[pow_succ, Module.End.mul_apply, hLT])`.

Simplify using `only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero, Module.End.one_apply] at h2`. Conclude with `(hU T l).unique h2`. Establish `hS` using `hSA T`. Rewrite `hS` using `[hUT]`. Establish `hk1 : ((om.comp (MonoidHom.inl _ _)).comp γ) (Multiplicative.ofAdd 1) = om (k, 1)`.

Simplify using `[hγ1]`. Rewrite `hS` using `[hk1]`. Conclude with `(hLaws F (Fin n × Fin d) (Φ T) (Φ T) (Φ T)).2.1 _ (map_zero _) hS`.
-/
theorem kFix_iff_mem_chiPart : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d P Q R S : ℕ) (X : Spc F E n) (W : Spc F E d) (om : Rep σ X W)
    (A : InfinitePlace F → Matrix (Fin n) (Formalism.BasicNotions.TH.Ix P Q) ℂ) (Φ : GlobalTheory.RealLift.Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d))
    (c : InfinitePlace F → ℚ), IsCMExt F E σ →
    (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w)) →
    (∀ w, X.θ w * A w = A w * Formalism.BasicNotions.TH.Jm P Q) → Function.Injective Φ →
    GlobalTheory.RealLift.ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (Formalism.BasicNotions.TH.fockAct1 P Q R S) (fun w => -((c w : ℚ) : ℂ)) →
    (∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d)) →
    ∀ T, IsKFix B om (Φ T) ↔ T ∈ GlobalTheory.KFixIrr.chiPart (InfinitePlace F) P Q R S c := by
  intro hLaws hLine hK F E _ _ _ _ _ σ B n d P Q R S X W om A Φ c hCM hFr hθ hinj hAB hadm T
  constructor
  · intro hfix
    rw [mem_chiPart]
    have key : ∀ w (Y : Formalism.BasicNotions.TH.Mat P Q), Y ∈ Formalism.BasicNotions.TH.upq P Q → Formalism.BasicNotions.TH.IsKC Y →
        atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct1 P Q R S Y) T =
          ((c w : ℂ) * Y.trace) • T := by
      intro w Y hY hYK
      set Y' : InfinitePlace F → Formalism.BasicNotions.TH.Mat P Q := Function.update 0 w Y with hY'
      have hY'K : ∀ w', Formalism.BasicNotions.TH.IsKC (Y' w') := by
        intro w'
        by_cases h : w' = w
        · subst h; simpa [hY'] using hYK
        · rw [hY', Function.update_of_ne h]; intro a b _; rfl
      have hY'u : ∀ w', Y' w' ∈ Formalism.BasicNotions.TH.upq P Q := by
        intro w'
        by_cases h : w' = w
        · subst h; simpa [hY'] using hY
        · rw [hY', Function.update_of_ne h]; show (0 : Formalism.BasicNotions.TH.Mat P Q)ᴴ * _ + _ * 0 = 0; simp
      obtain ⟨γ, hγ, hgen⟩ := hLine F E σ (Fin n) P Q B.emb (incM F X.J) 1 A hCM hFr Y' hY'u
      have hkin : ∀ t : ℝ, γ (Multiplicative.ofAdd t) ∈ KInf σ X B.emb := by
        intro t
        refine ⟨hγ.2 _, fun w' => ?_⟩
        obtain ⟨A', hA'⟩ := (hFr w').2
        exact commute_of_frame hA' (hgen t w') (hθ w') (((commute_jm _ (hY'K w')).smul_left t).exp_left)
      have hSD0 : SD (fun t => (om.comp (MonoidHom.inl _ _)) (γ (Multiplicative.ofAdd t))) (Φ T) (Φ 0) := by
        intro g hg l hl
        have hc : (fun t : ℝ => l ((om.comp (MonoidHom.inl _ _)) (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) =
            fun _ => l (pureA F (Φ T) g) := by
          funext t
          have := GlobalTheory.KInfPol.sa_of_acts (hfix _ (hkin t)) g hg
          simp only [MonoidHom.comp_apply, MonoidHom.inl_apply]
          rw [this]
        rw [hc, map_zero, pureA_zero', map_zero]
        exact hasDerivAt_const _ _
      have h2 := hAB γ hγ Y' hgen T
      have hz := hinj ((hLaws F (Fin n × Fin d) (Φ T) _ _).2.2.2.2 _ h2 hSD0)
      have hsum : sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S)
          (fun w' => Formalism.BasicNotions.TH.fockAct1 P Q R S (Y' w') + ((-((c w' : ℚ) : ℂ)) * (Y' w').trace) • 1) =
          atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w
            (Formalism.BasicNotions.TH.fockAct1 P Q R S Y + ((-((c w : ℚ) : ℂ)) * Y.trace) • 1) := by
        unfold sumPl
        rw [Finset.sum_eq_single w]
        · simp [hY']
        · intro w' _ hne
          simp only [hY', Function.update_of_ne hne, Pi.zero_apply, map_zero, Matrix.trace_zero, mul_zero, zero_smul,
            add_zero]
          exact atPl_zero' w'
        · intro h; exact absurd (Finset.mem_univ w) h
      rw [hsum, atPl_shift_apply] at hz
      rw [eq_neg_of_add_eq_zero_left hz, ← neg_smul, neg_mul, neg_neg]
    intro w Xm hXm
    obtain ⟨Y₁, Y₂, h1u, h1k, h2u, h2k, rfl⟩ := isKC_decomp Xm hXm
    rw [map_add, map_smul, GlobalTheory.TensIrr.atPl_add, GlobalTheory.TensIrr.atPl_smul, LinearMap.add_apply, LinearMap.smul_apply,
      key w Y₁ h1u h1k, key w Y₂ h2u h2k, Matrix.trace_add, Matrix.trace_smul, smul_smul, ← add_smul]
    congr 1
    simp only [smul_eq_mul]
    ring
  · intro hT k hk
    rw [mem_chiPart] at hT
    obtain ⟨γ, hγ, Y, hgen, hYK, hγ1⟩ := hK F E σ (Fin n) P Q B.emb (incM F X.J) 1 A X.θ hCM hFr hθ k hk.1 hk.2
    set L := sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S)
      (fun w => Formalism.BasicNotions.TH.fockAct1 P Q R S (Y w) + ((-((c w : ℚ) : ℂ)) * (Y w).trace) • 1) with hL
    have hLT : L T = 0 := by
      rw [hL]
      unfold sumPl
      rw [LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [atPl_shift_apply, hT w (Y w) (hYK w), ← add_smul]
      simp
    have hLF : LocFin L := GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => locFin_fockAct1 (Y w) (hYK w) _
    obtain ⟨U, hU, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F (Fin n × Fin d) (Tens F P Q R S) Φ L
      ((om.comp (MonoidHom.inl _ _)).comp γ) hLF (fun t l hl => hadm _ l hl) (fun T' => hAB γ hγ Y hgen T')
    have hUT : U T = T := GlobalTheory.ExpAct.eq_of_forms fun l => by
      have h2 := hasSum_single (f := fun m : ℕ => ((m.factorial : ℂ))⁻¹ * l ((L ^ m) T)) 0 (by
        intro m hm
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
        simp [pow_succ, Module.End.mul_apply, hLT])
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero, Module.End.one_apply] at h2
      exact (hU T l).unique h2
    have hS := hSA T
    rw [hUT] at hS
    have hk1 : ((om.comp (MonoidHom.inl _ _)).comp γ) (Multiplicative.ofAdd 1) = om (k, 1) := by
      simp [hγ1]
    rw [hk1] at hS
    exact (hLaws F (Fin n × Fin d) (Φ T) (Φ T) (Φ T)).2.1 _ (map_zero _) hS

end GlobalTheory.KFixIrr

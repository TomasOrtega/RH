import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemCompletedLatticeIffDualSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameIntegStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitRowLat

variable {D : D7}

/- English proof (translation)
Introduce `a ha y hy`. Express the relevant statement in the definitionally equal form `y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) at hy`. Express the relevant statement in the definitionally equal form `_ ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))`. Proceed by induction on `ha using AddSubgroup.closure_induction with`. Consider the case `mem a ha`.

Take `⟨s, hs, o, rfl⟩` from `ha`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨t, ht, x, hx, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x, Λ.smul_mem o hx, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Both sides reduce to the same expression. Consider the case `zero`. Simplify using `only [Pi.zero_apply, mul_zero]`.

Conclude with `zero_mem _`. Consider the case `add u w _ _ hu hw`. Simplify using `only [Pi.add_apply, mul_add]`. Conclude with `add_mem hu hw`. Consider the case `neg u _ hu`.

Simplify using `only [Pi.neg_apply, mul_neg]`. Conclude with `neg_mem hu`. Consider the case `zero`. Simplify using `only [zero_mul]`. Conclude with `zero_mem _`.

Consider the case `add u w _ _ hu hw`. Simplify using `only [add_mul]`. Conclude with `add_mem hu hw`. Consider the case `neg u _ hu`. Simplify using `only [neg_mul]`.

Conclude with `neg_mem hu`.
-/
theorem smul_mem_latHat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    ∀ a ∈ intAE D, ∀ y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)),
      (fun i => a * y i) ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
  intro a ha y hy
  change y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) at hy
  change _ ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨s, hs, o, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x,
        Λ.smul_mem o hx, ?_⟩
      funext i
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | zero =>
      simp only [Pi.zero_apply, mul_zero]
      exact zero_mem _
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, mul_add]
      exact add_mem hu hw
    | neg u _ hu =>
      simp only [Pi.neg_apply, mul_neg]
      exact neg_mem hu
  | zero =>
    simp only [zero_mul]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [add_mul]
    exact add_mem hu hw
  | neg u _ hu =>
    simp only [neg_mul]
    exact neg_mem hu

/- English proof (translation)
Take `⟨-, -, -, -, hcc, -, -, hG, hdet, -, -⟩` from `GlobalTheory.Member.latHat_eq_hat_and_gram D V`. Establish `hsum : ∀ w x : Fin V.rank → D.host.E, (∑ a, ∑ b, w a * (HSpace.gram V)ᵀ a b * (GlobalTheory.Member.cF D) (x b)) = ∑ i, ∑ j, star (x i) * HSpace.gram V i j * w j`. Introduce `w x`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.transpose_apply]`. Express the relevant statement in the definitionally equal form `w b * HSpace.gram V a b * star (x a) = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hL : ∀ w : Fin V.rank → D.host.E, (∀ x ∈ Λ, ∑ a, ∑ b, w a * (HSpace.gram V)ᵀ a b * (GlobalTheory.Member.cF D) (x b) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ w ∈ Λ`. Introduce `w`.

Rewrite using `[hΛ.2 w]`. Use `forall₂_congr fun x _ => ?_` and prove the remaining obligations. Rewrite using `[FractionalIdeal.mem_one_iff, hsum]`. Establish `key` using `GlobalTheory.AdLat.hat_selfDual D.host.F D.host.E V.rank Λ (GlobalTheory.Member.cF D) (HSpace.gram V)ᵀ 1 hΛ.1.fg hΛ.1.span_eq_top hcc hG hdet one_ne_zero hL`. Rewrite `key` using `[← GlobalTheory.LatDual.integralTensorAdeles_eq_adelicCompletion_one]`.

Simplify using `only [GlobalTheory.LatDual.hR_eq_hermA]`. Prove the components needed by the constructor for the conclusion. Introduce `hy z hz`. Express the relevant statement in the definitionally equal form `z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) at hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`.

Consider the case `mem z hz`. Take `⟨t, ht, x, hx, rfl⟩` from `hz`. Establish `h1 : (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) ∈ intAE D` using `AddSubgroup.subset_closure ⟨t, ht, 1, rfl⟩`. Establish `h2` using `(key _).2 (smul_mem_latHat V Λ _ h1 y hy) x hx`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Unfold `GlobalTheory.AdLat.hermA`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `e : GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (t ⊗ₜ[D.host.F] x b) = (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) * GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (GlobalTheory.AdLat.fv D.h …`. Simplify using `[GlobalTheory.AdLat.sg, GlobalTheory.AdLat.fv]`. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Establish `: GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y 0 = 0` using `by simp [GlobalTheory.AdLat.hermA]`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Consider the case `add u w _ _ hu hw`. Establish `: GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (u + w) = GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u + GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y w`. Simplify using `only [GlobalTheory.AdLat.hermA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`. Rewrite using `[this]`. Conclude with `add_mem hu hw`.

Consider the case `neg u _ hu`. Establish `: GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (-u) = -GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u`. Simplify using `only [GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]`. Rewrite using `[this]`. Conclude with `neg_mem hu`.

Introduce `h`. Use `(key y).1 fun x hx => h _ ?_` and prove the remaining obligations. Conclude with `AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩`.
-/
theorem latHat_selfDual (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) (y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔
      ∀ z ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)),
        hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram z y ∈ intAE D := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hsum : ∀ w x : Fin V.rank → D.host.E,
      (∑ a, ∑ b, w a * (HSpace.gram V)ᵀ a b * (GlobalTheory.Member.cF D) (x b)) =
        ∑ i, ∑ j, star (x i) * HSpace.gram V i j * w j := by
    intro w x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.transpose_apply]
    change w b * HSpace.gram V a b * star (x a) = _
    ring
  have hL : ∀ w : Fin V.rank → D.host.E,
      (∀ x ∈ Λ, ∑ a, ∑ b, w a * (HSpace.gram V)ᵀ a b * (GlobalTheory.Member.cF D) (x b) ∈
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ w ∈ Λ := by
    intro w
    rw [hΛ.2 w]
    refine forall₂_congr fun x _ => ?_
    rw [FractionalIdeal.mem_one_iff, hsum]
  have key := GlobalTheory.AdLat.hat_selfDual D.host.F D.host.E V.rank Λ (GlobalTheory.Member.cF D)
    (HSpace.gram V)ᵀ 1 hΛ.1.fg hΛ.1.span_eq_top hcc hG hdet one_ne_zero hL
  rw [← GlobalTheory.LatDual.integralTensorAdeles_eq_adelicCompletion_one] at key
  simp only [GlobalTheory.LatDual.hR_eq_hermA]
  constructor
  · intro hy z hz
    change z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hz
      have h1 : (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨t, ht, 1, rfl⟩
      have h2 := (key _).2 (smul_mem_latHat V Λ _ h1 y hy) x hx
      convert h2 using 1
      unfold GlobalTheory.AdLat.hermA
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have e : GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (t ⊗ₜ[D.host.F] x b) =
          (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) *
            GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (GlobalTheory.AdLat.fv D.host.F x b) := by
        simp [GlobalTheory.AdLat.sg, GlobalTheory.AdLat.fv]
      rw [e]
      ring
    | zero =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y 0 = 0 := by simp [GlobalTheory.AdLat.hermA]
      rw [this]; exact zero_mem _
    | add u w _ _ hu hw =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (u + w) =
          GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u +
            GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y w := by
        simp only [GlobalTheory.AdLat.hermA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      rw [this]; exact add_mem hu hw
    | neg u _ hu =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (-u) =
          -GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u := by
        simp only [GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
      rw [this]; exact neg_mem hu
  · intro h
    refine (key y).1 fun x hx => h _ ?_
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩

/- English proof (translation)
Rewrite using `[latHat_selfDual V Λ hΛ]`. Prove the components needed by the constructor for the conclusion. Introduce `h z hz`. Rewrite using `[← GlobalTheory.SplitDualLat.cA_form, GlobalTheory.SplitDualLat.finPart_cA, GlobalTheory.SplitDualLat.finPart_form]`. Conclude with `GlobalTheory.SplitDualLat.sigR_mem_intAE (h _ hz)`.

Introduce `h z hz`. Take `⟨w, rfl⟩ : ∃ w : Fin V.rank → AE D, (fun i => finPart D (w i)) = z` from `by choose s hs using GlobalTheory.SplitDualLat.finPart_surjective (D := D)`. Conclude with `⟨fun i => s (z i), funext fun i => hs _⟩`. Rewrite using `[← GlobalTheory.SplitDualLat.finPart_form, ← GlobalTheory.SplitDualLat.cA_form, GlobalTheory.SplitDualLat.finPart_cA]`. Conclude with `GlobalTheory.SplitDualLat.sigR_mem_intAE (h _ hz)`.
-/
theorem mem_iff (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) (x : Fin V.rank → AE D) :
    (fun i => finPart D (x i)) ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔
      ∀ z : Fin V.rank → AE D,
        (fun i => finPart D (z i)) ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) →
          finPart D (GlobalTheory.SplitDualLat.form V x z) ∈ intAE D := by
  rw [latHat_selfDual V Λ hΛ]
  constructor
  · intro h z hz
    rw [← GlobalTheory.SplitDualLat.cA_form, GlobalTheory.SplitDualLat.finPart_cA, GlobalTheory.SplitDualLat.finPart_form]
    exact GlobalTheory.SplitDualLat.sigR_mem_intAE (h _ hz)
  · intro h z hz
    obtain ⟨w, rfl⟩ : ∃ w : Fin V.rank → AE D, (fun i => finPart D (w i)) = z := by
      choose s hs using GlobalTheory.SplitDualLat.finPart_surjective (D := D)
      exact ⟨fun i => s (z i), funext fun i => hs _⟩
    rw [← GlobalTheory.SplitDualLat.finPart_form, ← GlobalTheory.SplitDualLat.cA_form, GlobalTheory.SplitDualLat.finPart_cA]
    exact GlobalTheory.SplitDualLat.sigR_mem_intAE (h _ hz)

/- English proof (translation)
Rewrite using `[GlobalTheory.SplitHecke.isInt_iff, ← HeightOneSpectrum.mem_adicCompletionIntegers]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, rfl⟩`. Conclude with `o.2`. Introduce `hx`.

Conclude with `⟨⟨x, hx⟩, rfl⟩`.
-/
theorem isInt_iff_le_one {v : FinPl D} (x : Fv D.host.F v) :
    GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) x ↔ Valued.v x ≤ 1 := by
  rw [GlobalTheory.SplitHecke.isInt_iff, ← HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · rintro ⟨o, rfl⟩
    exact o.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/- English proof (translation)
Introduce `D V Λ β hΛ hβ v φ e he y`. Take `⟨hπ, -, hQ, -, -⟩` from `GlobalTheory.T.splitProjAdeleComponent_chart_properties D v φ e he`. Establish `hcol` using `GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D V Λ β hΛ hβ v φ e he`. Establish `hmapQ : V.gram.map (rdQ φ) = V.gram.map fun a => rdA φ (incA D a)`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, hQ]`. Rewrite using `[mem_iff V Λ hΛ, hmapQ]`. Prove the components needed by the constructor for the conclusion. Introduce `h j choose s hs using hπ.1`. Establish `h1 : (fun k => rdA φ (s ((frCo φ β).1 k j))) = (frCo φ β).1 *ᵥ Pi.single j 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[hs, Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Establish `h2` using `h _ ((hcol fun k => s ((frCo φ β).1 k j)).2 fun i => by`. Rewrite using `[h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`.

Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Rewrite using `[Pi.single_eq_same]`. Simplify using the standard rewrite rules. Rewrite using `[Pi.single_eq_of_ne hi]`.

Use the proof step `simp)`. Rewrite `h2` using `[GlobalTheory.SplitDualLat.form_mul, GlobalTheory.SplitDualLat.cA_cA, he.1.1, hπ.2.2.2, GlobalTheory.SplitDualLat.map_form, h1, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, dotProduct_single, mul_one]`. Conclude with `(isInt_iff_le_one _).1 h2`. Introduce `h z hz`. Establish `h1` using `smul_mem_latHat V Λ _ (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← RingHom.map_mul, he.1.1])) _ hz`.

Simplify using `only [← RingHom.map_mul] at h1`. Establish `h2` using `(hcol z).1 h1`. Establish `h3` using `GlobalTheory.SplitDualLat.form_mul V (cA D e) 1 y z`. Simplify using `only [one_mul, mul_one, GlobalTheory.SplitDualLat.cA_cA] at h3`. Establish `h4 : (fun k => rdA φ (z k)) = (frCo φ β).1 *ᵥ (((frCo φ β)⁻¹).1 *ᵥ fun k => rdA φ (z k))`.

Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Rewrite using `[h3, hπ.2.2.2, GlobalTheory.SplitDualLat.map_form, h4, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, GlobalTheory.SplitHecke.isInt_iff]`. Conclude with `sum_mem fun i _ => mul_mem (GlobalTheory.SplitHecke.isInt_iff.1 ((isInt_iff_le_one _).2 (h i))) (GlobalTheory.SplitHecke.isInt_iff.1 ((isInt_iff_le_one _).2 (h2 i)))`.
-/
theorem conj_mem_latHat_iff : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ j, Valued.v (((fun i => rdA φ (cA D (y i))) ᵥ* ((V.gram.map (rdQ φ)) * (frCo φ β).1)) j) ≤ 1 := by
  intro D V Λ β hΛ hβ v φ e he y
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.T.splitProjAdeleComponent_chart_properties D v φ e he
  have hcol := GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D V Λ β hΛ hβ v φ e he
  have hmapQ : V.gram.map (rdQ φ) = V.gram.map fun a => rdA φ (incA D a) := by
    ext i j
    simp only [Matrix.map_apply, hQ]
  rw [mem_iff V Λ hΛ, hmapQ]
  constructor
  · intro h j
    choose s hs using hπ.1
    have h1 : (fun k => rdA φ (s ((frCo φ β).1 k j))) = (frCo φ β).1 *ᵥ Pi.single j 1 := by
      funext k
      rw [hs, Matrix.mulVec_single_one]
      rfl
    have h2 := h _ ((hcol fun k => s ((frCo φ β).1 k j)).2 fun i => by
      rw [h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      by_cases hi : i = j
      · subst hi; rw [Pi.single_eq_same]; simp
      · rw [Pi.single_eq_of_ne hi]; simp)
    rw [GlobalTheory.SplitDualLat.form_mul, GlobalTheory.SplitDualLat.cA_cA, he.1.1, hπ.2.2.2, GlobalTheory.SplitDualLat.map_form, h1,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, dotProduct_single, mul_one] at h2
    exact (isInt_iff_le_one _).1 h2
  · intro h z hz
    have h1 := smul_mem_latHat V Λ _
      (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← RingHom.map_mul, he.1.1])) _ hz
    simp only [← RingHom.map_mul] at h1
    have h2 := (hcol z).1 h1
    have h3 := GlobalTheory.SplitDualLat.form_mul V (cA D e) 1 y z
    simp only [one_mul, mul_one, GlobalTheory.SplitDualLat.cA_cA] at h3
    have h4 : (fun k => rdA φ (z k)) = (frCo φ β).1 *ᵥ (((frCo φ β)⁻¹).1 *ᵥ fun k => rdA φ (z k)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [h3, hπ.2.2.2, GlobalTheory.SplitDualLat.map_form, h4, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      GlobalTheory.SplitHecke.isInt_iff]
    exact sum_mem fun i _ => mul_mem (GlobalTheory.SplitHecke.isInt_iff.1 ((isInt_iff_le_one _).2 (h i)))
      (GlobalTheory.SplitHecke.isInt_iff.1 ((isInt_iff_le_one _).2 (h2 i)))

end GlobalTheory.SplitRowLat

end

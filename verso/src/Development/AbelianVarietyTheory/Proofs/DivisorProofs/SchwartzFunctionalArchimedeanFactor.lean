import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeTranslationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeFourierInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproxScaledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIndicatorCosetSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumIndicatorNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartzStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.ThetaFunctionalUnique

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

variable (F κ) in

abbrev boxInd (a : F) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ))

variable (F κ) in

abbrev cosInd (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ))

/- English proof (translation)
Simplify using `[InfiniteAdeleRing.ringEquiv_mixedSpace]`. Both sides reduce to the same expression.
-/
theorem inf_rat (q : F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AF F) q).1 = mixedEmbedding F q := by
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

/- English proof (translation)
Establish `h` using `GlobalTheory.T.scaled_coset_indicator_schwartz F κ a ha 0`. Use `h using 2` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Simplify using the standard rewrite rules.
-/
theorem boxInd_mem_SB {a : F} (ha : a ≠ 0) : boxInd F κ a ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  have h := GlobalTheory.T.scaled_coset_indicator_schwartz F κ a ha 0
  convert h using 2
  ext y
  simp

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨f, g, hg, rfl⟩`.
-/
theorem pure_mem (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[schr, dotProduct]`.
-/
theorem schr_trans (ψ : AddChar (AF F) ℂ) (ξ : κ → F) (Φ : (κ → AF F) → ℂ) :
    schr ψ ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((0 : κ → F) i))) Φ =
      fun x => Φ (x + fun i => algebraMap F (AF F) (ξ i)) := by
  funext x
  simp [schr, dotProduct]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [pureA, hf, hg]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i + algebraMap F (AF F) (ξ i)).1) = InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 + mixedEmbedding F (ξ i)`.

Rewrite using `[← inf_rat]`. Conclude with `map_add _ _ _`.
-/
theorem pure_shift (f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (ξ : κ → F)
    (g g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hf : ∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i)))
    (hg : ∀ y, g' y = g (y + fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))) :
    (fun x => pureA F f g (x + fun i => algebraMap F (AF F) (ξ i))) = pureA F f' g' := by
  funext x
  simp only [pureA, hf, hg]
  congr 2
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i + algebraMap F (AF F) (ξ i)).1) =
    InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 + mixedEmbedding F (ξ i)
  rw [← inf_rat]
  exact map_add _ _ _

/- English proof (translation)
Establish `h` using `hinv ξ 0 Φ hΦ`. Rewrite `h` using `[schr_trans]`. Then use the resulting hypothesis.
-/
theorem L_shift (ψ : AddChar (AF F) ℂ) (L : ((κ → AF F) → ℂ) → ℂ)
    (hinv : ∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ)
    (ξ : κ → F) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    L (fun x => Φ (x + fun i => algebraMap F (AF F) (ξ i))) = L Φ := by
  have h := hinv ξ 0 Φ hΦ
  rwa [schr_trans] at h

/- English proof (translation)
Establish `h` using `GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F ψ hψ.2.1 ξ 0 Φ`. Rewrite `h` using `[schr_trans]`. Then use the resulting hypothesis.
-/
theorem theta_shift (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (ξ : κ → F) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (fun x => Φ (x + fun i => algebraMap F (AF F) (ξ i))) = thetaSum F Φ := by
  have h := GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F ψ hψ.2.1 ξ 0 Φ
  rwa [schr_trans] at h

/- English proof (translation)
Take `⟨c, hc⟩` from `GlobalTheory.T.scaled_lattice_translation_invariant F κ a ha T (fun ξ hξ f f' hf => by`. Rewrite using `[← hT, ← hT]`. Establish `e` using `pure_shift f f' ξ (boxInd F κ a) (boxInd F κ a) hf (fun y => by`. Simplify using `only [Set.indicator_apply, SetLike.mem_coe, AddSubgroup.add_mem_cancel_right _ hξ])`. Rewrite using `[← e]`.

Conclude with `L_shift ψ L hinv ξ (pure_mem f (boxInd_mem_SB ha)))`. Use the proof step `(fun b hb f f' hf => by`. Rewrite using `[← hT, ← hT, ← GlobalTheory.T.scaled_lattice_fourier_invariant F ψ hψ κ a ha b hb f f' hf]`. Establish `h` using `hinv 0 b _ (pure_mem f (boxInd_mem_SB ha))`. Establish `e0 : (fun i => algebraMap F (AF F) ((0 : κ → F) i)) = 0` using `by funext i; simp`.

Rewrite `h` using `[e0]`. Conclude with `h)`. Use `⟨c, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[hT, hc f]`. Use `congr 1`.

Unfold `thetaSum`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Establish `e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) i).1) = fun i => mixedEmbedding F (ξ i)`. Use function extensionality and compare the values at `i`. Conclude with `inf_rat (ξ i)`.

Establish `e2 : (fun i => ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) i).2) = fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)` using `rfl`. Simplify using `only [pureA, e1, e2, Set.indicator_apply, SetLike.mem_coe, Set.mem_setOf_eq]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem box_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (L : ((κ → AF F) → ℂ) → ℂ)
    (hinv : ∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ)
    {a : F} (ha : a ≠ 0) (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ)
    (hT : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f (boxInd F κ a)) = T f) :
    ∃ c : ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f (boxInd F κ a)) = c * thetaSum F (pureA F f (boxInd F κ a)) := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.scaled_lattice_translation_invariant F κ a ha T (fun ξ hξ f f' hf => by
      rw [← hT, ← hT]
      have e := pure_shift f f' ξ (boxInd F κ a) (boxInd F κ a) hf (fun y => by
        simp only [Set.indicator_apply, SetLike.mem_coe, AddSubgroup.add_mem_cancel_right _ hξ])
      rw [← e]
      exact L_shift ψ L hinv ξ (pure_mem f (boxInd_mem_SB ha)))
    (fun b hb f f' hf => by
      rw [← hT, ← hT, ← GlobalTheory.T.scaled_lattice_fourier_invariant F ψ hψ κ a ha b hb f f' hf]
      have h := hinv 0 b _ (pure_mem f (boxInd_mem_SB ha))
      have e0 : (fun i => algebraMap F (AF F) ((0 : κ → F) i)) = 0 := by funext i; simp
      rw [e0] at h
      exact h)
  refine ⟨c, fun f => ?_⟩
  rw [hT, hc f]
  congr 1
  unfold thetaSum
  refine tsum_congr fun ξ => ?_
  have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) i).1) = fun i => mixedEmbedding F (ξ i) := by
    funext i; exact inf_rat (ξ i)
  have e2 : (fun i => ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) i).2) =
      fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) := rfl
  simp only [pureA, e1, e2, Set.indicator_apply, SetLike.mem_coe, Set.mem_setOf_eq]
  split_ifs <;> simp

end GlobalTheory.ThetaFunctionalUnique

namespace GlobalTheory.ThetaFunctionalUnique

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
The claim follows from `GlobalTheory.T.scaled_coset_indicator_schwartz F κ a ha r`.
-/
theorem cosInd_mem_SB {a : F} (ha : a ≠ 0) (r : κ → FiniteAdeleRing (𝓞 F) F) :
    cosInd F κ a r ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) :=
  GlobalTheory.T.scaled_coset_indicator_schwartz F κ a ha r

/- English proof (translation)
Take `⟨ξ, hξ⟩` from `GlobalTheory.T.finite_adele_approx_scaled F κ a ha r`. Establish `hs : {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} = {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a}`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `add_mem h hξ` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Introduce `h`. Use `sub_mem h hξ` as an intermediate fact.

Rewrite `this` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Establish `hr : cosInd F κ a r = cosInd F κ a (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))`. Simplify using `only [cosInd, hs]`. Rewrite using `[hr]`. Use `set f' := SchwartzMap.compSubConstCLM ℂ (-(fun i => mixedEmbedding F (ξ i))) f with hf'def`.

Establish `hf' : ∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i))`. Introduce `x`. Simplify using `[hf'def, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]`. Establish `e` using `pure_shift f f' ξ (cosInd F κ a (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))) (boxInd F κ a) hf' (fun y => by simp only [Set.indicator_apply, SetLike.mem_coe, Set.mem_setOf_eq, add_sub_cancel_right])`. Establish `hm` using `pure_mem f (cosInd_mem_SB ha (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)))`.

Rewrite using `[← L_shift ψ L hinv ξ hm, ← theta_shift ψ hψ ξ, e, hc f']`.
-/
theorem cos_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (L : ((κ → AF F) → ℂ) → ℂ)
    (hinv : ∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ)
    {a : F} (ha : a ≠ 0) {c : ℂ}
    (hc : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      L (pureA F f (boxInd F κ a)) = c * thetaSum F (pureA F f (boxInd F κ a)))
    (r : κ → FiniteAdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    L (pureA F f (cosInd F κ a r)) = c * thetaSum F (pureA F f (cosInd F κ a r)) := by
  obtain ⟨ξ, hξ⟩ := GlobalTheory.T.finite_adele_approx_scaled F κ a ha r
  have hs : {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} =
      {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have := add_mem h hξ
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h hξ
      rwa [sub_sub_sub_cancel_right] at this
  have hr : cosInd F κ a r = cosInd F κ a (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) := by
    simp only [cosInd, hs]
  rw [hr]
  set f' := SchwartzMap.compSubConstCLM ℂ (-(fun i => mixedEmbedding F (ξ i))) f with hf'def
  have hf' : ∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i)) := by
    intro x
    simp [hf'def, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  have e := pure_shift f f' ξ (cosInd F κ a (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)))
    (boxInd F κ a) hf' (fun y => by simp only [Set.indicator_apply, SetLike.mem_coe, Set.mem_setOf_eq, add_sub_cancel_right])
  have hm := pure_mem f (cosInd_mem_SB ha (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)))
  rw [← L_shift ψ L hinv ξ hm, ← theta_shift ψ hψ ξ, e, hc f']

/- English proof (translation)
Establish `hL0 : L 0 = 0`. Establish `h` using `hsmul 0 0 (zero_mem _)`. Simplify using `using h`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hL0`.

Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.sum_insert hj, hadd _ (hΦ j (Finset.mem_insert_self _ _)) _ (Submodule.sum_mem _ fun k hk => hΦ k (Finset.mem_insert_of_mem hk)), ih fun k hk => hΦ k (Finset.mem_insert_of_mem hk)]`.
-/
theorem L_sum (L : ((κ → AF F) → ℂ) → ℂ) (hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, L (Φ + Ψ) = L Φ + L Ψ)
    (hsmul : ∀ (c : ℂ), ∀ Φ ∈ schA F κ, L (c • Φ) = c * L Φ) {ι : Type} (s : Finset ι)
    (Φ : ι → (κ → AF F) → ℂ) (hΦ : ∀ j ∈ s, Φ j ∈ schA F κ) : L (∑ j ∈ s, Φ j) = ∑ j ∈ s, L (Φ j) := by
  have hL0 : L 0 = 0 := by
    have h := hsmul 0 0 (zero_mem _)
    simpa using h
  induction s using Finset.induction_on with
  | empty => simpa using hL0
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      hadd _ (hΦ j (Finset.mem_insert_self _ _)) _ (Submodule.sum_mem _ fun k hk => hΦ k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hΦ k (Finset.mem_insert_of_mem hk)]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [thetaSum]`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.sum_insert hj, GlobalTheory.WeilM.thetaSum_add F (hΦ j (Finset.mem_insert_self _ _)) (Submodule.sum_mem _ fun k hk => hΦ k (Finset.mem_insert_of_mem hk)), ih fun k hk => hΦ k (Finset.mem_insert_of_mem hk)]`.
-/
theorem theta_sum {ι : Type} (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ) (hΦ : ∀ j ∈ s, Φ j ∈ schA F κ) :
    thetaSum F (∑ j ∈ s, Φ j) = ∑ j ∈ s, thetaSum F (Φ j) := by
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      GlobalTheory.WeilM.thetaSum_add F (hΦ j (Finset.mem_insert_self _ _))
        (Submodule.sum_mem _ fun k hk => hΦ k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hΦ k (Finset.mem_insert_of_mem hk)]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pure_sum (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {ι : Type} (s : Finset ι)
    (w : ι → ℂ) (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f (∑ j ∈ s, w j • g j) = ∑ j ∈ s, w j • pureA F f (g j) := by
  funext x
  simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Take `⟨R, hR⟩` from `GlobalTheory.T.scaled_indicator_coset_sum F κ a ha m hm`. Take `⟨f, hf⟩` from `GlobalTheory.T.theta_sum_indicator_nonzero F κ a ha`. Establish `ham : a * (m : F) ≠ 0` using `mul_ne_zero ha (by simpa using hm)`. Establish `hb : boxInd F κ a = cosInd F κ a 0`. Unfold `boxInd cosInd`.

Use `congr 1`. Use extensionality with `y`. Simplify using the standard rewrite rules. Establish `hsplit : pureA F f (boxInd F κ a) = ∑ ξ ∈ R, (1 : ℂ) • pureA F f (cosInd F κ (a * m) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)))`. Rewrite using `[← pure_sum]`.

Use `congr 1`. Rewrite using `[show boxInd F κ a = _ from hR]`. Simplify using the standard rewrite rules. Establish `hmem : ∀ ξ ∈ R, (1 : ℂ) • pureA F f (cosInd F κ (a * m) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))) ∈ schA F κ` using `fun ξ _ => Submodule.smul_mem _ _ (pure_mem f (cosInd_mem_SB ham _))`. Establish `h1` using `hc a ha 0 f`.

Rewrite `h1` using `[← hb]`. Establish `h2 : L (pureA F f (boxInd F κ a)) = c (a * m) * thetaSum F (pureA F f (boxInd F κ a))`. Rewrite using `[hsplit, L_sum L hadd hsmul R _ hmem, theta_sum R _ hmem, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun ξ _ => ?_` and prove the remaining obligations. Rewrite using `[one_smul, hc _ ham]`.

Conclude with `mul_right_cancel₀ hf (h1.symm.trans h2)`.
-/
theorem const_mul (L : ((κ → AF F) → ℂ) → ℂ) (hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, L (Φ + Ψ) = L Φ + L Ψ)
    (hsmul : ∀ (c : ℂ), ∀ Φ ∈ schA F κ, L (c • Φ) = c * L Φ) (c : F → ℂ)
    (hc : ∀ a : F, a ≠ 0 → ∀ (r : κ → FiniteAdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      L (pureA F f (cosInd F κ a r)) = c a * thetaSum F (pureA F f (cosInd F κ a r)))
    {a : F} (ha : a ≠ 0) (m : 𝓞 F) (hm : m ≠ 0) : c a = c (a * m) := by
  obtain ⟨R, hR⟩ := GlobalTheory.T.scaled_indicator_coset_sum F κ a ha m hm
  obtain ⟨f, hf⟩ := GlobalTheory.T.theta_sum_indicator_nonzero F κ a ha
  have ham : a * (m : F) ≠ 0 := mul_ne_zero ha (by simpa using hm)
  have hb : boxInd F κ a = cosInd F κ a 0 := by
    unfold boxInd cosInd
    congr 1
    ext y
    simp
  have hsplit : pureA F f (boxInd F κ a) = ∑ ξ ∈ R, (1 : ℂ) •
      pureA F f (cosInd F κ (a * m) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))) := by
    rw [← pure_sum]
    congr 1
    rw [show boxInd F κ a = _ from hR]
    simp
  have hmem : ∀ ξ ∈ R, (1 : ℂ) •
      pureA F f (cosInd F κ (a * m) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))) ∈ schA F κ :=
    fun ξ _ => Submodule.smul_mem _ _ (pure_mem f (cosInd_mem_SB ham _))
  have h1 := hc a ha 0 f
  rw [← hb] at h1
  have h2 : L (pureA F f (boxInd F κ a)) = c (a * m) * thetaSum F (pureA F f (boxInd F κ a)) := by
    rw [hsplit, L_sum L hadd hsmul R _ hmem, theta_sum R _ hmem, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [one_smul, hc _ ham]
  exact mul_right_cancel₀ hf (h1.symm.trans h2)

end GlobalTheory.ThetaFunctionalUnique

namespace GlobalTheory.ThetaFunctionalUnique

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ L hadd hsmul hadm hinv`. Establish `hbox : ∀ a : F, ∃ c : ℂ, a ≠ 0 → ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f (boxInd F κ a)) = c * thetaSum F (pureA F f (boxInd F κ a))`. Introduce `a`. Distinguish the cases in `ha : a = 0`. Conclude with `⟨0, fun h => absurd ha h⟩`.

Take `⟨T, hT⟩` from `hadm _ (boxInd_mem_SB ha)`. Take `⟨c, hc⟩` from `box_eq ψ hψ L hinv ha T hT`. Conclude with `⟨c, fun _ => hc⟩`. Use `choose c hc using hbox`. Establish `hcos : ∀ a : F, a ≠ 0 → ∀ (r : κ → FiniteAdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), L (pureA F f (cosInd F κ a r)) = c a * thetaSum F (pureA F f (cosInd F κ a r))` using `fun a ha r f => cos_eq ψ hψ L hinv ha (hc a ha) r f`.

Establish `hall : ∀ a : F, a ≠ 0 → c a = c 1`. Introduce `a ha`. Take `⟨p, q, hq, hpq⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) a`. Establish `hq0 : q ≠ 0` using `nonZeroDivisors.ne_zero hq`. Establish `hqF : (algebraMap (𝓞 F) F q) ≠ 0` using `by simpa using hq0`.

Establish `hp0 : p ≠ 0`. Introduce and unpack `rfl`. Apply `ha` to reduce the goal to its premises. Rewrite using `[← hpq]`. Simplify using the standard rewrite rules.

Establish `e : a * (q : F) = 1 * (p : F)`. Rewrite using `[← hpq]`. Establish `: (algebraMap (𝓞 F) F q) = (q : F)` using `rfl`. Establish `: (algebraMap (𝓞 F) F p) = (p : F)` using `rfl`. Clear the denominators using the available nonvanishing facts.

Combine the equalities or inequalities in the displayed calculation. Use `⟨c 1, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Establish `hΦ' : Φ ∈ Submodule.span ℂ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g}` using `hΦ`. Proceed by induction on `hΦ' using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨f, g, hg, rfl⟩` from `hx`. Take `⟨a, ha, R, hR⟩` from `GlobalTheory.EvAdm.exists_sum_cosets hg`. Establish `hsplit : pureA F f g = ∑ r ∈ R, g r • pureA F f (cosInd F κ a r)`. Rewrite using `[← pure_sum]`. Use `congr 1`.

Establish `hmem : ∀ r ∈ R, g r • pureA F f (cosInd F κ a r) ∈ schA F κ` using `fun r _ => Submodule.smul_mem _ _ (pure_mem f (cosInd_mem_SB ha r))`. Rewrite using `[hsplit, L_sum L hadd hsmul R _ hmem, theta_sum R _ hmem, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[hsmul _ _ (pure_mem f (cosInd_mem_SB ha r)), GlobalTheory.WeilM.thetaSum_smul F, hcos a ha r f, hall a ha]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `zero`. Establish `h` using `hsmul 0 0 (zero_mem _)`. Simplify using `only [zero_smul, zero_mul] at h`. Rewrite using `[h]`. Simplify using `[thetaSum]`.

Consider the case `add x y hx hy ihx ihy`. Rewrite using `[hadd x hx y hy, GlobalTheory.WeilM.thetaSum_add F hx hy, ihx hx, ihy hy]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul t x hx ih`. Rewrite using `[hsmul t x hx, GlobalTheory.WeilM.thetaSum_smul F, ih hx]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : ((κ → AF F) → ℂ) → ℂ),
    (∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, L (Φ + Ψ) = L Φ + L Ψ) →
    (∀ (c : ℂ), ∀ Φ ∈ schA F κ, L (c • Φ) = c * L Φ) →
    (∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f g) = T f) →
    (∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ) →
    ∃ c : ℂ, ∀ Φ ∈ schA F κ, L Φ = c * thetaSum F Φ := by
  intro F _ _ ψ hψ κ _ L hadd hsmul hadm hinv
  have hbox : ∀ a : F, ∃ c : ℂ, a ≠ 0 → ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      L (pureA F f (boxInd F κ a)) = c * thetaSum F (pureA F f (boxInd F κ a)) := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, fun h => absurd ha h⟩
    obtain ⟨T, hT⟩ := hadm _ (boxInd_mem_SB ha)
    obtain ⟨c, hc⟩ := box_eq ψ hψ L hinv ha T hT
    exact ⟨c, fun _ => hc⟩
  choose c hc using hbox
  have hcos : ∀ a : F, a ≠ 0 → ∀ (r : κ → FiniteAdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      L (pureA F f (cosInd F κ a r)) = c a * thetaSum F (pureA F f (cosInd F κ a r)) :=
    fun a ha r f => cos_eq ψ hψ L hinv ha (hc a ha) r f
  have hall : ∀ a : F, a ≠ 0 → c a = c 1 := by
    intro a ha
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqF : (algebraMap (𝓞 F) F q) ≠ 0 := by simpa using hq0
    have hp0 : p ≠ 0 := by
      rintro rfl
      apply ha
      rw [← hpq]
      simp
    have e : a * (q : F) = 1 * (p : F) := by
      rw [← hpq]
      have : (algebraMap (𝓞 F) F q) = (q : F) := rfl
      have : (algebraMap (𝓞 F) F p) = (p : F) := rfl
      field_simp
    calc c a = c (a * q) := const_mul L hadd hsmul c hcos ha q hq0
      _ = c (1 * p) := by rw [e]
      _ = c 1 := (const_mul L hadd hsmul c hcos one_ne_zero p hp0).symm
  refine ⟨c 1, fun Φ hΦ => ?_⟩
  have hΦ' : Φ ∈ Submodule.span ℂ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
      (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g} := hΦ
  induction hΦ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨a, ha, R, hR⟩ := GlobalTheory.EvAdm.exists_sum_cosets hg
    have hsplit : pureA F f g = ∑ r ∈ R, g r • pureA F f (cosInd F κ a r) := by
      rw [← pure_sum]
      congr 1
    have hmem : ∀ r ∈ R, g r • pureA F f (cosInd F κ a r) ∈ schA F κ :=
      fun r _ => Submodule.smul_mem _ _ (pure_mem f (cosInd_mem_SB ha r))
    rw [hsplit, L_sum L hadd hsmul R _ hmem, theta_sum R _ hmem, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hsmul _ _ (pure_mem f (cosInd_mem_SB ha r)), GlobalTheory.WeilM.thetaSum_smul F, hcos a ha r f, hall a ha]
    ring
  | zero =>
    have h := hsmul 0 0 (zero_mem _)
    simp only [zero_smul, zero_mul] at h
    rw [h]
    simp [thetaSum]
  | add x y hx hy ihx ihy =>
    rw [hadd x hx y hy, GlobalTheory.WeilM.thetaSum_add F hx hy, ihx hx, ihy hy]
    ring
  | smul t x hx ih =>
    rw [hsmul t x hx, GlobalTheory.WeilM.thetaSum_smul F, ih hx]
    ring

end GlobalTheory.ThetaFunctionalUnique

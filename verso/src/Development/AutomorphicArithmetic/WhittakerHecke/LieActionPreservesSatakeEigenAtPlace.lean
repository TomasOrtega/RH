import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLe
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

/- English proof (translation)
Introduce `E _ _ _ w B f X hf g`. Establish `hc : ∀ (k : GL (Fin 2) (Af E)) (φ : Sm E 2) (x : GA E 2), (lie E 2 X φ).1 (x * finGL E 2 k) = (lie E 2 X (GlobalTheory.CuspRep.rt E 2 (finGL E 2 k) φ)).1 x`. Introduce `k φ x`. Establish `h` using `LinearMap.congr_fun (lie_rt_fin X k) φ`. Conclude with `(congrArg (fun ψ : Sm E 2 => ψ.1 x) h).symm`.

Establish `hev : ∀ (k : GA E 2) (φ : Sm E 2) (x : GA E 2), (GlobalTheory.CuspRep.rt E 2 k φ).1 x = φ.1 (x * k)` using `fun _ _ _ => rfl`. Use `⟨(hf 1).card, ?_, ?_⟩` and prove the remaining obligations. Introduce `y k hk`. Establish `hfix : GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w k)) f = f`. Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations.

Establish `h` using `(hf x).inv 1 k hk`. Simplify using `only [one_mul, map_one, mul_one] at h`. Rewrite using `[hev]`. Conclude with `h`. Establish `e1 : g * finGL E 2 (locGL E 2 w (y * k)) = g * finGL E 2 (locGL E 2 w y) * finGL E 2 (locGL E 2 w k)`.

Simplify using `only [map_mul, mul_assoc]`. Use `show (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (y * k))) = (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w y))`. Rewrite using `[e1, hc, hfix]`. Introduce `ϖ hϖ j hj x`. Establish `hfin` using `(GlobalTheory.TjCount.tj_cosets_finite_card_le E w 2 ϖ hϖ j hj).1`.

Establish `hsum : ∀ W : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w 2 → ℂ, ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c = ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c`. Introduce `W`. Use `finsum_eq_sum_of_support_subset _ fun c hc' => ?_` and prove the remaining obligations. Rewrite using `[Set.Finite.coe_toFinset]`. Conclude with `fun h0 => hc' (by simp [h0])`.

Establish `key : ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out • GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w c.out)) f = GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 B j • f`. Use `Subtype.ext (funext fun z => ?_)` and prove the remaining obligations. Establish `h` using `(hf z).eig ϖ hϖ j hj 1`. Simplify using `only [one_mul, map_one, mul_one] at h`. Rewrite `h` using `[hsum fun c => f.1 (z * finGL E 2 (locGL E 2 w c.out))]`.

Simplify `h` using `[Submodule.coe_sum, Finset.sum_apply, hev]`. Establish `h2` using `congrArg (fun ψ : Sm E 2 => (lie E 2 X ψ).1 (g * finGL E 2 (locGL E 2 w x))) key`. Simplify using `only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h2`. Rewrite using `[hsum fun c => (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (x * c.out)))]`. Rewrite using `[← h2]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ← mul_assoc, hc]`.
-/
theorem UpperTheory.lie_action_preserves_satake_eigen_at_place :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (w : H.P E) (B : Multiset ℂˣ) (f : Sm E 2) (X : Lie E 2), UpperTheory.V.Af.Smo.EigAt w B f.1 → UpperTheory.V.Af.Smo.EigAt w B (lie E 2 X f).1 := by
  intro E _ _ _ w B f X hf g
  have hc : ∀ (k : GL (Fin 2) (Af E)) (φ : Sm E 2) (x : GA E 2),
      (lie E 2 X φ).1 (x * finGL E 2 k) = (lie E 2 X (GlobalTheory.CuspRep.rt E 2 (finGL E 2 k) φ)).1 x := by
    intro k φ x
    have h := LinearMap.congr_fun (lie_rt_fin X k) φ
    exact (congrArg (fun ψ : Sm E 2 => ψ.1 x) h).symm
  have hev : ∀ (k : GA E 2) (φ : Sm E 2) (x : GA E 2), (GlobalTheory.CuspRep.rt E 2 k φ).1 x = φ.1 (x * k) :=
    fun _ _ _ => rfl
  refine ⟨(hf 1).card, ?_, ?_⟩
  · intro y k hk
    have hfix : GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w k)) f = f := by
      refine Subtype.ext (funext fun x => ?_)
      have h := (hf x).inv 1 k hk
      simp only [one_mul, map_one, mul_one] at h
      rw [hev]
      exact h
    have e1 : g * finGL E 2 (locGL E 2 w (y * k)) =
        g * finGL E 2 (locGL E 2 w y) * finGL E 2 (locGL E 2 w k) := by
      simp only [map_mul, mul_assoc]
    show (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (y * k))) = (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w y))
    rw [e1, hc, hfix]
  · intro ϖ hϖ j hj x
    have hfin := (GlobalTheory.TjCount.tj_cosets_finite_card_le E w 2 ϖ hϖ j hj).1
    have hsum : ∀ W : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w 2 → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c =
          ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c := by
      intro W
      refine finsum_eq_sum_of_support_subset _ fun c hc' => ?_
      rw [Set.Finite.coe_toFinset]
      exact fun h0 => hc' (by simp [h0])
    have key : ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out •
          GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w c.out)) f =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 B j • f := by
      refine Subtype.ext (funext fun z => ?_)
      have h := (hf z).eig ϖ hϖ j hj 1
      simp only [one_mul, map_one, mul_one] at h
      rw [hsum fun c => f.1 (z * finGL E 2 (locGL E 2 w c.out))] at h
      simpa [Submodule.coe_sum, Finset.sum_apply, hev] using h
    have h2 := congrArg (fun ψ : Sm E 2 => (lie E 2 X ψ).1 (g * finGL E 2 (locGL E 2 w x))) key
    simp only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul] at h2
    rw [hsum fun c => (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (x * c.out)))]
    rw [← h2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_mul, ← mul_assoc, hc]

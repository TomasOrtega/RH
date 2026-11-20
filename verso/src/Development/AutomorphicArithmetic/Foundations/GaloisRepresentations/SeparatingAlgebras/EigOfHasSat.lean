import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.MemIffLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetEqOne
import GroundTheory.GlobalFields.LocalFieldAtPlace
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

/- English proof (translation)
Use `⟨hB.card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hv k hk]`. Establish `he` using `(hB.2 v hv hv0).2.2.2 ϖ hϖ j hj`. Set `ev : V →+ ℂ` to `{ toFun := fun ψ => l (ρ y ψ) map_zero' := by simp map_add' := fun _ _ => by simp }`. Establish `hs` using `ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w a) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ v)`.

Use `Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans ((congrArg ev he).trans ?_))` and prove the remaining obligations. Simplify using `[ev, map_mul, Module.End.mul_apply]`. Simplify using `[ev]`.
-/
private theorem eig_of_hasSat {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w ρ B) {v : V} (hv : v ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w a)) (hv0 : v ≠ 0)
    (l : Module.Dual ℂ V) : UpperTheory.V.Af.Smo.Eig w B fun g => l (ρ g v) := by
  refine ⟨hB.card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩
  · rw [map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hv k hk]
  · have he := (hB.2 v hv hv0).2.2.2 ϖ hϖ j hj
    let ev : V →+ ℂ :=
      { toFun := fun ψ => l (ρ y ψ)
        map_zero' := by simp
        map_add' := fun _ _ => by simp }
    have hs := ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w a)
      (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ v)
    refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans ((congrArg ev he).trans ?_))
    · simp [ev, map_mul, Module.End.mul_apply]
    · simp [ev]

/- English proof (translation)
Take `⟨hKeq, hu, hq, -⟩` from `UpperTheory.V.Af.Smo.sphDict E a w`. Establish `hTj` using `UpperTheory.V.Af.Smo.tjSet UpperTheory.V.Af.Smo.sphDict E a w`. Establish `hT : ∀ r ≤ a, minusculeHecke μ r ∈ eigenSubalgebra μ z f hf`. Introduce `r hr`. Use `GlobalTheory.HenQ.ShellOp.minuscule_mem_of z hf hr fun g => ?_` and prove the remaining obligations.

Rewrite using `[hKeq, ← hTj r hr, hE.eig _ hu r hr g, hq r hr, GlobalTheory.HenQ.ShellOp.esymm_eq, GlobalTheory.LFun.satEig]`. Conclude with `eigenSubalgebra_eq_top z hf hT (GlobalTheory.HenQ.ShellOp.central_mem_of_top z hf (hT a le_rfl))`.
-/
private theorem eigen_top {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}
    [MeasurableSpace (GL (Fin a) (w.adicCompletion E))] [BorelSpace (GL (Fin a) (w.adicCompletion E))]
    (μ : Measure (GL (Fin a) (w.adicCompletion E))) [μ.IsHaarMeasure] (z : Fin a → ℂˣ)
    {f : GL (Fin a) (w.adicCompletion E) → ℂ} (hE : UpperTheory.V.Af.Smo.Eig w (Finset.univ.val.map z) f)
    (hf : ∀ g, ∀ k ∈ GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a, f (g * k) = f g) :
    eigenSubalgebra μ z f hf = ⊤ := by
  obtain ⟨hKeq, hu, hq, -⟩ := UpperTheory.V.Af.Smo.sphDict E a w
  have hTj := UpperTheory.V.Af.Smo.tjSet UpperTheory.V.Af.Smo.sphDict E a w
  have hT : ∀ r ≤ a, minusculeHecke μ r ∈ eigenSubalgebra μ z f hf := by
    intro r hr
    refine GlobalTheory.HenQ.ShellOp.minuscule_mem_of z hf hr fun g => ?_
    rw [hKeq, ← hTj r hr, hE.eig _ hu r hr g, hq r hr, GlobalTheory.HenQ.ShellOp.esymm_eq, GlobalTheory.LFun.satEig]
  exact eigenSubalgebra_eq_top z hf hT (GlobalTheory.HenQ.ShellOp.central_mem_of_top z hf (hT a le_rfl))

end UpperTheory.Gal.Gen

open GroundTheory.Automorphic in
/- English proof (translation)
Introduce `hR hP E _ _ w a`. Use `borelize (GL (Fin a) (w.adicCompletion E))`. Set `μ : Measure (GL (Fin a) (w.adicCompletion E))` to `Measure.haar`. Take `⟨C0, hC0⟩` from `hP (w.adicCompletion E) a μ`. Establish `hKeq` using `(UpperTheory.V.Af.Smo.sphDict E a w).1`.

Take `⟨m, hm⟩ : ∃ m : ℝ, m = μ.real (GLnLocal.integralGL (w.adicCompletion E) a : Set (GL (Fin a) (w.adicCompletion E)))` from `⟨_, rfl⟩`. Use `⟨m ^ 2 * C0, fun p hp => ?_⟩` and prove the remaining obligations. Rewrite `hp` using `[← range_satakeTransform (μ := μ) (F := w.adicCompletion E) (n := a)]`. Take `⟨H, rfl⟩` from `(AlgHom.mem_range _).1 hp`. Take `⟨T, hT⟩` from `hR (w.adicCompletion E) a μ H`.

Set `h : GL (Fin a) (w.adicCompletion E) →₀ ℂ` to `Finsupp.onFinset T (fun g => if g ∈ T then (m : ℂ) * (H : HeckeAlgebra μ) g else 0) (fun g hg => by`. Assume the negation of the conclusion as `hgT`. Simplify using `[hgT] at hg)`. Establish `hsupp : h.support ⊆ T` using `Finsupp.support_onFinset_subset`. Establish `hval : ∀ g ∈ T, h g = (m : ℂ) * (H : HeckeAlgebra μ) g` using `fun g hg => by`.

Simplify using `[h, hg]`. Use `⟨h, fun g hg g' hg' hk => hT.1 g (hsupp hg) g' (hsupp hg') (hKeq ▸ hk), ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun g hg => ?_` and prove the remaining obligations.

Rewrite using `[hval g hg, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Use `_ ≤ m ^ 2 * (C0 * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) (satakeTransform μ H)‖ ^ 2) := mul_le_mul_of_nonneg_left (hC0 H T hT) (by positivity)`. Use `_ = _ := by ring`. Introduce `σ z hz v hv`. Distinguish the cases in `hv0 : v = 0`.

Substitute `hv0` using the available equality. Simplify using `[opOf]`. Rewrite using `[← sub_eq_zero]`. Use `(Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_` and prove the remaining obligations. Establish `hE` using `eig_of_hasSat w σ.ρ hz hv hv0 l`.

Establish `hf : ∀ g, ∀ k ∈ GLnLocal.integralGL (w.adicCompletion E) a, l (σ.ρ (g * k) v) = l (σ.ρ g v)`. Rewrite using `[hKeq]`. Conclude with `hE.inv`. Establish `h1 : H ∈ eigenSubalgebra μ z (fun g => l (σ.ρ g v)) hf` using `eigen_top w μ z hE hf ▸ Algebra.mem_top`. Establish `h2` using `h1 1`.

Simplify using `only [one_mul, map_one, Module.End.one_apply] at h2`. Establish `h3` using `hT.2 (fun g => l (σ.ρ g v)) hf`. Establish `h4 : l (opOf σ.ρ h v) = (m : ℂ) * ∑ g ∈ T, (H : HeckeAlgebra μ) g * l (σ.ρ g v)`. Rewrite using `[opOf, Finsupp.sum_of_support_subset h hsupp _ (by simp), map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun g hg => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, hval g hg, smul_eq_mul, mul_assoc]`. Rewrite using `[map_sub, map_smul, smul_eq_mul, h4, hm, ← h3, h2, sub_self]`.
-/
theorem UpperTheory.Gal.Gen.locOp_pf :
    UpperTheory.Gal.Gen.RepsEx → UpperTheory.Gal.Gen.Planch → UpperTheory.Gal.Gen.LocOp := by
  intro hR hP E _ _ w a
  classical
  borelize (GL (Fin a) (w.adicCompletion E))
  let μ : Measure (GL (Fin a) (w.adicCompletion E)) := Measure.haar
  obtain ⟨C0, hC0⟩ := hP (w.adicCompletion E) a μ
  have hKeq := (UpperTheory.V.Af.Smo.sphDict E a w).1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = μ.real (GLnLocal.integralGL (w.adicCompletion E) a : Set (GL (Fin a) (w.adicCompletion E))) := ⟨_, rfl⟩
  refine ⟨m ^ 2 * C0, fun p hp => ?_⟩
  rw [← range_satakeTransform (μ := μ) (F := w.adicCompletion E) (n := a)] at hp
  obtain ⟨H, rfl⟩ := (AlgHom.mem_range _).1 hp
  obtain ⟨T, hT⟩ := hR (w.adicCompletion E) a μ H
  let h : GL (Fin a) (w.adicCompletion E) →₀ ℂ :=
    Finsupp.onFinset T (fun g => if g ∈ T then (m : ℂ) * (H : HeckeAlgebra μ) g else 0) (fun g hg => by
      by_contra hgT
      simp [hgT] at hg)
  have hsupp : h.support ⊆ T := Finsupp.support_onFinset_subset
  have hval : ∀ g ∈ T, h g = (m : ℂ) * (H : HeckeAlgebra μ) g := fun g hg => by
    simp [h, hg]
  refine ⟨h, fun g hg g' hg' hk => hT.1 g (hsupp hg) g' (hsupp hg') (hKeq ▸ hk), ?_, ?_⟩
  · calc ∑ g ∈ h.support, ‖h g‖ ^ 2 ≤ ∑ g ∈ T, ‖h g‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsupp fun _ _ _ => by positivity
      _ = m ^ 2 * ∑ g ∈ T, ‖(H : HeckeAlgebra μ) g‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g hg => ?_
          rw [hval g hg, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ ≤ m ^ 2 * (C0 * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) (satakeTransform μ H)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hC0 H T hT) (by positivity)
      _ = _ := by ring
  · intro σ z hz v hv
    by_cases hv0 : v = 0
    · subst hv0
      simp [opOf]
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_
    have hE := eig_of_hasSat w σ.ρ hz hv hv0 l
    have hf : ∀ g, ∀ k ∈ GLnLocal.integralGL (w.adicCompletion E) a, l (σ.ρ (g * k) v) = l (σ.ρ g v) := by
      rw [hKeq]
      exact hE.inv
    have h1 : H ∈ eigenSubalgebra μ z (fun g => l (σ.ρ g v)) hf := eigen_top w μ z hE hf ▸ Algebra.mem_top
    have h2 := h1 1
    simp only [one_mul, map_one, Module.End.one_apply] at h2
    have h3 := hT.2 (fun g => l (σ.ρ g v)) hf
    have h4 : l (opOf σ.ρ h v) = (m : ℂ) * ∑ g ∈ T, (H : HeckeAlgebra μ) g * l (σ.ρ g v) := by
      rw [opOf, Finsupp.sum_of_support_subset h hsupp _ (by simp), map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_smul, hval g hg, smul_eq_mul, mul_assoc]
    rw [map_sub, map_smul, smul_eq_mul, h4, hm, ← h3, h2, sub_self]

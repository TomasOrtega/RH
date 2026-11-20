import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaFixedProd

/- English proof (translation)
Establish `hs : IsAddFundamentalDomain Γ ((fun x => x - l) ⁻¹' 𝓕) μ` using `h𝓕.preimage_of_equiv (measurePreserving_sub_right μ l).quasiMeasurePreserving (e := id) Function.bijective_id (fun g x => by show (g +ᵥ x) - l = g +ᵥ (x - l)`. Simplify using `only [AddSubgroup.vadd_def, vadd_eq_add]`. Use the proof step `abel)`. Establish `e1 : ∫ x in 𝓕, h (x + l) ∂μ = ∫ y in (fun x => x - l) ⁻¹' 𝓕, h y ∂μ`. Rewrite using `[← (measurePreserving_add_right μ l).setIntegral_preimage_emb (measurableEmbedding_addRight l) h]`.

Use `congr 2`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[e1]`. Conclude with `hs.setIntegral_eq h𝓕 fun g x => hper g g.2 x`.
-/
theorem setIntegral_add_right {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] {𝓕 : Set G} (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → ℂ)
    (hper : ∀ γ ∈ Γ, ∀ x, h (γ + x) = h x) (l : G) :
    ∫ x in 𝓕, h (x + l) ∂μ = ∫ x in 𝓕, h x ∂μ := by
  have hs : IsAddFundamentalDomain Γ ((fun x => x - l) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_sub_right μ l).quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by
        show (g +ᵥ x) - l = g +ᵥ (x - l)
        simp only [AddSubgroup.vadd_def, vadd_eq_add]
        abel)
  have e1 : ∫ x in 𝓕, h (x + l) ∂μ = ∫ y in (fun x => x - l) ⁻¹' 𝓕, h y ∂μ := by
    rw [← (measurePreserving_add_right μ l).setIntegral_preimage_emb (measurableEmbedding_addRight l) h]
    congr 2
    ext x
    simp
  rw [e1]
  exact hs.setIntegral_eq h𝓕 fun g x => hper g g.2 x

/- English proof (translation)
Introduce `D ψ S T hψ N M hMV hc hn f g hf hfN hg hgN x`. Take `⟨i1, i2, i3, i4, i5, K, hK, hKc⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D T S`. Use `haveI : BorelSpace (WO S T) := ⟨rfl⟩`. Use `haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Take `⟨μ, 𝓕, hμ, h𝓕, -⟩` from `(GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1`.

Use `haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by`. Rewrite using `[Measure.restrict_apply_univ]`. Conclude with `GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩`. Take `⟨l1, l2, -, l4, -⟩` from `GlobalTheory.OrientedFormLaws.symplOH_laws D S T`. Establish `hth` using `(GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1`.

Establish `hcomp` using `(GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1`. Set `Θ : Submodule ℂ (WO S T → ℂ)` to `{ carrier := {f | IsThetaFunO ψ S T f ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f} add_mem' := fun {a b} ha hb => ⟨GlobalTheory.WeilVacMove.isTheta_add ha.1 hb.1, fun u hu h0 => by`. Use function extensionality and compare the values at `w`. Establish `e1` using `congrFun (ha.2 u hu h0) w`. Establish `e2` using `congrFun (hb.2 u hu h0) w`.

Simplify using `only [heisO, Pi.add_apply] at e1 e2 ⊢`. Rewrite using `[mul_add, e1, e2]⟩`. Use the proof step `zero_mem' := ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun u _ _ => by funext w; simp [heisO]⟩`. Use the proof step `smul_mem' := fun c a ha => ⟨GlobalTheory.WeilVacMove.isTheta_smul c ha.1, fun u hu h0 => by`. Use function extensionality and compare the values at `w`.

Establish `e1` using `congrFun (ha.2 u hu h0) w`. Simplify using `only [heisO, Pi.smul_apply, smul_eq_mul] at e1 ⊢`. Rewrite using `[mul_left_comm, e1]⟩ }`. Establish `hb : ∀ a ∈ Θ, ∃ C : ℝ, ∀ w, ‖a w‖ ≤ C` using `fun a ha => by`. Establish `hp : ∀ γ ∈ ratL T S, ∀ w, ‖a (γ + w)‖ = ‖a w‖`.

Introduce and unpack `_ ⟨γ, rfl⟩ w`. Conclude with `(congrArg norm (ha.1.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul])`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn ha.1.cont.continuousOn`. Use `⟨C, fun w => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, h⟩` from `hKc w`.

Rewrite using `[← hp γ hγ w]`. Conclude with `hC _ h`. Establish `hMΘ : ∀ a ∈ Θ, M a ∈ Θ` using `fun a ha => hMV a ha.1 ha.2`. Establish `hpol : ∀ a a', a ∈ Θ → a' ∈ Θ → ∫ w in 𝓕, M a w * star (M a' w) ∂μ = ∫ w in 𝓕, a w * star (a' w) ∂μ` using `fun a a' ha ha' => GlobalTheory.Mem.LiftPolar.integral_mul_star_eq (μ.restrict 𝓕) Θ (fun b hb => hb.1.cont.measurable) hb M hMΘ (fun b hb => hn μ 𝓕 hμ h𝓕 b hb.1 hb.2) a a' ha ha'`. Establish `hint : ∀ a a', IsThetaFunO ψ S T a → IsThetaFunO ψ S T a' → Integrable (fun w => a w * star (a' w)) (μ.restrict 𝓕)` using `fun a a' ha ha' => by`.

Establish `hcont : Continuous fun w => a w * star (a' w)` using `ha.cont.mul ha'.cont.star`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hcont.continuousOn`. Use `Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Take `⟨γ, hγ, h⟩` from `hKc w`. Rewrite using `[← GlobalTheory.ThetaSchur.prod_periodic hψ ha ha' hγ w]`.

Conclude with `hC _ h`. Establish `hfix : ∀ a a', a ∈ Θ → a' ∈ Θ → ∀ l ∈ N, l.map (infPart D) = 0 → ∀ w, a (w + l) * star (a' (w + l)) = a w * star (a' w)` using `fun a a' ha ha' l hl h0 w => by`. Establish `e1` using `congrFun (ha.2 l hl h0) w`. Establish `e2` using `congrFun (ha'.2 l hl h0) w`. Simplify using `only [heisO] at e1 e2`.

Rewrite using `[← e1, ← e2, star_mul']`. Take the linear combination `-(a (w + l) * star (a' (w + l))) * GlobalTheory.ThetaSchur.mul_star_psi hψ (symplOH S T w l)`. Establish `hfΘ : f ∈ Θ` using `⟨hf, hfN⟩`. Establish `hgΘ : g ∈ Θ` using `⟨hg, hgN⟩`. Establish `hadd : ∀ y z γ : WO S T, ψ (symplO S T (y + z) γ) = ψ (symplO S T y γ) * ψ (symplO S T z γ)` using `fun y z γ => by`.

Simplify using `only [← l4, l1, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `key` using `GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S) (fun γ x => ψ (symplO S T x γ)) (fun γ => by`. Establish `: Continuous fun x : WO S T => symplOH S T x (γ : WO S T)` using `GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const`. Simplify using `only [← l4]`.

Conclude with `hψ.1.1.comp (this.add this))`. Use the proof step `(fun γ x y => hadd x y γ)`. Use the proof step `(fun γ γ' x => by`. Simplify using `only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]`. Use the proof step `ring)`.

Use the proof step `(fun x => by`. Simplify using `only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])`. Use the proof step `(fun γ x => hψ.1.2.1 _)`. Use the proof step `(fun x => by`. Rewrite using `[← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]`.

Conclude with `⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)`. Use `μ 𝓕 hμ h𝓕 (fun x => M f x * star (M g x) - f x * star (g x))`. Use the proof step `(((hMΘ f hfΘ).1.cont.mul (hMΘ g hgΘ).1.cont.star).sub (hf.cont.mul hg.cont.star))`. Use the proof step `(fun γ hγ x => by`. Rewrite using `[GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hγ, GlobalTheory.ThetaSchur.prod_periodic hψ (hMΘ f hfΘ).1 (hMΘ g hgΘ).1 hγ])`.

Use the proof step `(fun γ => by show ∫ x in 𝓕, ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)) ∂μ = 0`. Distinguish the cases in `hγ : ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (γ : WO S T) l) = 1`. Establish `hγf : heisO ψ S T γ f ∈ Θ` using `⟨hth _ f hf, fun u hu h0 => by`. Use function extensionality and compare the values at `w`. Establish `a1` using `congrFun (hcomp u γ f) w`.

Establish `a2` using `congrFun (hcomp γ u f) w`. Rewrite `a2` using `[hfN u hu h0, add_comm (γ : WO S T) u]`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at a1 a2`. Rewrite using `[a1, a2]`. Use `congr 1`.

Establish `h1` using `hγ u hu h0`. Rewrite `h1` using `[← l4, AddChar.map_add_eq_mul]`. Rewrite using `[GlobalTheory.WeilVacMove.symplOH_skew S T (γ : WO S T) u]`. Establish `h2 : ψ (-symplOH S T (γ : WO S T) u) * ψ (symplOH S T (γ : WO S T) u) = 1`. Rewrite using `[← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]`.

Take the linear combination `(-ψ (-symplOH S T (γ : WO S T) u)) * h1 + ψ (symplOH S T (γ : WO S T) u) * h2⟩`. Establish `e : (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) = fun x => M (heisO ψ S T γ f) x * star (M g x) - heisO ψ S T γ f x * star (g x)`. Use function extensionality and compare the values at `x`. Rewrite using `[hc _ f hf hfN hγ, GlobalTheory.ThetaSchur.heisO_rat hf γ.2, GlobalTheory.ThetaSchur.heisO_rat (hMΘ f hfΘ).1 γ.2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, integral_sub (hint _ _ (hMΘ _ hγf).1 (hMΘ g hgΘ).1) (hint _ _ hγf.1 hg), hpol _ _ hγf hgΘ, sub_self]`. Use `push_neg at hγ`. Take `⟨l, hl, h0, hne⟩` from `hγ`. Establish `hper : ∀ δ ∈ ratL T S, ∀ x, (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) (δ + x) = (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) x`. Introduce `δ hδ x`.

Simplify using `only`. Rewrite using `[hadd, (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T δ).2 hδ γ γ.2, one_mul, GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hδ, GlobalTheory.ThetaSchur.prod_periodic hψ (hMΘ f hfΘ).1 (hMΘ g hgΘ).1 hδ]`. Establish `htr` using `GlobalTheory.ThetaFixedProd.setIntegral_add_right (G := WO S T) (ratL T S) μ h𝓕 (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) hper l`. Simplify using `only [hadd, hfix _ _ (hMΘ f hfΘ) (hMΘ g hgΘ) l hl h0, hfix _ _ hfΘ hgΘ l hl h0] at htr`. Establish `hsk : symplO S T l γ = -symplO S T (γ : WO S T) l`.

Rewrite using `[← l4, ← l4, GlobalTheory.WeilVacMove.symplOH_skew S T (γ : WO S T) l]`. Normalize the expressions using the abelian group laws. Establish `hc1 : ψ (symplO S T l γ) ≠ 1` using `fun h1 => by`. Apply `hne` to reduce the goal to its premises. Rewrite `h1` using `[hsk]`.

Establish `h2 : ψ (symplO S T (γ : WO S T) l) * ψ (-symplO S T (γ : WO S T) l) = 1`. Rewrite using `[← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`. Rewrite `h2` using `[h1, mul_one]`. Conclude with `h2`. Establish `e2 : (fun x => ψ (symplO S T x γ) * ψ (symplO S T l γ) * (M f x * star (M g x) - f x * star (g x))) = fun x => ψ (symplO S T l γ) * (ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)))`.

Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Rewrite `htr` using `[e2, integral_const_mul]`. Establish `h3 : (ψ (symplO S T l γ) - 1) * ∫ x in 𝓕, ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)) ∂μ = 0`. Take the linear combination `htr`.

Conclude with `(mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc1))`. Conclude with `sub_eq_zero.1 (congrFun key x)`.
-/
theorem prod_eq_of_fixed : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (M f) = M f) → (∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → ∀ x, M f x * star (M g x) = f x * star (g x) := by
  intro D ψ S T hψ N M hMV hc hn f g hf hfN hg hgN x
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hcomp := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1
  let Θ : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | IsThetaFunO ψ S T f ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f}
      add_mem' := fun {a b} ha hb => ⟨GlobalTheory.WeilVacMove.isTheta_add ha.1 hb.1, fun u hu h0 => by
        funext w
        have e1 := congrFun (ha.2 u hu h0) w
        have e2 := congrFun (hb.2 u hu h0) w
        simp only [heisO, Pi.add_apply] at e1 e2 ⊢
        rw [mul_add, e1, e2]⟩
      zero_mem' := ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun u _ _ => by funext w; simp [heisO]⟩
      smul_mem' := fun c a ha => ⟨GlobalTheory.WeilVacMove.isTheta_smul c ha.1, fun u hu h0 => by
        funext w
        have e1 := congrFun (ha.2 u hu h0) w
        simp only [heisO, Pi.smul_apply, smul_eq_mul] at e1 ⊢
        rw [mul_left_comm, e1]⟩ }
  have hb : ∀ a ∈ Θ, ∃ C : ℝ, ∀ w, ‖a w‖ ≤ C := fun a ha => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖a (γ + w)‖ = ‖a w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (ha.1.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ha.1.cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  have hMΘ : ∀ a ∈ Θ, M a ∈ Θ := fun a ha => hMV a ha.1 ha.2
  have hpol : ∀ a a', a ∈ Θ → a' ∈ Θ → ∫ w in 𝓕, M a w * star (M a' w) ∂μ = ∫ w in 𝓕, a w * star (a' w) ∂μ :=
    fun a a' ha ha' => GlobalTheory.Mem.LiftPolar.integral_mul_star_eq (μ.restrict 𝓕) Θ (fun b hb => hb.1.cont.measurable) hb M
      hMΘ (fun b hb => hn μ 𝓕 hμ h𝓕 b hb.1 hb.2) a a' ha ha'
  have hint : ∀ a a', IsThetaFunO ψ S T a → IsThetaFunO ψ S T a' →
      Integrable (fun w => a w * star (a' w)) (μ.restrict 𝓕) := fun a a' ha ha' => by
    have hcont : Continuous fun w => a w * star (a' w) := ha.cont.mul ha'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ ha ha' hγ w]
    exact hC _ h
  have hfix : ∀ a a', a ∈ Θ → a' ∈ Θ → ∀ l ∈ N, l.map (infPart D) = 0 → ∀ w,
      a (w + l) * star (a' (w + l)) = a w * star (a' w) := fun a a' ha ha' l hl h0 w => by
    have e1 := congrFun (ha.2 l hl h0) w
    have e2 := congrFun (ha'.2 l hl h0) w
    simp only [heisO] at e1 e2
    rw [← e1, ← e2, star_mul']
    linear_combination -(a (w + l) * star (a' (w + l))) * GlobalTheory.ThetaSchur.mul_star_psi hψ (symplOH S T w l)
  have hfΘ : f ∈ Θ := ⟨hf, hfN⟩
  have hgΘ : g ∈ Θ := ⟨hg, hgN⟩
  have hadd : ∀ y z γ : WO S T, ψ (symplO S T (y + z) γ) = ψ (symplO S T y γ) * ψ (symplO S T z γ) := fun y z γ => by
    simp only [← l4, l1, AddChar.map_add_eq_mul]
    ring
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => hadd x y γ)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    μ 𝓕 hμ h𝓕 (fun x => M f x * star (M g x) - f x * star (g x))
    (((hMΘ f hfΘ).1.cont.mul (hMΘ g hgΘ).1.cont.star).sub (hf.cont.mul hg.cont.star))
    (fun γ hγ x => by
      rw [GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hγ,
        GlobalTheory.ThetaSchur.prod_periodic hψ (hMΘ f hfΘ).1 (hMΘ g hgΘ).1 hγ])
    (fun γ => by
      show ∫ x in 𝓕, ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)) ∂μ = 0
      by_cases hγ : ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (γ : WO S T) l) = 1
      · have hγf : heisO ψ S T γ f ∈ Θ := ⟨hth _ f hf, fun u hu h0 => by
          funext w
          have a1 := congrFun (hcomp u γ f) w
          have a2 := congrFun (hcomp γ u f) w
          rw [hfN u hu h0, add_comm (γ : WO S T) u] at a2
          simp only [Pi.smul_apply, smul_eq_mul] at a1 a2
          rw [a1, a2]
          congr 1
          have h1 := hγ u hu h0
          rw [← l4, AddChar.map_add_eq_mul] at h1
          rw [GlobalTheory.WeilVacMove.symplOH_skew S T (γ : WO S T) u]
          have h2 : ψ (-symplOH S T (γ : WO S T) u) * ψ (symplOH S T (γ : WO S T) u) = 1 := by
            rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
          linear_combination (-ψ (-symplOH S T (γ : WO S T) u)) * h1 + ψ (symplOH S T (γ : WO S T) u) * h2⟩
        have e : (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) = fun x =>
            M (heisO ψ S T γ f) x * star (M g x) - heisO ψ S T γ f x * star (g x) := by
          funext x
          rw [hc _ f hf hfN hγ, GlobalTheory.ThetaSchur.heisO_rat hf γ.2, GlobalTheory.ThetaSchur.heisO_rat (hMΘ f hfΘ).1 γ.2]
          ring
        rw [e, integral_sub (hint _ _ (hMΘ _ hγf).1 (hMΘ g hgΘ).1) (hint _ _ hγf.1 hg), hpol _ _ hγf hgΘ, sub_self]
      · push_neg at hγ
        obtain ⟨l, hl, h0, hne⟩ := hγ
        have hper : ∀ δ ∈ ratL T S, ∀ x, (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)))
            (δ + x) = (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) x := by
          intro δ hδ x
          simp only
          rw [hadd, (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T δ).2 hδ γ γ.2, one_mul,
            GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hδ,
            GlobalTheory.ThetaSchur.prod_periodic hψ (hMΘ f hfΘ).1 (hMΘ g hgΘ).1 hδ]
        have htr := GlobalTheory.ThetaFixedProd.setIntegral_add_right (G := WO S T) (ratL T S) μ h𝓕
          (fun x => ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) hper l
        simp only [hadd, hfix _ _ (hMΘ f hfΘ) (hMΘ g hgΘ) l hl h0, hfix _ _ hfΘ hgΘ l hl h0] at htr
        have hsk : symplO S T l γ = -symplO S T (γ : WO S T) l := by
          rw [← l4, ← l4, GlobalTheory.WeilVacMove.symplOH_skew S T (γ : WO S T) l]
          abel
        have hc1 : ψ (symplO S T l γ) ≠ 1 := fun h1 => by
          apply hne
          rw [hsk] at h1
          have h2 : ψ (symplO S T (γ : WO S T) l) * ψ (-symplO S T (γ : WO S T) l) = 1 := by
            rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
          rw [h1, mul_one] at h2
          exact h2
        have e2 : (fun x => ψ (symplO S T x γ) * ψ (symplO S T l γ) * (M f x * star (M g x) - f x * star (g x))) =
            fun x => ψ (symplO S T l γ) * (ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x))) := by
          funext x
          ring
        rw [e2, integral_const_mul] at htr
        have h3 : (ψ (symplO S T l γ) - 1) *
            ∫ x in 𝓕, ψ (symplO S T x γ) * (M f x * star (M g x) - f x * star (g x)) ∂μ = 0 := by
          linear_combination htr
        exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc1))
  exact sub_eq_zero.1 (congrFun key x)

end GlobalTheory.ThetaFixedProd

end

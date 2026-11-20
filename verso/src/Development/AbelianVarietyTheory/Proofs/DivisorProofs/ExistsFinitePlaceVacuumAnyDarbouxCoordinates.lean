import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGeneratoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAddCharSymplecticSelfPairingPlaceCoordStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOneStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacAny

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co v`. Take `⟨θ, hθ⟩` from `GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB`. Take `⟨M, _, g, hΓ⟩` from `GlobalTheory.T.tensorLatticeAtFinitePlace_eq_integral_span_generators X Y hX.lat hY.lat v`. Set `γf : (M → v.adicCompletionIntegers F) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)` to `fun a => ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)`. Set `u : M → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)` to `fun m => (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i), fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i))`.

Set `χ : (M → v.adicCompletionIntegers F) → ℂ` to `fun a => B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM …`. Establish `he : ∀ a, co.e (γf a) = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))`. Introduce `a`. Simplify using `only [γf, map_sum, map_smul]`. Establish `hcomp : ∀ a i, (co.e (γf a)).1 i = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i ∧ (co.e (γf a)).2 i = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRo …`.

Introduce `a i`. Rewrite using `[he]`. Simplify using `[Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, smul_eq_mul]`. Establish `hAt : ∀ a i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 i) ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).2 i)`. Introduce `a i`.

Rewrite using `[(hcomp a i).1, (hcomp a i).2]`. Conclude with `⟨GlobalTheory.VacAny.at_sum _ fun m _ => GlobalTheory.VacAny.at_mul_right (GlobalTheory.VacAny.at_atPlace _) _, GlobalTheory.VacAny.at_sum _ fun m _ => GlobalTheory.VacAny.at_mul_right (GlobalTheory.VacAny.at_atPlace _) _⟩`. Establish `hev : ∀ a, ((fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i)), (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i))) = ∑ m, (a m : Fv F v) • u m`. Introduce `a`. Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations.

Simplify using `[(hcomp a i).1, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.fst_sum, Finset.sum_apply, u]`. Simplify using `[(hcomp a i).2, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.snd_sum, Finset.sum_apply, u]`. Establish `hψ : ∀ z : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → B.ψ z = GlobalTheory.VacAny.psiV B.ψ v (GlobalTheory.AdelicU.evFin F v z)` using `fun z hz => by`. Rewrite using `[GlobalTheory.VacAny.psiV_apply, ← GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v z hz]`. Establish `hzero : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → γf a = 0`.

Introduce `a h`. Rewrite `h` using `[← hev a]`. Establish `h1 : co.e (γf a) = 0`. Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v _ (hAt a i).1, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i) = 0 from congrFun (congrArg Prod.fst h) i, map_zero]`.

Both sides reduce to the same expression. Rewrite using `[GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v _ (hAt a i).2, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i) = 0 from congrFun (congrArg Prod.snd h) i, map_zero]`. Both sides reduce to the same expression. Conclude with `co.e.map_eq_zero_iff.1 h1`. Establish `hker : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → χ a = 1`.

Introduce `a h`. Simplify using `only [χ, hzero a h]`. Simplify using `[GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]`. Establish `hadd : ∀ a b, γf (a + b) = γf a + γf b`. Introduce `a b`.

Simplify using `only [γf]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[show (((a + b) m : v.adicCompletionIntegers F) : Fv F v) = (a m : Fv F v) + b m from rfl, map_add, add_smul]`. Establish `hmem : ∀ a, γf a ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v` using `fun a => (hΓ _).2 ⟨a, rfl⟩`.

Establish `hdot : ∀ a b, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) ∧ GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) = (∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2`. Introduce `a b`. Use `⟨GlobalTheory.VacAny.at_sum _ fun i _ => GlobalTheory.VacAny.at_mul_right (hAt a i).1 _, ?_⟩` and prove the remaining obligations. Rewrite using `[← hev a, ← hev b]`. Simplify using `only [dotProduct, map_sum, map_mul]`.

Establish `hcoc : ∀ a b, χ (a + b) = χ a * χ b * GlobalTheory.VacAny.psiV B.ψ v (-(⅟(2 : Fv F v) * ((∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 - (∑ m, (b m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (a m : Fv F v) • u m).2)))`. Introduce `a b`. Simplify using `only [χ]`. Rewrite using `[hadd, GlobalTheory.T.addChar_halfTrace_tensorLattice_heisenbergCocycle B hB X Y r s r' s' hX hY θ hθ v _ (hmem a) _ (hmem b), co.form]`. Use `congr 1`.

Establish `hz` using `GlobalTheory.VacAny.at_neg (GlobalTheory.VacAny.at_mul_left (⅟(2 : AF F)) (GlobalTheory.VacAny.at_sub (hdot a b).1 (hdot b a).1))`. Rewrite using `[hψ _ hz, map_neg, map_mul, map_sub, (hdot a b).2, (hdot b a).2, GlobalTheory.VacAny.evFin_invOf_two]`. Take `⟨φ, hφSB, hφ0, hφ⟩` from `GlobalTheory.T.exists_schroedinger_eigenvector_compact_cocycle v (GlobalTheory.VacAny.psiV B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v) (GlobalTheory.T.standardTraceAdelicAddChar_localComponent_ne_one B.ψ hB.std v) u χ (GlobalTheory.T.continuous_addChar_symplecticSelfP …`. Use `⟨φ, hφSB, hφ0, θ, hθ, ?_⟩` and prove the remaining obligations. Introduce `γ hγ`.

Take `⟨a, rfl⟩` from `(hΓ γ).1 hγ`. Introduce `rr hrr`. Use `show GlobalTheory.WeilM.schr B.ψ (co.e (γf a)) _ = _`. Rewrite using `[GlobalTheory.T.adelicSchrodinger_tensor_eq_local_of_supportedAt B.ψ v (co.e (γf a)) (fun i => (hAt a i).1) (fun i => (hAt a i).2) φ rr hrr.1, hev a, hφ a]`.
-/
theorem exists_isVac_any_darboux : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
    ∃ φ, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v φ := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co v
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB
  obtain ⟨M, _, g, hΓ⟩ := GlobalTheory.T.tensorLatticeAtFinitePlace_eq_integral_span_generators X Y hX.lat hY.lat v
  let γf : (M → v.adicCompletionIntegers F) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :=
    fun a => ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)
  let u : M → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) := fun m =>
    (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i),
     fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i))
  let χ : (M → v.adicCompletionIntegers F) → ℂ := fun a => B.ψ (⅟(2 : AF F) *
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γf a) (γf a))
  have he : ∀ a, co.e (γf a) =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) := by
    intro a
    simp only [γf, map_sum, map_smul]
  have hcomp : ∀ a i, (co.e (γf a)).1 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i ∧
      (co.e (γf a)).2 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i := by
    intro a i
    rw [he]
    simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, smul_eq_mul]
  have hAt : ∀ a i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 i) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).2 i) := by
    intro a i
    rw [(hcomp a i).1, (hcomp a i).2]
    exact ⟨GlobalTheory.VacAny.at_sum _ fun m _ => GlobalTheory.VacAny.at_mul_right (GlobalTheory.VacAny.at_atPlace _) _,
      GlobalTheory.VacAny.at_sum _ fun m _ => GlobalTheory.VacAny.at_mul_right (GlobalTheory.VacAny.at_atPlace _) _⟩
  have hev : ∀ a, ((fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i)),
      (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i))) = ∑ m, (a m : Fv F v) • u m := by
    intro a
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [(hcomp a i).1, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.fst_sum, Finset.sum_apply, u]
    · simp [(hcomp a i).2, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.snd_sum, Finset.sum_apply, u]
  have hψ : ∀ z : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z →
      B.ψ z = GlobalTheory.VacAny.psiV B.ψ v (GlobalTheory.AdelicU.evFin F v z) := fun z hz => by
    rw [GlobalTheory.VacAny.psiV_apply, ← GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v z hz]
  have hzero : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → γf a = 0 := by
    intro a h
    rw [← hev a] at h
    have h1 : co.e (γf a) = 0 := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · rw [GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v _ (hAt a i).1, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i) = 0 from
          congrFun (congrArg Prod.fst h) i, map_zero]
        rfl
      · rw [GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v _ (hAt a i).2, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i) = 0 from
          congrFun (congrArg Prod.snd h) i, map_zero]
        rfl
    exact co.e.map_eq_zero_iff.1 h1
  have hker : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → χ a = 1 := by
    intro a h
    simp only [χ, hzero a h]
    simp [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
  have hadd : ∀ a b, γf (a + b) = γf a + γf b := by
    intro a b
    simp only [γf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show (((a + b) m : v.adicCompletionIntegers F) : Fv F v) = (a m : Fv F v) + b m from rfl, map_add, add_smul]
  have hmem : ∀ a, γf a ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v := fun a => (hΓ _).2 ⟨a, rfl⟩
  have hdot : ∀ a b, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) ∧
      GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) =
        (∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 := by
    intro a b
    refine ⟨GlobalTheory.VacAny.at_sum _ fun i _ => GlobalTheory.VacAny.at_mul_right (hAt a i).1 _, ?_⟩
    rw [← hev a, ← hev b]
    simp only [dotProduct, map_sum, map_mul]
  have hcoc : ∀ a b, χ (a + b) = χ a * χ b * GlobalTheory.VacAny.psiV B.ψ v
      (-(⅟(2 : Fv F v) * ((∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 -
        (∑ m, (b m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (a m : Fv F v) • u m).2))) := by
    intro a b
    simp only [χ]
    rw [hadd, GlobalTheory.T.addChar_halfTrace_tensorLattice_heisenbergCocycle B hB X Y r s r' s' hX hY θ hθ v _ (hmem a) _ (hmem b), co.form]
    congr 1
    have hz := GlobalTheory.VacAny.at_neg (GlobalTheory.VacAny.at_mul_left (⅟(2 : AF F))
      (GlobalTheory.VacAny.at_sub (hdot a b).1 (hdot b a).1))
    rw [hψ _ hz, map_neg, map_mul, map_sub, (hdot a b).2, (hdot b a).2, GlobalTheory.VacAny.evFin_invOf_two]
  obtain ⟨φ, hφSB, hφ0, hφ⟩ := GlobalTheory.T.exists_schroedinger_eigenvector_compact_cocycle v (GlobalTheory.VacAny.psiV B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (GlobalTheory.T.standardTraceAdelicAddChar_localComponent_ne_one B.ψ hB.std v) u χ (GlobalTheory.T.continuous_addChar_symplecticSelfPairing_placeCoordinates σ B.ψ hB.std.1 X.J Y.J (θ : E) v g) hker hcoc
  refine ⟨φ, hφSB, hφ0, θ, hθ, ?_⟩
  intro γ hγ
  obtain ⟨a, rfl⟩ := (hΓ γ).1 hγ
  intro rr hrr
  show GlobalTheory.WeilM.schr B.ψ (co.e (γf a)) _ = _
  rw [GlobalTheory.T.adelicSchrodinger_tensor_eq_local_of_supportedAt B.ψ v (co.e (γf a)) (fun i => (hAt a i).1) (fun i => (hAt a i).2) φ rr hrr.1, hev a, hφ a]

end GlobalTheory.VacAny

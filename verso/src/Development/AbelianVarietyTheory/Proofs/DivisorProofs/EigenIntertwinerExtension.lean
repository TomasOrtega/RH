import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvNeZero

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨a, ha⟩ : ∃ a, g a ≠ 0` from `by by_contra! h`. Conclude with `hg (SchwartzMap.ext h)`. Establish `hfin : {v | ¬ φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite` using `hstd`. Use `set T := hfin.toFinset with hT`. Establish `hy : ∀ v, ∃ y : κ → Fv F v, φ v y ≠ 0` using `fun v => by by_contra! h`.

Conclude with `h0 v (funext h)`. Use `choose y hy using hy`. Set `xf : κ → Af F` to `fun i => ⟨fun v => if v ∈ T then y v i else 0, by filter_upwards [T.eventually_cofinite_notMem] with v hv`. Simplify using `only [if_neg hv]`. Conclude with `zero_mem _⟩`.

Set `x : κ → AF F` to `fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), xf i)`. Introduce `hz`. Establish `hx` using `congrFun hz x`. Establish `e1 : (fun i => evI F (x i)) = a` using `funext fun i => by simp [x, evI]`. Establish `e2 : ∀ v, (fun i => evFin F v (x i)) = fun i => if v ∈ T then y v i else 0` using `fun v => funext fun i => rfl`.

Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, e1, e2] at hx`. Rewrite `hx` using `[finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_]`. Break down `mul_eq_zero.1 hx with h | h` into its components or cases. Conclude with `ha h`. Take `⟨v, hv, h⟩` from `Finset.prod_eq_zero_iff.1 h`.

Simplify using `only [hv, if_true] at h`. Conclude with `hy v h`. Introduce `v hv`. Assume the negation of the conclusion as `hvT`. Apply `hv` to reduce the goal to its premises.

Establish `hφ : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1`. Assume the negation of the conclusion as `hc`. Conclude with `hvT (hfin.mem_toFinset.2 hc)`. Establish `hvT' : v ∉ T` using `hvT`. Simplify using `only [hvT', if_false, hφ]`.

Rewrite using `[Set.indicator_of_mem (s := {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}) (a := fun _ => 0) (fun i => zero_mem _)]`. Both sides reduce to the same expression.
-/
theorem pure_ne_zero {κ : Type} [Fintype κ] (g : SInf F κ) (hg : g ≠ 0) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
    by_contra! h
    exact hg (SchwartzMap.ext h)
  have hfin : {v | ¬ φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite := hstd
  set T := hfin.toFinset with hT
  have hy : ∀ v, ∃ y : κ → Fv F v, φ v y ≠ 0 := fun v => by
    by_contra! h
    exact h0 v (funext h)
  choose y hy using hy
  let xf : κ → Af F := fun i => ⟨fun v => if v ∈ T then y v i else 0, by
    filter_upwards [T.eventually_cofinite_notMem] with v hv
    simp only [if_neg hv]
    exact zero_mem _⟩
  let x : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), xf i)
  intro hz
  have hx := congrFun hz x
  have e1 : (fun i => evI F (x i)) = a := funext fun i => by simp [x, evI]
  have e2 : ∀ v, (fun i => evFin F v (x i)) = fun i => if v ∈ T then y v i else 0 := fun v => funext fun i => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, e1, e2] at hx
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_] at hx
  · rcases mul_eq_zero.1 hx with h | h
    · exact ha h
    · obtain ⟨v, hv, h⟩ := Finset.prod_eq_zero_iff.1 h
      simp only [hv, if_true] at h
      exact hy v h
  · intro v hv
    by_contra hvT
    apply hv
    have hφ : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      by_contra hc
      exact hvT (hfin.mem_toFinset.2 hc)
    have hvT' : v ∉ T := hvT
    simp only [hvT', if_false, hφ]
    rw [Set.indicator_of_mem (s := {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}) (a := fun _ => 0)
      (fun i => zero_mem _)]
    rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ he`. Take `⟨ei, ev, hei, hev, hpure⟩` from `he.loc`. Take `⟨f, hf⟩ : ∃ f, ei f ≠ 0` from `by by_contra! h`. Conclude with `hei (ContinuousLinearMap.ext h)`. Establish `hfam : GlobalTheory.BigNZ.Fam M M.vac` using `⟨fun v => (hM.vac v).1, Filter.Eventually.of_forall fun _ => rfl⟩`.

Use `⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac, hfam.mem hM f, ?_⟩` and prove the remaining obligations. Rewrite using `[hpure f M.vac hfam.1 hfam.2]`. Establish `hv : (fun v => ev v (M.vac v)) = M₁.vac` using `funext fun v => (hev v).1`. Rewrite using `[hv]`. Conclude with `pure_ne_zero (ei f) hf M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std`.
-/
theorem exists_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ he
  obtain ⟨ei, ev, hei, hev, hpure⟩ := he.loc
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra! h
    exact hei (ContinuousLinearMap.ext h)
  have hfam : GlobalTheory.BigNZ.Fam M M.vac := ⟨fun v => (hM.vac v).1, Filter.Eventually.of_forall fun _ => rfl⟩
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac, hfam.mem hM f, ?_⟩
  rw [hpure f M.vac hfam.1 hfam.2]
  have hv : (fun v => ev v (M.vac v)) = M₁.vac := funext fun v => (hev v).1
  rw [hv]
  exact pure_ne_zero (ei f) hf M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std

end GlobalTheory.ThK.EvNeZero

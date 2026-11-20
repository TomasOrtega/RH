import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSpanFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxDerivativeExistence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.IndLine.LowFin

open GlobalTheory.ThK.PlaneEv (dH HasDH)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def dHdir (f : SInf F κ) :
    ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) → ℂ) where
  toFun v := dH v.1 v.2 ⇑f
  map_add' v w := by
    funext x
    simp only [dH, Prod.fst_add, Prod.snd_add, map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    push_cast
    ring
  map_smul' r v := by
    funext x
    simp only [dH, Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Pi.smul_apply, mul_smul_comm,
      ← Finset.smul_sum, smul_eq_mul, Complex.real_smul]
    push_cast
    ring

def dHfun (a b : κ → mixedEmbedding.mixedSpace F) : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) where
  toFun f := dH a b ⇑f
  map_add' f g := by
    funext x
    have e : (⇑(f + g) : (κ → mixedEmbedding.mixedSpace F) → ℂ) = ⇑f + ⇑g := by ext y; simp
    simp only [dH, Pi.add_apply]
    rw [e, fderiv_add (f.differentiableAt) (g.differentiableAt)]
    simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
    ring
  map_smul' c f := by
    funext x
    have e : (⇑(c • f) : (κ → mixedEmbedding.mixedSpace F) → ℂ) = c • ⇑f := by ext y; simp
    simp only [dH, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [e, fderiv_const_smul (f.differentiableAt)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.smul_apply]
    ring

def coeL : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) where
  toFun f := ⇑f
  map_add' f g := by ext y; simp
  map_smul' c f := by ext y; simp

/- English proof (translation)
Set `bV` to `Module.finBasis ℝ ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))`. Set `bN` to `Module.finBasis ℂ N`. Set `T : Submodule ℂ ((κ → mixedEmbedding.mixedSpace F) → ℂ)` to `Submodule.span ℂ (Set.range fun p : Fin (Module.finrank ℝ ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) × Fin (Module.finrank ℂ N) => dH (bV p.1).1 (bV p.1).2 ⇑(bN p.2 : SInf F κ))`. Use `haveI hT : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)`. Establish `base : ∀ (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) j, dH v.1 v.2 ⇑(bN j : SInf F κ) ∈ T`.

Introduce `v j`. Establish `e : dH v.1 v.2 ⇑(bN j : SInf F κ) = dHdir (bN j : SInf F κ) v` using `rfl`. Rewrite using `[e, ← bV.sum_repr v, map_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`.

Conclude with `Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(k, j), rfl⟩)`. Establish `key : ∀ (a b : κ → mixedEmbedding.mixedSpace F), ∀ f ∈ N, dH a b ⇑f ∈ T`. Introduce `a b f hf`. Establish `hf' : f = ∑ j, bN.repr ⟨f, hf⟩ j • (bN j : SInf F κ)`. Use `congrArg N.subtype (bN.sum_repr ⟨f, hf⟩)` as an intermediate fact.

Rewrite `this` using `[map_sum]`. Simplify using `only [map_smul, Submodule.subtype_apply] at this`. Conclude with `this.symm`. Establish `e : dH a b ⇑f = dHfun a b f` using `rfl`. Rewrite using `[e, hf', map_sum]`.

Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ (base (a, b) j)`. Establish `hinj : Function.Injective (coeL (F` using `F) (κ := κ)) := fun f g h => SchwartzMap.ext (congrFun h)`. Set `ι : T.comap coeL →ₗ[ℂ] T` to `(coeL.domRestrict (T.comap coeL)).codRestrict T (fun x => x.2)`.

Establish `hι : Function.Injective ι`. Introduce `x y h`. Conclude with `Subtype.ext (hinj (congrArg Subtype.val h))`. Use `haveI : FiniteDimensional ℂ (T.comap coeL) := Module.Finite.of_injective ι hι`. Establish `hle : Submodule.span ℂ {f₁ : SInf F κ | ∃ a b, ∃ f ∈ N, ⇑f₁ = dH a b ⇑f} ≤ T.comap coeL`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `f₁ ⟨a, b, f, hf, h⟩`. Use `show ⇑f₁ ∈ T`. Rewrite using `[h]`. Conclude with `key a b f hf`.

Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem finiteDimensional_span_dH (N : Submodule ℂ (SInf F κ)) [FiniteDimensional ℂ N] :
    FiniteDimensional ℂ (Submodule.span ℂ {f₁ : SInf F κ | ∃ a b, ∃ f ∈ N, ⇑f₁ = dH a b ⇑f}) := by
  let bV := Module.finBasis ℝ ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
  let bN := Module.finBasis ℂ N
  let T : Submodule ℂ ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    Submodule.span ℂ (Set.range fun p : Fin (Module.finrank ℝ ((κ → mixedEmbedding.mixedSpace F) ×
      (κ → mixedEmbedding.mixedSpace F))) × Fin (Module.finrank ℂ N) =>
        dH (bV p.1).1 (bV p.1).2 ⇑(bN p.2 : SInf F κ))
  haveI hT : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have base : ∀ (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) j,
      dH v.1 v.2 ⇑(bN j : SInf F κ) ∈ T := by
    intro v j
    have e : dH v.1 v.2 ⇑(bN j : SInf F κ) = dHdir (bN j : SInf F κ) v := rfl
    rw [e, ← bV.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(k, j), rfl⟩)
  have key : ∀ (a b : κ → mixedEmbedding.mixedSpace F), ∀ f ∈ N, dH a b ⇑f ∈ T := by
    intro a b f hf
    have hf' : f = ∑ j, bN.repr ⟨f, hf⟩ j • (bN j : SInf F κ) := by
      have := congrArg N.subtype (bN.sum_repr ⟨f, hf⟩)
      rw [map_sum] at this
      simp only [map_smul, Submodule.subtype_apply] at this
      exact this.symm
    have e : dH a b ⇑f = dHfun a b f := rfl
    rw [e, hf', map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (base (a, b) j)
  have hinj : Function.Injective (coeL (F := F) (κ := κ)) := fun f g h => SchwartzMap.ext (congrFun h)
  let ι : T.comap coeL →ₗ[ℂ] T := (coeL.domRestrict (T.comap coeL)).codRestrict T (fun x => x.2)
  have hι : Function.Injective ι := by
    intro x y h
    exact Subtype.ext (hinj (congrArg Subtype.val h))
  haveI : FiniteDimensional ℂ (T.comap coeL) := Module.Finite.of_injective ι hι
  have hle : Submodule.span ℂ {f₁ : SInf F κ | ∃ a b, ∃ f ∈ N, ⇑f₁ = dH a b ⇑f} ≤ T.comap coeL := by
    refine Submodule.span_le.2 ?_
    rintro f₁ ⟨a, b, f, hf, h⟩
    show ⇑f₁ ∈ T
    rw [h]
    exact key a b f hf
  exact Submodule.finiteDimensional_of_le hle

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Establish `hL` using `GlobalTheory.ThK.PlaneEv.LineDer.derivLines F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ _ _ M.co hψ GlobalTheory.T.archHeisenbergDerivatives_exist GlobalTheory.RealLift.actsLaws`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact h0`. Consider the case `succ k ih`.

Rewrite using `[fockDeg_succ]`. Use `haveI := ih`. Use `haveI := finiteDimensional_span_dH (F := F) (fockDeg M ψ τ k)`. Establish `hle : Submodule.span ℂ {f₁ : SInf F (Fin n × Fin d) | ∃ u, At (evI F) u ∧ ∃ f ∈ fockDeg M ψ τ k, ActsD (evI F) (M.heisLine ψ u) f f₁} ≤ Submodule.span ℂ {f₁ : SInf F (Fin n × Fin d) | ∃ a b, ∃ f ∈ fockDeg M ψ τ k, ⇑f₁ = dH a b ⇑f}`. Use `Submodule.span_mono ?_` and prove the remaining obligations.

Introduce and unpack `f₁ ⟨u, hu, f, hf, hd⟩`. Conclude with `⟨_, _, f, hf, (hL.2.1 u hu f f₁).1 hd⟩`. Use `haveI := Submodule.finiteDimensional_of_le hle`. Use `infer_instance`.
-/
theorem finiteDimensional_fockDeg (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (hψ : IsStd ψ) (h0 : FiniteDimensional ℂ (Submodule.span ℂ {f₀ | M.IsGauss ψ τ f₀})) :
    ∀ k, FiniteDimensional ℂ (fockDeg M ψ τ k) := by
  have hL := GlobalTheory.ThK.PlaneEv.LineDer.derivLines F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ _ _ M.co hψ GlobalTheory.T.archHeisenbergDerivatives_exist
    GlobalTheory.RealLift.actsLaws
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [fockDeg_succ]
    haveI := ih
    haveI := finiteDimensional_span_dH (F := F) (fockDeg M ψ τ k)
    have hle : Submodule.span ℂ {f₁ : SInf F (Fin n × Fin d) | ∃ u, At (evI F) u ∧ ∃ f ∈ fockDeg M ψ τ k,
        ActsD (evI F) (M.heisLine ψ u) f f₁} ≤
        Submodule.span ℂ {f₁ : SInf F (Fin n × Fin d) | ∃ a b, ∃ f ∈ fockDeg M ψ τ k, ⇑f₁ = dH a b ⇑f} := by
      refine Submodule.span_mono ?_
      rintro f₁ ⟨u, hu, f, hf, hd⟩
      exact ⟨_, _, f, hf, (hL.2.1 u hu f f₁).1 hd⟩
    haveI := Submodule.finiteDimensional_of_le hle
    infer_instance

end GlobalTheory.IndLine.LowFin

namespace GlobalTheory.IndLine

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B a a' G X om om' R Rf hM`. Establish `hP` using `(GlobalTheory.ThK.Check.isPair_of_isTriple hM.triple).1`. Establish `h0` using `GlobalTheory.T.fockVacua_span_finiteDimensional F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP`. Use `haveI := LowFin.finiteDimensional_fockDeg G.M B.ψ B.emb hM.triple.base.std h0 (lowDegInf B G.M R.p)`. Unfold `lowPartInf`.

Use `infer_instance`.
-/
theorem finiteDimensional_lowPartInf : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      FiniteDimensional ℂ (lowPartInf B G.M R.p) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hM.triple).1
  have h0 := GlobalTheory.T.fockVacua_span_finiteDimensional F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hP
  haveI := LowFin.finiteDimensional_fockDeg G.M B.ψ B.emb hM.triple.base.std h0 (lowDegInf B G.M R.p)
  unfold lowPartInf
  infer_instance

end GlobalTheory.IndLine

/- English proof (translation)
The claim follows from `GlobalTheory.IndLine.finiteDimensional_lowPartInf`.
-/
example : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      FiniteDimensional ℂ (lowPartInf B G.M R.p) := GlobalTheory.IndLine.finiteDimensional_lowPartInf

end

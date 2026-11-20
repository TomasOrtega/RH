import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LowKTypeStab

open GlobalTheory.FockCompactW GlobalTheory.RealLift

section Filt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Take `⟨D, hD⟩` from `GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ`. Establish `hL` using `actsLaws F (Fin n × Fin d)`. Establish `hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine ψ u) φ (D u φ)` using `fun u hu φ => (hD u hu φ).1`. Establish `hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) φ (D u φ)` using `fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M ψ u) (hSD u hu φ)`. Establish `hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ))` using `fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))`.

Establish `hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul]`. Express the relevant statement in the definitionally equal form `(mat (k * k⁻¹))ᵀ = 1`. Rewrite using `[mul_inv_cancel]`. Conclude with `Matrix.transpose_one`.

Establish `hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u` using `fun u => by`. Rewrite using `[Matrix.mul_assoc, hkk, Matrix.mul_one]`. Establish `hgauss : ∀ f₀, M.IsGauss ψ τ f₀ → M.IsGauss ψ τ (A f₀)`. Introduce `f₀ hf₀`. Take `⟨ε, hε⟩` from `hf₀`.

Use `⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩` and prove the remaining obligations. Establish `hv` using `at_mul_right hu (mat k⁻¹)ᵀ`. Establish `hv'` using `at_mul_right hu' (mat k⁻¹)ᵀ`. Establish `h1` using `hint _ hv f₀`. Establish `h2` using `hint _ hv' f₀`.

Rewrite `h1`, `h2` using `[hcan]`. Establish `e1` using `(hL _ _ _).2.2.1 _ hg h1`. Establish `e2` using `(hL _ _ _).2.2.1 _ hg' h2`. Establish `key` using `hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)`. Rewrite using `[e1, e2, key, map_smul]`.

Establish `hm : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1`. Rewrite using `[← Matrix.map_mul]`. Express the relevant statement in the definitionally equal form `(mat (k⁻¹ * k)).map _ = 1`. Rewrite using `[inv_mul_cancel]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.

Establish `hm' : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1` using `mul_eq_one_comm.1 hm`. Establish `hc : (mat k⁻¹).map (piInf (τ w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (τ w))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]`. Use `congr 1`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]`. Proceed by induction on `j with`. Consider the case `zero`. Rewrite using `[fockDeg_zero]`.

Conclude with `Submodule.span_le.2 fun f₀ hf₀ => Submodule.subset_span (hgauss f₀ hf₀)`. Consider the case `succ j ih`. Rewrite using `[fockDeg_succ]`. Use `sup_le (ih.trans (Submodule.comap_mono le_sup_left)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `φ₁ ⟨u, hu, φ, hφ, hd⟩`.

Establish `e : φ₁ = D u φ` using `(hL _ _ _).2.2.1 _ hd (hAD u hu φ)`. Rewrite using `[e]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨u * (mat k)ᵀ, at_mul_right hu _, A φ, ih hφ, hint u hu φ⟩)`.
-/
theorem fockDeg_stable {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W}
    (hψ : IsStd ψ) (hw : M.IsWeil ψ χX χW om) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {k : UA σ W.J} (hk : k ∈ KInf σ W τ) (A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))
    (hA : ∀ φ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (⇑φ) (⇑(A φ))) (j : ℕ) :
    fockDeg M ψ τ j ≤ (fockDeg M ψ τ j).comap A := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  have hgauss : ∀ f₀, M.IsGauss ψ τ f₀ → M.IsGauss ψ τ (A f₀) := by
    intro f₀ hf₀
    obtain ⟨ε, hε⟩ := hf₀
    refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
    have hv := at_mul_right hu (mat k⁻¹)ᵀ
    have hv' := at_mul_right hu' (mat k⁻¹)ᵀ
    have h1 := hint _ hv f₀
    have h2 := hint _ hv' f₀
    rw [hcan] at h1 h2
    have e1 := (hL _ _ _).2.2.1 _ hg h1
    have e2 := (hL _ _ _).2.2.1 _ hg' h2
    have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
    · rw [e1, e2, key, map_smul]
    · have hm : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
        rw [← Matrix.map_mul]
        change (mat (k⁻¹ * k)).map _ = 1
        rw [inv_mul_cancel]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      have hm' : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := mul_eq_one_comm.1 hm
      have hc : (mat k⁻¹).map (piInf (τ w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (τ w)) := by
        calc _ = (mat k⁻¹).map (piInf (τ w)) * W.θ w *
              ((mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w))) := by rw [hm', Matrix.mul_one]
          _ = (mat k⁻¹).map (piInf (τ w)) * (W.θ w * (mat k).map (piInf (τ w))) *
              (mat k⁻¹).map (piInf (τ w)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
      rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]
  induction j with
  | zero =>
    rw [fockDeg_zero]
    exact Submodule.span_le.2 fun f₀ hf₀ => Submodule.subset_span (hgauss f₀ hf₀)
  | succ j ih =>
    rw [fockDeg_succ]
    refine sup_le (ih.trans (Submodule.comap_mono le_sup_left)) (Submodule.span_le.2 ?_)
    rintro φ₁ ⟨u, hu, φ, hφ, hd⟩
    have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hd (hAD u hu φ)
    rw [e]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨u * (mat k)ᵀ, at_mul_right hu _, A φ, ih hφ, hint u hu φ⟩)

end Filt

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' R Rf hM k hk f hf f₁ hf₁ hlow`. Establish `hψ : IsStd B.ψ` using `hM.triple.base.std`. Establish `h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evI F)`. Introduce `u _`. Simplify using `[mat]`.

Establish `h1' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evI F)`. Introduce `u _`. Simplify using `[mat]`. Take `⟨A, hA⟩` from `exists_op_of_UAt hψ hM.triple.weil (1, k) h1 hk.1`. Take `⟨A', hA'⟩` from `exists_op_of_UAt hψ hM.triple.weil' (1, k) h1' hk.1`.

Take `⟨g, hg, hgf⟩` from `hlow`. Establish `hgPol` using `fockDeg_le_pol G.M B.ψ B.emb _ hg`. Establish `hfm : R.p f ∈ (G.M'.Pol B.ψ B.emb).map R.p'`. Rewrite using `[hM.real.quot'.onto]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨f', hf', hf'e⟩` from `hfm`. Establish `e1 : R.p f₁ = R.p' (A' f')` using `hM.real.cpt k hk f hf f' hf' f₁ (A' f') hf₁ (hA' f') hf'e.symm`. Establish `e2 : R.p (A g) = R.p' (A' f')` using `hM.real.cpt k hk g hgPol f' hf' (A g) (A' f') (hA g) (hA' f') (hgf.trans hf'e.symm)`. Conclude with `⟨A g, fockDeg_stable hψ hM.triple.weil B.emb hk A hA _ hg, e2.trans e1.symm⟩`.
-/
theorem lowPartInf_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      Acts (evI F) (om (1, k)) f f₁ → R.p f ∈ lowPartInf B G.M R.p → R.p f₁ ∈ lowPartInf B G.M R.p := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hM k hk f hf f₁ hf₁ hlow
  have hψ : IsStd B.ψ := hM.triple.base.std
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evI F) := by
    intro u _
    simp [mat]
  have h1' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evI F) := by
    intro u _
    simp [mat]
  obtain ⟨A, hA⟩ := exists_op_of_UAt hψ hM.triple.weil (1, k) h1 hk.1
  obtain ⟨A', hA'⟩ := exists_op_of_UAt hψ hM.triple.weil' (1, k) h1' hk.1
  obtain ⟨g, hg, hgf⟩ := hlow
  have hgPol := fockDeg_le_pol G.M B.ψ B.emb _ hg
  have hfm : R.p f ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by
    rw [hM.real.quot'.onto]
    trivial
  obtain ⟨f', hf', hf'e⟩ := hfm
  have e1 : R.p f₁ = R.p' (A' f') := hM.real.cpt k hk f hf f' hf' f₁ (A' f') hf₁ (hA' f') hf'e.symm
  have e2 : R.p (A g) = R.p' (A' f') :=
    hM.real.cpt k hk g hgPol f' hf' (A g) (A' f') (hA g) (hA' f') (hgf.trans hf'e.symm)
  exact ⟨A g, fockDeg_stable hψ hM.triple.weil B.emb hk A hA _ hg, e2.trans e1.symm⟩

end GlobalTheory.LowKTypeStab

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaTripleProportionalToNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperThetaSubmoduleInKernel
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Take `⟨D, hD⟩` from `GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std`. Establish `hL` using `GlobalTheory.RealLift.actsLaws F (Fin n × Fin d)`. Establish `hSD : ∀ u, At (evI F) u → ∀ φ, GlobalTheory.RealLift.SD (M.heisLine B.ψ u) φ (D u φ)` using `fun u hu φ => (hD u hu φ).1`. Establish `hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ)` using `fun u hu φ => (hL φ _ φ).1 _ (GlobalTheory.KInfPol.heisLine_zero M B.ψ u) (hSD u hu φ)`. Establish `hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ))` using `fun u hu φ => (hL _ _ φ).1 _ (GlobalTheory.KInfPol.heisLine_zero M B.ψ _) (GlobalTheory.KInfPol.sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))`.

Establish `hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul]`. Express the relevant statement in the definitionally equal form `(mat (k * k⁻¹))ᵀ = 1`. Rewrite using `[mul_inv_cancel]`. Conclude with `Matrix.transpose_one`.

Establish `hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u` using `fun u => by`. Rewrite using `[Matrix.mul_assoc, hkk, Matrix.mul_one]`. Establish `gauss : ∀ f₀, M.IsGauss B.ψ B.emb f₀ → M.IsGauss B.ψ B.emb (A f₀)`. Introduce `f₀ hf₀`. Take `⟨ε, hε⟩` from `hf₀`.

Use `⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩` and prove the remaining obligations. Establish `hv` using `GlobalTheory.KInfPol.at_mul_right hu (mat k⁻¹)ᵀ`. Establish `hv'` using `GlobalTheory.KInfPol.at_mul_right hu' (mat k⁻¹)ᵀ`. Establish `h1` using `hint _ hv f₀`. Establish `h2` using `hint _ hv' f₀`.

Rewrite `h1`, `h2` using `[hcan]`. Establish `e1` using `(hL _ _ _).2.2.1 _ hg h1`. Establish `e2` using `(hL _ _ _).2.2.1 _ hg' h2`. Establish `key` using `hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)`. Rewrite using `[e1, e2, key, map_smul]`.

Establish `hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1`. Rewrite using `[← Matrix.map_mul]`. Express the relevant statement in the definitionally equal form `(mat (k⁻¹ * k)).map _ = 1`. Rewrite using `[inv_mul_cancel]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.

Establish `hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1` using `mul_eq_one_comm.1 hm`. Establish `hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]`. Use `congr 1`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]`. Proceed by induction on `m with`. Consider the case `zero`. Rewrite using `[fockDeg_zero]`.

Conclude with `Submodule.span_le.2 fun f₀ hf₀ => Submodule.subset_span (gauss f₀ hf₀)`. Consider the case `succ m ih`. Establish `hmono : fockDeg M B.ψ B.emb m ≤ fockDeg M B.ψ B.emb (m + 1)` using `fockDeg_mono M B.ψ B.emb (Nat.le_succ m)`. Rewrite using `[fockDeg_succ]`. Use `sup_le (ih.trans (Submodule.comap_mono (le_sup_left))) (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `f₁ ⟨u, hu, f, hf, hd⟩`. Establish `e : f₁ = D u f` using `(hL _ _ _).2.2.1 _ hd (hAD u hu f)`. Substitute `e` using the available equality. Use `Submodule.mem_comap.2 ?_` and prove the remaining obligations. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨u * (mat k)ᵀ, GlobalTheory.KInfPol.at_mul_right hu _, A f, ih hf, hint u hu f⟩)`.
-/
theorem fockDeg_le_comap_of_kInf (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {χ₁ χ₂ : Chr F E}
    (hB : B.IsGood σ) (hw : M.IsWeil B.ψ χ₁ χ₂ om) {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb)
    (A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))
    (hA : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f (A f)) (m : ℕ) :
    fockDeg M B.ψ B.emb m ≤ (fockDeg M B.ψ B.emb m).comap A := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std
  have hL := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, GlobalTheory.RealLift.SD (M.heisLine B.ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (GlobalTheory.KInfPol.heisLine_zero M B.ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (GlobalTheory.KInfPol.heisLine_zero M B.ψ _)
      (GlobalTheory.KInfPol.sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  have gauss : ∀ f₀, M.IsGauss B.ψ B.emb f₀ → M.IsGauss B.ψ B.emb (A f₀) := by
    intro f₀ hf₀
    obtain ⟨ε, hε⟩ := hf₀
    refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
    have hv := GlobalTheory.KInfPol.at_mul_right hu (mat k⁻¹)ᵀ
    have hv' := GlobalTheory.KInfPol.at_mul_right hu' (mat k⁻¹)ᵀ
    have h1 := hint _ hv f₀
    have h2 := hint _ hv' f₀
    rw [hcan] at h1 h2
    have e1 := (hL _ _ _).2.2.1 _ hg h1
    have e2 := (hL _ _ _).2.2.1 _ hg' h2
    have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
    · rw [e1, e2, key, map_smul]
    · have hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
        rw [← Matrix.map_mul]
        change (mat (k⁻¹ * k)).map _ = 1
        rw [inv_mul_cancel]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      have hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := mul_eq_one_comm.1 hm
      have hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
        calc _ = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w *
              ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by rw [hm', Matrix.mul_one]
          _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) *
              (mat k⁻¹).map (piInf (B.emb w)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
      rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]
  induction m with
  | zero =>
    rw [fockDeg_zero]
    exact Submodule.span_le.2 fun f₀ hf₀ => Submodule.subset_span (gauss f₀ hf₀)
  | succ m ih =>
    have hmono : fockDeg M B.ψ B.emb m ≤ fockDeg M B.ψ B.emb (m + 1) := fockDeg_mono M B.ψ B.emb (Nat.le_succ m)
    rw [fockDeg_succ]
    refine sup_le (ih.trans (Submodule.comap_mono (le_sup_left))) (Submodule.span_le.2 ?_)
    rintro f₁ ⟨u, hu, f, hf, hd⟩
    have e : f₁ = D u f := (hL _ _ _).2.2.1 _ hd (hAD u hu f)
    subst e
    refine Submodule.mem_comap.2 ?_
    exact Submodule.mem_sup_right (Submodule.subset_span
      ⟨u * (mat k)ᵀ, GlobalTheory.KInfPol.at_mul_right hu _, A f, ih hf, hint u hu f⟩)

/- English proof (translation)
Set `L : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ)` to `{ toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hLi : Function.Injective L` using `fun f g h => DFunLike.coe_injective h`. Use `haveI : FiniteDimensional ℂ (N.map L) := inferInstance`. Establish `hcl : IsClosed ((N.map L : Submodule ℂ _) : Set ((κ → mixedEmbedding.mixedSpace F) → ℂ))` using `Submodule.closed_of_finiteDimensional _`. Establish `ht : Tendsto (fun t : ℝ => L (((t⁻¹ : ℝ) : ℂ) • (c t - c 0))) (𝓝[≠] 0) (𝓝 (L g))`.

Use `tendsto_pi_nhds.2 fun x => ?_` and prove the remaining obligations. Establish `h` using `(hg x).tendsto_slope_zero`. Simplify using `only [zero_add] at h`. Use `h.congr fun t => ?_` and prove the remaining obligations. Use `show (t⁻¹ : ℝ) • (c t x - c 0 x) = (((t⁻¹ : ℝ) : ℂ) • (c t - c 0)) x`.

Simplify using `[Complex.real_smul]`. Establish `hmem` using `hcl.mem_of_tendsto ht (Eventually.of_forall fun t => Submodule.mem_map_of_mem (N.smul_mem _ (N.sub_mem (hc t) (hc 0))))`. Take `⟨h, hh, e⟩` from `hmem`. Rewrite `hh` using `[hLi e]`. Conclude with `hh`.
-/
theorem mem_of_hasDerivAt_of_finiteDimensional {κ : Type} [Fintype κ] (N : Submodule ℂ (SInf F κ))
    [FiniteDimensional ℂ N] (c : ℝ → SInf F κ) (hc : ∀ t, c t ∈ N) (g : SInf F κ)
    (hg : ∀ x, HasDerivAt (fun t => c t x) (g x) 0) : g ∈ N := by
  let L : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hLi : Function.Injective L := fun f g h => DFunLike.coe_injective h
  haveI : FiniteDimensional ℂ (N.map L) := inferInstance
  have hcl : IsClosed ((N.map L : Submodule ℂ _) : Set ((κ → mixedEmbedding.mixedSpace F) → ℂ)) :=
    Submodule.closed_of_finiteDimensional _
  have ht : Tendsto (fun t : ℝ => L (((t⁻¹ : ℝ) : ℂ) • (c t - c 0))) (𝓝[≠] 0) (𝓝 (L g)) := by
    refine tendsto_pi_nhds.2 fun x => ?_
    have h := (hg x).tendsto_slope_zero
    simp only [zero_add] at h
    refine h.congr fun t => ?_
    show (t⁻¹ : ℝ) • (c t x - c 0 x) = (((t⁻¹ : ℝ) : ℂ) • (c t - c 0)) x
    simp [Complex.real_smul]
  have hmem := hcl.mem_of_tendsto ht (Eventually.of_forall fun t =>
    Submodule.mem_map_of_mem (N.smul_mem _ (N.sub_mem (hc t) (hc 0))))
  obtain ⟨h, hh, e⟩ := hmem
  rw [hLi e] at hh
  exact hh

end GlobalTheory.IndLine

namespace GlobalTheory.IndLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def derMap {κ : Type} [Fintype κ] (φ : SInf F κ) :
    ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) → ℂ) where
  toFun p x := fderiv ℝ φ x p.1 - 2 * Real.pi * Complex.I *
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * p.2 i) : ℝ) : ℂ) * φ x
  map_add' p q := by
    funext x
    simp only [Prod.fst_add, Prod.snd_add, map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.ofReal_add]
    ring
  map_smul' c p := by
    funext x
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul,
      Complex.real_smul, mul_smul_comm, ← Finset.smul_sum, Complex.ofReal_mul]
    ring

/- English proof (translation)
Take `⟨D, hD⟩` from `GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ G.M.co h.base.std`. Establish `hL` using `GlobalTheory.RealLift.actsLaws F (Fin a × Fin (a + a'))`. Establish `hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (G.M.heisLine B.ψ u) φ (D u φ)` using `fun u hu φ => (hL φ _ φ).1 _ (GlobalTheory.KInfPol.heisLine_zero G.M B.ψ u) (hD u hu φ).1`. Proceed by induction on `m with`. Consider the case `zero`.

Rewrite using `[fockDeg_zero]`. Distinguish the cases in `h0 : ∃ f₀, f₀ ≠ 0 ∧ G.M.IsGauss B.ψ B.emb f₀`. Take `⟨f₀, hne, hg⟩` from `h0`. Establish `hle : Submodule.span ℂ {f₀ | G.M.IsGauss B.ψ B.emb f₀} ≤ Submodule.span ℂ {f₀}` using `Submodule.span_le.2 fun g hg' => by`. Take `⟨c, rfl⟩` from `GlobalTheory.T.fockVacua_triple_proportional_to_nonzero B G X om om' h f₀ hne hg g hg'`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span rfl)`. Conclude with `Submodule.finiteDimensional_of_le hle`. Use `push_neg at h0`. Establish `: Submodule.span ℂ {f₀ | G.M.IsGauss B.ψ B.emb f₀} = ⊥`. Rewrite using `[Submodule.span_eq_bot]`.

Introduce `g hg`. Assume the negation of the conclusion as `hne`. Conclude with `h0 g hne hg`. Rewrite using `[this]`. Use `infer_instance`.

Consider the case `succ m ih`. Rewrite using `[fockDeg_succ]`. Use `set N := fockDeg G.M B.ψ B.emb m`. Set `bN` to `Module.finBasis ℂ N`. Set `bR` to `Module.finBasis ℝ (((Fin a × Fin (a + a')) → mixedEmbedding.mixedSpace F) × ((Fin a × Fin (a + a')) → mixedEmbedding.mixedSpace F))`.

Set `L : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) → ℂ)` to `{ toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hLi : Function.Injective L` using `fun f g h => DFunLike.coe_injective h`. Set `T : Set ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) → ℂ)` to `Set.range fun p : Fin (Module.finrank ℂ N) × Fin (Module.finrank ℝ _) => derMap (bN p.1 : SInf F _) (bR p.2)`. Establish `hT : T.Finite` using `Set.finite_range _`. Establish `hone : ∀ (φ : SInf F (Fin a × Fin (a + a'))) (i : Fin (Module.finrank ℂ N)), φ = bN i → ∀ u, At (evI F) u → L (D u φ) ∈ Submodule.span ℂ T`.

Introduce `φ i hφ u hu`. Establish `e : L (D u φ) = derMap φ (fun j => evI F ((G.M.co.e u).1 j), fun j => evI F ((G.M.co.e u).2 j))`. Use function extensionality and compare the values at `x`. Conclude with `(hD u hu φ).2 x`. Rewrite using `[e, ← bR.sum_repr (_, _), map_sum]`.

Use `Submodule.sum_mem _ fun r _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Use `Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(i, r), ?_⟩)` and prove the remaining obligations. Rewrite using `[hφ]`. Establish `hS : Submodule.span ℂ {f₁ : SInf F (Fin a × Fin (a + a')) | ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (G.M.heisLine B.ψ u) f f₁} ≤ (Submodule.span ℂ T).comap L`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `f₁ ⟨u, hu, f, hf, hd⟩`. Establish `e1 : f₁ = D u f` using `(hL _ _ _).2.2.1 _ hd (hAD u hu f)`. Establish `e2 : f = ∑ i, bN.repr ⟨f, hf⟩ i • (bN i : SInf F _)`. Use `congrArg Subtype.val (bN.sum_repr ⟨f, hf⟩)` as an intermediate fact.

Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at this`. Conclude with `this.symm`. Substitute `e1` using the available equality. Use `Submodule.mem_comap.2 ?_` and prove the remaining obligations.

Rewrite using `[e2, map_sum, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul]`. Conclude with `Submodule.smul_mem _ _ (hone _ i rfl u hu)`. Use `haveI : FiniteDimensional ℂ (Submodule.span ℂ T) := FiniteDimensional.span_of_finite ℂ hT`.

Establish `h1 : FiniteDimensional ℂ ((Submodule.span ℂ {f₁ : SInf F (Fin a × Fin (a + a')) | ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (G.M.heisLine B.ψ u) f f₁}).map L)` using `Submodule.finiteDimensional_of_le (Submodule.map_le_iff_le_comap.2 hS)`. Use `haveI := (Submodule.equivMapOfInjective L hLi (Submodule.span ℂ {f₁ : SInf F (Fin a × Fin (a + a')) | ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (G.M.heisLine B.ψ u) f f₁})).symm.finiteDimensional`. Use `infer_instance`.
-/
theorem fockDeg_finiteDimensional {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (h : IsTriple B G X om om') (m : ℕ) :
    FiniteDimensional ℂ (fockDeg G.M B.ψ B.emb m) := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ G.M.co h.base.std
  have hL := GlobalTheory.RealLift.actsLaws F (Fin a × Fin (a + a'))
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin a × Fin (a + a')),
      ActsD (evI F) (G.M.heisLine B.ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (GlobalTheory.KInfPol.heisLine_zero G.M B.ψ u) (hD u hu φ).1
  induction m with
  | zero =>
    rw [fockDeg_zero]
    by_cases h0 : ∃ f₀, f₀ ≠ 0 ∧ G.M.IsGauss B.ψ B.emb f₀
    · obtain ⟨f₀, hne, hg⟩ := h0
      have hle : Submodule.span ℂ {f₀ | G.M.IsGauss B.ψ B.emb f₀} ≤ Submodule.span ℂ {f₀} :=
        Submodule.span_le.2 fun g hg' => by
          obtain ⟨c, rfl⟩ := GlobalTheory.T.fockVacua_triple_proportional_to_nonzero B G X om om' h f₀ hne hg g hg'
          exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      exact Submodule.finiteDimensional_of_le hle
    · push_neg at h0
      have : Submodule.span ℂ {f₀ | G.M.IsGauss B.ψ B.emb f₀} = ⊥ := by
        rw [Submodule.span_eq_bot]
        intro g hg
        by_contra hne
        exact h0 g hne hg
      rw [this]
      infer_instance
  | succ m ih =>
    rw [fockDeg_succ]
    set N := fockDeg G.M B.ψ B.emb m
    let bN := Module.finBasis ℂ N
    let bR := Module.finBasis ℝ (((Fin a × Fin (a + a')) → mixedEmbedding.mixedSpace F) ×
      ((Fin a × Fin (a + a')) → mixedEmbedding.mixedSpace F))
    let L : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) → ℂ) :=
      { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hLi : Function.Injective L := fun f g h => DFunLike.coe_injective h
    let T : Set ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) → ℂ) :=
      Set.range fun p : Fin (Module.finrank ℂ N) × Fin (Module.finrank ℝ _) => derMap (bN p.1 : SInf F _) (bR p.2)
    have hT : T.Finite := Set.finite_range _
    have hone : ∀ (φ : SInf F (Fin a × Fin (a + a'))) (i : Fin (Module.finrank ℂ N)), φ = bN i → ∀ u, At (evI F) u →
        L (D u φ) ∈ Submodule.span ℂ T := by
      intro φ i hφ u hu
      have e : L (D u φ) = derMap φ (fun j => evI F ((G.M.co.e u).1 j), fun j => evI F ((G.M.co.e u).2 j)) := by
        funext x
        exact (hD u hu φ).2 x
      rw [e, ← bR.sum_repr (_, _), map_sum]
      refine Submodule.sum_mem _ fun r _ => ?_
      rw [map_smul]
      refine Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(i, r), ?_⟩)
      rw [hφ]
    have hS : Submodule.span ℂ {f₁ : SInf F (Fin a × Fin (a + a')) | ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (G.M.heisLine B.ψ u) f f₁} ≤
        (Submodule.span ℂ T).comap L := by
      refine Submodule.span_le.2 ?_
      rintro f₁ ⟨u, hu, f, hf, hd⟩
      have e1 : f₁ = D u f := (hL _ _ _).2.2.1 _ hd (hAD u hu f)
      have e2 : f = ∑ i, bN.repr ⟨f, hf⟩ i • (bN i : SInf F _) := by
        have := congrArg Subtype.val (bN.sum_repr ⟨f, hf⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      subst e1
      refine Submodule.mem_comap.2 ?_
      rw [e2, map_sum, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ _ (hone _ i rfl u hu)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ T) := FiniteDimensional.span_of_finite ℂ hT
    have h1 : FiniteDimensional ℂ ((Submodule.span ℂ {f₁ : SInf F (Fin a × Fin (a + a')) | ∃ u, At (evI F) u ∧ ∃ f ∈ N,
        ActsD (evI F) (G.M.heisLine B.ψ u) f f₁}).map L) :=
      Submodule.finiteDimensional_of_le (Submodule.map_le_iff_le_comap.2 hS)
    haveI := (Submodule.equivMapOfInjective L hLi (Submodule.span ℂ {f₁ : SInf F (Fin a × Fin (a + a')) |
      ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (G.M.heisLine B.ψ u) f f₁})).symm.finiteDimensional
    infer_instance

end GlobalTheory.IndLine

namespace GlobalTheory.IndLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use `choose Aop hAop using fun t : ℝ => GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a (a + a') G.V G.W G.M om X.β (X.β / X.α) h.base h.geo.hM h.weil (γ (Multiplicative.ofAdd t)) (hK _)`. Use `haveI := fockDeg_finiteDimensional B G X om om' h m`. Use `mem_of_hasDerivAt_of_finiteDimensional _ (fun t => Aop t g) (fun t => fockDeg_le_comap_of_kInf B G.M om h.base h.weil (hK _) (Aop t) (hAop t) m hg) g₁ ?_` and prove the remaining obligations. Introduce `y`. Use `set g₀ : (Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.RealLift.intPts F (Fin a × Fin (a + a'))).indicator 1 with hg₀def`.

Establish `hg₀ : g₀ ∈ SB _` using `GlobalTheory.RealLift.indicator_intPts_mem_SB`. Establish `hg₀0 : g₀ 0 = 1` using `by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl`. Use `set r₀ : (Fin a × Fin (a + a') → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def`. Establish `hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x`. Introduce `x z hz`.

Express the relevant statement in the definitionally equal form `g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)`. Use `congr 1`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(x i).2 + (z i).2 = (x i).2`. Rewrite using `[GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]`.

Establish `hrest : Rest (evI F) (⇑g) r₀` using `⟨hr₀inv, Submodule.subset_span ⟨g, g₀, hg₀, rfl⟩⟩`. Establish `e : ∀ φ : SInf F (Fin a × Fin (a + a')), tens (evI F) φ r₀ (GlobalTheory.RealLift.ptAt y 0) = φ y` using `fun φ => by show pureA F φ g₀ (GlobalTheory.RealLift.ptAt y 0) = φ y`. Rewrite using `[GlobalTheory.RealLift.pureA_ptAt, hg₀0, mul_one]`. Establish `h1` using `hd r₀ hrest (GlobalTheory.RealLift.ptAt y 0)`. Rewrite `h1` using `[e]`.

Use `h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Use `show Aop t g y = om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) g r₀) (GlobalTheory.RealLift.ptAt y 0)`. Rewrite using `[hAop t g r₀ hrest, e]`.
-/
theorem fockDeg_line_stab {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (h : IsTriple B G X om om') (γ : Multiplicative ℝ →* UA σ G.W.J)
    (hK : ∀ s, γ s ∈ KInf σ G.W B.emb) (m : ℕ) {g : SInf F (Fin a × Fin (a + a'))}
    (hg : g ∈ fockDeg G.M B.ψ B.emb m) (g₁ : SInf F (Fin a × Fin (a + a')))
    (hd : ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) g g₁) : g₁ ∈ fockDeg G.M B.ψ B.emb m := by
  choose Aop hAop using fun t : ℝ => GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a (a + a') G.V G.W G.M om X.β (X.β / X.α) h.base h.geo.hM
    h.weil (γ (Multiplicative.ofAdd t)) (hK _)
  haveI := fockDeg_finiteDimensional B G X om om' h m
  refine mem_of_hasDerivAt_of_finiteDimensional _ (fun t => Aop t g)
    (fun t => fockDeg_le_comap_of_kInf B G.M om h.base h.weil (hK _) (Aop t) (hAop t) m hg) g₁ ?_
  intro y
  set g₀ : (Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (GlobalTheory.RealLift.intPts F (Fin a × Fin (a + a'))).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB _ := GlobalTheory.RealLift.indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl
  set r₀ : (Fin a × Fin (a + a') → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
  have hrest : Rest (evI F) (⇑g) r₀ := ⟨hr₀inv, Submodule.subset_span ⟨g, g₀, hg₀, rfl⟩⟩
  have e : ∀ φ : SInf F (Fin a × Fin (a + a')), tens (evI F) φ r₀ (GlobalTheory.RealLift.ptAt y 0) = φ y := fun φ => by
    show pureA F φ g₀ (GlobalTheory.RealLift.ptAt y 0) = φ y
    rw [GlobalTheory.RealLift.pureA_ptAt, hg₀0, mul_one]
  have h1 := hd r₀ hrest (GlobalTheory.RealLift.ptAt y 0)
  rw [e] at h1
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  show Aop t g y = om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) g r₀) (GlobalTheory.RealLift.ptAt y 0)
  rw [hAop t g r₀ hrest, e]

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM`. Establish `hT` using `hM.triple`. Establish `hKr` using `GlobalTheory.T.matched_pair_theta_identity hKP F E σ B a a' G X om om' R Rf hM`. Take `⟨-, -, hstW, -⟩` from `GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hT`. Establish `hle` using `fockDeg_le_pol G.M B.ψ B.emb (lowDegInf B G.M R.p)`.

Establish `hL` using `GlobalTheory.RealLift.actsLaws F (Fin a × Fin (a + a'))`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `k hk f hf f₁ hd ⟨g, hg, hpg⟩`. Take `⟨A, hA⟩` from `GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a (a + a') G.V G.W G.M om X.β (X.β / X.α) hT.base hT.geo.hM hT.weil k hk`. Establish `hg₁ : A g ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p)` using `fockDeg_le_comap_of_kInf B G.M om hT.base hT.weil hk A hA _ hg`.

Distinguish the cases in `hfg : f - g = 0`. Take `rfl : f = g` from `(sub_eq_zero.mp hfg)`. Rewrite using `[(hL _ _ _).2.2.2.1 _ hd (hA f)]`. Conclude with `Submodule.mem_map_of_mem hg₁`. Establish `hk' : f - g ∈ G.M.Pol B.ψ B.emb ⊓ LinearMap.ker R.p` using `Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hf (hle hg), LinearMap.mem_ker.2 (by rw [map_sub, hpg, sub_self])⟩`.

Establish `h0 : R.p (f₁ - A g) = 0` using `(hKr.2.2.2.2 k hk _ hk' _ (GlobalTheory.ThetaKerMaxInf.acts_sub (om (1, k)) hfg hd (hA g))).2`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Rewrite using `[h0]`. Conclude with `Submodule.mem_map_of_mem hg₁`. Introduce and unpack `γ hγ hK f hf f₁ hd ⟨g, hg, hpg⟩`.

Take `⟨g₁, -, hgd, huniq⟩` from `hstW γ hγ g (hle hg)`. Establish `hg₁ : g₁ ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p)` using `fockDeg_line_stab B G X om om' hT γ hK _ hg g₁ hgd`. Distinguish the cases in `hfg : f - g = 0`. Take `rfl : f = g` from `(sub_eq_zero.mp hfg)`. Rewrite using `[huniq f₁ hd]`.

Conclude with `Submodule.mem_map_of_mem hg₁`. Establish `hk' : f - g ∈ G.M.Pol B.ψ B.emb ⊓ LinearMap.ker R.p` using `Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hf (hle hg), LinearMap.mem_ker.2 (by rw [map_sub, hpg, sub_self])⟩`. Establish `h0 : R.p (f₁ - g₁) = 0` using `(hKr.2.2.2.1 γ hγ _ hk' _ (GlobalTheory.ThetaKerMaxInf.actsD_sub (fun t => om (1, γ (Multiplicative.ofAdd t))) hfg hd hgd)).2`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Rewrite using `[h0]`.

Conclude with `Submodule.mem_map_of_mem hg₁`.
-/
theorem lowPartInf_kStab : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      KStab B G.M om R.p (lowPartInf B G.M R.p) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  have hT := hM.triple
  have hKr := GlobalTheory.T.matched_pair_theta_identity hKP F E σ B a a' G X om om' R Rf hM
  obtain ⟨-, -, hstW, -⟩ := GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hT
  have hle := fockDeg_le_pol G.M B.ψ B.emb (lowDegInf B G.M R.p)
  have hL := GlobalTheory.RealLift.actsLaws F (Fin a × Fin (a + a'))
  constructor
  · rintro k hk f hf f₁ hd ⟨g, hg, hpg⟩
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B a (a + a') G.V G.W G.M om X.β (X.β / X.α) hT.base hT.geo.hM hT.weil k hk
    have hg₁ : A g ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p) :=
      fockDeg_le_comap_of_kInf B G.M om hT.base hT.weil hk A hA _ hg
    by_cases hfg : f - g = 0
    · obtain rfl : f = g := (sub_eq_zero.mp hfg)
      rw [(hL _ _ _).2.2.2.1 _ hd (hA f)]
      exact Submodule.mem_map_of_mem hg₁
    · have hk' : f - g ∈ G.M.Pol B.ψ B.emb ⊓ LinearMap.ker R.p :=
        Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hf (hle hg), LinearMap.mem_ker.2 (by rw [map_sub, hpg, sub_self])⟩
      have h0 : R.p (f₁ - A g) = 0 := (hKr.2.2.2.2 k hk _ hk' _ (GlobalTheory.ThetaKerMaxInf.acts_sub (om (1, k)) hfg hd (hA g))).2
      rw [map_sub, sub_eq_zero] at h0
      rw [h0]
      exact Submodule.mem_map_of_mem hg₁
  · rintro γ hγ hK f hf f₁ hd ⟨g, hg, hpg⟩
    obtain ⟨g₁, -, hgd, huniq⟩ := hstW γ hγ g (hle hg)
    have hg₁ : g₁ ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p) :=
      fockDeg_line_stab B G X om om' hT γ hK _ hg g₁ hgd
    by_cases hfg : f - g = 0
    · obtain rfl : f = g := (sub_eq_zero.mp hfg)
      rw [huniq f₁ hd]
      exact Submodule.mem_map_of_mem hg₁
    · have hk' : f - g ∈ G.M.Pol B.ψ B.emb ⊓ LinearMap.ker R.p :=
        Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hf (hle hg), LinearMap.mem_ker.2 (by rw [map_sub, hpg, sub_self])⟩
      have h0 : R.p (f₁ - g₁) = 0 := (hKr.2.2.2.1 γ hγ _ hk' _
        (GlobalTheory.ThetaKerMaxInf.actsD_sub (fun t => om (1, γ (Multiplicative.ofAdd t))) hfg hd hgd)).2
      rw [map_sub, sub_eq_zero] at h0
      rw [h0]
      exact Submodule.mem_map_of_mem hg₁

end GlobalTheory.IndLine

/- English proof (translation)
The claim follows from `GlobalTheory.IndLine.lowPartInf_kStab`.
-/
example : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      KStab B G.M om R.p (lowPartInf B G.M R.p) := GlobalTheory.IndLine.lowPartInf_kStab

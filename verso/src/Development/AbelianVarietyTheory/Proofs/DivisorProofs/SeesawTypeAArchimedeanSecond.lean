import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationTriplePeriodCaseAFourth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

open scoped Classical

noncomputable section

namespace GlobalTheory.ConeArchDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `hl : l = ∑ i, GlobalTheory.XTermMaj.crd F E l i ⊗ₜ[F] Module.finBasis F E i` using `by conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun l]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Both sides reduce to the same expression. Establish `h1 : ∀ (a : AF F) (x : E), piInf τ (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x` using `fun a x => rfl`.

Use `conv_lhs => rw [hl]`. Rewrite using `[map_sum]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[h1, norm_mul, (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]`.
-/
theorem norm_piInf_le {w : InfinitePlace F} (τ : EmbOver E w) (l : AE F E) :
    ‖piInf τ l‖ ≤ ∑ i, ‖(GlobalTheory.XTermMaj.crd F E l i).1 w‖ * ‖τ.1 (Module.finBasis F E i)‖ := by
  have hl : l = ∑ i, GlobalTheory.XTermMaj.crd F E l i ⊗ₜ[F] Module.finBasis F E i := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun l]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  have h1 : ∀ (a : AF F) (x : E), piInf τ (a ⊗ₜ[F] x) =
      InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x := fun a x => rfl
  conv_lhs => rw [hl]
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [h1, norm_mul, (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]

/- English proof (translation)
Use `set M : ℝ := ∑ w : InfinitePlace F, ∑ i, ‖(B.emb w).1 (Module.finBasis F E i)‖ with hM`. Establish `hM0 : 0 ≤ M` using `by positivity`. Use `⟨M, hM0, fun l => ?_⟩` and prove the remaining obligations. Use `set R := ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E l i).1 v‖ with hR`. Establish `hR0 : 0 ≤ R` using `by positivity`.

Establish `h1 : ∑ w, ‖piInf (B.emb w) l‖ ≤ M * R`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `_ = M * R := by`. Rewrite using `[hR, Finset.mul_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun v _ => mul_comm _ _`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_one_add_le (B : Base F E) : ∃ M : ℝ, 0 ≤ M ∧ ∀ l : AE F E,
    1 + ∑ w, ‖piInf (B.emb w) l‖ ≤ (1 + M) * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E l i).1 v‖) := by
  set M : ℝ := ∑ w : InfinitePlace F, ∑ i, ‖(B.emb w).1 (Module.finBasis F E i)‖ with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M, hM0, fun l => ?_⟩
  set R := ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E l i).1 v‖ with hR
  have hR0 : 0 ≤ R := by positivity
  have h1 : ∑ w, ‖piInf (B.emb w) l‖ ≤ M * R := by
    calc ∑ w, ‖piInf (B.emb w) l‖
        ≤ ∑ w, ∑ i, ‖(GlobalTheory.XTermMaj.crd F E l i).1 w‖ * ‖(B.emb w).1 (Module.finBasis F E i)‖ :=
          Finset.sum_le_sum fun w _ => norm_piInf_le (B.emb w) l
      _ ≤ ∑ w, ∑ i, ‖(GlobalTheory.XTermMaj.crd F E l i).1 w‖ * M := by
          refine Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          calc ‖(B.emb w).1 (Module.finBasis F E i)‖ ≤ ∑ i', ‖(B.emb w).1 (Module.finBasis F E i')‖ :=
                Finset.single_le_sum (f := fun i' => ‖(B.emb w).1 (Module.finBasis F E i')‖) (fun _ _ => norm_nonneg _)
                  (Finset.mem_univ i)
            _ ≤ M := Finset.single_le_sum (f := fun w' : InfinitePlace F => ∑ i', ‖(B.emb w').1 (Module.finBasis F E i')‖)
                  (fun _ _ => by positivity) (Finset.mem_univ w)
      _ = M * R := by
          rw [hR, Finset.mul_sum, Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  nlinarith

section Arch

open GlobalTheory.XTermDecay GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay

/- English proof (translation)
Establish `hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om` using `hT.weil`. Take `⟨m, g, f, hg, hdec, hf⟩` from `exists_decomp (fun k : C => om (k.1, 1) Ψ) (fun k => hw.isUSplitting.pres (k.1, 1) Ψ hΨ) fun l hl => by`. Establish `hc` using `(hw.2.2 l hl Ψ hΨ).comp (continuous_id.prodMk continuous_const : Continuous fun g : UA σ G.V.J => (g, (1 : UA σ G.W.J)))`. Take `⟨D, hD⟩` from `hCc.exists_bound_of_continuousOn hc.continuousOn`. Conclude with `⟨D, fun k => hD k.1 k.2⟩`.

Take `⟨t, ht⟩` from `GlobalTheory.T.symplectic_trace_basis_exists F E σ _ _ G.V.J G.W.J H.x H.y H'.x H'.y hC.hH.xy (by`. Rewrite using `[form_swap hT.base.cm hT.geo.hW.skew, hC.hH'.xy, map_one])`. Set `S` to `fun j => G.M.co.e (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))`. Set `U'` to `fun i => G.M.co.e (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x))`. Establish `hp : Continuous ⇑(SchwartzMap.seminorm ℂ 0 0 : Seminorm ℂ (SInf F (Fin b × Fin (b + a'))))` using `(schwartz_withSeminorms ℂ (Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F) ℂ).continuous_seminorm (0, 0)`.

Use `choose D₀ hCb using fun j => slice_decay B.ψ hT.base.std S U' (fun i j => by rw [← G.M.co.form]; convert ht i j) (sliceL c ∘ₗ e) (exists_slice_clm hT.geo.hM he c) (fun i a Ψ hΨ => by`. Use `he.inv (Matrix.vecMulVec (a • inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x)) (Or.inl ⟨_, rfl⟩) Ψ hΨ` as an intermediate fact. Rewrite `this` using `[Matrix.smul_vecMulVec, Darboux.rho, map_smul]`. Conclude with `congrArg (sliceL c) this) (hg j) (f j) (hf j)`. Use the proof step `(isCompact_singleton (x := (0 : Fin (Module.finrank F E) → Af F))) _ hp N`.

Use `⟨∑ j, D₀ j, fun k hk l => ?_⟩` and prove the remaining obligations. Use `set x : Fin (Module.finrank F E) → AF F := fun i => realAd F 1 * GlobalTheory.XTermMaj.crd F E (l : AE F E) i with hx`. Establish `hx2 : (fun i => (x i).2) ∈ ({0} : Set (Fin (Module.finrank F E) → Af F))`. Use function extensionality and compare the values at `i`. Use `show (realAd F 1).2 * (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2 = 0`.

Rewrite using `[show (realAd F 1).2 = 0 from rfl, zero_mul]`. Establish `hx1 : ∀ i (v : InfinitePlace F), (x i).1 v = (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v` using `fun i v => by show (realAd F 1).1 v * (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v = _`. Rewrite using `[show (realAd F 1).1 = 1 by show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1) = 1`. Rewrite using `[map_one, map_one]]`. Conclude with `one_mul _`.

Use `choose f₁ hf₁ hb₁ using fun j => hCb j ⟨k, hk⟩ x hx2`. Establish `hS0 : G.M.co.e (shiftA H H' l) = ∑ i, GlobalTheory.XTermMaj.crd F E (l : AE F E) i • S i`. Simplify using `only [S, ← map_smul, ← map_sum, ← smul_assoc, ← Finset.sum_smul]`. Use `congr 2`. Rewrite using `[shiftA]`.

Use `congr 1`. Use `((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (l : AE F E)).symm.trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_apply]`. Both sides reduce to the same expression.

Establish `hS : G.M.co.e (partInf F (shiftA H H' l)) = ∑ i, x i • S i`. Rewrite using `[partInf, map_smul, hS0, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => smul_smul _ _ _`. Establish `hR : ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ = ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖` using `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => by rw [hx1]`. Use `⟨∑ j, f₁ j, fun y => ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `hdec ⟨k, hk⟩`. Simplify using `only at h1`. Rewrite using `[h1, Darboux.rho, hS]`. Express the relevant statement in the definitionally equal form `coeL (∑ j, f₁ j) y = (sliceL c ∘ₗ e) (schrL B.ψ _ _) y`. Rewrite using `[map_sum, map_sum, map_sum]`.

Conclude with `congrFun (Finset.sum_congr rfl fun j _ => hf₁ j) y`. Rewrite using `[Finset.sum_mul]`. Use `(Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations. Use `hb₁ j` as an intermediate fact. Rewrite `this` using `[hR]`. Then use the resulting hypothesis.
-/
theorem arch_slice_decay {B : Base F E} {b a' : ℕ} {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'}
    {H : Plane E (b + 2) b} {H' : Plane E (b + 2 + a') (b + a')} (hC : CfgA B G G₁ H H')
    {e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')} (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om')
    {Ψ : Fn F (b + 2) (b + 2 + a')} (hΨ : Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')))
    {C : Set (UA σ G.V.J)} (hCc : IsCompact C) (c : Fin b × Fin (b + a') → Af F) (N : ℕ) :
    ∃ D : ℝ, ∀ k ∈ C, ∀ l : (AE F E)ˣ,
      ∃ f : SInf F (Fin b × Fin (b + a')), (∀ y, f y = e (G.M.co.rho B.ψ (partInf F (shiftA H H' l)) (om (k, 1) Ψ))
          (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), c q))) ∧
        SchwartzMap.seminorm ℂ 0 0 f ≤
          D * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) := by
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hT.weil
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp (fun k : C => om (k.1, 1) Ψ)
    (fun k => hw.isUSplitting.pres (k.1, 1) Ψ hΨ) fun l hl => by
      have hc := (hw.2.2 l hl Ψ hΨ).comp
        (continuous_id.prodMk continuous_const : Continuous fun g : UA σ G.V.J => (g, (1 : UA σ G.W.J)))
      obtain ⟨D, hD⟩ := hCc.exists_bound_of_continuousOn hc.continuousOn
      exact ⟨D, fun k => hD k.1 k.2⟩
  obtain ⟨t, ht⟩ := GlobalTheory.T.symplectic_trace_basis_exists F E σ _ _ G.V.J G.W.J H.x H.y H'.x H'.y hC.hH.xy (by
    rw [form_swap hT.base.cm hT.geo.hW.skew, hC.hH'.xy, map_one])
  let S := fun j => G.M.co.e (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  let U' := fun i => G.M.co.e (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x))
  have hp : Continuous ⇑(SchwartzMap.seminorm ℂ 0 0 : Seminorm ℂ (SInf F (Fin b × Fin (b + a')))) :=
    (schwartz_withSeminorms ℂ (Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F) ℂ).continuous_seminorm (0, 0)
  choose D₀ hCb using fun j => slice_decay B.ψ hT.base.std S U' (fun i j => by rw [← G.M.co.form]; convert ht i j)
    (sliceL c ∘ₗ e) (exists_slice_clm hT.geo.hM he c) (fun i a Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (a • inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x)) (Or.inl ⟨_, rfl⟩) Ψ hΨ
      rw [Matrix.smul_vecMulVec, Darboux.rho, map_smul] at this
      exact congrArg (sliceL c) this) (hg j) (f j) (hf j)
      (isCompact_singleton (x := (0 : Fin (Module.finrank F E) → Af F))) _ hp N
  refine ⟨∑ j, D₀ j, fun k hk l => ?_⟩
  set x : Fin (Module.finrank F E) → AF F := fun i => realAd F 1 * GlobalTheory.XTermMaj.crd F E (l : AE F E) i with hx
  have hx2 : (fun i => (x i).2) ∈ ({0} : Set (Fin (Module.finrank F E) → Af F)) := by
    funext i
    show (realAd F 1).2 * (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2 = 0
    rw [show (realAd F 1).2 = 0 from rfl, zero_mul]
  have hx1 : ∀ i (v : InfinitePlace F), (x i).1 v = (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v := fun i v => by
    show (realAd F 1).1 v * (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v = _
    rw [show (realAd F 1).1 = 1 by
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1) = 1
      rw [map_one, map_one]]
    exact one_mul _
  choose f₁ hf₁ hb₁ using fun j => hCb j ⟨k, hk⟩ x hx2
  have hS0 : G.M.co.e (shiftA H H' l) = ∑ i, GlobalTheory.XTermMaj.crd F E (l : AE F E) i • S i := by
    simp only [S, ← map_smul, ← map_sum, ← smul_assoc, ← Finset.sum_smul]
    congr 2
    rw [shiftA]
    congr 1
    refine ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (l : AE F E)).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  have hS : G.M.co.e (partInf F (shiftA H H' l)) = ∑ i, x i • S i := by
    rw [partInf, map_smul, hS0, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  have hR : ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ =
      ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖ :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => by rw [hx1]
  refine ⟨∑ j, f₁ j, fun y => ?_, ?_⟩
  · have h1 := hdec ⟨k, hk⟩
    simp only at h1
    rw [h1, Darboux.rho, hS]
    change coeL (∑ j, f₁ j) y = (sliceL c ∘ₗ e) (schrL B.ψ _ _) y
    rw [map_sum, map_sum, map_sum]
    exact congrFun (Finset.sum_congr rfl fun j _ => hf₁ j) y
  · rw [Finset.sum_mul]
    refine (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)
    have := hb₁ j
    rwa [hR] at this

end Arch

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hP B b a' G G₁ H H' hC e he ei ev hloc K hK X om om' hT hG₁ f y N`. Take `⟨-, hev, hpure⟩` from `hloc`. Establish `hKc : IsCompact (K : Set (UA σ G.V.J))`. Take `⟨K', _, _, hK', hc, -, -⟩` from `GlobalTheory.StabHaar.stabEx hP F E σ B _ G.V _ _ hT.base hT.geo.hV`. Establish `hKK : K = K'`.

Use extensionality with `g`. Rewrite using `[hK g, hK' g]`. Substitute `hKK` using the available equality. Conclude with `hc`. Establish `hM` using `hT.geo.hM`.

Establish `hSB : ∀ v, G.M.vac v ∈ SB _` using `fun v => (hM.vac v).1`. Establish `hΦ : pure f G.M.vac ∈ schA F _` using `GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std`. Establish `hrest : ∀ h : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Rest (evI F) (⇑h) (GlobalTheory.EvZeroInf.finPart G.M.vac)` using `fun h => ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, GlobalTheory.TensUniq.pure_mem_schA h _ hSB hM.std⟩`. Take `⟨x₀, hx₀⟩` from `GlobalTheory.EvZeroInf.exists_finPart_ne_zero G₁.M.vac (fun v => (hG₁.vac v).2.1) hG₁.std`. Take `⟨D, hD⟩` from `arch_slice_decay hC he hT hΦ (isCompact_KAt hKc (evI F)) x₀ N`.

Use `set c : ℂ := GlobalTheory.EvZeroInf.finPart G₁.M.vac (fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), x₀ i)) with hc`. Establish `hc0 : c ≠ 0` using `hx₀ _ fun i => rfl`. Establish `key : ∀ k ∈ KAt K (evI F), ∀ l : (AE F E)ˣ, e (G.M.co.rho B.ψ (partInf F (shiftA H H' l)) (om (k, 1) (pure f G.M.vac))) (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), x₀ q)) = ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) (locOpInf (om (k, 1)) f)) y …`. Introduce `k hk l`. Establish `hA1` using `acts_locOpInf (GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ G.V G.W G.M B.ψ X.β (X.β / X.α) om hT.base.cm hT.base.std hT.weil k (mem_KAt.1 hk).2 f) _ (hrest f)`.

Establish `hA2` using `(locOpInf_rho G.M.co hT.base.std (shiftA H H' l) (locOpInf (om (k, 1)) f)).1 _ (hrest _)`. Establish `h3` using `hpure (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) (locOpInf (om (k, 1)) f)) G.M.vac hSB (Eventually.of_forall fun _ => rfl)`. Establish `h4 : (fun v => ev v (G.M.vac v)) = G₁.M.vac` using `funext fun v => (hev v).1`. Rewrite `h3` using `[h4]`. Rewrite using `[GlobalTheory.EvZeroInf.pure_eq_tens, hA1, hA2, ← GlobalTheory.EvZeroInf.pure_eq_tens, h3, GlobalTheory.EvZeroInf.pure_eq_tens]`.

Use `show ei _ (fun i => evI F _) * GlobalTheory.EvZeroInf.finPart G₁.M.vac _ = _`. Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `(InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _`. Take `⟨Mb, hMb0, hMb⟩` from `exists_one_add_le (F := F) (E := E) B`.

Use `⟨‖c‖⁻¹ * |D| * (1 + Mb) ^ N, fun k hk l _ => ?_⟩` and prove the remaining obligations. Take `⟨g₁, hg₁, hgb⟩` from `hD k hk l`. Use `set Q := ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) (locOpInf (om (k, 1)) f)) y with hQ`. Use `set R := ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖ with hR`. Use `set A := 1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖ with hA`.

Establish `hR0 : 0 ≤ R` using `by positivity`. Establish `hA1 : 1 ≤ A` using `le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)`. Establish `hcpos : 0 < ‖c‖` using `norm_pos_iff.2 hc0`. Establish `hQc : g₁ y = Q * c` using `(hg₁ y).trans (key k hk l)`. Establish `h1 : ‖Q‖ * ‖c‖ ≤ |D| * (1 + R) ^ (-(N : ℝ))`.

Rewrite using `[← norm_mul, ← hQc]`. Use `(SchwartzMap.norm_le_seminorm ℂ g₁ y).trans (hgb.trans ?_)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)`. Establish `h2 : (1 + R) ^ (-(N : ℝ)) * A ^ N ≤ (1 + Mb) ^ N`. Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_natCast, inv_mul_le_iff₀ (by positivity), ← mul_pow]`.

Conclude with `pow_le_pow_left₀ (by linarith) (by rw [mul_comm]; exact hMb _) N`. Establish `hApos : 0 < A ^ N` using `by positivity`. Rewrite using `[le_div_iff₀ hApos]`. Establish `h3 : ‖Q‖ ≤ ‖c‖⁻¹ * (|D| * (1 + R) ^ (-(N : ℝ)))`. Rewrite using `[le_inv_mul_iff₀ hcpos, mul_comm]`.

Conclude with `h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decay_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ → ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')), IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
    (ei ≠ 0 ∧ (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (y : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F),
      ∀ N : ℕ, ∃ C : ℝ, ∀ k ∈ KAt K (evI F), ∀ l ∈ idelesAt E (evI F),
        ‖ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) (locOpInf (om (k, 1)) f)) y‖ ≤
          C / (1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖) ^ N := by
  intro F E _ _ _ _ _ σ hP B b a' G G₁ H H' hC e he ei ev hloc K hK X om om' hT hG₁ f y N
  obtain ⟨-, hev, hpure⟩ := hloc
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    obtain ⟨K', _, _, hK', hc, -, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B _ G.V _ _ hT.base hT.geo.hV
    have hKK : K = K' := by
      ext g
      rw [hK g, hK' g]
    subst hKK
    exact hc
  have hM := hT.geo.hM
  have hSB : ∀ v, G.M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hΦ : pure f G.M.vac ∈ schA F _ := GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std
  have hrest : ∀ h : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Rest (evI F) (⇑h) (GlobalTheory.EvZeroInf.finPart G.M.vac) :=
    fun h => ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, GlobalTheory.TensUniq.pure_mem_schA h _ hSB hM.std⟩
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.EvZeroInf.exists_finPart_ne_zero G₁.M.vac (fun v => (hG₁.vac v).2.1) hG₁.std
  obtain ⟨D, hD⟩ := arch_slice_decay hC he hT hΦ (isCompact_KAt hKc (evI F)) x₀ N
  set c : ℂ := GlobalTheory.EvZeroInf.finPart G₁.M.vac (fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), x₀ i)) with hc
  have hc0 : c ≠ 0 := hx₀ _ fun i => rfl
  have key : ∀ k ∈ KAt K (evI F), ∀ l : (AE F E)ˣ,
      e (G.M.co.rho B.ψ (partInf F (shiftA H H' l)) (om (k, 1) (pure f G.M.vac)))
          (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), x₀ q)) =
        ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) (locOpInf (om (k, 1)) f)) y * c := by
    intro k hk l
    have hA1 := acts_locOpInf (GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ G.V G.W G.M B.ψ X.β (X.β / X.α) om
      hT.base.cm hT.base.std hT.weil k (mem_KAt.1 hk).2 f) _ (hrest f)
    have hA2 := (locOpInf_rho G.M.co hT.base.std (shiftA H H' l) (locOpInf (om (k, 1)) f)).1 _ (hrest _)
    have h3 := hpure (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) (locOpInf (om (k, 1)) f)) G.M.vac hSB
      (Eventually.of_forall fun _ => rfl)
    have h4 : (fun v => ev v (G.M.vac v)) = G₁.M.vac := funext fun v => (hev v).1
    rw [h4] at h3
    rw [GlobalTheory.EvZeroInf.pure_eq_tens, hA1, hA2, ← GlobalTheory.EvZeroInf.pure_eq_tens, h3, GlobalTheory.EvZeroInf.pure_eq_tens]
    show ei _ (fun i => evI F _) * GlobalTheory.EvZeroInf.finPart G₁.M.vac _ = _
    congr 2
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  obtain ⟨Mb, hMb0, hMb⟩ := exists_one_add_le (F := F) (E := E) B
  refine ⟨‖c‖⁻¹ * |D| * (1 + Mb) ^ N, fun k hk l _ => ?_⟩
  obtain ⟨g₁, hg₁, hgb⟩ := hD k hk l
  set Q := ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) (locOpInf (om (k, 1)) f)) y with hQ
  set R := ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖ with hR
  set A := 1 + ∑ w, ‖piInf (B.emb w) (l : AE F E)‖ with hA
  have hR0 : 0 ≤ R := by positivity
  have hA1 : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hQc : g₁ y = Q * c := (hg₁ y).trans (key k hk l)
  have h1 : ‖Q‖ * ‖c‖ ≤ |D| * (1 + R) ^ (-(N : ℝ)) := by
    rw [← norm_mul, ← hQc]
    refine (SchwartzMap.norm_le_seminorm ℂ g₁ y).trans (hgb.trans ?_)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have h2 : (1 + R) ^ (-(N : ℝ)) * A ^ N ≤ (1 + Mb) ^ N := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_mul_le_iff₀ (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by rw [mul_comm]; exact hMb _) N
  have hApos : 0 < A ^ N := by positivity
  rw [le_div_iff₀ hApos]
  have h3 : ‖Q‖ ≤ ‖c‖⁻¹ * (|D| * (1 + R) ^ (-(N : ℝ))) := by
    rw [le_inv_mul_iff₀ hcpos, mul_comm]
    exact h1
  calc ‖Q‖ * A ^ N ≤ ‖c‖⁻¹ * (|D| * (1 + R) ^ (-(N : ℝ))) * A ^ N :=
        mul_le_mul_of_nonneg_right h3 hApos.le
    _ = ‖c‖⁻¹ * |D| * ((1 + R) ^ (-(N : ℝ)) * A ^ N) := by ring
    _ ≤ ‖c‖⁻¹ * |D| * (1 + Mb) ^ N := mul_le_mul_of_nonneg_left h2 (by positivity)

end GlobalTheory.ConeArchDecay

import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.InfTypeLocal

/- English proof (translation)
Establish `hg : Topology.IsOpenEmbedding (Pi.map (fun (w : InfinitePlace L) => (Units.val : (w.Completion)ˣ → w.Completion)))` using `Topology.IsOpenEmbedding.piMap (fun w => Units.isOpenEmbedding_val)`. Rewrite using `[DenseRange, dense_iff_inter_open]`. Introduce and unpack `U hU ⟨u, hu⟩`. Take `⟨k, v, hv, hk⟩` from `(InfiniteAdeleRing.denseRange_algebraMap L).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩`. Establish `hk0 : k ≠ 0`.

Introduce and unpack `rfl`. Take `⟨w⟩ : Nonempty (InfinitePlace L)` from `inferInstance`. Establish `h1` using `congrFun hk w`. Rewrite `h1` using `[map_zero]`. Conclude with `(v w).ne_zero h1`.

Use `⟨v, hv, Units.mk0 k hk0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Conclude with `Units.ext (congrFun hk w).symm`.
-/
theorem denseRange_atInf (L : Type) [Field L] [NumberField L] :
    DenseRange (fun (k : Lˣ) (w : InfinitePlace L) => atInf w k) := by
  have hg : Topology.IsOpenEmbedding
      (Pi.map (fun (w : InfinitePlace L) => (Units.val : (w.Completion)ˣ → w.Completion))) :=
    Topology.IsOpenEmbedding.piMap (fun w => Units.isOpenEmbedding_val)
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (InfiniteAdeleRing.denseRange_algebraMap L).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
    have h1 := congrFun hk w
    rw [map_zero] at h1
    exact (v w).ne_zero h1
  refine ⟨v, hv, Units.mk0 k hk0, ?_⟩
  funext w
  exact Units.ext (congrFun hk w).symm

/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Conclude with `Continuous.prodMk (continuous_mulSingle w) continuous_const`.
-/
theorem continuous_infIdele (L : Type) [Field L] [NumberField L] (w : InfinitePlace L) :
    Continuous (infIdele L w) := by
  classical
  refine Continuous.units_map _ ?_
  exact Continuous.prodMk (continuous_mulSingle w) continuous_const

/- English proof (translation)
Establish `h0 : ∀ k : L, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ) (algebraMap L _ k) = (InfinitePlace.mk φ).embedding k` using `fun k => InfinitePlace.Completion.extensionEmbedding_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ k)`. Establish `hc` using `(InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk φ)).continuous`. Break down `InfinitePlace.embedding_mk_eq φ with h | h` into its components or cases. Conclude with `⟨_, hc, fun k => by rw [h0, h]⟩`. Use `⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _), Complex.continuous_conj.comp hc, fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply, h0, h]`. Simplify using the standard rewrite rules.
-/
theorem exists_ext {L : Type} [Field L] (φ : L →+* ℂ) :
    ∃ e : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous e ∧
      ∀ k : L, e (algebraMap L _ k) = φ k := by
  have h0 : ∀ k : L, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ) (algebraMap L _ k) =
      (InfinitePlace.mk φ).embedding k := fun k =>
    InfinitePlace.Completion.extensionEmbedding_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ k)
  have hc := (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk φ)).continuous
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨_, hc, fun k => by rw [h0, h]⟩
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp hc, fun k => ?_⟩
    rw [RingHom.comp_apply, h0, h]
    simp

open Classical in

/- English proof (translation)
Introduce `L _ _ I _ φ hφ ψ hψ n`. Establish `hd : ∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ)`. Introduce `k`. Unfold `infDiag`. Rewrite using `[MonoidHom.finsetProd_apply, map_prod, Units.coe_prod]`.

Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `h choose e hec he using fun i => exists_ext (φ i)`. Establish `key : (fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => ∏ w, ((ψ (infIdele L w (u w)) : ℂˣ) : ℂ)) = fun u => ∏ i, (e i (u (InfinitePlace.mk (φ i))) / ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ)) ^ n i`. Use `(denseRange_atInf L).equalizer ?_ ?_ ?_` and prove the remaining obligations.

Use `continuous_finsetProd _ fun w _ => ?_` and prove the remaining obligations. Conclude with `Units.continuous_val.comp (hψ.comp ((continuous_infIdele L w).comp (continuous_apply w)))`. Use `continuous_finsetProd _ fun i _ => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => e i (u (InfinitePlace.mk (φ i)))` using `(hec i).comp (Units.continuous_val.comp (continuous_apply _))`. Establish `h2 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, e i (u (InfinitePlace.mk (φ i))) ≠ 0` using `fun u => (map_ne_zero _).2 (Units.ne_zero (u (InfinitePlace.mk (φ i))))`.

Establish `h3 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ) ≠ 0` using `fun u => by`. Conclude with `norm_ne_zero_iff.2 (h2 u)` after adjusting the coercions. Conclude with `(h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _ fun u => Or.inl (div_ne_zero (h2 u) (h3 u))`. Use function extensionality and compare the values at `k show ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ) = ∏ i, (e i (algebraMap L _ (k : L)) / ((‖e i (algebraMap L _ (k : L))‖ : ℝ) : ℂ)) ^ n i`. Rewrite using `[← hd, h]`.

Simplify using `only [he]`. Introduce `i k`. Establish `h1` using `congrFun key (Pi.mulSingle (InfinitePlace.mk (φ i)) (atInf _ k))`. Use `beta_reduce at h1`. Rewrite `h1` using `[Finset.prod_eq_single (InfinitePlace.mk (φ i)), Finset.prod_eq_single i]`.

Rewrite `h1` using `[Pi.mulSingle_eq_same]`. Rewrite using `[h1, ← he i k]`. Both sides reduce to the same expression. Introduce `j _ hj`. Rewrite using `[Pi.mulSingle_eq_of_ne (fun hh => hj (hφ.1 hh))]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce `w _ hw`. Rewrite using `[Pi.mulSingle_eq_of_ne hw]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Introduce `h k`. Rewrite using `[hd, ← hφ.prod_comp]`. Conclude with `Finset.prod_congr rfl fun i _ => h i k`.
-/
theorem infType_iff_local : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ n : I → ℤ, ((∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ↔ ∀ i (k : Lˣ), ((ψ (infIdele L (InfinitePlace.mk (φ i)) (atInf _ k)) : ℂˣ) : ℂ) = (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) := by
  intro L _ _ I _ φ hφ ψ hψ n
  have hd : ∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ) := by
    intro k
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, map_prod, Units.coe_prod]
    rfl
  constructor
  · intro h
    choose e hec he using fun i => exists_ext (φ i)
    have key : (fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => ∏ w, ((ψ (infIdele L w (u w)) : ℂˣ) : ℂ)) =
        fun u => ∏ i, (e i (u (InfinitePlace.mk (φ i))) / ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ)) ^ n i := by
      refine (denseRange_atInf L).equalizer ?_ ?_ ?_
      · refine continuous_finsetProd _ fun w _ => ?_
        exact Units.continuous_val.comp (hψ.comp ((continuous_infIdele L w).comp (continuous_apply w)))
      · refine continuous_finsetProd _ fun i _ => ?_
        have h1 : Continuous fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => e i (u (InfinitePlace.mk (φ i))) :=
          (hec i).comp (Units.continuous_val.comp (continuous_apply _))
        have h2 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, e i (u (InfinitePlace.mk (φ i))) ≠ 0 := fun u =>
          (map_ne_zero _).2 (Units.ne_zero (u (InfinitePlace.mk (φ i))))
        have h3 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ) ≠ 0 := fun u => by
          exact_mod_cast norm_ne_zero_iff.2 (h2 u)
        exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _ fun u => Or.inl (div_ne_zero (h2 u) (h3 u))
      · funext k
        show ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ) =
          ∏ i, (e i (algebraMap L _ (k : L)) / ((‖e i (algebraMap L _ (k : L))‖ : ℝ) : ℂ)) ^ n i
        rw [← hd, h]
        simp only [he]
    intro i k
    have h1 := congrFun key (Pi.mulSingle (InfinitePlace.mk (φ i)) (atInf _ k))
    beta_reduce at h1
    rw [Finset.prod_eq_single (InfinitePlace.mk (φ i)), Finset.prod_eq_single i] at h1
    · rw [Pi.mulSingle_eq_same] at h1
      rw [h1, ← he i k]
      rfl
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne (fun hh => hj (hφ.1 hh))]
      simp
    · simp
    · intro w _ hw
      rw [Pi.mulSingle_eq_of_ne hw]
      simp
    · simp
  · intro h k
    rw [hd, ← hφ.prod_comp]
    exact Finset.prod_congr rfl fun i _ => h i k

end GlobalTheory.InfTypeLocal

import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdUnifMulUnitIdl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.Determ

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _)`. Rewrite using `[Filter.le_principal_iff]`. Conclude with `(Set.finite_singleton v).compl_mem_cofinite`. Set `f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _))` to `fun x => ⟨Pi.mulSingle v x, by`. Rewrite using `[Filter.eventually_principal]`.

Introduce `w hw`. Establish `h' : w ≠ v` using `hw`. Rewrite using `[Pi.mulSingle_eq_of_ne h']`. Conclude with `one_mem _⟩`. Establish `hf : Continuous f`.

Rewrite using `[RestrictedProduct.continuous_rng_of_principal]`. Conclude with `continuous_mulSingle (A := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v`. Use `(RestrictedProduct.continuous_inclusion hle).comp hf` as an intermediate fact. Conclude with `this`.
-/
theorem continuous_finSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (finiteSingle L v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.mulSingle v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Pi.mulSingle_eq_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_mulSingle (A := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
  have := (RestrictedProduct.continuous_inclusion hle).comp hf
  exact this

/- English proof (translation)
Apply `Continuous.units_map` to reduce the goal to its premises. Conclude with `Continuous.prodMk continuous_const (continuous_finSingle v)`.
-/
theorem continuous_localIdele (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finSingle v)

/- English proof (translation)
Establish `hg : Topology.IsOpenEmbedding (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L)`. Use `⟨Units.isEmbedding_val₀, ?_⟩` and prove the remaining obligations. Establish `: Set.range (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L) = {0}ᶜ`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, rfl⟩`. Conclude with `u.ne_zero`. Introduce `hz`. Conclude with `⟨Units.mk0 z hz, rfl⟩`. Rewrite using `[this]`.

Conclude with `isOpen_compl_singleton`. Rewrite using `[DenseRange, dense_iff_inter_open]`. Introduce and unpack `U hU ⟨u, hu⟩`. Take `⟨k, x, hx, hk⟩` from `(HeightOneSpectrum.denseRange_algebraMap L v).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩`. Establish `hk0 : k ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hk` using `[map_zero]`. Conclude with `x.ne_zero hk`. Conclude with `⟨x, hx, Units.mk0 k hk0, Units.ext hk.symm⟩`.
-/
theorem denseRange_atFin (v : HeightOneSpectrum (𝓞 L)) : DenseRange (atFin v) := by
  have hg : Topology.IsOpenEmbedding (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L) := by
    refine ⟨Units.isEmbedding_val₀, ?_⟩
    have : Set.range (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L) = {0}ᶜ := by
      ext z
      constructor
      · rintro ⟨u, rfl⟩
        exact u.ne_zero
      · intro hz
        exact ⟨Units.mk0 z hz, rfl⟩
    rw [this]
    exact isOpen_compl_singleton
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, x, hx, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap L v).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact x.ne_zero hk
  exact ⟨x, hx, Units.mk0 k hk0, Units.ext hk.symm⟩

/- English proof (translation)
Set `p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion` to `fun w => { toFun := fun x => x.1 w, map_one' := rfl, map_mul' := fun _ _ => rfl }`. Use `⟨fun w => Units.map (p w) a, ?_⟩` and prove the remaining obligations. Establish `h : ((∏ w, infIdele L w (Units.map (p w) a) : Ideles L) : AdeleRing (𝓞 L) L) = ((a : AdeleRing (𝓞 L) L).1, 1)`. Rewrite using `[Units.coe_prod]`. Set `ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L` to `MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)`.

Express the relevant statement in the definitionally equal form `∏ w : InfinitePlace L, ι (Pi.mulSingle w ((a : AdeleRing (𝓞 L) L).1 w)) = ι (fun w => (a : AdeleRing (𝓞 L) L).1 w)`. Rewrite using `[← map_prod]`. Conclude with `congrArg ι (Finset.univ_prod_mulSingle (fun w : InfinitePlace L => ((a : AdeleRing (𝓞 L) L).1 w : w.Completion)))`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, h]`.

Conclude with `Prod.ext (mul_one _) (one_mul _)`.
-/
theorem exists_prod_inf_mul_finPart (a : Ideles L) :
    ∃ y : ∀ w : InfinitePlace L, (w.Completion)ˣ, (∏ w, infIdele L w (y w)) * finPartI L a = a := by
  classical
  let p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion := fun w =>
    { toFun := fun x => x.1 w, map_one' := rfl, map_mul' := fun _ _ => rfl }
  refine ⟨fun w => Units.map (p w) a, ?_⟩
  have h : ((∏ w, infIdele L w (Units.map (p w) a) : Ideles L) : AdeleRing (𝓞 L) L) = ((a : AdeleRing (𝓞 L) L).1, 1) := by
    rw [Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w ((a : AdeleRing (𝓞 L) L).1 w)) = ι (fun w => (a : AdeleRing (𝓞 L) L).1 w)
    rw [← map_prod]
    exact congrArg ι (Finset.univ_prod_mulSingle (fun w : InfinitePlace L => ((a : AdeleRing (𝓞 L) L).1 w : w.Completion)))
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

/- English proof (translation)
The claim follows from `congrFun ((denseRange_atFin v).equalizer (g := fun x => ψ (localIdele L v x)) (h := fun _ => 1) (hψ.comp (continuous_localIdele v)) continuous_const (funext h)) x`.
-/
theorem loc_eq_one {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 L))
    (h : ∀ k, ψ (localIdele L v (atFin v k)) = 1) (x : (v.adicCompletion L)ˣ) : ψ (localIdele L v x) = 1 :=
  congrFun ((denseRange_atFin v).equalizer (g := fun x => ψ (localIdele L v x)) (h := fun _ => 1)
    (hψ.comp (continuous_localIdele v)) continuous_const (funext h)) x

/- English proof (translation)
Use `congrFun ((GlobalTheory.InfTypeLocal.denseRange_atInf L).equalizer (g := fun y : ∀ w : InfinitePlace L, (w.Completion)ˣ => ψ (∏ w, infIdele L w (y w))) (h := fun _ => 1) (hψ.comp (continuous_finsetProd _ fun w _ => (GlobalTheory.InfTypeLocal.continuous_infIdele L w).comp (continu …` and prove the remaining obligations. Establish `h1` using `h k`. Unfold `infDiag at h1`. Rewrite `h1` using `[MonoidHom.finsetProd_apply]`. Conclude with `h1`.
-/
theorem inf_eq_one {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ) (h : ∀ k, ψ (infDiag k) = 1)
    (y : ∀ w : InfinitePlace L, (w.Completion)ˣ) : ψ (∏ w, infIdele L w (y w)) = 1 := by
  refine congrFun ((GlobalTheory.InfTypeLocal.denseRange_atInf L).equalizer
    (g := fun y : ∀ w : InfinitePlace L, (w.Completion)ˣ => ψ (∏ w, infIdele L w (y w))) (h := fun _ => 1)
    (hψ.comp (continuous_finsetProd _ fun w _ =>
      (GlobalTheory.InfTypeLocal.continuous_infIdele L w).comp (continuous_apply w))) continuous_const (funext fun k => ?_)) y
  have h1 := h k
  unfold infDiag at h1
  rw [MonoidHom.finsetProd_apply] at h1
  exact h1

/- English proof (translation)
Take `⟨S, n, u, hu, rfl, -⟩` from `exists_prod_unif_mul_unitIdl L a`. Take `⟨y, hy⟩` from `exists_prod_inf_mul_finPart u`. Establish `h1 : ψ (finPartI L u) = 1` using `GlobalTheory.Mem.LocTriv.eq_one_of_local L ψ hψ _ (finPartI_mem_unitIdl.2 hu) (fun _ => rfl) fun v x _ => loc_eq_one hψ v (hf v) x`. Rewrite using `[← hy, map_mul, map_mul, h1, inf_eq_one hψ hi, map_prod, mul_one, mul_one]`. Conclude with `Finset.prod_eq_one fun v _ => by rw [map_zpow, hf, one_zpow]`.
-/
theorem eq_one_of_components {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ)
    (hf : ∀ v k, ψ (localIdele L v (atFin v k)) = 1) (hi : ∀ k, ψ (infDiag k) = 1) (a : Ideles L) : ψ a = 1 := by
  obtain ⟨S, n, u, hu, rfl, -⟩ := exists_prod_unif_mul_unitIdl L a
  obtain ⟨y, hy⟩ := exists_prod_inf_mul_finPart u
  have h1 : ψ (finPartI L u) = 1 :=
    GlobalTheory.Mem.LocTriv.eq_one_of_local L ψ hψ _ (finPartI_mem_unitIdl.2 hu) (fun _ => rfl) fun v x _ => loc_eq_one hψ v (hf v) x
  rw [← hy, map_mul, map_mul, h1, inf_eq_one hψ hi, map_prod, mul_one, mul_one]
  exact Finset.prod_eq_one fun v _ => by rw [map_zpow, hf, one_zpow]

end GlobalTheory.Mem.Chr.Determ

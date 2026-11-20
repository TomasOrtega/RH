import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CocycleTransportH1fSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {E : Type} [Field E] [Algebra ℚ_[l] E]
  {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]

private noncomputable def spanT (l : ℕ) [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E]
    {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]
    (W : Submodule E V) : Submodule E (V ⊗[ℚ_[l]] Bdr l) :=
  Submodule.span E {y | ∃ v ∈ W, ∃ b ∈ ((PP l).PD (botExt l)).Fil 0, y = v ⊗ₜ[ℚ_[l]] b}

/- English proof (translation)
Introduce and unpack `_ ⟨z, rfl⟩`. Proceed by induction on `z with`. Consider the case `zero => simp`. Consider the case `tmul v b => exact Submodule.subset_span ⟨v, trivial, b.1, b.2, by simp⟩`. Consider the case `add x y hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`.
-/
private theorem filT_le_spanT : FilT (l := l) E V 0 ≤ spanT l (⊤ : Submodule E V) := by
  rintro _ ⟨z, rfl⟩
  induction z with
  | zero => simp
  | tmul v b => exact Submodule.subset_span ⟨v, trivial, b.1, b.2, by simp⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, -, b, hb, rfl⟩`. Conclude with `⟨v ⊗ₜ ⟨b, hb⟩, by simp⟩`.
-/
private theorem spanT_le_filT (W : Submodule E V) : spanT l W ≤ FilT (l := l) E V 0 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, -, b, hb, rfl⟩
  exact ⟨v ⊗ₜ ⟨b, hb⟩, by simp⟩

/- English proof (translation)
Use `Submodule.span_eq_bot.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, b, -, rfl⟩`. Rewrite `hv` using `[Submodule.mem_bot]`. Simplify using `[hv]`.
-/
private theorem spanT_bot : spanT l (⊥ : Submodule E V) = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨v, hv, b, -, rfl⟩
  rw [Submodule.mem_bot] at hv
  simp [hv]

/- English proof (translation)
Establish `: spanT l W ≤ (spanT l W').comap (AlgebraTensorModule.map f (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, b, hb, rfl⟩`. Conclude with `Submodule.subset_span ⟨f v, hf v hv, b, hb, by simp⟩`. Conclude with `this hy`.
-/
private theorem map_spanT {V' : Type} [AddCommGroup V'] [Module E V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] E V'] (f : V →ₗ[E] V') (W : Submodule E V) (W' : Submodule E V')
    (hf : ∀ v ∈ W, f v ∈ W') (y : V ⊗[ℚ_[l]] Bdr l) (hy : y ∈ spanT l W) :
    AlgebraTensorModule.map f (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) y ∈ spanT l W' := by
  have : spanT l W ≤ (spanT l W').comap
      (AlgebraTensorModule.map f (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, b, hb, rfl⟩
    exact Submodule.subset_span ⟨f v, hf v hv, b, hb, by simp⟩
  exact this hy

/- English proof (translation)
Use `set L := AlgebraTensorModule.map lam (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) with hL`. Establish `hcomm : ∀ g, ∀ z ∈ spanT l W', L (actD φ ρ g z) = actD φ (chRep κ) g (L z)`. Introduce `g z hz`. Establish `: spanT l W' ≤ LinearMap.eqLocus (L ∘ₗ actD φ ρ g) (actD φ (chRep κ) g ∘ₗ L)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨v, hv, b, hb, rfl⟩`. Simplify using `[LinearMap.mem_eqLocus, hL, actD, chRep, heq g v hv]`. Conclude with `this hz`. Establish `h0 : L y = 0`. Establish `: L y ∈ FilD φ (chRep κ) 0`.

Use `⟨?_, spanT_le_filT ⊤ (map_spanT lam W' ⊤ (fun _ _ => trivial) y hy)⟩` and prove the remaining obligations. Simplify using `only [Ddr, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hD ⊢`. Introduce `g`. Rewrite using `[← hcomm g y hy, hD g]`. Rewrite `this` using `[hκ, Submodule.mem_bot]`. Then use the resulting hypothesis.

Establish `h1` using `map_spanT (LinearMap.id - LinearMap.toSpanSingleton E V x ∘ₗ lam) W' W (fun v hv => by simpa using hp v hv) y hy`. Establish `h2 : ∀ z : V ⊗[ℚ_[l]] Bdr l, AlgebraTensorModule.map (LinearMap.id - LinearMap.toSpanSingleton E V x ∘ₗ lam) (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) z = z - AlgebraTensorModule.map (LinearMap.toSpanSingleton E V x) (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) (L z)`. Introduce `z`. Proceed by induction on `z with`. Consider the case `zero => simp`.

Consider the case `tmul v b => simp [hL, sub_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Normalize the expressions using the abelian group laws. Rewrite `h1` using `[h2, h0, map_zero, sub_zero]`. Then use the resulting hypothesis.
-/
private theorem step (φ : G →* GQ l) (ρ : Representation E G V) (κ : G →* Eˣ)
    (hκ : FilD φ (chRep κ) 0 = ⊥) (W W' : Submodule E V) (x : V) (lam : V →ₗ[E] E)
    (hp : ∀ v ∈ W', v - lam v • x ∈ W)
    (heq : ∀ g, ∀ v ∈ W', lam (ρ g v) = (κ g : E) * lam v)
    (y : V ⊗[ℚ_[l]] Bdr l) (hy : y ∈ spanT l W') (hD : y ∈ Ddr φ ρ) : y ∈ spanT l W := by
  set L := AlgebraTensorModule.map lam (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) with hL
  have hcomm : ∀ g, ∀ z ∈ spanT l W', L (actD φ ρ g z) = actD φ (chRep κ) g (L z) := by
    intro g z hz
    have : spanT l W' ≤ LinearMap.eqLocus (L ∘ₗ actD φ ρ g) (actD φ (chRep κ) g ∘ₗ L) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, b, hb, rfl⟩
      simp [LinearMap.mem_eqLocus, hL, actD, chRep, heq g v hv]
    exact this hz
  have h0 : L y = 0 := by
    have : L y ∈ FilD φ (chRep κ) 0 := by
      refine ⟨?_, spanT_le_filT ⊤ (map_spanT lam W' ⊤ (fun _ _ => trivial) y hy)⟩
      simp only [Ddr, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hD ⊢
      intro g
      rw [← hcomm g y hy, hD g]
    rwa [hκ, Submodule.mem_bot] at this
  have h1 := map_spanT (LinearMap.id - LinearMap.toSpanSingleton E V x ∘ₗ lam) W' W
    (fun v hv => by simpa using hp v hv) y hy
  have h2 : ∀ z : V ⊗[ℚ_[l]] Bdr l,
      AlgebraTensorModule.map (LinearMap.id - LinearMap.toSpanSingleton E V x ∘ₗ lam)
        (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) z =
      z - AlgebraTensorModule.map (LinearMap.toSpanSingleton E V x)
        (LinearMap.id : Bdr l →ₗ[ℚ_[l]] Bdr l) (L z) := by
    intro z
    induction z with
    | zero => simp
    | tmul v b => simp [hL, sub_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]; abel
  rwa [h2, h0, map_zero, sub_zero] at h1

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Rewrite `hv` using `[mem_riemannRochSpace_iff_regularAt_everywhere]`. Use `haveI : Nontrivial (Bdr l) := nontrivial_of_ne 1 0 fun h1 => ((PP l).PD (botExt l)).not_mem_filtration_two (by`. Establish `: (((PP l).PD (botExt l)).ι ((PP l).PD (botExt l)).t : Bdr l) = 0`.

Rewrite using `[← mul_one (((PP l).PD (botExt l)).ι _), h1, mul_zero]`. Rewrite using `[this]`. Conclude with `zero_mem _)`. Establish `hm : v ⊗ₜ[ℚ_[l]] (1 : Bdr l) ∈ FilD φ ρ 0`. Use `⟨?_, v ⊗ₜ ⟨1, ((PP l).PD (botExt l)).one_mem⟩, by simp⟩` and prove the remaining obligations.

Simplify using `only [Ddr, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Introduce `g`. Simplify using `[actD, hv g]`. Rewrite `hm` using `[h, Submodule.mem_bot]`. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_eq_one ℚ_[l] (one_ne_zero : (1 : Bdr l) ≠ 0)`.

Use `congrArg (fun z => TensorProduct.rid ℚ_[l] V (TensorProduct.map LinearMap.id f z)) hm` as an intermediate fact. Simplify `this` using `[hf]`.
-/
private theorem H0_eq_bot_of_filD_zero_eq_bot (φ : G →* GQ l) (ρ : Representation E G V) [TopologicalSpace G]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V]
    (h : FilD φ ρ 0 = ⊥) : H0 ρ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [mem_riemannRochSpace_iff_regularAt_everywhere] at hv
  haveI : Nontrivial (Bdr l) := nontrivial_of_ne 1 0 fun h1 =>
    ((PP l).PD (botExt l)).not_mem_filtration_two (by
      have : (((PP l).PD (botExt l)).ι ((PP l).PD (botExt l)).t : Bdr l) = 0 := by
        rw [← mul_one (((PP l).PD (botExt l)).ι _), h1, mul_zero]
      rw [this]; exact zero_mem _)
  have hm : v ⊗ₜ[ℚ_[l]] (1 : Bdr l) ∈ FilD φ ρ 0 := by
    refine ⟨?_, v ⊗ₜ ⟨1, ((PP l).PD (botExt l)).one_mem⟩, by simp⟩
    simp only [Ddr, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    simp [actD, hv g]
  rw [h, Submodule.mem_bot] at hm
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ_[l] (one_ne_zero : (1 : Bdr l) ≠ 0)
  have := congrArg (fun z => TensorProduct.rid ℚ_[l] V (TensorProduct.map LinearMap.id f z)) hm
  simpa [hf] using this

end SlopeTestRemainingChoices

end UpperTheory.V.Loc

/- English proof (translation)
Introduce `hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ hpos`. Take `⟨hdr, n, F, hF0, hFn, hF⟩` from `hpos`. Use `letI : TopologicalSpace E := moduleTopology ℚ_[l] E`. Use `haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩`. Use `haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E`.

Establish `key : ∀ i ≤ n, (∀ g, ∀ v ∈ F i, ρ g v ∈ F i) ∧ ∀ y ∈ spanT l (F i), y ∈ Ddr φ ρ → y = 0`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_`.

Rewrite using `[hF0, spanT_bot]`. Use `⟨fun g v hv => ?_, fun y hy _ => hy⟩` and prove the remaining obligations. Rewrite `hv`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hv, map_zero]`. Consider the case `succ i ih`.

Introduce `hi`. Take `⟨hst, hz⟩` from `ih (by omega)`. Take `⟨hle, κ, ⟨w, hw, hκ⟩, x, hsup, hx⟩` from `hF i (by omega)`. Distinguish the cases in `hxi : x ∈ F i`. Establish `: F (i + 1) = F i`.

Rewrite using `[hsup, sup_eq_left, Submodule.span_singleton_le_iff_mem]`. Conclude with `hxi`. Rewrite using `[this]`. Conclude with `⟨hst, hz⟩`. Choose the witnesses or unpack the hypotheses as in `⟨lam, hl1, hl0⟩ : ∃ lam : V →ₗ[E] E, lam x = 1 ∧ ∀ v ∈ F i, lam v = 0 := by`.

Establish `hne : (F i).mkQ x ≠ 0` using `by simpa using hxi`. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_eq_one E hne`. Use `⟨f ∘ₗ (F i).mkQ, hf, fun v hv => ?_⟩` and prove the remaining obligations. Establish `: (F i).mkQ v = 0` using `by simpa using hv`. Rewrite using `[LinearMap.comp_apply, this, map_zero]`.

Establish `hdec : ∀ v ∈ F (i + 1), ∃ u ∈ F i, ∃ c : E, v = u + c • x`. Introduce `v hv`. Rewrite `hv` using `[hsup, Submodule.mem_sup]`. Take `⟨u, hu, z, hz, rfl⟩` from `hv`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hz`.

Conclude with `⟨u, hu, c, rfl⟩`. Establish `hx1 : x ∈ F (i + 1)`. Rewrite using `[hsup]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)`. Establish `hlx : ∀ g, lam (ρ g x) = (κ g : E)`.

Introduce `g`. Use `hl0 _ (hx g)` as an intermediate fact. Rewrite `this` using `[map_sub, map_smul, hl1, smul_eq_mul, mul_one, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hcont : Continuous (fun g => (κ g : E))`. Establish `h1 : Continuous (lam.restrictScalars ℚ_[l])` using `IsModuleTopology.continuous_of_linearMap _`.

Establish `h2 : Continuous (fun g => ρ g x)` using `hρ.comp (Continuous.prodMk_left x)`. Use `h1.comp h2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Conclude with `(hlx g).symm`.

Establish `hfil` using `((charFil φ hφ κ hcont w hκ).2 0).2 (by omega)`. Use `⟨fun g v hv => ?_, fun y hy hD => hz y (step φ ρ κ hfil (F i) (F (i + 1)) x lam ?_ ?_ y hy hD) hD⟩` and prove the remaining obligations. Take `⟨u, hu, c, rfl⟩` from `hdec v hv`. Rewrite using `[map_add, map_smul]`. Use `add_mem (hle (hst g u hu)) (Submodule.smul_mem _ _ ?_)` and prove the remaining obligations.

Use `add_mem (hle (hx g)) (Submodule.smul_mem _ (κ g : E) hx1)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce `v hv`. Take `⟨u, hu, c, rfl⟩` from `hdec v hv`. Simplify `hu` using `[hl0 u hu, hl1]`.

Introduce `g v hv`. Take `⟨u, hu, c, rfl⟩` from `hdec v hv`. Simplify using `[hl0 u hu, hl1, hl0 _ (hst g u hu), hlx, mul_comm]`. Establish `hfil : FilD φ ρ 0 = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `y hy`. Conclude with `(key n le_rfl).2 y (hFn ▸ filT_le_spanT hy.2) hy.1`. Establish `hH0` using `H0_eq_bot_of_filD_zero_eq_bot φ ρ hfil`. Take `⟨hfin, hdim⟩` from `bkDim hP φ hφ ρ hρ hdr`. Use `⟨hH0, hfil, hfin, ?_⟩` and prove the remaining obligations.

Rewrite `hdim` using `[hfil, hH0]`. Simplify using `using hdim`.
-/
theorem UpperTheory.V.Loc.posBasic :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → H0 ρ = ⊥ ∧ FilD φ ρ 0 = ⊥ ∧ Module.Finite E ↥(finiteCohomology φ ρ) ∧ finrank E ↥(finiteCohomology φ ρ) = φ.range.index * finrank E V := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ hpos
  obtain ⟨hdr, n, F, hF0, hFn, hF⟩ := hpos
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have key : ∀ i ≤ n, (∀ g, ∀ v ∈ F i, ρ g v ∈ F i) ∧ ∀ y ∈ spanT l (F i), y ∈ Ddr φ ρ → y = 0 := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hF0, spanT_bot]
      refine ⟨fun g v hv => ?_, fun y hy _ => hy⟩
      rw [Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
    | succ i ih =>
      intro hi
      obtain ⟨hst, hz⟩ := ih (by omega)
      obtain ⟨hle, κ, ⟨w, hw, hκ⟩, x, hsup, hx⟩ := hF i (by omega)
      by_cases hxi : x ∈ F i
      · have : F (i + 1) = F i := by
          rw [hsup, sup_eq_left, Submodule.span_singleton_le_iff_mem]; exact hxi
        rw [this]; exact ⟨hst, hz⟩
      obtain ⟨lam, hl1, hl0⟩ : ∃ lam : V →ₗ[E] E, lam x = 1 ∧ ∀ v ∈ F i, lam v = 0 := by
        have hne : (F i).mkQ x ≠ 0 := by simpa using hxi
        obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one E hne
        refine ⟨f ∘ₗ (F i).mkQ, hf, fun v hv => ?_⟩
        have : (F i).mkQ v = 0 := by simpa using hv
        rw [LinearMap.comp_apply, this, map_zero]
      have hdec : ∀ v ∈ F (i + 1), ∃ u ∈ F i, ∃ c : E, v = u + c • x := by
        intro v hv
        rw [hsup, Submodule.mem_sup] at hv
        obtain ⟨u, hu, z, hz, rfl⟩ := hv
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        exact ⟨u, hu, c, rfl⟩
      have hx1 : x ∈ F (i + 1) := by
        rw [hsup]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
      have hlx : ∀ g, lam (ρ g x) = (κ g : E) := by
        intro g
        have := hl0 _ (hx g)
        rwa [map_sub, map_smul, hl1, smul_eq_mul, mul_one, sub_eq_zero] at this
      have hcont : Continuous (fun g => (κ g : E)) := by
        have h1 : Continuous (lam.restrictScalars ℚ_[l]) :=
          IsModuleTopology.continuous_of_linearMap _
        have h2 : Continuous (fun g => ρ g x) := hρ.comp (Continuous.prodMk_left x)
        have := h1.comp h2
        convert this using 1
        funext g
        exact (hlx g).symm
      have hfil := ((charFil φ hφ κ hcont w hκ).2 0).2 (by omega)
      refine ⟨fun g v hv => ?_, fun y hy hD => hz y (step φ ρ κ hfil (F i) (F (i + 1)) x lam ?_ ?_ y hy hD) hD⟩
      · obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        rw [map_add, map_smul]
        refine add_mem (hle (hst g u hu)) (Submodule.smul_mem _ _ ?_)
        have := add_mem (hle (hx g)) (Submodule.smul_mem _ (κ g : E) hx1)
        rwa [sub_add_cancel] at this
      · intro v hv
        obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        simpa [hl0 u hu, hl1] using hu
      · intro g v hv
        obtain ⟨u, hu, c, rfl⟩ := hdec v hv
        simp [hl0 u hu, hl1, hl0 _ (hst g u hu), hlx, mul_comm]
  have hfil : FilD φ ρ 0 = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact (key n le_rfl).2 y (hFn ▸ filT_le_spanT hy.2) hy.1
  have hH0 := H0_eq_bot_of_filD_zero_eq_bot φ ρ hfil
  obtain ⟨hfin, hdim⟩ := bkDim hP φ hφ ρ hρ hdr
  refine ⟨hH0, hfil, hfin, ?_⟩
  rw [hfil, hH0] at hdim
  simpa using hdim

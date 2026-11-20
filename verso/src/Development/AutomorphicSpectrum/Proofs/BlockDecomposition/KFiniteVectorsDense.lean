import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFCA

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.DenseKFin

section Fixed

/- English proof (translation)
Take `⟨w, hwT, hw⟩` from `exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hc (0 : Y)`. Use `⟨w, hwT, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `ciInf_le (f := fun z : T => ‖(0 : Y) - z‖) ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩ ⟨y, hy⟩`. Rewrite `h1` using `[← hw]`. Simplify using `using h1`.
-/
theorem exists_min_norm {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] {T : Set Y}
    (hne : T.Nonempty) (hcl : IsClosed T) (hc : Convex ℝ T) : ∃ w ∈ T, ∀ y ∈ T, ‖w‖ ≤ ‖y‖ := by
  obtain ⟨w, hwT, hw⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hc (0 : Y)
  refine ⟨w, hwT, fun y hy => ?_⟩
  have h1 := ciInf_le (f := fun z : T => ‖(0 : Y) - z‖)
    ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩ ⟨y, hy⟩
  rw [← hw] at h1
  simpa using h1

variable {X Γ : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] [Group Γ]

/- English proof (translation)
Use `set S : Set X := Set.range fun g => π g v with hS`. Use `set T : Set X := closure (convexHull ℝ S) with hT`. Establish `hTc : Convex ℝ T` using `(convex_convexHull ℝ S).closure`. Establish `hTcl : IsClosed T` using `isClosed_closure`. Establish `hne : T.Nonempty` using `⟨π 1 v, subset_closure (subset_convexHull ℝ S ⟨1, rfl⟩)⟩`.

Take `⟨w, hwT, hmin⟩` from `@exists_min_norm X _ (InnerProductSpace.rclikeToReal ℂ X) _ T hne hTcl hTc`. Establish `hTinv : ∀ g, ∀ y ∈ T, π g y ∈ T`. Introduce `g`. Establish `hpre : IsClosed ((π g) ⁻¹' T)` using `hTcl.preimage (π g).continuous`. Establish `hconv : Convex ℝ ((π g) ⁻¹' T)` using `hTc.linear_preimage (((π g).toLinearMap).restrictScalars ℝ)`.

Establish `hsub : S ⊆ (π g) ⁻¹' T`. Introduce and unpack `_ ⟨h, rfl⟩`. Use `subset_closure (subset_convexHull ℝ S ⟨g * h, ?_⟩)` and prove the remaining obligations. Simplify using `[map_mul]`. Conclude with `closure_minimal (convexHull_min hsub hconv) hpre`.

Establish `hfix : ∀ g, π g w = w`. Introduce `g`. Establish `hg` using `hTinv g w hwT`. Establish `hm : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • π g w ∈ T` using `hTc hwT hg (by norm_num) (by norm_num) (by norm_num)`. Establish `h1` using `hmin _ hm`.

Establish `hpar` using `parallelogram_law_with_norm ℂ w (π g w)`. Rewrite `hpar` using `[hiso]`. Establish `e : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • π g w = (1 / 2 : ℝ) • (w + π g w)`. Rewrite using `[smul_add]`. Rewrite `h1` using `[e, norm_smul]`.

Establish `h2 : ‖(1 / 2 : ℝ)‖ = 1 / 2` using `by norm_num`. Rewrite `h1` using `[h2]`. Establish `h3 : 2 * ‖w‖ ≤ ‖w + π g w‖` using `by linarith`. Establish `h4 : ‖w - π g w‖ * ‖w - π g w‖ ≤ 0`. Use polynomial arithmetic with `[norm_nonneg w, norm_nonneg (w + π g w), norm_nonneg (w - π g w)]`.

Establish `h5 : ‖w - π g w‖ = 0`. Use polynomial arithmetic with `[norm_nonneg (w - π g w)]`. Conclude with `(sub_eq_zero.1 (norm_eq_zero.1 h5)).symm`. Use `⟨w, ?_, hfix, ?_⟩` and prove the remaining obligations. Establish `hCc : Convex ℝ (C : Set X)` using `(C.restrictScalars ℝ).convex`.

Establish `hsub : S ⊆ C`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `hinv g v hv`. Conclude with `closure_minimal (convexHull_min hsub hCc) hC hwT`. Establish `hsub : S ⊆ Metric.closedBall v ε`.

Introduce and unpack `_ ⟨g, rfl⟩`. Simplify `hε g` using `[dist_eq_norm]`. Use `closure_minimal (convexHull_min hsub (convex_closedBall v ε)) Metric.isClosed_closedBall hwT` as an intermediate fact. Simplify `this` using `[dist_eq_norm]`.
-/
theorem exists_fixed_near (π : Γ →* (X →L[ℂ] X)) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (C : Submodule ℂ X) (hC : IsClosed (C : Set X)) (hinv : ∀ g, ∀ x ∈ C, π g x ∈ C)
    {v : X} (hv : v ∈ C) {ε : ℝ} (hε : ∀ g, ‖π g v - v‖ ≤ ε) :
    ∃ w ∈ C, (∀ g, π g w = w) ∧ ‖w - v‖ ≤ ε := by
  set S : Set X := Set.range fun g => π g v with hS
  set T : Set X := closure (convexHull ℝ S) with hT
  have hTc : Convex ℝ T := (convex_convexHull ℝ S).closure
  have hTcl : IsClosed T := isClosed_closure
  have hne : T.Nonempty := ⟨π 1 v, subset_closure (subset_convexHull ℝ S ⟨1, rfl⟩)⟩
  obtain ⟨w, hwT, hmin⟩ := @exists_min_norm X _ (InnerProductSpace.rclikeToReal ℂ X) _ T hne hTcl hTc
  have hTinv : ∀ g, ∀ y ∈ T, π g y ∈ T := by
    intro g
    have hpre : IsClosed ((π g) ⁻¹' T) := hTcl.preimage (π g).continuous
    have hconv : Convex ℝ ((π g) ⁻¹' T) :=
      hTc.linear_preimage (((π g).toLinearMap).restrictScalars ℝ)
    have hsub : S ⊆ (π g) ⁻¹' T := by
      rintro _ ⟨h, rfl⟩
      refine subset_closure (subset_convexHull ℝ S ⟨g * h, ?_⟩)
      simp [map_mul]
    exact closure_minimal (convexHull_min hsub hconv) hpre
  have hfix : ∀ g, π g w = w := by
    intro g
    have hg := hTinv g w hwT
    have hm : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • π g w ∈ T :=
      hTc hwT hg (by norm_num) (by norm_num) (by norm_num)
    have h1 := hmin _ hm
    have hpar := parallelogram_law_with_norm ℂ w (π g w)
    rw [hiso] at hpar
    have e : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • π g w = (1 / 2 : ℝ) • (w + π g w) := by
      rw [smul_add]
    rw [e, norm_smul] at h1
    have h2 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [h2] at h1
    have h3 : 2 * ‖w‖ ≤ ‖w + π g w‖ := by linarith
    have h4 : ‖w - π g w‖ * ‖w - π g w‖ ≤ 0 := by
      nlinarith [norm_nonneg w, norm_nonneg (w + π g w), norm_nonneg (w - π g w)]
    have h5 : ‖w - π g w‖ = 0 := by
      nlinarith [norm_nonneg (w - π g w)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h5)).symm
  refine ⟨w, ?_, hfix, ?_⟩
  · have hCc : Convex ℝ (C : Set X) := (C.restrictScalars ℝ).convex
    have hsub : S ⊆ C := by
      rintro _ ⟨g, rfl⟩
      exact hinv g v hv
    exact closure_minimal (convexHull_min hsub hCc) hC hwT
  · have hsub : S ⊆ Metric.closedBall v ε := by
      rintro _ ⟨g, rfl⟩
      simpa [dist_eq_norm] using hε g
    have := closure_minimal (convexHull_min hsub (convex_closedBall v ε)) Metric.isClosed_closedBall hwT
    simpa [dist_eq_norm] using this

end Fixed

section Nonarch

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/- English proof (translation)
Take `⟨K, hK⟩` from `NonarchimedeanAddGroup.is_nonarchimedean (V ∩ O) (Filter.inter_mem hV (hOo.mem_nhds O.zero_mem))`. Set `I : AddSubgroup A` to `{ carrier := {x | ∀ r ∈ O, r * x ∈ K} add_mem' := fun {x y} hx hy r hr => by`. Rewrite using `[mul_add]`. Conclude with `K.add_mem (hx r hr) (hy r hr)`. Use the proof step `zero_mem' := fun r _ => by rw [mul_zero]; exact K.zero_mem`.

Use the proof step `neg_mem' := fun {x} hx r hr => by rw [mul_neg]; exact K.neg_mem (hx r hr) }`. Establish `hIn : (I : Set A) ∈ 𝓝 (0 : A)`. Establish `hn : IsOpen {p : A × A | p.1 * p.2 ∈ (K : Set A)}` using `K.isOpen.preimage (continuous_fst.mul continuous_snd)`. Take `⟨u, v, -, hv, hu, h0, huv⟩` from `generalized_tube_lemma hOc (isCompact_singleton (x := (0 : A))) hn (by`. Introduce and unpack `⟨r, z⟩ ⟨-, hz⟩`.

Establish `hz' : z = 0` using `hz`. Express the relevant statement in the definitionally equal form `r * z ∈ (K : Set A)`. Rewrite using `[hz', mul_zero]`. Conclude with `K.zero_mem)`. Use `Filter.mem_of_superset (hv.mem_nhds (h0 rfl)) fun x hx r hr => ?_` and prove the remaining obligations.

Conclude with `huv (Set.mk_mem_prod (hu hr) hx)`. Use `⟨I, AddSubgroup.isOpen_of_mem_nhds I hIn, fun x hx => ?_, fun x hx y hy r hr => ?_⟩` and prove the remaining obligations. Use `hx 1 O.one_mem` as an intermediate fact. Rewrite `this` using `[one_mul]`. Conclude with `(hK this).1`.

Rewrite using `[← mul_assoc]`. Conclude with `hy _ (hK (hx r hr)).2`.
-/
theorem exists_mulClosed [NonarchimedeanAddGroup A] (O : Subring A) (hOo : IsOpen (O : Set A))
    (hOc : IsCompact (O : Set A)) {V : Set A} (hV : V ∈ 𝓝 (0 : A)) :
    ∃ I : AddSubgroup A, IsOpen (I : Set A) ∧ (I : Set A) ⊆ V ∧ ∀ x ∈ I, ∀ y ∈ I, x * y ∈ I := by
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean (V ∩ O)
    (Filter.inter_mem hV (hOo.mem_nhds O.zero_mem))
  let I : AddSubgroup A :=
    { carrier := {x | ∀ r ∈ O, r * x ∈ K}
      add_mem' := fun {x y} hx hy r hr => by
        rw [mul_add]; exact K.add_mem (hx r hr) (hy r hr)
      zero_mem' := fun r _ => by rw [mul_zero]; exact K.zero_mem
      neg_mem' := fun {x} hx r hr => by rw [mul_neg]; exact K.neg_mem (hx r hr) }
  have hIn : (I : Set A) ∈ 𝓝 (0 : A) := by
    have hn : IsOpen {p : A × A | p.1 * p.2 ∈ (K : Set A)} :=
      K.isOpen.preimage (continuous_fst.mul continuous_snd)
    obtain ⟨u, v, -, hv, hu, h0, huv⟩ := generalized_tube_lemma hOc (isCompact_singleton (x := (0 : A))) hn (by
      rintro ⟨r, z⟩ ⟨-, hz⟩
      have hz' : z = 0 := hz
      change r * z ∈ (K : Set A)
      rw [hz', mul_zero]
      exact K.zero_mem)
    refine Filter.mem_of_superset (hv.mem_nhds (h0 rfl)) fun x hx r hr => ?_
    exact huv (Set.mk_mem_prod (hu hr) hx)
  refine ⟨I, AddSubgroup.isOpen_of_mem_nhds I hIn, fun x hx => ?_, fun x hx y hy r hr => ?_⟩
  · have := hx 1 O.one_mem
    rw [one_mul] at this
    exact (hK this).1
  · rw [← mul_assoc]
    exact hy _ (hK (hx r hr)).2

/- English proof (translation)
Set `N' : Set (Fin n → Fin n → A)` to `N`. Establish `hN' : N' ∈ 𝓝 (0 : Fin n → Fin n → A)` using `hN`. Rewrite `hN'` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hs⟩` from `hN'`. Establish `key : ∀ i, ∃ V ∈ 𝓝 (0 : A), ∀ r : Fin n → A, (∀ j, r j ∈ V) → r ∈ t i`.

Introduce `i`. Establish `h` using `ht i`. Rewrite `h` using `[nhds_pi, Filter.mem_pi]`. Take `⟨J, -, s, hs', hss⟩` from `h`. Conclude with `⟨⋂ j, s j, Filter.iInter_mem.2 hs', fun r hr => hss fun j _ => Set.mem_iInter.1 (hr j) j⟩`.

Use `choose V hV hVt using key`. Conclude with `⟨⋂ i, V i, Filter.iInter_mem.2 hV, fun m hm => hs fun i _ => hVt i _ fun j => Set.mem_iInter.1 (hm i j) i⟩`.
-/
theorem exists_entry_nhds {n : ℕ} {N : Set (Matrix (Fin n) (Fin n) A)} (hN : N ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) A)) :
    ∃ V ∈ 𝓝 (0 : A), ∀ m : Matrix (Fin n) (Fin n) A, (∀ i j, m i j ∈ V) → m ∈ N := by
  let N' : Set (Fin n → Fin n → A) := N
  have hN' : N' ∈ 𝓝 (0 : Fin n → Fin n → A) := hN
  rw [nhds_pi, Filter.mem_pi] at hN'
  obtain ⟨I, -, t, ht, hs⟩ := hN'
  have key : ∀ i, ∃ V ∈ 𝓝 (0 : A), ∀ r : Fin n → A, (∀ j, r j ∈ V) → r ∈ t i := by
    intro i
    have h := ht i
    rw [nhds_pi, Filter.mem_pi] at h
    obtain ⟨J, -, s, hs', hss⟩ := h
    exact ⟨⋂ j, s j, Filter.iInter_mem.2 hs', fun r hr => hss fun j _ => Set.mem_iInter.1 (hr j) j⟩
  choose V hV hVt using key
  exact ⟨⋂ i, V i, Filter.iInter_mem.2 hV, fun m hm => hs fun i _ => hVt i _ fun j => Set.mem_iInter.1 (hm i j) i⟩

/- English proof (translation)
Rewrite `hW` using `[Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap]`. Take `⟨t, ht, hsub⟩` from `hW`. Set `M` to `Matrix (Fin n) (Fin n) A`. Establish `hc : Continuous fun p : M × M => ((1 + p.1, MulOpposite.op (1 + p.2)) : M × Mᵐᵒᵖ)` using `(continuous_const.add continuous_fst).prodMk (MulOpposite.continuous_op.comp (continuous_const.add continuous_snd))`. Establish `h0 : (fun p : M × M => ((1 + p.1, MulOpposite.op (1 + p.2)) : M × Mᵐᵒᵖ)) ⁻¹' t ∈ 𝓝 ((0, 0) : M × M)`.

Use `hc.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Simplify using `using ht`. Take `⟨u, hu, v, hv, huv⟩` from `mem_nhds_prod_iff.1 h0`. Take `⟨V, hV, hVN⟩` from `exists_entry_nhds (Filter.inter_mem hu hv)`. Take `⟨I, hIo, hIV, hImul⟩` from `hbase V hV`.

Establish `hPmul : ∀ x y : M, (∀ i j, x i j ∈ I) → (∀ i j, y i j ∈ I) → ∀ i j, (x * y) i j ∈ I`. Introduce `x y hx hy i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun k _ => hImul _ (hx i k) _ (hy k j)`. Establish `hPadd : ∀ x y : M, (∀ i j, x i j ∈ I) → (∀ i j, y i j ∈ I) → ∀ i j, (x + y) i j ∈ I` using `fun x y hx hy i j => I.add_mem (hx i j) (hy i j)`.

Establish `hstep : ∀ x y : M, (∀ i j, (x - 1) i j ∈ I) → (∀ i j, (y - 1) i j ∈ I) → ∀ i j, (x * y - 1) i j ∈ I`. Introduce `x y hx hy`. Establish `e : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1)`. Simplify using `only [sub_mul, mul_sub, mul_one, one_mul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `hPadd _ _ (hPadd _ _ (hPmul _ _ hx hy) hx) hy`. Set `U : Subgroup (GL (Fin n) A)` to `{ carrier := {g | (∀ i j, ((g : M) - 1) i j ∈ I) ∧ ∀ i j, (((g⁻¹ : GL (Fin n) A) : M) - 1) i j ∈ I} mul_mem' := by`. Introduce and unpack `g h ⟨hg, hg'⟩ ⟨hh, hh'⟩`. Use `⟨hstep _ _ hg hh, ?_⟩` and prove the remaining obligations.

Rewrite using `[_root_.mul_inv_rev]`. Conclude with `hstep _ _ hh' hg'`. Use the proof step `one_mem' := by simp [I.zero_mem]`. Use the proof step `inv_mem' := by`. Introduce and unpack `g ⟨hg, hg'⟩`.

Conclude with `⟨hg', by simpa using hg⟩ }`. Use `⟨U, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : IsOpen {g : GL (Fin n) A | ∀ i j, ((g : M) - 1) i j ∈ I}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hIo.preimage ((Units.continuous_val.sub continuous_const).matrix_elem i j)`.

Establish `h2 : IsOpen {g : GL (Fin n) A | ∀ i j, (((g⁻¹ : GL (Fin n) A) : M) - 1) i j ∈ I}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hIo.preimage ((Units.continuous_coe_inv.sub continuous_const).matrix_elem i j)`. Conclude with `h1.inter h2`. Introduce and unpack `g ⟨hg, hg'⟩`.

Use `hsub ?_` and prove the remaining obligations. Establish `e1` using `(hVN _ fun i j => hIV (hg i j)).1`. Establish `e2` using `(hVN _ fun i j => hIV (hg' i j)).2`. Use `huv (Set.mk_mem_prod e1 e2)` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_openSubgroup_GL {n : ℕ}
    (hbase : ∀ V ∈ 𝓝 (0 : A), ∃ I : AddSubgroup A, IsOpen (I : Set A) ∧ (I : Set A) ⊆ V ∧
      ∀ x ∈ I, ∀ y ∈ I, x * y ∈ I)
    {W : Set (GL (Fin n) A)} (hW : W ∈ 𝓝 (1 : GL (Fin n) A)) :
    ∃ U : Subgroup (GL (Fin n) A), IsOpen (U : Set (GL (Fin n) A)) ∧ (U : Set (GL (Fin n) A)) ⊆ W := by
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨t, ht, hsub⟩ := hW
  let M := Matrix (Fin n) (Fin n) A
  have hc : Continuous fun p : M × M => ((1 + p.1, MulOpposite.op (1 + p.2)) : M × Mᵐᵒᵖ) :=
    (continuous_const.add continuous_fst).prodMk
      (MulOpposite.continuous_op.comp (continuous_const.add continuous_snd))
  have h0 : (fun p : M × M => ((1 + p.1, MulOpposite.op (1 + p.2)) : M × Mᵐᵒᵖ)) ⁻¹' t ∈ 𝓝 ((0, 0) : M × M) := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using ht
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 h0
  obtain ⟨V, hV, hVN⟩ := exists_entry_nhds (Filter.inter_mem hu hv)
  obtain ⟨I, hIo, hIV, hImul⟩ := hbase V hV
  have hPmul : ∀ x y : M, (∀ i j, x i j ∈ I) → (∀ i j, y i j ∈ I) → ∀ i j, (x * y) i j ∈ I := by
    intro x y hx hy i j
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => hImul _ (hx i k) _ (hy k j)
  have hPadd : ∀ x y : M, (∀ i j, x i j ∈ I) → (∀ i j, y i j ∈ I) → ∀ i j, (x + y) i j ∈ I :=
    fun x y hx hy i j => I.add_mem (hx i j) (hy i j)
  have hstep : ∀ x y : M, (∀ i j, (x - 1) i j ∈ I) → (∀ i j, (y - 1) i j ∈ I) → ∀ i j, (x * y - 1) i j ∈ I := by
    intro x y hx hy
    have e : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by
      simp only [sub_mul, mul_sub, mul_one, one_mul]
      abel
    rw [e]
    exact hPadd _ _ (hPadd _ _ (hPmul _ _ hx hy) hx) hy
  let U : Subgroup (GL (Fin n) A) :=
    { carrier := {g | (∀ i j, ((g : M) - 1) i j ∈ I) ∧ ∀ i j, (((g⁻¹ : GL (Fin n) A) : M) - 1) i j ∈ I}
      mul_mem' := by
        rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
        refine ⟨hstep _ _ hg hh, ?_⟩
        rw [_root_.mul_inv_rev]
        exact hstep _ _ hh' hg'
      one_mem' := by simp [I.zero_mem]
      inv_mem' := by
        rintro g ⟨hg, hg'⟩
        exact ⟨hg', by simpa using hg⟩ }
  refine ⟨U, ?_, ?_⟩
  · have h1 : IsOpen {g : GL (Fin n) A | ∀ i j, ((g : M) - 1) i j ∈ I} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hIo.preimage ((Units.continuous_val.sub continuous_const).matrix_elem i j)
    have h2 : IsOpen {g : GL (Fin n) A | ∀ i j, (((g⁻¹ : GL (Fin n) A) : M) - 1) i j ∈ I} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hIo.preimage ((Units.continuous_coe_inv.sub continuous_const).matrix_elem i j)
    exact h1.inter h2
  · rintro g ⟨hg, hg'⟩
    refine hsub ?_
    have e1 := (hVN _ fun i j => hIV (hg i j)).1
    have e2 := (hVN _ fun i j => hIV (hg' i j)).2
    have := huv (Set.mk_mem_prod e1 e2)
    simpa using this

end Nonarch

section Abstract

variable {G X A K : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]

/- English proof (translation)
Introduce `F hF`. Express the relevant statement in the definitionally equal form `F ∈ closure _`. Use `Metric.mem_closure_iff.2 fun ε hε => ?_` and prove the remaining obligations. Establish `hnb : {u : A | ‖π (fin u) F - F‖ < ε / 2} ∈ 𝓝 (1 : A)`. Use `(isOpen_lt ((hfin F).sub continuous_const).norm continuous_const).mem_nhds ?_` and prove the remaining obligations.

Simplify using `[half_pos hε]`. Take `⟨U, hUo, hUs⟩` from `hopen _ hnb`. Take `⟨w, hwH, hwfix, hwd⟩` from `exists_fixed_near (π.comp (fin.comp U.subtype)) (fun g x => hiso _ x) H hH.1 (fun g x hx => hH.2 _ x hx) hF (ε := ε / 2) (fun g => (hUs g.2 : _ < _).le)`. Set `Y : Submodule ℂ X` to `{ carrier := {x | x ∈ H ∧ ∀ u ∈ U, π (fin u) x = x} add_mem' := fun {x y} hx hy => ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add, hx.2 u hu, hy.2 u hu]⟩ zero_mem' := ⟨H.zero_mem, fun u _ => map_zero _⟩ smul_mem' := fun c x hx => ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, …`. Establish `hYc : IsClosed (Y : Set X)`.

Establish `: (Y : Set X) = (H : Set X) ∩ ⋂ u ∈ U, {x | π (fin u) x = x}`. Use extensionality with `x`. Simplify using `[Y]`. Rewrite using `[this]`. Conclude with `hH.1.inter (isClosed_biInter fun u _ => isClosed_eq (π (fin u)).continuous continuous_id)`.

Use `haveI : CompleteSpace Y := hYc.completeSpace_coe`. Establish `hYinv : ∀ k, ∀ x ∈ Y, π (inf k) x ∈ Y`. Introduce `k x hx`. Use `⟨hH.2 _ x hx.1, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, hcomm, map_mul, ContinuousLinearMap.mul_apply, hx.2 u hu]`.

Set `ρ : K →* (Y →L[ℂ] Y)` to `{ toFun := fun k => ((π (inf k)).comp Y.subtypeL).codRestrict Y fun x => hYinv k x x.2 map_one' := by`. Use extensionality with `x`. Simplify using the standard rewrite rules. Use the proof step `map_mul' := by`. Introduce `k l`.

Use extensionality with `x`. Express the relevant statement in the definitionally equal form `π (inf (k * l)) x = π (inf k) (π (inf l) x)`. Rewrite using `[map_mul, map_mul, ContinuousLinearMap.mul_apply] }`. Establish `hd` using `GlobalTheory.CompactRep.dense_finite_vectors K Y ρ (fun k x => hiso _ x) (fun x => (hinf x).subtype_mk _)`. Take `⟨y, hyb, S, hSf, hyS, hSinv⟩` from `Metric.dense_iff.1 hd ⟨w, hwH, fun u hu => hwfix ⟨u, hu⟩⟩ (ε / 2) (half_pos hε)`.

Use `⟨y, Submodule.subset_span ⟨y.2.1, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Set `St : Subgroup A` to `{ carrier := {u | π (fin u) y = y} mul_mem' := fun {u v} hu hv => by`. Express the relevant statement in the definitionally equal form `π (fin (u * v)) y = y`. Rewrite using `[map_mul, map_mul, ContinuousLinearMap.mul_apply, hv, hu]`. Use the proof step `one_mem' := by`.

Express the relevant statement in the definitionally equal form `π (fin 1) y = y`. Simplify using the standard rewrite rules. Use the proof step `inv_mem' := fun {u} hu => by`. Express the relevant statement in the definitionally equal form `π (fin u⁻¹) y = y`. Establish `h1 : π (fin u⁻¹) (π (fin u) (y : X)) = y`.

Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel]`. Simplify using the standard rewrite rules. Rewrite using `[hu] at h1 }` and apply the resulting hypothesis. Conclude with `Subgroup.isOpen_mono (H₁ := U) (H₂ := St) (fun u hu => y.2.2 u hu) hUo`. Use `Submodule.finiteDimensional_of_le (S₂ := S.map Y.subtype) (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨ρ k y, hSinv k y hyS, rfl⟩`. Establish `h1 : dist F w ≤ ε / 2`. Rewrite using `[dist_comm, dist_eq_norm]`. Conclude with `hwd`.

Establish `h2 : dist w (y : X) < ε / 2`. Rewrite using `[dist_comm]`. Conclude with `hyb`. Combine the linear relations using `[dist_triangle F w (y : X)]`.
-/
theorem le_closure_span (π : G →* (X →L[ℂ] X)) (hiso : ∀ g x, ‖π g x‖ = ‖x‖) (fin : A →* G) (inf : K →* G)
    (hfin : ∀ x, Continuous fun u => π (fin u) x) (hinf : ∀ x, Continuous fun k => π (inf k) x)
    (hcomm : ∀ u k, fin u * inf k = inf k * fin u)
    (hopen : ∀ W ∈ 𝓝 (1 : A), ∃ U : Subgroup A, IsOpen (U : Set A) ∧ (U : Set A) ⊆ W)
    (H : Submodule ℂ X) (hH : IsSubrep π H) :
    H ≤ (Submodule.span ℂ {F | F ∈ H ∧ IsOpen {u | π (fin u) F = F} ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => π (inf k) F))}).topologicalClosure := by
  intro F hF
  change F ∈ closure _
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  have hnb : {u : A | ‖π (fin u) F - F‖ < ε / 2} ∈ 𝓝 (1 : A) := by
    refine (isOpen_lt ((hfin F).sub continuous_const).norm continuous_const).mem_nhds ?_
    simp [half_pos hε]
  obtain ⟨U, hUo, hUs⟩ := hopen _ hnb
  obtain ⟨w, hwH, hwfix, hwd⟩ := exists_fixed_near (π.comp (fin.comp U.subtype)) (fun g x => hiso _ x) H hH.1
    (fun g x hx => hH.2 _ x hx) hF (ε := ε / 2) (fun g => (hUs g.2 : _ < _).le)
  let Y : Submodule ℂ X :=
    { carrier := {x | x ∈ H ∧ ∀ u ∈ U, π (fin u) x = x}
      add_mem' := fun {x y} hx hy => ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add, hx.2 u hu, hy.2 u hu]⟩
      zero_mem' := ⟨H.zero_mem, fun u _ => map_zero _⟩
      smul_mem' := fun c x hx => ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩ }
  have hYc : IsClosed (Y : Set X) := by
    have : (Y : Set X) = (H : Set X) ∩ ⋂ u ∈ U, {x | π (fin u) x = x} := by
      ext x
      simp [Y]
    rw [this]
    exact hH.1.inter (isClosed_biInter fun u _ => isClosed_eq (π (fin u)).continuous continuous_id)
  haveI : CompleteSpace Y := hYc.completeSpace_coe
  have hYinv : ∀ k, ∀ x ∈ Y, π (inf k) x ∈ Y := by
    intro k x hx
    refine ⟨hH.2 _ x hx.1, fun u hu => ?_⟩
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, hcomm, map_mul, ContinuousLinearMap.mul_apply, hx.2 u hu]
  let ρ : K →* (Y →L[ℂ] Y) :=
    { toFun := fun k => ((π (inf k)).comp Y.subtypeL).codRestrict Y fun x => hYinv k x x.2
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro k l
        ext x
        change π (inf (k * l)) x = π (inf k) (π (inf l) x)
        rw [map_mul, map_mul, ContinuousLinearMap.mul_apply] }
  have hd := GlobalTheory.CompactRep.dense_finite_vectors K Y ρ (fun k x => hiso _ x)
    (fun x => (hinf x).subtype_mk _)
  obtain ⟨y, hyb, S, hSf, hyS, hSinv⟩ := Metric.dense_iff.1 hd ⟨w, hwH, fun u hu => hwfix ⟨u, hu⟩⟩ (ε / 2) (half_pos hε)
  refine ⟨y, Submodule.subset_span ⟨y.2.1, ?_, ?_⟩, ?_⟩
  · let St : Subgroup A :=
      { carrier := {u | π (fin u) y = y}
        mul_mem' := fun {u v} hu hv => by
          change π (fin (u * v)) y = y
          rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hv, hu]
        one_mem' := by
          change π (fin 1) y = y
          simp
        inv_mem' := fun {u} hu => by
          change π (fin u⁻¹) y = y
          have h1 : π (fin u⁻¹) (π (fin u) (y : X)) = y := by
            rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel]
            simp
          rwa [hu] at h1 }
    exact Subgroup.isOpen_mono (H₁ := U) (H₂ := St) (fun u hu => y.2.2 u hu) hUo
  · refine Submodule.finiteDimensional_of_le (S₂ := S.map Y.subtype) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨ρ k y, hSinv k y hyS, rfl⟩
  · have h1 : dist F w ≤ ε / 2 := by
      rw [dist_comm, dist_eq_norm]
      exact hwd
    have h2 : dist w (y : X) < ε / 2 := by
      rw [dist_comm]
      exact hyb
    linarith [dist_triangle F w (y : X)]

end Abstract

section Concrete

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

/- English proof (translation)
Use `haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := E)`. Conclude with `exists_openSubgroup_GL (fun V hV => exists_mulClosed (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd E) Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd Formalism.L2.Col.rlt_isCompact_i …`.
-/
theorem exists_openSubgroup_GLAf {W : Set (GL (Fin a) (Af E))} (hW : W ∈ 𝓝 (1 : GL (Fin a) (Af E))) :
    ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧
      (U : Set (GL (Fin a) (Af E))) ⊆ W := by
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := E)
  exact exists_openSubgroup_GL (fun V hV => exists_mulClosed (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd E)
    Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.isOpen_intAd Formalism.L2.Col.rlt_isCompact_intAd hV) hW

omit [IsTotallyComplex E] in

/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Establish `hs : Continuous (sFin E)` using `(continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))`. Conclude with `continuous_const.add (continuous_id.matrix_map hs)`.
-/
theorem continuous_finGL : Continuous (finGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E) :=
    (continuous_const.prodMk continuous_id :
      Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact continuous_const.add (continuous_id.matrix_map hs)

/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Establish `hs : Continuous (sInf E : Cinf E → Ad E)` using `(continuous_infEq E).prodMk continuous_const`. Conclude with `continuous_const.add (continuous_id.matrix_map hs)`.
-/
theorem continuous_infGL : Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.add (continuous_id.matrix_map hs)

end Concrete

/- English proof (translation)
Use `haveI := GlobalTheory.KinfCompactness.compactSpace_Kinf E a`. Use `haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Cinf E)) := inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Cinf E))`. Use `haveI : SecondCountableTopology (Kinf E a) := TopologicalSpace.Subtype.secondCountableTopology _`. Establish `hU : Continuous fun k : Kinf E a => (Unitary.toUnits k : GL (Fin a) (Cinf E))` using `Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩`. Establish `hc` using `fun F : L2 (latticeGL E a) μ => continuous_R (Γ := latticeGL E a) (μ := μ) F`.

Conclude with `le_closure_span (R (latticeGL E a) μ) (fun g x => norm_R g x) (finGL E a) ((infGL E a).comp Unitary.toUnits) (fun x => (hc x).comp continuous_finGL) (fun x => (hc x).comp (continuous_infGL.comp hU)) (fun u k => (infGL_comm _ u).symm) (fun W hW => exists_openSubgroup_GLAf hW) H hH`.
-/
theorem le_closure_span_K_finite (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ))
    (hH : IsSubrep (R (latticeGL E a) μ) H) :
    H ≤ (Submodule.span ℂ {F | F ∈ H ∧ IsKFinL2 μ F}).topologicalClosure := by
  haveI := GlobalTheory.KinfCompactness.compactSpace_Kinf E a
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Cinf E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Cinf E))
  haveI : SecondCountableTopology (Kinf E a) := TopologicalSpace.Subtype.secondCountableTopology _
  have hU : Continuous fun k : Kinf E a => (Unitary.toUnits k : GL (Fin a) (Cinf E)) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  have hc := fun F : L2 (latticeGL E a) μ => continuous_R (Γ := latticeGL E a) (μ := μ) F
  exact le_closure_span (R (latticeGL E a) μ) (fun g x => norm_R g x) (finGL E a) ((infGL E a).comp Unitary.toUnits)
    (fun x => (hc x).comp continuous_finGL)
    (fun x => (hc x).comp (continuous_infGL.comp hU))
    (fun u k => (infGL_comm _ u).symm) (fun W hW => exists_openSubgroup_GLAf hW) H hH

end GlobalTheory.CompanionTheory.DenseKFin

end

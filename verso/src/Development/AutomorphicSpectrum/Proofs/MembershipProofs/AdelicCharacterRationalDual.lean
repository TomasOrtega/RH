import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.AdelicCharacterRationalDualImports
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import GroundTheory.AutomorphicForms.GL2.GJMatrixFinite
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DenseHasCompactSupport

noncomputable section

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory Complex
open scoped Real TensorProduct Classical

namespace GlobalTheory.CompanionTheory.ThetaUniq

/- English proof (translation)
Introduce `V _ _ ι _ B T h1 h2`. Use `haveI : FiniteDimensional ℝ V := Module.Finite.of_basis B`. Set `e` to `Fintype.equivFin ι`. Set `C` to `B.reindex e`. Set `Cc : V ≃L[ℝ] (Fin (Fintype.card ι) → ℝ)` to `C.equivFun.toContinuousLinearEquiv`.

Set `P` to `SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ Cc`. Establish `hP : ∀ (f : SchwartzMap (Fin (Fintype.card ι) → ℝ) ℂ) x, P f x = f (Cc x)` using `fun _ _ => rfl`. Establish `hCc : ∀ x i, Cc x i = B.repr x (e.symm i)` using `fun x i => by`. Simplify using `[Cc, C, Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply]`. Establish `hsum : ∀ m : ι → ℤ, Cc (∑ i, (m i : ℝ) • B i) = fun j => (m (e.symm j) : ℝ)` using `fun m => by`.

Use function extensionality and compare the values at `j`. Rewrite using `[hCc, B.repr_sum_self]`. Establish `hA : ∀ (i : Fin (Fintype.card ι)) (f g : SchwartzMap (Fin (Fintype.card ι) → ℝ) ℂ), (∀ x, g x = cexp (2 * π * I * x i) * f x) → (T.comp P) g = (T.comp P) f`. Introduce `i f g h`. Use `h1 (e.symm i) (P f) (P g) fun x => ?_` and prove the remaining obligations.

Rewrite using `[hP, hP, h, hCc]`. Establish `hC : ∀ (m : Fin (Fintype.card ι) → ℤ) (f g : SchwartzMap (Fin (Fintype.card ι) → ℝ) ℂ), (∀ x, g x = f (x + fun i => (m i : ℝ))) → (T.comp P) g = (T.comp P) f`. Introduce `m f g h`. Use `h2 (fun i => m (e i)) (P f) (P g) fun x => ?_` and prove the remaining obligations. Rewrite using `[hP, hP, h]`.

Use `congr 1`. Rewrite using `[map_add, hsum]`. Simplify using the standard rewrite rules. Take `⟨a, ha⟩` from `GlobalTheory.CompanionTheory.DiracComb.eq_mul_comb _ (T.comp P) hA hC`. Use `⟨a, fun f => ?_⟩` and prove the remaining obligations.

Set `Q` to `SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ Cc.symm`. Establish `hPQ : P (Q f) = f`. Use extensionality with `x`. Use `show f (Cc.symm (Cc x)) = f x`. Rewrite using `[Cc.symm_apply_apply]`.

Establish `h3` using `ha (Q f)`. Rewrite `h3` using `[ContinuousLinearMap.comp_apply, hPQ]`. Rewrite using `[h3]`. Use `congr 1`. Use `Eq.trans ?_ ((Equiv.arrowCongr e (Equiv.refl ℤ)).symm.tsum_eq fun m => f (∑ i, (m i : ℝ) • B i))` and prove the remaining obligations.

Use `tsum_congr fun m => ?_` and prove the remaining obligations. Use `show f (Cc.symm _) = _`. Use `congr 1`. Rewrite using `[ContinuousLinearEquiv.symm_apply_eq, hsum]`. Simplify using `[Equiv.arrowCongr]`.
-/
theorem comb_of_basis : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (ι : Type) [Fintype ι] (B : Module.Basis ι ℝ V) (T : SchwartzMap V ℂ →L[ℂ] ℂ), (∀ (i : ι) (f g : SchwartzMap V ℂ), (∀ x, g x = cexp (2 * π * I * (B.repr x i : ℝ)) * f x) → T g = T f) → (∀ (m : ι → ℤ) (f g : SchwartzMap V ℂ), (∀ x, g x = f (x + ∑ i, (m i : ℝ) • B i)) → T g = T f) → ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * ∑' m : ι → ℤ, f (∑ i, (m i : ℝ) • B i) := by
  intro V _ _ ι _ B T h1 h2
  haveI : FiniteDimensional ℝ V := Module.Finite.of_basis B
  let e := Fintype.equivFin ι
  let C := B.reindex e
  let Cc : V ≃L[ℝ] (Fin (Fintype.card ι) → ℝ) := C.equivFun.toContinuousLinearEquiv
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ Cc
  have hP : ∀ (f : SchwartzMap (Fin (Fintype.card ι) → ℝ) ℂ) x, P f x = f (Cc x) := fun _ _ => rfl
  have hCc : ∀ x i, Cc x i = B.repr x (e.symm i) := fun x i => by
    simp [Cc, C, Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply]
  have hsum : ∀ m : ι → ℤ, Cc (∑ i, (m i : ℝ) • B i) = fun j => (m (e.symm j) : ℝ) := fun m => by
    funext j
    rw [hCc, B.repr_sum_self]
  have hA : ∀ (i : Fin (Fintype.card ι)) (f g : SchwartzMap (Fin (Fintype.card ι) → ℝ) ℂ),
      (∀ x, g x = cexp (2 * π * I * x i) * f x) → (T.comp P) g = (T.comp P) f := by
    intro i f g h
    refine h1 (e.symm i) (P f) (P g) fun x => ?_
    rw [hP, hP, h, hCc]
  have hC : ∀ (m : Fin (Fintype.card ι) → ℤ) (f g : SchwartzMap (Fin (Fintype.card ι) → ℝ) ℂ),
      (∀ x, g x = f (x + fun i => (m i : ℝ))) → (T.comp P) g = (T.comp P) f := by
    intro m f g h
    refine h2 (fun i => m (e i)) (P f) (P g) fun x => ?_
    rw [hP, hP, h]
    congr 1
    rw [map_add, hsum]
    simp
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.DiracComb.eq_mul_comb _ (T.comp P) hA hC
  refine ⟨a, fun f => ?_⟩
  let Q := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ Cc.symm
  have hPQ : P (Q f) = f := by
    ext x
    show f (Cc.symm (Cc x)) = f x
    rw [Cc.symm_apply_apply]
  have h3 := ha (Q f)
  rw [ContinuousLinearMap.comp_apply, hPQ] at h3
  rw [h3]
  congr 1
  refine Eq.trans ?_ ((Equiv.arrowCongr e (Equiv.refl ℤ)).symm.tsum_eq fun m => f (∑ i, (m i : ℝ) • B i))
  refine tsum_congr fun m => ?_
  show f (Cc.symm _) = _
  congr 1
  rw [ContinuousLinearEquiv.symm_apply_eq, hsum]
  simp [Equiv.arrowCongr]

def levelSub (F : Type) [Field F] [NumberField F] (κ : Type) (N : ℕ) : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ i, ∃ u : FiniteAdeleRing (𝓞 F) F, (∀ v, u v ∈ v.adicCompletionIntegers F) ∧ x i = N • u}
  zero_mem' := fun i => ⟨0, fun v => zero_mem (v.adicCompletionIntegers F), by simp⟩
  add_mem' := by
    rintro x y hx hy i
    obtain ⟨u, hu, h⟩ := hx i
    obtain ⟨w, hw, h'⟩ := hy i
    exact ⟨u + w, (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).add_mem hu hw, by rw [Pi.add_apply, h, h', nsmul_add]⟩
  neg_mem' := by
    rintro x hx i
    obtain ⟨u, hu, h⟩ := hx i
    exact ⟨-u, (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).neg_mem hu, by rw [Pi.neg_apply, h, smul_neg]⟩

/- English proof (translation)
Use `AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN`. Use `Filter.mem_of_superset (set_pi_mem_nhds Set.finite_univ fun i _ => h) fun x hx i => ?_` and prove the remaining obligations. Conclude with `hx i (Set.mem_univ i)`.
-/
theorem levelSub_isOpen (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {N : ℕ} (hN : 0 < N) :
    IsOpen (levelSub F κ N : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  refine AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_
  have h := GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN
  refine Filter.mem_of_superset (set_pi_mem_nhds Set.finite_univ fun i _ => h) fun x hx i => ?_
  exact hx i (Set.mem_univ i)

/- English proof (translation)
Establish `h : IsCompact ((fun u : FiniteAdeleRing (𝓞 F) F => N • u) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)))` using `(GroundTheory.Global.isCompact_integralFiniteAdeles (K := F)).image (continuous_id.nsmul N)`. Use `isCompact_univ_pi fun _ : κ => h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx i _`.

Take `⟨u, hu, e⟩` from `hx i`. Conclude with `⟨u, hu, e.symm⟩`. Introduce `hx i`. Take `⟨u, hu, e⟩` from `hx i (Set.mem_univ i)`. Conclude with `⟨u, hu, e.symm⟩`.
-/
theorem levelSub_isCompact (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) :
    IsCompact (levelSub F κ N : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have h : IsCompact ((fun u : FiniteAdeleRing (𝓞 F) F => N • u) ''
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) :=
    (GroundTheory.Global.isCompact_integralFiniteAdeles (K := F)).image (continuous_id.nsmul N)
  convert isCompact_univ_pi fun _ : κ => h using 1
  ext x
  constructor
  · intro hx i _
    obtain ⟨u, hu, e⟩ := hx i
    exact ⟨u, hu, e.symm⟩
  · intro hx i
    obtain ⟨u, hu, e⟩ := hx i (Set.mem_univ i)
    exact ⟨u, hu, e.symm⟩

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[GroundTheory.Automorphic.GJMatrix.cosetInd_apply, cosetInd]`. Rewrite using `[Set.indicator_apply]`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Use `forall_congr' fun i => exists_congr fun u => and_congr_right fun _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.sub_apply, sub_eq_iff_eq_add']`.
-/
theorem cosetInd_eq (F : Type) [Field F] [NumberField F] {κ : Type} (N : ℕ) (d : κ → F) :
    cosetInd F N d = GroundTheory.Automorphic.GJMatrix.cosetInd (levelSub F κ N)
      (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i)) := by
  funext x
  rw [GroundTheory.Automorphic.GJMatrix.cosetInd_apply, cosetInd]
  rw [Set.indicator_apply]
  refine if_congr ?_ rfl rfl
  refine forall_congr' fun i => exists_congr fun u => and_congr_right fun _ => ?_
  rw [Pi.sub_apply, sub_eq_iff_eq_add']

/- English proof (translation)
Introduce `F _ _ κ _ N hN d`. Rewrite using `[cosetInd_eq]`. Use `set c : κ → FiniteAdeleRing (𝓞 F) F := fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i)`. Establish `hop` using `levelSub_isOpen F κ hN`. Establish `hS : IsClopen ((fun x => x - c) ⁻¹' (levelSub F κ N : Set (κ → FiniteAdeleRing (𝓞 F) F)))` using `⟨(AddSubgroup.isClosed_of_isOpen _ hop).preimage (continuous_id.sub continuous_const), hop.preimage (continuous_id.sub continuous_const)⟩`.

Establish `e : GroundTheory.Automorphic.GJMatrix.cosetInd (levelSub F κ N) c = ⇑(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hS)`. Use function extensionality and compare the values at `x`. Rewrite using `[GroundTheory.Automorphic.GJMatrix.cosetInd_apply, LocallyConstant.indicator_apply_eq_if]`. Conclude with `if_congr Iff.rfl rfl rfl`. Use `⟨e ▸ LocallyConstant.isLocallyConstant _, ?_⟩` and prove the remaining obligations.

Establish `hK : IsCompact ((fun x => x - c) ⁻¹' (levelSub F κ N : Set (κ → FiniteAdeleRing (𝓞 F) F)))` using `(Homeomorph.subRight c).isCompact_preimage.2 (levelSub_isCompact F κ N)`. Use `HasCompactSupport.intro hK fun x hx => ?_` and prove the remaining obligations. Rewrite using `[GroundTheory.Automorphic.GJMatrix.cosetInd_apply, if_neg (show ¬ (x - c ∈ levelSub F κ N) from hx)]`.
-/
theorem cosetInd_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ), 0 < N → ∀ d : κ → F, cosetInd F N d ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ κ _ N hN d
  rw [cosetInd_eq]
  set c : κ → FiniteAdeleRing (𝓞 F) F := fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i)
  have hop := levelSub_isOpen F κ hN
  have hS : IsClopen ((fun x => x - c) ⁻¹' (levelSub F κ N : Set (κ → FiniteAdeleRing (𝓞 F) F))) :=
    ⟨(AddSubgroup.isClosed_of_isOpen _ hop).preimage (continuous_id.sub continuous_const),
      hop.preimage (continuous_id.sub continuous_const)⟩
  have e : GroundTheory.Automorphic.GJMatrix.cosetInd (levelSub F κ N) c =
      ⇑(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hS) := by
    funext x
    rw [GroundTheory.Automorphic.GJMatrix.cosetInd_apply, LocallyConstant.indicator_apply_eq_if]
    exact if_congr Iff.rfl rfl rfl
  refine ⟨e ▸ LocallyConstant.isLocallyConstant _, ?_⟩
  have hK : IsCompact ((fun x => x - c) ⁻¹' (levelSub F κ N : Set (κ → FiniteAdeleRing (𝓞 F) F))) :=
    (Homeomorph.subRight c).isCompact_preimage.2 (levelSub_isCompact F κ N)
  refine HasCompactSupport.intro hK fun x hx => ?_
  rw [GroundTheory.Automorphic.GJMatrix.cosetInd_apply, if_neg (show ¬ (x - c ∈ levelSub F κ N) from hx)]

/- English proof (translation)
Rewrite `hW` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hsub⟩` from `hW`. Use `choose M hM hMt using fun i => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F (t i) (ht i)`. Use `⟨∏ i, M i, Finset.prod_pos fun i _ => hM i, fun x hx => hsub fun i _ => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, e⟩` from `hx i`.

Rewrite using `[e, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_smul]`. Conclude with `hMt i _ (nsmul_mem (show u ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F from hu) _)`.
-/
theorem levelSub_basis (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (W : Set (κ → FiniteAdeleRing (𝓞 F) F)) (hW : W ∈ nhds (0 : κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ N : ℕ, 0 < N ∧ (levelSub F κ N : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ W := by
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, t, ht, hsub⟩ := hW
  choose M hM hMt using fun i => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F (t i) (ht i)
  refine ⟨∏ i, M i, Finset.prod_pos fun i _ => hM i, fun x hx => hsub fun i _ => ?_⟩
  obtain ⟨u, hu, e⟩ := hx i
  rw [e, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_smul]
  exact hMt i _ (nsmul_mem (show u ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F from hu) _)

/- English proof (translation)
Take `⟨r, rfl⟩` from `h`. Introduce `x hx i`. Take `⟨u, hu, e⟩` from `hx i`. Conclude with `⟨r • u, nsmul_mem (show u ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F from hu) _, by rw [e, mul_smul]⟩`.
-/
theorem levelSub_anti (F : Type) [Field F] [NumberField F] (κ : Type) {M N : ℕ} (h : M ∣ N) :
    levelSub F κ N ≤ levelSub F κ M := by
  obtain ⟨r, rfl⟩ := h
  intro x hx i
  obtain ⟨u, hu, e⟩ := hx i
  exact ⟨r • u, nsmul_mem (show u ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F from hu) _, by rw [e, mul_smul]⟩

/- English proof (translation)
Introduce `F _ _ κ _ g hg`. Take `⟨H, ⟨N₀, hN₀, rfl⟩, hinv⟩` from `GroundTheory.Automorphic.GJMatrix.exists_mem_forall_add_eq (𝓗 := {H | ∃ N : ℕ, 0 < N ∧ H = levelSub F κ N}) (by rintro _ ⟨N, hN, rfl⟩; exact levelSub_isOpen F κ hN) (fun W hW => by`. Take `⟨N, hN, h⟩` from `levelSub_basis F κ W hW`. Conclude with `⟨_, ⟨N, hN, rfl⟩, h⟩) hg.1 hg.2`. Use `⟨N₀, hN₀, fun N hN hd => ?_⟩` and prove the remaining obligations.

Take `⟨s, hs⟩` from `GroundTheory.Automorphic.GJMatrix.exists_eq_sum_cosetInd (levelSub_isOpen F κ hN) hg.2 fun x h hh => hinv x h (levelSub_anti F κ hd hh)`. Rewrite using `[hs]`. Use `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Use `choose d u hu e using fun i => GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F N hN (a i)`. Use `⟨d, ?_⟩` and prove the remaining obligations.

Use `show cosetInd F N d = _`. Rewrite using `[cosetInd_eq]`. Use function extensionality and compare the values at `x`. Rewrite using `[GroundTheory.Automorphic.GJMatrix.cosetInd_apply, GroundTheory.Automorphic.GJMatrix.cosetInd_apply]`. Establish `hm : a - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i)) ∈ levelSub F κ N` using `fun i => ⟨u i, hu i, by rw [Pi.sub_apply, e i, add_sub_cancel_left]⟩`.

Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Establish `e2 : x - a = (x - fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i)) - (a - fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i))` using `by abel`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[e2]`.

Conclude with `sub_mem h hm`. Introduce `h`. Establish `h3` using `add_mem h hm`. Rewrite `h3` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem mem_span_cosetInd : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → g ∈ Submodule.span ℂ (Set.range fun d : κ → F => cosetInd F N d) := by
  intro F _ _ κ _ g hg
  obtain ⟨H, ⟨N₀, hN₀, rfl⟩, hinv⟩ := GroundTheory.Automorphic.GJMatrix.exists_mem_forall_add_eq
    (𝓗 := {H | ∃ N : ℕ, 0 < N ∧ H = levelSub F κ N})
    (by rintro _ ⟨N, hN, rfl⟩; exact levelSub_isOpen F κ hN)
    (fun W hW => by
      obtain ⟨N, hN, h⟩ := levelSub_basis F κ W hW
      exact ⟨_, ⟨N, hN, rfl⟩, h⟩) hg.1 hg.2
  refine ⟨N₀, hN₀, fun N hN hd => ?_⟩
  obtain ⟨s, hs⟩ := GroundTheory.Automorphic.GJMatrix.exists_eq_sum_cosetInd (levelSub_isOpen F κ hN) hg.2
    fun x h hh => hinv x h (levelSub_anti F κ hd hh)
  rw [hs]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  choose d u hu e using fun i => GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F N hN (a i)
  refine ⟨d, ?_⟩
  show cosetInd F N d = _
  rw [cosetInd_eq]
  funext x
  rw [GroundTheory.Automorphic.GJMatrix.cosetInd_apply, GroundTheory.Automorphic.GJMatrix.cosetInd_apply]
  have hm : a - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i)) ∈ levelSub F κ N := fun i =>
    ⟨u i, hu i, by rw [Pi.sub_apply, e i, add_sub_cancel_left]⟩
  refine if_congr ?_ rfl rfl
  have e2 : x - a = (x - fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i)) -
      (a - fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i)) := by abel
  constructor
  · intro h
    rw [e2]
    exact sub_mem h hm
  · intro h
    have h3 := add_mem h hm
    rwa [sub_add_sub_cancel] at h3

/- English proof (translation)
Introduce `F _ _ ψ hψ h1 hn hF N hN φ hφ`. Establish `hmem : ∀ x, ψ x ∈ Submonoid.unitSphere ℂ` using `fun x => mem_sphere_zero_iff_norm.2 (hn x)`. Set `ψ' : AddChar (AdeleRing (𝓞 F) F) Circle` to `{ toFun := fun x => (⟨ψ x, hmem x⟩ : Submonoid.unitSphere ℂ) map_zero_eq_one' := Circle.ext (AddChar.map_zero_eq_one ψ) map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ a b) }`. Establish `hcoe : ∀ x, ((ψ' x : Circle) : ℂ) = ψ x` using `fun _ => rfl`. Establish `hψ' : Continuous ψ'` using `hψ.subtype_mk hmem`.

Take `⟨c, hc, -⟩` from `GroundTheory.Global.existsUnique_eq_adelicChar_mul ψ' hψ' (fun k => Circle.ext (by rw [hcoe, hF]; rfl))`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Apply `h1` to reduce the goal to its premises. Use extensionality with `x`.

Establish `h2` using `hc x`. Rewrite `h2` using `[map_zero, zero_mul, AddChar.map_zero_eq_one]`. Rewrite using `[← hcoe, h2]`. Both sides reduce to the same expression. Set `χ : AddChar (mixedEmbedding.mixedSpace F) Circle` to `Real.fourierChar.compAddMonoidHom (N • φ).toAddMonoidHom`.

Establish `hχa : ∀ m, χ m = Real.fourierChar (φ (N • m))` using `fun m => by show Real.fourierChar ((N • φ) m) = _`. Use `congr 1`. Rewrite using `[LinearMap.smul_apply, map_nsmul φ]`. Establish `hχ : Continuous χ` using `Real.continuous_fourierChar.comp (LinearMap.continuous_of_finiteDimensional (N • φ))`. Establish `hχ1 : ∀ a : 𝓞 F, χ (mixedEmbedding F (algebraMap (𝓞 F) F a)) = 1` using `fun a => by`.

Take `⟨k, hk⟩` from `hφ a`. Rewrite using `[hχa, show algebraMap (𝓞 F) F a = (a : F) from rfl, hk, Real.fourierChar_apply', Circle.exp_eq_one]`. Conclude with `⟨k, by ring⟩`. Take `⟨ξ, hξO, hξ⟩` from `GroundTheory.Global.exists_mixedSpace_char_eq χ hχ hχ1`. Establish `hNF : (N : F) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`.

Use `⟨ξ / (N * c), ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨u, hu, hx⟩`. Use `set x' : AdeleRing (𝓞 F) F := algebraMap F (AdeleRing (𝓞 F) F) (N : F)⁻¹ * x with hx'`. Establish `e1 : algebraMap F (AdeleRing (𝓞 F) F) c * (x * algebraMap F (AdeleRing (𝓞 F) F) (ξ / (N * c))) = algebraMap F (AdeleRing (𝓞 F) F) ξ * x'`. Establish `: c * (ξ / (N * c)) = ξ * (N : F)⁻¹` using `by field_simp`.

Rewrite using `[hx', mul_left_comm, ← map_mul, this, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : x'.2 = u` using `by show algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * x.2 = u`. Rewrite using `[hx, nsmul_eq_mul, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← mul_assoc, ← map_mul, inv_mul_cancel₀ hNF, map_one, one_mul]`. Establish `hξv : ∀ v : HeightOneSpectrum (𝓞 F), (ξ : v.adicCompletion F) ∈ GroundTheory.Global.localInvDifferent v` using `(GroundTheory.Global.forall_coe_mem_localInvDifferent_iff ξ).mpr hξO`.

Establish `e3 : (algebraMap F (AdeleRing (𝓞 F) F) ξ * x') ∈ GroundTheory.Global.invDifferentAdeles F`. Use `GroundTheory.Global.mem_invDifferentAdeles.mpr fun v => ?_` and prove the remaining obligations. Use `show (ξ : v.adicCompletion F) * x'.2 v ∈ GroundTheory.Global.localInvDifferent v`. Rewrite using `[mul_comm, e2]`. Conclude with `GroundTheory.Global.mul_mem_localInvDifferent (hu v) (hξv v)`.

Use `set m := InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 with hm`. Use `set m' := mixedEmbedding F (N : F)⁻¹ * m with hm'`. Establish `e4 : GroundTheory.Global.infiniteTrace F (algebraMap F (AdeleRing (𝓞 F) F) ξ * x').1 = GroundTheory.Global.mixedTrace F (mixedEmbedding F ξ * m')`. Rewrite using `[← GroundTheory.Global.mixedTrace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply]`. Use `congr 1`.

Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F _ ξ * (algebraMap F _ (N : F)⁻¹ * x.1)) = _`. Rewrite using `[map_mul, map_mul, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]`. Establish `e5 : N • m' = m`. Rewrite using `[hm', ← smul_mul_assoc, ← map_nsmul, nsmul_eq_mul, mul_inv_cancel₀ hNF, map_one, one_mul]`. Establish `e6 : ψ' (x * algebraMap F (AdeleRing (𝓞 F) F) (ξ / (N * c))) = Real.fourierChar (φ m)`.

Rewrite using `[hc, e1, GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles e3, e4, ← hξ, hχa, e5]`. Rewrite using `[← hcoe, e6, Real.fourierChar_apply]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_rat_modulation : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → ∀ (N : ℕ), 0 < N → ∀ φ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ, (∀ a : 𝓞 F, ∃ k : ℤ, φ (N • mixedEmbedding F (a : F)) = k) → ∃ y : F, ∀ x : AdeleRing (𝓞 F) F, (∃ u : FiniteAdeleRing (𝓞 F) F, (∀ v, u v ∈ v.adicCompletionIntegers F) ∧ x.2 = N • u) → ψ (x * algebraMap F (AdeleRing (𝓞 F) F) y) = cexp (2 * π * I * (φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) : ℝ)) := by
  intro F _ _ ψ hψ h1 hn hF N hN φ hφ
  have hmem : ∀ x, ψ x ∈ Submonoid.unitSphere ℂ := fun x => mem_sphere_zero_iff_norm.2 (hn x)
  let ψ' : AddChar (AdeleRing (𝓞 F) F) Circle :=
    { toFun := fun x => (⟨ψ x, hmem x⟩ : Submonoid.unitSphere ℂ)
      map_zero_eq_one' := Circle.ext (AddChar.map_zero_eq_one ψ)
      map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ a b) }
  have hcoe : ∀ x, ((ψ' x : Circle) : ℂ) = ψ x := fun _ => rfl
  have hψ' : Continuous ψ' := hψ.subtype_mk hmem
  obtain ⟨c, hc, -⟩ := GroundTheory.Global.existsUnique_eq_adelicChar_mul ψ' hψ'
    (fun k => Circle.ext (by rw [hcoe, hF]; rfl))
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h1
    ext x
    have h2 := hc x
    rw [map_zero, zero_mul, AddChar.map_zero_eq_one] at h2
    rw [← hcoe, h2]
    rfl
  let χ : AddChar (mixedEmbedding.mixedSpace F) Circle :=
    Real.fourierChar.compAddMonoidHom (N • φ).toAddMonoidHom
  have hχa : ∀ m, χ m = Real.fourierChar (φ (N • m)) := fun m => by
    show Real.fourierChar ((N • φ) m) = _
    congr 1
    rw [LinearMap.smul_apply, map_nsmul φ]
  have hχ : Continuous χ := Real.continuous_fourierChar.comp (LinearMap.continuous_of_finiteDimensional (N • φ))
  have hχ1 : ∀ a : 𝓞 F, χ (mixedEmbedding F (algebraMap (𝓞 F) F a)) = 1 := fun a => by
    obtain ⟨k, hk⟩ := hφ a
    rw [hχa, show algebraMap (𝓞 F) F a = (a : F) from rfl, hk, Real.fourierChar_apply', Circle.exp_eq_one]
    exact ⟨k, by ring⟩
  obtain ⟨ξ, hξO, hξ⟩ := GroundTheory.Global.exists_mixedSpace_char_eq χ hχ hχ1
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine ⟨ξ / (N * c), ?_⟩
  rintro x ⟨u, hu, hx⟩
  set x' : AdeleRing (𝓞 F) F := algebraMap F (AdeleRing (𝓞 F) F) (N : F)⁻¹ * x with hx'
  have e1 : algebraMap F (AdeleRing (𝓞 F) F) c * (x * algebraMap F (AdeleRing (𝓞 F) F) (ξ / (N * c))) = algebraMap F (AdeleRing (𝓞 F) F) ξ * x' := by
    have : c * (ξ / (N * c)) = ξ * (N : F)⁻¹ := by field_simp
    rw [hx', mul_left_comm, ← map_mul, this, map_mul]
    ring
  have e2 : x'.2 = u := by
    show algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * x.2 = u
    rw [hx, nsmul_eq_mul, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ hNF, map_one, one_mul]
  have hξv : ∀ v : HeightOneSpectrum (𝓞 F), (ξ : v.adicCompletion F) ∈ GroundTheory.Global.localInvDifferent v :=
    (GroundTheory.Global.forall_coe_mem_localInvDifferent_iff ξ).mpr hξO
  have e3 : (algebraMap F (AdeleRing (𝓞 F) F) ξ * x') ∈ GroundTheory.Global.invDifferentAdeles F := by
    refine GroundTheory.Global.mem_invDifferentAdeles.mpr fun v => ?_
    show (ξ : v.adicCompletion F) * x'.2 v ∈ GroundTheory.Global.localInvDifferent v
    rw [mul_comm, e2]
    exact GroundTheory.Global.mul_mem_localInvDifferent (hu v) (hξv v)
  set m := InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 with hm
  set m' := mixedEmbedding F (N : F)⁻¹ * m with hm'
  have e4 : GroundTheory.Global.infiniteTrace F (algebraMap F (AdeleRing (𝓞 F) F) ξ * x').1 =
      GroundTheory.Global.mixedTrace F (mixedEmbedding F ξ * m') := by
    rw [← GroundTheory.Global.mixedTrace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply]
    congr 1
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F _ ξ * (algebraMap F _ (N : F)⁻¹ * x.1)) = _
    rw [map_mul, map_mul, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  have e5 : N • m' = m := by
    rw [hm', ← smul_mul_assoc, ← map_nsmul, nsmul_eq_mul, mul_inv_cancel₀ hNF, map_one, one_mul]
  have e6 : ψ' (x * algebraMap F (AdeleRing (𝓞 F) F) (ξ / (N * c))) = Real.fourierChar (φ m) := by
    rw [hc, e1, GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles e3, e4, ← hξ, hχa, e5]
  rw [← hcoe, e6, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/- English proof (translation)
Unfold `pureA`. Use `congr 2`. Use function extensionality and compare the values at `i`. Rewrite using `[InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]`. Both sides reduce to the same expression.
-/
theorem pureA_algebraMap' (F : Type) [Field F] [NumberField F] {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (ξ : κ → F) :
    pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) =
      f (fun i => mixedEmbedding F (ξ i)) * g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) := by
  unfold pureA
  congr 2
  funext i
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

/- English proof (translation)
Take `⟨y, hy⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => by`. Use `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx v)` as an intermediate fact. Rewrite `this` using `[FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Then use the resulting hypothesis. Conclude with `⟨y, hy.symm⟩`.
-/
theorem int_of_integral (F : Type) [Field F] [NumberField F] (x : F)
    (hx : ∀ v, (algebraMap F (FiniteAdeleRing (𝓞 F) F) x) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) :
    ∃ y : 𝓞 F, x = y := by
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => by
    have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hx v)
    rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  exact ⟨y, hy.symm⟩

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
The claim follows from `HeightOneSpectrum.coe_mem_adicCompletionIntegers v k`.
-/
theorem natCast_integral (k : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (k : F)) v ∈ v.adicCompletionIntegers F :=
  HeightOneSpectrum.coe_mem_adicCompletionIntegers v k

def InCoset {κ : Type} (N : ℕ) (d : κ → F) (x : κ → FiniteAdeleRing (𝓞 F) F) : Prop :=
  ∀ i, ∃ u : FiniteAdeleRing (𝓞 F) F, (∀ v, u v ∈ v.adicCompletionIntegers F) ∧
    x i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i) + N • u

/- English proof (translation)
Unfold `cosetInd`. Rewrite using `[Set.indicator_apply]`. Both sides reduce to the same expression.
-/
theorem cosetInd_apply {κ : Type} (N : ℕ) (d : κ → F) (x : κ → FiniteAdeleRing (𝓞 F) F) :
    cosetInd F N d x = if InCoset F N d x then 1 else 0 := by
  unfold cosetInd
  rw [Set.indicator_apply]
  rfl

/- English proof (translation)
Establish `: InCoset F N d (fun i => x i + algebraMap F _ (d i)) ↔ InCoset F N 0 x`. Use `forall_congr' fun i => exists_congr fun u => and_congr_right fun _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.zero_apply, map_zero, zero_add]`. Rewrite using `[add_comm, add_right_inj]`. Rewrite using `[cosetInd_apply, cosetInd_apply]`.

Conclude with `if_congr this rfl rfl`.
-/
theorem cosetInd_add {κ : Type} (N : ℕ) (d : κ → F) (x : κ → FiniteAdeleRing (𝓞 F) F) :
    cosetInd F N d (fun i => x i + algebraMap F _ (d i)) = cosetInd F N 0 x := by
  have : InCoset F N d (fun i => x i + algebraMap F _ (d i)) ↔ InCoset F N 0 x := by
    refine forall_congr' fun i => exists_congr fun u => and_congr_right fun _ => ?_
    simp only [Pi.zero_apply, map_zero, zero_add]
    rw [add_comm, add_right_inj]
  rw [cosetInd_apply, cosetInd_apply]
  exact if_congr this rfl rfl

/- English proof (translation)
Establish `: InCoset F N 0 (fun i => x i + algebraMap F _ (N • (a i : F))) ↔ InCoset F N 0 x`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Simplify using `only [Pi.zero_apply, map_zero, zero_add, map_nsmul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, h⟩`.

Conclude with `⟨u - algebraMap F _ (a i : F), fun v => sub_mem (hu v) (natCast_integral F _ v), by rw [nsmul_sub, ← h, add_sub_cancel_right]⟩`. Introduce and unpack `⟨u, hu, h⟩`. Conclude with `⟨u + algebraMap F _ (a i : F), fun v => add_mem (hu v) (natCast_integral F _ v), by rw [nsmul_add, h]⟩`. Rewrite using `[cosetInd_apply, cosetInd_apply]`. Conclude with `if_congr this rfl rfl`.
-/
theorem cosetInd_add_lattice {κ : Type} (N : ℕ) (a : κ → 𝓞 F) (x : κ → FiniteAdeleRing (𝓞 F) F) :
    cosetInd F N 0 (fun i => x i + algebraMap F _ (N • (a i : F))) = cosetInd F N 0 x := by
  have : InCoset F N 0 (fun i => x i + algebraMap F _ (N • (a i : F))) ↔ InCoset F N 0 x := by
    refine forall_congr' fun i => ?_
    simp only [Pi.zero_apply, map_zero, zero_add, map_nsmul]
    constructor
    · rintro ⟨u, hu, h⟩
      exact ⟨u - algebraMap F _ (a i : F), fun v => sub_mem (hu v) (natCast_integral F _ v),
        by rw [nsmul_sub, ← h, add_sub_cancel_right]⟩
    · rintro ⟨u, hu, h⟩
      exact ⟨u + algebraMap F _ (a i : F), fun v => add_mem (hu v) (natCast_integral F _ v),
        by rw [nsmul_add, h]⟩
  rw [cosetInd_apply, cosetInd_apply]
  exact if_congr this rfl rfl

/- English proof (translation)
Establish `hN' : (N : F) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: ∀ i, ∃ a : 𝓞 F, ξ i = N • (a : F)` using `fun i => by`. Take `⟨u, hu, h⟩` from `h i`.

Simplify using `only [Pi.zero_apply, map_zero, zero_add] at h`. Establish `e : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((N : F)⁻¹ * ξ i) = u`. Rewrite using `[map_mul, h, nsmul_eq_mul, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← mul_assoc, ← map_mul, inv_mul_cancel₀ hN', map_one, one_mul]`. Take `⟨a, ha⟩` from `int_of_integral F _ (e ▸ hu)`. Conclude with `⟨a, by rw [← ha, nsmul_eq_mul, mul_inv_cancel_left₀ hN']⟩`.

Use `choose a ha using this`. Conclude with `⟨a, funext ha⟩`. Introduce and unpack `⟨a, rfl⟩ i`. Conclude with `⟨_, natCast_integral F (a i), by simp only [Pi.zero_apply, map_zero, zero_add, map_nsmul]⟩`.
-/
theorem inCoset_rat_iff {κ : Type} {N : ℕ} (hN : 0 < N) (ξ : κ → F) :
    InCoset F N 0 (fun i => algebraMap F _ (ξ i)) ↔ ∃ a : κ → 𝓞 F, ξ = fun i => N • (a i : F) := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  constructor
  · intro h
    have : ∀ i, ∃ a : 𝓞 F, ξ i = N • (a : F) := fun i => by
      obtain ⟨u, hu, h⟩ := h i
      simp only [Pi.zero_apply, map_zero, zero_add] at h
      have e : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((N : F)⁻¹ * ξ i) = u := by
        rw [map_mul, h, nsmul_eq_mul, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← mul_assoc,
          ← map_mul, inv_mul_cancel₀ hN', map_one, one_mul]
      obtain ⟨a, ha⟩ := int_of_integral F _ (e ▸ hu)
      exact ⟨a, by rw [← ha, nsmul_eq_mul, mul_inv_cancel_left₀ hN']⟩
    choose a ha using this
    exact ⟨a, funext ha⟩
  · rintro ⟨a, rfl⟩ i
    exact ⟨_, natCast_integral F (a i), by simp only [Pi.zero_apply, map_zero, zero_add, map_nsmul]⟩

/- English proof (translation)
Unfold `pureA`. Use `congr 2`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.add_apply, Pi.add_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← map_add]`. Both sides reduce to the same expression.
-/
theorem pureA_add_rat {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (d : κ → F) (x : κ → AdeleRing (𝓞 F) F) :
    pureA F f g (x + fun i => algebraMap F (AdeleRing (𝓞 F) F) (d i)) =
      f ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + fun i => mixedEmbedding F (d i)) *
        g (fun i => (x i).2 + algebraMap F _ (d i)) := by
  unfold pureA
  congr 2
  funext i
  rw [Pi.add_apply, Pi.add_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← map_add]
  rfl

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨f, g, hg, rfl⟩`.
-/
theorem pureA_mem {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩

/- English proof (translation)
Unfold `thetaSum`. Use `Eq.trans (tsum_congr fun ξ => congrArg Φ (funext fun i => ?_)) ((Equiv.addRight d).tsum_eq fun ξ => Φ fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem thetaSum_translate {κ : Type} (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (d : κ → F) :
    thetaSum F (fun x => Φ (x + fun i => algebraMap F (AdeleRing (𝓞 F) F) (d i))) = thetaSum F Φ := by
  unfold thetaSum
  refine Eq.trans (tsum_congr fun ξ => congrArg Φ (funext fun i => ?_))
    ((Equiv.addRight d).tsum_eq fun ξ => Φ fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
  simp

/- English proof (translation)
The claim follows from `((GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F κ).1 Φ hΦ).of_norm.tsum_add ((GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F κ).1 Ψ hΨ).of_norm`.
-/
theorem thetaAdd [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] {κ : Type} [Fintype κ]
    {Φ Ψ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΨ : Ψ ∈ schA F κ) :
    thetaSum F (Φ + Ψ) = thetaSum F Φ + thetaSum F Ψ :=
  ((GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F κ).1 Φ hΦ).of_norm.tsum_add ((GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F κ).1 Ψ hΨ).of_norm

/- English proof (translation)
The claim follows from `tsum_mul_left`.
-/
theorem thetaSmul {κ : Type} (c : ℂ) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    thetaSum F (c • Φ) = c * thetaSum F Φ :=
  tsum_mul_left

section Level

variable {F} [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] {κ : Type} [Fintype κ]
  {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {l : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ}

/- English proof (translation)
Establish `hN' : (N : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Establish `hsb` using `cosetInd_mem_SB F κ N hN 0`. Take `⟨T, hT⟩` from `hl _ hsb`. Set `b` to `(mixedEmbedding.latticeBasis F).isUnitSMul (w := fun _ => (N : ℝ)) fun _ => hN'.isUnit`. Set `ω` to `RingOfIntegers.basis F`.

Establish `hb : ∀ j, b j = N • mixedEmbedding F (ω j : F)` using `fun j => by`. Rewrite using `[Module.Basis.isUnitSMul_apply, mixedEmbedding.latticeBasis_apply, integralBasis_apply, Nat.cast_smul_eq_nsmul]`. Establish `hsum : ∀ m : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ j, (m j : ℝ) • b j = N • mixedEmbedding F ((∑ j, m j • ω j : 𝓞 F) : F)` using `fun m => by`. Rewrite using `[show ((∑ j, m j • ω j : 𝓞 F) : F) = algebraMap (𝓞 F) F (∑ j, m j • ω j) from rfl, map_sum, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hb, map_zsmul, map_zsmul, Int.cast_smul_eq_zsmul, smul_comm]`. Set `B` to `Pi.basis fun _ : κ => b`. Set `e : ((Σ _ : κ, Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → ℤ) → κ → 𝓞 F` to `fun m i => ∑ j, m ⟨i, j⟩ • ω j`. Establish `hB : ∀ m, ∑ p, (m p : ℝ) • B p = fun i => mixedEmbedding F (N • (e m i : F))` using `fun m => by`. Use function extensionality and compare the values at `i`.

Rewrite using `[map_nsmul, ← hsum, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single i]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[B]`. Introduce `k _ hk`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Simplify using `[B, Pi.single_eq_of_ne hk.symm]`. Simplify using the standard rewrite rules. Establish `hA : ∀ (p : Σ _ : κ, Module.Free.ChooseBasisIndex ℤ (𝓞 F)) (f g : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), (∀ x, g x = cexp (2 * π * I * (B.repr x p : ℝ)) * f x) → T g = T f`. Introduce `p f g h`. Take `⟨y, hy⟩` from `exists_rat_modulation F ψ hψ h1 hn hF N hN (b.coord p.2) fun a => ⟨ω.repr a p.2, by`.

Establish `e2 : N • mixedEmbedding F (a : F) = ∑ j, ((ω.repr a j : ℤ) : ℝ) • b j`. Rewrite using `[hsum, ω.sum_repr]`. Rewrite using `[e2, Module.Basis.coord_apply, b.repr_sum_self]⟩`. Rewrite using `[← hT, ← hT, ← hmod p.1 y _ (pureA_mem F f hsb)]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Unfold `pureA`. Rewrite using `[cosetInd_apply]`. Use `split_ifs with hx`. Take `⟨u, hu, hx⟩` from `hx p.1`.

Rewrite using `[hy (x p.1) ⟨u, hu, by simpa using hx⟩, h, mul_assoc]`. Simplify using `[B]`. Simplify using the standard rewrite rules. Establish `hC : ∀ (m : (Σ _ : κ, Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → ℤ) (f g : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), (∀ x, g x = f (x + ∑ p, (m p : ℝ) • B p)) → T g = T f`. Introduce `m f g h`.

Rewrite using `[← hT, ← hT, ← htr (fun i => N • (e m i : F)) _ (pureA_mem F f hsb)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[pureA_add_rat, cosetInd_add_lattice, ← hB, ← h]`. Both sides reduce to the same expression.

Take `⟨c, hc⟩` from `comb_of_basis _ _ B T hA hC`. Use `⟨c, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[hT, hc]`. Use `congr 1`. Unfold `thetaSum`.

Establish `hinj : Function.Injective fun m i => N • (e m i : F)` using `fun m m' h => by`. Use function extensionality and compare the values at `⟨i, j⟩`. Establish `h2 : e m i = e m' i` using `Subtype.ext (smul_right_injective F hN.ne' (congrFun h i))`. Establish `a1` using `congrFun (ω.repr_sum_self fun c => m ⟨i, c⟩) j`. Establish `a2` using `congrFun (ω.repr_sum_self fun c => m' ⟨i, c⟩) j`.

Rewrite using `[← a1, ← a2]`. Conclude with `congrArg (fun z => ω.repr z j) h2`. Rewrite using `[← hinj.tsum_eq]`. Use `tsum_congr fun m => ?_` and prove the remaining obligations. Rewrite using `[pureA_algebraMap', hB, cosetInd_apply, if_pos ((inCoset_rat_iff F hN _).2 ⟨_, rfl⟩), mul_one]`.

Introduce `ξ hξ`. Rewrite `hξ` using `[Function.mem_support, pureA_algebraMap', cosetInd_apply]`. Distinguish the cases in `h : InCoset F N 0 (fun i => algebraMap F _ (ξ i))`. Take `⟨a, rfl⟩` from `(inCoset_rat_iff F hN _).1 h`. Use `⟨fun p => ω.repr (a p.1) p.2, ?_⟩` and prove the remaining obligations.

Simplify using `only [e, Module.Basis.sum_repr]`. Rewrite `hξ` using `[if_neg h, mul_zero]`. Conclude with `absurd rfl hξ`.
-/
theorem level_zero (hψ : Continuous ψ) (h1 : ψ ≠ 1) (hn : ∀ x, ‖ψ x‖ = 1)
    (hF : ∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) (hl : l ∈ (adeleClass F).adm κ)
    (htr : ∀ d : κ → F, ∀ Φ ∈ schA F κ,
      l (fun x => Φ (x + fun i => algebraMap F (AdeleRing (𝓞 F) F) (d i))) = l Φ)
    (hmod : ∀ (i : κ) (y : F), ∀ Φ ∈ schA F κ,
      l (fun x => ψ (x i * algebraMap F (AdeleRing (𝓞 F) F) y) * Φ x) = l Φ)
    {N : ℕ} (hN : 0 < N) : ∃ c : ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      l (pureA F f (cosetInd F N 0)) = c * thetaSum F (pureA F f (cosetInd F N 0)) := by
  classical
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hsb := cosetInd_mem_SB F κ N hN 0
  obtain ⟨T, hT⟩ := hl _ hsb
  let b := (mixedEmbedding.latticeBasis F).isUnitSMul (w := fun _ => (N : ℝ)) fun _ => hN'.isUnit
  let ω := RingOfIntegers.basis F
  have hb : ∀ j, b j = N • mixedEmbedding F (ω j : F) := fun j => by
    rw [Module.Basis.isUnitSMul_apply, mixedEmbedding.latticeBasis_apply, integralBasis_apply,
      Nat.cast_smul_eq_nsmul]
  have hsum : ∀ m : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ,
      ∑ j, (m j : ℝ) • b j = N • mixedEmbedding F ((∑ j, m j • ω j : 𝓞 F) : F) := fun m => by
    rw [show ((∑ j, m j • ω j : 𝓞 F) : F) = algebraMap (𝓞 F) F (∑ j, m j • ω j) from rfl, map_sum, map_sum,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb, map_zsmul, map_zsmul, Int.cast_smul_eq_zsmul, smul_comm]
  let B := Pi.basis fun _ : κ => b
  let e : ((Σ _ : κ, Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → ℤ) → κ → 𝓞 F := fun m i => ∑ j, m ⟨i, j⟩ • ω j
  have hB : ∀ m, ∑ p, (m p : ℝ) • B p = fun i => mixedEmbedding F (N • (e m i : F)) := fun m => by
    funext i
    rw [map_nsmul, ← hsum, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp [B]
    · intro k _ hk
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [B, Pi.single_eq_of_ne hk.symm]
    · simp
  have hA : ∀ (p : Σ _ : κ, Module.Free.ChooseBasisIndex ℤ (𝓞 F)) (f g : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      (∀ x, g x = cexp (2 * π * I * (B.repr x p : ℝ)) * f x) → T g = T f := by
    intro p f g h
    obtain ⟨y, hy⟩ := exists_rat_modulation F ψ hψ h1 hn hF N hN (b.coord p.2) fun a => ⟨ω.repr a p.2, by
      have e2 : N • mixedEmbedding F (a : F) = ∑ j, ((ω.repr a j : ℤ) : ℝ) • b j := by
        rw [hsum, ω.sum_repr]
      rw [e2, Module.Basis.coord_apply, b.repr_sum_self]⟩
    rw [← hT, ← hT, ← hmod p.1 y _ (pureA_mem F f hsb)]
    congr 1
    funext x
    unfold pureA
    rw [cosetInd_apply]
    split_ifs with hx
    · obtain ⟨u, hu, hx⟩ := hx p.1
      rw [hy (x p.1) ⟨u, hu, by simpa using hx⟩, h, mul_assoc]
      simp [B]
    · simp
  have hC : ∀ (m : (Σ _ : κ, Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → ℤ) (f g : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      (∀ x, g x = f (x + ∑ p, (m p : ℝ) • B p)) → T g = T f := by
    intro m f g h
    rw [← hT, ← hT, ← htr (fun i => N • (e m i : F)) _ (pureA_mem F f hsb)]
    congr 1
    funext x
    rw [pureA_add_rat, cosetInd_add_lattice, ← hB, ← h]
    rfl
  obtain ⟨c, hc⟩ := comb_of_basis _ _ B T hA hC
  refine ⟨c, fun f => ?_⟩
  rw [hT, hc]
  congr 1
  unfold thetaSum
  have hinj : Function.Injective fun m i => N • (e m i : F) := fun m m' h => by
    funext ⟨i, j⟩
    have h2 : e m i = e m' i := Subtype.ext (smul_right_injective F hN.ne' (congrFun h i))
    have a1 := congrFun (ω.repr_sum_self fun c => m ⟨i, c⟩) j
    have a2 := congrFun (ω.repr_sum_self fun c => m' ⟨i, c⟩) j
    rw [← a1, ← a2]
    exact congrArg (fun z => ω.repr z j) h2
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun m => ?_
    rw [pureA_algebraMap', hB, cosetInd_apply, if_pos ((inCoset_rat_iff F hN _).2 ⟨_, rfl⟩), mul_one]
  · intro ξ hξ
    rw [Function.mem_support, pureA_algebraMap', cosetInd_apply] at hξ
    by_cases h : InCoset F N 0 (fun i => algebraMap F _ (ξ i))
    · obtain ⟨a, rfl⟩ := (inCoset_rat_iff F hN _).1 h
      refine ⟨fun p => ω.repr (a p.1) p.2, ?_⟩
      simp only [e, Module.Basis.sum_repr]
    · rw [if_neg h, mul_zero] at hξ
      exact absurd rfl hξ

/- English proof (translation)
Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g h`. Take `⟨d, rfl⟩` from `h`. Establish `hm` using `pureA_mem F f (cosetInd_mem_SB F κ N hN d)`. Use `⟨hm, ?_⟩` and prove the remaining obligations.

Establish `e : (fun x => pureA F f (cosetInd F N d) (x + fun i => algebraMap F (AdeleRing (𝓞 F) F) (d i))) = pureA F (SchwartzMap.compSubConstCLM ℂ (-fun i => mixedEmbedding F (d i)) f) (cosetInd F N 0)`. Use function extensionality and compare the values at `x`. Rewrite using `[pureA_add_rat, cosetInd_add]`. Unfold `pureA`. Rewrite using `[SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]`.

Rewrite using `[← htr d _ hm, ← thetaSum_translate F _ d, e, hc]`. Consider the case `zero`. Establish `e : pureA F f (0 : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0` using `by funext x; simp [pureA]`. Rewrite using `[e]`. Conclude with `⟨zero_mem _, by simp [thetaSum]⟩`.

Consider the case `add g g' _ _ h h'`. Establish `e : pureA F f (g + g') = pureA F f g + pureA F f g'` using `by funext x; simp [pureA, mul_add]`. Rewrite using `[e]`. Conclude with `⟨add_mem h.1 h'.1, by rw [map_add, thetaAdd F h.1 h'.1, h.2, h'.2, mul_add]⟩`. Consider the case `smul a g _ h`.

Establish `e : pureA F f (a • g) = a • pureA F f g` using `by funext x; simp [pureA, mul_left_comm]`. Rewrite using `[e]`. Conclude with `⟨Submodule.smul_mem _ _ h.1, by rw [map_smul, thetaSmul, h.2, smul_eq_mul, mul_left_comm]⟩`.
-/
theorem level_span
    (htr : ∀ d : κ → F, ∀ Φ ∈ schA F κ,
      l (fun x => Φ (x + fun i => algebraMap F (AdeleRing (𝓞 F) F) (d i))) = l Φ)
    {N : ℕ} (hN : 0 < N) {c : ℂ} (hc : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      l (pureA F f (cosetInd F N 0)) = c * thetaSum F (pureA F f (cosetInd F N 0)))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ Submodule.span ℂ (Set.range fun d : κ → F => cosetInd F N d)) :
    pureA F f g ∈ schA F κ ∧ l (pureA F f g) = c * thetaSum F (pureA F f g) := by
  induction hg using Submodule.span_induction with
  | mem g h =>
    obtain ⟨d, rfl⟩ := h
    have hm := pureA_mem F f (cosetInd_mem_SB F κ N hN d)
    refine ⟨hm, ?_⟩
    have e : (fun x => pureA F f (cosetInd F N d) (x + fun i => algebraMap F (AdeleRing (𝓞 F) F) (d i))) =
        pureA F (SchwartzMap.compSubConstCLM ℂ (-fun i => mixedEmbedding F (d i)) f) (cosetInd F N 0) := by
      funext x
      rw [pureA_add_rat, cosetInd_add]
      unfold pureA
      rw [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
    rw [← htr d _ hm, ← thetaSum_translate F _ d, e, hc]
  | zero =>
    have e : pureA F f (0 : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0 := by funext x; simp [pureA]
    rw [e]
    exact ⟨zero_mem _, by simp [thetaSum]⟩
  | add g g' _ _ h h' =>
    have e : pureA F f (g + g') = pureA F f g + pureA F f g' := by funext x; simp [pureA, mul_add]
    rw [e]
    exact ⟨add_mem h.1 h'.1, by rw [map_add, thetaAdd F h.1 h'.1, h.2, h'.2, mul_add]⟩
  | smul a g _ h =>
    have e : pureA F f (a • g) = a • pureA F f g := by funext x; simp [pureA, mul_left_comm]
    rw [e]
    exact ⟨Submodule.smul_mem _ _ h.1, by rw [map_smul, thetaSmul, h.2, smul_eq_mul, mul_left_comm]⟩

end Level

/- English proof (translation)
Introduce `F _ _ _ _ κ _ ψ hψ h1 hF l hl hinv`. Establish `hn` using `(GlobalTheory.CompanionTheory.AdeleAnn.unitary_and_annihilator_eq F ψ hψ h1 hF).1`. Establish `htr : ∀ d : κ → F, ∀ Φ ∈ schA F κ, l (fun x => Φ (x + fun i => algebraMap F (AdeleRing (𝓞 F) F) (d i))) = l Φ` using `fun d Φ hΦ => by`. Rewrite using `[← hinv (d, 0) Φ hΦ]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `[schr, dotProduct]`. Establish `hmod : ∀ (i : κ) (y : F), ∀ Φ ∈ schA F κ, l (fun x => ψ (x i * algebraMap F (AdeleRing (𝓞 F) F) y) * Φ x) = l Φ` using `fun i y Φ hΦ => by`. Rewrite using `[← hinv (0, Pi.single i y) Φ hΦ]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Establish `e : (fun j => algebraMap F (AdeleRing (𝓞 F) F) (Pi.single (M` using `fun _ => F) i y j)) = Pi.single i (algebraMap F (AdeleRing (𝓞 F) F) y) := by`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `e0 : (fun j => algebraMap F (AdeleRing (𝓞 F) F) ((0 : κ → F) j)) = 0` using `by funext j; simp`. Simplify using `only [schr, e, e0, dotProduct_single, zero_dotProduct, mul_zero, add_zero]`. Simplify using `only [Pi.zero_apply, zero_mul, mul_zero, add_zero]`.

Use `choose! c hc using fun (N : ℕ) (hN : 0 < N) => level_zero hψ h1 hn hF hl htr hmod hN`. Establish `key : ∀ Φ ∈ schA F κ, ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → l Φ = c N * thetaSum F Φ`. Introduce `Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`.

Take `⟨f, g, hg, rfl⟩` from `h`. Take `⟨N₀, h0, h⟩` from `mem_span_cosetInd F κ g hg`. Conclude with `⟨N₀, h0, fun N hN hd => (level_span htr hN (hc N hN) f (h N hN hd)).2⟩`. Consider the case `zero => exact ⟨1, one_pos, fun N _ _ => by simp [thetaSum]⟩`. Consider the case `add Φ Ψ hΦ hΨ h h'`.

Take `⟨M, hM, h⟩` from `h`. Take `⟨M', hM', h'⟩` from `h'`. Use `⟨M * M', Nat.mul_pos hM hM', fun N hN hd => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, thetaAdd F hΦ hΨ, h N hN ((dvd_mul_right _ _).trans hd), h' N hN ((dvd_mul_left _ _).trans hd), mul_add]`. Consider the case `smul a Φ _ h`.

Take `⟨M, hM, h⟩` from `h`. Use `⟨M, hM, fun N hN hd => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, thetaSmul, h N hN hd, smul_eq_mul, mul_left_comm]`. Distinguish the cases in `h0 : ∃ Φ₀ ∈ schA F κ, thetaSum F Φ₀ ≠ 0`. Take `⟨Φ₀, hΦ₀, h0⟩` from `h0`.

Use `⟨l Φ₀ / thetaSum F Φ₀, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Take `⟨M, hM, h⟩` from `key Φ hΦ`. Take `⟨M', hM', h'⟩` from `key Φ₀ hΦ₀`. Rewrite using `[h _ (Nat.mul_pos hM hM') (dvd_mul_right _ _), h' _ (Nat.mul_pos hM hM') (dvd_mul_left _ _), mul_div_cancel_right₀ _ h0]`. Use `push_neg at h0`.

Use `⟨0, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Take `⟨M, hM, h⟩` from `key Φ hΦ`. Rewrite using `[h M hM dvd_rfl, h0 Φ hΦ, mul_zero, mul_zero]`.
-/
theorem theta_unique : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → ∀ l ∈ (adeleClass F).adm κ, (∀ (w : (κ → F) × (κ → F)), ∀ Φ ∈ schA F κ, l (schr ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (w.2 i)) Φ) = l Φ) → ∃ a : ℂ, ∀ Φ ∈ schA F κ, l Φ = a * thetaSum F Φ := by
  intro F _ _ _ _ κ _ ψ hψ h1 hF l hl hinv
  classical
  have hn := (GlobalTheory.CompanionTheory.AdeleAnn.unitary_and_annihilator_eq F ψ hψ h1 hF).1
  have htr : ∀ d : κ → F, ∀ Φ ∈ schA F κ,
      l (fun x => Φ (x + fun i => algebraMap F (AdeleRing (𝓞 F) F) (d i))) = l Φ := fun d Φ hΦ => by
    rw [← hinv (d, 0) Φ hΦ]
    congr 1
    funext x
    simp [schr, dotProduct]
  have hmod : ∀ (i : κ) (y : F), ∀ Φ ∈ schA F κ,
      l (fun x => ψ (x i * algebraMap F (AdeleRing (𝓞 F) F) y) * Φ x) = l Φ := fun i y Φ hΦ => by
    rw [← hinv (0, Pi.single i y) Φ hΦ]
    congr 1
    funext x
    have e : (fun j => algebraMap F (AdeleRing (𝓞 F) F) (Pi.single (M := fun _ => F) i y j)) =
        Pi.single i (algebraMap F (AdeleRing (𝓞 F) F) y) := by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    have e0 : (fun j => algebraMap F (AdeleRing (𝓞 F) F) ((0 : κ → F) j)) = 0 := by funext j; simp
    simp only [schr, e, e0, dotProduct_single, zero_dotProduct, mul_zero, add_zero]
    simp only [Pi.zero_apply, zero_mul, mul_zero, add_zero]
  choose! c hc using fun (N : ℕ) (hN : 0 < N) => level_zero hψ h1 hn hF hl htr hmod hN
  have key : ∀ Φ ∈ schA F κ, ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → l Φ = c N * thetaSum F Φ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, g, hg, rfl⟩ := h
      obtain ⟨N₀, h0, h⟩ := mem_span_cosetInd F κ g hg
      exact ⟨N₀, h0, fun N hN hd => (level_span htr hN (hc N hN) f (h N hN hd)).2⟩
    | zero => exact ⟨1, one_pos, fun N _ _ => by simp [thetaSum]⟩
    | add Φ Ψ hΦ hΨ h h' =>
      obtain ⟨M, hM, h⟩ := h
      obtain ⟨M', hM', h'⟩ := h'
      refine ⟨M * M', Nat.mul_pos hM hM', fun N hN hd => ?_⟩
      rw [map_add, thetaAdd F hΦ hΨ, h N hN ((dvd_mul_right _ _).trans hd),
        h' N hN ((dvd_mul_left _ _).trans hd), mul_add]
    | smul a Φ _ h =>
      obtain ⟨M, hM, h⟩ := h
      refine ⟨M, hM, fun N hN hd => ?_⟩
      rw [map_smul, thetaSmul, h N hN hd, smul_eq_mul, mul_left_comm]
  by_cases h0 : ∃ Φ₀ ∈ schA F κ, thetaSum F Φ₀ ≠ 0
  · obtain ⟨Φ₀, hΦ₀, h0⟩ := h0
    refine ⟨l Φ₀ / thetaSum F Φ₀, fun Φ hΦ => ?_⟩
    obtain ⟨M, hM, h⟩ := key Φ hΦ
    obtain ⟨M', hM', h'⟩ := key Φ₀ hΦ₀
    rw [h _ (Nat.mul_pos hM hM') (dvd_mul_right _ _), h' _ (Nat.mul_pos hM hM') (dvd_mul_left _ _),
      mul_div_cancel_right₀ _ h0]
  · push_neg at h0
    refine ⟨0, fun Φ hΦ => ?_⟩
    obtain ⟨M, hM, h⟩ := key Φ hΦ
    rw [h M hM dvd_rfl, h0 Φ hΦ, mul_zero, mul_zero]

end GlobalTheory.CompanionTheory.ThetaUniq

end

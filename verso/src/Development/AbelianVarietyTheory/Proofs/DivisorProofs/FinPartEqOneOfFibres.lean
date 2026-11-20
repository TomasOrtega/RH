import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane

noncomputable section

open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.CMVal.Fibre

variable {E : Type} [Field E] [NumberField E]

open Classical in

/- English proof (translation)
Set `S : Set (HeightOneSpectrum (𝓞 E))` to `{v | a v ∈ v.adicCompletionIntegers E}`. Establish `hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal S`. Rewrite using `[Filter.le_principal_iff]`. Conclude with `a.2`. Set `P` to `RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E) (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Filter.principal S)`.

Set `f : Finset (HeightOneSpectrum (𝓞 E)) → P` to `fun T => ⟨fun v => if v ∈ T then a v else 1, by`. Rewrite using `[Filter.eventually_principal]`. Introduce `w hw`. Distinguish the cases in `h : w ∈ T`. Simplify using `only [h, if_true]`.

Conclude with `hw`. Simplify using `only [h, if_false]`. Conclude with `one_mem _⟩`. Set `a' : P` to `⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩`. Establish `hf : Filter.Tendsto f Filter.atTop (nhds a')`.

Rewrite using `[RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]`. Introduce `v`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT`. Establish `: v ∈ T` using `hT (Finset.mem_singleton_self v)`.

Express the relevant statement in the definitionally equal form `a v = if v ∈ T then a v else 1`. Rewrite using `[if_pos this]`. Establish `h2` using `((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf`. Establish `h3 : g = (RestrictedProduct.inclusion _ _ hle) ∘ f`. Use function extensionality and compare the values at `fun T => Subtype.ext (funext fun v => hg T v)`.

Rewrite using `[h3]`. Conclude with `h2`.
-/
theorem tendsto_of_cut (a : Af E) (g : Finset (HeightOneSpectrum (𝓞 E)) → Af E)
    (hg : ∀ T v, g T v = if v ∈ T then a v else 1) : Tendsto g atTop (𝓝 a) := by
  let S : Set (HeightOneSpectrum (𝓞 E)) := {v | a v ∈ v.adicCompletionIntegers E}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 E)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
    rw [Filter.eventually_principal]
    intro w hw
    by_cases h : w ∈ T
    · simp only [h, if_true]; exact hw
    · simp only [h, if_false]; exact one_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = if v ∈ T then a v else 1
    rw [if_pos this]
  have h2 := ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf
  have h3 : g = (RestrictedProduct.inclusion _ _ hle) ∘ f :=
    funext fun T => Subtype.ext (funext fun v => hg T v)
  rw [h3]
  exact h2

open Classical in

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, if_neg (Finset.notMem_empty v)]`. Both sides reduce to the same expression. Consider the case `insert u T hu ih`. Rewrite using `[Finset.prod_insert hu, Units.val_mul]`.

Express the relevant statement in the definitionally equal form `(single u (coord u y) : Af E) v * ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E) v = _`. Rewrite using `[ih]`. Distinguish the cases in `h : v = u`. Substitute `h` using the available equality. Rewrite using `[single_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one, coe_coord]`.

Rewrite using `[suppAt_single u _ v h, one_mul]`. Simplify using `[h]`.
-/
theorem prod_single_apply (y : (Af E)ˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 E)) :
    ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E) v = if v ∈ T then (y : Af E) v else 1 := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, if_neg (Finset.notMem_empty v)]; rfl
  | insert u T hu ih =>
    rw [Finset.prod_insert hu, Units.val_mul]
    change (single u (coord u y) : Af E) v * ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E) v = _
    rw [ih]
    by_cases h : v = u
    · subst h
      rw [single_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one, coe_coord]
    · rw [suppAt_single u _ v h, one_mul]; simp [h]

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem coord_inv' (P : HeightOneSpectrum (𝓞 E)) (y : (Af E)ˣ) : coord P y⁻¹ = (coord P y)⁻¹ := Units.ext rfl

/- English proof (translation)
Establish `h : ∀ y : (Af E)ˣ, Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E)) atTop (𝓝 (y : Af E))` using `fun y => tendsto_of_cut _ _ (prod_single_apply y)`. Express the relevant statement in the definitionally equal form `Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, single P (coord P y)) atTop (𝓝 y)`. Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Use `(h y).prodMk_nhds ?_` and prove the remaining obligations. Use `(MulOpposite.continuous_op.tendsto _).comp ?_` and prove the remaining obligations.

Establish `h2` using `h y⁻¹`. Simplify using `only [coord_inv', map_inv, Finset.prod_inv_distrib] at h2`. Conclude with `h2`.
-/
theorem hasProd_single (y : (Af E)ˣ) : HasProd (fun P => single P (coord P y)) y := by
  have h : ∀ y : (Af E)ˣ, Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) =>
      ((∏ P ∈ T, single P (coord P y) : (Af E)ˣ) : Af E)) atTop (𝓝 (y : Af E)) := fun y =>
    tendsto_of_cut _ _ (prod_single_apply y)
  change Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, single P (coord P y)) atTop (𝓝 y)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h y).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h y⁻¹
  simp only [coord_inv', map_inv, Finset.prod_inv_distrib] at h2
  exact h2

/- English proof (translation)
The claim follows from `χ.2.1.comp (Continuous.units_map (MonoidHom.inr (InfiniteAdeleRing E) (Af E)) (continuous_const.prodMk continuous_id))`.
-/
theorem continuous_finPart (χ : HChar E) : Continuous (finPart χ) :=
  χ.2.1.comp (Continuous.units_map (MonoidHom.inr (InfiniteAdeleRing E) (Af E)) (continuous_const.prodMk continuous_id))

/- English proof (translation)
The claim follows from `(hasProd_single y).map (finPart χ) (continuous_finPart χ)`.
-/
theorem hasProd_loc (χ : HChar E) (y : (Af E)ˣ) : HasProd (fun P => χ.loc P (coord P y)) (finPart χ y) :=
  (hasProd_single y).map (finPart χ) (continuous_finPart χ)

/- English proof (translation)
Set `U : Finset (HeightOneSpectrum (OF E)) → Finset (HeightOneSpectrum (𝓞 E))` to `fun S => S.biUnion (Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E))`. Establish `hmem : ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)), P ∈ Formalism.L2.Host.aboveF (L` using `E) (maximalRealSubfield E) v ↔ P.under (OF E) = v := fun v P => by`. Unfold `Formalism.L2.Host.aboveF`. Rewrite using `[Set.Finite.mem_toFinset]`. Both sides reduce to the same expression.

Establish `hU : Tendsto U atTop atTop`. Use `tendsto_atTop_finset_of_monotone (fun S S' hS => Finset.biUnion_subset_biUnion_of_subset_left _ hS) fun P => ?_` and prove the remaining obligations. Conclude with `⟨{P.under (OF E)}, Finset.mem_biUnion.2 ⟨_, Finset.mem_singleton_self _, (hmem _ _).2 rfl⟩⟩`. Establish `h1 : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, χ.loc P (coord P y)) atTop (𝓝 (finPart χ y))` using `hasProd_loc χ y`. Establish `h2` using `h1.comp hU`.

Establish `h3 : ((fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, χ.loc P (coord P y)) ∘ U) = fun _ => 1`. Use function extensionality and compare the values at `S`. Express the relevant statement in the definitionally equal form `∏ P ∈ S.biUnion _, _ = 1`. Rewrite using `[Finset.prod_biUnion]`. Conclude with `Finset.prod_eq_one fun v _ => h v`.

Introduce `v _ w _ hvw`. Use `Finset.disjoint_left.2 fun P hv hw => hvw ?_` and prove the remaining obligations. Rewrite using `[← (hmem _ _).1 hv, ← (hmem _ _).1 hw]`. Rewrite `h2` using `[h3]`. Conclude with `tendsto_nhds_unique h2 tendsto_const_nhds`.
-/
theorem finPart_eq_one_of_fibres (E : Type) [Field E] [NumberField E] (χ : HChar E) (y : (Af E)ˣ)
    (h : ∀ v : HeightOneSpectrum (OF E),
      ∏ P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v, χ.loc P (coord P y) = 1) : finPart χ y = 1 := by
  classical
  let U : Finset (HeightOneSpectrum (OF E)) → Finset (HeightOneSpectrum (𝓞 E)) :=
    fun S => S.biUnion (Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E))
  have hmem : ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)),
      P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v ↔ P.under (OF E) = v := fun v P => by
    unfold Formalism.L2.Host.aboveF
    rw [Set.Finite.mem_toFinset]; rfl
  have hU : Tendsto U atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun S S' hS => Finset.biUnion_subset_biUnion_of_subset_left _ hS) fun P => ?_
    exact ⟨{P.under (OF E)}, Finset.mem_biUnion.2 ⟨_, Finset.mem_singleton_self _, (hmem _ _).2 rfl⟩⟩
  have h1 : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, χ.loc P (coord P y)) atTop (𝓝 (finPart χ y)) :=
    hasProd_loc χ y
  have h2 := h1.comp hU
  have h3 : ((fun T : Finset (HeightOneSpectrum (𝓞 E)) => ∏ P ∈ T, χ.loc P (coord P y)) ∘ U) = fun _ => 1 := by
    funext S
    change ∏ P ∈ S.biUnion _, _ = 1
    rw [Finset.prod_biUnion]
    · exact Finset.prod_eq_one fun v _ => h v
    · intro v _ w _ hvw
      refine Finset.disjoint_left.2 fun P hv hw => hvw ?_
      rw [← (hmem _ _).1 hv, ← (hmem _ _).1 hw]
  rw [h3] at h2
  exact tendsto_nhds_unique h2 tendsto_const_nhds

end GlobalTheory.CMVal.Fibre

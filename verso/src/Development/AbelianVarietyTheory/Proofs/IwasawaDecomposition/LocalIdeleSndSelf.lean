import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host nonZeroDivisors

namespace GlobalTheory.HeckeProduct

section Comp
variable (L : Type) [Field L] [NumberField L]

/- English proof (translation)
Use `show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) v = x`. Use `Pi.mulSingle_eq_same v (x : v.adicCompletion L)` and compare the differences between its conclusion and the goal.
-/
theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion L)

/- English proof (translation)
Use `show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) w = 1`. Use `Pi.mulSingle_eq_of_ne h (x : v.adicCompletion L)` and compare the differences between its conclusion and the goal.
-/
theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion L)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem localIdele_fst (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := rfl

/- English proof (translation)
Use `show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) w = x`. Use `Pi.mulSingle_eq_same w (x : w.Completion)` and compare the differences between its conclusion and the goal.
-/
theorem infIdele_fst_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 w = x := by
  classical
  show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) w = x
  convert Pi.mulSingle_eq_same w (x : w.Completion)

/- English proof (translation)
Use `show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) u = 1`. Use `Pi.mulSingle_eq_of_ne h (x : w.Completion)` and compare the differences between its conclusion and the goal.
-/
theorem infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by
  classical
  show (Pi.mulSingle w (x : w.Completion) : ∀ u : InfinitePlace L, u.Completion) u = 1
  convert Pi.mulSingle_eq_of_ne h (x : w.Completion)

end Comp

section Parts
variable (F : Type) [Field F] [NumberField F]

def infPart : Ideles F →* (InfiniteAdeleRing F)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def finPart : Ideles F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

variable {F}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Apply `Units.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `w`. Rewrite using `[infDiag, MonoidHom.finset_prod_apply, map_prod, Units.coe_prod]`. Establish `e : (∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)) w = ∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w` using `Finset.prod_apply _ _ _`.

Rewrite using `[e, Finset.prod_eq_single w]`. Conclude with `infIdele_fst_self F w _`. Introduce `u _ hu`. Conclude with `infIdele_fst_ne F u w (Ne.symm hu) _`. Simplify using the standard rewrite rules.

Rewrite using `[infDiag, MonoidHom.finset_prod_apply, map_prod]`. Conclude with `Finset.prod_eq_one fun u _ => Units.ext rfl`.
-/
theorem infDiag_parts (k : Fˣ) : infPart F (infDiag k) = infPart F (diagUnits F k) ∧ finPart F (infDiag k) = 1 := by
  classical
  constructor
  · apply Units.ext
    funext w
    rw [infDiag, MonoidHom.finset_prod_apply, map_prod, Units.coe_prod]
    have e : (∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) : (InfiniteAdeleRing F)ˣ) :
        InfiniteAdeleRing F)) w = ∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) :
          (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w := Finset.prod_apply _ _ _
    rw [e, Finset.prod_eq_single w]
    · exact infIdele_fst_self F w _
    · intro u _ hu
      exact infIdele_fst_ne F u w (Ne.symm hu) _
    · simp
  · rw [infDiag, MonoidHom.finset_prod_apply, map_prod]
    exact Finset.prod_eq_one fun u _ => Units.ext rfl

end Parts

section Product

variable {F : Type} [Field F] [NumberField F]

open Classical in

def cut (a : FiniteAdeleRing (𝓞 F) F) (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then a v else 1, by
    refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    apply hw
    have h' : w ∉ T := h
    simp only [h', if_false]
    exact one_mem _⟩

/- English proof (translation)
Set `S : Set (HeightOneSpectrum (𝓞 F))` to `{v | a v ∈ v.adicCompletionIntegers F}`. Establish `hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S`. Rewrite using `[Filter.le_principal_iff]`. Conclude with `a.2`. Set `P` to `RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)`.

Set `f : Finset (HeightOneSpectrum (𝓞 F)) → P` to `fun T => ⟨fun v => if v ∈ T then a v else 1, by`. Rewrite using `[Filter.eventually_principal]`. Introduce `w hw`. Distinguish the cases in `h : w ∈ T`. Simplify using `only [h, if_true]`.

Conclude with `hw`. Simplify using `only [h, if_false]`. Conclude with `one_mem _⟩`. Set `a' : P` to `⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩`. Establish `hf : Filter.Tendsto f Filter.atTop (nhds a')`.

Rewrite using `[RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]`. Introduce `v`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT`. Establish `: v ∈ T` using `hT (Finset.mem_singleton_self v)`.

Express the relevant statement in the definitionally equal form `a v = if v ∈ T then a v else 1`. Rewrite using `[if_pos this]`. Conclude with `((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf`.
-/
theorem tendsto_cut (a : FiniteAdeleRing (𝓞 F) F) : Filter.Tendsto (cut a) Filter.atTop (nhds a) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | a v ∈ v.adicCompletionIntegers F}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
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
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((infPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = _`. Establish `e : ∏ v ∈ T, infPart F (localIdele F v (atFin v k)) = 1` using `Finset.prod_eq_one (fun v _ => Units.ext rfl)`. Rewrite using `[map_mul, map_prod, (infDiag_parts k).1, e, mul_one]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `((finPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = _`. Rewrite using `[map_mul, (infDiag_parts k).2, one_mul]`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, map_one]; exact Subtype.ext (funext fun v => by simp [cut]; rfl)`. Consider the case `insert u T hu ih`.

Rewrite using `[Finset.prod_insert hu, map_mul, Units.val_mul, ih]`. Use `Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((localIdele F u (atFin u k) : Ideles F) : AdeleRing (𝓞 F) F).2 v * (if v ∈ T then _ else 1) = if v ∈ insert u T then _ else 1`. Distinguish the cases in `h : v = u`. Substitute `h` using the available equality.

Rewrite using `[localIdele_snd_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one]`. Both sides reduce to the same expression. Rewrite using `[localIdele_snd_ne F u v h, one_mul]`. Simplify using `[h]`.
-/
theorem prod_local (k : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F) =
      (((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).1, cut ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).2 T) := by
  classical
  refine Prod.ext ?_ ?_
  · change ((infPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = _
    have e : ∏ v ∈ T, infPart F (localIdele F v (atFin v k)) = 1 := Finset.prod_eq_one (fun v _ => Units.ext rfl)
    rw [map_mul, map_prod, (infDiag_parts k).1, e, mul_one]
    rfl
  · change ((finPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = _
    rw [map_mul, (infDiag_parts k).2, one_mul]
    induction T using Finset.induction_on with
    | empty => rw [Finset.prod_empty, map_one]; exact Subtype.ext (funext fun v => by simp [cut]; rfl)
    | insert u T hu ih =>
      rw [Finset.prod_insert hu, map_mul, Units.val_mul, ih]
      refine Subtype.ext (funext fun v => ?_)
      change ((localIdele F u (atFin u k) : Ideles F) : AdeleRing (𝓞 F) F).2 v * (if v ∈ T then _ else 1) =
        if v ∈ insert u T then _ else 1
      by_cases h : v = u
      · subst h
        rw [localIdele_snd_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one]; rfl
      · rw [localIdele_snd_ne F u v h, one_mul]; simp [h]

/- English proof (translation)
Establish `h : ∀ k : Fˣ, Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F)) Filter.atTop (nhds ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F))` using `fun k => by`. Simplify using `only [prod_local]`. Conclude with `tendsto_const_nhds.prodMk_nhds (tendsto_cut _)`. Rewrite using `[Units.isEmbedding_embedProduct.tendsto_nhds_iff]`. Use `(h k).prodMk_nhds ?_` and prove the remaining obligations.

Use `(MulOpposite.continuous_op.tendsto _).comp ?_` and prove the remaining obligations. Establish `h2` using `h k⁻¹`. Simplify using `only [map_inv, Finset.prod_inv_distrib, ← mul_inv] at h2`. Conclude with `h2`.
-/
theorem tendsto_prod_local (k : Fˣ) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
      Filter.atTop (nhds (diagUnits F k)) := by
  have h : ∀ k : Fˣ, Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F))
      Filter.atTop (nhds ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F)) := fun k => by
    simp only [prod_local]
    exact tendsto_const_nhds.prodMk_nhds (tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h k).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h k⁻¹
  simp only [map_inv, Finset.prod_inv_distrib, ← mul_inv] at h2
  exact h2

/- English proof (translation)
Establish `hu : IsUnitAt v (atFin v (k * (unif v ^ ordF v k)⁻¹))`. Establish `h2` using `unif_spec v`. Establish `hk : Valued.v ((atFin v k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = v.valuation F (k : F)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)`. Establish `h0 : v.valuation F (k : F) ≠ 0` using `by simp`. Unfold `IsUnitAt IsUnifAt at *`.

Rewrite using `[map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, h2, hk, ← WithZero.exp_zsmul, ordF]`. Simplify using `only [smul_eq_mul, mul_neg, mul_one, neg_neg]`. Rewrite using `[WithZero.exp_log h0, mul_inv_cancel₀ h0]`. Establish `h3 : χ.locK v (k * (unif v ^ ordF v k)⁻¹) = 1` using `h _ hu`. Rewrite `h3` using `[map_mul, map_inv, map_zpow, mul_inv_eq_one]`.

Conclude with `h3`.
-/
theorem locK_unr (χ : HChar F) {v : HeightOneSpectrum (𝓞 F)} (h : χ.UnrAt v) (k : Fˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by
  have hu : IsUnitAt v (atFin v (k * (unif v ^ ordF v k)⁻¹)) := by
    have h2 := unif_spec v
    have hk : Valued.v ((atFin v k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = v.valuation F (k : F) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
    have h0 : v.valuation F (k : F) ≠ 0 := by simp
    unfold IsUnitAt IsUnifAt at *
    rw [map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h2, hk, ← WithZero.exp_zsmul, ordF]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
  have h3 : χ.locK v (k * (unif v ^ ordF v k)⁻¹) = 1 := h _ hu
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
  exact h3

/- English proof (translation)
Establish `h` using `Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (FiniteAdeleRing.unitEmbedding (𝓞 F) F k))`. Use `h.subset fun v hv h0 => hv ?_` and prove the remaining obligations. Establish `hk : Valued.v (((FiniteAdeleRing.unitEmbedding (𝓞 F) F k : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = v.valuation F (k : F)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)`. Rewrite `h0` using `[GlobalTheory.Idele.ord_vw, hk]`. Conclude with `h0`.
-/
theorem finite_ordF (k : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordF v k ≠ 0}.Finite := by
  have h := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (FiniteAdeleRing.unitEmbedding (𝓞 F) F k))
  refine h.subset fun v hv h0 => hv ?_
  have hk : Valued.v (((FiniteAdeleRing.unitEmbedding (𝓞 F) F k : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v) = v.valuation F (k : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
  rw [GlobalTheory.Idele.ord_vw, hk] at h0
  exact h0

/- English proof (translation)
Introduce `S hS k`. Establish `h1` using `(χ.2.1.tendsto _).comp (tendsto_prod_local k)`. Rewrite `h1` using `[χ.2.2 k]`. Use `tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h1` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop (S ∪ (finite_ordF k).toFinset)] with T hT`.

Establish `hST : S ⊆ T` using `Finset.subset_union_left.trans hT`. Express the relevant statement in the definitionally equal form `_ = χ.1 (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))`. Rewrite using `[map_mul, map_prod, mul_assoc, ← Finset.prod_sdiff hST, mul_comm (∏ v ∈ T \ S, _)]`. Use `congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl ?_)` and prove the remaining obligations. Rewrite using `[finprod_cond_eq_prod_of_cond_iff (fun v => χ.val v ^ ordF v k) (p := fun v => v ∉ S) (t := T \ S)]`.

Conclude with `Finset.prod_congr rfl fun v hv => (locK_unr χ (hS v (Finset.mem_sdiff.1 hv).2) k).symm`. Introduce `v hv`. Rewrite using `[Finset.mem_sdiff]`. Use `⟨fun h => ⟨hT (Finset.mem_union_right _ ?_), h⟩, fun h => h.2⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`.

Introduce `h0`. Conclude with `hv (by rw [h0, zpow_zero])`.
-/
theorem productRule (χ : HChar F) : χ.ProductRule := by
  classical
  intro S hS k
  have h1 := (χ.2.1.tendsto _).comp (tendsto_prod_local k)
  rw [χ.2.2 k] at h1
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h1
  filter_upwards [Filter.eventually_ge_atTop (S ∪ (finite_ordF k).toFinset)] with T hT
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  change _ = χ.1 (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
  rw [map_mul, map_prod, mul_assoc, ← Finset.prod_sdiff hST, mul_comm (∏ v ∈ T \ S, _)]
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl ?_)
  rw [finprod_cond_eq_prod_of_cond_iff (fun v => χ.val v ^ ordF v k) (p := fun v => v ∉ S) (t := T \ S)]
  · exact Finset.prod_congr rfl fun v hv => (locK_unr χ (hS v (Finset.mem_sdiff.1 hv).2) k).symm
  · intro v hv
    rw [Finset.mem_sdiff]
    refine ⟨fun h => ⟨hT (Finset.mem_union_right _ ?_), h⟩, fun h => h.2⟩
    rw [Set.Finite.mem_toFinset]
    intro h0
    exact hv (by rw [h0, zpow_zero])

end Product

/- English proof (translation)
Introduce `_ _ _ χ` and use `productRule χ`.
-/
theorem hchar_productRule : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), χ.ProductRule :=
  fun _ _ _ χ => productRule χ

end GlobalTheory.HeckeProduct

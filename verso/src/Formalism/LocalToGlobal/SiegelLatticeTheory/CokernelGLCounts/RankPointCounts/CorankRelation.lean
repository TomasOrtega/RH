import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.DensInertDisplayHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.FinrankOrthAddLe

noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Matrix

namespace Formalism.L2.SG.NGCut.CorankRelation

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hx`. Establish `hdet : (Formalism.L2.SG.GramJoint.gramFF F F').det ≠ 0`. Rewrite using `[Formalism.L2.SG.Closed.GramDetFlag_holds E S r T T' F F']`. Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) hG`. Establish `hc : Formalism.L2.SG.GramJoint.gramFF F F' *ᵥ c = 0`.

Use function extensionality and compare the values at `i`. Establish `h` using `ho i`. Rewrite `h` using `[map_sum]`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`. Rewrite using `[← h]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Formalism.L2.SG.GramJoint.gramFF, Formalism.L2.SG.GramJoint.pairVec, brS, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `Matrix.eq_zero_of_mulVec_eq_zero hdet hc`. Simplify using `[h0]`.
-/
theorem span_pair_orth_eq_zero {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0)
    (x : S.V) (hx : x ∈ Submodule.span E (Set.range (Sum.elim F.fvec F'.fvec)))
    (ho : ∀ i, S.hT (Sum.elim F.fvec F'.fvec i) x = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  have hdet : (Formalism.L2.SG.GramJoint.gramFF F F').det ≠ 0 := by
    rw [Formalism.L2.SG.Closed.GramDetFlag_holds E S r T T' F F']
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hG
  have hc : Formalism.L2.SG.GramJoint.gramFF F F' *ᵥ c = 0 := by
    funext i
    have h := ho i
    rw [map_sum] at h
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Formalism.L2.SG.GramJoint.gramFF, Formalism.L2.SG.GramJoint.pairVec, brS, map_smul, smul_eq_mul]
    ring
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hc
  simp [h0]

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.subset_span ⟨Sum.inl (Fin.castSucc a), by simp [FlagG.fvec]⟩`.
-/
theorem Xsp_le_span {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') :
    F.X ≤ Submodule.span E (Set.range (Sum.elim F.fvec F'.fvec)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨Sum.inl (Fin.castSucc a), by simp [FlagG.fvec]⟩

/- English proof (translation)
Establish `hx' : x ∈ orth S (UUE Λ F F')` using `hx`. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx'`. Conclude with `hx' y hy`.
-/
theorem hT_eq_zero_of_mem_Hp {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    {x y : S.V} (hx : x ∈ Hp Λ F F') (hy : y ∈ UUE Λ F F') : S.hT y x = 0 := by
  have hx' : x ∈ orth S (UUE Λ F F') := hx
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx'
  exact hx' y hy

/- English proof (translation)
Use `span_pair_orth_eq_zero F.fl F'.fl hG x (Xsp_le_span F.fl F'.fl hx) fun i => ?_` and prove the remaining obligations. Conclude with `hT_eq_zero_of_mem_Hp Λ F F' hH (PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL' i)`.
-/
theorem Xsp_Hp_eq_zero {T T' : E} (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') (hG : Gval F F' ≠ 0)
    {x : S.V} (hx : x ∈ Xsp F) (hH : x ∈ Hp Λ F F') : x = 0 := by
  refine span_pair_orth_eq_zero F.fl F'.fl hG x (Xsp_le_span F.fl F'.fl hx) fun i => ?_
  exact hT_eq_zero_of_mem_Hp Λ F F' hH (PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL' i)

/- English proof (translation)
Set `K : Submodule E S.V` to `LinearMap.ker (S.hT.flip v)`. Establish `hK : ∀ y, y ∈ K ↔ S.hT y v = 0` using `fun y => by simp [K]`. Establish `hXK : ∀ {T₀ : E} (G : LFlag S r T₀), (∀ a, S.hT (G.fl.e a) v = 0) → Xsp G ≤ K`. Introduce `T₀ G hG`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `(hK _).2 (hG a)`. Establish `he : ∀ a, S.hT (F.fl.e a) v = 0` using `fun a => by`. Use `hv (Sum.inl (Fin.castSucc a))` as an intermediate fact. Simplify `this` using `[FlagG.fvec]`.

Establish `he' : ∀ a, S.hT (F'.fl.e a) v = 0` using `fun a => by`. Use `hv (Sum.inr (Fin.castSucc a))` as an intermediate fact. Simplify `this` using `[FlagG.fvec]`. Establish `hz : S.hT F.zt v = 0`. Use `hv (Sum.inl (Fin.last r))` as an intermediate fact.

Rewrite using `[hL.2]`. Simplify `this` using `[FlagG.fvec]`. Establish `hz' : S.hT F'.zt v = 0`. Use `hv (Sum.inr (Fin.last r))` as an intermediate fact. Rewrite using `[hL'.2]`.

Simplify `this` using `[FlagG.fvec]`. Establish `hUU : UU Λ F F' ≤ K.restrictScalars (𝓞 E)`. Unfold `UU`. Use `sup_le (sup_le (sup_le ?_ ?_) ?_) ?_` and prove the remaining obligations. Conclude with `inf_le_right.trans (Submodule.restrictScalars_mono _ (hXK F he))`.

Conclude with `Submodule.span_le.2 (by rintro _ rfl; exact (hK _).2 hz)`. Conclude with `inf_le_right.trans (Submodule.restrictScalars_mono _ (hXK F' he'))`. Conclude with `Submodule.span_le.2 (by rintro _ rfl; exact (hK _).2 hz')`. Establish `hUUE : UUE Λ F F' ≤ K` using `Submodule.span_le.2 fun y hy => hUU hy`. Use `show v ∈ orth S (UUE Λ F F')`.

Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `y hy`. Conclude with `(hK y).1 (hUUE hy)`.
-/
theorem mem_Hp_of_orth {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    (hL : IsLift Λ F) (hL' : IsLift Λ F') (v : S.V) (hv : ∀ i, S.hT (Sum.elim F.fl.fvec F'.fl.fvec i) v = 0) :
    v ∈ Hp Λ F F' := by
  let K : Submodule E S.V := LinearMap.ker (S.hT.flip v)
  have hK : ∀ y, y ∈ K ↔ S.hT y v = 0 := fun y => by simp [K]
  have hXK : ∀ {T₀ : E} (G : LFlag S r T₀), (∀ a, S.hT (G.fl.e a) v = 0) → Xsp G ≤ K := by
    intro T₀ G hG
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact (hK _).2 (hG a)
  have he : ∀ a, S.hT (F.fl.e a) v = 0 := fun a => by
    have := hv (Sum.inl (Fin.castSucc a)); simpa [FlagG.fvec] using this
  have he' : ∀ a, S.hT (F'.fl.e a) v = 0 := fun a => by
    have := hv (Sum.inr (Fin.castSucc a)); simpa [FlagG.fvec] using this
  have hz : S.hT F.zt v = 0 := by
    have := hv (Sum.inl (Fin.last r)); rw [hL.2]; simpa [FlagG.fvec] using this
  have hz' : S.hT F'.zt v = 0 := by
    have := hv (Sum.inr (Fin.last r)); rw [hL'.2]; simpa [FlagG.fvec] using this
  have hUU : UU Λ F F' ≤ K.restrictScalars (𝓞 E) := by
    unfold UU
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact inf_le_right.trans (Submodule.restrictScalars_mono _ (hXK F he))
    · exact Submodule.span_le.2 (by rintro _ rfl; exact (hK _).2 hz)
    · exact inf_le_right.trans (Submodule.restrictScalars_mono _ (hXK F' he'))
    · exact Submodule.span_le.2 (by rintro _ rfl; exact (hK _).2 hz')
  have hUUE : UUE Λ F F' ≤ K := Submodule.span_le.2 fun y hy => hUU hy
  show v ∈ orth S (UUE Λ F F')
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y hy
  exact (hK y).1 (hUUE hy)

/- English proof (translation)
Establish `hu` using `PI.PairCorankPos.W.linIndep F.fl F'.fl hG`. Establish `h1` using `PI.PairCorankPos.W.finrank_orth_add_le S _ hu (UUE Λ F F') (PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL')`. Rewrite `h1` using `[Fintype.card_sum, Fintype.card_fin]`. Establish `h3 : finrank E (Hp Λ F F') = finrank E (orth S (UUE Λ F F'))` using `rfl`. Set `Φ : S.V →ₗ[E] (Fin (r + 1) ⊕ Fin (r + 1) → E)` to `LinearMap.pi (fun i => S.hT (Sum.elim F.fl.fvec F'.fl.fvec i))`.

Establish `hker : LinearMap.ker Φ ≤ Hp Λ F F'`. Introduce `v hv`. Rewrite `hv` using `[LinearMap.mem_ker]`. Conclude with `mem_Hp_of_orth Λ F F' hL hL' v fun i => congrFun hv i`. Establish `h4` using `LinearMap.finrank_range_add_finrank_ker Φ`.

Establish `h5 : finrank E (LinearMap.range Φ) ≤ 2 * r + 2`. Use `Submodule.finrank_le (LinearMap.range Φ)` as an intermediate fact. Rewrite `this` using `[Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Establish `h6` using `Submodule.finrank_mono hker`.

Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_Hp {T T' : E} (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F')
    (hG : Gval F F' ≠ 0) : finrank E (Hp Λ F F') = k - 1 ∧ 1 ≤ k := by
  have hu := PI.PairCorankPos.W.linIndep F.fl F'.fl hG
  have h1 := PI.PairCorankPos.W.finrank_orth_add_le S _ hu (UUE Λ F F')
    (PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL')
  rw [Fintype.card_sum, Fintype.card_fin] at h1
  have h3 : finrank E (Hp Λ F F') = finrank E (orth S (UUE Λ F F')) := rfl
  let Φ : S.V →ₗ[E] (Fin (r + 1) ⊕ Fin (r + 1) → E) :=
    LinearMap.pi (fun i => S.hT (Sum.elim F.fl.fvec F'.fl.fvec i))
  have hker : LinearMap.ker Φ ≤ Hp Λ F F' := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    exact mem_Hp_of_orth Λ F F' hL hL' v fun i => congrFun hv i
  have h4 := LinearMap.finrank_range_add_finrank_ker Φ
  have h5 : finrank E (LinearMap.range Φ) ≤ 2 * r + 2 := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at this
    omega
  have h6 := Submodule.finrank_mono hker
  omega

/- English proof (translation)
Take `⟨h1, hk⟩` from `finrank_Hp k hdim Λ hΛ F F' hL hL' hG`. Establish `hle` using `PI.PairCorankPos.W.Th_le_Hp Λ F F' F'' β`. Establish `h2` using `Submodule.finrank_mono hle`. Unfold `s0`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `Submodule.eq_of_le_of_finrank_le hle (by omega)`. Introduce `h`. Rewrite using `[h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem s0_eq_one_iff_Th_eq_Hp {T T' : E} (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hL : IsLift Λ F) (hL' : IsLift Λ F') (hG : Gval F F' ≠ 0) :
    s0 Λ F F' F'' β k = 1 ↔ Th Λ F F' F'' β = Hp Λ F F' := by
  obtain ⟨h1, hk⟩ := finrank_Hp k hdim Λ hΛ F F' hL hL' hG
  have hle := PI.PairCorankPos.W.Th_le_Hp Λ F F' F'' β
  have h2 := Submodule.finrank_mono hle
  unfold s0
  constructor
  · intro h
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)
  · intro h
    rw [h]; omega

/- English proof (translation)
Simplify using `only [ThPairs, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]`. The claim follows by propositional logic.
-/
theorem mem_ThPairs {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β : S.V ≃ₗ[E] S.V) (p : S.V × S.V) :
    p ∈ ThPairs Λ F F' F'' β ↔ p.1 ∈ Hp Λ F F' ∧ p.2 ∈ Hp Λ F F'' ∧ p.1 - p.2 ∈ Xsp F ∧
      β p.1 - p.2 ∈ Xsp F'' := by
  simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  tauto

/- English proof (translation)
Use `le_antisymm (PI.PairCorankPos.W.Th_le_Hp Λ F F' F' 1) fun x hx => ?_` and prove the remaining obligations. Use `Submodule.mem_map.2 ⟨(x, x), (mem_ThPairs Λ F F' F' 1 (x, x)).2 ⟨hx, hx, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `show (1 : S.V ≃ₗ[E] S.V) x - x ∈ Xsp F'`. Simplify using the standard rewrite rules.
-/
theorem Th_one {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Th Λ F F' F' 1 = Hp Λ F F' := by
  refine le_antisymm (PI.PairCorankPos.W.Th_le_Hp Λ F F' F' 1) fun x hx => ?_
  refine Submodule.mem_map.2 ⟨(x, x), (mem_ThPairs Λ F F' F' 1 (x, x)).2 ⟨hx, hx, ?_, ?_⟩, rfl⟩
  · simp
  · show (1 : S.V ≃ₗ[E] S.V) x - x ∈ Xsp F'
    simp

/- English proof (translation)
Set `P` to `ThPairs Λ F F₁ F₂ β`. Establish `hd₁` using `(finrank_Hp k hdim Λ hΛ F F₁ hL hL₁ hG₁).1`. Establish `hd₂` using `(finrank_Hp k hdim Λ hΛ F F₂ hL hL₂ hG₂).1`. Set `f : P →ₗ[E] S.V` to `(LinearMap.snd E S.V S.V).domRestrict P`. Establish `hf : Function.Injective f`.

Introduce `a b hab`. Establish `hsub` using `(mem_ThPairs Λ F F₁ F₂ β ((a : S.V × S.V) - b)).1 (P.sub_mem a.2 b.2)`. Establish `h2 : ((a : S.V × S.V) - b).2 = 0`. Establish `: (a : S.V × S.V).2 = (b : S.V × S.V).2` using `hab`. Simplify using `[this]`.

Rewrite `hsub` using `[h2, sub_zero]`. Establish `h1` using `Xsp_Hp_eq_zero Λ hΛ F F₁ hL hL₁ hG₁ hsub.2.2.1 hsub.1`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Prod.ext (sub_eq_zero.1 (by simpa using h1)) hab`. Establish `hrange : LinearMap.range f = P.map (LinearMap.snd E S.V S.V)` using `LinearMap.range_domRestrict _ _`.

Establish `hTh2 : finrank E P ≤ finrank E (P.map (LinearMap.snd E S.V S.V))`. Rewrite using `[← hrange, LinearMap.finrank_range_of_inj hf]`. Establish `hTh1 : finrank E (Th Λ F F₁ F₂ β) ≤ finrank E P` using `Submodule.finrank_map_le _ _`. Establish `hle2 : P.map (LinearMap.snd E S.V S.V) ≤ Hp Λ F F₂`. Introduce `y hy`.

Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.1 hy`. Conclude with `((mem_ThPairs Λ F F₁ F₂ β p).1 hp).2.1`. Establish `hTh' : P.map (LinearMap.snd E S.V S.V) = Hp Λ F F₂`. Use `Submodule.eq_of_le_of_finrank_le hle2 ?_` and prove the remaining obligations. Rewrite `hTh1` using `[h]`.

Use linear arithmetic over natural numbers and integers. Use `le_antisymm (PI.PairCorankPos.W.Th_le_Hp Λ F F₂ F₁ β⁻¹) ?_` and prove the remaining obligations. Rewrite using `[← hTh']`. Introduce `y hy`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.1 hy`.

Take `⟨hp1, hp2, hp3, hp4⟩` from `(mem_ThPairs Λ F F₁ F₂ β p).1 hp`. Use `Submodule.mem_map.2 ⟨(p.2, p.1), (mem_ThPairs Λ F F₂ F₁ β⁻¹ _).2 ⟨hp2, hp1, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Use `(Xsp F).neg_mem hp3` as an intermediate fact. Simplify using `using this`. Use `show β.symm p.2 - p.1 ∈ Xsp F₁`.

Rewrite using `[hβ]`. Establish `: β (β.symm p.2 - p.1) = -(β p.1 - p.2)`. Rewrite using `[map_sub, LinearEquiv.apply_symm_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`.

Conclude with `(Xsp F₂).neg_mem hp4`.
-/
theorem Th_symm {T T' : E} (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F₁ F₂ : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hL : IsLift Λ F) (hL₁ : IsLift Λ F₁) (hL₂ : IsLift Λ F₂) (hG₁ : Gval F F₁ ≠ 0) (hG₂ : Gval F F₂ ≠ 0)
    (hβ : ∀ x, x ∈ Xsp F₁ ↔ β x ∈ Xsp F₂) (h : Th Λ F F₁ F₂ β = Hp Λ F F₁) :
    Th Λ F F₂ F₁ β⁻¹ = Hp Λ F F₂ := by
  let P := ThPairs Λ F F₁ F₂ β
  have hd₁ := (finrank_Hp k hdim Λ hΛ F F₁ hL hL₁ hG₁).1
  have hd₂ := (finrank_Hp k hdim Λ hΛ F F₂ hL hL₂ hG₂).1

  let f : P →ₗ[E] S.V := (LinearMap.snd E S.V S.V).domRestrict P
  have hf : Function.Injective f := by
    intro a b hab
    have hsub := (mem_ThPairs Λ F F₁ F₂ β ((a : S.V × S.V) - b)).1 (P.sub_mem a.2 b.2)
    have h2 : ((a : S.V × S.V) - b).2 = 0 := by
      have : (a : S.V × S.V).2 = (b : S.V × S.V).2 := hab
      simp [this]
    rw [h2, sub_zero] at hsub
    have h1 := Xsp_Hp_eq_zero Λ hΛ F F₁ hL hL₁ hG₁ hsub.2.2.1 hsub.1
    apply Subtype.ext
    exact Prod.ext (sub_eq_zero.1 (by simpa using h1)) hab
  have hrange : LinearMap.range f = P.map (LinearMap.snd E S.V S.V) := LinearMap.range_domRestrict _ _
  have hTh2 : finrank E P ≤ finrank E (P.map (LinearMap.snd E S.V S.V)) := by
    rw [← hrange, LinearMap.finrank_range_of_inj hf]
  have hTh1 : finrank E (Th Λ F F₁ F₂ β) ≤ finrank E P := Submodule.finrank_map_le _ _
  have hle2 : P.map (LinearMap.snd E S.V S.V) ≤ Hp Λ F F₂ := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
    exact ((mem_ThPairs Λ F F₁ F₂ β p).1 hp).2.1
  have hTh' : P.map (LinearMap.snd E S.V S.V) = Hp Λ F F₂ := by
    refine Submodule.eq_of_le_of_finrank_le hle2 ?_
    rw [h] at hTh1
    omega
  refine le_antisymm (PI.PairCorankPos.W.Th_le_Hp Λ F F₂ F₁ β⁻¹) ?_
  rw [← hTh']
  intro y hy
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨hp1, hp2, hp3, hp4⟩ := (mem_ThPairs Λ F F₁ F₂ β p).1 hp
  refine Submodule.mem_map.2 ⟨(p.2, p.1), (mem_ThPairs Λ F F₂ F₁ β⁻¹ _).2 ⟨hp2, hp1, ?_, ?_⟩, rfl⟩
  · have := (Xsp F).neg_mem hp3
    simpa using this
  · show β.symm p.2 - p.1 ∈ Xsp F₁
    rw [hβ]
    have : β (β.symm p.2 - p.1) = -(β p.1 - p.2) := by
      rw [map_sub, LinearEquiv.apply_symm_apply]; abel
    rw [this]
    exact (Xsp F₂).neg_mem hp4

/- English proof (translation)
Use `le_antisymm (PI.PairCorankPos.W.Th_le_Hp Λ F F₁ F₃ (β' * β)) fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[← h]`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.1 hx`. Take `⟨hp1, hp2, hp3, hp4⟩` from `(mem_ThPairs Λ F F₁ F₂ β p).1 hp`. Establish `hy : p.2 ∈ Th Λ F F₂ F₃ β'` using `by rw [h']; exact hp2`.

Take `⟨q, hq, hq1⟩` from `Submodule.mem_map.1 hy`. Take `⟨hq1', hq2, hq3, hq4⟩` from `(mem_ThPairs Λ F F₂ F₃ β' q).1 hq`. Establish `hq1e : q.1 = p.2` using `hq1`. Rewrite `hq3`, `hq4` using `[hq1e]`. Use `Submodule.mem_map.2 ⟨(p.1, q.2), (mem_ThPairs Λ F F₁ F₃ (β' * β) _).2 ⟨hp1, hq2, ?_, ?_⟩, rfl⟩` and prove the remaining obligations.

Use `(Xsp F).add_mem hp3 hq3` as an intermediate fact. Simplify using `using this`. Use `show β' (β p.1) - q.2 ∈ Xsp F₃`. Use `(Xsp F₃).add_mem (hβ' _ hp4) hq4` as an intermediate fact. Simplify `this` using `[map_sub]`.
-/
theorem Th_trans {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F₁ F₂ F₃ : LFlag S r T')
    (β β' : S.V ≃ₗ[E] S.V) (hβ' : ∀ x, x ∈ Xsp F₂ → β' x ∈ Xsp F₃)
    (h : Th Λ F F₁ F₂ β = Hp Λ F F₁) (h' : Th Λ F F₂ F₃ β' = Hp Λ F F₂) :
    Th Λ F F₁ F₃ (β' * β) = Hp Λ F F₁ := by
  refine le_antisymm (PI.PairCorankPos.W.Th_le_Hp Λ F F₁ F₃ (β' * β)) fun x hx => ?_
  rw [← h] at hx
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨hp1, hp2, hp3, hp4⟩ := (mem_ThPairs Λ F F₁ F₂ β p).1 hp
  have hy : p.2 ∈ Th Λ F F₂ F₃ β' := by rw [h']; exact hp2
  obtain ⟨q, hq, hq1⟩ := Submodule.mem_map.1 hy
  obtain ⟨hq1', hq2, hq3, hq4⟩ := (mem_ThPairs Λ F F₂ F₃ β' q).1 hq
  have hq1e : q.1 = p.2 := hq1
  rw [hq1e] at hq3 hq4
  refine Submodule.mem_map.2 ⟨(p.1, q.2), (mem_ThPairs Λ F F₁ F₃ (β' * β) _).2 ⟨hp1, hq2, ?_, ?_⟩, rfl⟩
  · have := (Xsp F).add_mem hp3 hq3
    simpa using this
  · show β' (β p.1) - q.2 ∈ Xsp F₃
    have := (Xsp F₃).add_mem (hβ' _ hp4) hq4
    simpa [map_sub] using this

/- English proof (translation)
Establish `h1 : Xsp (Formalism.L2.SG.TermOp.mapLF γ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V)`. Unfold `Formalism.L2.SG.TermOp.mapLF`. Rewrite using `[dif_pos hγ]`. Use `show Submodule.span E (Set.range fun a => γ (F.fl.e a)) = (Submodule.span E (Set.range F.fl.e)).map (γ : S.V →ₗ[E] S.V)`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[h1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`.

Introduce `h`. Conclude with `⟨γ.symm x, h, by simp⟩`.
-/
theorem mem_Xsp_mapLF {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (x : S.V) :
    x ∈ Xsp (Formalism.L2.SG.TermOp.mapLF γ F) ↔ γ.symm x ∈ Xsp F := by
  have h1 : Xsp (Formalism.L2.SG.TermOp.mapLF γ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) := by
    unfold Formalism.L2.SG.TermOp.mapLF
    rw [dif_pos hγ]
    show Submodule.span E (Set.range fun a => γ (F.fl.e a)) =
      (Submodule.span E (Set.range F.fl.e)).map (γ : S.V →ₗ[E] S.V)
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [h1]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

end Gen

section Terms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

/- English proof (translation)
Unfold `GTerm.frame`. Rewrite using `[mem_Xsp_mapLF (γ := t.lin) t.rep.2.2.1, mem_Xsp_mapLF (γ := t'.lin) t'.rep.2.2.1]`. Establish `h : t'.lin.symm ((t'.lin * t.lin⁻¹) x) = t.lin.symm x` using `by show t'.lin.symm (t'.lin (t.lin.symm x)) = t.lin.symm x`. Simplify using the standard rewrite rules. Rewrite using `[h]`.
-/
theorem frame_mem_iff (t t' : GTerm X u u' F0 F0' what₂ rows') (x : (VS D).V) :
    x ∈ Xsp t.frame ↔ (t'.lin * t.lin⁻¹) x ∈ Xsp t'.frame := by
  unfold GTerm.frame
  rw [mem_Xsp_mapLF (γ := t.lin) t.rep.2.2.1, mem_Xsp_mapLF (γ := t'.lin) t'.rep.2.2.1]
  have h : t'.lin.symm ((t'.lin * t.lin⁻¹) x) = t.lin.symm x := by
    show t'.lin.symm (t'.lin (t.lin.symm x)) = t.lin.symm x
    simp
  rw [h]

end Terms

/- English proof (translation)
Introduce `D X Y u u' _hT`. Establish `hdim` using `Formalism.L2.SG.Corank.finrank_VS D`. Establish `hGv : ∀ t ∈ (Y.tO u u').ngSet, Gval (lf D (X.Fu u)) t.frame ≠ 0`. Introduce `t ht h`. Apply `ht.1` to reduce the goal to its premises.

Use `show Formalism.L2.SG.TermOp.Gt t = 0`. Unfold `Formalism.L2.SG.TermOp.Gt`. Rewrite using `[if_pos ((Formalism.L2.SG.Pf.SatGram.gterm_G Y t).trans h)]`. Establish `hlat : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), Submodule.IsLattice D.host.E t.lam` using `fun t => ((Y.rowsOK u).1 t.lam t.mem).2.1.1`. Establish `hLF : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), IsLift t.lam (lf D (X.Fu u))` using `fun t => ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1`.

Establish `hLt : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), IsLift t.lam t.frame` using `fun t => t.rep.2.2.2.2.1`. Use `⟨fun t ht => ?_, fun t ht t' ht' hr h1 => ?_, fun t ht t' ht' t'' ht'' hr1 hr2 h1 h2 => ?_⟩` and prove the remaining obligations. Use `show Formalism.L2.SG.TermOp.s0T t t = 1`. Unfold `Formalism.L2.SG.TermOp.s0T`. Rewrite using `[if_pos ⟨rfl, rfl⟩, mul_inv_cancel]`.

Conclude with `(s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t.frame 1 (hLF t) (hLt t) (hGv t ht)).2 (Th_one _ _ _)`. Establish `hlam : t.lam = t'.lam` using `congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr`. Establish `hlam' : t.lam' = t'.lam'` using `congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr`. Establish `h1' : Formalism.L2.SG.TermOp.s0T t t' = 1` using `h1`. Use `show Formalism.L2.SG.TermOp.s0T t' t = 1`.

Unfold `Formalism.L2.SG.TermOp.s0T at h1' ⊢`. Rewrite `h1'` using `[if_pos ⟨hlam, hlam'⟩]`. Rewrite using `[if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]`. Establish `hth` using `(s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t) (hGv t ht)).1 h1'`. Establish `hL' : IsLift t.lam t'.frame` using `by rw [hlam]; exact hLt t'`.

Establish `hsym` using `Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL' (hGv t ht) (hGv t' ht') (frame_mem_iff t t') hth`. Establish `hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹` using `by group`. Rewrite `hsym` using `[hinv]`. Conclude with `(s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' ht')).2 hsym`. Establish `hl1 : t.lam = t'.lam` using `congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1`.

Establish `hl1' : t.lam' = t'.lam'` using `congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1`. Establish `hl2 : t'.lam = t''.lam` using `congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2`. Establish `hl2' : t'.lam' = t''.lam'` using `congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2`. Establish `h1' : Formalism.L2.SG.TermOp.s0T t t' = 1` using `h1`. Establish `h2' : Formalism.L2.SG.TermOp.s0T t' t'' = 1` using `h2`.

Use `show Formalism.L2.SG.TermOp.s0T t t'' = 1`. Unfold `Formalism.L2.SG.TermOp.s0T at h1' h2' ⊢`. Rewrite `h1'` using `[if_pos ⟨hl1, hl1'⟩]`. Rewrite `h2'` using `[if_pos ⟨hl2, hl2'⟩, ← hl1]`. Rewrite using `[if_pos ⟨hl1.trans hl2, hl1'.trans hl2'⟩]`.

Establish `hL' : IsLift t.lam t'.frame` using `by rw [hl1]; exact hLt t'`. Establish `hth1` using `(s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t) (hGv t ht)).1 h1'`. Establish `hth2` using `(s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t''.frame _ (hLF t) hL' (hGv t' ht')).1 h2'`. Establish `htr` using `Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹) (t''.lin * t'.lin⁻¹) (fun x hx => (frame_mem_iff t' t'' x).1 hx) hth1 hth2`. Establish `hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹` using `by group`.

Rewrite `htr` using `[hmul]`. Conclude with `(s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t''.frame _ (hLF t) (hLt t) (hGv t ht)).2 htr`.
-/
theorem corankOne_equivalence_holds : CorankOneEquivalence := by
  intro D X Y u u' _hT
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t ∈ (Y.tO u u').ngSet, Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro t ht h
    apply ht.1
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos ((Formalism.L2.SG.Pf.SatGram.gterm_G Y t).trans h)]
  have hlat : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      Submodule.IsLattice D.host.E t.lam := fun t => ((Y.rowsOK u).1 t.lam t.mem).2.1.1
  have hLF : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      IsLift t.lam (lf D (X.Fu u)) := fun t => ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), IsLift t.lam t.frame :=
    fun t => t.rep.2.2.2.2.1
  refine ⟨fun t ht => ?_, fun t ht t' ht' hr h1 => ?_, fun t ht t' ht' t'' ht'' hr1 hr2 h1 h2 => ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨rfl, rfl⟩, mul_inv_cancel]
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t.frame 1 (hLF t) (hLt t) (hGv t ht)).2
      (Th_one _ _ _)
  · have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' ⊢
    rw [if_pos ⟨hlam, hlam'⟩] at h1'
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    have hth := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
    have hsym := Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
      (hGv t ht) (hGv t' ht') (frame_mem_iff t t') hth
    have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
    rw [hinv] at hsym
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' ht')).2 hsym
  · have hl1 : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl1' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl2 : t'.lam = t''.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have hl2' : t'.lam' = t''.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    have h2' : Formalism.L2.SG.TermOp.s0T t' t'' = 1 := h2
    show Formalism.L2.SG.TermOp.s0T t t'' = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' h2' ⊢
    rw [if_pos ⟨hl1, hl1'⟩] at h1'
    rw [if_pos ⟨hl2, hl2'⟩, ← hl1] at h2'
    rw [if_pos ⟨hl1.trans hl2, hl1'.trans hl2'⟩]
    have hL' : IsLift t.lam t'.frame := by rw [hl1]; exact hLt t'
    have hth1 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hth2 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t''.frame _ (hLF t) hL'
      (hGv t' ht')).1 h2'
    have htr := Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹) (t''.lin * t'.lin⁻¹)
      (fun x hx => (frame_mem_iff t' t'' x).1 hx) hth1 hth2
    have hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹ := by group
    rw [hmul] at htr
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t''.frame _ (hLF t) (hLt t) (hGv t ht)).2 htr

end Formalism.L2.SG.NGCut.CorankRelation

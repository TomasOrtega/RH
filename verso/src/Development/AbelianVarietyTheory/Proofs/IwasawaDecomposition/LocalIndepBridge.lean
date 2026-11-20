import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.Pst Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace GlobalTheory.Pst
namespace BridgeInd

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

/- English proof (translation)
Use `set S := IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => B.j (algebraMap E Ω x)) with hS`. Establish `hfin : FiniteDimensional ℚ_[l] S` using `GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (B.j.comp (algebraMap E Ω))`. Establish `hcl : IsClosed (S : Set (Om l))` using `Submodule.closed_of_finiteDimensional (S.toSubalgebra.toSubmodule)`. Use `le_antisymm (fun x hx => ?_) ?_` and prove the remaining obligations. Establish `h1` using `B.j_dense hx`.

Establish `h2 : closure (Set.range fun x : E => B.j (algebraMap E Ω x)) ⊆ (S : Set (Om l))` using `closure_minimal (IntermediateField.subset_adjoin _ _) hcl`. Conclude with `h2 h1`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `B.j_E x`.
-/
theorem kw_eq_adjoin (B : LocBridge l E Ω Gw O) :
    B.Kw.1 = IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => B.j (algebraMap E Ω x)) := by
  set S := IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => B.j (algebraMap E Ω x)) with hS
  have hfin : FiniteDimensional ℚ_[l] S :=
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (B.j.comp (algebraMap E Ω))
  have hcl : IsClosed (S : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (S.toSubalgebra.toSubmodule)
  refine le_antisymm (fun x hx => ?_) ?_
  · have h1 := B.j_dense hx
    have h2 : closure (Set.range fun x : E => B.j (algebraMap E Ω x)) ⊆ (S : Set (Om l)) :=
      closure_minimal (IntermediateField.subset_adjoin _ _) hcl
    exact h2 h1
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact B.j_E x

end BridgeInd
end GlobalTheory.Pst

namespace GlobalTheory.Pst
namespace BridgeInd

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']

/- English proof (translation)
Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed E`. Establish `hd : DenseRange B.j` using `GlobalTheory.PlaceBridge.denseRange_embedding B.j`. Take `⟨g, hg⟩` from `GlobalTheory.PlaceBridge.exists_algEquiv B.j B'.j hd (GlobalTheory.PlaceBridge.norm_eq_of_le_one_iff B.j B'.j fun x => (hB x).symm.trans (hB' x))`. Use `⟨g, hg, fun x => ?_⟩` and prove the remaining obligations. Establish `hm : B'.Kw.1 = B.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l)`.

Rewrite using `[kw_eq_adjoin B, kw_eq_adjoin B', IntermediateField.adjoin_map, ← Set.range_comp]`. Conclude with `congrArg _ (congrArg Set.range (funext fun y => (hg _).symm))`. Rewrite using `[hm, IntermediateField.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨x, hx, rfl⟩`. Introduce and unpack `⟨y, hy, hyx⟩`. Establish `: y = x` using `g.injective hyx`. Conclude with `this ▸ hy`.
-/
theorem exists_conj [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    (B : LocBridge l E Ω (Dec (F := E) A) O) (B' : LocBridge l E Ω (Dec (F := E) A) O')
    (hB : Induces B) (hB' : Induces B') :
    ∃ g : GQ l, (∀ x, g (B.j x) = B'.j x) ∧ ∀ x, x ∈ B.Kw.1 ↔ g x ∈ B'.Kw.1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hd : DenseRange B.j := GlobalTheory.PlaceBridge.denseRange_embedding B.j
  obtain ⟨g, hg⟩ := GlobalTheory.PlaceBridge.exists_algEquiv B.j B'.j hd
    (GlobalTheory.PlaceBridge.norm_eq_of_le_one_iff B.j B'.j fun x => (hB x).symm.trans (hB' x))
  refine ⟨g, hg, fun x => ?_⟩
  have hm : B'.Kw.1 = B.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l) := by
    rw [kw_eq_adjoin B, kw_eq_adjoin B', IntermediateField.adjoin_map, ← Set.range_comp]
    exact congrArg _ (congrArg Set.range (funext fun y => (hg _).symm))
  rw [hm, IntermediateField.mem_map]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := g.injective hyx
    exact this ▸ hy

end BridgeInd
end GlobalTheory.Pst

namespace GlobalTheory.Pst
namespace BridgeInd

section Transport

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

/- English proof (translation)
Rewrite `hh`, the goal using `[GK, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `y hy`. Establish `hy' : g⁻¹ y ∈ K.1` using `(hK _).2 (by rwa [show g (g⁻¹ y) = y from g.apply_symm_apply y])`. Use `show g (h (g⁻¹ y)) = y`. Rewrite using `[hh _ hy']`.

Conclude with `g.apply_symm_apply y`.
-/
theorem mem_GK_conj {K K' : FinExt l} {g : GQ l} (hK : ∀ x, x ∈ K.1 ↔ g x ∈ K'.1) {h : GQ l}
    (hh : h ∈ GK K) : g * h * g⁻¹ ∈ GK K' := by
  rw [GK, IntermediateField.mem_fixingSubgroup_iff] at hh ⊢
  intro y hy
  have hy' : g⁻¹ y ∈ K.1 := (hK _).2 (by rwa [show g (g⁻¹ y) = y from g.apply_symm_apply y])
  show g (h (g⁻¹ y)) = y
  rw [hh _ hy']
  exact g.apply_symm_apply y

/- English proof (translation)
Rewrite `hh`, the goal using `[GK, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `y hy`. Use `show g⁻¹ (h (g y)) = y`. Rewrite using `[hh _ ((hK y).1 hy)]`. Conclude with `g.symm_apply_apply y`.
-/
theorem mem_GK_conj_inv {K K' : FinExt l} {g : GQ l} (hK : ∀ x, x ∈ K.1 ↔ g x ∈ K'.1) {h : GQ l}
    (hh : h ∈ GK K') : g⁻¹ * h * g ∈ GK K := by
  rw [GK, IntermediateField.mem_fixingSubgroup_iff] at hh ⊢
  intro y hy
  show g⁻¹ (h (g y)) = y
  rw [hh _ ((hK y).1 hy)]
  exact g.symm_apply_apply y

/- English proof (translation)
Establish `e : S.map (Φ : M →ₗ[LL] M) = S'`. Use extensionality with `y`. Rewrite using `[Submodule.mem_map_equiv, h, Φ.apply_symm_apply]`. Rewrite using `[← e, LinearEquiv.finrank_map_eq]`.
-/
theorem finrank_eq_of_mem_iff {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M] (Φ : M ≃ₗ[LL] M)
    (S S' : Submodule LL M) (h : ∀ x, x ∈ S ↔ Φ x ∈ S') : finrank LL ↥S = finrank LL ↥S' := by
  have e : S.map (Φ : M →ₗ[LL] M) = S' := by
    ext y
    rw [Submodule.mem_map_equiv, h, Φ.apply_symm_apply]
  rw [← e, LinearEquiv.finrank_map_eq]

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[IntermediateField.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨g⁻¹ y, (h _).2 (by rwa [show g (g⁻¹ y) = y from g.apply_symm_apply y]), g.apply_symm_apply y⟩`.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(h x).1 hx`.
-/
theorem map_eq_of_mem_iff {S S' : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (h : ∀ x, x ∈ S ↔ g x ∈ S') :
    S' = S.map (g : Om l →ₐ[ℚ_[l]] Om l) := by
  ext y
  rw [IntermediateField.mem_map]
  constructor
  · intro hy
    exact ⟨g⁻¹ y, (h _).2 (by rwa [show g (g⁻¹ y) = y from g.apply_symm_apply y]), g.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx

/- English proof (translation)
Rewrite using `[e, IntermediateField.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨x, hx, rfl⟩`. Introduce and unpack `⟨y, hy, hyx⟩`.

Establish `: y = x` using `g.injective hyx`. Conclude with `this ▸ hy`.
-/
theorem mem_iff_of_map_eq {S S' : IntermediateField ℚ_[l] (Om l)} {g : GQ l}
    (e : S' = S.map (g : Om l →ₐ[ℚ_[l]] Om l)) (x : Om l) : x ∈ S ↔ g x ∈ S' := by
  rw [e, IntermediateField.mem_map]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := g.injective hyx
    exact this ▸ hy

/- English proof (translation)
Rewrite using `[map_eq_of_mem_iff h]`. Conclude with `(IntermediateField.equivMap S _).toLinearEquiv.finrank_eq`.
-/
theorem finrank_eq_of_mem_iff_field {S S' : IntermediateField ℚ_[l] (Om l)} {g : GQ l}
    (h : ∀ x, x ∈ S ↔ g x ∈ S') : finrank ℚ_[l] ↥S = finrank ℚ_[l] ↥S' := by
  rw [map_eq_of_mem_iff h]
  exact (IntermediateField.equivMap S _).toLinearEquiv.finrank_eq

/- English proof (translation)
Use `mem_iff_of_map_eq ?_ x` and prove the remaining obligations. Rewrite using `[MaximalUnramifiedExtension, IntermediateField.adjoin_map]`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, hm, hl, hy⟩`. Use `⟨g⁻¹ y, ⟨m, hm, hl, ?_⟩, g.apply_symm_apply y⟩` and prove the remaining obligations. Rewrite using `[← map_pow, hy, map_one]`. Introduce and unpack `⟨x, ⟨m, hm, hl, hx⟩, rfl⟩`. Conclude with `⟨m, hm, hl, by rw [← map_pow]; simp [hx]⟩`.
-/
theorem mem_Kur_iff (g : GQ l) (x : Om l) : x ∈ MaximalUnramifiedExtension l ↔ g x ∈ MaximalUnramifiedExtension l := by
  refine mem_iff_of_map_eq ?_ x
  rw [MaximalUnramifiedExtension, IntermediateField.adjoin_map]
  congr 1
  ext y
  constructor
  · rintro ⟨m, hm, hl, hy⟩
    refine ⟨g⁻¹ y, ⟨m, hm, hl, ?_⟩, g.apply_symm_apply y⟩
    rw [← map_pow, hy, map_one]
  · rintro ⟨x, ⟨m, hm, hl, hx⟩, rfl⟩
    exact ⟨m, hm, hl, by rw [← map_pow]; simp [hx]⟩

end Transport

end BridgeInd
end GlobalTheory.Pst

namespace GlobalTheory.Pst
namespace BridgeInd

section Tensor

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

variable (LL V) in

def conjB (g : GQ l) : V ⊗[ℚ_[l]] P.R.B ≃ₗ[LL] V ⊗[ℚ_[l]] P.R.B :=
  AlgebraTensorModule.congr (LinearEquiv.refl LL V) (P.actQ g).toLinearEquiv

variable (LL V) in

def conjdR (g : GQ l) : V ⊗[ℚ_[l]] P.R.BdR ≃ₗ[LL] V ⊗[ℚ_[l]] P.R.BdR :=
  AlgebraTensorModule.congr (LinearEquiv.refl LL V) (P.actQdR g).toLinearEquiv

variable {K K' : FinExt l} {g : GQ l} {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K') V}
  (hρ : ∀ (h : ↥(GK K)) (h' : ↥(GK K')), (h' : GQ l) = g * h * g⁻¹ → ρ' h' = ρ h)

include hρ in
/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`. Simplify using `only [conjdR, actVdR, AlgebraTensorModule.congr_tmul, AlgebraTensorModule.map_tmul, LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, AlgEquiv.coe_algHom]`. Rewrite using `[hρ h h' hh, P.PD_actdR, P.PD_actdR, hh]`.

Use `congr 1`. Rewrite using `[← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem conjdR_actVdR (h : ↥(GK K)) (h' : ↥(GK K')) (hh : (h' : GQ l) = g * h * g⁻¹)
    (x : V ⊗[ℚ_[l]] P.R.BdR) :
    conjdR P LL V g (actVdR (P.PD K) ρ h x) = actVdR (P.PD K') ρ' h' (conjdR P LL V g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [conjdR, actVdR, AlgebraTensorModule.congr_tmul, AlgebraTensorModule.map_tmul,
      LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.coe_restrictScalars,
      AlgHom.toLinearMap_apply, AlgEquiv.coe_algHom]
    rw [hρ h h' hh, P.PD_actdR, P.PD_actdR, hh]
    congr 1
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (hK : ∀ x, x ∈ K.1 ↔ g x ∈ K'.1)
include hρ hK

/- English proof (translation)
Simplify using `only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `hx h'`. Set `h : ↥(GK K)` to `⟨g⁻¹ * h' * g, mem_GK_conj_inv hK h'.2⟩`. Establish `hh : (h' : GQ l) = g * h * g⁻¹` using `by show (h' : GQ l) = g * (g⁻¹ * h' * g) * g⁻¹ group`.

Rewrite using `[← conjdR_actVdR P hρ h h' hh, hx]`. Introduce `hx h`. Set `h' : ↥(GK K')` to `⟨g * h * g⁻¹, mem_GK_conj hK h.2⟩`. Apply `(conjdR P LL V g).injective` to reduce the goal to its premises. Rewrite using `[conjdR_actVdR P hρ h h' rfl, hx]`.
-/
theorem mem_DdR_conj (x : V ⊗[ℚ_[l]] P.R.BdR) :
    x ∈ DdR (P.PD K) ρ ↔ conjdR P LL V g x ∈ DdR (P.PD K') ρ' := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  constructor
  · intro hx h'
    let h : ↥(GK K) := ⟨g⁻¹ * h' * g, mem_GK_conj_inv hK h'.2⟩
    have hh : (h' : GQ l) = g * h * g⁻¹ := by
      show (h' : GQ l) = g * (g⁻¹ * h' * g) * g⁻¹
      group
    rw [← conjdR_actVdR P hρ h h' hh, hx]
  · intro hx h
    let h' : ↥(GK K') := ⟨g * h * g⁻¹, mem_GK_conj hK h.2⟩
    apply (conjdR P LL V g).injective
    rw [conjdR_actVdR P hρ h h' rfl, hx]

/- English proof (translation)
The claim follows from `finrank_eq_of_mem_iff _ _ _ (mem_DdR_conj P hρ hK)`.
-/
theorem finrank_DdR_conj : finrank LL ↥(DdR (P.PD K) ρ) = finrank LL ↥(DdR (P.PD K') ρ') :=
  finrank_eq_of_mem_iff _ _ _ (mem_DdR_conj P hρ hK)

end Tensor

end BridgeInd
end GlobalTheory.Pst

namespace GlobalTheory.Pst
namespace BridgeInd

section Fil

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

def botExt (l : ℕ) [Fact l.Prime] : FinExt l := ⟨⊥, inferInstance⟩

/- English proof (translation)
The claim follows from `(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => by obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hx exact σ.commutes r`.
-/
theorem mem_GK_bot (σ : GQ l) : σ ∈ GK (botExt l) :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => by
    obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact σ.commutes r

/- English proof (translation)
Establish `e` using `P.PD_Fil K (botExt l) a`. Rewrite `hb`, the goal using `[← SetLike.mem_coe, e]`. Use `(P.PD (botExt l)).Fil_G ⟨σ, mem_GK_bot σ⟩ a b hb` as an intermediate fact. Rewrite `this` using `[P.PD_actdR]`. Then use the resulting hypothesis.
-/
theorem fil_act (K : FinExt l) (σ : GQ l) (a : ℤ) {b : P.R.BdR} (hb : b ∈ (P.PD K).Fil a) :
    P.actQdR σ b ∈ (P.PD K).Fil a := by
  have e := P.PD_Fil K (botExt l) a
  rw [← SetLike.mem_coe, e] at hb ⊢
  have := (P.PD (botExt l)).Fil_G ⟨σ, mem_GK_bot σ⟩ a b hb
  rwa [P.PD_actdR] at this

/- English proof (translation)
Establish `e : ((P.PD K).Fil a).restrictScalars ℚ_[l] = ((P.PD K').Fil a).restrictScalars ℚ_[l]` using `SetLike.coe_injective (P.PD_Fil K K' a)`. Unfold `FilV`. Rewrite using `[e]`.
-/
theorem filV_eq (K K' : FinExt l) (a : ℤ) :
    FilV (P.PD K) (LL := LL) (V := V) a = FilV (P.PD K') (LL := LL) (V := V) a := by
  have e : ((P.PD K).Fil a).restrictScalars ℚ_[l] = ((P.PD K').Fil a).restrictScalars ℚ_[l] :=
    SetLike.coe_injective (P.PD_Fil K K' a)
  unfold FilV
  rw [e]

/- English proof (translation)
Take `⟨z, rfl⟩` from `hx`. Set `r : ↥(((P.PD K).Fil a).restrictScalars ℚ_[l]) →ₗ[ℚ_[l]] ↥(((P.PD K).Fil a).restrictScalars ℚ_[l])` to `(P.actQdR σ).toLinearMap.restrict fun b hb => fil_act P K σ a hb`. Use `⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) r z, ?_⟩` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul v b => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem conjdR_mem_filV (K : FinExt l) (σ : GQ l) (a : ℤ) {x : V ⊗[ℚ_[l]] P.R.BdR}
    (hx : x ∈ FilV (P.PD K) (LL := LL) (V := V) a) : conjdR P LL V σ x ∈ FilV (P.PD K) (LL := LL) (V := V) a := by
  obtain ⟨z, rfl⟩ := hx
  let r : ↥(((P.PD K).Fil a).restrictScalars ℚ_[l]) →ₗ[ℚ_[l]] ↥(((P.PD K).Fil a).restrictScalars ℚ_[l]) :=
    (P.actQdR σ).toLinearMap.restrict fun b hb => fil_act P K σ a hb
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) r z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`. Simplify using `only [conjdR, AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply]`. Rewrite using `[← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]`.

Both sides reduce to the same expression. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem conjdR_inv (σ : GQ l) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    conjdR P LL V σ⁻¹ (conjdR P LL V σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [conjdR, AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply]
    rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Rewrite using `[← filV_eq P K K' a]`. Use `⟨conjdR_mem_filV P K σ a, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[← conjdR_inv P (LL := LL) σ x]`. Conclude with `conjdR_mem_filV P K σ⁻¹ a h`.
-/
theorem mem_filV_conj (K K' : FinExt l) (σ : GQ l) (a : ℤ) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    x ∈ FilV (P.PD K) (LL := LL) (V := V) a ↔ conjdR P LL V σ x ∈ FilV (P.PD K') (LL := LL) (V := V) a := by
  rw [← filV_eq P K K' a]
  refine ⟨conjdR_mem_filV P K σ a, fun h => ?_⟩
  rw [← conjdR_inv P (LL := LL) σ x]
  exact conjdR_mem_filV P K σ⁻¹ a h

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`. Simplify using `only [conjdR, mulVdR, AlgebraTensorModule.congr_tmul, AlgebraTensorModule.map_tmul, LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.id_apply, LinearMap.mulLeft_apply]`. Use `congr 1`.

Rewrite using `[map_mul]`. Use `congr 1`. Use `show P.actQdR g (algebraMap (Om l) P.R.BdR (c : Om l)) = algebraMap (Om l) P.R.BdR (c' : Om l)`. Rewrite using `[P.actQdR_Om, hc]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem conjdR_mulVdR {K K' : FinExt l} (g : GQ l) (c : ↥K.1) (c' : ↥K'.1) (hc : (c' : Om l) = g c)
    (x : V ⊗[ℚ_[l]] P.R.BdR) :
    conjdR P LL V g (mulVdR (K := ↥K.1) (BdR := P.R.BdR) (V := V) (LL := LL) c x) =
      mulVdR (K := ↥K'.1) (BdR := P.R.BdR) (V := V) (LL := LL) c' (conjdR P LL V g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [conjdR, mulVdR, AlgebraTensorModule.congr_tmul, AlgebraTensorModule.map_tmul,
      LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.id_apply, LinearMap.mulLeft_apply]
    congr 1
    rw [map_mul]
    congr 1
    show P.actQdR g (algebraMap (Om l) P.R.BdR (c : Om l)) = algebraMap (Om l) P.R.BdR (c' : Om l)
    rw [P.actQdR_Om, hc]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {K K' : FinExt l} {g : GQ l} {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K') V}
  (hρ : ∀ (h : ↥(GK K)) (h' : ↥(GK K')), (h' : GQ l) = g * h * g⁻¹ → ρ' h' = ρ h)
  (hK : ∀ x, x ∈ K.1 ↔ g x ∈ K'.1)
include hρ hK

/- English proof (translation)
Simplify using `only [FildR, DdRE, Submodule.mem_inf]`. Use `and_congr (and_congr (mem_DdR_conj P hρ hK x) ?_) (mem_filV_conj P K K' g a x)` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `hx c'`.

Establish `hm : g⁻¹ (c' : Om l) ∈ K.1` using `(hK _).2 (by rw [show g (g⁻¹ (c' : Om l)) = c' from g.apply_symm_apply _]; exact c'.2)`. Set `c : ↥K.1` to `⟨g⁻¹ (c' : Om l), hm⟩`. Establish `hc : (c' : Om l) = g c` using `(g.apply_symm_apply _).symm`. Rewrite using `[← conjdR_mulVdR P g c c' hc, hx c, map_smul, hτ c c' hc]`. Introduce `hx c`.

Set `c' : ↥K'.1` to `⟨g c, (hK _).1 c.2⟩`. Apply `(conjdR P LL V g).injective` to reduce the goal to its premises. Rewrite using `[conjdR_mulVdR P g c c' rfl, hx c', map_smul, hτ c c' rfl]`.
-/
theorem mem_FildR_conj (τ₁ : ↥K.1 →ₐ[ℚ_[l]] LL) (τ₂ : ↥K'.1 →ₐ[ℚ_[l]] LL)
    (hτ : ∀ (c : ↥K.1) (c' : ↥K'.1), (c' : Om l) = g c → τ₂ c' = τ₁ c) (a : ℤ) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    x ∈ FildR (P.PD K) ρ τ₁ a ↔ conjdR P LL V g x ∈ FildR (P.PD K') ρ' τ₂ a := by
  simp only [FildR, DdRE, Submodule.mem_inf]
  refine and_congr (and_congr (mem_DdR_conj P hρ hK x) ?_) (mem_filV_conj P K K' g a x)
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro hx c'
    have hm : g⁻¹ (c' : Om l) ∈ K.1 :=
      (hK _).2 (by rw [show g (g⁻¹ (c' : Om l)) = c' from g.apply_symm_apply _]; exact c'.2)
    let c : ↥K.1 := ⟨g⁻¹ (c' : Om l), hm⟩
    have hc : (c' : Om l) = g c := (g.apply_symm_apply _).symm
    rw [← conjdR_mulVdR P g c c' hc, hx c, map_smul, hτ c c' hc]
  · intro hx c
    let c' : ↥K'.1 := ⟨g c, (hK _).1 c.2⟩
    apply (conjdR P LL V g).injective
    rw [conjdR_mulVdR P g c c' rfl, hx c', map_smul, hτ c c' rfl]

/- English proof (translation)
Unfold `multV`. Rewrite using `[finrank_eq_of_mem_iff _ _ _ (mem_FildR_conj P hρ hK τ₁ τ₂ hτ a), finrank_eq_of_mem_iff _ _ _ (mem_FildR_conj P hρ hK τ₁ τ₂ hτ (a + 1))]`.
-/
theorem multV_conj (τ₁ : ↥K.1 →ₐ[ℚ_[l]] LL) (τ₂ : ↥K'.1 →ₐ[ℚ_[l]] LL)
    (hτ : ∀ (c : ↥K.1) (c' : ↥K'.1), (c' : Om l) = g c → τ₂ c' = τ₁ c) (a : ℤ) :
    multV (P.PD K) ρ τ₁ a = multV (P.PD K') ρ' τ₂ a := by
  unfold multV
  rw [finrank_eq_of_mem_iff _ _ _ (mem_FildR_conj P hρ hK τ₁ τ₂ hτ a),
    finrank_eq_of_mem_iff _ _ _ (mem_FildR_conj P hρ hK τ₁ τ₂ hτ (a + 1))]

end Fil

end BridgeInd
end GlobalTheory.Pst

namespace GlobalTheory.Pst
namespace BridgeInd

section Bridges

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
  (B : LocBridge l E Ω Gw O) (B' : LocBridge l E Ω Gw O') {g : GQ l} (hg : ∀ x, g (B.j x) = B'.j x)
include hg

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `AlgEquiv.ext` to reduce the goal to its premises. Introduce `x`. Apply `B'.j.injective` to reduce the goal to its premises. Establish `h1` using `B'.e_comm (B'.e.symm h') x`.

Establish `h2` using `B.e_comm (B.e.symm h) x`. Rewrite `h1`, `h2` using `[MulEquiv.apply_symm_apply]`. Rewrite using `[← h1, hh, ← hg, ← hg]`. Use `show g ((h : GQ l) (g⁻¹ (g (B.j x)))) = g (B.j _)`. Rewrite using `[show g⁻¹ (g (B.j x)) = B.j x from g.symm_apply_apply _, h2]`.
-/
theorem e_symm_conj (h : ↥(GK B.Kw)) (h' : ↥(GK B'.Kw)) (hh : (h' : GQ l) = g * h * g⁻¹) :
    B'.e.symm h' = B.e.symm h := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply B'.j.injective
  have h1 := B'.e_comm (B'.e.symm h') x
  have h2 := B.e_comm (B.e.symm h) x
  rw [MulEquiv.apply_symm_apply] at h1 h2
  rw [← h1, hh, ← hg, ← hg]
  show g ((h : GQ l) (g⁻¹ (g (B.j x)))) = g (B.j _)
  rw [show g⁻¹ (g (B.j x)) = B.j x from g.symm_apply_apply _, h2]

/- English proof (translation)
Simplify using `only [LocBridge.repE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]`. Rewrite using `[e_symm_conj B B' hg h h' hh]`.
-/
theorem repE_conj (L : FinExt l) {m : ℕ} (r : ↥Gw →* GL (Fin m) ↥L.1) (h : ↥(GK B.Kw)) (h' : ↥(GK B'.Kw))
    (hh : (h' : GQ l) = g * h * g⁻¹) : B'.repE L r h' = B.repE L r h := by
  simp only [LocBridge.repE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [e_symm_conj B B' hg h h' hh]

end Bridges

variable {l : ℕ} [Fact l.Prime]

def pullExt {K K' : FinExt l} (g : GQ l) (hK : ∀ x, x ∈ K.1 ↔ g x ∈ K'.1) : ↥K'.1 →ₐ[ℚ_[l]] ↥K.1 :=
  ((g⁻¹ : GQ l).toAlgHom.comp K'.1.val).codRestrict K.1.toSubalgebra fun c =>
    (hK _).2 (by show g (g⁻¹ (c : Om l)) ∈ K'.1; rw [show g (g⁻¹ (c : Om l)) = c from g.apply_symm_apply _]; exact c.2)

end BridgeInd

end GlobalTheory.Pst

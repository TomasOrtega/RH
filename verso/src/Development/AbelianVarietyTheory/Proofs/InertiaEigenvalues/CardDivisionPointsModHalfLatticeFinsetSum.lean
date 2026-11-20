import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceModelIndicatorEqMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.DivPtFourier.Prod

/- English proof (translation)
Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i hi' => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => ho i hi' j hj (Ne.symm hji)) (fun h => absurd hi' h), hi i hi']`.
-/
theorem sum_idem {D : D7} {ι : Type} (s : Finset ι) (cs : ι → AE D)
    (hi : ∀ i ∈ s, cs i * cs i = cs i) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cs i * cs j = 0) :
    (∑ i ∈ s, cs i) * (∑ i ∈ s, cs i) = ∑ i ∈ s, cs i := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi' => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => ho i hi' j hj (Ne.symm hji))
    (fun h => absurd hi' h), hi i hi']

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_eq_zero ho`.
-/
theorem sum_orth {D : D7} {ι : Type} (s : Finset ι) (cs : ι → AE D) (i : ι) (hi : i ∉ s)
    (ho : ∀ j ∈ s, cs i * cs j = 0) : cs i * (∑ j ∈ s, cs j) = 0 := by
  rw [Finset.mul_sum]; exact Finset.sum_eq_zero ho

set_option maxHeartbeats 800000 in
/- English proof (translation)
Establish `h₂₁ : c₂ * c₁ = 0` using `by rw [mul_comm]; exact h₁₂`. Establish `orth : ∀ (a b : AE D), a * b = 0 → ∀ x : WO S T, b • x = x → a • x = 0`. Introduce `a b hab x hx`. Rewrite using `[← hx, smul_smul, hab, zero_smul]`. Establish `gmem : ∀ (c : AE D), c * c = c → ∀ y ∈ divPts Λ (c₁ + c₂) N, c • y ∈ divPts Λ c N`.

Introduce `c hc y hy`. Use `⟨by rw [smul_smul, hc], ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `hst c hc _ hy.2`. Set `g : ∀ (c : AE D), c * c = c → ↥(divPts Λ (c₁ + c₂) N) →+ ↥(divPts Λ c N)` to `fun c hc => { toFun := fun y => ⟨c • (y : WO S T), gmem c hc _ y.2⟩ map_zero' := Subtype.ext (smul_zero _) map_add' := fun x y => Subtype.ext (smul_add _ _ _) }`.

Set `φ : ↥(divPts Λ (c₁ + c₂) N) →+ DQ Λ c₁ N × DQ Λ c₂ N` to `((QuotientAddGroup.mk' _).comp (g c₁ h₁)).prod ((QuotientAddGroup.mk' _).comp (g c₂ h₂))`. Establish `hker : ∀ (c : AE D) (hc : c * c = c) (y : ↥(divPts Λ (c₁ + c₂) N)), (QuotientAddGroup.mk' ((Λ ⊓ GlobalTheory.PlaceModel.half S T c).addSubgroupOf (divPts Λ c N))) (g c hc y) = 0 ↔ c • (y : WO S T) ∈ Λ`. Introduce `c hc y`. Rewrite using `[QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, (GlobalTheory.PlaceModel.mem_half S T).2 (gmem c hc _ y.2).1⟩⟩`.

Establish `hle : (Λ ⊓ GlobalTheory.PlaceModel.half S T (c₁ + c₂)).addSubgroupOf (divPts Λ (c₁ + c₂) N) ≤ φ.ker`. Introduce `y hy`. Rewrite `hy` using `[AddSubgroup.mem_addSubgroupOf]`. Rewrite using `[AddMonoidHom.mem_ker]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Conclude with `(hker c₁ h₁ y).2 (hst c₁ h₁ _ hy.1)`. Conclude with `(hker c₂ h₂ y).2 (hst c₂ h₂ _ hy.1)`. Set `ψ'` to `QuotientAddGroup.lift _ φ hle`. Establish `hbij : Function.Bijective ψ'`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `q hq`. Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H y`. Establish `e` using `hq`.

Express the relevant statement in the definitionally equal form `φ y = 0 at e`. Establish `e1` using `(hker c₁ h₁ y).1 (congrArg Prod.fst e)`. Establish `e2` using `(hker c₂ h₂ y).1 (congrArg Prod.snd e)`. Rewrite using `[QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Establish `hy : (c₁ + c₂) • (y : WO S T) = y` using `y.2.1`.

Use `⟨?_, (GlobalTheory.PlaceModel.mem_half S T).2 hy⟩` and prove the remaining obligations. Rewrite using `[← hy, add_smul]`. Conclude with `Λ.add_mem e1 e2`. Introduce and unpack `⟨q₁, q₂⟩`. Proceed by induction on `q₁ using QuotientAddGroup.induction_on with`.

Consider the case `H y₁`. Proceed by induction on `q₂ using QuotientAddGroup.induction_on with`. Consider the case `H y₂`. Establish `a₁ : c₁ • (y₁ : WO S T) = y₁` using `y₁.2.1`. Establish `a₂ : c₂ • (y₂ : WO S T) = y₂` using `y₂.2.1`.

Establish `b₁ : c₁ • (y₂ : WO S T) = 0` using `orth c₁ c₂ h₁₂ _ a₂`. Establish `b₂ : c₂ • (y₁ : WO S T) = 0` using `orth c₂ c₁ h₂₁ _ a₁`. Establish `hmem : (y₁ : WO S T) + y₂ ∈ divPts Λ (c₁ + c₂) N`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_smul, smul_add, smul_add, a₁, a₂, b₁, b₂, add_zero, zero_add]`.

Rewrite using `[nsmul_add]`. Conclude with `Λ.add_mem y₁.2.2 y₂.2.2`. Use `⟨QuotientAddGroup.mk ⟨_, hmem⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ ⟨_, hmem⟩ = _`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `QuotientAddGroup.mk (g c₁ h₁ ⟨_, hmem⟩) = QuotientAddGroup.mk y₁`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `c₁ • ((y₁ : WO S T) + y₂) = y₁`. Rewrite using `[smul_add, a₁, b₁, add_zero]`.

Express the relevant statement in the definitionally equal form `QuotientAddGroup.mk (g c₂ h₂ ⟨_, hmem⟩) = QuotientAddGroup.mk y₂`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `c₂ • ((y₁ : WO S T) + y₂) = y₂`. Rewrite using `[smul_add, a₂, b₂, zero_add]`.

Rewrite using `[Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod]`.
-/
theorem card_add {D : D7} {S T : HSp D} (Λ : AddSubgroup (WO S T))
    (hst : ∀ c : AE D, c * c = c → ∀ u ∈ Λ, c • u ∈ Λ) (c₁ c₂ : AE D) (h₁ : c₁ * c₁ = c₁) (h₂ : c₂ * c₂ = c₂)
    (h₁₂ : c₁ * c₂ = 0) (N : ℕ) :
    Nat.card (DQ Λ (c₁ + c₂) N) = Nat.card (DQ Λ c₁ N) * Nat.card (DQ Λ c₂ N) := by
  have h₂₁ : c₂ * c₁ = 0 := by rw [mul_comm]; exact h₁₂
  have orth : ∀ (a b : AE D), a * b = 0 → ∀ x : WO S T, b • x = x → a • x = 0 := by
    intro a b hab x hx
    rw [← hx, smul_smul, hab, zero_smul]
  have gmem : ∀ (c : AE D), c * c = c → ∀ y ∈ divPts Λ (c₁ + c₂) N, c • y ∈ divPts Λ c N := by
    intro c hc y hy
    refine ⟨by rw [smul_smul, hc], ?_⟩
    rw [smul_comm]; exact hst c hc _ hy.2
  let g : ∀ (c : AE D), c * c = c → ↥(divPts Λ (c₁ + c₂) N) →+ ↥(divPts Λ c N) := fun c hc =>
    { toFun := fun y => ⟨c • (y : WO S T), gmem c hc _ y.2⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun x y => Subtype.ext (smul_add _ _ _) }
  let φ : ↥(divPts Λ (c₁ + c₂) N) →+ DQ Λ c₁ N × DQ Λ c₂ N :=
    ((QuotientAddGroup.mk' _).comp (g c₁ h₁)).prod ((QuotientAddGroup.mk' _).comp (g c₂ h₂))
  have hker : ∀ (c : AE D) (hc : c * c = c) (y : ↥(divPts Λ (c₁ + c₂) N)),
      (QuotientAddGroup.mk' ((Λ ⊓ GlobalTheory.PlaceModel.half S T c).addSubgroupOf (divPts Λ c N))) (g c hc y) = 0 ↔
        c • (y : WO S T) ∈ Λ := by
    intro c hc y
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact ⟨fun h => h.1, fun h => ⟨h, (GlobalTheory.PlaceModel.mem_half S T).2 (gmem c hc _ y.2).1⟩⟩
  have hle : (Λ ⊓ GlobalTheory.PlaceModel.half S T (c₁ + c₂)).addSubgroupOf (divPts Λ (c₁ + c₂) N) ≤ φ.ker := by
    intro y hy
    rw [AddSubgroup.mem_addSubgroupOf] at hy
    rw [AddMonoidHom.mem_ker]
    refine Prod.ext ?_ ?_
    · exact (hker c₁ h₁ y).2 (hst c₁ h₁ _ hy.1)
    · exact (hker c₂ h₂ y).2 (hst c₂ h₂ _ hy.1)
  let ψ' := QuotientAddGroup.lift _ φ hle
  have hbij : Function.Bijective ψ' := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H y =>
      have e := hq
      change φ y = 0 at e
      have e1 := (hker c₁ h₁ y).1 (congrArg Prod.fst e)
      have e2 := (hker c₂ h₂ y).1 (congrArg Prod.snd e)
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      have hy : (c₁ + c₂) • (y : WO S T) = y := y.2.1
      refine ⟨?_, (GlobalTheory.PlaceModel.mem_half S T).2 hy⟩
      rw [← hy, add_smul]; exact Λ.add_mem e1 e2
    · rintro ⟨q₁, q₂⟩
      induction q₁ using QuotientAddGroup.induction_on with
      | H y₁ =>
      induction q₂ using QuotientAddGroup.induction_on with
      | H y₂ =>
      have a₁ : c₁ • (y₁ : WO S T) = y₁ := y₁.2.1
      have a₂ : c₂ • (y₂ : WO S T) = y₂ := y₂.2.1
      have b₁ : c₁ • (y₂ : WO S T) = 0 := orth c₁ c₂ h₁₂ _ a₂
      have b₂ : c₂ • (y₁ : WO S T) = 0 := orth c₂ c₁ h₂₁ _ a₁
      have hmem : (y₁ : WO S T) + y₂ ∈ divPts Λ (c₁ + c₂) N := by
        refine ⟨?_, ?_⟩
        · rw [add_smul, smul_add, smul_add, a₁, a₂, b₁, b₂, add_zero, zero_add]
        · rw [nsmul_add]; exact Λ.add_mem y₁.2.2 y₂.2.2
      refine ⟨QuotientAddGroup.mk ⟨_, hmem⟩, ?_⟩
      change φ ⟨_, hmem⟩ = _
      refine Prod.ext ?_ ?_
      · change QuotientAddGroup.mk (g c₁ h₁ ⟨_, hmem⟩) = QuotientAddGroup.mk y₁
        congr 1; apply Subtype.ext; change c₁ • ((y₁ : WO S T) + y₂) = y₁
        rw [smul_add, a₁, b₁, add_zero]
      · change QuotientAddGroup.mk (g c₂ h₂ ⟨_, hmem⟩) = QuotientAddGroup.mk y₂
        congr 1; apply Subtype.ext; change c₂ • ((y₁ : WO S T) + y₂) = y₂
        rw [smul_add, a₂, b₂, zero_add]
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod]

/- English proof (translation)
Use `haveI : Subsingleton (DQ Λ (0 : AE D) N) := by`. Prove the components needed by the constructor for the conclusion. Introduce `q₁ q₂`. Proceed by induction on `q₁ using QuotientAddGroup.induction_on with`. Consider the case `H y₁`.

Proceed by induction on `q₂ using QuotientAddGroup.induction_on with`. Consider the case `H y₂`. Establish `e₁ : y₁ = 0` using `Subtype.ext (by rw [← y₁.2.1, zero_smul]; rfl)`. Establish `e₂ : y₂ = 0` using `Subtype.ext (by rw [← y₂.2.1, zero_smul]; rfl)`. Rewrite using `[e₁, e₂]`.

Conclude with `Nat.card_of_subsingleton (0 : DQ Λ (0 : AE D) N)`.
-/
theorem card_zero {D : D7} {S T : HSp D} (Λ : AddSubgroup (WO S T)) (N : ℕ) :
    Nat.card (DQ Λ (0 : AE D) N) = 1 := by
  haveI : Subsingleton (DQ Λ (0 : AE D) N) := by
    constructor
    intro q₁ q₂
    induction q₁ using QuotientAddGroup.induction_on with
    | H y₁ =>
    induction q₂ using QuotientAddGroup.induction_on with
    | H y₂ =>
    have e₁ : y₁ = 0 := Subtype.ext (by rw [← y₁.2.1, zero_smul]; rfl)
    have e₂ : y₂ = 0 := Subtype.ext (by rw [← y₂.2.1, zero_smul]; rfl)
    rw [e₁, e₂]
  exact Nat.card_of_subsingleton (0 : DQ Λ (0 : AE D) N)

end GlobalTheory.DivPtFourier.Prod

/- English proof (translation)
Introduce `D S T Λ hst ι s cs hi ho N`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using GlobalTheory.DivPtFourier.Prod.card_zero Λ N`. Consider the case `insert i s his ih`. Establish `hi' : ∀ j ∈ s, cs j * cs j = cs j` using `fun j hj => hi j (Finset.mem_insert_of_mem hj)`.

Establish `ho' : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → cs j * cs k = 0` using `fun j hj k hk hjk => ho j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk`. Rewrite using `[Finset.sum_insert his, Finset.prod_insert his, GlobalTheory.DivPtFourier.Prod.card_add Λ hst _ _ (hi i (Finset.mem_insert_self i s)) (GlobalTheory.DivPtFourier.Prod.sum_idem s cs hi' ho') (GlobalTheory.DivPtFourier.Prod.sum_orth s cs i his fun j hj => ho i (Finset.mem_insert_sel …`.
-/
theorem GlobalTheory.DivPtFourier.card_DQ_sum : ∀ {D : D7} {S T : HSp D} (Λ : AddSubgroup (WO S T)), (∀ c : AE D, c * c = c → ∀ u ∈ Λ, c • u ∈ Λ) → ∀ {ι : Type} (s : Finset ι) (cs : ι → AE D), (∀ i ∈ s, cs i * cs i = cs i) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → cs i * cs j = 0) → ∀ N : ℕ, Nat.card (GlobalTheory.DivPtFourier.DQ Λ (∑ i ∈ s, cs i) N) = ∏ i ∈ s, Nat.card (GlobalTheory.DivPtFourier.DQ Λ (cs i) N) := by
  intro D S T Λ hst ι s cs hi ho N
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.DivPtFourier.Prod.card_zero Λ N
  | insert i s his ih =>
    have hi' : ∀ j ∈ s, cs j * cs j = cs j := fun j hj => hi j (Finset.mem_insert_of_mem hj)
    have ho' : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → cs j * cs k = 0 := fun j hj k hk hjk =>
      ho j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    rw [Finset.sum_insert his, Finset.prod_insert his,
      GlobalTheory.DivPtFourier.Prod.card_add Λ hst _ _ (hi i (Finset.mem_insert_self i s))
        (GlobalTheory.DivPtFourier.Prod.sum_idem s cs hi' ho')
        (GlobalTheory.DivPtFourier.Prod.sum_orth s cs i his fun j hj =>
          ho i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj) (fun h => his (h ▸ hj))),
      ih hi' ho']

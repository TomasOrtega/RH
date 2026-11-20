import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

noncomputable section

namespace GlobalTheory.CompanionTheory.Lattice

open CompanionTheory.Rg.FlB
open scoped NormedField Valued

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp, by simp⟩`. Consider the case `insert i s _ ih`. Take `⟨d, hd, h⟩` from `ih`. Take `⟨a, ha, hi⟩` from `hfrac (g i)`.

Use `⟨a * d, by simp [ha, hd], fun j hj => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hj with rfl | hj` into its components or cases. Establish `: ((a * d : O) : L) * g j = (d : L) * ((a : L) * g j)` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `O.mul_mem d.2 hi`.

Establish `: ((a * d : O) : L) * g j = (a : L) * ((d : L) * g j)` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `O.mul_mem a.2 (h j hj)`.
-/
theorem exists_common_denom {L ι : Type} [Field L] (O : Subring L)
    (hfrac : ∀ x : L, ∃ a : O, (a : L) ≠ 0 ∧ (a : L) * x ∈ O) (s : Finset ι) (g : ι → L) :
    ∃ d : O, (d : L) ≠ 0 ∧ ∀ i ∈ s, (d : L) * g i ∈ O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert i s _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, ha, hi⟩ := hfrac (g i)
    refine ⟨a * d, by simp [ha, hd], fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · have : ((a * d : O) : L) * g j = (d : L) * ((a : L) * g j) := by push_cast; ring
      rw [this]
      exact O.mul_mem d.2 hi
    · have : ((a * d : O) : L) * g j = (a : L) * ((d : L) * g j) := by push_cast; ring
      rw [this]
      exact O.mul_mem a.2 (h j hj)

/- English proof (translation)
Set `ψ : (Fin m → O) →ₗ[O] V` to `{ toFun := fun y => c⁻¹ • ∑ j, (y j : L) • b j map_add' := fun y z => by`. Simplify using `only [Pi.add_apply, Subring.coe_add, add_smul, Finset.sum_add_distrib, smul_add]`. Use the proof step `map_smul' := fun a y => by`. Simplify using `only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, Subring.coe_mul, mul_smul]`. Conclude with `Finset.sum_congr rfl fun j _ => smul_comm _ _ _ }`.

Establish `hψ : ∀ y, ψ y = c⁻¹ • ∑ j, (y j : L) • b j` using `fun _ => rfl`. Establish `hinj : LinearMap.ker ψ = ⊥`. Use `LinearMap.ker_eq_bot'.2 fun y hy => ?_` and prove the remaining obligations. Rewrite `hy` using `[hψ]`. Establish `h0 : ∑ j, (y j : L) • b j = 0` using `(smul_eq_zero.1 hy).resolve_left (inv_ne_zero hc)`.

Use `Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => (y j : L)) h0` as an intermediate fact. Conclude with `funext fun j => Subtype.ext (this j)`. Set `N : Submodule O (Fin m → O)` to `{ carrier := {y | ψ y ∈ Λ} add_mem' := fun {y z} hy hz => by`. Simplify `Λ.add_mem hy hz` using `[map_add]`. Use the proof step `zero_mem' := by simp [Λ.zero_mem]`.

Use the proof step `smul_mem' := fun a y hy => by`. Simplify `hO a a.2 _ hy }` using `[map_smul, Subring.smul_def]`. Take `⟨n, bN⟩` from `Submodule.basisOfPid (Pi.basisFun O (Fin m)) N`. Set `v : Fin n → V` to `fun i => ψ (bN i : Fin m → O)`. Establish `hvΛ : ∀ i, v i ∈ Λ` using `fun i => (bN i).2`.

Establish `hrep : ∀ z ∈ Λ, ∃ o : Fin n → O, z = ∑ i, (o i : L) • v i`. Introduce `z hz`. Set `y : Fin m → O` to `fun j => ⟨b.repr (c • z) j, h1 z hz j⟩`. Establish `hy : ψ y = z`. Rewrite using `[hψ]`.

Establish `: ∑ j, (y j : L) • b j = c • z` using `b.sum_repr (c • z)`. Rewrite using `[this, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Establish `hyN : y ∈ N`. Express the relevant statement in the definitionally equal form `ψ y ∈ Λ`. Rewrite using `[hy]` and apply the resulting hypothesis.

Use `⟨fun i => bN.repr ⟨y, hyN⟩ i, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun w : N => ψ (w : Fin m → O)) (bN.sum_repr ⟨y, hyN⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hy] at h2`. Rewrite using `[← h2]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [Subring.smul_def]`.

Establish `hliO : LinearIndependent O v`. Establish `h3 : LinearIndependent O (fun i => (bN i : Fin m → O))` using `bN.linearIndependent.map' N.subtype (Submodule.ker_subtype N)`. Conclude with `h3.map' ψ hinj`. Establish `hli : LinearIndependent L v`. Use `Fintype.linearIndependent_iff.2 fun g hg i => ?_` and prove the remaining obligations.

Take `⟨d, hd, hdg⟩` from `exists_common_denom O hfrac Finset.univ g`. Establish `h4 : ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j = 0`. Establish `: ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j = (d : L) • ∑ j, g j • v j`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [Subring.smul_def, mul_smul]`.

Rewrite using `[this, hg, smul_zero]`. Establish `h5` using `Fintype.linearIndependent_iff.1 hliO _ h4 i`. Establish `h6 : (d : L) * g i = 0` using `congrArg Subtype.val h5`. Conclude with `(mul_eq_zero.1 h6).resolve_left hd`. Establish `hsp : ⊤ ≤ Submodule.span L (Set.range v)`.

Introduce `x _`. Take `⟨a, ha, hax⟩` from `hspan x`. Take `⟨o, ho⟩` from `hrep _ hax`. Establish `hx : x = a⁻¹ • (a • x)` using `by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]`. Rewrite using `[hx, ho]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`. Set `B` to `Module.Basis.mk hli hsp`. Establish `hB : ∀ i, B i = v i` using `fun i => by simp [B]`. Use `⟨n, B, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩` and prove the remaining obligations. Take `⟨o, ho⟩` from `hrep x hx`.

Establish `h7 : x = ∑ j, (o j : L) • B j` using `by simpa only [hB] using ho`. Establish `h8 : B.repr x i = (o i : L)`. Rewrite using `[h7, B.repr_sum_self]`. Rewrite using `[h8]`. Conclude with `(o i).2`.

Rewrite using `[← B.sum_repr x]`. Conclude with `Λ.sum_mem fun i _ => hO _ (hx i) _ (by rw [hB]; exact hvΛ i)`.
-/
theorem exists_basis_of_pid {L V : Type} [Field L] [AddCommGroup V] [Module L V] (O : Subring L)
    [IsPrincipalIdealRing O]
    (hfrac : ∀ x : L, ∃ a : O, (a : L) ≠ 0 ∧ (a : L) * x ∈ O) {m : ℕ}
    (b : Module.Basis (Fin m) L V) (Λ : AddSubgroup V) (c : L) (hc : c ≠ 0)
    (h1 : ∀ x ∈ Λ, ∀ i, b.repr (c • x) i ∈ O) (hspan : ∀ x : V, ∃ a : L, a ≠ 0 ∧ a • x ∈ Λ)
    (hO : ∀ a ∈ O, ∀ x ∈ Λ, a • x ∈ Λ) :
    ∃ (n : ℕ) (B : Module.Basis (Fin n) L V), ∀ x, x ∈ Λ ↔ ∀ i, B.repr x i ∈ O := by
  classical

  let ψ : (Fin m → O) →ₗ[O] V :=
    { toFun := fun y => c⁻¹ • ∑ j, (y j : L) • b j
      map_add' := fun y z => by
        simp only [Pi.add_apply, Subring.coe_add, add_smul, Finset.sum_add_distrib, smul_add]
      map_smul' := fun a y => by
        simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
          Subring.coe_mul, mul_smul]
        exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _ }
  have hψ : ∀ y, ψ y = c⁻¹ • ∑ j, (y j : L) • b j := fun _ => rfl
  have hinj : LinearMap.ker ψ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun y hy => ?_
    rw [hψ] at hy
    have h0 : ∑ j, (y j : L) • b j = 0 := (smul_eq_zero.1 hy).resolve_left (inv_ne_zero hc)
    have := Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => (y j : L)) h0
    exact funext fun j => Subtype.ext (this j)
  let N : Submodule O (Fin m → O) :=
    { carrier := {y | ψ y ∈ Λ}
      add_mem' := fun {y z} hy hz => by
        simpa [map_add] using Λ.add_mem hy hz
      zero_mem' := by simp [Λ.zero_mem]
      smul_mem' := fun a y hy => by
        simpa [map_smul, Subring.smul_def] using hO a a.2 _ hy }
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin m)) N
  let v : Fin n → V := fun i => ψ (bN i : Fin m → O)
  have hvΛ : ∀ i, v i ∈ Λ := fun i => (bN i).2

  have hrep : ∀ z ∈ Λ, ∃ o : Fin n → O, z = ∑ i, (o i : L) • v i := by
    intro z hz
    let y : Fin m → O := fun j => ⟨b.repr (c • z) j, h1 z hz j⟩
    have hy : ψ y = z := by
      rw [hψ]
      have : ∑ j, (y j : L) • b j = c • z := b.sum_repr (c • z)
      rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hyN : y ∈ N := by
      change ψ y ∈ Λ
      rwa [hy]
    refine ⟨fun i => bN.repr ⟨y, hyN⟩ i, ?_⟩
    have h2 := congrArg (fun w : N => ψ (w : Fin m → O)) (bN.sum_repr ⟨y, hyN⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hy] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [Subring.smul_def]

  have hliO : LinearIndependent O v := by
    have h3 : LinearIndependent O (fun i => (bN i : Fin m → O)) :=
      bN.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
    exact h3.map' ψ hinj
  have hli : LinearIndependent L v := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    obtain ⟨d, hd, hdg⟩ := exists_common_denom O hfrac Finset.univ g
    have h4 : ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j = 0 := by
      have : ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j
          = (d : L) • ∑ j, g j • v j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Subring.smul_def, mul_smul]
      rw [this, hg, smul_zero]
    have h5 := Fintype.linearIndependent_iff.1 hliO _ h4 i
    have h6 : (d : L) * g i = 0 := congrArg Subtype.val h5
    exact (mul_eq_zero.1 h6).resolve_left hd
  have hsp : ⊤ ≤ Submodule.span L (Set.range v) := by
    intro x _
    obtain ⟨a, ha, hax⟩ := hspan x
    obtain ⟨o, ho⟩ := hrep _ hax
    have hx : x = a⁻¹ • (a • x) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [hx, ho]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  let B := Module.Basis.mk hli hsp
  have hB : ∀ i, B i = v i := fun i => by simp [B]
  refine ⟨n, B, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · obtain ⟨o, ho⟩ := hrep x hx
    have h7 : x = ∑ j, (o j : L) • B j := by simpa only [hB] using ho
    have h8 : B.repr x i = (o i : L) := by
      rw [h7, B.repr_sum_self]
    rw [h8]
    exact (o i).2
  · rw [← B.sum_repr x]
    exact Λ.sum_mem fun i _ => hO _ (hx i) _ (by rw [hB]; exact hvΛ i)

/- English proof (translation)
Introduce `L _ _ hp V _ _ Λ₀ Λ c ⟨m, b, hb⟩ hc hcΛ hspan hO`. Establish `hmem : ∀ x : L, x ∈ 𝒪[L] ↔ ‖x‖ ≤ 1` using `fun x => Valued.integer.mem_iff`. Use `haveI : CompactSpace 𝒪[L] := by`. Establish `hset : ((𝒪[L] : Subring L) : Set L) = Metric.closedBall 0 1`. Use extensionality with `x`.

Simplify using `[hmem]`. Establish `hk : IsCompact ((𝒪[L] : Subring L) : Set L)`. Rewrite using `[hset]`. Conclude with `isCompact_closedBall 0 1`. Conclude with `isCompact_iff_compactSpace.1 hk`.

Use `haveI : (Valued.v : Valuation L NNReal).IsNontrivial := by`. Take `⟨x, hx0, hx1⟩` from `NormedField.exists_norm_lt_one L`. Use `(Valued.v : Valuation L NNReal).isNontrivial_iff_exists_lt_one.2 ⟨x, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hx0`. Simplify `hx1` using `[← NNReal.coe_lt_coe]`.

Use `haveI : IsDiscreteValuationRing 𝒪[L] := Valued.integer.isDiscreteValuationRing_of_compactSpace`. Establish `hfrac : ∀ x : L, ∃ a : 𝒪[L], (a : L) ≠ 0 ∧ (a : L) * x ∈ 𝒪[L]`. Introduce `x`. Distinguish the cases in `hx : ‖x‖ ≤ 1`. Conclude with `⟨1, by simp, by simpa using (hmem x).2 hx⟩`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx`. Establish `hlt : 1 < ‖x‖` using `not_le.1 hx`. Use `⟨⟨x⁻¹, (hmem _).2 ?_⟩, by simpa using hx0, ?_⟩` and prove the remaining obligations.

Rewrite using `[norm_inv]`. Conclude with `inv_le_one_of_one_le₀ hlt.le`. Simplify using `[hx0, one_mem]`. Take `⟨n, B, hB⟩` from `exists_basis_of_pid 𝒪[L] hfrac b Λ c hc (fun x hx i => (hmem _).2 ((hb _).1 (hcΛ x hx) i)) hspan (fun a ha x hx => hO a ((hmem a).1 ha) x hx)`. Conclude with `⟨n, B, fun x => (hB x).trans (forall_congr' fun i => hmem _)⟩`.
-/
theorem stSandwich : StSandwich := by
  intro L _ _ hp V _ _ Λ₀ Λ c ⟨m, b, hb⟩ hc hcΛ hspan hO
  have hmem : ∀ x : L, x ∈ 𝒪[L] ↔ ‖x‖ ≤ 1 := fun x => Valued.integer.mem_iff
  haveI : CompactSpace 𝒪[L] := by
    have hset : ((𝒪[L] : Subring L) : Set L) = Metric.closedBall 0 1 := by
      ext x
      simp [hmem]
    have hk : IsCompact ((𝒪[L] : Subring L) : Set L) := by
      rw [hset]
      exact isCompact_closedBall 0 1
    exact isCompact_iff_compactSpace.1 hk
  haveI : (Valued.v : Valuation L NNReal).IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one L
    refine (Valued.v : Valuation L NNReal).isNontrivial_iff_exists_lt_one.2 ⟨x, ?_, ?_⟩
    · simpa using hx0
    · simpa [← NNReal.coe_lt_coe] using hx1
  haveI : IsDiscreteValuationRing 𝒪[L] := Valued.integer.isDiscreteValuationRing_of_compactSpace
  have hfrac : ∀ x : L, ∃ a : 𝒪[L], (a : L) ≠ 0 ∧ (a : L) * x ∈ 𝒪[L] := by
    intro x
    by_cases hx : ‖x‖ ≤ 1
    · exact ⟨1, by simp, by simpa using (hmem x).2 hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hlt : 1 < ‖x‖ := not_le.1 hx
      refine ⟨⟨x⁻¹, (hmem _).2 ?_⟩, by simpa using hx0, ?_⟩
      · rw [norm_inv]
        exact inv_le_one_of_one_le₀ hlt.le
      · simp [hx0, one_mem]
  obtain ⟨n, B, hB⟩ := exists_basis_of_pid 𝒪[L] hfrac b Λ c hc
    (fun x hx i => (hmem _).2 ((hb _).1 (hcΛ x hx) i)) hspan
    (fun a ha x hx => hO a ((hmem a).1 ha) x hx)
  exact ⟨n, B, fun x => (hB x).trans (forall_congr' fun i => hmem _)⟩

end GlobalTheory.CompanionTheory.Lattice

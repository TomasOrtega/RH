import Mathlib
import GroundTheory.LocalFields.LocalFourierHaar
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Topology Filter
open scoped WithZero Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Basis

/- English proof (translation)
Use `⟨fun t => ⟨fun ht => ?_, fun ⟨n, _, hn⟩ => Filter.mem_of_superset (valBall_mem_nhds n) hn⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `h' : ∀ n : ℤ, ¬ (valBall K n : Set K) ⊆ t` using `fun n hn => h ⟨n, trivial, hn⟩`. Establish `hex : ∀ k : ℕ, ∃ x : K, x ∈ valBall K k ∧ x ∉ t` using `fun k => by`. Use `h' k` as an intermediate fact.

Rewrite `this` using `[Set.not_subset]`. Conclude with `this`. Use `choose x hx hxt using hex`. Establish `hlim : Tendsto x atTop (𝓝 0)`. Rewrite using `[tendsto_zero_iff_valBall]`.

Introduce `N`. Use `filter_upwards [eventually_ge_atTop N.toNat] with k hk`. Conclude with `valBall_antitone (by omega) (hx k)`. Take `⟨k, hk⟩` from `(hlim.eventually ht).exists`. Conclude with `hxt k hk`.
-/
theorem hasBasis_nhds_zero_valBall :
    (𝓝 (0 : K)).HasBasis (fun _ : ℤ => True) (fun n => (valBall K n : Set K)) := by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨n, _, hn⟩ => Filter.mem_of_superset (valBall_mem_nhds n) hn⟩⟩
  by_contra h
  have h' : ∀ n : ℤ, ¬ (valBall K n : Set K) ⊆ t := fun n hn => h ⟨n, trivial, hn⟩
  have hex : ∀ k : ℕ, ∃ x : K, x ∈ valBall K k ∧ x ∉ t := fun k => by
    have := h' k
    rw [Set.not_subset] at this
    exact this
  choose x hx hxt using hex
  have hlim : Tendsto x atTop (𝓝 0) := by
    rw [tendsto_zero_iff_valBall]
    intro N
    filter_upwards [eventually_ge_atTop N.toNat] with k hk
    exact valBall_antitone (by omega) (hx k)
  obtain ⟨k, hk⟩ := (hlim.eventually ht).exists
  exact hxt k hk

/- English proof (translation)
Establish `: x ∈ c • (valBall K 0 : Set K)`. Rewrite using `[smul_valBall hc, zero_add]`. Conclude with `hx`. Take `⟨y, hy, rfl⟩` from `this`. Conclude with `⟨⟨y, mem_valBall_zero_iff.mp hy⟩, rfl⟩`.
-/
theorem exists_mul_of_mem_valBall {c : K} (hc : c ≠ 0) {x : K} (hx : x ∈ valBall K (ord c)) :
    ∃ y : 𝒪[K], x = c * y := by
  have : x ∈ c • (valBall K 0 : Set K) := by
    rw [smul_valBall hc, zero_add]
    exact hx
  obtain ⟨y, hy, rfl⟩ := this
  exact ⟨⟨y, mem_valBall_zero_iff.mp hy⟩, rfl⟩

end Basis

section Characters

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Use `GroundTheory.Global.eq_one_of_sq_mem (s := (fun y => (χ y : ℂ)) '' (H : Set K)) ?_ ?_ ⟨x, hx, rfl⟩` as an intermediate fact. Conclude with `Circle.coe_eq_one.mp this`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `⟨y + y, H.add_mem hy hy, ?_⟩` and prove the remaining obligations. Simplify using `[AddChar.map_add_eq_mul, sq]`.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `h y hy`.
-/
theorem eq_one_of_forall_norm_sub_one_lt (χ : AddChar K Circle) (H : AddSubgroup K)
    (h : ∀ x ∈ H, ‖(χ x : ℂ) - 1‖ < 1 / 2) {x : K} (hx : x ∈ H) : χ x = 1 := by
  have := GroundTheory.Global.eq_one_of_sq_mem (s := (fun y => (χ y : ℂ)) '' (H : Set K)) ?_ ?_
    ⟨x, hx, rfl⟩
  · exact Circle.coe_eq_one.mp this
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨y + y, H.add_mem hy hy, ?_⟩
    simp [AddChar.map_add_eq_mul, sq]
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy

/- English proof (translation)
Establish `hc : Continuous fun z : Circle ↦ ‖(z : ℂ) - 1‖` using `(continuous_subtype_val.sub continuous_const).norm`. Conclude with `(isOpen_lt hc continuous_const).mem_nhds (by simp)`.
-/
theorem setOf_norm_sub_one_lt_mem_nhds :
    {z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Circle) := by
  have hc : Continuous fun z : Circle ↦ ‖(z : ℂ) - 1‖ :=
    (continuous_subtype_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

variable (ψ : AddChar K Circle)

def IsTrivialOn (n : ℤ) : Prop := ∀ x ∈ valBall K n, ψ x = 1

variable {ψ} in
/- English proof (translation)
Introduce `x hx` and use `h x (valBall_antitone hmn hx)`.
-/
theorem IsTrivialOn.mono {m n : ℤ} (h : IsTrivialOn ψ m) (hmn : m ≤ n) : IsTrivialOn ψ n :=
  fun x hx => h x (valBall_antitone hmn hx)

/- English proof (translation)
Establish `: ψ ⁻¹' {z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : K)`. Apply `hψ.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Rewrite using `[AddChar.map_zero_eq_one]`. Conclude with `setOf_norm_sub_one_lt_mem_nhds`. Take `⟨n, -, hn⟩` from `hasBasis_nhds_zero_valBall.mem_iff.mp this`.

Conclude with `⟨n, fun x hx => eq_one_of_forall_norm_sub_one_lt ψ (valBall K n) (fun y hy => hn hy) hx⟩`.
-/
theorem exists_isTrivialOn (hψ : Continuous ψ) : ∃ n, IsTrivialOn ψ n := by
  have : ψ ⁻¹' {z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : K) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact setOf_norm_sub_one_lt_mem_nhds
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp this
  exact ⟨n, fun x hx => eq_one_of_forall_norm_sub_one_lt ψ (valBall K n) (fun y hy => hn hy) hx⟩

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by`. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_not] at h`. Conclude with `hψ1 (DFunLike.ext _ _ fun a => (h a).trans (AddChar.one_apply a).symm)`. Use `⟨ord x + 1, fun n hn => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Conclude with `hx (hn x (valBall_antitone (by omega : n ≤ ord x) mem_valBall_ord))`.
-/
theorem exists_le_of_isTrivialOn (hψ1 : ψ ≠ 1) : ∃ N, ∀ n, IsTrivialOn ψ n → N ≤ n := by
  obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hψ1 (DFunLike.ext _ _ fun a => (h a).trans (AddChar.one_apply a).symm)
  refine ⟨ord x + 1, fun n hn => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  exact hx (hn x (valBall_antitone (by omega : n ≤ ord x) mem_valBall_ord))

def addCharConductor : ℤ := sInf {n : ℤ | IsTrivialOn ψ n}

variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

omit hψ in
/- English proof (translation)
Take `⟨N, hN⟩` from `exists_le_of_isTrivialOn ψ hψ1`. Conclude with `⟨N, fun m hm => hN m hm⟩`.
-/
theorem bddBelow_isTrivialOn : BddBelow {n : ℤ | IsTrivialOn ψ n} := by
  obtain ⟨N, hN⟩ := exists_le_of_isTrivialOn ψ hψ1
  exact ⟨N, fun m hm => hN m hm⟩

/- English proof (translation)
Take `⟨n, hn⟩` from `exists_isTrivialOn ψ hψ`. Conclude with `Int.csInf_mem ⟨n, hn⟩ (bddBelow_isTrivialOn hψ1)`.
-/
theorem isTrivialOn_addCharConductor : IsTrivialOn ψ (addCharConductor ψ) := by
  obtain ⟨n, hn⟩ := exists_isTrivialOn ψ hψ
  exact Int.csInf_mem ⟨n, hn⟩ (bddBelow_isTrivialOn hψ1)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => csInf_le (bddBelow_isTrivialOn hψ1) h, fun h => (isTrivialOn_addCharConductor hψ hψ1).mono h⟩`.
-/
theorem isTrivialOn_iff (n : ℤ) : IsTrivialOn ψ n ↔ addCharConductor ψ ≤ n :=
  ⟨fun h => csInf_le (bddBelow_isTrivialOn hψ1) h,
    fun h => (isTrivialOn_addCharConductor hψ hψ1).mono h⟩

/- English proof (translation)
Rewrite using `[isTrivialOn_iff hψ hψ1]`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_isTrivialOn_addCharConductor_sub_one : ¬ IsTrivialOn ψ (addCharConductor ψ - 1) := by
  rw [isTrivialOn_iff hψ hψ1]
  omega

omit hψ hψ1 in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Establish `hy' : y ∈ a • (valBall K n : Set K)`. Rewrite using `[smul_valBall ha]`. Conclude with `hy`.

Take `⟨x, hx, rfl⟩` from `hy'`. Use `h x hx` as an intermediate fact. Rewrite `this` using `[AddChar.mulShift_apply]`. Then use the resulting hypothesis. Introduce `h x hx`. Rewrite using `[AddChar.mulShift_apply]`.

Apply `h` to reduce the goal to its premises. Establish `: a • x ∈ a • (valBall K n : Set K)` using `Set.smul_mem_smul_set hx`. Rewrite `this` using `[smul_valBall ha]`. Conclude with `this`.
-/
theorem isTrivialOn_mulShift_iff {a : K} (ha : a ≠ 0) (n : ℤ) :
    IsTrivialOn (ψ.mulShift a) n ↔ IsTrivialOn ψ (n + ord a) := by
  constructor
  · intro h y hy
    have hy' : y ∈ a • (valBall K n : Set K) := by
      rw [smul_valBall ha]
      exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    have := h x hx
    rwa [AddChar.mulShift_apply] at this
  · intro h x hx
    rw [AddChar.mulShift_apply]
    apply h
    have : a • x ∈ a • (valBall K n : Set K) := Set.smul_mem_smul_set hx
    rw [smul_valBall ha] at this
    exact this

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Simplify using `[ha, IsTrivialOn]`. Rewrite using `[isTrivialOn_mulShift_iff ha, isTrivialOn_iff hψ hψ1, mem_valBall_iff_le_ord ha]`. Use linear arithmetic over natural numbers and integers.
-/
theorem isTrivialOn_mulShift_iff_mem (a : K) (n : ℤ) :
    IsTrivialOn (ψ.mulShift a) n ↔ a ∈ valBall K (addCharConductor ψ - n) := by
  by_cases ha : a = 0
  · simp [ha, IsTrivialOn]
  rw [isTrivialOn_mulShift_iff ha, isTrivialOn_iff hψ hψ1, mem_valBall_iff_le_ord ha]
  omega

omit hψ1 in
/- English proof (translation)
Establish `: (ψ.mulShift a : K → Circle) = fun x => ψ (a * x)`. Use extensionality with `x`. Rewrite using `[AddChar.mulShift_apply]`. Rewrite using `[this]`. Conclude with `hψ.comp (continuous_const_mul a)`.
-/
theorem continuous_mulShift (a : K) : Continuous (ψ.mulShift a) := by
  have : (ψ.mulShift a : K → Circle) = fun x => ψ (a * x) := by
    ext x
    rw [AddChar.mulShift_apply]
  rw [this]
  exact hψ.comp (continuous_const_mul a)

omit hψ [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/- English proof (translation)
The claim follows from `AddChar.IsPrimitive.of_ne_one hψ1 ha`.
-/
theorem mulShift_ne_one {a : K} (ha : a ≠ 0) : ψ.mulShift a ≠ 1 :=
  AddChar.IsPrimitive.of_ne_one hψ1 ha

omit hψ [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
The claim follows from `AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ1)`.
-/
theorem mulShift_injective : Function.Injective ψ.mulShift :=
  AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ1)

/- English proof (translation)
Establish `hc` using `continuous_mulShift hψ a`. Establish `h1` using `mulShift_ne_one hψ1 ha`. Establish `key : ∀ n, addCharConductor (ψ.mulShift a) ≤ n ↔ addCharConductor ψ - ord a ≤ n` using `fun n => by`. Rewrite using `[← isTrivialOn_iff hc h1, isTrivialOn_mulShift_iff ha, isTrivialOn_iff hψ hψ1]`. Use linear arithmetic over natural numbers and integers.

Conclude with `le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)`.
-/
theorem addCharConductor_mulShift {a : K} (ha : a ≠ 0) :
    addCharConductor (ψ.mulShift a) = addCharConductor ψ - ord a := by
  have hc := continuous_mulShift hψ a
  have h1 := mulShift_ne_one hψ1 ha
  have key : ∀ n, addCharConductor (ψ.mulShift a) ≤ n ↔ addCharConductor ψ - ord a ≤ n := fun n => by
    rw [← isTrivialOn_iff hc h1, isTrivialOn_mulShift_iff ha, isTrivialOn_iff hψ hψ1]
    omega
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)

end Characters

section Residue

def residueLift (t : 𝓀[K]) : 𝒪[K] := Function.surjInv IsLocalRing.residue_surjective t

/- English proof (translation)
The claim follows from `Function.surjInv_eq _ t`.
-/
theorem residue_residueLift (t : 𝓀[K]) : IsLocalRing.residue 𝒪[K] (residueLift t) = t :=
  Function.surjInv_eq _ t

/- English proof (translation)
Rewrite `h` using `[residue_eq_residue_iff]`. Establish `e : c * (y : K) = c * y' + c * ((y : K) - y')` using `by ring`. Rewrite using `[e, AddChar.map_add_eq_mul]`. It suffices to establish `χ (c * ((y : K) - y')) = 1 by rw [this, mul_one]`. Distinguish the cases in `hc : c = 0`.

Simplify using `[hc]`. Apply `hχ` to reduce the goal to its premises. Use `show c * ((y : K) - y') ∈ (valBall K (ord c + 1) : Set K)`. Rewrite using `[add_comm, ← smul_valBall hc]`. Conclude with `Set.smul_mem_smul_set h`.
-/
theorem apply_mul_eq_of_residue_eq {χ : AddChar K Circle} {c : K} (hχ : IsTrivialOn χ (ord c + 1))
    {y y' : 𝒪[K]} (h : IsLocalRing.residue 𝒪[K] y = IsLocalRing.residue 𝒪[K] y') :
    χ (c * y) = χ (c * y') := by
  rw [residue_eq_residue_iff] at h
  have e : c * (y : K) = c * y' + c * ((y : K) - y') := by ring
  rw [e, AddChar.map_add_eq_mul]
  suffices χ (c * ((y : K) - y')) = 1 by rw [this, mul_one]
  by_cases hc : c = 0
  · simp [hc]
  apply hχ
  show c * ((y : K) - y') ∈ (valBall K (ord c + 1) : Set K)
  rw [add_comm, ← smul_valBall hc]
  exact Set.smul_mem_smul_set h

def residueChar (χ : AddChar K Circle) (c : K) (hχ : IsTrivialOn χ (ord c + 1)) :
    AddChar 𝓀[K] Circle where
  toFun t := χ (c * (residueLift t : K))
  map_zero_eq_one' := by
    have := apply_mul_eq_of_residue_eq hχ (y := residueLift 0) (y' := 0)
      (by rw [residue_residueLift, map_zero])
    simpa using this
  map_add_eq_mul' t t' := by
    have := apply_mul_eq_of_residue_eq hχ (y := residueLift (t + t'))
      (y' := residueLift t + residueLift t') (by simp [residue_residueLift])
    rw [this]
    push_cast
    rw [mul_add, AddChar.map_add_eq_mul]

/- English proof (translation)
The claim follows from `apply_mul_eq_of_residue_eq hχ (residue_residueLift _)`.
-/
theorem residueChar_apply (χ : AddChar K Circle) (c : K) (hχ : IsTrivialOn χ (ord c + 1))
    (y : 𝒪[K]) : residueChar χ c hχ (IsLocalRing.residue 𝒪[K] y) = χ (c * y) :=
  apply_mul_eq_of_residue_eq hχ (residue_residueLift _)

/- English proof (translation)
Establish `: Fintype 𝓀[K]` using `Fintype.ofFinite _`. Set `e : AddChar 𝓀[K] Circle → AddChar 𝓀[K] ℂ` to `fun χ => Circle.coeHom.compAddChar χ`. Establish `he : Function.Injective e` using `MonoidHom.compAddChar_injective_right _ (fun a b h => Circle.coe_inj.mp h)`. Establish `he1 : e 1 = 1`. Use extensionality with `t`.

Simplify using `[e]`. Establish `hp : (e φ).IsPrimitive` using `AddChar.IsPrimitive.of_ne_one fun h => hφ (he (h.trans he1.symm))`. Establish `hbij : Function.Bijective (e φ).mulShift` using `(Fintype.bijective_iff_injective_and_card _).mpr ⟨AddChar.to_mulShift_inj_of_isPrimitive hp, AddChar.card_eq.symm⟩`. Take `⟨s, hs⟩` from `hbij.2 (e l)`. Use `⟨s, DFunLike.ext _ _ fun t => ?_⟩` and prove the remaining obligations.

Use `congrArg (fun χ : AddChar 𝓀[K] ℂ => χ t) hs` as an intermediate fact. Simplify using `only [e, AddChar.mulShift_apply, MonoidHom.compAddChar_apply, Function.comp_apply] at this`. Rewrite using `[AddChar.mulShift_apply]`. Conclude with `(Circle.coe_inj.mp this).symm`.
-/
theorem exists_eq_mulShift_residue {φ : AddChar 𝓀[K] Circle} (hφ : φ ≠ 1)
    (l : AddChar 𝓀[K] Circle) : ∃ s, l = φ.mulShift s := by
  classical
  have : Fintype 𝓀[K] := Fintype.ofFinite _
  let e : AddChar 𝓀[K] Circle → AddChar 𝓀[K] ℂ := fun χ => Circle.coeHom.compAddChar χ
  have he : Function.Injective e :=
    MonoidHom.compAddChar_injective_right _ (fun a b h => Circle.coe_inj.mp h)
  have he1 : e 1 = 1 := by
    ext t
    simp [e]
  have hp : (e φ).IsPrimitive := AddChar.IsPrimitive.of_ne_one fun h => hφ (he (h.trans he1.symm))
  have hbij : Function.Bijective (e φ).mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨AddChar.to_mulShift_inj_of_isPrimitive hp, AddChar.card_eq.symm⟩
  obtain ⟨s, hs⟩ := hbij.2 (e l)
  refine ⟨s, DFunLike.ext _ _ fun t => ?_⟩
  have := congrArg (fun χ : AddChar 𝓀[K] ℂ => χ t) hs
  simp only [e, AddChar.mulShift_apply, MonoidHom.compAddChar_apply, Function.comp_apply] at this
  rw [AddChar.mulShift_apply]
  exact (Circle.coe_inj.mp this).symm

end Residue

section Duality

variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

/- English proof (translation)
Take `⟨m, hm⟩` from `exists_isTrivialOn χ hχ`. Set `S : ℕ → Set K` to `fun j => {a | ∀ x ∈ valBall K (m - j), χ x = ψ (a * x)}`. Establish `hS0 : S 0 ⊆ valBall K (addCharConductor ψ - m)`. Introduce `a ha`. Rewrite using `[SetLike.mem_coe, ← isTrivialOn_mulShift_iff_mem hψ hψ1]`.

Introduce `x hx`. Establish `hx' : x ∈ valBall K (m - ((0 : ℕ) : ℤ))` using `by simpa using hx`. Rewrite using `[AddChar.mulShift_apply, ← ha x hx', hm x hx]`. Establish `hclosed : ∀ j, IsClosed (S j)` using `fun j => by`. Establish `: S j = ⋂ x ∈ valBall K (m - j), {a : K | ψ (a * x) = χ x}`.

Use extensionality with `a`. Simplify using `[S, eq_comm]`. Rewrite using `[this]`. Conclude with `isClosed_biInter fun x _ => isClosed_eq (hψ.comp (continuous_mul_const x)) continuous_const`. Establish `hanti : ∀ j, S (j + 1) ⊆ S j` using `fun j a ha x hx => ha x (valBall_antitone (by push_cast; omega) hx)`.

Establish `hstep : ∀ j : ℕ, (S j).Nonempty → (S (j + 1)).Nonempty`. Introduce and unpack `j ⟨b, hb⟩`. Take `⟨c₁, hc₁, hc₁k⟩` from `exists_ord_eq K (m - j - 1)`. Take `⟨c₂, hc₂, hc₂n⟩` from `exists_ord_eq K (addCharConductor ψ - 1)`. Set `χ' : AddChar K Circle` to `χ * ψ.mulShift (-b)`.

Establish `hχ' : IsTrivialOn χ' (ord c₁ + 1)`. Introduce `x hx`. Rewrite `hx` using `[hc₁k, sub_add_cancel]`. Simplify using `only [χ', AddChar.mul_apply, AddChar.mulShift_apply]`. Rewrite using `[hb x hx, ← AddChar.map_add_eq_mul, neg_mul, add_neg_cancel, AddChar.map_zero_eq_one]`.

Establish `hψ' : IsTrivialOn ψ (ord c₂ + 1)`. Rewrite using `[hc₂n, sub_add_cancel]`. Conclude with `isTrivialOn_addCharConductor hψ hψ1`. Establish `hphi : residueChar ψ c₂ hψ' ≠ 1`. Introduce `h`.

Apply `not_isTrivialOn_addCharConductor_sub_one hψ hψ1` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[← hc₂n]`. Take `⟨y, rfl⟩` from `exists_mul_of_mem_valBall hc₂ hx`. Rewrite using `[← residueChar_apply ψ c₂ hψ' y, h, AddChar.one_apply]`.

Take `⟨s, hs⟩` from `exists_eq_mulShift_residue hphi (residueChar χ' c₁ hχ')`. Use `⟨b + c₂ * c₁⁻¹ * (residueLift s : K), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : x ∈ valBall K (ord c₁)`. Establish `e : m - ((j + 1 : ℕ) : ℤ) = m - j - 1` using `by push_cast; ring`. Rewrite using `[hc₁k, ← e]`.

Conclude with `hx`. Take `⟨y, rfl⟩` from `exists_mul_of_mem_valBall hc₁ hx'`. Establish `h1 : χ' (c₁ * y) = ψ (c₂ * ((residueLift s : K) * y))`. Establish `e : s * IsLocalRing.residue 𝒪[K] y = IsLocalRing.residue 𝒪[K] (residueLift s * y)`. Rewrite using `[map_mul, residue_residueLift]`.

Rewrite using `[← residueChar_apply χ' c₁ hχ' y, hs, AddChar.mulShift_apply, e, residueChar_apply]`. Use `push_cast`. Both sides reduce to the same expression. Establish `h2 : χ (c₁ * y) = χ' (c₁ * y) * ψ (b * (c₁ * y))`. Simplify using `only [χ', AddChar.mul_apply, AddChar.mulShift_apply]`.

Rewrite using `[mul_assoc, ← AddChar.map_add_eq_mul, neg_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]`. Rewrite using `[h2, h1, ← AddChar.map_add_eq_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hne : ∀ j, (S j).Nonempty` using `fun j => by`. Proceed by induction on `j with`. Consider the case `zero`. Use `⟨0, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[zero_mul, AddChar.map_zero_eq_one]`.

Conclude with `hm x (by simpa using hx)`. Consider the case `succ j ih => exact hstep j ih`. Establish `hcpt : IsCompact (S 0)` using `(isCompact_valBall _).of_isClosed_subset (hclosed 0) hS0`. Take `⟨a, ha⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne hcpt hclosed`. Use `⟨a, DFunLike.ext _ _ fun x => ?_⟩` and prove the remaining obligations.

Rewrite `ha` using `[Set.mem_iInter]`. Rewrite using `[AddChar.mulShift_apply]`. Conclude with `ha (m - ord x).toNat x (valBall_antitone (by omega) mem_valBall_ord)`.
-/
theorem exists_eq_mulShift (χ : AddChar K Circle) (hχ : Continuous χ) :
    ∃ a : K, χ = ψ.mulShift a := by
  obtain ⟨m, hm⟩ := exists_isTrivialOn χ hχ
  let S : ℕ → Set K := fun j => {a | ∀ x ∈ valBall K (m - j), χ x = ψ (a * x)}
  have hS0 : S 0 ⊆ valBall K (addCharConductor ψ - m) := by
    intro a ha
    rw [SetLike.mem_coe, ← isTrivialOn_mulShift_iff_mem hψ hψ1]
    intro x hx
    have hx' : x ∈ valBall K (m - ((0 : ℕ) : ℤ)) := by simpa using hx
    rw [AddChar.mulShift_apply, ← ha x hx', hm x hx]
  have hclosed : ∀ j, IsClosed (S j) := fun j => by
    have : S j = ⋂ x ∈ valBall K (m - j), {a : K | ψ (a * x) = χ x} := by
      ext a
      simp [S, eq_comm]
    rw [this]
    exact isClosed_biInter fun x _ => isClosed_eq (hψ.comp (continuous_mul_const x))
      continuous_const
  have hanti : ∀ j, S (j + 1) ⊆ S j := fun j a ha x hx =>
    ha x (valBall_antitone (by push_cast; omega) hx)
  have hstep : ∀ j : ℕ, (S j).Nonempty → (S (j + 1)).Nonempty := by
    rintro j ⟨b, hb⟩
    obtain ⟨c₁, hc₁, hc₁k⟩ := exists_ord_eq K (m - j - 1)
    obtain ⟨c₂, hc₂, hc₂n⟩ := exists_ord_eq K (addCharConductor ψ - 1)
    let χ' : AddChar K Circle := χ * ψ.mulShift (-b)
    have hχ' : IsTrivialOn χ' (ord c₁ + 1) := by
      intro x hx
      rw [hc₁k, sub_add_cancel] at hx
      simp only [χ', AddChar.mul_apply, AddChar.mulShift_apply]
      rw [hb x hx, ← AddChar.map_add_eq_mul, neg_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    have hψ' : IsTrivialOn ψ (ord c₂ + 1) := by
      rw [hc₂n, sub_add_cancel]
      exact isTrivialOn_addCharConductor hψ hψ1
    have hphi : residueChar ψ c₂ hψ' ≠ 1 := by
      intro h
      apply not_isTrivialOn_addCharConductor_sub_one hψ hψ1
      intro x hx
      rw [← hc₂n] at hx
      obtain ⟨y, rfl⟩ := exists_mul_of_mem_valBall hc₂ hx
      rw [← residueChar_apply ψ c₂ hψ' y, h, AddChar.one_apply]
    obtain ⟨s, hs⟩ := exists_eq_mulShift_residue hphi (residueChar χ' c₁ hχ')
    refine ⟨b + c₂ * c₁⁻¹ * (residueLift s : K), fun x hx => ?_⟩
    have hx' : x ∈ valBall K (ord c₁) := by
      have e : m - ((j + 1 : ℕ) : ℤ) = m - j - 1 := by push_cast; ring
      rw [hc₁k, ← e]
      exact hx
    obtain ⟨y, rfl⟩ := exists_mul_of_mem_valBall hc₁ hx'
    have h1 : χ' (c₁ * y) = ψ (c₂ * ((residueLift s : K) * y)) := by
      have e : s * IsLocalRing.residue 𝒪[K] y = IsLocalRing.residue 𝒪[K] (residueLift s * y) := by
        rw [map_mul, residue_residueLift]
      rw [← residueChar_apply χ' c₁ hχ' y, hs, AddChar.mulShift_apply, e, residueChar_apply]
      push_cast
      rfl
    have h2 : χ (c₁ * y) = χ' (c₁ * y) * ψ (b * (c₁ * y)) := by
      simp only [χ', AddChar.mul_apply, AddChar.mulShift_apply]
      rw [mul_assoc, ← AddChar.map_add_eq_mul, neg_mul, neg_add_cancel, AddChar.map_zero_eq_one,
        mul_one]
    rw [h2, h1, ← AddChar.map_add_eq_mul]
    congr 1
    field_simp
    ring
  have hne : ∀ j, (S j).Nonempty := fun j => by
    induction j with
    | zero =>
      refine ⟨0, fun x hx => ?_⟩
      rw [zero_mul, AddChar.map_zero_eq_one]
      exact hm x (by simpa using hx)
    | succ j ih => exact hstep j ih
  have hcpt : IsCompact (S 0) := (isCompact_valBall _).of_isClosed_subset (hclosed 0) hS0
  obtain ⟨a, ha⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne hcpt hclosed
  refine ⟨a, DFunLike.ext _ _ fun x => ?_⟩
  rw [Set.mem_iInter] at ha
  rw [AddChar.mulShift_apply]
  exact ha (m - ord x).toNat x (valBall_antitone (by omega) mem_valBall_ord)

end Duality

section SelfDual

variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)

def dualOf (a : K) : PontryaginDual (Multiplicative K) where
  toMonoidHom := (ψ.mulShift a).toMonoidHom
  continuous_toFun := (continuous_mulShift hψ a).comp continuous_toAdd

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dualOf_apply (a : K) (x : Multiplicative K) : dualOf hψ a x = ψ (a * x.toAdd) := rfl

def dualHom : Multiplicative K →* PontryaginDual (Multiplicative K) where
  toFun a := dualOf hψ a.toAdd
  map_one' := PontryaginDual.ext fun x => by
    rw [dualOf_apply, toAdd_one, zero_mul, AddChar.map_zero_eq_one, PontryaginDual.one_apply]
  map_mul' a b := PontryaginDual.ext fun x => by
    rw [dualOf_apply, toAdd_mul, add_mul, AddChar.map_add_eq_mul]
    rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dualHom_apply (a x : Multiplicative K) : dualHom hψ a x = ψ (a.toAdd * x.toAdd) := rfl

include hψ1 in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b h`. Establish `: ψ.mulShift a.toAdd = ψ.mulShift b.toAdd` using `DFunLike.ext _ _ fun x => by`. Use `congrArg (fun χ : PontryaginDual (Multiplicative K) => χ (Multiplicative.ofAdd x)) h` as an intermediate fact. Simplify using `using this`.

Conclude with `mulShift_injective hψ1 this`. Introduce `χ`. Set `χ' : AddChar K Circle` to `AddChar.toMonoidHomEquiv.symm χ.toMonoidHom`. Establish `hc : Continuous χ'` using `χ.continuous.comp continuous_ofAdd`. Take `⟨a, ha⟩` from `exists_eq_mulShift hψ hψ1 χ' hc`.

Use `⟨Multiplicative.ofAdd a, PontryaginDual.ext fun x => ?_⟩` and prove the remaining obligations. Use `congrArg (fun f : AddChar K Circle => f x.toAdd) ha` as an intermediate fact. Simplify using `only [χ', AddChar.toMonoidHomEquiv_symm_apply, AddChar.mulShift_apply] at this`. Rewrite using `[dualHom_apply, toAdd_ofAdd]`. Conclude with `this.symm`.
-/
theorem dualHom_bijective : Function.Bijective (dualHom hψ) := by
  constructor
  · intro a b h
    have : ψ.mulShift a.toAdd = ψ.mulShift b.toAdd := DFunLike.ext _ _ fun x => by
      have := congrArg (fun χ : PontryaginDual (Multiplicative K) => χ (Multiplicative.ofAdd x)) h
      simpa using this
    exact mulShift_injective hψ1 this
  · intro χ
    let χ' : AddChar K Circle := AddChar.toMonoidHomEquiv.symm χ.toMonoidHom
    have hc : Continuous χ' := χ.continuous.comp continuous_ofAdd
    obtain ⟨a, ha⟩ := exists_eq_mulShift hψ hψ1 χ' hc
    refine ⟨Multiplicative.ofAdd a, PontryaginDual.ext fun x => ?_⟩
    have := congrArg (fun f : AddChar K Circle => f x.toAdd) ha
    simp only [χ', AddChar.toMonoidHomEquiv_symm_apply, AddChar.mulShift_apply] at this
    rw [dualHom_apply, toAdd_ofAdd]
    exact this.symm

def selfDualMulEquiv : Multiplicative K ≃* PontryaginDual (Multiplicative K) :=
  MulEquiv.ofBijective (dualHom hψ) (dualHom_bijective hψ hψ1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem selfDualMulEquiv_apply (a x : Multiplicative K) :
    selfDualMulEquiv hψ hψ1 a x = ψ (a.toAdd * x.toAdd) := rfl

/- English proof (translation)
Use `ContinuousMonoidHom.continuous_of_continuous_uncurry _ ?_` and prove the remaining obligations. Conclude with `hψ.comp ((continuous_toAdd.comp continuous_fst).mul (continuous_toAdd.comp continuous_snd))`.
-/
theorem continuous_selfDualMulEquiv : Continuous (selfDualMulEquiv hψ hψ1) := by
  refine ContinuousMonoidHom.continuous_of_continuous_uncurry _ ?_
  exact hψ.comp ((continuous_toAdd.comp continuous_fst).mul (continuous_toAdd.comp continuous_snd))

/- English proof (translation)
Use `continuous_of_continuousAt_one (selfDualMulEquiv hψ hψ1).symm ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_one]`. Establish `hb : (𝓝 (1 : Multiplicative K)).HasBasis (fun _ : ℤ => True) (fun n => Multiplicative.toAdd ⁻¹' (valBall K n : Set K))` using `hasBasis_nhds_zero_valBall (K := K)`. Rewrite using `[hb.tendsto_right_iff]`. Introduce `N _`.

Set `C : Set (Multiplicative K)` to `Multiplicative.toAdd ⁻¹' (valBall K (addCharConductor ψ - N) : Set K)`. Establish `hC : IsCompact C` using `isCompact_valBall (K := K) (addCharConductor ψ - N)`. Set `V : Set Circle` to `{z | ‖(z : ℂ) - 1‖ < 1 / 2}`. Establish `hV : IsOpen V` using `isOpen_lt (continuous_subtype_val.sub continuous_const).norm continuous_const`. Set `W : Set (PontryaginDual (Multiplicative K))` to `{χ | Set.MapsTo χ C V}`.

Establish `hW : IsOpen W` using `(ContinuousMap.isOpen_setOfPred_mapsTo hC hV).preimage (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous`. Establish `h1W : (1 : PontryaginDual (Multiplicative K)) ∈ W` using `fun x _ => by`. Simplify using `[V, PontryaginDual.one_apply]`. Use `filter_upwards [hW.mem_nhds h1W] with χ hχ`. Take `⟨a, rfl⟩` from `(selfDualMulEquiv hψ hψ1).surjective χ`.

Rewrite using `[MulEquiv.symm_apply_apply]`. Use `show a.toAdd ∈ valBall K N`. Establish `htriv : IsTrivialOn (ψ.mulShift a.toAdd) (addCharConductor ψ - N)` using `fun x hx => eq_one_of_forall_norm_sub_one_lt (ψ.mulShift a.toAdd) (valBall K (addCharConductor ψ - N)) (fun y hy => by`. Use `hχ (show Multiplicative.ofAdd y ∈ C from hy)` as an intermediate fact. Simplify `this) hx` using `[V, selfDualMulEquiv_apply]`.

Rewrite `htriv` using `[isTrivialOn_mulShift_iff_mem hψ hψ1]`. Simplify using `using htriv`.
-/
theorem continuous_selfDualMulEquiv_symm : Continuous (selfDualMulEquiv hψ hψ1).symm := by
  refine continuous_of_continuousAt_one (selfDualMulEquiv hψ hψ1).symm ?_
  rw [ContinuousAt, map_one]
  have hb : (𝓝 (1 : Multiplicative K)).HasBasis (fun _ : ℤ => True)
      (fun n => Multiplicative.toAdd ⁻¹' (valBall K n : Set K)) :=
    hasBasis_nhds_zero_valBall (K := K)
  rw [hb.tendsto_right_iff]
  intro N _
  let C : Set (Multiplicative K) := Multiplicative.toAdd ⁻¹' (valBall K (addCharConductor ψ - N) : Set K)
  have hC : IsCompact C := isCompact_valBall (K := K) (addCharConductor ψ - N)
  let V : Set Circle := {z | ‖(z : ℂ) - 1‖ < 1 / 2}
  have hV : IsOpen V :=
    isOpen_lt (continuous_subtype_val.sub continuous_const).norm continuous_const
  let W : Set (PontryaginDual (Multiplicative K)) := {χ | Set.MapsTo χ C V}
  have hW : IsOpen W := (ContinuousMap.isOpen_setOfPred_mapsTo hC hV).preimage
    (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous
  have h1W : (1 : PontryaginDual (Multiplicative K)) ∈ W := fun x _ => by
    simp [V, PontryaginDual.one_apply]
  filter_upwards [hW.mem_nhds h1W] with χ hχ
  obtain ⟨a, rfl⟩ := (selfDualMulEquiv hψ hψ1).surjective χ
  rw [MulEquiv.symm_apply_apply]
  show a.toAdd ∈ valBall K N
  have htriv : IsTrivialOn (ψ.mulShift a.toAdd) (addCharConductor ψ - N) := fun x hx =>
    eq_one_of_forall_norm_sub_one_lt (ψ.mulShift a.toAdd) (valBall K (addCharConductor ψ - N))
      (fun y hy => by
        have := hχ (show Multiplicative.ofAdd y ∈ C from hy)
        simpa [V, selfDualMulEquiv_apply] using this) hx
  rw [isTrivialOn_mulShift_iff_mem hψ hψ1] at htriv
  simpa using htriv

def selfDual : Multiplicative K ≃ₜ* PontryaginDual (Multiplicative K) where
  toMulEquiv := selfDualMulEquiv hψ hψ1
  continuous_toFun := continuous_selfDualMulEquiv hψ hψ1
  continuous_invFun := continuous_selfDualMulEquiv_symm hψ hψ1

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem selfDual_apply (a x : Multiplicative K) : selfDual hψ hψ1 a x = ψ (a.toAdd * x.toAdd) :=
  rfl

end SelfDual

end GroundTheory.LocalField

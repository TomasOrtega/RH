import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_KC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)

abbrev red (n r : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r) :=
  Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ r))

variable (k) in

def H (n r : ℕ) : Subgroup (GL (Fin n) k) := (red (k := k) n r).ker.map (incl n)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, e⟩`. Establish `: z = y` using `Subtype.val_injective e`. Conclude with `this ▸ hz`. Introduce `h`.

Conclude with `⟨y, h, rfl⟩`.
-/
theorem inPow_algebraMap (r : ℕ) (y : 𝒪[k]) :
    InPow r (algebraMap 𝒪[k] k y) ↔ y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  constructor
  · rintro ⟨z, hz, e⟩
    have : z = y := Subtype.val_injective e
    exact this ▸ hz
  · intro h
    exact ⟨y, h, rfl⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Apply the tactic sequence `split_ifs <;> simp [Matrix.GeneralLinearGroup.map]`.
-/
theorem entry_sub (n : ℕ) (u : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (((incl n u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) =
      algebraMap 𝒪[k] k ((u : Matrix (Fin n) (Fin n) 𝒪[k]) i j - if i = j then 1 else 0) := by
  split_ifs <;> simp [Matrix.GeneralLinearGroup.map]

/- English proof (translation)
Rewrite using `[Units.ext_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Establish `h'` using `congrFun (congrFun h i) j`. Rewrite using `[← Ideal.Quotient.eq]`.

Use `split_ifs with hij`. Simplify `h'` using `[Matrix.GeneralLinearGroup.map, hij]`. Simplify `h'` using `[Matrix.GeneralLinearGroup.map, hij]`. Introduce `h`. Use extensionality with `i j`.

Establish `h'` using `Ideal.Quotient.eq.2 (h i j)`. Use `split_ifs at h' with hij`. Simplify `h'` using `[Matrix.GeneralLinearGroup.map, hij]`. Simplify `h'` using `[Matrix.GeneralLinearGroup.map, hij]`.
-/
theorem red_eq_one_iff (n r : ℕ) (u : GL (Fin n) 𝒪[k]) :
    red (k := k) n r u = 1 ↔ ∀ i j, ((u : Matrix (Fin n) (Fin n) 𝒪[k]) i j - if i = j then 1 else 0) ∈
      IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  rw [Units.ext_iff]
  constructor
  · intro h i j
    have h' := congrFun (congrFun h i) j
    rw [← Ideal.Quotient.eq]
    split_ifs with hij
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
  · intro h
    ext i j
    have h' := Ideal.Quotient.eq.2 (h i j)
    split_ifs at h' with hij
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨u, rfl⟩, hP⟩`. Use `⟨u, (red_eq_one_iff n r u).2 fun i j => ?_, rfl⟩` and prove the remaining obligations. Use `hP i j` as an intermediate fact. Rewrite `this` using `[entry_sub, inPow_algebraMap]`. Then use the resulting hypothesis.

Introduce and unpack `⟨u, hu, rfl⟩`. Use `⟨⟨u, rfl⟩, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[entry_sub, inPow_algebraMap]`. Conclude with `(red_eq_one_iff n r u).1 hu i j`.
-/
theorem mem_KC_iff (n r : ℕ) (g : GL (Fin n) k) : g ∈ KC k n r ↔ g ∈ H k n r := by
  constructor
  · rintro ⟨⟨u, rfl⟩, hP⟩
    refine ⟨u, (red_eq_one_iff n r u).2 fun i j => ?_, rfl⟩
    have := hP i j
    rwa [entry_sub, inPow_algebraMap] at this
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    rw [entry_sub, inPow_algebraMap]
    exact (red_eq_one_iff n r u).1 hu i j

/- English proof (translation)
The claim follows from `Set.ext fun g => (mem_KC_iff n r g).symm`.
-/
theorem coe_H (n r : ℕ) : (H k n r : Set (GL (Fin n) k)) = KC k n r :=
  Set.ext fun g => (mem_KC_iff n r g).symm

/- English proof (translation)
Set `A : AddSubgroup k` to `(IsLocalRing.maximalIdeal 𝒪[k] ^ r).toAddSubgroup.map (algebraMap 𝒪[k] k).toAddMonoidHom`. Establish `hA : (A : Set k) = {x : k | InPow r x}`. Use extensionality with `x`. Simplify using `only [A, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_ofPred_eq, InPow]`. Both sides reduce to the same expression.

Rewrite using `[← hA]`. Take `⟨w, hw, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (IsDiscreteValuationRing.not_a_field 𝒪[k])`. Establish `hc : (algebraMap 𝒪[k] k w) ^ r ≠ 0`. Use `pow_ne_zero _ ?_` and prove the remaining obligations. Introduce `h`.

Conclude with `hw0 (Subtype.val_injective h)`. Use `A.isOpen_of_mem_nhds (g := 0) ?_` and prove the remaining obligations. Rewrite using `[mem_nhds_iff]`. Use `⟨(fun x => (algebraMap 𝒪[k] k w) ^ r * x) '' (𝒪[k] : Set k), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Use `⟨w ^ r * ⟨y, hy⟩, Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw r), ?_⟩` and prove the remaining obligations. Use `show algebraMap 𝒪[k] k (w ^ r * ⟨y, hy⟩) = algebraMap 𝒪[k] k w ^ r * y`. Rewrite using `[map_mul, map_pow]`. Both sides reduce to the same expression. Use `(Homeomorph.mulLeft₀ _ hc).isOpenMap _ (Valuation.isOpen_integer (v := valuation k))` as an intermediate fact.

Simplify using `using this`. Conclude with `⟨0, zero_mem _, mul_zero _⟩`.
-/
theorem isOpen_inPow (r : ℕ) : IsOpen {x : k | InPow r x} := by
  let A : AddSubgroup k :=
    (IsLocalRing.maximalIdeal 𝒪[k] ^ r).toAddSubgroup.map (algebraMap 𝒪[k] k).toAddMonoidHom
  have hA : (A : Set k) = {x : k | InPow r x} := by
    ext x
    simp only [A, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_ofPred_eq, InPow]
    rfl
  rw [← hA]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (IsDiscreteValuationRing.not_a_field 𝒪[k])
  have hc : (algebraMap 𝒪[k] k w) ^ r ≠ 0 := by
    refine pow_ne_zero _ ?_
    intro h
    exact hw0 (Subtype.val_injective h)
  refine A.isOpen_of_mem_nhds (g := 0) ?_
  rw [mem_nhds_iff]
  refine ⟨(fun x => (algebraMap 𝒪[k] k w) ^ r * x) '' (𝒪[k] : Set k), ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨w ^ r * ⟨y, hy⟩, Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw r), ?_⟩
    show algebraMap 𝒪[k] k (w ^ r * ⟨y, hy⟩) = algebraMap 𝒪[k] k w ^ r * y
    rw [map_mul, map_pow]
    rfl
  · have := (Homeomorph.mulLeft₀ _ hc).isOpenMap _ (Valuation.isOpen_integer (v := valuation k))
    simpa using this
  · exact ⟨0, zero_mem _, mul_zero _⟩

/- English proof (translation)
Establish `e : KC k n r = (KO k (Fin n) : Set (GL (Fin n) k)) ∩ ⋂ i, ⋂ j, (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) ⁻¹' {x : k | InPow r x}`. Use extensionality with `g`. Simplify using `only [KC, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]`. Rewrite using `[e]`. Use `GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_inPow r).preimage ?_)` and prove the remaining obligations.

Use `Units.continuous_val (M := Matrix (Fin n) (Fin n) k)` as an intermediate fact. Use `fun_prop`.
-/
theorem isOpen_KC (n r : ℕ) : IsOpen (KC k n r) := by
  have e : KC k n r = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) ⁻¹'
        {x : k | InPow r x} := by
    ext g
    simp only [KC, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_inPow r).preimage ?_)
  have := Units.continuous_val (M := Matrix (Fin n) (Fin n) k)
  fun_prop

end UpperTheory.TNZ.Grp.P_KC

namespace UpperTheory.TNZ.Grp

open P_KC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `hB r`. Use `⟨?_, ?_, isOpen_KC n r, fun g hg => hg.1, ?_⟩` and prove the remaining obligations. Use `show ((Subgroup.closure (KC k n r) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = KC k n r`. Rewrite using `[← coe_H, Subgroup.closure_eq]`. Introduce `g hg u hu`.

Take `⟨v, rfl⟩` from `hg`. Take `⟨w, hw, rfl⟩` from `(mem_KC_iff n r u).1 hu`. Use `(mem_KC_iff n r _).2 ⟨v * w * v⁻¹, ?_, by simp⟩` and prove the remaining obligations. Rewrite `hw`, the goal using `[SetLike.mem_coe, MonoidHom.mem_ker]`. Simplify using `[hw]`.

Introduce `hr g hg`. Use `⟨hg.1, fun i j hij => ?_⟩` and prove the remaining obligations. Establish `hne : i ≠ j` using `fun h => (ne_of_lt hij) (h ▸ rfl)`. Take `⟨y, hy, e⟩` from `hg.2 i j`. Rewrite `e` using `[if_neg hne, sub_zero]`.

Establish `hc : cc G.μ (G.bl j) (G.bl i) ≤ r` using `(hB.2.1 (G.bl j) (G.bl i)).le.trans hr`. Conclude with `⟨y, Ideal.pow_le_pow_right hc hy, e⟩`.
-/
theorem step_KC {n : ℕ} (G : Grp k n) : CompactOpenKernelProp G := by
  intro hB r
  refine ⟨?_, ?_, isOpen_KC n r, fun g hg => hg.1, ?_⟩
  · show ((Subgroup.closure (KC k n r) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = KC k n r
    rw [← coe_H, Subgroup.closure_eq]
  · intro g hg u hu
    obtain ⟨v, rfl⟩ := hg
    obtain ⟨w, hw, rfl⟩ := (mem_KC_iff n r u).1 hu
    refine (mem_KC_iff n r _).2 ⟨v * w * v⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hw ⊢
    simp [hw]
  · intro hr g hg
    refine ⟨hg.1, fun i j hij => ?_⟩
    have hne : i ≠ j := fun h => (ne_of_lt hij) (h ▸ rfl)
    obtain ⟨y, hy, e⟩ := hg.2 i j
    rw [if_neg hne, sub_zero] at e
    have hc : cc G.μ (G.bl j) (G.bl i) ≤ r := (hB.2.1 (G.bl j) (G.bl i)).le.trans hr
    exact ⟨y, Ideal.pow_le_pow_right hc hy, e⟩

end UpperTheory.TNZ.Grp

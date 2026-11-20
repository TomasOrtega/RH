import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

def sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) where
  carrier := {x | ∀ v ∉ S, ord v x = 0}
  one_mem' v _ := ord_one v
  mul_mem' {x y} hx hy v hv := by rw [ord_mul, hx v hv, hy v hv, add_zero]
  inv_mem' {x} hx v hv := by rw [ord_inv, hx v hv, neg_zero]

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_sIdeles {x : IdeleGroup K} : x ∈ sIdeles S ↔ ∀ v ∉ S, ord v x = 0 :=
  Iff.rfl

/- English proof (translation)
Simplify using `only [mem_sIdeles, ord_eq_zero_iff]`.
-/
theorem mem_sIdeles_iff {x : IdeleGroup K} :
    x ∈ sIdeles S ↔ ∀ v ∉ S, (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by
  simp only [mem_sIdeles, ord_eq_zero_iff]

/- English proof (translation)
The claim follows from `fun _ hx v _ ↦ mem_standardOpenSubgroup_iff_ord.1 hx v`.
-/
theorem standardOpenSubgroup_le_sIdeles : standardOpenSubgroup K ≤ sIdeles S :=
  fun _ hx v _ ↦ mem_standardOpenSubgroup_iff_ord.1 hx v

/- English proof (translation)
The claim follows from `fun _ hx v hv ↦ hx v fun hvS ↦ hv (h hvS)`.
-/
theorem sIdeles_mono {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    sIdeles S ≤ sIdeles T :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (h hvS)

/- English proof (translation)
Rewrite using `[neg_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← exp_log hy, h, exp_zero]`. Introduce and unpack `rfl`.

Conclude with `log_one`.
-/
theorem neg_log_eq_zero_iff {y : ℤᵐ⁰} (hy : y ≠ 0) : -log y = 0 ↔ y = 1 := by
  rw [neg_eq_zero]
  constructor
  · intro h
    rw [← exp_log hy, h, exp_zero]
  · rintro rfl
    exact log_one

/- English proof (translation)
Establish `ha : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (a : K) ≠ 0` using `fun v ↦ (Valuation.ne_zero_iff _).2 a.ne_zero`. Simplify using `only [mem_sIdeles, ord_diagonal, neg_log_eq_zero_iff (ha _)]`. Both sides reduce to the same expression.
-/
theorem diagonal_mem_sIdeles_iff (a : Kˣ) : diagonal K a ∈ sIdeles S ↔ a ∈ S.unit K := by
  have ha : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (a : K) ≠ 0 := fun v ↦
    (Valuation.ne_zero_iff _).2 a.ne_zero
  simp only [mem_sIdeles, ord_diagonal, neg_log_eq_zero_iff (ha _)]
  rfl

/- English proof (translation)
Establish `hx : x ∈ (diagonal K).range ⊔ sIdeles S` using `h ▸ Subgroup.mem_top x`. Take `⟨_, ⟨a, rfl⟩, s, hs, hx⟩` from `Subgroup.mem_sup.1 hx`. Conclude with `⟨a, s, hs, hx⟩`.
-/
theorem exists_diagonal_mul_of_sup_eq_top (h : (diagonal K).range ⊔ sIdeles S = ⊤)
    (x : IdeleGroup K) : ∃ a : Kˣ, ∃ s ∈ sIdeles S, diagonal K a * s = x := by
  have hx : x ∈ (diagonal K).range ⊔ sIdeles S := h ▸ Subgroup.mem_top x
  obtain ⟨_, ⟨a, rfl⟩, s, hs, hx⟩ := Subgroup.mem_sup.1 hx
  exact ⟨a, s, hs, hx⟩

/- English proof (translation)
The claim follows from `eq_top_iff.2 (h.symm.le.trans (sup_le_sup_left (sIdeles_mono hST) _))`.
-/
theorem sup_sIdeles_eq_top_of_subset {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T)
    (h : (diagonal K).range ⊔ sIdeles S = ⊤) : (diagonal K).range ⊔ sIdeles T = ⊤ :=
  eq_top_iff.2 (h.symm.le.trans (sup_le_sup_left (sIdeles_mono hST) _))

/- English proof (translation)
Use `choose x hx using toClassGroup_surjective (K := K)`. Set `S : Finset (HeightOneSpectrum (𝓞 K))` to `Finset.univ.biUnion fun c ↦ (Filter.eventually_cofinite.1 (eventually_ord_eq_zero (x c))).toFinset`. Establish `hxS : ∀ c, x c ∈ sIdeles (S : Set (HeightOneSpectrum (𝓞 K)))`. Introduce `c v hv`. Assume the negation of the conclusion as `h`.

Conclude with `hv (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ c, Set.Finite.mem_toFinset _ |>.2 h⟩)`. Use `⟨S, eq_top_iff.2 fun y _ ↦ ?_⟩` and prove the remaining obligations. Establish `hker : y * (x (toClassGroup y))⁻¹ ∈ (toClassGroup (K` using `K)).ker := by`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel]`. Rewrite `hker` using `[ker_toClassGroup]`.

Establish `h` using `mul_mem (sup_le_sup_left (standardOpenSubgroup_le_sIdeles _) _ hker) (Subgroup.mem_sup_right (hxS (toClassGroup y)))`. Rewrite `h` using `[inv_mul_cancel_right]`. Then use the resulting hypothesis.
-/
theorem exists_finset_sup_sIdeles_eq_top :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  classical
  choose x hx using toClassGroup_surjective (K := K)
  let S : Finset (HeightOneSpectrum (𝓞 K)) := Finset.univ.biUnion fun c ↦
    (Filter.eventually_cofinite.1 (eventually_ord_eq_zero (x c))).toFinset
  have hxS : ∀ c, x c ∈ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro c v hv
    by_contra h
    exact hv (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ c, Set.Finite.mem_toFinset _ |>.2 h⟩)
  refine ⟨S, eq_top_iff.2 fun y _ ↦ ?_⟩
  have hker : y * (x (toClassGroup y))⁻¹ ∈ (toClassGroup (K := K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel]
  rw [ker_toClassGroup] at hker
  have h := mul_mem (sup_le_sup_left (standardOpenSubgroup_le_sIdeles _) _ hker)
    (Subgroup.mem_sup_right (hxS (toClassGroup y)))
  rwa [inv_mul_cancel_right] at h

def sUnitsToSIdeles : S.unit K →* sIdeles S :=
  ((diagonal K).comp (S.unit K).subtype).codRestrict (sIdeles S) fun a ↦
    (diagonal_mem_sIdeles_iff S a).2 a.2

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_sUnitsToSIdeles (a : S.unit K) :
    (sUnitsToSIdeles S a : IdeleGroup K) = diagonal K a :=
  rfl

def sIdelesToIdeleClassGroup : sIdeles S →* IdeleClassGroup K :=
  (IdeleClassGroup.mk K).comp (sIdeles S).subtype

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sIdelesToIdeleClassGroup_apply (s : sIdeles S) :
    sIdelesToIdeleClassGroup S s = IdeleClassGroup.mk K s :=
  rfl

/- English proof (translation)
The claim follows from `fun _ _ h ↦ Subtype.ext (diagonal_injective K (congrArg Subtype.val h))`.
-/
theorem sUnitsToSIdeles_injective : Function.Injective (sUnitsToSIdeles S) := fun _ _ h ↦
  Subtype.ext (diagonal_injective K (congrArg Subtype.val h))

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Rewrite using `[MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, coe_sUnitsToSIdeles]`. Conclude with `IdeleClassGroup.mk_diagonal K a`.

Introduce `hy`. Rewrite `hy` using `[MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, ← MonoidHom.mem_ker, IdeleClassGroup.ker_mk]`. Take `⟨a, ha⟩` from `hy`. Establish `haS : a ∈ S.unit K` using `(diagonal_mem_sIdeles_iff S a).1 (ha ▸ y.2)`. Conclude with `⟨⟨a, haS⟩, Subtype.ext ha⟩`.
-/
theorem range_sUnitsToSIdeles :
    (sUnitsToSIdeles S).range = (sIdelesToIdeleClassGroup S).ker := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, coe_sUnitsToSIdeles]
    exact IdeleClassGroup.mk_diagonal K a
  · intro hy
    rw [MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, ← MonoidHom.mem_ker,
      IdeleClassGroup.ker_mk] at hy
    obtain ⟨a, ha⟩ := hy
    have haS : a ∈ S.unit K := (diagonal_mem_sIdeles_iff S a).1 (ha ▸ y.2)
    exact ⟨⟨a, haS⟩, Subtype.ext ha⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `eq_top_iff.2 fun y _ ↦ ?_` and prove the remaining obligations. Take `⟨s, hs⟩` from `h (IdeleClassGroup.mk K y)`. Rewrite `hs` using `[sIdelesToIdeleClassGroup_apply]`.

Establish `hr : (s : IdeleGroup K)⁻¹ * y ∈ (diagonal K).range`. Rewrite using `[← IdeleClassGroup.ker_mk, MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]`. Establish `h'` using `mul_mem (Subgroup.mem_sup_right (S := (diagonal K).range) s.2) (Subgroup.mem_sup_left (T := sIdeles S) hr)`. Rewrite `h'` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis. Introduce `h c`.

Take `⟨y, rfl⟩` from `IdeleClassGroup.mk_surjective K c`. Take `⟨a, s, hs, rfl⟩` from `exists_diagonal_mul_of_sup_eq_top S h y`. Use `⟨⟨s, hs⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[sIdelesToIdeleClassGroup_apply, map_mul, IdeleClassGroup.mk_diagonal]`. Conclude with `(one_mul (IdeleClassGroup.mk K s)).symm`.
-/
theorem sIdelesToIdeleClassGroup_surjective_iff :
    Function.Surjective (sIdelesToIdeleClassGroup S) ↔ (diagonal K).range ⊔ sIdeles S = ⊤ := by
  constructor
  · intro h
    refine eq_top_iff.2 fun y _ ↦ ?_
    obtain ⟨s, hs⟩ := h (IdeleClassGroup.mk K y)
    rw [sIdelesToIdeleClassGroup_apply] at hs
    have hr : (s : IdeleGroup K)⁻¹ * y ∈ (diagonal K).range := by
      rw [← IdeleClassGroup.ker_mk, MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
    have h' := mul_mem (Subgroup.mem_sup_right (S := (diagonal K).range) s.2)
      (Subgroup.mem_sup_left (T := sIdeles S) hr)
    rwa [mul_inv_cancel_left] at h'
  · intro h c
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective K c
    obtain ⟨a, s, hs, rfl⟩ := exists_diagonal_mul_of_sup_eq_top S h y
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [sIdelesToIdeleClassGroup_apply, map_mul, IdeleClassGroup.mk_diagonal]
    exact (one_mul (IdeleClassGroup.mk K s)).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨sUnitsToSIdeles_injective S, range_sUnitsToSIdeles S, (sIdelesToIdeleClassGroup_surjective_iff S).2 h⟩`.
-/
theorem sUnits_sIdeles_exact (h : (diagonal K).range ⊔ sIdeles S = ⊤) :
    Function.Injective (sUnitsToSIdeles S) ∧
      (sUnitsToSIdeles S).range = (sIdelesToIdeleClassGroup S).ker ∧
      Function.Surjective (sIdelesToIdeleClassGroup S) :=
  ⟨sUnitsToSIdeles_injective S, range_sUnitsToSIdeles S,
    (sIdelesToIdeleClassGroup_surjective_iff S).2 h⟩

instance : (sUnitsToSIdeles S).range.Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

def sIdelesQuotientEquiv (h : (diagonal K).range ⊔ sIdeles S = ⊤) :
    sIdeles S ⧸ (sUnitsToSIdeles S).range ≃* IdeleClassGroup K :=
  (QuotientGroup.quotientMulEquivOfEq (range_sUnitsToSIdeles S)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((sIdelesToIdeleClassGroup_surjective_iff S).2 h))

end IdeleGroup

end

end GroundTheory.Global

import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobDense

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]

/- English proof (translation)
Unfold `Dat3.HL`. Use `infer_instance`.
-/
theorem hl_normal' (D : Dat3 l O) : D.HL.Normal := by
  unfold Dat3.HL; infer_instance

/- English proof (translation)
Establish `e : (D.η.ker : Set (GQ l)) = (D.Kv.1.fixingSubgroup : Set (GQ l))`. Use extensionality with `g`. Conclude with `D.η_ker g`. Establish `h1 : IsOpen (D.η.ker : Set (GQ l))`. Rewrite using `[e]`.

Use `haveI := D.Kv.2`. Conclude with `IntermediateField.fixingSubgroup_isOpen D.Kv.1`. Conclude with `h1.inter D.τ_open`.
-/
theorem hl_isOpen' (D : Dat3 l O) : IsOpen (D.HL : Set (GQ l)) := by
  have e : (D.η.ker : Set (GQ l)) = (D.Kv.1.fixingSubgroup : Set (GQ l)) := by
    ext g; exact D.η_ker g
  have h1 : IsOpen (D.η.ker : Set (GQ l)) := by
    rw [e]; haveI := D.Kv.2; exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  exact h1.inter D.τ_open

/- English proof (translation)
Use `haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`.
-/
theorem finiteIndex_of_open' (H : OpenSubgroup (GQ l)) : (H : Subgroup (GQ l)).FiniteIndex := by
  haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
  exact Subgroup.finiteIndex_of_finite_quotient

/- English proof (translation)
Use `haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))`. Use `haveI hHn : D.HL.Normal := hl_normal' D`. Establish `hHo : IsOpen (D.HL : Set (GQ l))` using `hl_isOpen' D`. Take `⟨hIn, -, -, ⟨σ₀, hσ₀⟩, -⟩` from `iqBasic l`. Use `haveI : D.HL.FiniteIndex := finiteIndex_of_open' ⟨D.HL, hHo⟩`.

Use `set N : Subgroup (GQ l) := D.HL ⊔ Iq l with hN`. Use `haveI : N.FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left`. Use `haveI : N.Normal := Subgroup.sup_normal _ _`. Use `set q : GQ l ⧸ N := (σ₀ : GQ l ⧸ N)`. Use `set m := orderOf q with hm`.

Establish `hm1 : 1 ≤ m` using `orderOf_pos q`. Establish `hmN : σ₀ ^ m ∈ N`. Rewrite using `[← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]`. Conclude with `pow_orderOf_eq_one q`. Take `⟨h, hh, i₀, hi₀, hhi⟩` from `Subgroup.mem_sup_of_normal_right.1 hmN`.

Set `φ` to `QuotientGroup.mk' (Iq l)`. Establish `hφ : ∀ {x}, φ x = 1 ↔ x ∈ Iq l` using `fun {x} => QuotientGroup.eq_one_iff x`. Establish `hφm : φ σ₀ ^ m = φ h`. Rewrite using `[← map_pow, ← hhi, map_mul, hφ.2 hi₀, mul_one]`. Use `⟨h, ⟨hh, ?_⟩, σ₀, m, hσ₀, hm1, ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce `g _`. Rewrite using `[← SetLike.mem_coe, Subgroup.topologicalClosure_coe]`. Rewrite using `[mem_closure_iff]`. Introduce `U hU hgU`.

Establish `hdense` using `frobDense σ₀ hσ₀`. Establish `hV : IsOpen (D.HL.subtype '' U)` using `(hHo.isOpenEmbedding_subtypeVal).isOpenMap U hU`. Establish `hcl : (D.HL.subtype g) ∈ closure ((Iq l ⊔ Subgroup.zpowers σ₀ : Subgroup (GQ l)) : Set (GQ l))`. Rewrite using `[← Subgroup.topologicalClosure_coe, hdense]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨x, ⟨u, huU, rfl⟩, hxT⟩` from `mem_closure_iff.1 hcl _ hV ⟨g, hgU, rfl⟩`. Take `⟨i, hi, z, hz, hiz⟩` from `Subgroup.mem_sup_of_normal_left.1 hxT`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hz`. Express the relevant statement in the definitionally equal form `i * σ₀ ^ k = (u : GQ l) at hiz`. Establish `hkN : σ₀ ^ k ∈ N`.

Establish `: σ₀ ^ k = i⁻¹ * (u : GQ l)` using `by rw [← hiz]; group`. Rewrite using `[this]`. Conclude with `N.mul_mem (Subgroup.mem_sup_right (Subgroup.inv_mem _ hi)) (Subgroup.mem_sup_left u.2)`. Establish `hdvd : (m : ℤ) ∣ k`. Rewrite using `[hm, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]`.

Conclude with `hkN`. Take `⟨j, rfl⟩` from `hdvd`. Establish `hφu : φ (u : GQ l) = φ h ^ j`. Rewrite using `[← hiz, map_mul, hφ.2 hi, one_mul, map_zpow, zpow_mul, zpow_natCast, hφm]`. Establish `hy : (u : GQ l) * h ^ (-j) ∈ Iq l`.

Rewrite using `[← hφ, map_mul, map_zpow, hφu, zpow_neg, mul_inv_cancel]`. Use `⟨u, huU, ?_⟩` and prove the remaining obligations. Establish `e : u = (⟨(u : GQ l) * h ^ (-j), D.HL.mul_mem u.2 (D.HL.zpow_mem hh _)⟩ : ↥D.HL) * (⟨h, hh⟩ : ↥D.HL) ^ j` using `by ext; simp`. Rewrite using `[SetLike.mem_coe, e]`. Conclude with `Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))`.

Rewrite using `[← hhi]`. Simplify using `using Subgroup.inv_mem _ hi₀`.
-/
theorem exists_isFr (D : Dat3 l O) : ∃ σ, IsFr D σ := by
  haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
  haveI hHn : D.HL.Normal := hl_normal' D
  have hHo : IsOpen (D.HL : Set (GQ l)) := hl_isOpen' D
  obtain ⟨hIn, -, -, ⟨σ₀, hσ₀⟩, -⟩ := iqBasic l
  haveI : D.HL.FiniteIndex := finiteIndex_of_open' ⟨D.HL, hHo⟩
  set N : Subgroup (GQ l) := D.HL ⊔ Iq l with hN
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  haveI : N.Normal := Subgroup.sup_normal _ _
  set q : GQ l ⧸ N := (σ₀ : GQ l ⧸ N)
  set m := orderOf q with hm
  have hm1 : 1 ≤ m := orderOf_pos q
  have hmN : σ₀ ^ m ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact pow_orderOf_eq_one q
  obtain ⟨h, hh, i₀, hi₀, hhi⟩ := Subgroup.mem_sup_of_normal_right.1 hmN
  let φ := QuotientGroup.mk' (Iq l)
  have hφ : ∀ {x}, φ x = 1 ↔ x ∈ Iq l := fun {x} => QuotientGroup.eq_one_iff x
  have hφm : φ σ₀ ^ m = φ h := by
    rw [← map_pow, ← hhi, map_mul, hφ.2 hi₀, mul_one]
  refine ⟨h, ⟨hh, ?_⟩, σ₀, m, hσ₀, hm1, ?_⟩
  ·
    rw [eq_top_iff]
    intro g _
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
    rw [mem_closure_iff]
    intro U hU hgU
    have hdense := frobDense σ₀ hσ₀
    have hV : IsOpen (D.HL.subtype '' U) := (hHo.isOpenEmbedding_subtypeVal).isOpenMap U hU
    have hcl : (D.HL.subtype g) ∈ closure ((Iq l ⊔ Subgroup.zpowers σ₀ : Subgroup (GQ l)) : Set (GQ l)) := by
      rw [← Subgroup.topologicalClosure_coe, hdense]; trivial
    obtain ⟨x, ⟨u, huU, rfl⟩, hxT⟩ := mem_closure_iff.1 hcl _ hV ⟨g, hgU, rfl⟩
    obtain ⟨i, hi, z, hz, hiz⟩ := Subgroup.mem_sup_of_normal_left.1 hxT
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    change i * σ₀ ^ k = (u : GQ l) at hiz
    have hkN : σ₀ ^ k ∈ N := by
      have : σ₀ ^ k = i⁻¹ * (u : GQ l) := by rw [← hiz]; group
      rw [this]
      exact N.mul_mem (Subgroup.mem_sup_right (Subgroup.inv_mem _ hi)) (Subgroup.mem_sup_left u.2)
    have hdvd : (m : ℤ) ∣ k := by
      rw [hm, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]; exact hkN
    obtain ⟨j, rfl⟩ := hdvd
    have hφu : φ (u : GQ l) = φ h ^ j := by
      rw [← hiz, map_mul, hφ.2 hi, one_mul, map_zpow, zpow_mul, zpow_natCast, hφm]
    have hy : (u : GQ l) * h ^ (-j) ∈ Iq l := by
      rw [← hφ, map_mul, map_zpow, hφu, zpow_neg, mul_inv_cancel]
    refine ⟨u, huU, ?_⟩
    have e : u = (⟨(u : GQ l) * h ^ (-j), D.HL.mul_mem u.2 (D.HL.zpow_mem hh _)⟩ : ↥D.HL) * (⟨h, hh⟩ : ↥D.HL) ^ j := by
      ext; simp
    rw [SetLike.mem_coe, e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
  · rw [← hhi]; simpa using Subgroup.inv_mem _ hi₀

/- English proof (translation)
Introduce `l _ O _ _ _ D`. Conclude with `Classical.epsilon_spec (exists_isFr D)`.
-/
theorem fr_isFr : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O),
    GlobalTheory.OrdLoc.IsFr D (GlobalTheory.OrdLoc.fr D) := by
  intro l _ O _ _ _ D
  exact Classical.epsilon_spec (exists_isFr D)

end GlobalTheory.OrdLoc

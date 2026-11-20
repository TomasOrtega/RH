import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocRootsY
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArithFrobeniusAbsGalois
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `h0 : (x : PadicAlgCl l) ≠ 0`. Introduce `e`. Rewrite `h` using `[e, norm_zero]`. Conclude with `zero_ne_one h`. Use `IsUnit.of_mul_eq_one ⟨(x : PadicAlgCl l)⁻¹, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ?_⟩ (Subtype.ext (mul_inv_cancel₀ h0))` and prove the remaining obligations.

Rewrite using `[norm_inv, h, inv_one]`.
-/
private theorem iqb_unit (x : integralClosure ℤ_[l] (PadicAlgCl l)) (h : ‖(x : PadicAlgCl l)‖ = 1) : IsUnit x := by
  have h0 : (x : PadicAlgCl l) ≠ 0 := by
    intro e; rw [e, norm_zero] at h; exact zero_ne_one h
  refine IsUnit.of_mul_eq_one ⟨(x : PadicAlgCl l)⁻¹, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ?_⟩
    (Subtype.ext (mul_inv_cancel₀ h0))
  rw [norm_inv, h, inv_one]

/- English proof (translation)
Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_` and prove the remaining obligations. Establish `hx : ‖(x : PadicAlgCl l)‖ ≤ 1` using `(GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 x.2`. Break down `hx.eq_or_lt with h | h` into its components or cases. Conclude with `Or.inl (iqb_unit x h)`. Use `Or.inr (iqb_unit _ ?_)` and prove the remaining obligations.

Establish `: ‖(1 : PadicAlgCl l)‖ ≠ ‖-(x : PadicAlgCl l)‖` using `by rw [norm_one, norm_neg]; exact h.ne'`. Establish `h2` using `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this`. Rewrite `h2` using `[norm_one, norm_neg, max_eq_left hx]`. Simplify `h2` using `[sub_eq_add_neg]`.
-/
private theorem iqb_local : IsLocalRing (integralClosure ℤ_[l] (PadicAlgCl l)) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  have hx : ‖(x : PadicAlgCl l)‖ ≤ 1 := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 x.2
  rcases hx.eq_or_lt with h | h
  · exact Or.inl (iqb_unit x h)
  · refine Or.inr (iqb_unit _ ?_)
    have : ‖(1 : PadicAlgCl l)‖ ≠ ‖-(x : PadicAlgCl l)‖ := by rw [norm_one, norm_neg]; exact h.ne'
    have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this
    rw [norm_one, norm_neg, max_eq_left hx] at h2
    simpa [sub_eq_add_neg] using h2

/- English proof (translation)
Use `haveI := iqb_local (l := l)`. Establish `e : IsLocalRing.ResidueField ℤ_[l] ≃+* ZMod l` using `PadicInt.residueField`. Take `⟨g, hg⟩` from `GlobalTheory.exists_arithFrobenius_absGalois ℤ_[l] ℚ_[l] (Finite.of_equiv _ e.symm.toEquiv) (PadicAlgCl l)`. Use `⟨g, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hm⟩` from `hg ⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩`.

Rewrite `hm` using `[Nat.card_congr e.toEquiv, Nat.card_zmod]`. Establish `hle` using `(GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 (y - (⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩ : integralClosure ℤ_[l] (PadicAlgCl l)) ^ l).2`. Establish `hne` using `mt (iqb_unit _) hm`. Use `lt_of_le_of_ne hle hne` as an intermediate fact. Simplify `this` using `[hy]`.
-/
private theorem iqb_frob : ∃ g : GQ l, IsFrob g := by
  haveI := iqb_local (l := l)
  have e : IsLocalRing.ResidueField ℤ_[l] ≃+* ZMod l := PadicInt.residueField
  obtain ⟨g, hg⟩ := GlobalTheory.exists_arithFrobenius_absGalois ℤ_[l] ℚ_[l] (Finite.of_equiv _ e.symm.toEquiv) (PadicAlgCl l)
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨y, hy, hm⟩ := hg ⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod] at hm
  have hle := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1
    (y - (⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩ : integralClosure ℤ_[l] (PadicAlgCl l)) ^ l).2
  have hne := mt (iqb_unit _) hm
  have := lt_of_le_of_ne hle hne
  simpa [hy] using this

/- English proof (translation)
The claim follows from `KStar.IdealValuations.norm_aut_and_roots.1 g x`.
-/
private theorem iqb_norm (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := KStar.IdealValuations.norm_aut_and_roots.1 g x

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by rwa [norm_neg]))`.
-/
private theorem iqb_sub {x y : Om l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by rwa [norm_neg]))

/- English proof (translation)
Rewrite using `[Iq, IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hg x hx`. Break down `lt_or_eq_of_le hx with hlt | heq` into its components or cases. Conclude with `iqb_sub (by rwa [iqb_norm]) hlt`.

Take `⟨m, ζ, hm, hζ, hxζ⟩` from `KStar.IdealValuations.exists_root_congr heq`. Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))`. Establish `h1 : g ζ = ζ` using `hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)`. Establish `h2 : g x - x = g (x - ζ) - (x - ζ)` using `by rw [map_sub, h1]; ring`. Rewrite using `[h2]`.

Conclude with `iqb_sub (by rwa [iqb_norm]) hxζ`. Introduce `hg x hx`. Establish `hle : MaximalUnramifiedExtension l ≤ IntermediateField.fixedField (Subgroup.zpowers g)`. Rewrite using `[MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]`. Introduce and unpack `ζ ⟨m, hm0, hm, hζ⟩`.

Establish `hn : ‖ζ‖ = 1`. Establish `h1 : ‖ζ‖ ^ m = 1` using `by rw [← norm_pow, hζ, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').mp h1`. Establish `h1 : g ζ = ζ` using `KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hζ, map_one]) hζ (hg ζ hn.le)`. Establish `h2 : Subgroup.zpowers g ≤ MulAction.stabilizer (GQ l) ζ` using `(Subgroup.zpowers_le (G := GQ l)).2 h1`.

Conclude with `(IntermediateField.mem_fixedField_iff _ _).2 fun f hf => h2 hf`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 (hle hx) g (Subgroup.mem_zpowers g)`.
-/
private theorem iqb_mem (g : GQ l) : g ∈ Iq l ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖g x - x‖ < 1 := by
  rw [Iq, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact iqb_sub (by rwa [iqb_norm]) hlt
    · obtain ⟨m, ζ, hm, hζ, hxζ⟩ := KStar.IdealValuations.exists_root_congr heq
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
      have h1 : g ζ = ζ := hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
      have h2 : g x - x = g (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
      rw [h2]
      exact iqb_sub (by rwa [iqb_norm]) hxζ
  · intro hg x hx
    have hle : MaximalUnramifiedExtension l ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      rw [MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]
      rintro ζ ⟨m, hm0, hm, hζ⟩
      have hn : ‖ζ‖ = 1 := by
        have h1 : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, hζ, norm_one]
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').mp h1
      have h1 : g ζ = ζ := KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hζ, map_one]) hζ
        (hg ζ hn.le)
      have h2 : Subgroup.zpowers g ≤ MulAction.stabilizer (GQ l) ζ :=
        (Subgroup.zpowers_le (G := GQ l)).2 h1
      exact (IntermediateField.mem_fixedField_iff _ _).2 fun f hf => h2 hf
    exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) g (Subgroup.mem_zpowers g)

end UpperTheory.V.Loc

/- English proof (translation)
Introduce `v _`. Use `⟨⟨fun n hn g => ?_⟩, ?_, iqb_mem, iqb_frob, fun σ σ' hσ => ?_⟩` and prove the remaining obligations. Rewrite `hn`, the goal using `[iqb_mem]`. Introduce `x hx`. Establish `h` using `hn (g⁻¹ x) (by rwa [iqb_norm])`.

Establish `e : (g * n * g⁻¹) x - x = g (n (g⁻¹ x) - g⁻¹ x)`. Rewrite using `[map_sub, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹ x, mul_inv_cancel, AlgEquiv.one_apply]`. Rewrite using `[e, iqb_norm]` and apply the resulting hypothesis. Establish `: IsGalois ℚ_[v] (Om v)` using `{}`. Conclude with `InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension v)`.

Establish `e : ∀ x : Om v, ‖(σ⁻¹ * σ') x - x‖ = ‖σ' x - σ x‖` using `fun x => by`. Rewrite using `[← iqb_norm σ, map_sub, ← AlgEquiv.mul_apply, mul_inv_cancel_left]`. Rewrite using `[iqb_mem]`. Simplify using `only [e]`. Prove the components needed by the constructor for the conclusion.

Introduce `h x hx`. Establish `h2 : σ' x - σ x = (σ' x - x ^ v) - (σ x - x ^ v)` using `by ring`. Rewrite using `[h2]`. Conclude with `iqb_sub (h x hx) (hσ x hx)`. Introduce `h x hx`.

Establish `h2 : σ' x - x ^ v = (σ' x - σ x) - -(σ x - x ^ v)` using `by ring`. Rewrite using `[h2]`. Conclude with `iqb_sub (h x hx) (by rw [norm_neg]; exact hσ x hx)`.
-/
theorem UpperTheory.V.Loc.iqBasic :
    ∀ (v : ℕ) [Fact v.Prime], (Iq v).Normal ∧ IsClosed (Iq v : Set (GQ v)) ∧ (∀ g : GQ v, g ∈ Iq v ↔ ∀ x : Om v, ‖x‖ ≤ 1 → ‖g x - x‖ < 1) ∧ (∃ σ : GQ v, IsFrob σ) ∧ ∀ σ σ' : GQ v, IsFrob σ → (IsFrob σ' ↔ σ⁻¹ * σ' ∈ Iq v) := by
  intro v _
  refine ⟨⟨fun n hn g => ?_⟩, ?_, iqb_mem, iqb_frob, fun σ σ' hσ => ?_⟩
  · rw [iqb_mem] at hn ⊢
    intro x hx
    have h := hn (g⁻¹ x) (by rwa [iqb_norm])
    have e : (g * n * g⁻¹) x - x = g (n (g⁻¹ x) - g⁻¹ x) := by
      rw [map_sub, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹ x, mul_inv_cancel,
        AlgEquiv.one_apply]
    rwa [e, iqb_norm]
  · have : IsGalois ℚ_[v] (Om v) := {}
    exact InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension v)
  · have e : ∀ x : Om v, ‖(σ⁻¹ * σ') x - x‖ = ‖σ' x - σ x‖ := fun x => by
      rw [← iqb_norm σ, map_sub, ← AlgEquiv.mul_apply, mul_inv_cancel_left]
    rw [iqb_mem]
    simp only [e]
    constructor
    · intro h x hx
      have h2 : σ' x - σ x = (σ' x - x ^ v) - (σ x - x ^ v) := by ring
      rw [h2]
      exact iqb_sub (h x hx) (hσ x hx)
    · intro h x hx
      have h2 : σ' x - x ^ v = (σ' x - σ x) - -(σ x - x ^ v) := by ring
      rw [h2]
      exact iqb_sub (h x hx) (by rw [norm_neg]; exact hσ x hx)

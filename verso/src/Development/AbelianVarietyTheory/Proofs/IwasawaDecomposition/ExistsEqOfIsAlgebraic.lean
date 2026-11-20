import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramInIffDifferentIdealEqTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAlgHomRayField

noncomputable section

open Formalism.L2.Host GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.HilbertInClosure

/- English proof (translation)
Set `` to `ι.toAlgebra`. Establish `hi : IsIntegral Qb z` using `(hz.tower_top Qb).isIntegral`. Conclude with `minpoly.mem_range_of_degree_eq_one Qb z (IsAlgClosed.degree_eq_one_of_irreducible Qb (minpoly.irreducible hi))`.
-/
theorem exists_eq_of_isAlgebraic (ι : Qb →+* ℂ) {z : ℂ} (hz : IsAlgebraic ℚ z) : ∃ x, ι x = z := by
  let := ι.toAlgebra
  have hi : IsIntegral Qb z := (hz.tower_top Qb).isIntegral
  exact minpoly.mem_range_of_degree_eq_one Qb z
    (IsAlgClosed.degree_eq_one_of_irreducible Qb (minpoly.irreducible hi))

def qbEquiv (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ M] : qb ι M ≃+* M :=
  RingEquiv.ofBijective ((ι.comp (qb ι M).val.toRingHom).codRestrict M fun x => x.2) ⟨RingHom.injective _, fun z => by
    obtain ⟨x, hx⟩ := exists_eq_of_isAlgebraic ι
      (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z))
    exact ⟨⟨x, mem_qb.2 (hx ▸ z.2)⟩, Subtype.ext hx⟩⟩

/- English proof (translation)
The claim follows from `NumberField.of_ringEquiv M _ (qbEquiv ι M).symm`.
-/
theorem numberField_qb (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] : NumberField (qb ι M) :=
  NumberField.of_ringEquiv M _ (qbEquiv ι M).symm

variable {E : Type} [Field E] [NumberField E] (j : E →ₐ[ℚ] Qb)

@[instance_reducible] def algThrough (L : Fld) (h : j.fieldRange ≤ L) : Algebra E L :=
  (j.toRingHom.codRestrict L fun x => h ⟨x, rfl⟩).toAlgebra

/- English proof (translation)
Rewrite using `[← Module.finrank_mul_finrank ℚ E L, Nat.mul_div_cancel_left _ Module.finrank_pos]`.
-/
theorem finrank_div (L : Type) [Field L] [NumberField L] [Algebra E L] :
    Module.finrank ℚ L / Module.finrank ℚ E = Module.finrank E L := by
  rw [← Module.finrank_mul_finrank ℚ E L, Nat.mul_div_cancel_left _ Module.finrank_pos]

/- English proof (translation)
Take `⟨h, hN, hR⟩` from `hM`. Establish `hle : j.fieldRange ≤ qb ι M`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `h x`. Use `⟨numberField_qb ι M, hle, ?_⟩` and prove the remaining obligations.

Set `` to `algOf _ M h`. Set `` to `algThrough j _ hle`. Use `numberField_qb ι M` as an intermediate fact. Conclude with `hR.of_algEquiv (AlgEquiv.ofRingEquiv (f := qbEquiv ι M) fun x => rfl).symm`.
-/
theorem isRayField_qb (ι : Qb →+* ℂ) {𝔮 : Ideal (𝓞 E)} {M : IntermediateField ℚ ℂ}
    (hM : IsRayFieldIn (ι.comp j.toRingHom) 𝔮 M) :
    ∃ (_ : NumberField (qb ι M)) (h : j.fieldRange ≤ qb ι M), letI := algThrough j _ h; IsRayField E (qb ι M) 𝔮 := by
  obtain ⟨h, hN, hR⟩ := hM
  have hle : j.fieldRange ≤ qb ι M := by
    rintro _ ⟨x, rfl⟩
    exact h x
  refine ⟨numberField_qb ι M, hle, ?_⟩
  let := algOf _ M h
  let := algThrough j _ hle
  have := numberField_qb ι M
  exact hR.of_algEquiv (AlgEquiv.ofRingEquiv (f := qbEquiv ι M) fun x => rfl).symm

/- English proof (translation)
Set `` to `algThrough j L hL`. Set `` to `algThrough j N hN`. Set `: Algebra E Qb` to `j.toRingHom.toAlgebra`. Establish `: IsScalarTower E L Qb` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: IsScalarTower E N Qb` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Set `φ : L →ₐ[E] Qb` to `(IsScalarTower.toAlgHom E N Qb).comp ψ`. Introduce `x hx`. Take `⟨y, hy⟩` from `(φ.restrictNormal' L).surjective ⟨x, hx⟩`. Establish `h1 : algebraMap L Qb (φ.restrictNormal' L y) = φ y` using `φ.restrictNormal_commutes L y`. Rewrite `h1` using `[hy]`.

Establish `h2 : x = (ψ y : Qb)` using `h1`. Conclude with `h2 ▸ (ψ y).2`.
-/
theorem le_of_algHom {L N : Fld} (hL : j.fieldRange ≤ L) (hN : j.fieldRange ≤ N)
    (hn : letI := algThrough j L hL; Normal E L)
    (ψ : letI := algThrough j L hL; letI := algThrough j N hN; L →ₐ[E] N) : L ≤ N := by
  let := algThrough j L hL
  let := algThrough j N hN
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower E N Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φ : L →ₐ[E] Qb := (IsScalarTower.toAlgHom E N Qb).comp ψ
  intro x hx
  obtain ⟨y, hy⟩ := (φ.restrictNormal' L).surjective ⟨x, hx⟩
  have h1 : algebraMap L Qb (φ.restrictNormal' L y) = φ y := φ.restrictNormal_commutes L y
  rw [hy] at h1
  have h2 : x = (ψ y : Qb) := h1
  exact h2 ▸ (ψ y).2

/- English proof (translation)
Set `` to `algThrough j L h`. Set `: Algebra E Qb` to `j.toRingHom.toAlgebra`. Establish `: IsScalarTower E L Qb` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: IsScalarTower ℚ E Qb` using `IsScalarTower.of_algebraMap_eq fun q => (j.commutes q).symm`. Establish `: IsAlgClosure ℚ Qb` using `AlgebraicClosure.instIsAlgClosure ℚ`.

Establish `: IsGalois ℚ Qb` using `IsAlgClosure.isGalois ℚ Qb`. Establish `: IsGalois E Qb` using `IsGalois.tower_top_of_isGalois ℚ E Qb`. Establish `hmem : ∀ s : Qb ≃ₐ[E] Qb, s.restrictScalars ℚ ∈ GalOf j.fieldRange` using `fun s => by`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `s.commutes x`. Prove the components needed by the constructor for the conclusion. Introduce `hab s hs t ht x hx`. Rewrite `hs`, `ht` using `[IntermediateField.mem_fixingSubgroup_iff]`. Set `s' : Qb ≃ₐ[E] Qb` to `AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun y => hs _ ⟨y, rfl⟩`.

Set `t' : Qb ≃ₐ[E] Qb` to `AlgEquiv.ofRingEquiv (f := t.toRingEquiv) fun y => ht _ ⟨y, rfl⟩`. Establish `hc : AlgEquiv.restrictNormalHom L (s' * t') = AlgEquiv.restrictNormalHom L (t' * s')`. Rewrite using `[map_mul, map_mul, IsMulCommutative.is_comm.comm]`. Establish `h1` using `AlgEquiv.restrictNormal_commutes (s' * t') L ⟨x, hx⟩`. Establish `h2` using `AlgEquiv.restrictNormal_commutes (t' * s') L ⟨x, hx⟩`.

Establish `h3 : (s' * t').restrictNormal L = (t' * s').restrictNormal L` using `hc`. Rewrite `h1` using `[h3, h2]`. Conclude with `h1.symm`. Introduce `H`. Establish `hst : ∀ s : Qb ≃ₐ[E] Qb, ∀ x ∈ L, s x ∈ L` using `fun s x hx => by`.

Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]`. Introduce `t ht`. Establish `h1` using `H t (IntermediateField.fixingSubgroup_antitone h ht) _ (hmem s) x hx`. Rewrite `h1` using `[(IntermediateField.mem_fixingSubgroup_iff _ _).1 ht x hx]`. Conclude with `h1`.

Set `L' : IntermediateField E Qb` to `(IsScalarTower.toAlgHom E L Qb).fieldRange`. Establish `hn' : Normal E L'` using `IntermediateField.normal_iff_forall_map_le'.2 fun s => by`. Introduce and unpack `_ ⟨_, ⟨x, rfl⟩, rfl⟩`. Conclude with `⟨⟨_, hst s x x.2⟩, rfl⟩`. Set `e : L ≃ₐ[E] L'` to `AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom E L Qb)`.

Establish `hn : Normal E L` using `Normal.of_algEquiv e.symm`. Establish `: IsGalois E L` using `{}`. Use `{ is_comm := ⟨fun a b => ?_⟩ }` and prove the remaining obligations. Take `⟨s, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) Qb a`. Take `⟨t, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) Qb b`.

Rewrite using `[← map_mul, ← map_mul]`. Use `AlgEquiv.ext fun x => (algebraMap L Qb).injective ?_` and prove the remaining obligations. Conclude with `(AlgEquiv.restrictNormal_commutes (s * t) L x).trans ((H _ (hmem s) _ (hmem t) x x.2).trans (AlgEquiv.restrictNormal_commutes (t * s) L x).symm)`.
-/
theorem isAbelianGalois_iff (L : Fld) (h : j.fieldRange ≤ L) :
    (letI := algThrough j L h; IsAbelianGalois E L) ↔
      ∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ L, s (t x) = t (s x) := by
  let := algThrough j L h
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ E Qb := IsScalarTower.of_algebraMap_eq fun q => (j.commutes q).symm
  have : IsAlgClosure ℚ Qb := AlgebraicClosure.instIsAlgClosure ℚ
  have : IsGalois ℚ Qb := IsAlgClosure.isGalois ℚ Qb
  have : IsGalois E Qb := IsGalois.tower_top_of_isGalois ℚ E Qb
  have hmem : ∀ s : Qb ≃ₐ[E] Qb, s.restrictScalars ℚ ∈ GalOf j.fieldRange := fun s => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨x, rfl⟩
    exact s.commutes x
  constructor
  · intro hab s hs t ht x hx
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs ht
    let s' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun y => hs _ ⟨y, rfl⟩
    let t' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := t.toRingEquiv) fun y => ht _ ⟨y, rfl⟩
    have hc : AlgEquiv.restrictNormalHom L (s' * t') = AlgEquiv.restrictNormalHom L (t' * s') := by
      rw [map_mul, map_mul, IsMulCommutative.is_comm.comm]
    have h1 := AlgEquiv.restrictNormal_commutes (s' * t') L ⟨x, hx⟩
    have h2 := AlgEquiv.restrictNormal_commutes (t' * s') L ⟨x, hx⟩
    have h3 : (s' * t').restrictNormal L = (t' * s').restrictNormal L := hc
    rw [h3, h2] at h1
    exact h1.symm
  · intro H
    have hst : ∀ s : Qb ≃ₐ[E] Qb, ∀ x ∈ L, s x ∈ L := fun s x hx => by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
      intro t ht
      have h1 := H t (IntermediateField.fixingSubgroup_antitone h ht) _ (hmem s) x hx
      rw [(IntermediateField.mem_fixingSubgroup_iff _ _).1 ht x hx] at h1
      exact h1
    let L' : IntermediateField E Qb := (IsScalarTower.toAlgHom E L Qb).fieldRange
    have hn' : Normal E L' := IntermediateField.normal_iff_forall_map_le'.2 fun s => by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨⟨_, hst s x x.2⟩, rfl⟩
    let e : L ≃ₐ[E] L' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom E L Qb)
    have hn : Normal E L := Normal.of_algEquiv e.symm
    have : IsGalois E L := {}
    refine { is_comm := ⟨fun a b => ?_⟩ }
    obtain ⟨s, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) Qb a
    obtain ⟨t, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) Qb b
    rw [← map_mul, ← map_mul]
    refine AlgEquiv.ext fun x => (algebraMap L Qb).injective ?_
    exact (AlgEquiv.restrictNormal_commutes (s * t) L x).trans
      ((H _ (hmem s) _ (hmem t) x x.2).trans (AlgEquiv.restrictNormal_commutes (t * s) L x).symm)

/- English proof (translation)
Set `` to `algThrough j L h`. Set `: Algebra E Qb` to `j.toRingHom.toAlgebra`. Establish `: IsScalarTower E L Qb` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Introduce `s hs x hx`. Rewrite `hs` using `[IntermediateField.mem_fixingSubgroup_iff]`.

Set `s' : Qb ≃ₐ[E] Qb` to `AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun y => hs _ ⟨y, rfl⟩`. Establish `h1 : ((s'.restrictNormal L ⟨x, hx⟩ : L) : Qb) = s x` using `AlgEquiv.restrictNormal_commutes s' L ⟨x, hx⟩`. Conclude with `h1 ▸ (s'.restrictNormal L ⟨x, hx⟩).2`.
-/
theorem map_mem_of_normal (L : Fld) (h : j.fieldRange ≤ L) (hn : letI := algThrough j L h; Normal E L) :
    ∀ s ∈ GalOf j.fieldRange, ∀ x ∈ L, s x ∈ L := by
  let := algThrough j L h
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro s hs x hx
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs
  let s' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun y => hs _ ⟨y, rfl⟩
  have h1 : ((s'.restrictNormal L ⟨x, hx⟩ : L) : Qb) = s x := AlgEquiv.restrictNormal_commutes s' L ⟨x, hx⟩
  exact h1 ▸ (s'.restrictNormal L ⟨x, hx⟩).2

omit j in

/- English proof (translation)
Introduce `H E _ _ _ j ι M hM`. Take `⟨hN, h, hR⟩` from `isRayField_qb j ι hM`. Set `` to `algThrough j _ h`. Use `hR.1` as an intermediate fact. Use `⟨hN, h, hR.1, ?_, fun L _ hL hab hd => ?_⟩` and prove the remaining obligations.

Rewrite using `[finrank_div]`. Conclude with `(GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr E _).1 fun 𝔭 => hR.2.1 𝔭 fun hd => 𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hd))`. Set `` to `algThrough j L hL`. Rewrite `hd` using `[finrank_div]`. Take `⟨ψ⟩` from `GlobalTheory.UnramInRay.nonempty_algHom_rayField H E L (qb ι M) ⊤ top_ne_bot hR ((GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr E L).2 hd)`.

Conclude with `le_of_algHom j hL h inferInstance ψ`.
-/
theorem hilbert_qb : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ), IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ (_ : NumberField (qb ι M)) (h : j.fieldRange ≤ qb ι M),
      (letI := algThrough j _ h; IsAbelianGalois E (qb ι M)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L] (hL : j.fieldRange ≤ L), (letI := algThrough j L hL; IsAbelianGalois E L) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hR⟩ := isRayField_qb j ι hM
  let := algThrough j _ h
  have := hR.1
  refine ⟨hN, h, hR.1, ?_, fun L _ hL hab hd => ?_⟩
  · rw [finrank_div]
    exact (GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr E _).1 fun 𝔭 =>
      hR.2.1 𝔭 fun hd => 𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hd))
  · let := algThrough j L hL
    rw [finrank_div] at hd
    obtain ⟨ψ⟩ := GlobalTheory.UnramInRay.nonempty_algHom_rayField H E L (qb ι M) ⊤ top_ne_bot hR
      ((GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr E L).2 hd)
    exact le_of_algHom j hL h inferInstance ψ

omit j in

/- English proof (translation)
Introduce `H E _ _ _ j ι M hM`. Take `⟨hN, h, hab, hd, hmax⟩` from `hilbert_qb H E j ι M hM`. Use `⟨hN, h, map_mem_of_normal j _ h ?_, (isAbelianGalois_iff j _ h).1 hab, hd, fun L _ hL hc => hmax L hL ((isAbelianGalois_iff j L hL).2 hc)⟩` and prove the remaining obligations. Set `` to `algThrough j _ h`. Use `infer_instance`.
-/
theorem hilbert_qb_aut : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ), IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ _ : NumberField (qb ι M), j.fieldRange ≤ qb ι M ∧
      (∀ s ∈ GalOf j.fieldRange, ∀ x ∈ qb ι M, s x ∈ qb ι M) ∧
      (∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ qb ι M, s (t x) = t (s x)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L], j.fieldRange ≤ L →
        (∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ L, s (t x) = t (s x)) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hab, hd, hmax⟩ := hilbert_qb H E j ι M hM
  refine ⟨hN, h, map_mem_of_normal j _ h ?_, (isAbelianGalois_iff j _ h).1 hab, hd,
    fun L _ hL hc => hmax L hL ((isAbelianGalois_iff j L hL).2 hc)⟩
  let := algThrough j _ h
  infer_instance

end GlobalTheory.HilbertInClosure

end

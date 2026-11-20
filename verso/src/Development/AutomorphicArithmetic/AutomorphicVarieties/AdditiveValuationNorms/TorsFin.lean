import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Formalism.GaloisCohomology.Statement
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj

open UpperTheory.V UpperTheory.V.PropA Formalism.GaloisCohomology

/- English proof (translation)
Introduce `l _ D _ _ hfin`. Establish `hl : l.Prime` using `Fact.out`. Take `⟨ι, hιinj, hιrange, -⟩` from `UpperTheory.V.Kum.zmodToQZ l 1`. Use `haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Use `haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.one_lt⟩`.

Use `set Q : Set (QZ l) := {q | (l : ℤ_[l]) • q = 0} with hQ`. Establish `hQfin : Q.Finite`. Establish `: Q = Set.range ι`. Use extensionality with `q`. Rewrite using `[hιrange q, pow_one]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Set.finite_range ι`. Establish `hι1 : ι 1 ≠ 0`. Introduce `h`.

Establish `h0 : ι 1 = ι 0` using `by rw [h, map_zero]`. Use `hιinj h0` as an intermediate fact. Conclude with `one_ne_zero this`. Establish `hlι : (l : ℤ_[l]) • ι 1 = 0`. Use `(hιrange (ι 1)).mp ⟨1, rfl⟩` as an intermediate fact.

Simplify using `using this`. Take `⟨s, hs⟩` from `hfin.fg_top`. Establish `hsep : ∀ t : D, (l : ℤ_[l]) • t = 0 → (∀ g ∈ s, g t = 0) → t = 0`. Introduce `t htl hg`. Establish `hall : LinearMap.applyₗ (R` using `ℤ_[l]) (M₂ := QZ l) t = 0 := LinearMap.ext_on hs (fun g hg' => by simpa using hg g hg')`.

Assume the negation of the conclusion as `ht`. Set `μt : ℤ_[l] →ₗ[ℤ_[l]] D` to `LinearMap.toSpanSingleton ℤ_[l] D t`. Set `ν : ℤ_[l] →ₗ[ℤ_[l]] QZ l` to `LinearMap.toSpanSingleton ℤ_[l] (QZ l) (ι 1)`. Establish `hker : LinearMap.ker μt ≤ LinearMap.ker ν`. Introduce `a ha`.

Establish `ha' : a • t = 0` using `by simpa [μt] using ha`. Use `show a • ι 1 = 0`. Distinguish the cases in `hu : IsUnit a`. Conclude with `absurd ((hu.smul_eq_zero).mp ha') ht`. Establish `hm : a ∈ IsLocalRing.maximalIdeal ℤ_[l]` using `(IsLocalRing.mem_maximalIdeal a).mpr hu`.

Rewrite `hm` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']`. Take `⟨b, rfl⟩` from `hm`. Rewrite using `[mul_smul, hlι, smul_zero]`. Set `g0 : LinearMap.range μt →ₗ[ℤ_[l]] QZ l` to `((LinearMap.ker μt).liftQ ν hker).comp (LinearMap.quotKerEquivRange μt).symm.toLinearMap`. Take `⟨y, hy⟩` from `(qzInj l).out (LinearMap.range μt).subtype Subtype.val_injective g0`.

Establish `hmem : μt 1 ∈ LinearMap.range μt` using `LinearMap.mem_range_self μt 1`. Establish `h3 : (LinearMap.quotKerEquivRange μt).symm ⟨μt 1, hmem⟩ = Submodule.Quotient.mk 1`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Establish `h1` using `hy ⟨μt 1, hmem⟩`.

Establish `h2 : g0 ⟨μt 1, hmem⟩ = ι 1`. Simplify using `only [g0, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]`. Rewrite using `[h3, Submodule.liftQ_apply]`. Simplify using `[ν]`. Rewrite `h1` using `[h2]`.

Establish `hyt : y t = 0`. Use `LinearMap.congr_fun hall y` as an intermediate fact. Simplify using `using this`. Establish `: μt 1 = t` using `by simp [μt]`. Simplify using `only [Submodule.coe_subtype, this] at h1`.

Conclude with `hι1 (h1 ▸ hyt)`. Set `f : D → (s → QZ l)` to `fun φ g => (g : D →ₗ[ℤ_[l]] QZ l) φ`. Establish `hpi : (Set.pi Set.univ (fun _ : s => Q)).Finite` using `Set.Finite.pi (fun _ => hQfin)`. Apply `Set.Finite.of_finite_image (f := f) _ _` to reduce the goal to its premises. Apply `hpi.subset` to reduce the goal to its premises.

Introduce and unpack `_ ⟨φ, hφ, rfl⟩ g _`. Use `show (l : ℤ_[l]) • (g : D →ₗ[ℤ_[l]] QZ l) φ = 0`. Rewrite using `[← map_smul, show (l : ℤ_[l]) • φ = 0 from hφ, map_zero]`. Introduce `φ hφ ψ hψ hfe`. Establish `hφ' : (l : ℤ_[l]) • φ = 0` using `hφ`.

Establish `hψ' : (l : ℤ_[l]) • ψ = 0` using `hψ`. Use `hsep (φ - ψ) (by rw [smul_sub, hφ', hψ', sub_zero]) (fun g hg => by` as an intermediate fact. Use `congr_fun hfe ⟨g, hg⟩` as an intermediate fact. Simplify using `only [f] at this`. Rewrite using `[map_sub, this, sub_self])`.

Conclude with `sub_eq_zero.mp this`.
-/
theorem UpperTheory.V.PropA.torsFin :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D], Module.Finite ℤ_[l] (D →ₗ[ℤ_[l]] QZ l) →
      {φ : D | (l : ℤ_[l]) • φ = 0}.Finite := by
  intro l _ D _ _ hfin
  have hl : l.Prime := Fact.out
  obtain ⟨ι, hιinj, hιrange, -⟩ := UpperTheory.V.Kum.zmodToQZ l 1
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.one_lt⟩
  set Q : Set (QZ l) := {q | (l : ℤ_[l]) • q = 0} with hQ
  have hQfin : Q.Finite := by
    have : Q = Set.range ι := by
      ext q
      rw [hιrange q, pow_one]
      rfl
    rw [this]
    exact Set.finite_range ι
  have hι1 : ι 1 ≠ 0 := by
    intro h
    have h0 : ι 1 = ι 0 := by rw [h, map_zero]
    have := hιinj h0
    exact one_ne_zero this
  have hlι : (l : ℤ_[l]) • ι 1 = 0 := by
    have := (hιrange (ι 1)).mp ⟨1, rfl⟩
    simpa using this
  obtain ⟨s, hs⟩ := hfin.fg_top
  have hsep : ∀ t : D, (l : ℤ_[l]) • t = 0 → (∀ g ∈ s, g t = 0) → t = 0 := by
    intro t htl hg
    have hall : LinearMap.applyₗ (R := ℤ_[l]) (M₂ := QZ l) t = 0 :=
      LinearMap.ext_on hs (fun g hg' => by simpa using hg g hg')
    by_contra ht
    let μt : ℤ_[l] →ₗ[ℤ_[l]] D := LinearMap.toSpanSingleton ℤ_[l] D t
    let ν : ℤ_[l] →ₗ[ℤ_[l]] QZ l := LinearMap.toSpanSingleton ℤ_[l] (QZ l) (ι 1)
    have hker : LinearMap.ker μt ≤ LinearMap.ker ν := by
      intro a ha
      have ha' : a • t = 0 := by simpa [μt] using ha
      show a • ι 1 = 0
      by_cases hu : IsUnit a
      · exact absurd ((hu.smul_eq_zero).mp ha') ht
      · have hm : a ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal a).mpr hu
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hm
        obtain ⟨b, rfl⟩ := hm
        rw [mul_smul, hlι, smul_zero]
    let g0 : LinearMap.range μt →ₗ[ℤ_[l]] QZ l :=
      ((LinearMap.ker μt).liftQ ν hker).comp (LinearMap.quotKerEquivRange μt).symm.toLinearMap
    obtain ⟨y, hy⟩ := (qzInj l).out (LinearMap.range μt).subtype Subtype.val_injective g0
    have hmem : μt 1 ∈ LinearMap.range μt := LinearMap.mem_range_self μt 1
    have h3 : (LinearMap.quotKerEquivRange μt).symm ⟨μt 1, hmem⟩ = Submodule.Quotient.mk 1 := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    have h1 := hy ⟨μt 1, hmem⟩
    have h2 : g0 ⟨μt 1, hmem⟩ = ι 1 := by
      simp only [g0, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      rw [h3, Submodule.liftQ_apply]
      simp [ν]
    rw [h2] at h1
    have hyt : y t = 0 := by
      have := LinearMap.congr_fun hall y
      simpa using this
    have : μt 1 = t := by simp [μt]
    simp only [Submodule.coe_subtype, this] at h1
    exact hι1 (h1 ▸ hyt)
  let f : D → (s → QZ l) := fun φ g => (g : D →ₗ[ℤ_[l]] QZ l) φ
  have hpi : (Set.pi Set.univ (fun _ : s => Q)).Finite := Set.Finite.pi (fun _ => hQfin)
  apply Set.Finite.of_finite_image (f := f) _ _
  · apply hpi.subset
    rintro _ ⟨φ, hφ, rfl⟩ g _
    show (l : ℤ_[l]) • (g : D →ₗ[ℤ_[l]] QZ l) φ = 0
    rw [← map_smul, show (l : ℤ_[l]) • φ = 0 from hφ, map_zero]
  · intro φ hφ ψ hψ hfe
    have hφ' : (l : ℤ_[l]) • φ = 0 := hφ
    have hψ' : (l : ℤ_[l]) • ψ = 0 := hψ
    have := hsep (φ - ψ) (by rw [smul_sub, hφ', hψ', sub_zero]) (fun g hg => by
      have := congr_fun hfe ⟨g, hg⟩
      simp only [f] at this
      rw [map_sub, this, sub_self])
    exact sub_eq_zero.mp this

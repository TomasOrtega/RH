import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLocLaurent
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByForm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialLocalizedLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial HomLocLaurent

noncomputable section

universe u

set_option linter.style.haveILetI false

section Mult

/- English proof (translation)
The claim follows from `Module.length_eq_of_surjective h`.
-/
theorem length_quotient_of_surjective {S C : Type*} [CommRing S] [CommRing C] [Algebra S C]
    (h : Function.Surjective (algebraMap S C)) (I : Ideal C) :
    Module.length S (C ⧸ I) = Module.length C (C ⧸ I) :=
  Module.length_eq_of_surjective h

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
  {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]

/- English proof (translation)
Use `letI := (algQC hPW).toAlgebra`. Use `haveI := wbar_isPrime hPW`. Use `haveI := locC_isLocalization hPW`. Use `set J := P ⊔ Ideal.span {x}`. Use `set I : Ideal (locC hPW) := Ideal.span {algQC hPW (Ideal.Quotient.mk P x)}`.

Use `set θ : MRing ι R →+* locC hPW := (algQC hPW).comp (Ideal.Quotient.mk P) with hθ`. Establish `hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0` using `fun hg => fr_ne_zero fun h => hg (hPW h)`. Establish `hunit : ∀ {s : MRing ι R}, s ∉ W → IsUnit (θ s)` using `fun hs => (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr fun h => hs ((Ideal.mem_quotient_iff_mem hPW).mp h)`. Take `⟨θW, hθWdef⟩ : ∃ φ : Localization.AtPrime W →+* locC hPW, φ = IsLocalization.lift (M` from `W.primeCompl) (g := θ) fun s => hunit s.2 := ⟨_, rfl⟩`. Establish `hθW : ∀ f, θW (algebraMap (MRing ι R) (Localization.AtPrime W) f) = θ f` using `fun f => by`.

Rewrite using `[hθWdef]`. Conclude with `IsLocalization.lift_eq _ _`. Establish `hval : ∀ (a s : MRing ι R) (hs : s ∈ W.primeCompl), (θW (IsLocalization.mk' (Localization.AtPrime W) a ⟨s, hs⟩) : FractionRing (MRing ι R ⧸ P)) * fr P s = fr P a`. Introduce `a s hs`. Use `congrArg θW (IsLocalization.mk'_spec (Localization.AtPrime W) a ⟨s, hs⟩)` as an intermediate fact.

Rewrite `this` using `[RingHom.map_mul, hθW, hθW]`. Conclude with `congrArg Subtype.val this`. Establish `hsurj : Function.Surjective θW`. Introduce and unpack `⟨c, a', s', hs', rfl⟩`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a'`.

Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective s'`. Establish `hsW : s ∉ W` using `fun h => hs' (Ideal.mem_map_of_mem _ h)`. Use `⟨IsLocalization.mk' (Localization.AtPrime W) a (⟨s, hsW⟩ : W.primeCompl), Subtype.ext ?_⟩` and prove the remaining obligations. Establish `h` using `hval a s hsW`. Express the relevant statement in the definitionally equal form `_ = fr P a * (fr P s)⁻¹`.

Rewrite using `[← h, mul_assoc, mul_inv_cancel₀ (hne hsW), mul_one]`. Use `letI : Algebra (Localization.AtPrime W) (locC hPW) := θW.toAlgebra`. Set `f : Localization.AtPrime W →ₐ[Localization.AtPrime W] (locC hPW ⧸ I)` to `Algebra.ofId (Localization.AtPrime W) (locC hPW ⧸ I)`. Establish `hf : ∀ y, f y = Ideal.Quotient.mk I (θW y)` using `fun y => rfl`. Establish `hfs : Function.Surjective f` using `fun q => by`.

Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Take `⟨y, rfl⟩` from `hsurj c`. Conclude with `⟨y, hf y⟩`. Establish `hker : RingHom.ker f = J.map (algebraMap (MRing ι R) (Localization.AtPrime W))`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `y hy`. Rewrite `hy` using `[RingHom.mem_ker, hf, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Take `⟨⟨c, b', t', ht', hc⟩, hcy⟩` from `hy`. Take `⟨⟨a, ⟨s, hs⟩⟩, rfl⟩` from `IsLocalization.mk'_surjective W.primeCompl y`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b'`.

Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective t'`. Establish `htW : t ∉ W` using `fun h => ht' (Ideal.mem_map_of_mem _ h)`. Establish `h1` using `hval a s hs`. Rewrite `h1` using `[← hcy]`. Express the relevant statement in the definitionally equal form `c * fr P x * fr P s = fr P a at h1`.

Rewrite `h1` using `[hc]`. Express the relevant statement in the definitionally equal form `fr P b * (fr P t)⁻¹ * fr P x * fr P s = fr P a at h1`. Establish `hat : a * t - b * x * s ∈ P`. Establish `h2 : fr P a * fr P t = fr P b * fr P x * fr P s`. Rewrite using `[← h1]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← fr_eq_zero_iff, map_sub, map_mul, map_mul, map_mul, h2, sub_self]`. Establish `hatJ : a * t ∈ J`. Establish `: a * t = (a * t - b * x * s) + (b * s) * x` using `by ring`. Rewrite using `[this]`.

Conclude with `J.add_mem (Ideal.mem_sup_left hat) (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))`. Establish `hst : s * t ∈ W.primeCompl` using `fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs htW`. Establish `heq : IsLocalization.mk' (Localization.AtPrime W) a (⟨s, hs⟩ : W.primeCompl) * algebraMap (MRing ι R) (Localization.AtPrime W) (s * t) = algebraMap (MRing ι R) (Localization.AtPrime W) (a * t)`. Rewrite using `[map_mul, ← mul_assoc, IsLocalization.mk'_spec, map_mul]`. Establish `hu : IsUnit (algebraMap (MRing ι R) (Localization.AtPrime W) (s * t))` using `IsLocalization.map_units (Localization.AtPrime W) (⟨s * t, hst⟩ : W.primeCompl)`.

Rewrite using `[← Ideal.mul_unit_mem_iff_mem _ hu, heq]`. Conclude with `Ideal.mem_map_of_mem _ hatJ`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `j hj`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hf, hθW, Ideal.Quotient.eq_zero_iff_mem]`.

Establish `hJ : J ≤ I.comap θ`. Use `sup_le (fun p hp => ?_) ?_` and prove the remaining obligations. Establish `h0 : Ideal.Quotient.mk P p = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hp`. Rewrite using `[Ideal.mem_comap, hθ, RingHom.comp_apply, h0, RingHom.map_zero]`. Conclude with `zero_mem _`.

Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.subset_span rfl`. Conclude with `Ideal.mem_comap.mp (hJ hj)`. Establish `hlen` using `(Ideal.quotientKerAlgEquivOfSurjective hfs).toLinearEquiv.length_eq`. Rewrite using `[multAt, length_localizedModule_quotient_eq, ← (Submodule.quotEquivOfEq _ _ hker).length_eq, hlen]`.

Conclude with `length_quotient_of_surjective hsurj I`.
-/
theorem multAt_eq_length_locC (hPW : P ≤ W) (x : MRing ι R) :
    multAt (P ⊔ Ideal.span {x}) W =
      Module.length (locC hPW) (locC hPW ⧸ Ideal.span {algQC hPW (Ideal.Quotient.mk P x)}) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  set J := P ⊔ Ideal.span {x}
  set I : Ideal (locC hPW) := Ideal.span {algQC hPW (Ideal.Quotient.mk P x)}
  set θ : MRing ι R →+* locC hPW := (algQC hPW).comp (Ideal.Quotient.mk P) with hθ
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero fun h => hg (hPW h)
  have hunit : ∀ {s : MRing ι R}, s ∉ W → IsUnit (θ s) := fun hs =>
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hs ((Ideal.mem_quotient_iff_mem hPW).mp h)
  obtain ⟨θW, hθWdef⟩ : ∃ φ : Localization.AtPrime W →+* locC hPW,
      φ = IsLocalization.lift (M := W.primeCompl) (g := θ) fun s => hunit s.2 := ⟨_, rfl⟩
  have hθW : ∀ f, θW (algebraMap (MRing ι R) (Localization.AtPrime W) f) = θ f := fun f => by
    rw [hθWdef]
    exact IsLocalization.lift_eq _ _

  have hval : ∀ (a s : MRing ι R) (hs : s ∈ W.primeCompl),
      (θW (IsLocalization.mk' (Localization.AtPrime W) a ⟨s, hs⟩) : FractionRing (MRing ι R ⧸ P)) *
        fr P s = fr P a := by
    intro a s hs
    have := congrArg θW (IsLocalization.mk'_spec (Localization.AtPrime W) a ⟨s, hs⟩)
    rw [RingHom.map_mul, hθW, hθW] at this
    exact congrArg Subtype.val this
  have hsurj : Function.Surjective θW := by
    rintro ⟨c, a', s', hs', rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
    have hsW : s ∉ W := fun h => hs' (Ideal.mem_map_of_mem _ h)
    refine ⟨IsLocalization.mk' (Localization.AtPrime W) a (⟨s, hsW⟩ : W.primeCompl), Subtype.ext ?_⟩
    have h := hval a s hsW
    change _ = fr P a * (fr P s)⁻¹
    rw [← h, mul_assoc, mul_inv_cancel₀ (hne hsW), mul_one]
  letI : Algebra (Localization.AtPrime W) (locC hPW) := θW.toAlgebra
  let f : Localization.AtPrime W →ₐ[Localization.AtPrime W] (locC hPW ⧸ I) :=
    Algebra.ofId (Localization.AtPrime W) (locC hPW ⧸ I)
  have hf : ∀ y, f y = Ideal.Quotient.mk I (θW y) := fun y => rfl
  have hfs : Function.Surjective f := fun q => by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := hsurj c
    exact ⟨y, hf y⟩
  have hker : RingHom.ker f = J.map (algebraMap (MRing ι R) (Localization.AtPrime W)) := by
    apply le_antisymm
    · intro y hy
      rw [RingHom.mem_ker, hf, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hy
      obtain ⟨⟨c, b', t', ht', hc⟩, hcy⟩ := hy
      obtain ⟨⟨a, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl y
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t'
      have htW : t ∉ W := fun h => ht' (Ideal.mem_map_of_mem _ h)
      have h1 := hval a s hs
      rw [← hcy] at h1
      change c * fr P x * fr P s = fr P a at h1
      rw [hc] at h1
      change fr P b * (fr P t)⁻¹ * fr P x * fr P s = fr P a at h1
      have hat : a * t - b * x * s ∈ P := by
        have h2 : fr P a * fr P t = fr P b * fr P x * fr P s := by
          rw [← h1]
          calc _ = fr P b * fr P x * fr P s * ((fr P t)⁻¹ * fr P t) := by ring
            _ = _ := by rw [inv_mul_cancel₀ (hne htW), mul_one]
        rw [← fr_eq_zero_iff, map_sub, map_mul, map_mul, map_mul, h2, sub_self]
      have hatJ : a * t ∈ J := by
        have : a * t = (a * t - b * x * s) + (b * s) * x := by ring
        rw [this]
        exact J.add_mem (Ideal.mem_sup_left hat)
          (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
      have hst : s * t ∈ W.primeCompl := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs htW
      have heq : IsLocalization.mk' (Localization.AtPrime W) a (⟨s, hs⟩ : W.primeCompl) *
          algebraMap (MRing ι R) (Localization.AtPrime W) (s * t) =
            algebraMap (MRing ι R) (Localization.AtPrime W) (a * t) := by
        rw [map_mul, ← mul_assoc, IsLocalization.mk'_spec, map_mul]
      have hu : IsUnit (algebraMap (MRing ι R) (Localization.AtPrime W) (s * t)) :=
        IsLocalization.map_units (Localization.AtPrime W) (⟨s * t, hst⟩ : W.primeCompl)
      rw [← Ideal.mul_unit_mem_iff_mem _ hu, heq]
      exact Ideal.mem_map_of_mem _ hatJ
    · rw [Ideal.map_le_iff_le_comap]
      intro j hj
      rw [Ideal.mem_comap, RingHom.mem_ker, hf, hθW, Ideal.Quotient.eq_zero_iff_mem]
      have hJ : J ≤ I.comap θ := by
        refine sup_le (fun p hp => ?_) ?_
        · have h0 : Ideal.Quotient.mk P p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
          rw [Ideal.mem_comap, hθ, RingHom.comp_apply, h0, RingHom.map_zero]
          exact zero_mem _
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          exact Ideal.subset_span rfl
      exact Ideal.mem_comap.mp (hJ hj)
  have hlen := (Ideal.quotientKerAlgEquivOfSurjective hfs).toLinearEquiv.length_eq
  rw [multAt, length_localizedModule_quotient_eq, ← (Submodule.quotEquivOfEq _ _ hker).length_eq, hlen]
  exact length_quotient_of_surjective hsurj I

end Mult

/- English proof (translation)
Introduce `O _ _ _ K _ _ ι _ P hP c x hx hxP W hW hWrel g hg hgW hz`. Use `haveI := hP.isPrime`. Use `haveI : W.IsPrime := hW.1.1`. Establish `hPW : P ≤ W` using `le_trans le_sup_left hW.1.2`. Establish `hWh : IsMultiHomogIdeal W` using `MinimalPrimeMultiHomog.proof O K ι _ W (isMultiHomogIdeal_sup_span_of_form hP.multiHomog hx) hW`.

Use `haveI : IsLocalRing (homLocRing P W) := (h O K ι P hP c x hx hxP W hW hWrel).1`. Use `choose T hT using hWrel`. Rewrite using `[← length_quotient_incAC T hPW hT hP.multiHomog hWh, multAt_eq_length_locC hPW x]`. Use `letI := (algQC hPW).toAlgebra`. Use `haveI := wbar_isPrime hPW`.

Use `haveI := locC_isLocalization hPW`. Establish `hgu : IsUnit (algQC hPW (Ideal.Quotient.mk P g))` using `(IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr fun h => hgW ((Ideal.mem_quotient_iff_mem hPW).mp h)`. Establish `hxz : algQC hPW (Ideal.Quotient.mk P x) = incAC hPW ⟨_, hz⟩ * algQC hPW (Ideal.Quotient.mk P g)`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `fr P x = fr P x / fr P g * fr P g`.

Rewrite using `[div_mul_cancel₀ _ (fr_ne_zero fun h => hgW (hPW h))]`. Rewrite using `[hxz, Ideal.span_singleton_mul_right_unit hgu]`.
-/
theorem DivCycleHomLoc.proof (h : HomLocRingLocal.Statement.{u}) : DivCycleHomLoc.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP c x hx hxP W hW hWrel g hg hgW hz
  haveI := hP.isPrime
  haveI : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_trans le_sup_left hW.1.2
  have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof O K ι _ W
    (isMultiHomogIdeal_sup_span_of_form hP.multiHomog hx) hW
  haveI : IsLocalRing (homLocRing P W) := (h O K ι P hP c x hx hxP W hW hWrel).1
  choose T hT using hWrel
  rw [← length_quotient_incAC T hPW hT hP.multiHomog hWh, multAt_eq_length_locC hPW x]
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  have hgu : IsUnit (algQC hPW (Ideal.Quotient.mk P g)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hgW ((Ideal.mem_quotient_iff_mem hPW).mp h)
  have hxz : algQC hPW (Ideal.Quotient.mk P x) =
      incAC hPW ⟨_, hz⟩ * algQC hPW (Ideal.Quotient.mk P g) := by
    apply Subtype.ext
    change fr P x = fr P x / fr P g * fr P g
    rw [div_mul_cancel₀ _ (fr_ne_zero fun h => hgW (hPW h))]
  rw [hxz, Ideal.span_singleton_mul_right_unit hgu]

end

end GroundTheory.Heights₂.Heights.NumbersDVR

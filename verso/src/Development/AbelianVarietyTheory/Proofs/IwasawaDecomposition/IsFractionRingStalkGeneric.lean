import Mathlib
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `X x ξ e hd hgen`. Establish `hnil : ∀ s : X.presheaf.stalk ξ, X.residue ξ s = 0 → IsNilpotent s`. Introduce `s hs`. Establish `hs' : s ∈ IsLocalRing.maximalIdeal _` using `(IsLocalRing.residue_eq_zero_iff s).mp hs`. Rewrite using `[← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]`.

Introduce `J hJ`. Set `q : PrimeSpectrum (X.presheaf.stalk ξ)` to `⟨J, hJ⟩`. Establish `h1 : X.fromSpecStalk ξ q ⤳ ξ`. Establish `: X.fromSpecStalk ξ q ∈ Set.range (X.fromSpecStalk ξ)` using `⟨q, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis.

Establish `h2 : q = IsLocalRing.closedPoint _` using `(X.fromSpecStalk ξ).isEmbedding.injective ((hgen _ h1).trans Scheme.fromSpecStalk_closedPoint.symm)`. Establish `h3 : J = IsLocalRing.maximalIdeal _` using `congrArg PrimeSpectrum.asIdeal h2`. Rewrite using `[h3]`. Conclude with `hs'`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`.

Establish `hξU : ξ ∈ U` using `e.mem_open U.2 hxU`. Use `letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)`. Use `letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨ξ, hξU⟩ : U)`. Use `haveI hLx := hU.isLocalization_stalk ⟨x, hxU⟩`. Use `haveI hLξ := hU.isLocalization_stalk ⟨ξ, hξU⟩`.

Establish `hsp : ∀ a : Γ(X, U), X.presheaf.stalkSpecializes e (X.presheaf.germ U x hxU a) = X.presheaf.germ U ξ hξU a` using `fun a => X.presheaf.germ_stalkSpecializes_apply hxU e a`. Establish `hunitξ : ∀ b ∈ (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl, IsUnit (X.presheaf.germ U ξ hξU b)` using `fun b hb => IsLocalization.map_units (X.presheaf.stalk (⟨ξ, hξU⟩ : U)) (⟨b, hb⟩ : (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl)`. Establish `hne : ∀ b ∈ (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl, X.presheaf.germ U x hxU b ≠ 0`. Introduce `b hb h0`. Establish `h'` using `congrArg (X.presheaf.stalkSpecializes e) h0`.

Rewrite `h'` using `[hsp, map_zero]`. Conclude with `(hunitξ b hb).ne_zero h'`. Establish `hinj : ∀ r : X.presheaf.stalk x, X.residue ξ (X.presheaf.stalkSpecializes e r) = 0 → r = 0`. Introduce `r hr`. Take `⟨⟨a, d⟩, hrad⟩` from `IsLocalization.surj (S := X.presheaf.stalk (⟨x, hxU⟩ : U)) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl r`.

Express the relevant statement in the definitionally equal form `r * X.presheaf.germ U x hxU d = X.presheaf.germ U x hxU a at hrad`. Establish `hres : X.residue ξ (X.presheaf.germ U ξ hξU a) = 0`. Rewrite using `[← hsp, ← hrad, map_mul, map_mul, hr, zero_mul]`. Take `⟨n, hn⟩` from `hnil _ hres`. Establish `hn' : algebraMap Γ(X, U) (X.presheaf.stalk (⟨ξ, hξU⟩ : U)) (a ^ n) = 0`.

Rewrite using `[map_pow]`. Conclude with `hn`. Take `⟨c, hc⟩` from `(IsLocalization.map_eq_zero_iff (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl _ _).mp hn'`. Establish `hc' : X.presheaf.germ U x hxU c * (X.presheaf.germ U x hxU a) ^ n = 0`. Rewrite using `[← map_pow, ← map_mul, hc, map_zero]`.

Establish `ha0 : X.presheaf.germ U x hxU a = 0` using `IsNilpotent.eq_zero ⟨n, (mul_eq_zero.mp hc').resolve_left (hne c c.2)⟩`. Rewrite `hrad` using `[ha0]`. Conclude with `(IsUnit.mul_left_eq_zero (IsLocalization.map_units (X.presheaf.stalk (⟨x, hxU⟩ : U)) d)).mp hrad`. Use `letI alg := RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom`. Establish `halg : ∀ r, algebraMap (X.presheaf.stalk x) (X.residueField ξ) r = X.residue ξ (X.presheaf.stalkSpecializes e r)` using `fun _ => rfl`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Rewrite using `[isUnit_iff_ne_zero, halg]`. Conclude with `fun h => nonZeroDivisors.ne_zero y.2 (hinj _ h)`. Introduce `z`.

Take `⟨s, rfl⟩` from `X.residue_surjective ξ z`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (S := X.presheaf.stalk (⟨ξ, hξU⟩ : U)) (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl s`. Express the relevant statement in the definitionally equal form `s * X.presheaf.germ U ξ hξU b = X.presheaf.germ U ξ hξU a at hab`. Use `⟨⟨X.presheaf.germ U x hxU a, ⟨X.presheaf.germ U x hxU b, mem_nonZeroDivisors_of_ne_zero (hne b b.2)⟩⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `X.residue ξ s * algebraMap _ _ (X.presheaf.germ U x hxU b) = algebraMap _ _ (X.presheaf.germ U x hxU a)`.

Rewrite using `[halg, halg, hsp, hsp, ← map_mul, hab]`. Introduce `r t h`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `h0` using `hinj (r - t) (by rw [map_sub, map_sub, ← halg, ← halg, h, sub_self])`. Rewrite using `[sub_eq_zero.mp h0]`.
-/
theorem residueField_isFractionRing_of_generic : ∀ (X : Scheme.{0}) (x ξ : X) (e : ξ ⤳ x),
    IsDomain (X.presheaf.stalk x) → (∀ y, y ⤳ ξ → y = ξ) →
    @IsFractionRing (X.presheaf.stalk x) _ (X.residueField ξ) _
      (RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom) := by
  intro X x ξ e hd hgen

  have hnil : ∀ s : X.presheaf.stalk ξ, X.residue ξ s = 0 → IsNilpotent s := by
    intro s hs
    have hs' : s ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.residue_eq_zero_iff s).mp hs
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro J hJ
    let q : PrimeSpectrum (X.presheaf.stalk ξ) := ⟨J, hJ⟩
    have h1 : X.fromSpecStalk ξ q ⤳ ξ := by
      have : X.fromSpecStalk ξ q ∈ Set.range (X.fromSpecStalk ξ) := ⟨q, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h2 : q = IsLocalRing.closedPoint _ :=
      (X.fromSpecStalk ξ).isEmbedding.injective
        ((hgen _ h1).trans Scheme.fromSpecStalk_closedPoint.symm)
    have h3 : J = IsLocalRing.maximalIdeal _ := congrArg PrimeSpectrum.asIdeal h2
    rw [h3]; exact hs'
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hξU : ξ ∈ U := e.mem_open U.2 hxU
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨ξ, hξU⟩ : U)
  haveI hLx := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI hLξ := hU.isLocalization_stalk ⟨ξ, hξU⟩
  have hsp : ∀ a : Γ(X, U), X.presheaf.stalkSpecializes e (X.presheaf.germ U x hxU a) =
      X.presheaf.germ U ξ hξU a :=
    fun a => X.presheaf.germ_stalkSpecializes_apply hxU e a
  have hunitξ : ∀ b ∈ (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl,
      IsUnit (X.presheaf.germ U ξ hξU b) :=
    fun b hb => IsLocalization.map_units (X.presheaf.stalk (⟨ξ, hξU⟩ : U))
      (⟨b, hb⟩ : (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl)
  have hne : ∀ b ∈ (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl,
      X.presheaf.germ U x hxU b ≠ 0 := by
    intro b hb h0
    have h' := congrArg (X.presheaf.stalkSpecializes e) h0
    rw [hsp, map_zero] at h'
    exact (hunitξ b hb).ne_zero h'
  have hinj : ∀ r : X.presheaf.stalk x,
      X.residue ξ (X.presheaf.stalkSpecializes e r) = 0 → r = 0 := by
    intro r hr
    obtain ⟨⟨a, d⟩, hrad⟩ := IsLocalization.surj (S := X.presheaf.stalk (⟨x, hxU⟩ : U))
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl r
    change r * X.presheaf.germ U x hxU d = X.presheaf.germ U x hxU a at hrad
    have hres : X.residue ξ (X.presheaf.germ U ξ hξU a) = 0 := by
      rw [← hsp, ← hrad, map_mul, map_mul, hr, zero_mul]
    obtain ⟨n, hn⟩ := hnil _ hres
    have hn' : algebraMap Γ(X, U) (X.presheaf.stalk (⟨ξ, hξU⟩ : U)) (a ^ n) = 0 := by
      rw [map_pow]; exact hn
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff
      (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl _ _).mp hn'
    have hc' : X.presheaf.germ U x hxU c * (X.presheaf.germ U x hxU a) ^ n = 0 := by
      rw [← map_pow, ← map_mul, hc, map_zero]
    have ha0 : X.presheaf.germ U x hxU a = 0 :=
      IsNilpotent.eq_zero ⟨n, (mul_eq_zero.mp hc').resolve_left (hne c c.2)⟩
    rw [ha0] at hrad
    exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units
      (X.presheaf.stalk (⟨x, hxU⟩ : U)) d)).mp hrad
  letI alg := RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom
  have halg : ∀ r, algebraMap (X.presheaf.stalk x) (X.residueField ξ) r =
      X.residue ξ (X.presheaf.stalkSpecializes e r) := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [isUnit_iff_ne_zero, halg]
    exact fun h => nonZeroDivisors.ne_zero y.2 (hinj _ h)
  · intro z
    obtain ⟨s, rfl⟩ := X.residue_surjective ξ z
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (S := X.presheaf.stalk (⟨ξ, hξU⟩ : U))
      (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl s
    change s * X.presheaf.germ U ξ hξU b = X.presheaf.germ U ξ hξU a at hab
    refine ⟨⟨X.presheaf.germ U x hxU a,
      ⟨X.presheaf.germ U x hxU b, mem_nonZeroDivisors_of_ne_zero (hne b b.2)⟩⟩, ?_⟩
    change X.residue ξ s * algebraMap _ _ (X.presheaf.germ U x hxU b) =
      algebraMap _ _ (X.presheaf.germ U x hxU a)
    rw [halg, halg, hsp, hsp, ← map_mul, hab]
  · intro r t h
    refine ⟨1, ?_⟩
    have h0 := hinj (r - t) (by rw [map_sub, map_sub, ← halg, ← halg, h, sub_self])
    rw [sub_eq_zero.mp h0]

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

/- English proof (translation)
Use `haveI : Module.Flat B M := Module.Flat.of_projective`. Set `S` to `P.asIdeal.primeCompl`. Set `f` to `LocalizedModule.mkLinearMap S M`. Use `haveI : Module.Free (Localization.AtPrime P.asIdeal) (LocalizedModule S M) := Module.mem_freeLocus.mp (by simp only [Module.freeLocus_eq_univ, Set.mem_univ])`. Use `haveI : Module.Finite (Localization.AtPrime P.asIdeal) (LocalizedModule S M) := Module.Finite.of_isLocalizedModule S f`.

Set `e` to `Module.finBasisOfFinrankEq (Localization.AtPrime P.asIdeal) (LocalizedModule S M) h`. Take `⟨⟨m, s0⟩, hm⟩` from `IsLocalizedModule.surj S f (e 0)`. Use `⟨m, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : f x = (e.repr (f x) 0) • e 0`. Establish `hsum` using `e.sum_repr (f x)`.

Rewrite `hsum` using `[Fin.sum_univ_one]`. Conclude with `hsum.symm`. Take `⟨⟨a, u⟩, hu⟩` from `IsLocalization.surj S (e.repr (f x) 0)`. Establish `key : f (((u : B) * (s0 : B)) • x) = f (a • m)`. Rewrite using `[map_smul, map_smul, hx, ← hm, Submonoid.smul_def, ← algebraMap_smul (Localization.AtPrime P.asIdeal) ((u : B) * (s0 : B)), ← algebraMap_smul (Localization.AtPrime P.asIdeal) a, ← algebraMap_smul (Localization.AtPrime P.asIdeal) (s0 : B)]`.

Simplify using `only [smul_smul]`. Use `congr 1`. Rewrite using `[map_mul, ← hu]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨v, hv⟩` from `(IsLocalizedModule.eq_iff_exists S f).mp key`.

Use `⟨(v : B) * ((u : B) * (s0 : B)), (v * (u * s0)).2, (v : B) * a, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `(rw [mul_smul (v : B) ((u : B) * (s0 : B)) x, mul_smul (v : B) a m]; exact hv)`. Consider the case `simpa only [Submonoid.smul_def, mul_smul] using hv`.
-/
theorem exists_generator_of_rankAtStalk_eq_one {B M : Type*} [CommRing B] [AddCommGroup M]
    [Module B M] [Module.Finite B M] [Module.Projective B M] (P : PrimeSpectrum B)
    (h : Module.rankAtStalk M P = 1) :
    ∃ m : M, ∀ x : M, ∃ s : B, s ∉ P.asIdeal ∧ ∃ b : B, s • x = b • m := by
  haveI : Module.Flat B M := Module.Flat.of_projective
  let S := P.asIdeal.primeCompl
  let f := LocalizedModule.mkLinearMap S M
  haveI : Module.Free (Localization.AtPrime P.asIdeal) (LocalizedModule S M) :=
    Module.mem_freeLocus.mp (by simp only [Module.freeLocus_eq_univ, Set.mem_univ])
  haveI : Module.Finite (Localization.AtPrime P.asIdeal) (LocalizedModule S M) :=
    Module.Finite.of_isLocalizedModule S f
  let e := Module.finBasisOfFinrankEq (Localization.AtPrime P.asIdeal) (LocalizedModule S M) h
  obtain ⟨⟨m, s0⟩, hm⟩ := IsLocalizedModule.surj S f (e 0)
  refine ⟨m, fun x => ?_⟩
  have hx : f x = (e.repr (f x) 0) • e 0 := by
    have hsum := e.sum_repr (f x)
    rw [Fin.sum_univ_one] at hsum
    exact hsum.symm
  obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj S (e.repr (f x) 0)
  have key : f (((u : B) * (s0 : B)) • x) = f (a • m) := by
    rw [map_smul, map_smul, hx, ← hm, Submonoid.smul_def,
      ← algebraMap_smul (Localization.AtPrime P.asIdeal) ((u : B) * (s0 : B)),
      ← algebraMap_smul (Localization.AtPrime P.asIdeal) a,
      ← algebraMap_smul (Localization.AtPrime P.asIdeal) (s0 : B)]
    simp only [smul_smul]
    congr 1
    rw [map_mul, ← hu]
    ring
  obtain ⟨v, hv⟩ := (IsLocalizedModule.eq_iff_exists S f).mp key
  refine ⟨(v : B) * ((u : B) * (s0 : B)), (v * (u * s0)).2, (v : B) * a, ?_⟩
  first
    | (rw [mul_smul (v : B) ((u : B) * (s0 : B)) x, mul_smul (v : B) a m]; exact hv)
    | simpa only [Submonoid.smul_def, mul_smul] using hv

/- English proof (translation)
Use `set p := P.asIdeal.comap (Ideal.Quotient.mk I) with hp_def`. Use `haveI hpP : p.IsPrime := Ideal.comap_isPrime _ _`. Establish `hIp : I ≤ p` using `fun x hx => by`. Rewrite using `[hp_def, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]`. Conclude with `P.asIdeal.zero_mem`.

Take `⟨m0, hm0⟩` from `GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.exists_generator_of_rankAtStalk_eq_one P hP`. Take `⟨⟨f0, hf0I⟩, hf0⟩` from `Ideal.toCotangent_surjective I m0`. Establish `hsm : ∀ (r : A) (y : I.Cotangent), Ideal.Quotient.mk I r • y = r • y`. Introduce `r y`. Use `first`.

Consider the case `(rw [← Ideal.Quotient.algebraMap_eq]; exact algebraMap_smul (A ⧸ I) r y)`. Consider the case `rfl`. Consider the case `(obtain ⟨y', rfl⟩ := Ideal.toCotangent_surjective I y; rfl)`. Establish `step : ∀ x ∈ I, ∃ s ∉ p, ∃ b : A, s * x - b * f0 ∈ I ^ 2`. Introduce `x hx`.

Take `⟨sq, hsq, bq, hsb⟩` from `hm0 (I.toCotangent ⟨x, hx⟩)`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective sq`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective bq`. Use `⟨s, hsq, b, ?_⟩` and prove the remaining obligations. Rewrite `hsb` using `[← hf0, hsm, hsm, ← map_smul I.toCotangent, ← map_smul I.toCotangent, Ideal.toCotangent_eq]`.

Simplify `hsb` using `only [Submodule.coe_smul, smul_eq_mul]`. Set `φ` to `algebraMap A (Localization.AtPrime p)`. Use `set K : Ideal A := Ideal.span {f0} with hK`. Establish `hIfg : I.FG` using `IsNoetherian.noetherian I`. Establish `hle : I.map φ ≤ K.map φ ⊔ IsLocalRing.maximalIdeal (Localization.AtPrime p) • I.map φ`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap]`. Take `⟨s, hs, b, hsb⟩` from `step x hx`. Establish `hunit : IsUnit (φ s)` using `IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)`.

Rewrite using `[← Ideal.unit_mul_mem_iff_mem _ hunit, ← map_mul]`. Establish `hdecomp : s * x = b * f0 + (s * x - b * f0)` using `by ring`. Rewrite using `[hdecomp, map_add]`. Use `Submodule.add_mem_sup ?_ ?_` and prove the remaining obligations. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f0))`.

Establish `h2 : φ (s * x - b * f0) ∈ (I ^ 2).map φ` using `Ideal.mem_map_of_mem _ hsb`. Rewrite `h2` using `[Ideal.map_pow, pow_two]`. Rewrite using `[Ideal.smul_eq_mul]`. Conclude with `Ideal.mul_mono_left (le_trans (Ideal.map_mono hIp) (Localization.AtPrime.map_eq_maximalIdeal).le) h2`. Establish `hnak : I.map φ ≤ K.map φ` using `Submodule.le_of_le_smul_of_le_jacobson_bot (hIfg.map φ) (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle`.

Establish `hloc : ∀ x ∈ I, ∃ s ∉ p, s * x ∈ K`. Introduce `x hx`. Take `⟨s, hs, hsx⟩` from `(IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p) K x).mp (hnak (Ideal.mem_map_of_mem φ hx))`. Conclude with `⟨s, hs, hsx⟩`. Establish `hunif : ∀ N : Submodule A A, N.FG → N ≤ I → ∃ s ∉ p, ∀ y ∈ N, s * y ∈ K`.

Introduce `N hN`. Use `Submodule.fg_induction (motive := fun N _ => N ≤ I → ∃ s ∉ p, ∀ y ∈ N, s * y ∈ K) ?_ ?_ N hN` and prove the remaining obligations. Introduce `x hxI`. Take `⟨s, hs, hsx⟩` from `hloc x (hxI (Submodule.mem_span_singleton_self x))`. Use `⟨s, hs, fun y hy => ?_⟩` and prove the remaining obligations.

Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hy`. Rewrite using `[smul_eq_mul, mul_left_comm]`. Conclude with `K.mul_mem_left c hsx`. Introduce `N₁ N₂ _ _ ih₁ ih₂ h₁₂`. Take `⟨s₁, hs₁, h₁⟩` from `ih₁ (le_trans le_sup_left h₁₂)`.

Take `⟨s₂, hs₂, h₂⟩` from `ih₂ (le_trans le_sup_right h₁₂)`. Use `⟨s₁ * s₂, fun hmem => (hpP.mem_or_mem hmem).elim hs₁ hs₂, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨y₁, hy₁, y₂, hy₂, rfl⟩` from `Submodule.mem_sup.mp hy`. Establish `hsplit : s₁ * s₂ * (y₁ + y₂) = s₂ * (s₁ * y₁) + s₁ * (s₂ * y₂)` using `by ring`. Rewrite using `[hsplit]`.

Conclude with `K.add_mem (K.mul_mem_left _ (h₁ y₁ hy₁)) (K.mul_mem_left _ (h₂ y₂ hy₂))`. Take `⟨t, ht, htI⟩` from `hunif I hIfg le_rfl`. Establish `hf0ne : f0 ≠ 0`. Introduce `h0`. Establish `hbot : ∀ y : I, y = 0`.

Introduce `y`. Apply `Subtype.ext` to reduce the goal to its premises. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp (htI y y.2)`. Rewrite `ha` using `[h0, mul_zero]`. Break down `mul_eq_zero.mp ha.symm with h | h` into its components or cases.

Rewrite `ht` using `[h]`. Conclude with `absurd p.zero_mem ht`. Conclude with `h`. Use `haveI : Subsingleton I.Cotangent := ⟨fun a b => by`. Take `⟨a', rfl⟩` from `Ideal.toCotangent_surjective I a`.

Take `⟨b', rfl⟩` from `Ideal.toCotangent_surjective I b`. Rewrite using `[hbot a', hbot b']⟩`. Establish `h0rank` using `Module.rankAtStalk_eq_zero_of_subsingleton (R := A ⧸ I) (M := I.Cotangent)`. Rewrite `hP` using `[h0rank]`. Use `first`.

Consider the case `exact zero_ne_one hP`. Consider the case `simp at hP`. Use `⟨t, f0, ht, hf0I, hf0ne, fun g hg => ⟨1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[pow_one]`. Conclude with `htI g hg`.
-/
theorem locPrincipal_of_rankAtStalk_eq_one {A : Type} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent]
    [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I))
    (hP : Module.rankAtStalk I.Cotangent P = 1) :
    LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) := by
  set p := P.asIdeal.comap (Ideal.Quotient.mk I) with hp_def
  haveI hpP : p.IsPrime := Ideal.comap_isPrime _ _
  have hIp : I ≤ p := fun x hx => by
    rw [hp_def, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact P.asIdeal.zero_mem
  obtain ⟨m0, hm0⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.exists_generator_of_rankAtStalk_eq_one P hP
  obtain ⟨⟨f0, hf0I⟩, hf0⟩ := Ideal.toCotangent_surjective I m0
  have hsm : ∀ (r : A) (y : I.Cotangent), Ideal.Quotient.mk I r • y = r • y := by
    intro r y
    first
      | (rw [← Ideal.Quotient.algebraMap_eq]; exact algebraMap_smul (A ⧸ I) r y)
      | rfl
      | (obtain ⟨y', rfl⟩ := Ideal.toCotangent_surjective I y; rfl)
  have step : ∀ x ∈ I, ∃ s ∉ p, ∃ b : A, s * x - b * f0 ∈ I ^ 2 := by
    intro x hx
    obtain ⟨sq, hsq, bq, hsb⟩ := hm0 (I.toCotangent ⟨x, hx⟩)
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective sq
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bq
    refine ⟨s, hsq, b, ?_⟩
    rw [← hf0, hsm, hsm, ← map_smul I.toCotangent, ← map_smul I.toCotangent,
      Ideal.toCotangent_eq] at hsb
    simpa only [Submodule.coe_smul, smul_eq_mul] using hsb
  let φ := algebraMap A (Localization.AtPrime p)
  set K : Ideal A := Ideal.span {f0} with hK
  have hIfg : I.FG := IsNoetherian.noetherian I
  have hle : I.map φ ≤ K.map φ ⊔ IsLocalRing.maximalIdeal (Localization.AtPrime p) • I.map φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    obtain ⟨s, hs, b, hsb⟩ := step x hx
    have hunit : IsUnit (φ s) :=
      IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
    rw [← Ideal.unit_mul_mem_iff_mem _ hunit, ← map_mul]
    have hdecomp : s * x = b * f0 + (s * x - b * f0) := by ring
    rw [hdecomp, map_add]
    refine Submodule.add_mem_sup ?_ ?_
    · exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f0))
    · have h2 : φ (s * x - b * f0) ∈ (I ^ 2).map φ := Ideal.mem_map_of_mem _ hsb
      rw [Ideal.map_pow, pow_two] at h2
      rw [Ideal.smul_eq_mul]
      exact Ideal.mul_mono_left
        (le_trans (Ideal.map_mono hIp) (Localization.AtPrime.map_eq_maximalIdeal).le) h2
  have hnak : I.map φ ≤ K.map φ :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (hIfg.map φ)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle
  have hloc : ∀ x ∈ I, ∃ s ∉ p, s * x ∈ K := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
      (Localization.AtPrime p) K x).mp (hnak (Ideal.mem_map_of_mem φ hx))
    exact ⟨s, hs, hsx⟩
  have hunif : ∀ N : Submodule A A, N.FG → N ≤ I → ∃ s ∉ p, ∀ y ∈ N, s * y ∈ K := by
    intro N hN
    refine Submodule.fg_induction
      (motive := fun N _ => N ≤ I → ∃ s ∉ p, ∀ y ∈ N, s * y ∈ K) ?_ ?_ N hN
    · intro x hxI
      obtain ⟨s, hs, hsx⟩ := hloc x (hxI (Submodule.mem_span_singleton_self x))
      refine ⟨s, hs, fun y hy => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [smul_eq_mul, mul_left_comm]
      exact K.mul_mem_left c hsx
    · intro N₁ N₂ _ _ ih₁ ih₂ h₁₂
      obtain ⟨s₁, hs₁, h₁⟩ := ih₁ (le_trans le_sup_left h₁₂)
      obtain ⟨s₂, hs₂, h₂⟩ := ih₂ (le_trans le_sup_right h₁₂)
      refine ⟨s₁ * s₂, fun hmem => (hpP.mem_or_mem hmem).elim hs₁ hs₂, fun y hy => ?_⟩
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      have hsplit : s₁ * s₂ * (y₁ + y₂) = s₂ * (s₁ * y₁) + s₁ * (s₂ * y₂) := by ring
      rw [hsplit]
      exact K.add_mem (K.mul_mem_left _ (h₁ y₁ hy₁)) (K.mul_mem_left _ (h₂ y₂ hy₂))
  obtain ⟨t, ht, htI⟩ := hunif I hIfg le_rfl
  have hf0ne : f0 ≠ 0 := by
    intro h0
    have hbot : ∀ y : I, y = 0 := by
      intro y
      apply Subtype.ext
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (htI y y.2)
      rw [h0, mul_zero] at ha
      rcases mul_eq_zero.mp ha.symm with h | h
      · rw [h] at ht
        exact absurd p.zero_mem ht
      · exact h
    haveI : Subsingleton I.Cotangent := ⟨fun a b => by
      obtain ⟨a', rfl⟩ := Ideal.toCotangent_surjective I a
      obtain ⟨b', rfl⟩ := Ideal.toCotangent_surjective I b
      rw [hbot a', hbot b']⟩
    have h0rank := Module.rankAtStalk_eq_zero_of_subsingleton (R := A ⧸ I) (M := I.Cotangent)
    rw [h0rank] at hP
    first
      | exact zero_ne_one hP
      | simp at hP
  refine ⟨t, f0, ht, hf0I, hf0ne, fun g hg => ⟨1, ?_⟩⟩
  rw [pow_one]
  exact htI g hg

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

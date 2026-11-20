import Mathlib

namespace GlobalTheory.CompanionTheory.Ggeo.RegularDvd

def Div {R B : Type} [CommRing R] [CommRing B] (u : R →+* B) (m : Ideal B) (x y : B) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (ψ : B →+* O),
    (∀ b, b ∉ m → IsUnit (ψ b)) ∧ (∀ b ∈ m, ¬ IsUnit (ψ b)) ∧
      Function.Injective (ψ.comp u) ∧ ∃ c, ψ x = ψ y * c

/- English proof (translation)
Use `haveI := hp.isPrime`. Set `A` to `Localization.AtPrime p`. Use `haveI : IsDiscreteValuationRing A := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hne A`. Establish `hinj : Function.Injective (algebraMap R A)` using `IsLocalization.injective A p.primeCompl_le_nonZeroDivisors`. Establish `hunit : ∀ x : R, IsUnit (algebraMap R A x) ↔ x ∉ p` using `fun x => IsLocalization.AtPrime.isUnit_to_map_iff A p x`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible A`. Take `⟨⟨π, s⟩, hs⟩` from `IsLocalization.surj p.primeCompl ϖ`. Establish `hsu : IsUnit (algebraMap R A (s : R))` using `(hunit _).2 s.2`. Establish `hπ : Irreducible (algebraMap R A π)`. Establish `: Associated ϖ (algebraMap R A π)` using `⟨hsu.unit, by simpa using hs⟩`.

Conclude with `this.irreducible hϖ`. Use `⟨π, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hπ.ne_zero (map_zero _)`. Assume the negation of the conclusion as `h`.

Conclude with `hπ.not_isUnit ((hunit π).2 h)`. Introduce `x hx`. Establish `hmem : algebraMap R A x ∈ IsLocalRing.maximalIdeal A`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]`. Simplify using `using hx`.

Rewrite `hmem` using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ, Ideal.mem_span_singleton]`. Take `⟨z, hz⟩` from `hmem`. Take `⟨⟨z0, s0⟩, hz0⟩` from `IsLocalization.surj p.primeCompl z`. Use `⟨s0, s0.2, z0, hinj ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul] at hz0 ⊢`.

Rewrite using `[hz, ← hz0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd' : algebraMap R A d ≠ 0` using `fun h => hd (hinj (by simpa using h))`. Take `⟨n, w, hw⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hd' hπ`. Take `⟨⟨w0, t0⟩, hw0⟩` from `IsLocalization.surj p.primeCompl (w : A)`.

Establish `ht0 : IsUnit (algebraMap R A (t0 : R))` using `(hunit _).2 t0.2`. Establish `hw0u : w0 ∉ p`. Rewrite using `[← hunit, ← hw0]`. Conclude with `w.isUnit.mul ht0`. Use `⟨n, w0, t0, hw0u, t0.2, hinj ?_⟩` and prove the remaining obligations.

Simplify using `only [map_mul, map_pow] at hw0 ⊢`. Rewrite using `[← hw, ← hw0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_uniformizer {R : Type} [CommRing R] [IsDedekindDomain R] (p : Ideal R)
    (hp : p.IsMaximal) (hne : p ≠ ⊥) (d : R) (hd : d ≠ 0) :
    ∃ π : R, π ≠ 0 ∧ π ∈ p ∧ (∀ x ∈ p, ∃ s, s ∉ p ∧ ∃ z, s * x = π * z) ∧
      ∃ (a : ℕ) (t t' : R), t ∉ p ∧ t' ∉ p ∧ t * d = t' * π ^ a := by
  haveI := hp.isPrime
  let A := Localization.AtPrime p
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hne A
  have hinj : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A p.primeCompl_le_nonZeroDivisors
  have hunit : ∀ x : R, IsUnit (algebraMap R A x) ↔ x ∉ p := fun x =>
    IsLocalization.AtPrime.isUnit_to_map_iff A p x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨⟨π, s⟩, hs⟩ := IsLocalization.surj p.primeCompl ϖ
  have hsu : IsUnit (algebraMap R A (s : R)) := (hunit _).2 s.2
  have hπ : Irreducible (algebraMap R A π) := by
    have : Associated ϖ (algebraMap R A π) := ⟨hsu.unit, by simpa using hs⟩
    exact this.irreducible hϖ
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact hπ.ne_zero (map_zero _)
  · by_contra h
    exact hπ.not_isUnit ((hunit π).2 h)
  · intro x hx
    have hmem : algebraMap R A x ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
      simpa using hx
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ, Ideal.mem_span_singleton] at hmem
    obtain ⟨z, hz⟩ := hmem
    obtain ⟨⟨z0, s0⟩, hz0⟩ := IsLocalization.surj p.primeCompl z
    refine ⟨s0, s0.2, z0, hinj ?_⟩
    simp only [map_mul] at hz0 ⊢
    rw [hz, ← hz0]
    ring
  · have hd' : algebraMap R A d ≠ 0 := fun h => hd (hinj (by simpa using h))
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd' hπ
    obtain ⟨⟨w0, t0⟩, hw0⟩ := IsLocalization.surj p.primeCompl (w : A)
    have ht0 : IsUnit (algebraMap R A (t0 : R)) := (hunit _).2 t0.2
    have hw0u : w0 ∉ p := by
      rw [← hunit, ← hw0]
      exact w.isUnit.mul ht0
    refine ⟨n, w0, t0, hw0u, t0.2, hinj ?_⟩
    simp only [map_mul, map_pow] at hw0 ⊢
    rw [← hw, ← hw0]
    ring

/- English proof (translation)
Establish `hPne : p.map u ≠ ⊤` using `fun h => hg (h ▸ Submodule.mem_top)`. Use `haveI hP : (p.map u).IsPrime := ⟨hPne, fun {a b} h => hprime a b h⟩`. Use `letI : Field (R ⧸ p) := Ideal.Quotient.field p`. Set `q : R ⧸ p →+* B ⧸ p.map u` to `Ideal.quotientMap (p.map u) u Ideal.le_comap_map`. Establish `hq : q.FiniteType`.

Apply `RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk p)` to reduce the goal to its premises. Establish `: q.comp (Ideal.Quotient.mk p) = (Ideal.Quotient.mk (p.map u)).comp u` using `Ideal.quotientMap_comp_mk _`. Rewrite using `[this]`. Conclude with `(RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hft`. Use `haveI : IsJacobsonRing (B ⧸ p.map u) := hq.isJacobsonRing`.

Establish `hj : (⊥ : Ideal (B ⧸ p.map u)).jacobson = ⊥` using `IsJacobsonRing.out inferInstance Ideal.isPrime_bot.isRadical`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hmem : Ideal.Quotient.mk (p.map u) g ∈ (⊥ : Ideal (B ⧸ p.map u)).jacobson`. Use `(Ideal.mem_sInf).2 ?_` and prove the remaining obligations.

Introduce and unpack `J ⟨-, hJ⟩`. Use `haveI := hJ`. Establish `hc : (J.comap (Ideal.Quotient.mk (p.map u))).IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Use `h _ hc ?_` and prove the remaining obligations. Introduce `x hx`.

Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]`. Conclude with `J.zero_mem`. Rewrite `hmem` using `[hj, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hg hmem`.
-/
theorem exists_maximal_not_mem {R B : Type} [CommRing R] [CommRing B] (u : R →+* B)
    (hft : u.FiniteType) (p : Ideal R) (hp : p.IsMaximal)
    (hprime : ∀ a b : B, a * b ∈ p.map u → a ∈ p.map u ∨ b ∈ p.map u)
    (g : B) (hg : g ∉ p.map u) : ∃ m : Ideal B, m.IsMaximal ∧ p.map u ≤ m ∧ g ∉ m := by
  have hPne : p.map u ≠ ⊤ := fun h => hg (h ▸ Submodule.mem_top)
  haveI hP : (p.map u).IsPrime := ⟨hPne, fun {a b} h => hprime a b h⟩
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  let q : R ⧸ p →+* B ⧸ p.map u := Ideal.quotientMap (p.map u) u Ideal.le_comap_map
  have hq : q.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk p)
    have : q.comp (Ideal.Quotient.mk p) = (Ideal.Quotient.mk (p.map u)).comp u :=
      Ideal.quotientMap_comp_mk _
    rw [this]
    exact (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hft
  haveI : IsJacobsonRing (B ⧸ p.map u) := hq.isJacobsonRing
  have hj : (⊥ : Ideal (B ⧸ p.map u)).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance Ideal.isPrime_bot.isRadical
  by_contra h
  push_neg at h
  have hmem : Ideal.Quotient.mk (p.map u) g ∈ (⊥ : Ideal (B ⧸ p.map u)).jacobson := by
    refine (Ideal.mem_sInf).2 ?_
    rintro J ⟨-, hJ⟩
    haveI := hJ
    have hc : (J.comap (Ideal.Quotient.mk (p.map u))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    refine h _ hc ?_
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact J.zero_mem
  rw [hj, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hg hmem

/- English proof (translation)
Use `Submodule.span_induction (p := fun g _ => ∃ t, t ∉ p ∧ ∃ h, u t * g = u π * h) ?_ ?_ ?_ ?_ hg` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨s, hs, z, hz⟩` from `hloc x hx`. Conclude with `⟨s, hs, u z, by rw [← map_mul, hz, map_mul]⟩`. Conclude with `⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h), 0, by simp⟩`.

Introduce and unpack `x y - - ⟨t₁, ht₁, h₁, e₁⟩ ⟨t₂, ht₂, h₂, e₂⟩`. Use `⟨t₁ * t₂, fun h => (hp.mem_or_mem h).elim ht₁ ht₂, u t₂ * h₁ + u t₁ * h₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Take the linear combination `(u t₂) * e₁ + (u t₁) * e₂`. Introduce and unpack `b x - ⟨t, ht, h, e⟩`.

Use `⟨t, ht, b * h, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`. Take the linear combination `b * e`.
-/
theorem exists_of_mem_map {R B : Type} [CommRing R] [CommRing B] (u : R →+* B) (p : Ideal R)
    (hp : p.IsPrime) (π : R) (hloc : ∀ x ∈ p, ∃ s, s ∉ p ∧ ∃ z, s * x = π * z)
    (g : B) (hg : g ∈ p.map u) : ∃ t, t ∉ p ∧ ∃ h, u t * g = u π * h := by
  refine Submodule.span_induction (p := fun g _ => ∃ t, t ∉ p ∧ ∃ h, u t * g = u π * h)
    ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, z, hz⟩ := hloc x hx
    exact ⟨s, hs, u z, by rw [← map_mul, hz, map_mul]⟩
  · exact ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h), 0, by simp⟩
  · rintro x y - - ⟨t₁, ht₁, h₁, e₁⟩ ⟨t₂, ht₂, h₂, e₂⟩
    refine ⟨t₁ * t₂, fun h => (hp.mem_or_mem h).elim ht₁ ht₂, u t₂ * h₁ + u t₁ * h₂, ?_⟩
    rw [map_mul]
    linear_combination (u t₂) * e₁ + (u t₁) * e₂
  · rintro b x - ⟨t, ht, h, e⟩
    refine ⟨t, ht, b * h, ?_⟩
    rw [smul_eq_mul]
    linear_combination b * e

/- English proof (translation)
Introduce `h`. Establish `hle : p ≤ m.comap u` using `Ideal.map_le_iff_le_comap.1 hpm`. Establish `hne : m.comap u ≠ ⊤` using `(Ideal.comap_ne_top _ hm.ne_top)`. Conclude with `ht ((hp.eq_of_le hne hle).symm ▸ h)`.
-/
theorem map_not_mem {R B : Type} [CommRing R] [CommRing B] (u : R →+* B) (p : Ideal R)
    (hp : p.IsMaximal) (m : Ideal B) (hm : m.IsMaximal) (hpm : p.map u ≤ m) (t : R) (ht : t ∉ p) :
    u t ∉ m := by
  intro h
  have hle : p ≤ m.comap u := Ideal.map_le_iff_le_comap.1 hpm
  have hne : m.comap u ≠ ⊤ := (Ideal.comap_ne_top _ hm.ne_top)
  exact ht ((hp.eq_of_le hne hle).symm ▸ h)

/- English proof (translation)
Establish `hpp` using `hp.isPrime`. Proceed by induction on `a with`. Consider the case `zero`. Introduce `g _`. Conclude with `⟨1, fun h => hpp.ne_top ((Ideal.eq_top_iff_one _).2 h), g, by simp⟩`.

Consider the case `succ a ih`. Introduce `g hg`. Establish `hgP : g ∈ p.map u`. Assume the negation of the conclusion as `hn`. Take `⟨m, hm, hpm, hgm⟩` from `exists_maximal_not_mem u hft p hp hprime g hn`.

Take `⟨O, _, _, ψ, hu, hnu, -, c, hc⟩` from `hg m hm hpm`. Establish `hπm : u π ∈ m` using `hpm (Ideal.mem_map_of_mem u hπ)`. Use `hnu _ hπm ?_` and prove the remaining obligations. Establish `h1 : IsUnit (ψ (u π) * (ψ (u π) ^ a * c))`. Use `hu g hgm` as an intermediate fact.

Rewrite `this` using `[hc, map_pow]`. Rewrite `this` using `[pow_succ', mul_assoc]`. Then use the resulting hypothesis. Conclude with `isUnit_of_mul_isUnit_left h1`. Take `⟨t, ht, g', e⟩` from `exists_of_mem_map u p hpp π hloc g hgP`. Take `⟨t₂, ht₂, h, e₂⟩` from `ih g' (fun m hm hpm => by`.

Take `⟨O, i₁, i₂, ψ, hu, hnu, hinj, c, hc⟩` from `hg m hm hpm`. Use `⟨O, i₁, i₂, ψ, hu, hnu, hinj, ψ (u t) * c, ?_⟩` and prove the remaining obligations. Establish `hne : ψ (u π) ≠ 0` using `fun h0 => hπ0 (hinj (by simpa using h0))`. Establish `e' : ψ (u t) * ψ g = ψ (u π) * ψ g'` using `by rw [← map_mul, e, map_mul]`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises.

Rewrite using `[← e', hc, map_pow, map_pow]`. Use the proof step `ring)`. Use `⟨t₂ * t, fun h => (hpp.mem_or_mem h).elim ht₂ ht, h, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Take the linear combination `(u t₂) * e + (u π) * e₂`.
-/
theorem local_pow {R B : Type} [CommRing R] [CommRing B] (u : R →+* B) (hft : u.FiniteType)
    (p : Ideal R) (hp : p.IsMaximal)
    (hprime : ∀ a b : B, a * b ∈ p.map u → a ∈ p.map u ∨ b ∈ p.map u)
    (π : R) (hπ0 : π ≠ 0) (hπ : π ∈ p) (hloc : ∀ x ∈ p, ∃ s, s ∉ p ∧ ∃ z, s * x = π * z) (a : ℕ) :
    ∀ g : B, (∀ m : Ideal B, m.IsMaximal → p.map u ≤ m → Div u m g (u π ^ a)) →
      ∃ t, t ∉ p ∧ ∃ h, u t * g = u π ^ a * h := by
  have hpp := hp.isPrime
  induction a with
  | zero =>
    intro g _
    exact ⟨1, fun h => hpp.ne_top ((Ideal.eq_top_iff_one _).2 h), g, by simp⟩
  | succ a ih =>
    intro g hg
    have hgP : g ∈ p.map u := by
      by_contra hn
      obtain ⟨m, hm, hpm, hgm⟩ := exists_maximal_not_mem u hft p hp hprime g hn
      obtain ⟨O, _, _, ψ, hu, hnu, -, c, hc⟩ := hg m hm hpm
      have hπm : u π ∈ m := hpm (Ideal.mem_map_of_mem u hπ)
      refine hnu _ hπm ?_
      have h1 : IsUnit (ψ (u π) * (ψ (u π) ^ a * c)) := by
        have := hu g hgm
        rw [hc, map_pow] at this
        rwa [pow_succ', mul_assoc] at this
      exact isUnit_of_mul_isUnit_left h1
    obtain ⟨t, ht, g', e⟩ := exists_of_mem_map u p hpp π hloc g hgP
    obtain ⟨t₂, ht₂, h, e₂⟩ := ih g' (fun m hm hpm => by
      obtain ⟨O, i₁, i₂, ψ, hu, hnu, hinj, c, hc⟩ := hg m hm hpm
      refine ⟨O, i₁, i₂, ψ, hu, hnu, hinj, ψ (u t) * c, ?_⟩
      have hne : ψ (u π) ≠ 0 := fun h0 => hπ0 (hinj (by simpa using h0))
      have e' : ψ (u t) * ψ g = ψ (u π) * ψ g' := by rw [← map_mul, e, map_mul]
      apply mul_left_cancel₀ hne
      rw [← e', hc, map_pow, map_pow]
      ring)
    refine ⟨t₂ * t, fun h => (hpp.mem_or_mem h).elim ht₂ ht, h, ?_⟩
    rw [map_mul]
    linear_combination (u t₂) * e + (u π) * e₂

/- English proof (translation)
Introduce `R B _ _ _ _ _ u hft hprime f d hd H`. Set `I : Ideal R` to `{ carrier := {r | ∃ a, u r * f = u d * a} add_mem' := by`. Introduce and unpack `x y ⟨a, ha⟩ ⟨b, hb⟩`. Conclude with `⟨a + b, by rw [map_add]; linear_combination ha + hb⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨a, ha⟩`. Conclude with `⟨u c * a, by rw [smul_eq_mul, map_mul]; linear_combination (u c) * ha⟩ }`. Distinguish the cases in `hI : I = ⊤`. Establish `h1 : (1 : R) ∈ I` using `hI ▸ Submodule.mem_top`.

Take `⟨a, ha⟩` from `h1`. Conclude with `⟨a, by simpa using ha⟩`. It suffices to derive a contradiction. Take `⟨p, hp, hIp⟩` from `Ideal.exists_le_maximal I hI`. Establish `hpp` using `hp.isPrime`.

Establish `hdI : d ∈ I` using `⟨f, rfl⟩`. Establish `hne : p ≠ ⊥` using `fun h => hd (by simpa [h] using hIp hdI)`. Take `⟨π, hπ0, hπ, hloc, a, t, t', ht, ht', e⟩` from `exists_uniformizer p hp hne d hd`. Take `⟨s, hs, h, es⟩` from `local_pow u hft p hp (hprime p hp) π hπ0 hπ hloc a f (fun m hm hpm => by`. Take `⟨O, i₁, i₂, ψ, hu, hnu, hinj, c, hc⟩` from `H m hm`.

Take `⟨v, hv⟩` from `(hu _ (map_not_mem u p hp m hm hpm t ht)).exists_left_inv`. Use `⟨O, i₁, i₂, ψ, hu, hnu, hinj, v * ψ (u t') * c, ?_⟩` and prove the remaining obligations. Establish `e' : ψ (u t) * ψ (u d) = ψ (u t') * ψ (u π) ^ a`. Rewrite using `[← map_mul, ← map_mul, ← map_pow, ← map_pow, ← map_mul, ← map_mul, e]`. Rewrite using `[hc, map_pow]`.

Take the linear combination `(-(ψ (u d)) * c) * hv + c * v * e')`. Establish `hmem : t' * s ∈ I`. Use `⟨u t * h, ?_⟩` and prove the remaining obligations. Establish `e' : u t * u d = u t' * u π ^ a` using `by rw [← map_mul, e, map_mul, map_pow]`. Rewrite using `[map_mul]`.

Take the linear combination `(u t') * es + h * (-e')`. Conclude with `(hpp.mem_or_mem (hIp hmem)).elim ht' hs`.
-/
theorem dvd_of_local : ∀ (R B : Type) [CommRing R] [IsDedekindDomain R] [CommRing B] [IsDomain B]
    [IsNoetherianRing B] (u : R →+* B), u.FiniteType →
    (∀ p : Ideal R, p.IsMaximal → ∀ a b : B, a * b ∈ p.map u → a ∈ p.map u ∨ b ∈ p.map u) →
    ∀ (f : B) (d : R), d ≠ 0 →
    (∀ m : Ideal B, m.IsMaximal → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (ψ : B →+* O),
      (∀ b, b ∉ m → IsUnit (ψ b)) ∧ (∀ b ∈ m, ¬ IsUnit (ψ b)) ∧
        Function.Injective (ψ.comp u) ∧ ∃ c, ψ f = ψ (u d) * c) →
    ∃ a, f = u d * a := by
  intro R B _ _ _ _ _ u hft hprime f d hd H
  let I : Ideal R :=
    { carrier := {r | ∃ a, u r * f = u d * a}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by rw [map_add]; linear_combination ha + hb⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, ha⟩
        exact ⟨u c * a, by rw [smul_eq_mul, map_mul]; linear_combination (u c) * ha⟩ }
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, by simpa using ha⟩
  exfalso
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
  have hpp := hp.isPrime
  have hdI : d ∈ I := ⟨f, rfl⟩
  have hne : p ≠ ⊥ := fun h => hd (by simpa [h] using hIp hdI)
  obtain ⟨π, hπ0, hπ, hloc, a, t, t', ht, ht', e⟩ := exists_uniformizer p hp hne d hd
  obtain ⟨s, hs, h, es⟩ := local_pow u hft p hp (hprime p hp) π hπ0 hπ hloc a f
    (fun m hm hpm => by
      obtain ⟨O, i₁, i₂, ψ, hu, hnu, hinj, c, hc⟩ := H m hm
      obtain ⟨v, hv⟩ := (hu _ (map_not_mem u p hp m hm hpm t ht)).exists_left_inv
      refine ⟨O, i₁, i₂, ψ, hu, hnu, hinj, v * ψ (u t') * c, ?_⟩
      have e' : ψ (u t) * ψ (u d) = ψ (u t') * ψ (u π) ^ a := by
        rw [← map_mul, ← map_mul, ← map_pow, ← map_pow, ← map_mul, ← map_mul, e]
      rw [hc, map_pow]
      linear_combination (-(ψ (u d)) * c) * hv + c * v * e')
  have hmem : t' * s ∈ I := by
    refine ⟨u t * h, ?_⟩
    have e' : u t * u d = u t' * u π ^ a := by rw [← map_mul, e, map_mul, map_pow]
    rw [map_mul]
    linear_combination (u t') * es + h * (-e')
  exact (hpp.mem_or_mem (hIp hmem)).elim ht' hs

end GlobalTheory.CompanionTheory.Ggeo.RegularDvd

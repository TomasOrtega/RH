import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL GlobalTheory.UnitaryBC

/- English proof (translation)
Introduce `hCj hBar hKey hRoot E _ _ _ A x hG q hq hs w hw`. Establish `hadj : IntermediateField.adjoin ℚ {x} = IntermediateField.adjoin ℚ {(A.ω : E)}` using `le_antisymm (IntermediateField.adjoin_simple_le_iff.2 hG.2) (IntermediateField.adjoin_simple_le_iff.2 hG.1)`. Establish `hS : ∀ u u' : HeightOneSpectrum (𝓞 E), CertificateRingHomMap.SameK x u u' ↔ ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} → (y ∈ u.asIdeal ↔ y ∈ u'.asIdeal)` using `fun u u' => by`. Unfold `CertificateRingHomMap.SameK`. Rewrite using `[hadj]`.

Establish `hnd` using `hs.1`. Establish `hmemω : ∀ s : ℤ, ((A.ω - (s : 𝓞 E) : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)}` using `fun s => by`. Establish `e : ((A.ω - (s : 𝓞 E) : 𝓞 E) : E) = (A.ω : E) - (s : E)`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _ - _`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `sub_mem (IntermediateField.mem_adjoin_simple_self ℚ _) (intCast_mem _ s)`. Establish `hmemq : ((q : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)}`. Establish `e : ((q : 𝓞 E) : E) = (q : E)`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E _ = _`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `natCast_mem _ q`. Establish `hbarI : ∀ s : ℤ, A.bar (s : 𝓞 E) = (s : 𝓞 E)` using `fun s => map_intCast A.bar s`. Establish `hbarN : A.bar (q : 𝓞 E) = (q : 𝓞 E)` using `map_natCast A.bar q`.

Establish `hbarω : A.bar A.ω = (A.tr : 𝓞 E) - A.ω`. Rewrite using `[← A.tr_eq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hbarsub : ∀ s : ℤ, A.bar (A.ω - (s : 𝓞 E)) = (A.tr : 𝓞 E) - A.ω - (s : 𝓞 E)` using `fun s => by`. Rewrite using `[map_sub, hbarω, hbarI]`.

Establish `hquad : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0`. Rewrite using `[← A.tr_eq, ← A.nm_eq]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨r, hr, hrw⟩` from `hRoot E A q hq hs w hw`. Establish `hne1 : ¬ CertificateRingHomMap.SameK x (CertificateRingHomMap.cj w) w`.

Introduce `h`. Establish `h1 : A.ω - (r : 𝓞 E) ∈ (CertificateRingHomMap.cj w).asIdeal` using `((hS _ _).1 h _ (hmemω r)).2 hrw`. Establish `h2 : (A.tr : 𝓞 E) - A.ω - (r : 𝓞 E) ∈ w.asIdeal`. Rewrite using `[← hbarsub]`. Conclude with `(hCj E A w _).1 h1`.

Establish `h3 : ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) ∈ w.asIdeal`. Use `w.asIdeal.sub_mem hrw h2` as an intermediate fact. Establish `e : A.ω - (r : 𝓞 E) - ((A.tr : 𝓞 E) - A.ω - (r : 𝓞 E)) = (2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)` using `by ring`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `h4 : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) ∈ w.asIdeal`.

Use `w.asIdeal.mul_mem_left ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) h3` as an intermediate fact. Establish `e : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) = ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) * ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) - 4 * (A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E)) * (-1) - 8 * (A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E))` using `by push_cast; ring`. Rewrite using `[e, hquad]`. Simplify using `using this`. Take `⟨a, b, hab⟩` from `((Nat.prime_iff_prime_int.1 hq).irreducible.coprime_iff_not_dvd).2 hnd`.

Establish `h5 : (1 : 𝓞 E) ∈ w.asIdeal`. Establish `e : (1 : 𝓞 E) = (a : 𝓞 E) * (q : 𝓞 E) + (b : 𝓞 E) * ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E)`. Conclude with `(congrArg (Int.cast : ℤ → 𝓞 E) hab).symm` after adjusting the coercions. Rewrite using `[e]`. Conclude with `w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ h4)`.

Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h5)`. Use `⟨hne1, ?_, ?_, ?_, ?_, ⟨r, hr, hrw⟩, ?_⟩` and prove the remaining obligations. Use `⟨CertificateRingHomMap.cj w, fun h => hne1 (by rw [h]; exact fun _ _ => Iff.rfl), ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.DefU.ClassFin.under_conjSrc _ (fun y => (IsCMField.complexConj E).commutes y) w`. Introduce `u hu`.

Take `⟨k, hk⟩` from `hr`. Establish `hkE : (r : 𝓞 E) ^ 2 - (A.tr : 𝓞 E) * (r : 𝓞 E) + (A.nm : 𝓞 E) = (q : 𝓞 E) * (k : 𝓞 E)`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 E) hk` after adjusting the coercions. Establish `hprod : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) = (q : 𝓞 E) * (-(k : 𝓞 E))`. Use `push_cast`.

Take the linear combination `hquad - hkE`. Establish `hmem : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) ∈ u.asIdeal`. Rewrite using `[hprod]`. Conclude with `u.asIdeal.mul_mem_right _ hu`. Break down `u.isPrime.mem_or_mem hmem with h | h` into its components or cases.

Conclude with `Or.inl ((hS _ _).2 (hKey E A q hq hnd r u w hu hw h hrw))`. Use `Or.inr ((hS _ _).2 (hKey E A q hq hnd r (CertificateRingHomMap.cj u) w ?_ hw ?_ hrw))` and prove the remaining obligations. Rewrite using `[hCj E A u, hbarN]`. Conclude with `hu`. Rewrite using `[hCj E A u, hbarsub]`.

Establish `e : (A.tr : 𝓞 E) - A.ω - (r : 𝓞 E) = -(A.ω - ((A.tr - r : ℤ) : 𝓞 E))` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `u.asIdeal.neg_mem h`. Introduce `u h`. Conclude with `((hS _ _).1 h _ hmemq).2 hw`.

Introduce `u u' h y hy`. Rewrite `hy` using `[hadj]`. Rewrite using `[hCj E A u, hCj E A u']`. Conclude with `(hS _ _).1 h _ (hBar E A y hy)`. Introduce `s hsw u`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨((hS _ _).1 h _ hmemq).2 hw, ((hS _ _).1 h _ (hmemω s)).2 hsw⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `(hS _ _).2 (hKey E A q hq hnd s u w h1 hw h2 hsw)`.
-/
theorem UpperTheory.Gal.G1.pSides :
    CjMem → BarAdj → KeyK → RootAt → Pl.Sides := by
  intro hCj hBar hKey hRoot E _ _ _ A x hG q hq hs w hw
  have hadj : IntermediateField.adjoin ℚ {x} = IntermediateField.adjoin ℚ {(A.ω : E)} :=
    le_antisymm (IntermediateField.adjoin_simple_le_iff.2 hG.2) (IntermediateField.adjoin_simple_le_iff.2 hG.1)
  have hS : ∀ u u' : HeightOneSpectrum (𝓞 E), CertificateRingHomMap.SameK x u u' ↔
      ∀ y : 𝓞 E, (y : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} → (y ∈ u.asIdeal ↔ y ∈ u'.asIdeal) := fun u u' => by
    unfold CertificateRingHomMap.SameK
    rw [hadj]
  have hnd := hs.1
  have hmemω : ∀ s : ℤ, ((A.ω - (s : 𝓞 E) : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} := fun s => by
    have e : ((A.ω - (s : 𝓞 E) : 𝓞 E) : E) = (A.ω : E) - (s : E) := by
      change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _ - _
      simp
    rw [e]
    exact sub_mem (IntermediateField.mem_adjoin_simple_self ℚ _) (intCast_mem _ s)
  have hmemq : ((q : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(A.ω : E)} := by
    have e : ((q : 𝓞 E) : E) = (q : E) := by
      change algebraMap (𝓞 E) E _ = _
      simp
    rw [e]
    exact natCast_mem _ q
  have hbarI : ∀ s : ℤ, A.bar (s : 𝓞 E) = (s : 𝓞 E) := fun s => map_intCast A.bar s
  have hbarN : A.bar (q : 𝓞 E) = (q : 𝓞 E) := map_natCast A.bar q
  have hbarω : A.bar A.ω = (A.tr : 𝓞 E) - A.ω := by
    rw [← A.tr_eq]; ring
  have hbarsub : ∀ s : ℤ, A.bar (A.ω - (s : 𝓞 E)) = (A.tr : 𝓞 E) - A.ω - (s : 𝓞 E) := fun s => by
    rw [map_sub, hbarω, hbarI]
  have hquad : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0 := by
    rw [← A.tr_eq, ← A.nm_eq]; ring
  obtain ⟨r, hr, hrw⟩ := hRoot E A q hq hs w hw
  have hne1 : ¬ CertificateRingHomMap.SameK x (CertificateRingHomMap.cj w) w := by
    intro h
    have h1 : A.ω - (r : 𝓞 E) ∈ (CertificateRingHomMap.cj w).asIdeal := ((hS _ _).1 h _ (hmemω r)).2 hrw
    have h2 : (A.tr : 𝓞 E) - A.ω - (r : 𝓞 E) ∈ w.asIdeal := by
      rw [← hbarsub]; exact (hCj E A w _).1 h1
    have h3 : ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) ∈ w.asIdeal := by
      have := w.asIdeal.sub_mem hrw h2
      have e : A.ω - (r : 𝓞 E) - ((A.tr : 𝓞 E) - A.ω - (r : 𝓞 E)) = (2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E) := by ring
      rwa [e] at this
    have h4 : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) ∈ w.asIdeal := by
      have := w.asIdeal.mul_mem_left ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) h3
      have e : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) = ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) * ((2 : 𝓞 E) * A.ω - (A.tr : 𝓞 E)) - 4 * (A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E)) * (-1) - 8 * (A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E)) := by
        push_cast; ring
      rw [e, hquad]
      simpa using this
    obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hq).irreducible.coprime_iff_not_dvd).2 hnd
    have h5 : (1 : 𝓞 E) ∈ w.asIdeal := by
      have e : (1 : 𝓞 E) = (a : 𝓞 E) * (q : 𝓞 E) + (b : 𝓞 E) * ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) := by
        exact_mod_cast (congrArg (Int.cast : ℤ → 𝓞 E) hab).symm
      rw [e]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ h4)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h5)
  refine ⟨hne1, ?_, ?_, ?_, ?_, ⟨r, hr, hrw⟩, ?_⟩
  · refine ⟨CertificateRingHomMap.cj w, fun h => hne1 (by rw [h]; exact fun _ _ => Iff.rfl), ?_⟩
    exact GlobalTheory.DefU.ClassFin.under_conjSrc _ (fun y => (IsCMField.complexConj E).commutes y) w
  · intro u hu
    obtain ⟨k, hk⟩ := hr
    have hkE : (r : 𝓞 E) ^ 2 - (A.tr : 𝓞 E) * (r : 𝓞 E) + (A.nm : 𝓞 E) = (q : 𝓞 E) * (k : 𝓞 E) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hk
    have hprod : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) = (q : 𝓞 E) * (-(k : 𝓞 E)) := by
      push_cast
      linear_combination hquad - hkE
    have hmem : (A.ω - (r : 𝓞 E)) * (A.ω - ((A.tr - r : ℤ) : 𝓞 E)) ∈ u.asIdeal := by
      rw [hprod]; exact u.asIdeal.mul_mem_right _ hu
    rcases u.isPrime.mem_or_mem hmem with h | h
    · exact Or.inl ((hS _ _).2 (hKey E A q hq hnd r u w hu hw h hrw))
    · refine Or.inr ((hS _ _).2 (hKey E A q hq hnd r (CertificateRingHomMap.cj u) w ?_ hw ?_ hrw))
      · rw [hCj E A u, hbarN]; exact hu
      · rw [hCj E A u, hbarsub]
        have e : (A.tr : 𝓞 E) - A.ω - (r : 𝓞 E) = -(A.ω - ((A.tr - r : ℤ) : 𝓞 E)) := by
          push_cast; ring
        rw [e]
        exact u.asIdeal.neg_mem h
  · intro u h
    exact ((hS _ _).1 h _ hmemq).2 hw
  · intro u u' h y hy
    rw [hadj] at hy
    rw [hCj E A u, hCj E A u']
    exact (hS _ _).1 h _ (hBar E A y hy)
  · intro s hsw u
    constructor
    · intro h
      exact ⟨((hS _ _).1 h _ hmemq).2 hw, ((hS _ _).1 h _ (hmemω s)).2 hsw⟩
    · rintro ⟨h1, h2⟩
      exact (hS _ _).2 (hKey E A q hq hnd s u w h1 hw h2 hsw)

import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

namespace UpperTheory.V.X.GaloisIndexPlaces

/- English proof (translation)
Establish `h : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.mp hl`. Rewrite using `[← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]`. Conclude with `h`.
-/
private theorem prime_p {l : ℕ} (hl : l.Prime) : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact h

private noncomputable def vQ (l : ℕ) (hl : l.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_p hl).ne_zero).mpr (prime_p hl)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_p hl).ne_zero

/- English proof (translation)
The claim follows from `Ideal.mem_span_singleton_self _`.
-/
private theorem mem_vQ (l : ℕ) (hl : l.Prime) : ((l : ℕ) : 𝓞 ℚ) ∈ (vQ l hl).asIdeal :=
  Ideal.mem_span_singleton_self _

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Establish `hle : (vQ l hl).asIdeal ≤ v.asIdeal` using `by show Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `h`. Conclude with `(vQ l hl).isMaximal.eq_of_le v.isPrime.ne_top hle`.
-/
private theorem eq_vQ (l : ℕ) (hl : l.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (h : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    vQ l hl = v := by
  apply HeightOneSpectrum.ext
  have hle : (vQ l hl).asIdeal ≤ v.asIdeal := by
    show Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≤ v.asIdeal
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h
  exact (vQ l hl).isMaximal.eq_of_le v.isPrime.ne_top hle

/- English proof (translation)
Establish `h1 : ((p : ℕ) : 𝓞 ℚ) ∈ (vQ q hq).asIdeal` using `h ▸ mem_vQ p hp`. Establish `h2 : ((q : ℕ) : 𝓞 ℚ) ∣ ((p : ℕ) : 𝓞 ℚ)` using `Ideal.mem_span_singleton.1 h1`. Establish `h3` using `map_dvd Rat.ringOfIntegersEquiv h2`. Simplify using `only [map_natCast] at h3`. Conclude with `((Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 h3)).symm`.
-/
private theorem vQ_inj {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : vQ p hp = vQ q hq) : p = q := by
  have h1 : ((p : ℕ) : 𝓞 ℚ) ∈ (vQ q hq).asIdeal := h ▸ mem_vQ p hp
  have h2 : ((q : ℕ) : 𝓞 ℚ) ∣ ((p : ℕ) : 𝓞 ℚ) := Ideal.mem_span_singleton.1 h1
  have h3 := map_dvd Rat.ringOfIntegersEquiv h2
  simp only [map_natCast] at h3
  exact ((Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 h3)).symm

/- English proof (translation)
Use `haveI : Fact l.Prime := ⟨hl⟩`. Take `⟨hne, htop, hab, -⟩` from `UpperTheory.V.Base.places ℚ Ω l A`. Establish `hAT : A ≠ ⊤`. Introduce `hT`. Conclude with `(htop hT).2 hA`.

Take `⟨v, hv⟩` from `hne hAT`. Establish `hlv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal` using `(hab v hv).mp hA`. Rewrite using `[eq_vQ l hl v hlv]`. Conclude with `hv`.
-/
private theorem isPlaceOver_vQ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) (hl : l.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) : IsPlaceOver (F := ℚ) A (vQ l hl) := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨hne, htop, hab, -⟩ := UpperTheory.V.Base.places ℚ Ω l A
  have hAT : A ≠ ⊤ := by
    intro hT
    exact (htop hT).2 hA
  obtain ⟨v, hv⟩ := hne hAT
  have hlv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := (hab v hv).mp hA
  rw [eq_vQ l hl v hlv]
  exact hv

end UpperTheory.V.X.GaloisIndexPlaces

open UpperTheory.V.X.GaloisIndexPlaces in
/- English proof (translation)
Introduce `Ω _ _ _ l SP T Q v0 pl K hD`. Establish `hex : ∃ f : ℕ → HeightOneSpectrum (𝓞 ℚ), ∀ (p : ℕ) (hp : Nat.Prime p), f p = vQ p hp` using `⟨fun p => if hp : Nat.Prime p then vQ p hp else vQ 2 Nat.prime_two, fun p hp => dif_pos hp⟩`. Take `⟨f, hf⟩` from `hex`. Establish `hpr : ∀ p, p ∈ T ∨ p ∈ Q → p.Prime` using `hD.prime`. Establish `hmemS : ∀ p, p ∈ T ∨ p ∈ Q → f p ∈ (T ∪ Q).image f`.

Introduce `p hp`. Conclude with `Finset.mem_image_of_mem f (Finset.mem_union.mpr hp)`. Establish `hfinj : ∀ p q, (p ∈ T ∨ p ∈ Q) → (q ∈ T ∨ q ∈ Q) → f p = f q → p = q`. Introduce `p q hp hq he`. Rewrite `he` using `[hf p (hpr p hp), hf q (hpr q hq)]`.

Conclude with `vQ_inj _ _ he`. Set `g : T ⊕ Q → (T ∪ Q).image f` to `fun x => match x with`. Consider the case `.inl p => ⟨f p, hmemS p (Or.inl p.2)⟩`. Consider the case `.inr q => ⟨f q, hmemS q (Or.inr q.2)⟩`. Establish `hg : Function.Bijective g`.

Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩) he <;> simp only [g, Subtype.mk.injEq] at he`. Use `hfinj a b (Or.inl ha) (Or.inl hb) he` as an intermediate fact. Substitute `this` using the available equality. Both sides reduce to the same expression.

Use `hfinj a b (Or.inl ha) (Or.inr hb) he` as an intermediate fact. Substitute `this` using the available equality. Conclude with `absurd hb (Finset.disjoint_left.mp hD.disj ha)`. Use `hfinj a b (Or.inr ha) (Or.inl hb) he` as an intermediate fact. Substitute `this` using the available equality.

Conclude with `absurd ha (Finset.disjoint_left.mp hD.disj hb)`. Use `hfinj a b (Or.inr ha) (Or.inr hb) he` as an intermediate fact. Substitute `this` using the available equality. Both sides reduce to the same expression. Introduce and unpack `⟨s, hs⟩`.

Take `⟨p, hp, rfl⟩` from `Finset.mem_image.mp hs`. Break down `Finset.mem_union.mp hp with hp | hp` into its components or cases. Conclude with `⟨.inl ⟨p, hp⟩, rfl⟩`. Conclude with `⟨.inr ⟨p, hp⟩, rfl⟩`. Use `⟨(T ∪ Q).image f, Equiv.ofBijective g hg, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `v`. Rewrite using `[hD.mem v, Finset.mem_coe, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, hpv⟩`. Use `⟨p, Finset.mem_union.mpr hp, ?_⟩` and prove the remaining obligations.

Rewrite using `[hf p (hpr p hp)]`. Conclude with `eq_vQ p _ v hpv`. Introduce and unpack `⟨p, hp, rfl⟩`. Establish `hp'` using `Finset.mem_union.mp hp`. Use `⟨p, hp', ?_⟩` and prove the remaining obligations.

Rewrite using `[hf p (hpr p hp')]`. Conclude with `mem_vQ p _`. Introduce `v hv`. Establish `hl : l ∈ T ∨ l ∈ Q` using `Or.inl hD.l_mem`. Establish `: f l = v`.

Rewrite using `[hf l (hpr l hl)]`. Conclude with `eq_vQ l _ v hv`. Rewrite using `[← this]`. Conclude with `hmemS l hl`. Introduce `p`.

Establish `hp : (p : ℕ) ∈ T ∨ (p : ℕ) ∈ Q` using `Or.inl p.2`. Use `show IsPlaceOver (pl p) (f p)`. Rewrite using `[hf p (hpr p hp)]`. Conclude with `isPlaceOver_vQ p _ (pl p) (hD.isOver p hp)`. Introduce `q`.

Establish `hq : (q : ℕ) ∈ T ∨ (q : ℕ) ∈ Q` using `Or.inr q.2`. Use `show IsPlaceOver (pl q) (f q)`. Rewrite using `[hf q (hpr q hq)]`. Conclude with `isPlaceOver_vQ q _ (pl q) (hD.isOver q hq)`.
-/
theorem UpperTheory.V.X.galIdx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (e : T ⊕ Q ≃ S), SP = S ∧ (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S) ∧ (∀ v : T, IsPlaceOver (pl v) (e (.inl v)).1) ∧ ∀ q : Q, IsPlaceOver (pl q) (e (.inr q)).1 := by
  classical
  intro Ω _ _ _ l SP T Q v0 pl K hD
  have hex : ∃ f : ℕ → HeightOneSpectrum (𝓞 ℚ), ∀ (p : ℕ) (hp : Nat.Prime p), f p = vQ p hp :=
    ⟨fun p => if hp : Nat.Prime p then vQ p hp else vQ 2 Nat.prime_two, fun p hp => dif_pos hp⟩
  obtain ⟨f, hf⟩ := hex
  have hpr : ∀ p, p ∈ T ∨ p ∈ Q → p.Prime := hD.prime
  have hmemS : ∀ p, p ∈ T ∨ p ∈ Q → f p ∈ (T ∪ Q).image f := by
    intro p hp
    exact Finset.mem_image_of_mem f (Finset.mem_union.mpr hp)
  have hfinj : ∀ p q, (p ∈ T ∨ p ∈ Q) → (q ∈ T ∨ q ∈ Q) → f p = f q → p = q := by
    intro p q hp hq he
    rw [hf p (hpr p hp), hf q (hpr q hq)] at he
    exact vQ_inj _ _ he
  let g : T ⊕ Q → (T ∪ Q).image f := fun x => match x with
    | .inl p => ⟨f p, hmemS p (Or.inl p.2)⟩
    | .inr q => ⟨f q, hmemS q (Or.inr q.2)⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩) he <;> simp only [g, Subtype.mk.injEq] at he
      · have := hfinj a b (Or.inl ha) (Or.inl hb) he
        subst this
        rfl
      · have := hfinj a b (Or.inl ha) (Or.inr hb) he
        subst this
        exact absurd hb (Finset.disjoint_left.mp hD.disj ha)
      · have := hfinj a b (Or.inr ha) (Or.inl hb) he
        subst this
        exact absurd ha (Finset.disjoint_left.mp hD.disj hb)
      · have := hfinj a b (Or.inr ha) (Or.inr hb) he
        subst this
        rfl
    · rintro ⟨s, hs⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ⟨.inl ⟨p, hp⟩, rfl⟩
      · exact ⟨.inr ⟨p, hp⟩, rfl⟩
  refine ⟨(T ∪ Q).image f, Equiv.ofBijective g hg, ?_, ?_, ?_, ?_⟩
  · ext v
    rw [hD.mem v, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, hpv⟩
      refine ⟨p, Finset.mem_union.mpr hp, ?_⟩
      rw [hf p (hpr p hp)]
      exact eq_vQ p _ v hpv
    · rintro ⟨p, hp, rfl⟩
      have hp' := Finset.mem_union.mp hp
      refine ⟨p, hp', ?_⟩
      rw [hf p (hpr p hp')]
      exact mem_vQ p _
  · intro v hv
    have hl : l ∈ T ∨ l ∈ Q := Or.inl hD.l_mem
    have : f l = v := by
      rw [hf l (hpr l hl)]
      exact eq_vQ l _ v hv
    rw [← this]
    exact hmemS l hl
  · intro p
    have hp : (p : ℕ) ∈ T ∨ (p : ℕ) ∈ Q := Or.inl p.2
    show IsPlaceOver (pl p) (f p)
    rw [hf p (hpr p hp)]
    exact isPlaceOver_vQ p _ (pl p) (hD.isOver p hp)
  · intro q
    have hq : (q : ℕ) ∈ T ∨ (q : ℕ) ∈ Q := Or.inr q.2
    show IsPlaceOver (pl q) (f q)
    rw [hf q (hpr q hq)]
    exact isPlaceOver_vQ q _ (pl q) (hD.isOver q hq)

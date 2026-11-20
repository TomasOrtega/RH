import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Use extensionality with `g`. Establish `hg` using `congrArg (fun ψ : DirichletCharacter O N => ψ ((UpperTheory.V.Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N)) h`. Simplify using `only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hg`. Simplify using `[UpperTheory.V.Chr.dirG, hg]`.
-/
private theorem dirG_pow_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) {m : ℕ} (h : χ ^ m = 1) : UpperTheory.V.Chr.dirG ℚ Ω χ ^ m = 1 := by
  ext g
  have hg := congrArg (fun ψ : DirichletCharacter O N => ψ ((UpperTheory.V.Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N)) h
  simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hg
  simp [UpperTheory.V.Chr.dirG, hg]

/- English proof (translation)
Establish `hnot : ¬ A.valuation (N : Ω) < 1`. Introduce `hNv`. Establish `hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1` using `fun z => A.valuation_le_one (⟨z, by simp⟩ : A)`. Establish `hgcd` using `Nat.gcd_eq_gcd_ab v N`. Rewrite `hgcd` using `[hN]`.

Establish `h1 : ((1 : ℤ) : Ω) = (v : Ω) * (v.gcdA N : Ω) + (N : Ω) * (v.gcdB N : Ω)`. Conclude with `hgcd` after adjusting the coercions. Establish `hlt : A.valuation ((v : Ω) * (v.gcdA N : Ω) + (N : Ω) * (v.gcdB N : Ω)) < 1`. Apply `Valuation.map_add_lt` to reduce the goal to its premises. Rewrite using `[map_mul]`.

Conclude with `mul_lt_one_of_lt_of_le hA (hint _)`. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_lt_of_le hNv (hint _)`. Rewrite `hlt` using `[← h1]`. Simplify using `at hlt`.

Establish `hker` using `(UpperTheory.V.Chr.clsFacts ℚ Ω N).2.2.2.2 A hnot hg`. Rewrite `hker` using `[MonoidHom.mem_ker]`. Simplify using `[UpperTheory.V.Chr.dirG, hker]`.
-/
private theorem dirG_unr {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) {A : ValuationSubring Ω} {v : ℕ} (hA : A.valuation (v : Ω) < 1) (hN : v.Coprime N)
    {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) : UpperTheory.V.Chr.dirG ℚ Ω χ g = 1 := by
  have hnot : ¬ A.valuation (N : Ω) < 1 := by
    intro hNv
    have hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => A.valuation_le_one (⟨z, by simp⟩ : A)
    have hgcd := Nat.gcd_eq_gcd_ab v N
    rw [hN] at hgcd
    have h1 : ((1 : ℤ) : Ω) = (v : Ω) * (v.gcdA N : Ω) + (N : Ω) * (v.gcdB N : Ω) := by
      exact_mod_cast hgcd
    have hlt : A.valuation ((v : Ω) * (v.gcdA N : Ω) + (N : Ω) * (v.gcdB N : Ω)) < 1 := by
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hA (hint _)
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le hNv (hint _)
    rw [← h1] at hlt
    simp at hlt
  have hker := (UpperTheory.V.Chr.clsFacts ℚ Ω N).2.2.2.2 A hnot hg
  rw [MonoidHom.mem_ker] at hker
  simp [UpperTheory.V.Chr.dirG, hker]

/- English proof (translation)
Introduce `hdvd`. Use `haveI : NeZero m := ⟨hm⟩`. Establish `hle : H.map φ ≤ rootsOfUnity m O`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Rewrite using `[mem_rootsOfUnity]`.

Use `congrArg (fun f => f x) h` as an intermediate fact. Simplify `this` using `[MonoidHom.pow_apply]`. Use `haveI : Finite (H.map φ) := Finite.of_injective _ (Subgroup.inclusion_injective hle)`. Take `⟨y, hy⟩` from `exists_prime_orderOf_dvd_card' (G := H.map φ) l hdvd`. Establish `hym : orderOf y ∣ m`.

Apply `orderOf_dvd_of_pow_eq_one` to reduce the goal to its premises. Take `⟨x, -, hx⟩` from `y.2`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (fun f => f x) h` as an intermediate fact. Simplify using `only [MonoidHom.pow_apply, MonoidHom.one_apply] at this`.

Simplify using `[← hx, this]`. Rewrite `hym` using `[hy]`. Use `Nat.Coprime.eq_one_of_dvd hl hym` as an intermediate fact. Conclude with `(Fact.out : l.Prime).one_lt.ne' this`.
-/
private theorem not_dvd_card {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] (φ : Γ →* Oˣ) {m l : ℕ} [Fact l.Prime]
    (hm : m ≠ 0) (hl : l.Coprime m) (h : φ ^ m = 1) (H : Subgroup Γ) : ¬ l ∣ Nat.card (H.map φ) := by
  intro hdvd
  haveI : NeZero m := ⟨hm⟩
  have hle : H.map φ ≤ rootsOfUnity m O := by
    rintro _ ⟨x, -, rfl⟩
    rw [mem_rootsOfUnity]
    have := congrArg (fun f => f x) h
    simpa [MonoidHom.pow_apply] using this
  haveI : Finite (H.map φ) := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H.map φ) l hdvd
  have hym : orderOf y ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    obtain ⟨x, -, hx⟩ := y.2
    apply Subtype.ext
    have := congrArg (fun f => f x) h
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    simp [← hx, this]
  rw [hy] at hym
  have := Nat.Coprime.eq_one_of_dvd hl hym
  exact (Fact.out : l.Prime).one_lt.ne' this

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D h3`. Take `⟨hG, h, t, e, ψ, hBig, he0, het, hX, hIII, hA⟩` from `h3`. Take `⟨he, hψ, hS, hx⟩` from `hA`. Take `⟨_, ξ', ξ₀, -, -, -, hξ⟩` from `hx`. Take `⟨hlB, hle, hodd, -⟩` from `hIII`.

Establish `hlp : l.Prime` using `Fact.out`. Establish `hl2 : l ≠ 2` using `hG.l_odd`. Take `⟨-, -, -, -, hB⟩` from `bchiFacts h t hBig`. Take `⟨h5, hno, -, -, -, hl1, -, hfin⟩` from `hB l hlp hl2 hlB`. Establish `hlN : ¬ l ∣ h.N` using `(hfin e he0 het hle).2.2`.

Establish `hchar` using `((Host.mem_X h).1 hX).1`. Establish `hdo` using `((hostOdd h c.O ψ hchar).1 hodd).1`. Establish `hcop : l.Coprime (orderOf ψ)`. Rewrite using `[Nat.Prime.coprime_iff_not_dvd hlp]`. Introduce `hd`.

Conclude with `hno (hd.trans (hdo.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd _ _))))`. Establish `hpow : D.ψ ^ orderOf ψ = 1`. Rewrite using `[hψ]`. Conclude with `dirG_pow_one ψ (pow_orderOf_eq_one ψ)`. Establish `hm0 : orderOf ψ ≠ 0`.

Introduce `h0`. Rewrite `hodd` using `[h0]`. Conclude with `Nat.not_odd_zero hodd`. Use `⟨h5, he ▸ hle, ?_, ⟨orderOf ψ, hodd, hcop, hpow⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[GradeZeroInterpolatingElement.Raw.Sb, Finset.filter_eq_empty_iff]`.

Introduce and unpack `p - ⟨-, hd⟩`. Conclude with `not_dvd_card D.ψ hm0 hcop hpow _ hd`. Introduce `A hA g hg`. Establish `hcN : l.Coprime h.N` using `(Nat.Prime.coprime_iff_not_dvd hlp).2 hlN`. Establish `hc1 : l.Coprime (UpperTheory.V.pOne h.chi)` using `(Nat.coprime_primes hlp (UpperTheory.V.pK_pOne_prime_conditions h.chi).2.1.1).2 hl1`.

Establish `hc2 : l.Coprime (2 ^ h.nIII l ψ)` using `Nat.Coprime.pow_right _ ((Nat.coprime_primes hlp Nat.prime_two).2 hl2)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show g ∈ D.ξ.ker`. Rewrite using `[MonoidHom.mem_ker, hξ, MonoidHom.mul_apply, dirG_unr ξ₀ hA hc1 hg, dirG_unr ξ' hA hc2 hg, mul_one]`. Use `show g ∈ D.ψ.ker`.

Rewrite using `[MonoidHom.mem_ker, hψ, dirG_unr ψ hA hcN hg]`.
-/
theorem UpperTheory.V.Ws.large₂.host3 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D → 5 ≤ l ∧ l - 1 ∣ 2 * D.e ∧ D.Sb = ∅ ∧ (∃ m : ℕ, Odd m ∧ l.Coprime m ∧ D.ψ ^ m = 1) ∧
      ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ D.ξ.ker ⊓ D.ψ.ker := by
  intro Ω _ _ _ l _ c D h3
  obtain ⟨hG, h, t, e, ψ, hBig, he0, het, hX, hIII, hA⟩ := h3
  obtain ⟨he, hψ, hS, hx⟩ := hA
  obtain ⟨_, ξ', ξ₀, -, -, -, hξ⟩ := hx
  obtain ⟨hlB, hle, hodd, -⟩ := hIII
  have hlp : l.Prime := Fact.out
  have hl2 : l ≠ 2 := hG.l_odd
  obtain ⟨-, -, -, -, hB⟩ := bchiFacts h t hBig
  obtain ⟨h5, hno, -, -, -, hl1, -, hfin⟩ := hB l hlp hl2 hlB
  have hlN : ¬ l ∣ h.N := (hfin e he0 het hle).2.2
  have hchar := ((Host.mem_X h).1 hX).1
  have hdo := ((hostOdd h c.O ψ hchar).1 hodd).1
  have hcop : l.Coprime (orderOf ψ) := by
    rw [Nat.Prime.coprime_iff_not_dvd hlp]
    intro hd
    exact hno (hd.trans (hdo.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd _ _))))
  have hpow : D.ψ ^ orderOf ψ = 1 := by
    rw [hψ]; exact dirG_pow_one ψ (pow_orderOf_eq_one ψ)
  have hm0 : orderOf ψ ≠ 0 := by
    intro h0; rw [h0] at hodd; exact Nat.not_odd_zero hodd
  refine ⟨h5, he ▸ hle, ?_, ⟨orderOf ψ, hodd, hcop, hpow⟩, ?_⟩
  · rw [GradeZeroInterpolatingElement.Raw.Sb, Finset.filter_eq_empty_iff]
    rintro p - ⟨-, hd⟩
    exact not_dvd_card D.ψ hm0 hcop hpow _ hd
  · intro A hA g hg
    have hcN : l.Coprime h.N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
    have hc1 : l.Coprime (UpperTheory.V.pOne h.chi) :=
      (Nat.coprime_primes hlp (UpperTheory.V.pK_pOne_prime_conditions h.chi).2.1.1).2 hl1
    have hc2 : l.Coprime (2 ^ h.nIII l ψ) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hlp Nat.prime_two).2 hl2)
    refine ⟨?_, ?_⟩
    · show g ∈ D.ξ.ker
      rw [MonoidHom.mem_ker, hξ, MonoidHom.mul_apply, dirG_unr ξ₀ hA hc1 hg, dirG_unr ξ' hA hc2 hg, mul_one]
    · show g ∈ D.ψ.ker
      rw [MonoidHom.mem_ker, hψ, dirG_unr ψ hA hcN hg]

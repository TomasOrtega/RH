import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwRamSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff

open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Use `haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `set L : IntermediateField ℚ Ω := IntermediateField.fixedField V with hLdef`. Establish `hVc : IsClosed (V : Set (G ℚ Ω))` using `Subgroup.isClosed_of_isOpen V hV`. Establish `hLV : L.fixingSubgroup = V` using `InfiniteGalois.fixingSubgroup_fixedField ⟨V, hVc⟩`.

Use `haveI : FiniteDimensional ℚ L := by`. Rewrite using `[← InfiniteGalois.isOpen_iff_finite]`. Rewrite using `[hLV]`. Conclude with `hV`. Establish `hVn : V.Normal`.

Prove the components needed by the constructor for the conclusion. Introduce `v hv g`. Establish `hcm : g * v * g⁻¹ * v⁻¹ ∈ V` using `hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top v))`. Establish `: g * v * g⁻¹ = (g * v * g⁻¹ * v⁻¹) * v` using `by group`. Rewrite using `[this]`.

Conclude with `V.mul_mem hcm hv`. Use `haveI : IsGalois ℚ L := by`. Use `(InfiniteGalois.normal_iff_isGalois L).1 (by rw [hLV]; exact hVn)` as an intermediate fact. Use `this` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`.

Establish `hres : ∀ σ : G ℚ Ω, resTo ℚ L Ω σ = 1 ↔ σ ∈ V`. Introduce `σ`. Rewrite using `[← hLV, IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`.

Use `resTo_commutes ℚ L Ω σ ⟨x, hx⟩` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `using this.symm`. Introduce `h`. Use extensionality with `x`.

Use `resTo_commutes ℚ L Ω σ x` as an intermediate fact. Establish `h2 : σ (algebraMap L Ω x) = algebraMap L Ω x` using `h x.1 x.2`. Rewrite `this` using `[h2]`. Simplify using `using this`. Use `haveI : IsMulCommutative Gal(L/ℚ) := by`.

Use `⟨⟨fun a b => ?_⟩⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `resTo_surjective ℚ L Ω a`. Take `⟨h, rfl⟩` from `resTo_surjective ℚ L Ω b`. Establish `hcm : g * h * g⁻¹ * h⁻¹ ∈ V` using `hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))`. Establish `h1` using `(hres _).2 hcm`.

Simplify using `only [map_mul, map_inv] at h1`. Use `show resTo ℚ L Ω g * resTo ℚ L Ω h = resTo ℚ L Ω h * resTo ℚ L Ω g`. Combine the equalities or inequalities in the displayed calculation. Use `haveI : IsAbelianGalois ℚ L := ⟨⟩`. Establish `hunr : ∀ p : ℕ, Nat.Prime p → ¬ p ∣ M → UnramAt L p`.

Introduce `p hp hpM`. Rewrite using `[(unramIff.1 L p hp)]`. Introduce `w hpw`. Take `⟨A, hA⟩` from `exists_isPlaceOver (F := L) Ω w`. Rewrite using `[← ineAbs ℚ L Ω A w hA]`.

Establish `hAV : Ine (F` using `ℚ) A ≤ V := by`. Apply `hI` to reduce the goal to its premises. Introduce `hlt`. Establish `hMw : ((M : 𝓞 L)) ∈ w.asIdeal`. Rewrite using `[← hA]`.

Simplify using `using hlt`. Establish `hcop : Nat.Coprime p M` using `(Nat.Prime.coprime_iff_not_dvd hp).2 hpM`. Establish `h1 : (1 : 𝓞 L) ∈ w.asIdeal`. Use `Nat.gcd_eq_gcd_ab p M` as an intermediate fact. Rewrite `this` using `[hcop]`.

Establish `e : ((1 : ℤ) : 𝓞 L) = ((p : ℤ) : 𝓞 L) * ((Nat.gcdA p M : ℤ) : 𝓞 L) + ((M : ℤ) : 𝓞 L) * ((Nat.gcdB p M : ℤ) : 𝓞 L)`. Rewrite using `[← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add]`. Use `congr 1`. Simplify using `only [Int.cast_one, Int.cast_natCast] at e`. Rewrite using `[e]`.

Conclude with `w.asIdeal.add_mem (w.asIdeal.mul_mem_right _ hpw) (w.asIdeal.mul_mem_right _ hMw)`. Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `x ⟨y, hy, rfl⟩`. Conclude with `(hres y).2 (hAV hy)`.

Take `⟨n, ζ, hζ, hLζ⟩` from `kwRamSub Ω L M hM hunr`. Use `⟨n, fun g hg => ?_⟩` and prove the remaining obligations. Set `S : Subgroup (G ℚ Ω)` to `MulAction.stabilizer (G ℚ Ω) ζ`. Establish `hζS : ζ ∈ IntermediateField.fixedField S`. Rewrite using `[IntermediateField.mem_fixedField_iff]`.

Introduce `f hf`. Conclude with `hf`. Establish `hLS : L ≤ IntermediateField.fixedField S` using `hLζ.trans (IntermediateField.adjoin_simple_le_iff.2 hζS)`. Establish `hgS : g ∈ S` using `hg ζ hζ.pow_eq_one`. Rewrite using `[← hLV]`.

Conclude with `(IntermediateField.le_iff_le S L).1 hLS hgS`.
-/
private theorem abelian_ramification_cyclotomic_bound (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (V : Subgroup (G ℚ Ω))
    (hV : IsOpen (V : Set (G ℚ Ω))) (hc : commutator (G ℚ Ω) ≤ V) (M : ℕ) (hM : 0 < M)
    (hI : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ V) :
    ∃ n : ℕ, ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ M ^ n = 1 → g ζ = ζ) → g ∈ V := by
  classical
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  set L : IntermediateField ℚ Ω := IntermediateField.fixedField V with hLdef
  have hVc : IsClosed (V : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen V hV
  have hLV : L.fixingSubgroup = V :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨V, hVc⟩
  haveI : FiniteDimensional ℚ L := by
    rw [← InfiniteGalois.isOpen_iff_finite]
    rw [hLV]
    exact hV
  have hVn : V.Normal := by
    constructor
    intro v hv g
    have hcm : g * v * g⁻¹ * v⁻¹ ∈ V :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top v))
    have : g * v * g⁻¹ = (g * v * g⁻¹ * v⁻¹) * v := by group
    rw [this]
    exact V.mul_mem hcm hv
  haveI : IsGalois ℚ L := by
    have := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hLV]; exact hVn)
    convert this
    exact Subsingleton.elim _ _
  have hres : ∀ σ : G ℚ Ω, resTo ℚ L Ω σ = 1 ↔ σ ∈ V := by
    intro σ
    rw [← hLV, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have := resTo_commutes ℚ L Ω σ ⟨x, hx⟩
      rw [h] at this
      simpa using this.symm
    · intro h
      ext x
      have := resTo_commutes ℚ L Ω σ x
      have h2 : σ (algebraMap L Ω x) = algebraMap L Ω x := h x.1 x.2
      rw [h2] at this
      simpa using this
  haveI : IsMulCommutative Gal(L/ℚ) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨g, rfl⟩ := resTo_surjective ℚ L Ω a
    obtain ⟨h, rfl⟩ := resTo_surjective ℚ L Ω b
    have hcm : g * h * g⁻¹ * h⁻¹ ∈ V :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
    have h1 := (hres _).2 hcm
    simp only [map_mul, map_inv] at h1
    show resTo ℚ L Ω g * resTo ℚ L Ω h = resTo ℚ L Ω h * resTo ℚ L Ω g
    calc resTo ℚ L Ω g * resTo ℚ L Ω h
        = (resTo ℚ L Ω g * resTo ℚ L Ω h * (resTo ℚ L Ω g)⁻¹ * (resTo ℚ L Ω h)⁻¹) *
            (resTo ℚ L Ω h * resTo ℚ L Ω g) := by group
      _ = resTo ℚ L Ω h * resTo ℚ L Ω g := by rw [h1, one_mul]
  haveI : IsAbelianGalois ℚ L := ⟨⟩
  have hunr : ∀ p : ℕ, Nat.Prime p → ¬ p ∣ M → UnramAt L p := by
    intro p hp hpM
    rw [(unramIff.1 L p hp)]
    intro w hpw
    obtain ⟨A, hA⟩ := exists_isPlaceOver (F := L) Ω w
    rw [← ineAbs ℚ L Ω A w hA]
    have hAV : Ine (F := ℚ) A ≤ V := by
      apply hI
      intro hlt
      have hMw : ((M : 𝓞 L)) ∈ w.asIdeal := by
        rw [← hA]
        simpa using hlt
      have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).2 hpM
      have h1 : (1 : 𝓞 L) ∈ w.asIdeal := by
        have := Nat.gcd_eq_gcd_ab p M
        rw [hcop] at this
        have e : ((1 : ℤ) : 𝓞 L) = ((p : ℤ) : 𝓞 L) * ((Nat.gcdA p M : ℤ) : 𝓞 L)
            + ((M : ℤ) : 𝓞 L) * ((Nat.gcdB p M : ℤ) : 𝓞 L) := by
          rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add]
          congr 1
        simp only [Int.cast_one, Int.cast_natCast] at e
        rw [e]
        exact w.asIdeal.add_mem (w.asIdeal.mul_mem_right _ hpw) (w.asIdeal.mul_mem_right _ hMw)
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    rw [eq_bot_iff]
    rintro x ⟨y, hy, rfl⟩
    exact (hres y).2 (hAV hy)
  obtain ⟨n, ζ, hζ, hLζ⟩ := kwRamSub Ω L M hM hunr
  refine ⟨n, fun g hg => ?_⟩
  let S : Subgroup (G ℚ Ω) := MulAction.stabilizer (G ℚ Ω) ζ
  have hζS : ζ ∈ IntermediateField.fixedField S := by
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    exact hf
  have hLS : L ≤ IntermediateField.fixedField S :=
    hLζ.trans (IntermediateField.adjoin_simple_le_iff.2 hζS)
  have hgS : g ∈ S := hg ζ hζ.pow_eq_one
  rw [← hLV]
  exact (IntermediateField.le_iff_le S L).1 hLS hgS

/- English proof (translation)
Introduce `Ω _ alg _ V hV hc M hM hI`. Establish `hch : CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Take `rfl : alg = DivisionRing.toRatAlgebra` from `Subsingleton.elim _ _`. Conclude with `abelian_ramification_cyclotomic_bound Ω V hV hc M hM hI`.
-/
theorem UpperTheory.V.CF.kwAbsRam :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (V : Subgroup (G ℚ Ω)), IsOpen (V : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ V → ∀ M : ℕ, 0 < M → (∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ V) → ∃ n : ℕ, ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ M ^ n = 1 → g ζ = ζ) → g ∈ V := by
  intro Ω _ alg _ V hV hc M hM hI
  have hch : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : alg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact abelian_ramification_cyclotomic_bound Ω V hV hc M hM hI

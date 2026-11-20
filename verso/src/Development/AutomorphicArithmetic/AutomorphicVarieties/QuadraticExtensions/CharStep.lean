import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.TameGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Introduce `hl`. Establish `hg` using `Nat.gcd_eq_gcd_ab p l`. Rewrite `hg` using `[h.gcd_eq_one]`. Establish `hΩ : (1 : Ω) = (p : Ω) * ((p.gcdA l : ℤ) : Ω) + (l : Ω) * ((p.gcdB l : ℤ) : Ω)`. Use `congrArg (fun z : ℤ => (z : Ω)) hg` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1` using `fun z => by`. Simplify using `using A.valuation_le_one (z : A)`. Establish `h1 : A.valuation ((p : Ω) * ((p.gcdA l : ℤ) : Ω)) < 1`.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hp`. Establish `h2 : A.valuation ((l : Ω) * ((p.gcdB l : ℤ) : Ω)) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hl`.

Establish `h3` using `Valuation.map_add_lt A.valuation h1 h2`. Rewrite `h3` using `[← hΩ, map_one]`. Conclude with `lt_irrefl _ h3`.
-/
private theorem not_valuation_lt_one_of_coprime_of_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p l : ℕ}
    (h : p.Coprime l) (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (l : Ω) < 1 := by
  intro hl
  have hg := Nat.gcd_eq_gcd_ab p l
  rw [h.gcd_eq_one] at hg
  have hΩ : (1 : Ω) = (p : Ω) * ((p.gcdA l : ℤ) : Ω) + (l : Ω) * ((p.gcdB l : ℤ) : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hg
    push_cast at this
    exact this
  have hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => by
    simpa using A.valuation_le_one (z : A)
  have h1 : A.valuation ((p : Ω) * ((p.gcdA l : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hp
  have h2 : A.valuation ((l : Ω) * ((p.gcdB l : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hl
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [← hΩ, map_one] at h3
  exact lt_irrefl _ h3

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ V N p n k hcop hT hV hN`. Use `haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩`. Take `⟨T, hTc, hTp, hTcov⟩` from `hT`. Establish `hl : ∀ B ∈ T, ¬ B.valuation (l : Ω) < 1` using `fun B hB => not_valuation_lt_one_of_coprime_of_lt_one B hcop (hTp B hB)`. Use `choose γ hγ using fun B : {B // B ∈ T} => tameGen F Ω l B.1 (hl B.1 B.2)`.

Set `L : CharOff V (ineOff F Ω (N * p)) l → ({B // B ∈ T} → ZMod l)` to `fun φ B => (φ : V → ZMod l) ⟨(γ B : G F Ω), hV B.1 (hTp B.1 B.2) (γ B).2⟩`. Establish `key : ∀ φ ψ : CharOff V (ineOff F Ω (N * p)) l, L φ = L ψ → ((φ : V → ZMod l) - (ψ : V → ZMod l)) ∈ CharOff V (ineOff F Ω N) l`. Introduce `φ ψ h`. Set `χ : V → ZMod l` to `(φ : V → ZMod l) - (ψ : V → ZMod l)`. Establish `hm : IsLocallyConstant χ ∧ (∀ a b : V, χ (a * b) = χ a + χ b) ∧ ∀ u : V, (u : G F Ω) ∈ ineOff F Ω (N * p) → χ u = 0` using `(φ - ψ).2`.

Take `⟨hlc, hadd, hoff⟩` from `hm`. Express the relevant statement in the definitionally equal form `IsLocallyConstant χ ∧ (∀ a b : V, χ (a * b) = χ a + χ b) ∧ ∀ u : V, (u : G F Ω) ∈ ineOff F Ω N → χ u = 0`. Use `⟨hlc, hadd, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨A, hAN, huA⟩` from `hu`. Distinguish the cases in `hAp : A.valuation (p : Ω) < 1`.

Take `⟨B, hB, v, hv, rfl⟩` from `hTcov A hAp`. Establish `hg : v⁻¹ * (u : G F Ω) * v ∈ Ine B` using `(ineConj F Ω v).1 B u huA`. Establish `hBV : Ine (F` using `F) B ≤ V := hV B (hTp B hB)`. Set `Bt : {B // B ∈ T}` to `⟨B, hB⟩`. Set `ι : Ine (F` to `F) B → V := fun σ => ⟨(σ : G F Ω), hBV σ.2⟩`.

Establish `hι : ∀ a b : Ine (F` using `F) B, ι (a * b) = ι a * ι b := fun a b => rfl`. Set `χ' : Ine (F` to `F) B → ZMod l := fun σ => χ (ι σ)`. Establish `hcont : Continuous ι` using `Continuous.subtype_mk continuous_subtype_val _`. Establish `hχlc : IsLocallyConstant χ'` using `hlc.comp_continuous hcont`. Establish `hχadd : ∀ a b : Ine (F` using `F) B, χ' (a * b) = χ' a + χ' b := by`.

Introduce `a b`. Use `show χ (ι (a * b)) = χ (ι a) + χ (ι b)`. Rewrite using `[hι]`. Conclude with `hadd _ _`. Establish `hχγ : χ' (γ Bt) = 0`.

Use `congrFun h Bt` as an intermediate fact. Conclude with `sub_eq_zero.mpr this`. Establish `h0` using `hγ Bt χ' hχlc hχadd hχγ ⟨_, hg⟩`. Set `v' : V` to `⟨v, hv⟩`. Establish `e3 : χ (v'⁻¹ * u * v') = 0` using `h0`.

Establish `e1 : χ (v'⁻¹ * u * v') = χ v'⁻¹ + χ u + χ v'`. Rewrite using `[hadd, hadd]`. Establish `h1 : χ 1 = 0`. Use `hadd 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Take the linear combination `-this`. Establish `e2 : χ v'⁻¹ + χ v' = 0`. Rewrite using `[← hadd, inv_mul_cancel, h1]`. Take the linear combination `e3 - e1 - e2`. Apply `hoff u` to reduce the goal to its premises.

Use `⟨A, ?_, huA⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[map_mul]`. Introduce `hlt`. Conclude with `(not_lt.mpr (one_le_mul (not_lt.mp hAN) (not_lt.mp hAp))) hlt`.

Use `haveI : Nonempty (CharOff V (ineOff F Ω (N * p)) l) := ⟨0⟩`. Set `s` to `Function.invFun L`. Establish `hs : ∀ φ, L (s (L φ)) = L φ` using `fun φ => Function.invFun_eq ⟨φ, rfl⟩`. Set `f : CharOff V (ineOff F Ω (N * p)) l → ({B // B ∈ T} → ZMod l) × CharOff V (ineOff F Ω N) l` to `fun φ => (L φ, ⟨(φ : V → ZMod l) - (s (L φ) : V → ZMod l), key φ (s (L φ)) (hs φ).symm⟩)`. Establish `hf : Function.Injective f`.

Introduce `φ ψ hfe`. Establish `h1 : L φ = L ψ` using `congrArg Prod.fst hfe`. Establish `h2` using `congrArg (fun x => ((x.2 : CharOff V (ineOff F Ω N) l) : V → ZMod l)) hfe`. Simplify using `only [f] at h2`. Rewrite `h2` using `[h1]`.

Conclude with `Subtype.ext (sub_left_inj.mp h2)`. Use `haveI : Finite (CharOff V (ineOff F Ω N) l) := hN.1`. Use `⟨Finite.of_injective f hf, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.card_prod, Nat.card_fun, Nat.card_zmod]`.

Simplify using the standard rewrite rules. Use `_ ≤ l ^ k * n := Nat.mul_le_mul (Nat.pow_le_pow_right (Fact.out : l.Prime).pos hTc) hN.2`. Use `_ = n * l ^ k := Nat.mul_comm _ _`.
-/
theorem UpperTheory.V.Two.charStep :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (V : Subgroup (G F Ω)) (N p n k : ℕ), p.Coprime l → OrbLe V p k → (∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Ine (F := F) A ≤ V) →
      CardLe (CharOff V (ineOff F Ω N) l) n → CardLe (CharOff V (ineOff F Ω (N * p)) l) (n * l ^ k) := by
  intro F Ω _ _ _ _ _ l _ V N p n k hcop hT hV hN
  classical
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨T, hTc, hTp, hTcov⟩ := hT
  have hl : ∀ B ∈ T, ¬ B.valuation (l : Ω) < 1 := fun B hB => not_valuation_lt_one_of_coprime_of_lt_one B hcop (hTp B hB)
  choose γ hγ using fun B : {B // B ∈ T} => tameGen F Ω l B.1 (hl B.1 B.2)
  let L : CharOff V (ineOff F Ω (N * p)) l → ({B // B ∈ T} → ZMod l) := fun φ B =>
    (φ : V → ZMod l) ⟨(γ B : G F Ω), hV B.1 (hTp B.1 B.2) (γ B).2⟩
  have key : ∀ φ ψ : CharOff V (ineOff F Ω (N * p)) l, L φ = L ψ →
      ((φ : V → ZMod l) - (ψ : V → ZMod l)) ∈ CharOff V (ineOff F Ω N) l := by
    intro φ ψ h
    let χ : V → ZMod l := (φ : V → ZMod l) - (ψ : V → ZMod l)
    have hm : IsLocallyConstant χ ∧ (∀ a b : V, χ (a * b) = χ a + χ b) ∧
        ∀ u : V, (u : G F Ω) ∈ ineOff F Ω (N * p) → χ u = 0 := (φ - ψ).2
    obtain ⟨hlc, hadd, hoff⟩ := hm
    change IsLocallyConstant χ ∧ (∀ a b : V, χ (a * b) = χ a + χ b) ∧
        ∀ u : V, (u : G F Ω) ∈ ineOff F Ω N → χ u = 0
    refine ⟨hlc, hadd, fun u hu => ?_⟩
    obtain ⟨A, hAN, huA⟩ := hu
    by_cases hAp : A.valuation (p : Ω) < 1
    · obtain ⟨B, hB, v, hv, rfl⟩ := hTcov A hAp
      have hg : v⁻¹ * (u : G F Ω) * v ∈ Ine B := (ineConj F Ω v).1 B u huA
      have hBV : Ine (F := F) B ≤ V := hV B (hTp B hB)
      let Bt : {B // B ∈ T} := ⟨B, hB⟩
      let ι : Ine (F := F) B → V := fun σ => ⟨(σ : G F Ω), hBV σ.2⟩
      have hι : ∀ a b : Ine (F := F) B, ι (a * b) = ι a * ι b := fun a b => rfl
      let χ' : Ine (F := F) B → ZMod l := fun σ => χ (ι σ)
      have hcont : Continuous ι := Continuous.subtype_mk continuous_subtype_val _
      have hχlc : IsLocallyConstant χ' := hlc.comp_continuous hcont
      have hχadd : ∀ a b : Ine (F := F) B, χ' (a * b) = χ' a + χ' b := by
        intro a b
        show χ (ι (a * b)) = χ (ι a) + χ (ι b)
        rw [hι]
        exact hadd _ _
      have hχγ : χ' (γ Bt) = 0 := by
        have := congrFun h Bt
        exact sub_eq_zero.mpr this
      have h0 := hγ Bt χ' hχlc hχadd hχγ ⟨_, hg⟩
      let v' : V := ⟨v, hv⟩
      have e3 : χ (v'⁻¹ * u * v') = 0 := h0
      have e1 : χ (v'⁻¹ * u * v') = χ v'⁻¹ + χ u + χ v' := by
        rw [hadd, hadd]
      have h1 : χ 1 = 0 := by
        have := hadd 1 1
        rw [mul_one] at this
        linear_combination -this
      have e2 : χ v'⁻¹ + χ v' = 0 := by
        rw [← hadd, inv_mul_cancel, h1]
      linear_combination e3 - e1 - e2
    · apply hoff u
      refine ⟨A, ?_, huA⟩
      push_cast
      rw [map_mul]
      intro hlt
      exact (not_lt.mpr (one_le_mul (not_lt.mp hAN) (not_lt.mp hAp))) hlt
  haveI : Nonempty (CharOff V (ineOff F Ω (N * p)) l) := ⟨0⟩
  let s := Function.invFun L
  have hs : ∀ φ, L (s (L φ)) = L φ := fun φ => Function.invFun_eq ⟨φ, rfl⟩
  let f : CharOff V (ineOff F Ω (N * p)) l → ({B // B ∈ T} → ZMod l) × CharOff V (ineOff F Ω N) l :=
    fun φ => (L φ, ⟨(φ : V → ZMod l) - (s (L φ) : V → ZMod l), key φ (s (L φ)) (hs φ).symm⟩)
  have hf : Function.Injective f := by
    intro φ ψ hfe
    have h1 : L φ = L ψ := congrArg Prod.fst hfe
    have h2 := congrArg (fun x => ((x.2 : CharOff V (ineOff F Ω N) l) : V → ZMod l)) hfe
    simp only [f] at h2
    rw [h1] at h2
    exact Subtype.ext (sub_left_inj.mp h2)
  haveI : Finite (CharOff V (ineOff F Ω N) l) := hN.1
  refine ⟨Finite.of_injective f hf, ?_⟩
  calc Nat.card (CharOff V (ineOff F Ω (N * p)) l)
      ≤ Nat.card (({B // B ∈ T} → ZMod l) × CharOff V (ineOff F Ω N) l) :=
        Nat.card_le_card_of_injective f hf
    _ = l ^ T.card * Nat.card (CharOff V (ineOff F Ω N) l) := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod]
        simp
    _ ≤ l ^ k * n := Nat.mul_le_mul (Nat.pow_le_pow_right (Fact.out : l.Prime).pos hTc) hN.2
    _ = n * l ^ k := Nat.mul_comm _ _

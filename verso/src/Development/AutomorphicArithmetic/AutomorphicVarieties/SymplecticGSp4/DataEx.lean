import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ReFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcXvan
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcPrimProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcOmDir
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDirVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Th1Facts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PsiBar
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostSb
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsPrimitiveOddDirichletCharacterTwoPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsDirichletCharacterPrimeOfOrderOfDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoPowLtSqMulOfPrimitiveCharPowEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsPrimitiveTwoPowTwistMul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Take `⟨f₁, φ₁, p1, d1, t1, v1⟩` from `X.primProd O l N ω θ`. Establish `hcN : θ.conductor ∣ N` using `θ.conductor_dvd_level`. Establish `d1' : f₁ ∣ l * N` using `d1.trans (Nat.mul_dvd_mul_left l hcN)`. Use `haveI : NeZero f₁ := ⟨fun h0 => mul_ne_zero (NeZero.ne l) (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ d1'))⟩`. Take `⟨f, φ, p2, d2, t2, v2⟩` from `X.primProd O p f₁ ξ₀ φ₁`.

Rewrite `d2` using `[show φ₁.conductor = f₁ from p1]`. Take `⟨ξ₁, p3, v3⟩` from `UpperTheory.exists_primitive_two_pow_twist_mul O N χ c n hc hcn ξ hξ`. Establish `d3 : f ∣ p * l * θ.conductor` using `by rw [mul_assoc]; exact d2.trans (Nat.mul_dvd_mul_left p d1)`. Establish `d4 : f ∣ p * l * N` using `d3.trans (Nat.mul_dvd_mul_left _ hcN)`. Establish `hodd : Odd (p * l * θ.conductor)` using `(hp.mul hl).mul hθ`.

Establish `h2n : 2 ∣ 2 ^ n` using `dvd_pow_self 2 (by omega)`. Establish `hv : ∀ a : ℤ, IsCoprime a (p * l * N * 2 ^ n : ℕ) → φ a * ξ₁ a = ω a * (χ a * θ a) * (ξ₀ a * ξ a)` using `fun a ha => by`. Establish `c1 : ∀ m : ℕ, m ∣ p * l * N * 2 ^ n → IsCoprime a m` using `fun m hm => ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hm)`. Rewrite using `[v2 a (c1 _ (Dvd.dvd.mul_right (by rw [mul_assoc]; exact Nat.mul_dvd_mul_left p d1') _)), v1 a (c1 _ (Dvd.dvd.mul_right (by rw [mul_assoc]; exact dvd_mul_left _ _) _)), v3 a (c1 _ (by rw [mul_comm 2 N]; exact mul_dvd_mul (dvd_mul_left _ _) h2n))]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨f, φ, ξ₁, ⟨hd, h4, hodd.of_dvd_nat d3, p2, orderOf_dvd_of_pow_eq_one (t2 _ o3 (t1 _ o1 o2)), p3, (Nat.mul_le_mul_right _ (Nat.le_of_dvd hodd.pos d3)).trans big, ?_⟩, d4, fun a ha => ?_⟩` and prove the remaining obligations. Use `hv (-1) isCoprime_one_left.neg_left` as an intermediate fact. Simplify `this` using `only [Int.cast_neg, Int.cast_one, odd]`. Establish `ha' : IsCoprime a (f * 2 ^ n : ℕ)` using `ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (Nat.mul_dvd_mul_right d4 _))`. Rewrite using `[← hv a ha, X.prodX, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha', DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha']`.
-/
private theorem dirX {O : Type} [CommRing O] [IsDomain O] {l d N p n c : ℕ} [NeZero l] [NeZero N] [NeZero p]
    (ω : DirichletCharacter O l) (θ χ : DirichletCharacter O N) (ξ₀ : DirichletCharacter O p) (ξ : DirichletCharacter O (2 ^ n))
    (hl : Odd l) (hp : Odd p) (hθ : Odd θ.conductor) (hd : 0 < d) (h4 : 4 ∣ l ^ d - 1) (o1 : ω ^ (l ^ d - 1) = 1)
    (o2 : θ ^ (l ^ d - 1) = 1) (o3 : ξ₀ ^ (l ^ d - 1) = 1) (hc : χ.conductor = 2 ^ c) (hcn : c < n) (hξ : ξ.IsPrimitive)
    (big : p * l * θ.conductor * 4 ^ (l ^ d - 1).factorization 2 ≤ 2 ^ n)
    (odd : ω (-1) * (χ (-1) * θ (-1)) * (ξ₀ (-1) * ξ (-1)) = -1) :
    ∃ (f : ℕ) (φ : DirichletCharacter O f) (ξ₁ : DirichletCharacter O (2 ^ n)), X.XData l d φ ξ₁ ∧ f ∣ p * l * N ∧
      ∀ a : ℤ, IsCoprime a (p * l * N * 2 ^ n : ℕ) → X.prodX φ ξ₁ a = ω a * (χ a * θ a) * (ξ₀ a * ξ a) := by
  obtain ⟨f₁, φ₁, p1, d1, t1, v1⟩ := X.primProd O l N ω θ
  have hcN : θ.conductor ∣ N := θ.conductor_dvd_level
  have d1' : f₁ ∣ l * N := d1.trans (Nat.mul_dvd_mul_left l hcN)
  haveI : NeZero f₁ := ⟨fun h0 => mul_ne_zero (NeZero.ne l) (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ d1'))⟩
  obtain ⟨f, φ, p2, d2, t2, v2⟩ := X.primProd O p f₁ ξ₀ φ₁
  rw [show φ₁.conductor = f₁ from p1] at d2
  obtain ⟨ξ₁, p3, v3⟩ := UpperTheory.exists_primitive_two_pow_twist_mul O N χ c n hc hcn ξ hξ
  have d3 : f ∣ p * l * θ.conductor := by rw [mul_assoc]; exact d2.trans (Nat.mul_dvd_mul_left p d1)
  have d4 : f ∣ p * l * N := d3.trans (Nat.mul_dvd_mul_left _ hcN)
  have hodd : Odd (p * l * θ.conductor) := (hp.mul hl).mul hθ
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hv : ∀ a : ℤ, IsCoprime a (p * l * N * 2 ^ n : ℕ) → φ a * ξ₁ a = ω a * (χ a * θ a) * (ξ₀ a * ξ a) := fun a ha => by
    have c1 : ∀ m : ℕ, m ∣ p * l * N * 2 ^ n → IsCoprime a m := fun m hm =>
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hm)
    rw [v2 a (c1 _ (Dvd.dvd.mul_right (by rw [mul_assoc]; exact Nat.mul_dvd_mul_left p d1') _)),
      v1 a (c1 _ (Dvd.dvd.mul_right (by rw [mul_assoc]; exact dvd_mul_left _ _) _)),
      v3 a (c1 _ (by rw [mul_comm 2 N]; exact mul_dvd_mul (dvd_mul_left _ _) h2n))]
    ring
  refine ⟨f, φ, ξ₁, ⟨hd, h4, hodd.of_dvd_nat d3, p2, orderOf_dvd_of_pow_eq_one (t2 _ o3 (t1 _ o1 o2)), p3,
    (Nat.mul_le_mul_right _ (Nat.le_of_dvd hodd.pos d3)).trans big, ?_⟩, d4, fun a ha => ?_⟩
  · have := hv (-1) isCoprime_one_left.neg_left
    simpa only [Int.cast_neg, Int.cast_one, odd] using this
  · have ha' : IsCoprime a (f * 2 ^ n : ℕ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (Nat.mul_dvd_mul_right d4 _))
    rw [← hv a ha, X.prodX, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha',
      DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha']

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

/- English proof (translation)
Use extensionality with `g`. Establish `h1 : (χ ^ m) (Chr.cls ℚ Ω N g : ZMod N) = 1` using `by rw [h, MulChar.one_apply_coe]`. Rewrite `h1` using `[MulChar.pow_apply_coe]`. Rewrite using `[MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one]`. Conclude with `h1`.
-/
private theorem dirG_pow_one {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) {m : ℕ} (h : χ ^ m = 1) : Chr.dirG ℚ Ω χ ^ m = 1 := by
  ext g
  have h1 : (χ ^ m) (Chr.cls ℚ Ω N g : ZMod N) = 1 := by rw [h, MulChar.one_apply_coe]
  rw [MulChar.pow_apply_coe] at h1
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one]
  exact h1

/- English proof (translation)
Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Use extensionality with `g`. Establish `h1 : (χ⁻¹ * χ) (Chr.cls ℚ Ω N g : ZMod N) = 1` using `by rw [inv_mul_cancel, MulChar.one_apply_coe]`. Conclude with `h1`.
-/
private theorem dirG_inv {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) : Chr.dirG ℚ Ω χ⁻¹ = (Chr.dirG ℚ Ω χ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  ext g
  have h1 : (χ⁻¹ * χ) (Chr.cls ℚ Ω N g : ZMod N) = 1 := by rw [inv_mul_cancel, MulChar.one_apply_coe]
  exact h1

/- English proof (translation)
The claim follows from `Subgroup.isOpen_mono (fun g hg => by rw [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one]) (Chr.clsFacts ℚ Ω N).1`.
-/
private theorem dirG_open {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    IsOpen ((Chr.dirG ℚ Ω χ).ker : Set (G ℚ Ω)) :=
  Subgroup.isOpen_mono (fun g hg => by
    rw [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one]) (Chr.clsFacts ℚ Ω N).1

/- English proof (translation)
Introduce `g hg` and use `by rw [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 ((Chr.clsFacts ℚ Ω N).2.2.2.2 A hA hg), map_one]`.
-/
private theorem dirG_unr {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {A : ValuationSubring Ω}
    (hA : ¬ A.valuation (N : Ω) < 1) : Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω χ).ker := fun g hg => by
  rw [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 ((Chr.clsFacts ℚ Ω N).2.2.2.2 A hA hg), map_one]

/- English proof (translation)
Rewrite using `[Chr.dirG, MonoidHom.comp_apply, (Chr.clsFacts ℚ Ω N).2.2.2.1 σ h, MulChar.coe_toUnitHom, Units.val_neg, Units.val_one]`.
-/
private theorem dirG_cc {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {σ : G ℚ Ω} (h : IsCC σ) :
    (Chr.dirG ℚ Ω χ σ : O) = χ (-1) := by
  rw [Chr.dirG, MonoidHom.comp_apply, (Chr.clsFacts ℚ Ω N).2.2.2.1 σ h, MulChar.coe_toUnitHom, Units.val_neg, Units.val_one]

/- English proof (translation)
The claim follows from `(ML.placeBasic Ω).2.2.2.1 A v M ((Nat.Prime.coprime_iff_not_dvd hv).2 hM) hA`.
-/
private theorem not_over {A : ValuationSubring Ω} {v M : ℕ} (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hM : ¬ v ∣ M) :
    ¬ A.valuation (M : Ω) < 1 :=
  (ML.placeBasic Ω).2.2.2.1 A v M ((Nat.Prime.coprime_iff_not_dvd hv).2 hM) hA

/- English proof (translation)
Establish `h1` using `(ML.placeBasic Ω).2.2.2.2.2.2.1 A v N σ h (not_over hv hA hN)`. Establish `h2` using `(Chr.clsFacts ℚ Ω N).2.2.1 σ (ZMod.unitOfCoprime v ((Nat.Prime.coprime_iff_not_dvd hv).2 hN)) fun ζ hζ => by`. Rewrite using `[h1 ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod v hζ]`. Rewrite using `[Chr.dirG, MonoidHom.comp_apply, h2, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]`.
-/
private theorem dirG_frob {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {A : ValuationSubring Ω} {v : ℕ}
    (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hN : ¬ v ∣ N) {σ : G ℚ Ω} (h : IsFrob (F := ℚ) A v σ) :
    (Chr.dirG ℚ Ω χ σ : O) = χ v := by
  have h1 := (ML.placeBasic Ω).2.2.2.2.2.2.1 A v N σ h (not_over hv hA hN)
  have h2 := (Chr.clsFacts ℚ Ω N).2.2.1 σ (ZMod.unitOfCoprime v ((Nat.Prime.coprime_iff_not_dvd hv).2 hN)) fun ζ hζ => by
    rw [h1 ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod v hζ]
  rw [Chr.dirG, MonoidHom.comp_apply, h2, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]

variable {l : ℕ} [Fact l.Prime] {c : Coef l}

/- English proof (translation)
The claim follows from `Ideal.Quotient.eq`.
-/
private theorem res_iff {x y : c.O} : residue c.O x = residue c.O y ↔ x - y ∈ maximalIdeal c.O := Ideal.Quotient.eq

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Take `⟨⟨w, hw, -⟩, hom⟩` from `omT Ω l c`. Take `⟨-, -, -, -, -, -, o7, -⟩` from `hom w hw`.

Take `⟨⟨b, -, -, hb⟩, -⟩` from `psiBar Ω l c w hw N ψ`. Take `⟨ce, -, -, -, cf⟩` from `congrFacts Ω l c`. Establish `hc : Congr c (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) 1` using `fun g => res_iff.1 ((hn g).trans (map_one _).symm)`. Establish `hnd : ¬ l ∣ (l - 1) * orderOf (chiP l ψ)` using `fun h => by`. Break down `hl.dvd_mul.1 h with h | h` into its components or cases.

Use `hl.two_le; have := Nat.le_of_dvd (by omega) h; omega` as an intermediate fact. Conclude with `h2 h`. Establish `hone : w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ) = 1` using `cf _ _ _ hnd (by`. Rewrite using `[mul_pow, ← pow_mul, mul_comm (e + b), mul_assoc, pow_mul, hw.1, one_pow, one_mul, mul_comm, pow_mul, dirG_pow_one _ (pow_orderOf_eq_one _), one_pow]) (one_pow _) (ce.trans (ce.symm (hb e)) hc)`. Take `⟨A, hA⟩` from `(Chr.placesQ Ω).1 l hl`.

Establish `hI` using `((compIne Ω N l hl A hA).2 c.O (chiP l ψ)).2.2 h1`. Take `⟨k, hk⟩` from `o7 A hA (e + b) fun g hg => by`. Use `DFunLike.congr_fun hone g` as an intermediate fact. Rewrite `this` using `[MonoidHom.mul_apply, MonoidHom.mem_ker.1 (hI hg), mul_one]`. Then use the resulting hypothesis. Rewrite `hone` using `[hk, pow_mul, hw.1, one_pow, one_mul]`.

Use `h3 (((psiBar Ω l c w hw N (chiP l ψ)).2.2.2 1).2 (hone.trans ?_))` and prove the remaining obligations. Simplify using `using (dirG_pow_one (Ω := Ω) (1 : DirichletCharacter c.O N) (pow_one 1)).symm`.
-/
private theorem psi_ne {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N) (e : ℕ) (h1 : comp l (chiP l ψ) = 1)
    (h2 : ¬ l ∣ orderOf (chiP l ψ)) (h3 : chiP l ψ ≠ 1) : ∃ g, Raw.bar (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) g ≠ 1 := by
  have hl : l.Prime := Fact.out
  by_contra hn
  push Not at hn
  obtain ⟨⟨w, hw, -⟩, hom⟩ := omT Ω l c
  obtain ⟨-, -, -, -, -, -, o7, -⟩ := hom w hw
  obtain ⟨⟨b, -, -, hb⟩, -⟩ := psiBar Ω l c w hw N ψ
  obtain ⟨ce, -, -, -, cf⟩ := congrFacts Ω l c
  have hc : Congr c (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) 1 := fun g => res_iff.1 ((hn g).trans (map_one _).symm)
  have hnd : ¬ l ∣ (l - 1) * orderOf (chiP l ψ) := fun h => by
    rcases hl.dvd_mul.1 h with h | h
    · have := hl.two_le; have := Nat.le_of_dvd (by omega) h; omega
    · exact h2 h
  have hone : w ^ (e + b) * Chr.dirG ℚ Ω (chiP l ψ) = 1 := cf _ _ _ hnd (by
    rw [mul_pow, ← pow_mul, mul_comm (e + b), mul_assoc, pow_mul, hw.1, one_pow, one_mul, mul_comm, pow_mul,
      dirG_pow_one _ (pow_orderOf_eq_one _), one_pow]) (one_pow _) (ce.trans (ce.symm (hb e)) hc)
  obtain ⟨A, hA⟩ := (Chr.placesQ Ω).1 l hl
  have hI := ((compIne Ω N l hl A hA).2 c.O (chiP l ψ)).2.2 h1
  obtain ⟨k, hk⟩ := o7 A hA (e + b) fun g hg => by
    have := DFunLike.congr_fun hone g
    rwa [MonoidHom.mul_apply, MonoidHom.mem_ker.1 (hI hg), mul_one] at this
  rw [hk, pow_mul, hw.1, one_pow, one_mul] at hone
  refine h3 (((psiBar Ω l c w hw N (chiP l ψ)).2.2.2 1).2 (hone.trans ?_))
  simpa using (dirG_pow_one (Ω := Ω) (1 : DirichletCharacter c.O N) (pow_one 1)).symm

/- English proof (translation)
Introduce `p hp`. Establish `hl : l.Prime` using `Fact.out`. Break down `Finset.mem_insert.1 hp with rfl | hp` into its components or cases. Conclude with `Finset.mem_insert_self _ _`. Take `⟨h1, h2, h3⟩ : p ∈ D.S ∧ p ≠ l ∧ l ∣ Nat.card ((D.Ip p).map D.ψ)` from `by classical`.

Simplify `hp` using `only [Raw.Sb, Finset.mem_filter]`. Establish `hpp` using `hS p h1`. Use `Finset.mem_insert_of_mem (((hostSb h c.O ψ hψ l hl hl2).2.2.2.1 p hpp h2).2 ?_)` and prove the remaining obligations. Rewrite `h3` using `[hD]`. Use `haveI : Finite ((D.Ip p).map (Chr.dirG ℚ Ω ψ)) := by`.

Rewrite using `[Chr.dirG, ← Subgroup.map_map]`. Conclude with `Finite.Set.finite_image _ _`. Take `⟨⟨_, g, hg, rfl⟩, hx⟩` from `exists_prime_orderOf_dvd_card' l h3`. Use `hx.symm.dvd.trans (orderOf_dvd_of_pow_eq_one (Subtype.ext ?_))` and prove the remaining obligations. Use `show Chr.dirG ℚ Ω ψ g ^ _ = 1`.

Rewrite using `[((compIne Ω h.N p hpp _ (hpl p hpp)).2 c.O ψ).1 g hg]`. Conclude with `DFunLike.congr_fun (dirG_pow_one _ (pow_orderOf_eq_one _)) g`.
-/
private theorem t_sub (h : Host) (ψ : DirichletCharacter c.O h.N) (hψ : h.IsChar ψ) (hl2 : l ≠ 2) (D : Raw Ω c)
    (hS : ∀ p ∈ D.S, p.Prime) (hD : D.ψ = Chr.dirG ℚ Ω ψ) (hpl : ∀ p : ℕ, p.Prime → (D.pl p).valuation (p : Ω) < 1) :
    ∀ v ∈ D.T, v ∈ Tb l ψ := by
  intro p hp
  have hl : l.Prime := Fact.out
  rcases Finset.mem_insert.1 hp with rfl | hp
  · exact Finset.mem_insert_self _ _
  obtain ⟨h1, h2, h3⟩ : p ∈ D.S ∧ p ≠ l ∧ l ∣ Nat.card ((D.Ip p).map D.ψ) := by
    classical
    simpa only [Raw.Sb, Finset.mem_filter] using hp
  have hpp := hS p h1
  refine Finset.mem_insert_of_mem (((hostSb h c.O ψ hψ l hl hl2).2.2.2.1 p hpp h2).2 ?_)
  rw [hD] at h3
  haveI : Finite ((D.Ip p).map (Chr.dirG ℚ Ω ψ)) := by
    rw [Chr.dirG, ← Subgroup.map_map]
    exact Finite.Set.finite_image _ _
  obtain ⟨⟨_, g, hg, rfl⟩, hx⟩ := exists_prime_orderOf_dvd_card' l h3
  refine hx.symm.dvd.trans (orderOf_dvd_of_pow_eq_one (Subtype.ext ?_))
  show Chr.dirG ℚ Ω ψ g ^ _ = 1
  rw [((compIne Ω h.N p hpp _ (hpl p hpp)).2 c.O ψ).1 g hg]
  exact DFunLike.congr_fun (dirG_pow_one _ (pow_orderOf_eq_one _)) g

/- English proof (translation)
Take `⟨k, rfl⟩` from `hm`. Establish `h1 : (χ ^ (2 * k + 1)) ((-1 : (ZMod N)ˣ) : ZMod N) = 1` using `by rw [h, MulChar.one_apply_coe]`. Rewrite `h1` using `[MulChar.pow_apply_coe, pow_succ, pow_mul, ← map_pow, Units.val_neg, Units.val_one, neg_one_sq, map_one, one_pow, one_mul]`. Then use the resulting hypothesis.
-/
private theorem even_of_odd {O : Type} [CommRing O] {N m : ℕ} {χ : DirichletCharacter O N} (h : χ ^ m = 1) (hm : Odd m) :
    χ (-1) = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have h1 : (χ ^ (2 * k + 1)) ((-1 : (ZMod N)ˣ) : ZMod N) = 1 := by rw [h, MulChar.one_apply_coe]
  rwa [MulChar.pow_apply_coe, pow_succ, pow_mul, ← map_pow, Units.val_neg, Units.val_one, neg_one_sq, map_one, one_pow,
    one_mul] at h1

/- English proof (translation)
Establish `h1 : (χ⁻¹ * χ) ((-1 : (ZMod N)ˣ) : ZMod N) = 1` using `by rw [inv_mul_cancel, MulChar.one_apply_coe]`. Rewrite `h1` using `[MulChar.mul_apply, Units.val_neg, Units.val_one]`. Establish `h2 : χ (-1) * χ (-1) = 1` using `by rw [← map_mul, neg_mul_neg, one_mul, map_one]`. Rewrite using `[← mul_one (χ⁻¹ (-1)), ← h2, ← mul_assoc, h1, one_mul]`.
-/
private theorem inv_at_neg {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) : χ⁻¹ (-1) = χ (-1) := by
  have h1 : (χ⁻¹ * χ) ((-1 : (ZMod N)ˣ) : ZMod N) = 1 := by rw [inv_mul_cancel, MulChar.one_apply_coe]
  rw [MulChar.mul_apply, Units.val_neg, Units.val_one] at h1
  have h2 : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_mul_neg, one_mul, map_one]
  rw [← mul_one (χ⁻¹ (-1)), ← h2, ← mul_assoc, h1, one_mul]

/- English proof (translation)
Take `⟨f, φ, ξ₁, hd', hf, hv⟩` from `dirX ω θ χ ξ₀ ξ hl hp hθ hd h4 o1 o2 o3 hc hcn hξ big odd`. Use `haveI hM : NeZero (p * l * N * 2 ^ n) := inferInstance`. Establish `hdvd : f * 2 ^ n ∣ p * l * N * 2 ^ n` using `Nat.mul_dvd_mul_right hf _`. Use `haveI : NeZero (f * 2 ^ n) := ⟨fun h0 => hM.out (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))⟩`. Use `X.xvan hX D hT d f n φ ξ₁ hd' γ fun g => ?_` and prove the remaining obligations.

Take `⟨a, ha, hw⟩` from `X.dirVal Ω (p * l * N * 2 ^ n) g`. Establish `e1 : (X.redChar Ω (residue c.O) (X.prodX φ ξ₁) g : ResidueField c.O) = residue c.O (X.prodX φ ξ₁ a)`. Rewrite using `[← hw _ hdvd]`. Both sides reduce to the same expression. Rewrite using `[e1, hv a ha, hγ]`.

Simplify using `only [Raw.bar, map_mul]`. Rewrite using `[hw l (((dvd_mul_left l p).mul_right N).mul_right _), hw N ((dvd_mul_left N _).mul_right _), hw N ((dvd_mul_left N _).mul_right _), hw p (((dvd_mul_right p l).mul_right N).mul_right _), hw _ (dvd_mul_left _ _)]`.
-/
private theorem xvOf (hX : X.CorX) (D : Raw Ω c) (hT : ∀ p ∈ D.T, p.Prime ∧ (D.pl p).valuation (p : Ω) < 1)
    {d N p n k : ℕ} [NeZero N] [NeZero p]
    (ω : DirichletCharacter c.O l) (θ χ : DirichletCharacter c.O N) (ξ₀ : DirichletCharacter c.O p)
    (ξ : DirichletCharacter c.O (2 ^ n))
    (hl : Odd l) (hp : Odd p) (hθ : Odd θ.conductor) (hd : 0 < d) (h4 : 4 ∣ l ^ d - 1) (o1 : ω ^ (l ^ d - 1) = 1)
    (o2 : θ ^ (l ^ d - 1) = 1) (o3 : ξ₀ ^ (l ^ d - 1) = 1) (hc : χ.conductor = 2 ^ k) (hcn : k < n) (hξ : ξ.IsPrimitive)
    (big : p * l * θ.conductor * 4 ^ (l ^ d - 1).factorization 2 ≤ 2 ^ n)
    (odd : ω (-1) * (χ (-1) * θ (-1)) * (ξ₀ (-1) * ξ (-1)) = -1) (γ : G ℚ Ω →* c.Oˣ)
    (hγ : ∀ g, Raw.bar γ g = Raw.bar (Chr.dirG ℚ Ω ω) g * (Raw.bar (Chr.dirG ℚ Ω χ) g * Raw.bar (Chr.dirG ℚ Ω θ) g) *
      (Raw.bar (Chr.dirG ℚ Ω ξ₀) g * Raw.bar (Chr.dirG ℚ Ω ξ) g)) : D.XVan γ ∧ D.XVan γ⁻¹ := by
  obtain ⟨f, φ, ξ₁, hd', hf, hv⟩ := dirX ω θ χ ξ₀ ξ hl hp hθ hd h4 o1 o2 o3 hc hcn hξ big odd
  haveI hM : NeZero (p * l * N * 2 ^ n) := inferInstance
  have hdvd : f * 2 ^ n ∣ p * l * N * 2 ^ n := Nat.mul_dvd_mul_right hf _
  haveI : NeZero (f * 2 ^ n) := ⟨fun h0 => hM.out (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))⟩
  refine X.xvan hX D hT d f n φ ξ₁ hd' γ fun g => ?_
  obtain ⟨a, ha, hw⟩ := X.dirVal Ω (p * l * N * 2 ^ n) g
  have e1 : (X.redChar Ω (residue c.O) (X.prodX φ ξ₁) g : ResidueField c.O) = residue c.O (X.prodX φ ξ₁ a) := by
    rw [← hw _ hdvd]; rfl
  rw [e1, hv a ha, hγ]
  simp only [Raw.bar, map_mul]
  rw [hw l (((dvd_mul_left l p).mul_right N).mul_right _), hw N ((dvd_mul_left N _).mul_right _),
    hw N ((dvd_mul_left N _).mul_right _), hw p (((dvd_mul_right p l).mul_right N).mul_right _), hw _ (dvd_mul_left _ _)]

private noncomputable def rd (c : Coef l) : c.Oˣ →* (ResidueField c.O)ˣ := Units.map (residue c.O).toMonoidHom

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
private theorem dirG_mul {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ χ' : DirichletCharacter O N) (g : G ℚ Ω) :
    Chr.dirG ℚ Ω (χ * χ') g = Chr.dirG ℚ Ω χ g * Chr.dirG ℚ Ω χ' g := Units.ext rfl

/- English proof (translation)
The claim follows from `Units.ext (MulChar.pow_apply_coe χ k _)`.
-/
private theorem dirG_pow {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (k : ℕ) (g : G ℚ Ω) :
    Chr.dirG ℚ Ω (χ ^ k) g = Chr.dirG ℚ Ω χ g ^ k := Units.ext (MulChar.pow_apply_coe χ k _)

/- English proof (translation)
The claim follows from `Units.ext (MulChar.one_apply_coe _)`.
-/
private theorem dirG_one {O : Type} [CommRing O] {N : ℕ} [NeZero N] (g : G ℚ Ω) :
    Chr.dirG ℚ Ω (1 : DirichletCharacter O N) g = 1 := Units.ext (MulChar.one_apply_coe _)

set_option maxHeartbeats 800000 in
/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hlo : Odd l` using `hl.odd_of_ne_two hl2`. Take `⟨D, dS, de, dψ, dξ, dpl, dcc, dom, dbar, dfr, dcyc, dph, dg0, ds0, dord⟩` from `rawEx (Ω := Ω) (c := c) hl2 (2 * l * h.N * p).primeFactors e (Chr.dirG ℚ Ω ψ) (Chr.dirG ℚ Ω ξ₀ * Chr.dirG ℚ Ω ξ) (dirG_open ψ)`. Establish `hM : 2 * l * h.N * p ≠ 0` using `NeZero.ne _`. Establish `hS : ∀ q ∈ D.S, q.Prime` using `fun q hq => Nat.prime_of_mem_primeFactors (dS ▸ hq)`.

Establish `hTb` using `t_sub h ψ hψ hl2 D hS dψ dpl`. Take `⟨sb1, -⟩` from `hostSb h c.O ψ hψ l hl hl2`. Establish `hT : ∀ v ∈ D.T, v.Prime ∧ v ≠ 2 ∧ (v = l ∨ v ≠ l ∧ v ≡ 1 [MOD l])` using `fun v hv => by`. Break down `Finset.mem_insert.1 (hTb v hv) with rfl | hv'` into its components or cases. Conclude with `⟨hl, hl2, Or.inl rfl⟩`.

Take `⟨x1, x2, x3, -, x4⟩` from `sb1 v hv'`. Conclude with `⟨x1, x2, Or.inr ⟨x3, x4⟩⟩`. Establish `h2n : ∀ v ∈ D.T, ¬ v ∣ 2 ^ n` using `fun v hv hd => (hT v hv).2.1 ((Nat.prime_dvd_prime_iff_eq (hT v hv).1 Nat.prime_two).1 ((hT v hv).1.dvd_of_dvd_pow hd))`. Establish `haw : ∀ A, Raw.Away D.S A → ∀ m k : ℕ, m ≠ 0 → m ∣ (2 * l * h.N * p) ^ k → ¬ A.valuation (m : Ω) < 1` using `fun A hA m k hm hd hv => by`. Take `⟨q, hq, hq'⟩` from `((Chr.placesQ Ω).2.1 A m hm).1 hv`.

Establish `hqp` using `Nat.prime_of_mem_primeFactors hq`. Conclude with `hA q (dS ▸ Nat.mem_primeFactors.2 ⟨hqp, hqp.dvd_of_dvd_pow ((Nat.dvd_of_mem_primeFactors hq).trans hd), hM⟩) hq'`. Establish `hom : IsOmT c D.om` using `⟨dom, fun g => res_iff.1 (dbar g)⟩`. Take `⟨ω, hω, hωT⟩` from `X.omDir Ω l c`. Establish `eω : D.om = Chr.dirG ℚ Ω ω` using `(omT Ω l c).1.unique hom hωT`.

Take `⟨tψ, ⟨s, hs⟩, -, f1, f2, f3, f4⟩` from `X.th1Facts c.O h.N ψ l hl hl2`. Take `⟨-, -, -, -, t5, -, -, t8, t9, -⟩` from `hostTh1 h c.O ψ hψ l hl hl2`. Establish `ePsi : D.Psi = Chr.Psi l e (Chr.dirG ℚ Ω ψ)` using `by rw [Raw.Psi, de, dψ]`. Establish `rom : ∀ g, rd c (chiO ℚ Ω l c.O g) = rd c (Chr.dirG ℚ Ω ω g)` using `fun g => by`. Rewrite using `[← eω]`.

Conclude with `Units.ext (dbar g).symm`. Establish `ral : ∀ g, rd c (D.al g) = rd c (Chr.dirG ℚ Ω ξ₀ g) * rd c (Chr.dirG ℚ Ω ξ g)` using `fun g => by`. Rewrite using `[show D.al g = chiO ℚ Ω l c.O g * (D.om g)⁻¹ * D.ξ g from rfl, map_mul, map_mul, map_inv, rom, eω, mul_inv_cancel, one_mul, dξ, MonoidHom.mul_apply, map_mul]`. Establish `rPsi0 : ∀ g, rd c (D.Psi g) = rd c (Chr.dirG ℚ Ω ω g) ^ e * rd c (Chr.dirG ℚ Ω ψ g)` using `fun g => by`. Rewrite using `[ePsi, Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, map_mul, map_pow, rom]`.

Establish `rPsi : ∀ g, rd c (D.Psi g) = rd c (Chr.dirG ℚ Ω (ω ^ e) g) * (rd c (Chr.dirG ℚ Ω (psi2 ψ) g) * rd c (Chr.dirG ℚ Ω (th1 l ψ) g))` using `fun g => by`. Establish `hk : rd c (Chr.dirG ℚ Ω (kap l ψ) g) = rd c 1` using `Units.ext (res_iff.2 ((congrFacts Ω l c).2.2.1 _ s (dirG_pow_one _ hs) g))`. Rewrite using `[rPsi0, dirG_pow, map_pow]`. Use `conv_lhs => rw [tψ]`. Rewrite using `[dirG_mul, dirG_mul, map_mul, map_mul, hk, map_one, mul_one]`.

Establish `hD : ∀ v ∈ D.T, ∀ i : ℤ, Raw.bar (D.ξ * D.Psi ^ i) (D.sg v) ≠ 1` using `fun v hv i hb => by`. Take `⟨hvp, hv2, hvl⟩` from `hT v hv`. Establish `r1 : rd c (Chr.dirG ℚ Ω ω (D.sg v)) = 1`. Break down `hvl with rfl | ⟨hne, hm⟩` into its components or cases. Rewrite using `[← rom, chiO, MonoidHom.comp_apply, dcyc, map_one, map_one]`.

Use `dirG_frob ω hvp (dpl v hvp) (fun hd => hne ((Nat.prime_dvd_prime_iff_eq hvp hl).1 hd)) (dfr v hvp)` as an intermediate fact. Rewrite `this` using `[(ZMod.natCast_eq_natCast_iff _ _ _).2 hm, Nat.cast_one, map_one]`. Rewrite using `[Units.val_eq_one.1 this, map_one]`. Establish `r2 : rd c ((D.ξ * D.Psi ^ i) (D.sg v)) = 1` using `Units.ext hb`. Rewrite `r2` using `[MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow, rPsi0, r1, one_pow, one_mul, dξ, MonoidHom.mul_apply, map_mul]`.

Establish `r3` using `congrArg (· ^ (2 ^ a * u)) r2`. Simplify using `only [mul_pow, one_pow] at r3`. Rewrite `r3` using `[← zpow_natCast (_ ^ i), ← zpow_mul, mul_comm i, zpow_mul, zpow_natCast, ← map_pow (rd c), ← map_pow (rd c), ← map_pow (rd c), ← dirG_pow ξ₀, ← dirG_pow ψ, u1, u2, dirG_one, dirG_one, map_one, one_zpow, one_mul, mul_one]`. Establish `r4 : Chr.dirG ℚ Ω ξ (D.sg v) ^ (2 ^ a * u) = 1`. Use `(congrFacts Ω l c).2.2.2.1 _ _ (Nat.totient (2 ^ n)) ?_ ?_ (one_pow _) (res_iff.1 (congrArg Units.val (r3.trans (map_one (rd c)).symm)))` and prove the remaining obligations.

Rewrite using `[Nat.totient_prime_pow Nat.prime_two (by omega)]`. Conclude with `fun hd => hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow (by simpa using hd)))`. Rewrite using `[← pow_mul, mul_comm, pow_mul, Chr.dirG, MonoidHom.comp_apply, ← map_pow, ZMod.pow_totient, map_one, one_pow]`. Establish `r5` using `congrArg Units.val r4`. Rewrite `r5` using `[Units.val_pow_eq_pow_val, dirG_frob ξ hvp (dpl v hvp) (h2n v hv) (dfr v hvp)]`.

Conclude with `(UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one c.O n ξ hξ v a u (hvp.odd_of_ne_two hv2) hvp.one_lt hu r5).not_ge (hvb v (hTb v hv))`. Establish `hT' : ∀ v ∈ D.T, v.Prime ∧ (D.pl v).valuation (v : Ω) < 1` using `fun v hv => ⟨(hT v hv).1, dpl v (hT v hv).1⟩`. Establish `o1 : (ω ^ e) ^ (l ^ f0 l ψ - 1) = 1`. Take `⟨k, hk⟩` from `f4`. Rewrite using `[← pow_mul, mul_comm, hk, mul_assoc, pow_mul, hω, one_pow]`.

Establish `hc2 : (psi2 ψ).conductor = 2 ^ c2 ψ` using `(compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.1.symm`. Establish `sg : (ω ^ e) (-1) * (psi2 ψ (-1) * th1 l ψ (-1)) = 1`. Establish `a1 : Chr.dirG ℚ Ω ω D.cc = -1` using `((omT Ω l c).2 _ hωT).2.2.2.2.1 _ dcc hl2`. Establish `a2 : (psi2 ψ (-1) * th1 l ψ (-1) : c.O) = (-1) ^ e`. Rewrite using `[← show ψ (-1) = (-1) ^ e from hev]`.

Use `conv_rhs => rw [tψ]`. Rewrite using `[MulChar.mul_apply, MulChar.mul_apply, even_of_odd hs hlo.pow, mul_one]`. Rewrite using `[← dirG_cc _ dcc, dirG_pow, a1, a2, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]`. Simplify using the standard rewrite rules. Establish `hg` using `dg0 ⟨D.sg l, fun hb => hD l (Finset.mem_insert_self _ _) 0 (by`.

Establish `: rd c (D.al (D.sg l)) = 1` using `Units.ext hb`. Rewrite `this` using `[ral, ← map_mul, ← MonoidHom.mul_apply, ← dξ]`. Rewrite using `[zpow_zero, mul_one]`. Conclude with `congrArg Units.val this)⟩ (ePsi ▸ psi_ne ψ e t8 t9 hchi)`. Use `⟨D, ⟨hl2, hS, ?_, ?_, de ▸ he, dpl, dcc, dψ ▸ dirG_open ψ, fun A hA => ?_, ?_, dom, dbar, ?_, ?_, fun A hA => ?_, fun v hv => ?_, ?_, fun v hv => dfr v (hT v hv).1, dcyc, hD, ?_, dph, hg.1, hg.2, ds0, dord⟩, de, dψ, dS, inferInstance, ξ, ξ₀, hξ, hξo, rfl, dξ⟩` and prove the remaining obligations.

Conclude with `dS ▸ Nat.mem_primeFactors.2 ⟨Nat.prime_two, ((dvd_mul_right 2 l).mul_right _).mul_right _, hM⟩`. Conclude with `dS ▸ Nat.mem_primeFactors.2 ⟨hl, ((dvd_mul_left l 2).mul_right _).mul_right _, hM⟩`. Rewrite using `[dψ]`. Conclude with `dirG_unr ψ (haw A hA _ 1 (NeZero.ne _) (by rw [pow_one]; exact (dvd_mul_left _ _).mul_right _))`. Rewrite using `[ePsi]`.

Conclude with `((psiBar Ω l c _ hom h.N ψ).2.1 e).1 hev _ dcc`. Rewrite using `[dξ]`. Conclude with `Subgroup.isOpen_mono (H₁ := _ ⊓ _) (fun g hg => by`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mem_ker.1 hg.1, MonoidHom.mem_ker.1 hg.2, mul_one])`. Use the proof step `(IsOpen.inter (dirG_open ξ₀) (dirG_open ξ))`.

Use `⟨(l ^ f0 l ψ - 1) * Nat.totient (2 ^ n), Nat.Coprime.mul_right ?_ ?_, ?_⟩` and prove the remaining obligations. Conclude with `Nat.Coprime.coprime_dvd_left (dvd_pow_self l f1.ne') ((Nat.coprime_self_sub_right (Nat.one_le_pow _ _ hl.pos)).2 (by simp))`. Rewrite using `[Nat.totient_prime_pow Nat.prime_two (by omega)]`. Simplify using `using Nat.Coprime.pow_right _ ((Nat.coprime_primes hl Nat.prime_two).2 hl2)`. Rewrite using `[dξ, mul_pow, pow_mul, dirG_pow_one _ o3, one_pow, one_mul, mul_comm, pow_mul]`.

Establish `: Chr.dirG ℚ Ω ξ ^ Nat.totient (2 ^ n) = 1` using `MonoidHom.ext fun g => by`. Rewrite using `[MonoidHom.pow_apply, Chr.dirG, MonoidHom.comp_apply, ← map_pow, ZMod.pow_totient, map_one, MonoidHom.one_apply]`. Rewrite using `[this, one_pow]`. Introduce `g hg`. Rewrite using `[dξ, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mem_ker.1 (dirG_unr ξ₀ (haw A hA _ 1 (NeZero.ne _) (by rw [pow_one]; exact dvd_mul_left _ _)) hg), MonoidHom.mem_ker.1 (dirG_unr ξ (haw A hA _ n (NeZero.ne _) (pow_dvd_pow_of_dvd (((dvd_mul_right 2 l).mul_right _).mul_right _ …`.

Introduce `g hg`. Rewrite using `[dξ, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mem_ker.1 (dirG_unr ξ₀ (not_over (hT' v hv).1 (hT' v hv).2 (hpT v (hTb v hv))) hg), MonoidHom.mem_ker.1 (dirG_unr ξ (not_over (hT' v hv).1 (hT' v hv).2 (h2n v hv)) hg), mul_one]`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[dξ, MonoidHom.mul_apply, Units.val_mul, dirG_cc _ dcc, dirG_cc _ dcc, ev0, hξo, one_mul, Units.val_neg, Units.val_one]`. Introduce `γ hγ`.

Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hγ`. Break down `hγ with rfl | rfl | rfl` into its components or cases. Use `xvOf hX D hT' (d := f0 l ψ) (N := h.N) (k := 0) 1 1 1 ξ₀ ξ hlo hp ?_ f1 f2 (one_pow _) (one_pow _) o3 ?_ (by omega) hξ ?_ ?_ _ fun g => ?_` and prove the remaining obligations. Rewrite using `[DirichletCharacter.conductor_one]`. Conclude with `odd_one`.

Rewrite using `[DirichletCharacter.conductor_one, pow_zero]`. Rewrite using `[DirichletCharacter.conductor_one]`. Conclude with `le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ t5.pos)) big`. Rewrite using `[even_of_odd (pow_one _) odd_one, even_of_odd (pow_one _) odd_one, ev0, hξo]`. Simplify using the standard rewrite rules.

Simplify using `only [Raw.bar, dirG_one, Units.val_one, map_one, one_mul]`. Conclude with `congrArg Units.val (ral g)`. Use `xvOf hX D hT' (ω ^ e) (th1 l ψ) (psi2 ψ) ξ₀⁻¹ ξ⁻¹ hlo hp t5 f1 f2 o1 f3 (by rw [inv_pow, o3, inv_one]) hc2 hcn ((DirichletCharacter.conductor_inv ξ).trans hξ) big ?_ _ fun g => ?_` and prove the remaining obligations. Rewrite using `[sg, inv_at_neg, inv_at_neg, ev0, hξo]`. Simplify using the standard rewrite rules.

Establish `: rd c (D.be g) = rd c (Chr.dirG ℚ Ω (ω ^ e) g) * (rd c (Chr.dirG ℚ Ω (psi2 ψ) g) * rd c (Chr.dirG ℚ Ω (th1 l ψ) g)) * (rd c (Chr.dirG ℚ Ω ξ₀⁻¹ g) * rd c (Chr.dirG ℚ Ω ξ⁻¹ g))`. Rewrite using `[show D.be g = D.Psi g * (D.al g)⁻¹ from rfl, map_mul, map_inv, rPsi, ral, mul_inv, dirG_inv, dirG_inv, MonoidHom.inv_apply, MonoidHom.inv_apply, map_inv, map_inv]`. Conclude with `congrArg Units.val this`. Use `xvOf hX D hT' (ω ^ e) (th1 l ψ) (psi2 ψ) ξ₀ ξ hlo hp t5 f1 f2 o1 f3 o3 hc2 hcn hξ big ?_ _ fun g => ?_` and prove the remaining obligations. Rewrite using `[sg, ev0, hξo]`.

Simplify using the standard rewrite rules. Establish `: rd c (D.th g) = rd c (Chr.dirG ℚ Ω (ω ^ e) g) * (rd c (Chr.dirG ℚ Ω (psi2 ψ) g) * rd c (Chr.dirG ℚ Ω (th1 l ψ) g)) * (rd c (Chr.dirG ℚ Ω ξ₀ g) * rd c (Chr.dirG ℚ Ω ξ g))`. Rewrite using `[show D.th g = D.al g * D.Psi g from rfl, map_mul, rPsi, ral, mul_comm]`. Conclude with `congrArg Units.val this`.
-/
private theorem core (hX : X.CorX) (h : Host) (e : ℕ) (hl2 : l ≠ 2) (he : 2 ≤ e) (ψ : DirichletCharacter c.O h.N)
    (hψ : h.IsChar ψ) (hev : PsiEven e ψ) (hchi : chiP l ψ ≠ 1) {p n : ℕ} [NeZero p] (hp : Odd p)
    (ξ₀ : DirichletCharacter c.O p) (ξ : DirichletCharacter c.O (2 ^ n)) (hξ : ξ.IsPrimitive) (hξo : ξ (-1) = -1)
    (hpT : ∀ v ∈ Tb l ψ, ¬ v ∣ p) (o3 : ξ₀ ^ (l ^ f0 l ψ - 1) = 1) (ev0 : ξ₀ (-1) = 1) (hcn : c2 ψ < n)
    (big : p * l * (th1 l ψ).conductor * 4 ^ n0 l ψ ≤ 2 ^ n) {a u : ℕ} (hu : Odd u) (u1 : ψ ^ (2 ^ a * u) = 1)
    (u2 : ξ₀ ^ (2 ^ a * u) = 1) (hvb : ∀ v ∈ Tb l ψ, v ^ 2 * 2 ^ a ≤ 2 ^ n) :
    ∃ D : Raw Ω c, D.Good ∧ Aut.OfChar D e ψ n p (orderOf ξ₀) := by
  have hl : l.Prime := Fact.out
  have hlo : Odd l := hl.odd_of_ne_two hl2
  obtain ⟨D, dS, de, dψ, dξ, dpl, dcc, dom, dbar, dfr, dcyc, dph, dg0, ds0, dord⟩ :=
    rawEx (Ω := Ω) (c := c) hl2 (2 * l * h.N * p).primeFactors e (Chr.dirG ℚ Ω ψ) (Chr.dirG ℚ Ω ξ₀ * Chr.dirG ℚ Ω ξ) (dirG_open ψ)
  have hM : 2 * l * h.N * p ≠ 0 := NeZero.ne _
  have hS : ∀ q ∈ D.S, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (dS ▸ hq)
  have hTb := t_sub h ψ hψ hl2 D hS dψ dpl
  obtain ⟨sb1, -⟩ := hostSb h c.O ψ hψ l hl hl2
  have hT : ∀ v ∈ D.T, v.Prime ∧ v ≠ 2 ∧ (v = l ∨ v ≠ l ∧ v ≡ 1 [MOD l]) := fun v hv => by
    rcases Finset.mem_insert.1 (hTb v hv) with rfl | hv'
    · exact ⟨hl, hl2, Or.inl rfl⟩
    · obtain ⟨x1, x2, x3, -, x4⟩ := sb1 v hv'
      exact ⟨x1, x2, Or.inr ⟨x3, x4⟩⟩
  have h2n : ∀ v ∈ D.T, ¬ v ∣ 2 ^ n := fun v hv hd =>
    (hT v hv).2.1 ((Nat.prime_dvd_prime_iff_eq (hT v hv).1 Nat.prime_two).1 ((hT v hv).1.dvd_of_dvd_pow hd))
  have haw : ∀ A, Raw.Away D.S A → ∀ m k : ℕ, m ≠ 0 → m ∣ (2 * l * h.N * p) ^ k → ¬ A.valuation (m : Ω) < 1 :=
    fun A hA m k hm hd hv => by
      obtain ⟨q, hq, hq'⟩ := ((Chr.placesQ Ω).2.1 A m hm).1 hv
      have hqp := Nat.prime_of_mem_primeFactors hq
      exact hA q (dS ▸ Nat.mem_primeFactors.2 ⟨hqp, hqp.dvd_of_dvd_pow ((Nat.dvd_of_mem_primeFactors hq).trans hd), hM⟩) hq'
  have hom : IsOmT c D.om := ⟨dom, fun g => res_iff.1 (dbar g)⟩
  obtain ⟨ω, hω, hωT⟩ := X.omDir Ω l c
  have eω : D.om = Chr.dirG ℚ Ω ω := (omT Ω l c).1.unique hom hωT
  obtain ⟨tψ, ⟨s, hs⟩, -, f1, f2, f3, f4⟩ := X.th1Facts c.O h.N ψ l hl hl2
  obtain ⟨-, -, -, -, t5, -, -, t8, t9, -⟩ := hostTh1 h c.O ψ hψ l hl hl2
  have ePsi : D.Psi = Chr.Psi l e (Chr.dirG ℚ Ω ψ) := by rw [Raw.Psi, de, dψ]
  have rom : ∀ g, rd c (chiO ℚ Ω l c.O g) = rd c (Chr.dirG ℚ Ω ω g) := fun g => by
    rw [← eω]; exact Units.ext (dbar g).symm
  have ral : ∀ g, rd c (D.al g) = rd c (Chr.dirG ℚ Ω ξ₀ g) * rd c (Chr.dirG ℚ Ω ξ g) := fun g => by
    rw [show D.al g = chiO ℚ Ω l c.O g * (D.om g)⁻¹ * D.ξ g from rfl, map_mul, map_mul, map_inv, rom, eω, mul_inv_cancel,
      one_mul, dξ, MonoidHom.mul_apply, map_mul]
  have rPsi0 : ∀ g, rd c (D.Psi g) = rd c (Chr.dirG ℚ Ω ω g) ^ e * rd c (Chr.dirG ℚ Ω ψ g) := fun g => by
    rw [ePsi, Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, map_mul, map_pow, rom]
  have rPsi : ∀ g, rd c (D.Psi g) = rd c (Chr.dirG ℚ Ω (ω ^ e) g) *
      (rd c (Chr.dirG ℚ Ω (psi2 ψ) g) * rd c (Chr.dirG ℚ Ω (th1 l ψ) g)) := fun g => by
    have hk : rd c (Chr.dirG ℚ Ω (kap l ψ) g) = rd c 1 :=
      Units.ext (res_iff.2 ((congrFacts Ω l c).2.2.1 _ s (dirG_pow_one _ hs) g))
    rw [rPsi0, dirG_pow, map_pow]
    conv_lhs => rw [tψ]
    rw [dirG_mul, dirG_mul, map_mul, map_mul, hk, map_one, mul_one]
  have hD : ∀ v ∈ D.T, ∀ i : ℤ, Raw.bar (D.ξ * D.Psi ^ i) (D.sg v) ≠ 1 := fun v hv i hb => by
    obtain ⟨hvp, hv2, hvl⟩ := hT v hv
    have r1 : rd c (Chr.dirG ℚ Ω ω (D.sg v)) = 1 := by
      rcases hvl with rfl | ⟨hne, hm⟩
      · rw [← rom, chiO, MonoidHom.comp_apply, dcyc, map_one, map_one]
      · have := dirG_frob ω hvp (dpl v hvp) (fun hd => hne ((Nat.prime_dvd_prime_iff_eq hvp hl).1 hd)) (dfr v hvp)
        rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hm, Nat.cast_one, map_one] at this
        rw [Units.val_eq_one.1 this, map_one]
    have r2 : rd c ((D.ξ * D.Psi ^ i) (D.sg v)) = 1 := Units.ext hb
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, map_mul, map_zpow, rPsi0, r1, one_pow, one_mul, dξ, MonoidHom.mul_apply,
      map_mul] at r2
    have r3 := congrArg (· ^ (2 ^ a * u)) r2
    simp only [mul_pow, one_pow] at r3
    rw [← zpow_natCast (_ ^ i), ← zpow_mul, mul_comm i, zpow_mul, zpow_natCast, ← map_pow (rd c), ← map_pow (rd c), ← map_pow (rd c),
      ← dirG_pow ξ₀, ← dirG_pow ψ, u1, u2, dirG_one, dirG_one, map_one, one_zpow, one_mul, mul_one] at r3
    have r4 : Chr.dirG ℚ Ω ξ (D.sg v) ^ (2 ^ a * u) = 1 := by
      refine (congrFacts Ω l c).2.2.2.1 _ _ (Nat.totient (2 ^ n)) ?_ ?_ (one_pow _) (res_iff.1 (congrArg Units.val (r3.trans (map_one (rd c)).symm)))
      · rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
        exact fun hd => hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow (by simpa using hd)))
      · rw [← pow_mul, mul_comm, pow_mul, Chr.dirG, MonoidHom.comp_apply, ← map_pow, ZMod.pow_totient, map_one, one_pow]
    have r5 := congrArg Units.val r4
    rw [Units.val_pow_eq_pow_val, dirG_frob ξ hvp (dpl v hvp) (h2n v hv) (dfr v hvp)] at r5
    exact (UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one c.O n ξ hξ v a u (hvp.odd_of_ne_two hv2) hvp.one_lt hu r5).not_ge (hvb v (hTb v hv))
  have hT' : ∀ v ∈ D.T, v.Prime ∧ (D.pl v).valuation (v : Ω) < 1 := fun v hv => ⟨(hT v hv).1, dpl v (hT v hv).1⟩
  have o1 : (ω ^ e) ^ (l ^ f0 l ψ - 1) = 1 := by
    obtain ⟨k, hk⟩ := f4
    rw [← pow_mul, mul_comm, hk, mul_assoc, pow_mul, hω, one_pow]
  have hc2 : (psi2 ψ).conductor = 2 ^ c2 ψ := (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.1.symm
  have sg : (ω ^ e) (-1) * (psi2 ψ (-1) * th1 l ψ (-1)) = 1 := by
    have a1 : Chr.dirG ℚ Ω ω D.cc = -1 := ((omT Ω l c).2 _ hωT).2.2.2.2.1 _ dcc hl2
    have a2 : (psi2 ψ (-1) * th1 l ψ (-1) : c.O) = (-1) ^ e := by
      rw [← show ψ (-1) = (-1) ^ e from hev]
      conv_rhs => rw [tψ]
      rw [MulChar.mul_apply, MulChar.mul_apply, even_of_odd hs hlo.pow, mul_one]
    rw [← dirG_cc _ dcc, dirG_pow, a1, a2, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]
    simp
  have hg := dg0 ⟨D.sg l, fun hb => hD l (Finset.mem_insert_self _ _) 0 (by
    have : rd c (D.al (D.sg l)) = 1 := Units.ext hb
    rw [ral, ← map_mul, ← MonoidHom.mul_apply, ← dξ] at this
    rw [zpow_zero, mul_one]
    exact congrArg Units.val this)⟩ (ePsi ▸ psi_ne ψ e t8 t9 hchi)
  refine ⟨D, ⟨hl2, hS, ?_, ?_, de ▸ he, dpl, dcc, dψ ▸ dirG_open ψ, fun A hA => ?_, ?_, dom, dbar, ?_, ?_, fun A hA => ?_,
    fun v hv => ?_, ?_, fun v hv => dfr v (hT v hv).1, dcyc, hD, ?_, dph, hg.1, hg.2, ds0, dord⟩,
    de, dψ, dS, inferInstance, ξ, ξ₀, hξ, hξo, rfl, dξ⟩
  · exact dS ▸ Nat.mem_primeFactors.2 ⟨Nat.prime_two, ((dvd_mul_right 2 l).mul_right _).mul_right _, hM⟩
  · exact dS ▸ Nat.mem_primeFactors.2 ⟨hl, ((dvd_mul_left l 2).mul_right _).mul_right _, hM⟩
  · rw [dψ]
    exact dirG_unr ψ (haw A hA _ 1 (NeZero.ne _) (by rw [pow_one]; exact (dvd_mul_left _ _).mul_right _))
  · rw [ePsi]
    exact ((psiBar Ω l c _ hom h.N ψ).2.1 e).1 hev _ dcc
  · rw [dξ]
    exact Subgroup.isOpen_mono (H₁ := _ ⊓ _) (fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mem_ker.1 hg.1, MonoidHom.mem_ker.1 hg.2, mul_one])
      (IsOpen.inter (dirG_open ξ₀) (dirG_open ξ))
  · refine ⟨(l ^ f0 l ψ - 1) * Nat.totient (2 ^ n), Nat.Coprime.mul_right ?_ ?_, ?_⟩
    · exact Nat.Coprime.coprime_dvd_left (dvd_pow_self l f1.ne') ((Nat.coprime_self_sub_right (Nat.one_le_pow _ _ hl.pos)).2 (by simp))
    · rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
      simpa using Nat.Coprime.pow_right _ ((Nat.coprime_primes hl Nat.prime_two).2 hl2)
    · rw [dξ, mul_pow, pow_mul, dirG_pow_one _ o3, one_pow, one_mul, mul_comm, pow_mul]
      have : Chr.dirG ℚ Ω ξ ^ Nat.totient (2 ^ n) = 1 := MonoidHom.ext fun g => by
        rw [MonoidHom.pow_apply, Chr.dirG, MonoidHom.comp_apply, ← map_pow, ZMod.pow_totient, map_one, MonoidHom.one_apply]
      rw [this, one_pow]
  · intro g hg
    rw [dξ, MonoidHom.mem_ker, MonoidHom.mul_apply,
      MonoidHom.mem_ker.1 (dirG_unr ξ₀ (haw A hA _ 1 (NeZero.ne _) (by rw [pow_one]; exact dvd_mul_left _ _)) hg),
      MonoidHom.mem_ker.1 (dirG_unr ξ (haw A hA _ n (NeZero.ne _)
        (pow_dvd_pow_of_dvd (((dvd_mul_right 2 l).mul_right _).mul_right _) n)) hg), mul_one]
  · intro g hg
    rw [dξ, MonoidHom.mem_ker, MonoidHom.mul_apply,
      MonoidHom.mem_ker.1 (dirG_unr ξ₀ (not_over (hT' v hv).1 (hT' v hv).2 (hpT v (hTb v hv))) hg),
      MonoidHom.mem_ker.1 (dirG_unr ξ (not_over (hT' v hv).1 (hT' v hv).2 (h2n v hv)) hg), mul_one]
  · refine Units.ext ?_
    rw [dξ, MonoidHom.mul_apply, Units.val_mul, dirG_cc _ dcc, dirG_cc _ dcc, ev0, hξo, one_mul, Units.val_neg, Units.val_one]
  · intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl
    · refine xvOf hX D hT' (d := f0 l ψ) (N := h.N) (k := 0) 1 1 1 ξ₀ ξ hlo hp ?_ f1 f2 (one_pow _) (one_pow _) o3 ?_ (by omega) hξ ?_ ?_ _
        fun g => ?_
      · rw [DirichletCharacter.conductor_one]; exact odd_one
      · rw [DirichletCharacter.conductor_one, pow_zero]
      · rw [DirichletCharacter.conductor_one]
        exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ t5.pos)) big
      · rw [even_of_odd (pow_one _) odd_one, even_of_odd (pow_one _) odd_one, ev0, hξo]; simp
      · simp only [Raw.bar, dirG_one, Units.val_one, map_one, one_mul]
        exact congrArg Units.val (ral g)
    · refine xvOf hX D hT' (ω ^ e) (th1 l ψ) (psi2 ψ) ξ₀⁻¹ ξ⁻¹ hlo hp t5 f1 f2 o1 f3 (by rw [inv_pow, o3, inv_one]) hc2 hcn
        ((DirichletCharacter.conductor_inv ξ).trans hξ) big ?_ _ fun g => ?_
      · rw [sg, inv_at_neg, inv_at_neg, ev0, hξo]; simp
      · have : rd c (D.be g) = rd c (Chr.dirG ℚ Ω (ω ^ e) g) * (rd c (Chr.dirG ℚ Ω (psi2 ψ) g) * rd c (Chr.dirG ℚ Ω (th1 l ψ) g)) *
            (rd c (Chr.dirG ℚ Ω ξ₀⁻¹ g) * rd c (Chr.dirG ℚ Ω ξ⁻¹ g)) := by
          rw [show D.be g = D.Psi g * (D.al g)⁻¹ from rfl, map_mul, map_inv, rPsi, ral, mul_inv, dirG_inv, dirG_inv,
            MonoidHom.inv_apply, MonoidHom.inv_apply, map_inv, map_inv]
        exact congrArg Units.val this
    · refine xvOf hX D hT' (ω ^ e) (th1 l ψ) (psi2 ψ) ξ₀ ξ hlo hp t5 f1 f2 o1 f3 o3 hc2 hcn hξ big ?_ _ fun g => ?_
      · rw [sg, ev0, hξo]; simp
      · have : rd c (D.th g) = rd c (Chr.dirG ℚ Ω (ω ^ e) g) * (rd c (Chr.dirG ℚ Ω (psi2 ψ) g) * rd c (Chr.dirG ℚ Ω (th1 l ψ) g)) *
            (rd c (Chr.dirG ℚ Ω ξ₀ g) * rd c (Chr.dirG ℚ Ω ξ g)) := by
          rw [show D.th g = D.al g * D.Psi g from rfl, map_mul, rPsi, ral, mul_comm]
        exact congrArg Units.val this

end Gal

/- English proof (translation)
Use `haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩`. Establish `h1 : χ.primitiveCharacter ^ Nat.totient χ.conductor = 1`. Use extensionality with `u`. Rewrite using `[MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one, MulChar.one_apply_coe]`. Establish `h2 : Nat.totient χ.conductor ∣ 2 ^ k`.

Rewrite using `[h]`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Nat.totient_prime_pow Nat.prime_two hk]`. Simplify using `using pow_dvd_pow 2 (Nat.sub_le k 1)`.

Take `⟨j, hj⟩` from `h2`. Rewrite using `[← χ.changeLevel_primitiveCharacter, ← map_pow, hj, pow_mul, h1, one_pow, map_one]`.
-/
private theorem pow_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {k : ℕ}
    (h : χ.conductor = 2 ^ k) : χ ^ 2 ^ k = 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h1 : χ.primitiveCharacter ^ Nat.totient χ.conductor = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one,
      MulChar.one_apply_coe]
  have h2 : Nat.totient χ.conductor ∣ 2 ^ k := by
    rw [h]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two hk]
      simpa using pow_dvd_pow 2 (Nat.sub_le k 1)
  obtain ⟨j, hj⟩ := h2
  rw [← χ.changeLevel_primitiveCharacter, ← map_pow, hj, pow_mul, h1, one_pow, map_one]

/- English proof (translation)
Introduce `hX Ω _ _ _ h t hB l hl c e hl2 he0 het ψ hmem hc r2 r3`. Take `⟨hψ, hev⟩` from `h.mem_X.1 hmem`. Establish `hlp : l.Prime` using `hl.out`. Establish `hq : 0 < h.q` using `NeZero.pos _`. Take `⟨tψ, ⟨s, hs⟩, -, -, -, f3, -⟩` from `X.th1Facts c.O h.N ψ l hlp hl2`.

Take `⟨-, t2, t3, -⟩` from `hostTh1 h c.O ψ hψ l hlp hl2`. Break down `hc with hc | hc` into its components or cases. Establish `ho : 0 < h.o` using `orderOf_pos _`. Take `⟨b1, b2⟩` from `max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nII l ψ)`. Establish `hn : c2 ψ + 6 ≤ h.nII l ψ` using `(Nat.pow_le_pow_iff_right one_lt_two).1 (le_trans (by`.

Rewrite using `[mul_assoc, mul_assoc]`. Conclude with `Nat.le_mul_of_pos_right _ (by have := hlp.pos; positivity)) b2)`. Take `⟨ξ, hξ, hξo⟩` from `UpperTheory.exists_primitive_odd_dirichletCharacter_two_pow c.O _ (by omega) r2`. Use `(core (Ω := Ω) hX h e hl2 hc.1 ψ hψ hev (fun h1 => by simpa [EV, h1] using hc.2.1) odd_one (1 : DirichletCharacter c.O 1) ξ hξ hξo (a := c2 ψ + 1 + h.o.factorization 2) (u := ordCompl[2] h.o * l ^ s) (fun v hv hd => ?_) (one_pow _) (even_of_odd (pow_one _) odd_one) (by omega) ?_ …` and prove the remaining obligations. Rewrite `hv` using `[Nat.dvd_one.1 hd]`.

Break down `Finset.mem_insert.1 hv with h1 | h1` into its components or cases. Conclude with `hlp.ne_one h1.symm`. Conclude with `((hostSb h c.O ψ hψ l hlp hl2).1 1 h1).1.ne_one rfl`. Rewrite using `[one_mul]`. Conclude with `le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_of_dvd h.N_pos (th1 l ψ).conductor_dvd_level))) b1`.

Conclude with `(Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (Nat.not_dvd_ordCompl Nat.prime_two ho.ne'))).mul (hlp.odd_of_ne_two hl2).pow`. Establish `e1 : 2 ^ (c2 ψ + 1 + h.o.factorization 2) * (ordCompl[2] h.o * l ^ s) = 2 ^ c2 ψ * (2 * h.o) * l ^ s` using `by conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self h.o 2]`. Expand and normalize the polynomial expressions, which then agree. Establish `p1` using `pow_cond (psi2 ψ) (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.1.symm`. Establish `p2` using `orderOf_dvd_iff_pow_eq_one.1 t3`.

Rewrite using `[e1]`. Generalize the expression as in `c2 ψ = k at p1 ⊢`. Establish `p3 : (psi2 ψ * th1 l ψ * kap l ψ) ^ (2 ^ k * (2 * h.o) * l ^ s) = 1`. Rewrite using `[mul_pow, mul_pow, mul_assoc (2 ^ k), pow_mul, p1, one_pow, one_mul, mul_left_comm, pow_mul, p2, one_pow, one_mul, ← mul_assoc, mul_comm, pow_mul, hs, one_pow]`. Rewrite `p3` using `[← tψ]`. Then use the resulting hypothesis.

Establish `v1 : v ≤ l * h.q` using `Nat.le_of_dvd (Nat.mul_pos hlp.pos hq) ((hostSb h c.O ψ hψ l hlp hl2).2.2.2.2 v hv)`. Establish `v2 : 2 ^ h.o.factorization 2 ≤ h.o` using `Nat.ordProj_le 2 ho.ne'`. Use `le_trans ?_ b2` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Evaluate the numerical expressions.

Use linear arithmetic over natural numbers and integers. Conclude with `hlp.one_le`. Use `_ = _ := by ring`. Take `⟨c1, c2', c3, c4⟩` from `hc`. Take `⟨-, -, -, -, hb⟩` from `bchiFacts h t hB`.

Take `⟨-, n1, -, -, -, n2, -, n3⟩` from `hb l hlp hl2 c1`. Take `⟨e2, -, n4⟩` from `n3 e he0 het c2'`. Take `⟨-, ⟨p1, p2, p3⟩, -⟩` from `pK_pOne_prime_conditions h.chi`. Take `⟨k1, k2, k3, -, k5⟩` from `(hostOdd h c.O ψ hψ).1 c3`. Take `⟨kk, k0⟩ : kap l ψ = 1 ∧ th0 l ψ = ψ` from `(partOrd _ l hlp ψ c3.pos).2.2.2.2.2.1 fun hd => n1 (hd.trans (k1.trans (Nat.ordCompl_dvd _ _)))`.

Establish `k6 : th1 l ψ = ψ` using `by rw [k0, k2, one_mul] at t2; exact t2.symm`. Establish `k7 : chiP l ψ = ψ`. Rewrite using `[chiP, k0, ((compAlg c.O h.N l hlp).2.2.2.2.2.1 ψ).2.2.1 n4, inv_one, mul_one]`. Establish `k8 : ∀ v ∈ Tb l ψ, v = l` using `fun v hv => (Finset.mem_insert.1 hv).resolve_right fun h1 => by`. Establish `h2` using `((hostSb h c.O ψ hψ l hlp hl2).1 v h1).1`.

Simplify using `only [Sb, Finset.mem_filter, kk] at h1`. Conclude with `h1.2.2 (compAlg c.O h.N v h2).2.2.1`. Use `haveI : NeZero (pOne h.chi) := ⟨p1.ne_zero⟩`. Take `⟨b1, b2⟩` from `max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nIII l ψ)`. Establish `hn : 3 ≤ h.nIII l ψ` using `(Nat.pow_le_pow_iff_right one_lt_two).1 (le_trans (Nat.le_mul_of_pos_right _ (pow_pos hlp.pos 2)) b2)`.

Take `⟨ξ, hξ, hξo⟩` from `UpperTheory.exists_primitive_odd_dirichletCharacter_two_pow c.O _ hn r3`. Take `⟨ξ₀, h0⟩` from `UpperTheory.exists_dirichletCharacter_prime_of_orderOf_dvd c.O h.N ψ _ p1 (k1.trans ((Nat.modEq_iff_dvd' p1.one_le).1 p2.symm))`. Establish `h1 : ξ₀ ^ orderOf ψ = 1` using `h0 ▸ pow_orderOf_eq_one ξ₀`. Use `(core (Ω := Ω) hX h e hl2 e2 ψ hψ hev (k7.trans_ne c4) (Nat.coprime_two_right.1 ((p3.coprime_mul_right_right).coprime_mul_right_right)) ξ₀ ξ hξ hξo (a := 0) (u := orderOf ψ) (fun v hv hd => ?_) ?_ (even_of_odd h1 c3) (by omega) ?_ c3 (by simp) (by simpa using h1) fun v hv => ?_). …` and prove the remaining obligations. Rewrite `hd` using `[k8 v hv]`.

Conclude with `n2 ((Nat.prime_dvd_prime_iff_eq hlp p1).1 hd)`. Use `orderOf_dvd_iff_pow_eq_one.1 (h0.dvd.trans (orderOf_dvd_of_pow_eq_one ?_))` and prove the remaining obligations. Generalize the expression as in `l ^ f0 l ψ - 1 = m at f3`. Rewrite `f3` using `[k6]`. Then use the resulting hypothesis. Use `le_trans (Nat.mul_le_mul_right _ ?_) b1` and prove the remaining obligations.

Rewrite using `[k6, mul_assoc, mul_comm]`. Conclude with `Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_of_dvd hq k5))`. Rewrite using `[k8 v hv, pow_zero, mul_one]`. Conclude with `le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) b2`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.dataEx :
    X.CorX → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, h.CaseII l e ψ ∨ h.CaseIII l e ψ → HasEnoughRootsOfUnity c.O (2 ^ h.nII l ψ) → HasEnoughRootsOfUnity c.O (2 ^ h.nIII l ψ) → ∃ D : Raw Ω c, D.Good ∧ Aut.OfCase D h e ψ := by
  intro hX Ω _ _ _ h t hB l hl c e hl2 he0 het ψ hmem hc r2 r3
  obtain ⟨hψ, hev⟩ := h.mem_X.1 hmem
  have hlp : l.Prime := hl.out
  have hq : 0 < h.q := NeZero.pos _
  obtain ⟨tψ, ⟨s, hs⟩, -, -, -, f3, -⟩ := X.th1Facts c.O h.N ψ l hlp hl2
  obtain ⟨-, t2, t3, -⟩ := hostTh1 h c.O ψ hψ l hlp hl2
  rcases hc with hc | hc
  · have ho : 0 < h.o := orderOf_pos _
    obtain ⟨b1, b2⟩ := max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nII l ψ)
    have hn : c2 ψ + 6 ≤ h.nII l ψ := (Nat.pow_le_pow_iff_right one_lt_two).1 (le_trans (by
      rw [mul_assoc, mul_assoc]
      exact Nat.le_mul_of_pos_right _ (by have := hlp.pos; positivity)) b2)
    obtain ⟨ξ, hξ, hξo⟩ := UpperTheory.exists_primitive_odd_dirichletCharacter_two_pow c.O _ (by omega) r2
    refine (core (Ω := Ω) hX h e hl2 hc.1 ψ hψ hev (fun h1 => by simpa [EV, h1] using hc.2.1) odd_one
      (1 : DirichletCharacter c.O 1) ξ hξ hξo (a := c2 ψ + 1 + h.o.factorization 2) (u := ordCompl[2] h.o * l ^ s)
      (fun v hv hd => ?_) (one_pow _) (even_of_odd (pow_one _) odd_one) (by omega) ?_ ?_ ?_ (one_pow _) fun v hv => ?_).imp
      fun D hD => ⟨hD.1, Or.inl ⟨hc, by simpa only [orderOf_one] using hD.2⟩⟩
    · rw [Nat.dvd_one.1 hd] at hv
      rcases Finset.mem_insert.1 hv with h1 | h1
      · exact hlp.ne_one h1.symm
      · exact ((hostSb h c.O ψ hψ l hlp hl2).1 1 h1).1.ne_one rfl
    · rw [one_mul]
      exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (Nat.le_of_dvd h.N_pos (th1 l ψ).conductor_dvd_level))) b1
    · exact (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (Nat.not_dvd_ordCompl Nat.prime_two ho.ne'))).mul (hlp.odd_of_ne_two hl2).pow
    · have e1 : 2 ^ (c2 ψ + 1 + h.o.factorization 2) * (ordCompl[2] h.o * l ^ s) = 2 ^ c2 ψ * (2 * h.o) * l ^ s := by
        conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self h.o 2]
        ring
      have p1 := pow_cond (psi2 ψ) (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.1.symm
      have p2 := orderOf_dvd_iff_pow_eq_one.1 t3
      rw [e1]
      generalize c2 ψ = k at p1 ⊢
      have p3 : (psi2 ψ * th1 l ψ * kap l ψ) ^ (2 ^ k * (2 * h.o) * l ^ s) = 1 := by
        rw [mul_pow, mul_pow, mul_assoc (2 ^ k), pow_mul, p1, one_pow, one_mul, mul_left_comm, pow_mul, p2, one_pow, one_mul,
          ← mul_assoc, mul_comm, pow_mul, hs, one_pow]
      rwa [← tψ] at p3
    · have v1 : v ≤ l * h.q := Nat.le_of_dvd (Nat.mul_pos hlp.pos hq) ((hostSb h c.O ψ hψ l hlp hl2).2.2.2.2 v hv)
      have v2 : 2 ^ h.o.factorization 2 ≤ h.o := Nat.ordProj_le 2 ho.ne'
      refine le_trans ?_ b2
      calc v ^ 2 * 2 ^ (c2 ψ + 1 + h.o.factorization 2) = v ^ 2 * 2 ^ h.o.factorization 2 * 2 ^ (c2 ψ + 1) * 1 := by ring
        _ ≤ (l * h.q) ^ 2 * h.o * 2 ^ (c2 ψ + 6) * l := by
          gcongr
          · norm_num
          · omega
          · exact hlp.one_le
        _ = _ := by ring
  · obtain ⟨c1, c2', c3, c4⟩ := hc
    obtain ⟨-, -, -, -, hb⟩ := bchiFacts h t hB
    obtain ⟨-, n1, -, -, -, n2, -, n3⟩ := hb l hlp hl2 c1
    obtain ⟨e2, -, n4⟩ := n3 e he0 het c2'
    obtain ⟨-, ⟨p1, p2, p3⟩, -⟩ := pK_pOne_prime_conditions h.chi
    obtain ⟨k1, k2, k3, -, k5⟩ := (hostOdd h c.O ψ hψ).1 c3
    obtain ⟨kk, k0⟩ : kap l ψ = 1 ∧ th0 l ψ = ψ := (partOrd _ l hlp ψ c3.pos).2.2.2.2.2.1 fun hd =>
      n1 (hd.trans (k1.trans (Nat.ordCompl_dvd _ _)))
    have k6 : th1 l ψ = ψ := by rw [k0, k2, one_mul] at t2; exact t2.symm
    have k7 : chiP l ψ = ψ := by
      rw [chiP, k0, ((compAlg c.O h.N l hlp).2.2.2.2.2.1 ψ).2.2.1 n4, inv_one, mul_one]
    have k8 : ∀ v ∈ Tb l ψ, v = l := fun v hv => (Finset.mem_insert.1 hv).resolve_right fun h1 => by
      have h2 := ((hostSb h c.O ψ hψ l hlp hl2).1 v h1).1
      simp only [Sb, Finset.mem_filter, kk] at h1
      exact h1.2.2 (compAlg c.O h.N v h2).2.2.1
    haveI : NeZero (pOne h.chi) := ⟨p1.ne_zero⟩
    obtain ⟨b1, b2⟩ := max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nIII l ψ)
    have hn : 3 ≤ h.nIII l ψ := (Nat.pow_le_pow_iff_right one_lt_two).1 (le_trans
      (Nat.le_mul_of_pos_right _ (pow_pos hlp.pos 2)) b2)
    obtain ⟨ξ, hξ, hξo⟩ := UpperTheory.exists_primitive_odd_dirichletCharacter_two_pow c.O _ hn r3
    obtain ⟨ξ₀, h0⟩ := UpperTheory.exists_dirichletCharacter_prime_of_orderOf_dvd c.O h.N ψ _ p1 (k1.trans ((Nat.modEq_iff_dvd' p1.one_le).1 p2.symm))
    have h1 : ξ₀ ^ orderOf ψ = 1 := h0 ▸ pow_orderOf_eq_one ξ₀
    refine (core (Ω := Ω) hX h e hl2 e2 ψ hψ hev (k7.trans_ne c4)
      (Nat.coprime_two_right.1 ((p3.coprime_mul_right_right).coprime_mul_right_right)) ξ₀ ξ hξ hξo (a := 0) (u := orderOf ψ)
      (fun v hv hd => ?_) ?_ (even_of_odd h1 c3) (by omega) ?_ c3 (by simp) (by simpa using h1) fun v hv => ?_).imp
      fun D hD => ⟨hD.1, Or.inr ⟨⟨c1, c2', c3, c4⟩, h0 ▸ hD.2⟩⟩
    · rw [k8 v hv] at hd
      exact n2 ((Nat.prime_dvd_prime_iff_eq hlp p1).1 hd)
    · refine orderOf_dvd_iff_pow_eq_one.1 (h0.dvd.trans (orderOf_dvd_of_pow_eq_one ?_))
      generalize l ^ f0 l ψ - 1 = m at f3
      rwa [k6] at f3
    · refine le_trans (Nat.mul_le_mul_right _ ?_) b1
      rw [k6, mul_assoc, mul_comm]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_of_dvd hq k5))
    · rw [k8 v hv, pow_zero, mul_one]
      exact le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) b2

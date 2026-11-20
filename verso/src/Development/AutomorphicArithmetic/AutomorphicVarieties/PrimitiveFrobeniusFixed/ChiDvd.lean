import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Use `haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Use `haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' hl.one_lt⟩`.

Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩`. Use `haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance`. Establish `h1 : (1 : ZMod (l ^ n)) = modularCyclotomicCharacter Ω (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (l ^ n)) (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)`.

Apply `modularCyclotomicCharacter.unique` to reduce the goal to its premises. Introduce `t ht`. Rewrite using `[ZMod.val_one, pow_one]`. Rewrite `ht` using `[mem_rootsOfUnity]`. Conclude with `h (t : Ω) (by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one])`.

Establish `h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)).val.toZModPow n = 1`. Rewrite using `[cyclotomicCharacter.toZModPow, ← h1]`. Establish `h3 : (l : ℤ_[l]) ^ n ∣ (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)).val - 1`. Rewrite using `[← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h2, map_one, sub_self]`. Establish `h4` using `map_dvd (algebraMap ℤ_[l] O) h3`.

Simplify `h4` using `[chiO, cycZ]`.
-/
private theorem chi_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [Algebra ℤ_[l] O] (n : ℕ) (g : G ℚ Ω) (h : g ∈ fixMu ℚ Ω (l ^ n)) :
    (l : O) ^ n ∣ (chiO ℚ Ω l O g : O) - 1 := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' hl.one_lt⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have h1 : (1 : ZMod (l ^ n)) = modularCyclotomicCharacter Ω
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (l ^ n)) (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) := by
    apply modularCyclotomicCharacter.unique
    intro t ht
    rw [ZMod.val_one, pow_one]
    rw [mem_rootsOfUnity] at ht
    exact h (t : Ω) (by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one])
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)).val.toZModPow n = 1 := by
    rw [cyclotomicCharacter.toZModPow, ← h1]
  have h3 : (l : ℤ_[l]) ^ n ∣ (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)).val - 1 := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h2, map_one, sub_self]
  have h4 := map_dvd (algebraMap ℤ_[l] O) h3
  simpa [chiO, cycZ] using h4

/- English proof (translation)
Introduce `hRec Ω _ _ _ l _ O _ _ _ _ _ N₀ m F N q α hD hFN hN hq hq1 ν hν δ a₀ a w₀ ha₀a hal hw₀ hνa c hc hyp A hA g hg τ hτ y hy`. Take `⟨⟨hlc, hcoc⟩, -, hac0, hunrc, hlocc⟩` from `hc`. Establish `hl : l.Prime` using `Fact.out`. Establish `hF : F ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hN (zero_dvd_iff.mp hFN)`. Establish `hlmF : l ^ m ∣ F` using `Dvd.intro_left N₀ hD.lev.symm`. Establish `hlF : l ∣ F` using `(dvd_pow_self l (by have := hD.pos; omega)).trans hlmF`. Establish `hlN : l ∣ N` using `hlF.trans hFN`. Establish `hql : q ≠ l`.

Introduce `hql`. Establish `h` using `hq1.of_dvd hlF`. Rewrite `h` using `[hql]`. Unfold `Nat.ModEq at h`. Rewrite `h` using `[Nat.mod_self, Nat.mod_eq_of_lt hl.one_lt]`.

Conclude with `absurd h (by norm_num)`. Take `⟨-, hopen, -, -, -, -, -, -, -, -⟩` from `galBasic Ω F hF`. Take `⟨-, hfrobEx, hoverMul, hcopNot, hIne, -, hPows, -, hplace, -⟩` from `placeBasic Ω`. Establish `hcop : q.Coprime F` using `hq1.gcd_eq.trans (Nat.gcd_one_left F)`. Establish `hAF : ¬Over A F` using `hcopNot A q F hcop hA`.

Establish `hIneA : Ine A ≤ fixMu ℚ Ω F` using `hIne A F hAF`. Establish `hdivA : ∀ x ∈ fixMu ℚ Ω F, a ∣ (α x : O) - 1` using `fun x hx => hal.trans (hD.triv x hx)`. Establish `hl0 : (l : O) ≠ 0`. Take `⟨hinj, -⟩` from `dvrFacts l O`. Introduce `h0`.

Establish `h1 : algebraMap ℤ_[l] O (l : ℤ_[l]) = algebraMap ℤ_[l] O 0` using `by simpa using h0`. Conclude with `(Nat.cast_ne_zero.mpr hl.ne_zero : (l : ℤ_[l]) ≠ 0) (hinj h1)`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `pow_ne_zero m hl0 (zero_dvd_iff.mp hal)`.

Set `S : Subgroup (G ℚ Ω)` to `{ carrier := {x | a ∣ (α x : O) - 1} mul_mem' := fun {x z} hx hz => by`. Establish `e : (α (x * z) : O) - 1 = (α x : O) * ((α z : O) - 1) + ((α x : O) - 1)`. Rewrite using `[map_mul, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `show a ∣ (α (x * z) : O) - 1`.

Rewrite using `[e]`. Conclude with `dvd_add (dvd_mul_of_dvd_right hz _) hx`. Use the proof step `one_mem' := by show a ∣ (α 1 : O) - 1`. Simplify using the standard rewrite rules. Use the proof step `inv_mem' := fun {x} hx => by`.

Establish `hxx : (α x⁻¹ : O) * (α x : O) = 1`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Establish `e : (α x⁻¹ : O) - 1 = -(α x⁻¹ : O) * ((α x : O) - 1)`. Take the linear combination `hxx`. Use `show a ∣ (α x⁻¹ : O) - 1`.

Rewrite using `[e]`. Conclude with `dvd_mul_of_dvd_right hx _ }`. Establish `hSo : IsOpen {x : G ℚ Ω | a ∣ (α x : O) - 1}` using `Subgroup.isOpen_mono (H₁ := fixMu ℚ Ω F) (H₂ := S) (fun x hx => hdivA x hx) hopen`. Take `⟨φ, hφ⟩` from `hfrobEx A q hq hA`. Establish `hφF : φ ∈ fixMu ℚ Ω F`.

Introduce `z hz`. Rewrite using `[hPows A q F φ hφ hAF z hz, pow_eq_pow_mod q hz, hq1, ← pow_eq_pow_mod 1 hz, pow_one]`. Take `⟨v, hv, hnv, -⟩` from `hplace A q hq hA`. Establish `hfr : IsFrob A (normV v) φ` using `by rw [hnv]; exact hφ`. Establish `hDecA : Dec A ≤ fixMu ℚ Ω F` using `Kum.decGen ℚ Ω A v φ (fixMu ℚ Ω F) hv hfr hopen hIneA hφF`.

Take `⟨δ', hδ'⟩` from `hD.notCyc`. Establish `hβ : IsUnit (((dualChar l α) δ' : O) - 1)`. Establish `hu : (((α δ')⁻¹ : Oˣ) : O) * (α δ' : O) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `e : ((dualChar l α) δ' : O) - 1 = -(((α δ')⁻¹ : Oˣ) : O) * ((α δ' : O) - (chiO ℚ Ω l O δ' : O))`.

Simplify using `only [dualChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]`. Take the linear combination `hu`. Rewrite using `[e]`. Conclude with `(Units.isUnit _).neg.mul hδ'`. Take `⟨n, hncoc, hnν, hnform⟩` from `ext Ω O (QO l O) (l ^ m) F (N * q) hF (dualChar l α) ν hν δ' hβ`.

Establish `han : ∀ x, a • n x = 0`. Introduce `x`. Take `⟨u, hu, z, hz⟩` from `hnform x`. Rewrite using `[hz, smul_comm, hνa u hu, smul_zero]`. Establish `hac : ∀ x, a • c x = 0`.

Introduce `x`. Take `⟨k, hk⟩` from `ha₀a`. Rewrite using `[hk, mul_comm, mul_smul, hac0, smul_zero]`. Establish `hnotF : ∀ B : ValuationSubring Ω, ¬Over B (N * q) → ¬Over B F`. Introduce `B hB hBF`.

Take `⟨k, hk⟩` from `hFN`. Conclude with `hB ((hoverMul B N q).mpr (Or.inl (by rw [hk]; exact (hoverMul B F k).mpr (Or.inl hBF))))`. Establish `hunr : ∀ B : ValuationSubring Ω, ¬Over B (N * q) → ∀ x ∈ Ine B, a ∣ (α x : O) - 1 ∧ c x = 0 ∧ n x = 0`. Introduce `B hB x hx`. Establish `hBF` using `hnotF B hB`.

Establish `hxF` using `hIne B F hBF hx`. Conclude with `⟨hdivA x hxF, hunrc B hBF x hx, by rw [hnν x hxF]; exact hν.unr B hB x hx⟩`. Establish `hloc : ∀ B : ValuationSubring Ω, Over B N → ¬Over B q → ∃ w, a • w = 0 ∧ ∀ x ∈ Dec B, c x = (α x : O) • w - w`. Introduce `B hBN hBq`. Distinguish the cases in `hBF : Over B F`.

Take `⟨w, hw, hw'⟩` from `hlocc B hBF`. Take `⟨k, hk⟩` from `ha₀a`. Conclude with `⟨w, by rw [hk, mul_comm, mul_smul, hw, smul_zero], hw'⟩`. Conclude with `⟨0, smul_zero _, fun x hx => by rw [hyp B hBN hBF hBq x hx, smul_zero, sub_zero]⟩`. Establish `hdec : ∀ x ∈ Dec A, a ∣ (α x : O) - 1 ∧ a ∣ ((dualChar l α) x : O) - 1`.

Introduce `x hx`. Establish `hxF` using `hDecA hx`. Use `⟨hdivA x hxF, ?_⟩` and prove the remaining obligations. Establish `hxl : x ∈ fixMu ℚ Ω (l ^ m)` using `fixMu_le ℚ Ω hlmF hxF`. Establish `h1` using `chi_dvd Ω l O m x hxl`.

Establish `h2` using `hdivA x⁻¹ (inv_mem hxF)`. Establish `e : ((dualChar l α) x : O) - 1 = (chiO ℚ Ω l O x : O) * ((α x⁻¹ : O) - 1) + ((chiO ℚ Ω l O x : O) - 1)`. Simplify using `only [dualChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `dvd_add (dvd_mul_of_dvd_right h2 _) (hal.trans h1)`. Establish `hine : ∀ x ∈ Ine A, c x = 0` using `fun x hx => hunrc A hAF x hx`. Establish `hnτ : n τ = y • w₀` using `by rw [hnν τ (hIneA hτ)]; exact hy`. Conclude with `hRec Ω l hD.odd_l O α a ha0 w₀ hw₀ hSo N q hN hlN hq hql c n ⟨hlc, hcoc⟩ hncoc hac han hunr hloc A hA hdec hine g hg τ hτ y hnτ`.
-/
theorem UpperTheory.V.ML.step :
    Rec → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F N q : ℕ) (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → F ∣ N → N ≠ 0 → q.Prime → q ≡ 1 [MOD F] →
    ∀ ν : G ℚ Ω → QO l O, IsNu (l ^ m) F (N * q) (dualChar l α) ν → ∀ (δ : G ℚ Ω) (a₀ a : O) (w₀ : QO l O), a₀ ∣ a → a ∣ (l : O) ^ m → (∀ y : O, y • w₀ = 0 ↔ a ∣ y) →
    (∀ u ∈ fixMu ℚ Ω F, a • ν u = 0) → ∀ c ∈ ShT (QO l O) α δ F a₀,
    (∀ A : ValuationSubring Ω, Over A N → ¬ Over A F → ¬ Over A q → ∀ g ∈ Dec (F := ℚ) A, c g = 0) →
    ∀ A : ValuationSubring Ω, Over A q → ∀ g ∈ Dec (F := ℚ) A, ∀ τ ∈ Ine (F := ℚ) A, ∀ y : O, ν τ = y • w₀ → y • c g = 0 := by
  intro hRec Ω _ _ _ l _ O _ _ _ _ _ N₀ m F N q α hD hFN hN hq hq1 ν hν δ a₀ a w₀ ha₀a hal hw₀ hνa c hc hyp A hA g hg τ hτ y hy
  obtain ⟨⟨hlc, hcoc⟩, -, hac0, hunrc, hlocc⟩ := hc
  have hl : l.Prime := Fact.out
  have hF : F ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.mp hFN)
  have hlmF : l ^ m ∣ F := Dvd.intro_left N₀ hD.lev.symm
  have hlF : l ∣ F := (dvd_pow_self l (by have := hD.pos; omega)).trans hlmF
  have hlN : l ∣ N := hlF.trans hFN
  have hql : q ≠ l := by
    intro hql
    have h := hq1.of_dvd hlF
    rw [hql] at h
    unfold Nat.ModEq at h
    rw [Nat.mod_self, Nat.mod_eq_of_lt hl.one_lt] at h
    exact absurd h (by norm_num)
  obtain ⟨-, hopen, -, -, -, -, -, -, -, -⟩ := galBasic Ω F hF
  obtain ⟨-, hfrobEx, hoverMul, hcopNot, hIne, -, hPows, -, hplace, -⟩ := placeBasic Ω
  have hcop : q.Coprime F := hq1.gcd_eq.trans (Nat.gcd_one_left F)
  have hAF : ¬Over A F := hcopNot A q F hcop hA
  have hIneA : Ine A ≤ fixMu ℚ Ω F := hIne A F hAF
  have hdivA : ∀ x ∈ fixMu ℚ Ω F, a ∣ (α x : O) - 1 := fun x hx => hal.trans (hD.triv x hx)
  have hl0 : (l : O) ≠ 0 := by
    obtain ⟨hinj, -⟩ := dvrFacts l O
    intro h0
    have h1 : algebraMap ℤ_[l] O (l : ℤ_[l]) = algebraMap ℤ_[l] O 0 := by simpa using h0
    exact (Nat.cast_ne_zero.mpr hl.ne_zero : (l : ℤ_[l]) ≠ 0) (hinj h1)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact pow_ne_zero m hl0 (zero_dvd_iff.mp hal)
  let S : Subgroup (G ℚ Ω) :=
    { carrier := {x | a ∣ (α x : O) - 1}
      mul_mem' := fun {x z} hx hz => by
        have e : (α (x * z) : O) - 1 = (α x : O) * ((α z : O) - 1) + ((α x : O) - 1) := by
          rw [map_mul, Units.val_mul]; ring
        show a ∣ (α (x * z) : O) - 1
        rw [e]
        exact dvd_add (dvd_mul_of_dvd_right hz _) hx
      one_mem' := by
        show a ∣ (α 1 : O) - 1
        simp
      inv_mem' := fun {x} hx => by
        have hxx : (α x⁻¹ : O) * (α x : O) = 1 := by
          rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
        have e : (α x⁻¹ : O) - 1 = -(α x⁻¹ : O) * ((α x : O) - 1) := by
          linear_combination hxx
        show a ∣ (α x⁻¹ : O) - 1
        rw [e]
        exact dvd_mul_of_dvd_right hx _ }
  have hSo : IsOpen {x : G ℚ Ω | a ∣ (α x : O) - 1} :=
    Subgroup.isOpen_mono (H₁ := fixMu ℚ Ω F) (H₂ := S) (fun x hx => hdivA x hx) hopen
  obtain ⟨φ, hφ⟩ := hfrobEx A q hq hA
  have hφF : φ ∈ fixMu ℚ Ω F := by
    intro z hz
    rw [hPows A q F φ hφ hAF z hz, pow_eq_pow_mod q hz, hq1, ← pow_eq_pow_mod 1 hz, pow_one]
  obtain ⟨v, hv, hnv, -⟩ := hplace A q hq hA
  have hfr : IsFrob A (normV v) φ := by rw [hnv]; exact hφ
  have hDecA : Dec A ≤ fixMu ℚ Ω F := Kum.decGen ℚ Ω A v φ (fixMu ℚ Ω F) hv hfr hopen hIneA hφF
  obtain ⟨δ', hδ'⟩ := hD.notCyc
  have hβ : IsUnit (((dualChar l α) δ' : O) - 1) := by
    have hu : (((α δ')⁻¹ : Oˣ) : O) * (α δ' : O) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e : ((dualChar l α) δ' : O) - 1 =
        -(((α δ')⁻¹ : Oˣ) : O) * ((α δ' : O) - (chiO ℚ Ω l O δ' : O)) := by
      simp only [dualChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
      linear_combination hu
    rw [e]
    exact (Units.isUnit _).neg.mul hδ'
  obtain ⟨n, hncoc, hnν, hnform⟩ := ext Ω O (QO l O) (l ^ m) F (N * q) hF (dualChar l α) ν hν δ' hβ
  have han : ∀ x, a • n x = 0 := by
    intro x
    obtain ⟨u, hu, z, hz⟩ := hnform x
    rw [hz, smul_comm, hνa u hu, smul_zero]
  have hac : ∀ x, a • c x = 0 := by
    intro x
    obtain ⟨k, hk⟩ := ha₀a
    rw [hk, mul_comm, mul_smul, hac0, smul_zero]
  have hnotF : ∀ B : ValuationSubring Ω, ¬Over B (N * q) → ¬Over B F := by
    intro B hB hBF
    obtain ⟨k, hk⟩ := hFN
    exact hB ((hoverMul B N q).mpr (Or.inl (by rw [hk]; exact (hoverMul B F k).mpr (Or.inl hBF))))
  have hunr : ∀ B : ValuationSubring Ω, ¬Over B (N * q) → ∀ x ∈ Ine B,
      a ∣ (α x : O) - 1 ∧ c x = 0 ∧ n x = 0 := by
    intro B hB x hx
    have hBF := hnotF B hB
    have hxF := hIne B F hBF hx
    exact ⟨hdivA x hxF, hunrc B hBF x hx, by rw [hnν x hxF]; exact hν.unr B hB x hx⟩
  have hloc : ∀ B : ValuationSubring Ω, Over B N → ¬Over B q →
      ∃ w, a • w = 0 ∧ ∀ x ∈ Dec B, c x = (α x : O) • w - w := by
    intro B hBN hBq
    by_cases hBF : Over B F
    · obtain ⟨w, hw, hw'⟩ := hlocc B hBF
      obtain ⟨k, hk⟩ := ha₀a
      exact ⟨w, by rw [hk, mul_comm, mul_smul, hw, smul_zero], hw'⟩
    · exact ⟨0, smul_zero _, fun x hx => by rw [hyp B hBN hBF hBq x hx, smul_zero, sub_zero]⟩
  have hdec : ∀ x ∈ Dec A, a ∣ (α x : O) - 1 ∧ a ∣ ((dualChar l α) x : O) - 1 := by
    intro x hx
    have hxF := hDecA hx
    refine ⟨hdivA x hxF, ?_⟩
    have hxl : x ∈ fixMu ℚ Ω (l ^ m) := fixMu_le ℚ Ω hlmF hxF
    have h1 := chi_dvd Ω l O m x hxl
    have h2 := hdivA x⁻¹ (inv_mem hxF)
    have e : ((dualChar l α) x : O) - 1 =
        (chiO ℚ Ω l O x : O) * ((α x⁻¹ : O) - 1) + ((chiO ℚ Ω l O x : O) - 1) := by
      simp only [dualChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_inv]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right h2 _) (hal.trans h1)
  have hine : ∀ x ∈ Ine A, c x = 0 := fun x hx => hunrc A hAF x hx
  have hnτ : n τ = y • w₀ := by rw [hnν τ (hIneA hτ)]; exact hy
  exact hRec Ω l hD.odd_l O α a ha0 w₀ hw₀ hSo N q hN hlN hq hql c n ⟨hlc, hcoc⟩ hncoc hac han hunr hloc
    A hA hdec hine g hg τ hτ y hnτ

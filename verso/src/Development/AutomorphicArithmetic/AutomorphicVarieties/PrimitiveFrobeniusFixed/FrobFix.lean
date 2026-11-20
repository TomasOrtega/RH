import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.NuSysEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AddPowNsmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ChiDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.QocEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ShtNu
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AdmProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Mathlib.NumberTheory.PrimesCongruentOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

open IsDiscreteValuationRing in
/- English proof (translation)
Establish `hne : IsDiscreteValuationRing.addVal O a ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis. Conclude with `ENat.coe_toNat hne`.
-/
private theorem cast_val {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a : O} (ha : a ≠ 0) :
    (((addVal O a).toNat : ℕ) : ℕ∞) = addVal O a := by
  have hne : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  exact ENat.coe_toNat hne

/- English proof (translation)
Set `I : Submodule O O` to `⨅ u ∈ U, LinearMap.ker (LinearMap.toSpanSingleton O W (ν u))`. Take `⟨a, ha⟩` from `(IsPrincipalIdealRing.principal I).principal`. Use `⟨a, fun y => ?_⟩` and prove the remaining obligations. Establish `hy : y ∈ I ↔ ∀ u ∈ U, y • ν u = 0`. Simplify using `[I, Submodule.mem_iInf]`.

Rewrite using `[← hy, ha, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, rfl⟩`. Conclude with `Dvd.intro_left t rfl`. Introduce and unpack `⟨t, rfl⟩`.

Conclude with `⟨t, by rw [smul_eq_mul, mul_comm]⟩`.
-/
private theorem annEx {O W X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup W] [Module O W]
    (U : Set X) (ν : X → W) : ∃ a : O, ∀ y : O, (∀ u ∈ U, y • ν u = 0) ↔ a ∣ y := by
  classical
  let I : Submodule O O := ⨅ u ∈ U, LinearMap.ker (LinearMap.toSpanSingleton O W (ν u))
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
  refine ⟨a, fun y => ?_⟩
  have hy : y ∈ I ↔ ∀ u ∈ U, y • ν u = 0 := by
    simp [I, Submodule.mem_iInf]
  rw [← hy, ha, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, rfl⟩
    exact Dvd.intro_left t rfl
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [smul_eq_mul, mul_comm]⟩

private def Sn {Ω : Type} [Field Ω] [Algebra ℚ Ω] {O : Type} (W : Type) [CommRing O] [AddCommGroup W] [Module O W]
    (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) (F : ℕ) (a : O) (n : ℕ) : Submodule O (G ℚ Ω → W) where
  carrier := {c | c ∈ ShT W α δ F a ∧ ∀ A : ValuationSubring Ω, Over A n → ∀ g ∈ Dec (F := ℚ) A, c g = 0}
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ _ _ => rfl⟩
  add_mem' {x y} hx hy := ⟨Submodule.add_mem _ hx.1 hy.1, fun A hA g hg => by simp [hx.2 A hA g hg, hy.2 A hA g hg]⟩
  smul_mem' t x hx := ⟨Submodule.smul_mem _ t hx.1, fun A hA g hg => by simp [hx.2 A hA g hg]⟩

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] {N₀ m F : ℕ} {α : G ℚ Ω →* Oˣ}

/- English proof (translation)
Apply `pow_ne_zero` to reduce the goal to its premises. Establish `hinj` using `(UpperTheory.V.Base.dvrFacts l O).1`. Establish `hl : ((l : ℤ_[l])) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`. Introduce `h`. Apply `hl` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Simplify using `using h`.
-/
private theorem lpow_ne (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (m : ℕ) : (l : O) ^ m ≠ 0 := by
  apply pow_ne_zero
  have hinj := (UpperTheory.V.Base.dvrFacts l O).1
  have hl : ((l : ℤ_[l])) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  intro h
  apply hl
  apply hinj
  simpa using h

/- English proof (translation)
The claim follows from `(placeBasic Ω).2.2.2.1 A q F (Nat.coprime_of_mul_modEq_one 1 (by simpa using hq1)) hA`.
-/
private theorem not_over {q : ℕ} (hq1 : q ≡ 1 [MOD F]) {A : ValuationSubring Ω} (hA : Over A q) : ¬ Over A F :=
  (placeBasic Ω).2.2.2.1 A q F (Nat.coprime_of_mul_modEq_one 1 (by simpa using hq1)) hA

/- English proof (translation)
Introduce `x hx` and use `by rw [(placeBasic Ω).2.2.2.2.2.2.1 A q F φ hφ (not_over hq1 hA) x hx, pow_eq_pow_mod q hx, hq1, ← pow_eq_pow_mod 1 hx, pow_one]`.
-/
private theorem frob_fix {q : ℕ} (hq1 : q ≡ 1 [MOD F]) {A : ValuationSubring Ω} (hA : Over A q) {φ : G ℚ Ω}
    (hφ : IsFrob (F := ℚ) A q φ) : φ ∈ fixMu ℚ Ω F := fun x hx => by
  rw [(placeBasic Ω).2.2.2.2.2.2.1 A q F φ hφ (not_over hq1 hA) x hx, pow_eq_pow_mod q hx, hq1, ← pow_eq_pow_mod 1 hx,
    pow_one]

/- English proof (translation)
Establish `hnF : ¬ Over A F` using `not_over hq1 hA`. Establish `hτF : τ ∈ fixMu ℚ Ω F` using `(placeBasic Ω).2.2.2.2.1 A F hnF hτ`. Establish `hlm : ∀ u ∈ fixMu ℚ Ω F, ((l : O) ^ m) • ν u = 0`. Introduce `u hu`. Establish `h` using `hν.tors u hu`.

Rewrite `h` using `[← Nat.cast_smul_eq_nsmul O]`. Simplify using `using h`. Establish `ha'l : a' ∣ (l : O) ^ m` using `(ha' _).1 hlm`. Establish `ha'0 : a' ≠ 0` using `fun h => lpow_ne l O m (zero_dvd_iff.1 (h ▸ ha'l))`. Establish `haa' : a ∣ a'` using `(ha a').1 ((ha' a').2 dvd_rfl τ hτF)`.

Take `⟨e, he⟩` from `haa'`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `ha'0 (by simp [he])`. Establish `ha₀a' : a₀ ∣ a'` using `h0.trans (Dvd.intro e he.symm)`.

Establish `ha₀l : a₀ ∣ (l : O) ^ m` using `ha₀a'.trans ha'l`. Take `⟨w₀, hw₀⟩` from `(qoCyc l O).2.1 a' ha'0`. Take `⟨y, hy⟩` from `(qoCyc l O).2.2.1 a' w₀ ha'0 hw₀ (ν τ) ((ha' a').2 dvd_rfl τ hτF)`. Establish `hkill : ∀ c ∈ Sn (QO l O) α δ F a₀ n, e • c φ = 0`. Introduce `c hc`.

Establish `hyc : y • c φ = 0` using `step hR Ω l O N₀ m F (F * n) q α hD (dvd_mul_right F n) (mul_ne_zero hF hn) hq hq1 ν hν δ a₀ a' w₀ ha₀a' ha'l hw₀ (fun u hu => (ha' a').2 dvd_rfl u hu) c hc.1 (fun A' hA' hA'F _ g hg => hc.2 A' ((((placeBasic Ω).2.2.1 A' F n).1 hA').resolve_left hA'F) g hg) A hA φ hφ.1 τ hτ y hy`. Break down `le_total (IsDiscreteValuationRing.addVal O y) (IsDiscreteValuationRing.addVal O a') with hle | hle` into its components or cases. Rewrite `hle` using `[IsDiscreteValuationRing.addVal_le_iff_dvd]`. Take `⟨t, ht⟩` from `hle`. Establish `hat : a ∣ t` using `(ha t).1 (by rw [hy, smul_smul, mul_comm t y, ← ht]; exact (hw₀ a').2 dvd_rfl)`.

Take `⟨s, rfl⟩` from `hat`. Establish `hes : e = y * s`. Apply `mul_left_cancel₀ ha0` to reduce the goal to its premises. Rewrite using `[← he, ht]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hes, mul_comm, ← smul_smul, hyc, smul_zero]`. Rewrite `hle` using `[IsDiscreteValuationRing.addVal_le_iff_dvd]`. Establish `hντ : ν τ = 0`. Rewrite using `[hy]`. Conclude with `(hw₀ y).2 hle`.

Establish `hu : IsUnit a₀` using `isUnit_of_dvd_one (h0.trans ((ha 1).1 (by rw [hντ, smul_zero])))`. Establish `hcφ : c φ = 0`. Establish `h1 : a₀ • c φ = 0` using `hc.1.2.2.1 φ`. Rewrite `h1` using `[hu.smul_eq_zero]`. Then use the resulting hypothesis. Rewrite using `[hcφ, smul_zero]`.

Establish `hsub : ∀ c ∈ Sn (QO l O) α δ F a₀ n, c φ = 0 → c ∈ Sn (QO l O) α δ F a₀ (n * q)`. Introduce `c hc hcφ`. Use `⟨hc.1, fun A' hA' g hg => ?_⟩` and prove the remaining obligations. Break down `((placeBasic Ω).2.2.1 A' n q).1 hA' with h | h` into its components or cases. Conclude with `hc.2 A' h g hg`.

Conclude with `((shtNu Ω l O N₀ m F α hD δ hδ a₀ ha₀l c hc.1).2.2 q A φ hq hq1 hA hφ hcφ) A' h g hg`. Set `f : Sn (QO l O) α δ F a₀ n →ₗ[O] QO l O` to `(LinearMap.proj φ).comp (Sn (QO l O) α δ F a₀ n).subtype`. Establish `hf : ∀ v, e • f v = 0` using `fun v => hkill v.1 v.2`. Establish `hlen` using `(qoCyc l O).2.2.2.2 _ f e hf`. Set `incl : LinearMap.ker f →ₗ[O] Sn (QO l O) α δ F a₀ (n * q)` to `LinearMap.codRestrict _ ((Sn (QO l O) α δ F a₀ n).subtype.comp (LinearMap.ker f).subtype) (fun v => hsub v.1.1 v.1.2 (LinearMap.mem_ker.1 v.2))`.

Establish `hinj : Function.Injective incl`. Introduce `x x' hxx`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `congrArg (fun z : Sn (QO l O) α δ F a₀ (n * q) => (z : G ℚ Ω → QO l O)) hxx`.

Conclude with `⟨e, he, hkill, hlen.trans (add_le_add (Module.length_le_of_injective incl hinj) le_rfl)⟩`.
-/
private theorem key (hR : Rec) (hD : Dat l N₀ m F α) (hF : F ≠ 0) {n q : ℕ} (hn : n ≠ 0) (hq : q.Prime) (hq1 : q ≡ 1 [MOD F])
    {ν : G ℚ Ω → QO l O} (hν : IsNu (l ^ m) F (F * n * q) (dualChar l α) ν) {δ : G ℚ Ω} (hδ : IsUnit ((α δ : O) - 1))
    {a₀ a a' : O} (h0 : a₀ ∣ a) (ha' : ∀ y : O, (∀ u ∈ fixMu ℚ Ω F, y • ν u = 0) ↔ a' ∣ y)
    {A : ValuationSubring Ω} (hA : Over A q) {φ : G ℚ Ω} (hφ : IsFrob (F := ℚ) A q φ) {τ : G ℚ Ω}
    (hτ : τ ∈ Ine (F := ℚ) A) (ha : ∀ y : O, y • ν τ = 0 ↔ a ∣ y) :
    ∃ e : O, a' = a * e ∧ (∀ c ∈ Sn (QO l O) α δ F a₀ n, e • c φ = 0) ∧
      Module.length O (Sn (QO l O) α δ F a₀ n) ≤
        Module.length O (Sn (QO l O) α δ F a₀ (n * q)) + IsDiscreteValuationRing.addVal O e := by
  classical
  have hnF : ¬ Over A F := not_over hq1 hA
  have hτF : τ ∈ fixMu ℚ Ω F := (placeBasic Ω).2.2.2.2.1 A F hnF hτ
  have hlm : ∀ u ∈ fixMu ℚ Ω F, ((l : O) ^ m) • ν u = 0 := by
    intro u hu
    have h := hν.tors u hu
    rw [← Nat.cast_smul_eq_nsmul O] at h
    simpa using h
  have ha'l : a' ∣ (l : O) ^ m := (ha' _).1 hlm
  have ha'0 : a' ≠ 0 := fun h => lpow_ne l O m (zero_dvd_iff.1 (h ▸ ha'l))
  have haa' : a ∣ a' := (ha a').1 ((ha' a').2 dvd_rfl τ hτF)
  obtain ⟨e, he⟩ := haa'
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha'0 (by simp [he])
  have ha₀a' : a₀ ∣ a' := h0.trans (Dvd.intro e he.symm)
  have ha₀l : a₀ ∣ (l : O) ^ m := ha₀a'.trans ha'l
  obtain ⟨w₀, hw₀⟩ := (qoCyc l O).2.1 a' ha'0
  obtain ⟨y, hy⟩ := (qoCyc l O).2.2.1 a' w₀ ha'0 hw₀ (ν τ) ((ha' a').2 dvd_rfl τ hτF)
  have hkill : ∀ c ∈ Sn (QO l O) α δ F a₀ n, e • c φ = 0 := by
    intro c hc
    have hyc : y • c φ = 0 :=
      step hR Ω l O N₀ m F (F * n) q α hD (dvd_mul_right F n) (mul_ne_zero hF hn) hq hq1 ν hν δ a₀ a' w₀
        ha₀a' ha'l hw₀ (fun u hu => (ha' a').2 dvd_rfl u hu) c hc.1
        (fun A' hA' hA'F _ g hg => hc.2 A' ((((placeBasic Ω).2.2.1 A' F n).1 hA').resolve_left hA'F) g hg)
        A hA φ hφ.1 τ hτ y hy
    rcases le_total (IsDiscreteValuationRing.addVal O y) (IsDiscreteValuationRing.addVal O a') with hle | hle
    · rw [IsDiscreteValuationRing.addVal_le_iff_dvd] at hle
      obtain ⟨t, ht⟩ := hle
      have hat : a ∣ t := (ha t).1 (by rw [hy, smul_smul, mul_comm t y, ← ht]; exact (hw₀ a').2 dvd_rfl)
      obtain ⟨s, rfl⟩ := hat
      have hes : e = y * s := by
        apply mul_left_cancel₀ ha0
        rw [← he, ht]
        ring
      rw [hes, mul_comm, ← smul_smul, hyc, smul_zero]
    · rw [IsDiscreteValuationRing.addVal_le_iff_dvd] at hle
      have hντ : ν τ = 0 := by
        rw [hy]
        exact (hw₀ y).2 hle
      have hu : IsUnit a₀ := isUnit_of_dvd_one (h0.trans ((ha 1).1 (by rw [hντ, smul_zero])))
      have hcφ : c φ = 0 := by
        have h1 : a₀ • c φ = 0 := hc.1.2.2.1 φ
        rwa [hu.smul_eq_zero] at h1
      rw [hcφ, smul_zero]
  have hsub : ∀ c ∈ Sn (QO l O) α δ F a₀ n, c φ = 0 → c ∈ Sn (QO l O) α δ F a₀ (n * q) := by
    intro c hc hcφ
    refine ⟨hc.1, fun A' hA' g hg => ?_⟩
    rcases ((placeBasic Ω).2.2.1 A' n q).1 hA' with h | h
    · exact hc.2 A' h g hg
    · exact ((shtNu Ω l O N₀ m F α hD δ hδ a₀ ha₀l c hc.1).2.2 q A φ hq hq1 hA hφ hcφ) A' h g hg
  let f : Sn (QO l O) α δ F a₀ n →ₗ[O] QO l O :=
    (LinearMap.proj φ).comp (Sn (QO l O) α δ F a₀ n).subtype
  have hf : ∀ v, e • f v = 0 := fun v => hkill v.1 v.2
  have hlen := (qoCyc l O).2.2.2.2 _ f e hf
  let incl : LinearMap.ker f →ₗ[O] Sn (QO l O) α δ F a₀ (n * q) :=
    LinearMap.codRestrict _ ((Sn (QO l O) α δ F a₀ n).subtype.comp (LinearMap.ker f).subtype)
      (fun v => hsub v.1.1 v.1.2 (LinearMap.mem_ker.1 v.2))
  have hinj : Function.Injective incl := by
    intro x x' hxx
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Sn (QO l O) α δ F a₀ (n * q) => (z : G ℚ Ω → QO l O)) hxx
  exact ⟨e, he, hkill, hlen.trans (add_le_add (Module.length_le_of_injective incl hinj) le_rfl)⟩

end

/- English proof (translation)
Introduce `hR Ω _ _ _ l _ O _ _ _ _ _ N₀ m F b _ α hD hb δ hδ σ hσ a₀ hz`. Establish `hF : F ≠ 0` using `NeZero.ne F`. Establish `hlm0 : (l : O) ^ m ≠ 0` using `lpow_ne l O m`. Take `⟨k, hk⟩ : zVal α σ b ∣ (l : O) ^ m` from `(Dvd.intro_left a₀ rfl).trans hz`. Establish `hz0 : zVal α σ b ≠ 0`.

Introduce `h`. Rewrite `hk` using `[h, zero_mul]`. Conclude with `hlm0 hk`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hk` using `[mul_zero]`. Conclude with `hlm0 hk`. Establish `ha₀k : a₀ ∣ k`. Establish `h1 : a₀ * zVal α σ b ∣ k * zVal α σ b`. Rewrite using `[mul_comm k, ← hk]`.

Conclude with `hz`. Conclude with `(mul_dvd_mul_iff_right hz0).1 h1`. Establish `ha₀l : a₀ ∣ (l : O) ^ m` using `(Dvd.intro _ rfl).trans hz`. Take `⟨w, hw⟩` from `(qoCyc l O).2.1 ((l : O) ^ m) hlm0`. Establish `hw' : l ^ m • w = 0`.

Establish `h1` using `(hw ((l : O) ^ m)).2 dvd_rfl`. Rewrite using `[← Nat.cast_smul_eq_nsmul O]`. Simplify using `using h1`. Take `⟨r, hr, -, hr1⟩` from `Nat.exists_prime_gt_modEq_one 0 hF`. Establish `hrF : r.Coprime F`.

Establish `h` using `hr1.gcd_eq`. Simplify `h` using `[Nat.Coprime]`. Take `⟨A₀, hA₀⟩` from `(placeBasic Ω).1 r hr`. Take `⟨ν, hνs⟩` from `nuSysEx Ω l O N₀ m F r b α hD hr hr1 hb A₀ hA₀ σ hσ w hw'`. Use `choose aL haL using fun L : List ℕ => annEx (O := O) (fixMu ℚ Ω F : Set (G ℚ Ω)) (ν L)`.

Establish `hνtors : ∀ L, AdmL l F r L → ∀ u ∈ fixMu ℚ Ω F, ((l : O) ^ m) • ν L u = 0`. Introduce `L hL u hu`. Establish `h` using `(hνs.isNu L hL).tors u hu`. Rewrite `h` using `[← Nat.cast_smul_eq_nsmul O]`. Simplify using `using h`.

Establish `haLl : ∀ L, AdmL l F r L → aL L ∣ (l : O) ^ m` using `fun L hL => (haL L _).1 (hνtors L hL)`. Establish `haL0 : ∀ L, AdmL l F r L → aL L ≠ 0` using `fun L hL h => hlm0 (zero_dvd_iff.1 (h ▸ haLl L hL))`. Take `⟨τ₀, hτ₀, u₀, hu₀⟩` from `hνs.init`. Take `⟨φ₀, hφ₀⟩` from `(placeBasic Ω).2.1 A₀ r hr hA₀`. Establish `hν0 : IsNu (l ^ m) F (F * 1 * r) (dualChar l α) (ν [])`.

Establish `h` using `hνs.isNu [] (isAdmissiblePrimeList_nil l F r)`. Establish `e1 : F * r * ([] : List ℕ).prod = F * 1 * r` using `by simp`. Rewrite `h` using `[e1]`. Then use the resulting hypothesis. Establish `hbase : ∀ y : O, y • ν [] τ₀ = 0 ↔ k ∣ y`. Introduce `y`.

Rewrite using `[hu₀, smul_comm y (u₀ : O), (u₀.isUnit).smul_eq_zero, smul_smul, hw, hk, mul_comm y, mul_dvd_mul_iff_left hz0]`. Take `⟨e₀, he₀, -, hlen₀⟩` from `key hR hD hF one_ne_zero hr hr1 hν0 hδ ha₀k (haL []) hA₀ hφ₀ hτ₀ hbase`. Set `St` to `{L : List ℕ // AdmL l F r L ∧ a₀ ∣ aL L}`. Set `S : St → Submodule O (G ℚ Ω → QO l O)` to `fun s => Sn (QO l O) α δ F a₀ (r * s.1.prod)`. Set `j : St → ℕ` to `fun s => (IsDiscreteValuationRing.addVal O (aL s.1)).toNat`.

Set `J : ℕ` to `(IsDiscreteValuationRing.addVal O ((l : O) ^ m)).toNat`. Establish `hjc : ∀ s : St, ((j s : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal O (aL s.1)` using `fun s => cast_val (haL0 s.1 s.2.1)`. Establish `hJc : ((J : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal O ((l : O) ^ m)` using `cast_val hlm0`. Establish `hjJ : ∀ s : St, j s ≤ J`. Introduce `s`.

Establish `h : ((j s : ℕ) : ℕ∞) ≤ ((J : ℕ) : ℕ∞)`. Rewrite using `[hjc, hJc, IsDiscreteValuationRing.addVal_le_iff_dvd]`. Conclude with `haLl s.1 s.2.1`. Conclude with `h` after adjusting the coercions. Establish `hstep : ∀ s : St, S s ≠ ⊥ → ∃ s' : St, j s < j s' ∧ Module.length O (S s) + (j s : ℕ∞) ≤ Module.length O (S s') + (j s' : ℕ∞)`.

Introduce and unpack `⟨L, hL, hdiv⟩ hne`. Take `⟨c, hc, hc0⟩` from `(Submodule.ne_bot_iff _).1 hne`. Establish `hsc` using `shtNu Ω l O N₀ m F α hD δ hδ a₀ ha₀l c hc.1`. Establish `hcu : ∃ u ∈ fixMu ℚ Ω F, c u ≠ 0`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hc0 (hsc.2.1 hcon)`. Establish `hP` using `isCrys_isDR_prod l F r L hL`. Take `⟨q, A, φ, hAdm, hqT, hA, hφ, hcφ, hgen⟩` from `pick Ω l O N₀ m F r (F * r * L.prod) F L.prod α hD hr hrF hP.2.1 (ν L) c (hνs.isNu L hL) hsc.1 hcu`. Establish `hqL : q ∉ L` using `fun h => hqT (List.dvd_prod h)`.

Establish `hL' : AdmL l F r (q :: L)` using `⟨List.nodup_cons.2 ⟨hqL, hL.1⟩, List.forall_mem_cons.2 ⟨hAdm, hL.2⟩⟩`. Take `⟨τ, hτ, u, hu⟩` from `hνs.step q L hL' A hA φ hφ`. Establish `hq` using `hAdm.1`. Establish `hq1` using `hAdm.2.1`. Establish `hφF : φ ∈ fixMu ℚ Ω F` using `frob_fix hq1 hA hφ`.

Establish `hνq : IsNu (l ^ m) F (F * (r * L.prod) * q) (dualChar l α) (ν (q :: L))`. Establish `h` using `hνs.isNu (q :: L) hL'`. Establish `e1 : F * r * (q :: L).prod = F * (r * L.prod) * q`. Rewrite using `[List.prod_cons]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[e1]`. Then use the resulting hypothesis. Establish `hann : ∀ y : O, y • ν (q :: L) τ = 0 ↔ aL L ∣ y`. Introduce `y`. Rewrite using `[hu, smul_comm y (u : O), (u.isUnit).smul_eq_zero, ← haL L y]`. Prove the components needed by the constructor for the conclusion.

Introduce `h v hv`. Take `⟨y', hy'⟩` from `hgen v hv`. Rewrite using `[hy', smul_comm, h, smul_zero]`. Introduce `h`. Conclude with `h φ hφF`.

Establish `hrL : r * L.prod ≠ 0` using `mul_ne_zero hr.ne_zero hP.2.1`. Take `⟨e, he, hkill, hlen⟩` from `key hR hD hF hrL hq hq1 hνq hδ hdiv (haL (q :: L)) hA hφ hτ hann`. Establish `hdiv' : a₀ ∣ aL (q :: L)`. Rewrite using `[he]`. Conclude with `hdiv.mul_right e`.

Use `⟨⟨q :: L, hL', hdiv'⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `he1 : IsDiscreteValuationRing.addVal O e ≠ 0`. Introduce `h0`. Rewrite `h0` using `[IsDiscreteValuationRing.addVal_eq_zero_iff]`. Conclude with `hcφ ((h0.smul_eq_zero).1 (hkill c hc))`.

Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Conclude with `haL0 _ hL' (by rw [he, mul_zero])`. Establish `hE` using `cast_val he0`. Establish `hjeq : j ⟨q :: L, hL', hdiv'⟩ = j ⟨L, hL, hdiv⟩ + (IsDiscreteValuationRing.addVal O e).toNat`.

Apply `Nat.cast_injective (R := ℕ∞)` to reduce the goal to its premises. Rewrite using `[Nat.cast_add, hjc, hjc, hE]`. Use `show IsDiscreteValuationRing.addVal O (aL (q :: L)) = IsDiscreteValuationRing.addVal O (aL L) + IsDiscreteValuationRing.addVal O e`. Rewrite using `[he, IsDiscreteValuationRing.addVal_mul]`. Establish `hEpos : (IsDiscreteValuationRing.addVal O e).toNat ≠ 0`.

Introduce `h`. Apply `he1` to reduce the goal to its premises. Rewrite using `[← hE, h, Nat.cast_zero]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hjc, hjc] show Module.length O (Sn (QO l O) α δ F a₀ (r * L.prod)) + IsDiscreteValuationRing.addVal O (aL L) ≤ Module.length O (Sn (QO l O) α δ F a₀ (r * (q :: L).prod)) + IsDiscreteValuationRing.addVal O (aL (q :: L))`.

Rewrite using `[List.prod_cons, show r * (q * L.prod) = r * L.prod * q by ring, he, IsDiscreteValuationRing.addVal_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hch` using `chain O (G ℚ Ω → QO l O) St S j J hjJ hstep`. Establish `hdiv0 : a₀ ∣ aL []`. Rewrite using `[he₀]`.

Conclude with `ha₀k.mul_right e₀`. Establish `h0` using `hch ⟨[], isAdmissiblePrimeList_nil l F r, hdiv0⟩`. Rewrite `h0` using `[hjc, hJc]`. Express the relevant statement in the definitionally equal form `Module.length O (Sn (QO l O) α δ F a₀ (r * ([] : List ℕ).prod)) + IsDiscreteValuationRing.addVal O (aL []) ≤ IsDiscreteValuationRing.addVal O ((l : O) ^ m) at h0`. Rewrite `h0` using `[List.prod_nil, mul_one, he₀, IsDiscreteValuationRing.addVal_mul, hk, IsDiscreteValuationRing.addVal_mul]`.

Rewrite `hlen₀` using `[one_mul]`. Establish `hsub : ShT (QO l O) α δ F a₀ ≤ Sn (QO l O) α δ F a₀ 1`. Introduce `c hc`. Use `⟨hc, fun A hA => ?_⟩` and prove the remaining obligations. It suffices to derive a contradiction.

Establish `hv : ¬ (A.valuation ((1 : ℕ) : Ω) < 1)` using `by simp`. Conclude with `hv hA`. Establish `hlenS` using `Module.length_le_of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)`. Establish `hk_ne : IsDiscreteValuationRing.addVal O k ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]`.

Conclude with `hk0`. Establish `h1 : Module.length O (Sn (QO l O) α δ F a₀ r) + IsDiscreteValuationRing.addVal O e₀ ≤ IsDiscreteValuationRing.addVal O (zVal α σ b)`. Establish `h2 : Module.length O (Sn (QO l O) α δ F a₀ r) + IsDiscreteValuationRing.addVal O e₀ + IsDiscreteValuationRing.addVal O k ≤ IsDiscreteValuationRing.addVal O (zVal α σ b) + IsDiscreteValuationRing.addVal O k`. Rewrite using `[add_assoc, add_comm (IsDiscreteValuationRing.addVal O e₀)]`. Conclude with `h0`.

Conclude with `(WithTop.add_le_add_iff_right hk_ne).1 h2`. Conclude with `hlenS.trans (hlen₀.trans h1)`.
-/
theorem UpperTheory.V.ML.count :
    Rec → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F b : ℕ) [NeZero F] (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → b < F → ∀ δ : G ℚ Ω, IsUnit ((α δ : O) - 1) →
    ∀ σ : (ZMod F)ˣ → G ℚ Ω, (∀ t, Lifts F t (σ t)) → ∀ a₀ : O, a₀ * zVal α σ b ∣ (l : O) ^ m → Module.length O (ShT (QO l O) α δ F a₀) ≤ IsDiscreteValuationRing.addVal O (zVal α σ b) := by
  intro hR Ω _ _ _ l _ O _ _ _ _ _ N₀ m F b _ α hD hb δ hδ σ hσ a₀ hz
  classical
  have hF : F ≠ 0 := NeZero.ne F
  have hlm0 : (l : O) ^ m ≠ 0 := lpow_ne l O m
  obtain ⟨k, hk⟩ : zVal α σ b ∣ (l : O) ^ m := (Dvd.intro_left a₀ rfl).trans hz
  have hz0 : zVal α σ b ≠ 0 := by
    intro h
    rw [h, zero_mul] at hk
    exact hlm0 hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact hlm0 hk
  have ha₀k : a₀ ∣ k := by
    have h1 : a₀ * zVal α σ b ∣ k * zVal α σ b := by
      rw [mul_comm k, ← hk]
      exact hz
    exact (mul_dvd_mul_iff_right hz0).1 h1
  have ha₀l : a₀ ∣ (l : O) ^ m := (Dvd.intro _ rfl).trans hz
  obtain ⟨w, hw⟩ := (qoCyc l O).2.1 ((l : O) ^ m) hlm0
  have hw' : l ^ m • w = 0 := by
    have h1 := (hw ((l : O) ^ m)).2 dvd_rfl
    rw [← Nat.cast_smul_eq_nsmul O]
    simpa using h1
  obtain ⟨r, hr, -, hr1⟩ := Nat.exists_prime_gt_modEq_one 0 hF
  have hrF : r.Coprime F := by
    have h := hr1.gcd_eq
    simpa [Nat.Coprime] using h
  obtain ⟨A₀, hA₀⟩ := (placeBasic Ω).1 r hr
  obtain ⟨ν, hνs⟩ := nuSysEx Ω l O N₀ m F r b α hD hr hr1 hb A₀ hA₀ σ hσ w hw'
  choose aL haL using fun L : List ℕ => annEx (O := O) (fixMu ℚ Ω F : Set (G ℚ Ω)) (ν L)
  have hνtors : ∀ L, AdmL l F r L → ∀ u ∈ fixMu ℚ Ω F, ((l : O) ^ m) • ν L u = 0 := by
    intro L hL u hu
    have h := (hνs.isNu L hL).tors u hu
    rw [← Nat.cast_smul_eq_nsmul O] at h
    simpa using h
  have haLl : ∀ L, AdmL l F r L → aL L ∣ (l : O) ^ m := fun L hL => (haL L _).1 (hνtors L hL)
  have haL0 : ∀ L, AdmL l F r L → aL L ≠ 0 := fun L hL h => hlm0 (zero_dvd_iff.1 (h ▸ haLl L hL))
  obtain ⟨τ₀, hτ₀, u₀, hu₀⟩ := hνs.init
  obtain ⟨φ₀, hφ₀⟩ := (placeBasic Ω).2.1 A₀ r hr hA₀
  have hν0 : IsNu (l ^ m) F (F * 1 * r) (dualChar l α) (ν []) := by
    have h := hνs.isNu [] (isAdmissiblePrimeList_nil l F r)
    have e1 : F * r * ([] : List ℕ).prod = F * 1 * r := by simp
    rwa [e1] at h
  have hbase : ∀ y : O, y • ν [] τ₀ = 0 ↔ k ∣ y := by
    intro y
    rw [hu₀, smul_comm y (u₀ : O), (u₀.isUnit).smul_eq_zero, smul_smul, hw, hk, mul_comm y,
      mul_dvd_mul_iff_left hz0]
  obtain ⟨e₀, he₀, -, hlen₀⟩ := key hR hD hF one_ne_zero hr hr1 hν0 hδ ha₀k (haL []) hA₀ hφ₀ hτ₀ hbase
  let St := {L : List ℕ // AdmL l F r L ∧ a₀ ∣ aL L}
  let S : St → Submodule O (G ℚ Ω → QO l O) := fun s => Sn (QO l O) α δ F a₀ (r * s.1.prod)
  let j : St → ℕ := fun s => (IsDiscreteValuationRing.addVal O (aL s.1)).toNat
  let J : ℕ := (IsDiscreteValuationRing.addVal O ((l : O) ^ m)).toNat
  have hjc : ∀ s : St, ((j s : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal O (aL s.1) :=
    fun s => cast_val (haL0 s.1 s.2.1)
  have hJc : ((J : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal O ((l : O) ^ m) := cast_val hlm0
  have hjJ : ∀ s : St, j s ≤ J := by
    intro s
    have h : ((j s : ℕ) : ℕ∞) ≤ ((J : ℕ) : ℕ∞) := by
      rw [hjc, hJc, IsDiscreteValuationRing.addVal_le_iff_dvd]
      exact haLl s.1 s.2.1
    exact_mod_cast h
  have hstep : ∀ s : St, S s ≠ ⊥ → ∃ s' : St, j s < j s' ∧
      Module.length O (S s) + (j s : ℕ∞) ≤ Module.length O (S s') + (j s' : ℕ∞) := by
    rintro ⟨L, hL, hdiv⟩ hne
    obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hne
    have hsc := shtNu Ω l O N₀ m F α hD δ hδ a₀ ha₀l c hc.1
    have hcu : ∃ u ∈ fixMu ℚ Ω F, c u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hc0 (hsc.2.1 hcon)
    have hP := isCrys_isDR_prod l F r L hL
    obtain ⟨q, A, φ, hAdm, hqT, hA, hφ, hcφ, hgen⟩ :=
      pick Ω l O N₀ m F r (F * r * L.prod) F L.prod α hD hr hrF hP.2.1 (ν L) c (hνs.isNu L hL) hsc.1 hcu
    have hqL : q ∉ L := fun h => hqT (List.dvd_prod h)
    have hL' : AdmL l F r (q :: L) := ⟨List.nodup_cons.2 ⟨hqL, hL.1⟩, List.forall_mem_cons.2 ⟨hAdm, hL.2⟩⟩
    obtain ⟨τ, hτ, u, hu⟩ := hνs.step q L hL' A hA φ hφ
    have hq := hAdm.1
    have hq1 := hAdm.2.1
    have hφF : φ ∈ fixMu ℚ Ω F := frob_fix hq1 hA hφ
    have hνq : IsNu (l ^ m) F (F * (r * L.prod) * q) (dualChar l α) (ν (q :: L)) := by
      have h := hνs.isNu (q :: L) hL'
      have e1 : F * r * (q :: L).prod = F * (r * L.prod) * q := by
        rw [List.prod_cons]
        ring
      rwa [e1] at h
    have hann : ∀ y : O, y • ν (q :: L) τ = 0 ↔ aL L ∣ y := by
      intro y
      rw [hu, smul_comm y (u : O), (u.isUnit).smul_eq_zero, ← haL L y]
      constructor
      · intro h v hv
        obtain ⟨y', hy'⟩ := hgen v hv
        rw [hy', smul_comm, h, smul_zero]
      · intro h
        exact h φ hφF
    have hrL : r * L.prod ≠ 0 := mul_ne_zero hr.ne_zero hP.2.1
    obtain ⟨e, he, hkill, hlen⟩ := key hR hD hF hrL hq hq1 hνq hδ hdiv (haL (q :: L)) hA hφ hτ hann
    have hdiv' : a₀ ∣ aL (q :: L) := by
      rw [he]
      exact hdiv.mul_right e
    refine ⟨⟨q :: L, hL', hdiv'⟩, ?_, ?_⟩
    · have he1 : IsDiscreteValuationRing.addVal O e ≠ 0 := by
        intro h0
        rw [IsDiscreteValuationRing.addVal_eq_zero_iff] at h0
        exact hcφ ((h0.smul_eq_zero).1 (hkill c hc))
      have he0 : e ≠ 0 := by
        rintro rfl
        exact haL0 _ hL' (by rw [he, mul_zero])
      have hE := cast_val he0
      have hjeq : j ⟨q :: L, hL', hdiv'⟩ = j ⟨L, hL, hdiv⟩ + (IsDiscreteValuationRing.addVal O e).toNat := by
        apply Nat.cast_injective (R := ℕ∞)
        rw [Nat.cast_add, hjc, hjc, hE]
        show IsDiscreteValuationRing.addVal O (aL (q :: L)) =
          IsDiscreteValuationRing.addVal O (aL L) + IsDiscreteValuationRing.addVal O e
        rw [he, IsDiscreteValuationRing.addVal_mul]
      have hEpos : (IsDiscreteValuationRing.addVal O e).toNat ≠ 0 := by
        intro h
        apply he1
        rw [← hE, h, Nat.cast_zero]
      omega
    · rw [hjc, hjc]
      show Module.length O (Sn (QO l O) α δ F a₀ (r * L.prod)) + IsDiscreteValuationRing.addVal O (aL L) ≤
        Module.length O (Sn (QO l O) α δ F a₀ (r * (q :: L).prod)) +
          IsDiscreteValuationRing.addVal O (aL (q :: L))
      rw [List.prod_cons, show r * (q * L.prod) = r * L.prod * q by ring, he,
        IsDiscreteValuationRing.addVal_mul]
      calc Module.length O (Sn (QO l O) α δ F a₀ (r * L.prod)) + IsDiscreteValuationRing.addVal O (aL L)
          ≤ Module.length O (Sn (QO l O) α δ F a₀ (r * L.prod * q)) + IsDiscreteValuationRing.addVal O e +
              IsDiscreteValuationRing.addVal O (aL L) := add_le_add hlen le_rfl
        _ = _ := by ring
  have hch := chain O (G ℚ Ω → QO l O) St S j J hjJ hstep
  have hdiv0 : a₀ ∣ aL [] := by
    rw [he₀]
    exact ha₀k.mul_right e₀
  have h0 := hch ⟨[], isAdmissiblePrimeList_nil l F r, hdiv0⟩
  rw [hjc, hJc] at h0
  change Module.length O (Sn (QO l O) α δ F a₀ (r * ([] : List ℕ).prod)) +
    IsDiscreteValuationRing.addVal O (aL []) ≤ IsDiscreteValuationRing.addVal O ((l : O) ^ m) at h0
  rw [List.prod_nil, mul_one, he₀, IsDiscreteValuationRing.addVal_mul, hk,
    IsDiscreteValuationRing.addVal_mul] at h0
  rw [one_mul] at hlen₀
  have hsub : ShT (QO l O) α δ F a₀ ≤ Sn (QO l O) α δ F a₀ 1 := by
    intro c hc
    refine ⟨hc, fun A hA => ?_⟩
    exfalso
    have hv : ¬ (A.valuation ((1 : ℕ) : Ω) < 1) := by simp
    exact hv hA
  have hlenS := Module.length_le_of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)
  have hk_ne : IsDiscreteValuationRing.addVal O k ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact hk0
  have h1 : Module.length O (Sn (QO l O) α δ F a₀ r) + IsDiscreteValuationRing.addVal O e₀ ≤
      IsDiscreteValuationRing.addVal O (zVal α σ b) := by
    have h2 : Module.length O (Sn (QO l O) α δ F a₀ r) + IsDiscreteValuationRing.addVal O e₀ +
        IsDiscreteValuationRing.addVal O k ≤
        IsDiscreteValuationRing.addVal O (zVal α σ b) + IsDiscreteValuationRing.addVal O k := by
      rw [add_assoc, add_comm (IsDiscreteValuationRing.addVal O e₀)]
      exact h0
    exact (WithTop.add_le_add_iff_right hk_ne).1 h2
  exact hlenS.trans (hlen₀.trans h1)

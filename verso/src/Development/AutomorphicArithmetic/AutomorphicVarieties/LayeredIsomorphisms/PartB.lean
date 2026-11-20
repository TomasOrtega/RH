import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AbelianFieldHasMuIffExistsPrimitiveRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Exc
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layerex
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.EquivOfRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layeriso
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Point2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Vvat
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Final

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Take `⟨N, hN, j, ζ, h1, h2, h3⟩` from `hL`. Take `⟨k, hk⟩` from `hA.1.trans h1`. Establish `hz : IsPrimitiveRoot (ζ ^ k) l` using `h2.pow (NeZero.pos N) (by rw [hk, mul_comm])`. Establish `key : ζ ^ k ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup j.fieldRange)`. Introduce and unpack `⟨τ, hτ⟩`.

Rewrite `hτ` using `[IntermediateField.mem_fixingSubgroup_iff]`. Take `⟨a, -, ha⟩` from `h2.eq_pow_of_pow_eq_one (show (τ ζ) ^ N = 1 by rw [← map_pow, h2.pow_eq_one, map_one])`. Establish `hker` using `(h3 τ a ha.symm).mp (fun x => hτ (j x) ⟨x, rfl⟩)`. Establish `hmod` using `hA.2 a hker`. Use `show τ (ζ ^ k) = ζ ^ k`.

Rewrite using `[map_pow, ← ha, ← pow_mul]`. Establish `ha1 : 1 ≤ a`. Break down `Nat.eq_zero_or_pos a with h | h` into its components or cases. Substitute `h` using the available equality. Establish `hl1 : l ∣ 1` using `Nat.modEq_zero_iff_dvd.mp hmod.symm`.

Conclude with `absurd (Nat.le_of_dvd one_pos hl1) (not_le.mpr (Fact.out : l.Prime).one_lt)`. Conclude with `h`. Take `⟨q, hq⟩` from `(Nat.modEq_iff_dvd' ha1).mp hmod.symm`. Establish `ha' : a = l * q + 1` using `(Nat.sub_eq_iff_eq_add ha1).mp hq`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Rewrite using `[ha', hk]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ζ ^ k := by rw [pow_add, pow_mul, h2.pow_eq_one, one_pow, mul_one]`. Use `haveI : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois (S := {N}) (K := ℚ) (L := CyclotomicField N ℚ)`.

Rewrite `key` using `[IsGalois.fixedField_fixingSubgroup]`. Take `⟨y, hy⟩` from `key`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[← hy]`. Conclude with `(IsPrimitiveRoot.map_iff_of_injective j.toRingHom.injective).mp hz`.
-/
private theorem exists_isPrimitiveRoot_of_hasMu_of_isAbField (A : AbF) (l : ℕ) [Fact l.Prime] (hA : A.HasMu l) (L : Type) [Field L]
    [NumberField L] (hL : IsAbField A L) : ∃ ζ : L, IsPrimitiveRoot ζ l := by
  obtain ⟨N, hN, j, ζ, h1, h2, h3⟩ := hL
  obtain ⟨k, hk⟩ := hA.1.trans h1
  have hz : IsPrimitiveRoot (ζ ^ k) l := h2.pow (NeZero.pos N) (by rw [hk, mul_comm])
  have key : ζ ^ k ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup j.fieldRange) := by
    rintro ⟨τ, hτ⟩
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    obtain ⟨a, -, ha⟩ := h2.eq_pow_of_pow_eq_one
      (show (τ ζ) ^ N = 1 by rw [← map_pow, h2.pow_eq_one, map_one])
    have hker := (h3 τ a ha.symm).mp (fun x => hτ (j x) ⟨x, rfl⟩)
    have hmod := hA.2 a hker
    show τ (ζ ^ k) = ζ ^ k
    rw [map_pow, ← ha, ← pow_mul]
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h
        have hl1 : l ∣ 1 := Nat.modEq_zero_iff_dvd.mp hmod.symm
        exact absurd (Nat.le_of_dvd one_pos hl1) (not_le.mpr (Fact.out : l.Prime).one_lt)
      · exact h
    obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' ha1).mp hmod.symm
    have ha' : a = l * q + 1 := (Nat.sub_eq_iff_eq_add ha1).mp hq
    calc ζ ^ (a * k) = ζ ^ (k + N * q) := by
          congr 1
          rw [ha', hk]
          ring
      _ = ζ ^ k := by rw [pow_add, pow_mul, h2.pow_eq_one, one_pow, mul_one]
  haveI : IsGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isGalois (S := {N}) (K := ℚ) (L := CyclotomicField N ℚ)
  rw [IsGalois.fixedField_fixingSubgroup] at key
  obtain ⟨y, hy⟩ := key
  refine ⟨y, ?_⟩
  rw [← hy] at hz
  exact (IsPrimitiveRoot.map_iff_of_injective j.toRingHom.injective).mp hz

/- English proof (translation)
Introduce `CK hCK hK l R _ hl2 A hA L₀ _ _ hL₀ hAB J Ct eps A1 hJ hCt heps`. Establish `hmu0 : HasMuQ l L₀`. Take `⟨ζ, hζ⟩` from `exists_isPrimitiveRoot_of_hasMu_of_isAbField A l hA L₀ hL₀`. Conclude with `⟨ζ, by rw [if_neg hl2]; exact hζ⟩`. Take `⟨c, -, hc⟩` from `exc l R L₀ hAB`.

Take `⟨L₂, i1, i2, i3, hL₂⟩` from `layerex l (jZero l R) Fact.out L₀ hmu0`. Establish `hc0 : 0 ≤ Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ))`. Apply `Real.log_nonneg` to reduce the goal to its premises. Establish `: (1 : ℝ) ≤ ((NumberField.discr L₂).natAbs : ℝ)` using `Nat.one_le_cast.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L₂))`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨C, -, hP⟩` from `point2 CK hCK hK l R c (Module.finrank ℚ L₂) (Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ))) J Ct eps (jZero l R : ℝ) hc0 hJ hCt heps (Nat.cast_nonneg _)`. Take `⟨x1, hx1two, hx1⟩` from `final Ct eps C heps`. Use `⟨x1, fun e t hAdm X => ?_⟩` and prove the remaining obligations. Take `⟨Exc, hExc⟩` from `hc ⌊X ^ Ct⌋₊`. Use `⟨Exc, hExc.1, fun x hx hXx hxX hgood L₀' _ _ hL₀' L₁ _ _ _ hL₁ => ?_⟩` and prove the remaining obligations.

Take `⟨f0⟩` from `abiso A L₀ L₀' hL₀ hL₀'`. Take `⟨f1⟩` from `layeriso l (jZero l R) Fact.out L₀ L₀' L₂ L₁ ⟨f0⟩ hL₂ hL₁`. Establish `hx1' : (1 : ℝ) ≤ x` using `by linarith`. Establish `hadm` using `hAdm x (by linarith)`. Establish `hQ : ∀ e' : ℕ, 1 ≤ e' → (e' : ℝ) ≤ x ^ Ct → shaInv L₂ l e' ≠ ⊤ ∧ ((shaInv L₂ l e').toNat : ℝ) + 1 ≤ ptBound C eps x`.

Introduce `e' he1 he2`. Use `hP L₀ hmu0 hAB.2 c X Exc le_rfl hExc L₂ hL₂ le_rfl x hx1' hXx hxX hgood ?_ e' he1 he2 (jZero l R) L₂ hL₂ ?_` and prove the remaining obligations. Conclude with `le_mul_of_one_le_right hc0 (Real.one_le_rpow hx1' (by positivity))`. Conclude with `le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith [Real.log_nonneg hx1'])`. Establish `hb : 0 ≤ ptBound C eps x`.

Use `(hQ 1 le_rfl (by simpa using Real.one_le_rpow hx1' hCt)).2` as an intermediate fact. Establish `: (0 : ℝ) ≤ ((shaInv L₂ l 1).toNat : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Use `vvat l (t x) L₁ (x ^ Ct) (ptBound C eps x) _ hb hadm.2.2.2 (hx1 x hx) ?_` and prove the remaining obligations. Introduce `e' he1 he2`.

Rewrite using `[← shaInv_congr f1]`. Establish `h` using `hQ e' he1 (le_trans (by exact_mod_cast he2.le) hadm.2.2.2)`. Conclude with `⟨h.1, by linarith [h.2]⟩`.
-/
theorem UpperTheory.V.Win.partB :
    ∀ CK : ℝ, 0 < CK → LemmaK CK → ∀ (l R : ℕ) [Fact l.Prime], l ≠ 2 → ∀ A : AbF, A.HasMu l →
      ∀ (L₀ : Type) [Field L₀] [NumberField L₀], IsAbField A L₀ → ABound l R L₀ →
        ∀ J Ct eps A1 : ℝ, 0 < J → 0 ≤ Ct → 0 < eps → ∃ x0 : ℝ, ∀ e t : ℝ → ℕ, admitted A1 Ct e t → ∀ X : ℝ,
          ∃ Exc : Finset ℕ, Exc.card ≤ R ∧ ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct Exc x →
            ∀ (L₀' : Type) [Field L₀'] [NumberField L₀'], IsAbField A L₀' →
              ∀ (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀' L₁], IsLayer l (jZero l R) L₀' L₁ →
                VVat l L₁ (t x) (Real.exp (x ^ (4 * eps / 5))) := by
  intro CK hCK hK l R _ hl2 A hA L₀ _ _ hL₀ hAB J Ct eps A1 hJ hCt heps
  have hmu0 : HasMuQ l L₀ := by
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_hasMu_of_isAbField A l hA L₀ hL₀
    exact ⟨ζ, by rw [if_neg hl2]; exact hζ⟩
  obtain ⟨c, -, hc⟩ := exc l R L₀ hAB
  obtain ⟨L₂, i1, i2, i3, hL₂⟩ := layerex l (jZero l R) Fact.out L₀ hmu0
  have hc0 : 0 ≤ Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((NumberField.discr L₂).natAbs : ℝ) :=
      Nat.one_le_cast.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L₂))
    linarith
  obtain ⟨C, -, hP⟩ := point2 CK hCK hK l R c (Module.finrank ℚ L₂)
    (Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ))) J Ct eps (jZero l R : ℝ) hc0 hJ hCt heps
    (Nat.cast_nonneg _)
  obtain ⟨x1, hx1two, hx1⟩ := final Ct eps C heps
  refine ⟨x1, fun e t hAdm X => ?_⟩
  obtain ⟨Exc, hExc⟩ := hc ⌊X ^ Ct⌋₊
  refine ⟨Exc, hExc.1, fun x hx hXx hxX hgood L₀' _ _ hL₀' L₁ _ _ _ hL₁ => ?_⟩
  obtain ⟨f0⟩ := abiso A L₀ L₀' hL₀ hL₀'
  obtain ⟨f1⟩ := layeriso l (jZero l R) Fact.out L₀ L₀' L₂ L₁ ⟨f0⟩ hL₂ hL₁
  have hx1' : (1 : ℝ) ≤ x := by linarith
  have hadm := hAdm x (by linarith)
  have hQ : ∀ e' : ℕ, 1 ≤ e' → (e' : ℝ) ≤ x ^ Ct →
      shaInv L₂ l e' ≠ ⊤ ∧ ((shaInv L₂ l e').toNat : ℝ) + 1 ≤ ptBound C eps x := by
    intro e' he1 he2
    refine hP L₀ hmu0 hAB.2 c X Exc le_rfl hExc L₂ hL₂ le_rfl x hx1' hXx hxX hgood ?_ e' he1 he2
      (jZero l R) L₂ hL₂ ?_
    · exact le_mul_of_one_le_right hc0 (Real.one_le_rpow hx1' (by positivity))
    · exact le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith [Real.log_nonneg hx1'])
  have hb : 0 ≤ ptBound C eps x := by
    have := (hQ 1 le_rfl (by simpa using Real.one_le_rpow hx1' hCt)).2
    have : (0 : ℝ) ≤ ((shaInv L₂ l 1).toNat : ℝ) := Nat.cast_nonneg _
    linarith
  refine vvat l (t x) L₁ (x ^ Ct) (ptBound C eps x) _ hb hadm.2.2.2 (hx1 x hx) ?_
  intro e' he1 he2
  rw [← shaInv_congr f1]
  have h := hQ e' he1 (le_trans (by exact_mod_cast he2.le) hadm.2.2.2)
  exact ⟨h.1, by linarith [h.2]⟩

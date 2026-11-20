import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.CycDescend
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Distinguish the cases in `hc : N.Coprime M`. Conclude with `⟨1, N, 0, by simp, by simp, hc⟩`. Take `⟨p, hp, hpN, hpM⟩` from `Nat.Prime.not_coprime_iff_dvd.mp hc`.

Take `⟨N', rfl⟩` from `hpN`. Establish `hN' : 0 < N'` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hN)`. Establish `hlt : N' < p * N'` using `by have := hp.two_le; nlinarith`. Take `⟨a, b, n, rfl, ha, hb⟩` from `ih N' hlt hN'`. Use `⟨p * a, b, n + 1, by ring, ?_, hb⟩` and prove the remaining obligations.

Rewrite using `[pow_succ']`. Conclude with `mul_dvd_mul hpM ha`.
-/
private theorem kwRam_split (M N : ℕ) (hN : 0 < N) :
    ∃ a b n : ℕ, N = a * b ∧ a ∣ M ^ n ∧ b.Coprime M := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hc : N.Coprime M
    · exact ⟨1, N, 0, by simp, by simp, hc⟩
    · obtain ⟨p, hp, hpN, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      obtain ⟨N', rfl⟩ := hpN
      have hN' : 0 < N' := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
      have hlt : N' < p * N' := by have := hp.two_le; nlinarith
      obtain ⟨a, b, n, rfl, ha, hb⟩ := ih N' hlt hN'
      refine ⟨p * a, b, n + 1, by ring, ?_, hb⟩
      rw [pow_succ']
      exact mul_dvd_mul hpM ha

/- English proof (translation)
Introduce `L _ _ _ M hM hram`. Take `⟨N, hN, ⟨f⟩⟩` from `kwHom L`. Take `⟨a, b, n, rfl, ha, hb⟩` from `kwRam_split M N hN`. Establish `ha0 : a ≠ 0` using `by rintro rfl; simp at hN`. Establish `hb0 : b ≠ 0` using `by rintro rfl; simp at hN`.

Establish `hab : a.Coprime b` using `Nat.Coprime.coprime_dvd_left ha (hb.pow_right n).symm`. Use `haveI : NeZero (a * b) := ⟨hN.ne'⟩`. Use `haveI : NeZero ((a * b : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩`. Use `haveI : IsCyclotomicExtension {a * b} ℚ (CyclotomicField (a * b) ℚ) := by`. Use `CyclotomicField.isCyclotomicExtension (a * b) ℚ` and compare the differences between its conclusion and the goal.

Both sides reduce to the same expression. Conclude with `Subsingleton.elim _ _`. Take `⟨ζ, hζ⟩ : ∃ z : CyclotomicField (a * b) ℚ, IsPrimitiveRoot z (a * b)` from `⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩`. Set `F : IntermediateField ℚ (CyclotomicField (a * b) ℚ)` to `f.fieldRange`. Set `e : L ≃ₐ[ℚ] F` to `AlgEquiv.ofInjectiveField f`.

Establish `hF : ∀ p : ℕ, p.Prime → p ∣ b → UnramAt F p`. Introduce `p hp hpb`. Establish `hpM : ¬ p ∣ M` using `fun h => hp.not_dvd_one (Nat.Coprime.gcd_eq_one hb ▸ Nat.dvd_gcd hpb h)`. Use `letI : Algebra F L := e.symm.toRingHom.toAlgebra`. Conclude with `unramIff.2.2 F L p hp (hram p hp hpM)`.

Establish `hle` using `cycDescend a b (CyclotomicField (a * b) ℚ) ζ F hab hζ hF`. Establish `hζb : IsPrimitiveRoot (ζ ^ b) a`. Establish `h` using `hζ.pow_of_dvd hb0 (dvd_mul_left b a)`. Rewrite `h` using `[Nat.mul_div_cancel a (Nat.pos_of_ne_zero hb0)]`. Then use the resulting hypothesis. Establish `hapos : 0 < a` using `Nat.pos_of_ne_zero ha0`.

Establish `hint : IsIntegral ℚ (ζ ^ b)` using `(hζb.isIntegral hapos).tower_top`. Use `haveI : NeZero (M ^ n) := ⟨pow_ne_zero _ hM.ne'⟩`. Use `haveI : NeZero ((M ^ n : ℕ) : ℚ) := ⟨by exact_mod_cast pow_ne_zero _ hM.ne'⟩`. Use `haveI : IsCyclotomicExtension {M ^ n} ℚ (CyclotomicField (M ^ n) ℚ) := by`. Use `CyclotomicField.isCyclotomicExtension (M ^ n) ℚ` and compare the differences between its conclusion and the goal.

Both sides reduce to the same expression. Conclude with `Subsingleton.elim _ _`. Take `⟨ω, hω⟩ : ∃ z : CyclotomicField (M ^ n) ℚ, IsPrimitiveRoot z (M ^ n)` from `⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩`. Establish `hq0 : M ^ n / a ≠ 0` using `(Nat.div_pos (Nat.le_of_dvd (pow_pos hM n) ha) hapos).ne'`. Establish `hη` using `hω.pow_of_dvd hq0 (Nat.div_dvd_of_dvd ha)`.

Rewrite `hη` using `[Nat.div_div_self ha (pow_ne_zero _ hM.ne')]`. Establish `hmem : ω ^ (M ^ n / a) ∈ (minpoly ℚ (ζ ^ b)).aroots (CyclotomicField (M ^ n) ℚ)`. Rewrite using `[← Polynomial.cyclotomic_eq_minpoly_rat hζb hapos, Polynomial.mem_aroots]`. Use `⟨Polynomial.cyclotomic_ne_zero _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`.

Conclude with `hη.isRoot_cyclotomic hapos`. Set `g` to `(IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨_, hmem⟩`. Conclude with `⟨n, ⟨(g.comp (IntermediateField.inclusion hle)).comp e.toAlgHom⟩⟩`.
-/
theorem UpperTheory.V.CF.kwRam :
    ∀ (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] (M : ℕ), 0 < M → (∀ p : ℕ, p.Prime → ¬ p ∣ M → UnramAt L p) → ∃ n : ℕ, Nonempty (L →ₐ[ℚ] CyclotomicField (M ^ n) ℚ) := by
  intro L _ _ _ M hM hram
  obtain ⟨N, hN, ⟨f⟩⟩ := kwHom L
  obtain ⟨a, b, n, rfl, ha, hb⟩ := kwRam_split M N hN
  have ha0 : a ≠ 0 := by rintro rfl; simp at hN
  have hb0 : b ≠ 0 := by rintro rfl; simp at hN
  have hab : a.Coprime b := Nat.Coprime.coprime_dvd_left ha (hb.pow_right n).symm
  haveI : NeZero (a * b) := ⟨hN.ne'⟩
  haveI : NeZero ((a * b : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {a * b} ℚ (CyclotomicField (a * b) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (a * b) ℚ
    · rfl
    · exact Subsingleton.elim _ _
  obtain ⟨ζ, hζ⟩ : ∃ z : CyclotomicField (a * b) ℚ, IsPrimitiveRoot z (a * b) :=
    ⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩
  let F : IntermediateField ℚ (CyclotomicField (a * b) ℚ) := f.fieldRange
  let e : L ≃ₐ[ℚ] F := AlgEquiv.ofInjectiveField f
  have hF : ∀ p : ℕ, p.Prime → p ∣ b → UnramAt F p := by
    intro p hp hpb
    have hpM : ¬ p ∣ M := fun h => hp.not_dvd_one (Nat.Coprime.gcd_eq_one hb ▸ Nat.dvd_gcd hpb h)
    letI : Algebra F L := e.symm.toRingHom.toAlgebra
    exact unramIff.2.2 F L p hp (hram p hp hpM)
  have hle := cycDescend a b (CyclotomicField (a * b) ℚ) ζ F hab hζ hF
  have hζb : IsPrimitiveRoot (ζ ^ b) a := by
    have h := hζ.pow_of_dvd hb0 (dvd_mul_left b a)
    rwa [Nat.mul_div_cancel a (Nat.pos_of_ne_zero hb0)] at h
  have hapos : 0 < a := Nat.pos_of_ne_zero ha0
  have hint : IsIntegral ℚ (ζ ^ b) := (hζb.isIntegral hapos).tower_top
  haveI : NeZero (M ^ n) := ⟨pow_ne_zero _ hM.ne'⟩
  haveI : NeZero ((M ^ n : ℕ) : ℚ) := ⟨by exact_mod_cast pow_ne_zero _ hM.ne'⟩
  haveI : IsCyclotomicExtension {M ^ n} ℚ (CyclotomicField (M ^ n) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (M ^ n) ℚ
    · rfl
    · exact Subsingleton.elim _ _
  obtain ⟨ω, hω⟩ : ∃ z : CyclotomicField (M ^ n) ℚ, IsPrimitiveRoot z (M ^ n) :=
    ⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩
  have hq0 : M ^ n / a ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (pow_pos hM n) ha) hapos).ne'
  have hη := hω.pow_of_dvd hq0 (Nat.div_dvd_of_dvd ha)
  rw [Nat.div_div_self ha (pow_ne_zero _ hM.ne')] at hη
  have hmem : ω ^ (M ^ n / a) ∈ (minpoly ℚ (ζ ^ b)).aroots (CyclotomicField (M ^ n) ℚ) := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζb hapos, Polynomial.mem_aroots]
    refine ⟨Polynomial.cyclotomic_ne_zero _ _, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hη.isRoot_cyclotomic hapos
  let g := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨_, hmem⟩
  exact ⟨n, ⟨(g.comp (IntermediateField.inclusion hle)).comp e.toAlgHom⟩⟩

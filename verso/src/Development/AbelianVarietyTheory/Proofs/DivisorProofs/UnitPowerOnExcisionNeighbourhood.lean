import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExcisionNbhdAdjoinRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosedStatement
open GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `k B _ _ _ _ _ _ q hq f g hg u t n' d' hn hd hu`. Establish `hq0 : q ≠ 0` using `by rintro rfl; simp at hq`. Take `⟨a, bn, ha⟩` from `hn`. Take `⟨a', bd, hb⟩` from `hd`. Establish `hw : (a * a' * g - a - a') * g = n' * d' * (bn * bd) - 1`.

Take the linear combination `(-(bd * d')) * ha + (a * g - 1) * hb`. Establish `hC' : IsExcisionNbhd B (Localization.Away (n' * d')) g` using `GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B B g (isExcisionNbhd_self B g) (n' * d') (bn * bd) (Ideal.mem_span_singleton'.mpr ⟨_, hw⟩)`. Use `set C' := Localization.Away (n' * d') with hC'def`. Establish `hnd : IsUnit (algebraMap B C' (n' * d'))` using `IsLocalization.Away.algebraMap_isUnit _`. Rewrite `hnd` using `[map_mul]`.

Establish `hnC : IsUnit (algebraMap B C' n')` using `isUnit_of_mul_isUnit_left hnd`. Establish `hdC : IsUnit (algebraMap B C' d')` using `isUnit_of_mul_isUnit_right hnd`. Use `set Di : C' := ((hdC.unit⁻¹ : C'ˣ) : C') with hDi`. Establish `hDi1 : Di * algebraMap B C' d' = 1` using `by rw [hDi]; exact hdC.val_inv_mul`. Use `set ε : C' := algebraMap B C' n' * Di with hεdef`.

Establish `hε : IsUnit ε` using `hnC.mul (Units.isUnit _)`. Establish `hεd : ε * algebraMap B C' d' = algebraMap B C' n'` using `by rw [hεdef, mul_assoc, hDi1, mul_one]`. Take `⟨r, hr⟩` from `GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B q hq g hg (n' * bd) (bn * d') (Ideal.mem_span_singleton'.mpr ⟨a * a' * g - a - a', by linear_combination hw⟩)`. Take `⟨w, hw'⟩` from `Ideal.mem_span_singleton'.mp hr`. Establish `hqC : IsUnit (q : C')` using `by simpa using hq.map ((algebraMap B C').comp (algebraMap k B))`.

Establish `hεr : ε - algebraMap B C' r ^ q ∈ Ideal.span {algebraMap B C' g}`. Use `Ideal.mem_span_singleton'.mpr ⟨algebraMap B C' n' * Di * algebraMap B C' a' + algebraMap B C' w, ?_⟩` and prove the remaining obligations. Establish `e1` using `congrArg (algebraMap B C') hw'`. Establish `e2` using `congrArg (algebraMap B C') hb`. Simplify using `only [map_mul, map_sub, map_add, map_pow, map_one] at e1 e2`.

Rewrite using `[hεdef]`. Take the linear combination `e1 + (algebraMap B C' n' * Di) * e2 - (algebraMap B C' n' * algebraMap B C' bd) * hDi1`. Take `⟨C, _, _, hC, x, hx⟩` from `GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit C' (algebraMap B C' g) q hqC ε (algebraMap B C' r) hε hεr`. Use `letI : Algebra B C := ((algebraMap C' C).comp (algebraMap B C')).toAlgebra`. Use `haveI : IsScalarTower B C' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Use `⟨C, inferInstance, inferInstance, GlobalTheory.T.isExcisionNbhd_trans' B C' C g hC' hC, ?_⟩` and prove the remaining obligations. Use `set L := Localization.Away (algebraMap B C (f * g))`. Use `set ψ : B →+* L := (algebraMap C L).comp (algebraMap B C) with hψ`. Use `set ρ : C' →+* L := (algebraMap C L).comp (algebraMap C' C) with hρ`. Establish `hψρ : ∀ y : B, ψ y = ρ (algebraMap B C' y)` using `fun _ => rfl`.

Establish `hφ : ∀ y : B, Localization.awayMap (algebraMap B C) (f * g) (algebraMap B (Localization.Away (f * g)) y) = ψ y`. Introduce `y`. Conclude with `IsLocalization.map_eq _ _`. Establish `hu' : Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d') = ψ n'`. Establish `h` using `congrArg (Localization.awayMap (algebraMap B C) (f * g)) hu`.

Rewrite `h` using `[map_mul (Localization.awayMap (algebraMap B C) (f * g)), hφ, hφ]`. Rewrite using `[← map_pow ψ, ← map_mul ψ]`. Conclude with `h`. Establish `hnL : IsUnit (ψ n')` using `by rw [hψρ]; exact hnC.map ρ`. Establish `hdL : IsUnit (ψ d')` using `by rw [hψρ]; exact hdC.map ρ`.

Establish `hεL : ρ ε * ψ d' = ψ n'`. Use `congrArg ρ hεd` as an intermediate fact. Rewrite `this` using `[map_mul]`. Rewrite using `[hψρ, hψρ]`. Conclude with `this`.

Establish `hxL : algebraMap C L x ^ q = ρ ε`. Use `congrArg (algebraMap C L) hx` as an intermediate fact. Rewrite `this` using `[map_pow]`. Conclude with `this.symm`. Establish `hXU : algebraMap C L x ^ q = Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * ψ t ^ q`.

Rewrite using `[← hdL.mul_left_inj, hxL, hεL, ← hu', mul_assoc]`. Establish `hTq : IsUnit (ψ t ^ q)`. Establish `h : IsUnit (Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d'))`. Rewrite using `[hu']`. Conclude with `hnL`.

Conclude with `isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)`. Establish `hT : IsUnit (ψ t)` using `(isUnit_pow_iff hq0).mp hTq`. Establish `hX : IsUnit (algebraMap C L x)`. Use `(isUnit_pow_iff hq0).mp ?_` and prove the remaining obligations. Rewrite using `[hXU]`.

Conclude with `((Units.map (Localization.awayMap (algebraMap B C) (f * g) : Localization.Away (f * g) →* L)) u).isUnit.mul hTq`. Use `⟨hX.unit * hT.unit⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, mul_pow, IsUnit.unit_spec, hXU, mul_assoc, ← mul_pow, hT.mul_val_inv, one_pow, mul_one]`.
-/
theorem unit_isPow_on_excisionNbhd : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f g : B, g ≠ 0 → ∀ (u : (Localization.Away (f * g))ˣ) (t n' d' : B), IsCoprime g n' → IsCoprime g d' → (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' → ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro k B _ _ _ _ _ _ q hq f g hg u t n' d' hn hd hu
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨a, bn, ha⟩ := hn
  obtain ⟨a', bd, hb⟩ := hd
  have hw : (a * a' * g - a - a') * g = n' * d' * (bn * bd) - 1 := by
    linear_combination (-(bd * d')) * ha + (a * g - 1) * hb
  have hC' : IsExcisionNbhd B (Localization.Away (n' * d')) g :=
    GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B B g (isExcisionNbhd_self B g) (n' * d') (bn * bd)
      (Ideal.mem_span_singleton'.mpr ⟨_, hw⟩)
  set C' := Localization.Away (n' * d') with hC'def
  have hnd : IsUnit (algebraMap B C' (n' * d')) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at hnd
  have hnC : IsUnit (algebraMap B C' n') := isUnit_of_mul_isUnit_left hnd
  have hdC : IsUnit (algebraMap B C' d') := isUnit_of_mul_isUnit_right hnd
  set Di : C' := ((hdC.unit⁻¹ : C'ˣ) : C') with hDi
  have hDi1 : Di * algebraMap B C' d' = 1 := by rw [hDi]; exact hdC.val_inv_mul
  set ε : C' := algebraMap B C' n' * Di with hεdef
  have hε : IsUnit ε := hnC.mul (Units.isUnit _)
  have hεd : ε * algebraMap B C' d' = algebraMap B C' n' := by rw [hεdef, mul_assoc, hDi1, mul_one]
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B q hq g hg (n' * bd) (bn * d')
    (Ideal.mem_span_singleton'.mpr ⟨a * a' * g - a - a', by linear_combination hw⟩)
  obtain ⟨w, hw'⟩ := Ideal.mem_span_singleton'.mp hr
  have hqC : IsUnit (q : C') := by simpa using hq.map ((algebraMap B C').comp (algebraMap k B))
  have hεr : ε - algebraMap B C' r ^ q ∈ Ideal.span {algebraMap B C' g} := by
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap B C' n' * Di * algebraMap B C' a' + algebraMap B C' w, ?_⟩
    have e1 := congrArg (algebraMap B C') hw'
    have e2 := congrArg (algebraMap B C') hb
    simp only [map_mul, map_sub, map_add, map_pow, map_one] at e1 e2
    rw [hεdef]
    linear_combination e1 + (algebraMap B C' n' * Di) * e2 - (algebraMap B C' n' * algebraMap B C' bd) * hDi1
  obtain ⟨C, _, _, hC, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit C' (algebraMap B C' g) q hqC ε (algebraMap B C' r) hε hεr
  letI : Algebra B C := ((algebraMap C' C).comp (algebraMap B C')).toAlgebra
  haveI : IsScalarTower B C' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨C, inferInstance, inferInstance, GlobalTheory.T.isExcisionNbhd_trans' B C' C g hC' hC, ?_⟩
  set L := Localization.Away (algebraMap B C (f * g))
  set ψ : B →+* L := (algebraMap C L).comp (algebraMap B C) with hψ
  set ρ : C' →+* L := (algebraMap C L).comp (algebraMap C' C) with hρ
  have hψρ : ∀ y : B, ψ y = ρ (algebraMap B C' y) := fun _ => rfl
  have hφ : ∀ y : B, Localization.awayMap (algebraMap B C) (f * g)
      (algebraMap B (Localization.Away (f * g)) y) = ψ y := by
    intro y; exact IsLocalization.map_eq _ _
  have hu' : Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d') = ψ n' := by
    have h := congrArg (Localization.awayMap (algebraMap B C) (f * g)) hu
    rw [map_mul (Localization.awayMap (algebraMap B C) (f * g)), hφ, hφ] at h
    rw [← map_pow ψ, ← map_mul ψ]; exact h
  have hnL : IsUnit (ψ n') := by rw [hψρ]; exact hnC.map ρ
  have hdL : IsUnit (ψ d') := by rw [hψρ]; exact hdC.map ρ
  have hεL : ρ ε * ψ d' = ψ n' := by
    have := congrArg ρ hεd; rw [map_mul] at this; rw [hψρ, hψρ]; exact this
  have hxL : algebraMap C L x ^ q = ρ ε := by
    have := congrArg (algebraMap C L) hx; rw [map_pow] at this; exact this.symm
  have hXU : algebraMap C L x ^ q = Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * ψ t ^ q := by
    rw [← hdL.mul_left_inj, hxL, hεL, ← hu', mul_assoc]
  have hTq : IsUnit (ψ t ^ q) := by
    have h : IsUnit (Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d')) := by
      rw [hu']; exact hnL
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)
  have hT : IsUnit (ψ t) := (isUnit_pow_iff hq0).mp hTq
  have hX : IsUnit (algebraMap C L x) := by
    refine (isUnit_pow_iff hq0).mp ?_
    rw [hXU]; exact ((Units.map (Localization.awayMap (algebraMap B C) (f * g) : Localization.Away (f * g) →* L)) u).isUnit.mul hTq
  refine ⟨hX.unit * hT.unit⁻¹, ?_⟩
  rw [Units.val_mul, mul_pow, IsUnit.unit_spec, hXU, mul_assoc, ← mul_pow, hT.mul_val_inv, one_pow, mul_one]

end GlobalTheory.EtC

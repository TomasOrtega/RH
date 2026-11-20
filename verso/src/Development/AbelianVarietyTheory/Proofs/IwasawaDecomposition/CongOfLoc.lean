import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.CongSplit

/- English proof (translation)
Establish `hm` using `x.2`. Simplify using `only [GA, UGroup, Subgroup.mem_mk] at hm`. Establish `h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1` using `Units.inv_eq_of_mul_eq_one_right hm`. Simplify using `only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]`.
-/
theorem conj_entry {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (x : GA L n) (i j : Fin n) :
    conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hm := x.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
    Units.inv_eq_of_mul_eq_one_right hm
  simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]

/- English proof (translation)
Introduce `L _ _ _ n s N hN x hx h1 h2`. Take `⟨e, he, he'⟩` from `GlobalTheory.SplitSep.exists_sep L s`. Establish `hNL : (N : L) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Take `⟨u, hu⟩ : ∃ u : AL L, (N : AL L) * u = 1` from `⟨algebraMap L (AL L) (N : L)⁻¹, by`. Rewrite using `[← map_natCast (algebraMap L (AL L)), ← map_mul, mul_inv_cancel₀ hNL, map_one]⟩`.

Establish `key : ∀ (f : AL L →+* s.v.adicCompletion (maximalRealSubfield L)) (z : AL L), Valued.v (f z) ≤ Valued.v ((N : s.v.adicCompletion (maximalRealSubfield L))) → Valued.v (f (u * z)) ≤ 1`. Introduce `f z hz`. Establish `h` using `congrArg (fun t => Valued.v (f t)) hu`. Simplify using `only [map_mul, map_natCast, map_one] at h`. Rewrite using `[map_mul, map_mul, ← h, mul_comm]`.

Conclude with `mul_le_mul_left hz _`. It suffices to establish `H : ∀ i j : Fin n, ∃ y ∈ ALint L, (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * y by`. Use `⟨fun i j => ?_, H⟩` and prove the remaining obligations. Take `⟨y, hy, hxy⟩` from `H i j`. Rewrite using `[sub_eq_iff_eq_add.1 hxy]`.

Use `add_mem (mul_mem (natCast_mem _ N) hy) ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem]`. Introduce `i j`. Use `⟨u * ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j), ?_, ?_⟩` and prove the remaining obligations. Apply `GlobalTheory.mem_ALint_of_supported_at_split L s e he he'` to reduce the goal to its premises.

Introduce `w hw`. Use `congrFun (congrFun (hx w (by simpa using hw)) i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`. Rewrite using `[map_mul, map_sub, this]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.

Apply `key` to reduce the goal to its premises. Establish `e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) = ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j` using `rfl`. Establish `e2 : s.proj ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Rewrite using `[map_sub, e1, e2]`.

Conclude with `h1 i j`. Apply `key (s.proj.comp (conjAL L))` to reduce the goal to its premises. Establish `e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) = ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i` using `rfl`. Establish `e2 : (s.proj.comp (conjAL L)) ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i`. Distinguish the cases in `hij : i = j`.

Simplify using `[Matrix.one_apply, hij]`. Simplify using `[Matrix.one_apply, hij, Ne.symm hij]`. Rewrite using `[map_sub, e2, RingHom.comp_apply, conj_entry, e1]`. Conclude with `h2 j i`. Rewrite using `[← mul_assoc, hu, one_mul]`.
-/
theorem cong_of_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (N : ℕ), 0 < N →
    ∀ x : GAf L n, TrivOutside {s.v} x →
    (∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
    (∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
    NG.Cong L n N x := by
  intro L _ _ _ n s N hN x hx h1 h2
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  have hNL : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨u, hu⟩ : ∃ u : AL L, (N : AL L) * u = 1 := ⟨algebraMap L (AL L) (N : L)⁻¹, by
    rw [← map_natCast (algebraMap L (AL L)), ← map_mul, mul_inv_cancel₀ hNL, map_one]⟩
  have key : ∀ (f : AL L →+* s.v.adicCompletion (maximalRealSubfield L)) (z : AL L),
      Valued.v (f z) ≤ Valued.v ((N : s.v.adicCompletion (maximalRealSubfield L))) → Valued.v (f (u * z)) ≤ 1 := by
    intro f z hz
    have h := congrArg (fun t => Valued.v (f t)) hu
    simp only [map_mul, map_natCast, map_one] at h
    rw [map_mul, map_mul, ← h, mul_comm]
    exact mul_le_mul_left hz _
  suffices H : ∀ i j : Fin n, ∃ y ∈ ALint L, (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * y by
    refine ⟨fun i j => ?_, H⟩
    obtain ⟨y, hy, hxy⟩ := H i j
    rw [sub_eq_iff_eq_add.1 hxy]
    refine add_mem (mul_mem (natCast_mem _ N) hy) ?_
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem]
  intro i j
  refine ⟨u * ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j), ?_, ?_⟩
  · apply GlobalTheory.mem_ALint_of_supported_at_split L s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_mul, map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · apply key
      have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl
      have e2 : s.proj ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [map_sub, e1, e2]
      exact h1 i j
    · apply key (s.proj.comp (conjAL L))
      have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := rfl
      have e2 : (s.proj.comp (conjAL L)) ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := by
        by_cases hij : i = j
        · simp [Matrix.one_apply, hij]
        · simp [Matrix.one_apply, hij, Ne.symm hij]
      rw [map_sub, e2, RingHom.comp_apply, conj_entry, e1]
      exact h2 j i
  · rw [← mul_assoc, hu, one_mul]

end GlobalTheory.CongSplit

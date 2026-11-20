import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IwahoriFactorizationLowerDiagUpper

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Rewrite using `[sub_ne_zero]`. Introduce `h`. Establish `h' : u ^ w 3 i = u ^ w 3 j` using `Units.ext h`. Establish `a : u ≠ 1` using `fun e => hu (by rw [e, one_pow])`. Establish `b : u ≠ u⁻¹` using `fun e => hu (by rw [sq]; exact mul_eq_one_iff_eq_inv.2 e)`.

Establish `w0 : w 3 0 = 1` using `by decide`. Establish `w1 : w 3 1 = 0` using `by decide`. Establish `w2 : w 3 2 = -1` using `by decide`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first`. Consider the case `exact hij rfl`.

Consider the case `(simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg] at h' first`. Consider the case `exact a h'`. Consider the case `exact a h'.symm`. Consider the case `exact b h'`. Consider the case `exact b h'.symm`.

Consider the case `exact a (inv_eq_one.1 h')`. Consider the case `exact a (inv_eq_one.1 h'.symm))`.
-/
private theorem unit_sub {k : Type} [Field k] (u : kˣ) (hu : u ^ 2 ≠ 1) (i j : Fin 3) (hij : i ≠ j) :
    ((u ^ w 3 i : kˣ) : k) - ((u ^ w 3 j : kˣ) : k) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have h' : u ^ w 3 i = u ^ w 3 j := Units.ext h
  have a : u ≠ 1 := fun e => hu (by rw [e, one_pow])
  have b : u ≠ u⁻¹ := fun e => hu (by rw [sq]; exact mul_eq_one_iff_eq_inv.2 e)
  have w0 : w 3 0 = 1 := by decide
  have w1 : w 3 1 = 0 := by decide
  have w2 : w 3 2 = -1 := by decide
  fin_cases i <;> fin_cases j <;>
    first
    | exact hij rfl
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg] at h'
       first
       | exact a h'
       | exact a h'.symm
       | exact b h'
       | exact b h'.symm
       | exact a (inv_eq_one.1 h')
       | exact a (inv_eq_one.1 h'.symm))

/- English proof (translation)
Introduce `l _ k _ _ F C₀ h Q _ _ ρ hb ht hc`. Establish `w0 : w 3 0 = 1` using `by decide`. Establish `w1 : w 3 1 = 0` using `by decide`. Establish `w2 : w 3 2 = -1` using `by decide`. Establish `hz : ∀ g i j, i < j → ρ.r g i j = 0` using `fun g i j hij => (Submodule.eq_bot_iff _).1 ht _ (Ideal.subset_span ⟨g, i, j, hij, rfl⟩)`.

Establish `hs` using `(UpperTheory.V.Fr.star h).2.2.2.2 ρ`. Establish `s1 : ∀ g, ρ.r (F.star g) 1 0 = ρ.r g 2 1` using `fun g => hs g 1 0`. Establish `s2 : ∀ g, ρ.r (F.star g) 2 0 = ρ.r g 2 0` using `fun g => hs g 2 0`. Establish `d0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q (F.Ψ g : k)` using `fun g => by rw [hb.1, w0, zpow_one]`. Establish `d1 : ∀ g : F.G0, ρ.r g 1 1 = 1` using `fun g => by rw [hb.1, w1, zpow_zero, Units.val_one, map_one]`.

Establish `d2 : ∀ g : F.G0, ρ.r g 2 2 = algebraMap k Q (((F.Ψ g)⁻¹ : kˣ) : k)` using `fun g => by`. Rewrite using `[hb.1, w2, _root_.zpow_neg, zpow_one]`. Use `⟨hc 1 0, hc 2 0, fun g g' => ?_, fun g g' => ?_, s2, sub_eq_zero.1 (ρ.diag 1 0 (by decide)), fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Matrix.mul_apply, Fin.sum_univ_three, d0, d1, hz g 1 2 (by decide), Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[map_mul, Matrix.mul_apply, Fin.sum_univ_three, d0, d2, s1, Algebra.smul_def, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨s₀, h₀⟩` from `h.f3 v`. Take `⟨α, β, γ, H⟩` from `UpperTheory.iwahori_factorization_lower_diag_upper (fun s => ρ.r (F.loc0 v s)) (fun i s => (ρ.ψ v i s : Q)) s₀ (fun i j hij => by`. Rewrite using `[hb.2, hb.2, ← map_sub]`.

Conclude with `(IsUnit.mk0 _ (unit_sub _ h₀ i j hij)).map _)`. Use the proof step `(fun s => hz _) (fun s i => (hb.1 _ i).trans (hb.2 v i s).symm) (ρ.ord v)`. Use `⟨α, β, γ, fun s => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `H s`. Simplify using `only [hb.2, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg, Units.val_one, map_one] at h1 h2 h3`.

Simplify using `only [Algebra.smul_def, map_sub, map_one, s1]`. Conclude with `⟨h1, h2, h3⟩`.
-/
theorem UpperTheory.one_add_maximalIdeal_subset_units :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 3 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → F.Low Q (fun g => ρ.r g 1 0) (fun g => ρ.r g 2 0) := by
  intro l _ k _ _ F C₀ h Q _ _ ρ hb ht hc
  have w0 : w 3 0 = 1 := by decide
  have w1 : w 3 1 = 0 := by decide
  have w2 : w 3 2 = -1 := by decide
  have hz : ∀ g i j, i < j → ρ.r g i j = 0 := fun g i j hij =>
    (Submodule.eq_bot_iff _).1 ht _ (Ideal.subset_span ⟨g, i, j, hij, rfl⟩)
  have hs := (UpperTheory.V.Fr.star h).2.2.2.2 ρ
  have s1 : ∀ g, ρ.r (F.star g) 1 0 = ρ.r g 2 1 := fun g => hs g 1 0
  have s2 : ∀ g, ρ.r (F.star g) 2 0 = ρ.r g 2 0 := fun g => hs g 2 0
  have d0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q (F.Ψ g : k) := fun g => by rw [hb.1, w0, zpow_one]
  have d1 : ∀ g : F.G0, ρ.r g 1 1 = 1 := fun g => by rw [hb.1, w1, zpow_zero, Units.val_one, map_one]
  have d2 : ∀ g : F.G0, ρ.r g 2 2 = algebraMap k Q (((F.Ψ g)⁻¹ : kˣ) : k) := fun g => by
    rw [hb.1, w2, _root_.zpow_neg, zpow_one]
  refine ⟨hc 1 0, hc 2 0, fun g g' => ?_, fun g g' => ?_, s2, sub_eq_zero.1 (ρ.diag 1 0 (by decide)), fun v => ?_⟩
  · rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, d0, d1, hz g 1 2 (by decide), Algebra.smul_def]
    ring
  · rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, d0, d2, s1, Algebra.smul_def, Algebra.smul_def]
    ring
  · obtain ⟨s₀, h₀⟩ := h.f3 v
    obtain ⟨α, β, γ, H⟩ := UpperTheory.iwahori_factorization_lower_diag_upper (fun s => ρ.r (F.loc0 v s)) (fun i s => (ρ.ψ v i s : Q)) s₀
      (fun i j hij => by
        rw [hb.2, hb.2, ← map_sub]
        exact (IsUnit.mk0 _ (unit_sub _ h₀ i j hij)).map _)
      (fun s => hz _) (fun s i => (hb.1 _ i).trans (hb.2 v i s).symm) (ρ.ord v)
    refine ⟨α, β, γ, fun s => ?_⟩
    obtain ⟨h1, h2, h3⟩ := H s
    simp only [hb.2, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg, Units.val_one, map_one] at h1 h2 h3
    simp only [Algebra.smul_def, map_sub, map_one, s1]
    exact ⟨h1, h2, h3⟩

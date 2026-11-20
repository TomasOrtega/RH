import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

namespace UpperTheory.Gal.TP.Sub.PFrobSub

/- English proof (translation)
Proceed by induction on `S using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a S ih`. Establish `e : c * (x / c - a) = x - a * c`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ← ih, ← e]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem prod_scale {K : Type} [Field K] {c : K} (hc : c ≠ 0) (x : K) (S : Multiset K) :
    c ^ Multiset.card S * (S.map fun z => x / c - z).prod = (S.map fun z => x - z * c).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have e : c * (x / c - a) = x - a * c := by
      field_simp
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ← ih, ← e]
    ring

/- English proof (translation)
Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `x`. Establish `hn : Multiset.card S = n`. Use `congrArg Polynomial.natDegree h` as an intermediate fact. Rewrite `this` using `[Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]`.

Simplify using `using this.symm`. Establish `key : Matrix.scalar (Fin n) x - c • M = c • (Matrix.scalar (Fin n) (x / c) - M)`. Rewrite using `[smul_sub]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> field_simp`. Rewrite using `[Matrix.eval_charpoly, key, Matrix.det_smul, ← Matrix.eval_charpoly, h, Fintype.card_fin, ← hn, Polynomial.eval_multiset_prod, Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]`. Simplify using `only [Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`. Conclude with `prod_scale hc x S`.
-/
private theorem charpoly_smul_eq {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) (S : Multiset K) (h : M.charpoly = (S.map fun z => X - C z).prod) :
    (c • M).charpoly = (S.map fun z => X - C (z * c)).prod := by
  apply Polynomial.funext
  intro x
  have hn : Multiset.card S = n := by
    have := congrArg Polynomial.natDegree h
    rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have key : Matrix.scalar (Fin n) x - c • M = c • (Matrix.scalar (Fin n) (x / c) - M) := by
    rw [smul_sub]
    congr 1
    ext i j
    simp [Matrix.diagonal_apply]
    split_ifs <;> field_simp
  rw [Matrix.eval_charpoly, key, Matrix.det_smul, ← Matrix.eval_charpoly, h, Fintype.card_fin, ← hn,
    Polynomial.eval_multiset_prod, Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact prod_scale hc x S

/- English proof (translation)
Simplify using `[sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom]`. Both sides reduce to the same expression.
-/
private theorem sumRep_left {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k)
    (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  simp [sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom]
  rfl

/- English proof (translation)
Unfold `rk1`. Simplify using the standard rewrite rules.
-/
private theorem characterAsRankOneRep_entry {Γ k : Type} [Group Γ] [Field k] (μ : Γ →* kˣ) (g : Γ) :
    (rk1 μ g : Matrix (Fin 1) (Fin 1) k) 0 0 = (μ g : k) := by
  unfold rk1
  simp

end UpperTheory.Gal.TP.Sub.PFrobSub

open UpperTheory.Gal.TP.Sub.PFrobSub in
/- English proof (translation)
Introduce `h E Ω _ _ _ _ _ l _ ι a w S c μ hμ`. Establish `hc : ∀ A, IsPlaceOver A w → ∀ σ : G E Ω, IsFrob A (normV w) σ → ι.toRingHom (μ σ⁻¹ : Qbar l) = c`. Introduce `A hA σ hσ`. Establish `h1` using `(hμ A hA).2 σ hσ`. Establish `h2` using `(h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹`.

Unfold `cp at h2`. Rewrite `h1` using `[h2]`. Simplify using `using h1`. Use `⟨fun s hs => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Introduce `A hA`.

Take `⟨hI, hF⟩` from `hs A hA`. Use `⟨fun σ hσ => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Establish `e` using `hI σ hσ`. Use extensionality with `i j`. Establish `hij` using `sumRep_left s (rk1 μ) σ i j`.

Rewrite `hij` using `[e]`. Rewrite using `[← hij]`. Simplify using `[Matrix.one_apply]`. Establish `e` using `hF σ hσ`. Establish `h3` using `(h (G E Ω) (Qbar l) a 1).1 s (rk1 μ) σ⁻¹`.

Establish `h4` using `(h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹`. Unfold `cp at h3 h4`. Rewrite `e` using `[h3, Polynomial.map_mul, h4]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e`. Rewrite `e` using `[hc A hA σ hσ, Multiset.map_add, Multiset.prod_add, Multiset.map_singleton, Multiset.prod_singleton]`.

Conclude with `mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero c) e`. Introduce `A hA`. Take `⟨hI, hF⟩` from `hs A hA`. Take `⟨hIμ, -⟩` from `hμ A hA`. Use `⟨fun σ hσ => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations.

Establish `e1` using `hI σ hσ`. Establish `e2 : (μ σ : Qbar l) = 1`. Apply the tactic sequence `rw [← characterAsRankOneRep_entry μ σ, hIμ σ hσ]`. Simplify using the standard rewrite rules. Use extensionality with `i j`.

Rewrite using `[UpperTheory.V.Af.tw_val, e1, e2]`. Simplify using the standard rewrite rules. Establish `e` using `hF σ hσ`. Establish `hc'` using `hc A hA σ hσ`. Establish `hc0 : c ≠ 0`.

Rewrite using `[← hc']`. Simplify using the standard rewrite rules. Rewrite using `[UpperTheory.V.Af.tw_val, ← Matrix.charpoly_map]`. Rewrite `e` using `[← Matrix.charpoly_map]`. Establish `hm : ((μ σ⁻¹ : Qbar l) • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l))).map ι.toRingHom = c • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom`.

Rewrite using `[← hc']`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[hm, Multiset.map_map]`. Conclude with `charpoly_smul_eq _ hc0 S e`.
-/
theorem UpperTheory.Gal.TP.Sub.frobSub_holds :
    CpFacts → FrobSub := by
  intro h E Ω _ _ _ _ _ l _ ι a w S c μ hμ
  have hc : ∀ A, IsPlaceOver A w → ∀ σ : G E Ω, IsFrob A (normV w) σ →
      ι.toRingHom (μ σ⁻¹ : Qbar l) = c := by
    intro A hA σ hσ
    have h1 := (hμ A hA).2 σ hσ
    have h2 := (h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹
    unfold cp at h2
    rw [h2] at h1
    simpa using h1
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · intro A hA
    obtain ⟨hI, hF⟩ := hs A hA
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have e := hI σ hσ
      ext i j
      have hij := sumRep_left s (rk1 μ) σ i j
      rw [e] at hij
      rw [← hij]
      simp [Matrix.one_apply]
    · have e := hF σ hσ
      have h3 := (h (G E Ω) (Qbar l) a 1).1 s (rk1 μ) σ⁻¹
      have h4 := (h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹
      unfold cp at h3 h4
      rw [h3, Polynomial.map_mul, h4] at e
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
      rw [hc A hA σ hσ, Multiset.map_add, Multiset.prod_add, Multiset.map_singleton,
        Multiset.prod_singleton] at e
      exact mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero c) e
  · intro A hA
    obtain ⟨hI, hF⟩ := hs A hA
    obtain ⟨hIμ, -⟩ := hμ A hA
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have e1 := hI σ hσ
      have e2 : (μ σ : Qbar l) = 1 := by
        rw [← characterAsRankOneRep_entry μ σ, hIμ σ hσ]
        simp
      ext i j
      rw [UpperTheory.V.Af.tw_val, e1, e2]
      simp
    · have e := hF σ hσ
      have hc' := hc A hA σ hσ
      have hc0 : c ≠ 0 := by
        rw [← hc']
        simp
      rw [UpperTheory.V.Af.tw_val, ← Matrix.charpoly_map]
      rw [← Matrix.charpoly_map] at e
      have hm : ((μ σ⁻¹ : Qbar l) • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l))).map ι.toRingHom =
          c • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom := by
        rw [← hc']
        ext i j
        simp
      rw [hm, Multiset.map_map]
      exact charpoly_smul_eq _ hc0 S e

import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

/- English proof (translation)
Introduce `l _ L m _ hmL z t ht0 ht1 V _ f`. Establish `hd : l ^ m ∣ l ^ L` using `pow_dvd_pow l hmL`. Use `set φ := ZMod.castHom hd (ZMod (l ^ m)) with hφ`. Establish `hcast : ∀ x : ZMod (l ^ L), ((x.val : ℕ) : ZMod (l ^ m)) = φ x`. Introduce `x`.

Rewrite using `[ZMod.natCast_val, hφ, ZMod.castHom_apply]`. Establish `hmod : ∀ a : (ZMod (l ^ L))ˣ, (a : ZMod (l ^ L)).val ≡ 1 [MOD l ^ m] ↔ φ a = 1`. Introduce `a`. Rewrite using `[← ZMod.natCast_eq_natCast_iff, hcast, Nat.cast_one]`. Establish `hdet : ∀ h u, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det = (u : ZMod (l ^ L))`.

Introduce `h u`. Establish `h1 : (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det = 1` using `h.prop`. Rewrite `h1`, the goal using `[Matrix.det_fin_two]`. Rewrite using `[ht0, ht0, ht1, ht1]`. Take the linear combination `(u : ZMod (l ^ L)) * h1`.

Rewrite using `[← Finset.sum_product']`. Apply `Finset.sum_bij (fun p _ => t p.1 (p.2 * z))` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp`. Simplify using `only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, ht0, hcast, hdet]`.

Use `⟨hp.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, map_mul, (hmod _).mp hp.2, one_mul]`. Introduce `p _ q _ hpq`. Establish `hu : p.2 * z = q.2 * z`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[← hdet p.1, ← hdet q.1, hpq]`. Establish `ha : p.2 = q.2` using `mul_right_cancel hu`. Establish `hh : p.1 = q.1`. Use extensionality with `i j`. Use `fin_cases j`.

Use `congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0) hpq` as an intermediate fact. Simplify `this` using `[ht0]`. Use `congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1) hpq` as an intermediate fact. Simplify using `only [ht1] at this`. Rewrite `this` using `[hu]`.

Conclude with `(Units.mul_right_inj _).mp this`. Conclude with `Prod.ext hh ha`. Introduce `γ hγ`. Simplify using `only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, hcast] at hγ`. Use `set g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) := (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) with hg`.

Use `set u : (ZMod (l ^ L))ˣ := Matrix.GeneralLinearGroup.det γ with hu`. Establish `hug : (u : ZMod (l ^ L)) = g.det` using `rfl`. Use `set M : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) := !![g 0 0, (↑u⁻¹ : ZMod (l ^ L)) * g 0 1; g 1 0, (↑u⁻¹ : ZMod (l ^ L)) * g 1 1] with hM`. Establish `hMdet : M.det = 1`. Rewrite using `[hM, Matrix.det_fin_two_of]`.

Establish `h2 : (↑u⁻¹ : ZMod (l ^ L)) * g.det = 1`. Rewrite using `[← hug, Units.inv_mul]`. Rewrite `h2` using `[Matrix.det_fin_two]`. Take the linear combination `h2`. Use `⟨(⟨M, hMdet⟩, u * z⁻¹), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.mem_product]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, hγ.1⟩`. Rewrite using `[Finset.mem_filter]`.

Use `⟨Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Rewrite using `[hmod, Units.val_mul, map_mul, hug, hγ.2, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]`. Apply `Units.ext` to reduce the goal to its premises. Establish `hz : u * z⁻¹ * z = u` using `by group`. Establish `e0 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0 = g i 0`.

Introduce `i`. Use `(ht0 _ _ i).trans ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> rfl`. Establish `e1 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1 = g i 1`. Introduce `i`.

Use `(ht1 _ _ i).trans ?_` and prove the remaining obligations. Rewrite using `[hz]`. Use `fin_cases i`. Express the relevant statement in the definitionally equal form `(u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 0 1) = g 0 1`. Rewrite using `[← mul_assoc, Units.mul_inv, one_mul]`.

Express the relevant statement in the definitionally equal form `(u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 1 1) = g 1 1`. Rewrite using `[← mul_assoc, Units.mul_inv, one_mul]`. Use extensionality with `i j`. Use `fin_cases j`. Conclude with `e0 i`.

Conclude with `e1 i`. Introduce `p _`. Both sides reduce to the same expression.
-/
theorem UpperTheory.congruence_action_invariant :
    ∀ (l : ℕ) [Fact l.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ (z : (ZMod (l ^ L))ˣ) (t : SL(2, ZMod (l ^ L)) → (ZMod (l ^ L))ˣ → GL (Fin 2) (ZMod (l ^ L))), (∀ h u i, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0 = h i 0) → (∀ h u i, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1 = (u : ZMod (l ^ L)) * h i 1) → ∀ (V : Type) [AddCommMonoid V] (f : GL (Fin 2) (ZMod (l ^ L)) → V), ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ L)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ L))ˣ => (a : ZMod (l ^ L)).val ≡ 1 [MOD l ^ m]), f (t h (a * z)) = ∑ γ ∈ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = (((z : ZMod (l ^ L)).val : ℕ) : ZMod (l ^ m))), f γ := by
  intro l _ L m _ hmL z t ht0 ht1 V _ f
  have hd : l ^ m ∣ l ^ L := pow_dvd_pow l hmL
  set φ := ZMod.castHom hd (ZMod (l ^ m)) with hφ
  have hcast : ∀ x : ZMod (l ^ L), ((x.val : ℕ) : ZMod (l ^ m)) = φ x := by
    intro x
    rw [ZMod.natCast_val, hφ, ZMod.castHom_apply]
  have hmod : ∀ a : (ZMod (l ^ L))ˣ, (a : ZMod (l ^ L)).val ≡ 1 [MOD l ^ m] ↔ φ a = 1 := by
    intro a
    rw [← ZMod.natCast_eq_natCast_iff, hcast, Nat.cast_one]
  have hdet : ∀ h u, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det
      = (u : ZMod (l ^ L)) := by
    intro h u
    have h1 : (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det = 1 := h.prop
    rw [Matrix.det_fin_two] at h1 ⊢
    rw [ht0, ht0, ht1, ht1]
    linear_combination (u : ZMod (l ^ L)) * h1
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun p _ => t p.1 (p.2 * z))
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, ht0, hcast, hdet]
    refine ⟨hp.1, ?_⟩
    rw [Units.val_mul, map_mul, (hmod _).mp hp.2, one_mul]
  · intro p _ q _ hpq
    have hu : p.2 * z = q.2 * z := by
      apply Units.ext
      rw [← hdet p.1, ← hdet q.1, hpq]
    have ha : p.2 = q.2 := mul_right_cancel hu
    have hh : p.1 = q.1 := by
      ext i j
      fin_cases j
      · have := congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0) hpq
        simpa [ht0] using this
      · have := congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1) hpq
        simp only [ht1] at this
        rw [hu] at this
        exact (Units.mul_right_inj _).mp this
    exact Prod.ext hh ha
  · intro γ hγ
    simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, hcast] at hγ
    set g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) := (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) with hg
    set u : (ZMod (l ^ L))ˣ := Matrix.GeneralLinearGroup.det γ with hu
    have hug : (u : ZMod (l ^ L)) = g.det := rfl
    set M : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) :=
      !![g 0 0, (↑u⁻¹ : ZMod (l ^ L)) * g 0 1; g 1 0, (↑u⁻¹ : ZMod (l ^ L)) * g 1 1] with hM
    have hMdet : M.det = 1 := by
      rw [hM, Matrix.det_fin_two_of]
      have h2 : (↑u⁻¹ : ZMod (l ^ L)) * g.det = 1 := by
        rw [← hug, Units.inv_mul]
      rw [Matrix.det_fin_two] at h2
      linear_combination h2
    refine ⟨(⟨M, hMdet⟩, u * z⁻¹), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hγ.1⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hmod, Units.val_mul, map_mul, hug, hγ.2, ← map_mul, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, map_one]
    · apply Units.ext
      have hz : u * z⁻¹ * z = u := by group
      have e0 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) :
          Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0 = g i 0 := by
        intro i
        refine (ht0 _ _ i).trans ?_
        fin_cases i <;> rfl
      have e1 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) :
          Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1 = g i 1 := by
        intro i
        refine (ht1 _ _ i).trans ?_
        rw [hz]
        fin_cases i
        · change (u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 0 1) = g 0 1
          rw [← mul_assoc, Units.mul_inv, one_mul]
        · change (u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 1 1) = g 1 1
          rw [← mul_assoc, Units.mul_inv, one_mul]
      ext i j
      fin_cases j
      · exact e0 i
      · exact e1 i
  · intro p _
    rfl

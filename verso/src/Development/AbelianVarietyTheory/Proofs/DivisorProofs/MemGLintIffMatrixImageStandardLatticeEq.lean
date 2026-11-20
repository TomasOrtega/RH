import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrbGL

variable {K : Type} [Field K] (V : ValuationSubring K)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `a.2`. Introduce `h`. Conclude with `⟨⟨x, h⟩, rfl⟩`.
-/
theorem mem_range_iff (x : K) : x ∈ (algebraMap V K).range ↔ x ∈ V := by
  constructor
  · rintro ⟨a, rfl⟩; exact a.2
  · intro h; exact ⟨⟨x, h⟩, rfl⟩

/- English proof (translation)
Introduce `v hv`. Rewrite `hv` using `[mem_matLat]`. Take `⟨u, hu, rfl⟩` from `hv`. Rewrite `hu`, the goal using `[mem_stdLat]`. Introduce `i`.

Establish `hu'` using `fun j => (mem_range_iff V _).1 (hu j)`. Apply `(mem_range_iff V _).2` to reduce the goal to its premises. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `V.toSubring.sum_mem fun j _ => V.toSubring.mul_mem (hg i j) (hu' j)`.
-/
theorem matLat_le_of_entries {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (hg : ∀ i j, g i j ∈ V) :
    matLat V g (stdLat V n) ≤ stdLat V n := by
  intro v hv
  rw [mem_matLat] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rw [mem_stdLat] at hu ⊢
  intro i
  have hu' := fun j => (mem_range_iff V _).1 (hu j)
  apply (mem_range_iff V _).2
  simp only [Matrix.mulVec, dotProduct]
  exact V.toSubring.sum_mem fun j _ => V.toSubring.mul_mem (hg i j) (hu' j)

/- English proof (translation)
Establish `hs : (Pi.single j (1 : K) : Fin n → K) ∈ stdLat V n`. Rewrite using `[mem_stdLat]`. Introduce `l`. Rewrite using `[mem_range_iff]`. Distinguish the cases in `h : l = j`.

Substitute `h` using the available equality. Simplify using `[V.one_mem]`. Simplify using `[Pi.single_apply, h, V.zero_mem]`. Establish `hm : g *ᵥ (Pi.single j (1 : K)) ∈ stdLat V n` using `hg ((mem_matLat _ _ _).2 ⟨_, hs, rfl⟩)`. Rewrite `hm` using `[mem_stdLat]`.

Use `(mem_range_iff V _).1 (hm i)` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single]`.
-/
theorem entries_of_matLat_le {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : matLat V g (stdLat V n) ≤ stdLat V n) (i j : Fin n) : g i j ∈ V := by
  have hs : (Pi.single j (1 : K) : Fin n → K) ∈ stdLat V n := by
    rw [mem_stdLat]
    intro l
    rw [mem_range_iff]
    by_cases h : l = j
    · subst h; simp [V.one_mem]
    · simp [Pi.single_apply, h, V.zero_mem]
  have hm : g *ᵥ (Pi.single j (1 : K)) ∈ stdLat V n := hg ((mem_matLat _ _ _).2 ⟨_, hs, rfl⟩)
  rw [mem_stdLat] at hm
  have := (mem_range_iff V _).1 (hm i)
  simpa [Matrix.mulVec_single] using this

/- English proof (translation)
The claim follows from `Submodule.map_mono h`.
-/
theorem matLat_mono {n : ℕ} (g : Matrix (Fin n) (Fin n) K) {M N : Submodule V (Fin n → K)}
    (h : M ≤ N) : matLat V g M ≤ matLat V g N := Submodule.map_mono h

end GlobalTheory.LatOrbGL

open GlobalTheory.LatOrbGL in

/- English proof (translation)
Introduce `K _ V n k`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩ set k := Formalism.UG.bc V.toSubring.subtype g with hk`. Establish `e1 : ∀ i j, k.val i j ∈ V`. Introduce `i j`.

Conclude with `((g : Matrix (Fin n) (Fin n) V.toSubring) i j).2`. Establish `e2 : ∀ i j, (k⁻¹).val i j ∈ V`. Introduce `i j`. Rewrite using `[hk, ← map_inv]`. Conclude with `(((g⁻¹ : GL (Fin n) V.toSubring) : Matrix (Fin n) (Fin n) V.toSubring) i j).2`.

Apply `le_antisymm (matLat_le_of_entries V _ e1)` to reduce the goal to its premises. Establish `: k.val * (k⁻¹).val = 1` using `by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]`. Combine the equalities or inequalities in the displayed calculation. Introduce `h`. Establish `e1` using `entries_of_matLat_le V k.val h.le`.

Establish `h2 : matLat V (k⁻¹ : GL (Fin n) K).val (stdLat V n) = stdLat V n` using `by conv_lhs => rw [← h]`. Rewrite using `[← matLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, matLat_one]`. Establish `e2` using `entries_of_matLat_le V (k⁻¹ : GL (Fin n) K).val h2.le`. Set `A : Matrix (Fin n) (Fin n) V.toSubring` to `Matrix.of fun i j => ⟨k.val i j, e1 i j⟩`. Set `B : Matrix (Fin n) (Fin n) V.toSubring` to `Matrix.of fun i j => ⟨(k⁻¹ : GL (Fin n) K).val i j, e2 i j⟩`.

Establish `hA : (RingHom.mapMatrix V.toSubring.subtype) A = k.val` using `by ext i j; rfl`. Establish `hB : (RingHom.mapMatrix V.toSubring.subtype) B = (k⁻¹ : GL (Fin n) K).val` using `by ext i j; rfl`. Establish `inj : Function.Injective (RingHom.mapMatrix (m` using `Fin n) V.toSubring.subtype) := by`. Introduce `X Y hXY`. Use extensionality with `i j`.

Conclude with `congrFun (congrFun hXY i) j`. Establish `hAB : A * B = 1` using `inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])`. Establish `hBA : B * A = 1` using `inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])`. Use `⟨⟨A, B, hAB, hBA⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Both sides reduce to the same expression.
-/
theorem GlobalTheory.LatOrb.mem_GLint_iff_matLat_std :
    ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (k : GL (Fin n) K),
    k ∈ Formalism.UG.GLint (Fin n) V.toSubring ↔ matLat V k.val (stdLat V n) = stdLat V n := by
  intro K _ V n k
  constructor
  · rintro ⟨g, rfl⟩
    set k := Formalism.UG.bc V.toSubring.subtype g with hk
    have e1 : ∀ i j, k.val i j ∈ V := by
      intro i j; exact ((g : Matrix (Fin n) (Fin n) V.toSubring) i j).2
    have e2 : ∀ i j, (k⁻¹).val i j ∈ V := by
      intro i j; rw [hk, ← map_inv]; exact (((g⁻¹ : GL (Fin n) V.toSubring) : Matrix (Fin n) (Fin n) V.toSubring) i j).2
    apply le_antisymm (matLat_le_of_entries V _ e1)
    have : k.val * (k⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc stdLat V n = matLat V (k.val * (k⁻¹).val) (stdLat V n) := by rw [this, matLat_one]
      _ = _ := matLat_mul _ _ _
      _ ≤ _ := matLat_mono V _ (matLat_le_of_entries V _ e2)
  · intro h
    have e1 := entries_of_matLat_le V k.val h.le
    have h2 : matLat V (k⁻¹ : GL (Fin n) K).val (stdLat V n) = stdLat V n := by
      conv_lhs => rw [← h]
      rw [← matLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, matLat_one]
    have e2 := entries_of_matLat_le V (k⁻¹ : GL (Fin n) K).val h2.le
    let A : Matrix (Fin n) (Fin n) V.toSubring := Matrix.of fun i j => ⟨k.val i j, e1 i j⟩
    let B : Matrix (Fin n) (Fin n) V.toSubring := Matrix.of fun i j => ⟨(k⁻¹ : GL (Fin n) K).val i j, e2 i j⟩
    have hA : (RingHom.mapMatrix V.toSubring.subtype) A = k.val := by ext i j; rfl
    have hB : (RingHom.mapMatrix V.toSubring.subtype) B = (k⁻¹ : GL (Fin n) K).val := by ext i j; rfl
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) V.toSubring.subtype) := by
      intro X Y hXY; ext i j; exact congrFun (congrFun hXY i) j
    have hAB : A * B = 1 := inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    have hBA : B * A = 1 := inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl

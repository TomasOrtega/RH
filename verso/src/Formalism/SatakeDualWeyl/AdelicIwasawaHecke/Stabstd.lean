import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.UG.P

open Matrix

variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Simplify using `only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range, Algebra.linearMap_apply, Set.mem_range]`.
-/
theorem mem_stdLat_iff' (x : n → A) :
    x ∈ stdLat (n := n) (A := A) R ↔ ∀ i, x i ∈ Set.range (algebraMap R A) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range,
    Algebra.linearMap_apply, Set.mem_range]

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_stdLat_iff']`. Use `choose y hy using hx`. Establish `hxy : x = fun j => algebraMap R A (y j)` using `funext fun j => (hy j).symm`. Substitute `hxy` using the available equality. Introduce `i`.

Use `⟨(M *ᵥ y) i, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]`.
-/
theorem map_mulVec_mem_stdLat (M : Matrix n n R) (x : n → A)
    (hx : x ∈ stdLat (n := n) (A := A) R) :
    (M.map (algebraMap R A)) *ᵥ x ∈ stdLat (n := n) (A := A) R := by
  rw [mem_stdLat_iff'] at hx ⊢
  choose y hy using hx
  have hxy : x = fun j => algebraMap R A (y j) := funext fun j => (hy j).symm
  subst hxy
  intro i
  refine ⟨(M *ᵥ y) i, ?_⟩

  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

/- English proof (translation)
Establish `hmem : (Pi.single j 1 : n → A) ∈ stdLat (n` using `n) (A := A) R := by`. Rewrite using `[mem_stdLat_iff']`. Introduce `k`. Distinguish the cases in `hk : k = j`. Substitute `hk; exact ⟨1, by simp⟩` using the available equality.

Conclude with `⟨0, by simp [Pi.single_apply, hk]⟩`. Establish `h2` using `((hh (Pi.single j 1)).1 hmem)`. Rewrite `h2` using `[mem_stdLat_iff']`. Establish `h3` using `h2 i`. Simplify `h3` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem entries_mem_of_mem_stabGL (h : GL n A) (hh : h ∈ stabGL (stdLat (n := n) (A := A) R))
    (i j : n) : (h : Matrix n n A) i j ∈ Set.range (algebraMap R A) := by
  have hmem : (Pi.single j 1 : n → A) ∈ stdLat (n := n) (A := A) R := by
    rw [mem_stdLat_iff']
    intro k
    by_cases hk : k = j
    · subst hk; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, hk]⟩
  have h2 := ((hh (Pi.single j 1)).1 hmem)
  rw [mem_stdLat_iff'] at h2
  have h3 := h2 i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_bc (φ : R →+* A) (u : GL n R) :
    ((bc (n := n) φ u : GL n A) : Matrix n n A) = (u : Matrix n n R).map φ := by
  rfl

/- English proof (translation)
Introduce `A R _ _ _ n _ _ hinj`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `hg' : g⁻¹ ∈ stabGL (stdLat (n` using `n) (A := A) R) := inv_mem hg`.

Use `choose r hr using entries_mem_of_mem_stabGL (R := R) g hg`. Use `choose r' hr' using entries_mem_of_mem_stabGL (R := R) g⁻¹ hg'`. Set `M : Matrix n n R` to `Matrix.of r`. Set `M' : Matrix n n R` to `Matrix.of r'`. Establish `hM : M.map (algebraMap R A) = (g : Matrix n n A)`.

Use extensionality with `i j`. Simplify using `[M, hr]`. Establish `hM' : M'.map (algebraMap R A) = ((g⁻¹ : GL n A) : Matrix n n A)`. Use extensionality with `i j`. Simplify using `[M', hr']`.

Establish `h1 : M * M' = 1`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `Units.mul_inv g`.

Establish `h2 : M' * M = 1`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `Units.inv_mul g`.

Use `⟨⟨M, M', h1, h2⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `: 1`. Rewrite using `[coe_bc]`. Conclude with `hM`. Introduce and unpack `⟨u, rfl⟩`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Rewrite using `[coe_bc]`. Conclude with `map_mulVec_mem_stdLat _ x hx`.

Introduce `hx`. Establish `hinv` using `map_mulVec_mem_stdLat (A := A) ((u⁻¹ : GL n R) : Matrix n n R) _ hx`. Rewrite `hinv` using `[← coe_bc, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]`. Conclude with `hinv`.
-/
theorem stabilizer_standard_lattice : Formalism.UG.StabStd := by
  intro A R _ _ _ n _ _ hinj
  ext g
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ stabGL (stdLat (n := n) (A := A) R) := inv_mem hg
    choose r hr using entries_mem_of_mem_stabGL (R := R) g hg
    choose r' hr' using entries_mem_of_mem_stabGL (R := R) g⁻¹ hg'
    let M : Matrix n n R := Matrix.of r
    let M' : Matrix n n R := Matrix.of r'
    have hM : M.map (algebraMap R A) = (g : Matrix n n A) := by
      ext i j; simp [M, hr]
    have hM' : M'.map (algebraMap R A) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j; simp [M', hr']
    have h1 : M * M' = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact Units.mul_inv g
    have h2 : M' * M = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact Units.inv_mul g
    refine ⟨⟨M, M', h1, h2⟩, ?_⟩
    ext : 1
    rw [coe_bc]
    exact hM
  · rintro ⟨u, rfl⟩
    intro x
    constructor
    · intro hx
      rw [coe_bc]
      exact map_mulVec_mem_stdLat _ x hx
    · intro hx
      have hinv := map_mulVec_mem_stdLat (A := A) ((u⁻¹ : GL n R) : Matrix n n R) _ hx
      rw [← coe_bc, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
        Units.val_one, Matrix.one_mulVec] at hinv
      exact hinv

end Formalism.UG.P

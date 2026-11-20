import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

open GlobalTheory.SmGL in

/- English proof (translation)
Introduce `R _ _ n a b h ha hb`. Use `set e := stdBlocks ![a, b] h with he`. Set `i : Fin n` to `e ⟨0, ⟨0, by simpa using ha⟩⟩`. Set `j : Fin n` to `e ⟨1, ⟨0, by simpa using hb⟩⟩`. Establish `hij : i ≠ j`.

Introduce `hh`. Use `congrArg Sigma.fst (e.injective hh)` as an intermediate fact. Simplify using `at this`. Set `g : GL (Fin n) R` to `⟨Matrix.transvection i j 1, Matrix.transvection i j (-1), by show Matrix.transvection i j (1 : R) * Matrix.transvection i j (-1) = 1`. Rewrite using `[Matrix.transvection_mul_transvection_same i j hij]`.

Use the proof step `simp,`. Use `by show Matrix.transvection i j (-1 : R) * Matrix.transvection i j 1 = 1`. Rewrite using `[Matrix.transvection_mul_transvection_same i j hij]`. Use the proof step `simp⟩`. Establish `hg : (g : Matrix (Fin n) (Fin n) R) = 1 + Matrix.single i j 1` using `rfl`.

Establish `hmem : g ∈ unipRad R e`. Rewrite using `[mem_unipRad]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_parab]`. Introduce `p q hpq`.

Establish `hne : p ≠ q` using `by rintro rfl; exact lt_irrefl _ hpq`. Rewrite using `[hg, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]`. Distinguish the cases in `hp : p = i`. Distinguish the cases in `hq : q = j`. Substitute `hp` using the available equality.

Substitute `hq` using the available equality. Rewrite `hpq` using `[blk_apply, blk_apply]`. Conclude with `absurd hpq (by decide)`. Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨_, h'⟩`.

Conclude with `hq h'.symm`. Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨h', _⟩`. Conclude with `hp h'.symm`. Introduce `c x y`.

Rewrite using `[hg, Matrix.add_apply]`. Establish `h1 : (1 : Matrix (Fin n) (Fin n) R) (e ⟨c, x⟩) (e ⟨c, y⟩) = (1 : Matrix _ _ R) x y`. Distinguish the cases in `hxy : x = y`. Substitute `hxy` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.one_apply_ne, Matrix.one_apply_ne hxy]`. Introduce `hh`. Use `e.injective hh` as an intermediate fact. Simplify using `at this`. Conclude with `hxy this`.

Rewrite using `[h1]`. Establish `h2 : Matrix.single i j (1 : R) (e ⟨c, x⟩) (e ⟨c, y⟩) = 0`. Rewrite using `[Matrix.single_apply]`. Use `split_ifs with hh`. Take `⟨h3, h4⟩` from `hh`.

Establish `e3` using `congrArg Sigma.fst (e.injective h3)`. Establish `e4` using `congrArg Sigma.fst (e.injective h4)`. Simplify using `only at e3 e4`. Rewrite `e4` using `[← e3]`. Conclude with `absurd e4 (by decide)`.

Both sides reduce to the same expression. Rewrite using `[h2, add_zero]`. Introduce `hbot`. Rewrite `hmem` using `[hbot, Subgroup.mem_bot]`. Use `congrArg (fun u : GL (Fin n) R => (u : Matrix (Fin n) (Fin n) R) i j) hmem` as an intermediate fact.

Simplify using `[hg, Matrix.one_apply_ne hij] at this`.
-/
theorem unipRad_stdBlocks_two_ne_bot : ∀ (R : Type) [CommRing R] [Nontrivial R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n), 0 < a → 0 < b → unipRad R (stdBlocks ![a, b] h) ≠ ⊥ := by
  intro R _ _ n a b h ha hb
  set e := stdBlocks ![a, b] h with he
  let i : Fin n := e ⟨0, ⟨0, by simpa using ha⟩⟩
  let j : Fin n := e ⟨1, ⟨0, by simpa using hb⟩⟩
  have hij : i ≠ j := by
    intro hh
    have := congrArg Sigma.fst (e.injective hh)
    simp at this
  let g : GL (Fin n) R :=
    ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by
        show Matrix.transvection i j (1 : R) * Matrix.transvection i j (-1) = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp,
      by
        show Matrix.transvection i j (-1 : R) * Matrix.transvection i j 1 = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp⟩
  have hg : (g : Matrix (Fin n) (Fin n) R) = 1 + Matrix.single i j 1 := rfl
  have hmem : g ∈ unipRad R e := by
    rw [mem_unipRad]
    refine ⟨?_, ?_⟩
    · rw [mem_parab]
      intro p q hpq
      have hne : p ≠ q := by rintro rfl; exact lt_irrefl _ hpq
      rw [hg, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
      by_cases hp : p = i
      · by_cases hq : q = j
        · subst hp; subst hq
          rw [blk_apply, blk_apply] at hpq
          exact absurd hpq (by decide)
        · rw [Matrix.single_apply, if_neg]
          rintro ⟨_, h'⟩; exact hq h'.symm
      · rw [Matrix.single_apply, if_neg]
        rintro ⟨h', _⟩; exact hp h'.symm
    · intro c x y
      rw [hg, Matrix.add_apply]
      have h1 : (1 : Matrix (Fin n) (Fin n) R) (e ⟨c, x⟩) (e ⟨c, y⟩) = (1 : Matrix _ _ R) x y := by
        by_cases hxy : x = y
        · subst hxy; simp
        · rw [Matrix.one_apply_ne, Matrix.one_apply_ne hxy]
          intro hh
          have := e.injective hh
          simp at this
          exact hxy this
      rw [h1]
      have h2 : Matrix.single i j (1 : R) (e ⟨c, x⟩) (e ⟨c, y⟩) = 0 := by
        rw [Matrix.single_apply]
        split_ifs with hh
        · obtain ⟨h3, h4⟩ := hh
          have e3 := congrArg Sigma.fst (e.injective h3)
          have e4 := congrArg Sigma.fst (e.injective h4)
          simp only at e3 e4
          rw [← e3] at e4
          exact absurd e4 (by decide)
        · rfl
      rw [h2, add_zero]
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  have := congrArg (fun u : GL (Fin n) R => (u : Matrix (Fin n) (Fin n) R) i j) hmem
  simp [hg, Matrix.one_apply_ne hij] at this

end GlobalTheory

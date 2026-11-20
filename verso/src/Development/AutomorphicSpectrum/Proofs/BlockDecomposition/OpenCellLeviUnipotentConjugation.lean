import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.LeviPart

section Order

variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

def pos : (Σ a, Fin (d a)) ≃ Fin N := (stdBlocks d hd).trans (wOpen d hd).symm

/- English proof (translation)
Simplify using `[pos]`.
-/
theorem wOpen_pos (x : Σ a, Fin (d a)) : wOpen d hd (pos d hd x) = stdBlocks d hd x := by
  simp [pos]

/- English proof (translation)
Introduce `x y hxy`. Conclude with `congrArg (fun z => (ofLex z).2) hxy`.
-/
theorem wKey_injective : Function.Injective (wKey d hd) := by
  intro x y hxy
  exact congrArg (fun z => (ofLex z).2) hxy

/- English proof (translation)
The claim follows from `(Tuple.monotone_sort (wKey d hd)).strictMono_of_injective ((wKey_injective d hd).comp (wOpen d hd).injective)`.
-/
theorem key_strictMono : StrictMono (wKey d hd ∘ wOpen d hd) :=
  (Tuple.monotone_sort (wKey d hd)).strictMono_of_injective
    ((wKey_injective d hd).comp (wOpen d hd).injective)

/- English proof (translation)
Simplify using `[blk]`.
-/
theorem blk_std (x : Σ a, Fin (d a)) : blk (stdBlocks d hd) (stdBlocks d hd x) = x.1 := by
  simp [blk]

/- English proof (translation)
Rewrite using `[wKey, wKey, Prod.Lex.lt_iff]`. Simplify using `[blk_std]`.
-/
theorem key_lt (x y : Σ a, Fin (d a)) :
    wKey d hd (stdBlocks d hd x) < wKey d hd (stdBlocks d hd y) ↔
      y.1 < x.1 ∨ x.1 = y.1 ∧ stdBlocks d hd x < stdBlocks d hd y := by
  rw [wKey, wKey, Prod.Lex.lt_iff]
  simp [blk_std]

/- English proof (translation)
Rewrite using `[Fin.lt_def, stdBlocks_val, stdBlocks_val, Fin.lt_def]`. Use linear arithmetic over natural numbers and integers.
-/
theorem std_lt (a : Fin h) (i j : Fin (d a)) :
    stdBlocks d hd ⟨a, i⟩ < stdBlocks d hd ⟨a, j⟩ ↔ i < j := by
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, Fin.lt_def]
  omega

/- English proof (translation)
Rewrite using `[← (key_strictMono d hd).lt_iff_lt, Function.comp, Function.comp, wOpen_pos, wOpen_pos, key_lt]`.
-/
theorem pos_lt_iff (x y : Σ a, Fin (d a)) :
    pos d hd x < pos d hd y ↔ y.1 < x.1 ∨ x.1 = y.1 ∧ stdBlocks d hd x < stdBlocks d hd y := by
  rw [← (key_strictMono d hd).lt_iff_lt, Function.comp, Function.comp, wOpen_pos, wOpen_pos, key_lt]

/- English proof (translation)
Rewrite using `[pos_lt_iff, std_lt]`. Simplify using the standard rewrite rules.
-/
theorem pos_lt (a : Fin h) (i j : Fin (d a)) : pos d hd ⟨a, i⟩ < pos d hd ⟨a, j⟩ ↔ i < j := by
  rw [pos_lt_iff, std_lt]
  simp

/- English proof (translation)
Establish `hlt : pos d hd ⟨a, i⟩ < pos d hd ⟨a, j⟩` using `(pos_lt d hd a i j).2 (Fin.lt_def.2 (by omega))`. Assume the negation of the conclusion as `hne`. Establish `hlt'` using `Fin.lt_def.1 hlt`. Establish `hN` using `(pos d hd ⟨a, j⟩).2`. Set `t : Fin N` to `⟨pos d hd ⟨a, i⟩ + 1, by omega⟩`.

Take `⟨⟨b, l⟩, hl⟩` from `(pos d hd).surjective t`. Establish `h1 : pos d hd ⟨a, i⟩ < pos d hd ⟨b, l⟩`. Rewrite using `[hl]; exact Fin.lt_def.2 (by simp [t])`. Establish `h2 : pos d hd ⟨b, l⟩ < pos d hd ⟨a, j⟩`. Rewrite using `[hl]; exact Fin.lt_def.2 (by simp only [t]; omega)`.

Rewrite `h1`, `h2` using `[pos_lt_iff]`. Establish `hab : a = b`. Break down `h1 with h1 | h1` into its components or cases. Break down `h2 with h2 | h2` into its components or cases. Conclude with `absurd h1 (lt_asymm h2)`.

Conclude with `absurd h2.1 (ne_of_lt h1)`. Conclude with `h1.1`. Substitute `hab` using the available equality. Establish `h3` using `(std_lt d hd a i l).1 (h1.elim (fun e => absurd e (lt_irrefl _)) (·.2))`. Establish `h4` using `(std_lt d hd a l j).1 (h2.elim (fun e => absurd e (lt_irrefl _)) (·.2))`.

Use `Fin.lt_def.1 h3` as an intermediate fact. Use `Fin.lt_def.1 h4` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem pos_succ (a : Fin h) (i j : Fin (d a)) (hij : (j : ℕ) = i + 1) :
    (pos d hd ⟨a, j⟩ : ℕ) = pos d hd ⟨a, i⟩ + 1 := by
  have hlt : pos d hd ⟨a, i⟩ < pos d hd ⟨a, j⟩ := (pos_lt d hd a i j).2 (Fin.lt_def.2 (by omega))
  by_contra hne
  have hlt' := Fin.lt_def.1 hlt
  have hN := (pos d hd ⟨a, j⟩).2
  let t : Fin N := ⟨pos d hd ⟨a, i⟩ + 1, by omega⟩
  obtain ⟨⟨b, l⟩, hl⟩ := (pos d hd).surjective t
  have h1 : pos d hd ⟨a, i⟩ < pos d hd ⟨b, l⟩ := by
    rw [hl]; exact Fin.lt_def.2 (by simp [t])
  have h2 : pos d hd ⟨b, l⟩ < pos d hd ⟨a, j⟩ := by
    rw [hl]; exact Fin.lt_def.2 (by simp only [t]; omega)
  rw [pos_lt_iff] at h1 h2
  have hab : a = b := by
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd h1 (lt_asymm h2)
      · exact absurd h2.1 (ne_of_lt h1)
    · exact h1.1
  subst hab
  have h3 := (std_lt d hd a i l).1 (h1.elim (fun e => absurd e (lt_irrefl _)) (·.2))
  have h4 := (std_lt d hd a l j).1 (h2.elim (fun e => absurd e (lt_irrefl _)) (·.2))
  have := Fin.lt_def.1 h3
  have := Fin.lt_def.1 h4
  omega

/- English proof (translation)
Establish `hlt : i < j` using `(pos_lt d hd a i j).1 (Fin.lt_def.2 (by omega))`. Assume the negation of the conclusion as `hne`. Establish `hlt'` using `Fin.lt_def.1 hlt`. Establish `hj` using `j.2`. Set `l : Fin (d a)` to `⟨i + 1, by omega⟩`.

Establish `h1` using `Fin.lt_def.1 ((pos_lt d hd a i l).2 (Fin.lt_def.2 (by simp [l])))`. Establish `h2` using `Fin.lt_def.1 ((pos_lt d hd a l j).2 (Fin.lt_def.2 (by simp only [l]; omega)))`. Use linear arithmetic over natural numbers and integers.
-/
theorem pos_succ' (a : Fin h) (i j : Fin (d a)) (hij : (pos d hd ⟨a, j⟩ : ℕ) = pos d hd ⟨a, i⟩ + 1) :
    (j : ℕ) = i + 1 := by
  have hlt : i < j := (pos_lt d hd a i j).1 (Fin.lt_def.2 (by omega))
  by_contra hne
  have hlt' := Fin.lt_def.1 hlt
  have hj := j.2
  let l : Fin (d a) := ⟨i + 1, by omega⟩
  have h1 := Fin.lt_def.1 ((pos_lt d hd a i l).2 (Fin.lt_def.2 (by simp [l])))
  have h2 := Fin.lt_def.1 ((pos_lt d hd a l j).2 (Fin.lt_def.2 (by simp only [l]; omega)))
  omega

/- English proof (translation)
Rewrite using `[Finset.sum_sigma']`. Use `symm`. Use `Finset.sum_bij_ne_zero (fun x _ _ => (pos d hd ⟨x.1, x.2.1⟩, pos d hd ⟨x.1, x.2.2⟩)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨b, i, j⟩ hx -`. Establish `hx' : (j : ℕ) = i + 1` using `by simpa using hx`.

Simplify using `using pos_succ d hd b i j hx'`. Introduce and unpack `⟨b, i, j⟩ - - ⟨c, i', j'⟩ - - hxy`. Establish `h1` using `(pos d hd).injective (Prod.ext_iff.1 hxy).1`. Establish `h2` using `(pos d hd).injective (Prod.ext_iff.1 hxy).2`. Simplify using `only [Sigma.mk.injEq] at h1 h2`.

Take `⟨rfl, h1⟩` from `h1`. Take `⟨-, h2⟩` from `h2`. Take `rfl` from `eq_of_heq h1`. Take `rfl` from `eq_of_heq h2`. Both sides reduce to the same expression.

Introduce and unpack `⟨p, q⟩ hpq hne`. Establish `hpq' : (q : ℕ) = p + 1` using `by simpa using hpq`. Take `⟨⟨b, i⟩, rfl⟩` from `(pos d hd).surjective p`. Take `⟨⟨c, j⟩, rfl⟩` from `(pos d hd).surjective q`. Establish `hbc : b = c`.

Assume the negation of the conclusion as `hbc`. Conclude with `hne (hA _ _ hbc)`. Substitute `hbc` using the available equality. Use `⟨⟨b, i, j⟩, ?_, hne, rfl⟩` and prove the remaining obligations. Simplify using `using pos_succ' d hd b i j hpq'`.

Introduce `x _ _`. Both sides reduce to the same expression.
-/
theorem sum_superdiag {R : Type} [AddCommMonoid R] (A : Fin N → Fin N → R)
    (hA : ∀ x y : Σ a, Fin (d a), x.1 ≠ y.1 → A (pos d hd x) (pos d hd y) = 0) :
    ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, A p.1 p.2 =
      ∑ b, ∑ p : Fin (d b) × Fin (d b) with (p.2 : ℕ) = p.1 + 1, A (pos d hd ⟨b, p.1⟩) (pos d hd ⟨b, p.2⟩) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => (pos d hd ⟨x.1, x.2.1⟩, pos d hd ⟨x.1, x.2.2⟩)) ?_ ?_ ?_ ?_
  · rintro ⟨b, i, j⟩ hx -
    have hx' : (j : ℕ) = i + 1 := by simpa using hx
    simpa using pos_succ d hd b i j hx'
  · rintro ⟨b, i, j⟩ - - ⟨c, i', j'⟩ - - hxy
    have h1 := (pos d hd).injective (Prod.ext_iff.1 hxy).1
    have h2 := (pos d hd).injective (Prod.ext_iff.1 hxy).2
    simp only [Sigma.mk.injEq] at h1 h2
    obtain ⟨rfl, h1⟩ := h1
    obtain ⟨-, h2⟩ := h2
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    rfl
  · rintro ⟨p, q⟩ hpq hne
    have hpq' : (q : ℕ) = p + 1 := by simpa using hpq
    obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    obtain ⟨⟨c, j⟩, rfl⟩ := (pos d hd).surjective q
    have hbc : b = c := by
      by_contra hbc
      exact hne (hA _ _ hbc)
    subst hbc
    refine ⟨⟨b, i, j⟩, ?_, hne, rfl⟩
    simpa using pos_succ' d hd b i j hpq'
  · intro x _ _
    rfl

end Order

section Entries

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

/- English proof (translation)
Rewrite using `[← map_inv, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply, Units.val_mul, GroundTheory.Automorphic.permGL_mul_apply]`. Simplify using the standard rewrite rules.
-/
theorem conj_apply (w : Equiv.Perm (Fin N)) (A : GL (Fin N) k) (p q : Fin N) :
    ((pm k w * A * (pm k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (w p) (w q) =
      (A : Matrix (Fin N) (Fin N) k) p q := by
  rw [← map_inv, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply, Units.val_mul,
    GroundTheory.Automorphic.permGL_mul_apply]
  simp

variable {d hd}
variable {A : GL (Fin N) k} {m : Levi k fun a => Fin (d a)}

/- English proof (translation)
Rewrite using `[← leviEmb_apply_same k (stdBlocks d hd) m b i j, ← hm, ← wOpen_pos d hd, ← wOpen_pos d hd, conj_apply]`.
-/
theorem ent_same (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m)
    (b : Fin h) (i j : Fin (d b)) :
    (m b : Matrix (Fin (d b)) (Fin (d b)) k) i j =
      (A : Matrix (Fin N) (Fin N) k) (pos d hd ⟨b, i⟩) (pos d hd ⟨b, j⟩) := by
  rw [← leviEmb_apply_same k (stdBlocks d hd) m b i j, ← hm, ← wOpen_pos d hd, ← wOpen_pos d hd, conj_apply]

/- English proof (translation)
Take `⟨b, i⟩` from `x`. Take `⟨c, j⟩` from `y`. Rewrite using `[← conj_apply (wOpen d hd) A, wOpen_pos, wOpen_pos, hm]`. Conclude with `leviEmb_apply_ne k (stdBlocks d hd) m hxy i j`.
-/
theorem ent_ne (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m)
    (x y : Σ a, Fin (d a)) (hxy : x.1 ≠ y.1) :
    (A : Matrix (Fin N) (Fin N) k) (pos d hd x) (pos d hd y) = 0 := by
  obtain ⟨b, i⟩ := x
  obtain ⟨c, j⟩ := y
  rw [← conj_apply (wOpen d hd) A, wOpen_pos, wOpen_pos, hm]
  exact leviEmb_apply_ne k (stdBlocks d hd) m hxy i j

/- English proof (translation)
Take `⟨h1, h2⟩` from `(mem_unipB k).1 hA`. Use `fun b _ => (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[ent_same hm]`. Conclude with `h1 _ _ ((pos_lt d hd b j i).2 hij)`. Rewrite using `[ent_same hm]`.

Conclude with `h2 _`.
-/
theorem mem_unipM_of (hA : A ∈ unipB k (Fin N))
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    m ∈ unipM k d := by
  obtain ⟨h1, h2⟩ := (mem_unipB k).1 hA
  refine fun b _ => (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [ent_same hm]
    exact h1 _ _ ((pos_lt d hd b j i).2 hij)
  · rw [ent_same hm]
    exact h2 _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]`.
-/
theorem addChar_sum {ι : Type} (ψ : AddChar k Circle) (s : Finset ι) (f : ι → k) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/- English proof (translation)
Use `show Circle.toUnits (ψ _) = ∏ a : Fin h, Circle.toUnits (ψ _)`. Rewrite using `[← map_prod, ← addChar_sum]`. Use `congrArg _ (congrArg _ ?_)` and prove the remaining obligations. Use `(sum_superdiag d hd (fun p q => (A : Matrix (Fin N) (Fin N) k) p q) (ent_ne hm)).trans ?_` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => (ent_same hm b p.1 p.2).symm`.
-/
theorem whit_eq (ψ : AddChar k Circle) (hA : A ∈ unipB k (Fin N)) (hm' : m ∈ unipM k d)
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    whitChar ψ N ⟨A, hA⟩ = whitM d ψ ⟨m, hm'⟩ := by
  show Circle.toUnits (ψ _) = ∏ a : Fin h, Circle.toUnits (ψ _)
  rw [← map_prod, ← addChar_sum]
  refine congrArg _ (congrArg _ ?_)
  refine (sum_superdiag d hd (fun p q => (A : Matrix (Fin N) (Fin N) k) p q) (ent_ne hm)).trans ?_
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => (ent_same hm b p.1 p.2).symm

/- English proof (translation)
Use `(mem_unipB k).2 ⟨fun p q hpq => ?_, fun p => ?_⟩` and prove the remaining obligations. Take `⟨⟨b, i⟩, rfl⟩` from `(pos d hd).surjective p`. Take `⟨⟨c, j⟩, rfl⟩` from `(pos d hd).surjective q`. Distinguish the cases in `hbc : b = c`. Substitute `hbc` using the available equality.

Rewrite using `[← ent_same hm]`. Conclude with `((mem_unipB k).1 (hm' b (Set.mem_univ b))).1 i j ((pos_lt d hd b j i).1 hpq)`. Conclude with `ent_ne hm _ _ hbc`. Take `⟨⟨b, i⟩, rfl⟩` from `(pos d hd).surjective p`. Rewrite using `[← ent_same hm]`.

Conclude with `((mem_unipB k).1 (hm' b (Set.mem_univ b))).2 i`.
-/
theorem mem_unipB_of (hm' : m ∈ unipM k d)
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    A ∈ unipB k (Fin N) := by
  refine (mem_unipB k).2 ⟨fun p q hpq => ?_, fun p => ?_⟩
  · obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    obtain ⟨⟨c, j⟩, rfl⟩ := (pos d hd).surjective q
    by_cases hbc : b = c
    · subst hbc
      rw [← ent_same hm]
      exact ((mem_unipB k).1 (hm' b (Set.mem_univ b))).1 i j ((pos_lt d hd b j i).1 hpq)
    · exact ent_ne hm _ _ hbc
  · obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    rw [← ent_same hm]
    exact ((mem_unipB k).1 (hm' b (Set.mem_univ b))).2 i

end Entries

/- English proof (translation)
Introduce `k _ _ _ _ ψ h N d hd`. Use `⟨fun a ha hb => ?_, fun m => ?_⟩` and prove the remaining obligations. Take `⟨m₀, hm₀⟩` from `(Subgroup.mem_inf.1 ha).2`. Establish `hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m₀` using `hm₀.symm`. Establish `hm'` using `mem_unipM_of hb hm`.

Conclude with `⟨⟨m₀, hm'⟩, hm, whit_eq ψ hb hm' hm⟩`. Establish `hc : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * leviEmb k (stdBlocks d hd) m.1 * pm k (wOpen d hd)) * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1` using `by group`. Conclude with `⟨_, Subgroup.mem_inf.2 ⟨mem_unipB_of m.2 hc, ⟨m.1, hc.symm⟩⟩, hc⟩`.
-/
theorem levi_part : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (hb : a ∈ unipB k (Fin N)), ∃ m : unipM k d, pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 ∧ whitChar ψ N ⟨a, hb⟩ = whitM d ψ m) ∧ ∀ m : unipM k d, ∃ a ∈ unipL k d hd, pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 := by
  intro k _ _ _ _ ψ h N d hd
  refine ⟨fun a ha hb => ?_, fun m => ?_⟩
  · obtain ⟨m₀, hm₀⟩ := (Subgroup.mem_inf.1 ha).2
    have hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m₀ := hm₀.symm
    have hm' := mem_unipM_of hb hm
    exact ⟨⟨m₀, hm'⟩, hm, whit_eq ψ hb hm' hm⟩
  · have hc : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * leviEmb k (stdBlocks d hd) m.1 * pm k (wOpen d hd)) *
        (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 := by group
    exact ⟨_, Subgroup.mem_inf.2 ⟨mem_unipB_of m.2 hc, ⟨m.1, hc.symm⟩⟩, hc⟩

end GlobalTheory.CompanionTheory.Rodier.LeviPart

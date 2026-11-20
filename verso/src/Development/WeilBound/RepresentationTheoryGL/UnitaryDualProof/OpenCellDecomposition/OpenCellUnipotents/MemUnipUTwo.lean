import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.BlockIndexOfWeylShuffle

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier

namespace PositivityTheory.RgUd.CellA

variable {r m : ℕ}

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Rewrite using `[wOpen_two, ← map_inv, Units.val_mul, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply, GroundTheory.Automorphic.permGL_mul_apply]`. Both sides reduce to the same expression.
-/
theorem wConj_apply (u : GL (Fin (r + m)) k) (i j : Fin (r + m)) :
    ((pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ : GL (Fin (r + m)) k) :
      Matrix (Fin (r + m)) (Fin (r + m)) k) i j =
      (u : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm i) ((w2 r m).symm j) := by
  rw [wOpen_two, ← map_inv, Units.val_mul, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply,
    GroundTheory.Automorphic.permGL_mul_apply]
  rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use `set e := stdBlocks (dd r m) (hdd r m) with he`. Establish `hblk : ∀ (a : Fin 2) (i' : Fin (dd r m a)), ((w2 r m).symm (e ⟨a, i'⟩) : ℕ) < m ↔ a = 1`. Introduce `a i'`. Use `weyl_shuffle_symm_lt_iff (r := r) (m := m) (e ⟨a, i'⟩)` as an intermediate fact. Rewrite `this` using `[blk_apply]`. Then use the resulting hypothesis.

Establish `hone : ∀ (a b : Fin 2) (i' : Fin (dd r m a)) (j' : Fin (dd r m b)), (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm (e ⟨a, i'⟩)) ((w2 r m).symm (e ⟨b, j'⟩)) = if (⟨a, i'⟩ : Σ c, Fin (dd r m c)) = ⟨b, j'⟩ then 1 else 0`. Introduce `a b i' j'`. Rewrite using `[Matrix.one_apply]`. Distinguish the cases in `h : (⟨a, i'⟩ : Σ c, Fin (dd r m c)) = ⟨b, j'⟩`. Rewrite using `[if_pos h, if_pos (by rw [h])]`.

Rewrite using `[if_neg h, if_neg (fun h' => h (e.injective ((w2 r m).symm.injective h')))]`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Use `⟨hu.1, fun p q hpq => ?_⟩` and prove the remaining obligations. Establish `h2 : pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈ unipRadLower k e` using `hu.2`.

Take `⟨hP, hD⟩` from `(mem_unipRadLower k).1 h2`. Take `⟨⟨a, i'⟩, hi⟩` from `e.surjective (w2 r m p)`. Take `⟨⟨b, j'⟩, hj⟩` from `e.surjective (w2 r m q)`. Establish `hp : p = (w2 r m).symm (e ⟨a, i'⟩)` using `by rw [hi, Equiv.symm_apply_apply]`. Establish `hq : q = (w2 r m).symm (e ⟨b, j'⟩)` using `by rw [hj, Equiv.symm_apply_apply]`.

Establish `hpa` using `hblk a i'`. Establish `hqb` using `hblk b j'`. Rewrite `hpa` using `[← hp]`. Rewrite `hqb` using `[← hq]`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases.

It suffices to derive a contradiction. Establish `h3` using `(mem_parabLower_iff k).1 hP a b i' j' hab`. Rewrite `h3` using `[wConj_apply, ← hp, ← hq]`. Apply `hpq` to reduce the goal to its premises. Rewrite using `[h3, hp, hq, hone, if_neg (fun h => hab.ne (congrArg Sigma.fst h))]`.

It suffices to derive a contradiction. Establish `h3` using `hD a i' j'`. Rewrite `h3` using `[wConj_apply, ← hp, ← hq]`. Apply `hpq` to reduce the goal to its premises. Rewrite using `[h3, hp, hq, hone, Matrix.one_apply]`.

Distinguish the cases in `h : i' = j'`. Rewrite using `[if_pos h, if_pos (by rw [h])]`. Rewrite using `[if_neg h, if_neg (fun h' => h (by simpa using h'))]`. Apply the tactic sequence `have ha : a = 1 := by fin_cases a <;> fin_cases b <;> simp_all`. Apply the tactic sequence `have hb : b = 0 := by fin_cases a <;> fin_cases b <;> simp_all`.

Use `⟨hpa.2 ha, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hq'`. Use `push_neg at hq'`. Conclude with `absurd (hqb.1 hq') (by rw [hb]; decide)`. Introduce and unpack `⟨hB, hc⟩`.

Use `⟨hB, ?_⟩` and prove the remaining obligations. Use `show pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈ unipRadLower k e`. Use `(mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i' j' hab => ?_, fun a i' j' => ?_⟩` and prove the remaining obligations. Rewrite using `[wConj_apply]`. Apply the tactic sequence `have ha : a = 0 := by fin_cases a <;> fin_cases b <;> simp_all`.

Apply the tactic sequence `have hb : b = 1 := by fin_cases a <;> fin_cases b <;> simp_all`. Assume the negation of the conclusion as `hne`. Establish `h1` using `hc _ _ (by`. Rewrite using `[hone, if_neg (fun h => hab.ne (congrArg Sigma.fst h))]`. Conclude with `hne)`.

Establish `h2` using `(hblk a i').1 h1.1`. Rewrite `h2` using `[ha]`. Conclude with `absurd h2 (by decide)`. Rewrite using `[wConj_apply]`. Establish `hpq : (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm (e ⟨a, i'⟩)) ((w2 r m).symm (e ⟨a, j'⟩)) = (1 : Matrix (Fin (dd r m a)) (Fin (dd r m a)) k) i' j'`.

Rewrite using `[hone, Matrix.one_apply]`. Distinguish the cases in `h' : i' = j'`. Substitute `h'` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h => h' (by simpa using h)), if_neg h']`.

Rewrite using `[← hpq]`. Assume the negation of the conclusion as `hne`. Take `⟨h1, h2⟩` from `hc _ _ hne`. Conclude with `absurd ((hblk a j').2 ((hblk a i').1 h1)) (not_lt.2 h2)`.
-/
theorem mem_unipU_two {u : GL (Fin (r + m)) k} :
    u ∈ unipU k (dd r m) (hdd r m) ↔ u ∈ unipB k (Fin (r + m)) ∧ ∀ i j : Fin (r + m),
      (u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j ≠ (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j →
        (i : ℕ) < m ∧ m ≤ (j : ℕ) := by
  set e := stdBlocks (dd r m) (hdd r m) with he
  have hblk : ∀ (a : Fin 2) (i' : Fin (dd r m a)), ((w2 r m).symm (e ⟨a, i'⟩) : ℕ) < m ↔ a = 1 := by
    intro a i'
    have := weyl_shuffle_symm_lt_iff (r := r) (m := m) (e ⟨a, i'⟩)
    rwa [blk_apply] at this
  have hone : ∀ (a b : Fin 2) (i' : Fin (dd r m a)) (j' : Fin (dd r m b)),
      (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm (e ⟨a, i'⟩)) ((w2 r m).symm (e ⟨b, j'⟩)) =
        if (⟨a, i'⟩ : Σ c, Fin (dd r m c)) = ⟨b, j'⟩ then 1 else 0 := by
    intro a b i' j'
    rw [Matrix.one_apply]
    by_cases h : (⟨a, i'⟩ : Σ c, Fin (dd r m c)) = ⟨b, j'⟩
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (e.injective ((w2 r m).symm.injective h')))]
  constructor
  · intro hu
    refine ⟨hu.1, fun p q hpq => ?_⟩
    have h2 : pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈
        unipRadLower k e := hu.2
    obtain ⟨hP, hD⟩ := (mem_unipRadLower k).1 h2
    obtain ⟨⟨a, i'⟩, hi⟩ := e.surjective (w2 r m p)
    obtain ⟨⟨b, j'⟩, hj⟩ := e.surjective (w2 r m q)
    have hp : p = (w2 r m).symm (e ⟨a, i'⟩) := by rw [hi, Equiv.symm_apply_apply]
    have hq : q = (w2 r m).symm (e ⟨b, j'⟩) := by rw [hj, Equiv.symm_apply_apply]
    have hpa := hblk a i'
    have hqb := hblk b j'
    rw [← hp] at hpa
    rw [← hq] at hqb
    rcases lt_trichotomy a b with hab | rfl | hab
    · exfalso
      have h3 := (mem_parabLower_iff k).1 hP a b i' j' hab
      rw [wConj_apply, ← hp, ← hq] at h3
      apply hpq
      rw [h3, hp, hq, hone, if_neg (fun h => hab.ne (congrArg Sigma.fst h))]
    · exfalso
      have h3 := hD a i' j'
      rw [wConj_apply, ← hp, ← hq] at h3
      apply hpq
      rw [h3, hp, hq, hone, Matrix.one_apply]
      by_cases h : i' = j'
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun h' => h (by simpa using h'))]
    · have ha : a = 1 := by fin_cases a <;> fin_cases b <;> simp_all
      have hb : b = 0 := by fin_cases a <;> fin_cases b <;> simp_all
      refine ⟨hpa.2 ha, ?_⟩
      by_contra hq'
      push_neg at hq'
      exact absurd (hqb.1 hq') (by rw [hb]; decide)
  · rintro ⟨hB, hc⟩
    refine ⟨hB, ?_⟩
    show pm k (wOpen (dd r m) (hdd r m)) * u * (pm k (wOpen (dd r m) (hdd r m)))⁻¹ ∈ unipRadLower k e
    refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i' j' hab => ?_, fun a i' j' => ?_⟩
    · rw [wConj_apply]
      have ha : a = 0 := by fin_cases a <;> fin_cases b <;> simp_all
      have hb : b = 1 := by fin_cases a <;> fin_cases b <;> simp_all
      by_contra hne
      have h1 := hc _ _ (by
        rw [hone, if_neg (fun h => hab.ne (congrArg Sigma.fst h))]
        exact hne)
      have h2 := (hblk a i').1 h1.1
      rw [ha] at h2
      exact absurd h2 (by decide)
    · rw [wConj_apply]
      have hpq : (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) ((w2 r m).symm (e ⟨a, i'⟩)) ((w2 r m).symm (e ⟨a, j'⟩)) =
          (1 : Matrix (Fin (dd r m a)) (Fin (dd r m a)) k) i' j' := by
        rw [hone, Matrix.one_apply]
        by_cases h' : i' = j'
        · subst h'
          simp
        · rw [if_neg (fun h => h' (by simpa using h)), if_neg h']
      rw [← hpq]
      by_contra hne
      obtain ⟨h1, h2⟩ := hc _ _ hne
      exact absurd ((hblk a j').2 ((hblk a i').1 h1)) (not_lt.2 h2)

end PositivityTheory.RgUd.CellA

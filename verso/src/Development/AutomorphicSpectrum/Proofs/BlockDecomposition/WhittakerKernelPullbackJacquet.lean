import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadical

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair

noncomputable section

namespace GlobalTheory.CompanionTheory.BZNuPair.DerComap

section Groups

variable {k : Type} [Field k] {N : ℕ} (d : Fin 2 → ℕ) (h : ∑ a, d a = N)

/- English proof (translation)
Simplify using `using stdBlocks_val d h 0 i`.
-/
theorem stdBlocks_zero_val (i : Fin (d 0)) : (stdBlocks d h ⟨0, i⟩ : ℕ) = i := by
  simpa using stdBlocks_val d h 0 i

/- English proof (translation)
Use `stdBlocks_val d h 1 i` as an intermediate fact. Simplify using `using this`.
-/
theorem stdBlocks_one_val (i : Fin (d 1)) : (stdBlocks d h ⟨1, i⟩ : ℕ) = d 0 + i := by
  have := stdBlocks_val d h 1 i
  simpa using this

/- English proof (translation)
Take `⟨⟨c, i'⟩, rfl⟩` from `(stdBlocks d h).surjective i`. Establish `key : ∀ (c : Fin 2) (i' : Fin (d c)), (∃ a : Fin (d 0), stdBlocks d h ⟨c, i'⟩ = stdBlocks d h ⟨0, a⟩) ∨ ∃ a : Fin (d 1), stdBlocks d h ⟨c, i'⟩ = stdBlocks d h ⟨1, a⟩` using `Fin.forall_fin_two.2 ⟨fun i' => Or.inl ⟨i', rfl⟩, fun i' => Or.inr ⟨i', rfl⟩⟩`. Conclude with `key c i'`.
-/
theorem idx_cases (i : Fin N) : (∃ a : Fin (d 0), i = stdBlocks d h ⟨0, a⟩) ∨
    ∃ a : Fin (d 1), i = stdBlocks d h ⟨1, a⟩ := by
  obtain ⟨⟨c, i'⟩, rfl⟩ := (stdBlocks d h).surjective i
  have key : ∀ (c : Fin 2) (i' : Fin (d c)),
      (∃ a : Fin (d 0), stdBlocks d h ⟨c, i'⟩ = stdBlocks d h ⟨0, a⟩) ∨
        ∃ a : Fin (d 1), stdBlocks d h ⟨c, i'⟩ = stdBlocks d h ⟨1, a⟩ :=
    Fin.forall_fin_two.2 ⟨fun i' => Or.inl ⟨i', rfl⟩, fun i' => Or.inr ⟨i', rfl⟩⟩
  exact key c i'

/- English proof (translation)
Break down `idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Rewrite using `[blk_apply, stdBlocks_zero_val, if_pos a.2]`. Rewrite using `[blk_apply, stdBlocks_one_val, if_neg (by omega)]`.
-/
theorem blk_two (i : Fin N) : blk (stdBlocks d h) i = if (i : ℕ) < d 0 then 0 else 1 := by
  rcases idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [blk_apply, stdBlocks_zero_val, if_pos a.2]
  · rw [blk_apply, stdBlocks_one_val, if_neg (by omega)]

/- English proof (translation)
Rewrite using `[GlobalTheory.RadRev.mem_unipRad_entries]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[blk_two, blk_two]`. Establish `: ((if (i : ℕ) < d 0 then (0 : Fin 2) else 1) < if (j : ℕ) < d 0 then 0 else 1) ↔ ((i : ℕ) < d 0 ∧ d 0 ≤ (j : ℕ))`. Apply the tactic sequence `by_cases hi : (i : ℕ) < d 0 <;> by_cases hj : (j : ℕ) < d 0 <;> simp [hi, hj] <;> omega`.

Rewrite using `[this]`.
-/
theorem mem_unipRad_iff {g : GL (Fin N) k} :
    g ∈ unipRad k (stdBlocks d h) ↔
      ∀ i j : Fin N, ¬ ((i : ℕ) < d 0 ∧ d 0 ≤ (j : ℕ)) →
        (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [GlobalTheory.RadRev.mem_unipRad_entries]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [blk_two, blk_two]
  have : ((if (i : ℕ) < d 0 then (0 : Fin 2) else 1) < if (j : ℕ) < d 0 then 0 else 1) ↔
      ((i : ℕ) < d 0 ∧ d 0 ≤ (j : ℕ)) := by
    by_cases hi : (i : ℕ) < d 0 <;> by_cases hj : (j : ℕ) < d 0 <;> simp [hi, hj] <;> omega
  rw [this]

/- English proof (translation)
Establish `h1` using `congrFun ((Subgroup.mem_inf.1 hw).2 i hi) r`. Establish `hc : ((w : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (w : Matrix (Fin N) (Fin N) k) r i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite `h1` using `[hc]`. Rewrite using `[h1, Matrix.one_apply, Pi.single_apply]`.
-/
theorem derUnip_col {n : ℕ} {w : GL (Fin N) k} (hw : w ∈ derUnip k N n) (r i : Fin N) (hi : (i : ℕ) < n) :
    (w : Matrix (Fin N) (Fin N) k) r i = (1 : Matrix (Fin N) (Fin N) k) r i := by
  have h1 := congrFun ((Subgroup.mem_inf.1 hw).2 i hi) r
  have hc : ((w : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (w : Matrix (Fin N) (Fin N) k) r i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hc] at h1
  rw [h1, Matrix.one_apply, Pi.single_apply]

/- English proof (translation)
Use `Subgroup.mem_inf.2 ⟨hg, fun i hi => ?_⟩` and prove the remaining obligations. Use extensionality with `r`. Establish `e : ((g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (g : Matrix (Fin N) (Fin N) k) r i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[e, hc r i hi, Matrix.one_apply, Pi.single_apply]`.
-/
theorem mem_derUnip_of_col {n : ℕ} {g : GL (Fin N) k} (hg : g ∈ unipB k (Fin N))
    (hc : ∀ r i : Fin N, (i : ℕ) < n →
      (g : Matrix (Fin N) (Fin N) k) r i = (1 : Matrix (Fin N) (Fin N) k) r i) :
    g ∈ derUnip k N n := by
  refine Subgroup.mem_inf.2 ⟨hg, fun i hi => ?_⟩
  ext r
  have e : ((g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (g : Matrix (Fin N) (Fin N) k) r i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e, hc r i hi, Matrix.one_apply, Pi.single_apply]

/- English proof (translation)
Introduce `g hg`. Establish `hE` using `(mem_unipRad_iff d h).1 hg`. Use `mem_derUnip_of_col ((mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩) fun r i hi => ?_` and prove the remaining obligations. Use `Fin.lt_def.1 hji` as an intermediate fact. Rewrite using `[hE i j (by omega), one_apply_ne (ne_of_gt hji)]`.

Rewrite using `[hE i i (by omega), one_apply_eq]`. Conclude with `hE r i (by omega)`.
-/
theorem unipRad_le_derUnip : unipRad k (stdBlocks d h) ≤ derUnip k N (d 0) := by
  intro g hg
  have hE := (mem_unipRad_iff d h).1 hg
  refine mem_derUnip_of_col ((mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩) fun r i hi => ?_
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]
  · exact hE r i (by omega)

def secEmb : GL (Fin (d 1)) k →* GL (Fin N) k := (leviEmb k (stdBlocks d h)).comp (secondEmb d)

/- English proof (translation)
Simplify using `[secEmb, secondEmb]`.
-/
theorem secEmb_one_one (u : GL (Fin (d 1)) k) (a b : Fin (d 1)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨1, a⟩) (stdBlocks d h ⟨1, b⟩) =
      (u : Matrix (Fin (d 1)) (Fin (d 1)) k) a b := by
  simp [secEmb, secondEmb]

/- English proof (translation)
Simplify using `[secEmb, secondEmb]`.
-/
theorem secEmb_zero_zero (u : GL (Fin (d 1)) k) (a b : Fin (d 0)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨0, a⟩) (stdBlocks d h ⟨0, b⟩) =
      (1 : Matrix (Fin (d 0)) (Fin (d 0)) k) a b := by
  simp [secEmb, secondEmb]

/- English proof (translation)
The claim follows from `leviEmb_apply_ne (m := fun a => Fin (d a)) k (stdBlocks d h) (secondEmb d u) (a := 0) (b := 1) (by decide) a b`.
-/
theorem secEmb_zero_one (u : GL (Fin (d 1)) k) (a : Fin (d 0)) (b : Fin (d 1)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨0, a⟩) (stdBlocks d h ⟨1, b⟩) = 0 :=
  leviEmb_apply_ne (m := fun a => Fin (d a)) k (stdBlocks d h) (secondEmb d u) (a := 0) (b := 1) (by decide) a b

/- English proof (translation)
The claim follows from `leviEmb_apply_ne (m := fun a => Fin (d a)) k (stdBlocks d h) (secondEmb d u) (a := 1) (b := 0) (by decide) a b`.
-/
theorem secEmb_one_zero (u : GL (Fin (d 1)) k) (a : Fin (d 1)) (b : Fin (d 0)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨1, a⟩) (stdBlocks d h ⟨0, b⟩) = 0 :=
  leviEmb_apply_ne (m := fun a => Fin (d a)) k (stdBlocks d h) (secondEmb d u) (a := 1) (b := 0) (by decide) a b

/- English proof (translation)
Take `⟨u1, u2⟩` from `(mem_unipB k).1 hu`. Use `mem_derUnip_of_col ((mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩) fun r i hi => ?_` and prove the remaining obligations. Establish `hlt` using `Fin.lt_def.1 hji`. Apply the tactic sequence `rcases idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases idx_cases d h j with ⟨b, rfl⟩ | ⟨b, rfl⟩`. Rewrite using `[secEmb_zero_zero, one_apply_ne]`.

Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hlt`. Conclude with `secEmb_zero_one d h u a b`. Conclude with `secEmb_one_zero d h u a b`. Rewrite using `[secEmb_one_one]`.

Rewrite `hlt` using `[stdBlocks_one_val, stdBlocks_one_val]`. Conclude with `u1 a b (Fin.lt_def.2 (by omega))`. Break down `idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Rewrite using `[secEmb_zero_zero, one_apply_eq]`. Rewrite using `[secEmb_one_one, u2]`.

Break down `idx_cases d h i with ⟨b, rfl⟩ | ⟨b, rfl⟩` into its components or cases. Break down `idx_cases d h r with ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Rewrite using `[secEmb_zero_zero]`. Distinguish the cases in `e : a = b`. Substitute `e` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[one_apply_ne e, one_apply_ne fun e' => e (by simpa using e')]`. Rewrite using `[secEmb_one_zero, one_apply_ne]`. Introduce `e'`. Establish `h1` using `congrArg Fin.val e'`.

Rewrite `h1` using `[stdBlocks_one_val, stdBlocks_zero_val]`. Use `b.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `hi` using `[stdBlocks_one_val]`. Use linear arithmetic over natural numbers and integers.
-/
theorem secEmb_mem {u : GL (Fin (d 1)) k} (hu : u ∈ unipB k (Fin (d 1))) :
    secEmb d h u ∈ derUnip k N (d 0) := by
  obtain ⟨u1, u2⟩ := (mem_unipB k).1 hu
  refine mem_derUnip_of_col ((mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩) fun r i hi => ?_
  · have hlt := Fin.lt_def.1 hji
    rcases idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases idx_cases d h j with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [secEmb_zero_zero, one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hlt
    · exact secEmb_zero_one d h u a b
    · exact secEmb_one_zero d h u a b
    · rw [secEmb_one_one]
      rw [stdBlocks_one_val, stdBlocks_one_val] at hlt
      exact u1 a b (Fin.lt_def.2 (by omega))
  · rcases idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [secEmb_zero_zero, one_apply_eq]
    · rw [secEmb_one_one, u2]
  · rcases idx_cases d h i with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rcases idx_cases d h r with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [secEmb_zero_zero]
        by_cases e : a = b
        · subst e; simp
        · rw [one_apply_ne e, one_apply_ne fun e' => e (by simpa using e')]
      · rw [secEmb_one_zero, one_apply_ne]
        intro e'
        have h1 := congrArg Fin.val e'
        rw [stdBlocks_one_val, stdBlocks_zero_val] at h1
        have := b.2
        omega
    · rw [stdBlocks_one_val] at hi
      omega

/- English proof (translation)
Take `⟨u1, u2⟩` from `(mem_unipB k).1 hu`. Use `ext`. Rewrite using `[GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular (fun i j hij => u1 i j hij)]`. Simplify using `[u2]`.
-/
theorem det_eq_one {m : ℕ} {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) :
    GeneralLinearGroup.det u = 1 := by
  obtain ⟨u1, u2⟩ := (mem_unipB k).1 hu
  ext
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular (fun i j hij => u1 i j hij)]
  simp [u2]

/- English proof (translation)
Establish `hB` using `(mem_unipB k).1 (derUnip_le_unipB k N (d 0) hw)`. Establish `hp : w ∈ parab k (stdBlocks d h)`. Use `mem_parab.2 fun i j hij => ?_` and prove the remaining obligations. Rewrite `hij` using `[blk_two, blk_two]`. Use `hB.1 i j (Fin.lt_def.2 ?_)` and prove the remaining obligations.

Apply the tactic sequence `by_cases hi : (i : ℕ) < d 0 <;> by_cases hj : (j : ℕ) < d 0 <;> simp [hi, hj] at hij`. Use linear arithmetic over natural numbers and integers. Take `⟨r', hr', e1⟩` from `exists_levi_mul_unip k (stdBlocks d h) ⟨w, hp⟩`. Use `set l := leviProj k (stdBlocks d h) ⟨w, hp⟩ with hl`. Establish `hl0 : l 0 = 1`.

Use extensionality with `i j`. Rewrite using `[hl, leviProj_apply]`. Use `derUnip_col hw (stdBlocks d h ⟨0, i⟩) (stdBlocks d h ⟨0, j⟩) (by rw [stdBlocks_zero_val]; exact j.2)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[Units.val_one]`.

Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[one_apply_ne e, one_apply_ne fun e' => e (by simpa using e')]`. Establish `hlsec : l = secondEmb d (l 1)`.

Establish `key : ∀ a, l a = secondEmb d (l 1) a` using `Fin.forall_fin_two.2 ⟨by simp [secondEmb, hl0], by simp [secondEmb]⟩`. Conclude with `funext key`. Establish `hu : l 1 ∈ unipB k (Fin (d 1))`. Use `(mem_unipB k).2 ⟨fun a c hca => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hl, leviProj_apply]`.

Use `hB.1 _ _ (Fin.lt_def.2 ?_)` and prove the remaining obligations. Rewrite using `[stdBlocks_one_val, stdBlocks_one_val]`. Use `Fin.lt_def.1 hca` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hl, leviProj_apply]`.

Conclude with `hB.2 _`. Establish `hs : secEmb d h (l 1) = leviEmb k (stdBlocks d h) l` using `by show leviEmb k (stdBlocks d h) (secondEmb d (l 1)) = _`. Rewrite using `[← hlsec]`. Establish `e1' : w = leviEmb k (stdBlocks d h) l * r'` using `e1`. Use `⟨leviEmb k (stdBlocks d h) l * r' * (leviEmb k (stdBlocks d h) l)⁻¹, (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (stdBlocks d h) l) r').1 hr', l 1, hu, ?_⟩` and prove the remaining obligations.

Rewrite using `[hs]`. Conclude with `e1'.trans (by group)`.
-/
theorem exists_decomp {w : GL (Fin N) k} (hw : w ∈ derUnip k N (d 0)) :
    ∃ r ∈ unipRad k (stdBlocks d h), ∃ u ∈ unipB k (Fin (d 1)), w = r * secEmb d h u := by
  have hB := (mem_unipB k).1 (derUnip_le_unipB k N (d 0) hw)
  have hp : w ∈ parab k (stdBlocks d h) := by
    refine mem_parab.2 fun i j hij => ?_
    rw [blk_two, blk_two] at hij
    refine hB.1 i j (Fin.lt_def.2 ?_)
    by_cases hi : (i : ℕ) < d 0 <;> by_cases hj : (j : ℕ) < d 0 <;> simp [hi, hj] at hij
    omega
  obtain ⟨r', hr', e1⟩ := exists_levi_mul_unip k (stdBlocks d h) ⟨w, hp⟩
  set l := leviProj k (stdBlocks d h) ⟨w, hp⟩ with hl
  have hl0 : l 0 = 1 := by
    ext i j
    rw [hl, leviProj_apply]
    have := derUnip_col hw (stdBlocks d h ⟨0, i⟩) (stdBlocks d h ⟨0, j⟩)
      (by rw [stdBlocks_zero_val]; exact j.2)
    refine this.trans ?_
    rw [Units.val_one]
    by_cases e : i = j
    · subst e; simp
    · rw [one_apply_ne e, one_apply_ne fun e' => e (by simpa using e')]
  have hlsec : l = secondEmb d (l 1) := by
    have key : ∀ a, l a = secondEmb d (l 1) a :=
      Fin.forall_fin_two.2 ⟨by simp [secondEmb, hl0], by simp [secondEmb]⟩
    exact funext key
  have hu : l 1 ∈ unipB k (Fin (d 1)) := by
    refine (mem_unipB k).2 ⟨fun a c hca => ?_, fun a => ?_⟩
    · rw [hl, leviProj_apply]
      refine hB.1 _ _ (Fin.lt_def.2 ?_)
      rw [stdBlocks_one_val, stdBlocks_one_val]
      have := Fin.lt_def.1 hca
      omega
    · rw [hl, leviProj_apply]
      exact hB.2 _
  have hs : secEmb d h (l 1) = leviEmb k (stdBlocks d h) l := by
    show leviEmb k (stdBlocks d h) (secondEmb d (l 1)) = _
    rw [← hlsec]
  have e1' : w = leviEmb k (stdBlocks d h) l * r' := e1
  refine ⟨leviEmb k (stdBlocks d h) l * r' * (leviEmb k (stdBlocks d h) l)⁻¹,
    (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (stdBlocks d h) l) r').1 hr', l 1, hu, ?_⟩
  rw [hs]
  exact e1'.trans (by group)

end Groups

section Chars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} (d : Fin 2 → ℕ) (h : ∑ a, d a = N)

/- English proof (translation)
Establish `hE` using `(mem_unipRad_iff d h).1 hu`. Use `show Circle.toUnits _ = 1`. Rewrite using `[Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]`. Introduce `p hp`. Take `⟨h1, h2⟩` from `(Finset.mem_filter.1 hp).2`.

Use `(hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)` and prove the remaining obligations. Rewrite `h1` using `[e]`. Use linear arithmetic over natural numbers and integers.
-/
theorem derChar_eq_one_of_mem_unipRad (ψ : AddChar k Circle) (u : derUnip k N (d 0))
    (hu : (u : GL (Fin N) k) ∈ unipRad k (stdBlocks d h)) : derChar k ψ N (d 0) u = 1 := by
  have hE := (mem_unipRad_iff d h).1 hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

/- English proof (translation)
Use `show Circle.toUnits _ = Circle.toUnits _`. Use `congrArg _ (congrArg _ ?_)` and prove the remaining obligations. Use `symm`. Use `Finset.sum_bij (fun q _ => (stdBlocks d h ⟨1, q.1⟩, stdBlocks d h ⟨1, q.2⟩)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `q hq`.

Use `(Finset.mem_filter.1 hq).2` as an intermediate fact. Use `Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [stdBlocks_one_val]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [stdBlocks_one_val]`.

Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨a, b⟩ _ ⟨a', b'⟩ _ e`. Establish `e1` using `(stdBlocks d h).injective (congrArg Prod.fst e)`. Establish `e2` using `(stdBlocks d h).injective (congrArg Prod.snd e)`. Simplify using `only [Sigma.mk.injEq, heq_eq_eq, true_and] at e1 e2`.

Simplify using `[e1, e2]`. Introduce and unpack `⟨p1, p2⟩ hp`. Take `⟨h1, h2⟩` from `(Finset.mem_filter.1 hp).2`. Simplify using `only at h1 h2`. Break down `idx_cases d h p1 with ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases.

Rewrite `h2` using `[stdBlocks_zero_val]`. Use `a.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Break down `idx_cases d h p2 with ⟨b, rfl⟩ | ⟨b, rfl⟩` into its components or cases. Rewrite `h1` using `[stdBlocks_zero_val, stdBlocks_one_val]`.

Use `b.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite `h1` using `[stdBlocks_one_val, stdBlocks_one_val]`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. Introduce `q _`. Conclude with `(secEmb_one_one d h _ q.1 q.2).symm`.
-/
theorem derChar_secEmb (ψ : AddChar k Circle) (u : unipB k (Fin (d 1)))
    (hs : secEmb d h (u : GL (Fin (d 1)) k) ∈ derUnip k N (d 0)) :
    derChar k ψ N (d 0) ⟨_, hs⟩ = whitChar ψ (d 1) u := by
  show Circle.toUnits _ = Circle.toUnits _
  refine congrArg _ (congrArg _ ?_)
  symm
  refine Finset.sum_bij (fun q _ => (stdBlocks d h ⟨1, q.1⟩, stdBlocks d h ⟨1, q.2⟩)) ?_ ?_ ?_ ?_
  · intro q hq
    have := (Finset.mem_filter.1 hq).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · simp only [stdBlocks_one_val]
      omega
    · simp only [stdBlocks_one_val]
      omega
  · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ e
    have e1 := (stdBlocks d h).injective (congrArg Prod.fst e)
    have e2 := (stdBlocks d h).injective (congrArg Prod.snd e)
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at e1 e2
    simp [e1, e2]
  · rintro ⟨p1, p2⟩ hp
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    simp only at h1 h2
    rcases idx_cases d h p1 with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [stdBlocks_zero_val] at h2
      have := a.2
      omega
    rcases idx_cases d h p2 with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [stdBlocks_zero_val, stdBlocks_one_val] at h1
      have := b.2
      omega
    refine ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rw [stdBlocks_one_val, stdBlocks_one_val] at h1
    simp only
    omega
  · intro q _
    exact (secEmb_one_one d h _ q.1 q.2).symm

/- English proof (translation)
Rewrite using `[deltaHalf_apply]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Establish `key : ∀ a, GeneralLinearGroup.det ((secondEmb d u : Levi k fun a => Fin (d a)) a) = 1` using `Fin.forall_fin_two.2 ⟨by simp [secondEmb], by simpa [secondEmb] using det_eq_one hu⟩`. Rewrite using `[key, map_one]`.
-/
theorem deltaHalf_secondEmb {u : GL (Fin (d 1)) k} (hu : u ∈ unipB k (Fin (d 1))) :
    deltaHalf k (fun a => Fin (d a)) (secondEmb d u) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have key : ∀ a, GeneralLinearGroup.det ((secondEmb d u : Levi k fun a => Fin (d a)) a) = 1 :=
    Fin.forall_fin_two.2 ⟨by simp [secondEmb], by simpa [secondEmb] using det_eq_one hu⟩
  rw [key, map_one]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, v, rfl⟩`. Use `⟨⟨u, unipRad_le_derUnip d h u.2⟩, v, ?_⟩` and prove the remaining obligations. Rewrite using `[derChar_eq_one_of_mem_unipRad d h ψ _ u.2]`. Simplify using the standard rewrite rules.
-/
theorem twKer_unipRad_le (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (unipRad k (stdBlocks d h)) 1 ≤ twKer π (derUnip k N (d 0)) (derChar k ψ N (d 0)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨u, v, rfl⟩
  refine ⟨⟨u, unipRad_le_derUnip d h u.2⟩, v, ?_⟩
  rw [derChar_eq_one_of_mem_unipRad d h ψ _ u.2]
  simp

/- English proof (translation)
Rewrite using `[jac_mk, deltaHalf_secondEmb d hu]`. Simplify using `[secEmb]`.
-/
theorem jac_secondEmb (π : Representation ℂ (GL (Fin N) k) V) {u : GL (Fin (d 1)) k}
    (hu : u ∈ unipB k (Fin (d 1))) (v : V) :
    jac (stdBlocks d h) π (secondEmb d u) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (π (secEmb d h u) v) := by
  rw [jac_mk, deltaHalf_secondEmb d hu]
  simp [secEmb]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, x, rfl⟩`. Take `⟨v, rfl⟩` from `Submodule.mkQ_surjective _ x`. Establish `hs` using `secEmb_mem d h u.2`.

Use `⟨π (secEmb d h u) v - (whitChar ψ (d 1) u : ℂ) • v, Submodule.subset_span ⟨⟨_, hs⟩, v, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[derChar_secEmb d h ψ u hs]`. Rewrite using `[map_sub, map_smul]`. Conclude with `congrArg₂ _ (jac_secondEmb d h π u.2 v).symm rfl`. Use `Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨⟨w, hw⟩, v, rfl⟩`. Take `⟨r, hr, u, hu, rfl⟩` from `exists_decomp d h hw`. Establish `hs` using `secEmb_mem d h hu`. Establish `hc : derChar k ψ N (d 0) ⟨_, hw⟩ = whitChar ψ (d 1) ⟨u, hu⟩`. Establish `e : (⟨_, hw⟩ : derUnip k N (d 0)) = ⟨r, unipRad_le_derUnip d h hr⟩ * ⟨_, hs⟩` using `rfl`.

Rewrite using `[e, map_mul, derChar_eq_one_of_mem_unipRad d h ψ _ hr, one_mul]`. Conclude with `derChar_secEmb d h ψ ⟨u, hu⟩ hs`. Establish `hr' : Submodule.mkQ (twKer π (unipRad k (stdBlocks d h)) 1) (π (r * secEmb d h u) v) = Submodule.Quotient.mk (π (secEmb d h u) v)`. Use `(Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨r, hr⟩, π (secEmb d h u) v, ?_⟩)` and prove the remaining obligations. Simplify using the standard rewrite rules.

Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Rewrite using `[hc, map_sub, map_smul, hr', ← jac_secondEmb d h π hu v]`. Conclude with `Submodule.subset_span ⟨⟨u, hu⟩, Submodule.Quotient.mk v, rfl⟩`.
-/
theorem whitKer_jac_eq_map (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    whitKer ψ d (jac (stdBlocks d h) π) =
      (twKer π (derUnip k N (d 0)) (derChar k ψ N (d 0))).map
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks d h)) 1)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, x, rfl⟩
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ x
    have hs := secEmb_mem d h u.2
    refine ⟨π (secEmb d h u) v - (whitChar ψ (d 1) u : ℂ) • v,
      Submodule.subset_span ⟨⟨_, hs⟩, v, ?_⟩, ?_⟩
    · rw [derChar_secEmb d h ψ u hs]
    · rw [map_sub, map_smul]
      exact congrArg₂ _ (jac_secondEmb d h π u.2 v).symm rfl
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨⟨w, hw⟩, v, rfl⟩
    obtain ⟨r, hr, u, hu, rfl⟩ := exists_decomp d h hw
    have hs := secEmb_mem d h hu
    have hc : derChar k ψ N (d 0) ⟨_, hw⟩ = whitChar ψ (d 1) ⟨u, hu⟩ := by
      have e : (⟨_, hw⟩ : derUnip k N (d 0)) = ⟨r, unipRad_le_derUnip d h hr⟩ * ⟨_, hs⟩ := rfl
      rw [e, map_mul, derChar_eq_one_of_mem_unipRad d h ψ _ hr, one_mul]
      exact derChar_secEmb d h ψ ⟨u, hu⟩ hs
    have hr' : Submodule.mkQ (twKer π (unipRad k (stdBlocks d h)) 1) (π (r * secEmb d h u) v) =
        Submodule.Quotient.mk (π (secEmb d h u) v) := by
      refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨r, hr⟩, π (secEmb d h u) v, ?_⟩)
      simp
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rw [hc, map_sub, map_smul, hr', ← jac_secondEmb d h π hu v]
    exact Submodule.subset_span ⟨⟨u, hu⟩, Submodule.Quotient.mk v, rfl⟩

/- English proof (translation)
Rewrite using `[whitKer_jac_eq_map, Submodule.comap_map_eq, Submodule.ker_mkQ]`. Conclude with `sup_eq_left.2 (twKer_unipRad_le d h ψ π)`.
-/
theorem comap_whitKer_jac (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    (whitKer ψ d (jac (stdBlocks d h) π)).comap
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks d h)) 1)) =
      twKer π (derUnip k N (d 0)) (derChar k ψ N (d 0)) := by
  rw [whitKer_jac_eq_map, Submodule.comap_map_eq, Submodule.ker_mkQ]
  exact sup_eq_left.2 (twKer_unipRad_le d h ψ π)

end Chars

/- English proof (translation)
Introduce `_ _ _ _ _ ψ _ _ _ _ _ π hd` and use `comap_whitKer_jac _ hd ψ π`.
-/
theorem whitKer_jac_comap_eq_twKer_derUnip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1),
    (whitKer ψ ![n, j + 1] (jac (stdBlocks ![n, j + 1] hd) π)).comap
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks ![n, j + 1] hd)) 1)) =
      twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) :=
  fun _ _ _ _ _ ψ _ _ _ _ _ π hd => comap_whitKer_jac _ hd ψ π

end GlobalTheory.CompanionTheory.BZNuPair.DerComap

end

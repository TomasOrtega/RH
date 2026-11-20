import Mathlib

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrA

variable {K : Type*} [Field K] {d : ℕ}

def PiLocalization₂ (G : ℤ → Submodule K (Fin d → K)) (hi u : ℤ) : Prop :=
  ∃ (S : Set (Fin d → K)) (ℓ : (Fin d → K) → ℤ), LinearIndepOn K id S ∧
    (∀ x ∈ S, x ∈ G (ℓ x) ∧ u ≤ ℓ x ∧ ℓ x ≤ hi) ∧ S ⊆ G u ∧
    ∀ u', u ≤ u' → u' ≤ hi → G u' ≤ Submodule.span K {x | x ∈ S ∧ u' ≤ ℓ x}

/- English proof (translation)
Unfold `PiLocalization₂`. Take `⟨b, hbt, hspan, hli⟩` from `exists_linearIndependent K (G hi : Set (Fin d → K))`. Use `⟨b, fun _ => hi, hli, fun x hx => ⟨hbt hx, le_rfl, le_rfl⟩, hbt, ?_⟩` and prove the remaining obligations. Introduce `u' h1 h2 v hv`. Establish `hsub : b ⊆ {x | x ∈ b ∧ u' ≤ (fun _ => hi) x}` using `fun x hx => ⟨hx, h2⟩`.

Use `Submodule.span_mono hsub ?_` and prove the remaining obligations. Rewrite using `[hspan, Submodule.span_eq]`. Rewrite using `[← le_antisymm h2 h1]` and apply the resulting hypothesis.
-/
theorem stage_top (G : ℤ → Submodule K (Fin d → K)) (hi : ℤ) : PiLocalization₂ G hi hi := by
  unfold PiLocalization₂
  obtain ⟨b, hbt, hspan, hli⟩ := exists_linearIndependent K (G hi : Set (Fin d → K))
  refine ⟨b, fun _ => hi, hli, fun x hx => ⟨hbt hx, le_rfl, le_rfl⟩, hbt, ?_⟩
  intro u' h1 h2 v hv
  have hsub : b ⊆ {x | x ∈ b ∧ u' ≤ (fun _ => hi) x} := fun x hx => ⟨hx, h2⟩
  refine Submodule.span_mono hsub ?_
  rw [hspan, Submodule.span_eq]
  rwa [← le_antisymm h2 h1]

/- English proof (translation)
Unfold `PiLocalization₂ at h ⊢`. Take `⟨S, ℓ, hli, hmem, hSG, hspan⟩` from `h`. Establish `hSu : S ⊆ (G u : Set (Fin d → K))` using `fun x hx => hG (by omega : u ≤ u + 1) (hSG hx)`. Take `⟨b, hbt, hSb, htb, hlib⟩` from `exists_linearIndepOn_id_extension hli hSu`. Use `⟨b, fun x => if x ∈ S then ℓ x else u, hlib, ?_, hbt, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Distinguish the cases in `hxS : x ∈ S`. Take `⟨h1, h2, h3⟩` from `hmem x hxS`. Simplify using `only [hxS, if_true]`. Conclude with `⟨h1, by omega, h3⟩`.

Simplify using `only [hxS, if_false]`. Conclude with `⟨hbt hx, le_rfl, hu.le⟩`. Introduce `u' h1 h2`. Break down `eq_or_lt_of_le h1 with rfl | hlt` into its components or cases. Introduce `v hv`.

Establish `hsub : b ⊆ {x | x ∈ b ∧ u ≤ (fun x => if x ∈ S then ℓ x else u) x}`. Introduce `x hx`. Use `⟨hx, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hxS : x ∈ S`. Establish `h3` using `(hmem x hxS).2.1`.

Simplify using `only [hxS, if_true]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [hxS, if_false]`. Conclude with `le_rfl`. Conclude with `Submodule.span_mono hsub (htb hv)`.

Use `(hspan u' (by omega) h2).trans (Submodule.span_mono ?_)` and prove the remaining obligations. Introduce and unpack `x ⟨hxS, hx⟩`. Conclude with `⟨hSb hxS, by simpa [hxS] using hx⟩`.
-/
theorem stage_step (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (hi u : ℤ) (hu : u < hi)
    (h : PiLocalization₂ G hi (u + 1)) : PiLocalization₂ G hi u := by
  unfold PiLocalization₂ at h ⊢
  obtain ⟨S, ℓ, hli, hmem, hSG, hspan⟩ := h
  have hSu : S ⊆ (G u : Set (Fin d → K)) := fun x hx => hG (by omega : u ≤ u + 1) (hSG hx)
  obtain ⟨b, hbt, hSb, htb, hlib⟩ := exists_linearIndepOn_id_extension hli hSu
  refine ⟨b, fun x => if x ∈ S then ℓ x else u, hlib, ?_, hbt, ?_⟩
  · intro x hx
    by_cases hxS : x ∈ S
    · obtain ⟨h1, h2, h3⟩ := hmem x hxS
      simp only [hxS, if_true]
      exact ⟨h1, by omega, h3⟩
    · simp only [hxS, if_false]
      exact ⟨hbt hx, le_rfl, hu.le⟩
  · intro u' h1 h2
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · intro v hv
      have hsub : b ⊆ {x | x ∈ b ∧ u ≤ (fun x => if x ∈ S then ℓ x else u) x} := by
        intro x hx
        refine ⟨hx, ?_⟩
        by_cases hxS : x ∈ S
        · have h3 := (hmem x hxS).2.1
          simp only [hxS, if_true]
          omega
        · simp only [hxS, if_false]
          exact le_rfl
      exact Submodule.span_mono hsub (htb hv)
    · refine (hspan u' (by omega) h2).trans (Submodule.span_mono ?_)
      rintro x ⟨hxS, hx⟩
      exact ⟨hSb hxS, by simpa [hxS] using hx⟩

/- English proof (translation)
Establish `key : ∀ k : ℕ, PiLocalization₂ G hi (hi - k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using stage_top G hi`. Consider the case `succ k ih`.

Use `stage_step G hG hi (hi - ((k + 1 : ℕ) : ℤ)) (by push_cast; omega) ?_` and prove the remaining obligations. Establish `e : hi - ((k + 1 : ℕ) : ℤ) + 1 = hi - (k : ℤ)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `ih`. Introduce `u hu`.

Establish `h` using `key (hi - u).toNat`. Rewrite `h` using `[Int.toNat_of_nonneg (by omega), sub_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem stage_all (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (hi : ℤ) :
    ∀ u ≤ hi, PiLocalization₂ G hi u := by
  have key : ∀ k : ℕ, PiLocalization₂ G hi (hi - k) := by
    intro k
    induction k with
    | zero => simpa using stage_top G hi
    | succ k ih =>
      refine stage_step G hG hi (hi - ((k + 1 : ℕ) : ℤ)) (by push_cast; omega) ?_
      have e : hi - ((k + 1 : ℕ) : ℤ) + 1 = hi - (k : ℤ) := by push_cast; ring
      rw [e]
      exact ih
  intro u hu
  have h := key (hi - u).toNat
  rwa [Int.toNat_of_nonneg (by omega), sub_sub_cancel] at h

/- English proof (translation)
Take `⟨S, ℓ, hli, hmem, _, hspan⟩` from `stage_all G hG hi lo hlh`. Establish `hfin : S.Finite` using `LinearIndependent.set_finite_of_isNoetherian hli`. Use `hfin.fintype` as an intermediate fact. Establish `hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : S → Fin d → K))`. Rewrite using `[Subtype.range_coe, ← hlo]`.

Conclude with `(hspan lo le_rfl hlh).trans (Submodule.span_mono fun x hx => hx.1)`. Set `B0 : Module.Basis S K (Fin d → K)` to `Module.Basis.mk (v := ((↑) : S → Fin d → K)) hli hsp`. Set `e` to `Fintype.equivFin S`. Set `B` to `B0.reindex e`. Establish `hB : ∀ i, B i = ((e.symm i : S) : Fin d → K)` using `fun i => by`.

Simplify using `only [B, B0, Module.Basis.reindex_apply]`. Conclude with `Module.Basis.mk_apply hli hsp (e.symm i)`. Establish `hQ : ∀ (c : Fin d → K) i, ∑ m, B.repr (Pi.single m 1) i * c m = B.repr c i`. Introduce `c i`. Use `conv_rhs => rw [← Finset.univ_sum_single c]`.

Rewrite using `[map_sum, Finsupp.finsetSum_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `hs : (Pi.single m (c m) : Fin d → K) = c m • Pi.single m 1`. Use extensionality with `j`. Distinguish the cases in `hj : j = m`.

Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`. Rewrite using `[hs, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]`. Use `⟨Fintype.card S, fun i => B i, fun i m => B.repr (Pi.single m 1) i, fun i => ℓ (B i), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `c`. Simplify using `only [hQ]`. Conclude with `(B.sum_repr c).symm`. Introduce `i show B i ∈ G (ℓ (B i))`. Rewrite using `[hB]`.

Conclude with `(hmem _ (e.symm i).2).1`. Introduce `i show lo ≤ ℓ (B i) ∧ ℓ (B i) ≤ hi`. Rewrite using `[hB]`. Take `⟨_, h1, h2⟩` from `hmem _ (e.symm i).2`. Conclude with `⟨h1, h2⟩`.

Introduce `u hu c hc i hi'`. Establish `hi'' : ℓ (B i) < u` using `hi'`. Use `show ∑ m, B.repr (Pi.single m 1) i * c m = 0`. Rewrite using `[hQ]`. Distinguish the cases in `hul : u ≤ lo`.

It suffices to derive a contradiction. Establish `h1` using `(hmem _ (e.symm i).2).2.1`. Rewrite `hi''` using `[hB]`. Use linear arithmetic over natural numbers and integers. Establish `hcs` using `hspan u (by omega) hu hc`.

Establish `hset : {x | x ∈ S ∧ u ≤ ℓ x} = B '' {j | u ≤ ℓ (B j)}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxS, hx⟩`. Use `⟨e ⟨x, hxS⟩, ?_, ?_⟩` and prove the remaining obligations.

Use `show u ≤ ℓ (B (e ⟨x, hxS⟩))`. Rewrite using `[hB, Equiv.symm_apply_apply]`. Conclude with `hx`. Rewrite using `[hB, Equiv.symm_apply_apply]`. Introduce and unpack `⟨j, hj, rfl⟩`.

Conclude with `⟨by rw [hB]; exact (e.symm j).2, hj⟩`. Rewrite `hcs` using `[hset, Module.Basis.mem_span_image]`. Assume the negation of the conclusion as `hne`. Establish `hmemi` using `hcs (Finsupp.mem_support_iff.2 hne)`. Conclude with `absurd (show u ≤ ℓ (B i) from hmemi) (not_le.2 hi'')`.
-/
theorem adapted (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (lo hi : ℤ) (hlh : lo ≤ hi)
    (hlo : G lo = ⊤) :
    ∃ (I : ℕ) (P : Fin I → Fin d → K) (Q : Fin I → Fin d → K) (h : Fin I → ℤ),
      (∀ c : Fin d → K, c = ∑ i, (∑ m, Q i m * c m) • P i) ∧
      (∀ i, P i ∈ G (h i)) ∧ (∀ i, lo ≤ h i ∧ h i ≤ hi) ∧
      ∀ u : ℤ, u ≤ hi → ∀ c ∈ G u, ∀ i, h i < u → ∑ m, Q i m * c m = 0 := by
  obtain ⟨S, ℓ, hli, hmem, _, hspan⟩ := stage_all G hG hi lo hlh
  have hfin : S.Finite := LinearIndependent.set_finite_of_isNoetherian hli
  have := hfin.fintype
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : S → Fin d → K)) := by
    rw [Subtype.range_coe, ← hlo]
    exact (hspan lo le_rfl hlh).trans (Submodule.span_mono fun x hx => hx.1)
  let B0 : Module.Basis S K (Fin d → K) := Module.Basis.mk (v := ((↑) : S → Fin d → K)) hli hsp
  let e := Fintype.equivFin S
  let B := B0.reindex e
  have hB : ∀ i, B i = ((e.symm i : S) : Fin d → K) := fun i => by
    simp only [B, B0, Module.Basis.reindex_apply]
    exact Module.Basis.mk_apply hli hsp (e.symm i)
  have hQ : ∀ (c : Fin d → K) i, ∑ m, B.repr (Pi.single m 1) i * c m = B.repr c i := by
    intro c i
    conv_rhs => rw [← Finset.univ_sum_single c]
    rw [map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hs : (Pi.single m (c m) : Fin d → K) = c m • Pi.single m 1 := by
      ext j
      by_cases hj : j = m
      · subst hj
        simp
      · simp [hj]
    rw [hs, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨Fintype.card S, fun i => B i, fun i m => B.repr (Pi.single m 1) i, fun i => ℓ (B i),
    ?_, ?_, ?_, ?_⟩
  · intro c
    simp only [hQ]
    exact (B.sum_repr c).symm
  · intro i
    show B i ∈ G (ℓ (B i))
    rw [hB]
    exact (hmem _ (e.symm i).2).1
  · intro i
    show lo ≤ ℓ (B i) ∧ ℓ (B i) ≤ hi
    rw [hB]
    obtain ⟨_, h1, h2⟩ := hmem _ (e.symm i).2
    exact ⟨h1, h2⟩
  · intro u hu c hc i hi'
    have hi'' : ℓ (B i) < u := hi'
    show ∑ m, B.repr (Pi.single m 1) i * c m = 0
    rw [hQ]
    by_cases hul : u ≤ lo
    · exfalso
      have h1 := (hmem _ (e.symm i).2).2.1
      rw [hB] at hi''
      omega
    · have hcs := hspan u (by omega) hu hc
      have hset : {x | x ∈ S ∧ u ≤ ℓ x} = B '' {j | u ≤ ℓ (B j)} := by
        ext x
        constructor
        · rintro ⟨hxS, hx⟩
          refine ⟨e ⟨x, hxS⟩, ?_, ?_⟩
          · show u ≤ ℓ (B (e ⟨x, hxS⟩))
            rw [hB, Equiv.symm_apply_apply]
            exact hx
          · rw [hB, Equiv.symm_apply_apply]
        · rintro ⟨j, hj, rfl⟩
          exact ⟨by rw [hB]; exact (e.symm j).2, hj⟩
      rw [hset, Module.Basis.mem_span_image] at hcs
      by_contra hne
      have hmemi := hcs (Finsupp.mem_support_iff.2 hne)
      exact absurd (show u ≤ ℓ (B i) from hmemi) (not_le.2 hi'')

end Formalism.MainNotions.UnusedSlot80.CrA

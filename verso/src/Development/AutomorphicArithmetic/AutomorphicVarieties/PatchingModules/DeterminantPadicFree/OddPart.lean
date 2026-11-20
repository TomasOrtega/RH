import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.BlockPrinc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.RelPair

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Simplify using `only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul, Matrix.add_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib, mul_add]`. Rewrite using `[Finset.sum_comm (s := c.support) (f := fun x k => c x * (α k * (κ k x * r x) i j)), Finset.sum_comm (s := c.support) (f := fun x k => c x * (β k * (la k x * r x) i j))]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
private theorem comb_entry {F G : Type} [Field F] {n m : ℕ} (r : G → Matrix (Fin n) (Fin n) F)
    (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (α β : Fin m → F) (c : G →₀ F) (i j : Fin n) :
    (c.sum fun g x => x • ((∑ k, α k • κ k g + ∑ k, β k • la k g) * r g)) i j =
      ∑ k, ((c.sum fun g x => x • (κ k g * r g)) i j * α k + (c.sum fun g x => x • (la k g * r g)) i j * β k) := by
  simp only [Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_mul, Matrix.sum_mul,
    Matrix.smul_mul, Matrix.add_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_comm (s := c.support) (f := fun x k => c x * (α k * (κ k x * r x) i j)),
    Finset.sum_comm (s := c.support) (f := fun x k => c x * (β k * (la k x * r x) i j))]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Introduce `F G _ _ n D m κ la s ph hK hT k`. Distinguish the cases in `ha : D.a < n`. Establish `hpos` using `D.a_pos`. Set `i : Fin n` to `⟨0, by omega⟩`. Set `j : Fin n` to `⟨D.a, ha⟩`.

Establish `hij : ¬((i : ℕ) < D.a ↔ (j : ℕ) < D.a)`. Introduce `h`. Conclude with `lt_irrefl D.a (h.mp (show (0 : ℕ) < D.a by omega))`. Establish `hji : ¬((j : ℕ) < D.a ↔ (i : ℕ) < D.a)` using `fun h => hij h.symm`. Establish `step1 : ∀ c' : G →₀ F, (∀ g ∈ c'.support, g ∈ D.G') → (c'.sum fun g x => x • D.r g) = 0 → ∀ k', (c'.sum fun g x => x • (la k' g * D.r g)) j i = 0`.

Introduce `c' hc' hr'`. Establish `hkill : D.KillsRel (fun g => ∑ q, (fun q => (c'.sum fun g x => x • (la q g * D.r g)) j i) q • κ q g + ∑ q, (fun q => (c'.sum fun g x => x • (κ q g * D.r g)) j i) q • la q g) i j`. Introduce `c hc hr`. Use `show (c.sum fun g x => x • ((∑ q, (fun q => (c'.sum fun g x => x • (la q g * D.r g)) j i) q • κ q g + ∑ q, (fun q => (c'.sum fun g x => x • (κ q g * D.r g)) j i) q • la q g) * D.r g)) i j = 0`. Rewrite using `[comb_entry]`.

Conclude with `Det.relPair D κ la s ph hK hT c c' hc hc' hr hr' i j hij`. Establish `h` using `(Det.ann D κ la s ph hK hT _ _ i j hij hkill).1`. Introduce `k'`. Conclude with `congrFun h k'`. Establish `hkill2 : D.KillsRel (fun g => ∑ q, (0 : Fin m → F) q • κ q g + ∑ q, (Pi.single k (1 : F) : Fin m → F) q • la q g) j i`.

Introduce `c hc hr`. Use `show (c.sum fun g x => x • ((∑ q, (0 : Fin m → F) q • κ q g + ∑ q, (Pi.single k (1 : F) : Fin m → F) q • la q g) * D.r g)) j i = 0`. Rewrite using `[comb_entry]`. Simplify using `[step1 c hc hr]`. Take `⟨_, Y, hY, hs, hg⟩` from `Det.ann D κ la s ph hK hT 0 (Pi.single k 1) j i hji hkill2`.

Use `⟨Y, hY, hs, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← hg g]`. Simplify using `[Pi.single_apply]`. Establish `han : D.a = n` using `le_antisymm D.a_le (not_lt.mp ha)`. Use `⟨0, Submodule.zero_mem _, by simp, fun g => ?_⟩` and prove the remaining obligations.

Establish `h0 : la k g = 0`. Use extensionality with `i j`. Establish `hm` using `(hT.od k g i j).1 (by rw [han]; exact iff_of_true i.2 j.2)`. Conclude with `(Submodule.mem_bot F).mp hm`. Rewrite using `[h0]`.

Simplify using `[dTw]`.
-/
theorem UpperTheory.V.Pa.Det.oddPart :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∀ k, ∃ Y ∈ Od F F n D.a, s • Yᵀ = Y ∧ ∀ g, la k g = dTw D.χF D.r Y g := by
  intro F G _ _ n D m κ la s ph hK hT k
  classical
  by_cases ha : D.a < n
  · have hpos := D.a_pos
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨D.a, ha⟩
    have hij : ¬((i : ℕ) < D.a ↔ (j : ℕ) < D.a) := by
      intro h
      exact lt_irrefl D.a (h.mp (show (0 : ℕ) < D.a by omega))
    have hji : ¬((j : ℕ) < D.a ↔ (i : ℕ) < D.a) := fun h => hij h.symm
    have step1 : ∀ c' : G →₀ F, (∀ g ∈ c'.support, g ∈ D.G') → (c'.sum fun g x => x • D.r g) = 0 →
        ∀ k', (c'.sum fun g x => x • (la k' g * D.r g)) j i = 0 := by
      intro c' hc' hr'
      have hkill : D.KillsRel (fun g => ∑ q, (fun q => (c'.sum fun g x => x • (la q g * D.r g)) j i) q • κ q g
          + ∑ q, (fun q => (c'.sum fun g x => x • (κ q g * D.r g)) j i) q • la q g) i j := by
        intro c hc hr
        show (c.sum fun g x => x • ((∑ q, (fun q => (c'.sum fun g x => x • (la q g * D.r g)) j i) q • κ q g
          + ∑ q, (fun q => (c'.sum fun g x => x • (κ q g * D.r g)) j i) q • la q g) * D.r g)) i j = 0
        rw [comb_entry]
        exact Det.relPair D κ la s ph hK hT c c' hc hc' hr hr' i j hij
      have h := (Det.ann D κ la s ph hK hT _ _ i j hij hkill).1
      intro k'
      exact congrFun h k'
    have hkill2 : D.KillsRel (fun g => ∑ q, (0 : Fin m → F) q • κ q g
        + ∑ q, (Pi.single k (1 : F) : Fin m → F) q • la q g) j i := by
      intro c hc hr
      show (c.sum fun g x => x • ((∑ q, (0 : Fin m → F) q • κ q g
        + ∑ q, (Pi.single k (1 : F) : Fin m → F) q • la q g) * D.r g)) j i = 0
      rw [comb_entry]
      simp [step1 c hc hr]
    obtain ⟨_, Y, hY, hs, hg⟩ := Det.ann D κ la s ph hK hT 0 (Pi.single k 1) j i hji hkill2
    refine ⟨Y, hY, hs, fun g => ?_⟩
    rw [← hg g]
    simp [Pi.single_apply]
  · have han : D.a = n := le_antisymm D.a_le (not_lt.mp ha)
    refine ⟨0, Submodule.zero_mem _, by simp, fun g => ?_⟩
    have h0 : la k g = 0 := by
      ext i j
      have hm := (hT.od k g i j).1 (by rw [han]; exact iff_of_true i.2 j.2)
      exact (Submodule.mem_bot F).mp hm
    rw [h0]
    simp [dTw]

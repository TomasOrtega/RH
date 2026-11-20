import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.HT.CoA

open Pb

variable {K B E : Type} [Field K] [CommRing B] [Algebra K B] [CommRing E] (θ : B →+* E)

def one {N : Type} [AddCommGroup N] [Module K N] {M H : Type 1} [AddCommGroup M] [Module K M] [AddCommGroup H] [Module K H]
    (lam : N →+ E) (hl : ∀ (k : K) n, lam (k • n) = θ (algebraMap K B k) * lam n) (e : H ≃ₗ[K] M) :
    N ⊗[K] M →+ (Module.Dual K H →+ E) :=
  TensorProduct.liftAddHom
    { toFun := fun n =>
        { toFun := fun x =>
            { toFun := fun φ => lam n * θ (algebraMap K B (φ (e.symm x)))
              map_zero' := by simp
              map_add' := fun _ _ => by simp [mul_add] }
          map_zero' := by ext; simp
          map_add' := fun _ _ => by ext; simp [mul_add] }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    (fun k n x => by
      ext φ
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, hl, map_smul, smul_eq_mul, map_mul]
      ring)

/- English proof (translation)
Unfold `one`. Rewrite using `[TensorProduct.liftAddHom_tmul]`. Simplify using the standard rewrite rules.
-/
theorem one_tmul {N : Type} [AddCommGroup N] [Module K N] {M H : Type 1} [AddCommGroup M] [Module K M] [AddCommGroup H] [Module K H]
    (lam : N →+ E) (hl : ∀ (k : K) n, lam (k • n) = θ (algebraMap K B k) * lam n) (e : H ≃ₗ[K] M) (n : N) (y : H)
    (φ : Module.Dual K H) : one θ lam hl e (n ⊗ₜ e y) φ = lam n * θ (algebraMap K B (φ y)) := by
  unfold one
  rw [TensorProduct.liftAddHom_tmul]
  simp

/- English proof (translation)
Take `⟨g, hg⟩` from `hT`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `P h0 hadd hgen w`. Establish `key : ∀ (i : Fin m) (t : N i ⊗[K] M i), P (g (Pi.single i t))`. Introduce `i t`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rw [Pi.single_zero, map_zero]`. Conclude with `h0`. Consider the case `tmul n x`. Distinguish the cases in `hi : r < (i : ℕ)`.

Use `hz i hi` as an intermediate fact. Rewrite using `[Subsingleton.elim x 0, TensorProduct.tmul_zero, Pi.single_zero, map_zero]`. Conclude with `h0`. Take `⟨a, ha, rfl⟩ : ∃ a, ∃ ha : a ≤ r, i = ⟨r - a, Nat.lt_of_le_of_lt (Nat.sub_le r a) hr⟩` from `⟨r - (i : ℕ), by omega, Fin.ext (show (i : ℕ) = r - (r - (i : ℕ)) by omega)⟩`. Take `⟨b, hb⟩` from `h1 _ n`.

Rewrite using `[hg, ← (e a ha).apply_symm_apply x, he a ha n b _ hb]`. Conclude with `hgen a ha b _`. Consider the case `add t t' ht ht' => rw [Pi.single_add, map_add]`. Conclude with `hadd _ _ ht ht'`. Rewrite using `[← g.apply_symm_apply w, ← Finset.univ_sum_single (g.symm w), map_sum]`.

Conclude with `Finset.sum_induction _ P hadd h0 (fun i _ => key i _)`. Set `coT : (∀ i, N i ⊗[K] M i) →+ ∀ a, Module.Dual K (H a) →+ E` to `{ toFun := fun T a => if ha : a ≤ r then one θ (lam ⟨r - a, by omega⟩) (hl _) (e a ha) (T ⟨r - a, by omega⟩) else 0 map_zero' := by`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases ha : a ≤ r <;> simp [ha]`. Use the proof step `map_add' := fun T T' => by`.

Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases ha : a ≤ r <;> simp [ha] }`. Use `⟨coT.comp g.symm.toAddMonoidHom, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha b y φ`. Take `⟨n, hn⟩` from `h2 ⟨r - a, by omega⟩ b`.

Establish `hw : g.symm (b • μ a y) = Pi.single (⟨r - a, by omega⟩ : Fin m) (n ⊗ₜ e a ha y)`. Rewrite using `[AddEquiv.symm_apply_eq, hg, he a ha n b y hn]`. Use `show coT (g.symm (b • μ a y)) a φ = _`. Rewrite using `[hw]`. Simplify using `only [coT, AddMonoidHom.coe_mk, ZeroHom.coe_mk, dif_pos ha, Pi.single_eq_same, one_tmul, h3 _ n b hn]`.

Introduce `a' ha' a hne b y`. Take `⟨n, hn⟩` from `h2 ⟨r - a', by omega⟩ b`. Establish `hw : g.symm (b • μ a' y) = Pi.single (⟨r - a', by omega⟩ : Fin m) (n ⊗ₜ e a' ha' y)`. Rewrite using `[AddEquiv.symm_apply_eq, hg, he a' ha' n b y hn]`. Use `show coT (g.symm (b • μ a' y)) a = 0`.

Rewrite using `[hw]`. Simplify using `only [coT, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`. Use `split_ifs with ha`. Rewrite using `[Pi.single_eq_of_ne, map_zero]`. Introduce `h`.

Apply `hne` to reduce the goal to its premises. Rewrite `h` using `[Fin.mk.injEq]`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Introduce `a ha w show coT (g.symm w) a = 0`.

Simplify using `only [coT, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`. Rewrite using `[dif_neg (by omega)]`.
-/
theorem co_abs {W : Type 1} [AddCommGroup W] [Module B W] {m r : ℕ} (hr : r < m) (N : Fin m → Type) [∀ i, AddCommGroup (N i)]
    [∀ i, Module K (N i)] (M : Fin m → Type 1) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] (H : ℕ → Type 1)
    [∀ a, AddCommGroup (H a)] [∀ a, Module K (H a)] (μ : ∀ a, H a → W) (f : ∀ i, N i → M i → W) (hT : Tens K f)
    (R : ∀ i : Fin m, N i → B → Prop) (lam : ∀ i, N i →+ E) (hl : ∀ i (k : K) n, lam i (k • n) = θ (algebraMap K B k) * lam i n)
    (h1 : ∀ i n, ∃ b, R i n b) (h2 : ∀ i b, ∃ n, R i n b) (h3 : ∀ i n b, R i n b → lam i n = θ b)
    (hz : ∀ i : Fin m, r < i → Subsingleton (M i)) (e : ∀ a, a ≤ r → H a ≃ₗ[K] M ⟨r - a, by omega⟩)
    (he : ∀ a (ha : a ≤ r) n b y, R _ n b → f _ n (e a ha y) = b • μ a y) :
    (∀ P : W → Prop, P 0 → (∀ x y, P x → P y → P (x + y)) → (∀ a ≤ r, ∀ (b : B) y, P (b • μ a y)) → ∀ w, P w) ∧
    ∃ co : W →+ ∀ a, Module.Dual K (H a) →+ E, (∀ a ≤ r, ∀ (b : B) y φ, co (b • μ a y) a φ = θ b * θ (algebraMap K B (φ y))) ∧
      (∀ a' ≤ r, ∀ a, a ≠ a' → ∀ (b : B) y, co (b • μ a' y) a = 0) ∧ ∀ a, r < a → ∀ w, co w a = 0 := by
  obtain ⟨g, hg⟩ := hT
  refine ⟨?_, ?_⟩
  · intro P h0 hadd hgen w
    have key : ∀ (i : Fin m) (t : N i ⊗[K] M i), P (g (Pi.single i t)) := by
      intro i t
      induction t using TensorProduct.induction_on with
      | zero => rw [Pi.single_zero, map_zero]; exact h0
      | tmul n x =>
        by_cases hi : r < (i : ℕ)
        · have := hz i hi
          rw [Subsingleton.elim x 0, TensorProduct.tmul_zero, Pi.single_zero, map_zero]
          exact h0
        · obtain ⟨a, ha, rfl⟩ : ∃ a, ∃ ha : a ≤ r, i = ⟨r - a, Nat.lt_of_le_of_lt (Nat.sub_le r a) hr⟩ :=
            ⟨r - (i : ℕ), by omega, Fin.ext (show (i : ℕ) = r - (r - (i : ℕ)) by omega)⟩
          obtain ⟨b, hb⟩ := h1 _ n
          rw [hg, ← (e a ha).apply_symm_apply x, he a ha n b _ hb]
          exact hgen a ha b _
      | add t t' ht ht' => rw [Pi.single_add, map_add]; exact hadd _ _ ht ht'
    rw [← g.apply_symm_apply w, ← Finset.univ_sum_single (g.symm w), map_sum]
    exact Finset.sum_induction _ P hadd h0 (fun i _ => key i _)
  · let coT : (∀ i, N i ⊗[K] M i) →+ ∀ a, Module.Dual K (H a) →+ E :=
      { toFun := fun T a => if ha : a ≤ r then
            one θ (lam ⟨r - a, by omega⟩) (hl _) (e a ha) (T ⟨r - a, by omega⟩) else 0
        map_zero' := by
          funext a
          by_cases ha : a ≤ r <;> simp [ha]
        map_add' := fun T T' => by
          funext a
          by_cases ha : a ≤ r <;> simp [ha] }
    refine ⟨coT.comp g.symm.toAddMonoidHom, ?_, ?_, ?_⟩
    · intro a ha b y φ
      obtain ⟨n, hn⟩ := h2 ⟨r - a, by omega⟩ b
      have hw : g.symm (b • μ a y) = Pi.single (⟨r - a, by omega⟩ : Fin m) (n ⊗ₜ e a ha y) := by
        rw [AddEquiv.symm_apply_eq, hg, he a ha n b y hn]
      show coT (g.symm (b • μ a y)) a φ = _
      rw [hw]
      simp only [coT, AddMonoidHom.coe_mk, ZeroHom.coe_mk, dif_pos ha, Pi.single_eq_same, one_tmul, h3 _ n b hn]
    · intro a' ha' a hne b y
      obtain ⟨n, hn⟩ := h2 ⟨r - a', by omega⟩ b
      have hw : g.symm (b • μ a' y) = Pi.single (⟨r - a', by omega⟩ : Fin m) (n ⊗ₜ e a' ha' y) := by
        rw [AddEquiv.symm_apply_eq, hg, he a' ha' n b y hn]
      show coT (g.symm (b • μ a' y)) a = 0
      rw [hw]
      simp only [coT, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      split_ifs with ha
      · rw [Pi.single_eq_of_ne, map_zero]
        intro h
        apply hne
        rw [Fin.mk.injEq] at h
        omega
      · rfl
    · intro a ha w
      show coT (g.symm w) a = 0
      simp only [coT, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [dif_neg (by omega)]

end CrystallineSemistableComparison.HT.CoA

import Mathlib

open IsLocalRing

/- English proof (translation)
Introduce `R M _ _ _ I J n hn hIJ hI`. Establish `hle : ∀ k, J ^ ((n + 1) * k) • (⊤ : Submodule R M) ≤ I ^ k • ⊤` using `fun k => by`. Apply `Submodule.smul_mono_left` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hge : ∀ k, I ^ k • (⊤ : Submodule R M) ≤ J ^ k • ⊤` using `fun k => Submodule.smul_mono_left (Ideal.pow_right_mono hIJ k)`.

Use `{ haus' := fun x hx => hI.toIsHausdorff.haus' x fun k => (hx ((n + 1) * k)).mono (hle k) prec' := fun f hf => ?_ }` and prove the remaining obligations. Take `⟨L, hL⟩` from `hI.toIsPrecomplete.prec' (fun k => f ((n + 1) * k)) (fun {a b} hab => (hf (Nat.mul_le_mul_left (n + 1) hab)).mono (hle a))`. Use `⟨L, fun m => ?_⟩` and prove the remaining obligations. Conclude with `(hf (Nat.le_mul_of_pos_left m (Nat.succ_pos n))).trans ((hL m).mono (hge m))`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.cofinalCompl :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (I J : Ideal R) (n : ℕ), J ^ n ≤ I → I ≤ J → IsAdicComplete I M → IsAdicComplete J M := by
  intro R M _ _ _ I J n hn hIJ hI
  have hle : ∀ k, J ^ ((n + 1) * k) • (⊤ : Submodule R M) ≤ I ^ k • ⊤ := fun k => by
    apply Submodule.smul_mono_left
    calc J ^ ((n + 1) * k) ≤ J ^ (n * k) :=
          Ideal.pow_le_pow_right (Nat.mul_le_mul_right k (Nat.le_succ n))
      _ = (J ^ n) ^ k := pow_mul J n k
      _ ≤ I ^ k := Ideal.pow_right_mono hn k
  have hge : ∀ k, I ^ k • (⊤ : Submodule R M) ≤ J ^ k • ⊤ := fun k =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ k)
  refine
    { haus' := fun x hx => hI.toIsHausdorff.haus' x fun k => (hx ((n + 1) * k)).mono (hle k)
      prec' := fun f hf => ?_ }
  obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec' (fun k => f ((n + 1) * k))
    (fun {a b} hab => (hf (Nat.mul_le_mul_left (n + 1) hab)).mono (hle a))
  refine ⟨L, fun m => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left m (Nat.succ_pos n))).trans ((hL m).mono (hge m))

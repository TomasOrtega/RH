import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RqFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain

open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

/- English proof (translation)
Introduce `R _ q k B _ _ Φ hΦ`. Take `⟨cls, hcls⟩` from `bridge k`. Establish `hrq` using `rqFacts q`. Establish `hsc` using `sChain ℤ`. Set `g : (n : ℕ) → ↥(bd ℤ (GL (Fin n) R) k).ker →+ B` to `fun n => ((Φ n).toAddMonoidHom.comp (rq q (GL (Fin n) R) (k + 1))).comp (bd ℤ (GL (Fin n) R) k).ker.subtype.toAddMonoidHom`.

Establish `hg : ∀ n (z : ↥(bd ℤ (GL (Fin n) R) k).ker), g n z = Φ n (rq q (GL (Fin n) R) (k + 1) z)` using `fun _ _ => rfl`. Establish `hker : ∀ n, (cls (GL (Fin n) R)).ker ≤ (g n).ker`. Introduce `n z hz`. Rewrite `hz`, the goal using `[AddMonoidHom.mem_ker]`. Rewrite `hz` using `[hcls.zero _ z]`.

Take `⟨w, hw⟩` from `LinearMap.mem_range.mp hz`. Rewrite using `[hg]`. Apply `hΦ.bdry` to reduce the goal to its premises. Use `LinearMap.mem_range.mpr ⟨rq q _ (k + 1 + 1) w, ?_⟩` and prove the remaining obligations. Rewrite using `[hrq.1 _ (k + 1) w, hw]`.

Set `φ : (n : ℕ) → ↑(grpH (GL (Fin n) R) (k + 1)) →+ B` to `fun n => (cls (GL (Fin n) R)).liftOfRightInverse (Function.surjInv (hcls.surj _)) (Function.rightInverse_surjInv _) ⟨g n, hker n⟩`. Establish `hφ : ∀ n (z : ↥(bd ℤ (GL (Fin n) R) k).ker), φ n (cls (GL (Fin n) R) z) = Φ n (rq q (GL (Fin n) R) (k + 1) z)` using `fun n z => AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z`. Establish `hcyc : ∀ n (z : ↥(bd ℤ (GL (Fin n) R) k).ker), Cyc (rq q (GL (Fin n) R) (k + 1) (z : Ch ℤ (GL (Fin n) R) (k + 1)))`. Introduce `n z`. Use `show bd (ZMod q) _ k _ = 0`.

Rewrite using `[hrq.1, LinearMap.mem_ker.mp z.2, map_zero]`. Establish `hnat : ∀ n n' (f : GL (Fin n) R →* GL (Fin n') R) (z : ↥(bd ℤ (GL (Fin n) R) k).ker), ∃ z' : ↥(bd ℤ (GL (Fin n') R) k).ker, (z' : Ch ℤ (GL (Fin n') R) (k + 1)) = cm ℤ f (k + 1) z`. Introduce `n n' f z`. Use `⟨⟨cm ℤ f (k + 1) z, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, hsc.2.1, LinearMap.mem_ker.mp z.2, map_zero]`.

Use `⟨φ, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `n n' h x`. Take `⟨z, rfl⟩` from `hcls.surj _ x`. Take `⟨z', hz'⟩` from `hnat n n' (stab R n n' h) z`. Rewrite using `[← hcls.nat _ _ _ z z' hz', hφ, hφ, hz', ← hrq.2.1]`.

Conclude with `hΦ.stab n n' h _ (hcyc n z)`. Introduce `d n x`. Take `⟨z, rfl⟩` from `hcls.surj _ x`. Take `⟨z', hz'⟩` from `hnat n (d * n) (psi R d n) z`. Rewrite using `[← hcls.nat _ _ _ z z' hz', hφ, hφ, hz', ← hrq.2.1, hΦ.psi d n _ (hcyc n z), Nat.cast_smul_eq_nsmul]`.

Introduce `n z hz`. Conclude with `⟨cls _ ⟨z, hz⟩, hφ n ⟨z, hz⟩⟩`.
-/
theorem UpperTheory.V.ZK.Up.descend : UpperTheory.V.ZK.Up.Descend := by
  intro R _ q k B _ _ Φ hΦ
  obtain ⟨cls, hcls⟩ := bridge k
  have hrq := rqFacts q
  have hsc := sChain ℤ
  let g : (n : ℕ) → ↥(bd ℤ (GL (Fin n) R) k).ker →+ B := fun n =>
    ((Φ n).toAddMonoidHom.comp (rq q (GL (Fin n) R) (k + 1))).comp
      (bd ℤ (GL (Fin n) R) k).ker.subtype.toAddMonoidHom
  have hg : ∀ n (z : ↥(bd ℤ (GL (Fin n) R) k).ker),
      g n z = Φ n (rq q (GL (Fin n) R) (k + 1) z) := fun _ _ => rfl
  have hker : ∀ n, (cls (GL (Fin n) R)).ker ≤ (g n).ker := by
    intro n z hz
    rw [AddMonoidHom.mem_ker] at hz ⊢
    rw [hcls.zero _ z] at hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hz
    rw [hg]
    apply hΦ.bdry
    refine LinearMap.mem_range.mpr ⟨rq q _ (k + 1 + 1) w, ?_⟩
    rw [hrq.1 _ (k + 1) w, hw]
  let φ : (n : ℕ) → ↑(grpH (GL (Fin n) R) (k + 1)) →+ B := fun n =>
    (cls (GL (Fin n) R)).liftOfRightInverse (Function.surjInv (hcls.surj _))
      (Function.rightInverse_surjInv _) ⟨g n, hker n⟩
  have hφ : ∀ n (z : ↥(bd ℤ (GL (Fin n) R) k).ker),
      φ n (cls (GL (Fin n) R) z) = Φ n (rq q (GL (Fin n) R) (k + 1) z) := fun n z =>
    AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z
  have hcyc : ∀ n (z : ↥(bd ℤ (GL (Fin n) R) k).ker),
      Cyc (rq q (GL (Fin n) R) (k + 1) (z : Ch ℤ (GL (Fin n) R) (k + 1))) := by
    intro n z
    show bd (ZMod q) _ k _ = 0
    rw [hrq.1, LinearMap.mem_ker.mp z.2, map_zero]
  have hnat : ∀ n n' (f : GL (Fin n) R →* GL (Fin n') R) (z : ↥(bd ℤ (GL (Fin n) R) k).ker),
      ∃ z' : ↥(bd ℤ (GL (Fin n') R) k).ker,
        (z' : Ch ℤ (GL (Fin n') R) (k + 1)) = cm ℤ f (k + 1) z := by
    intro n n' f z
    refine ⟨⟨cm ℤ f (k + 1) z, ?_⟩, rfl⟩
    rw [LinearMap.mem_ker, hsc.2.1, LinearMap.mem_ker.mp z.2, map_zero]
  refine ⟨φ, ⟨?_, ?_⟩, ?_⟩
  · intro n n' h x
    obtain ⟨z, rfl⟩ := hcls.surj _ x
    obtain ⟨z', hz'⟩ := hnat n n' (stab R n n' h) z
    rw [← hcls.nat _ _ _ z z' hz', hφ, hφ, hz', ← hrq.2.1]
    exact hΦ.stab n n' h _ (hcyc n z)
  · intro d n x
    obtain ⟨z, rfl⟩ := hcls.surj _ x
    obtain ⟨z', hz'⟩ := hnat n (d * n) (psi R d n) z
    rw [← hcls.nat _ _ _ z z' hz', hφ, hφ, hz', ← hrq.2.1, hΦ.psi d n _ (hcyc n z),
      Nat.cast_smul_eq_nsmul]
  · intro n z hz
    exact ⟨cls _ ⟨z, hz⟩, hφ n ⟨z, hz⟩⟩

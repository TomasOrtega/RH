import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `: NeZero (n ^ J)` using `⟨pow_ne_zero _ hn⟩`. Establish `hv : n ^ J ∣ n * t.val`. Rewrite using `[← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]`. Conclude with `ht`. Take `⟨k, hk⟩` from `hv`.

Establish `h1 : t.val = n * (n ^ (J - 2) * k)`. Apply `Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)` to reduce the goal to its premises. Rewrite using `[hk, show n ^ J = n * (n * n ^ (J - 2)) by`. Rewrite using `[← pow_succ', ← pow_succ']`. Use `congr 1`.

Use the proof step `omega]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨((n ^ (J - 2) * k : ℕ) : ZMod (n ^ J)), ?_⟩` and prove the remaining obligations. Rewrite using `[nsmul_eq_mul, ← Nat.cast_mul, ← h1, ZMod.natCast_zmod_val]`.
-/
theorem zmod_pow_exists_eq_nsmul_of_nsmul_eq_zero (n J : ℕ) (hn : n ≠ 0) (hJ : 2 ≤ J)
    (t : ZMod (n ^ J)) (ht : n • t = 0) : ∃ s : ZMod (n ^ J), t = n • s := by
  have : NeZero (n ^ J) := ⟨pow_ne_zero _ hn⟩
  have hv : n ^ J ∣ n * t.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]
    exact ht
  obtain ⟨k, hk⟩ := hv
  have h1 : t.val = n * (n ^ (J - 2) * k) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
    rw [hk, show n ^ J = n * (n * n ^ (J - 2)) by
      rw [← pow_succ', ← pow_succ']; congr 1; omega]
    ring
  refine ⟨((n ^ (J - 2) * k : ℕ) : ZMod (n ^ J)), ?_⟩
  rw [nsmul_eq_mul, ← Nat.cast_mul, ← h1, ZMod.natCast_zmod_val]

/- English proof (translation)
Introduce `I X _ _ n J M hn hJ hM yy hyy Z hZ hcov`. Substitute `hM` using the available equality. Establish `key : ∀ b : I → ZMod (n ^ J), n • b = 0 → b ∈ yy.ker → ∃ k ∈ yy.ker, n • k = b`. Introduce `b hb hbk`. Establish `hc : ∀ i, ∃ s, b i = n • s` using `fun i => zmod_pow_exists_eq_nsmul_of_nsmul_eq_zero n J hn hJ (b i) (by`.

Simplify using `using congrFun hb i)`. Use `choose c hc using hc`. Establish `hbc : b = n • c` using `funext fun i => by simpa using hc i`. Take `⟨x, hx⟩` from `QuotientAddGroup.mk_surjective (yy c)`. Establish `hnx : n • x ∈ (nsmulAddMonoidHom (n ^ J) : X →+ X).range`.

Rewrite using `[← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, hx, ← map_nsmul, ← hbc]`. Conclude with `hbk`. Take `⟨x', hx'⟩` from `hnx`. Establish `hx'' : (n ^ J) • x' = n • x` using `hx'`. Establish `hxx : x = n ^ (J - 1) • x'`.

Establish `h2 : (n : ℤ) • x = (n : ℤ) • (n ^ (J - 1) • x')`. Rewrite using `[natCast_zsmul, natCast_zsmul, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega]`. Conclude with `hx''.symm`. Conclude with `smul_right_injective X (by exact_mod_cast hn) h2`. Take `⟨c', hc'⟩` from `hyy (QuotientAddGroup.mk x')`.

Use `⟨c - n ^ (J - 1) • c', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AddMonoidHom.mem_ker, map_sub, map_nsmul, hc', ← QuotientAddGroup.mk_nsmul, ← hxx, hx, sub_self]`. Establish `h0 : (n ^ J) • c' = 0` using `funext fun i => by`. Simplify using `only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]`. Rewrite using `[smul_sub, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega, ← hbc, h0, sub_zero]`.

Apply `le_antisymm` to reduce the goal to its premises. Conclude with `(AddSubgroup.closure_le _).2 hZ`. Introduce `a ha`. Take `⟨b, hb, hab⟩` from `hcov a ha`. Establish `hbk : b ∈ yy.ker`.

Establish `h3 : yy (a + b) = 0` using `hZ hab`. Rewrite `ha`, the goal using `[AddMonoidHom.mem_ker]`. Rewrite `h3` using `[map_add, ha, zero_add]`. Then use the resulting hypothesis. Take `⟨k, hk, hkb⟩` from `key b hb hbk`. Take `⟨b', hb', hkb'⟩` from `hcov k hk`.

Establish `h4 : a = (a + b) - n • (k + b')`. Rewrite using `[smul_add, hb', add_zero, hkb, add_sub_cancel_right]`. Rewrite using `[h4]`. Conclude with `sub_mem (AddSubgroup.subset_closure hab) (nsmul_mem (AddSubgroup.subset_closure hkb') n)`.
-/
theorem closure_eq_ker_of_meets_torsion_cosets :
    ∀ (I X : Type) [AddCommGroup X] [Module.Free ℤ X] (n J M : ℕ), n ≠ 0 → 2 ≤ J → M = n ^ J → ∀ (yy : (I → ZMod M) →+ X ⧸ (nsmulAddMonoidHom M : X →+ X).range), Function.Surjective yy → ∀ Z : Set (I → ZMod M), Z ⊆ yy.ker → (∀ a ∈ yy.ker, ∃ b, n • b = 0 ∧ a + b ∈ Z) → AddSubgroup.closure Z = yy.ker := by
  intro I X _ _ n J M hn hJ hM yy hyy Z hZ hcov
  subst hM
  have key : ∀ b : I → ZMod (n ^ J), n • b = 0 → b ∈ yy.ker → ∃ k ∈ yy.ker, n • k = b := by
    intro b hb hbk
    have hc : ∀ i, ∃ s, b i = n • s := fun i =>
      zmod_pow_exists_eq_nsmul_of_nsmul_eq_zero n J hn hJ (b i) (by
        simpa using congrFun hb i)
    choose c hc using hc
    have hbc : b = n • c := funext fun i => by simpa using hc i
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (yy c)
    have hnx : n • x ∈ (nsmulAddMonoidHom (n ^ J) : X →+ X).range := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, hx, ← map_nsmul, ← hbc]
      exact hbk
    obtain ⟨x', hx'⟩ := hnx
    have hx'' : (n ^ J) • x' = n • x := hx'
    have hxx : x = n ^ (J - 1) • x' := by
      have h2 : (n : ℤ) • x = (n : ℤ) • (n ^ (J - 1) • x') := by
        rw [natCast_zsmul, natCast_zsmul, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega]
        exact hx''.symm
      exact smul_right_injective X (by exact_mod_cast hn) h2
    obtain ⟨c', hc'⟩ := hyy (QuotientAddGroup.mk x')
    refine ⟨c - n ^ (J - 1) • c', ?_, ?_⟩
    · rw [AddMonoidHom.mem_ker, map_sub, map_nsmul, hc', ← QuotientAddGroup.mk_nsmul, ← hxx, hx,
        sub_self]
    · have h0 : (n ^ J) • c' = 0 := funext fun i => by
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rw [smul_sub, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega, ← hbc, h0, sub_zero]
  apply le_antisymm
  · exact (AddSubgroup.closure_le _).2 hZ
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    have hbk : b ∈ yy.ker := by
      have h3 : yy (a + b) = 0 := hZ hab
      rw [AddMonoidHom.mem_ker] at ha ⊢
      rwa [map_add, ha, zero_add] at h3
    obtain ⟨k, hk, hkb⟩ := key b hb hbk
    obtain ⟨b', hb', hkb'⟩ := hcov k hk
    have h4 : a = (a + b) - n • (k + b') := by
      rw [smul_add, hb', add_zero, hkb, add_sub_cancel_right]
    rw [h4]
    exact sub_mem (AddSubgroup.subset_closure hab) (nsmul_mem (AddSubgroup.subset_closure hkb') n)

end GlobalTheory

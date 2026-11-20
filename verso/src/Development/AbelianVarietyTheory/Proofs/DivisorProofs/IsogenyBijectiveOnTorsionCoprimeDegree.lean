import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory

/- English proof (translation)
Introduce `hla hmu hlm hml hMd`. Use `⟨fun y hyM hyl => ?_, fun g hgM => ?_⟩` and prove the remaining obligations. Establish `hyd : y ^ d = 1`. Establish `h1 : y ≫ (la ≫ mu) = y ^ d`. Rewrite using `[hlm, MonObj.comp_pow, Category.comp_id]`.

Rewrite using `[← h1, ← Category.assoc, hyl, MonObj.one_comp]`. Establish `h` using `(pow_gcd_eq_one (a := y) (m := M) (n := d)).2 ⟨hyM, hyd⟩`. Rewrite `h` using `[Nat.Coprime.gcd_eq_one hMd, pow_one]`. Then use the resulting hypothesis. Use `set e := d ^ (Nat.totient M - 1) with he`. Establish `hde : d * e % M = 1 % M`.

Break down `Nat.eq_zero_or_pos M with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Establish `hd1 : d = 1` using `(Nat.coprime_zero_left d).1 hMd`. Substitute `hd1` using the available equality. Simplify using `[he]`.

Establish `ht : 0 < Nat.totient M` using `Nat.totient_pos.2 hpos`. Establish `hpow : d * e = d ^ Nat.totient M`. Rewrite using `[he, ← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hpow]`. Conclude with `Nat.ModEq.pow_totient (Nat.Coprime.symm hMd)`. Use `⟨(g ≫ mu) ^ e, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, ← MonObj.pow_comp, hgM, MonObj.one_comp, one_pow]`. Establish `h1 : (g ≫ mu) ≫ la = g ^ d`.

Rewrite using `[Category.assoc, hml, MonObj.comp_pow, Category.comp_id]`. Rewrite using `[MonObj.pow_comp, h1, ← pow_mul, pow_eq_pow_mod (d * e) hgM, hde, ← pow_eq_pow_mod 1 hgM, pow_one]`.
-/
theorem isogeny_torsion_bij {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A]
    [IsCommMonObj B] (la : A ⟶ B) (mu : B ⟶ A) (d M : ℕ) (T : Over S) :
    IsMonHom la → IsMonHom mu → la ≫ mu = 𝟙 A ^ d → mu ≫ la = 𝟙 B ^ d → M.Coprime d →
      (∀ y : T ⟶ A, y ^ M = 1 → y ≫ la = 1 → y = 1) ∧
        (∀ g : T ⟶ B, g ^ M = 1 → ∃ y : T ⟶ A, y ^ M = 1 ∧ y ≫ la = g) := by
  intro hla hmu hlm hml hMd
  refine ⟨fun y hyM hyl => ?_, fun g hgM => ?_⟩
  · have hyd : y ^ d = 1 := by
      have h1 : y ≫ (la ≫ mu) = y ^ d := by
        rw [hlm, MonObj.comp_pow, Category.comp_id]
      rw [← h1, ← Category.assoc, hyl, MonObj.one_comp]
    have h := (pow_gcd_eq_one (a := y) (m := M) (n := d)).2 ⟨hyM, hyd⟩
    rwa [Nat.Coprime.gcd_eq_one hMd, pow_one] at h
  ·
    set e := d ^ (Nat.totient M - 1) with he
    have hde : d * e % M = 1 % M := by
      rcases Nat.eq_zero_or_pos M with h0 | hpos
      · subst h0
        have hd1 : d = 1 := (Nat.coprime_zero_left d).1 hMd
        subst hd1
        simp [he]
      · have ht : 0 < Nat.totient M := Nat.totient_pos.2 hpos
        have hpow : d * e = d ^ Nat.totient M := by
          rw [he, ← pow_succ']
          congr 1
          omega
        rw [hpow]
        exact Nat.ModEq.pow_totient (Nat.Coprime.symm hMd)
    refine ⟨(g ≫ mu) ^ e, ?_, ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, ← MonObj.pow_comp, hgM, MonObj.one_comp, one_pow]
    · have h1 : (g ≫ mu) ≫ la = g ^ d := by
        rw [Category.assoc, hml, MonObj.comp_pow, Category.comp_id]
      rw [MonObj.pow_comp, h1, ← pow_mul, pow_eq_pow_mod (d * e) hgM, hde,
        ← pow_eq_pow_mod 1 hgM, pow_one]

end GlobalTheory

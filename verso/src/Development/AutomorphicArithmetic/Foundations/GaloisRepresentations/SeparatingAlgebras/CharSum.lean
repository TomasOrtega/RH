import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowValAdd

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `N _`. Establish `hN : N ≠ 0` using `NeZero.ne N`. Take `⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N` from `⟨_, Complex.isPrimitiveRoot_exp N hN⟩`. Establish `hz0 : ζ ≠ 0` using `hζ.ne_zero hN`. Set `u : ℂˣ` to `Units.mk0 ζ hz0`.

Establish `huN : u ^ N = 1`. Use `ext`. Simplify using `[u, hζ.pow_eq_one]`. Establish `hu : ∀ j : ℕ, (u ^ j) ^ N = 1`. Introduce `j`.

Rewrite using `[← pow_mul, mul_comm, pow_mul, huN, one_pow]`. Set `χ : Fin N → (Multiplicative (ZMod N) →* ℂˣ)` to `fun j => GlobalTheory.CongSc.zchar (u ^ (j : ℕ)) (hu j)`. Establish `hval : ∀ (j : Fin N) (x : Multiplicative (ZMod N)), ((χ j x : ℂˣ) : ℂ) = (ζ ^ (j : ℕ)) ^ (Multiplicative.toAdd x).val`. Introduce `j x`. Simplify using `[χ, GlobalTheory.CongSc.zchar_apply, u]`.

Establish `hone : ∀ j : Fin N, j ≠ 0 → ((χ j (Multiplicative.ofAdd 1) : ℂˣ) : ℂ) = ζ ^ (j : ℕ)`. Introduce `j hj`. Rewrite using `[hval]`. Establish `hj' : (j : ℕ) ≠ 0` using `fun h => hj (Fin.ext h)`. Establish `h1 : 1 < N`.

Use `j.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[toAdd_ofAdd, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]`. Use `⟨(Finset.univ.erase 0).image χ, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hc`.

Rewrite `hc` using `[Finset.mem_image]`. Take `⟨j, hj, rfl⟩` from `hc`. Establish `hj0 : j ≠ 0` using `Finset.ne_of_mem_erase hj`. Introduce `h`. Establish `h2 : ζ ^ (j : ℕ) = 1`.

Rewrite using `[← hone j hj0, h]`. Simplify using the standard rewrite rules. Establish `hd` using `(hζ.pow_eq_one_iff_dvd (j : ℕ)).mp h2`. Conclude with `hj0 (Fin.ext (Nat.eq_zero_of_dvd_of_lt hd j.isLt))`. Introduce `x`.

Rewrite using `[Finset.sum_image (by`. Introduce `j hj k hk hjk`. Establish `hj0 : j ≠ 0` using `Finset.ne_of_mem_erase hj`. Establish `hk0 : k ≠ 0` using `Finset.ne_of_mem_erase hk`. Establish `h3` using `hone j hj0`.

Rewrite `h3` using `[hjk, hone k hk0]`. Conclude with `(Fin.ext (hζ.pow_inj k.isLt j.isLt h3)).symm)]`. Repeatedly rewrite using `[hval]`. Establish `key` using `GlobalTheory.CongSc.sum_roots hζ (Multiplicative.toAdd x).val (ZMod.val_lt _)`. Rewrite `key` using `[← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin N))]`.

Simplify using `only [Fin.val_zero, pow_zero, one_pow] at key`. Use `split_ifs at key`. Conclude with `Or.inr key`. Conclude with `Or.inl key`.
-/
theorem UpperTheory.Gal.Gen.charSum_pf :
    UpperTheory.Gal.Gen.CharSum := by
  intro N _
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hN⟩
  have hz0 : ζ ≠ 0 := hζ.ne_zero hN
  let u : ℂˣ := Units.mk0 ζ hz0
  have huN : u ^ N = 1 := by
    ext
    simp [u, hζ.pow_eq_one]
  have hu : ∀ j : ℕ, (u ^ j) ^ N = 1 := by
    intro j
    rw [← pow_mul, mul_comm, pow_mul, huN, one_pow]
  let χ : Fin N → (Multiplicative (ZMod N) →* ℂˣ) := fun j => GlobalTheory.CongSc.zchar (u ^ (j : ℕ)) (hu j)
  have hval : ∀ (j : Fin N) (x : Multiplicative (ZMod N)),
      ((χ j x : ℂˣ) : ℂ) = (ζ ^ (j : ℕ)) ^ (Multiplicative.toAdd x).val := by
    intro j x
    simp [χ, GlobalTheory.CongSc.zchar_apply, u]
  have hone : ∀ j : Fin N, j ≠ 0 → ((χ j (Multiplicative.ofAdd 1) : ℂˣ) : ℂ) = ζ ^ (j : ℕ) := by
    intro j hj
    rw [hval]
    have hj' : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    have h1 : 1 < N := by
      have := j.isLt
      omega
    rw [toAdd_ofAdd, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]
  refine ⟨(Finset.univ.erase 0).image χ, ?_, ?_⟩
  · intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
    intro h
    have h2 : ζ ^ (j : ℕ) = 1 := by
      rw [← hone j hj0, h]
      simp
    have hd := (hζ.pow_eq_one_iff_dvd (j : ℕ)).mp h2
    exact hj0 (Fin.ext (Nat.eq_zero_of_dvd_of_lt hd j.isLt))
  · intro x
    rw [Finset.sum_image (by
      intro j hj k hk hjk
      have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
      have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
      have h3 := hone j hj0
      rw [hjk, hone k hk0] at h3
      exact (Fin.ext (hζ.pow_inj k.isLt j.isLt h3)).symm)]
    simp_rw [hval]
    have key := GlobalTheory.CongSc.sum_roots hζ (Multiplicative.toAdd x).val (ZMod.val_lt _)
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin N))] at key
    simp only [Fin.val_zero, pow_zero, one_pow] at key
    split_ifs at key
    · exact Or.inr key
    · exact Or.inl key

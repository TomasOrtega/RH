import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Introduce `k D A _ _ _ _ _ _ ρ x hD h`. Use `letI := Fintype.ofFinite D`. Establish `hexp : ((Monoid.exponent D : ℕ) : k) ≠ 0`. Introduce `h0`. Take `⟨c, hc⟩` from `Group.exponent_dvd_nat_card (G := D)`.

Apply `hD` to reduce the goal to its premises. Rewrite using `[hc]`. Use `push_cast`. Rewrite using `[h0, zero_mul]`. Use `haveI : NeZero ((Monoid.exponent D : ℕ) : k) := ⟨hexp⟩`.

Use `haveI : NeZero (Monoid.exponent D) := ⟨fun h0 => hexp (by rw [h0]; simp)⟩`. Use `haveI : HasEnoughRootsOfUnity k (Monoid.exponent D) := inferInstance`. Establish `hcard : Nat.card (D →* kˣ) = Nat.card D` using `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity D k`. Use `haveI : Finite (D →* kˣ) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')`. Use `letI := Fintype.ofFinite (D →* kˣ)`.

Establish `h1 : ∀ ψ : D →* kˣ, x * (∑ d : D, ((ψ d⁻¹ : kˣ) : k) • ρ d) = 0`. Introduce `ψ`. Apply `h ψ` to reduce the goal to its premises. Introduce `g`. Rewrite using `[Finset.mul_sum, Finset.smul_sum]`.

Use `Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_` and prove the remaining obligations. Introduce `d`. Simplify using `only [Equiv.coe_mulLeft, mul_smul_comm, smul_smul, ← map_mul, ← Units.val_mul]`. Use `congr 3`. Rewrite using `[mul_inv, mul_inv_cancel_left]`.

Establish `h2 : ∀ d : D, d ≠ 1 → ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = 0`. Introduce `d hd`. Take `⟨φ, hφ⟩` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity D k (a := d⁻¹) (inv_ne_one.mpr hd)`. Establish `e : ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = (φ d⁻¹ : k) * ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k)`. Rewrite using `[Finset.mul_sum]`.

Use `(Fintype.sum_equiv (Equiv.mulLeft φ) _ _ ?_).symm` and prove the remaining obligations. Introduce `ψ`. Simplify using `only [Equiv.coe_mulLeft, MonoidHom.mul_apply, Units.val_mul]`. Establish `hne : ((φ d⁻¹ : kˣ) : k) ≠ 1` using `fun h' => hφ (Units.val_eq_one.mp h')`. Establish `: (1 - ((φ d⁻¹ : kˣ) : k)) * ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = 0`.

Rewrite using `[sub_mul, one_mul, ← e, sub_self]`. Conclude with `(mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne.symm)`. Establish `h3 : ∑ ψ : D →* kˣ, ∑ d : D, ((ψ d⁻¹ : kˣ) : k) • ρ d = (Nat.card D : k) • (1 : A)`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul]`.

Rewrite using `[Finset.sum_eq_single (1 : D)]`. Rewrite using `[← hcard, Nat.card_eq_fintype_card]`. Simplify using the standard rewrite rules. Introduce `d _ hd`. Rewrite using `[h2 d hd, zero_smul]`.

Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`. Establish `h4 : x * ((Nat.card D : k) • (1 : A)) = 0`. Rewrite using `[← h3, Finset.mul_sum]`. Conclude with `Finset.sum_eq_zero fun ψ _ => h1 ψ`.

Rewrite `h4` using `[mul_smul_comm, mul_one]`. Conclude with `(smul_eq_zero.mp h4).resolve_left hD`.
-/
theorem UpperTheory.V.FW.sepChar :
    ∀ (k D A : Type) [Field k] [IsAlgClosed k] [CommGroup D] [Finite D] [CommRing A] [Algebra k A] (ρ : D →* A) (x : A), (Nat.card D : k) ≠ 0 → (∀ (ψ : D →* kˣ) (e : A), (∀ d, ρ d * e = (ψ d : k) • e) → x * e = 0) → x = 0 := by
  intro k D A _ _ _ _ _ _ ρ x hD h
  classical
  letI := Fintype.ofFinite D
  have hexp : ((Monoid.exponent D : ℕ) : k) ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := Group.exponent_dvd_nat_card (G := D)
    apply hD
    rw [hc]; push_cast; rw [h0, zero_mul]
  haveI : NeZero ((Monoid.exponent D : ℕ) : k) := ⟨hexp⟩
  haveI : NeZero (Monoid.exponent D) := ⟨fun h0 => hexp (by rw [h0]; simp)⟩
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent D) := inferInstance
  have hcard : Nat.card (D →* kˣ) = Nat.card D :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity D k
  haveI : Finite (D →* kˣ) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  letI := Fintype.ofFinite (D →* kˣ)
  have h1 : ∀ ψ : D →* kˣ, x * (∑ d : D, ((ψ d⁻¹ : kˣ) : k) • ρ d) = 0 := by
    intro ψ
    apply h ψ
    intro g
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_
    intro d
    simp only [Equiv.coe_mulLeft, mul_smul_comm, smul_smul, ← map_mul, ← Units.val_mul]
    congr 3
    rw [mul_inv, mul_inv_cancel_left]
  have h2 : ∀ d : D, d ≠ 1 → ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = 0 := by
    intro d hd
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity D k (a := d⁻¹) (inv_ne_one.mpr hd)
    have e : ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = (φ d⁻¹ : k) * ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) := by
      rw [Finset.mul_sum]
      refine (Fintype.sum_equiv (Equiv.mulLeft φ) _ _ ?_).symm
      intro ψ
      simp only [Equiv.coe_mulLeft, MonoidHom.mul_apply, Units.val_mul]
    have hne : ((φ d⁻¹ : kˣ) : k) ≠ 1 := fun h' => hφ (Units.val_eq_one.mp h')
    have : (1 - ((φ d⁻¹ : kˣ) : k)) * ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = 0 := by
      rw [sub_mul, one_mul, ← e, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne.symm)
  have h3 : ∑ ψ : D →* kˣ, ∑ d : D, ((ψ d⁻¹ : kˣ) : k) • ρ d = (Nat.card D : k) • (1 : A) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single (1 : D)]
    · rw [← hcard, Nat.card_eq_fintype_card]
      simp
    · intro d _ hd
      rw [h2 d hd, zero_smul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  have h4 : x * ((Nat.card D : k) • (1 : A)) = 0 := by
    rw [← h3, Finset.mul_sum]
    exact Finset.sum_eq_zero fun ψ _ => h1 ψ
  rw [mul_smul_comm, mul_one] at h4
  exact (smul_eq_zero.mp h4).resolve_left hD

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simp`. Consider the case `succ s ih`. Set `T` to `Submodule.torsionBy ℤ W (l ^ (s + 1))`. Set `m : T →ₗ[ℤ] W` to `l • T.subtype`.

Establish `hr : LinearMap.range m ≤ Submodule.torsionBy ℤ W (l ^ s)`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Submodule.mem_torsionBy_iff]`. Establish `hw` using `(Submodule.mem_torsionBy_iff _ _).1 w.2`. Express the relevant statement in the definitionally equal form `l ^ s • (l • (w : W)) = 0`.

Rewrite using `[smul_smul, ← pow_succ]`. Conclude with `hw`. Establish `h1 : Nat.card T = Nat.card (T ⧸ LinearMap.ker m) * Nat.card (LinearMap.ker m)` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker m).toAddSubgroup`. Rewrite `h1` using `[Nat.card_congr m.quotKerEquivRange.toEquiv]`. Establish `h2 : Nat.card (LinearMap.range m) ≤ Nat.card (Submodule.torsionBy ℤ W (l ^ s))` using `Nat.card_le_card_of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)`.

Establish `h3 : Nat.card (LinearMap.ker m) ≤ Nat.card {w : W // l • w = 0}` using `Nat.card_le_card_of_injective (fun k => ⟨((k : T) : W), k.2⟩) (fun a b hab => by`. Establish `h` using `congrArg Subtype.val hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `h)`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem card_tors (W : Type) [AddCommGroup W] [Finite W] (l : ℤ) (s : ℕ) :
    Nat.card (Submodule.torsionBy ℤ W (l ^ s)) ≤ Nat.card {w : W // l • w = 0} ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    let T := Submodule.torsionBy ℤ W (l ^ (s + 1))
    let m : T →ₗ[ℤ] W := l • T.subtype
    have hr : LinearMap.range m ≤ Submodule.torsionBy ℤ W (l ^ s) := by
      rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_torsionBy_iff]
      have hw := (Submodule.mem_torsionBy_iff _ _).1 w.2
      change l ^ s • (l • (w : W)) = 0
      rw [smul_smul, ← pow_succ]
      exact hw
    have h1 : Nat.card T = Nat.card (T ⧸ LinearMap.ker m) * Nat.card (LinearMap.ker m) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker m).toAddSubgroup
    rw [Nat.card_congr m.quotKerEquivRange.toEquiv] at h1
    have h2 : Nat.card (LinearMap.range m) ≤ Nat.card (Submodule.torsionBy ℤ W (l ^ s)) :=
      Nat.card_le_card_of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)
    have h3 : Nat.card (LinearMap.ker m) ≤ Nat.card {w : W // l • w = 0} :=
      Nat.card_le_card_of_injective (fun k => ⟨((k : T) : W), k.2⟩)
        (fun a b hab => by
          have h := congrArg Subtype.val hab
          apply Subtype.ext
          apply Subtype.ext
          exact h)
    calc Nat.card T = Nat.card (LinearMap.range m) * Nat.card (LinearMap.ker m) := h1
      _ ≤ Nat.card (Submodule.torsionBy ℤ W (l ^ s)) * Nat.card {w : W // l • w = 0} :=
          Nat.mul_le_mul h2 h3
      _ ≤ Nat.card {w : W // l • w = 0} ^ s * Nat.card {w : W // l • w = 0} :=
          Nat.mul_le_mul_right _ ih
      _ = Nat.card {w : W // l • w = 0} ^ (s + 1) := (pow_succ _ _).symm

/- English proof (translation)
Introduce `W Z _ _ _ f l s g u hl hlu hker hW`. Use `haveI := Fact.mk hl`. Set `K` to `LinearMap.ker f`. Set `gm : K →ₗ[ℤ] K` to `((l : ℤ) ^ s) • LinearMap.id`. Use `haveI : Finite (LinearMap.range f) := Finite.of_surjective _ f.surjective_rangeRestrict`.

Establish `hWc : Nat.card W = Nat.card (LinearMap.range f) * Nat.card K`. Establish `h : Nat.card W = Nat.card (W ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f)` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup`. Rewrite `h` using `[Nat.card_congr f.quotKerEquivRange.toEquiv]`. Then use the resulting hypothesis. Establish `hKc : Nat.card K = Nat.card (LinearMap.range gm) * Nat.card (LinearMap.ker gm)`. Establish `h : Nat.card K = Nat.card (K ⧸ LinearMap.ker gm) * Nat.card (LinearMap.ker gm)` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker gm).toAddSubgroup`.

Rewrite `h` using `[Nat.card_congr gm.quotKerEquivRange.toEquiv]`. Then use the resulting hypothesis. Establish `hR0 : Nat.card (LinearMap.range f) ≠ 0` using `Nat.card_pos.ne'`. Establish `hK0 : Nat.card K ≠ 0` using `Nat.card_pos.ne'`. Establish `hRg0 : Nat.card (LinearMap.range gm) ≠ 0` using `Nat.card_pos.ne'`. Establish `hKg0 : Nat.card (LinearMap.ker gm) ≠ 0` using `Nat.card_pos.ne'`.

Establish `hcop : ¬ l ∣ Nat.card (LinearMap.range gm)`. Introduce `hd`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' l hd`. Establish `hux : u • x = 0`. Break down `x with ⟨y, k, rfl⟩` into its components or cases.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `u • ((l : ℤ) ^ s • ((k : K) : W)) = 0`. Rewrite using `[smul_smul]`. Conclude with `hker _ k.2`.

Establish `hdv` using `addOrderOf_dvd_iff_zsmul_eq_zero.2 hux`. Rewrite `hdv` using `[hx]`. Conclude with `hlu hdv`. Establish `hvK : (Nat.card K).factorization l = (Nat.card (LinearMap.ker gm)).factorization l`. Rewrite using `[hKc, Nat.factorization_mul hRg0 hKg0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hcop, zero_add]`.

Establish `hA : Nat.card (LinearMap.ker gm) ≤ l ^ (s * g)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Submodule.mem_torsionBy_iff]`. Conclude with `congrArg Subtype.val (LinearMap.mem_ker.1 a.2)⟩)`. Use the proof step `(fun a b hab => by`.

Establish `h` using `congrArg Subtype.val hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `h)`. Use `_ ≤ Nat.card {w : W // (l : ℤ) • w = 0} ^ s := card_tors W l s`.

Use `_ ≤ (l ^ g) ^ s := Nat.pow_le_pow_left hW s`. Use `_ = l ^ (s * g) := by rw [← pow_mul, mul_comm]`. Establish `hR : l ^ (Nat.card (LinearMap.range f)).factorization l ≤ Nat.card (LinearMap.range f)` using `Nat.ordProj_le l hR0`. Establish `hKl : l ^ (Nat.card (LinearMap.ker gm)).factorization l ≤ Nat.card (LinearMap.ker gm)` using `Nat.ordProj_le l hKg0`. Rewrite using `[hWc, Nat.factorization_mul hR0 hK0, Finsupp.add_apply, pow_add, hvK]`.

Conclude with `Nat.mul_le_mul hR (hKl.trans hA)`.
-/
theorem UpperTheory.V.ZK.Ct.pCount :
    ∀ (W Z : Type) [AddCommGroup W] [AddCommGroup Z] [Finite W] (f : W →ₗ[ℤ] Z) (l s g : ℕ) (u : ℤ), l.Prime → ¬(l : ℤ) ∣ u → (∀ w, f w = 0 → (u * (l : ℤ) ^ s) • w = 0) → Nat.card {w : W // (l : ℤ) • w = 0} ≤ l ^ g → l ^ (Nat.card W).factorization l ≤ Nat.card (LinearMap.range f) * l ^ (s * g) := by
  intro W Z _ _ _ f l s g u hl hlu hker hW
  haveI := Fact.mk hl
  let K := LinearMap.ker f
  let gm : K →ₗ[ℤ] K := ((l : ℤ) ^ s) • LinearMap.id
  haveI : Finite (LinearMap.range f) := Finite.of_surjective _ f.surjective_rangeRestrict
  have hWc : Nat.card W = Nat.card (LinearMap.range f) * Nat.card K := by
    have h : Nat.card W = Nat.card (W ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup
    rwa [Nat.card_congr f.quotKerEquivRange.toEquiv] at h
  have hKc : Nat.card K = Nat.card (LinearMap.range gm) * Nat.card (LinearMap.ker gm) := by
    have h : Nat.card K = Nat.card (K ⧸ LinearMap.ker gm) * Nat.card (LinearMap.ker gm) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker gm).toAddSubgroup
    rwa [Nat.card_congr gm.quotKerEquivRange.toEquiv] at h
  have hR0 : Nat.card (LinearMap.range f) ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hRg0 : Nat.card (LinearMap.range gm) ≠ 0 := Nat.card_pos.ne'
  have hKg0 : Nat.card (LinearMap.ker gm) ≠ 0 := Nat.card_pos.ne'
  have hcop : ¬ l ∣ Nat.card (LinearMap.range gm) := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hd
    have hux : u • x = 0 := by
      rcases x with ⟨y, k, rfl⟩
      apply Subtype.ext
      apply Subtype.ext
      change u • ((l : ℤ) ^ s • ((k : K) : W)) = 0
      rw [smul_smul]
      exact hker _ k.2
    have hdv := addOrderOf_dvd_iff_zsmul_eq_zero.2 hux
    rw [hx] at hdv
    exact hlu hdv
  have hvK : (Nat.card K).factorization l = (Nat.card (LinearMap.ker gm)).factorization l := by
    rw [hKc, Nat.factorization_mul hRg0 hKg0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hcop, zero_add]
  have hA : Nat.card (LinearMap.ker gm) ≤ l ^ (s * g) := by
    calc Nat.card (LinearMap.ker gm) ≤ Nat.card (Submodule.torsionBy ℤ W ((l : ℤ) ^ s)) :=
          Nat.card_le_card_of_injective
            (fun a => ⟨((a : K) : W), by
              rw [Submodule.mem_torsionBy_iff]
              exact congrArg Subtype.val (LinearMap.mem_ker.1 a.2)⟩)
            (fun a b hab => by
              have h := congrArg Subtype.val hab
              apply Subtype.ext
              apply Subtype.ext
              exact h)
      _ ≤ Nat.card {w : W // (l : ℤ) • w = 0} ^ s := card_tors W l s
      _ ≤ (l ^ g) ^ s := Nat.pow_le_pow_left hW s
      _ = l ^ (s * g) := by rw [← pow_mul, mul_comm]
  have hR : l ^ (Nat.card (LinearMap.range f)).factorization l ≤ Nat.card (LinearMap.range f) :=
    Nat.ordProj_le l hR0
  have hKl : l ^ (Nat.card (LinearMap.ker gm)).factorization l ≤ Nat.card (LinearMap.ker gm) :=
    Nat.ordProj_le l hKg0
  rw [hWc, Nat.factorization_mul hR0 hK0, Finsupp.add_apply, pow_add, hvK]
  exact Nat.mul_le_mul hR (hKl.trans hA)

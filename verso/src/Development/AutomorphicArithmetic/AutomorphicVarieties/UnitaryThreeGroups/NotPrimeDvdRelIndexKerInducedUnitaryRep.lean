import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

/- English proof (translation)
Introduce `l _ k _ _ _ hl2 Γ _ η Ψ I`. Use `haveI := Fintype.ofFinite k`. Establish `hp : l.Prime` using `Fact.out`. Take `⟨n, -, hcard⟩` from `FiniteField.card k l`. Set `φ : Γ →* kˣ × ℤˣ` to `Ψ.prod η`.

Set `ψ : kˣ × ℤˣ →* GG 3 k` to `r0 (MonoidHom.snd kˣ ℤˣ) (MonoidHom.fst kˣ ℤˣ)`. Establish `hle : (φ.domRestrict I).ker ≤ ((r0 η Ψ).domRestrict I).ker`. Introduce `g hg`. Rewrite `hg`, the goal using `[MonoidHom.mem_ker]`. Use `show ψ (φ.domRestrict I g) = 1`.

Rewrite using `[hg, map_one]`. Establish `h1 : (I ⊓ (r0 η Ψ).ker).relIndex I ∣ (φ.domRestrict I).ker.index`. Rewrite using `[inf_comm, Subgroup.inf_relIndex_right, Subgroup.relIndex, ← MonoidHom.ker_restrict]`. Conclude with `Subgroup.index_dvd_of_le hle`. Establish `h2 : (φ.domRestrict I).ker.index ∣ (Nat.card k - 1) * 2`.

Rewrite using `[Subgroup.index_ker]`. Establish `hd` using `Subgroup.card_subgroup_dvd_card (φ.domRestrict I).range`. Rewrite `hd` using `[Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int]`. Then use the resulting hypothesis. Rewrite `h2` using `[Nat.card_eq_fintype_card, hcard]`. Introduce `hdvd`.

Establish `h3` using `dvd_trans hdvd (dvd_trans h1 h2)`. Break down `(Nat.Prime.dvd_mul hp).mp h3 with h4 | h4` into its components or cases. Establish `h5 : l ∣ l ^ (n : ℕ)` using `dvd_pow_self l n.ne_zero`. Establish `hpos : 1 ≤ l ^ (n : ℕ)` using `Nat.one_le_pow _ _ hp.pos`. Establish `he : l ^ (n : ℕ) = (l ^ (n : ℕ) - 1) + 1` using `by omega`.

Rewrite `h5` using `[he]`. Establish `h6` using `(Nat.dvd_add_right h4).mp h5`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.mp h6)`. Establish `h7` using `Nat.le_of_dvd (by norm_num) h4`. Establish `h8` using `hp.two_le`.

Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.not_prime_dvd_relIndex_ker_inducedUnitaryRep :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l], l ≠ 2 → ∀ {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* kˣ) (I : Subgroup Γ),
          ¬ l ∣ (I ⊓ (r0 η Ψ).ker).relIndex I := by
  intro l _ k _ _ _ hl2 Γ _ η Ψ I
  haveI := Fintype.ofFinite k
  have hp : l.Prime := Fact.out
  obtain ⟨n, -, hcard⟩ := FiniteField.card k l
  let φ : Γ →* kˣ × ℤˣ := Ψ.prod η
  let ψ : kˣ × ℤˣ →* GG 3 k := r0 (MonoidHom.snd kˣ ℤˣ) (MonoidHom.fst kˣ ℤˣ)
  have hle : (φ.domRestrict I).ker ≤ ((r0 η Ψ).domRestrict I).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    show ψ (φ.domRestrict I g) = 1
    rw [hg, map_one]
  have h1 : (I ⊓ (r0 η Ψ).ker).relIndex I ∣ (φ.domRestrict I).ker.index := by
    rw [inf_comm, Subgroup.inf_relIndex_right, Subgroup.relIndex, ← MonoidHom.ker_restrict]
    exact Subgroup.index_dvd_of_le hle
  have h2 : (φ.domRestrict I).ker.index ∣ (Nat.card k - 1) * 2 := by
    rw [Subgroup.index_ker]
    have hd := Subgroup.card_subgroup_dvd_card (φ.domRestrict I).range
    rwa [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card (α := ℤˣ),
      Fintype.card_units_int] at hd
  rw [Nat.card_eq_fintype_card, hcard] at h2
  intro hdvd
  have h3 := dvd_trans hdvd (dvd_trans h1 h2)
  rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
  · have h5 : l ∣ l ^ (n : ℕ) := dvd_pow_self l n.ne_zero
    have hpos : 1 ≤ l ^ (n : ℕ) := Nat.one_le_pow _ _ hp.pos
    have he : l ^ (n : ℕ) = (l ^ (n : ℕ) - 1) + 1 := by omega
    rw [he] at h5
    have h6 := (Nat.dvd_add_right h4).mp h5
    exact hp.one_lt.ne' (Nat.dvd_one.mp h6)
  · have h7 := Nat.le_of_dvd (by norm_num) h4
    have h8 := hp.two_le
    omega

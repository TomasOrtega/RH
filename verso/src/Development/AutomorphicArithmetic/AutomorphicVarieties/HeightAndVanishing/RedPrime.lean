import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PartModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SignLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.EigV
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.VLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Introduce `E _ _ _ N _ H hH l _ hl2 hlH c _ Ω' _ _ _ D Ω _ _ _ e he T hT`. Use `haveI := c.dvr`. Use `haveI := c.fin`. Take `⟨σ, hσ, hplus, -⟩` from `Chr.partModel E N H hH l c.O Ω' D Ω e`. Use `haveI hroots : HasEnoughRootsOfUnity c.O (Monoid.exponent ((ZMod N)ˣ ⧸ H)) := by`.

Establish `hdvd : Monoid.exponent ((ZMod N)ˣ ⧸ H) ∣ Nat.totient N`. Use `Group.exponent_dvd_nat_card.trans ?_` and prove the remaining obligations. Rewrite using `[← Subgroup.index_eq_card, ← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]`. Conclude with `Subgroup.index_dvd_card H`. Conclude with `HasEnoughRootsOfUnity.of_dvd c.O hdvd`.

Rewrite using `[hplus]`. Use `(Chr.signLe Ω N H l c.O hl2 e e σ hσ T (by rw [hT])).trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun χ hχ => ?_` and prove the remaining obligations. Establish `hχ' : χ ∈ Chr.evenSet c.O H e`. Establish `: χ ∈ (T : Set _)` using `hχ`.

Rewrite `this` using `[hT]`. Then use the resulting hypothesis. Establish `hker : H ≤ (MulChar.toUnitHom χ).ker` using `hχ'.1`. Take `⟨hopen, -⟩` from `Chr.clsFacts ℚ Ω N`. Establish `hsurj` using `(Chr.clsOnto Ω N).1`. Establish `hUopen : IsOpen ((Chr.levH ℚ Ω H : Subgroup (G ℚ Ω)) : Set (G ℚ Ω))`.

Use `Subgroup.isOpen_mono ?_ hopen` and prove the remaining obligations. Introduce `g hg`. Use `show Chr.cls ℚ Ω N g ∈ H`. Rewrite using `[MonoidHom.mem_ker.mp hg]`. Conclude with `H.one_mem`.

Establish `hUker : Chr.levH ℚ Ω H ≤ (Chr.dirG ℚ Ω χ).ker`. Introduce `g hg`. Conclude with `hker hg`. Establish `hidx : (Chr.levH ℚ Ω H).index = H.index` using `Subgroup.index_comap_of_surjective H hsurj`. Establish `hHidx : H.index ≠ 0` using `Subgroup.index_ne_zero_of_finite`.

Rewrite using `[Chr.eigV ℚ Ω l c.O e (Chr.dirG ℚ Ω χ) (Chr.levH ℚ Ω H) hUopen hUker (by rwa [hidx])]`. Establish `hψopen : IsOpen ((Chr.dirG ℚ Ω χ).ker : Set (G ℚ Ω))` using `Subgroup.isOpen_mono hUker hUopen`. Establish `hpow : Chr.dirG ℚ Ω χ ^ H.index = 1`. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Establish `hm : (Chr.cls ℚ Ω N g) ^ H.index ∈ H` using `Subgroup.pow_index_mem H _`.

Use `hker hm` as an intermediate fact. Rewrite `this` using `[MonoidHom.mem_ker, map_pow]`. Rewrite using `[MonoidHom.pow_apply, MonoidHom.one_apply]`. Conclude with `this`. Conclude with `((Chr.vLe Ω l c.O N e H.index (Chr.dirG ℚ Ω χ) (NeZero.ne N) he hHidx hψopen hpow).2 hlH)`.
-/
theorem UpperTheory.V.HV.redPrime :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), Chr.HasLevel E N H → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ H.index →
      ∀ (c : Coef l) [HasEnoughRootsOfUnity c.O (Nat.totient N)] (Ω' : Type) [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω'] (D : LData E Ω' l)
        (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (e : ℕ), e ≠ 0 → ∀ T : Finset (DirichletCharacter c.O N), (T : Set _) = Chr.evenSet c.O H e →
        plusLen D e * eO l c.O ≤ ∑ ψ ∈ T, Vlen Ω c e ψ := by
  intro E _ _ _ N _ H hH l _ hl2 hlH c _ Ω' _ _ _ D Ω _ _ _ e he T hT
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨σ, hσ, hplus, -⟩ := Chr.partModel E N H hH l c.O Ω' D Ω e
  haveI hroots : HasEnoughRootsOfUnity c.O (Monoid.exponent ((ZMod N)ˣ ⧸ H)) := by
    have hdvd : Monoid.exponent ((ZMod N)ˣ ⧸ H) ∣ Nat.totient N := by
      refine Group.exponent_dvd_nat_card.trans ?_
      rw [← Subgroup.index_eq_card, ← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
      exact Subgroup.index_dvd_card H
    exact HasEnoughRootsOfUnity.of_dvd c.O hdvd
  rw [hplus]
  refine (Chr.signLe Ω N H l c.O hl2 e e σ hσ T (by rw [hT])).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have hχ' : χ ∈ Chr.evenSet c.O H e := by
    have : χ ∈ (T : Set _) := hχ
    rwa [hT] at this
  have hker : H ≤ (MulChar.toUnitHom χ).ker := hχ'.1
  obtain ⟨hopen, -⟩ := Chr.clsFacts ℚ Ω N
  have hsurj := (Chr.clsOnto Ω N).1
  have hUopen : IsOpen ((Chr.levH ℚ Ω H : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono ?_ hopen
    intro g hg
    show Chr.cls ℚ Ω N g ∈ H
    rw [MonoidHom.mem_ker.mp hg]
    exact H.one_mem
  have hUker : Chr.levH ℚ Ω H ≤ (Chr.dirG ℚ Ω χ).ker := by
    intro g hg
    exact hker hg
  have hidx : (Chr.levH ℚ Ω H).index = H.index :=
    Subgroup.index_comap_of_surjective H hsurj
  have hHidx : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [Chr.eigV ℚ Ω l c.O e (Chr.dirG ℚ Ω χ) (Chr.levH ℚ Ω H) hUopen hUker (by rwa [hidx])]
  have hψopen : IsOpen ((Chr.dirG ℚ Ω χ).ker : Set (G ℚ Ω)) :=
    Subgroup.isOpen_mono hUker hUopen
  have hpow : Chr.dirG ℚ Ω χ ^ H.index = 1 := by
    refine MonoidHom.ext fun g => ?_
    have hm : (Chr.cls ℚ Ω N g) ^ H.index ∈ H := Subgroup.pow_index_mem H _
    have := hker hm
    rw [MonoidHom.mem_ker, map_pow] at this
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    exact this
  exact ((Chr.vLe Ω l c.O N e H.index (Chr.dirG ℚ Ω χ) (NeZero.ne N) he hHidx hψopen hpow).2 hlH)

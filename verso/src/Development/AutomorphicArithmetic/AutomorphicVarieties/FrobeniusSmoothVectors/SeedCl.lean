import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScStrip
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScDisc
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SoCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScTeich
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScCong

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
Introduce `s hs` and use `hχ s fun ζ hζ => hs ζ (by obtain ⟨k, rfl⟩ := h rw [pow_mul, hζ, one_pow])`.
-/
private theorem km_mono {Ω C : Type} [Field Ω] [CharZero Ω] [Monoid C] {m n : ℕ} (h : m ∣ n) {χ : G ℚ Ω →* C}
    (hχ : Af.KillsMu m χ) : Af.KillsMu n χ := fun s hs => hχ s fun ζ hζ => hs ζ (by
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul, hζ, one_pow])

/- English proof (translation)
Assemble the required witnesses or components as `⟨hχ, fun s hs => hχ s fun ζ hζ => by rw [hs ζ hζ, pow_eq_pow_mod w hζ, hw, ← pow_eq_pow_mod 1 hζ, pow_one]⟩`.
-/
private theorem split_of {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] {N w : ℕ} (hw : w ≡ 1 [MOD N])
    {χ : G ℚ Ω →* (Qbar l)ˣ} (hχ : Af.KillsMu N χ) : Sd.SplitAt N w χ :=
  ⟨hχ, fun s hs => hχ s fun ζ hζ => by
    rw [hs ζ hζ, pow_eq_pow_mod w hζ, hw, ← pow_eq_pow_mod 1 hζ, pow_one]⟩

/- English proof (translation)
Introduce `Ω _ _ _ l _ c _ η Ψ σ B M Hb hG`. Establish `hlp : l.Prime` using `Fact.out`. Take `⟨a, hηa, hΨa⟩` from `hG.cyc`. Take `⟨j, hj⟩` from `hG.Ψ_l`. Take `⟨D, δ, hD, -, hδ, hηδ⟩` from `hG.quad`.

Take `⟨K, iK, nK, aK, hK2, hKc, hKη⟩` from `sc_quad Ω η D δ hD hδ hηδ`. Take `⟨T, hT, hTa⟩` from `sc_teich Ω l c hG.fin`. Establish `hM : M ^ a * l ≠ 0` using `mul_ne_zero (pow_ne_zero _ hG.M_ne) hlp.ne_zero`. Take `⟨r, N, hlN, hN⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hM l hlp.one_lt.ne'`. Establish `hN0 : N ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hM (by rw [hN, mul_zero])`. Set `φ : G ℚ Ω →* (ResidueField c.O)ˣ` to `barChar c.O Ψ * (omO Ω l c.O ^ j)⁻¹`. Set `χ' : G ℚ Ω →* (Qbar l)ˣ` to `T.comp φ`. Set `η' : G ℚ Ω →* (Qbar l)ˣ` to `(Units.map (Int.castRingHom (Qbar l)).toMonoidHom).comp η`.

Establish `hφ : ∀ s, φ s = barChar c.O Ψ s * ((omO Ω l c.O) s ^ j)⁻¹` using `fun s => rfl`. Establish `hχ : ∀ s, χ' s = T (φ s)` using `fun s => rfl`. Establish `hη'ker : η'.ker = η.ker`. Use extensionality with `s`. Simplify using `only [MonoidHom.mem_ker]`.

Conclude with `map_eq_one_iff _ (Units.map_injective (f := (Int.castRingHom (Qbar l)).toMonoidHom) Int.cast_injective)`. Establish `hφK : Af.KillsMu (M ^ a * l) φ`. Introduce `s hs`. Establish `h1 : barChar c.O Ψ s = 1` using `km_mono (dvd_mul_right _ _) hΨa s hs`. Establish `h2 : omO Ω l c.O s = 1` using `km_mono (dvd_mul_left _ _) (sc_om Ω l c.O).1 s hs`.

Rewrite using `[hφ, h1, h2, one_pow, inv_one, mul_one]`. Establish `hχK : Af.KillsMu (M ^ a * l) χ'`. Introduce `s hs`. Rewrite using `[hχ, hφK s hs, map_one]`. Establish `hη'K : Af.KillsMu (M ^ a * l) η'`.

Introduce `s hs`. Establish `h1 : η s = 1` using `km_mono (dvd_mul_right _ _) hηa s hs`. Use `show Units.map _ (η s) = 1`. Rewrite using `[h1, map_one]`. Establish `hχN : Af.KillsMu N χ'`.

Use `sc_strip Ω l _ χ' r N hN0 hlN (hN ▸ hχK) B hG.over_l ?_` and prove the remaining obligations. Introduce `s hs`. Rewrite using `[MonoidHom.mem_ker, hχ, hφ, hj B hG.over_l s hs, mul_inv_cancel, map_one]`. Establish `hη'N : Af.KillsMu N η'`. Use `sc_strip Ω l _ η' r N hN0 hlN (hN ▸ hη'K) B hG.over_l ?_` and prove the remaining obligations.

Rewrite using `[hη'ker]`. Conclude with `hG.η_l B hG.over_l`. Establish `hT1 : T (-1) = -1`. Establish `hne : (-1 : (ResidueField c.O)ˣ) ≠ 1`. Introduce `h`.

Establish `h' : (-1 : ResidueField c.O) = 1`. Simplify using `using congrArg (fun u : (ResidueField c.O)ˣ => (u : ResidueField c.O)) h`. Rewrite `h'` using `[neg_one_eq_one_iff, ringChar.eq (ResidueField c.O) l]`. Conclude with `hG.odd h'`. Establish `hsq : ((T (-1) : (Qbar l)ˣ) : Qbar l) * (T (-1) : Qbar l) = 1`.

Rewrite using `[← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]`. Break down `mul_self_eq_one_iff.1 hsq with h | h` into its components or cases. Conclude with `absurd (hT (by rw [map_one]; exact Units.ext h)) hne`. Conclude with `Units.ext (by rw [h, Units.val_neg, Units.val_one])`. Establish `happ : ∀ s, (GlobalTheory.GalOfCusp.cycBar ℚ Ω l ^ j * χ') s = (GlobalTheory.GalOfCusp.cycBar ℚ Ω l) s ^ j * T ((Units.map ↑(residue c.O)) (Ψ s) * ((omO Ω l c.O) s ^ j)⁻¹)` using `fun s => rfl`.

Establish `hord : ¬ l ∣ orderOf χ'` using `by classical haveI := Fintype.ofFinite (ResidueField c.O)`. Establish `hpow : χ' ^ Fintype.card (ResidueField c.O)ˣ = 1` using `MonoidHom.ext fun s => by show (T (φ s)) ^ Fintype.card (ResidueField c.O)ˣ = 1`. Rewrite using `[← map_pow, pow_card_eq_one, map_one]`. Introduce `hd`. Establish `hd2` using `hd.trans (orderOf_dvd_of_pow_eq_one hpow)`.

Take `⟨n, -, hcard⟩` from `FiniteField.card (ResidueField c.O) l`. Rewrite `hd2` using `[Fintype.card_units, hcard]`. Establish `hl1 : l ∣ l ^ (n : ℕ)` using `dvd_pow_self l n.ne_zero`. Establish `hpos : 1 ≤ l ^ (n : ℕ)` using `Nat.one_le_pow _ _ hlp.pos`. Establish `h3 : l ∣ (l ^ (n : ℕ) - 1) + 1`.

Rewrite using `[Nat.sub_add_cancel hpos]`. Conclude with `hl1`. Conclude with `hlp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hd2).1 h3))`. Use `⟨N, hN0, ?_⟩` and prove the remaining obligations. Introduce `L _ _ _ _ w hLab hLgal hw hwQ hLth hs0`.

Take `⟨s0, hs0L, hs0⟩` from `hs0`. Take `⟨θ, hθker, hθ1, hθl, hθw⟩` from `sc_theta Ω l w hw.prime hw.one`. Establish `hwN : ¬ w ∣ N`. Introduce `hd`. Establish `hd' : w ∣ M ^ a * l` using `hN ▸ dvd_mul_of_dvd_right hd _`.

Break down `(Nat.Prime.dvd_mul hw.prime).1 hd' with h | h` into its components or cases. Conclude with `hw.cop (hw.prime.dvd_of_dvd_pow h)`. Establish `hwl` using `(Nat.prime_dvd_prime_iff_eq hw.prime hlp).1 h`. Establish `h1 : w % l = 1 % l` using `hw.one`. Rewrite `h1` using `[hwl, Nat.mod_self, Nat.mod_eq_of_lt hlp.one_lt]`.

Conclude with `zero_ne_one h1`. Establish `hLK : galOf ℚ L Ω ≤ galOf ℚ K Ω`. Rewrite using `[hKη, hLgal]`. Conclude with `inf_le_right`. Use `⟨K, iK, nK, aK, N, w, χ', η', θ, j, ?_, ?_, hord, fun s => rfl, fun s => happ s ▸ hTa (Ψ s) j s, ?_⟩` and prove the remaining obligations.

Use `⟨hG.cc, ⟨hG.odd, Nat.pos_of_ne_zero hN0, hlN, hw.prime, hwN, hθ1, hθl, hθw⟩, hK2, hKc, hLab, hLK, by rw [hη'ker, hKη], split_of hwQ hη'N, split_of hwQ hχN, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hθker, hLgal]`. Conclude with `inf_le_left.trans hLth`. Rewrite using `[hχ, hφ, hG.even, (sc_om Ω l c.O).2 σ hG.cc, one_mul, ← inv_pow, inv_neg_one, map_pow, hT1]`. Use `⟨s0, hs0L, fun hc => hs0 ?_⟩` and prove the remaining obligations.

Conclude with `sc_cong l c (Ψ s0) _ (happ s0 ▸ hTa (Ψ s0) j s0) hc`. Introduce `heq`. Apply `hG.g4` to reduce the goal to its premises. Introduce `s hs`. Rewrite `hs` using `[Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]`.

Establish `h1 : χ' s = 1`. Rewrite using `[hχ, hφ, hs.1, hs.2, one_pow, inv_one, mul_one, map_one]`. Rewrite `h1` using `[heq]`. Rewrite using `[← hη'ker]`. Conclude with `h1`.

Conclude with `sc_disc Ω l K hK2 (fun B' hB' => hKη ▸ hG.η_l B' hB')`.
-/
theorem UpperTheory.V.Fr.seed_cl :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∃ Q : ℕ, Q ≠ 0 ∧ ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (w : ℕ), IsAbelianGalois ℚ L → galOf ℚ L Ω = upl Ω L ⊓ η.ker → FrobeniusWitnessPrime l η Ψ M w → w ≡ 1 [MOD Q] → upl Ω L ≤ Hth Ω l w → (∃ s ∈ galOf ℚ L Ω, barChar c.O Ψ s ^ 2 ≠ 1) → SeedClause c η Ψ σ L := by
  intro Ω _ _ _ l _ c _ η Ψ σ B M Hb hG
  have hlp : l.Prime := Fact.out
  obtain ⟨a, hηa, hΨa⟩ := hG.cyc
  obtain ⟨j, hj⟩ := hG.Ψ_l
  obtain ⟨D, δ, hD, -, hδ, hηδ⟩ := hG.quad
  obtain ⟨K, iK, nK, aK, hK2, hKc, hKη⟩ := sc_quad Ω η D δ hD hδ hηδ
  obtain ⟨T, hT, hTa⟩ := sc_teich Ω l c hG.fin
  have hM : M ^ a * l ≠ 0 := mul_ne_zero (pow_ne_zero _ hG.M_ne) hlp.ne_zero
  obtain ⟨r, N, hlN, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM l hlp.one_lt.ne'
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hM (by rw [hN, mul_zero])
  let φ : G ℚ Ω →* (ResidueField c.O)ˣ := barChar c.O Ψ * (omO Ω l c.O ^ j)⁻¹
  let χ' : G ℚ Ω →* (Qbar l)ˣ := T.comp φ
  let η' : G ℚ Ω →* (Qbar l)ˣ := (Units.map (Int.castRingHom (Qbar l)).toMonoidHom).comp η
  have hφ : ∀ s, φ s = barChar c.O Ψ s * ((omO Ω l c.O) s ^ j)⁻¹ := fun s => rfl
  have hχ : ∀ s, χ' s = T (φ s) := fun s => rfl
  have hη'ker : η'.ker = η.ker := by
    ext s
    simp only [MonoidHom.mem_ker]
    exact map_eq_one_iff _ (Units.map_injective (f := (Int.castRingHom (Qbar l)).toMonoidHom) Int.cast_injective)
  have hφK : Af.KillsMu (M ^ a * l) φ := by
    intro s hs
    have h1 : barChar c.O Ψ s = 1 := km_mono (dvd_mul_right _ _) hΨa s hs
    have h2 : omO Ω l c.O s = 1 := km_mono (dvd_mul_left _ _) (sc_om Ω l c.O).1 s hs
    rw [hφ, h1, h2, one_pow, inv_one, mul_one]
  have hχK : Af.KillsMu (M ^ a * l) χ' := by
    intro s hs
    rw [hχ, hφK s hs, map_one]
  have hη'K : Af.KillsMu (M ^ a * l) η' := by
    intro s hs
    have h1 : η s = 1 := km_mono (dvd_mul_right _ _) hηa s hs
    show Units.map _ (η s) = 1
    rw [h1, map_one]
  have hχN : Af.KillsMu N χ' := by
    refine sc_strip Ω l _ χ' r N hN0 hlN (hN ▸ hχK) B hG.over_l ?_
    intro s hs
    rw [MonoidHom.mem_ker, hχ, hφ, hj B hG.over_l s hs, mul_inv_cancel, map_one]
  have hη'N : Af.KillsMu N η' := by
    refine sc_strip Ω l _ η' r N hN0 hlN (hN ▸ hη'K) B hG.over_l ?_
    rw [hη'ker]
    exact hG.η_l B hG.over_l
  have hT1 : T (-1) = -1 := by
    have hne : (-1 : (ResidueField c.O)ˣ) ≠ 1 := by
      intro h
      have h' : (-1 : ResidueField c.O) = 1 := by
        simpa using congrArg (fun u : (ResidueField c.O)ˣ => (u : ResidueField c.O)) h
      rw [neg_one_eq_one_iff, ringChar.eq (ResidueField c.O) l] at h'
      exact hG.odd h'
    have hsq : ((T (-1) : (Qbar l)ˣ) : Qbar l) * (T (-1) : Qbar l) = 1 := by
      rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exact absurd (hT (by rw [map_one]; exact Units.ext h)) hne
    · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
  have happ : ∀ s, (GlobalTheory.GalOfCusp.cycBar ℚ Ω l ^ j * χ') s =
      (GlobalTheory.GalOfCusp.cycBar ℚ Ω l) s ^ j * T ((Units.map ↑(residue c.O)) (Ψ s) * ((omO Ω l c.O) s ^ j)⁻¹) :=
    fun s => rfl
  have hord : ¬ l ∣ orderOf χ' := by
    classical
    haveI := Fintype.ofFinite (ResidueField c.O)
    have hpow : χ' ^ Fintype.card (ResidueField c.O)ˣ = 1 := MonoidHom.ext fun s => by
      show (T (φ s)) ^ Fintype.card (ResidueField c.O)ˣ = 1
      rw [← map_pow, pow_card_eq_one, map_one]
    intro hd
    have hd2 := hd.trans (orderOf_dvd_of_pow_eq_one hpow)
    obtain ⟨n, -, hcard⟩ := FiniteField.card (ResidueField c.O) l
    rw [Fintype.card_units, hcard] at hd2
    have hl1 : l ∣ l ^ (n : ℕ) := dvd_pow_self l n.ne_zero
    have hpos : 1 ≤ l ^ (n : ℕ) := Nat.one_le_pow _ _ hlp.pos
    have h3 : l ∣ (l ^ (n : ℕ) - 1) + 1 := by
      rw [Nat.sub_add_cancel hpos]
      exact hl1
    exact hlp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hd2).1 h3))
  refine ⟨N, hN0, ?_⟩
  intro L _ _ _ _ w hLab hLgal hw hwQ hLth hs0
  obtain ⟨s0, hs0L, hs0⟩ := hs0
  obtain ⟨θ, hθker, hθ1, hθl, hθw⟩ := sc_theta Ω l w hw.prime hw.one
  have hwN : ¬ w ∣ N := by
    intro hd
    have hd' : w ∣ M ^ a * l := hN ▸ dvd_mul_of_dvd_right hd _
    rcases (Nat.Prime.dvd_mul hw.prime).1 hd' with h | h
    · exact hw.cop (hw.prime.dvd_of_dvd_pow h)
    · have hwl := (Nat.prime_dvd_prime_iff_eq hw.prime hlp).1 h
      have h1 : w % l = 1 % l := hw.one
      rw [hwl, Nat.mod_self, Nat.mod_eq_of_lt hlp.one_lt] at h1
      exact zero_ne_one h1
  have hLK : galOf ℚ L Ω ≤ galOf ℚ K Ω := by
    rw [hKη, hLgal]
    exact inf_le_right
  refine ⟨K, iK, nK, aK, N, w, χ', η', θ, j, ?_, ?_, hord, fun s => rfl, fun s => happ s ▸ hTa (Ψ s) j s, ?_⟩
  · refine ⟨hG.cc, ⟨hG.odd, Nat.pos_of_ne_zero hN0, hlN, hw.prime, hwN, hθ1, hθl, hθw⟩, hK2, hKc, hLab, hLK,
      by rw [hη'ker, hKη], split_of hwQ hη'N, split_of hwQ hχN, ?_, ?_, ?_⟩
    · rw [hθker, hLgal]
      exact inf_le_left.trans hLth
    · rw [hχ, hφ, hG.even, (sc_om Ω l c.O).2 σ hG.cc, one_mul, ← inv_pow, inv_neg_one, map_pow, hT1]
    · refine ⟨s0, hs0L, fun hc => hs0 ?_⟩
      exact sc_cong l c (Ψ s0) _ (happ s0 ▸ hTa (Ψ s0) j s0) hc
  · intro heq
    apply hG.g4
    intro s hs
    rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hs
    have h1 : χ' s = 1 := by
      rw [hχ, hφ, hs.1, hs.2, one_pow, inv_one, mul_one, map_one]
    rw [heq] at h1
    rw [← hη'ker]
    exact h1
  · exact sc_disc Ω l K hK2 (fun B' hB' => hKη ▸ hG.η_l B' hB')

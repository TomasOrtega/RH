import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Establish `hcl : Nat.Coprime l (ordCompl[l] N)` using `Nat.coprime_ordCompl hl hN`. Establish `hcop : Nat.Coprime (ordCompl[l] N) (ordProj[l] N)` using `(Nat.Coprime.pow_left _ hcl).symm`. Take `⟨k, hk1, hk2⟩` from `Nat.chineseRemainder hcop l 1`. Establish `hc1 : Nat.Coprime k (ordCompl[l] N)`. Unfold `Nat.Coprime`.

Rewrite using `[Nat.ModEq.gcd_eq hk1]`. Conclude with `hcl`. Establish `hc2 : Nat.Coprime k (ordProj[l] N)`. Unfold `Nat.Coprime`. Rewrite using `[Nat.ModEq.gcd_eq hk2]`.

Simplify using the standard rewrite rules. Establish `hco : Nat.Coprime k N`. Establish `h` using `Nat.Coprime.mul_right hc2 hc1`. Rewrite `h` using `[Nat.ordProj_mul_ordCompl_eq_self]`. Then use the resulting hypothesis. Use `⟨ZMod.unitOfCoprime k hco, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[ZMod.coe_unitOfCoprime, ZMod.val_natCast]`. Conclude with `((Nat.mod_modEq k N).of_dvd (Nat.ordCompl_dvd N l)).trans hk1`. Rewrite using `[ZMod.coe_unitOfCoprime, ZMod.val_natCast]`. Conclude with `((Nat.mod_modEq k N).of_dvd (Nat.ordProj_dvd N l)).trans hk2`.
-/
private theorem exists_unit {N l : ℕ} (hN : N ≠ 0) (hl : l.Prime) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ l [MOD ordCompl[l] N] ∧ (u : ZMod N).val ≡ 1 [MOD ordProj[l] N] := by
  have hcl : Nat.Coprime l (ordCompl[l] N) := Nat.coprime_ordCompl hl hN
  have hcop : Nat.Coprime (ordCompl[l] N) (ordProj[l] N) := (Nat.Coprime.pow_left _ hcl).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop l 1
  have hc1 : Nat.Coprime k (ordCompl[l] N) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hk1]
    exact hcl
  have hc2 : Nat.Coprime k (ordProj[l] N) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hk2]
    simp
  have hco : Nat.Coprime k N := by
    have h := Nat.Coprime.mul_right hc2 hc1
    rwa [Nat.ordProj_mul_ordCompl_eq_self] at h
  refine ⟨ZMod.unitOfCoprime k hco, ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq k N).of_dvd (Nat.ordCompl_dvd N l)).trans hk1
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq k N).of_dvd (Nat.ordProj_dvd N l)).trans hk2

/- English proof (translation)
Establish `hcop : Nat.Coprime (ordProj[l] N) (ordCompl[l] N)` using `Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hN)`. Establish `h` using `(Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, h1⟩`. Rewrite `h` using `[Nat.ordProj_mul_ordCompl_eq_self]`. Use `haveI : NeZero N := ⟨hN⟩`. Apply `Units.ext` to reduce the goal to its premises.

Apply `ZMod.val_injective` to reduce the goal to its premises. Establish `hu` using `ZMod.val_lt (u : ZMod N)`. Establish `hv` using `ZMod.val_lt (v : ZMod N)`. Unfold `Nat.ModEq at h`. Rewrite `h` using `[Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv]`. Then use the resulting hypothesis.
-/
private theorem unit_unique {N l : ℕ} (hN : N ≠ 0) (hl : l.Prime) {u v : (ZMod N)ˣ}
    (h1 : (u : ZMod N).val ≡ (v : ZMod N).val [MOD ordCompl[l] N])
    (h2 : (u : ZMod N).val ≡ (v : ZMod N).val [MOD ordProj[l] N]) : u = v := by
  have hcop : Nat.Coprime (ordProj[l] N) (ordCompl[l] N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hN)
  have h := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, h1⟩
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h
  haveI : NeZero N := ⟨hN⟩
  apply Units.ext
  apply ZMod.val_injective
  have hu := ZMod.val_lt (u : ZMod N)
  have hv := ZMod.val_lt (v : ZMod N)
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at h

/- English proof (translation)
Rewrite using `[ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff]`.
-/
private theorem val_iff {N f : ℕ} [NeZero N] (hf : f ∣ N) (u : (ZMod N)ˣ) (a : ℕ) :
    (u : ZMod N).val ≡ a [MOD f] ↔ ((ZMod.unitsMap hf u : (ZMod f)ˣ) : ZMod f) = (a : ZMod f) := by
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff]

/- English proof (translation)
Introduce `φ H l hl`. Use `haveI : NeZero H.condN := ⟨H.condN_ne_zero⟩`. Establish `hN : H.condN ≠ 0` using `H.condN_ne_zero`. Establish `hex` using `exists_unit hN hl`. Establish `hart : H.artL l = H.art hex.choose`.

Unfold `UpperTheory.HF.Formalism.HC.HostRaw.artL`. Rewrite using `[dif_pos hex]`. Take `⟨hc1, hc2⟩` from `hex.choose_spec`. Establish `part2 : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] → (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] → H.art u = H.artL l`. Introduce `u hu1 hu2`.

Rewrite using `[hart, unit_unique hN hl (hu1.trans hc1.symm) (hu2.trans hc2.symm)]`. Use `⟨⟨hex.choose, hc1, hc2, hart⟩, part2, ?_⟩` and prove the remaining obligations. Establish `hA : ordCompl[l] H.condN ∣ H.condN` using `Nat.ordCompl_dvd _ _`. Use `haveI : NeZero (ordCompl[l] H.condN) := ⟨fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hA))⟩`. Take `⟨lA, hlA⟩ : ∃ w : (ZMod (ordCompl[l] H.condN))ˣ, (w : ZMod (ordCompl[l] H.condN)) = (l : ZMod _)` from `⟨ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl hN), ZMod.coe_unitOfCoprime _ _⟩`.

Establish `key : ∀ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ↔ ZMod.unitsMap hA u = lA ^ k`. Introduce `u k`. Rewrite using `[val_iff hA u (l ^ k), Units.ext_iff, Units.val_pow_eq_pow_val, hlA, Nat.cast_pow]`. Set `T : Subgroup φ.GG` to `((Subgroup.zpowers lA).comap (ZMod.unitsMap hA)).map H.art`. Establish `memT : ∀ g, g ∈ T ↔ ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ g = H.art u`.

Introduce `g`. Simplify using `only [T, Subgroup.mem_map, Subgroup.mem_comap, ← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, ⟨k, hk⟩, rfl⟩`. Conclude with `⟨u, k, (key u k).mpr hk.symm, rfl⟩`.

Introduce and unpack `⟨u, k, hk, rfl⟩`. Conclude with `⟨u, ⟨k, ((key u k).mp hk).symm⟩, rfl⟩`. Establish `hle1 : UpperTheory.HF.Formalism.HC.HostRaw.decG H l ≤ T`. Unfold `UpperTheory.HF.Formalism.HC.HostRaw.decG`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Introduce `g hg`. Take `⟨u, hu, rfl⟩` from `(UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l g).mp hg`. Conclude with `(memT _).mpr ⟨u, 0, by simpa using hu, rfl⟩`. Rewrite using `[Subgroup.zpowers_le, hart]`. Conclude with `(memT _).mpr ⟨hex.choose, 1, by simpa using hc1, rfl⟩`.

Establish `hu1 : ZMod.unitsMap hA hex.choose = lA`. Establish `h` using `(key hex.choose 1).mp (by simpa using hc1)`. Simplify using `using h`. Establish `hle2 : T ≤ UpperTheory.HF.Formalism.HC.HostRaw.decG H l`. Introduce `g hg`.

Take `⟨u, k, hk, rfl⟩` from `(memT g).mp hg`. Establish `hw : ((u * (hex.choose ^ k)⁻¹ : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN]`. Establish `h` using `(key (u * (hex.choose ^ k)⁻¹) 0).mpr (by rw [map_mul, map_inv, map_pow, hu1, (key u k).mp hk]; simp)`. Simplify using `using h`. Establish `hmem : H.art (u * (hex.choose ^ k)⁻¹) ∈ UpperTheory.HF.Formalism.HC.HostRaw.inertG H l` using `(UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l _).mpr ⟨_, hw, rfl⟩`.

Establish `heq : H.art u = H.art (u * (hex.choose ^ k)⁻¹) * H.artL l ^ k`. Rewrite using `[hart, map_mul, map_inv, map_pow, inv_mul_cancel_right]`. Rewrite using `[heq]`. Unfold `UpperTheory.HF.Formalism.HC.HostRaw.decG`. Conclude with `Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem) (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)`.

Introduce `g`. Rewrite using `[show UpperTheory.HF.Formalism.HC.HostRaw.decG H l = T from le_antisymm hle1 hle2]`. Conclude with `memT g`.
-/
theorem UpperTheory.HF.artL_spec :
    ∀ {φ : Frame} (H : HostRaw φ) {l : ℕ}, l.Prime → (∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] ∧ H.artL l = H.art u) ∧ (∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] → (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] → H.art u = H.artL l) ∧ ∀ g : φ.GG, g ∈ H.decG l ↔ ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ g = H.art u := by
  intro φ H l hl
  haveI : NeZero H.condN := ⟨H.condN_ne_zero⟩
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  have hex := exists_unit hN hl
  have hart : H.artL l = H.art hex.choose := by
    unfold UpperTheory.HF.Formalism.HC.HostRaw.artL
    rw [dif_pos hex]
  obtain ⟨hc1, hc2⟩ := hex.choose_spec
  have part2 : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] →
      (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] → H.art u = H.artL l := by
    intro u hu1 hu2
    rw [hart, unit_unique hN hl (hu1.trans hc1.symm) (hu2.trans hc2.symm)]
  refine ⟨⟨hex.choose, hc1, hc2, hart⟩, part2, ?_⟩
  have hA : ordCompl[l] H.condN ∣ H.condN := Nat.ordCompl_dvd _ _
  haveI : NeZero (ordCompl[l] H.condN) :=
    ⟨fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hA))⟩
  obtain ⟨lA, hlA⟩ : ∃ w : (ZMod (ordCompl[l] H.condN))ˣ, (w : ZMod (ordCompl[l] H.condN)) = (l : ZMod _) :=
    ⟨ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl hN), ZMod.coe_unitOfCoprime _ _⟩
  have key : ∀ (u : (ZMod H.condN)ˣ) (k : ℕ),
      (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ↔ ZMod.unitsMap hA u = lA ^ k := by
    intro u k
    rw [val_iff hA u (l ^ k), Units.ext_iff, Units.val_pow_eq_pow_val, hlA, Nat.cast_pow]
  let T : Subgroup φ.GG := ((Subgroup.zpowers lA).comap (ZMod.unitsMap hA)).map H.art
  have memT : ∀ g, g ∈ T ↔ ∃ (u : (ZMod H.condN)ˣ) (k : ℕ),
      (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ g = H.art u := by
    intro g
    simp only [T, Subgroup.mem_map, Subgroup.mem_comap, ← mem_powers_iff_mem_zpowers,
      Submonoid.mem_powers_iff]
    constructor
    · rintro ⟨u, ⟨k, hk⟩, rfl⟩
      exact ⟨u, k, (key u k).mpr hk.symm, rfl⟩
    · rintro ⟨u, k, hk, rfl⟩
      exact ⟨u, ⟨k, ((key u k).mp hk).symm⟩, rfl⟩
  have hle1 : UpperTheory.HF.Formalism.HC.HostRaw.decG H l ≤ T := by
    unfold UpperTheory.HF.Formalism.HC.HostRaw.decG
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨u, hu, rfl⟩ := (UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l g).mp hg
      exact (memT _).mpr ⟨u, 0, by simpa using hu, rfl⟩
    · rw [Subgroup.zpowers_le, hart]
      exact (memT _).mpr ⟨hex.choose, 1, by simpa using hc1, rfl⟩
  have hu1 : ZMod.unitsMap hA hex.choose = lA := by
    have h := (key hex.choose 1).mp (by simpa using hc1)
    simpa using h
  have hle2 : T ≤ UpperTheory.HF.Formalism.HC.HostRaw.decG H l := by
    intro g hg
    obtain ⟨u, k, hk, rfl⟩ := (memT g).mp hg
    have hw : ((u * (hex.choose ^ k)⁻¹ : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1
        [MOD ordCompl[l] H.condN] := by
      have h := (key (u * (hex.choose ^ k)⁻¹) 0).mpr
        (by rw [map_mul, map_inv, map_pow, hu1, (key u k).mp hk]; simp)
      simpa using h
    have hmem : H.art (u * (hex.choose ^ k)⁻¹) ∈ UpperTheory.HF.Formalism.HC.HostRaw.inertG H l :=
      (UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l _).mpr ⟨_, hw, rfl⟩
    have heq : H.art u = H.art (u * (hex.choose ^ k)⁻¹) * H.artL l ^ k := by
      rw [hart, map_mul, map_inv, map_pow, inv_mul_cancel_right]
    rw [heq]
    unfold UpperTheory.HF.Formalism.HC.HostRaw.decG
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)
  intro g
  rw [show UpperTheory.HF.Formalism.HC.HostRaw.decG H l = T from le_antisymm hle1 hle2]
  exact memT g

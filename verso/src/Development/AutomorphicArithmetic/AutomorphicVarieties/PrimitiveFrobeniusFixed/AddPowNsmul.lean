import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.RadEqv
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ChebQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.QocEquiv
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AddPowNsmul

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Take `⟨a, ha, ha'⟩` from `SetLike.not_le_iff_exists.1 hA`. Take `⟨b, hb, hb'⟩` from `SetLike.not_le_iff_exists.1 hB`. Distinguish the cases in `h1 : a ∈ B`. Distinguish the cases in `h2 : b ∈ A`. Conclude with `⟨a * b, H.mul_mem ha hb, fun h => ha' ((A.mul_mem_cancel_right h2).1 h), fun h => hb' ((B.mul_mem_cancel_left h1).1 h)⟩`.

Conclude with `⟨b, hb, h2, hb'⟩`. Conclude with `⟨a, ha, ha', h1⟩`.
-/
private theorem two_sub {Γ : Type} [Group Γ] (H A B : Subgroup Γ) (hA : ¬ H ≤ A) (hB : ¬ H ≤ B) :
    ∃ x ∈ H, x ∉ A ∧ x ∉ B := by
  obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 hA
  obtain ⟨b, hb, hb'⟩ := SetLike.not_le_iff_exists.1 hB
  by_cases h1 : a ∈ B
  · by_cases h2 : b ∈ A
    · exact ⟨a * b, H.mul_mem ha hb, fun h => ha' ((A.mul_mem_cancel_right h2).1 h),
        fun h => hb' ((B.mul_mem_cancel_left h1).1 h)⟩
    · exact ⟨b, hb, h2, hb'⟩
  · exact ⟨a, ha, ha', h1⟩

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Establish `h : ∀ x ∈ H, x ∈ A ∨ x ∈ B ∨ x ∈ C` using `fun x hx => by`. Assume the negation of the conclusion as `h'`. Conclude with `hcon ⟨x, hx, by tauto⟩`. Take `⟨x, hx, hxB, hxC⟩` from `two_sub H B C hB hC`.

Take `⟨y, hy, hyA, hyC⟩` from `two_sub H A C hA hC`. Establish `hxA : x ∈ A` using `by have := h x hx; tauto`. Establish `hyB : y ∈ B` using `by have := h y hy; tauto`. Establish `hxy : x * y ∈ C`. Break down `h _ (H.mul_mem hx hy) with h1 | h1 | h1` into its components or cases.

Conclude with `absurd ((A.mul_mem_cancel_left hxA).1 h1) hyA`. Conclude with `absurd ((B.mul_mem_cancel_right hyB).1 h1) hxB`. Conclude with `h1`. Break down `h _ (H.mul_mem hx (H.mul_mem hx hy)) with h1 | h1 | h1` into its components or cases. Conclude with `hyA ((A.mul_mem_cancel_left hxA).1 ((A.mul_mem_cancel_left hxA).1 h1))`.

Rewrite `h1` using `[← mul_assoc]`. Establish `h2 : x ^ 2 ∈ B` using `by rw [sq]; exact (B.mul_mem_cancel_right hyB).1 h1`. Take `⟨j, rfl⟩` from `hk`. Establish `h3` using `hpow x hx`. Rewrite `h3` using `[pow_succ, pow_mul]`.

Conclude with `hxB ((B.mul_mem_cancel_left (B.pow_mem h2 j)).1 h3)`. Conclude with `hxC ((C.mul_mem_cancel_right hxy).1 h1)`.
-/
private theorem three_sub {Γ : Type} [Group Γ] (H A B C : Subgroup Γ) (hA : ¬ H ≤ A) (hB : ¬ H ≤ B) (hC : ¬ H ≤ C)
    (k : ℕ) (hk : Odd k) (hpow : ∀ x ∈ H, x ^ k ∈ B) : ∃ x ∈ H, x ∉ A ∧ x ∉ B ∧ x ∉ C := by
  by_contra hcon
  have h : ∀ x ∈ H, x ∈ A ∨ x ∈ B ∨ x ∈ C := fun x hx => by
    by_contra h'
    exact hcon ⟨x, hx, by tauto⟩
  obtain ⟨x, hx, hxB, hxC⟩ := two_sub H B C hB hC
  obtain ⟨y, hy, hyA, hyC⟩ := two_sub H A C hA hC
  have hxA : x ∈ A := by have := h x hx; tauto
  have hyB : y ∈ B := by have := h y hy; tauto
  have hxy : x * y ∈ C := by
    rcases h _ (H.mul_mem hx hy) with h1 | h1 | h1
    · exact absurd ((A.mul_mem_cancel_left hxA).1 h1) hyA
    · exact absurd ((B.mul_mem_cancel_right hyB).1 h1) hxB
    · exact h1
  rcases h _ (H.mul_mem hx (H.mul_mem hx hy)) with h1 | h1 | h1
  · exact hyA ((A.mul_mem_cancel_left hxA).1 ((A.mul_mem_cancel_left hxA).1 h1))
  · rw [← mul_assoc] at h1
    have h2 : x ^ 2 ∈ B := by rw [sq]; exact (B.mul_mem_cancel_right hyB).1 h1
    obtain ⟨j, rfl⟩ := hk
    have h3 := hpow x hx
    rw [pow_succ, pow_mul] at h3
    exact hxB ((B.mul_mem_cancel_left (B.pow_mem h2 j)).1 h3)
  · exact hxC ((C.mul_mem_cancel_right hxy).1 h1)

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf49.add_pow_nsmul U f hf`.
-/
private theorem add_pow_nsmul {Γ W : Type} [Group Γ] [AddCommGroup W] (U : Subgroup Γ) (f : Γ → W)
    (hf : ∀ u ∈ U, ∀ v ∈ U, f (u * v) = f u + f v) : f 1 = 0 ∧ ∀ u ∈ U, ∀ k : ℕ, f (u ^ k) = k • f u :=
  _root_.UpperTheory.Reformulated.B.Qf49.add_pow_nsmul U f hf

/- English proof (translation)
Establish `h1` using `(add_pow_nsmul U f hf).1`. Use `⟨{ carrier := {u | u ∈ U ∧ f u ∈ P} one_mem' := ⟨U.one_mem, h1 ▸ P.zero_mem⟩ mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, hf a ha.1 b hb.1 ▸ P.add_mem ha.2 hb.2⟩ inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, ?_⟩ }, ?_, fun u => Iff.rfl⟩` and prove the remaining obligations. Establish `h2` using `hf a ha.1 a⁻¹ (U.inv_mem ha.1)`. Rewrite `h2` using `[mul_inv_cancel, h1]`. Rewrite using `[eq_neg_of_add_eq_zero_right h2.symm]`.

Conclude with `P.neg_mem ha.2`. Establish `h2` using `hU.isOpenMap_subtype_val _ (hlc (P : Set W))`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `u`. Conclude with `⟨fun h => ⟨⟨u, h.1⟩, h.2, rfl⟩, fun ⟨v, hv, e⟩ => e ▸ ⟨v.2, hv⟩⟩`.
-/
private theorem ex_sub {Γ W : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup W] (U : Subgroup Γ)
    (hU : IsOpen (U : Set Γ)) (f : Γ → W) (hf : ∀ u ∈ U, ∀ v ∈ U, f (u * v) = f u + f v)
    (hlc : IsLocallyConstant fun u : U => f u) (P : AddSubgroup W) :
    ∃ K : Subgroup Γ, IsOpen (K : Set Γ) ∧ ∀ u, u ∈ K ↔ u ∈ U ∧ f u ∈ P := by
  have h1 := (add_pow_nsmul U f hf).1
  refine ⟨{ carrier := {u | u ∈ U ∧ f u ∈ P}
            one_mem' := ⟨U.one_mem, h1 ▸ P.zero_mem⟩
            mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, hf a ha.1 b hb.1 ▸ P.add_mem ha.2 hb.2⟩
            inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, ?_⟩ }, ?_, fun u => Iff.rfl⟩
  · have h2 := hf a ha.1 a⁻¹ (U.inv_mem ha.1)
    rw [mul_inv_cancel, h1] at h2
    rw [eq_neg_of_add_eq_zero_right h2.symm]
    exact P.neg_mem ha.2
  · have h2 := hU.isOpenMap_subtype_val _ (hlc (P : Set W))
    convert h2 using 1
    ext u
    exact ⟨fun h => ⟨⟨u, h.1⟩, h.2, rfl⟩, fun ⟨v, hv, e⟩ => e ▸ ⟨v.2, hv⟩⟩

/- English proof (translation)
Introduce `hle`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Establish `hFl : F * l ≠ 0` using `mul_ne_zero hF hl.ne_zero`. Use `haveI : NeZero (F * l) := ⟨hFl⟩`. Take `⟨-, -, -, hex, -, -, -, -, -, hmul⟩` from `galBasic Ω (F * l) hFl`.

Establish `hnorm` using `(galBasic Ω F hF).1`. Establish `hc1 : (1 + F).Coprime F` using `by simp`. Establish `hcop : (1 + F).Coprime (F * l)` using `hc1.mul_right (hc1.coprime_dvd_right hlF)`. Take `⟨u, hu⟩` from `hex (ZMod.unitOfCoprime _ hcop)`. Take `⟨g, hg⟩` from `hex (-1)`.

Establish `hpow : ∀ x : Ω, x ^ F = 1 → x ^ (F * l) = 1` using `fun x hx => by rw [pow_mul, hx, one_pow]`. Establish `huU : u ∈ fixMu ℚ Ω F` using `fun x hx => by`. Rewrite using `[hu x (hpow x hx), ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ (hpow x hx), pow_add, hx, pow_one, mul_one]`. Establish `hginv : ∀ x : Ω, x ^ F = 1 → g x * x = 1` using `fun x hx => by`. Rewrite using `[hg x (hpow x hx), ← pow_succ]`.

Establish `: F * l ∣ ((-1 : (ZMod (F * l))ˣ) : ZMod (F * l)).val + 1`. Rewrite using `[← ZMod.natCast_eq_zero_iff]`. Simplify using the standard rewrite rules. Take `⟨c, hc⟩` from `this`. Rewrite using `[hc, pow_mul, hpow x hx, one_pow]`.

Establish `hr0 : (r : Ω) ≠ 0` using `Nat.cast_ne_zero.2 hr`. Establish `hM0 : M ≠ 0` using `fun h => hF (by rw [h] at hM; exact zero_dvd_iff.1 hM)`. Establish `hρ0 : ρ ≠ 0` using `fun h => hr0 (by rw [← hρ, h, zero_pow hM0])`. Establish `hrt : ∀ s : G ℚ Ω, ∃ ξ : Ω, ξ ^ F = 1 ∧ s ρ = ξ * ρ` using `fun s => by`. Use `⟨s ρ / ρ, ?_, (div_mul_cancel₀ _ hρ0).symm⟩` and prove the remaining obligations.

Take `⟨c, rfl⟩` from `hM`. Rewrite using `[pow_mul, div_pow, ← map_pow, hρ, map_natCast, div_self hr0, one_pow]`. Take `⟨ξ, hξ, hξ'⟩` from `hrt u`. Take `⟨η, hη, hη'⟩` from `hrt g⁻¹`. Establish `hconj : g * u * g⁻¹ ∈ fixMu ℚ Ω F` using `hnorm.conj_mem u huU g`.

Establish `hmem : g * u * g⁻¹ * u ∈ fixMu ℚ Ω F ⊓ MulAction.stabilizer (G ℚ Ω) ρ`. Use `⟨mul_mem hconj huU, ?_⟩` and prove the remaining obligations. Use `show (g * u * g⁻¹) (u ρ) = ρ`. Rewrite using `[hξ', map_mul, hconj ξ hξ]`. Use `show ξ * g (u (g⁻¹ ρ)) = ρ`.

Establish `e : u (g⁻¹ ρ) = ξ * g⁻¹ ρ` using `by rw [hη', map_mul, huU η hη, hξ']; ring`. Establish `e2 : g (g⁻¹ ρ) = ρ` using `g.apply_symm_apply ρ`. Rewrite using `[e, map_mul, e2, ← mul_assoc, mul_comm ξ, hginv ξ hξ, one_mul]`. Establish `h1 : Lifts (F * l) 1 (1 : G ℚ Ω)` using `fun x hx => by`. Rewrite using `[Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hx, pow_one]`.

Both sides reduce to the same expression. Establish `h2` using `(hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ hg hu).1 (hmul _ _ _ _ hg hu).2.1).1 hu).1`. Establish `h3` using `(hmul _ _ _ _ h1 h2).2.2.2 (by simpa using hle hmem)`. Establish `h4` using `congrArg Units.val h3`. Simplify using `only [Units.val_one, Units.val_mul, inv_neg_one, Units.val_neg, ZMod.coe_unitOfCoprime] at h4`.

Establish `h5 : ((F * (2 + F) : ℕ) : ZMod (F * l)) = 0`. Move the coercions through the operations in `at h4 ⊢`. Take the linear combination `-h4`. Rewrite `h5` using `[ZMod.natCast_eq_zero_iff]`. Establish `h6 : l ∣ 2` using `(Nat.dvd_add_left hlF).1 (Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hF) h5)`.

Conclude with `hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h6)`.
-/
private theorem third (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l M F r : ℕ) (hl : l.Prime) (hl2 : l ≠ 2)
    (hF : F ≠ 0) (hlF : l ∣ F) (hM : M ∣ F) (hr : r ≠ 0) (ρ : Ω) (hρ : ρ ^ M = (r : Ω)) :
    ¬ fixMu ℚ Ω F ⊓ MulAction.stabilizer (G ℚ Ω) ρ ≤ fixMu ℚ Ω (F * l) := by
  intro hle
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hFl : F * l ≠ 0 := mul_ne_zero hF hl.ne_zero
  haveI : NeZero (F * l) := ⟨hFl⟩
  obtain ⟨-, -, -, hex, -, -, -, -, -, hmul⟩ := galBasic Ω (F * l) hFl
  have hnorm := (galBasic Ω F hF).1
  have hc1 : (1 + F).Coprime F := by simp
  have hcop : (1 + F).Coprime (F * l) := hc1.mul_right (hc1.coprime_dvd_right hlF)
  obtain ⟨u, hu⟩ := hex (ZMod.unitOfCoprime _ hcop)
  obtain ⟨g, hg⟩ := hex (-1)
  have hpow : ∀ x : Ω, x ^ F = 1 → x ^ (F * l) = 1 := fun x hx => by rw [pow_mul, hx, one_pow]
  have huU : u ∈ fixMu ℚ Ω F := fun x hx => by
    rw [hu x (hpow x hx), ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ (hpow x hx), pow_add, hx,
      pow_one, mul_one]
  have hginv : ∀ x : Ω, x ^ F = 1 → g x * x = 1 := fun x hx => by
    rw [hg x (hpow x hx), ← pow_succ]
    have : F * l ∣ ((-1 : (ZMod (F * l))ˣ) : ZMod (F * l)).val + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      simp
    obtain ⟨c, hc⟩ := this
    rw [hc, pow_mul, hpow x hx, one_pow]
  have hr0 : (r : Ω) ≠ 0 := Nat.cast_ne_zero.2 hr
  have hM0 : M ≠ 0 := fun h => hF (by rw [h] at hM; exact zero_dvd_iff.1 hM)
  have hρ0 : ρ ≠ 0 := fun h => hr0 (by rw [← hρ, h, zero_pow hM0])
  have hrt : ∀ s : G ℚ Ω, ∃ ξ : Ω, ξ ^ F = 1 ∧ s ρ = ξ * ρ := fun s => by
    refine ⟨s ρ / ρ, ?_, (div_mul_cancel₀ _ hρ0).symm⟩
    obtain ⟨c, rfl⟩ := hM
    rw [pow_mul, div_pow, ← map_pow, hρ, map_natCast, div_self hr0, one_pow]
  obtain ⟨ξ, hξ, hξ'⟩ := hrt u
  obtain ⟨η, hη, hη'⟩ := hrt g⁻¹
  have hconj : g * u * g⁻¹ ∈ fixMu ℚ Ω F := hnorm.conj_mem u huU g
  have hmem : g * u * g⁻¹ * u ∈ fixMu ℚ Ω F ⊓ MulAction.stabilizer (G ℚ Ω) ρ := by
    refine ⟨mul_mem hconj huU, ?_⟩
    show (g * u * g⁻¹) (u ρ) = ρ
    rw [hξ', map_mul, hconj ξ hξ]
    show ξ * g (u (g⁻¹ ρ)) = ρ
    have e : u (g⁻¹ ρ) = ξ * g⁻¹ ρ := by rw [hη', map_mul, huU η hη, hξ']; ring
    have e2 : g (g⁻¹ ρ) = ρ := g.apply_symm_apply ρ
    rw [e, map_mul, e2, ← mul_assoc, mul_comm ξ, hginv ξ hξ, one_mul]
  have h1 : Lifts (F * l) 1 (1 : G ℚ Ω) := fun x hx => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hx, pow_one]
    rfl
  have h2 := (hmul _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ hg hu).1 (hmul _ _ _ _ hg hu).2.1).1 hu).1
  have h3 := (hmul _ _ _ _ h1 h2).2.2.2 (by simpa using hle hmem)
  have h4 := congrArg Units.val h3
  simp only [Units.val_one, Units.val_mul, inv_neg_one, Units.val_neg, ZMod.coe_unitOfCoprime] at h4
  have h5 : ((F * (2 + F) : ℕ) : ZMod (F * l)) = 0 := by
    push_cast at h4 ⊢
    linear_combination -h4
  rw [ZMod.natCast_eq_zero_iff] at h5
  have h6 : l ∣ 2 := (Nat.dvd_add_left hlF).1 (Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hF) h5)
  exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h6)

/- English proof (translation)
Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : NeZero F := ⟨hF⟩`. Take `⟨-, -, -, hcop, -, -, hpows, -⟩` from `placeBasic Ω`. Establish `hno : ∀ k : ℕ, k ∣ F * l * r → ¬ Over A k` using `fun k hk => hcop A q k ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqT (h.trans hk)) hA`.

Establish `hM0 : M ≠ 0` using `fun h => hF (by rw [hlev, h, mul_zero])`. Establish `hmod : q ≡ 1 [MOD F]`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω F`. Establish `e` using `hpows A q F φ hφ (hno F ((dvd_mul_right F l).mul_right r)) ζ hζ.pow_eq_one`. Rewrite `e` using `[h1 ζ hζ.pow_eq_one]`.

Rewrite using `[hζ.eq_orderOf, ← (isOfFinOrder_iff_pow_eq_one.2 ⟨F, Nat.pos_of_ne_zero hF, hζ.pow_eq_one⟩).pow_eq_pow_iff_modEq, pow_one]`. Conclude with `e.symm`. Take `⟨k, hk⟩` from `(Nat.modEq_iff_dvd' hq.one_le).1 hmod.symm`. Establish `hq' : q = F * k + 1` using `by have := hq.one_le; omega`. Establish `hlk : ¬ l ∣ k`.

Introduce and unpack `⟨j, rfl⟩`. Use `h3 fun x hx => ?_` and prove the remaining obligations. Rewrite using `[hpows A q (F * l) φ hφ (hno _ (dvd_mul_right _ r)) x hx, hq', pow_succ, ← mul_assoc, pow_mul, hx, one_pow, one_mul]`. Use `⟨hq, hmod, fun h => hqT (h ▸ dvd_mul_left _ _), fun hord => ?_⟩` and prove the remaining obligations. Establish `hvr : A.valuation (r : Ω) = 1` using `le_antisymm ((A.valuation_le_one_iff _).2 (natCast_mem A r)) (not_lt.1 (hno r (dvd_mul_left _ _)))`.

Establish `hvρ : A.valuation ρ = 1`. Rewrite `hvr` using `[← hρ, map_pow]`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le hM0).1 hvr`. Establish `h4` using `hφ.2 ρ hvρ.le`. Establish `hge : 1 ≤ r ^ (N₀ * k)` using `Nat.one_le_pow _ _ hr.pos`.

Establish `e : φ ρ - ρ ^ q = -(ρ * ((r ^ (N₀ * k) - 1 : ℕ) : Ω))`. Rewrite using `[h2, Nat.cast_sub hge, Nat.cast_pow, ← hρ, hq', hlev]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h4` using `[e, Valuation.map_neg, map_mul, hvρ, one_mul]`.

Establish `h5 : q ∣ r ^ (N₀ * k) - 1`. Assume the negation of the conclusion as `h`. Conclude with `hcop A q _ ((Nat.Prime.coprime_iff_not_dvd hq).2 h) hA h4`. Establish `h6 : (r : ZMod q) ^ (N₀ * k) = 1`. Use `(ZMod.natCast_eq_zero_iff _ _).2 h5` as an intermediate fact.

Rewrite `this` using `[Nat.cast_sub hge]`. Move the coercions through the operations in `at this`. Conclude with `sub_eq_zero.1 this`. Establish `h7` using `hord.trans (orderOf_dvd_of_pow_eq_one h6)`. Conclude with `hlk (hN.symm.dvd_of_dvd_mul_left h7)`.
-/
private theorem adm (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l M N₀ F r q : ℕ) (hl : l.Prime)
    (hF : F ≠ 0) (hlev : F = N₀ * M) (hN : N₀.Coprime l) (hr : r.Prime) (hq : q.Prime) (hqT : ¬ q ∣ F * l * r)
    (ρ : Ω) (hρ : ρ ^ M = (r : Ω)) (A : ValuationSubring Ω) (hA : Over A q) (φ : G ℚ Ω) (hφ : IsFrob (F := ℚ) A q φ)
    (h1 : φ ∈ fixMu ℚ Ω F) (h2 : φ ρ = ρ) (h3 : φ ∉ fixMu ℚ Ω (F * l)) : AdmP l F r q := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero F := ⟨hF⟩
  obtain ⟨-, -, -, hcop, -, -, hpows, -⟩ := placeBasic Ω
  have hno : ∀ k : ℕ, k ∣ F * l * r → ¬ Over A k := fun k hk =>
    hcop A q k ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqT (h.trans hk)) hA
  have hM0 : M ≠ 0 := fun h => hF (by rw [hlev, h, mul_zero])
  have hmod : q ≡ 1 [MOD F] := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω F
    have e := hpows A q F φ hφ (hno F ((dvd_mul_right F l).mul_right r)) ζ hζ.pow_eq_one
    rw [h1 ζ hζ.pow_eq_one] at e
    rw [hζ.eq_orderOf, ← (isOfFinOrder_iff_pow_eq_one.2 ⟨F, Nat.pos_of_ne_zero hF, hζ.pow_eq_one⟩).pow_eq_pow_iff_modEq,
      pow_one]
    exact e.symm
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hq.one_le).1 hmod.symm
  have hq' : q = F * k + 1 := by have := hq.one_le; omega
  have hlk : ¬ l ∣ k := by
    rintro ⟨j, rfl⟩
    refine h3 fun x hx => ?_
    rw [hpows A q (F * l) φ hφ (hno _ (dvd_mul_right _ r)) x hx, hq', pow_succ, ← mul_assoc, pow_mul, hx, one_pow,
      one_mul]
  refine ⟨hq, hmod, fun h => hqT (h ▸ dvd_mul_left _ _), fun hord => ?_⟩
  have hvr : A.valuation (r : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).2 (natCast_mem A r)) (not_lt.1 (hno r (dvd_mul_left _ _)))
  have hvρ : A.valuation ρ = 1 := by
    rw [← hρ, map_pow] at hvr
    exact (pow_eq_one_iff_of_nonneg zero_le hM0).1 hvr
  have h4 := hφ.2 ρ hvρ.le
  have hge : 1 ≤ r ^ (N₀ * k) := Nat.one_le_pow _ _ hr.pos
  have e : φ ρ - ρ ^ q = -(ρ * ((r ^ (N₀ * k) - 1 : ℕ) : Ω)) := by
    rw [h2, Nat.cast_sub hge, Nat.cast_pow, ← hρ, hq', hlev]
    push_cast
    ring
  rw [e, Valuation.map_neg, map_mul, hvρ, one_mul] at h4
  have h5 : q ∣ r ^ (N₀ * k) - 1 := by
    by_contra h
    exact hcop A q _ ((Nat.Prime.coprime_iff_not_dvd hq).2 h) hA h4
  have h6 : (r : ZMod q) ^ (N₀ * k) = 1 := by
    have := (ZMod.natCast_eq_zero_iff _ _).2 h5
    rw [Nat.cast_sub hge] at this
    push_cast at this
    exact sub_eq_zero.1 this
  have h7 := hord.trans (orderOf_dvd_of_pow_eq_one h6)
  exact hlk (hN.symm.dvd_of_dvd_mul_left h7)

/- English proof (translation)
Introduce `Ω _ _ _ l hl O _ _ _ _ _ N₀ m F r n n' T α hD hr hrF hT ν c hν hc ⟨u₁, hu₁, hcu₁⟩`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Use `haveI : IsGalois ℚ Ω := inferInstance`.

Establish `hlp` using `hl.out`. Establish `hm0 : m ≠ 0` using `by have := hD.pos; omega`. Establish `hN0 : N₀ ≠ 0` using `fun h => hlp.ne_one (by have := hD.cop; rwa [h, Nat.coprime_zero_left] at this)`. Establish `hM0 : l ^ m ≠ 0` using `pow_ne_zero _ hlp.ne_zero`. Establish `hF : F ≠ 0` using `hD.lev ▸ mul_ne_zero hN0 hM0`.

Establish `hMF : l ^ m ∣ F` using `hD.lev ▸ dvd_mul_left _ _`. Establish `hlF : l ∣ F` using `(dvd_pow_self l hm0).trans hMF`. Establish `hFl : F * l ≠ 0` using `mul_ne_zero hF hlp.ne_zero`. Establish `hodd : Odd l` using `hlp.odd_of_ne_two hD.odd_l`. Take `⟨ρ, hρ⟩` from `IsAlgClosed.exists_pow_nat_eq (r : Ω) (Nat.pos_of_ne_zero hM0)`.

Take `⟨-, hUo, -, hex, -⟩` from `galBasic Ω F hF`. Use `set U := fixMu ℚ Ω F with hU`. Use `set H := U ⊓ MulAction.stabilizer (G ℚ Ω) ρ with hH`. Establish `hHo : IsOpen (H : Set (G ℚ Ω))` using `hUo.inter (stabilizer_isOpen_of_isIntegral (K := ℚ) ρ)`. Take `⟨B, hBo, hB⟩` from `ex_sub U hUo c hc.add hc.lc ⊥`.

Establish `hHB : ¬ H ≤ B` using `fun h => by`. Take `⟨g, hg⟩` from `hD.notCyc`. Use `radEqv Ω l O (QO l O) m F r hF hMF hr.ne_zero ρ hρ α c hc.add hc.eqv hc.tors (fun u hu hu' => ((hB u).1 (h ⟨hu, hu'⟩)).2) g u₁ hu₁` as an intermediate fact. Conclude with `hcu₁ (hg.smul_eq_zero.1 this)`. Establish `hlm : (l : O) ∈ IsLocalRing.maximalIdeal O` using `fun h => by`.

Use `hc.tors u₁ hu₁` as an intermediate fact. Rewrite `this` using `[← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]`. Conclude with `hcu₁ ((h.pow m).smul_eq_zero.1 this)`. Establish `hex1 : ∃ K : Subgroup (G ℚ Ω), IsOpen (K : Set (G ℚ Ω)) ∧ ¬ H ≤ K ∧ ∀ φ ∈ U, φ ∉ K → ∀ u ∈ U, ∃ y : O, ν u = y • ν φ` using `by haveI : CompactSpace U := isCompact_iff_compactSpace.1 (U.isClosed_of_isOpen hUo).isCompact`. Take `⟨_, ⟨u₀, rfl⟩, hmax⟩` from `Set.Finite.exists_maximalFor (fun w : QO l O => Submodule.span O {w}) _ hν.lc.range_finite ⟨_, ⟨1, rfl⟩⟩`.

Establish `hgen : ∀ u ∈ U, ∃ y : O, ν u = y • ν u₀` using `fun u hu => by`. Break down `(qoCyc l O).2.2.2.1 (ν u₀) (ν u) with h | ⟨y, h⟩` into its components or cases. Conclude with `h`. Establish `h1 : Submodule.span O {ν u₀} ≤ Submodule.span O {ν u}` using `(Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_span_singleton.2 ⟨y, h.symm⟩)`. Take `⟨z, hz⟩` from `Submodule.mem_span_singleton.1 (hmax ⟨⟨u, hu⟩, rfl⟩ h1 (Submodule.mem_span_singleton_self _))`.

Conclude with `⟨z, hz.symm⟩`. Distinguish the cases in `h0 : ν u₀ = 0`. Use `⟨B, hBo, hHB, fun φ _ _ u hu => ⟨0, ?_⟩⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hgen u hu`. Rewrite using `[hy, h0, smul_zero, zero_smul]`.

Set `P : Submodule O (QO l O)` to `Submodule.map (LinearMap.toSpanSingleton O _ (ν u₀)) (IsLocalRing.maximalIdeal O)`. Take `⟨K, hKo, hK⟩` from `ex_sub U hUo ν hν.add hν.lc P.toAddSubgroup`. Use `⟨K, hKo, fun h => h0 ?_, fun φ hφ hφK u hu => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `hex (-1)`. Establish `h1` using `radEqv Ω l O (QO l O ⧸ P) m F r hF hMF hr.ne_zero ρ hρ (dualChar l α) (fun u => P.mkQ (ν u)) (fun u hu v hv => by rw [hν.add u hu v hv, map_add]) (fun g u hu => by rw [hν.eqv g u hu, map_smul]) (fun u hu => by rw [← map_nsmul, hν.tors u hu, map_zero]) (fun u hu hu' => (Submodule. …`.

Establish `h2 : IsUnit (1 - (α g : O))`. Assume the negation of the conclusion as `h2`. Establish `h3 : (α g : O) + 1 ∈ IsLocalRing.maximalIdeal O` using `Ideal.mem_of_dvd _ ((dvd_pow_self _ hm0).trans (hD.odd g hg)) hlm`. Establish `h4 : 1 - (α g : O) ∈ IsLocalRing.maximalIdeal O` using `h2`. Take `⟨j, hj⟩` from `hodd`.

Establish `h5 : (1 : O) = l - j * ((α g : O) + 1 + (1 - (α g : O)))`. Rewrite using `[hj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 ?_)` and prove the remaining obligations.

Rewrite using `[h5]`. Conclude with `sub_mem hlm (Ideal.mul_mem_left _ _ (add_mem h3 h4))`. Establish `e : (dualChar l α g : O) - (chiO ℚ Ω l O g : O) = (dualChar l α g : O) * (1 - (α g : O))`. Rewrite using `[mul_sub, mul_one, ← Units.val_mul]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[e]`. Establish `h6` using `((Units.isUnit _).mul h2).smul_eq_zero.1 h1`. Take `⟨y, hy, hy'⟩` from `(Submodule.Quotient.mk_eq_zero P).1 h6`. Establish `h7 : IsUnit (1 - y)` using `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits y hy`. Use `h7.smul_eq_zero.1 ?_` and prove the remaining obligations.

Rewrite using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `hy'.symm`. Take `⟨y, hy⟩` from `hgen φ hφ`. Establish `hyu : IsUnit y`. Assume the negation of the conclusion as `h`.

Conclude with `hφK ((hK φ).2 ⟨hφ, y, h, hy.symm⟩)`. Take `⟨z, hz⟩` from `hgen u hu`. Take `⟨y', hy'⟩` from `hyu.exists_left_inv`. Conclude with `⟨z * y', by rw [hz, hy, smul_smul, mul_assoc, hy', mul_one]⟩`. Take `⟨K, hKo, hHK, hK⟩` from `hex1`.

Establish `hCo` using `(galBasic Ω (F * l) hFl).2.1`. Take `⟨x, hx⟩` from `three_sub H K B (fixMu ℚ Ω (F * l)) hHK hHB (third Ω l (l ^ m) F r hlp hD.odd_l hF hlF hMF hr.ne_zero ρ hρ) (l ^ m) hodd.pow fun x hx => (hB _).2 ⟨pow_mem hx.1 _, by`. Rewrite using `[(add_pow_nsmul U c hc.add).2 x hx.1, hc.tors x hx.1]`. Conclude with `zero_mem _⟩`. Take `⟨q, A, φ, hq, hqT, hA, hφ, hφH, hφK, hφB, hφC⟩` from `chebQ Ω {x | x ∈ H ∧ x ∉ K ∧ x ∉ B ∧ x ∉ fixMu ℚ Ω (F * l)} (hHo.inter ((K.isClosed_of_isOpen hKo).isOpen_compl.inter ((B.isClosed_of_isOpen hBo).isOpen_compl.inter (Subgroup.isClosed_of_isOpen _ hCo).isOpen_compl))) ⟨x, hx⟩ (T * (F * l * r)) (mul_ne_zero hT (mul_ne_zero hFl hr.n …`.

Conclude with `⟨q, A, φ, adm Ω l (l ^ m) N₀ F r q hlp hF hD.lev hD.cop hr hq (fun h => hqT (h.mul_left _)) ρ hρ A hA φ hφ hφH.1 hφH.2 hφC, fun h => hqT (h.mul_right _), hA, hφ, fun h => hφB ((hB φ).2 ⟨hφH.1, h⟩), hK φ hφH.1 hφK⟩`.
-/
theorem UpperTheory.V.ML.pick :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F r n n' T : ℕ) (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → r.Prime → r.Coprime F → T ≠ 0 →
    ∀ ν c : G ℚ Ω → QO l O, IsNu (l ^ m) F n (dualChar l α) ν → IsNu (l ^ m) F n' α c → (∃ u ∈ fixMu ℚ Ω F, c u ≠ 0) →
    ∃ (q : ℕ) (A : ValuationSubring Ω) (φ : G ℚ Ω), AdmP l F r q ∧ ¬ q ∣ T ∧ Over A q ∧ IsFrob (F := ℚ) A q φ ∧ c φ ≠ 0 ∧ ∀ u ∈ fixMu ℚ Ω F, ∃ y : O, ν u = y • ν φ := by
  intro Ω _ _ _ l hl O _ _ _ _ _ N₀ m F r n n' T α hD hr hrF hT ν c hν hc ⟨u₁, hu₁, hcu₁⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois ℚ Ω := inferInstance
  have hlp := hl.out
  have hm0 : m ≠ 0 := by have := hD.pos; omega
  have hN0 : N₀ ≠ 0 := fun h => hlp.ne_one (by have := hD.cop; rwa [h, Nat.coprime_zero_left] at this)
  have hM0 : l ^ m ≠ 0 := pow_ne_zero _ hlp.ne_zero
  have hF : F ≠ 0 := hD.lev ▸ mul_ne_zero hN0 hM0
  have hMF : l ^ m ∣ F := hD.lev ▸ dvd_mul_left _ _
  have hlF : l ∣ F := (dvd_pow_self l hm0).trans hMF
  have hFl : F * l ≠ 0 := mul_ne_zero hF hlp.ne_zero
  have hodd : Odd l := hlp.odd_of_ne_two hD.odd_l
  obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (r : Ω) (Nat.pos_of_ne_zero hM0)
  obtain ⟨-, hUo, -, hex, -⟩ := galBasic Ω F hF
  set U := fixMu ℚ Ω F with hU
  set H := U ⊓ MulAction.stabilizer (G ℚ Ω) ρ with hH
  have hHo : IsOpen (H : Set (G ℚ Ω)) := hUo.inter (stabilizer_isOpen_of_isIntegral (K := ℚ) ρ)
  obtain ⟨B, hBo, hB⟩ := ex_sub U hUo c hc.add hc.lc ⊥
  have hHB : ¬ H ≤ B := fun h => by
    obtain ⟨g, hg⟩ := hD.notCyc
    have := radEqv Ω l O (QO l O) m F r hF hMF hr.ne_zero ρ hρ α c hc.add hc.eqv hc.tors
      (fun u hu hu' => ((hB u).1 (h ⟨hu, hu'⟩)).2) g u₁ hu₁
    exact hcu₁ (hg.smul_eq_zero.1 this)
  have hlm : (l : O) ∈ IsLocalRing.maximalIdeal O := fun h => by
    have := hc.tors u₁ hu₁
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at this
    exact hcu₁ ((h.pow m).smul_eq_zero.1 this)
  have hex1 : ∃ K : Subgroup (G ℚ Ω), IsOpen (K : Set (G ℚ Ω)) ∧ ¬ H ≤ K ∧
      ∀ φ ∈ U, φ ∉ K → ∀ u ∈ U, ∃ y : O, ν u = y • ν φ := by
    haveI : CompactSpace U := isCompact_iff_compactSpace.1 (U.isClosed_of_isOpen hUo).isCompact
    obtain ⟨_, ⟨u₀, rfl⟩, hmax⟩ := Set.Finite.exists_maximalFor (fun w : QO l O => Submodule.span O {w}) _
      hν.lc.range_finite ⟨_, ⟨1, rfl⟩⟩
    have hgen : ∀ u ∈ U, ∃ y : O, ν u = y • ν u₀ := fun u hu => by
      rcases (qoCyc l O).2.2.2.1 (ν u₀) (ν u) with h | ⟨y, h⟩
      · exact h
      · have h1 : Submodule.span O {ν u₀} ≤ Submodule.span O {ν u} :=
          (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.mem_span_singleton.2 ⟨y, h.symm⟩)
        obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1
          (hmax ⟨⟨u, hu⟩, rfl⟩ h1 (Submodule.mem_span_singleton_self _))
        exact ⟨z, hz.symm⟩
    by_cases h0 : ν u₀ = 0
    · refine ⟨B, hBo, hHB, fun φ _ _ u hu => ⟨0, ?_⟩⟩
      obtain ⟨y, hy⟩ := hgen u hu
      rw [hy, h0, smul_zero, zero_smul]
    · let P : Submodule O (QO l O) := Submodule.map (LinearMap.toSpanSingleton O _ (ν u₀)) (IsLocalRing.maximalIdeal O)
      obtain ⟨K, hKo, hK⟩ := ex_sub U hUo ν hν.add hν.lc P.toAddSubgroup
      refine ⟨K, hKo, fun h => h0 ?_, fun φ hφ hφK u hu => ?_⟩
      · obtain ⟨g, hg⟩ := hex (-1)
        have h1 := radEqv Ω l O (QO l O ⧸ P) m F r hF hMF hr.ne_zero ρ hρ (dualChar l α) (fun u => P.mkQ (ν u))
          (fun u hu v hv => by rw [hν.add u hu v hv, map_add])
          (fun g u hu => by rw [hν.eqv g u hu, map_smul])
          (fun u hu => by rw [← map_nsmul, hν.tors u hu, map_zero])
          (fun u hu hu' => (Submodule.Quotient.mk_eq_zero P).2 ((hK u).1 (h ⟨hu, hu'⟩)).2) g u₀ u₀.2
        have h2 : IsUnit (1 - (α g : O)) := by
          by_contra h2
          have h3 : (α g : O) + 1 ∈ IsLocalRing.maximalIdeal O :=
            Ideal.mem_of_dvd _ ((dvd_pow_self _ hm0).trans (hD.odd g hg)) hlm
          have h4 : 1 - (α g : O) ∈ IsLocalRing.maximalIdeal O := h2
          obtain ⟨j, hj⟩ := hodd
          have h5 : (1 : O) = l - j * ((α g : O) + 1 + (1 - (α g : O))) := by
            rw [hj]
            push_cast
            ring
          refine (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 ?_)
          rw [h5]
          exact sub_mem hlm (Ideal.mul_mem_left _ _ (add_mem h3 h4))
        have e : (dualChar l α g : O) - (chiO ℚ Ω l O g : O) = (dualChar l α g : O) * (1 - (α g : O)) := by
          rw [mul_sub, mul_one, ← Units.val_mul]
          simp
        rw [e] at h1
        have h6 := ((Units.isUnit _).mul h2).smul_eq_zero.1 h1
        obtain ⟨y, hy, hy'⟩ := (Submodule.Quotient.mk_eq_zero P).1 h6
        have h7 : IsUnit (1 - y) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits y hy
        refine h7.smul_eq_zero.1 ?_
        rw [sub_smul, one_smul, sub_eq_zero]
        exact hy'.symm
      · obtain ⟨y, hy⟩ := hgen φ hφ
        have hyu : IsUnit y := by
          by_contra h
          exact hφK ((hK φ).2 ⟨hφ, y, h, hy.symm⟩)
        obtain ⟨z, hz⟩ := hgen u hu
        obtain ⟨y', hy'⟩ := hyu.exists_left_inv
        exact ⟨z * y', by rw [hz, hy, smul_smul, mul_assoc, hy', mul_one]⟩
  obtain ⟨K, hKo, hHK, hK⟩ := hex1
  have hCo := (galBasic Ω (F * l) hFl).2.1
  obtain ⟨x, hx⟩ := three_sub H K B (fixMu ℚ Ω (F * l)) hHK hHB
    (third Ω l (l ^ m) F r hlp hD.odd_l hF hlF hMF hr.ne_zero ρ hρ) (l ^ m) hodd.pow fun x hx =>
      (hB _).2 ⟨pow_mem hx.1 _, by
        rw [(add_pow_nsmul U c hc.add).2 x hx.1, hc.tors x hx.1]
        exact zero_mem _⟩
  obtain ⟨q, A, φ, hq, hqT, hA, hφ, hφH, hφK, hφB, hφC⟩ :=
    chebQ Ω {x | x ∈ H ∧ x ∉ K ∧ x ∉ B ∧ x ∉ fixMu ℚ Ω (F * l)}
      (hHo.inter ((K.isClosed_of_isOpen hKo).isOpen_compl.inter ((B.isClosed_of_isOpen hBo).isOpen_compl.inter
        (Subgroup.isClosed_of_isOpen _ hCo).isOpen_compl))) ⟨x, hx⟩ (T * (F * l * r))
      (mul_ne_zero hT (mul_ne_zero hFl hr.ne_zero))
  exact ⟨q, A, φ, adm Ω l (l ^ m) N₀ F r q hlp hF hD.lev hD.cop hr hq (fun h => hqT (h.mul_left _)) ρ hρ A hA φ hφ
    hφH.1 hφH.2 hφC, fun h => hqT (h.mul_right _), hA, hφ, fun h => hφB ((hB φ).2 ⟨hφH.1, h⟩), hK φ hφH.1 hφK⟩

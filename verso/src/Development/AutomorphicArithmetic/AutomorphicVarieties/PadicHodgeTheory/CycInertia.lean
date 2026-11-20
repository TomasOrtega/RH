import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.FrobeniusLocalisation.locRoots
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Establish `hx : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Use `haveI := IntermediateField.adjoin.finiteDimensional hx`. Establish `hU` using `IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ_[l] {x})`. Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`. Introduce `σ hσ`.

Establish `hc : Continuous fun τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l => σ⁻¹ * τ` using `by fun_prop`. Establish `h1` using `(hU.preimage hc).mem_nhds (x := σ) (by simp)`. Use `Filter.mem_of_superset h1 fun τ hτ h => hσ ?_` and prove the remaining obligations. Establish `h2 : (σ⁻¹ * τ) x = x` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.mem_adjoin_simple_self _ _)`. Establish `h3 : τ x = y` using `h`.

Establish `h4 : σ ((σ⁻¹ * τ) x) = τ x`. Rewrite using `[← AlgEquiv.mul_apply, mul_inv_cancel_left]`. Use `show σ x = y`. Rewrite using `[← h3, ← h4, h2]`.
-/
private theorem UpperTheory.V.Loc.ci_closed (l : ℕ) [Fact l.Prime] (x y : PadicAlgCl l) :
    IsClosed {σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l | σ x = y} := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hx
  have hU := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ_[l] {x})
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro σ hσ
  have hc : Continuous fun τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l => σ⁻¹ * τ := by fun_prop
  have h1 := (hU.preimage hc).mem_nhds (x := σ) (by simp)
  refine Filter.mem_of_superset h1 fun τ hτ h => hσ ?_
  have h2 : (σ⁻¹ * τ) x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.mem_adjoin_simple_self _ _)
  have h3 : τ x = y := h
  have h4 : σ ((σ⁻¹ * τ) x) = τ x := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
  show σ x = y
  rw [← h3, ← h4, h2]

/- English proof (translation)
Rewrite using `[← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]`.
-/
private theorem UpperTheory.V.Loc.ci_dvd_sub_iff (l : ℕ) [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    (l : ℤ_[l]) ^ r ∣ x - y ↔ PadicInt.toZModPow r x = PadicInt.toZModPow r y := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

/- English proof (translation)
Rewrite using `[pow_eq_pow_mod a hx, pow_eq_pow_mod b hx, h]`.
-/
private theorem UpperTheory.V.Loc.ci_pow_congr {K : Type*} [Monoid K] {x : K} {M a b : ℕ} (hx : x ^ M = 1)
    (h : a ≡ b [MOD M]) : x ^ a = x ^ b := by
  rw [pow_eq_pow_mod a hx, pow_eq_pow_mod b hx, h]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Use `set v := M.factorization l with hv`. Establish `hcop : Nat.Coprime (ordCompl[l] M) (l ^ v)` using `(Nat.coprime_ordCompl hp hM).symm.pow_right _`. Use `haveI : NeZero (l ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Take `⟨c, h1, h2⟩` from `Nat.chineseRemainder hcop 1 (PadicInt.toZModPow v (a : ℤ_[l])).val`.

Establish `hc : ((c : ℕ) : ZMod (l ^ v)) = PadicInt.toZModPow v (a : ℤ_[l])`. Rewrite using `[(ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]`. Establish `hcoP : c.Coprime (l ^ v)`. Rewrite using `[← ZMod.isUnit_iff_coprime, hc]`. Conclude with `(Units.isUnit a).map _`.

Establish `hcoN : c.Coprime (ordCompl[l] M)`. Unfold `Nat.Coprime`. Rewrite using `[h1.gcd_eq, Nat.gcd_one_left]`. Use `⟨c, ?_, h1, fun k hk => ?_⟩` and prove the remaining obligations. Use `Nat.Coprime.mul_right hcoP hcoN` as an intermediate fact.

Rewrite `this` using `[hv, Nat.ordProj_mul_ordCompl_eq_self]`. Then use the resulting hypothesis. Establish `hd : (l : ℤ_[l]) ^ v ∣ (c : ℤ_[l]) - (a : ℤ_[l])`. Rewrite using `[UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast, hc]`. Use `(pow_dvd_pow _ hk).trans hd` as an intermediate fact. Rewrite `this` using `[UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast]`. Then use the resulting hypothesis.
-/
private theorem UpperTheory.V.Loc.ci_crt (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) (M : ℕ) (hM : M ≠ 0) :
    ∃ c : ℕ, c.Coprime M ∧ c ≡ 1 [MOD ordCompl[l] M] ∧
      ∀ k ≤ M.factorization l, (c : ZMod (l ^ k)) = PadicInt.toZModPow k (a : ℤ_[l]) := by
  have hp : l.Prime := Fact.out
  set v := M.factorization l with hv
  have hcop : Nat.Coprime (ordCompl[l] M) (l ^ v) := (Nat.coprime_ordCompl hp hM).symm.pow_right _
  haveI : NeZero (l ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨c, h1, h2⟩ := Nat.chineseRemainder hcop 1 (PadicInt.toZModPow v (a : ℤ_[l])).val
  have hc : ((c : ℕ) : ZMod (l ^ v)) = PadicInt.toZModPow v (a : ℤ_[l]) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]
  have hcoP : c.Coprime (l ^ v) := by
    rw [← ZMod.isUnit_iff_coprime, hc]
    exact (Units.isUnit a).map _
  have hcoN : c.Coprime (ordCompl[l] M) := by
    unfold Nat.Coprime
    rw [h1.gcd_eq, Nat.gcd_one_left]
  refine ⟨c, ?_, h1, fun k hk => ?_⟩
  · have := Nat.Coprime.mul_right hcoP hcoN
    rwa [hv, Nat.ordProj_mul_ordCompl_eq_self] at this
  · have hd : (l : ℤ_[l]) ^ v ∣ (c : ℤ_[l]) - (a : ℤ_[l]) := by
      rw [UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast, hc]
    have := (pow_dvd_pow _ hk).trans hd
    rwa [UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast] at this

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Take `⟨M, hM⟩ : ∃ M, M = n.factorial * l ^ n` from `⟨_, rfl⟩`. Establish `hM0 : M ≠ 0`. Rewrite using `[hM]`. Conclude with `mul_ne_zero n.factorial_ne_zero (pow_ne_zero _ hp.ne_zero)`.

Establish `hv : n ≤ M.factorization l` using `(hp.pow_dvd_iff_le_factorization hM0).1 (by rw [hM]; exact Dvd.intro_left _ rfl)`. Take `⟨c, hcM, hc1, hc2⟩` from `UpperTheory.V.Loc.ci_crt l a M hM0`. Establish `hval : ∀ (N : ℕ) (h : c.Coprime N), ((ZMod.unitOfCoprime c h : (ZMod N)ˣ) : ZMod N).val ≡ c [MOD N]`. Introduce `N h`. Rewrite using `[ZMod.coe_unitOfCoprime, ZMod.val_natCast]`.

Conclude with `Nat.mod_modEq _ _`. Take `⟨σ, hσ⟩` from `(UpperTheory.HF.loc_roots l M (Nat.pos_of_ne_zero hM0)).2 (ZMod.unitOfCoprime c hcM) 0 (by rw [pow_zero]; exact ((hval M hcM).of_dvd (Nat.ordCompl_dvd _ _)).trans hc1)`. Establish `hσc : ∀ d, d ∣ M → ∀ x : PadicAlgCl l, x ^ d = 1 → σ x = x ^ c`. Introduce `d ⟨e, he⟩ x hx`. Establish `hxM : x ^ M = 1` using `by rw [he, pow_mul, hx, one_pow]`.

Rewrite using `[hσ x hxM]`. Conclude with `UpperTheory.V.Loc.ci_pow_congr hxM (hval M hcM)`. Use `⟨σ, fun m hm hm0 hlm x hx => ?_, fun k hk x hx => ?_⟩` and prove the remaining obligations. Establish `hmM : m ∣ M`. Rewrite using `[hM]`.

Conclude with `(Nat.dvd_factorial hm0 hm).mul_right _`. Establish `hm' : m ∣ ordCompl[l] M` using `Nat.dvd_ordCompl_of_dvd_not_dvd hmM hlm`. Rewrite using `[hσc m hmM x hx, UpperTheory.V.Loc.ci_pow_congr hx (hc1.of_dvd hm'), pow_one]`. Establish `hkM : l ^ k ∣ M`. Rewrite using `[hM]`.

Conclude with `(pow_dvd_pow _ hk).mul_left _`. Use `haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Rewrite using `[hσc _ hkM x hx]`. Use `UpperTheory.V.Loc.ci_pow_congr hx ?_` and prove the remaining obligations. Rewrite using `[← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]`.

Conclude with `hc2 k (le_trans hk hv)`.
-/
private theorem UpperTheory.V.Loc.ci_fin (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) (n : ℕ) :
    ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l),
      (∀ m ≤ n, 0 < m → ¬ l ∣ m → ∀ x : PadicAlgCl l, x ^ m = 1 → σ x = x) ∧
      ∀ k ≤ n, ∀ x : PadicAlgCl l, x ^ l ^ k = 1 → σ x = x ^ (PadicInt.toZModPow k (a : ℤ_[l])).val := by
  have hp : l.Prime := Fact.out
  obtain ⟨M, hM⟩ : ∃ M, M = n.factorial * l ^ n := ⟨_, rfl⟩
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact mul_ne_zero n.factorial_ne_zero (pow_ne_zero _ hp.ne_zero)
  have hv : n ≤ M.factorization l :=
    (hp.pow_dvd_iff_le_factorization hM0).1 (by rw [hM]; exact Dvd.intro_left _ rfl)
  obtain ⟨c, hcM, hc1, hc2⟩ := UpperTheory.V.Loc.ci_crt l a M hM0
  have hval : ∀ (N : ℕ) (h : c.Coprime N), ((ZMod.unitOfCoprime c h : (ZMod N)ˣ) : ZMod N).val ≡ c [MOD N] := by
    intro N h
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  obtain ⟨σ, hσ⟩ := (UpperTheory.HF.loc_roots l M (Nat.pos_of_ne_zero hM0)).2 (ZMod.unitOfCoprime c hcM) 0
    (by rw [pow_zero]; exact ((hval M hcM).of_dvd (Nat.ordCompl_dvd _ _)).trans hc1)
  have hσc : ∀ d, d ∣ M → ∀ x : PadicAlgCl l, x ^ d = 1 → σ x = x ^ c := by
    intro d ⟨e, he⟩ x hx
    have hxM : x ^ M = 1 := by rw [he, pow_mul, hx, one_pow]
    rw [hσ x hxM]
    exact UpperTheory.V.Loc.ci_pow_congr hxM (hval M hcM)
  refine ⟨σ, fun m hm hm0 hlm x hx => ?_, fun k hk x hx => ?_⟩
  · have hmM : m ∣ M := by
      rw [hM]
      exact (Nat.dvd_factorial hm0 hm).mul_right _
    have hm' : m ∣ ordCompl[l] M := Nat.dvd_ordCompl_of_dvd_not_dvd hmM hlm
    rw [hσc m hmM x hx, UpperTheory.V.Loc.ci_pow_congr hx (hc1.of_dvd hm'), pow_one]
  · have hkM : l ^ k ∣ M := by
      rw [hM]
      exact (pow_dvd_pow _ hk).mul_left _
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [hσc _ hkM x hx]
    refine UpperTheory.V.Loc.ci_pow_congr hx ?_
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    exact hc2 k (le_trans hk hv)

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Set `S : ℕ → Set (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)` to `fun n => {σ | (∀ m ≤ n, 0 < m → ¬ l ∣ m → ∀ x : PadicAlgCl l, x ^ m = 1 → σ x = x) ∧ ∀ k ≤ n, ∀ x : PadicAlgCl l, x ^ l ^ k = 1 → σ x = x ^ (PadicInt.toZModPow k (a : ℤ_[l])).val}`. Establish `hcl : ∀ n, IsClosed (S n)`. Introduce `n`. Simplify using `only [S, Set.setOf_and, Set.setOf_forall]`.

Use `IsClosed.inter ?_ ?_` and prove the remaining obligations. Conclude with `isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => UpperTheory.V.Loc.ci_closed l _ _`. Conclude with `isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => UpperTheory.V.Loc.ci_closed l _ _`. Use `haveI : IsGalois ℚ_[l] (PadicAlgCl l) := {}`. Take `⟨σ, hσ⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S (fun n σ hσ => ⟨fun m hm => hσ.1 m (hm.trans n.le_succ), fun k hk => hσ.2 k (hk.trans n.le_succ)⟩) (fun n => UpperTheory.V.Loc.ci_fin l a n) (hcl 0).isCompact hcl`.

Rewrite `hσ` using `[Set.mem_iInter]`. Use `⟨σ, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_, ?_⟩` and prove the remaining obligations. Unfold `MaximalUnramifiedExtension at hx`. Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem x hx`.

Take `⟨m, hm0, hlm, hx⟩` from `hx`. Conclude with `(hσ m).1 m le_rfl hm0 hlm x hx`. Consider the case `algebraMap r => exact σ.commutes r`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`. Consider the case `inv x _ hx => rw [map_inv₀, hx]`.

Consider the case `mul x y _ _ hx hy => rw [map_mul, hx, hy]`. Use `haveI (i : ℕ) : HasEnoughRootsOfUnity (PadicAlgCl l) (l ^ i) := by haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩ infer_instance`. Use `Units.ext (PadicInt.ext_of_toZModPow.1 fun k => ?_)` and prove the remaining obligations. Use `haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Take `⟨η, hη⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ k)`.

Establish `h1` using `cyclotomicCharacter.spec l (n := k) (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (PadicAlgCl l) σ) η hη.pow_eq_one`. Establish `h2` using `(hσ k).2 k le_rfl η hη.pow_eq_one`. Establish `h3` using `h1.symm.trans h2`. Conclude with `ZMod.val_injective _ (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)`.
-/
private theorem UpperTheory.V.Loc.ci_surj (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) : ∃ g ∈ Iq l, cyc l l g = a := by
  have hp : l.Prime := Fact.out
  let S : ℕ → Set (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) := fun n =>
    {σ | (∀ m ≤ n, 0 < m → ¬ l ∣ m → ∀ x : PadicAlgCl l, x ^ m = 1 → σ x = x) ∧
      ∀ k ≤ n, ∀ x : PadicAlgCl l, x ^ l ^ k = 1 → σ x = x ^ (PadicInt.toZModPow k (a : ℤ_[l])).val}
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    simp only [S, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_iInter fun _ => UpperTheory.V.Loc.ci_closed l _ _
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        UpperTheory.V.Loc.ci_closed l _ _
  haveI : IsGalois ℚ_[l] (PadicAlgCl l) := {}
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
    (fun n σ hσ => ⟨fun m hm => hσ.1 m (hm.trans n.le_succ), fun k hk => hσ.2 k (hk.trans n.le_succ)⟩)
    (fun n => UpperTheory.V.Loc.ci_fin l a n) (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_, ?_⟩
  · unfold MaximalUnramifiedExtension at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm0, hlm, hx⟩ := hx
      exact (hσ m).1 m le_rfl hm0 hlm x hx
    | algebraMap r => exact σ.commutes r
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  · haveI (i : ℕ) : HasEnoughRootsOfUnity (PadicAlgCl l) (l ^ i) := by
      haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
      infer_instance
    refine Units.ext (PadicInt.ext_of_toZModPow.1 fun k => ?_)
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ k)
    have h1 := cyclotomicCharacter.spec l (n := k)
      (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (PadicAlgCl l) σ) η hη.pow_eq_one
    have h2 := (hσ k).2 k le_rfl η hη.pow_eq_one
    have h3 := h1.symm.trans h2
    exact ZMod.val_injective _ (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hu : IsUnit (((l + 1 : ℕ)) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`. Conclude with `PadicInt.norm_natCast_eq_one_iff.2 (by simp)`. Use `⟨hu.unit, fun h => ?_⟩` and prove the remaining obligations.

Take `⟨n, hn, h⟩` from `isOfFinOrder_iff_pow_eq_one.1 h`. Establish `h2` using `congrArg Units.val h`. Rewrite `h2` using `[Units.val_pow_eq_pow_val, hu.unit_spec, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one]`. Use `hp.one_lt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem UpperTheory.V.Loc.ci_inf (l : ℕ) [Fact l.Prime] : ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hp : l.Prime := Fact.out
  have hu : IsUnit (((l + 1 : ℕ)) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  refine ⟨hu.unit, fun h => ?_⟩
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have h2 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, hu.unit_spec, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one,
    Nat.pow_eq_one] at h2
  have := hp.one_lt
  omega

/- English proof (translation)
Introduce `l _`. Use `⟨UpperTheory.V.Loc.ci_surj l, fun U hU => ?_⟩` and prove the remaining obligations. Use `haveI : IsGalois ℚ_[l] (Om l) := {}`. Use `haveI : Finite (GQ l ⧸ U) := U.quotient_finite_of_isOpen hU`. Use `haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`.

Establish `hc : Continuous (cyc l l)` using `cyclotomicCharacter.continuous l ℚ_[l] (Om l)`. Prove the components needed by the constructor for the conclusion. Establish `hs : Function.Surjective ((cyc l l).comp (Iq l).subtype)` using `fun u => by`. Take `⟨g, hg, h⟩` from `UpperTheory.V.Loc.ci_surj l u`. Conclude with `⟨⟨g, hg⟩, h⟩`.

Establish `he : (U ⊓ Iq l).map (cyc l l) = (U.subgroupOf (Iq l)).map ((cyc l l).comp (Iq l).subtype)`. Rewrite using `[← Subgroup.map_map, Subgroup.subgroupOf_map_subtype]`. Use `haveI : ((U ⊓ Iq l).map (cyc l l)).FiniteIndex := ⟨by`. Rewrite using `[he]`. Conclude with `ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (Subgroup.index_map_dvd _ hs)⟩`.

Use `Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_` and prove the remaining obligations. Rewrite using `[Subgroup.coe_map, Subgroup.coe_inf]`. Conclude with `(((U.isClosed_of_isOpen hU).inter (InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension l))).isCompact.image hc).isClosed`. Take `⟨u, hu⟩` from `UpperTheory.V.Loc.ci_inf l`. Take `⟨g, hg, h⟩` from `UpperTheory.V.Loc.ci_surj l u`.

Take `⟨n, hn, -, hgn⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := U)) g`. Use `⟨g ^ n, ⟨hgn, pow_mem hg n⟩, fun hf => hu ?_⟩` and prove the remaining obligations. Rewrite `hf` using `[map_pow, h]`. Conclude with `hf.of_pow hn.ne'`.
-/
theorem UpperTheory.V.Loc.cycInertia :
    ∀ (l : ℕ) [Fact l.Prime], (∀ u : ℤ_[l]ˣ, ∃ g ∈ Iq l, cyc l l g = u) ∧ ∀ U : Subgroup (GQ l), IsOpen (U : Set (GQ l)) → IsOpen (((U ⊓ Iq l).map (cyc l l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) ∧ ∃ s ∈ U ⊓ Iq l, ¬ IsOfFinOrder (cyc l l s) := by
  intro l _
  refine ⟨UpperTheory.V.Loc.ci_surj l, fun U hU => ?_⟩
  haveI : IsGalois ℚ_[l] (Om l) := {}
  haveI : Finite (GQ l ⧸ U) := U.quotient_finite_of_isOpen hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : Continuous (cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (Om l)
  constructor
  · have hs : Function.Surjective ((cyc l l).comp (Iq l).subtype) := fun u => by
      obtain ⟨g, hg, h⟩ := UpperTheory.V.Loc.ci_surj l u
      exact ⟨⟨g, hg⟩, h⟩
    have he : (U ⊓ Iq l).map (cyc l l) = (U.subgroupOf (Iq l)).map ((cyc l l).comp (Iq l).subtype) := by
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
    haveI : ((U ⊓ Iq l).map (cyc l l)).FiniteIndex := ⟨by
      rw [he]
      exact ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (Subgroup.index_map_dvd _ hs)⟩
    refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
    rw [Subgroup.coe_map, Subgroup.coe_inf]
    exact (((U.isClosed_of_isOpen hU).inter
      (InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension l))).isCompact.image hc).isClosed
  · obtain ⟨u, hu⟩ := UpperTheory.V.Loc.ci_inf l
    obtain ⟨g, hg, h⟩ := UpperTheory.V.Loc.ci_surj l u
    obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.FiniteIndex.index_ne_zero (H := U)) g
    refine ⟨g ^ n, ⟨hgn, pow_mem hg n⟩, fun hf => hu ?_⟩
    rw [map_pow, h] at hf
    exact hf.of_pow hn.ne'

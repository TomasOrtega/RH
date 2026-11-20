import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

open GroundTheory.PAdicHodge GroundTheory.PAdicHodge.EigenChar

/- English proof (translation)
Introduce `l _ h L _`. Set `H : Subgroup Gal(Om l/↥L)` to `{ carrier := {σ | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w} mul_mem' := by`. Introduce `a b ha hb w hw`. Use `show a (b w) = w`. Rewrite using `[hb w hw, ha w hw]`.

Use the proof step `one_mem' := by`. Introduce `w _`. Both sides reduce to the same expression. Use the proof step `inv_mem' := by`. Introduce `a ha w hw`.

Establish `haw : a w = w` using `ha w hw`. Combine the equalities or inequalities in the displayed calculation. Introduce `hfin`. Take `⟨M, hM⟩ : ∃ M : Subgroup ℤ_[l]ˣ, M = H.map (GroundTheory.PAdicHodge.cycloChar L)` from `⟨_, rfl⟩`. Establish `hMfin : Finite M`.

Establish `hs : (M : Set ℤ_[l]ˣ).Finite`. Rewrite using `[hM, Subgroup.coe_map]`. Conclude with `hfin`. Conclude with `hs.to_subtype`. Take `⟨n, hnM⟩ : ∃ n : ℕ, n = Nat.card M` from `⟨_, rfl⟩`.

Establish `hn : 0 < n`. Rewrite using `[hnM]`. Conclude with `Nat.card_pos`. Establish `hpow : ∀ σ ∈ H, (GroundTheory.PAdicHodge.cycloChar L σ) ^ n = 1`. Introduce `σ hσ`.

Establish `hmem : GroundTheory.PAdicHodge.cycloChar L σ ∈ M`. Rewrite using `[hM]`. Conclude with `Subgroup.mem_map_of_mem _ hσ`. Establish `h1 : (⟨GroundTheory.PAdicHodge.cycloChar L σ, hmem⟩ : M) ^ n = 1`. Rewrite using `[hnM]`.

Conclude with `pow_card_eq_one'`. Establish `h2` using `congrArg Subtype.val h1`. Simplify using `using h2`. Establish `hroots : ∀ σ : Gal(Om l/↥L), GroundTheory.LocalField.unramifiedDegree ↥L (Om l) σ = 1 → σ ∈ H`. Introduce `σ hσ`.

Establish `hfix` using `(GroundTheory.LocalField.unramifiedDegree_eq_one_iff σ).mp hσ`. Establish `hS : ∀ y ∈ GroundTheory.PAdicHodge.primeToPRoots l, σ y = y`. Introduce and unpack `y ⟨m, hm0, hmcop, hym⟩`. Apply `hfix` to reduce the goal to its premises. Establish `hcop : Nat.Coprime l m` using `Nat.Coprime.symm hmcop`.

Establish `hmod : l ^ Nat.totient m ≡ 1 [MOD m]` using `Nat.ModEq.pow_totient hcop`. Establish `hle : 1 ≤ l ^ Nat.totient m` using `Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out)`. Establish `hdvd : m ∣ l ^ Nat.totient m - 1` using `(Nat.modEq_iff_dvd' hle).mp hmod.symm`. Take `⟨c, hc⟩` from `hdvd`. Use `GroundTheory.PAdicHodge.EigenWitt.mem_unramifiedRoots_of_pow_eq_one (L := L) (Nat.totient_pos.2 hm0) ?_` and prove the remaining obligations.

Rewrite using `[hc, pow_mul, hym, one_pow]`. Establish `hσ' : (σ.restrictScalars ℚ_[l]) ∈ (IntermediateField.adjoin ℚ_[l] (GroundTheory.PAdicHodge.primeToPRoots l)).fixingSubgroup` using `GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff.mpr (fun y hy => hS y hy)`. Use `show ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w`. Introduce `w hw`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ' w hw`.

Set `ψ : Gal(Om l/↥L) →* ℤ_[l]ˣ` to `(powMonoidHom n).comp (GroundTheory.PAdicHodge.cycloChar L)`. Establish `hψc : Continuous ψ` using `(GroundTheory.PAdicHodge.continuous_cycloChar L).pow n`. Establish `hψu : ∀ σ, GroundTheory.LocalField.unramifiedDegree ↥L (Om l) σ = 1 → ψ σ = 1`. Introduce `σ hσ`. Conclude with `hpow σ (hroots σ hσ)`.

Take `⟨f, hf, x, hx0, hx⟩` from `h L ψ hψc hψu`. Take `⟨j, hj⟩ : ∃ j : ℤ, j = -((n * f : ℕ) : ℤ)` from `⟨_, rfl⟩`. Establish `hj0 : j ≠ 0`. Rewrite using `[hj, neg_ne_zero, Nat.cast_ne_zero]`. Conclude with `Nat.mul_ne_zero hn.ne' hf.ne'`.

Establish `hinv : x ∈ (GroundTheory.PAdicHodge.cpTwistRep L j).invariants`. Express the relevant statement in the definitionally equal form `∀ σ, (GroundTheory.PAdicHodge.cpTwistRep L j σ) x = x`. Introduce `σ`. Establish `key : (((GroundTheory.PAdicHodge.cycloChar L σ ^ j : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) * ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) ^ f = 1`. Establish `hψσ : ψ σ = GroundTheory.PAdicHodge.cycloChar L σ ^ n` using `rfl`.

Establish `hu : GroundTheory.PAdicHodge.cycloChar L σ ^ j * (GroundTheory.PAdicHodge.cycloChar L σ ^ n) ^ f = 1`. Rewrite using `[hj, ← pow_mul, zpow_neg, zpow_natCast, inv_mul_cancel]`. Rewrite using `[hψσ, ← PadicInt.coe_pow, ← PadicInt.coe_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, hu]`. Simplify using the standard rewrite rules. Rewrite using `[GroundTheory.PAdicHodge.cpTwistRep_apply, hx σ, GroundTheory.PAdicHodge.twistScalar, ← mul_assoc, ← map_mul, key, map_one, one_mul]`.

Rewrite `hinv` using `[GroundTheory.PAdicHodge.cpTwistRep_invariants_eq_bot L hj0]`. Conclude with `hx0 ((Submodule.mem_bot _).mp hinv)`.
-/
theorem cycloChar_inertia_image_infinite : ∀ {l : ℕ} [Fact l.Prime],
    (∀ (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E] (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ), Continuous ψ →
      (∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) →
      ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
        σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x) →
    ∀ (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥L],
      ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite := by
  intro l _ h L _
  let H : Subgroup Gal(Om l/↥L) :=
    { carrier := {σ | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}
      mul_mem' := by
        intro a b ha hb w hw
        show a (b w) = w
        rw [hb w hw, ha w hw]
      one_mem' := by
        intro w _
        rfl
      inv_mem' := by
        intro a ha w hw
        have haw : a w = w := ha w hw
        calc a⁻¹ w = a⁻¹ (a w) := by rw [haw]
          _ = w := by simp [AlgEquiv.aut_inv] }
  intro hfin
  obtain ⟨M, hM⟩ : ∃ M : Subgroup ℤ_[l]ˣ, M = H.map (GroundTheory.PAdicHodge.cycloChar L) := ⟨_, rfl⟩
  have hMfin : Finite M := by
    have hs : (M : Set ℤ_[l]ˣ).Finite := by
      rw [hM, Subgroup.coe_map]
      exact hfin
    exact hs.to_subtype
  obtain ⟨n, hnM⟩ : ∃ n : ℕ, n = Nat.card M := ⟨_, rfl⟩
  have hn : 0 < n := by
    rw [hnM]
    exact Nat.card_pos
  have hpow : ∀ σ ∈ H, (GroundTheory.PAdicHodge.cycloChar L σ) ^ n = 1 := by
    intro σ hσ
    have hmem : GroundTheory.PAdicHodge.cycloChar L σ ∈ M := by
      rw [hM]
      exact Subgroup.mem_map_of_mem _ hσ
    have h1 : (⟨GroundTheory.PAdicHodge.cycloChar L σ, hmem⟩ : M) ^ n = 1 := by
      rw [hnM]
      exact pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hroots : ∀ σ : Gal(Om l/↥L), GroundTheory.LocalField.unramifiedDegree ↥L (Om l) σ = 1 → σ ∈ H := by
    intro σ hσ
    have hfix := (GroundTheory.LocalField.unramifiedDegree_eq_one_iff σ).mp hσ
    have hS : ∀ y ∈ GroundTheory.PAdicHodge.primeToPRoots l, σ y = y := by
      rintro y ⟨m, hm0, hmcop, hym⟩
      apply hfix
      have hcop : Nat.Coprime l m := Nat.Coprime.symm hmcop
      have hmod : l ^ Nat.totient m ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
      have hle : 1 ≤ l ^ Nat.totient m := Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out)
      have hdvd : m ∣ l ^ Nat.totient m - 1 := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      obtain ⟨c, hc⟩ := hdvd
      refine GroundTheory.PAdicHodge.EigenWitt.mem_unramifiedRoots_of_pow_eq_one (L := L)
        (Nat.totient_pos.2 hm0) ?_
      rw [hc, pow_mul, hym, one_pow]
    have hσ' : (σ.restrictScalars ℚ_[l]) ∈
        (IntermediateField.adjoin ℚ_[l] (GroundTheory.PAdicHodge.primeToPRoots l)).fixingSubgroup :=
      GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff.mpr (fun y hy => hS y hy)
    show ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w
    intro w hw
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ' w hw
  let ψ : Gal(Om l/↥L) →* ℤ_[l]ˣ := (powMonoidHom n).comp (GroundTheory.PAdicHodge.cycloChar L)
  have hψc : Continuous ψ := (GroundTheory.PAdicHodge.continuous_cycloChar L).pow n
  have hψu : ∀ σ, GroundTheory.LocalField.unramifiedDegree ↥L (Om l) σ = 1 → ψ σ = 1 := by
    intro σ hσ
    exact hpow σ (hroots σ hσ)
  obtain ⟨f, hf, x, hx0, hx⟩ := h L ψ hψc hψu
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = -((n * f : ℕ) : ℤ) := ⟨_, rfl⟩
  have hj0 : j ≠ 0 := by
    rw [hj, neg_ne_zero, Nat.cast_ne_zero]
    exact Nat.mul_ne_zero hn.ne' hf.ne'
  have hinv : x ∈ (GroundTheory.PAdicHodge.cpTwistRep L j).invariants := by
    change ∀ σ, (GroundTheory.PAdicHodge.cpTwistRep L j σ) x = x
    intro σ
    have key : (((GroundTheory.PAdicHodge.cycloChar L σ ^ j : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) *
        ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) ^ f = 1 := by
      have hψσ : ψ σ = GroundTheory.PAdicHodge.cycloChar L σ ^ n := rfl
      have hu : GroundTheory.PAdicHodge.cycloChar L σ ^ j * (GroundTheory.PAdicHodge.cycloChar L σ ^ n) ^ f = 1 := by
        rw [hj, ← pow_mul, zpow_neg, zpow_natCast, inv_mul_cancel]
      rw [hψσ, ← PadicInt.coe_pow, ← PadicInt.coe_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, hu]
      simp
    rw [GroundTheory.PAdicHodge.cpTwistRep_apply, hx σ, GroundTheory.PAdicHodge.twistScalar, ← mul_assoc, ← map_mul, key,
      map_one, one_mul]
  rw [GroundTheory.PAdicHodge.cpTwistRep_invariants_eq_bot L hj0] at hinv
  exact hx0 ((Submodule.mem_bot _).mp hinv)

end GlobalTheory.CompanionTheory.LTPer

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CyclotomicGlobalSections

/- English proof (translation)
Take `⟨hH, hsep⟩` from `hA`. Use `haveI := hH`. Establish `hqk : (q : IsLocalRing.ResidueField A) ≠ 0`. Use `hq.map (IsLocalRing.residue A)` as an intermediate fact. Simplify using `using this.ne_zero`.

Establish `hsepk : (Polynomial.cyclotomic q (IsLocalRing.ResidueField A)).Separable` using `(Polynomial.separable_X_pow_sub_C 1 hqk one_ne_zero).of_dvd (Polynomial.cyclotomic.dvd_X_pow_sub_one q _)`. Establish `hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField A)).degree ≠ 0`. Rewrite using `[Polynomial.degree_cyclotomic]`. Conclude with `(Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'` after adjusting the coercions. Take `⟨a0, ha0⟩` from `IsSepClosed.exists_root _ hdeg hsepk`.

Take `⟨b0, rfl⟩` from `IsLocalRing.residue_surjective a0`. Establish `hred : ∀ p : Polynomial A, IsLocalRing.residue A (p.eval b0) = (p.map (IsLocalRing.residue A)).eval (IsLocalRing.residue A b0)` using `fun p => by`. Rewrite using `[Polynomial.eval_map, Polynomial.eval₂_hom]`. Establish `h1 : (Polynomial.cyclotomic q A).eval b0 ∈ IsLocalRing.maximalIdeal A`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, hred, Polynomial.map_cyclotomic]`.

Apply the tactic sequence `all_goals exact ha0`. Establish `h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q A)).eval b0)`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, hred, ← Polynomial.derivative_map, Polynomial.map_cyclotomic]`. Use `hsepk.aeval_derivative_ne_zero (x := IsLocalRing.residue A b0) (by simpa [Polynomial.aeval_def] using ha0)` as an intermediate fact. Simplify `this` using `[Polynomial.aeval_def]`.

Take `⟨a, ha, -⟩` from `HenselianLocalRing.is_henselian (Polynomial.cyclotomic q A) (Polynomial.cyclotomic.monic q A) b0 h1 h2`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `ha`.
-/
theorem exists_cyclotomic_root (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A)) :
    ∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨hH, hsep⟩ := hA
  haveI := hH
  have hqk : (q : IsLocalRing.ResidueField A) ≠ 0 := by
    have := hq.map (IsLocalRing.residue A)
    simpa using this.ne_zero
  have hsepk : (Polynomial.cyclotomic q (IsLocalRing.ResidueField A)).Separable :=
    (Polynomial.separable_X_pow_sub_C 1 hqk one_ne_zero).of_dvd (Polynomial.cyclotomic.dvd_X_pow_sub_one q _)
  have hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField A)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  obtain ⟨a0, ha0⟩ := IsSepClosed.exists_root _ hdeg hsepk
  obtain ⟨b0, rfl⟩ := IsLocalRing.residue_surjective a0
  have hred : ∀ p : Polynomial A, IsLocalRing.residue A (p.eval b0) =
      (p.map (IsLocalRing.residue A)).eval (IsLocalRing.residue A b0) := fun p => by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have h1 : (Polynomial.cyclotomic q A).eval b0 ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, hred, Polynomial.map_cyclotomic]
    all_goals exact ha0
  have h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q A)).eval b0) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hred, ← Polynomial.derivative_map, Polynomial.map_cyclotomic]
    have := hsepk.aeval_derivative_ne_zero (x := IsLocalRing.residue A b0) (by simpa [Polynomial.aeval_def] using ha0)
    simpa [Polynomial.aeval_def] using this
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.cyclotomic q A)
    (Polynomial.cyclotomic.monic q A) b0 h1 h2
  refine ⟨a, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ha

end GlobalTheory.EtC.CyclotomicGlobalSections

open GlobalTheory.EtC.ConnectedGlobalSections in

/- English proof (translation)
Introduce `q _ A _ hA hq j`. Take `⟨ζ0, hζ0⟩` from `GlobalTheory.EtC.CyclotomicGlobalSections.exists_cyclotomic_root q A hA hq`. Take `⟨hH, -⟩` from `hA`. Use `haveI := hH`. Take `⟨-, e, -, -⟩` from `GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q j)`.

Use `haveI : Nonempty (Spec (CommRingCat.of A)) := inferInstance`. Set `ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤)` to `Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ⟨ζ0, hq, hζ0⟩`. Establish `hidem : ∀ x : A, IsIdempotentElem x → x = 0 ∨ x = 1` using `fun x hx => by`. Establish `h0 : x * (1 - x) = 0` using `by rw [mul_sub, mul_one, hx.eq, sub_self]`. Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self x with hu | hu` into its components or cases.

Conclude with `Or.inr (sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)).symm`. Conclude with `Or.inl ((hu.mul_left_eq_zero).1 h0)`. Set `φ : ZMod q →+ Sec (tw q j) (Spec (CommRingCat.of A))` to `{ toFun := fun c => (ULift.up c : ULift.{1} (ZMod q)) • twGen j ζ map_zero' := zero_smul _ _ map_add' := fun c d => add_smul (ULift.up c : ULift.{1} (ZMod q)) (ULift.up d) (twGen j ζ) }`. Establish `hφ : ∀ c : ZMod q, φ c = c.val • twGen j ζ` using `fun c => by`. Rewrite using `[nsmul_eq_up, ZMod.natCast_zmod_val]`.

Both sides reduce to the same expression. Establish `hbij : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion. Introduce `c d h`. Rewrite `h` using `[hφ, hφ]`.

Conclude with `scalar_eq ζ c d h`. Introduce `y`. Take `⟨n, rfl⟩` from `sec_eq_nsmul _ (clopen_of_idem A hidem) ζ y`. Conclude with `⟨(n : ZMod q), by rw [hφ, nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val]⟩`. Conclude with `⟨((AddEquiv.ofBijective φ hbij).trans (e _)).symm⟩`.
-/
theorem GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ j : ℤ, Nonempty (Ht q (sp A) 0 j ≃+ ZMod q) := by
  intro q _ A _ hA hq j
  obtain ⟨ζ0, hζ0⟩ := GlobalTheory.EtC.CyclotomicGlobalSections.exists_cyclotomic_root q A hA hq
  obtain ⟨hH, -⟩ := hA
  haveI := hH
  obtain ⟨-, e, -, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q j)
  haveI : Nonempty (Spec (CommRingCat.of A)) := inferInstance
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ⟨ζ0, hq, hζ0⟩
  have hidem : ∀ x : A, IsIdempotentElem x → x = 0 ∨ x = 1 := fun x hx => by
    have h0 : x * (1 - x) = 0 := by rw [mul_sub, mul_one, hx.eq, sub_self]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with hu | hu
    · exact Or.inr (sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)).symm
    · exact Or.inl ((hu.mul_left_eq_zero).1 h0)
  let φ : ZMod q →+ Sec (tw q j) (Spec (CommRingCat.of A)) :=
    { toFun := fun c => (ULift.up c : ULift.{1} (ZMod q)) • twGen j ζ
      map_zero' := zero_smul _ _
      map_add' := fun c d => add_smul (ULift.up c : ULift.{1} (ZMod q)) (ULift.up d) (twGen j ζ) }
  have hφ : ∀ c : ZMod q, φ c = c.val • twGen j ζ := fun c => by
    rw [nsmul_eq_up, ZMod.natCast_zmod_val]; rfl
  have hbij : Function.Bijective φ := by
    constructor
    · intro c d h
      rw [hφ, hφ] at h
      exact scalar_eq ζ c d h
    · intro y
      obtain ⟨n, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A hidem) ζ y
      exact ⟨(n : ZMod q), by rw [hφ, nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val]⟩
  exact ⟨((AddEquiv.ofBijective φ hbij).trans (e _)).symm⟩

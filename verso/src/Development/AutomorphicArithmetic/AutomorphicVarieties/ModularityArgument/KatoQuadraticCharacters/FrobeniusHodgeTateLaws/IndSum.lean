import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SerVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SerEqZmOfParity

open UpperTheory.V.Z.Kato.Joint GlobalTheory.EisM GlobalTheory.KummerEisensteinGalois

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem pm_one {R : Type*} [CommRing R] {K : Type*} [Field K] (χ : MulChar R K) : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul]; simp

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
private theorem ind_sum {N : ℕ} [NeZero N] (ν : DirichletCharacter ℂ N) (v : (ZMod N)ˣ) (B : ZMod N) :
    ∑ u : (ZMod N)ˣ, ν u * (if B = (u : ZMod N) * v then 1 else 0) = ν⁻¹ v * ν B := by
  by_cases hB : IsUnit B
  · obtain ⟨w, rfl⟩ := hB
    have h : ∀ u : (ZMod N)ˣ, ((w : ZMod N) = (u : ZMod N) * v) ↔ w * v⁻¹ = u := fun u => by
      rw [← Units.val_mul, Units.val_inj, mul_inv_eq_iff_eq_mul]
    simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Units.val_mul, map_mul]
    rw [mul_comm, MulChar.inv_apply_eq_inv']
    congr 1
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul]; simp
  · rw [MulChar.map_nonunit _ hB, mul_zero]
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [if_neg, mul_zero]
    rintro rfl
    exact hB (u * v).isUnit

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
private theorem twb_sum {N : ℕ} [NeZero N] (θ χ : DirichletCharacter ℂ N) (hχ : χ (-1) = -1) (b : ℤ) (hb : IsCoprime b N) (B : ℤ) :
    ∑ u : (ZMod N)ˣ, (θ * χ) u * twb N (θ (-1)) (((u : ZMod N).val : ℤ) * b) B =
      2 * (θ * χ)⁻¹ (b : ZMod N) * ch (θ * χ) B := by
  obtain ⟨v, hv⟩ : IsUnit (b : ZMod N) := (ZMod.coe_int_isUnit_iff_isCoprime b N).mpr hb.symm
  have h1 := ind_sum (θ * χ) v B
  have h2 := ind_sum (θ * χ) v (-B)
  have h3 : (θ * χ) (-(B : ZMod N)) = -θ (-1) * (θ * χ) B := by
    rw [← neg_one_mul (B : ZMod N), map_mul, MulChar.mul_apply θ χ (-1), hχ]; ring
  simp only [neg_eq_iff_eq_neg] at h2
  simp only [twb, ch, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, ← hv, mul_sub, Finset.sum_sub_distrib,
    mul_left_comm _ (θ (-1)), ← Finset.mul_sum]
  rw [h1, h2, h3]
  linear_combination ((θ * χ)⁻¹ v * (θ * χ) B) * pm_one θ

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem Zm_sum {ι : Type*} (S : Finset ι) (k l : ℕ) (u : ℤ → ℂ) (c : ι → ℂ) (v : ι → ℤ → ℂ) (e : ℂ) (w : ℤ → ℂ)
    (F : ℕ → ℕ → ℂ) (h : ∀ B, ∑ j ∈ S, c j * v j B = e * w B) (n : ℕ) :
    ∑ j ∈ S, c j * Zm k l u (v j) F n = e * Zm k l u w F n := by
  simp only [Zm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp
  · calc _ = (x.1 : ℂ) ^ (k - 2) * u x.1 * F x.1 y.2 * ∑ j ∈ S, c j * v j y.1 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by rw [h]; ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Kato.Joint.avgEq :
    UpperTheory.V.Z.Kato.Joint.AvgEq := by
  intro l _ ι N _ θ χ m k ψ a b _ _ hk ho hχ ha hb
  refine ⟨fun hne => ?_, fun a' b' haa hbb => ?_, fun hs i => ?_⟩
  · funext i
    apply ι.injective
    have h1 : ι (ψ (-1)) * ι (ψ (-1)) = 1 := by rw [← map_mul, pm_one, map_one]
    have h2 := pm_one θ
    have h3 : ι (ψ (-1)) + θ (-1) = 0 := by
      refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
      linear_combination h1 - h2
    have h4 : 1 + ι (ψ (-1)) * θ (-1) = 0 := by linear_combination θ (-1) * h3 - h2
    rw [ser_eq_Zm ι N θ m k ψ a b hk ho ha, h4]
    simp
  · have e1 : (a : ZMod N) = a' := (ZMod.intCast_eq_intCast_iff _ _ _).mpr haa
    have e2 : (b : ZMod N) = b' := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hbb
    have ha' : IsCoprime a' N := by
      refine ((ZMod.coe_int_isUnit_iff_isCoprime a' N).mp ?_).symm
      rw [← e1]
      exact (ZMod.coe_int_isUnit_iff_isCoprime a N).mpr ha.symm
    have e3 : twb N (ι (ψ (-1))) b = twb N (ι (ψ (-1))) b' := by
      funext B; simp only [twb, e2]
    funext i
    apply ι.injective
    rw [ser_eq_Zm ι N θ m k ψ a b hk ho ha, ser_eq_Zm ι N θ m k ψ a' b' hk ho ha', e1, e3]
  · have hu : ∀ u : (ZMod N)ˣ, IsCoprime (((u : ZMod N).val : ℤ) * a) N := fun u =>
      IsCoprime.mul_left (Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime u)) ha
    have key := Zm_sum Finset.univ k l (hat θ) _ _ _ _
      (fun A d => ι (ψ ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) (twb_sum θ χ hχ b hb) (l ^ m * i)
    simp only [ser_eq_Zm_of_parity ι N θ m k ψ _ _ hk ho (hu _) hs, frm, Uo_iterate]
    calc _ = θ (a : ZMod N) * ∑ u : (ZMod N)ˣ, (θ * χ) u * Zm k l (hat θ) (twb N (θ (-1)) (((u : ZMod N).val : ℤ) * b))
            (fun A d => ι (ψ ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) (l ^ m * i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, map_mul θ, MulChar.mul_apply]
          ring
      _ = _ := by rw [key]; ring

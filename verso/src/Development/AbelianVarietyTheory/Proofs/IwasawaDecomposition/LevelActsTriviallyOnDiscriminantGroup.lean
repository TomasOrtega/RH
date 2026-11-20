import Mathlib
import Formalism.LocalToGlobal.HermitianForms.DefsGH
import Formalism.LocalToGlobal.Columns.RecLevelLocT
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `[sigR, inclE]`.
-/
theorem sigR_inclE_adic (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E) :
    sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) a) =
      inclE (F := F) (v.adicCompletion F) (σ a) := by
  simp [sigR, inclE]

/- English proof (translation)
Establish `key : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F))`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨x, b, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)`. Use `show sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E b)) ∈ intV E v`. Rewrite using `[sigR_inclE_adic]`.

Establish `h : IsIntegral ℤ ((σ : E →+* E) (algebraMap (𝓞 E) E b))` using `(RingOfIntegers.isIntegral_coe b).map ((σ : E →+* E).toIntAlgHom)`. Conclude with `Formalism.UG.P.easyc_inclE_mem (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _ ⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ _⟩`. Use `show sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) ∈ intV E v`. Simplify using `only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]`. Conclude with `Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)`.

Conclude with `key hs`.
-/
theorem sigR_mem_intV_adic (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {s : E ⊗[F] v.adicCompletion F}
    (hs : s ∈ intV E v) : sigR σ (v.adicCompletion F) s ∈ intV E v := by
  have key : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, b, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show sigR σ (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E b)) ∈ intV E v
      rw [sigR_inclE_adic]
      have h : IsIntegral ℤ ((σ : E →+* E) (algebraMap (𝓞 E) E b)) :=
        (RingOfIntegers.isIntegral_coe b).map ((σ : E →+* E).toIntAlgHom)
      exact Formalism.UG.P.easyc_inclE_mem (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _
        ⟨IsIntegralClosure.mk' (𝓞 E) _ h, IsIntegralClosure.algebraMap_mk' _ _ _⟩
    · show sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) ∈ intV E v
      simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        map_one, AlgHom.coe_id, id_eq]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key hs

/- English proof (translation)
Take the linear combination `(-(a * b)) * h`.
-/
theorem mul_eq_unit_mul_of_triple_product_one {A : Type} [CommRing A] (a b P Q T : A) (h : P * Q * T = 1) :
    a * b = T * ((a * P) * (b * Q)) := by linear_combination (-(a * b)) * h

/- English proof (translation)
Take the linear combination `h`.
-/
theorem eq_one_add_mul_neg_of_add_mul_eq_one {A : Type} [CommRing A] (a T S : A) (h : a + T * S = 1) : a = 1 + T * (-S) := by
  linear_combination h

/- English proof (translation)
Take the linear combination `(P * Q) * hd + e * h`.
-/
theorem mul_sub_eq_of_triple_product_one {A : Type} [CommRing A] (P Q T d e : A) (h : P * Q * T = 1) (hd : d = 1 + T * e) :
    P * (d * Q - Q) = e := by linear_combination (P * Q) * hd + e * h

end SlopeTestRemainingChoices

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hT' : (T : E) ≠ 0` using `Nat.cast_ne_zero.2 hT`. Establish `hp0 : (p : E) ≠ 0` using `fun h => hT' (by rw [← hpq, h, zero_mul])`. Establish `hq0 : (q : E) ≠ 0` using `fun h => hT' (by rw [← hpq, h, mul_zero])`. Establish `hΛ : ∀ z, z ∈ latS (F` using `F) (v.adicCompletion F) (intV E v) S.Lb ↔ (∀ i, i ≠ lastIdx n → z i ∈ intV E v) ∧ inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * z (lastIdx n) ∈ intV E v := by`. Introduce `z`.

Rewrite using `[hLb]`. Conclude with `rll_mem_loc_dLat n v _ (inv_ne_zero hp0) z`. Establish `hΛ' : ∀ z, z ∈ latS (F` using `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)) ↔ (∀ i, i ≠ lastIdx n → z i ∈ intV E v) ∧ inclE (F := F) (v.adicCompletion F) (q : E) * z (lastIdx n) ∈ intV E v := by`. Introduce `z`. Rewrite using `[hdual]`.

Conclude with `rll_mem_loc_dLat n v _ hq0 z`. Rewrite `hx` using `[S.UlocAlt v hv]`. Take `⟨⟨hU, hstL⟩, hstL', hfix⟩` from `hx`. Use `set ι := inclE (F := F) (E := E) (v.adicCompletion F) with hιdef`. Use `set ℓ := lastIdx n with hℓ`.

Use `set X := (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) with hX`. Establish `hQQ : ι (q : E) * ι ((q : E)⁻¹) = 1` using `by rw [← map_mul, mul_inv_cancel₀ hq0, map_one]`. Establish `hPQi : ι ((p : E)⁻¹) * ι ((q : E)⁻¹) * (T : E ⊗[F] v.adicCompletion F) = 1`. Rewrite using `[← map_natCast ι T, ← map_mul, ← map_mul, ← hpq]`. Rewrite using `[show (p : E)⁻¹ * (q : E)⁻¹ * ((p : E) * (q : E)) = 1 by field_simp, map_one]`.

Establish `hPQ : ι (p : E) * ι (q : E) = (T : E ⊗[F] v.adicCompletion F)`. Rewrite using `[← map_mul, hpq, map_natCast]`. Use `set w : Fin n → E ⊗[F] v.adicCompletion F := Pi.single ℓ (ι ((q : E)⁻¹)) with hwdef`. Establish `hw : w ∈ (latS (F` using `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))) := by`. Use `(hΛ' w).2 ⟨fun i hi => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hwdef, Pi.single_eq_of_ne hi]`. Conclude with `zero_mem _`. Rewrite using `[hwdef, Pi.single_eq_same, hQQ]`. Conclude with `one_mem _`. Establish `hdec : ∀ z ∈ (latS (F` using `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))), ∃ r : intV E v, (r : E ⊗[F] v.adicCompletion F) = ι (q : E) * z ℓ ∧ z - (r : E ⊗[F] v.adicCompletion F) • w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) S.L …`.

Introduce `z hz`. Use `⟨⟨ι (q : E) * z ℓ, ((hΛ' z).1 hz).2⟩, rfl, (hΛ _).2 ⟨fun i hi => ?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef, Pi.single_eq_of_ne hi, mul_zero, sub_zero]`. Conclude with `((hΛ' z).1 hz).1 i hi`. Establish `h0 : z ℓ - (ι (q : E) * z ℓ) * ι ((q : E)⁻¹) = 0` using `by linear_combination (-z ℓ) * hQQ`.

Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef, Pi.single_eq_same]`. Rewrite using `[h0, mul_zero]`. Conclude with `zero_mem _`. Use `set m := S.fT v hv ⟨w, hw⟩ with hmdef`. Establish `hf : ∀ z : (latS (F` using `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))), ∃ r : intV E v, (r : E ⊗[F] v.adicCompletion F) = ι (q : E) * z.1 ℓ ∧ S.fT v hv z = r • m := by`.

Introduce and unpack `⟨z, hz⟩`. Take `⟨r, hr, hu⟩` from `hdec z hz`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Establish `h1` using `S.fT_L v hv ((⟨z, hz⟩ : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)))) - r • (⟨w, hw⟩ : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fi …`. Rewrite `h1` using `[map_sub]`.

Rewrite `h1` using `[LinearMap.map_smul]`. Rewrite `h1` using `[sub_eq_zero]`. Conclude with `h1`. Establish `hm0 : m ≠ 0`. Introduce `h0`.

Apply `S.fT_ne v hv` to reduce the goal to its premises. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Take `⟨r, -, hr⟩` from `hf z`. Rewrite using `[hr, h0, LinearMap.zero_apply]`. Conclude with `smul_zero r`.

Establish `hXw : X *ᵥ w = fun i => X i ℓ * ι ((q : E)⁻¹)`. Use function extensionality and compare the values at `i`. Use `show (fun j => X i j) ⬝ᵥ Pi.single ℓ (ι ((q : E)⁻¹)) = _`. Rewrite using `[dotProduct_single]`. Establish `hxw : X *ᵥ w ∈ (latS (F` using `F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))) := (hstL' w).1 hw`.

Establish `hb : ∀ i, i ≠ ℓ → X i ℓ * ι ((q : E)⁻¹) ∈ intV E v`. Introduce `i hi`. Establish `h1` using `((hΛ' _).1 hxw).1 i hi`. Rewrite `h1` using `[congrFun hXw i]`. Conclude with `h1`.

Establish `hXwi : ∀ i, (X *ᵥ w) i = X i ℓ * ι ((q : E)⁻¹)` using `fun i => congrFun hXw i`. Establish `hd : X ℓ ℓ ∈ intV E v`. Establish `h1` using `((hΛ' _).1 hxw).2`. Rewrite `h1` using `[hXwi ℓ, mul_left_comm, hQQ, mul_one]`. Conclude with `h1`.

Establish `h2 : ((⟨X ℓ ℓ, hd⟩ : intV E v) - 1) • m = 0`. Take `⟨r, hr, hrm⟩` from `hf ⟨X *ᵥ w, hxw⟩`. Establish `hr' : r = ⟨X ℓ ℓ, hd⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hr]`.

Use `show ι (q : E) * (X *ᵥ w) ℓ = X ℓ ℓ`. Rewrite using `[hXwi ℓ, mul_left_comm, hQQ, mul_one]`. Establish `hfx` using `hfix ⟨w, hw⟩`. Rewrite using `[sub_smul, one_smul, ← hr', ← hrm, sub_eq_zero]`. Conclude with `hfx`.

Establish `hU' : cT (sigR σ (v.adicCompletion F)) X * X = 1`. Establish `h1 : cT (sigR σ (v.adicCompletion F)) X * (1 : Matrix (Fin n) (Fin n) E).map ι * X = (1 : Matrix (Fin n) (Fin n) E).map ι` using `hU`. Rewrite `h1` using `[Matrix.map_one ι (map_zero ι) (map_one ι), Matrix.mul_one]`. Then use the resulting hypothesis. Establish `hsum : ∑ j, sigR σ (v.adicCompletion F) (X j ℓ) * X j ℓ = 1`. Establish `h1` using `congrFun (congrFun hU' ℓ) ℓ`.

Rewrite `h1` using `[Matrix.mul_apply, Matrix.one_apply_eq]`. Simplify `h1` using `only [cT, Matrix.transpose_apply, Matrix.map_apply]`. Establish `hs : ∀ a : E, sigR σ (v.adicCompletion F) (ι a) = ι (σ a)` using `fun a => sigR_inclE_adic σ v a`. Establish `hsq : σ (q : E) = p` using `by rw [hqp, hσ]`. Establish `hsQi : sigR σ (v.adicCompletion F) (ι ((q : E)⁻¹)) = ι ((p : E)⁻¹)` using `by rw [hs, map_inv₀, hsq]`.

Establish `hc' : -∑ j ∈ Finset.univ.erase ℓ, sigR σ (v.adicCompletion F) (X j ℓ * ι ((q : E)⁻¹)) * (X j ℓ * ι ((q : E)⁻¹)) ∈ intV E v` using `neg_mem (sum_mem fun j hj => mul_mem (sigR_mem_intV_adic σ v (hb j (Finset.ne_of_mem_erase hj))) (hb j (Finset.ne_of_mem_erase hj)))`. Establish `h3 : sigR σ (v.adicCompletion F) (X ℓ ℓ) * X ℓ ℓ = 1 + (T : E ⊗[F] v.adicCompletion F) * (-∑ j ∈ Finset.univ.erase ℓ, sigR σ (v.adicCompletion F) (X j ℓ * ι ((q : E)⁻¹)) * (X j ℓ * ι ((q : E)⁻¹)))`. Apply `eq_one_add_mul_neg_of_add_mul_eq_one` to reduce the goal to its premises. Rewrite `hsum` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)]`. Rewrite using `[Finset.mul_sum]`.

Use `hsum using 2` and compare the differences between its conclusion and the goal. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hsQi]`. Conclude with `(mul_eq_unit_mul_of_triple_product_one _ _ _ _ _ hPQi).symm`. Take `⟨e, he⟩` from `hH m hm0 ⟨X ℓ ℓ, hd⟩ ⟨_, hc'⟩ h2 h3`.

Establish `he' : X ℓ ℓ = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F)` using `he`. Establish `hwΛ : X *ᵥ w - w ∈ latS (F` using `F) (v.adicCompletion F) (intV E v) S.Lb := by`. Use `(hΛ _).2 ⟨fun i hi => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.sub_apply, hXwi i, hwdef, Pi.single_eq_of_ne hi, sub_zero]`. Conclude with `hb i hi`.

Rewrite using `[Pi.sub_apply, hXwi ℓ, hwdef, Pi.single_eq_same, mul_sub_eq_of_triple_product_one _ _ _ _ _ hPQi he']`. Conclude with `e.2`. Introduce `y hy`. Take `⟨r, -, hu⟩` from `hdec y hy`. Establish `hsplit : X *ᵥ y - y = (X *ᵥ (y - (r : E ⊗[F] v.adicCompletion F) • w) - (y - (r : E ⊗[F] v.adicCompletion F) • w)) + (r : E ⊗[F] v.adicCompletion F) • (X *ᵥ w - w)`.

Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[hsplit]`. Conclude with `add_mem (sub_mem ((hstL _).1 hu) hu) (Submodule.smul_mem _ r hwΛ)`.
-/
theorem uloc_acts_trivially_on_dual_quotient {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} [NeZero n] {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ (1 : Matrix (Fin n) (Fin n) E) T f bad) (p q : 𝓞 E) (hqp : (q : E) = σ (p : E))
    (hpq : (p : E) * (q : E) = (T : E)) (hT : T ≠ 0)
    (hLb : S.Lb = rll_dLat n ((p : E)⁻¹))
    (hdual : Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb) = rll_dLat n (q : E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (hH : ∀ m : S.fM v hv, m ≠ 0 → ∀ d c : intV E v, (d - 1) • m = 0 →
      sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F) →
      ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ S.Uloc v) :
    ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  have hT' : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hp0 : (p : E) ≠ 0 := fun h => hT' (by rw [← hpq, h, zero_mul])
  have hq0 : (q : E) ≠ 0 := fun h => hT' (by rw [← hpq, h, mul_zero])
  have hΛ : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ↔
      (∀ i, i ≠ lastIdx n → z i ∈ intV E v) ∧
        inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * z (lastIdx n) ∈ intV E v := by
    intro z; rw [hLb]; exact rll_mem_loc_dLat n v _ (inv_ne_zero hp0) z
  have hΛ' : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)) ↔
      (∀ i, i ≠ lastIdx n → z i ∈ intV E v) ∧
        inclE (F := F) (v.adicCompletion F) (q : E) * z (lastIdx n) ∈ intV E v := by
    intro z; rw [hdual]; exact rll_mem_loc_dLat n v _ hq0 z
  rw [S.UlocAlt v hv] at hx
  obtain ⟨⟨hU, hstL⟩, hstL', hfix⟩ := hx
  set ι := inclE (F := F) (E := E) (v.adicCompletion F) with hιdef
  set ℓ := lastIdx n with hℓ
  set X := (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) with hX
  have hQQ : ι (q : E) * ι ((q : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
  have hPQi : ι ((p : E)⁻¹) * ι ((q : E)⁻¹) * (T : E ⊗[F] v.adicCompletion F) = 1 := by
    rw [← map_natCast ι T, ← map_mul, ← map_mul, ← hpq]
    rw [show (p : E)⁻¹ * (q : E)⁻¹ * ((p : E) * (q : E)) = 1 by field_simp, map_one]
  have hPQ : ι (p : E) * ι (q : E) = (T : E ⊗[F] v.adicCompletion F) := by
    rw [← map_mul, hpq, map_natCast]

  set w : Fin n → E ⊗[F] v.adicCompletion F := Pi.single ℓ (ι ((q : E)⁻¹)) with hwdef
  have hw : w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))) := by
    refine (hΛ' w).2 ⟨fun i hi => ?_, ?_⟩
    · rw [hwdef, Pi.single_eq_of_ne hi]; exact zero_mem _
    · rw [hwdef, Pi.single_eq_same, hQQ]; exact one_mem _

  have hdec : ∀ z ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))), ∃ r : intV E v, (r : E ⊗[F] v.adicCompletion F) = ι (q : E) * z ℓ ∧
      z - (r : E ⊗[F] v.adicCompletion F) • w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := by
    intro z hz
    refine ⟨⟨ι (q : E) * z ℓ, ((hΛ' z).1 hz).2⟩, rfl, (hΛ _).2 ⟨fun i hi => ?_, ?_⟩⟩
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef, Pi.single_eq_of_ne hi, mul_zero, sub_zero]
      exact ((hΛ' z).1 hz).1 i hi
    · have h0 : z ℓ - (ι (q : E) * z ℓ) * ι ((q : E)⁻¹) = 0 := by linear_combination (-z ℓ) * hQQ
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwdef, Pi.single_eq_same]
      rw [h0, mul_zero]; exact zero_mem _

  set m := S.fT v hv ⟨w, hw⟩ with hmdef
  have hf : ∀ z : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))), ∃ r : intV E v, (r : E ⊗[F] v.adicCompletion F) = ι (q : E) * z.1 ℓ ∧ S.fT v hv z = r • m := by
    rintro ⟨z, hz⟩
    obtain ⟨r, hr, hu⟩ := hdec z hz
    refine ⟨r, hr, ?_⟩
    have h1 := S.fT_L v hv ((⟨z, hz⟩ : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)))) - r • (⟨w, hw⟩ : (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))))) hu
    rw [map_sub] at h1
    rw [LinearMap.map_smul] at h1
    rw [sub_eq_zero] at h1
    exact h1
  have hm0 : m ≠ 0 := by
    intro h0
    apply S.fT_ne v hv
    refine LinearMap.ext fun z => ?_
    obtain ⟨r, -, hr⟩ := hf z
    rw [hr, h0, LinearMap.zero_apply]
    exact smul_zero r

  have hXw : X *ᵥ w = fun i => X i ℓ * ι ((q : E)⁻¹) := by
    funext i
    show (fun j => X i j) ⬝ᵥ Pi.single ℓ (ι ((q : E)⁻¹)) = _
    rw [dotProduct_single]
  have hxw : X *ᵥ w ∈ (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb))) := (hstL' w).1 hw
  have hb : ∀ i, i ≠ ℓ → X i ℓ * ι ((q : E)⁻¹) ∈ intV E v := by
    intro i hi
    have h1 := ((hΛ' _).1 hxw).1 i hi
    rw [congrFun hXw i] at h1
    exact h1
  have hXwi : ∀ i, (X *ᵥ w) i = X i ℓ * ι ((q : E)⁻¹) := fun i => congrFun hXw i
  have hd : X ℓ ℓ ∈ intV E v := by
    have h1 := ((hΛ' _).1 hxw).2
    rw [hXwi ℓ, mul_left_comm, hQQ, mul_one] at h1
    exact h1
  have h2 : ((⟨X ℓ ℓ, hd⟩ : intV E v) - 1) • m = 0 := by
    obtain ⟨r, hr, hrm⟩ := hf ⟨X *ᵥ w, hxw⟩
    have hr' : r = ⟨X ℓ ℓ, hd⟩ := by
      apply Subtype.ext
      rw [hr]
      show ι (q : E) * (X *ᵥ w) ℓ = X ℓ ℓ
      rw [hXwi ℓ, mul_left_comm, hQQ, mul_one]
    have hfx := hfix ⟨w, hw⟩
    rw [sub_smul, one_smul, ← hr', ← hrm, sub_eq_zero]
    exact hfx
  have hU' : cT (sigR σ (v.adicCompletion F)) X * X = 1 := by
    have h1 : cT (sigR σ (v.adicCompletion F)) X * (1 : Matrix (Fin n) (Fin n) E).map ι * X =
        (1 : Matrix (Fin n) (Fin n) E).map ι := hU
    rwa [Matrix.map_one ι (map_zero ι) (map_one ι), Matrix.mul_one] at h1
  have hsum : ∑ j, sigR σ (v.adicCompletion F) (X j ℓ) * X j ℓ = 1 := by
    have h1 := congrFun (congrFun hU' ℓ) ℓ
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simpa only [cT, Matrix.transpose_apply, Matrix.map_apply] using h1
  have hs : ∀ a : E, sigR σ (v.adicCompletion F) (ι a) = ι (σ a) := fun a => sigR_inclE_adic σ v a
  have hsq : σ (q : E) = p := by rw [hqp, hσ]
  have hsQi : sigR σ (v.adicCompletion F) (ι ((q : E)⁻¹)) = ι ((p : E)⁻¹) := by rw [hs, map_inv₀, hsq]
  have hc' : -∑ j ∈ Finset.univ.erase ℓ, sigR σ (v.adicCompletion F) (X j ℓ * ι ((q : E)⁻¹)) * (X j ℓ * ι ((q : E)⁻¹))
      ∈ intV E v :=
    neg_mem (sum_mem fun j hj => mul_mem (sigR_mem_intV_adic σ v (hb j (Finset.ne_of_mem_erase hj)))
      (hb j (Finset.ne_of_mem_erase hj)))
  have h3 : sigR σ (v.adicCompletion F) (X ℓ ℓ) * X ℓ ℓ = 1 + (T : E ⊗[F] v.adicCompletion F) *
      (-∑ j ∈ Finset.univ.erase ℓ, sigR σ (v.adicCompletion F) (X j ℓ * ι ((q : E)⁻¹)) * (X j ℓ * ι ((q : E)⁻¹))) := by
    apply eq_one_add_mul_neg_of_add_mul_eq_one
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)] at hsum
    rw [Finset.mul_sum]
    convert hsum using 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hsQi]
    exact (mul_eq_unit_mul_of_triple_product_one _ _ _ _ _ hPQi).symm
  obtain ⟨e, he⟩ := hH m hm0 ⟨X ℓ ℓ, hd⟩ ⟨_, hc'⟩ h2 h3
  have he' : X ℓ ℓ = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F) := he
  have hwΛ : X *ᵥ w - w ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
    refine (hΛ _).2 ⟨fun i hi => ?_, ?_⟩
    · rw [Pi.sub_apply, hXwi i, hwdef, Pi.single_eq_of_ne hi, sub_zero]
      exact hb i hi
    · rw [Pi.sub_apply, hXwi ℓ, hwdef, Pi.single_eq_same, mul_sub_eq_of_triple_product_one _ _ _ _ _ hPQi he']
      exact e.2
  intro y hy
  obtain ⟨r, -, hu⟩ := hdec y hy
  have hsplit : X *ᵥ y - y = (X *ᵥ (y - (r : E ⊗[F] v.adicCompletion F) • w) - (y - (r : E ⊗[F] v.adicCompletion F) • w)) +
      (r : E ⊗[F] v.adicCompletion F) • (X *ᵥ w - w) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub]
    abel
  rw [hsplit]
  exact add_mem (sub_mem ((hstL _).1 hu) hu) (Submodule.smul_mem _ r hwΛ)

end GlobalTheory

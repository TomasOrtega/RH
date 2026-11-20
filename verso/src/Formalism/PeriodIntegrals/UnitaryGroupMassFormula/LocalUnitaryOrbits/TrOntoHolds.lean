import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ResAlgOfSp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRSumSmulRight

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Distinguish the cases in `hp : (IE (E := E) v).IsPrime`. Conclude with `qInert_holds σ J ψ v hstd hun hp`. Use `haveI : v.asIdeal.IsMaximal := v.isMaximal`. Use `letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal`. Take `⟨e, he⟩` from `qSplit_holds σ J ψ v hstd hun hp`.

Introduce `hid`. Establish `h` using `he (e.symm (1, 0))`. Rewrite `h` using `[hid, RingHom.id_apply, RingEquiv.apply_symm_apply]`. Conclude with `one_ne_zero (congrArg Prod.fst h)`.
-/
theorem sigQ_ne (hstd : StdHyp σ J ψ) (hun : UnramAt (E := E) v) : sigQ σ v ≠ RingHom.id _ := by
  by_cases hp : (IE (E := E) v).IsPrime
  · exact qInert_holds σ J ψ v hstd hun hp
  · haveI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    obtain ⟨e, he⟩ := qSplit_holds σ J ψ v hstd hun hp
    intro hid
    have h := he (e.symm (1, 0))
    rw [hid, RingHom.id_apply, RingEquiv.apply_symm_apply] at h
    exact one_ne_zero (congrArg Prod.fst h)

/- English proof (translation)
Introduce `hun s hs hfix`. Take `⟨θ, h3, h4⟩` from `theta_exists σ v hstd.1`. Establish `hsp` using `thetaSpan_holds σ J ψ v hstd hun θ h4`. Establish `hind` using `theta_indep σ v hstd.1 θ h3`. Use `set iθ : Fv F v ⊗[F] E := inclR (F := F) (Fv F v) (θ : E) with hiθ`.

Establish `hss : sigO σ (sigO σ θ) = θ` using `RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ hstd.1 _)`. Take `⟨t, ht⟩` from `fix_int σ hstd.1 (θ + sigO σ θ) (by rw [map_add, hss, add_comm])`. Establish `hσθ : sigO σ θ = algebraMap (𝓞 F) (𝓞 E) t - θ` using `by rw [ht]; ring`. Establish `hinc : ∀ a : 𝓞 F, inclR (F` using `F) (Fv F v) ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) = sc (E := E) v (iO v a) := fun a => inclR_alg' v (a : F)`. Establish `hsiθ : sigR (Fv F v) σ iθ = sc (E` using `E) v (iO v t) - iθ := by`.

Establish `e1` using `congrArg (fun y : 𝓞 E => inclR (F := F) (Fv F v) (y : E)) hσθ`. Simplify using `only [AddSubgroupClass.coe_sub, map_sub, hinc, sigO_coe] at e1`. Rewrite using `[hiθ, sigR_incl]`. Conclude with `e1`. Establish `htr : ∀ a b : Fv F v, (sc (E` using `E) v a + sc (E := E) v b * iθ) + sigR (Fv F v) σ (sc (E := E) v a + sc (E := E) v b * iθ) = sc (E := E) v (2 * a + b * iO v t) := by`.

Introduce `a b`. Rewrite using `[map_add, map_mul, sigR_sc, sigR_sc, hsiθ]`. Simplify using `only [sc_eq', map_add, map_mul, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨s0, s1, hs01⟩` from `hsp s hs`.

Establish `hs1 : (s1 : Fv F v) = 0`. Establish `h` using `htr s0 s1`. Rewrite `h` using `[← hs01, hfix]`. Establish `h'` using `hind (2 * s0 + s1 * iO v t - 2 * s0) (0 - 2 * s1) (by`. Rewrite `h` using `[hs01]`.

Simplify using `only [sc_eq', map_add, map_mul, map_sub, map_ofNat, map_zero] at h ⊢`. Take the linear combination `(-1 : Fv F v ⊗[F] E) * h)`. Establish `h2 : (2 : Fv F v) ≠ 0`. Establish `: (2 : Fv F v) = algebraMap F (Fv F v) 2` using `by rw [map_ofNat]`. Rewrite using `[this]`.

Conclude with `(map_ne_zero _).2 two_ne_zero`. Use `h'.2` as an intermediate fact. Rewrite `this` using `[zero_sub, neg_eq_zero, mul_eq_zero]`. Conclude with `this.resolve_left h2`. Establish `hmemO : ∀ a b : Fv F v, Valued.v a ≤ 1 → Valued.v b ≤ 1 → sc (E` using `E) v a + sc (E := E) v b * iθ ∈ OEv (E := E) v := fun a b ha hb => Orb.oev_add v (by simpa using sc_mul_mem_oEv v ha (Orb.oSub (E := E) v).1) (sc_mul_mem_oEv v hb (Orb.gen_mem v θ))`.

Establish `hs' : s = sc (E` using `E) v (s0 : Fv F v) := by rw [hs01, hs1]; simp [sc_eq']`. Establish `hs0 : Valued.v (s0 : Fv F v) ≤ 1` using `s0.2`. Distinguish the cases in `h2 : (2 : 𝓞 F) ∈ v.asIdeal`. Establish `htv : ¬ t ∈ v.asIdeal`. Introduce `htin`.

Apply `sigQ_ne σ J ψ v hstd hun` to reduce the goal to its premises. Establish `h2Q : (2 : QE (E` using `E) v) = 0 := by`. Establish `: (2 : QE (E` using `E) v) = Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) 2) := by`. Rewrite using `[map_ofNat, map_ofNat]`. Rewrite using `[this, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mem_map_of_mem _ h2`. Establish `htQ : Ideal.Quotient.mk (IE (E` using `E) v) (algebraMap (𝓞 F) (𝓞 E) t) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ htin)`. Establish `hθf : sigQ σ v (Ideal.Quotient.mk (IE (E` using `E) v) θ) = Ideal.Quotient.mk (IE (E := E) v) θ := by`. Rewrite using `[sigQ_mk, hσθ, map_sub, htQ, zero_sub]`. Take the linear combination `(-(Ideal.Quotient.mk (IE (E := E) v) θ)) * h2Q`.

Use `RingHom.ext fun q => ?_` and prove the remaining obligations. Take `⟨a0, a1, rfl⟩` from `h4 q`. Rewrite using `[map_add, map_mul, sigQ_alg, sigQ_alg, hθf]`. Both sides reduce to the same expression. Establish `hvt : Valued.v (iO v t) = 1` using `le_antisymm (v_iO_le v t) (not_lt.1 fun hlt => htv ((v_iO_lt_iff v t).1 hlt))`.

Establish `ht0 : iO v t ≠ 0` using `fun h0 => by rw [h0, map_zero] at hvt; exact zero_ne_one hvt`. Use `⟨sc (E := E) v 0 + sc (E := E) v ((s0 : Fv F v) * (iO v t)⁻¹) * iθ, hmemO _ _ (by simp) (by rw [map_mul, map_inv₀, hvt, inv_one, mul_one]; exact hs0), ?_⟩` and prove the remaining obligations. Rewrite using `[htr, hs']`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hv2 : Valued.v (iO v 2) = 1` using `le_antisymm (v_iO_le v 2) (not_lt.1 fun hlt => h2 ((v_iO_lt_iff v 2).1 hlt))`. Establish `hi2 : iO v 2 = (2 : Fv F v)` using `by show algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) = 2`. Rewrite using `[map_ofNat, map_ofNat]`. Rewrite `hv2` using `[hi2]`.

Establish `h20 : (2 : Fv F v) ≠ 0` using `fun h0 => by rw [h0, map_zero] at hv2; exact zero_ne_one hv2`. Use `⟨sc (E := E) v ((s0 : Fv F v) * 2⁻¹) + sc (E := E) v 0 * iθ, hmemO _ _ (by rw [map_mul, map_inv₀, hv2, inv_one, mul_one]; exact hs0) (by simp), ?_⟩` and prove the remaining obligations. Rewrite using `[htr, hs']`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem trOnto_holds (hstd : StdHyp σ J ψ) : TrOnto σ v := by
  intro hun s hs hfix
  obtain ⟨θ, h3, h4⟩ := theta_exists σ v hstd.1
  have hsp := thetaSpan_holds σ J ψ v hstd hun θ h4
  have hind := theta_indep σ v hstd.1 θ h3
  set iθ : Fv F v ⊗[F] E := inclR (F := F) (Fv F v) (θ : E) with hiθ
  have hss : sigO σ (sigO σ θ) = θ := RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ hstd.1 _)
  obtain ⟨t, ht⟩ := fix_int σ hstd.1 (θ + sigO σ θ) (by rw [map_add, hss, add_comm])
  have hσθ : sigO σ θ = algebraMap (𝓞 F) (𝓞 E) t - θ := by rw [ht]; ring
  have hinc : ∀ a : 𝓞 F, inclR (F := F) (Fv F v) ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) =
      sc (E := E) v (iO v a) := fun a => inclR_alg' v (a : F)
  have hsiθ : sigR (Fv F v) σ iθ = sc (E := E) v (iO v t) - iθ := by
    have e1 := congrArg (fun y : 𝓞 E => inclR (F := F) (Fv F v) (y : E)) hσθ
    simp only [AddSubgroupClass.coe_sub, map_sub, hinc, sigO_coe] at e1
    rw [hiθ, sigR_incl]
    exact e1
  have htr : ∀ a b : Fv F v, (sc (E := E) v a + sc (E := E) v b * iθ) +
      sigR (Fv F v) σ (sc (E := E) v a + sc (E := E) v b * iθ) = sc (E := E) v (2 * a + b * iO v t) := by
    intro a b
    rw [map_add, map_mul, sigR_sc, sigR_sc, hsiθ]
    simp only [sc_eq', map_add, map_mul, map_ofNat]
    ring
  obtain ⟨s0, s1, hs01⟩ := hsp s hs
  have hs1 : (s1 : Fv F v) = 0 := by
    have h := htr s0 s1
    rw [← hs01, hfix] at h
    have h' := hind (2 * s0 + s1 * iO v t - 2 * s0) (0 - 2 * s1) (by
      rw [hs01] at h
      simp only [sc_eq', map_add, map_mul, map_sub, map_ofNat, map_zero] at h ⊢
      linear_combination (-1 : Fv F v ⊗[F] E) * h)
    have h2 : (2 : Fv F v) ≠ 0 := by
      have : (2 : Fv F v) = algebraMap F (Fv F v) 2 := by rw [map_ofNat]
      rw [this]; exact (map_ne_zero _).2 two_ne_zero
    have := h'.2
    rw [zero_sub, neg_eq_zero, mul_eq_zero] at this
    exact this.resolve_left h2
  have hmemO : ∀ a b : Fv F v, Valued.v a ≤ 1 → Valued.v b ≤ 1 →
      sc (E := E) v a + sc (E := E) v b * iθ ∈ OEv (E := E) v := fun a b ha hb =>
    Orb.oev_add v (by simpa using sc_mul_mem_oEv v ha (Orb.oSub (E := E) v).1)
      (sc_mul_mem_oEv v hb (Orb.gen_mem v θ))
  have hs' : s = sc (E := E) v (s0 : Fv F v) := by rw [hs01, hs1]; simp [sc_eq']
  have hs0 : Valued.v (s0 : Fv F v) ≤ 1 := s0.2
  by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
  ·
    have htv : ¬ t ∈ v.asIdeal := by
      intro htin
      apply sigQ_ne σ J ψ v hstd hun
      have h2Q : (2 : QE (E := E) v) = 0 := by
        have : (2 : QE (E := E) v) = Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) 2) := by
          rw [map_ofNat, map_ofNat]
        rw [this, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ h2
      have htQ : Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) t) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ htin)
      have hθf : sigQ σ v (Ideal.Quotient.mk (IE (E := E) v) θ) = Ideal.Quotient.mk (IE (E := E) v) θ := by
        rw [sigQ_mk, hσθ, map_sub, htQ, zero_sub]
        linear_combination (-(Ideal.Quotient.mk (IE (E := E) v) θ)) * h2Q
      refine RingHom.ext fun q => ?_
      obtain ⟨a0, a1, rfl⟩ := h4 q
      rw [map_add, map_mul, sigQ_alg, sigQ_alg, hθf]
      rfl
    have hvt : Valued.v (iO v t) = 1 := le_antisymm (v_iO_le v t)
      (not_lt.1 fun hlt => htv ((v_iO_lt_iff v t).1 hlt))
    have ht0 : iO v t ≠ 0 := fun h0 => by rw [h0, map_zero] at hvt; exact zero_ne_one hvt
    refine ⟨sc (E := E) v 0 + sc (E := E) v ((s0 : Fv F v) * (iO v t)⁻¹) * iθ,
      hmemO _ _ (by simp) (by rw [map_mul, map_inv₀, hvt, inv_one, mul_one]; exact hs0), ?_⟩
    rw [htr, hs']
    congr 1
    field_simp
    ring
  · have hv2 : Valued.v (iO v 2) = 1 := le_antisymm (v_iO_le v 2)
      (not_lt.1 fun hlt => h2 ((v_iO_lt_iff v 2).1 hlt))
    have hi2 : iO v 2 = (2 : Fv F v) := by
      show algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) = 2
      rw [map_ofNat, map_ofNat]
    rw [hi2] at hv2
    have h20 : (2 : Fv F v) ≠ 0 := fun h0 => by rw [h0, map_zero] at hv2; exact zero_ne_one hv2
    refine ⟨sc (E := E) v ((s0 : Fv F v) * 2⁻¹) + sc (E := E) v 0 * iθ,
      hmemO _ _ (by rw [map_mul, map_inv₀, hv2, inv_one, mul_one]; exact hs0) (by simp), ?_⟩
    rw [htr, hs']
    congr 1
    field_simp
    ring

end PI.OmLocU.Red

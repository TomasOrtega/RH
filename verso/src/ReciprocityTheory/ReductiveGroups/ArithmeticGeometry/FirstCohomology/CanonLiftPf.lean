import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFiniteOrder
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftUnpacking

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Introduce `E _ _ _ H V _ _ _ t P hT`. Use `letI := H.starRing`. Introduce `α N hN hαN _hco _hNu F _ _ _ θ θα hpull p x hx hxα`. Take `⟨z, q, h, g0, hy, hgt, hι, hadd, hz⟩` from `CanonicalLiftUnpacking.alpha_unpack P hT (qkActExists_of hL.globalFns) α N hN hαN F p x hx hxα`. Use `haveI := P.oD.onB.hom (star α)`.

Use `haveI := P.oD.onB.hom α`. Take `⟨r, hr, hr0⟩` from `Geo.Tor.exists_ros (A := P.D.toPre.P.A) (L := P.D.toPre.P.L) hL.globalFns P.D.toPre.P.isAb P.D.toPre.P.isLB (P.oD.onB.act (star α)) (P.oD.onB.act α) (by have hR := P.oD.onB.rosati (star α); rwa [star_star] at hR)`. Take `⟨hb, hrel⟩` from `CanonicalLiftOrigin.gt_rel P.oD α p.g q.g h g0 z hgt hι hadd hz r hr hr0`. Take `⟨u0, hu0, hc0, -⟩` from `hpull.1 0`. Take `⟨w, hw, hwv⟩` from `CanonicalLiftTraces.exists_w P.oD α N hN p.g.b z hb u0 hu0`.

Establish `hfix : PhiRel P.D.toPre F (1 * N) p w θα θα` using `CanonicalLiftFrobenius.phi_fixes hL.globalFns P.oD α N p z hy hb r hr hr0 hrel u0 hu0 hc0 w hw hwv θ θα hpull`. Establish `hk : 1 ≤ 1 * N` using `by omega`. Take `⟨Φ, hΦ⟩` from `phiFun_of hL V (maximalIdeal V) P.D F (1 * N) hk p w hw`. Take `⟨c, hc0', hcpow⟩` from `phiPow_of hL V (maximalIdeal V) P.D F (1 * N) hk p w hw`. Establish `hpowc : ∀ s, (Φ ^ (1 * N)) s = c • s`.

Introduce `s`. Establish `h1` using `hcpow (fun i => (Φ ^ (i : ℕ)) s) (by`. Introduce `i`. Rewrite using `[hΦ]`. Simplify using `only [Fin.val_succ, Fin.coe_castSucc, pow_succ']`.

Use the proof step `rfl)`. Rewrite `h1` using `[isSmul_iff]`. Simplify using `using h1`. Establish `hΦθ : Φ θα = θα` using `((hΦ θα θα).1 hfix).symm`. Distinguish the cases in `hc1 : c = 1`.

Substitute `hc1` using the available equality. Use `⟨w, hw, ?_, hfix⟩` and prove the remaining obligations. Conclude with `CanonicalLiftFiniteOrder.finOrd_of_pow hk p w Φ hΦ (fun s => by rw [hpowc, one_smul])`. Establish `hθ : θα = 0`. Establish `hfixpow : ∀ n : ℕ, (Φ ^ n) θα = θα`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Both sides reduce to the same expression. Consider the case `succ n ih`.

Rewrite using `[pow_succ']`. Use `show Φ ((Φ ^ n) θα) = θα`. Rewrite using `[ih, hΦθ]`. Establish `h3 : θα = c • θα` using `by rw [← hpowc θα, hfixpow]`. Establish `h4 : (c - 1) • θα = 0` using `by rw [sub_smul, one_smul, ← h3, sub_self]`.

Establish `h5 : c - 1 ≠ 0` using `sub_ne_zero.mpr hc1`. Combine the equalities or inequalities in the displayed calculation. Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_pow_nat_eq (c⁻¹) (show 0 < 1 * N by omega)`. Establish `hζ0 : ζ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hζ` using `[zero_pow (by omega : 1 * N ≠ 0)]`. Conclude with `inv_ne_zero hc0' hζ.symm`. Establish `hsc` using `CanonicalLiftFiniteOrder.phiRel_scale hL.globalFns p w hw Φ hΦ ζ hζ0`. Use `⟨DVR.scaleGen (CanonicalLiftFiniteOrder.zUnit (V := V) ζ hζ0) w, DVR.scaleGen_isGen _ _ hw, ?_, ?_⟩` and prove the remaining obligations. Use `CanonicalLiftFiniteOrder.finOrd_of_pow hk p _ (ζ • Φ) (fun s t => by rw [hsc]; rfl) ?_` and prove the remaining obligations.

Introduce `s`. Rewrite using `[smul_pow, LinearMap.smul_apply, hpowc, smul_smul, hζ, inv_mul_cancel₀ hc0', one_smul]`. Rewrite using `[hsc, hθ, map_zero, smul_zero]`.
-/
theorem canonLiftFix_of_laws (hL : Out.Laws) : CanonLiftFixStatement := by
  intro E _ _ _ H V _ _ _ t P hT
  letI := H.starRing
  intro α N hN hαN _hco _hNu F _ _ _ θ θα hpull p x hx hxα
  obtain ⟨z, q, h, g0, hy, hgt, hι, hadd, hz⟩ :=
    CanonicalLiftUnpacking.alpha_unpack P hT (qkActExists_of hL.globalFns) α N hN hαN F p x hx hxα
  haveI := P.oD.onB.hom (star α)
  haveI := P.oD.onB.hom α
  obtain ⟨r, hr, hr0⟩ := Geo.Tor.exists_ros (A := P.D.toPre.P.A) (L := P.D.toPre.P.L)
    hL.globalFns P.D.toPre.P.isAb P.D.toPre.P.isLB (P.oD.onB.act (star α)) (P.oD.onB.act α)
    (by have hR := P.oD.onB.rosati (star α); rwa [star_star] at hR)
  obtain ⟨hb, hrel⟩ := CanonicalLiftOrigin.gt_rel P.oD α p.g q.g h g0 z hgt hι hadd hz r hr hr0
  obtain ⟨u0, hu0, hc0, -⟩ := hpull.1 0
  obtain ⟨w, hw, hwv⟩ := CanonicalLiftTraces.exists_w P.oD α N hN p.g.b z hb u0 hu0
  have hfix : PhiRel P.D.toPre F (1 * N) p w θα θα :=
    CanonicalLiftFrobenius.phi_fixes hL.globalFns P.oD α N p z hy hb r hr hr0 hrel u0 hu0 hc0 w hw hwv θ θα hpull
  have hk : 1 ≤ 1 * N := by omega
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL V (maximalIdeal V) P.D F (1 * N) hk p w hw
  obtain ⟨c, hc0', hcpow⟩ := phiPow_of hL V (maximalIdeal V) P.D F (1 * N) hk p w hw

  have hpowc : ∀ s, (Φ ^ (1 * N)) s = c • s := by
    intro s
    have h1 := hcpow (fun i => (Φ ^ (i : ℕ)) s) (by
      intro i
      rw [hΦ]
      simp only [Fin.val_succ, Fin.coe_castSucc, pow_succ']
      rfl)
    rw [isSmul_iff] at h1
    simpa using h1
  have hΦθ : Φ θα = θα := ((hΦ θα θα).1 hfix).symm
  by_cases hc1 : c = 1
  · subst hc1
    refine ⟨w, hw, ?_, hfix⟩
    exact CanonicalLiftFiniteOrder.finOrd_of_pow hk p w Φ hΦ (fun s => by rw [hpowc, one_smul])
  ·
    have hθ : θα = 0 := by
      have hfixpow : ∀ n : ℕ, (Φ ^ n) θα = θα := by
        intro n
        induction n with
        | zero => rw [pow_zero]; rfl
        | succ n ih =>
          rw [pow_succ']
          show Φ ((Φ ^ n) θα) = θα
          rw [ih, hΦθ]
      have h3 : θα = c • θα := by rw [← hpowc θα, hfixpow]
      have h4 : (c - 1) • θα = 0 := by rw [sub_smul, one_smul, ← h3, sub_self]
      have h5 : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
      calc θα = (c - 1)⁻¹ • ((c - 1) • θα) := by rw [smul_smul, inv_mul_cancel₀ h5, one_smul]
        _ = 0 := by rw [h4, smul_zero]

    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) (show 0 < 1 * N by omega)
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega : 1 * N ≠ 0)] at hζ
      exact inv_ne_zero hc0' hζ.symm
    have hsc := CanonicalLiftFiniteOrder.phiRel_scale hL.globalFns p w hw Φ hΦ ζ hζ0
    refine ⟨DVR.scaleGen (CanonicalLiftFiniteOrder.zUnit (V := V) ζ hζ0) w, DVR.scaleGen_isGen _ _ hw, ?_, ?_⟩
    · refine CanonicalLiftFiniteOrder.finOrd_of_pow hk p _ (ζ • Φ) (fun s t => by rw [hsc]; rfl) ?_
      intro s
      rw [smul_pow, LinearMap.smul_apply, hpowc, smul_smul, hζ, inv_mul_cancel₀ hc0', one_smul]
    · rw [hsc, hθ, map_zero, smul_zero]

end ReciprocityTheory.ChartRestriction.G.H1

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SigCancel

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section Lift

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

/- English proof (translation)
Rewrite using `[liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_one]`.
-/
theorem liftX_one : liftX k (1 : PS k 1 d) = 1 := by
  rw [liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_one]

/- English proof (translation)
Rewrite using `[liftX, liftX, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_add]`.
-/
theorem liftX_add (f g : PS k 1 d) : liftX k (f + g) = liftX k f + liftX k g := by
  rw [liftX, liftX, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_add]

/- English proof (translation)
Rewrite using `[liftX, liftX, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_sub]`.
-/
theorem liftX_sub (f g : PS k 1 d) : liftX k (f - g) = liftX k f - liftX k g := by
  rw [liftX, liftX, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_sub]

/- English proof (translation)
Establish `h1 : (C a : PS k 1 d) = algebraMap k (PS k 1 d) a`. Rewrite using `[MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Establish `h2 : (C a : AA k d) = algebraMap k (AA k d) a`. Rewrite using `[MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Rewrite using `[h1, h2, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), AlgHom.commutes]`.
-/
theorem liftX_C (a : k) : liftX k (C a : PS k 1 d) = C a := by
  have h1 : (C a : PS k 1 d) = algebraMap k (PS k 1 d) a := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h2 : (C a : AA k d) = algebraMap k (AA k d) a := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h1, h2, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), AlgHom.commutes]

end Lift

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

/- English proof (translation)
Simplify using `only [FB.FK, FGLaw.mapF]`. Conclude with `ig_map _`.
-/
theorem ig_FK (B : FB R d O) (j : Fin d) : B.FK k j ∈ Ig R k (Fin 2 × Fin d) := by
  simp only [FB.FK, FGLaw.mapF]
  exact ig_map _

/- English proof (translation)
Establish `cPA : CZ (![pt k (n` using `1) d 0, B.actK k w0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt 0) (CZ.cons (const_actK' B w0) CZ.nil)`. Establish `ccf : constantCoeff ((m : k) • B.hL k h w0) = 0`. Rewrite using `[nt_const_smul, hL_eq, cc_ev' cPA, cc_h hc, mul_zero]`. Establish `ccf' : constantCoeff (-((m : k) • B.hL k h w0)) = 0` using `by rw [map_neg, ccf, neg_zero]`. Establish `hinv : liftX k (FB.expS k (-((m : k) • B.hL k h w0))) * liftX k (FB.expS k ((m : k) • B.hL k h w0)) = 1`.

Rewrite using `[← liftX_mul, ← gt_expS_add _ _ ccf' ccf, neg_add_cancel, nt_expS_zero, liftX_one]`. Rewrite using `[nabla_eq, vf_mul, vf_cf_liftX, dof_expS _ _ ccf, liftX_mul]`. Establish `e : ∀ (a b x y z : AA k d), a * (b * x * G + b * y - z * (b * G)) = (a * b) * (x * G + y - z * G)` using `fun a b x y z => by ring`. Rewrite using `[e, hinv, one_mul, smul_eq_C_mul, dof_Cmul, liftX_mul, liftX_C]`. Establish `hfm : fm k h (fun i => algebraMap R k (u' i)) = ∑ i, X (Sum.inr i) * C (algebraMap R k (u' i)) - liftX k (∑ i, sgOf k h i * C (algebraMap R k (u' i)))`.

Simplify using `only [fm, sub_mul, Finset.sum_sub_distrib, liftX_sum, liftX_mul, liftX_C]`. Rewrite using `[hfm]`. Establish `e2 : ∀ (cm D S XC y : AA k d), cm * D * G + y - cm * (XC - S) * G = y + cm * (D + S - XC) * G` using `fun cm D S XC y => by ring`. Rewrite using `[e2, ← liftX_add]`. Establish `hm : (C ((m : ℕ) : k) : AA k d) ∈ Ig R k (Fin d ⊕ Fin d)`.

Rewrite using `[← map_natCast (algebraMap R k) m]`. Conclude with `ig_C _`. Use `add_mem ?_ (mul_mem (mul_mem hm (sub_mem (ig_liftX (rel_hL hc w0 hw _ fun j => ⟨u' j, rfl⟩)) ?_)) hG)` and prove the remaining obligations. Simplify using `only [vf]`. Use `sum_mem fun t _ => mul_mem ?_ (ig_pderiv hG t)` and prove the remaining obligations.

Break down `t with j | i` into its components or cases. Rewrite using `[cf_inl]`. Conclude with `ig_liftX (sum_mem fun i _ => mul_mem (ig_C _) (ig_ev cz1 integral_family_point_zero (ig_pderiv (ig_FK B j) _)))`. Establish `e3 : cf k B h (fun i => algebraMap R k (u' i)) (fun i => algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u' j)) i) (Sum.inr i) = liftX k (Dof (B.FK k) (fun j => algebraMap R k (u' j)) (sgOf k h i) - C (∑ j, sg1 k h i j * algebraMap R k (u' j))) + C (algebraMap …`. Rewrite using `[cf_inr, liftX_sub, liftX_C]`.

Simplify using `only [Matrix.mulVec, dotProduct, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3]`. Conclude with `add_mem (ig_liftX (dof_sig hc u' i)) (ig_C _)`. Conclude with `sum_mem fun i _ => mul_mem (ig_X _) (ig_C _)`.
-/
theorem exp_conj_connection_integral {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (w0 : O) (hw : w0 + star w0 = 1)
    (m : ℕ) (u' φ' : Fin d → R) (G : AA k d) (hG : G ∈ Ig R k (Fin d ⊕ Fin d)) :
    liftX k (FB.expS k (-((m : k) • B.hL k h w0))) *
      nabla k B h m (fun i => algebraMap R k (u' i))
        (fun i => algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u' j)) i)
        (liftX k (FB.expS k ((m : k) • B.hL k h w0)) * G) ∈ Ig R k (Fin d ⊕ Fin d) := by
  have cPA : CZ (![pt k (n := 1) d 0, B.actK k w0] : Fin 2 → Pt k 1 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (const_actK' B w0) CZ.nil)
  have ccf : constantCoeff ((m : k) • B.hL k h w0) = 0 := by
    rw [nt_const_smul, hL_eq, cc_ev' cPA, cc_h hc, mul_zero]
  have ccf' : constantCoeff (-((m : k) • B.hL k h w0)) = 0 := by rw [map_neg, ccf, neg_zero]
  have hinv : liftX k (FB.expS k (-((m : k) • B.hL k h w0))) * liftX k (FB.expS k ((m : k) • B.hL k h w0)) = 1 := by
    rw [← liftX_mul, ← gt_expS_add _ _ ccf' ccf, neg_add_cancel, nt_expS_zero, liftX_one]
  rw [nabla_eq, vf_mul, vf_cf_liftX, dof_expS _ _ ccf, liftX_mul]
  have e : ∀ (a b x y z : AA k d), a * (b * x * G + b * y - z * (b * G)) = (a * b) * (x * G + y - z * G) :=
    fun a b x y z => by ring
  rw [e, hinv, one_mul, smul_eq_C_mul, dof_Cmul, liftX_mul, liftX_C]
  have hfm : fm k h (fun i => algebraMap R k (u' i)) =
      ∑ i, X (Sum.inr i) * C (algebraMap R k (u' i)) - liftX k (∑ i, sgOf k h i * C (algebraMap R k (u' i))) := by
    simp only [fm, sub_mul, Finset.sum_sub_distrib, liftX_sum, liftX_mul, liftX_C]
  rw [hfm]
  have e2 : ∀ (cm D S XC y : AA k d), cm * D * G + y - cm * (XC - S) * G = y + cm * (D + S - XC) * G :=
    fun cm D S XC y => by ring
  rw [e2, ← liftX_add]
  have hm : (C ((m : ℕ) : k) : AA k d) ∈ Ig R k (Fin d ⊕ Fin d) := by
    rw [← map_natCast (algebraMap R k) m]
    exact ig_C _
  refine add_mem ?_ (mul_mem (mul_mem hm (sub_mem (ig_liftX (rel_hL hc w0 hw _ fun j => ⟨u' j, rfl⟩)) ?_)) hG)
  · simp only [vf]
    refine sum_mem fun t _ => mul_mem ?_ (ig_pderiv hG t)
    rcases t with j | i
    · rw [cf_inl]
      exact ig_liftX (sum_mem fun i _ => mul_mem (ig_C _) (ig_ev cz1 integral_family_point_zero (ig_pderiv (ig_FK B j) _)))
    · have e3 : cf k B h (fun i => algebraMap R k (u' i))
          (fun i => algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u' j)) i) (Sum.inr i) =
          liftX k (Dof (B.FK k) (fun j => algebraMap R k (u' j)) (sgOf k h i) -
            C (∑ j, sg1 k h i j * algebraMap R k (u' j))) + C (algebraMap R k (φ' i)) := by
        rw [cf_inr, liftX_sub, liftX_C]
        simp only [Matrix.mulVec, dotProduct, map_sub]
        ring
      rw [e3]
      exact add_mem (ig_liftX (dof_sig hc u' i)) (ig_C _)
  · exact sum_mem fun i _ => mul_mem (ig_X _) (ig_C _)

/- English proof (translation)
Introduce `R _ d O _ _ k _ _ _ _ B h hc w0 hw m ξ hξ G hG`. Take `⟨u, φ, rfl⟩` from `hξ`. Establish `hI : ∀ Y : AA k d, Y ∈ Ig R k (Fin d ⊕ Fin d) → IntAA (R` using `R) k Y := by`. Introduce and unpack `Y ⟨g, rfl⟩ n`. Conclude with `⟨MvPowerSeries.coeff n g, by rw [MvPowerSeries.coeff_map]⟩`.

Conclude with `hI _ (exp_conj_connection_integral hc w0 hw m u φ G (ig_of_intAA hG))`.
-/
theorem connection_first_identity : ConnectionIntegrality := by
  intro R _ d O _ _ k _ _ _ _ B h hc w0 hw m ξ hξ G hG
  obtain ⟨u, φ, rfl⟩ := hξ
  have hI : ∀ Y : AA k d, Y ∈ Ig R k (Fin d ⊕ Fin d) → IntAA (R := R) k Y := by
    rintro Y ⟨g, rfl⟩ n
    exact ⟨MvPowerSeries.coeff n g, by rw [MvPowerSeries.coeff_map]⟩
  exact hI _ (exp_conj_connection_integral hc w0 hw m u φ G (ig_of_intAA hG))

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofComm

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem Dof_X (F : Fin d → PS k 2 d) (u : Fin d → k) (j : Fin d) :
    Dof F u (X ((0 : Fin 1), j)) = ∑ i : Fin d, C (u i) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (F j)) := by
  unfold Dof
  simp only [MvPowerSeries.pderiv_X]
  rw [Finset.sum_eq_single j]
  · simp [Pi.single_apply]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem vf_fm (B : FB R d O) (h : PS k 2 d) (u φ u' : Fin d → k) :
    vf (cf k B h u φ) (fm k h u') = C (∑ i, φ i * u' i) := by
  simp only [fm, vf_sum, vf_mul, vf_C, mul_zero, add_zero, vf_sub, vf_X, vf_cf_liftX, cf_inr, add_sub_cancel_left,
    map_sum, map_mul]

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem cf_bracket (hC : GE.DofCommSt) (B : FB R d O) (h : PS k 2 d) (u φ u' φ' : Fin d → k)
    (t : Fin d ⊕ Fin d) : vf (cf k B h u φ) (cf k B h u' φ' t) - vf (cf k B h u' φ') (cf k B h u φ t) = 0 := by
  cases t with
  | inl j =>
    rw [cf_inl, cf_inl, ← Dof_X, ← Dof_X, vf_cf_liftX, vf_cf_liftX, hC R d O k B u u', sub_self]
  | inr i =>
    rw [cf_inr, cf_inr, vf_add, vf_add, vf_C, vf_C, add_zero, add_zero, vf_cf_liftX, vf_cf_liftX,
      hC R d O k B u u', sub_self]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem connection_second_of_commute (hC : GE.DofCommSt) : ConnectionCommutator := by
  intro R _ d O _ _ k _ _ _ B h m ξ η G
  obtain ⟨u, φ⟩ := ξ
  obtain ⟨u', φ'⟩ := η
  simp only [nabla_eq]
  rw [vfm_comm]
  have hb : (fun t => vf (cf k B h u φ) (cf k B h u' φ' t) - vf (cf k B h u' φ') (cf k B h u φ t)) =
      fun _ => (0 : AA k d) := funext (cf_bracket k hC B h u φ u' φ')
  rw [hb, vf_zeroc, vf_Cmul, vf_Cmul, vf_fm, vf_fm]
  simp only [betaH, map_mul, map_sum, map_sub, Finset.sum_sub_distrib]
  ring

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem connection_second_identity : ConnectionCommutator :=
  connection_second_of_commute invariantDerivations_commute_formal_connection

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

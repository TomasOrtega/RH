import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Ws UpperTheory.V.Sd

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F`. Establish `e : ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) = ⋂ x ∈ E, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω))`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, Subgroup.mem_comap, Set.mem_iInter, MulAction.mem_stabilizer_iff]`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `isClosed_biInter fun x _ => Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral x)`.
-/
private theorem closed_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F E : IntermediateField ℚ Ω) :
    IsClosed ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) := by
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  have e : ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) =
      ⋂ x ∈ E, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω)) := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_comap, Set.mem_iInter, MulAction.mem_stabilizer_iff]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rfl
  rw [e]
  exact isClosed_biInter fun x _ => Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral x)

/- English proof (translation)
Establish `ht : Filter.Tendsto (fun n : ℕ => ((ε (g ^ l ^ n) : ℤ_[l]ˣ) : ℤ_[l])) Filter.atTop (nhds 1)`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl)`. Use `squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0` and prove the remaining obligations.

Establish `h2` using `dvd_sub_pow_of_dvd_sub hg n`. Rewrite `h2` using `[one_pow]`. Establish `h3` using `(pow_dvd_pow _ n.le_succ).trans h2`. Rewrite using `[map_pow, Units.val_pow_eq_pow_val, inv_pow, ← zpow_natCast, ← zpow_neg, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]`. Conclude with `h3`.

Take `⟨h, hh, hc⟩` from `hS.isCompact.exists_mapClusterPt (f := Filter.atTop) (u := fun n : ℕ => g ^ l ^ n) (Filter.tendsto_principal.2 (Filter.Eventually.of_forall hm))`. Use `⟨h, hh, Units.ext ?_⟩` and prove the remaining obligations. Establish `hc'` using `hc.continuousAt_comp (Units.continuous_val.comp hε).continuousAt`. Conclude with `eq_of_nhds_neBot (hc'.clusterPt.mono ht)`.
-/
private theorem lim_pt {Γ : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime]
    (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (S : Set Γ) (hS : IsClosed S) (g : Γ)
    (hg : (l : ℤ_[l]) ∣ (ε g : ℤ_[l]) - 1) (hm : ∀ n : ℕ, g ^ l ^ n ∈ S) : ∃ h ∈ S, ε h = 1 := by
  have ht : Filter.Tendsto (fun n : ℕ => ((ε (g ^ l ^ n) : ℤ_[l]ˣ) : ℤ_[l])) Filter.atTop (nhds 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have h2 := dvd_sub_pow_of_dvd_sub hg n
    rw [one_pow] at h2
    have h3 := (pow_dvd_pow _ n.le_succ).trans h2
    rw [map_pow, Units.val_pow_eq_pow_val, inv_pow, ← zpow_natCast, ← zpow_neg,
      PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    exact h3
  obtain ⟨h, hh, hc⟩ := hS.isCompact.exists_mapClusterPt (f := Filter.atTop) (u := fun n : ℕ => g ^ l ^ n)
    (Filter.tendsto_principal.2 (Filter.Eventually.of_forall hm))
  refine ⟨h, hh, Units.ext ?_⟩
  have hc' := hc.continuousAt_comp (Units.continuous_val.comp hε).continuousAt
  exact eq_of_nhds_neBot (hc'.clusterPt.mono ht)

/- English proof (translation)
Take `⟨-, -, hloc, -⟩` from `dvrFacts l c.O`. Establish `h` using `hD.om_bar g`. Simplify using `only [Raw.bar, hg, Units.val_one] at h`. Establish `h1 : residue c.O (algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l g : ℤ_[l]) - 1)) = 0`. Rewrite using `[map_sub, map_sub, map_one, h, sub_eq_zero]`.

Both sides reduce to the same expression. Rewrite `h1` using `[residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]`. Establish `h2 : (cycZ ℚ Ω l g : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l]` using `fun hu => h1 (hu.map _)`. Rewrite `h2` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`. Then use the resulting hypothesis.
-/
private theorem dvd_of_om {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) (hg : D.om g = 1) : (l : ℤ_[l]) ∣ (cycZ ℚ Ω l g : ℤ_[l]) - 1 := by
  obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
  have h := hD.om_bar g
  simp only [Raw.bar, hg, Units.val_one] at h
  have h1 : residue c.O (algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l g : ℤ_[l]) - 1)) = 0 := by
    rw [map_sub, map_sub, map_one, h, sub_eq_zero]
    rfl
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h1
  have h2 : (cycZ ℚ Ω l g : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := fun hu => h1 (hu.map _)
  rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h2

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  (T : Tower D)

private noncomputable def eta : G T.F Ω →* (ResidueField c.O)ˣ :=
  (Units.map (residue c.O).toMonoidHom).comp ((T.fr ∅).rt wPs)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem eta_val (g : G T.F Ω) : (eta T g : ResidueField c.O) = T.rb wPs g := rfl

/- English proof (translation)
The claim follows from `Units.ext (by rw [Units.val_pow_eq_pow_val, eta_val, hT.sq, Units.val_one])`.
-/
private theorem eta_sq (hT : T.Two) (g : G T.F Ω) : eta T g ^ 2 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, eta_val, hT.sq, Units.val_one])

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F`. Use `haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩`. Use `haveI : IsGalois T.F Ω := {}`. Use `haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))`. Take `⟨k₀, -, -, -, hk⟩` from `hT.quad`.

Establish `hk' : ∀ g, eta T g = 1 ↔ g ∈ k₀.fixingSubgroup.comap (resQ T.F)` using `fun g => by`. Rewrite using `[Subgroup.mem_comap, ← hk, ← eta_val, Units.val_eq_one]`. Establish `hc : Continuous fun h : G T.F Ω => g⁻¹ * h` using `continuous_mul_left _`. Establish `h0 : IsClosed (T.GalL : Set (G T.F Ω))` using `closed_fix T.F T.K`. Establish `hd : (l : ℤ_[l]) ∣ (cycZ T.F Ω l g : ℤ_[l]) - 1` using `dvd_of_om D hD (resQ T.F g) hg`.

Take `⟨h, ⟨h1, h2⟩, h3⟩` from `lim_pt l (cycZ T.F Ω l) (continuous_cycZ T.F Ω l) _ (h0.inter ((closed_fix T.F k₀).preimage hc)) g hd (fun n => ⟨T.GalL.pow_mem hg' _, by`. Use `(hk' _).1 ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `(hl.out.odd_of_ne_two hD.l_odd).pow (n := n)`. Rewrite using `[map_mul, map_inv, map_pow, hm, pow_succ, pow_mul, eta_sq T hT, one_pow, one_mul, inv_mul_cancel]⟩)`. Establish `h4 : eta T h = 1`.

Rewrite using `[← Units.val_eq_one, eta_val]`. Conclude with `hne h ⟨h1, h3⟩`. Establish `h5` using `(hk' _).2 h2`. Rewrite `h5` using `[map_mul, h4, mul_one, map_inv, inv_eq_one]`. Then use the resulting hypothesis.
-/
private theorem eta_om (hD : D.Good) (hT : T.Two) (hne : ∀ g ∈ T.G', T.rb wPs g = 1) (g : G T.F Ω) (hg' : g ∈ T.GalL)
    (hg : D.om (resQ T.F g) = 1) : eta T g = 1 := by
  haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  obtain ⟨k₀, -, -, -, hk⟩ := hT.quad
  have hk' : ∀ g, eta T g = 1 ↔ g ∈ k₀.fixingSubgroup.comap (resQ T.F) := fun g => by
    rw [Subgroup.mem_comap, ← hk, ← eta_val, Units.val_eq_one]
  have hc : Continuous fun h : G T.F Ω => g⁻¹ * h := continuous_mul_left _
  have h0 : IsClosed (T.GalL : Set (G T.F Ω)) := closed_fix T.F T.K
  have hd : (l : ℤ_[l]) ∣ (cycZ T.F Ω l g : ℤ_[l]) - 1 := dvd_of_om D hD (resQ T.F g) hg
  obtain ⟨h, ⟨h1, h2⟩, h3⟩ := lim_pt l (cycZ T.F Ω l) (continuous_cycZ T.F Ω l) _
    (h0.inter ((closed_fix T.F k₀).preimage hc)) g hd (fun n => ⟨T.GalL.pow_mem hg' _, by
      refine (hk' _).1 ?_
      obtain ⟨m, hm⟩ := (hl.out.odd_of_ne_two hD.l_odd).pow (n := n)
      rw [map_mul, map_inv, map_pow, hm, pow_succ, pow_mul, eta_sq T hT, one_pow, one_mul, inv_mul_cancel]⟩)
  have h4 : eta T h = 1 := by
    rw [← Units.val_eq_one, eta_val]
    exact hne h ⟨h1, h3⟩
  have h5 := (hk' _).2 h2
  rwa [map_mul, h4, mul_one, map_inv, inv_eq_one] at h5

/- English proof (translation)
Establish `e : (T.fr ∅).rt wPs g = chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹` using `by show (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (0 : ℤ) * (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (1 : ℤ) = _`. Rewrite using `[zpow_zero, zpow_one, one_mul]`. Establish `e' : (T.fr ∅).rt wPs g = chi D T.pr 1 (resQ T.F g) * (chi D T.pr 3 (resQ T.F g))⁻¹`. Rewrite using `[e]`. Generalize the expression as in `resQ T.F g = s`.

Consider the cases of `T.pr`. Use `show D.al s * D.Psi s * (D.al s)⁻¹ = D.Psi s * 1⁻¹`. Rewrite using `[inv_one, mul_one, mul_inv_cancel_comm]`. Use `show D.al s * (D.al s * D.Psi s)⁻¹ = 1 * (D.Psi s)⁻¹`. Rewrite using `[one_mul, mul_inv, mul_inv_cancel_left]`.

Rewrite using `[eta_val]`. Prove the components needed by the constructor for the conclusion. Use `show residue c.O _ * residue c.O _ = residue c.O _`. Rewrite using `[← map_mul, ← Units.val_mul, e, inv_mul_cancel_right]`. Use `show residue c.O _ * residue c.O _ = residue c.O _`.

Rewrite using `[← map_mul, ← Units.val_mul, e', inv_mul_cancel_right]`.
-/
private theorem eta_mul (g : G T.F Ω) :
    eta T g * Raw.bar (chi D T.pr 2) (resQ T.F g) = Raw.bar (chi D T.pr 0) (resQ T.F g) ∧
    eta T g * Raw.bar (chi D T.pr 3) (resQ T.F g) = Raw.bar (chi D T.pr 1) (resQ T.F g) := by
  have e : (T.fr ∅).rt wPs g = chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹ := by
    show (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (0 : ℤ) *
      (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (1 : ℤ) = _
    rw [zpow_zero, zpow_one, one_mul]
  have e' : (T.fr ∅).rt wPs g = chi D T.pr 1 (resQ T.F g) * (chi D T.pr 3 (resQ T.F g))⁻¹ := by
    rw [e]
    generalize resQ T.F g = s
    cases T.pr
    · show D.al s * D.Psi s * (D.al s)⁻¹ = D.Psi s * 1⁻¹
      rw [inv_one, mul_one, mul_inv_cancel_comm]
    · show D.al s * (D.al s * D.Psi s)⁻¹ = 1 * (D.Psi s)⁻¹
      rw [one_mul, mul_inv, mul_inv_cancel_left]
  rw [eta_val]
  constructor
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e, inv_mul_cancel_right]
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e', inv_mul_cancel_right]

/- English proof (translation)
Rewrite using `[← h, ← mul_assoc, ← Units.val_mul, ← pow_two, eta_sq T hT, Units.val_one, one_mul]`.
-/
private theorem eta_mul' (hT : T.Two) (g : G T.F Ω) {u v : ResidueField c.O} (h : eta T g * u = v) : eta T g * v = u := by
  rw [← h, ← mul_assoc, ← Units.val_mul, ← pow_two, eta_sq T hT, Units.val_one, one_mul]

private noncomputable def etaL : T.GalL →* (ResidueField c.O)ˣ := (eta T).comp T.GalL.subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem etaL_app (g : T.GalL) : etaL T g = eta T g := rfl

/- English proof (translation)
Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.pow_apply, MonoidHom.one_apply, etaL_app, eta_sq T hT]`.
-/
private theorem etaL_sq (hT : T.Two) : etaL T ^ 2 = 1 := by
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, etaL_app, eta_sq T hT]

/- English proof (translation)
Simplify using `only [etaL_app]`. Use `match i with`. Consider the case `0 => exact ⟨2, fun g => eta_mul' T hT g (eta_mul T g).1⟩`. Consider the case `1 => exact ⟨3, fun g => eta_mul' T hT g (eta_mul T g).2⟩`. Consider the case `2 => exact ⟨0, fun g => (eta_mul T g).1⟩`.

Consider the case `3 => exact ⟨1, fun g => (eta_mul T g).2⟩`.
-/
private theorem etaL_perm (hT : T.Two) (i : Fin 4) : ∃ j, ∀ g : T.GalL, etaL T g * Raw.bar (chi D T.pr i) (resQ T.F g) =
      Raw.bar (chi D T.pr j) (resQ T.F g) := by
  simp only [etaL_app]
  match i with
  | 0 => exact ⟨2, fun g => eta_mul' T hT g (eta_mul T g).1⟩
  | 1 => exact ⟨3, fun g => eta_mul' T hT g (eta_mul T g).2⟩
  | 2 => exact ⟨0, fun g => (eta_mul T g).1⟩
  | 3 => exact ⟨1, fun g => (eta_mul T g).2⟩

end

/- English proof (translation)
Introduce `Ω _ _ _ l hl c D T hD hO hT`. Assume the negation of the conclusion as `hne`. Establish `hne' : ∀ g ∈ T.G', T.rb wPs g = 1` using `fun g hg => by_contra fun h => hne ⟨g, hg, h⟩`. Establish `key` using `hO.g3' (etaL T) (etaL_sq T hT) (fun g hg => by rw [etaL_app]; exact eta_om T hD hT hne' g g.2 hg) (etaL_perm T hT)`. Take `⟨g, hg, hg'⟩` from `hO.g3 wPs (by decide)`.

Establish `h1` using `etaL_app T ⟨g, hg⟩`. Rewrite `h1` using `[key, MonoidHom.one_apply]`. Apply `hg'` to reduce the goal to its premises. Rewrite using `[← eta_val, ← h1, Units.val_one]`.
-/
theorem UpperTheory.residual_characters_psi_ne :
    UpperTheory.V.Sd.S2.PsiNe := by
  intro Ω _ _ _ l hl c D T hD hO hT
  by_contra hne
  have hne' : ∀ g ∈ T.G', T.rb wPs g = 1 := fun g hg => by_contra fun h => hne ⟨g, hg, h⟩
  have key := hO.g3' (etaL T) (etaL_sq T hT)
    (fun g hg => by rw [etaL_app]; exact eta_om T hD hT hne' g g.2 hg) (etaL_perm T hT)
  obtain ⟨g, hg, hg'⟩ := hO.g3 wPs (by decide)
  have h1 := etaL_app T ⟨g, hg⟩
  rw [key, MonoidHom.one_apply] at h1
  apply hg'
  rw [← eta_val, ← h1, Units.val_one]

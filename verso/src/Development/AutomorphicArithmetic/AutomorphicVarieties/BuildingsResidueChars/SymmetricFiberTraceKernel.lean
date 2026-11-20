import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.ResidualAutomorphyOfLinkedEnds
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPairCorrespondence
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSupportFinite

open MulAction UpperTheory.V.Z.Sym

/- English proof (translation)
Use `set g := Quotient.out y with hg`. Establish `hy : ((g : G) : G ⧸ U) = y` using `Quotient.out_eq y`. Rewrite using `[← hy, MulAction.Quotient.smul_mk, QuotientGroup.eq]`. Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, smul_eq_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨g⁻¹ * a * g, ?_, by group⟩` and prove the remaining obligations. Use `inv_mem h` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Introduce and unpack `⟨u, hu, rfl⟩`.

Establish `: (g * u * g⁻¹ * g)⁻¹ * g = u⁻¹` using `by group`. Rewrite using `[this]`. Conclude with `inv_mem hu`.
-/
private theorem smul_quotient_eq_self_iff_exists_conj_out (G : Type) [Group G] (U : Subgroup G) (y : G ⧸ U) (a : G) :
    a • y = y ↔ ∃ u ∈ U, (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out y))) u = a := by
  set g := Quotient.out y with hg
  have hy : ((g : G) : G ⧸ U) = y := Quotient.out_eq y
  rw [← hy, MulAction.Quotient.smul_mk, QuotientGroup.eq]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, smul_eq_mul]
  constructor
  · intro h
    refine ⟨g⁻¹ * a * g, ?_, by group⟩
    have := inv_mem h
    simpa [mul_assoc] using this
  · rintro ⟨u, hu, rfl⟩
    have : (g * u * g⁻¹ * g)⁻¹ * g = u⁻¹ := by group
    rw [this]; exact inv_mem hu

/- English proof (translation)
Introduce `Γ G V _ _ _ _ _ B hFin hω hΓ₀ f hf`. Use `set s := Base.Tw.one B with hs`. Set `δ : ConjClasses Γ → Γ` to `fun i => Classical.choose (ConjClasses.exists_rep i)`. Establish `hδ : ∀ i, ConjClasses.mk (δ i) = i` using `fun i => Classical.choose_spec (ConjClasses.exists_rep i)`. Establish `hRel : ∀ a b : Γ, s.Rel a b ↔ IsConj a b`.

Introduce `a b`. Simplify using `only [Base.Tw.Rel, hs, Base.Tw.one, hΓ₀, Subgroup.mem_bot, MulEquiv.refl_apply, exists_eq_left, mul_one, isConj_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩; exact ⟨x⁻¹, by group⟩`. Introduce and unpack `⟨c, rfl⟩; exact ⟨c⁻¹, by group⟩`.

Establish `hCent : ∀ (a x : Γ), x ∈ s.Cent a ↔ x * a = a * x`. Introduce `a x`. Use `show (∃ z ∈ B.Γ₀, x⁻¹ * a * (MulEquiv.refl Γ) x = a * z) ↔ _`. Simplify using `only [hΓ₀, Subgroup.mem_bot, exists_eq_left, mul_one, MulEquiv.refl_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `h; calc x * a = x * (x⁻¹ * a * x) := by rw [h] _ = a * x := by group`. Introduce `h; calc x⁻¹ * a * x = x⁻¹ * (x * a) := by rw [mul_assoc, h] _ = a := by group`. Establish `h2 : ∀ z ∈ (⊥ : Subgroup Γ), ∀ y : G ⧸ B.U, B.ι z • y = y` using `fun z hz y => by`. Rewrite using `[Subgroup.mem_bot.mp hz, map_one, one_smul]`. Establish `h3 : ∀ h γ : Γ, LinearMap.trace ℂ V (B.W (h * γ * h⁻¹)) = LinearMap.trace ℂ V (B.W γ)` using `fun h γ => by`.

Rewrite using `[map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]`. Establish `h4 : ∀ u ∈ B.U, ∀ g : G, f (u⁻¹ * g * u) = f g` using `fun u hu g => by`. Establish `hl` using `hf.left ⟨u⁻¹, inv_mem hu⟩ (g * u)`. Establish `hr` using `hf.right ⟨u, hu⟩ g`. Simplify using `only [hs, Base.Tw.one, MulEquiv.refl_apply, hω, MonoidHom.one_apply, Units.val_one, inv_one, one_mul] at hl hr`.

Rewrite using `[mul_assoc, hl, hr]`. Establish `h5 : ∀ g : G, {γ | LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0}.Finite` using `fun g => (UpperTheory.orbitalFiber_support_finite Γ G V B hFin hΓ₀ f hf g).subset (fun γ h => right_ne_zero_of_mul h)`. Establish `h8 : ∀ i x, x ∈ ((s.Cent (δ i)).subtype).range ↔ x * δ i = δ i * x` using `fun i x => by`. Rewrite using `[Subgroup.range_subtype, hCent]`. Establish `h9 : ∀ (i i' : ConjClasses Γ) (h : Γ), δ i' = h * δ i * h⁻¹ → i = i'` using `fun i i' h e => by`.

Rewrite using `[← hδ i, ← hδ i', ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]`. Conclude with `⟨h, e.symm⟩`. Establish `h10 : ∀ (γ : Γ) (g : G), LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0 → ∃ i h, γ = h * δ i * h⁻¹` using `fun γ g _ => by`. Take `⟨c, hc⟩` from `isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ (ConjClasses.mk γ)))`. Conclude with `⟨ConjClasses.mk γ, c, hc.symm⟩`.

Establish `h7 : ∀ y : G ⧸ B.U, (⊥ : Subgroup Γ).relIndex (Subgroup.comap B.ι (stabilizer G y)) ≠ 0` using `fun y => by`. Use `hFin.stab (Quotient.out y)` as an intermediate fact. Rewrite `this` using `[hΓ₀]`. Use `this using 2` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Rewrite using `[Subgroup.mem_comap, Subgroup.mem_comap, mem_stabilizer_iff, Subgroup.mem_map]`. Conclude with `smul_quotient_eq_self_iff_exists_conj_out G B.U y (B.ι x)`. Establish `hT` using `(Tf.trace Γ G V B hFin s f hf (ConjClasses Γ) δ (fun i j h => by`. Rewrite using `[← hδ i, ← hδ j, ConjClasses.mk_eq_mk_iff_isConj]`. Conclude with `(hRel _ _).mp h)`.

Use the proof step `(fun γ _ => ⟨ConjClasses.mk γ, (hRel _ _).mpr (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ _))⟩)).2`. Establish `hP` using `UpperTheory.orbitalFiber_pair_correspondence Γ G (ConjClasses Γ) B.ι ⊥ B.U (fun γ => LinearMap.trace ℂ V (B.W γ)) f δ (fun i => ↥(s.Cent (δ i))) (fun i => (s.Cent (δ i)).subtype) bot_le h2 h3 h4 h5 hFin.cls h7 h8 h9 h10`. Rewrite using `[hT, hP]`. Use `finsum_congr fun i => ?_` and prove the remaining obligations. Simplify using `only [Base.Tw.term, hs, Base.Tw.one, LinearMap.comp_id]`.

Use `congr 2`. Rewrite using `[hΓ₀]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.symmetric_fiber_trace_kernel :
    UpperTheory.V.Z.Sym.Glob.Fib.TrKer := by
  intro Γ G V _ _ _ _ _ B hFin hω hΓ₀ f hf
  classical
  set s := Base.Tw.one B with hs
  let δ : ConjClasses Γ → Γ := fun i => Classical.choose (ConjClasses.exists_rep i)
  have hδ : ∀ i, ConjClasses.mk (δ i) = i := fun i => Classical.choose_spec (ConjClasses.exists_rep i)
  have hRel : ∀ a b : Γ, s.Rel a b ↔ IsConj a b := by
    intro a b
    simp only [Base.Tw.Rel, hs, Base.Tw.one, hΓ₀, Subgroup.mem_bot, MulEquiv.refl_apply, exists_eq_left, mul_one, isConj_iff]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x⁻¹, by group⟩
    · rintro ⟨c, rfl⟩; exact ⟨c⁻¹, by group⟩
  have hCent : ∀ (a x : Γ), x ∈ s.Cent a ↔ x * a = a * x := by
    intro a x
    show (∃ z ∈ B.Γ₀, x⁻¹ * a * (MulEquiv.refl Γ) x = a * z) ↔ _
    simp only [hΓ₀, Subgroup.mem_bot, exists_eq_left, mul_one, MulEquiv.refl_apply]
    constructor
    · intro h; calc x * a = x * (x⁻¹ * a * x) := by rw [h]
        _ = a * x := by group
    · intro h; calc x⁻¹ * a * x = x⁻¹ * (x * a) := by rw [mul_assoc, h]
        _ = a := by group
  have h2 : ∀ z ∈ (⊥ : Subgroup Γ), ∀ y : G ⧸ B.U, B.ι z • y = y := fun z hz y => by
    rw [Subgroup.mem_bot.mp hz, map_one, one_smul]
  have h3 : ∀ h γ : Γ, LinearMap.trace ℂ V (B.W (h * γ * h⁻¹)) = LinearMap.trace ℂ V (B.W γ) := fun h γ => by
    rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]
  have h4 : ∀ u ∈ B.U, ∀ g : G, f (u⁻¹ * g * u) = f g := fun u hu g => by
    have hl := hf.left ⟨u⁻¹, inv_mem hu⟩ (g * u)
    have hr := hf.right ⟨u, hu⟩ g
    simp only [hs, Base.Tw.one, MulEquiv.refl_apply, hω, MonoidHom.one_apply, Units.val_one, inv_one, one_mul] at hl hr
    rw [mul_assoc, hl, hr]
  have h5 : ∀ g : G, {γ | LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0}.Finite := fun g =>
    (UpperTheory.orbitalFiber_support_finite Γ G V B hFin hΓ₀ f hf g).subset (fun γ h => right_ne_zero_of_mul h)
  have h8 : ∀ i x, x ∈ ((s.Cent (δ i)).subtype).range ↔ x * δ i = δ i * x := fun i x => by
    rw [Subgroup.range_subtype, hCent]
  have h9 : ∀ (i i' : ConjClasses Γ) (h : Γ), δ i' = h * δ i * h⁻¹ → i = i' := fun i i' h e => by
    rw [← hδ i, ← hδ i', ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]; exact ⟨h, e.symm⟩
  have h10 : ∀ (γ : Γ) (g : G), LinearMap.trace ℂ V (B.W γ) * f (g⁻¹ * B.ι γ * g) ≠ 0 →
      ∃ i h, γ = h * δ i * h⁻¹ := fun γ g _ => by
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ (ConjClasses.mk γ)))
    exact ⟨ConjClasses.mk γ, c, hc.symm⟩
  have h7 : ∀ y : G ⧸ B.U, (⊥ : Subgroup Γ).relIndex (Subgroup.comap B.ι (stabilizer G y)) ≠ 0 := fun y => by
    have := hFin.stab (Quotient.out y)
    rw [hΓ₀] at this
    convert this using 2
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, mem_stabilizer_iff, Subgroup.mem_map]
    exact smul_quotient_eq_self_iff_exists_conj_out G B.U y (B.ι x)
  have hT := (Tf.trace Γ G V B hFin s f hf (ConjClasses Γ) δ (fun i j h => by
      rw [← hδ i, ← hδ j, ConjClasses.mk_eq_mk_iff_isConj]; exact (hRel _ _).mp h)
    (fun γ _ => ⟨ConjClasses.mk γ, (hRel _ _).mpr (ConjClasses.mk_eq_mk_iff_isConj.mp (hδ _))⟩)).2
  have hP := UpperTheory.orbitalFiber_pair_correspondence Γ G (ConjClasses Γ) B.ι ⊥ B.U (fun γ => LinearMap.trace ℂ V (B.W γ)) f δ
    (fun i => ↥(s.Cent (δ i))) (fun i => (s.Cent (δ i)).subtype) bot_le h2 h3 h4 h5
    hFin.cls h7 h8 h9 h10
  rw [hT, hP]
  refine finsum_congr fun i => ?_
  simp only [Base.Tw.term, hs, Base.Tw.one, LinearMap.comp_id]
  congr 2
  rw [hΓ₀]; rfl

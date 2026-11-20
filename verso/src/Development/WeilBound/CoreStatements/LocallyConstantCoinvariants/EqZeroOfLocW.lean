import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KdExistsInv

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {ψ : AddChar (AF F) ℂ}

/- English proof (translation)
The claim follows from `Prod.ext (funext fun i => map_mul (evFin F v) _ _) (funext fun i => map_mul (evFin F v) _ _)`.
-/
theorem locW_smul (a : AF F) (w : (κ → AF F) × (κ → AF F)) : locW v (a • w) = evFin F v a • locW v w :=
  Prod.ext (funext fun i => map_mul (evFin F v) _ _) (funext fun i => map_mul (evFin F v) _ _)

/- English proof (translation)
The claim follows from `Prod.ext (funext fun i => map_add (evFin F v) _ _) (funext fun i => map_add (evFin F v) _ _)`.
-/
theorem locW_add (w w' : (κ → AF F) × (κ → AF F)) : locW v (w + w') = locW v w + locW v w' :=
  Prod.ext (funext fun i => map_add (evFin F v) _ _) (funext fun i => map_add (evFin F v) _ _)

/- English proof (translation)
Rewrite using `[← kd_at_iff.1 ha]`. Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations. Establish `: evFin F v (w.1 i) = 0` using `congrFun (congrArg Prod.fst h) i`. Express the relevant statement in the definitionally equal form `sgl v 1 * w.1 i = 0`. Rewrite using `[mul_comm, mul_sgl, this, zero_mul, map_zero]`.

Establish `: evFin F v (w.2 i) = 0` using `congrFun (congrArg Prod.snd h) i`. Express the relevant statement in the definitionally equal form `sgl v 1 * w.2 i = 0`. Rewrite using `[mul_comm, mul_sgl, this, zero_mul, map_zero]`.
-/
theorem eq_zero_of_locW {w : (κ → AF F) × (κ → AF F)} (ha : At (evFin F v) w) (h : locW v w = 0) : w = 0 := by
  rw [← kd_at_iff.1 ha]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · have : evFin F v (w.1 i) = 0 := congrFun (congrArg Prod.fst h) i
    change sgl v 1 * w.1 i = 0
    rw [mul_comm, mul_sgl, this, zero_mul, map_zero]
  · have : evFin F v (w.2 i) = 0 := congrFun (congrArg Prod.snd h) i
    change sgl v 1 * w.2 i = 0
    rw [mul_comm, mul_sgl, this, zero_mul, map_zero]

/- English proof (translation)
Simplify using `only [dotProduct, map_sum, map_mul]`.
-/
theorem ev_dot (a b : κ → AF F) : evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ fun i => evFin F v (b i) := by
  simp only [dotProduct, map_sum, map_mul]

/- English proof (translation)
Simplify using `only [coord, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, neg_add]`. Both sides reduce to the same expression.
-/
theorem coord_add (u u' : Matrix α β (AE F E)) : coord σ t JA JB (u + u') = coord σ t JA JB u + coord σ t JA JB u' := by
  simp only [coord, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, neg_add]
  rfl

/- English proof (translation)
Simplify using `only [coord, h.smul1, h.smul2, Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]`. Both sides reduce to the same expression.
-/
theorem coord_smul (h : IsSec σ t sec) (a : AF F) (u : Matrix α β (AE F E)) :
    coord σ t JA JB (a • u) = evFin F v a • coord σ t JA JB u := by
  simp only [coord, h.smul1, h.smul2, Matrix.mul_smul, Matrix.smul_mul, ← smul_neg]
  rfl

/- English proof (translation)
Take `⟨A, hA⟩` from `hG.uA`. Take `⟨B, hB⟩` from `hG.uB`. Use `⟨secM sec (-toM w.2) (-((A⁻¹).1 * toM w.1 * ((B⁻¹).1)ᵀ)), h.atM _ _, ?_, fun h0 => ?_⟩` and prove the remaining obligations. Rewrite using `[coord, h.fstM, h.sndM, ← hA, ← hB, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.mul_one]`. Both sides reduce to the same expression.

Rewrite using `[h.sndM, h0, show toM (0 : α × β → Fv F v) = 0 from rfl, Matrix.mul_zero, Matrix.zero_mul, neg_zero]`.
-/
theorem exists_coord (h : IsSec σ t sec) (hG : Grams σ t JA JB) (w : (α × β → Fv F v) × (α × β → Fv F v)) :
    ∃ u, At (evFin F v) u ∧ coord σ t JA JB u = w ∧ (w.1 = 0 → u.map (piW (t.comp σ)) = 0) := by
  obtain ⟨A, hA⟩ := hG.uA
  obtain ⟨B, hB⟩ := hG.uB
  refine ⟨secM sec (-toM w.2) (-((A⁻¹).1 * toM w.1 * ((B⁻¹).1)ᵀ)), h.atM _ _, ?_, fun h0 => ?_⟩
  · rw [coord, h.fstM, h.sndM, ← hA, ← hB, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.mul_one]
    rfl
  · rw [h.sndM, h0, show toM (0 : α × β → Fv F v) = 0 from rfl, Matrix.mul_zero, Matrix.zero_mul, neg_zero]

/- English proof (translation)
Take `⟨A, hA⟩` from `hG.uA`. Take `⟨B, hB⟩` from `hG.uB`. Establish `h1 : -(JA.map (piW t) * u.map (piW (t.comp σ)) * (JB.map (piW t))ᵀ) = 0` using `congrArg toM (congrArg Prod.fst h0)`. Establish `h2 : -u.map (piW t) = 0` using `congrArg toM (congrArg Prod.snd h0)`. Use `h.extM (by rwa [sub_zero]) (by rw [neg_eq_zero.1 h2, Matrix.map_zero _ (map_zero _)]) ?_` and prove the remaining obligations.

Rewrite `h1` using `[neg_eq_zero, ← hA, ← hB]`. Use `congrArg (fun m => (A⁻¹).1 * m * ((B⁻¹).1)ᵀ) h1` as an intermediate fact. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul] at this`. Rewrite `this` using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul, Units.inv_mul, transpose_one, Matrix.mul_one, ← Matrix.map_zero (piW (t.comp σ)) (map_zero _)]`. Then use the resulting hypothesis.
-/
theorem coord_inj (h : IsSec σ t sec) (hG : Grams σ t JA JB) {u : Matrix α β (AE F E)} (ha : At (evFin F v) u)
    (h0 : coord σ t JA JB u = 0) : u = 0 := by
  obtain ⟨A, hA⟩ := hG.uA
  obtain ⟨B, hB⟩ := hG.uB
  have h1 : -(JA.map (piW t) * u.map (piW (t.comp σ)) * (JB.map (piW t))ᵀ) = 0 := congrArg toM (congrArg Prod.fst h0)
  have h2 : -u.map (piW t) = 0 := congrArg toM (congrArg Prod.snd h0)
  refine h.extM (by rwa [sub_zero]) (by rw [neg_eq_zero.1 h2, Matrix.map_zero _ (map_zero _)]) ?_
  rw [neg_eq_zero, ← hA, ← hB] at h1
  have := congrArg (fun m => (A⁻¹).1 * m * ((B⁻¹).1)ᵀ) h1
  simp only [Matrix.mul_zero, Matrix.zero_mul] at this
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul, Units.inv_mul,
    transpose_one, Matrix.mul_one, ← Matrix.map_zero (piW (t.comp σ)) (map_zero _)] at this

/- English proof (translation)
Use `choose s hs1 hs2 _ using exists_coord h hG`. Establish `key : ∀ u, locW v (d.e (s (coord σ t JA JB u))) = locW v (d.e u)` using `fun u => by`. Establish `: s (coord σ t JA JB u) = sgl v 1 • u`. Use `sub_eq_zero.1 (coord_inj h hG ((hs1 _).kd_sub (at_sgl_smul _ _)) ?_)` and prove the remaining obligations. Rewrite using `[sub_eq_add_neg, ← neg_smul, coord_add, coord_smul h, hs2, map_neg, ev_sgl, neg_smul, one_smul, add_neg_cancel]`.

Rewrite using `[this, map_smul, locW_smul, ev_sgl, one_smul]`. Set `f : ((α × β → Fv F v) × (α × β → Fv F v)) →ₗ[Fv F v] ((κ → Fv F v) × (κ → Fv F v))` to `{ toFun := fun w => locW v (d.e (s w)) map_add' := fun w w' => by rw [← locW_add, ← map_add, ← key (s w + s w'), coord_add, hs2, hs2] map_smul' := fun a w => by`. Use `key (sgl v a • s w)` as an intermediate fact. Rewrite `this` using `[coord_smul h, hs2, ev_sgl, map_smul, locW_smul, ev_sgl]`. Conclude with `this }`.

Establish `hb : Function.Bijective f`. Use `⟨(injective_iff_map_eq_zero f).2 fun w hw => ?_, fun w => ?_⟩` and prove the remaining obligations. Establish `h1 : s w = 0` using `d.e.map_eq_zero_iff.1 (eq_zero_of_locW ((hs1 w).kd_map d.e.toLinearMap) hw)`. Rewrite using `[← hs2 w, h1, ← zero_smul (AF F) (0 : Matrix α β (AE F E)), coord_smul h, map_zero, zero_smul]`. Use `⟨coord σ t JA JB (d.e.symm (fun i => sgl v (w.1 i), fun i => sgl v (w.2 i))), (key _).trans ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `Prod.ext (funext fun i => ev_sgl _) (funext fun i => ev_sgl _)`. Use `⟨LinearEquiv.ofBijective f hb, fun w w' => ?_, key⟩` and prove the remaining obligations. Use `congrArg (evFin F v) ((d.form (s w) (s w')).symm.trans (symp_eq h hG (hs1 w) (s w')))` as an intermediate fact. Rewrite `this` using `[ev_sgl, hs2, hs2, map_sub, ev_dot, ev_dot]`. Then use the resulting hypothesis.
-/
theorem exists_e (h : IsSec σ t sec) (hG : Grams σ t JA JB) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) :
    ∃ e : ((α × β → Fv F v) × (α × β → Fv F v)) ≃ₗ[Fv F v] ((κ → Fv F v) × (κ → Fv F v)),
      (∀ w w', (e w).1 ⬝ᵥ (e w').2 - (e w').1 ⬝ᵥ (e w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) ∧
      ∀ u, e (coord σ t JA JB u) = locW v (d.e u) := by
  choose s hs1 hs2 _ using exists_coord h hG
  have key : ∀ u, locW v (d.e (s (coord σ t JA JB u))) = locW v (d.e u) := fun u => by
    have : s (coord σ t JA JB u) = sgl v 1 • u := by
      refine sub_eq_zero.1 (coord_inj h hG ((hs1 _).kd_sub (at_sgl_smul _ _)) ?_)
      rw [sub_eq_add_neg, ← neg_smul, coord_add, coord_smul h, hs2, map_neg, ev_sgl, neg_smul, one_smul, add_neg_cancel]
    rw [this, map_smul, locW_smul, ev_sgl, one_smul]
  let f : ((α × β → Fv F v) × (α × β → Fv F v)) →ₗ[Fv F v] ((κ → Fv F v) × (κ → Fv F v)) :=
    { toFun := fun w => locW v (d.e (s w))
      map_add' := fun w w' => by rw [← locW_add, ← map_add, ← key (s w + s w'), coord_add, hs2, hs2]
      map_smul' := fun a w => by
        have := key (sgl v a • s w)
        rw [coord_smul h, hs2, ev_sgl, map_smul, locW_smul, ev_sgl] at this
        exact this }
  have hb : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun w hw => ?_, fun w => ?_⟩
    · have h1 : s w = 0 := d.e.map_eq_zero_iff.1 (eq_zero_of_locW ((hs1 w).kd_map d.e.toLinearMap) hw)
      rw [← hs2 w, h1, ← zero_smul (AF F) (0 : Matrix α β (AE F E)), coord_smul h, map_zero, zero_smul]
    · refine ⟨coord σ t JA JB (d.e.symm (fun i => sgl v (w.1 i), fun i => sgl v (w.2 i))), (key _).trans ?_⟩
      rw [LinearEquiv.apply_symm_apply]
      exact Prod.ext (funext fun i => ev_sgl _) (funext fun i => ev_sgl _)
  refine ⟨LinearEquiv.ofBijective f hb, fun w w' => ?_, key⟩
  have := congrArg (evFin F v) ((d.form (s w) (s w')).symm.trans (symp_eq h hG (hs1 w) (s w')))
  rwa [ev_sgl, hs2, hs2, map_sub, ev_dot, ev_dot] at this

variable (t ψ) in

structure LM (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (ι : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((α × β → Fv F v) → ℂ)) : Prop where
  bij : Set.BijOn ι (SB (κ → Fv F v) : Set _) (SB (α × β → Fv F v) : Set _)
  Heisenberg₂ : ∀ u, ∀ φ ∈ SB (κ → Fv F v), ι (schr (psiV ψ v) (locW v (d.e u)) φ) = schr (psiV ψ v) (coord σ t JA JB u) (ι φ)

/- English proof (translation)
Take `⟨e, h1, h2⟩` from `exists_e h hG d`. Take `⟨ι, hb, hι⟩` from `hM _ κ (α × β) (psiV ψ v) ((hA.psi F ψ hψ).2 v).1 ((hA.psi F ψ hψ).2 v).2 e h1`. Conclude with `⟨ι, hb, fun u φ hφ => by rw [← h2, hι _ φ hφ]⟩`.
-/
theorem exists_lm (hM : ModelEx) (hA : AdSt) (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t JA JB)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) : ∃ ι, LM t ψ d ι := by
  obtain ⟨e, h1, h2⟩ := exists_e h hG d
  obtain ⟨ι, hb, hι⟩ := hM _ κ (α × β) (psiV ψ v) ((hA.psi F ψ hψ).2 v).1 ((hA.psi F ψ hψ).2 v).2 e h1
  exact ⟨ι, hb, fun u φ hφ => by rw [← h2, hι _ φ hφ]⟩

/- English proof (translation)
Establish `h1` using `h.unit_rel g`. Rewrite `h1` using `[hg]`. Establish `h2 : (((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW (t.comp σ)))ᵀ * (JB.map (piW t))ᵀ = (JB.map (piW t))ᵀ * (g₀⁻¹).1`. Use `congrArg (fun m => mᵀ * (g₀⁻¹).1) h1` as an intermediate fact. Simplify using `only [transpose_mul, transpose_transpose, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this`.

Conclude with `this`. Simplify using `only [coord, actB, toM_ofM, Matrix.map_mul, transpose_map, hg, Matrix.neg_mul, Matrix.mul_assoc, h2]`.
-/
theorem coord_actB (h : IsSec σ t sec) (g : UG (cA σ) JB) (g₀ : GL β (Fv F v))
    (hg : ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = g₀) (u : Matrix α β (AE F E)) :
    coord σ t JA JB (actB (cA σ) g u) =
      (ofM (toM (coord σ t JA JB u).1 * (g₀⁻¹).1), ofM (toM (coord σ t JA JB u).2 * (g₀.1)ᵀ)) := by
  have h1 := h.unit_rel g
  rw [hg] at h1
  have h2 : (((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW (t.comp σ)))ᵀ * (JB.map (piW t))ᵀ =
      (JB.map (piW t))ᵀ * (g₀⁻¹).1 := by
    have := congrArg (fun m => mᵀ * (g₀⁻¹).1) h1
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
    exact this
  simp only [coord, actB, toM_ofM, Matrix.map_mul, transpose_map, hg, Matrix.neg_mul, Matrix.mul_assoc, h2]

/- English proof (translation)
Take `⟨e, -, he⟩` from `exists_e h hG d`. Establish `hc` using `((hA.psi F ψ hψ).2 v).1`. Establish `m : ∀ (a : GL β (Fv F v)), ∀ φ ∈ SB (κ → Fv F v), rmL a (ι φ) ∈ SB _` using `fun a φ hφ => rmL_mem a (hι.bij.1 hφ)`. Establish `inv : ∀ (a : GL β (Fv F v)), ∀ φ ∈ SB (κ → Fv F v), j (rmL a⁻¹ (ι (j (rmL a (ι φ))))) = φ` using `fun a φ hφ => by`. Rewrite using `[(hj _ (m a φ hφ)).2, rmL_inv]`.

Conclude with `hι.bij.2.1 (hj _ (hι.bij.1 hφ)).1 hφ (hj _ (hι.bij.1 hφ)).2`. Establish `hh : ∀ w, ∀ φ ∈ SB (κ → Fv F v), ι (schr (psiV ψ v) (e w) φ) = schr (psiV ψ v) w (ι φ)` using `fun w φ hφ => by`. Take `⟨u, -, rfl, -⟩` from `exists_coord h hG w`. Rewrite using `[he, hι.Heisenberg₂ u φ hφ]`. Use `hA.act F κ ψ hψ v (om g) (fun w => d.e (actB (cA σ) g (d.e.symm w))) (j ∘ₗ rmL g₀ ∘ₗ ι) (j ∘ₗ rmL g₀⁻¹ ∘ₗ ι) (fun w => e (ofM (toM (e.symm w).1 * (g₀⁻¹).1), ofM (toM (e.symm w).2 * (g₀.1)ᵀ))) (hom.pres g) (hom.adm g) (fun w Φ hΦ => ?_) (fun φ hφ => ⟨(hj _ (m _ φ hφ)).1, (hj _ (m …` and prove the remaining obligations.

Use `hom.impl g (d.e.symm w) Φ hΦ` as an intermediate fact. Simplify `this` using `only [Darboux.rho, LinearEquiv.apply_symm_apply]`. Simplify `inv g₀⁻¹ φ hφ` using `only [inv_inv, LinearMap.comp_apply]`. Take `⟨w, rfl⟩` from `e.surjective w`. Establish `h1` using `(hj _ (m g₀ φ hφ))`.

Use `hι.bij.2.1 (hj _ (m _ _ (schr_mem hc _ hφ))).1 (schr_mem hc _ h1.1) ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearEquiv.symm_apply_apply]`. Rewrite using `[(hj _ (m _ _ (schr_mem hc _ hφ))).2, hh _ _ h1.1, h1.2, hh _ _ hφ, rmL_schr]`. Take `⟨u, rfl⟩` from `d.e.surjective w`. Simplify using `only [LinearEquiv.symm_apply_apply]`.

Rewrite using `[← he, ← he, LinearEquiv.symm_apply_apply, coord_actB h g g₀ hg]`. Take `⟨u, rfl⟩` from `d.e.surjective w`. Simplify using `only [LinearEquiv.symm_apply_apply]`. Rewrite using `[← map_sub, show actB (cA σ) g u - u = u * (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1)ᵀ by`. Rewrite using `[actB, transpose_sub, transpose_one, Matrix.mul_sub, Matrix.mul_one]]`.

Conclude with `(ha.kd_transpose.kd_mul_left u).kd_map d.e.toLinearMap`.
-/
theorem acts_scalar (hA : AdSt) (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t JA JB)
    {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {ι} (hι : LM t ψ d ι)
    {j : ((α × β → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)} (hj : ∀ Φ ∈ SB _, j Φ ∈ SB _ ∧ ι (j Φ) = Φ)
    {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)} (hom : IsSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (g : UG (cA σ) JB) (ha : At (evFin F v) (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1)) (g₀ : GL β (Fv F v))
    (hg : ((g : GL β (AE F E)) : Matrix β β (AE F E)).map (piW t) = g₀) :
    ∃ c : ℂ, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) (om g) φ (c • j (rmL g₀ (ι φ))) := by
  obtain ⟨e, -, he⟩ := exists_e h hG d
  have hc := ((hA.psi F ψ hψ).2 v).1
  have m : ∀ (a : GL β (Fv F v)), ∀ φ ∈ SB (κ → Fv F v), rmL a (ι φ) ∈ SB _ := fun a φ hφ => rmL_mem a (hι.bij.1 hφ)
  have inv : ∀ (a : GL β (Fv F v)), ∀ φ ∈ SB (κ → Fv F v), j (rmL a⁻¹ (ι (j (rmL a (ι φ))))) = φ := fun a φ hφ => by
    rw [(hj _ (m a φ hφ)).2, rmL_inv]
    exact hι.bij.2.1 (hj _ (hι.bij.1 hφ)).1 hφ (hj _ (hι.bij.1 hφ)).2
  have hh : ∀ w, ∀ φ ∈ SB (κ → Fv F v), ι (schr (psiV ψ v) (e w) φ) = schr (psiV ψ v) w (ι φ) := fun w φ hφ => by
    obtain ⟨u, -, rfl, -⟩ := exists_coord h hG w
    rw [he, hι.Heisenberg₂ u φ hφ]
  refine hA.act F κ ψ hψ v (om g) (fun w => d.e (actB (cA σ) g (d.e.symm w))) (j ∘ₗ rmL g₀ ∘ₗ ι) (j ∘ₗ rmL g₀⁻¹ ∘ₗ ι)
    (fun w => e (ofM (toM (e.symm w).1 * (g₀⁻¹).1), ofM (toM (e.symm w).2 * (g₀.1)ᵀ))) (hom.pres g) (hom.adm g)
    (fun w Φ hΦ => ?_) (fun φ hφ => ⟨(hj _ (m _ φ hφ)).1, (hj _ (m _ φ hφ)).1, inv _ φ hφ, ?_⟩) (fun w φ hφ => ?_) fun w => ⟨?_, ?_⟩
  · have := hom.impl g (d.e.symm w) Φ hΦ
    simpa only [Darboux.rho, LinearEquiv.apply_symm_apply] using this
  · simpa only [inv_inv, LinearMap.comp_apply] using inv g₀⁻¹ φ hφ
  · obtain ⟨w, rfl⟩ := e.surjective w
    have h1 := (hj _ (m g₀ φ hφ))
    refine hι.bij.2.1 (hj _ (m _ _ (schr_mem hc _ hφ))).1 (schr_mem hc _ h1.1) ?_
    simp only [LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
    rw [(hj _ (m _ _ (schr_mem hc _ hφ))).2, hh _ _ h1.1, h1.2, hh _ _ hφ, rmL_schr]
  · obtain ⟨u, rfl⟩ := d.e.surjective w
    simp only [LinearEquiv.symm_apply_apply]
    rw [← he, ← he, LinearEquiv.symm_apply_apply, coord_actB h g g₀ hg]
  · obtain ⟨u, rfl⟩ := d.e.surjective w
    simp only [LinearEquiv.symm_apply_apply]
    rw [← map_sub, show actB (cA σ) g u - u = u * (((g : GL β (AE F E)) : Matrix β β (AE F E)) - 1)ᵀ by
      rw [actB, transpose_sub, transpose_one, Matrix.mul_sub, Matrix.mul_one]]
    exact (ha.kd_transpose.kd_mul_left u).kd_map d.e.toLinearMap

end PositivityTheory.KCo

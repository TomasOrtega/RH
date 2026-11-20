import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLawsOf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

namespace UpperTheory.V.Keep

section tri

variable {k : Type} [Field k]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
private theorem tri_mul (X Y : Matrix (Fin 4) (Fin 4) k) (hX : ∀ i j, j < i → X i j = 0) (hY : ∀ i j, j < i → Y i j = 0) :
    (∀ i j, j < i → (X * Y) i j = 0) ∧ ∀ i, (X * Y) i i = X i i * Y i i := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases lt_or_ge b i with h | h
    · rw [hX i b h, zero_mul]
    · rw [hY b j (hij.trans_le h), mul_zero]
  · intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hX i b h, zero_mul]
      · rw [hY b i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
private theorem flag_of {Γ : Type} [Group Γ] (H : Subgroup Γ) (r : Γ →* GL (Fin 4) k) (a : GL (Fin 4) k)
    (h : ∀ g ∈ H, ∀ i j, j < i → (a * r g * a⁻¹ : GL (Fin 4) k) i j = 0) :
    ∃ κ : Fin 4 → ↥H →* kˣ, Af.IsFlagOn r H κ := by
  let q : Fin 4 → ↥H →* k := fun i =>
    { toFun := fun g => (a * r g * a⁻¹ : GL (Fin 4) k) i i
      map_one' := by simp
      map_mul' := fun x y => by
        have e : (a * r ((x * y : ↥H) : Γ) * a⁻¹ : GL (Fin 4) k) =
            (a * r x * a⁻¹) * (a * r y * a⁻¹) := by
          simp only [Subgroup.coe_mul, map_mul]
          group
        rw [e, Units.val_mul]
        exact (tri_mul _ _ (h x x.2) (h y y.2)).2 i }
  exact ⟨fun i => (q i).toHomUnits, a, fun s => ⟨h s s.2, fun i => rfl⟩⟩

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem tri_step {Γ : Type} [Group Γ] (hU : UpTri) (r : Γ →* GL (Fin 4) k) (a : GL (Fin 4) k) (s g : Γ)
    (d : Fin 4 → k) (hd : Function.Injective d)
    (h1 : ∀ i j, j < i → (a * r s * a⁻¹ : GL (Fin 4) k) i j = 0)
    (h1' : ∀ i j, j < i → (a * r (g * s * g⁻¹) * a⁻¹ : GL (Fin 4) k) i j = 0)
    (h2 : ∀ i, (a * r s * a⁻¹ : GL (Fin 4) k) i i ^ 2 = d i)
    (h2' : ∀ i, (a * r (g * s * g⁻¹) * a⁻¹ : GL (Fin 4) k) i i ^ 2 = d i) :
    ∀ i j, j < i → (a * r g * a⁻¹ : GL (Fin 4) k) i j = 0 := by
  set X : GL (Fin 4) k := a * r s * a⁻¹ with hX
  set Y : GL (Fin 4) k := a * r (g * s * g⁻¹) * a⁻¹ with hY
  set B : GL (Fin 4) k := a * r g * a⁻¹ with hB
  have hBX : B * (X * X) = (Y * Y) * B := by
    simp only [hX, hY, hB, map_mul, map_inv]
    group
  have t1 := tri_mul (X : Matrix (Fin 4) (Fin 4) k) X h1 h1
  have t2 := tri_mul (Y : Matrix (Fin 4) (Fin 4) k) Y h1' h1'
  refine hU k 4 ((X : Matrix (Fin 4) (Fin 4) k) * X) ((Y : Matrix (Fin 4) (Fin 4) k) * Y) B d hd t1.1 t2.1
    (fun i => by rw [t1.2, ← sq, h2]) (fun i => by rw [t2.2, ← sq, h2']) ?_
  have := congrArg (Units.val) hBX
  simpa only [Units.val_mul] using this

end tri

section gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
private theorem exists_normal (F : IntermediateField ℚ Ω) [NumberField F] (U : Subgroup (G F Ω))
    (hU : IsOpen (U : Set (G F Ω))) :
    ∃ N : Subgroup (G ℚ Ω), N.Normal ∧ IsOpen (N : Set (G ℚ Ω)) ∧ ∀ s ∈ N, ∃ u ∈ U, resQ F u = s := by
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 (hU.mem_nhds U.one_mem)
  haveI : FiniteDimensional F E := hE
  haveI : FiniteDimensional ℚ E := Module.Finite.trans F E
  let E' : IntermediateField ℚ Ω := E.restrictScalars ℚ
  haveI : FiniteDimensional ℚ E' := ‹FiniteDimensional ℚ E›
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (IntermediateField.fixingSubgroup_isOpen E') E'.fixingSubgroup.one_mem
  refine ⟨N.toSubgroup, inferInstance, N.isOpen', fun s hs => ?_⟩
  have hsE : ∀ x ∈ E, s x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff E' s).1 (hN hs) x hx
  let u : G F Ω := { s.toRingEquiv with commutes' := fun x => hsE _ (E.algebraMap_mem x) }
  refine ⟨u, hEU ?_, by ext x; rfl⟩
  exact (IntermediateField.mem_fixingSubgroup_iff E u).2 hsE

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private theorem ine_res (F : IntermediateField ℚ Ω) [NumberField F] (A : ValuationSubring Ω) (u : G F Ω)
    (h : resQ F u ∈ Ine (F := ℚ) A) : u ∈ Ine (F := F) A := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, h2⟩

end gal

end UpperTheory.V.Keep

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Keep.flagQ :
    UpperTheory.V.Keep.FlagQ := by
  intro hInf hUp Ω _ _ _ l _ c D T hD r hfl v hv A hA
  have hl : A.valuation (l : Ω) < 1 := by
    have := (hA ((l : ℕ) : 𝓞 ℚ)).2 hv
    simpa using this
  obtain ⟨κ, hκ⟩ := hfl A hl
  obtain ⟨a, ha⟩ := hκ.flag
  obtain ⟨U, hUo, hw⟩ := hκ.wts
  obtain ⟨N, hNn, hNo, hNU⟩ := UpperTheory.V.Keep.exists_normal T.F U hUo
  obtain ⟨s, ⟨hsN, hsI⟩, hso⟩ := hInf ℚ Ω l A hl N hNo
  refine UpperTheory.V.Keep.flag_of _ _ a fun g hg => ?_
  have key : ∀ t ∈ N, t ∈ Ine (F := ℚ) A → cycBar ℚ Ω l t = cycBar ℚ Ω l s →
      (∀ i j, j < i → (a * r.toHomUnits t * a⁻¹ : GL (Fin 4) (Qbar l)) i j = 0) ∧
      ∀ i, (a * r.toHomUnits t * a⁻¹ : GL (Fin 4) (Qbar l)) i i ^ 2 =
        ((cycBar ℚ Ω l s ^ (2 * (D.wts4 i : ℤ)) : (Qbar l)ˣ) : Qbar l) := by
    intro t htN htI hc
    obtain ⟨u, huU, rfl⟩ := hNU t htN
    have huI := UpperTheory.V.Keep.ine_res T.F A u htI
    have huD : u ∈ Dec (F := T.F) A := Ine_le_Dec A huI
    obtain ⟨e1, e2⟩ := ha ⟨u, huD⟩
    refine ⟨e1, fun i => ?_⟩
    have e3 := hw i ⟨u, huD⟩ ⟨huU, huI⟩
    rw [← hc]
    have e4 : (a * r.toHomUnits (resQ T.F u) * a⁻¹ : GL (Fin 4) (Qbar l)) i i = (κ i ⟨u, huD⟩ : Qbar l) := e2 i
    rw [e4, ← Units.val_pow_eq_pow_val, e3]
    rfl
  have hinj : Function.Injective fun i : Fin 4 =>
      ((cycBar ℚ Ω l s ^ (2 * (D.wts4 i : ℤ)) : (Qbar l)ˣ) : Qbar l) := by
    intro i j e
    have e2 := injective_zpow_iff_not_isOfFinOrder.2 hso (Units.val_injective e)
    have := hD.two_le
    fin_cases i <;> fin_cases j <;> simp [Raw.wts4] at e2 ⊢ <;> omega
  have ht := key s hsN hsI rfl
  have hc : cycBar ℚ Ω l (g * s * g⁻¹) = cycBar ℚ Ω l s := by
    rw [map_mul, map_mul, map_inv, mul_comm (cycBar ℚ Ω l g), mul_inv_cancel_right]
  have ht' := key (g * s * g⁻¹) (hNn.conj_mem s hsN g) (conj_mem_Ine hg hsI) hc
  exact UpperTheory.V.Keep.tri_step hUp r.toHomUnits a s g _ hinj ht.1 ht'.1 ht.2 ht'.2

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLawsOf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

namespace UpperTheory.V.Keep

section tri

variable {k : Type} [Field k]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Break down `lt_or_ge b i with h | h` into its components or cases.

Rewrite using `[hX i b h, zero_mul]`. Rewrite using `[hY b j (hij.trans_le h), mul_zero]`. Introduce `i`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `b _ hb`.

Break down `lt_or_gt_of_ne hb with h | h` into its components or cases. Rewrite using `[hX i b h, zero_mul]`. Rewrite using `[hY b i h, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
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
Set `q : Fin 4 → ↥H →* k` to `fun i => { toFun := fun g => (a * r g * a⁻¹ : GL (Fin 4) k) i i map_one' := by simp map_mul' := fun x y => by`. Establish `e : (a * r ((x * y : ↥H) : Γ) * a⁻¹ : GL (Fin 4) k) = (a * r x * a⁻¹) * (a * r y * a⁻¹)`. Simplify using `only [Subgroup.coe_mul, map_mul]`. Use `group`. Rewrite using `[e, Units.val_mul]`.

Conclude with `(tri_mul _ _ (h x x.2) (h y y.2)).2 i }`. Conclude with `⟨fun i => (q i).toHomUnits, a, fun s => ⟨h s s.2, fun i => rfl⟩⟩`.
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
Use `set X : GL (Fin 4) k := a * r s * a⁻¹ with hX`. Use `set Y : GL (Fin 4) k := a * r (g * s * g⁻¹) * a⁻¹ with hY`. Use `set B : GL (Fin 4) k := a * r g * a⁻¹ with hB`. Establish `hBX : B * (X * X) = (Y * Y) * B`. Simplify using `only [hX, hY, hB, map_mul, map_inv]`.

Use `group`. Establish `t1` using `tri_mul (X : Matrix (Fin 4) (Fin 4) k) X h1 h1`. Establish `t2` using `tri_mul (Y : Matrix (Fin 4) (Fin 4) k) Y h1' h1'`. Use `hU k 4 ((X : Matrix (Fin 4) (Fin 4) k) * X) ((Y : Matrix (Fin 4) (Fin 4) k) * Y) B d hd t1.1 t2.1 (fun i => by rw [t1.2, ← sq, h2]) (fun i => by rw [t2.2, ← sq, h2']) ?_` and prove the remaining obligations. Use `congrArg (Units.val) hBX` as an intermediate fact.

Simplify `this` using `only [Units.val_mul]`.
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
Take `⟨E, hE, hEU⟩` from `(krullTopology_mem_nhds_one_iff F Ω U).1 (hU.mem_nhds U.one_mem)`. Use `haveI : FiniteDimensional F E := hE`. Use `haveI : FiniteDimensional ℚ E := Module.Finite.trans F E`. Set `E' : IntermediateField ℚ Ω` to `E.restrictScalars ℚ`. Use `haveI : FiniteDimensional ℚ E' := ‹FiniteDimensional ℚ E›`.

Use `haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω`. Take `⟨N, hN⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (IntermediateField.fixingSubgroup_isOpen E') E'.fixingSubgroup.one_mem`. Use `⟨N.toSubgroup, inferInstance, N.isOpen', fun s hs => ?_⟩` and prove the remaining obligations. Establish `hsE : ∀ x ∈ E, s x = x` using `fun x hx => (IntermediateField.mem_fixingSubgroup_iff E' s).1 (hN hs) x hx`. Set `u : G F Ω` to `{ s.toRingEquiv with commutes' := fun x => hsE _ (E.algebraMap_mem x) }`.

Use `⟨u, hEU ?_, by ext x; rfl⟩` and prove the remaining obligations. Conclude with `(IntermediateField.mem_fixingSubgroup_iff E u).2 hsE`.
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
Take `⟨h1, h2⟩` from `h`. Conclude with `⟨h1, h2⟩`.
-/
private theorem ine_res (F : IntermediateField ℚ Ω) [NumberField F] (A : ValuationSubring Ω) (u : G F Ω)
    (h : resQ F u ∈ Ine (F := ℚ) A) : u ∈ Ine (F := F) A := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, h2⟩

end gal

end UpperTheory.V.Keep

/- English proof (translation)
Introduce `hInf hUp Ω _ _ _ l _ c D T hD r hfl v hv A hA`. Establish `hl : A.valuation (l : Ω) < 1`. Use `(hA ((l : ℕ) : 𝓞 ℚ)).2 hv` as an intermediate fact. Simplify using `using this`. Take `⟨κ, hκ⟩` from `hfl A hl`.

Take `⟨a, ha⟩` from `hκ.flag`. Take `⟨U, hUo, hw⟩` from `hκ.wts`. Take `⟨N, hNn, hNo, hNU⟩` from `UpperTheory.V.Keep.exists_normal T.F U hUo`. Take `⟨s, ⟨hsN, hsI⟩, hso⟩` from `hInf ℚ Ω l A hl N hNo`. Use `UpperTheory.V.Keep.flag_of _ _ a fun g hg => ?_` and prove the remaining obligations.

Establish `key : ∀ t ∈ N, t ∈ Ine (F` using `ℚ) A → cycBar ℚ Ω l t = cycBar ℚ Ω l s → (∀ i j, j < i → (a * r.toHomUnits t * a⁻¹ : GL (Fin 4) (Qbar l)) i j = 0) ∧ ∀ i, (a * r.toHomUnits t * a⁻¹ : GL (Fin 4) (Qbar l)) i i ^ 2 = ((cycBar ℚ Ω l s ^ (2 * (D.wts4 i : ℤ)) : (Qbar l)ˣ) : Qbar l) := by`. Introduce `t htN htI hc`. Take `⟨u, huU, rfl⟩` from `hNU t htN`. Establish `huI` using `UpperTheory.V.Keep.ine_res T.F A u htI`. Establish `huD : u ∈ Dec (F` using `T.F) A := Ine_le_Dec A huI`.

Take `⟨e1, e2⟩` from `ha ⟨u, huD⟩`. Use `⟨e1, fun i => ?_⟩` and prove the remaining obligations. Establish `e3` using `hw i ⟨u, huD⟩ ⟨huU, huI⟩`. Rewrite using `[← hc]`. Establish `e4 : (a * r.toHomUnits (resQ T.F u) * a⁻¹ : GL (Fin 4) (Qbar l)) i i = (κ i ⟨u, huD⟩ : Qbar l)` using `e2 i`.

Rewrite using `[e4, ← Units.val_pow_eq_pow_val, e3]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective fun i : Fin 4 => ((cycBar ℚ Ω l s ^ (2 * (D.wts4 i : ℤ)) : (Qbar l)ˣ) : Qbar l)`. Introduce `i j e`. Establish `e2` using `injective_zpow_iff_not_isOfFinOrder.2 hso (Units.val_injective e)`.

Use `hD.two_le` as an intermediate fact. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Raw.wts4] at e2 ⊢ <;> omega`. Establish `ht` using `key s hsN hsI rfl`. Establish `hc : cycBar ℚ Ω l (g * s * g⁻¹) = cycBar ℚ Ω l s`. Rewrite using `[map_mul, map_mul, map_inv, mul_comm (cycBar ℚ Ω l g), mul_inv_cancel_right]`.

Establish `ht'` using `key (g * s * g⁻¹) (hNn.conj_mem s hsN g) (conj_mem_Ine hg hsI) hc`. Conclude with `UpperTheory.V.Keep.tri_step hUp r.toHomUnits a s g _ hinj ht.1 ht'.1 ht.2 ht'.2`.
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

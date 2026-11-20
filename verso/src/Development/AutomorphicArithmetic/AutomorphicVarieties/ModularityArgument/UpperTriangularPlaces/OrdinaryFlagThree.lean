import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.BlockValuationRep

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.Th UpperTheory.V.Z.J
open scoped Pointwise

namespace UpperTheory.V.Z.Keep.OrdinaryFlagThree

open UpperTheory.V.U3

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[hA (show id j < id i from h), zero_mul]`. Rewrite using `[hB (show id i < id j from h), mul_zero]`.
-/
private theorem diag_mul_of_tri {k : Type} [CommRing k] (A B : Matrix (Fin 3) (Fin 3) k)
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin 3) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA (show id j < id i from h), zero_mul]
  · rw [hB (show id i < id j from h), mul_zero]

/- English proof (translation)
Set `d : Fin 3 → H →* k` to `fun i => { toFun := fun s => (T s).val i i map_one' := by simp map_mul' := fun a b => by`. Rewrite using `[map_mul, Units.val_mul]`. Conclude with `diag_mul_of_tri _ _ (tri a) (tri b) i }`. Conclude with `⟨fun i => (d i).toHomUnits, fun s i => by simp [d]⟩`.
-/
private theorem chars_of_tri {H k : Type} [Group H] [Field k] (T : H →* GL (Fin 3) k)
    (tri : ∀ s, (T s).val.BlockTriangular id) :
    ∃ κ : Fin 3 → H →* kˣ, ∀ s i, ((κ i s : kˣ) : k) = (T s).val i i := by
  let d : Fin 3 → H →* k := fun i =>
    { toFun := fun s => (T s).val i i
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, Units.val_mul]
        exact diag_mul_of_tri _ _ (tri a) (tri b) i }
  exact ⟨fun i => (d i).toHomUnits, fun s i => by simp [d]⟩

/- English proof (translation)
Establish `hc : ((b⁻¹ : GL (Fin 3) k)).val.BlockTriangular id` using `by haveI : Invertible b.val := ⟨(b⁻¹ : GL (Fin 3) k).val, Units.inv_mul b, Units.mul_inv b⟩`. Rewrite using `[Matrix.coe_units_inv]`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hb`. Establish `hd : ∀ i, ((b⁻¹ : GL (Fin 3) k)).val i i = (b.val i i)⁻¹` using `fun i => by`. Establish `h1` using `congrFun (congrFun (Units.mul_inv b) i) i`.

Rewrite `h1` using `[diag_mul_of_tri _ _ hb hc, Matrix.one_apply_eq]`. Conclude with `eq_inv_of_mul_eq_one_right h1`. Establish `he : ∀ i j, (theta b).val i j = ((b⁻¹ : GL (Fin 3) k)).val j.rev i.rev` using `fun i j => by`. Rewrite using `[theta_val]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]`.

Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `hc (show id i.rev < id j.rev from Fin.rev_lt_rev.2 hij)`. Rewrite using `[he, hd]`.
-/
private theorem theta_upper {k : Type} [Field k] (b : GL (Fin 3) k) (hb : b.val.BlockTriangular id) :
    (theta b).val.BlockTriangular id ∧ ∀ i, (theta b).val i i = (b.val i.rev i.rev)⁻¹ := by
  have hc : ((b⁻¹ : GL (Fin 3) k)).val.BlockTriangular id := by
    haveI : Invertible b.val := ⟨(b⁻¹ : GL (Fin 3) k).val, Units.inv_mul b, Units.mul_inv b⟩
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hd : ∀ i, ((b⁻¹ : GL (Fin 3) k)).val i i = (b.val i i)⁻¹ := fun i => by
    have h1 := congrFun (congrFun (Units.mul_inv b) i) i
    rw [diag_mul_of_tri _ _ hb hc, Matrix.one_apply_eq] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have he : ∀ i j, (theta b).val i j = ((b⁻¹ : GL (Fin 3) k)).val j.rev i.rev := fun i j => by
    rw [theta_val]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [he]
    exact hc (show id i.rev < id j.rev from Fin.rev_lt_rev.2 hij)
  · rw [he, hd]

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> simp [wt1, Fin.rev]`.
-/
private theorem weight_rev_eq_neg (i : Fin 3) : wt1 i.rev = - wt1 i := by
  fin_cases i <;> simp [wt1, Fin.rev]

/- English proof (translation)
Simplify using `[SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_one]`.
-/
private theorem left_conj_pos {k : Type} [CommRing k] (x y : GG 3 k) (h1 : x.right = 1) (h2 : y.right = 1) :
    (x * y * x⁻¹).left = x.left * y.left * x.left⁻¹ := by
  simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_one]

/- English proof (translation)
Simplify using `[SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_neg_one, sgnAct_one, theta_theta]`.
-/
private theorem left_conj_neg {k : Type} [CommRing k] (x y : GG 3 k) (h1 : x.right = -1) (h2 : y.right = 1) :
    (x * y * x⁻¹).left = x.left * theta y.left * x.left⁻¹ := by
  simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, h1, h2, sgnAct_neg_one, sgnAct_one, theta_theta]

/- English proof (translation)
Simplify using `[conjBy, hs]`.
-/
private theorem conj_left {D A : Type} [Group D] [CommRing A] (h : GL (Fin 3) A) (r : D →* GG 3 A) (s : D)
    (hs : (r s).right = 1) : (conjBy h⁻¹ r s).left = h⁻¹ * (r s).left * h := by
  simp [conjBy, hs]

/- English proof (translation)
Establish `hY : ∀ s, (R (t⁻¹ * ι s * t)).right = 1` using `fun s => by`. Establish `e : ∀ x, (R x).right = (GG.nu (R x))` using `fun _ => rfl`. Rewrite using `[e, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, ← e (ι s), hK]`. Simplify using the standard rewrite rules. Establish `hc : ∀ s, R (ι s) = R t * R (t⁻¹ * ι s * t) * (R t)⁻¹` using `fun s => by`.

Rewrite using `[← map_inv, ← map_mul, ← map_mul]`. Use `congr 1`. Use `group`. It suffices to establish `hs : ∃ P : GL (Fin 3) k, ∃ f : GL (Fin 3) k →* GL (Fin 3) k, (∀ s, P * ρ s * P⁻¹ = f (b * (R (t⁻¹ * ι s * t)).left * b⁻¹)) ∧ (∀ x : GL (Fin 3) k, x.val.BlockTriangular id → (f x).val.BlockTriangular id) ∧ (∀ x : GL (Fin 3) k, x.val.BlockTriangular id → ∀ y : kˣ, (∀ i, x.val i i = …`. Take `⟨P, f, h1, h2, h3⟩` from `hs`.

Set `T : ↥H →* GL (Fin 3) k` to `(MulAut.conj P).toMonoidHom.comp (ρ.comp H.subtype)`. Establish `hT : ∀ s : ↥H, T s = f (b * (R (t⁻¹ * ι s * t)).left * b⁻¹)` using `fun s => h1 s`. Take `⟨κ, hκ⟩` from `chars_of_tri T fun s => by`. Rewrite using `[hT]`. Conclude with `h2 _ (tri s s.2)`.

Use `⟨κ, ⟨P, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩, fun i s hs => Units.ext ?_⟩` and prove the remaining obligations. Establish `: (T s).val.BlockTriangular id`. Rewrite using `[hT]`. Conclude with `h2 _ (tri s s.2)`. Conclude with `this hij`.

Conclude with `(hκ s i).symm`. Rewrite using `[hκ, hT]`. Conclude with `h3 _ (tri s s.2) _ (ine s s.2 hs) i`. Break down `Int.units_eq_one_or (R t).right with ht | ht` into its components or cases. Use `⟨b * (R t).left⁻¹, MonoidHom.id _, fun s => ?_, fun x h => h, fun x _ y h => h⟩` and prove the remaining obligations.

Establish `e1 : ρ s = (R t).left * (R (t⁻¹ * ι s * t)).left * (R t).left⁻¹` using `(hρ s).trans ((congrArg (·.left) (hc s)).trans (left_conj_pos _ _ ht (hY s)))`. Rewrite using `[e1, MonoidHom.id_apply]`. Use `group`. Use `⟨theta b * (R t).left⁻¹, thetaAut 3 k, fun s => ?_, fun x h => (theta_upper x h).1, fun x hx y h i => ?_⟩` and prove the remaining obligations. Establish `e1 : ρ s = (R t).left * theta (R (t⁻¹ * ι s * t)).left * (R t).left⁻¹` using `(hρ s).trans ((congrArg (·.left) (hc s)).trans (left_conj_neg _ _ ht (hY s)))`.

Establish `e2 : ∀ x y : GL (Fin 3) k, theta (x * y * x⁻¹) = theta x * theta y * (theta x)⁻¹` using `fun x y => by`. Establish `e : ∀ x : GL (Fin 3) k, theta x = thetaAut 3 k x` using `fun _ => rfl`. Simplify using `only [e, map_mul, map_inv]`. Use `show _ = theta (b * (R (t⁻¹ * ι s * t)).left * b⁻¹)`. Rewrite using `[e1, e2]`.

Use `group`. Use `show (theta x).val i i = _`. Rewrite using `[(theta_upper x hx).2, h, weight_rev_eq_neg]`. Simplify using the standard rewrite rules.
-/
private theorem flag_core {Γ Δ k : Type} [Group Γ] [Group Δ] [Field k] (R : Γ →* GG 3 k) (ι : Δ →* Γ)
    (ρ : Δ →* GL (Fin 3) k) (hρ : ∀ s, ρ s = (R (ι s)).left) (hK : ∀ s, (R (ι s)).right = 1)
    (H : Subgroup Δ) (I : Set Δ) (t : Γ) (b : GL (Fin 3) k) (c : Δ →* kˣ)
    (tri : ∀ s ∈ H, (b * (R (t⁻¹ * ι s * t)).left * b⁻¹ : GL (Fin 3) k).val.BlockTriangular id)
    (ine : ∀ s ∈ H, s ∈ I → ∀ i, (b * (R (t⁻¹ * ι s * t)).left * b⁻¹ : GL (Fin 3) k).val i i = ((c s ^ wt1 i : kˣ) : k)) :
    ∃ κ : Fin 3 → ↥H →* kˣ, Af.IsFlagOn ρ H κ ∧ ∀ i (s : ↥H), (s : Δ) ∈ I → κ i s = c s ^ wt1 i := by
  have hY : ∀ s, (R (t⁻¹ * ι s * t)).right = 1 := fun s => by
    have e : ∀ x, (R x).right = (GG.nu (R x)) := fun _ => rfl
    rw [e, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, ← e (ι s), hK]
    simp
  have hc : ∀ s, R (ι s) = R t * R (t⁻¹ * ι s * t) * (R t)⁻¹ := fun s => by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group

  suffices hs : ∃ P : GL (Fin 3) k, ∃ f : GL (Fin 3) k →* GL (Fin 3) k,
      (∀ s, P * ρ s * P⁻¹ = f (b * (R (t⁻¹ * ι s * t)).left * b⁻¹)) ∧
      (∀ x : GL (Fin 3) k, x.val.BlockTriangular id → (f x).val.BlockTriangular id) ∧
      (∀ x : GL (Fin 3) k, x.val.BlockTriangular id → ∀ y : kˣ, (∀ i, x.val i i = ((y ^ wt1 i : kˣ) : k)) →
        ∀ i, (f x).val i i = ((y ^ wt1 i : kˣ) : k)) by
    obtain ⟨P, f, h1, h2, h3⟩ := hs
    let T : ↥H →* GL (Fin 3) k := (MulAut.conj P).toMonoidHom.comp (ρ.comp H.subtype)
    have hT : ∀ s : ↥H, T s = f (b * (R (t⁻¹ * ι s * t)).left * b⁻¹) := fun s => h1 s
    obtain ⟨κ, hκ⟩ := chars_of_tri T fun s => by
      rw [hT]
      exact h2 _ (tri s s.2)
    refine ⟨κ, ⟨P, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩, fun i s hs => Units.ext ?_⟩
    · have : (T s).val.BlockTriangular id := by
        rw [hT]
        exact h2 _ (tri s s.2)
      exact this hij
    · exact (hκ s i).symm
    · rw [hκ, hT]
      exact h3 _ (tri s s.2) _ (ine s s.2 hs) i
  rcases Int.units_eq_one_or (R t).right with ht | ht
  · refine ⟨b * (R t).left⁻¹, MonoidHom.id _, fun s => ?_, fun x h => h, fun x _ y h => h⟩
    have e1 : ρ s = (R t).left * (R (t⁻¹ * ι s * t)).left * (R t).left⁻¹ :=
      (hρ s).trans ((congrArg (·.left) (hc s)).trans (left_conj_pos _ _ ht (hY s)))
    rw [e1, MonoidHom.id_apply]
    group
  · refine ⟨theta b * (R t).left⁻¹, thetaAut 3 k, fun s => ?_, fun x h => (theta_upper x h).1, fun x hx y h i => ?_⟩
    · have e1 : ρ s = (R t).left * theta (R (t⁻¹ * ι s * t)).left * (R t).left⁻¹ :=
        (hρ s).trans ((congrArg (·.left) (hc s)).trans (left_conj_neg _ _ ht (hY s)))
      have e2 : ∀ x y : GL (Fin 3) k, theta (x * y * x⁻¹) = theta x * theta y * (theta x)⁻¹ := fun x y => by
        have e : ∀ x : GL (Fin 3) k, theta x = thetaAut 3 k x := fun _ => rfl
        simp only [e, map_mul, map_inv]
      show _ = theta (b * (R (t⁻¹ * ι s * t)).left * b⁻¹)
      rw [e1, e2]
      group
    · show (theta x).val i i = _
      rw [(theta_upper x hx).2, h, weight_rev_eq_neg]
      simp

end UpperTheory.V.Z.Keep.OrdinaryFlagThree

namespace UpperTheory.V.Z.Keep.OrdinaryFlagThree

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω N`. Establish `h1` using `Chr.cls_spec N (galEmb ℚ K Ω s) ζ hζ.pow_eq_one`. Rewrite `h1` using `[galEmb_apply, h ζ hζ.pow_eq_one]`.

Use `nth_rewrite 1 [← pow_one ζ] at h1`. Establish `h2 : (1 : ℕ) ≡ ((Chr.cls ℚ Ω N (galEmb ℚ K Ω s) : (ZMod N)ˣ) : ZMod N).val [MOD N]`. Take `⟨z, rfl⟩` from `hζ.isUnit (NeZero.ne N)`. Establish `hz : IsPrimitiveRoot z N` using `IsPrimitiveRoot.coe_units_iff.1 hζ`. Establish `h0 : z ^ 1 = z ^ ((Chr.cls ℚ Ω N (galEmb ℚ K Ω s) : (ZMod N)ˣ) : ZMod N).val` using `Units.ext (by simpa using h1)`.

Establish `h4` using `(pow_eq_pow_iff_modEq).1 h0`. Rewrite `h4` using `[← hz.eq_orderOf]`. Then use the resulting hypothesis. Apply `Units.ext` to reduce the goal to its premises. Establish `h3` using `(ZMod.natCast_eq_natCast_iff _ _ _).2 h2`. Rewrite `h3` using `[ZMod.natCast_zmod_val]`.

Simplify using `using h3.symm`.
-/
private theorem cls_of_fix {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [NumberField K] [Algebra K Ω] (N : ℕ) [NeZero N]
    (s : G K Ω) (h : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) : Chr.cls ℚ Ω N (galEmb ℚ K Ω s) = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have h1 := Chr.cls_spec N (galEmb ℚ K Ω s) ζ hζ.pow_eq_one
  rw [galEmb_apply, h ζ hζ.pow_eq_one] at h1
  nth_rewrite 1 [← pow_one ζ] at h1
  have h2 : (1 : ℕ) ≡ ((Chr.cls ℚ Ω N (galEmb ℚ K Ω s) : (ZMod N)ˣ) : ZMod N).val [MOD N] := by
    obtain ⟨z, rfl⟩ := hζ.isUnit (NeZero.ne N)
    have hz : IsPrimitiveRoot z N := IsPrimitiveRoot.coe_units_iff.1 hζ
    have h0 : z ^ 1 = z ^ ((Chr.cls ℚ Ω N (galEmb ℚ K Ω s) : (ZMod N)ˣ) : ZMod N).val := Units.ext (by simpa using h1)
    have h4 := (pow_eq_pow_iff_modEq).1 h0
    rwa [← hz.eq_orderOf] at h4
  apply Units.ext
  have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
  rw [ZMod.natCast_zmod_val] at h3
  simpa using h3.symm

end UpperTheory.V.Z.Keep.OrdinaryFlagThree

/- English proof (translation)
Introduce `Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ C₀ k hok A _ _ r hr K _ _ _ _ _ hker ρ hρ w hw`. Take `⟨P, hP⟩` from `ReciprocityTheory.Gal.exists_isPlaceOver Ω w`. Use `⟨P, hP, ?_⟩` and prove the remaining obligations. Establish `hPl : P.valuation (l : Ω) < 1`. Use `hP ((l : ℕ) : 𝓞 K)` as an intermediate fact.

Simplify using `only [map_natCast] at this`. Conclude with `this.2 hw`. Take `⟨v, u, -, hPv⟩` from `(k.pl_all P hPl).exists`. Take `⟨γ, -, hpl⟩` from `k.pl_conj v`. Establish `hPt : P = (u * γ) • B` using `by rw [hPv, hpl, mul_smul]`.

Generalize the expression as in `u * γ = t at hPt`. Establish `hA : ∀ x, t.toRingEquiv x ∈ P ↔ x ∈ B` using `fun x => by`. Rewrite using `[hPt]`. Conclude with `ValuationSubring.smul_mem_pointwise_smul_iff (g := t)`. Establish `hL : IsLift (RingEquiv.refl ℚ) t.toRingEquiv` using `fun x => t.commutes x`.

Establish `hcg : ∀ g : G ℚ Ω, conjGal hL g = t⁻¹ * g * t` using `fun _ => rfl`. Establish `hmem : ∀ s : G K Ω, η (galEmb ℚ K Ω s) = 1` using `fun s => by`. Establish `: galEmb ℚ K Ω s ∈ η.ker` using `hker ▸ galEmb_mem ℚ K Ω s`. Conclude with `this`. Establish `hright : ∀ g, (UnitaryThreeInertia.push A.val r g).right = η g` using `hr.red.mult`.

Establish `hη : ∀ s, η (t⁻¹ * galEmb ℚ K Ω s * t) = 1` using `fun s => by`. Rewrite using `[map_mul, map_mul, map_inv, hmem, mul_one, inv_mul_cancel]`. Establish `hdec : ∀ s ∈ Dec (F` using `K) P, t⁻¹ * galEmb ℚ K Ω s * t ∈ Dec (F := ℚ) B := fun s hs => hcg _ ▸ conjGal_mem_Dec hL hA (show galEmb ℚ K Ω s ∈ Dec (F := ℚ) P from hs)`. Establish `hine : ∀ s ∈ Ine (F` using `K) P, t⁻¹ * galEmb ℚ K Ω s * t ∈ Ine (F := ℚ) B := fun s hs => hcg _ ▸ conjGal_mem_Ine hL hA (show galEmb ℚ K Ω s ∈ Ine (F := ℚ) P from hs)`. Take `⟨h, -, tri, ine⟩` from `hr.ord`.

Set `f : A →+* Qbar l` to `(A.val : A →+* PadicAlgCl l)`. Set `h' : GL (Fin 3) (Qbar l)` to `Matrix.GeneralLinearGroup.map f h`. Set `a : (c.O)ˣ →* (Qbar l)ˣ` to `Units.map (algebraMap c.O (Qbar l)).toMonoidHom`. Set `d : G K Ω →* (Qbar l)ˣ` to `a.comp ((Chr.dirG ℚ Ω ψ).comp (galEmb ℚ K Ω))`. Set `cc : G K Ω →* (Qbar l)ˣ` to `a.comp ((Chr.Psi l e (Chr.dirG ℚ Ω ψ)).comp (galEmb ℚ K Ω))`.

Establish `hent : ∀ s (hs : s ∈ Dec (F` using `K) P) i j, (h'⁻¹ * (UnitaryThreeInertia.push A.val r (t⁻¹ * galEmb ℚ K Ω s * t)).left * h'⁻¹⁻¹ : GL (Fin 3) (Qbar l)).val i j = f ((conjBy h⁻¹ (r.comp (Dec (F := ℚ) B).subtype) ⟨_, hdec s hs⟩).mat i j) := fun s hs i j => by`. Establish `e1 : (r (t⁻¹ * galEmb ℚ K Ω s * t)).right = 1` using `(hr.red.mult _).trans (hη s)`. Establish `e2` using `OrdinaryFlagThree.conj_left h (r.comp (Dec (F := ℚ) B).subtype) ⟨_, hdec s hs⟩ e1`. Establish `e3 : (UnitaryThreeInertia.push A.val r (t⁻¹ * galEmb ℚ K Ω s * t)).left = Matrix.GeneralLinearGroup.map f (r (t⁻¹ * galEmb ℚ K Ω s * t)).left` using `rfl`. Rewrite using `[GG.mat, e2, e3, inv_inv]`.

Establish `e4 : h'⁻¹ * Matrix.GeneralLinearGroup.map f (r (t⁻¹ * galEmb ℚ K Ω s * t)).left * h' = Matrix.GeneralLinearGroup.map f (h⁻¹ * (r (t⁻¹ * galEmb ℚ K Ω s * t)).left * h)`. Simplify using `only [h', map_mul, map_inv]`. Rewrite using `[e4]`. Both sides reduce to the same expression. Take `⟨κ, hf, hκ⟩` from `OrdinaryFlagThree.flag_core (UnitaryThreeInertia.push A.val r) (galEmb ℚ K Ω) ρ (fun s => Units.ext (hρ s)) (fun s => (hright _).trans (hmem s)) (Dec (F := K) P) (Ine (F := K) P : Set (G K Ω)) t h'⁻¹ cc (fun s hs i j hij => by`.

Rewrite using `[hent s hs]`. Establish `hij' : (j : ℕ) < i` using `hij`. Rewrite using `[tri ⟨_, hdec s hs⟩ (hη s) i j (by simp only [wt, wt1]; omega), map_zero])`. Use the proof step `(fun s hs hi i => by`. Rewrite using `[hent s hs]`.

Use `ine ⟨_, hdec s hs⟩ (Subgroup.mem_subgroupOf.2 (hine s hi)) (hη s) i` as an intermediate fact. Rewrite using `[this]`. Establish `hx : Chr.Psi l e (Chr.dirG ℚ Ω ψ) (t⁻¹ * galEmb ℚ K Ω s * t) = Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω s)`. Rewrite using `[map_mul, map_mul, map_inv, mul_comm _ (Chr.Psi l e (Chr.dirG ℚ Ω ψ) t), mul_inv_cancel_left]`. Establish `e1 : cc s ^ wt1 i = a (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (t⁻¹ * galEmb ℚ K Ω s * t) ^ wt1 i)`.

Rewrite using `[hx, map_zpow]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Conclude with `A.val.commutes _)`. Apply the tactic sequence `have hm : ∀ i : Fin 3, ![(e : ℤ), 0, -(e : ℤ)] i = (e : ℤ) * wt1 i := fun i => by fin_cases i <;> simp [wt1]`.

Establish `hcc : ∀ s, cc s = cycBar K Ω l s ^ (e : ℤ) * d s` using `fun s => by`. Establish `e1 : a (chiO ℚ Ω l c.O (galEmb ℚ K Ω s)) = cycBar K Ω l s` using `Units.ext rfl`. Use `show a (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω s)) = _`. Rewrite using `[Chr.Psi, MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply, map_zpow, e1]`. Both sides reduce to the same expression.

Use `⟨κ, fun i => d ^ wt1 i, fun i s hs => ?_, hf, fun i s hs => ?_⟩` and prove the remaining obligations. Establish `hd : d s = 1`. Simplify using `[d, Chr.dirG, OrdinaryFlagThree.cls_of_fix N s hs]`. Rewrite using `[MonoidHom.zpow_apply, hd, one_zpow]`. Rewrite using `[hκ i s hs, hcc, mul_zpow, ← zpow_mul, hm, MonoidHom.zpow_apply]`.
-/
theorem UpperTheory.V.Z.Keep.ordFlag3 :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ) (k : Pr.GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A), Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω], η.ker = galOf ℚ K Ω → ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), (∀ s, (ρ s).val = (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).mat) → ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → ∃ A' : ValuationSubring Ω, IsPlaceOver A' w ∧ ∃ κ, Af.FlagAt N ![(e : ℤ), 0, -(e : ℤ)] ρ A' κ := by
  intro Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ C₀ k hok A _ _ r hr K _ _ _ _ _ hker ρ hρ w hw
  obtain ⟨P, hP⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
  refine ⟨P, hP, ?_⟩
  have hPl : P.valuation (l : Ω) < 1 := by
    have := hP ((l : ℕ) : 𝓞 K)
    simp only [map_natCast] at this
    exact this.2 hw
  obtain ⟨v, u, -, hPv⟩ := (k.pl_all P hPl).exists
  obtain ⟨γ, -, hpl⟩ := k.pl_conj v
  have hPt : P = (u * γ) • B := by rw [hPv, hpl, mul_smul]
  generalize u * γ = t at hPt
  have hA : ∀ x, t.toRingEquiv x ∈ P ↔ x ∈ B := fun x => by
    rw [hPt]
    exact ValuationSubring.smul_mem_pointwise_smul_iff (g := t)
  have hL : IsLift (RingEquiv.refl ℚ) t.toRingEquiv := fun x => t.commutes x
  have hcg : ∀ g : G ℚ Ω, conjGal hL g = t⁻¹ * g * t := fun _ => rfl
  have hmem : ∀ s : G K Ω, η (galEmb ℚ K Ω s) = 1 := fun s => by
    have : galEmb ℚ K Ω s ∈ η.ker := hker ▸ galEmb_mem ℚ K Ω s
    exact this
  have hright : ∀ g, (UnitaryThreeInertia.push A.val r g).right = η g := hr.red.mult
  have hη : ∀ s, η (t⁻¹ * galEmb ℚ K Ω s * t) = 1 := fun s => by
    rw [map_mul, map_mul, map_inv, hmem, mul_one, inv_mul_cancel]
  have hdec : ∀ s ∈ Dec (F := K) P, t⁻¹ * galEmb ℚ K Ω s * t ∈ Dec (F := ℚ) B := fun s hs =>
    hcg _ ▸ conjGal_mem_Dec hL hA (show galEmb ℚ K Ω s ∈ Dec (F := ℚ) P from hs)
  have hine : ∀ s ∈ Ine (F := K) P, t⁻¹ * galEmb ℚ K Ω s * t ∈ Ine (F := ℚ) B := fun s hs =>
    hcg _ ▸ conjGal_mem_Ine hL hA (show galEmb ℚ K Ω s ∈ Ine (F := ℚ) P from hs)
  obtain ⟨h, -, tri, ine⟩ := hr.ord
  let f : A →+* Qbar l := (A.val : A →+* PadicAlgCl l)
  let h' : GL (Fin 3) (Qbar l) := Matrix.GeneralLinearGroup.map f h
  let a : (c.O)ˣ →* (Qbar l)ˣ := Units.map (algebraMap c.O (Qbar l)).toMonoidHom
  let d : G K Ω →* (Qbar l)ˣ := a.comp ((Chr.dirG ℚ Ω ψ).comp (galEmb ℚ K Ω))
  let cc : G K Ω →* (Qbar l)ˣ := a.comp ((Chr.Psi l e (Chr.dirG ℚ Ω ψ)).comp (galEmb ℚ K Ω))
  have hent : ∀ s (hs : s ∈ Dec (F := K) P) i j,
      (h'⁻¹ * (UnitaryThreeInertia.push A.val r (t⁻¹ * galEmb ℚ K Ω s * t)).left * h'⁻¹⁻¹ : GL (Fin 3) (Qbar l)).val i j =
        f ((conjBy h⁻¹ (r.comp (Dec (F := ℚ) B).subtype) ⟨_, hdec s hs⟩).mat i j) := fun s hs i j => by
    have e1 : (r (t⁻¹ * galEmb ℚ K Ω s * t)).right = 1 := (hr.red.mult _).trans (hη s)
    have e2 := OrdinaryFlagThree.conj_left h (r.comp (Dec (F := ℚ) B).subtype) ⟨_, hdec s hs⟩ e1
    have e3 : (UnitaryThreeInertia.push A.val r (t⁻¹ * galEmb ℚ K Ω s * t)).left =
      Matrix.GeneralLinearGroup.map f (r (t⁻¹ * galEmb ℚ K Ω s * t)).left := rfl
    rw [GG.mat, e2, e3, inv_inv]
    have e4 : h'⁻¹ * Matrix.GeneralLinearGroup.map f (r (t⁻¹ * galEmb ℚ K Ω s * t)).left * h' =
      Matrix.GeneralLinearGroup.map f (h⁻¹ * (r (t⁻¹ * galEmb ℚ K Ω s * t)).left * h) := by
      simp only [h', map_mul, map_inv]
    rw [e4]
    rfl
  obtain ⟨κ, hf, hκ⟩ := OrdinaryFlagThree.flag_core (UnitaryThreeInertia.push A.val r) (galEmb ℚ K Ω) ρ (fun s => Units.ext (hρ s))
    (fun s => (hright _).trans (hmem s)) (Dec (F := K) P) (Ine (F := K) P : Set (G K Ω)) t h'⁻¹ cc
    (fun s hs i j hij => by
      rw [hent s hs]
      have hij' : (j : ℕ) < i := hij
      rw [tri ⟨_, hdec s hs⟩ (hη s) i j (by simp only [wt, wt1]; omega), map_zero])
    (fun s hs hi i => by
      rw [hent s hs]
      have := ine ⟨_, hdec s hs⟩ (Subgroup.mem_subgroupOf.2 (hine s hi)) (hη s) i
      rw [this]
      have hx : Chr.Psi l e (Chr.dirG ℚ Ω ψ) (t⁻¹ * galEmb ℚ K Ω s * t) = Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω s) := by
        rw [map_mul, map_mul, map_inv, mul_comm _ (Chr.Psi l e (Chr.dirG ℚ Ω ψ) t), mul_inv_cancel_left]
      have e1 : cc s ^ wt1 i = a (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (t⁻¹ * galEmb ℚ K Ω s * t) ^ wt1 i) := by
        rw [hx, map_zpow]
        rfl
      rw [e1]
      exact A.val.commutes _)
  have hm : ∀ i : Fin 3, ![(e : ℤ), 0, -(e : ℤ)] i = (e : ℤ) * wt1 i := fun i => by
    fin_cases i <;> simp [wt1]
  have hcc : ∀ s, cc s = cycBar K Ω l s ^ (e : ℤ) * d s := fun s => by
    have e1 : a (chiO ℚ Ω l c.O (galEmb ℚ K Ω s)) = cycBar K Ω l s := Units.ext rfl
    show a (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω s)) = _
    rw [Chr.Psi, MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply, map_zpow, e1]
    rfl
  refine ⟨κ, fun i => d ^ wt1 i, fun i s hs => ?_, hf, fun i s hs => ?_⟩
  · have hd : d s = 1 := by
      simp [d, Chr.dirG, OrdinaryFlagThree.cls_of_fix N s hs]
    rw [MonoidHom.zpow_apply, hd, one_zpow]
  · rw [hκ i s hs, hcc, mul_zpow, ← zpow_mul, hm, MonoidHom.zpow_apply]

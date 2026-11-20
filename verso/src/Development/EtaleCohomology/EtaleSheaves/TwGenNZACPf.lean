import Development.EtaleCohomology.EtaleSheaves.LCBijPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.TwGenNZACPf

section Field
variable {q : ℕ} [NeZero q] {L : Type} [Field L]

/- English proof (translation)
Establish `: NeZero (q : L)` using `⟨z.2.1.ne_zero⟩`. Establish `h` using `z.2.2`. Rewrite `h` using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `Polynomial.isRoot_cyclotomic_iff.1 h`.
-/
theorem prim_isPrimitiveRoot (z : Prim q L) : IsPrimitiveRoot z.1 q := by
  have : NeZero (q : L) := ⟨z.2.1.ne_zero⟩
  have h := z.2.2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] at h
  exact Polynomial.isRoot_cyclotomic_iff.1 h

open Classical in

def lg (q : ℕ) (z x : L) : ZMod q := if h : ∃ n : ℕ, z ^ n = x then (h.choose : ZMod q) else 0

/- English proof (translation)
Establish `h : ∃ m : ℕ, z ^ m = z ^ n` using `⟨n, rfl⟩`. Unfold `lg`. Rewrite using `[dif_pos h, ZMod.natCast_eq_natCast_iff]`. Establish `h2` using `h.choose_spec`. Establish `h3` using `((hz.isOfFinOrder (NeZero.ne q)).pow_eq_pow_iff_modEq).1 h2`.

Rewrite `h3` using `[← hz.eq_orderOf]`. Then use the resulting hypothesis.
-/
theorem lg_pow {z : L} (hz : IsPrimitiveRoot z q) (n : ℕ) : lg q z (z ^ n) = n := by
  have h : ∃ m : ℕ, z ^ m = z ^ n := ⟨n, rfl⟩
  unfold lg
  rw [dif_pos h, ZMod.natCast_eq_natCast_iff]
  have h2 := h.choose_spec
  have h3 := ((hz.isOfFinOrder (NeZero.ne q)).pow_eq_pow_iff_modEq).1 h2
  rwa [← hz.eq_orderOf] at h3

open Classical in

def fv (q : ℕ) (i : ℤ) (z x : L) : ZMod q :=
  if h : IsUnit (lg q z x) then ((h.unit ^ i : (ZMod q)ˣ) : ZMod q) else 0

/- English proof (translation)
Establish `hz` using `prim_isPrimitiveRoot z`. Take `⟨m, -, hm⟩` from `hz.eq_pow_of_pow_eq_one (prim_isPrimitiveRoot ζ).pow_eq_one`. Establish `hl : lg q z.1 ξ.1 = lg q z.1 ζ.1 * a`. Rewrite using `[h, ← hm, ← pow_mul, lg_pow hz, lg_pow hz]`. Use `push_cast`.

Rewrite using `[ZMod.natCast_zmod_val]`. Unfold `fv`. Distinguish the cases in `hu : IsUnit (lg q z.1 ζ.1)`. Establish `hu' : IsUnit (lg q z.1 ξ.1)` using `hl ▸ hu.mul a.isUnit`. Rewrite using `[dif_pos hu, dif_pos hu']`.

Establish `: hu'.unit = hu.unit * a` using `Units.ext (by simp [hl])`. Rewrite using `[this, mul_zpow, Units.val_mul, mul_comm]`. Establish `hu' : ¬ IsUnit (lg q z.1 ξ.1)`. Rewrite using `[hl]`. Conclude with `fun h' => hu ((Units.isUnit_mul_units _ a).1 h')`.

Rewrite using `[dif_neg hu, dif_neg hu', mul_zero]`.
-/
theorem fv_rel (i : ℤ) (z : Prim q L) (ζ ξ : Prim q L) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    fv q i z.1 ξ.1 = ((a ^ i : (ZMod q)ˣ) : ZMod q) * fv q i z.1 ζ.1 := by
  have hz := prim_isPrimitiveRoot z
  obtain ⟨m, -, hm⟩ := hz.eq_pow_of_pow_eq_one (prim_isPrimitiveRoot ζ).pow_eq_one
  have hl : lg q z.1 ξ.1 = lg q z.1 ζ.1 * a := by
    rw [h, ← hm, ← pow_mul, lg_pow hz, lg_pow hz]
    push_cast
    rw [ZMod.natCast_zmod_val]
  unfold fv
  by_cases hu : IsUnit (lg q z.1 ζ.1)
  · have hu' : IsUnit (lg q z.1 ξ.1) := hl ▸ hu.mul a.isUnit
    rw [dif_pos hu, dif_pos hu']
    have : hu'.unit = hu.unit * a := Units.ext (by simp [hl])
    rw [this, mul_zpow, Units.val_mul, mul_comm]
  · have hu' : ¬ IsUnit (lg q z.1 ξ.1) := by
      rw [hl]; exact fun h' => hu ((Units.isUnit_mul_units _ a).1 h')
    rw [dif_neg hu, dif_neg hu', mul_zero]

/- English proof (translation)
Establish `hl : lg q z.1 z.1 = 1`. Use `lg_pow (prim_isPrimitiveRoot z) 1` as an intermediate fact. Rewrite `this` using `[pow_one]`. Rewrite using `[this, Nat.cast_one]`. Unfold `fv`.

Establish `hu : IsUnit (lg q z.1 z.1)` using `hl ▸ isUnit_one`. Rewrite using `[dif_pos hu]`. Establish `: hu.unit = 1` using `Units.ext (by simp [hl])`. Rewrite using `[this, one_zpow, Units.val_one]`.
-/
theorem fv_self (i : ℤ) (z : Prim q L) : fv q i z.1 z.1 = 1 := by
  have hl : lg q z.1 z.1 = 1 := by
    have := lg_pow (prim_isPrimitiveRoot z) 1
    rw [pow_one] at this
    rw [this, Nat.cast_one]
  unfold fv
  have hu : IsUnit (lg q z.1 z.1) := hl ▸ isUnit_one
  rw [dif_pos hu]
  have : hu.unit = 1 := Units.ext (by simp [hl])
  rw [this, one_zpow, Units.val_one]

def lin (i : ℤ) (z : L) : (Prim q L →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun ξ : Prim q L => ULift.up (fv q i z ξ.1))

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨ζ, ξ, a, h, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, lin, Finsupp.linearCombination_single]`. Rewrite using `[sub_eq_zero]`. Apply `ULift.ext` to reduce the goal to its premises.

Simplify using `[fv_rel i z ζ ξ a h]`.
-/
theorem lin_rel (i : ℤ) (z : Prim q L) : twRel q i L ≤ LinearMap.ker (lin i z.1) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, lin, Finsupp.linearCombination_single]
  rw [sub_eq_zero]
  apply ULift.ext
  simp [fv_rel i z ζ ξ a h]

/- English proof (translation)
Establish `h2` using `congrArg ((twRel q i L).liftQ (lin i z.1) (lin_rel i z)) h`. Rewrite `h2` using `[map_nsmul, Submodule.liftQ_apply, map_zero, lin, Finsupp.linearCombination_single, fv_self]`. Rewrite `h2` using `[one_smul]`. Establish `h3` using `congrArg AddEquiv.ulift h2`. Rewrite `h3` using `[map_nsmul, map_zero]`.

Express the relevant statement in the definitionally equal form `c.val • (1 : ZMod q) = 0 at h3`. Rewrite `h3` using `[nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]`. Then use the resulting hypothesis.
-/
theorem field_nz (i : ℤ) (z : Prim q L) (c : ZMod q)
    (h : c.val • (Submodule.Quotient.mk (Finsupp.single z 1) : (Prim q L →₀ ULift.{1} (ZMod q)) ⧸ twRel q i L) = 0) :
    c = 0 := by
  have h2 := congrArg ((twRel q i L).liftQ (lin i z.1) (lin_rel i z)) h
  rw [map_nsmul, Submodule.liftQ_apply, map_zero, lin, Finsupp.linearCombination_single, fv_self] at h2
  rw [one_smul] at h2
  have h3 := congrArg AddEquiv.ulift h2
  rw [map_nsmul, map_zero] at h3
  change c.val • (1 : ZMod q) = 0 at h3
  rwa [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] at h3

end Field

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal A`. Set `_` to `Ideal.Quotient.field M`. Apply `field_nz i (ζ.map (Ideal.Quotient.mk M)) c` to reduce the goal to its premises. Establish `h2` using `congrArg (Submodule.mapQ _ _ (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)) (Prim.map (Ideal.Quotient.mk M))) (twRel_le q i (Ideal.Quotient.mk M))) h`. Rewrite `h2` using `[map_nsmul, map_zero, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]`.

Conclude with `h2`.
-/
theorem ring_nz {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (c : ZMod q)
    (h : c.val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = 0) :
    c = 0 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ := Ideal.Quotient.field M
  apply field_nz i (ζ.map (Ideal.Quotient.mk M)) c
  have h2 := congrArg (Submodule.mapQ _ _ (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
    (Prim.map (Ideal.Quotient.mk M))) (twRel_le q i (Ideal.Quotient.mk M))) h
  rw [map_nsmul, map_zero, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at h2
  exact h2

/- English proof (translation)
Take `⟨y⟩` from `‹Nonempty V›`. Conclude with `RingHom.domain_nontrivial (V.presheaf.germ ⊤ y trivial).hom`.
-/
theorem gamma_nontrivial (V : Scheme.{0}) [Nonempty V] : Nontrivial Γ(V, ⊤) := by
  obtain ⟨y⟩ := ‹Nonempty V›
  exact RingHom.domain_nontrivial (V.presheaf.germ ⊤ y trivial).hom

/- English proof (translation)
Introduce `q _ i K _ _ ζ c h`. Set `P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))` to `Scheme.Γ ⋙ twF q i`. Set `U : Scheme.{0}` to `Spec (CommRingCat.of K)`. Set `m : P.obj (op U)` to `Submodule.Quotient.mk (Finsupp.single (gam ζ) 1)`. Establish `h1 : ((toSheafify Scheme.etaleTopology P).app (op U)).hom (c.val • m) = ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0`.

Rewrite using `[map_nsmul, map_zero]`. Conclude with `h`. Establish `hS` using `Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c.val • m) 0 h1`. Take `⟨𝒰, hle⟩` from `Scheme.exists_cover_of_mem_grothendieckTopology hS`. Take `⟨p⟩ : Nonempty U` from `inferInstance`.

Take `⟨j, y, -⟩` from `((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 p`. Establish `hj` using `hle _ _ (Presieve.ofArrows.mk j)`. Establish `: Nonempty (𝒰.X j)` using `⟨y⟩`. Establish `: Nontrivial (Scheme.Γ.obj (op (𝒰.X j)))` using `gamma_nontrivial (𝒰.X j)`. Apply `ring_nz i ((gam ζ).map (Scheme.Γ.map (𝒰.f j).op).hom) c` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(P.map (𝒰.f j).op).hom (c.val • m) = (P.map (𝒰.f j).op).hom 0 at hj`. Rewrite `hj` using `[map_nsmul, map_zero]`. Express the relevant statement in the definitionally equal form `c.val • Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map (𝒰.f j).op).hom) (Finsupp.single (gam ζ) 1)) = _ at hj`. Use `erw [Finsupp.mapDomain_single] at hj`. Conclude with `hj`.
-/
theorem TwGenNZAC_of : LateralTheory.E.LCBijPf.TwGenNZAC := by
  intro q _ i K _ _ ζ c h
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q i
  let U : Scheme.{0} := Spec (CommRingCat.of K)
  let m : P.obj (op U) := Submodule.Quotient.mk (Finsupp.single (gam ζ) 1)
  have h1 : ((toSheafify Scheme.etaleTopology P).app (op U)).hom (c.val • m) =
      ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by
    rw [map_nsmul, map_zero]
    exact h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c.val • m) 0 h1
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨p⟩ : Nonempty U := inferInstance
  obtain ⟨j, y, -⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 p
  have hj := hle _ _ (Presieve.ofArrows.mk j)
  have : Nonempty (𝒰.X j) := ⟨y⟩
  have : Nontrivial (Scheme.Γ.obj (op (𝒰.X j))) := gamma_nontrivial (𝒰.X j)
  apply ring_nz i ((gam ζ).map (Scheme.Γ.map (𝒰.f j).op).hom) c
  change (P.map (𝒰.f j).op).hom (c.val • m) = (P.map (𝒰.f j).op).hom 0 at hj
  rw [map_nsmul, map_zero] at hj
  change c.val • Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map (𝒰.f j).op).hom)
    (Finsupp.single (gam ζ) 1)) = _ at hj
  erw [Finsupp.mapDomain_single] at hj
  exact hj

end LateralTheory.E.TwGenNZACPf

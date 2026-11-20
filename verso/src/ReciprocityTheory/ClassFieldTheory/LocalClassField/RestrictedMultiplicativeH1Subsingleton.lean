import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.FiveTerm
import ReciprocityTheory.ClassFieldTheory.LocalClassField.KbarRepContAction

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

/- English proof (translation)
Set `r : H → (E →ₐ[K] L)` to `fun h => ((h : L ≃ₐ[K] L) : L →ₐ[K] L).comp E.val`. Establish `hr : ∀ (h : H) (x : E), r h x = (h : L ≃ₐ[K] L) (x : L)` using `fun _ _ => rfl`. Establish `hfr : ∀ g h : H, r g = r h → f g = f h`. Introduce `g h hgh`. Establish `hmem : ((g⁻¹ * h : H) : L ≃ₐ[K] L) ∈ E.fixingSubgroup`.

Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Establish `h1 : (g : L ≃ₐ[K] L) x = (h : L ≃ₐ[K] L) x` using `DFunLike.congr_fun hgh ⟨x, hx⟩`. Use `show ((g : L ≃ₐ[K] L)⁻¹ * (h : L ≃ₐ[K] L)) x = x`. Rewrite using `[AlgEquiv.mul_apply, ← h1]`.

Conclude with `(g : L ≃ₐ[K] L).symm_apply_apply x`. Establish `h2` using `hc g (g⁻¹ * h)`. Rewrite `h2` using `[mul_inv_cancel_left, hE _ hmem, map_one, mul_one]`. Conclude with `h2.symm`. Set `S` to `Set.range r`.

Establish `: Finite (E →ₐ[K] L)` using `inferInstance`. Set `_ : Fintype S` to `Fintype.ofFinite S`. Establish `hrep : ∀ s : S, ∃ h : H, r h = s.1` using `fun s => s.2`. Use `choose rep hrep using hrep`. Set `a : S → L` to `fun s => (f (rep s) : L)`.

Establish `hli : LinearIndependent L (fun s : S => ((s.1 : E →* L) : E → L))`. Use `(linearIndependent_monoidHom E L).comp (fun s : S => (s.1 : E →* L)) ?_` and prove the remaining obligations. Introduce `s t hst`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `AlgHom.ext` to reduce the goal to its premises.

Introduce `x`. Conclude with `DFunLike.congr_fun hst x`. Establish `hex : ∃ c : E, ∑ s : S, a s * s.1 c ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `h0 : ∑ s : S, a s • ((s.1 : E →* L) : E → L) = 0`. Use function extensionality and compare the values at `c`. Rewrite using `[Finset.sum_apply]`. Conclude with `hcon c`. Use `Fintype.linearIndependent_iff.1 hli a h0 ⟨r 1, 1, rfl⟩` as an intermediate fact.

Conclude with `(f (rep ⟨r 1, 1, rfl⟩)).ne_zero this`. Take `⟨c, hcne⟩` from `hex`. Use `set b : L := ∑ s : S, a s * s.1 c with hb`. Establish `key : ∀ h : H, b = f h * (h : L ≃ₐ[K] L) b`. Introduce `h`.

Set `m : S → S` to `fun s => ⟨r (h * rep s), _, rfl⟩`. Establish `hm1 : ∀ (s : S) (x : E), (m s).1 x = (h : L ≃ₐ[K] L) (s.1 x)`. Introduce `s x`. Use `show r (h * rep s) x = _`. Rewrite using `[← hrep s, hr, hr]`.

Both sides reduce to the same expression. Establish `hminj : Function.Injective m`. Introduce `s t hst`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `AlgHom.ext` to reduce the goal to its premises.

Introduce `x`. Apply `(h : L ≃ₐ[K] L).injective` to reduce the goal to its premises. Rewrite using `[← hm1, ← hm1, hst]`. Establish `hmbij : Function.Bijective m` using `Finite.injective_iff_bijective.1 hminj`. Establish `hma : ∀ s, a (m s) = f h * (h : L ≃ₐ[K] L) (a s)`.

Introduce `s`. Use `show (f (rep (m s)) : L) = _`. Rewrite using `[hfr (rep (m s)) (h * rep s) (hrep (m s)), hc]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hb, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[hma, hm1, map_mul, mul_assoc]`. Use `⟨(Units.mk0 b hcne)⁻¹, fun h => ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Establish `hb' : (h : L ≃ₐ[K] L) b ≠ 0`. Simplify using `using hcne`. Establish `e1 : ((Units.map ((h : L ≃ₐ[K] L) : L →* L) (Units.mk0 b hcne)⁻¹ / (Units.mk0 b hcne)⁻¹ : Lˣ) : L) = ((h : L ≃ₐ[K] L) b)⁻¹ * b`. Rewrite using `[map_inv, div_inv_eq_mul, Units.val_mul, Units.val_inv_eq_inv_val]`. Both sides reduce to the same expression.

Rewrite using `[e1]`. Clear the denominators using the available nonvanishing facts. Conclude with `(key h).symm`.
-/
theorem exists_units_of_cocycle {K L : Type*} [Field K] [Field L] [Algebra K L] (H : Subgroup (L ≃ₐ[K] L))
    (f : H → Lˣ) (E : IntermediateField K L) [FiniteDimensional K E]
    (hE : ∀ h : H, (h : L ≃ₐ[K] L) ∈ E.fixingSubgroup → f h = 1)
    (hc : ∀ g h : H, f (g * h) = f g * Units.map ((g : L ≃ₐ[K] L) : L →* L) (f h)) :
    ∃ β : Lˣ, ∀ h : H, f h = Units.map ((h : L ≃ₐ[K] L) : L →* L) β / β := by
  classical

  let r : H → (E →ₐ[K] L) := fun h => ((h : L ≃ₐ[K] L) : L →ₐ[K] L).comp E.val
  have hr : ∀ (h : H) (x : E), r h x = (h : L ≃ₐ[K] L) (x : L) := fun _ _ => rfl
  have hfr : ∀ g h : H, r g = r h → f g = f h := by
    intro g h hgh
    have hmem : ((g⁻¹ * h : H) : L ≃ₐ[K] L) ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (g : L ≃ₐ[K] L) x = (h : L ≃ₐ[K] L) x := DFunLike.congr_fun hgh ⟨x, hx⟩
      show ((g : L ≃ₐ[K] L)⁻¹ * (h : L ≃ₐ[K] L)) x = x
      rw [AlgEquiv.mul_apply, ← h1]
      exact (g : L ≃ₐ[K] L).symm_apply_apply x
    have h2 := hc g (g⁻¹ * h)
    rw [mul_inv_cancel_left, hE _ hmem, map_one, mul_one] at h2
    exact h2.symm
  let S := Set.range r
  have : Finite (E →ₐ[K] L) := inferInstance
  let _ : Fintype S := Fintype.ofFinite S
  have hrep : ∀ s : S, ∃ h : H, r h = s.1 := fun s => s.2
  choose rep hrep using hrep
  let a : S → L := fun s => (f (rep s) : L)
  have hli : LinearIndependent L (fun s : S => ((s.1 : E →* L) : E → L)) := by
    refine (linearIndependent_monoidHom E L).comp (fun s : S => (s.1 : E →* L)) ?_
    intro s t hst
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun hst x
  have hex : ∃ c : E, ∑ s : S, a s * s.1 c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ s : S, a s • ((s.1 : E →* L) : E → L) = 0 := by
      funext c
      rw [Finset.sum_apply]
      exact hcon c
    have := Fintype.linearIndependent_iff.1 hli a h0 ⟨r 1, 1, rfl⟩
    exact (f (rep ⟨r 1, 1, rfl⟩)).ne_zero this
  obtain ⟨c, hcne⟩ := hex
  set b : L := ∑ s : S, a s * s.1 c with hb
  have key : ∀ h : H, b = f h * (h : L ≃ₐ[K] L) b := by
    intro h
    let m : S → S := fun s => ⟨r (h * rep s), _, rfl⟩
    have hm1 : ∀ (s : S) (x : E), (m s).1 x = (h : L ≃ₐ[K] L) (s.1 x) := by
      intro s x
      show r (h * rep s) x = _
      rw [← hrep s, hr, hr]
      rfl
    have hminj : Function.Injective m := by
      intro s t hst
      apply Subtype.ext
      apply AlgHom.ext
      intro x
      apply (h : L ≃ₐ[K] L).injective
      rw [← hm1, ← hm1, hst]
    have hmbij : Function.Bijective m := Finite.injective_iff_bijective.1 hminj
    have hma : ∀ s, a (m s) = f h * (h : L ≃ₐ[K] L) (a s) := by
      intro s
      show (f (rep (m s)) : L) = _
      rw [hfr (rep (m s)) (h * rep s) (hrep (m s)), hc]
      rfl
    calc b = ∑ s, a (m s) * (m s).1 c := (hmbij.sum_comp (fun s => a s * s.1 c)).symm
      _ = f h * (h : L ≃ₐ[K] L) b := by
        rw [hb, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hma, hm1, map_mul, mul_assoc]
  refine ⟨(Units.mk0 b hcne)⁻¹, fun h => ?_⟩
  apply Units.ext
  have hb' : (h : L ≃ₐ[K] L) b ≠ 0 := by
    simpa using hcne
  have e1 : ((Units.map ((h : L ≃ₐ[K] L) : L →* L) (Units.mk0 b hcne)⁻¹ / (Units.mk0 b hcne)⁻¹ : Lˣ) : L)
      = ((h : L ≃ₐ[K] L) b)⁻¹ * b := by
    rw [map_inv, div_inv_eq_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  rw [e1]
  field_simp
  exact (key h).symm

/- English proof (translation)
Establish `h1 : e (f 1) = 1`. Establish `h` using `hc 1 1`. Rewrite `h` using `[mul_one]`. Establish `h' : Units.map (((1 : H) : L ≃ₐ[K] L) : L →* L) (e (f 1)) = e (f 1)` using `Units.ext rfl`. Rewrite `h` using `[h']`.

Conclude with `(left_eq_mul.1 h)`. Establish `hopen : IsOpen (f ⁻¹' {f 1})` using `(isOpen_discrete _).preimage hf`. Take `⟨V, hV, hVf⟩` from `isOpen_induced_iff.1 hopen`. Establish `h1V : (1 : L ≃ₐ[K] L) ∈ V`. Establish `: (1 : H) ∈ Subtype.val ⁻¹' V` using `by rw [hVf]; rfl`.

Conclude with `this`. Take `⟨E, hfin, hEV⟩` from `(krullTopology_mem_nhds_one_iff K L V).1 (hV.mem_nhds h1V)`. Use `exists_units_of_cocycle H (fun h => e (f h)) E (fun h hh => ?_) hc` and prove the remaining obligations. Establish `: h ∈ Subtype.val ⁻¹' V` using `hEV hh`. Rewrite `this` using `[hVf]`.

Establish `h2 : f h = f 1` using `this`. Use `show e (f h) = 1`. Rewrite using `[h2, h1]`.
-/
theorem exists_units_of_continuous_cocycle {K L : Type*} [Field K] [Field L] [Algebra K L]
    (H : Subgroup (L ≃ₐ[K] L)) {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (e : X ≃ Lˣ)
    (f : H → X) (hf : Continuous f)
    (hc : ∀ g h : H, e (f (g * h)) = e (f g) * Units.map ((g : L ≃ₐ[K] L) : L →* L) (e (f h))) :
    ∃ β : Lˣ, ∀ h : H, e (f h) = Units.map ((h : L ≃ₐ[K] L) : L →* L) β / β := by
  have h1 : e (f 1) = 1 := by
    have h := hc 1 1
    rw [mul_one] at h
    have h' : Units.map (((1 : H) : L ≃ₐ[K] L) : L →* L) (e (f 1)) = e (f 1) := Units.ext rfl
    rw [h'] at h
    exact (left_eq_mul.1 h)
  have hopen : IsOpen (f ⁻¹' {f 1}) := (isOpen_discrete _).preimage hf
  obtain ⟨V, hV, hVf⟩ := isOpen_induced_iff.1 hopen
  have h1V : (1 : L ≃ₐ[K] L) ∈ V := by
    have : (1 : H) ∈ Subtype.val ⁻¹' V := by rw [hVf]; rfl
    exact this
  obtain ⟨E, hfin, hEV⟩ := (krullTopology_mem_nhds_one_iff K L V).1 (hV.mem_nhds h1V)
  refine exists_units_of_cocycle H (fun h => e (f h)) E (fun h hh => ?_) hc
  have : h ∈ Subtype.val ⁻¹' V := hEV hh
  rw [hVf] at this
  have h2 : f h = f 1 := this
  show e (f h) = 1
  rw [h2, h1]

section Padic

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/- English proof (translation)
Take `⟨β, hβ⟩` from `exists_units_of_continuous_cocycle H (X := KbarMult p) (Additive.toMul : Additive (PadicAlgCl p)ˣ ≃ (PadicAlgCl p)ˣ) f hf (fun g h => congrArg (Additive.toMul : Additive (PadicAlgCl p)ˣ → (PadicAlgCl p)ˣ) (hc g h))`. Conclude with `⟨(Additive.ofMul β : Additive (PadicAlgCl p)ˣ), fun h => congrArg (Additive.ofMul : (PadicAlgCl p)ˣ → Additive (PadicAlgCl p)ˣ) (hβ h)⟩`.
-/
theorem kbar_cocycle_subgroup (H : Subgroup (GK p K)) (f : H → KbarMult p) (hf : Continuous f)
    (hc : ∀ g h : H, f (g * h) = f g + kbarRep p K g (f h)) :
    ∃ m : KbarMult p, ∀ h : H, f h = kbarRep p K h m - m := by
  obtain ⟨β, hβ⟩ := exists_units_of_continuous_cocycle H
    (X := KbarMult p) (Additive.toMul : Additive (PadicAlgCl p)ˣ ≃ (PadicAlgCl p)ˣ) f hf
    (fun g h => congrArg (Additive.toMul : Additive (PadicAlgCl p)ˣ → (PadicAlgCl p)ˣ) (hc g h))
  exact ⟨(Additive.ofMul β : Additive (PadicAlgCl p)ˣ), fun h =>
    congrArg (Additive.ofMul : (PadicAlgCl p)ˣ → Additive (PadicAlgCl p)ˣ) (hβ h)⟩

/- English proof (translation)
Take `⟨m, hm⟩` from `kbar_cocycle_subgroup p K ⊤ (fun h => f h.1) (hf.comp continuous_subtype_val) (fun g h => hc g.1 h.1)`. Conclude with `⟨m, fun h => hm ⟨h, Subgroup.mem_top h⟩⟩`.
-/
theorem kbar_cocycle (f : GK p K → KbarMult p) (hf : Continuous f)
    (hc : ∀ g h, f (g * h) = f g + kbarRep p K g (f h)) :
    ∃ m : KbarMult p, ∀ h, f h = kbarRep p K h m - m := by
  obtain ⟨m, hm⟩ := kbar_cocycle_subgroup p K ⊤ (fun h => f h.1) (hf.comp continuous_subtype_val)
    (fun g h => hc g.1 h.1)
  exact ⟨m, fun h => hm ⟨h, Subgroup.mem_top h⟩⟩

/- English proof (translation)
Rewrite using `[Submodule.Quotient.subsingleton_iff, eq_top_iff]`. Introduce and unpack `⟨z, hz⟩ -`. Rewrite using `[Submodule.mem_comap]`. Use `show z ∈ Bd1 _`. Rewrite using `[mem_contCoboundaries1]`.

Conclude with `kbar_cocycle p K z hz.1 hz.2`.
-/
theorem h1_kbarRep_subsingleton : Subsingleton (H1 (kbarRep p K)) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨z, hz⟩ -
  rw [Submodule.mem_comap]
  show z ∈ Bd1 _
  rw [mem_contCoboundaries1]
  exact kbar_cocycle p K z hz.1 hz.2

end Padic

section TRep

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/- English proof (translation)
Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ x : ((kbarT p K).resSub H).H 1, x = 0`. Introduce `x`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[mk_eq_zero_iff, mem_oneCoboundaries_iff]`.

Establish `hz : ((kbarT p K).resSub H).coch.d 1 z.1 = 0` using `(memZ z.1).1 z.2`. Conclude with `kbar_cocycle_subgroup p K H (fun h => z.1.1 (e1 h)) (Continuous.comp z.1.2 (continuous_pi fun _ => continuous_id)) ((wach_d1_eq_zero_iff _ z.1).1 hz)`. Rewrite using `[h0 x, h0 y]`.
-/
theorem restricted_multiplicative_h1_subsingleton (H : Subgroup (GK p K)) :
    Subsingleton (((kbarT p K).resSub H).H 1) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : ((kbarT p K).resSub H).H 1, x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mk_eq_zero_iff, mem_oneCoboundaries_iff]
    have hz : ((kbarT p K).resSub H).coch.d 1 z.1 = 0 := (memZ z.1).1 z.2
    exact kbar_cocycle_subgroup p K H (fun h => z.1.1 (e1 h))
      (Continuous.comp z.1.2 (continuous_pi fun _ => continuous_id))
      ((wach_d1_eq_zero_iff _ z.1).1 hz)
  rw [h0 x, h0 y]

/- English proof (translation)
Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ x : (kbarT p K).H 1, x = 0`. Introduce `x`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[mk_eq_zero_iff, mem_oneCoboundaries_iff]`.

Establish `hz : (kbarT p K).coch.d 1 z.1 = 0` using `(memZ z.1).1 z.2`. Conclude with `kbar_cocycle p K (fun h => z.1.1 (e1 h)) (Continuous.comp z.1.2 (continuous_pi fun _ => continuous_id)) ((wach_d1_eq_zero_iff _ z.1).1 hz)`. Rewrite using `[h0 x, h0 y]`.
-/
theorem multiplicative_cochain_h1_subsingleton : Subsingleton ((kbarT p K).H 1) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : (kbarT p K).H 1, x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mk_eq_zero_iff, mem_oneCoboundaries_iff]
    have hz : (kbarT p K).coch.d 1 z.1 = 0 := (memZ z.1).1 z.2
    exact kbar_cocycle p K (fun h => z.1.1 (e1 h))
      (Continuous.comp z.1.2 (continuous_pi fun _ => continuous_id))
      ((wach_d1_eq_zero_iff _ z.1).1 hz)
  rw [h0 x, h0 y]

/- English proof (translation)
The claim follows from `have := multiplicative_cochain_h1_subsingleton p K (inf_inj (kbarT p K) N Q P hP).subsingleton`.
-/
theorem quotient_multiplicative_h1_subsingleton (N : Subgroup (GK p K)) [N.Normal] (Q : TRep ℤ (GK p K ⧸ N))
    (P : Pair Q (kbarT p K)) (hP : IsInvRep (kbarT p K) N Q P) : Subsingleton (Q.H 1) :=
  have := multiplicative_cochain_h1_subsingleton p K
  (inf_inj (kbarT p K) N Q P hP).subsingleton

/- English proof (translation)
Establish `hint : Algebra.IsIntegral K (PadicAlgCl p)` using `Algebra.IsIntegral.tower_top (R := ℚ_[p])`. Establish `hs` using `restricted_multiplicative_h1_subsingleton p K N`. Take `⟨tg, -, hex⟩` from `fiveTerm_holds ℤ (GK p K) (kbarT p K) N hN Q P hP ⊤ (fun x => ⟨fun _ s c _ _ => Subsingleton.elim _ _, fun _ => Submodule.mem_top⟩)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`.

Take `⟨x, rfl⟩` from `(hex y).1 hy`. Establish `hx : x = 0` using `Subsingleton.elim _ _`. Rewrite using `[hx, map_zero]`.
-/
theorem multiplicative_inflation_h2_injective (N : Subgroup (GK p K)) [N.Normal] (hN : IsClosed (N : Set (GK p K)))
    (Q : TRep ℤ (GK p K ⧸ N)) (P : Pair Q (kbarT p K)) (hP : IsInvRep (kbarT p K) N Q P) :
    Function.Injective (P.hom.H 2) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  have hs := restricted_multiplicative_h1_subsingleton p K N
  obtain ⟨tg, -, hex⟩ := fiveTerm_holds ℤ (GK p K) (kbarT p K) N hN Q P hP ⊤
    (fun x => ⟨fun _ s c _ _ => Subsingleton.elim _ _, fun _ => Submodule.mem_top⟩)
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := (hex y).1 hy
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx, map_zero]

end TRep

end ReciprocityTheory.DiscreteGroups.LocalClassField

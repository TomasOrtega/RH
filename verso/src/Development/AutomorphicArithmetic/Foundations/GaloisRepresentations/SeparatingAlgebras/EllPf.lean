import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantZmodLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `hGrp E _ _ _ n C hLev H _ lam hU2 hfin`. Establish `hC` using `hLev.fin`. Establish `hCc` using `hLev.compact`. Take `⟨U1, hU1o, hU11, hU1C⟩` from `hLev.isOpen`. Take `⟨U2, hU2o, hU21, hU2l⟩` from `hU2`.

Use `set D : Subgroup (UA E n) := C ⊔ infU E n with hDdef`. Establish `hDC : D ≤ C.comap GlobalTheory.EllU.finPart` using `sup_le (fun c hc => by`. Express the relevant statement in the definitionally equal form `GlobalTheory.EllU.finPart c ∈ C`. Rewrite using `[GlobalTheory.EllU.finPart_of_finU (hC hc)]`. Conclude with `hc)`.

Use the proof step `(fun x hx => by`. Express the relevant statement in the definitionally equal form `GlobalTheory.EllU.finPart x ∈ C`. Rewrite using `[GlobalTheory.EllU.finPart_of_infU hx]`. Conclude with `C.one_mem)`. Set `f : D →* C` to `(GlobalTheory.EllU.finPart.comp D.subtype).codRestrict C (fun d => hDC d.2)`.

Set `lam' : D →* H` to `lam.comp f`. Use `haveI := GlobalTheory.InfUCompact.compactSpace_infU E n`. Establish `hI : IsCompact (infU E n : Set (UA E n))` using `isCompact_iff_compactSpace.2 inferInstance`. Establish `hDc : IsCompact (D : Set (UA E n))`. Rewrite using `[hDdef, Subgroup.mul_normal]`.

Conclude with `hCc.mul hI`. Establish `hyp : ∀ g : UA E n, ∀ γ ∈ ratU E n, ∀ d : D, γ * g = g * d → lam' d = 1`. Introduce `g γ hγ d h`. Establish `hγ' : g * (d : UA E n) * g⁻¹ ∈ ratU E n`. Rewrite using `[← h, mul_inv_cancel_right]`.

Conclude with `hγ`. Establish `hd : IsOfFinOrder (d : UA E n)` using `GlobalTheory.T.isOfFinOrder_of_compact_conj_mem_unitaryRationalPoints E n D hDc g d d.2 hγ'`. Take `⟨m, hm, hpow⟩` from `isOfFinOrder_iff_pow_eq_one.1 hd`. Establish `hdm : d ^ m = 1` using `Subtype.ext (by rw [Subgroup.coe_pow, hpow]; rfl)`. Conclude with `hfin (f d) (isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, by rw [← map_pow, hdm, map_one]⟩)`.

Take `⟨ℓ, h1, h2⟩` from `hGrp (UA E n) H (ratU E n) D lam' hyp`. Establish `hinf : ∀ g, ∀ x ∈ infU E n, ℓ (g * x) = ℓ g`. Introduce `g x hx`. Establish `e : f ⟨x, le_sup_right (a` using `C) hx⟩ = 1 := Subtype.ext (GlobalTheory.EllU.finPart_of_infU hx)`. Use `h2 g ⟨x, le_sup_right (a := C) hx⟩` as an intermediate fact.

Simplify using `only [lam', MonoidHom.comp_apply, e, map_one, mul_one] at this`. Conclude with `this`. Establish `hC' : ∀ g (c : C), ℓ (g * c) = ℓ g * lam c`. Introduce `g c`. Establish `e : f ⟨c, le_sup_left (b` using `infU E n) c.2⟩ = c := Subtype.ext (GlobalTheory.EllU.finPart_of_finU (hC c.2))`.

Use `h2 g ⟨c, le_sup_left (b := infU E n) c.2⟩` as an intermediate fact. Simplify using `only [lam', MonoidHom.comp_apply, e] at this`. Conclude with `this`. Use `set Wn : Set (UA E n) := GlobalTheory.EllU.finPart ⁻¹' (U1 ∩ U2) with hWn`. Establish `hWo : IsOpen Wn` using `(hU1o.inter hU2o).preimage GlobalTheory.EllU.continuous_finPart`.

Establish `hW1 : (1 : UA E n) ∈ Wn`. Express the relevant statement in the definitionally equal form `GlobalTheory.EllU.finPart 1 ∈ U1 ∩ U2`. Rewrite using `[map_one]`. Conclude with `⟨hU11, hU21⟩`. Establish `hWinv : ∀ g, ∀ w ∈ Wn, ℓ (g * w) = ℓ g`.

Introduce `g w hw`. Take `⟨hw1, hw2⟩` from `hw`. Establish `hkC : GlobalTheory.EllU.finPart w ∈ C` using `hU1C ⟨hw1, GlobalTheory.EllU.finPart_mem w⟩`. Establish `hl : lam ⟨GlobalTheory.EllU.finPart w, hkC⟩ = 1` using `hU2l ⟨GlobalTheory.EllU.finPart w, hkC⟩ hw2`. Establish `e : g * w = g * GlobalTheory.EllU.finPart w * ((GlobalTheory.EllU.finPart w)⁻¹ * w)` using `by group`.

Rewrite using `[e, hinf _ _ (GlobalTheory.EllU.inv_finPart_mul_mem w)]`. Use `hC' g ⟨GlobalTheory.EllU.finPart w, hkC⟩` as an intermediate fact. Rewrite `this` using `[hl, mul_one]`. Conclude with `this`. Use `⟨ℓ, hinf, hC', fun φ => ?_⟩` and prove the remaining obligations.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_iff_continuousAt.2 fun g => ?_` and prove the remaining obligations. Use `(continuousAt_const (y := φ (ℓ g))).congr ?_` and prove the remaining obligations. Establish `hc : Continuous fun y : UA E n => g⁻¹ * y` using `continuous_const.mul continuous_id`. Establish `hm : Wn ∈ nhds (g⁻¹ * g)`.

Rewrite using `[inv_mul_cancel]`. Conclude with `hWo.mem_nhds hW1`. Use `filter_upwards [hc.continuousAt.preimage_mem_nhds hm] with y hy`. Express the relevant statement in the definitionally equal form `φ (ℓ g) = φ (ℓ y)`. Use `hWinv g _ hy` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel_left]`. Rewrite using `[this]`. Introduce `γ hγ g`. Express the relevant statement in the definitionally equal form `φ (ℓ (γ * g)) = φ (ℓ g)`. Rewrite using `[h1 γ hγ g]`.

Set `S : Subgroup (finU E n)` to `{ carrier := {k | RU E n k (fun g => φ (ℓ g)) = fun g => φ (ℓ g)} one_mem' := by`. Express the relevant statement in the definitionally equal form `RU E n 1 _ = _`. Rewrite using `[map_one]`. Both sides reduce to the same expression. Use the proof step `mul_mem' := fun {a b} ha hb => by`.

Express the relevant statement in the definitionally equal form `RU E n ((a : UA E n) * b) _ = _`. Rewrite using `[map_mul, Module.End.mul_apply]`. Express the relevant statement in the definitionally equal form `RU E n a (RU E n b _) = _`. Rewrite using `[hb, ha]`. Use the proof step `inv_mem' := fun {a} ha => by`.

Express the relevant statement in the definitionally equal form `RU E n ((a : UA E n)⁻¹) _ = _`. Use `conv_lhs => rw [← ha]`. Express the relevant statement in the definitionally equal form `RU E n ((a : UA E n)⁻¹) (RU E n a _) = _`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`. Use `rfl }`.

Express the relevant statement in the definitionally equal form `IsOpen (S : Set (finU E n))`. Use `Subgroup.isOpen_of_mem_nhds S (g := 1) ?_` and prove the remaining obligations. Establish `ho : IsOpen ((Subtype.val : finU E n → UA E n) ⁻¹' Wn)` using `hWo.preimage continuous_subtype_val`. Use `Filter.mem_of_superset (ho.mem_nhds hW1) fun k hk => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `RU E n k _ = _`.

Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `φ (ℓ (g * k)) = φ (ℓ g)`. Rewrite using `[hWinv g _ hk]`. Use `FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton (fun g => φ (ℓ g))).subset ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`.

Express the relevant statement in the definitionally equal form `RU E n k _ = _`. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `φ (ℓ (g * k)) = φ (ℓ g)`. Rewrite using `[hinf g k k.2]`.
-/
theorem UpperTheory.Gal.Gen.ell_pf :
    UpperTheory.Gal.Gen.EllGrp → UpperTheory.Gal.Gen.Ell := by
  intro hGrp E _ _ _ n C hLev H _ lam hU2 hfin
  have hC := hLev.fin
  have hCc := hLev.compact
  obtain ⟨U1, hU1o, hU11, hU1C⟩ := hLev.isOpen
  obtain ⟨U2, hU2o, hU21, hU2l⟩ := hU2
  set D : Subgroup (UA E n) := C ⊔ infU E n with hDdef
  have hDC : D ≤ C.comap GlobalTheory.EllU.finPart := sup_le (fun c hc => by
      change GlobalTheory.EllU.finPart c ∈ C
      rw [GlobalTheory.EllU.finPart_of_finU (hC hc)]; exact hc)
    (fun x hx => by
      change GlobalTheory.EllU.finPart x ∈ C
      rw [GlobalTheory.EllU.finPart_of_infU hx]; exact C.one_mem)
  let f : D →* C := (GlobalTheory.EllU.finPart.comp D.subtype).codRestrict C (fun d => hDC d.2)
  let lam' : D →* H := lam.comp f
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E n
  have hI : IsCompact (infU E n : Set (UA E n)) := isCompact_iff_compactSpace.2 inferInstance
  have hDc : IsCompact (D : Set (UA E n)) := by
    rw [hDdef, Subgroup.mul_normal]
    exact hCc.mul hI
  have hyp : ∀ g : UA E n, ∀ γ ∈ ratU E n, ∀ d : D, γ * g = g * d → lam' d = 1 := by
    intro g γ hγ d h
    have hγ' : g * (d : UA E n) * g⁻¹ ∈ ratU E n := by
      rw [← h, mul_inv_cancel_right]; exact hγ
    have hd : IsOfFinOrder (d : UA E n) := GlobalTheory.T.isOfFinOrder_of_compact_conj_mem_unitaryRationalPoints E n D hDc g d d.2 hγ'
    obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hd
    have hdm : d ^ m = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hpow]; rfl)
    exact hfin (f d) (isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, by rw [← map_pow, hdm, map_one]⟩)
  obtain ⟨ℓ, h1, h2⟩ := hGrp (UA E n) H (ratU E n) D lam' hyp
  have hinf : ∀ g, ∀ x ∈ infU E n, ℓ (g * x) = ℓ g := by
    intro g x hx
    have e : f ⟨x, le_sup_right (a := C) hx⟩ = 1 := Subtype.ext (GlobalTheory.EllU.finPart_of_infU hx)
    have := h2 g ⟨x, le_sup_right (a := C) hx⟩
    simp only [lam', MonoidHom.comp_apply, e, map_one, mul_one] at this
    exact this
  have hC' : ∀ g (c : C), ℓ (g * c) = ℓ g * lam c := by
    intro g c
    have e : f ⟨c, le_sup_left (b := infU E n) c.2⟩ = c := Subtype.ext (GlobalTheory.EllU.finPart_of_finU (hC c.2))
    have := h2 g ⟨c, le_sup_left (b := infU E n) c.2⟩
    simp only [lam', MonoidHom.comp_apply, e] at this
    exact this
  set Wn : Set (UA E n) := GlobalTheory.EllU.finPart ⁻¹' (U1 ∩ U2) with hWn
  have hWo : IsOpen Wn := (hU1o.inter hU2o).preimage GlobalTheory.EllU.continuous_finPart
  have hW1 : (1 : UA E n) ∈ Wn := by
    change GlobalTheory.EllU.finPart 1 ∈ U1 ∩ U2
    rw [map_one]; exact ⟨hU11, hU21⟩
  have hWinv : ∀ g, ∀ w ∈ Wn, ℓ (g * w) = ℓ g := by
    intro g w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hkC : GlobalTheory.EllU.finPart w ∈ C := hU1C ⟨hw1, GlobalTheory.EllU.finPart_mem w⟩
    have hl : lam ⟨GlobalTheory.EllU.finPart w, hkC⟩ = 1 := hU2l ⟨GlobalTheory.EllU.finPart w, hkC⟩ hw2
    have e : g * w = g * GlobalTheory.EllU.finPart w * ((GlobalTheory.EllU.finPart w)⁻¹ * w) := by group
    rw [e, hinf _ _ (GlobalTheory.EllU.inv_finPart_mul_mem w)]
    have := hC' g ⟨GlobalTheory.EllU.finPart w, hkC⟩
    rw [hl, mul_one] at this
    exact this
  refine ⟨ℓ, hinf, hC', fun φ => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    refine (continuousAt_const (y := φ (ℓ g))).congr ?_
    have hc : Continuous fun y : UA E n => g⁻¹ * y := continuous_const.mul continuous_id
    have hm : Wn ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact hWo.mem_nhds hW1
    filter_upwards [hc.continuousAt.preimage_mem_nhds hm] with y hy
    change φ (ℓ g) = φ (ℓ y)
    have := hWinv g _ hy
    rw [mul_inv_cancel_left] at this
    rw [this]
  · intro γ hγ g
    change φ (ℓ (γ * g)) = φ (ℓ g)
    rw [h1 γ hγ g]
  · let S : Subgroup (finU E n) :=
      { carrier := {k | RU E n k (fun g => φ (ℓ g)) = fun g => φ (ℓ g)}
        one_mem' := by
          change RU E n 1 _ = _
          rw [map_one]; rfl
        mul_mem' := fun {a b} ha hb => by
          change RU E n ((a : UA E n) * b) _ = _
          rw [map_mul, Module.End.mul_apply]
          change RU E n a (RU E n b _) = _
          rw [hb, ha]
        inv_mem' := fun {a} ha => by
          change RU E n ((a : UA E n)⁻¹) _ = _
          conv_lhs => rw [← ha]
          change RU E n ((a : UA E n)⁻¹) (RU E n a _) = _
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    change IsOpen (S : Set (finU E n))
    refine Subgroup.isOpen_of_mem_nhds S (g := 1) ?_
    have ho : IsOpen ((Subtype.val : finU E n → UA E n) ⁻¹' Wn) := hWo.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho.mem_nhds hW1) fun k hk => ?_
    change RU E n k _ = _
    funext g
    change φ (ℓ (g * k)) = φ (ℓ g)
    rw [hWinv g _ hk]
  · refine FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton (fun g => φ (ℓ g))).subset ?_)
    rintro _ ⟨k, rfl⟩
    change RU E n k _ = _
    funext g
    change φ (ℓ (g * k)) = φ (ℓ g)
    rw [hinf g k k.2]

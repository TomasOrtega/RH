import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Set `m : k →+ A` to `AddMonoidHom.mk' μ h1`. Establish `h3 : ∀ (a : A) c, m (π a * c) = a * m c` using `h2`. Use `⟨m.mapMatrix, fun Y => rfl, fun M Y => ?_, fun M Y => ?_, fun Y => ?_, fun Y hY i j h => ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Simplify using `only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, h3]`.

Use extensionality with `a b`. Simplify using `only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (Y a c), h3, mul_comm]`. Use extensionality with `a b`.

Simplify using `only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, adj_apply, map_zsmul]`. Simplify using `only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, hY i j h, map_zero]`.
-/
private theorem exists_strictHenselian_absolutely_closed_local_ring {k A : Type} [CommRing k] [CommRing A] (π : A → k) (μ : k → A)
    (h1 : ∀ c d, μ (c + d) = μ c + μ d) (h2 : ∀ (a : A) c, μ (π a * c) = a * μ c) :
    ∃ T : M4 k →+ M4 A, (∀ Y, Y.map μ = T Y) ∧
      (∀ (M : M4 A) Y, M * T Y = T (M.map π * Y)) ∧
      (∀ (M : M4 A) Y, T Y * M = T (Y * M.map π)) ∧ (∀ Y, adj (T Y) = T (adj Y)) ∧
      ∀ Y, IsUp Y → IsUp (T Y) := by
  let m : k →+ A := AddMonoidHom.mk' μ h1
  have h3 : ∀ (a : A) c, m (π a * c) = a * m c := h2
  refine ⟨m.mapMatrix, fun Y => rfl, fun M Y => ?_, fun M Y => ?_, fun Y => ?_, fun Y hY i j h => ?_⟩
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, h3]
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm (Y a c), h3, mul_comm]
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, adj_apply, map_zsmul]
  · simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, hY i j h, map_zero]

/- English proof (translation)
Introduce `i j h`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : c < i`. Rewrite using `[hX i c hc, zero_mul]`.

Rewrite using `[hY c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]`.
-/
private theorem isUp_mul {k : Type} [CommRing k] {X Y : M4 k} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hX i c hc, zero_mul]
  · rw [hY c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

/- English proof (translation)
Introduce `i j h`. Rewrite using `[Matrix.add_apply, hX i j h, hY i j h, add_zero]`.
-/
private theorem isUp_add {k : Type} [CommRing k] {X Y : M4 k} (hX : IsUp X) (hY : IsUp Y) : IsUp (X + Y) := by
  intro i j h
  rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

/- English proof (translation)
Establish `: a * B * n * (a * g * n) = a * B * (n * a) * g * n` using `by simp only [mul_assoc]`. Rewrite using `[this, h]`. Use `noncomm_ring`.
-/
private theorem alg_id {S : Type} [Ring S] (a n B g y : S) (h : n * a = 1) :
    a * (B * g - (g * y - y * g)) * n + (a * (g * (y * n)) + a * -y * g * n) = a * B * n * (a * g * n) := by
  have : a * B * n * (a * g * n) = a * B * (n * a) * g * n := by simp only [mul_assoc]
  rw [this, h]
  noncomm_ring

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `s`. Establish `: ∀ a b, ∀ᶠ t in nhds s, rb t a b = rb s a b` using `fun a b => by filter_upwards [(hc a b 1).eventually_eq s] with t ht`. Rewrite `ht` using `[Ideal.Quotient.eq, pow_one, ← res_eq_zero_iff Λ, map_sub, sub_eq_zero]`. Rewrite using `[← hr, ← hr]`.

Conclude with `ht`. Use `filter_upwards [Filter.eventually_all.2 fun a => Filter.eventually_all.2 (this a)] with t ht`. Use extensionality with `a b`. Conclude with `ht a b`.
-/
private theorem rb_lc {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {Γ : Type} [TopologicalSpace Γ]
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (r : Γ → M4 R) (rb : Γ → M4 (ResidueField Λ))
    (hc : ∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) (hr : ∀ g, (r g).map (res Λ R) = rb g) :
    IsLocallyConstant rb := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ a b, ∀ᶠ t in nhds s, rb t a b = rb s a b := fun a b => by
    filter_upwards [(hc a b 1).eventually_eq s] with t ht
    rw [Ideal.Quotient.eq, pow_one, ← res_eq_zero_iff Λ, map_sub, sub_eq_zero] at ht
    rw [← hr, ← hr]
    exact ht
  filter_upwards [Filter.eventually_all.2 fun a => Filter.eventually_all.2 (this a)] with t ht
  ext a b
  exact ht a b

/- English proof (translation)
Introduce `Λ _ _ _ _ Γ V _ _ _ Gv _ _ _ loc hloc A R _ _ _ _ _ _ p hp hs ν r n hν hW hc rb nb hb hr hn D μ m1 m2 m3 x hx x1 x2`. Take `⟨T, T0, Tl, Tr, Ta, Tu⟩` from `exists_strictHenselian_absolutely_closed_local_ring (res Λ A) μ m1 m2`. Simplify using `only [T0, SL.om, SL.de] at x1 x2`. Establish `lc` using `rb_lc r rb hc hr`. Take `⟨h, y, b1, b3, b4⟩` from `hx`.

Take `⟨class_group_mod_eq_torsion, -, gA3, -, -, gA6, -⟩` from `grp A`. Take `⟨gR1, -, -, -, -, gR6, -⟩` from `grp R`. Take `⟨gk1, -⟩` from `grp (ResidueField Λ)`. Establish `aA : ∀ X : M4 A, (adj X).map (res Λ A) = adj (X.map (res Λ A))` using `fun X => (gA6 _ (res Λ A : A →+* ResidueField Λ) X).symm`. Establish `aR : ∀ X : M4 R, (adj X).map (res Λ R) = adj (X.map (res Λ R))` using `fun X => (gR6 _ (res Λ R : R →+* ResidueField Λ) X).symm`.

Establish `mR : ∀ X Y : M4 R, (X * Y).map (res Λ R) = X.map (res Λ R) * Y.map (res Λ R)` using `fun X Y => Matrix.map_mul (f := (res Λ R : R →+* ResidueField Λ))`. Establish `Tp : ∀ Y, (T Y).map p = 0` using `fun Y => by`. Rewrite using `[← T0]`. Use extensionality with `a b`. Conclude with `m3 _`.

Establish `Tres : ∀ Y, (T Y).map (res Λ A) = 0` using `fun Y => by`. Rewrite using `[← T0]`. Use extensionality with `a b`. Use `show res Λ A (μ _) = 0`. Rewrite using `[← res_map p, m3, map_zero]`.

Establish `TT : ∀ Y Y', T Y * T Y' = 0` using `fun Y Y' => by rw [Tl, Tres, zero_mul, map_zero]`. Establish `rtres : ∀ s, (D.rt s).map (res Λ A) = rb s` using `fun s => by`. Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, ← res_map p, ← hr, ← D.rt_map, Matrix.map_apply, Matrix.map_apply]`. Establish `ntres : ∀ v, (D.nt v).map (res Λ A) = nb v` using `fun s => by`.

Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, ← res_map p, ← hn, ← D.nt_map, Matrix.map_apply, Matrix.map_apply]`. Establish `pert : ∀ (c : A) (g : M4 A) (Y : M4 (ResidueField Λ)), IsGSp c g → Y ∈ sp4 (ResidueField Λ) → IsGSp c (g + T (Y * g.map (res Λ A)))` using `fun c g Y hg hY => by`. Establish `hY' : adj Y = -Y` using `hY`. Unfold `IsGSp at *`.

Rewrite using `[gA3, Ta, gk1, hY', add_mul, mul_add, mul_add, TT, Tl, Tr, hg, aA]`. Simplify using `only [mul_neg, neg_mul, map_neg, mul_assoc]`. Normalize the expressions using the abelian group laws. Establish `inv1 : ∀ s, rb s * rb s⁻¹ = 1` using `fun s => by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `inv2 : ∀ s, rb s⁻¹ * rb s = 1` using `fun s => by rw [← map_mul, inv_mul_cancel, map_one]`.

Use `set f : Γ → M4 A := fun s => D.rt s - T ((h s).1 * rb s) with hf`. Establish `fH : ∀ s, IsGSp (algebraMap Λ A (ν s)) (f s)` using `fun s => by`. Use `pert _ _ _ (D.rt_mult s) (-h s).2` as an intermediate fact. Rewrite `this` using `[rtres, Submodule.coe_neg, neg_mul, map_neg, ← sub_eq_add_neg]`. Conclude with `this`.

Establish `fmul : ∀ s t, f (s * t) = f s * f t` using `fun s t => by`. Establish `e` using `x1 s t`. Rewrite `e` using `[b3, sub_eq_iff_eq_add]`. Establish `e' : ((dOne (adSp rb hb) h (s, t)).1 : M4 _) * rb (s * t) = (h s).1 * rb s * rb t + rb s * ((h t).1 * rb t) - (h (s * t)).1 * rb (s * t)` using `by show ((h s).1 + rb s * (h t).1 * rb s⁻¹ - (h (s * t)).1) * rb (s * t) = _`. Rewrite using `[sub_mul, add_mul, map_mul, mul_assoc (rb s * (h t).1), ← mul_assoc (rb s⁻¹), inv2, one_mul]`.

Simplify using `only [mul_assoc]`. Rewrite using `[hf]`. Simplify using `only`. Rewrite using `[sub_mul, mul_sub, mul_sub, TT, Tl, Tr, rtres, rtres, e, e', map_sub, map_add]`. Normalize the expressions using the abelian group laws.

Establish `fone : f 1 = 1`. Establish `hu : adj (f 1) * f 1 = 1`. Use `fH 1` as an intermediate fact. Unfold `IsGSp at this`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Use `fmul 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `fp : ∀ s, (f s).map p = r s` using `fun s => by`.

Rewrite using `[hf]`. Simplify using `only`. Rewrite using `[Matrix.map_sub _ (map_sub p), Tp, D.rt_map, sub_zero]`. Establish `fres : ∀ s, (f s).map (res Λ A) = rb s` using `fun s => by`. Use extensionality with `a b`.

Rewrite using `[Matrix.map_apply, ← res_map p, ← hr, ← fp, Matrix.map_apply, Matrix.map_apply]`. Use `⟨{ toFun := f, map_one' := fone, map_mul' := fmul }, fun v => D.nt v + T ((y v).1 * nb v), ⟨fH, fun v => ?_, fun v s => ?_⟩, fun a b N => ?_, fp, fun v => ?_⟩` and prove the remaining obligations. Use `pert _ _ _ (D.nt_sp v) (y v).2` as an intermediate fact. Rewrite `this` using `[ntres]`. Then use the resulting hypothesis. Establish `n1 : adj (D.nt v) * D.nt v = 1`.

Use `D.nt_sp v` as an intermediate fact. Unfold `IsGSp at this`. Rewrite using `[this, one_smul]`. Establish `n2 : adj (nb v) * nb v = 1`. Rewrite using `[← ntres, ← aA]`.

Use `congrArg (fun X : M4 A => X.map (res Λ A : A →+* ResidueField Λ)) n1` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`. Rewrite `this` using `[Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `this`. Establish `n3 : nb v * adj (nb v) = 1` using `mul_eq_one_comm.1 n2`.

Establish `u1 : IsUp (adj (nb v) * rb (loc v s) * nb v)` using `fun i j hij => by`. Rewrite using `[← hn, ← hr, ← aR, ← mR, ← mR, Matrix.map_apply, hW.flag v s i j hij, map_zero]`. Establish `u2 : IsUp (adj (nb v) * ((x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1))) * nb v)` using `b4 v s`. Use `set B := (x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1)) with hB`. Establish `e` using `x2 v s`.

Rewrite `e` using `[sub_eq_iff_eq_add]`. Establish `hy : adj (y v).1 = -(y v).1` using `(y v).2`. Establish `e1 : f (loc v s) = D.nt v * D.t v s * adj (D.nt v) + T (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s)))`. Establish `: B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s)) = (x.2 v s).1 * rb (loc v s) - (h (loc v s)).1 * rb (loc v s)`. Rewrite using `[hB, sub_mul, sub_mul, sub_mul, mul_assoc _ _ (rb (loc v s)), inv2, mul_one]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this, map_sub, hf]`. Simplify using `only`. Rewrite using `[e]`. Normalize the expressions using the abelian group laws.

Establish `e2 : adj (D.nt v) * f (loc v s) * D.nt v = D.t v s + T (adj (nb v) * (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s))) * nb v)`. Rewrite using `[e1, mul_add, add_mul, Tl, Tr, aA, ntres]`. Use `congr 1`. Rewrite using `[← mul_assoc, ← mul_assoc, n1, one_mul, mul_assoc, n1, mul_one]`. Establish `key : adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)) = D.t v s + T ((adj (nb v) * B * nb v) * (adj (nb v) * rb (loc v s) * nb v))`.

Rewrite using `[gA3, Ta, gk1, hy, add_mul, add_mul, mul_add, mul_add, e2, Tr (f _), TT, Tr (D.nt v), mul_assoc (adj (D.nt v)), Tl, Tl, fres, aA, ntres, add_zero, add_assoc, add_assoc, ← map_add, ← map_add]`. Conclude with `congrArg (fun Z => D.t v s + T Z) (alg_id _ _ _ _ _ n3)`. Use `show IsUp (adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)))`. Rewrite using `[key]`. Conclude with `isUp_add (D.t_up v s) (Tu _ (isUp_mul u2 u1))`.

Establish `c1` using `D.rt_cont a b N`. Establish `c2 : IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal A ^ N) (T ((h s).1 * rb s) a b)` using `((b1.comp Subtype.val).mul lc).comp fun Y => Ideal.Quotient.mk (maximalIdeal A ^ N) (T Y a b)`. Establish `c3` using `c1.sub c2`. Use `c3 using 2 with s` and compare the differences between its conclusion and the goal. Conclude with `map_sub _ _ _`.

Use `show (D.nt v + T _).map p = _`. Rewrite using `[Matrix.map_add _ (map_add p), Tp, add_zero, D.nt_map]`.
-/
theorem UpperTheory.V.Ws.X1.obCor :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∀ (rb : Γ →* M4 (ResidueField Λ)) (nb : V → M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), (∀ g, (r g).map (res Λ R) = rb g) → (∀ v, (n v).map (res Λ R) = nb v) → ∀ (D : SL loc ν r n p) (μ : ResidueField Λ → A), (∀ c d, μ (c + d) = μ c + μ d) → (∀ (a : A) c, μ (res Λ A a * c) = a * μ c) → (∀ c, p (μ c) = 0) → ∀ x ∈ Fr.continuousCoboundaries2 loc (adSp rb hb) (fun v => bor (nb v)), (∀ s t, D.om s t = ((x.1 (s, t)).1 * rb (s * t)).map μ) → (∀ v s, D.de v s = ((x.2 v s).1 * rb (loc v s)).map μ) → WLift loc ν r n p := by
  intro Λ _ _ _ _ Γ V _ _ _ Gv _ _ _ loc hloc A R _ _ _ _ _ _ p hp hs ν r n hν hW hc rb nb hb hr hn D μ m1 m2 m3
    x hx x1 x2
  obtain ⟨T, T0, Tl, Tr, Ta, Tu⟩ := exists_strictHenselian_absolutely_closed_local_ring (res Λ A) μ m1 m2
  simp only [T0, SL.om, SL.de] at x1 x2
  have lc := rb_lc r rb hc hr
  obtain ⟨h, y, b1, b3, b4⟩ := hx
  obtain ⟨class_group_mod_eq_torsion, -, gA3, -, -, gA6, -⟩ := grp A
  obtain ⟨gR1, -, -, -, -, gR6, -⟩ := grp R
  obtain ⟨gk1, -⟩ := grp (ResidueField Λ)
  have aA : ∀ X : M4 A, (adj X).map (res Λ A) = adj (X.map (res Λ A)) := fun X =>
    (gA6 _ (res Λ A : A →+* ResidueField Λ) X).symm
  have aR : ∀ X : M4 R, (adj X).map (res Λ R) = adj (X.map (res Λ R)) := fun X =>
    (gR6 _ (res Λ R : R →+* ResidueField Λ) X).symm
  have mR : ∀ X Y : M4 R, (X * Y).map (res Λ R) = X.map (res Λ R) * Y.map (res Λ R) := fun X Y =>
    Matrix.map_mul (f := (res Λ R : R →+* ResidueField Λ))
  have Tp : ∀ Y, (T Y).map p = 0 := fun Y => by
    rw [← T0]; ext a b; exact m3 _
  have Tres : ∀ Y, (T Y).map (res Λ A) = 0 := fun Y => by
    rw [← T0]; ext a b
    show res Λ A (μ _) = 0
    rw [← res_map p, m3, map_zero]
  have TT : ∀ Y Y', T Y * T Y' = 0 := fun Y Y' => by rw [Tl, Tres, zero_mul, map_zero]
  have rtres : ∀ s, (D.rt s).map (res Λ A) = rb s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← hr, ← D.rt_map, Matrix.map_apply, Matrix.map_apply]
  have ntres : ∀ v, (D.nt v).map (res Λ A) = nb v := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← hn, ← D.nt_map, Matrix.map_apply, Matrix.map_apply]
  have pert : ∀ (c : A) (g : M4 A) (Y : M4 (ResidueField Λ)), IsGSp c g → Y ∈ sp4 (ResidueField Λ) →
      IsGSp c (g + T (Y * g.map (res Λ A))) := fun c g Y hg hY => by
    have hY' : adj Y = -Y := hY
    unfold IsGSp at *
    rw [gA3, Ta, gk1, hY', add_mul, mul_add, mul_add, TT, Tl, Tr, hg, aA]
    simp only [mul_neg, neg_mul, map_neg, mul_assoc]
    abel
  have inv1 : ∀ s, rb s * rb s⁻¹ = 1 := fun s => by rw [← map_mul, mul_inv_cancel, map_one]
  have inv2 : ∀ s, rb s⁻¹ * rb s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  set f : Γ → M4 A := fun s => D.rt s - T ((h s).1 * rb s) with hf
  have fH : ∀ s, IsGSp (algebraMap Λ A (ν s)) (f s) := fun s => by
    have := pert _ _ _ (D.rt_mult s) (-h s).2
    rw [rtres, Submodule.coe_neg, neg_mul, map_neg, ← sub_eq_add_neg] at this
    exact this
  have fmul : ∀ s t, f (s * t) = f s * f t := fun s t => by
    have e := x1 s t
    rw [b3, sub_eq_iff_eq_add] at e
    have e' : ((dOne (adSp rb hb) h (s, t)).1 : M4 _) * rb (s * t) =
        (h s).1 * rb s * rb t + rb s * ((h t).1 * rb t) - (h (s * t)).1 * rb (s * t) := by
      show ((h s).1 + rb s * (h t).1 * rb s⁻¹ - (h (s * t)).1) * rb (s * t) = _
      rw [sub_mul, add_mul, map_mul, mul_assoc (rb s * (h t).1), ← mul_assoc (rb s⁻¹), inv2, one_mul]
      simp only [mul_assoc]
    rw [hf]
    simp only
    rw [sub_mul, mul_sub, mul_sub, TT, Tl, Tr, rtres, rtres, e, e', map_sub, map_add]
    abel
  have fone : f 1 = 1 := by
    have hu : adj (f 1) * f 1 = 1 := by
      have := fH 1
      unfold IsGSp at this
      rw [this]; simp
    have := fmul 1 1
    rw [mul_one] at this
    calc f 1 = adj (f 1) * f 1 * f 1 := by rw [hu, one_mul]
      _ = 1 := by rw [mul_assoc, ← this, hu]
  have fp : ∀ s, (f s).map p = r s := fun s => by
    rw [hf]
    simp only
    rw [Matrix.map_sub _ (map_sub p), Tp, D.rt_map, sub_zero]
  have fres : ∀ s, (f s).map (res Λ A) = rb s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← hr, ← fp, Matrix.map_apply, Matrix.map_apply]
  refine ⟨{ toFun := f, map_one' := fone, map_mul' := fmul }, fun v => D.nt v + T ((y v).1 * nb v),
    ⟨fH, fun v => ?_, fun v s => ?_⟩, fun a b N => ?_, fp, fun v => ?_⟩
  · have := pert _ _ _ (D.nt_sp v) (y v).2
    rwa [ntres] at this
  · have n1 : adj (D.nt v) * D.nt v = 1 := by
      have := D.nt_sp v
      unfold IsGSp at this
      rw [this, one_smul]
    have n2 : adj (nb v) * nb v = 1 := by
      rw [← ntres, ← aA]
      have := congrArg (fun X : M4 A => X.map (res Λ A : A →+* ResidueField Λ)) n1
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    have n3 : nb v * adj (nb v) = 1 := mul_eq_one_comm.1 n2
    have u1 : IsUp (adj (nb v) * rb (loc v s) * nb v) := fun i j hij => by
      rw [← hn, ← hr, ← aR, ← mR, ← mR, Matrix.map_apply, hW.flag v s i j hij, map_zero]
    have u2 : IsUp (adj (nb v) * ((x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1)))
      * nb v) := b4 v s
    set B := (x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1)) with hB
    have e := x2 v s
    rw [sub_eq_iff_eq_add] at e
    have hy : adj (y v).1 = -(y v).1 := (y v).2
    have e1 : f (loc v s) = D.nt v * D.t v s * adj (D.nt v) +
        T (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s))) := by
      have : B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s)) =
          (x.2 v s).1 * rb (loc v s) - (h (loc v s)).1 * rb (loc v s) := by
        rw [hB, sub_mul, sub_mul, sub_mul, mul_assoc _ _ (rb (loc v s)), inv2, mul_one]
        abel
      rw [this, map_sub, hf]
      simp only
      rw [e]
      abel
    have e2 : adj (D.nt v) * f (loc v s) * D.nt v = D.t v s +
        T (adj (nb v) * (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s))) * nb v) := by
      rw [e1, mul_add, add_mul, Tl, Tr, aA, ntres]
      congr 1
      rw [← mul_assoc, ← mul_assoc, n1, one_mul, mul_assoc, n1, mul_one]
    have key : adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)) =
        D.t v s + T ((adj (nb v) * B * nb v) * (adj (nb v) * rb (loc v s) * nb v)) := by
      rw [gA3, Ta, gk1, hy, add_mul, add_mul, mul_add, mul_add, e2, Tr (f _), TT, Tr (D.nt v),
        mul_assoc (adj (D.nt v)), Tl, Tl, fres, aA, ntres, add_zero, add_assoc, add_assoc, ← map_add, ← map_add]
      exact congrArg (fun Z => D.t v s + T Z) (alg_id _ _ _ _ _ n3)
    show IsUp (adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)))
    rw [key]
    exact isUp_add (D.t_up v s) (Tu _ (isUp_mul u2 u1))
  · have c1 := D.rt_cont a b N
    have c2 : IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal A ^ N) (T ((h s).1 * rb s) a b) :=
      ((b1.comp Subtype.val).mul lc).comp fun Y => Ideal.Quotient.mk (maximalIdeal A ^ N) (T Y a b)
    have c3 := c1.sub c2
    convert c3 using 2 with s
    exact map_sub _ _ _
  · show (D.nt v + T _).map p = _
    rw [Matrix.map_add _ (map_add p), Tp, add_zero, D.nt_map]

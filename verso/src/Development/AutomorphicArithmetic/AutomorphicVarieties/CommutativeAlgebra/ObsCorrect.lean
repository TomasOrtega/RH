import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CocycleNormalForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhSmall
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Set `m : k →+ A` to `AddMonoidHom.mk' μ h1`. Establish `h3 : ∀ (a : A) c, m (π a * c) = a * m c` using `h2`. Use `⟨m.mapMatrix, fun Y => rfl, fun M Y => ?_, fun M Y => ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Simplify using `only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, h3]`.

Use extensionality with `a b`. Simplify using `only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (Y a c), h3, mul_comm]`.
-/
private theorem exists_strictHenselian_absolutely_closed_local_ring {k A ι : Type} [CommRing k] [CommRing A] [Fintype ι] (π : A → k) (μ : k → A)
    (h1 : ∀ c d, μ (c + d) = μ c + μ d) (h2 : ∀ (a : A) c, μ (π a * c) = a * μ c) :
    ∃ T : Matrix ι ι k →+ Matrix ι ι A, (∀ Y, Y.map μ = T Y) ∧
      (∀ (M : Matrix ι ι A) Y, M * T Y = T (M.map π * Y)) ∧
      ∀ (M : Matrix ι ι A) Y, T Y * M = T (Y * M.map π) := by
  let m : k →+ A := AddMonoidHom.mk' μ h1
  have h3 : ∀ (a : A) c, m (π a * c) = a * m c := h2
  refine ⟨m.mapMatrix, fun Y => rfl, fun M Y => ?_, fun M Y => ?_⟩
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, h3]
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm (Y a c), h3, mul_comm]

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `s`. Establish `: ∀ a b, ∀ᶠ t in nhds s, rbar t a b = rbar s a b` using `fun a b => by filter_upwards [(r.cont a b 1).eventually_eq s] with t ht`. Rewrite `ht` using `[Ideal.Quotient.eq, pow_one, ← res_eq_zero_iff O, map_sub, r.red, r.red, sub_eq_zero]`. Conclude with `ht`.

Use `filter_upwards [Filter.eventually_all.2 fun a => Filter.eventually_all.2 (this a)] with t ht`. Use extensionality with `a b`. Conclude with `ht a b`.
-/
private theorem rbar_lc {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ]
    [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} {R : Type} [CommRing R] [Algebra O R]
    [IsCO O R] (r : Lift O rbar R) : IsLocallyConstant fun s => rbar s := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ a b, ∀ᶠ t in nhds s, rbar t a b = rbar s a b := fun a b => by
    filter_upwards [(r.cont a b 1).eventually_eq s] with t ht
    rw [Ideal.Quotient.eq, pow_one, ← res_eq_zero_iff O, map_sub, r.red, r.red, sub_eq_zero] at ht
    exact ht
  filter_upwards [Filter.eventually_all.2 fun a => Filter.eventually_all.2 (this a)] with t ht
  ext a b
  exact ht a b

/- English proof (translation)
Introduce `O _ _ _ _ ι X _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar h0 F L hN hL B _ _ _ ρ A _ _ _ R _ _ _ p hp hs μ m1 m2 m3 i r rt t1 t2 t3 α a1 a2 rq q1 q2 q3 j x hx x1 x2 x3`. Take `⟨T, T0, Tl, Tr⟩` from `exists_strictHenselian_absolutely_closed_local_ring (ι := ι) (res O A) μ m1 m2`. Simplify using `only [T0] at x1 x2 x3`. Establish `lc` using `rbar_lc r0`. Establish `ad : ∀ s (Y : Φ.gw (ResidueField O) j), (FormData.adRep hbar j s Y).1 = rbar s * Y.1 * rbar s⁻¹` using `fun _ _ => rfl`.

Take `⟨h, y, b1, b2, b3, b4, b5⟩` from `cocycle_normal_form _ _ _ F (FormData.adRep hbar j) (fun m => by`. Use `IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective` and prove the remaining obligations. Conclude with `(lc.comp (· * m.1)).mul (lc.comp_continuous continuous_inv))`. Use the proof step `(fun q n hn m => Subtype.ext (by`. Rewrite using `[ad, ← map_inv, hN q n hn, hN q _ (inv_mem hn), one_mul, mul_one])) x hx`.

Establish `Tp : ∀ Y, (T Y).map p = 0` using `fun Y => by`. Rewrite using `[← T0]`. Use extensionality with `a b`. Conclude with `m3 _`. Establish `Tres : ∀ Y, (T Y).map (res O A) = 0` using `fun Y => by`.

Rewrite using `[← T0]`. Use extensionality with `a b`. Use `show res O A (μ _) = 0`. Rewrite using `[← res_map p, m3, map_zero]`. Establish `TT : ∀ Y Y', T Y * T Y' = 0` using `fun Y Y' => by rw [Tl, Tres, zero_mul, map_zero]`.

Establish `rtres : ∀ s, (rt s).map (res O A) = rbar s` using `fun s => by`. Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, ← res_map p, ← r.red, ← t3, Matrix.map_apply]`. Establish `r0res : ∀ s, ((r0.hom s).map (algebraMap O A)).map (res O A) = rbar s` using `fun s => by`. Use extensionality with `a b`.

Rewrite using `[Matrix.map_apply, Matrix.map_apply, ← r0.red]`. Conclude with `res_map (Algebra.ofId O A) _`. Establish `ρres : ∀ v s, (((ρ v).hom s).map i).map (res O A) = rbar (F.φ v s)` using `fun v s => by`. Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, Matrix.map_apply, res_map, (ρ v).red]`.

Both sides reduce to the same expression. Establish `Jres : (Φ.JR A).map (res O A) = Φ.JR (ResidueField O)`. Use extensionality with `a b`. Simplify using `[FormData.JR]`. Establish `Tg : ∀ Y : Φ.gw (ResidueField O) j, T Y.1 ∈ Φ.g A` using `fun Y => by`.

Take `⟨⟨y1, y2⟩, -⟩` from `Y.2`. Use `⟨?_, fun a b e => ?_⟩` and prove the remaining obligations. Establish `: (T Y.1).transpose = T Y.1.transpose` using `by rw [← T0, ← T0, Matrix.transpose_map]`. Rewrite using `[this, Tl, Tr, Jres, ← map_add, y1, map_zero]`. Establish `: T 0 a b = 0` using `by rw [map_zero]; rfl`.

Rewrite using `[← T0, Matrix.map_apply, y2 a b e, ← this, ← T0]`. Both sides reduce to the same expression. Take `⟨-, -, s3⟩` from `hh_small O ι X w Φ h2 A R p hp hs`. Take `⟨-, -, g3, -⟩` from `hh_group O ι X w Φ A`. Establish `inv1 : ∀ s, rbar s * rbar s⁻¹ = 1` using `fun s => by rw [← map_mul, mul_inv_cancel, map_one]`.

Establish `inv2 : ∀ s, rbar s⁻¹ * rbar s = 1` using `fun s => by rw [← map_mul, inv_mul_cancel, map_one]`. Use `set f : Γ → Matrix ι ι A := fun s => rt s - T ((h s).1 * rbar s) with hf`. Establish `fH : ∀ s, Φ.HH (f s * (r0.hom s⁻¹).map (algebraMap O A))` using `fun s => by`. Use `s3 _ _ (t1 s) (Tg (-h s)) (Tp _)` as an intermediate fact. Rewrite using `[hf]`.

Simplify using `only`. Rewrite using `[sub_mul, Tr, r0res, mul_assoc, inv1, mul_one, sub_eq_add_neg, ← map_neg]`. Conclude with `this`. Establish `fmul : ∀ s t, f (s * t) = f s * f t` using `fun s t => by`. Establish `e` using `x1 s t`.

Rewrite `e` using `[b3, sub_eq_iff_eq_add]`. Establish `e' : ((dOne (FormData.adRep hbar j) h (s, t)).1 : Matrix ι ι _) * rbar (s * t) = (h s).1 * rbar s * rbar t + rbar s * ((h t).1 * rbar t) - (h (s * t)).1 * rbar (s * t)` using `by show ((h s).1 + rbar s * (h t).1 * rbar s⁻¹ - (h (s * t)).1) * rbar (s * t) = _`. Rewrite using `[sub_mul, add_mul, map_mul, mul_assoc (rbar s * (h t).1), ← mul_assoc (rbar s⁻¹), inv2, one_mul]`. Simplify using `only [mul_assoc]`. Rewrite using `[hf]`.

Simplify using `only`. Rewrite using `[sub_mul, mul_sub, mul_sub, TT, Tl, Tr, rtres, rtres, e, e', map_sub, map_add]`. Normalize the expressions using the abelian group laws. Establish `fone : f 1 = 1`. Take `⟨u, -, hu, -⟩` from `g3 _ (fH 1)`.

Rewrite `hu` using `[inv_one, map_one, Matrix.map_one _ (map_zero _) (map_one _), mul_one]`. Use `fmul 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `fp : ∀ s, (f s).map p = r.hom s` using `fun s => by`.

Rewrite using `[hf]`. Simplify using `only`. Rewrite using `[Matrix.map_sub _ (map_sub p), Tp, t3, sub_zero]`. Set `r' : Lift O rbar A` to `{ hom := { toFun := f, map_one' := fone, map_mul' := fmul } cont := fun a b N => by`. Establish `c1` using `t2 a b N`.

Establish `c2 : IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal A ^ N) (T ((h s).1 * rbar s) a b)` using `((b1.comp Subtype.val).mul lc).comp fun Y => Ideal.Quotient.mk (maximalIdeal A ^ N) (T Y a b)`. Establish `c3` using `c1.sub c2`. Use `c3 using 2 with s` and compare the differences between its conclusion and the goal. Conclude with `map_sub _ _ _`. Use `red := fun s a b => by`.

Use `congrFun (congrFun (fp s) a) b` as an intermediate fact. Rewrite using `[← r.red, ← this, Matrix.map_apply, res_map]`. Use `rfl }`. Establish `r'p : r'.map p = r`. Use extensionality with `s a b`.

Conclude with `congrFun (congrFun (fp s) a) b`. Use `⟨r', fun v => α v + T (y v).1, ⟨fH, fun q => ?_, fun v => s3 _ _ (a1 v) (Tg _) (Tp _), ?_, fun v s => ?_⟩, r'p, fun v => ?_⟩` and prove the remaining obligations. Use `((hL q).tangent A R p hp hs (rq q) (r'.comap (F.ψ q) (F.hψ q)) (q1 q) (fun s => ?_) ?_ (q2 q)).2 fun n hn => ?_` and prove the remaining obligations. Use `fH (F.ψ q s)` as an intermediate fact. Rewrite `this` using `[← map_inv]`.

Conclude with `this`. Rewrite using `[q3, ← r'p]`. Both sides reduce to the same expression. Establish `e` using `x3 q n`. Rewrite `e` using `[b5 q n hn]`.

Use `show rt (F.ψ q n) - T _ = _`. Rewrite using `[← e, sub_sub_cancel]`. Simplify using `only [a2, b2]`. Simplify using the standard rewrite rules. Establish `e` using `x2 v s`.

Rewrite `e` using `[b4, sub_eq_iff_eq_add]`. Establish `e' : ((h (F.φ v s) - (FormData.adRep hbar j (F.φ v s) (y v) - y v)).1 : Matrix ι ι _) * rbar (F.φ v s) = (h (F.φ v s)).1 * rbar (F.φ v s) - (rbar (F.φ v s) * (y v).1 - (y v).1 * rbar (F.φ v s))` using `by show ((h (F.φ v s)).1 - (rbar (F.φ v s) * (y v).1 * rbar (F.φ v s)⁻¹ - (y v).1)) * rbar (F.φ v s) = _`. Rewrite using `[sub_mul, sub_mul, mul_assoc, inv2, mul_one]`. Use `show (rt (F.φ v s) - T _) * (α v + T _) = (α v + T _) * _`. Rewrite using `[sub_mul, mul_add, mul_add, add_mul, TT, Tl, Tr, Tr, rtres, ρres, (a1 v).2.2, mul_one, e, e', map_sub, map_sub]`.

Normalize the expressions using the abelian group laws. Use `show (α v + T _).map p = _`. Rewrite using `[Matrix.map_add _ (map_add p), Tp, add_zero]`.
-/
theorem UpperTheory.V.Alg.obs_correct :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) →
          ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B) (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : A →ₐ[O] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ →
          ∀ (μ : ResidueField O → A), (∀ c d, μ (c + d) = μ c + μ d) → (∀ (a : A) c, μ (res O A a * c) = a * μ c) → (∀ c, p (μ c) = 0) →
          ∀ (i : B →ₐ[O] A) (r : Lift O rbar R) (rt : Γ → Matrix ι ι A), (∀ s, Φ.HH (rt s * (r0.hom s⁻¹).map (algebraMap O A))) → (∀ a b, AdicCont (maximalIdeal A) fun s => rt s a b) → (∀ s, (rt s).map p = r.hom s) →
          ∀ (α : F.T → Matrix ι ι A), (∀ v, Φ.HH (α v)) → α F.v0 = 1 →
          ∀ (rq : ∀ q, Lift O (rbar.comp (F.ψ q)) A), (∀ q, Φ.InH (r0.hom.comp (F.ψ q)) A (rq q)) → (∀ q, L q A (rq q)) → (∀ q, (rq q).map p = r.comap (F.ψ q) (F.hψ q)) →
          ∀ (j : X), ∀ x ∈ F.framedTwoCoboundaries (FormData.adRep hbar j), (∀ s t, rt s * rt t - rt (s * t) = ((x.1 (s, t)).1 * rbar (s * t)).map μ) → (∀ v s, rt (F.φ v s) * α v - α v * ((ρ v).hom s).map i = ((x.2.1 v s).1 * rbar (F.φ v s)).map μ) → (∀ q s, rt (F.ψ q s) - (rq q).hom s = ((x.2.2 q s).1 * rbar (F.ψ q s)).map μ) →
          ∃ (r' : Lift O rbar A) (α' : F.T → Matrix ι ι A), IsFramed Φ r0.hom F L ρ i r' α' ∧ r'.map p = r ∧ ∀ v, (α' v).map p = (α v).map p := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar h0 F L hN hL B _ _ _ ρ A _ _ _ R _ _ _ p hp hs μ m1 m2 m3
    i r rt t1 t2 t3 α a1 a2 rq q1 q2 q3 j x hx x1 x2 x3
  obtain ⟨T, T0, Tl, Tr⟩ := exists_strictHenselian_absolutely_closed_local_ring (ι := ι) (res O A) μ m1 m2
  simp only [T0] at x1 x2 x3
  have lc := rbar_lc r0
  have ad : ∀ s (Y : Φ.gw (ResidueField O) j), (FormData.adRep hbar j s Y).1 = rbar s * Y.1 * rbar s⁻¹ :=
    fun _ _ => rfl
  obtain ⟨h, y, b1, b2, b3, b4, b5⟩ := cocycle_normal_form _ _ _ F (FormData.adRep hbar j) (fun m => by
      refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      exact (lc.comp (· * m.1)).mul (lc.comp_continuous continuous_inv))
    (fun q n hn m => Subtype.ext (by
      rw [ad, ← map_inv, hN q n hn, hN q _ (inv_mem hn), one_mul, mul_one])) x hx
  have Tp : ∀ Y, (T Y).map p = 0 := fun Y => by
    rw [← T0]; ext a b; exact m3 _
  have Tres : ∀ Y, (T Y).map (res O A) = 0 := fun Y => by
    rw [← T0]; ext a b
    show res O A (μ _) = 0
    rw [← res_map p, m3, map_zero]
  have TT : ∀ Y Y', T Y * T Y' = 0 := fun Y Y' => by rw [Tl, Tres, zero_mul, map_zero]
  have rtres : ∀ s, (rt s).map (res O A) = rbar s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← r.red, ← t3, Matrix.map_apply]
  have r0res : ∀ s, ((r0.hom s).map (algebraMap O A)).map (res O A) = rbar s := fun s => by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, ← r0.red]
    exact res_map (Algebra.ofId O A) _
  have ρres : ∀ v s, (((ρ v).hom s).map i).map (res O A) = rbar (F.φ v s) := fun v s => by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, res_map, (ρ v).red]
    rfl
  have Jres : (Φ.JR A).map (res O A) = Φ.JR (ResidueField O) := by
    ext a b
    simp [FormData.JR]
  have Tg : ∀ Y : Φ.gw (ResidueField O) j, T Y.1 ∈ Φ.g A := fun Y => by
    obtain ⟨⟨y1, y2⟩, -⟩ := Y.2
    refine ⟨?_, fun a b e => ?_⟩
    · have : (T Y.1).transpose = T Y.1.transpose := by rw [← T0, ← T0, Matrix.transpose_map]
      rw [this, Tl, Tr, Jres, ← map_add, y1, map_zero]
    · have : T 0 a b = 0 := by rw [map_zero]; rfl
      rw [← T0, Matrix.map_apply, y2 a b e, ← this, ← T0]
      rfl
  obtain ⟨-, -, s3⟩ := hh_small O ι X w Φ h2 A R p hp hs
  obtain ⟨-, -, g3, -⟩ := hh_group O ι X w Φ A
  have inv1 : ∀ s, rbar s * rbar s⁻¹ = 1 := fun s => by rw [← map_mul, mul_inv_cancel, map_one]
  have inv2 : ∀ s, rbar s⁻¹ * rbar s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  set f : Γ → Matrix ι ι A := fun s => rt s - T ((h s).1 * rbar s) with hf
  have fH : ∀ s, Φ.HH (f s * (r0.hom s⁻¹).map (algebraMap O A)) := fun s => by
    have := s3 _ _ (t1 s) (Tg (-h s)) (Tp _)
    rw [hf]
    simp only
    rw [sub_mul, Tr, r0res, mul_assoc, inv1, mul_one, sub_eq_add_neg, ← map_neg]
    exact this
  have fmul : ∀ s t, f (s * t) = f s * f t := fun s t => by
    have e := x1 s t
    rw [b3, sub_eq_iff_eq_add] at e
    have e' : ((dOne (FormData.adRep hbar j) h (s, t)).1 : Matrix ι ι _) * rbar (s * t) =
        (h s).1 * rbar s * rbar t + rbar s * ((h t).1 * rbar t) - (h (s * t)).1 * rbar (s * t) := by
      show ((h s).1 + rbar s * (h t).1 * rbar s⁻¹ - (h (s * t)).1) * rbar (s * t) = _
      rw [sub_mul, add_mul, map_mul, mul_assoc (rbar s * (h t).1), ← mul_assoc (rbar s⁻¹), inv2, one_mul]
      simp only [mul_assoc]
    rw [hf]
    simp only
    rw [sub_mul, mul_sub, mul_sub, TT, Tl, Tr, rtres, rtres, e, e', map_sub, map_add]
    abel
  have fone : f 1 = 1 := by
    obtain ⟨u, -, hu, -⟩ := g3 _ (fH 1)
    rw [inv_one, map_one, Matrix.map_one _ (map_zero _) (map_one _), mul_one] at hu
    have := fmul 1 1
    rw [mul_one] at this
    calc f 1 = f 1 * (f 1 * u) := by rw [hu, mul_one]
      _ = 1 := by rw [← mul_assoc, ← this, hu]
  have fp : ∀ s, (f s).map p = r.hom s := fun s => by
    rw [hf]
    simp only
    rw [Matrix.map_sub _ (map_sub p), Tp, t3, sub_zero]
  let r' : Lift O rbar A :=
    { hom := { toFun := f, map_one' := fone, map_mul' := fmul }
      cont := fun a b N => by
        have c1 := t2 a b N
        have c2 : IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal A ^ N) (T ((h s).1 * rbar s) a b) :=
          ((b1.comp Subtype.val).mul lc).comp fun Y => Ideal.Quotient.mk (maximalIdeal A ^ N) (T Y a b)
        have c3 := c1.sub c2
        convert c3 using 2 with s
        exact map_sub _ _ _
      red := fun s a b => by
        have := congrFun (congrFun (fp s) a) b
        rw [← r.red, ← this, Matrix.map_apply, res_map]
        rfl }
  have r'p : r'.map p = r := by
    ext s a b
    exact congrFun (congrFun (fp s) a) b
  refine ⟨r', fun v => α v + T (y v).1, ⟨fH, fun q => ?_, fun v => s3 _ _ (a1 v) (Tg _) (Tp _), ?_, fun v s => ?_⟩,
    r'p, fun v => ?_⟩
  · refine ((hL q).tangent A R p hp hs (rq q) (r'.comap (F.ψ q) (F.hψ q)) (q1 q) (fun s => ?_) ?_ (q2 q)).2
      fun n hn => ?_
    · have := fH (F.ψ q s)
      rw [← map_inv] at this
      exact this
    · rw [q3, ← r'p]
      rfl
    · have e := x3 q n
      rw [b5 q n hn] at e
      show rt (F.ψ q n) - T _ = _
      rw [← e, sub_sub_cancel]
  · simp only [a2, b2]
    simp
  · have e := x2 v s
    rw [b4, sub_eq_iff_eq_add] at e
    have e' : ((h (F.φ v s) - (FormData.adRep hbar j (F.φ v s) (y v) - y v)).1 : Matrix ι ι _) * rbar (F.φ v s) =
        (h (F.φ v s)).1 * rbar (F.φ v s) - (rbar (F.φ v s) * (y v).1 - (y v).1 * rbar (F.φ v s)) := by
      show ((h (F.φ v s)).1 - (rbar (F.φ v s) * (y v).1 * rbar (F.φ v s)⁻¹ - (y v).1)) * rbar (F.φ v s) = _
      rw [sub_mul, sub_mul, mul_assoc, inv2, mul_one]
    show (rt (F.φ v s) - T _) * (α v + T _) = (α v + T _) * _
    rw [sub_mul, mul_add, mul_add, add_mul, TT, Tl, Tr, Tr, rtres, ρres, (a1 v).2.2, mul_one, e, e', map_sub, map_sub]
    abel
  · show (α v + T _).map p = _
    rw [Matrix.map_add _ (map_add p), Tp, add_zero]

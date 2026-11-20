import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DCoord

open CategoryTheory Limits MvPolynomial

namespace UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Set `γ` to `eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j)))`. Set `Z : Fin D → MvPolynomial (Fin D) A` to `Function.update X j 1`. Set `α' : MvPolynomial (ULift.{0} (Fin D)) A →+* E` to `eval₂Hom p (fun k => s k.down)`. Set `β' : MvPolynomial (ULift.{0} (Fin D)) A →+* MvPolynomial (Fin D) A` to `eval₂Hom C (fun k => X j * Z k.down)`. Establish `hα' : α'.Etale`.

Establish `e1 : α' = (eval₂Hom p s).comp (MvPolynomial.renameEquiv A Equiv.ulift).toRingEquiv.toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[α']`. Introduce `k`.

Simplify using `[α']`. Rewrite using `[e1]`. Conclude with `RingHom.Etale.respectsIso.2 _ _ hφ`. Establish `hker : ∀ q ∈ Ideal.span (insert (X j - 1 : MvPolynomial (Fin D) E) (Set.range fun k => C (s k) - C (s j) * X k)), eval₂Hom ψ y q = 0`. Introduce `q hq`.

Rewrite `hq` using `[← ker]`. Conclude with `hq`. Establish `hyj : y j = 1`. Establish `h0` using `hker _ (Ideal.subset_span (Set.mem_insert _ _))`. Simplify using `only [map_sub, eval₂Hom_X', map_one] at h0`.

Conclude with `sub_eq_zero.1 h0`. Establish `hyk : ∀ k, ψ (s k) = ψ (s j) * y k`. Introduce `k`. Establish `h0` using `hker _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩))`. Simplify using `only [map_sub, map_mul, eval₂Hom_C, eval₂Hom_X'] at h0`.

Conclude with `sub_eq_zero.1 h0`. Establish `hγX : ∀ k, k ≠ j → γ (X k) = y k`. Introduce `k hk`. Simplify using `[γ, Function.update_of_ne hk]`. Establish `hγXj : γ (X j) = ψ (s j)` using `by simp [γ]`.

Establish `hγZ : ∀ k, γ (X j * Z k) = ψ (s k)`. Introduce `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `[Z, hγXj]`.

Rewrite using `[map_mul, hγXj]`. Simplify using `only [Z, Function.update_of_ne hk]`. Rewrite using `[hγX k hk, hyk k]`. Establish `hcompat : ∀ t, ψ (α' t) = γ (β' t)`. Introduce `t`.

Establish `h0 : ψ.comp α' = γ.comp β'`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[α', β', γ]`. Introduce `k`.

Simplify using `only [RingHom.comp_apply, α', β', eval₂Hom_X']`. Conclude with `(hγZ k.down).symm`. Conclude with `RingHom.congr_fun h0 t`. Use `letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) E := α'.toAlgebra`. Use `letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) := β'.toAlgebra`.

Use `letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) B := (γ.comp β').toAlgebra`. Establish `hbc` using `RingHom.Etale.isStableUnderBaseChange.tensorProduct (MvPolynomial (Fin D) A) (R := MvPolynomial (ULift.{0} (Fin D)) A) (S := E) hα'`. Set `fA : MvPolynomial (Fin D) A →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] B` to `{ γ with commutes' := fun _ => rfl }`. Set `gA : E →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] B` to `{ ψ with commutes' := fun t => hcompat t }`. Set `F` to `(Algebra.TensorProduct.lift fA gA (fun _ _ => Commute.all _ _)).toRingHom`.

Establish `hF : ∀ a e, F (TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) a e) = γ a * ψ e`. Introduce `a e`. Simplify using `[F, fA, gA]`. Establish `hT : ∀ t, TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (α' t) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (β' t) (1 : E)`. Introduce `t`.

Establish `h1 : α' t = t • (1 : E)`. Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Establish `h2 : β' t = t • (1 : MvPolynomial (Fin D) A)`. Rewrite using `[Algebra.smul_def, mul_one]`.

Both sides reduce to the same expression. Rewrite using `[h1, h2, TensorProduct.smul_tmul]`. Establish `hTs : ∀ k, TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (s k) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (X j * Z k) (1 : E)`. Introduce `k`. Simplify `hT (X ⟨k⟩)` using `[α', β']`.

Set `G0 : MvPolynomial (Fin D) E →+* TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E` to `eval₂Hom (Algebra.TensorProduct.includeRight : E →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E).toRingHom (fun k => TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E))`. Establish `hG0C : ∀ e, G0 (C e) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) e`. Introduce `e`. Simplify using `[G0]`. Establish `hG0X : ∀ k, G0 (X k) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E)`.

Introduce `k`. Simplify using `[G0]`. Establish `hG0 : RingHom.ker (eval₂Hom ψ y) ≤ RingHom.ker G0`. Rewrite using `[ker, Ideal.span_le]`. Introduce and unpack `q (rfl | ⟨k, rfl⟩)`.

Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hG0X]`. Simplify using `[Z, Algebra.TensorProduct.one_def]`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, hG0C, hG0C, hG0X, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hTs k]`. Establish `h3 : TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (s j) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E) * TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (s j)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.

Rewrite using `[h3, hTs j, Algebra.TensorProduct.tmul_mul_tmul]`. Simplify using `[Z, mul_comm]`. Set `G : B →+* TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E` to `(Ideal.Quotient.lift _ G0 (fun q hq => hG0 hq)).comp (RingHom.quotientKerEquivOfSurjective surj).symm.toRingHom`. Establish `hG : ∀ q, G (eval₂Hom ψ y q) = G0 q`. Introduce `q`.

Establish `h4 : (RingHom.quotientKerEquivOfSurjective surj).symm (eval₂Hom ψ y q) = Ideal.Quotient.mk _ q`. Rewrite using `[RingEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Use `show Ideal.Quotient.lift _ G0 (fun q hq => hG0 hq) ((RingHom.quotientKerEquivOfSurjective surj).symm (eval₂Hom ψ y q)) = G0 q`. Rewrite using `[h4]`.

Both sides reduce to the same expression. Establish `hGψ : ∀ e, G (ψ e) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) e`. Introduce `e`. Rewrite using `[← eval₂Hom_C ψ y e, hG, hG0C]`. Establish `hFG : F.comp G = RingHom.id B`.

Establish `h5 : F.comp G0 = eval₂Hom ψ y`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `e`. Rewrite using `[RingHom.comp_apply, hG0C, hF, map_one, one_mul, eval₂Hom_C]`. Introduce `k`.

Rewrite using `[RingHom.comp_apply, hG0X, hF, map_one, mul_one, eval₂Hom_X']`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `[Z, hyj]`. Simplify using `only [Z, Function.update_of_ne hk]`.

Conclude with `hγX k hk`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `b`. Take `⟨q, rfl⟩` from `surj b`. Rewrite using `[RingHom.comp_apply, hG, RingHom.id_apply]`.

Conclude with `RingHom.congr_fun h5 q`. Establish `hGγ : ∀ a, G (γ a) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) a (1 : E)`. Establish `h6 : G.comp γ = Algebra.TensorProduct.includeLeftRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`.

Establish `h7` using `hT (C c)`. Simplify using `only [α', β', eval₂Hom_C] at h7`. Simplify using `only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]`. Simplify using `only [γ, eval₂Hom_C, RingHom.comp_apply]`. Rewrite using `[hGψ, h7]`.

Introduce `k`. Simplify using `only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Rewrite using `[hγXj, hGψ, hTs]`.

Simplify using `[Z]`. Rewrite using `[hγX k hk, ← eval₂Hom_X' ψ y k, hG, hG0X]`. Simplify using `only [Z, Function.update_of_ne hk]`. Introduce `a`. Conclude with `RingHom.congr_fun h6 a`.

Establish `hGF : G.comp F = RingHom.id _`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a e`. Rewrite using `[RingHom.comp_apply, hF, map_mul, RingHom.id_apply, hGγ, hGψ, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Consider the case `add x y hx hy`. Simplify using `only [RingHom.comp_apply, RingHom.id_apply, map_add] at hx hy ⊢`. Rewrite using `[hx, hy]`.

Set `e` to `RingEquiv.ofRingHom F G hFG hGF`. Establish `h8` using `RingHom.Etale.respectsIso.1 _ e hbc`. Use `h8 using 1` and compare the differences between its conclusion and the goal. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `x`.

Use `show γ x = F (algebraMap _ _ x)`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, hF, map_one, mul_one]`. Both sides reduce to the same expression.
-/
private theorem etale_chart {A E B : Type} [CommRing A] [CommRing E] [CommRing B] {D : ℕ}
    (p : A →+* E) (ψ : E →+* B) (s : Fin D → E) (y : Fin D → B) (j : Fin D)
    (hφ : (eval₂Hom p s).Etale)
    (surj : Function.Surjective (eval₂Hom ψ y))
    (ker : RingHom.ker (eval₂Hom ψ y) = Ideal.span (insert (X j - 1 : MvPolynomial (Fin D) E)
      (Set.range fun k => MvPolynomial.C (s k) - MvPolynomial.C (s j) * X k))) :
    (eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j)))).Etale := by
  classical
  let γ := eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j)))
  let Z : Fin D → MvPolynomial (Fin D) A := Function.update X j 1
  let α' : MvPolynomial (ULift.{0} (Fin D)) A →+* E := eval₂Hom p (fun k => s k.down)
  let β' : MvPolynomial (ULift.{0} (Fin D)) A →+* MvPolynomial (Fin D) A :=
    eval₂Hom C (fun k => X j * Z k.down)
  have hα' : α'.Etale := by
    have e1 : α' = (eval₂Hom p s).comp
        (MvPolynomial.renameEquiv A Equiv.ulift).toRingEquiv.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [α']
      · intro k
        simp [α']
    rw [e1]
    exact RingHom.Etale.respectsIso.2 _ _ hφ
  have hker : ∀ q ∈ Ideal.span (insert (X j - 1 : MvPolynomial (Fin D) E)
      (Set.range fun k => C (s k) - C (s j) * X k)), eval₂Hom ψ y q = 0 := by
    intro q hq
    rw [← ker] at hq
    exact hq
  have hyj : y j = 1 := by
    have h0 := hker _ (Ideal.subset_span (Set.mem_insert _ _))
    simp only [map_sub, eval₂Hom_X', map_one] at h0
    exact sub_eq_zero.1 h0
  have hyk : ∀ k, ψ (s k) = ψ (s j) * y k := by
    intro k
    have h0 := hker _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩))
    simp only [map_sub, map_mul, eval₂Hom_C, eval₂Hom_X'] at h0
    exact sub_eq_zero.1 h0
  have hγX : ∀ k, k ≠ j → γ (X k) = y k := by
    intro k hk
    simp [γ, Function.update_of_ne hk]
  have hγXj : γ (X j) = ψ (s j) := by simp [γ]
  have hγZ : ∀ k, γ (X j * Z k) = ψ (s k) := by
    intro k
    by_cases hk : k = j
    · subst hk
      simp [Z, hγXj]
    · rw [map_mul, hγXj]
      simp only [Z, Function.update_of_ne hk]
      rw [hγX k hk, hyk k]
  have hcompat : ∀ t, ψ (α' t) = γ (β' t) := by
    intro t
    have h0 : ψ.comp α' = γ.comp β' := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [α', β', γ]
      · intro k
        simp only [RingHom.comp_apply, α', β', eval₂Hom_X']
        exact (hγZ k.down).symm
    exact RingHom.congr_fun h0 t
  letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) E := α'.toAlgebra
  letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) := β'.toAlgebra
  letI : Algebra (MvPolynomial (ULift.{0} (Fin D)) A) B := (γ.comp β').toAlgebra
  have hbc := RingHom.Etale.isStableUnderBaseChange.tensorProduct (MvPolynomial (Fin D) A)
    (R := MvPolynomial (ULift.{0} (Fin D)) A) (S := E) hα'
  let fA : MvPolynomial (Fin D) A →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] B :=
    { γ with commutes' := fun _ => rfl }
  let gA : E →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] B :=
    { ψ with commutes' := fun t => hcompat t }
  let F := (Algebra.TensorProduct.lift fA gA (fun _ _ => Commute.all _ _)).toRingHom
  have hF : ∀ a e, F (TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) a e) = γ a * ψ e := by
    intro a e
    simp [F, fA, gA]
  have hT : ∀ t, TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (α' t) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (β' t) (1 : E) := by
    intro t
    have h1 : α' t = t • (1 : E) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    have h2 : β' t = t • (1 : MvPolynomial (Fin D) A) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [h1, h2, TensorProduct.smul_tmul]
  have hTs : ∀ k, TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (s k) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (X j * Z k) (1 : E) := by
    intro k
    simpa [α', β'] using hT (X ⟨k⟩)
  let G0 : MvPolynomial (Fin D) E →+* TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E :=
    eval₂Hom (Algebra.TensorProduct.includeRight :
      E →ₐ[MvPolynomial (ULift.{0} (Fin D)) A] TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E).toRingHom (fun k => TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E))
  have hG0C : ∀ e, G0 (C e) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) e := by
    intro e
    simp [G0]
  have hG0X : ∀ k, G0 (X k) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E) := by
    intro k
    simp [G0]
  have hG0 : RingHom.ker (eval₂Hom ψ y) ≤ RingHom.ker G0 := by
    rw [ker, Ideal.span_le]
    rintro q (rfl | ⟨k, rfl⟩)
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hG0X]
      simp [Z, Algebra.TensorProduct.one_def]
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, hG0C, hG0C, hG0X,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hTs k]
      have h3 : TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (s j) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (Z k) (1 : E) * TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) (s j) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h3, hTs j, Algebra.TensorProduct.tmul_mul_tmul]
      simp [Z, mul_comm]
  let G : B →+* TensorProduct (MvPolynomial (ULift.{0} (Fin D)) A) (MvPolynomial (Fin D) A) E :=
    (Ideal.Quotient.lift _ G0 (fun q hq => hG0 hq)).comp
      (RingHom.quotientKerEquivOfSurjective surj).symm.toRingHom
  have hG : ∀ q, G (eval₂Hom ψ y q) = G0 q := by
    intro q
    have h4 : (RingHom.quotientKerEquivOfSurjective surj).symm (eval₂Hom ψ y q)
        = Ideal.Quotient.mk _ q := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.lift _ G0 (fun q hq => hG0 hq)
      ((RingHom.quotientKerEquivOfSurjective surj).symm (eval₂Hom ψ y q)) = G0 q
    rw [h4]
    rfl
  have hGψ : ∀ e, G (ψ e) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) (1 : MvPolynomial (Fin D) A) e := by
    intro e
    rw [← eval₂Hom_C ψ y e, hG, hG0C]
  have hFG : F.comp G = RingHom.id B := by
    have h5 : F.comp G0 = eval₂Hom ψ y := by
      apply MvPolynomial.ringHom_ext
      · intro e
        rw [RingHom.comp_apply, hG0C, hF, map_one, one_mul, eval₂Hom_C]
      · intro k
        rw [RingHom.comp_apply, hG0X, hF, map_one, mul_one, eval₂Hom_X']
        by_cases hk : k = j
        · subst hk
          simp [Z, hyj]
        · simp only [Z, Function.update_of_ne hk]
          exact hγX k hk
    apply RingHom.ext
    intro b
    obtain ⟨q, rfl⟩ := surj b
    rw [RingHom.comp_apply, hG, RingHom.id_apply]
    exact RingHom.congr_fun h5 q
  have hGγ : ∀ a, G (γ a) = TensorProduct.tmul (MvPolynomial (ULift.{0} (Fin D)) A) a (1 : E) := by
    have h6 : G.comp γ = Algebra.TensorProduct.includeLeftRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        have h7 := hT (C c)
        simp only [α', β', eval₂Hom_C] at h7
        simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
        simp only [γ, eval₂Hom_C, RingHom.comp_apply]
        rw [hGψ, h7]
      · intro k
        simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
        by_cases hk : k = j
        · subst hk
          rw [hγXj, hGψ, hTs]
          simp [Z]
        · rw [hγX k hk, ← eval₂Hom_X' ψ y k, hG, hG0X]
          simp only [Z, Function.update_of_ne hk]
    intro a
    exact RingHom.congr_fun h6 a
  have hGF : G.comp F = RingHom.id _ := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [RingHom.comp_apply, hF, map_mul, RingHom.id_apply, hGγ, hGψ,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy =>
      simp only [RingHom.comp_apply, RingHom.id_apply, map_add] at hx hy ⊢
      rw [hx, hy]
  let e := RingEquiv.ofRingHom F G hFG hGF
  have h8 := RingHom.Etale.respectsIso.1 _ e hbc
  convert h8 using 1
  apply RingHom.ext
  intro x
  show γ x = F (algebraMap _ _ x)
  rw [Algebra.TensorProduct.algebraMap_apply, hF, map_one, mul_one]
  rfl

end UpperTheory.Gal.KunnethLefschetz.G

open UpperTheory.Gal.DifferentialFormSections in
/- English proof (translation)
Introduce `R _ Z W π D c b j`. Conclude with `UpperTheory.Gal.KunnethLefschetz.G.etale_chart _ _ c.s (b.y j) j (dCoord R Z D c) (b.surj j) (b.ker j)`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.bCoord :
    UpperTheory.Gal.KunnethLefschetz.G.BCoord := by
  intro R _ Z W π D c b j
  exact UpperTheory.Gal.KunnethLefschetz.G.etale_chart _ _ c.s (b.y j) j (dCoord R Z D c) (b.surj j) (b.ker j)

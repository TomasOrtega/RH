import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.LamSmul

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro a b _; exact ⟨1, by simp⟩`. Consider the case `succ m ih`. Introduce `a b h`.

Take `⟨c, hc⟩` from `h 0`. Take `⟨d, hd⟩` from `ih (fun i => a i.succ) (fun i => b i.succ) fun i => h _`. Use `⟨c * d, ?_⟩` and prove the remaining obligations. Rewrite using `[List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, hc, hd, smul_mul_smul_comm]`.
-/
private theorem pt_prod {R E : Type} [CommRing R] [Ring E] [Algebra R E] :
    ∀ (m : ℕ) (a b : Fin m → E), (∀ i, ∃ c : R, a i = c • b i) → ∃ c : R, (List.ofFn a).prod = c • (List.ofFn b).prod := by
  intro m
  induction m with
  | zero => intro a b _; exact ⟨1, by simp⟩
  | succ m ih =>
    intro a b h
    obtain ⟨c, hc⟩ := h 0
    obtain ⟨d, hd⟩ := ih (fun i => a i.succ) (fun i => b i.succ) fun i => h _
    refine ⟨c * d, ?_⟩
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, hc, hd, smul_mul_smul_comm]

/- English proof (translation)
Introduce `N` and use `by simp only [map_mul] exact (hf N).mul (hg N)`.
-/
private theorem pt_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x := fun N => by
  simp only [map_mul]
  exact (hf N).mul (hg N)

/- English proof (translation)
Introduce `N` and use `by simp only [map_pow] exact (hf N).comp (· ^ k)`.
-/
private theorem pt_pow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f : Γ → R}
    (hf : AdicCont I f) (k : ℕ) : AdicCont I fun x => f x ^ k := fun N => by
  simp only [map_pow]
  exact (hf N).comp (· ^ k)

/- English proof (translation)
Rewrite using `[lam_twD, twA_single, ← lamSmul, MonoidAlgebra.smul_single, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.
-/
private theorem pt_single {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (γ : G →* Aˣ) (i : ℕ) (g : G) (a : A) :
    (twD D γ).lam i (MonoidAlgebra.single g a) = (γ g : A) ^ min i n * D.lam i (MonoidAlgebra.single g a) := by
  rw [lam_twD, twA_single, ← lamSmul, MonoidAlgebra.smul_single, smul_eq_mul, mul_comm]
  rfl

/- English proof (translation)
Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single g r => rw [twA_single, h, mul_one]`.
-/
private theorem pt_id {A G : Type} [CommRing A] [Group G] (γ : G →* Aˣ) (B : Type) [CommRing B] [Algebra A B]
    (h : ∀ g, algebraMap A B (γ g) = 1) (x : MonoidAlgebra B G) : twA γ B x = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => rw [twA_single, h, mul_one]

/- English proof (translation)
Introduce `l _ F O _ _ _ n r R _ _ _ p γ hγ`. Establish `hres : ∀ g, res O R (γ g) = 1` using `fun g => by`. Establish `h` using `(res_eq_zero_iff O R _).mpr (hγ.red g)`. Rewrite `h` using `[map_sub, map_one, sub_eq_zero]`. Then use the resulting hypothesis. Use `⟨ { D := twD p.D γ ψ := fun v i => p.ψ v i * γ.comp (F.φ v) cont := fun i => ?_ red := ?_ psi := fun v i => { cont := ?_ red := fun g => ?_ mu := fun g => ?_ } P := fun i g => ?_ Ord := fun v g h => ?_ I := fun u g hg h => ?_ }, rfl, fun _ _ => rfl⟩` and prove the remaining obligations.

Simplify using `only [pt_single]`. Conclude with `pt_mul (pt_pow hγ.cont _) (p.cont i)`. Rewrite using `[← p.red]`. Use `GDet.ext fun B _ _ x => ?_` and prove the remaining obligations. Use `letI : Algebra R B := ((algebraMap (ResidueField O) B).comp (res O R : R →+* ResidueField O)).toAlgebra`.

Express the relevant statement in the definitionally equal form `p.D.D B (twA γ B x) = p.D.D B x`. Rewrite using `[pt_id γ B fun g => ?_]`. Express the relevant statement in the definitionally equal form `algebraMap (ResidueField O) B (res O R (γ g)) = 1`. Rewrite using `[hres, map_one]`. Conclude with `pt_mul (p.psi v i).cont fun N => (hγ.cont N).comp_continuous (F.φ_cont v)`.

Express the relevant statement in the definitionally equal form `res O R (p.ψ v i g * γ (F.φ v g)) = _`. Rewrite using `[map_mul, hres, mul_one]`. Conclude with `(p.psi v i).red g`. Express the relevant statement in the definitionally equal form `(p.ψ v i g : R) * γ (F.φ v g) = _`. Rewrite using `[hγ.mu v g g.2, Units.val_one, mul_one]`.

Conclude with `(p.psi v i).mu g`. Establish `h1 : F.star O R n (MonoidAlgebra.single g 1) = MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)`. Simplify using `only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]`. Establish `h2 : γ (F.conj g)⁻¹ = γ g`. Rewrite using `[map_inv]`.

Conclude with `inv_eq_of_mul_eq_one_right (hγ.conj g)`. Rewrite using `[pt_single, ← p.P, h1, pt_single, h2]`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : R, twA γ R (F.oEl v (fun i => p.ψ v i * γ.comp (F.φ v)) g) = c • F.oEl v (p.ψ v) g := by`. Simplify using `only [GFrame.oEl, map_list_prod, List.map_ofFn, Function.comp_def]`. Use `pt_prod n _ _ fun i => ⟨γ (F.φ v (g i)), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, twA_single, twA_single, smul_sub, MonoidAlgebra.smul_single, MonoidAlgebra.smul_single]`. Simplify using `[mul_comm]`. Establish `h1 : twA γ R (MonoidAlgebra.single h 1) = (γ h : R) • MonoidAlgebra.single h 1`. Rewrite using `[twA_single, MonoidAlgebra.smul_single]`. Simplify using the standard rewrite rules.

Rewrite using `[GDet.tr, lam_twD, map_mul, hc, h1, smul_mul_smul_comm, lamSmul]`. Conclude with `(congrArg _ (p.Ord v g h)).trans (mul_zero _)`. Establish `hg1 : γ g = 1` using `hγ.iu u hg.1`. Establish `h1 : twA γ R (MonoidAlgebra.single h 1) = (γ h : R) • MonoidAlgebra.single h 1`. Rewrite using `[twA_single, MonoidAlgebra.smul_single]`.

Simplify using the standard rewrite rules. Establish `h2 : twA γ R (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1`. Rewrite using `[twA_single, hg1]`. Simplify using the standard rewrite rules. Rewrite using `[GDet.tr, lam_twD, map_mul, map_sub, map_one, h1, h2, smul_mul_assoc, lamSmul]`.

Conclude with `(congrArg _ (p.I u g hg h)).trans (mul_zero _)`.
-/
theorem UpperTheory.V.Ws.H5.pairTw :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R) (γ : F.G₀ →* Rˣ), TwCh F γ → ∃ p' : Pair r R, p'.D = twD p.D γ ∧ ∀ v i, p'.ψ v i = p.ψ v i * γ.comp (F.φ v) := by
  intro l _ F O _ _ _ n r R _ _ _ p γ hγ
  have hres : ∀ g, res O R (γ g) = 1 := fun g => by
    have h := (res_eq_zero_iff O R _).mpr (hγ.red g)
    rwa [map_sub, map_one, sub_eq_zero] at h
  refine ⟨
    { D := twD p.D γ
      ψ := fun v i => p.ψ v i * γ.comp (F.φ v)
      cont := fun i => ?_
      red := ?_
      psi := fun v i =>
        { cont := ?_
          red := fun g => ?_
          mu := fun g => ?_ }
      P := fun i g => ?_
      Ord := fun v g h => ?_
      I := fun u g hg h => ?_ }, rfl, fun _ _ => rfl⟩
  · simp only [pt_single]
    exact pt_mul (pt_pow hγ.cont _) (p.cont i)
  · rw [← p.red]
    refine GDet.ext fun B _ _ x => ?_
    letI : Algebra R B := ((algebraMap (ResidueField O) B).comp (res O R : R →+* ResidueField O)).toAlgebra
    change p.D.D B (twA γ B x) = p.D.D B x
    rw [pt_id γ B fun g => ?_]
    change algebraMap (ResidueField O) B (res O R (γ g)) = 1
    rw [hres, map_one]
  · exact pt_mul (p.psi v i).cont fun N => (hγ.cont N).comp_continuous (F.φ_cont v)
  · change res O R (p.ψ v i g * γ (F.φ v g)) = _
    rw [map_mul, hres, mul_one]
    exact (p.psi v i).red g
  · change (p.ψ v i g : R) * γ (F.φ v g) = _
    rw [hγ.mu v g g.2, Units.val_one, mul_one]
    exact (p.psi v i).mu g
  · have h1 : F.star O R n (MonoidAlgebra.single g 1) =
        MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R) := by
      simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_mk, OneHom.coe_mk,
        MulOpposite.unop_op]
    have h2 : γ (F.conj g)⁻¹ = γ g := by
      rw [map_inv]; exact inv_eq_of_mul_eq_one_right (hγ.conj g)
    rw [pt_single, ← p.P, h1, pt_single, h2]
  · obtain ⟨c, hc⟩ : ∃ c : R, twA γ R (F.oEl v (fun i => p.ψ v i * γ.comp (F.φ v)) g) = c • F.oEl v (p.ψ v) g := by
      simp only [GFrame.oEl, map_list_prod, List.map_ofFn, Function.comp_def]
      refine pt_prod n _ _ fun i => ⟨γ (F.φ v (g i)), ?_⟩
      rw [map_sub, twA_single, twA_single, smul_sub, MonoidAlgebra.smul_single, MonoidAlgebra.smul_single]
      simp [mul_comm]
    have h1 : twA γ R (MonoidAlgebra.single h 1) = (γ h : R) • MonoidAlgebra.single h 1 := by
      rw [twA_single, MonoidAlgebra.smul_single]; simp
    rw [GDet.tr, lam_twD, map_mul, hc, h1, smul_mul_smul_comm, lamSmul]
    exact (congrArg _ (p.Ord v g h)).trans (mul_zero _)
  · have hg1 : γ g = 1 := hγ.iu u hg.1
    have h1 : twA γ R (MonoidAlgebra.single h 1) = (γ h : R) • MonoidAlgebra.single h 1 := by
      rw [twA_single, MonoidAlgebra.smul_single]; simp
    have h2 : twA γ R (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
      rw [twA_single, hg1]; simp
    rw [GDet.tr, lam_twD, map_mul, map_sub, map_one, h1, h2, smul_mul_assoc, lamSmul]
    exact (congrArg _ (p.I u g hg h)).trans (mul_zero _)

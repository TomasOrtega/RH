import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ShaCoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Use `haveI : IsCO O (TrivSqZeroExt O (O ⧸ I)) := co_sqz O O _ fun _ => rfl`. Establish `hd' : I.mkQ ∘ₗ d ∈ PtDer x (O ⧸ I)` using `fun f g => by`. Use `hd f g` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, this, map_add, map_smul]`. Take `⟨y, hy⟩` from `(der_hom O R O (O ⧸ I) x _).1 ⟨_, hd', rfl⟩`.

Take `⟨y', hy'⟩` from `(der_hom O R O (O ⧸ I) x _).1 ⟨_, (PtDer x (O ⧸ I)).zero_mem, rfl⟩`. Establish `key : ∀ f, d f ∈ I ↔ y f = y' f` using `fun f => by`. Rewrite using `[TrivSqZeroExt.ext_iff, (hy f).1, (hy f).2, (hy' f).1, (hy' f).2]`. Simplify using `only [true_and, LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Establish `k' : ∀ f, π f = 0 → y' f = 0` using `fun f hf => TrivSqZeroExt.ext (by rw [(hy' f).1, hx f hf]; rfl) (by rw [(hy' f).2]; rfl)`.

Establish `k : ∀ f, π f = 0 → y f = 0` using `fun f hf => ((key f).1 (h0 f hf)).trans (k' f hf)`. Set `e` to `(Ideal.quotientKerAlgEquivOfSurjective hπ).symm`. Establish `he : ∀ f, e (π f) = Ideal.Quotient.mk _ f` using `fun f => by`. Simplify using `only [e]`. Rewrite using `[AlgEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Set `u : S →ₐ[O] TrivSqZeroExt O (O ⧸ I)` to `(Ideal.Quotient.liftₐ (RingHom.ker π) y k).comp e.toAlgHom`. Set `u' : S →ₐ[O] TrivSqZeroExt O (O ⧸ I)` to `(Ideal.Quotient.liftₐ (RingHom.ker π) y' k').comp e.toAlgHom`. Establish `hu : ∀ f, u (π f) = y f` using `fun f => by show Ideal.Quotient.liftₐ (RingHom.ker π) y k (e (π f)) = _`. Rewrite using `[he]`.

Both sides reduce to the same expression. Establish `hu' : ∀ f, u' (π f) = y' f` using `fun f => by show Ideal.Quotient.liftₐ (RingHom.ker π) y' k' (e (π f)) = _`. Rewrite using `[he]`. Both sides reduce to the same expression. Establish `huu : u = u'` using `hr _ u u' (Lift.ext (MonoidHom.ext fun g => Matrix.ext fun i j => by`.

Take `⟨f, hf, hf'⟩` from `h1 g i j`. Rewrite using `[Lift.map_hom, Lift.map_hom, ← hf, hu, hu', (key f).1 hf']))`. Rewrite using `[key, ← hu, ← hu', huu]`.
-/
private theorem der_zero {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R S : Type} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [IsCO O S] (π : R →ₐ[O] S)
    (hπ : Function.Surjective π) (r : Lift O rbar S) (hr : r.Generates) (x : R →ₐ[O] O) (hx : ∀ f, π f = 0 → x f = 0)
    (I : Ideal O) (d : R →ₗ[O] O) (hd : d ∈ PtDer x O) (h0 : ∀ f, π f = 0 → d f ∈ I)
    (h1 : ∀ g i j, ∃ f, π f = r.hom g i j ∧ d f ∈ I) (f : R) : d f ∈ I := by
  haveI : IsCO O (TrivSqZeroExt O (O ⧸ I)) := co_sqz O O _ fun _ => rfl
  have hd' : I.mkQ ∘ₗ d ∈ PtDer x (O ⧸ I) := fun f g => by
    have := hd f g
    simp only [LinearMap.comp_apply, this, map_add, map_smul]
  obtain ⟨y, hy⟩ := (der_hom O R O (O ⧸ I) x _).1 ⟨_, hd', rfl⟩
  obtain ⟨y', hy'⟩ := (der_hom O R O (O ⧸ I) x _).1 ⟨_, (PtDer x (O ⧸ I)).zero_mem, rfl⟩
  have key : ∀ f, d f ∈ I ↔ y f = y' f := fun f => by
    rw [TrivSqZeroExt.ext_iff, (hy f).1, (hy f).2, (hy' f).1, (hy' f).2]
    simp only [true_and, LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have k' : ∀ f, π f = 0 → y' f = 0 := fun f hf => TrivSqZeroExt.ext (by rw [(hy' f).1, hx f hf]; rfl) (by rw [(hy' f).2]; rfl)
  have k : ∀ f, π f = 0 → y f = 0 := fun f hf => ((key f).1 (h0 f hf)).trans (k' f hf)
  let e := (Ideal.quotientKerAlgEquivOfSurjective hπ).symm
  have he : ∀ f, e (π f) = Ideal.Quotient.mk _ f := fun f => by
    simp only [e]; rw [AlgEquiv.symm_apply_eq]; rfl
  let u : S →ₐ[O] TrivSqZeroExt O (O ⧸ I) := (Ideal.Quotient.liftₐ (RingHom.ker π) y k).comp e.toAlgHom
  let u' : S →ₐ[O] TrivSqZeroExt O (O ⧸ I) := (Ideal.Quotient.liftₐ (RingHom.ker π) y' k').comp e.toAlgHom
  have hu : ∀ f, u (π f) = y f := fun f => by
    show Ideal.Quotient.liftₐ (RingHom.ker π) y k (e (π f)) = _
    rw [he]; rfl
  have hu' : ∀ f, u' (π f) = y' f := fun f => by
    show Ideal.Quotient.liftₐ (RingHom.ker π) y' k' (e (π f)) = _
    rw [he]; rfl
  have huu : u = u' := hr _ u u' (Lift.ext (MonoidHom.ext fun g => Matrix.ext fun i j => by
    obtain ⟨f, hf, hf'⟩ := h1 g i j
    rw [Lift.map_hom, Lift.map_hom, ← hf, hu, hu', (key f).1 hf']))
  rw [key, ← hu, ← hu', huu]

/- English proof (translation)
Use `revert i j`. Evaluate the decidable proposition.
-/
private theorem wt_eq_neg (i j : Fin 4) : wt i j = -wPs → (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by revert i j; decide

/- English proof (translation)
Take `⟨p, hp, rfl⟩` from `hf`. Use `hp 0 (by rw [map_zero]; exact hj.symm)` as an intermediate fact. Rewrite using `[AlgHom.toLinearMap_apply, WPres.origin_π]`. Simplify using `using this`.
-/
private theorem origin_part {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (h : W.HasOrigin) {j : X} (hj : j ≠ 0) {f : R} (hf : f ∈ W.part j) : W.origin h f = 0 := by
  obtain ⟨p, hp, rfl⟩ := hf
  have := hp 0 (by rw [map_zero]; exact hj.symm)
  rw [AlgHom.toLinearMap_apply, WPres.origin_π]
  simpa using this

/- English proof (translation)
Use `choose δ h1 h2 h3 h4 using der`. Establish `hadd : ∀ μ ν f, Ideal.Quotient.mk (Ideal.span {a}) (δ (μ + ν) f) = Ideal.Quotient.mk _ (δ μ f) + Ideal.Quotient.mk _ (δ ν f)` using `fun μ ν f => by`. Rewrite using `[← map_add, Ideal.Quotient.eq]`. Use `der_zero π hπ r hr x hx (Ideal.span {a}) (δ (μ + ν) - (δ μ + δ ν)) (sub_mem (h1 _) (add_mem (h1 _) (h1 _))) (fun f hf => sub_mem (h3 _ f hf) (add_mem (h3 _ f hf) (h3 _ f hf))) (fun g i j => ?_) f` and prove the remaining obligations. Take `⟨f, hf, hf'⟩` from `hom g i j`.

Use `⟨f, hf', ?_⟩` and prove the remaining obligations. Use `show δ (μ + ν) f - (δ μ f + δ ν f) ∈ _`. Distinguish the cases in `hw : wt i j = -wPs`. Rewrite using `[← Ideal.Quotient.eq, map_add]`. Break down `wt_eq_neg i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases.

Rewrite using `[(h4 _ g f).1 hf', (h4 _ g f).1 hf', (h4 _ g f).1 hf', map_add, Pi.add_apply, mul_add]`. Rewrite using `[(h4 _ g f).2 hf', (h4 _ g f).2 hf', (h4 _ g f).2 hf', map_add, Pi.add_apply, mul_add]`. Rewrite using `[h2 _ _ hw f hf, h2 _ _ hw f hf, h2 _ _ hw f hf]`. Simplify using the standard rewrite rules. Set `Dm : N →+ (A →ₗ[O] O ⧸ Ideal.span {a})` to `AddMonoidHom.mk' (fun μ => (Ideal.span {a}).mkQ ∘ₗ δ μ ∘ₗ A.val.toLinearMap) fun μ ν => LinearMap.ext fun f => hadd μ ν f`.

Establish `hDm : ∀ μ (f : A), Dm μ f = Ideal.Quotient.mk _ (δ μ f)` using `fun _ _ => rfl`. Use `hM O A ℤ 𝒜 (x.comp A.val) (-1) (fun f hf => hx1 _ ((hA _ f).1 hf)) ι F hF a ha N Dm ?_ (fun μ i => ?_) fun μ => ⟨δ μ ∘ₗ A.val.toLinearMap, fun f g => h1 μ f g, fun n hn f hf => ?_, fun f => rfl⟩` and prove the remaining obligations. Use `(injective_iff_map_eq_zero Dm).2 fun μ hμ => hZ ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Use function extensionality and compare the values at `g`.

Take `⟨f, hf, hf'⟩` from `hom g 2 0`. Establish `e1` using `hDm μ ⟨f, hA' (-1) f (by rwa [show wt 2 0 = (0, -1) by decide] at hf)⟩`. Rewrite `e1` using `[hμ, LinearMap.zero_apply, (h4 μ g f).1 hf']`. Conclude with `((s g).isUnit.map (Ideal.Quotient.mk (Ideal.span {a}))).mul_right_eq_zero.1 e1.symm`. Rewrite using `[hDm, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `h3 μ _ (hF0 i)`. Conclude with `h2 μ (0, n) (fun h => hn (congrArg Prod.snd h)) _ ((hA n f).1 hf)`.
-/
private theorem len_le (hM : LemmaM') {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* M4 (ResidueField O)}
    {R S : Type} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [IsCO O S] (π : R →ₐ[O] S)
    (hπ : Function.Surjective π) (r : Lift O rbar S) (hr : r.Generates) (x : R →ₐ[O] O) (hx : ∀ f, π f = 0 → x f = 0)
    (P : ℤ × ℤ → Submodule O R) (hom : ∀ g i j, ∃ f ∈ P (wt i j), π f = r.hom g i j)
    (A : Subalgebra O R) (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (hA : ∀ n (f : A), f ∈ 𝒜 n ↔ f.1 ∈ P (0, n))
    (hA' : ∀ n f, f ∈ P (0, n) → f ∈ A) (hx1 : ∀ f ∈ P (0, -1), x f = 0)
    {ι : Type} (F : ι → A) (hF : ∀ i, F i ∈ 𝒜 (-1)) (hF0 : ∀ i, π (F i) = 0)
    (a : O) (ha : a ≠ 0) (N : Type) [AddCommGroup N] [Module O N] (Z : N →+ (Γ → O ⧸ Ideal.span {a}))
    (hZ : Function.Injective Z) (s t : Γ → Oˣ)
    (der : ∀ μ, ∃ δ ∈ PtDer x O, HasWt P (-wPs) δ ∧ (∀ f, π f = 0 → δ f ∈ Ideal.span {a}) ∧
      ∀ g f, (π f = r.hom g 2 0 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (s g : O) * Z μ g) ∧
        (π f = r.hom g 3 1 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (t g : O) * Z μ g)) :
    Module.length O N ≤ cotLen (x.comp A.val) 𝒜 (-1) F := by
  choose δ h1 h2 h3 h4 using der
  have hadd : ∀ μ ν f, Ideal.Quotient.mk (Ideal.span {a}) (δ (μ + ν) f) =
      Ideal.Quotient.mk _ (δ μ f) + Ideal.Quotient.mk _ (δ ν f) := fun μ ν f => by
    rw [← map_add, Ideal.Quotient.eq]
    refine der_zero π hπ r hr x hx (Ideal.span {a}) (δ (μ + ν) - (δ μ + δ ν))
      (sub_mem (h1 _) (add_mem (h1 _) (h1 _)))
      (fun f hf => sub_mem (h3 _ f hf) (add_mem (h3 _ f hf) (h3 _ f hf))) (fun g i j => ?_) f
    obtain ⟨f, hf, hf'⟩ := hom g i j
    refine ⟨f, hf', ?_⟩
    show δ (μ + ν) f - (δ μ f + δ ν f) ∈ _
    by_cases hw : wt i j = -wPs
    · rw [← Ideal.Quotient.eq, map_add]
      rcases wt_eq_neg i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [(h4 _ g f).1 hf', (h4 _ g f).1 hf', (h4 _ g f).1 hf', map_add, Pi.add_apply, mul_add]
      · rw [(h4 _ g f).2 hf', (h4 _ g f).2 hf', (h4 _ g f).2 hf', map_add, Pi.add_apply, mul_add]
    · rw [h2 _ _ hw f hf, h2 _ _ hw f hf, h2 _ _ hw f hf]; simp
  let Dm : N →+ (A →ₗ[O] O ⧸ Ideal.span {a}) :=
    AddMonoidHom.mk' (fun μ => (Ideal.span {a}).mkQ ∘ₗ δ μ ∘ₗ A.val.toLinearMap) fun μ ν =>
      LinearMap.ext fun f => hadd μ ν f
  have hDm : ∀ μ (f : A), Dm μ f = Ideal.Quotient.mk _ (δ μ f) := fun _ _ => rfl
  refine hM O A ℤ 𝒜 (x.comp A.val) (-1) (fun f hf => hx1 _ ((hA _ f).1 hf)) ι F hF a ha N Dm ?_ (fun μ i => ?_)
    fun μ => ⟨δ μ ∘ₗ A.val.toLinearMap, fun f g => h1 μ f g, fun n hn f hf => ?_, fun f => rfl⟩
  · refine (injective_iff_map_eq_zero Dm).2 fun μ hμ => hZ ?_
    rw [map_zero]
    funext g
    obtain ⟨f, hf, hf'⟩ := hom g 2 0
    have e1 := hDm μ ⟨f, hA' (-1) f (by rwa [show wt 2 0 = (0, -1) by decide] at hf)⟩
    rw [hμ, LinearMap.zero_apply, (h4 μ g f).1 hf'] at e1
    exact ((s g).isUnit.map (Ideal.Quotient.mk (Ideal.span {a}))).mul_right_eq_zero.1 e1.symm
  · rw [hDm, Ideal.Quotient.eq_zero_iff_mem]
    exact h3 μ _ (hF0 i)
  · exact h2 μ (0, n) (fun h => hn (congrArg Prod.snd h)) _ ((hA n f).1 hf)

end UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD M _ hM hS`. Take `⟨-, a, ha, Z, hZ, hc⟩` from `shaCoc D hD hS`. Use `haveI : Finite (ResidueField c.O) := by`. Take `⟨-, -, h, -⟩` from `dvrFacts l c.O`. Use `haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ PadicInt.residueField.symm.toEquiv`.

Conclude with `IsLocalRing.ResidueField.finite_of_finite ‹_›`. Establish `hx : ∀ f, M.π f = 0 → M.W.origin M.org f = 0` using `fun f hf => by`. Take `⟨e, -, he⟩` from `M.hom 1 0 0`. Establish `h1` using `M.at0 1 0 0 (f + e) (by rw [map_add, hf, he, zero_add])`. Rewrite `h1` using `[map_add, M.at0 1 0 0 e he]`.

Conclude with `add_eq_right.1 h1`. Conclude with `len_le hM M.π M.surj M.ru M.gen (M.W.origin M.org) hx M.W.part M.hom M.A M.gr (fun _ _ => Iff.rfl) (fun n f hf => M.aPart_le hf) (fun f hf => origin_part M.W M.org (by decide) hf) M.eqns.F M.eqns.hF (fun i => by show M.F i ∈ RingHom.ker M.π`. Rewrite using `[M.ker]`. Conclude with `Ideal.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))`. Use `a ha _ Z hZ D.th D.Psi fun μ => M.der a (Z μ) ha (hc μ)`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.mPrime :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], LemmaM' → SoFin Ω l → D.sha ≤ cotLen M.x0 M.gr (-1) M.eqns.F := by
  intro Ω _ _ _ l _ c D hD M _ hM hS
  obtain ⟨-, a, ha, Z, hZ, hc⟩ := shaCoc D hD hS
  haveI : Finite (ResidueField c.O) := by
    obtain ⟨-, -, h, -⟩ := dvrFacts l c.O
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ PadicInt.residueField.symm.toEquiv
    exact IsLocalRing.ResidueField.finite_of_finite ‹_›
  have hx : ∀ f, M.π f = 0 → M.W.origin M.org f = 0 := fun f hf => by
    obtain ⟨e, -, he⟩ := M.hom 1 0 0
    have h1 := M.at0 1 0 0 (f + e) (by rw [map_add, hf, he, zero_add])
    rw [map_add, M.at0 1 0 0 e he] at h1
    exact add_eq_right.1 h1
  exact len_le hM M.π M.surj M.ru M.gen (M.W.origin M.org) hx M.W.part M.hom M.A M.gr (fun _ _ => Iff.rfl)
    (fun n f hf => M.aPart_le hf) (fun f hf => origin_part M.W M.org (by decide) hf) M.eqns.F M.eqns.hF
    (fun i => by
      show M.F i ∈ RingHom.ker M.π
      rw [M.ker]
      exact Ideal.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))
    a ha _ Z hZ D.th D.Psi fun μ => M.der a (Z μ) ha (hc μ)

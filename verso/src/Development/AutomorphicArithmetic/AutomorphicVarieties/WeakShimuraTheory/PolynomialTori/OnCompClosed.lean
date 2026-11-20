import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Apply `Lift.ext` to reduce the goal to its premises. Use extensionality with `g a b`. Simplify using `[Lift.map]`.
-/
private theorem lift_map_id {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R) :
    Lift.map (AlgHom.id O R) r = r := by
  apply Lift.ext
  ext g a b
  simp [Lift.map]

/- English proof (translation)
Apply `Lift.ext` to reduce the goal to its premises. Use extensionality with `x a b`. Simplify using `[Lift.map]`.
-/
private theorem lift_map_map {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R S T : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
    [CommRing T] [Algebra O T] [IsCO O T] (f : R →ₐ[O] S) (g : S →ₐ[O] T) (r : Lift O rbar R) :
    Lift.map g (Lift.map f r) = Lift.map (g.comp f) r := by
  apply Lift.ext
  ext x a b
  simp [Lift.map]

/- English proof (translation)
Take `⟨I, hI⟩` from `hP R r`. Establish `h0` using `(hI R (AlgHom.id O R)).1 (by rw [lift_map_id]; exact hr)`. Use `(hI S f).2 fun x hx => ?_` and prove the remaining obligations. Use `h0 x hx` as an intermediate fact. Simplify using `only [AlgHom.id_apply] at this`.

Rewrite using `[this, map_zero]`.
-/
private theorem cond_map_of_isClosed {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    (P : Cond O rbar) (hP : P.IsClosed)
    {R S : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
    (r : Lift O rbar R) (hr : P R r) (f : R →ₐ[O] S) : P S (Lift.map f r) := by
  obtain ⟨I, hI⟩ := hP R r
  have h0 := (hI R (AlgHom.id O R)).1 (by rw [lift_map_id]; exact hr)
  refine (hI S f).2 fun x hx => ?_
  have := h0 x hx
  simp only [AlgHom.id_apply] at this
  rw [this, map_zero]

/- English proof (translation)
Introduce `O _ _ Γ ι _ _ _ _ rbar P ρ₀ hP U _ _ _ ρ hρ J hJ`. Introduce `R _ _ _ r`. Establish `onP : ∀ (S : Type) [CommRing S] [Algebra O S] [IsCO O S] (s : Lift O rbar S), OnComp P ρ₀ s → P S s`. Introduce `S _ _ _ s hs`. Take `⟨B, _, _, _, _, ρ', hP', -, y, hy⟩` from `hs`.

Substitute `hy` using the available equality. Conclude with `cond_map_of_isClosed P hP ρ' hP' y`. Take `⟨I0, hI0⟩` from `hP R r`. Distinguish the cases in `htop : I0 = ⊤`. Use `⟨⊤, fun R' _ _ _ f => ⟨fun h x _ => ?_, fun h => ?_⟩⟩` and prove the remaining obligations.

Conclude with `(hI0 R' f).1 (onP _ _ h) x (by rw [htop]; exact Submodule.mem_top)`. It suffices to derive a contradiction. Establish `h1` using `h 1 Submodule.mem_top`. Rewrite `h1` using `[map_one]`. Conclude with `one_ne_zero h1`.

Use `haveI : Nontrivial (R ⧸ I0) := Ideal.Quotient.nontrivial_iff.2 htop haveI : IsCO O (R ⧸ I0) := co_quot O R (R ⧸ I0) (Ideal.Quotient.mkₐ O I0) (Ideal.Quotient.mkₐ_surjective O I0)`. Establish `hPπ : P (R ⧸ I0) (Lift.map (Ideal.Quotient.mkₐ O I0) r)` using `(hI0 _ (Ideal.Quotient.mkₐ O I0)).2 fun x hx => by`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hx`. Take `⟨u, hu, -⟩` from `(hρ (R ⧸ I0)).2 _ hPπ`.

Use `⟨I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0), fun R' _ _ _ f => ?_⟩` and prove the remaining obligations. Establish `key : ∀ hf : ∀ a ∈ I0, f a = 0, (OnComp P ρ₀ (Lift.map f r) ↔ ∀ x ∈ I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0), f x = 0)`. Introduce `hf`. Use `set g := Ideal.Quotient.liftₐ I0 f hf with hg`. Establish `hgπ : ∀ x, g (Ideal.Quotient.mkₐ O I0 x) = f x` using `fun x => rfl`.

Establish `hfg : f = g.comp (Ideal.Quotient.mkₐ O I0)`. Use extensionality with `x`. Conclude with `(hgπ x).symm`. Establish `hmap : Lift.map f r = Lift.map (g.comp u) ρ`. Rewrite using `[hfg, ← lift_map_map, ← hu, lift_map_map]`.

Rewrite using `[hmap, hJ]`. Prove the components needed by the constructor for the conclusion. Introduce `hJk x hx`. Establish `hle : J.map u ≤ RingHom.ker g`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `z hz`. Conclude with `hJk hz`. Establish `hsup : I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0) ≤ RingHom.ker f`. Use `sup_le (fun a ha => RingHom.mem_ker.2 (hf a ha)) ?_` and prove the remaining obligations. Introduce `y hy`.

Establish `hy' : Ideal.Quotient.mkₐ O I0 y ∈ J.map u` using `hy`. Use `hle hy'` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker, hgπ]`. Conclude with `RingHom.mem_ker.2 this`. Conclude with `RingHom.mem_ker.1 (hsup hx)`.

Introduce `h y hy`. Take `⟨x, hx⟩` from `Ideal.Quotient.mkₐ_surjective O I0 (u y)`. Establish `hxm : x ∈ (J.map u).comap (Ideal.Quotient.mkₐ O I0)` using `by show Ideal.Quotient.mkₐ O I0 x ∈ J.map u`. Rewrite using `[hx]`. Conclude with `Ideal.mem_map_of_mem _ hy`.

Use `h x (Ideal.mem_sup_right hxm)` as an intermediate fact. Rewrite using `[RingHom.mem_ker, AlgHom.comp_apply, ← hx, hgπ]`. Conclude with `this`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `(key fun x hx => (hI0 R' f).1 (onP _ _ h) x hx).1 h`. Introduce `h`. Conclude with `(key fun a ha => h a (Ideal.mem_sup_left ha)).2 h`.
-/
theorem UpperTheory.V.Ws.Po.onCompClosed :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι]
      (rbar : Γ →* Matrix ι ι (ResidueField O)) (P : Cond O rbar) (ρ₀ : Γ →* Matrix ι ι O), P.IsClosed →
      ∀ (U : Type) [CommRing U] [Algebra O U] [IsCO O U] (ρ : Lift O rbar U), Represents P ρ → ∀ J : Ideal U,
      (∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : U →ₐ[O] C), OnComp P ρ₀ (ρ.map f) ↔ J ≤ RingHom.ker f) →
      Cond.IsClosed (rbar := rbar) fun _ _ _ _ r => OnComp P ρ₀ r := by
  intro O _ _ Γ ι _ _ _ _ rbar P ρ₀ hP U _ _ _ ρ hρ J hJ
  intro R _ _ _ r
  have onP : ∀ (S : Type) [CommRing S] [Algebra O S] [IsCO O S] (s : Lift O rbar S),
      OnComp P ρ₀ s → P S s := by
    intro S _ _ _ s hs
    obtain ⟨B, _, _, _, _, ρ', hP', -, y, hy⟩ := hs
    subst hy
    exact cond_map_of_isClosed P hP ρ' hP' y
  obtain ⟨I0, hI0⟩ := hP R r
  by_cases htop : I0 = ⊤
  · refine ⟨⊤, fun R' _ _ _ f => ⟨fun h x _ => ?_, fun h => ?_⟩⟩
    · exact (hI0 R' f).1 (onP _ _ h) x (by rw [htop]; exact Submodule.mem_top)
    · exfalso
      have h1 := h 1 Submodule.mem_top
      rw [map_one] at h1
      exact one_ne_zero h1
  · haveI : Nontrivial (R ⧸ I0) := Ideal.Quotient.nontrivial_iff.2 htop
    haveI : IsCO O (R ⧸ I0) :=
      co_quot O R (R ⧸ I0) (Ideal.Quotient.mkₐ O I0) (Ideal.Quotient.mkₐ_surjective O I0)
    have hPπ : P (R ⧸ I0) (Lift.map (Ideal.Quotient.mkₐ O I0) r) :=
      (hI0 _ (Ideal.Quotient.mkₐ O I0)).2 fun x hx => by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.2 hx
    obtain ⟨u, hu, -⟩ := (hρ (R ⧸ I0)).2 _ hPπ
    refine ⟨I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0), fun R' _ _ _ f => ?_⟩
    have key : ∀ hf : ∀ a ∈ I0, f a = 0, (OnComp P ρ₀ (Lift.map f r) ↔
        ∀ x ∈ I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0), f x = 0) := by
      intro hf
      set g := Ideal.Quotient.liftₐ I0 f hf with hg
      have hgπ : ∀ x, g (Ideal.Quotient.mkₐ O I0 x) = f x := fun x => rfl
      have hfg : f = g.comp (Ideal.Quotient.mkₐ O I0) := by
        ext x
        exact (hgπ x).symm
      have hmap : Lift.map f r = Lift.map (g.comp u) ρ := by
        rw [hfg, ← lift_map_map, ← hu, lift_map_map]
      rw [hmap, hJ]
      constructor
      · intro hJk x hx
        have hle : J.map u ≤ RingHom.ker g := by
          rw [Ideal.map_le_iff_le_comap]
          intro z hz
          exact hJk hz
        have hsup : I0 ⊔ (J.map u).comap (Ideal.Quotient.mkₐ O I0) ≤ RingHom.ker f := by
          refine sup_le (fun a ha => RingHom.mem_ker.2 (hf a ha)) ?_
          intro y hy
          have hy' : Ideal.Quotient.mkₐ O I0 y ∈ J.map u := hy
          have := hle hy'
          rw [RingHom.mem_ker, hgπ] at this
          exact RingHom.mem_ker.2 this
        exact RingHom.mem_ker.1 (hsup hx)
      · intro h y hy
        obtain ⟨x, hx⟩ := Ideal.Quotient.mkₐ_surjective O I0 (u y)
        have hxm : x ∈ (J.map u).comap (Ideal.Quotient.mkₐ O I0) := by
          show Ideal.Quotient.mkₐ O I0 x ∈ J.map u
          rw [hx]
          exact Ideal.mem_map_of_mem _ hy
        have := h x (Ideal.mem_sup_right hxm)
        rw [RingHom.mem_ker, AlgHom.comp_apply, ← hx, hgπ]
        exact this
    constructor
    · intro h
      exact (key fun x hx => (hI0 R' f).1 (onP _ _ h) x hx).1 h
    · intro h
      exact (key fun a ha => h a (Ideal.mem_sup_left ha)).2 h

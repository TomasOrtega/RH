import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Introduce `R _ F I M M' _ _ _ _ ν φ hI hν`. Establish `hev : ∀ j, ∀ᶠ N in F, I (ν N) ≤ I j` using `fun j => (tendsto_atTop.1 hν j).mono fun N hN => hI hN`. Establish `he : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R), (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) = (J • ⊤ : Submodule R X).map (K • ⊤ : Submodule R X).mkQ`. Introduce `X _ _ K J`. Rewrite using `[Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]`.

Establish `hlift : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R), K ≤ J → ∀ x : X, (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈ (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) → x ∈ (J • ⊤ : Submodule R X)`. Introduce `X _ _ K J hKJ x hx`. Rewrite `hx` using `[he]`. Take `⟨y, hy, hyx⟩` from `hx`. Establish `hd : x - y ∈ (K • ⊤ : Submodule R X)`.

Rewrite using `[← Submodule.Quotient.eq]`. Conclude with `hyx.symm`. Use `Submodule.add_mem _ (Submodule.smul_mono_left hKJ hd) hy` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hmk : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R) (x : X), x ∈ (J • ⊤ : Submodule R X) → (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈ (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X)))`.

Introduce `X _ _ K J x hx`. Rewrite using `[he]`. Conclude with `⟨x, hx, rfl⟩`. Establish `hφ : ∀ N j (z : M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))), z ∈ (I j • ⊤ : Submodule R _) → φ N z ∈ (I j • ⊤ : Submodule R _)`. Introduce `N j z hz`.

Establish `hle : (I j • ⊤ : Submodule R _).map (φ N) ≤ I j • ⊤`. Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`. Conclude with `hle ⟨z, hz, rfl⟩`. Set `π : (∀ N, M' N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N)))` to `LinearMap.pi fun N => (Submodule.mkQ _).comp (LinearMap.proj N)`.

Establish `hπ : Function.Surjective π` using `fun q => ⟨fun N => (Submodule.mkQ_surjective _ (q N)).choose,`. Use function extensionality and compare the values at `fun N => (Submodule.mkQ_surjective _ (q N)).choose_spec⟩`. Establish `hker : LinearMap.ker π ≤ LinearMap.ker (ULim.mk F I M')`. Introduce `p hp`. Rewrite `hp`, the goal using `[LinearMap.mem_ker]`.

Rewrite using `[ULim.mk_eq_zero]`. Introduce `j`. Use `(hev j).mono fun N hN => ?_` and prove the remaining obligations. Establish `hpN : p N ∈ (I (ν N) • ⊤ : Submodule R (M' N))`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`.

Conclude with `congrFun hp N`. Conclude with `Submodule.smul_mono_left hN hpN`. Set `φ' : (∀ N, M N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N)))` to `LinearMap.pi fun N => (φ N).comp ((Submodule.mkQ _).comp (LinearMap.proj N))`. Set `Φ0 : (∀ N, M N) →ₗ[R] ULim F I M'` to `((LinearMap.ker π).liftQ (ULim.mk F I M') hker).comp ((π.quotKerEquivOfSurjective hπ).symm.toLinearMap.comp φ')`. Establish `hΦ0 : ∀ p p', π p' = φ' p → Φ0 p = ULim.mk F I M' p'`.

Introduce `p p' h`. Simplify using `only [Φ0, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[← h]`. Establish `hs : (π.quotKerEquivOfSurjective hπ).symm (π p') = Submodule.Quotient.mk p'`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Rewrite using `[hs, Submodule.liftQ_apply]`. Establish `hnull : uNull F I M ≤ LinearMap.ker Φ0`. Introduce `p hp`. Establish `hp : ∀ j, ∀ᶠ N in F, p N ∈ (I j • ⊤ : Submodule R (M N))` using `hp`.

Rewrite using `[LinearMap.mem_ker]`. Take `⟨p', hp'⟩` from `hπ (φ' p)`. Rewrite using `[hΦ0 p p' hp', ULim.mk_eq_zero]`. Introduce `j`. Use `((hp j).and (hev j)).mono fun N ⟨h1, h2⟩ => ?_` and prove the remaining obligations.

Apply `hlift (I (ν N)) (I j) h2` to reduce the goal to its premises. Establish `hN : π p' N = φ N (Submodule.Quotient.mk (p N))` using `congrFun hp' N`. Express the relevant statement in the definitionally equal form `π p' N ∈ _`. Rewrite using `[hN]`. Conclude with `hφ N j _ (hmk _ _ _ h1)`.

Use `⟨(uNull F I M).liftQ Φ0 hnull, fun p p' h => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(uNull F I M).liftQ Φ0 hnull (Submodule.Quotient.mk p) = _`. Rewrite using `[Submodule.liftQ_apply]`. Take `⟨q, hq⟩` from `hπ (φ' p)`. Rewrite using `[hΦ0 p q hq, ← sub_eq_zero, ← map_sub, ULim.mk_eq_zero]`.

Introduce `j`. Use `(h.and (hev j)).mono fun N ⟨h1, h2⟩ => ?_` and prove the remaining obligations. Apply `Submodule.smul_mono_left h2` to reduce the goal to its premises. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Pi.sub_apply, Submodule.Quotient.mk_sub, h1]`. Establish `hN : π q N = φ N (Submodule.Quotient.mk (p N))` using `congrFun hq N`.

Conclude with `sub_eq_zero.2 hN`.
-/
theorem UpperTheory.V.Pa.Core.ulimQuot :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ) (I : ℕ → Ideal R) (M M' : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] [∀ N, AddCommGroup (M' N)] [∀ N, Module R (M' N)] (ν : ℕ → ℕ) (φ : ∀ N, (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N)))), Antitone I → Tendsto ν F atTop → ∃ Φ : ULim F I M →ₗ[R] ULim F I M', ∀ (p : ∀ N, M N) (p' : ∀ N, M' N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) = φ N (Submodule.Quotient.mk (p N))) → Φ (ULim.mk F I M p) = ULim.mk F I M' p' := by
  intro R _ F I M M' _ _ _ _ ν φ hI hν
  have hev : ∀ j, ∀ᶠ N in F, I (ν N) ≤ I j := fun j =>
    (tendsto_atTop.1 hν j).mono fun N hN => hI hN
  have he : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R),
      (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) =
        (J • ⊤ : Submodule R X).map (K • ⊤ : Submodule R X).mkQ := by
    intro X _ _ K J
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  have hlift : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R), K ≤ J → ∀ x : X,
      (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈
        (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) → x ∈ (J • ⊤ : Submodule R X) := by
    intro X _ _ K J hKJ x hx
    rw [he] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hd : x - y ∈ (K • ⊤ : Submodule R X) := by
      rw [← Submodule.Quotient.eq]
      exact hyx.symm
    have := Submodule.add_mem _ (Submodule.smul_mono_left hKJ hd) hy
    rwa [sub_add_cancel] at this
  have hmk : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R) (x : X),
      x ∈ (J • ⊤ : Submodule R X) →
        (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈
          (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) := by
    intro X _ _ K J x hx
    rw [he]
    exact ⟨x, hx, rfl⟩
  have hφ : ∀ N j (z : M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))),
      z ∈ (I j • ⊤ : Submodule R _) → φ N z ∈ (I j • ⊤ : Submodule R _) := by
    intro N j z hz
    have hle : (I j • ⊤ : Submodule R _).map (φ N) ≤ I j • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hle ⟨z, hz, rfl⟩
  let π : (∀ N, M' N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) :=
    LinearMap.pi fun N => (Submodule.mkQ _).comp (LinearMap.proj N)
  have hπ : Function.Surjective π := fun q =>
    ⟨fun N => (Submodule.mkQ_surjective _ (q N)).choose,
      funext fun N => (Submodule.mkQ_surjective _ (q N)).choose_spec⟩
  have hker : LinearMap.ker π ≤ LinearMap.ker (ULim.mk F I M') := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    rw [ULim.mk_eq_zero]
    intro j
    refine (hev j).mono fun N hN => ?_
    have hpN : p N ∈ (I (ν N) • ⊤ : Submodule R (M' N)) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact congrFun hp N
    exact Submodule.smul_mono_left hN hpN
  let φ' : (∀ N, M N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) :=
    LinearMap.pi fun N => (φ N).comp ((Submodule.mkQ _).comp (LinearMap.proj N))
  let Φ0 : (∀ N, M N) →ₗ[R] ULim F I M' :=
    ((LinearMap.ker π).liftQ (ULim.mk F I M') hker).comp
      ((π.quotKerEquivOfSurjective hπ).symm.toLinearMap.comp φ')
  have hΦ0 : ∀ p p', π p' = φ' p → Φ0 p = ULim.mk F I M' p' := by
    intro p p' h
    simp only [Φ0, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h]
    have hs : (π.quotKerEquivOfSurjective hπ).symm (π p') = Submodule.Quotient.mk p' := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [hs, Submodule.liftQ_apply]
  have hnull : uNull F I M ≤ LinearMap.ker Φ0 := by
    intro p hp
    have hp : ∀ j, ∀ᶠ N in F, p N ∈ (I j • ⊤ : Submodule R (M N)) := hp
    rw [LinearMap.mem_ker]
    obtain ⟨p', hp'⟩ := hπ (φ' p)
    rw [hΦ0 p p' hp', ULim.mk_eq_zero]
    intro j
    refine ((hp j).and (hev j)).mono fun N ⟨h1, h2⟩ => ?_
    apply hlift (I (ν N)) (I j) h2
    have hN : π p' N = φ N (Submodule.Quotient.mk (p N)) := congrFun hp' N
    change π p' N ∈ _
    rw [hN]
    exact hφ N j _ (hmk _ _ _ h1)
  refine ⟨(uNull F I M).liftQ Φ0 hnull, fun p p' h => ?_⟩
  change (uNull F I M).liftQ Φ0 hnull (Submodule.Quotient.mk p) = _
  rw [Submodule.liftQ_apply]
  obtain ⟨q, hq⟩ := hπ (φ' p)
  rw [hΦ0 p q hq, ← sub_eq_zero, ← map_sub, ULim.mk_eq_zero]
  intro j
  refine (h.and (hev j)).mono fun N ⟨h1, h2⟩ => ?_
  apply Submodule.smul_mono_left h2
  rw [← Submodule.Quotient.mk_eq_zero, Pi.sub_apply, Submodule.Quotient.mk_sub, h1]
  have hN : π q N = φ N (Submodule.Quotient.mk (p N)) := congrFun hq N
  exact sub_eq_zero.2 hN

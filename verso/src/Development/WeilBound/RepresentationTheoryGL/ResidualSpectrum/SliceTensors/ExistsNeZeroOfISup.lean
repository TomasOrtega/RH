import Mathlib

noncomputable section

open scoped MonoidAlgebra

namespace PositivityTheory.Rg.Rs.PLsAbs2

/- English proof (translation)
Establish `: IsSemisimpleModule R M` using `isSemisimpleModule_of_isSemisimpleModule_submodule' (fun i => IsSemisimpleModule.of_surjective (fs i).rangeRestrict (fs i).surjective_rangeRestrict) htop`. Break down `IsSemisimpleModule.eq_bot_or_exists_simple_le (Submodule.span R {x}) with hC | ⟨A, hAC, hA⟩` into its components or cases. Conclude with `absurd ((Submodule.span_singleton_eq_bot).1 hC) hx`. Take `⟨h, hh⟩` from `IsSemisimpleModule.extension_property A.subtype A.injective_subtype LinearMap.id`. Use `hA` as an intermediate fact.

Establish `hA0 : A ≠ ⊥` using `((isSimpleModule_iff_isAtom).1 hA).1`. Establish `hhx : h x ≠ 0`. Introduce `h0`. Apply `hA0` to reduce the goal to its premises. Establish `hle : Submodule.span R {x} ≤ LinearMap.ker h` using `(Submodule.span_singleton_le_iff_mem _ _).2 h0`.

Use `eq_bot_iff.2 fun a ha => ?_` and prove the remaining obligations. Establish `e1 : h a = ⟨a, ha⟩` using `LinearMap.congr_fun hh ⟨a, ha⟩`. Establish `e2 : h a = 0` using `LinearMap.mem_ker.1 (hle (hAC ha))`. Establish `e3 : (⟨a, ha⟩ : A) = 0` using `e1.symm.trans e2`. Conclude with `(Submodule.mem_bot R).2 (congrArg Subtype.val e3)`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, h ∘ₗ fs i ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `hle : (⨆ i, LinearMap.range (fs i)) ≤ LinearMap.ker h` using `iSup_le fun i => by`. Introduce and unpack `_ ⟨v, rfl⟩`.

Conclude with `LinearMap.congr_fun (hc i) v`. Rewrite `hle` using `[htop]`. Conclude with `hhx (hle Submodule.mem_top)`. Set `e` to `LinearEquiv.ofBijective (h ∘ₗ fs i) (LinearMap.bijective_of_ne_zero hi)`. Conclude with `⟨e.symm.toLinearMap ∘ₗ h, fun h0 => hhx (by simpa using congrArg e h0)⟩`.
-/
theorem exists_ne_zero_of_iSup {R M S : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S]
    [Module R S] [IsSimpleModule R S] {ι : Type} (fs : ι → S →ₗ[R] M)
    (htop : ⨆ i, LinearMap.range (fs i) = ⊤) (x : M) (hx : x ≠ 0) : ∃ p : M →ₗ[R] S, p x ≠ 0 := by
  have : IsSemisimpleModule R M := isSemisimpleModule_of_isSemisimpleModule_submodule'
    (fun i => IsSemisimpleModule.of_surjective (fs i).rangeRestrict (fs i).surjective_rangeRestrict) htop
  rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (Submodule.span R {x}) with hC | ⟨A, hAC, hA⟩
  · exact absurd ((Submodule.span_singleton_eq_bot).1 hC) hx
  obtain ⟨h, hh⟩ := IsSemisimpleModule.extension_property A.subtype A.injective_subtype LinearMap.id
  have := hA
  have hA0 : A ≠ ⊥ := ((isSimpleModule_iff_isAtom).1 hA).1
  have hhx : h x ≠ 0 := by
    intro h0
    apply hA0
    have hle : Submodule.span R {x} ≤ LinearMap.ker h := (Submodule.span_singleton_le_iff_mem _ _).2 h0
    refine eq_bot_iff.2 fun a ha => ?_
    have e1 : h a = ⟨a, ha⟩ := LinearMap.congr_fun hh ⟨a, ha⟩
    have e2 : h a = 0 := LinearMap.mem_ker.1 (hle (hAC ha))
    have e3 : (⟨a, ha⟩ : A) = 0 := e1.symm.trans e2
    exact (Submodule.mem_bot R).2 (congrArg Subtype.val e3)
  obtain ⟨i, hi⟩ : ∃ i, h ∘ₗ fs i ≠ 0 := by
    by_contra hc
    push Not at hc
    have hle : (⨆ i, LinearMap.range (fs i)) ≤ LinearMap.ker h := iSup_le fun i => by
      rintro _ ⟨v, rfl⟩
      exact LinearMap.congr_fun (hc i) v
    rw [htop] at hle
    exact hhx (hle Submodule.mem_top)
  let e := LinearEquiv.ofBijective (h ∘ₗ fs i) (LinearMap.bijective_of_ne_zero hi)
  exact ⟨e.symm.toLinearMap ∘ₗ h, fun h0 => hhx (by simpa using congrArg e h0)⟩

/- English proof (translation)
Use `set T := ⨆ i, LinearMap.range (Φ i) with hTdef`. Establish `hmemΦ : ∀ i v, Φ i v ∈ T` using `fun i v => Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self (Φ i) v)`. Establish `hgen : ∀ f₁ f₂ : M →ₗ[ℂ] M, (∀ i v, f₁ (Φ i v) = f₂ (Φ i v)) → ∀ s ∈ T, f₁ s = f₂ s`. Introduce `f₁ f₂ h s hs`. Establish `hle : T ≤ LinearMap.ker (f₁ - f₂)` using `iSup_le fun i => by`.

Introduce and unpack `_ ⟨v, rfl⟩`. Simplify using `[h i v]`. Use `hle hs` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hT : ∀ g, ∀ s ∈ T, σ g s ∈ T`.

Introduce `g s hs`. Establish `hle : T ≤ T.comap (σ g)` using `iSup_le fun i => by`. Introduce and unpack `_ ⟨v, rfl⟩`. Use `show σ g (Φ i v) ∈ T`. Rewrite using `[← hΦ]`.

Conclude with `hmemΦ i _`. Conclude with `hle hs`. Set `τ : Representation ℂ Γ T` to `{ toFun := fun g => (σ g).restrict (hT g) map_one' := LinearMap.ext fun s => Subtype.ext (by show σ 1 s.1 = s.1`. Conclude with `hgen (σ 1) LinearMap.id (fun i v => by rw [← hΦ, map_one]; rfl) s.1 s.2)`. Use the proof step `map_mul' := fun g h => LinearMap.ext fun s => Subtype.ext (by show σ (g * h) s.1 = σ g (σ h s.1)`.

Conclude with `hgen (σ (g * h)) (σ g ∘ₗ σ h) (fun i v => by`. Rewrite using `[LinearMap.comp_apply, ← hΦ i h v, ← hΦ i g, ← hΦ i (g * h), map_mul, Module.End.mul_apply]) s.1 s.2) }`. Set `Ψ : ι → Representation.IntertwiningMap ρ τ` to `fun i => ((Φ i).codRestrict T (hmemΦ i)).intertwiningMap_of_isIntertwiningMap ρ τ (fun g v => Subtype.ext (hΦ i g v))`. Set `A` to `Representation.IntertwiningMap.equivLinearMapAsModule ρ τ`. Establish `: IsSimpleModule ℂ[Γ] ρ.asModule` using `(Representation.irreducible_iff_isSimpleModule_asModule ρ).1 hρ`.

Establish `hN : ∀ y ∈ T, ∃ hy : y ∈ T, (show τ.asModule from ⟨y, hy⟩) ∈ ⨆ i, LinearMap.range (A (Ψ i))` using `fun y hy => Submodule.iSup_induction (fun i => LinearMap.range (Φ i)) (motive := fun y => ∃ hy : y ∈ T, (show τ.asModule from ⟨y, hy⟩) ∈ ⨆ i, LinearMap.range (A (Ψ i))) hy (fun i x hx => by`. Take `⟨v, rfl⟩` from `hx`. Conclude with `⟨hmemΦ i v, Submodule.mem_iSup_of_mem i (LinearMap.mem_range.2 ⟨v, rfl⟩)⟩)`. Use the proof step `⟨T.zero_mem, Submodule.zero_mem _⟩`. Use the proof step `(fun _ _ ⟨ha, h1⟩ ⟨hb, h2⟩ => ⟨T.add_mem ha hb, Submodule.add_mem _ h1 h2⟩)`.

Establish `htop : ⨆ i, LinearMap.range (A (Ψ i)) = ⊤`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Take `⟨_, hx⟩` from `hN (x : T).1 (x : T).2`. Conclude with `hx`. Take `⟨q, hq⟩` from `exists_ne_zero_of_iSup (fun i => A (Ψ i)) htop (show τ.asModule from ⟨t, ht⟩) (fun e => h0 (congrArg (fun y : T => y.1) e))`.

Set `qI` to `(Representation.IntertwiningMap.equivLinearMapAsModule τ ρ).symm q`. Take `⟨p, hp⟩` from `LinearMap.exists_extend qI.toLinearMap`. Establish `hpv : ∀ s (hs : s ∈ T), p s = qI.toLinearMap ⟨s, hs⟩` using `fun s hs => LinearMap.congr_fun hp ⟨s, hs⟩`. Use `⟨p, ?_, fun g s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[hpv t ht]`.

Conclude with `hq`. Rewrite using `[hpv _ (hT g s hs), hpv s hs]`. Conclude with `LinearMap.congr_fun (qI.isIntertwining' g) ⟨s, hs⟩`.
-/
theorem exists_proj {Γ M X : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup X] [Module ℂ X]
    (σ : Γ → M →ₗ[ℂ] M) (ρ : Representation ℂ Γ X) (hρ : ρ.IsIrreducible) {ι : Type} (Φ : ι → X →ₗ[ℂ] M)
    (hΦ : ∀ i g v, Φ i (ρ g v) = σ g (Φ i v)) {t : M} (ht : t ∈ ⨆ i, LinearMap.range (Φ i)) (h0 : t ≠ 0) :
    ∃ p : M →ₗ[ℂ] X, p t ≠ 0 ∧ ∀ g, ∀ s ∈ ⨆ i, LinearMap.range (Φ i), p (σ g s) = ρ g (p s) := by
  classical
  set T := ⨆ i, LinearMap.range (Φ i) with hTdef
  have hmemΦ : ∀ i v, Φ i v ∈ T := fun i v => Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self (Φ i) v)
  have hgen : ∀ f₁ f₂ : M →ₗ[ℂ] M, (∀ i v, f₁ (Φ i v) = f₂ (Φ i v)) → ∀ s ∈ T, f₁ s = f₂ s := by
    intro f₁ f₂ h s hs
    have hle : T ≤ LinearMap.ker (f₁ - f₂) := iSup_le fun i => by
      rintro _ ⟨v, rfl⟩
      simp [h i v]
    have := hle hs
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  have hT : ∀ g, ∀ s ∈ T, σ g s ∈ T := by
    intro g s hs
    have hle : T ≤ T.comap (σ g) := iSup_le fun i => by
      rintro _ ⟨v, rfl⟩
      show σ g (Φ i v) ∈ T
      rw [← hΦ]
      exact hmemΦ i _
    exact hle hs
  let τ : Representation ℂ Γ T :=
    { toFun := fun g => (σ g).restrict (hT g)
      map_one' := LinearMap.ext fun s => Subtype.ext (by
        show σ 1 s.1 = s.1
        exact hgen (σ 1) LinearMap.id (fun i v => by rw [← hΦ, map_one]; rfl) s.1 s.2)
      map_mul' := fun g h => LinearMap.ext fun s => Subtype.ext (by
        show σ (g * h) s.1 = σ g (σ h s.1)
        exact hgen (σ (g * h)) (σ g ∘ₗ σ h) (fun i v => by
          rw [LinearMap.comp_apply, ← hΦ i h v, ← hΦ i g, ← hΦ i (g * h), map_mul, Module.End.mul_apply]) s.1 s.2) }
  let Ψ : ι → Representation.IntertwiningMap ρ τ := fun i =>
    ((Φ i).codRestrict T (hmemΦ i)).intertwiningMap_of_isIntertwiningMap ρ τ (fun g v => Subtype.ext (hΦ i g v))
  let A := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ
  have : IsSimpleModule ℂ[Γ] ρ.asModule := (Representation.irreducible_iff_isSimpleModule_asModule ρ).1 hρ
  have hN : ∀ y ∈ T, ∃ hy : y ∈ T, (show τ.asModule from ⟨y, hy⟩) ∈ ⨆ i, LinearMap.range (A (Ψ i)) :=
    fun y hy => Submodule.iSup_induction (fun i => LinearMap.range (Φ i))
      (motive := fun y => ∃ hy : y ∈ T, (show τ.asModule from ⟨y, hy⟩) ∈ ⨆ i, LinearMap.range (A (Ψ i))) hy
      (fun i x hx => by
        obtain ⟨v, rfl⟩ := hx
        exact ⟨hmemΦ i v, Submodule.mem_iSup_of_mem i (LinearMap.mem_range.2 ⟨v, rfl⟩)⟩)
      ⟨T.zero_mem, Submodule.zero_mem _⟩
      (fun _ _ ⟨ha, h1⟩ ⟨hb, h2⟩ => ⟨T.add_mem ha hb, Submodule.add_mem _ h1 h2⟩)
  have htop : ⨆ i, LinearMap.range (A (Ψ i)) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨_, hx⟩ := hN (x : T).1 (x : T).2
    exact hx
  obtain ⟨q, hq⟩ := exists_ne_zero_of_iSup (fun i => A (Ψ i)) htop (show τ.asModule from ⟨t, ht⟩)
    (fun e => h0 (congrArg (fun y : T => y.1) e))
  let qI := (Representation.IntertwiningMap.equivLinearMapAsModule τ ρ).symm q
  obtain ⟨p, hp⟩ := LinearMap.exists_extend qI.toLinearMap
  have hpv : ∀ s (hs : s ∈ T), p s = qI.toLinearMap ⟨s, hs⟩ := fun s hs => LinearMap.congr_fun hp ⟨s, hs⟩
  refine ⟨p, ?_, fun g s hs => ?_⟩
  · rw [hpv t ht]
    exact hq
  · rw [hpv _ (hT g s hs), hpv s hs]
    exact LinearMap.congr_fun (qI.isIntertwining' g) ⟨s, hs⟩

end PositivityTheory.Rg.Rs.PLsAbs2

end

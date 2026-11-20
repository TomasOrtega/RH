import Mathlib

universe u_1 u_2 u_3

namespace GlobalTheory.IntertwiningFunctional

/- English proof (translation)
Proceed by induction on `a using FreeAlgebra.induction with`. Consider the case `grade0 c => intro v`. Simplify using `[AlgHom.commutes, Module.algebraMap_end_apply]`. Consider the case `grade1 k => intro v`. Simplify using `[FreeAlgebra.lift_ι_apply, hT]`.

Consider the case `mul a b ha hb => intro v`. Simplify using `only [map_mul, Module.End.mul_apply]`. Rewrite using `[ha, hb]`. Consider the case `add a b ha hb => intro v`. Simplify using `only [map_add, LinearMap.add_apply]`.

Rewrite using `[ha, hb]`.
-/
private theorem freeAlgebra_lift_intertwine {K : Type u_1} {F : Type u_2} {V : Type u_3}
    [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V) (T : V →ₗ[ℂ] F)
    (hT : ∀ (k : K) (v : V), T (ρ k v) = r k (T v)) (a : FreeAlgebra ℂ K) :
    ∀ v : V, T (FreeAlgebra.lift ℂ ρ a v) = FreeAlgebra.lift ℂ r a (T v) := by
  induction a using FreeAlgebra.induction with
  | grade0 c => intro v; simp [AlgHom.commutes, Module.algebraMap_end_apply]
  | grade1 k => intro v; simp [FreeAlgebra.lift_ι_apply, hT]
  | mul a b ha hb => intro v; simp only [map_mul, Module.End.mul_apply]; rw [ha, hb]
  | add a b ha hb => intro v; simp only [map_add, LinearMap.add_apply]; rw [ha, hb]

/- English proof (translation)
Introduce `f hf hf0`. Use `set S := ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T with hSdef`. Establish `: Nontrivial V`. Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`.

Apply `hf0` to reduce the goal to its premises. Establish `hS : S = ⊥`. Use `le_bot_iff.mp (iSup₂_le fun T _ => ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[Subsingleton.elim v 0, map_zero]`.

Conclude with `Submodule.zero_mem _`. Rewrite `hf` using `[hS, Submodule.mem_bot]`. Conclude with `hf`. Set `A` to `FreeAlgebra ℂ K`. Set `rA : A →ₐ[ℂ] Module.End ℂ F` to `FreeAlgebra.lift ℂ r`.

Set `ρA : A →ₐ[ℂ] Module.End ℂ V` to `FreeAlgebra.lift ℂ ρ`. Set `: Module A F` to `Module.compHom F rA.toRingHom`. Set `: Module A V` to `Module.compHom V ρA.toRingHom`. Establish `smulF : ∀ (a : A) (x : F), a • x = rA a x` using `fun _ _ => rfl`. Establish `smulV : ∀ (a : A) (x : V), a • x = ρA a x` using `fun _ _ => rfl`.

Establish `: IsScalarTower ℂ A F` using `⟨fun c a x => by`. Rewrite using `[smulF, smulF, map_smul, LinearMap.smul_apply]⟩`. Establish `: IsScalarTower ℂ A V` using `⟨fun c a x => by`. Rewrite using `[smulV, smulV, map_smul, LinearMap.smul_apply]⟩`. Establish `hιF : ∀ (k : K) (x : F), (FreeAlgebra.ι ℂ k : A) • x = r k x` using `fun k x => by show FreeAlgebra.lift ℂ r (FreeAlgebra.ι ℂ k) x = r k x`.

Rewrite using `[FreeAlgebra.lift_ι_apply]`. Establish `hιV : ∀ (k : K) (v : V), (FreeAlgebra.ι ℂ k : A) • v = ρ k v` using `fun k v => by show FreeAlgebra.lift ℂ ρ (FreeAlgebra.ι ℂ k) v = ρ k v`. Rewrite using `[FreeAlgebra.lift_ι_apply]`. Establish `hVs : IsSimpleModule A V`. Use `{ toNontrivial := inferInstance, eq_bot_or_eq_top := fun W => ?_ }` and prove the remaining obligations.

Establish `hWinv : ∀ (k : K), ∀ v ∈ W.restrictScalars ℂ, ρ k v ∈ W.restrictScalars ℂ`. Introduce `k v hv`. Rewrite using `[← hιV]`. Conclude with `W.smul_mem _ hv`. Break down `hirr (W.restrictScalars ℂ) hWinv with h | h` into its components or cases.

Conclude with `Or.inl (by simpa using h)`. Conclude with `Or.inr (by simpa using h)`. Set `mkA : ∀ T : V →ₗ[ℂ] F, (∀ (k : K) (v : V), T (ρ k v) = r k (T v)) → V →ₗ[A] F` to `fun T hT => { toFun := T map_add' := T.map_add map_smul' := fun a v => freeAlgebra_lift_intertwine r ρ T hT a v }`. Set `p : (V →ₗ[ℂ] F) → Submodule A F` to `fun T => if h : ∀ (k : K) (v : V), T (ρ k v) = r k (T v) then LinearMap.range (mkA T h) else ⊥`. Set `s : Set (V →ₗ[ℂ] F)` to `{T | P T}`.

Set `SA : Submodule A F` to `⨆ T ∈ s, p T`. Establish `hpT : ∀ T (hT : T ∈ s), p T = LinearMap.range (mkA T (hP T hT))` using `fun T hT => dif_pos (hP T hT)`. Establish `hpSA : ∀ T (hT : T ∈ s), p T ≤ SA` using `fun T hT => le_iSup₂ (f := fun T (_ : T ∈ s) => p T) T hT`. Establish `memSA : ∀ x : F, x ∈ S ↔ x ∈ SA`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hle : S ≤ SA.restrictScalars ℂ`. Use `iSup₂_le fun T hT => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, rfl⟩`.

Establish `h1 : T v ∈ p T`. Rewrite using `[hpT T hT]`. Conclude with `⟨v, rfl⟩`. Conclude with `hpSA T hT h1`. Conclude with `hle hx`.

Introduce `hx`. Use `Submodule.iSup_induction (fun T => ⨆ (_ : T ∈ s), p T) (motive := fun y => y ∈ S) hx ?_ (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _)` and prove the remaining obligations. Introduce `T y hy`. Distinguish the cases in `hT : T ∈ s`. Establish `hy' : y ∈ p T` using `(iSup_le fun _ => le_rfl : (⨆ (_ : T ∈ s), p T) ≤ p T) hy`.

Rewrite `hy'` using `[hpT T hT]`. Take `⟨v, rfl⟩` from `hy'`. Conclude with `(le_iSup₂ (f := fun T (_ : P T) => LinearMap.range T) T hT : _ ≤ S) ⟨v, rfl⟩`. Rewrite `hy` using `[iSup_neg hT, Submodule.mem_bot]`. Rewrite using `[hy]`.

Conclude with `Submodule.zero_mem _`. Establish `: IsSemisimpleModule A SA` using `isSemisimpleModule_biSup_of_isSemisimpleModule_submodule (fun T hT => by`. Rewrite using `[hpT T hT]`. Conclude with `IsSemisimpleModule.range _)`. Set `f₀ : SA` to `⟨f, (memSA f).mp hf⟩`.

Establish `hf₀ : f₀ ≠ 0` using `fun h => hf0 (congrArg Subtype.val h)`. Choose the witnesses or unpack the hypotheses as in `⟨m, hmN, hm⟩ : ∃ m ≤ Submodule.span A {f₀}, IsSimpleModule A m := by`. Break down `IsSemisimpleModule.eq_bot_or_exists_simple_le (Submodule.span A {f₀}) with h | h` into its components or cases. Conclude with `absurd (Submodule.span_singleton_eq_bot.mp h) hf₀`. Conclude with `h`.

Use `hm` as an intermediate fact. Establish `: Nontrivial m` using `IsSimpleModule.nontrivial A m`. Take `⟨q, hq⟩` from `exists_isCompl m`. Set `π : SA →ₗ[A] m` to `Submodule.projectionOnto m q hq`. Establish `hπleft : ∀ y : m, π y = y` using `fun y => Submodule.projectionOnto_apply_left hq y`.

Establish `hπf : π f₀ ≠ 0`. Introduce `h0`. Establish `hNk : Submodule.span A {f₀} ≤ LinearMap.ker π`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `h0`.

Take `⟨y, hy0⟩` from `exists_ne (0 : m)`. Apply `hy0` to reduce the goal to its premises. Establish `hyk : (y : SA) ∈ LinearMap.ker π` using `hNk (hmN y.2)`. Rewrite `hyk` using `[LinearMap.mem_ker, hπleft]`. Conclude with `hyk`.

Establish `hmemT : ∀ T (hT : T ∈ s) (v : V), mkA T (hP T hT) v ∈ SA` using `fun T hT v => hpSA T hT (by rw [hpT T hT]; exact ⟨v, rfl⟩)`. Choose the witnesses or unpack the hypotheses as in `⟨T, hT, hg⟩ : ∃ T, ∃ hT : T ∈ s, π ∘ₗ LinearMap.codRestrict SA (mkA T (hP T hT)) (hmemT T hT) ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Apply `hπf` to reduce the goal to its premises.

Establish `hle : SA ≤ (LinearMap.ker π).map SA.subtype`. Use `iSup₂_le fun T hT => ?_` and prove the remaining obligations. Rewrite using `[hpT T hT]`. Introduce and unpack `_ ⟨v, rfl⟩`. Use `⟨LinearMap.codRestrict SA (mkA T (hP T hT)) (hmemT T hT) v, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, ← LinearMap.comp_apply, hne T hT, LinearMap.zero_apply]`. Take `⟨y, hy, hyf⟩` from `hle f₀.2`. Establish `hyeq : y = f₀` using `Subtype.ext hyf`. Rewrite using `[← hyeq]`. Conclude with `hy`.

Set `e : V ≃ₗ[A] m` to `LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hg)`. Set `φ₀ : SA →ₗ[A] V` to `e.symm.toLinearMap ∘ₗ π`. Establish `hφ₀f : φ₀ f₀ ≠ 0`. Introduce `h`. Apply `hπf` to reduce the goal to its premises.

Establish `h1 : e (φ₀ f₀) = π f₀` using `e.apply_symm_apply (π f₀)`. Rewrite using `[← h1, h, map_zero]`. Set `ψ : S →ₗ[ℂ] V` to `{ toFun := fun x => φ₀ ⟨x.1, (memSA x.1).mp x.2⟩ map_add' := fun x y => by`. Rewrite using `[← map_add]`. Both sides reduce to the same expression.

Use the proof step `map_smul' := fun c x => by`. Establish `h1 : (⟨c • x.1, (memSA _).mp (S.smul_mem c x.2)⟩ : SA) = algebraMap ℂ A c • (⟨x.1, (memSA _).mp x.2⟩ : SA)` using `Subtype.ext (algebraMap_smul (A := A) c x.1).symm`. Use `show φ₀ ⟨c • x.1, (memSA _).mp (S.smul_mem c x.2)⟩ = c • φ₀ ⟨x.1, (memSA _).mp x.2⟩`. Rewrite using `[h1, map_smul, algebraMap_smul] }`. Take `⟨φ, hφext⟩` from `LinearMap.exists_extend ψ`.

Establish `hφ : ∀ (x : F) (hx : x ∈ S), φ x = φ₀ ⟨x, (memSA x).mp hx⟩` using `fun x hx => LinearMap.congr_fun hφext ⟨x, hx⟩`. Use `⟨φ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ f hf]`. Conclude with `hφ₀f`. Introduce `k x hx`.

Establish `hrk : r k x = (FreeAlgebra.ι ℂ k : A) • x` using `(hιF k x).symm`. Establish `hmem : r k x ∈ S`. Rewrite using `[memSA, hrk]`. Conclude with `SA.smul_mem _ ((memSA _).mp hx)`. Rewrite using `[hφ _ hmem, hφ _ hx, ← hιV k, ← map_smul φ₀]`.

Use `congr 1`. Conclude with `Subtype.ext hrk`.
-/
theorem exists_intertwining_functional {K : Type u_1} {F : Type u_2} {V : Type u_3}
    [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V)
    (hirr : ∀ (W : Submodule ℂ V), (∀ (k : K), ∀ v ∈ W, ρ k v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : (V →ₗ[ℂ] F) → Prop)
    (hP : ∀ (T : V →ₗ[ℂ] F), P T → ∀ (k : K) (v : V), T (ρ k v) = r k (T v)) :
    ∀ f ∈ ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T, f ≠ (0 : F) →
      ∃ (φ : F →ₗ[ℂ] V), φ f ≠ (0 : V) ∧ ∀ (k : K),
        ∀ f' ∈ ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T,
          φ (r k f') = ρ k (φ f') := by
  classical
  intro f hf hf0
  set S := ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T with hSdef

  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply hf0
    have hS : S = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun T _ => ?_)
      rintro _ ⟨v, rfl⟩
      rw [Subsingleton.elim v 0, map_zero]
      exact Submodule.zero_mem _
    rw [hS, Submodule.mem_bot] at hf
    exact hf

  let A := FreeAlgebra ℂ K
  let rA : A →ₐ[ℂ] Module.End ℂ F := FreeAlgebra.lift ℂ r
  let ρA : A →ₐ[ℂ] Module.End ℂ V := FreeAlgebra.lift ℂ ρ
  let : Module A F := Module.compHom F rA.toRingHom
  let : Module A V := Module.compHom V ρA.toRingHom
  have smulF : ∀ (a : A) (x : F), a • x = rA a x := fun _ _ => rfl
  have smulV : ∀ (a : A) (x : V), a • x = ρA a x := fun _ _ => rfl
  have : IsScalarTower ℂ A F := ⟨fun c a x => by
    rw [smulF, smulF, map_smul, LinearMap.smul_apply]⟩
  have : IsScalarTower ℂ A V := ⟨fun c a x => by
    rw [smulV, smulV, map_smul, LinearMap.smul_apply]⟩
  have hιF : ∀ (k : K) (x : F), (FreeAlgebra.ι ℂ k : A) • x = r k x := fun k x => by
    show FreeAlgebra.lift ℂ r (FreeAlgebra.ι ℂ k) x = r k x
    rw [FreeAlgebra.lift_ι_apply]
  have hιV : ∀ (k : K) (v : V), (FreeAlgebra.ι ℂ k : A) • v = ρ k v := fun k v => by
    show FreeAlgebra.lift ℂ ρ (FreeAlgebra.ι ℂ k) v = ρ k v
    rw [FreeAlgebra.lift_ι_apply]

  have hVs : IsSimpleModule A V := by
    refine { toNontrivial := inferInstance, eq_bot_or_eq_top := fun W => ?_ }
    have hWinv : ∀ (k : K), ∀ v ∈ W.restrictScalars ℂ, ρ k v ∈ W.restrictScalars ℂ := by
      intro k v hv
      rw [← hιV]
      exact W.smul_mem _ hv
    rcases hirr (W.restrictScalars ℂ) hWinv with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)

  let mkA : ∀ T : V →ₗ[ℂ] F, (∀ (k : K) (v : V), T (ρ k v) = r k (T v)) → V →ₗ[A] F :=
    fun T hT =>
      { toFun := T
        map_add' := T.map_add
        map_smul' := fun a v => freeAlgebra_lift_intertwine r ρ T hT a v }
  let p : (V →ₗ[ℂ] F) → Submodule A F := fun T =>
    if h : ∀ (k : K) (v : V), T (ρ k v) = r k (T v) then LinearMap.range (mkA T h) else ⊥
  let s : Set (V →ₗ[ℂ] F) := {T | P T}
  let SA : Submodule A F := ⨆ T ∈ s, p T
  have hpT : ∀ T (hT : T ∈ s), p T = LinearMap.range (mkA T (hP T hT)) :=
    fun T hT => dif_pos (hP T hT)
  have hpSA : ∀ T (hT : T ∈ s), p T ≤ SA := fun T hT =>
    le_iSup₂ (f := fun T (_ : T ∈ s) => p T) T hT
  have memSA : ∀ x : F, x ∈ S ↔ x ∈ SA := by
    intro x
    constructor
    · intro hx
      have hle : S ≤ SA.restrictScalars ℂ := by
        refine iSup₂_le fun T hT => ?_
        rintro _ ⟨v, rfl⟩
        have h1 : T v ∈ p T := by
          rw [hpT T hT]
          exact ⟨v, rfl⟩
        exact hpSA T hT h1
      exact hle hx
    · intro hx
      refine Submodule.iSup_induction (fun T => ⨆ (_ : T ∈ s), p T) (motive := fun y => y ∈ S)
        hx ?_ (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _)
      intro T y hy
      by_cases hT : T ∈ s
      · have hy' : y ∈ p T := (iSup_le fun _ => le_rfl : (⨆ (_ : T ∈ s), p T) ≤ p T) hy
        rw [hpT T hT] at hy'
        obtain ⟨v, rfl⟩ := hy'
        exact (le_iSup₂ (f := fun T (_ : P T) => LinearMap.range T) T hT : _ ≤ S) ⟨v, rfl⟩
      · rw [iSup_neg hT, Submodule.mem_bot] at hy
        rw [hy]
        exact Submodule.zero_mem _

  have : IsSemisimpleModule A SA :=
    isSemisimpleModule_biSup_of_isSemisimpleModule_submodule (fun T hT => by
      rw [hpT T hT]
      exact IsSemisimpleModule.range _)
  let f₀ : SA := ⟨f, (memSA f).mp hf⟩
  have hf₀ : f₀ ≠ 0 := fun h => hf0 (congrArg Subtype.val h)

  obtain ⟨m, hmN, hm⟩ : ∃ m ≤ Submodule.span A {f₀}, IsSimpleModule A m := by
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (Submodule.span A {f₀}) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hf₀
    · exact h
  have := hm
  have : Nontrivial m := IsSimpleModule.nontrivial A m
  obtain ⟨q, hq⟩ := exists_isCompl m
  let π : SA →ₗ[A] m := Submodule.projectionOnto m q hq
  have hπleft : ∀ y : m, π y = y := fun y => Submodule.projectionOnto_apply_left hq y
  have hπf : π f₀ ≠ 0 := by
    intro h0
    have hNk : Submodule.span A {f₀} ≤ LinearMap.ker π := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact h0
    obtain ⟨y, hy0⟩ := exists_ne (0 : m)
    apply hy0
    have hyk : (y : SA) ∈ LinearMap.ker π := hNk (hmN y.2)
    rw [LinearMap.mem_ker, hπleft] at hyk
    exact hyk

  have hmemT : ∀ T (hT : T ∈ s) (v : V), mkA T (hP T hT) v ∈ SA := fun T hT v =>
    hpSA T hT (by rw [hpT T hT]; exact ⟨v, rfl⟩)
  obtain ⟨T, hT, hg⟩ : ∃ T, ∃ hT : T ∈ s,
      π ∘ₗ LinearMap.codRestrict SA (mkA T (hP T hT)) (hmemT T hT) ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hπf
    have hle : SA ≤ (LinearMap.ker π).map SA.subtype := by
      refine iSup₂_le fun T hT => ?_
      rw [hpT T hT]
      rintro _ ⟨v, rfl⟩
      refine ⟨LinearMap.codRestrict SA (mkA T (hP T hT)) (hmemT T hT) v, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, ← LinearMap.comp_apply, hne T hT, LinearMap.zero_apply]
    obtain ⟨y, hy, hyf⟩ := hle f₀.2
    have hyeq : y = f₀ := Subtype.ext hyf
    rw [← hyeq]
    exact hy
  let e : V ≃ₗ[A] m := LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hg)
  let φ₀ : SA →ₗ[A] V := e.symm.toLinearMap ∘ₗ π
  have hφ₀f : φ₀ f₀ ≠ 0 := by
    intro h
    apply hπf
    have h1 : e (φ₀ f₀) = π f₀ := e.apply_symm_apply (π f₀)
    rw [← h1, h, map_zero]

  let ψ : S →ₗ[ℂ] V :=
    { toFun := fun x => φ₀ ⟨x.1, (memSA x.1).mp x.2⟩
      map_add' := fun x y => by
        rw [← map_add]
        rfl
      map_smul' := fun c x => by
        have h1 : (⟨c • x.1, (memSA _).mp (S.smul_mem c x.2)⟩ : SA) =
            algebraMap ℂ A c • (⟨x.1, (memSA _).mp x.2⟩ : SA) :=
          Subtype.ext (algebraMap_smul (A := A) c x.1).symm
        show φ₀ ⟨c • x.1, (memSA _).mp (S.smul_mem c x.2)⟩ = c • φ₀ ⟨x.1, (memSA _).mp x.2⟩
        rw [h1, map_smul, algebraMap_smul] }
  obtain ⟨φ, hφext⟩ := LinearMap.exists_extend ψ
  have hφ : ∀ (x : F) (hx : x ∈ S), φ x = φ₀ ⟨x, (memSA x).mp hx⟩ := fun x hx =>
    LinearMap.congr_fun hφext ⟨x, hx⟩
  refine ⟨φ, ?_, ?_⟩
  · rw [hφ f hf]
    exact hφ₀f
  · intro k x hx
    have hrk : r k x = (FreeAlgebra.ι ℂ k : A) • x := (hιF k x).symm
    have hmem : r k x ∈ S := by
      rw [memSA, hrk]
      exact SA.smul_mem _ ((memSA _).mp hx)
    rw [hφ _ hmem, hφ _ hx, ← hιV k, ← map_smul φ₀]
    congr 1
    exact Subtype.ext hrk

end GlobalTheory.IntertwiningFunctional

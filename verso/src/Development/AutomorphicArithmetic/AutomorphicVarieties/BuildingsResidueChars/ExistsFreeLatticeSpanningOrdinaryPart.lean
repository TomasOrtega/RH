import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpanOrdinaryPartEqSupUnitGeneralizedEigenspaces

open IsLocalRing UpperTheory.V.Hi UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

/- English proof (translation)
Introduce `O Ω V ι _ _ _ _ _ _ _ _ _ _ C T ev hinj hbij hTC hint`. Use `haveI : IsAdicComplete (maximalIdeal O) O := IsCNL.complete`. Use `haveI : Finite (ResidueField O) := IsCNL.finite`. Take `⟨hadm, hfin⟩` from `ordAdm_maximalIdeal_and_finite_quotients (R := O) (M := ι → O)`. Establish `hfin'` using `hfin ‹_›`.

Use `set A := algebraMap O Ω with hA`. Set `evC : C →ₗ[Ω] (ι → Ω)` to `ev ∘ₗ C.subtype`. Establish `hevC : Function.Bijective evC`. Use `⟨fun x y hxy => Subtype.ext (hbij.injOn x.2 y.2 hxy), fun w => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `hbij.surjOn (Set.mem_univ w)`.

Conclude with `⟨⟨x, hx⟩, rfl⟩`. Set `e` to `LinearEquiv.ofBijective evC hevC`. Set `g : (ι → Ω) →ₗ[Ω] V` to `C.subtype ∘ₗ e.symm.toLinearMap`. Establish `hgC : ∀ w, g w ∈ C` using `fun w => (e.symm w).2`. Establish `hevg : ∀ w, ev (g w) = w` using `fun w => e.apply_symm_apply w`.

Establish `hgev : ∀ F ∈ C, g (ev F) = F` using `fun F hF => by`. Establish `: e ⟨F, hF⟩ = ev F` using `rfl`. Use `show ((e.symm (ev F) : C) : V) = F`. Rewrite using `[← this, e.symm_apply_apply]`. Establish `hginj : Function.Injective g` using `fun a b h => by rw [← hevg a, ← hevg b, h]`.

Set `T' : Module.End Ω (ι → Ω)` to `ev ∘ₗ T ∘ₗ g`. Establish `hgT : ∀ w, g (T' w) = T (g w)` using `fun w => hgev _ (hTC _ (hgC w))`. Set `jL : (ι → O) →ₗ[O] (ι → Ω)` to `LinearMap.pi (fun i => (Algebra.linearMap O Ω) ∘ₗ LinearMap.proj i)`. Establish `hjL : ∀ v i, jL v i = A (v i)` using `fun v i => rfl`. Establish `hjinj : Function.Injective jL` using `fun v w h => funext fun i => hinj (by rw [← hjL, ← hjL, h])`.

Establish `hmem0 : ∀ x : O, A x ∈ mIm O Ω 0` using `fun x => mem_mIm.2 ⟨x, by simp, rfl⟩`. Establish `hint' : ∀ v : ι → O, ∀ i, ∃ x : O, A x = T' (jL v) i`. Introduce `v i`. Establish `h1 : ∀ i, ev (g (jL v)) i ∈ mIm O Ω 0` using `fun i => by rw [hevg]; exact hmem0 _`. Take `⟨x, -, hx⟩` from `mem_mIm.1 (hint _ (hgC _) h1 i)`.

Conclude with `⟨x, hx⟩`. Use `choose f0 hf0 using hint'`. Set `T₀ : Module.End O (ι → O)` to `{ toFun := f0 map_add' := fun v w => funext fun i => hinj (by`. Simplify using `only [Pi.add_apply, map_add, hf0])`. Use the proof step `map_smul' := fun c v => funext fun i => hinj (by`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, hf0, RingHom.id_apply]`. Rewrite using `[map_smul, ← algebraMap_smul Ω c (jL v), map_smul, Pi.smul_apply, smul_eq_mul]) }`. Establish `hT₀ : ∀ v, T' (jL v) = jL (T₀ v)` using `fun v => funext fun i => (hf0 v i).symm`. Establish `key` using `UpperTheory.span_ordinaryPart_eq_sup_unit_generalized_eigenspaces O Ω ι T₀ T' (fun v => hT₀ v)`. Set `L : (ι → O) →ₗ[O] V` to `(g.restrictScalars O) ∘ₗ jL`.

Establish `hLinj : Function.Injective L` using `hginj.comp hjinj`. Establish `hpow : ∀ m w, g ((T' ^ m) w) = (T ^ m) (g w)` using `pow_intertwine (U := T') (U' := T) (f := g) hgT`. Establish `hpow0 : ∀ m u, jL ((T₀ ^ m) u) = (T' ^ m) (jL u)` using `pow_intertwine (U := T₀) (U' := T') (f := jL) (fun u => (hT₀ u).symm)`. Establish `hcoord : ∀ k (x : ι → O), x ∈ maximalIdeal O ^ k • (⊤ : Submodule O (ι → O)) → ∀ i, x i ∈ maximalIdeal O ^ k`. Introduce `k x hx i`.

Use `map_mem_smul_top (LinearMap.proj (R := O) (φ := fun _ : ι => O) i) _ hx` as an intermediate fact. Simplify using `using this`. Use `⟨(ordPart T₀).map L, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := (ordProjective hadm T₀).1 inferInstance haveI := (ordProjective hadm T₀).2 inferInstance haveI : Module.Free O (ordPart T₀) := Module.free_of_flat_of_isLocalRing`. Conclude with `Module.Free.of_equiv (Submodule.equivMapOfInjective L hLinj _)`.

Establish `key' : (⨆ μ : {μ : Ω // IsIntUnit O μ}, T'.maxGenEigenspace μ.1) = Submodule.span Ω (jL '' (ordPart T₀ : Set (ι → O)))` using `key`. Establish `hspan : Submodule.span Ω (((ordPart T₀).map L : Submodule O V) : Set V) = (Submodule.span Ω (jL '' (ordPart T₀ : Set (ι → O)))).map g`. Rewrite using `[← Submodule.span_image, Submodule.map_coe, Set.image_image]`. Both sides reduce to the same expression. Establish `heig : ∀ μ : Ω, C ⊓ T.maxGenEigenspace μ = (T'.maxGenEigenspace μ).map g`.

Introduce `μ`. Establish `hpowμ : ∀ (k : ℕ) (w : ι → Ω), g (((T' - μ • (1 : Module.End Ω (ι → Ω))) ^ k) w) = ((T - μ • (1 : Module.End Ω V)) ^ k) (g w)` using `pow_intertwine (U := T' - μ • 1) (U' := T - μ • 1) (f := g) (fun w => by simp [hgT])`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxC, hx⟩`.

Take `⟨k, hk⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 hx`. Use `⟨ev x, (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, hginj ?_⟩, hgev x hxC⟩` and prove the remaining obligations. Rewrite using `[hpowμ, hgev x hxC, hk, map_zero]`. Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨k, hk⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 hw`.

Conclude with `⟨hgC w, (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [← hpowμ, hk, map_zero]⟩⟩`. Rewrite using `[hspan, ← key', Submodule.map_iSup]`. Conclude with `iSup_congr fun μ => heig μ.1`. Introduce and unpack `F ⟨v, hv, rfl⟩`. Use `⟨hgC _, fun i => ?_, fun k => ?_⟩` and prove the remaining obligations.

Use `show ev (g (jL v)) i ∈ _`. Rewrite using `[hevg]`. Conclude with `hmem0 _`. Take `⟨n, hn⟩` from `(ordPer hadm hfin' T₀ v).1 hv k`. Use `⟨n, fun i => ?_⟩` and prove the remaining obligations.

Use `show ev ((T ^ (n + 1)) (g (jL v)) - g (jL v)) i ∈ _`. Rewrite using `[← hpow, ← hpow0, ← map_sub, hevg, ← map_sub, hjL]`. Conclude with `mem_mIm.2 ⟨_, hcoord _ _ hn i, rfl⟩`. Introduce `F hF hFi choose v _ hv using fun i => mem_mIm.1 (hFi i)`. Establish `hFv : F = g (jL v)`.

Rewrite using `[← hgev F hF]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(hv i).symm`. Use `⟨L (ordProj (maximalIdeal O) T₀ v), ⟨_, ?_, rfl⟩, fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[← (ordExists hadm T₀).2.1]`. Conclude with `LinearMap.mem_range_self _ _`. Take `⟨N, hN⟩` from `(ordFactLim hadm hfin' T₀ _).2 rfl k`. Use `⟨N, fun j hj i => ?_⟩` and prove the remaining obligations. Rewrite using `[hFv]`.

Use `show ev ((T ^ j.factorial) (g (jL v)) - g (jL (ordProj _ T₀ v))) i ∈ _`. Rewrite using `[← hpow, ← hpow0, ← map_sub, hevg, ← map_sub, hjL]`. Conclude with `mem_mIm.2 ⟨_, hcoord _ _ (hN j hj v) i, rfl⟩`.
-/
theorem UpperTheory.exists_free_lattice_spanning_ordinary_part :
    ∀ (O Ω V ι : Type) [CommRing O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V] [Module O V] [IsScalarTower O Ω V] [Fintype ι] (C : Submodule Ω V) (T : Module.End Ω V) (ev : V →ₗ[Ω] (ι → Ω)), Function.Injective (algebraMap O Ω) → Set.BijOn ev C Set.univ → (∀ F ∈ C, T F ∈ C) → (∀ F ∈ C, (∀ i, ev F i ∈ mIm O Ω 0) → ∀ i, ev (T F) i ∈ mIm O Ω 0) → ∃ S : Submodule O V, Module.Free O S ∧ (⨆ μ : {μ : Ω // IsIntUnit O μ}, C ⊓ T.maxGenEigenspace μ.1) = Submodule.span Ω (S : Set V) ∧ (∀ F ∈ S, F ∈ C ∧ (∀ i, ev F i ∈ mIm O Ω 0) ∧ ∀ k : ℕ, ∃ n : ℕ, ∀ i, ev ((T ^ (n + 1)) F - F) i ∈ mIm O Ω k) ∧ ∀ F ∈ C, (∀ i, ev F i ∈ mIm O Ω 0) → ∃ F' ∈ S, ∀ k : ℕ, ∃ J : ℕ, ∀ j, J ≤ j → ∀ i, ev ((T ^ j.factorial) F - F') i ∈ mIm O Ω k := by
  intro O Ω V ι _ _ _ _ _ _ _ _ _ _ C T ev hinj hbij hTC hint
  haveI : IsAdicComplete (maximalIdeal O) O := IsCNL.complete
  haveI : Finite (ResidueField O) := IsCNL.finite
  obtain ⟨hadm, hfin⟩ := ordAdm_maximalIdeal_and_finite_quotients (R := O) (M := ι → O)
  have hfin' := hfin ‹_›
  set A := algebraMap O Ω with hA
  let evC : C →ₗ[Ω] (ι → Ω) := ev ∘ₗ C.subtype
  have hevC : Function.Bijective evC := by
    refine ⟨fun x y hxy => Subtype.ext (hbij.injOn x.2 y.2 hxy), fun w => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn (Set.mem_univ w)
    exact ⟨⟨x, hx⟩, rfl⟩
  let e := LinearEquiv.ofBijective evC hevC
  let g : (ι → Ω) →ₗ[Ω] V := C.subtype ∘ₗ e.symm.toLinearMap
  have hgC : ∀ w, g w ∈ C := fun w => (e.symm w).2
  have hevg : ∀ w, ev (g w) = w := fun w => e.apply_symm_apply w
  have hgev : ∀ F ∈ C, g (ev F) = F := fun F hF => by
    have : e ⟨F, hF⟩ = ev F := rfl
    show ((e.symm (ev F) : C) : V) = F
    rw [← this, e.symm_apply_apply]
  have hginj : Function.Injective g := fun a b h => by rw [← hevg a, ← hevg b, h]
  let T' : Module.End Ω (ι → Ω) := ev ∘ₗ T ∘ₗ g
  have hgT : ∀ w, g (T' w) = T (g w) := fun w => hgev _ (hTC _ (hgC w))
  let jL : (ι → O) →ₗ[O] (ι → Ω) := LinearMap.pi (fun i => (Algebra.linearMap O Ω) ∘ₗ LinearMap.proj i)
  have hjL : ∀ v i, jL v i = A (v i) := fun v i => rfl
  have hjinj : Function.Injective jL := fun v w h => funext fun i => hinj (by rw [← hjL, ← hjL, h])
  have hmem0 : ∀ x : O, A x ∈ mIm O Ω 0 := fun x => mem_mIm.2 ⟨x, by simp, rfl⟩
  have hint' : ∀ v : ι → O, ∀ i, ∃ x : O, A x = T' (jL v) i := by
    intro v i
    have h1 : ∀ i, ev (g (jL v)) i ∈ mIm O Ω 0 := fun i => by rw [hevg]; exact hmem0 _
    obtain ⟨x, -, hx⟩ := mem_mIm.1 (hint _ (hgC _) h1 i)
    exact ⟨x, hx⟩
  choose f0 hf0 using hint'
  let T₀ : Module.End O (ι → O) :=
    { toFun := f0
      map_add' := fun v w => funext fun i => hinj (by
        simp only [Pi.add_apply, map_add, hf0])
      map_smul' := fun c v => funext fun i => hinj (by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, hf0, RingHom.id_apply]
        rw [map_smul, ← algebraMap_smul Ω c (jL v), map_smul, Pi.smul_apply, smul_eq_mul]) }
  have hT₀ : ∀ v, T' (jL v) = jL (T₀ v) := fun v => funext fun i => (hf0 v i).symm
  have key := UpperTheory.span_ordinaryPart_eq_sup_unit_generalized_eigenspaces O Ω ι T₀ T' (fun v => hT₀ v)
  let L : (ι → O) →ₗ[O] V := (g.restrictScalars O) ∘ₗ jL
  have hLinj : Function.Injective L := hginj.comp hjinj
  have hpow : ∀ m w, g ((T' ^ m) w) = (T ^ m) (g w) := pow_intertwine (U := T') (U' := T) (f := g) hgT
  have hpow0 : ∀ m u, jL ((T₀ ^ m) u) = (T' ^ m) (jL u) :=
    pow_intertwine (U := T₀) (U' := T') (f := jL) (fun u => (hT₀ u).symm)
  have hcoord : ∀ k (x : ι → O), x ∈ maximalIdeal O ^ k • (⊤ : Submodule O (ι → O)) → ∀ i, x i ∈ maximalIdeal O ^ k := by
    intro k x hx i
    have := map_mem_smul_top (LinearMap.proj (R := O) (φ := fun _ : ι => O) i) _ hx
    simpa using this
  refine ⟨(ordPart T₀).map L, ?_, ?_, ?_, ?_⟩
  · haveI := (ordProjective hadm T₀).1 inferInstance
    haveI := (ordProjective hadm T₀).2 inferInstance
    haveI : Module.Free O (ordPart T₀) := Module.free_of_flat_of_isLocalRing
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective L hLinj _)
  · have key' : (⨆ μ : {μ : Ω // IsIntUnit O μ}, T'.maxGenEigenspace μ.1) =
        Submodule.span Ω (jL '' (ordPart T₀ : Set (ι → O))) := key
    have hspan : Submodule.span Ω (((ordPart T₀).map L : Submodule O V) : Set V) =
        (Submodule.span Ω (jL '' (ordPart T₀ : Set (ι → O)))).map g := by
      rw [← Submodule.span_image, Submodule.map_coe, Set.image_image]
      rfl
    have heig : ∀ μ : Ω, C ⊓ T.maxGenEigenspace μ = (T'.maxGenEigenspace μ).map g := by
      intro μ
      have hpowμ : ∀ (k : ℕ) (w : ι → Ω), g (((T' - μ • (1 : Module.End Ω (ι → Ω))) ^ k) w) =
          ((T - μ • (1 : Module.End Ω V)) ^ k) (g w) :=
        pow_intertwine (U := T' - μ • 1) (U' := T - μ • 1) (f := g) (fun w => by simp [hgT])
      ext x
      constructor
      · rintro ⟨hxC, hx⟩
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
        refine ⟨ev x, (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, hginj ?_⟩, hgev x hxC⟩
        rw [hpowμ, hgev x hxC, hk, map_zero]
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hw
        exact ⟨hgC w, (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [← hpowμ, hk, map_zero]⟩⟩
    rw [hspan, ← key', Submodule.map_iSup]
    exact iSup_congr fun μ => heig μ.1
  · rintro F ⟨v, hv, rfl⟩
    refine ⟨hgC _, fun i => ?_, fun k => ?_⟩
    · show ev (g (jL v)) i ∈ _
      rw [hevg]
      exact hmem0 _
    · obtain ⟨n, hn⟩ := (ordPer hadm hfin' T₀ v).1 hv k
      refine ⟨n, fun i => ?_⟩
      show ev ((T ^ (n + 1)) (g (jL v)) - g (jL v)) i ∈ _
      rw [← hpow, ← hpow0, ← map_sub, hevg, ← map_sub, hjL]
      exact mem_mIm.2 ⟨_, hcoord _ _ hn i, rfl⟩
  · intro F hF hFi
    choose v _ hv using fun i => mem_mIm.1 (hFi i)
    have hFv : F = g (jL v) := by
      rw [← hgev F hF]
      congr 1
      funext i
      exact (hv i).symm
    refine ⟨L (ordProj (maximalIdeal O) T₀ v), ⟨_, ?_, rfl⟩, fun k => ?_⟩
    · rw [← (ordExists hadm T₀).2.1]
      exact LinearMap.mem_range_self _ _
    · obtain ⟨N, hN⟩ := (ordFactLim hadm hfin' T₀ _).2 rfl k
      refine ⟨N, fun j hj i => ?_⟩
      rw [hFv]
      show ev ((T ^ j.factorial) (g (jL v)) - g (jL (ordProj _ T₀ v))) i ∈ _
      rw [← hpow, ← hpow0, ← map_sub, hevg, ← map_sub, hjL]
      exact mem_mIm.2 ⟨_, hcoord _ _ (hN j hj v) i, rfl⟩

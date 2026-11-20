import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

open scoped TensorProduct in
/- English proof (translation)
Establish `hzero : ∀ μ ∈ L, ∀ t : Set N, Submodule.span R t = ⊤ → (∀ y ∈ t, μ y = 0) → μ = 0`. Introduce `μ hμ t ht h0`. Use `AddMonoidHom.ext fun y => ?_` and prove the remaining obligations. Use `show μ y = 0`. Establish `hy : y ∈ Submodule.span R t` using `ht ▸ Submodule.mem_top`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact h0 x hx`. Consider the case `zero => exact map_zero μ`. Consider the case `add x z _ _ hx hz => rw [map_add, hx, hz, add_zero]`. Consider the case `smul b x _ hx => rw [(hL μ).1 hμ b x, hx, mul_zero]`.

Establish `hfin : Module.Finite F L`. Take `⟨n, s, hsp⟩` from `Module.Finite.exists_fin (R := R) (M := N)`. Set `Φ : L →ₗ[F] (Fin n → F)` to `{ toFun := fun μ i => (μ : N →+ F) (s i) map_add' := fun μ ν => by ext i; rfl map_smul' := fun c μ => by ext i; rfl }`. Use `Module.Finite.of_injective Φ ?_` and prove the remaining obligations. Use `(injective_iff_map_eq_zero Φ).2 fun μ hμ => Subtype.ext ?_` and prove the remaining obligations.

Use `hzero _ μ.2 _ hsp ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `congrFun hμ i`. Establish `hkill : ∀ y : N, (∀ μ ∈ L, μ y = 0) → y ∈ RingHom.ker φ • (⊤ : Submodule R N)`. Introduce `y hy`.

Assume the negation of the conclusion as `hny`. Use `set K := RingHom.ker φ`. Use `set P := K • (⊤ : Submodule R N)`. Establish `ht : Module.IsTorsionBySet R (N ⧸ P) (K : Set R)` using `(Module.isTorsionBySet_quotient_iff P _).2 fun x r hr => Submodule.smul_mem_smul hr Submodule.mem_top`. Use `letI : Module (R ⧸ K) (N ⧸ P) := ht.module`.

Set `e` to `RingHom.quotientKerEquivOfSurjective hs`. Use `letI : Module F (N ⧸ P) := Module.compHom (N ⧸ P) (e.symm : F →+* R ⧸ K)`. Establish `hcomp : ∀ (b : R) (q : N ⧸ P), φ b • q = b • q`. Introduce `b q`. Use `show (e.symm (φ b)) • q = b • q`.

Rewrite using `[← RingHom.quotientKerEquivOfSurjective_apply_mk hs b, RingEquiv.symm_apply_apply]`. Conclude with `Module.IsTorsionBySet.mk_smul ht b q`. Establish `hq : Submodule.Quotient.mk (p` using `P) y ≠ 0 := by`. Rewrite using `[Ne, Submodule.Quotient.mk_eq_zero]` and apply the resulting hypothesis. Take `⟨f, hf⟩ : ∃ f : Module.Dual F (N ⧸ P), f (Submodule.Quotient.mk y) ≠ 0` from `by by_contra! h`.

Conclude with `hq ((Module.forall_dual_apply_eq_zero_iff F _).1 h)`. Set `μ : N →+ F` to `f.toAddMonoidHom.comp P.mkQ.toAddMonoidHom`. Establish `hμ : μ ∈ L` using `(hL μ).2 fun b z => by show f (Submodule.Quotient.mk (b • z)) = φ b * f (Submodule.Quotient.mk z)`. Rewrite using `[Submodule.Quotient.mk_smul, ← hcomp, map_smul, smul_eq_mul]`. Conclude with `hf (hy μ hμ)`.

Use `⟨hfin, hkill, ?_⟩` and prove the remaining obligations. Introduce `ξ`. Use `haveI := hfin`. Set `ev : N → Module.Dual F L` to `fun y => { toFun := fun μ => (μ : N →+ F) y map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Set `W : Submodule F (Module.Dual F L)` to `{ carrier := {a | ∃ y : N, ∀ μ : L, (μ : N →+ F) y = a μ} add_mem' := by`.

Introduce and unpack `a b ⟨y, hy⟩ ⟨z, hz⟩`. Conclude with `⟨y + z, fun μ => by rw [map_add, hy, hz]; rfl⟩`. Use the proof step `zero_mem' := ⟨0, fun μ => by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨y, hy⟩`.

Take `⟨b, rfl⟩` from `hs c`. Conclude with `⟨b • y, fun μ => by rw [(hL _).1 μ.2, hy]; rfl⟩ }`. Assume the negation of the conclusion as `hξ`. Express the relevant statement in the definitionally equal form `ξ ∉ W at hξ`. Take `⟨f, hf, hfW⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hξ inferInstance`.

Use `set μ := (Module.evalEquiv F L).symm f with hμdef`. Establish `hμ0 : μ = 0`. Use `Subtype.ext (AddMonoidHom.ext fun y => ?_)` and prove the remaining obligations. Establish `hm : f (ev y) ∈ W.map f` using `Submodule.mem_map_of_mem ⟨y, fun _ => rfl⟩`. Rewrite `hm` using `[hfW, Submodule.mem_bot]`.

Use `Module.apply_evalEquiv_symm_apply F L (ev y) f` as an intermediate fact. Rewrite `this` using `[← hμdef, hm]`. Conclude with `this`. Establish `hfe : f = Module.evalEquiv F L μ` using `((Module.evalEquiv F L).apply_symm_apply f).symm`. Rewrite `hf` using `[hfe, hμ0, map_zero]`.

Conclude with `hf rfl`.
-/
private theorem UpperTheory.V.Pa.dual_functionals_finite_separating_surjective {R F N : Type} [CommRing R] [Field F] [AddCommGroup N] [Module R N]
    [Module.Finite R N] (φ : R →+* F) (hs : Function.Surjective φ) (L : Submodule F (N →+ F))
    (hL : ∀ μ, μ ∈ L ↔ ∀ (b : R) y, μ (b • y) = φ b * μ y) :
    Module.Finite F L ∧ (∀ y : N, (∀ μ ∈ L, μ y = 0) → y ∈ RingHom.ker φ • (⊤ : Submodule R N)) ∧
      ∀ ξ : Module.Dual F L, ∃ y : N, ∀ μ : L, (μ : N →+ F) y = ξ μ := by
  classical
  have hzero : ∀ μ ∈ L, ∀ t : Set N, Submodule.span R t = ⊤ → (∀ y ∈ t, μ y = 0) → μ = 0 := by
    intro μ hμ t ht h0
    refine AddMonoidHom.ext fun y => ?_
    show μ y = 0
    have hy : y ∈ Submodule.span R t := ht ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact h0 x hx
    | zero => exact map_zero μ
    | add x z _ _ hx hz => rw [map_add, hx, hz, add_zero]
    | smul b x _ hx => rw [(hL μ).1 hμ b x, hx, mul_zero]
  have hfin : Module.Finite F L := by
    obtain ⟨n, s, hsp⟩ := Module.Finite.exists_fin (R := R) (M := N)
    let Φ : L →ₗ[F] (Fin n → F) :=
      { toFun := fun μ i => (μ : N →+ F) (s i)
        map_add' := fun μ ν => by ext i; rfl
        map_smul' := fun c μ => by ext i; rfl }
    refine Module.Finite.of_injective Φ ?_
    refine (injective_iff_map_eq_zero Φ).2 fun μ hμ => Subtype.ext ?_
    refine hzero _ μ.2 _ hsp ?_
    rintro _ ⟨i, rfl⟩
    exact congrFun hμ i
  have hkill : ∀ y : N, (∀ μ ∈ L, μ y = 0) → y ∈ RingHom.ker φ • (⊤ : Submodule R N) := by
    intro y hy
    by_contra hny
    set K := RingHom.ker φ
    set P := K • (⊤ : Submodule R N)
    have ht : Module.IsTorsionBySet R (N ⧸ P) (K : Set R) :=
      (Module.isTorsionBySet_quotient_iff P _).2 fun x r hr =>
        Submodule.smul_mem_smul hr Submodule.mem_top
    letI : Module (R ⧸ K) (N ⧸ P) := ht.module
    let e := RingHom.quotientKerEquivOfSurjective hs
    letI : Module F (N ⧸ P) := Module.compHom (N ⧸ P) (e.symm : F →+* R ⧸ K)
    have hcomp : ∀ (b : R) (q : N ⧸ P), φ b • q = b • q := by
      intro b q
      show (e.symm (φ b)) • q = b • q
      rw [← RingHom.quotientKerEquivOfSurjective_apply_mk hs b, RingEquiv.symm_apply_apply]
      exact Module.IsTorsionBySet.mk_smul ht b q
    have hq : Submodule.Quotient.mk (p := P) y ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual F (N ⧸ P), f (Submodule.Quotient.mk y) ≠ 0 := by
      by_contra! h
      exact hq ((Module.forall_dual_apply_eq_zero_iff F _).1 h)
    let μ : N →+ F := f.toAddMonoidHom.comp P.mkQ.toAddMonoidHom
    have hμ : μ ∈ L := (hL μ).2 fun b z => by
      show f (Submodule.Quotient.mk (b • z)) = φ b * f (Submodule.Quotient.mk z)
      rw [Submodule.Quotient.mk_smul, ← hcomp, map_smul, smul_eq_mul]
    exact hf (hy μ hμ)
  refine ⟨hfin, hkill, ?_⟩
  intro ξ
  haveI := hfin
  let ev : N → Module.Dual F L := fun y =>
    { toFun := fun μ => (μ : N →+ F) y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let W : Submodule F (Module.Dual F L) :=
    { carrier := {a | ∃ y : N, ∀ μ : L, (μ : N →+ F) y = a μ}
      add_mem' := by
        rintro a b ⟨y, hy⟩ ⟨z, hz⟩
        exact ⟨y + z, fun μ => by rw [map_add, hy, hz]; rfl⟩
      zero_mem' := ⟨0, fun μ => by simp⟩
      smul_mem' := by
        rintro c a ⟨y, hy⟩
        obtain ⟨b, rfl⟩ := hs c
        exact ⟨b • y, fun μ => by rw [(hL _).1 μ.2, hy]; rfl⟩ }
  by_contra hξ
  change ξ ∉ W at hξ
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hξ inferInstance
  set μ := (Module.evalEquiv F L).symm f with hμdef
  have hμ0 : μ = 0 := by
    refine Subtype.ext (AddMonoidHom.ext fun y => ?_)
    have hm : f (ev y) ∈ W.map f := Submodule.mem_map_of_mem ⟨y, fun _ => rfl⟩
    rw [hfW, Submodule.mem_bot] at hm
    have := Module.apply_evalEquiv_symm_apply F L (ev y) f
    rw [← hμdef, hm] at this
    exact this
  have hfe : f = Module.evalEquiv F L μ := ((Module.evalEquiv F L).apply_symm_apply f).symm
  rw [hfe, hμ0, map_zero] at hf
  exact hf rfl

/- English proof (translation)
Introduce `l _ S`. Establish `hs : Function.Surjective S.rF` using `fun c => by`. Take `⟨o, ho⟩` from `S.oo_surj c`. Conclude with `⟨_, ho⟩`. Use `haveI := S.U.fin`.

Use `haveI hN : Module.Finite S.Bh S.U.N := Module.Finite.of_surjective (Submodule.linearProjOfIsCompl S.U.N 1 S.U.compl.symm) fun x => ⟨x, Submodule.linearProjOfIsCompl_apply_left _ x⟩`. Take `⟨h1, h2, h3⟩` from `UpperTheory.V.Pa.dual_functionals_finite_separating_surjective S.rF hs S.La (fun μ => Iff.rfl)`. Use `⟨h1, fun y hy => ?_, h3⟩` and prove the remaining obligations. Rewrite using `[← S.rF_ker]`. Conclude with `h2 y hy`.
-/
theorem UpperTheory.V.Pa.laDual :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), Module.Finite S.F S.La ∧ (∀ y : S.U.N, (∀ μ ∈ S.La, μ y = 0) → y ∈ maximalIdeal S.Bh • (⊤ : Submodule S.Bh S.U.N)) ∧ ∀ ξ : Module.Dual S.F S.La, ∃ y : S.U.N, ∀ μ : S.La, (μ : S.U.N →+ S.F) y = ξ μ := by
  intro l _ S
  have hs : Function.Surjective S.rF := fun c => by
    obtain ⟨o, ho⟩ := S.oo_surj c
    exact ⟨_, ho⟩
  haveI := S.U.fin
  haveI hN : Module.Finite S.Bh S.U.N :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl S.U.N 1 S.U.compl.symm)
      fun x => ⟨x, Submodule.linearProjOfIsCompl_apply_left _ x⟩
  obtain ⟨h1, h2, h3⟩ := UpperTheory.V.Pa.dual_functionals_finite_separating_surjective S.rF hs S.La (fun μ => Iff.rfl)
  refine ⟨h1, fun y hy => ?_, h3⟩
  rw [← S.rF_ker]
  exact h2 y hy

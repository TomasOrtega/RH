import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlSel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LaInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LaDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.KapF

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Establish `key : ∀ (a b : Fin g → F) (v : V), v - ∑ j, a j • κ j ∈ B → v - ∑ j, b j • κ j ∈ B → a = b`. Introduce `a b v ha hb`. Establish `h` using `hI (b - a) (by`. Establish `e : ∑ j, (b - a) j • κ j = (v - ∑ j, a j • κ j) - (v - ∑ j, b j • κ j)`. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `B.sub_mem ha hb)`. Conclude with `(sub_eq_zero.1 h).symm`. Use `choose c hc using hK`.

Set `C : L →ₗ[F] (Fin g → F)` to `{ toFun := fun μ => c μ μ.2 map_add' := fun μ ν => by`. Use `key _ _ _ (hc _ (μ + ν).2) ?_` and prove the remaining obligations. Establish `e : T ((μ + ν : L) : N →+ F) - ∑ j, (c μ μ.2 + c ν ν.2) j • κ j = (T μ - ∑ j, c μ μ.2 j • κ j) + (T ν - ∑ j, c ν ν.2 j • κ j)`. Simplify using `only [Submodule.coe_add, map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `B.add_mem (hc _ μ.2) (hc _ ν.2)`. Use the proof step `map_smul' := fun a μ => by`. Use `key _ _ _ (hc _ (a • μ).2) ?_` and prove the remaining obligations. Establish `e : T ((a • μ : L) : N →+ F) - ∑ j, (a • c μ μ.2) j • κ j = a • (T μ - ∑ j, c μ μ.2 j • κ j)`.

Simplify using `only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_smul, smul_sub, Finset.smul_sum]`. Rewrite using `[RingHom.id_apply, e]`. Conclude with `B.smul_mem a (hc _ μ.2) }`. Establish `hCinj : Function.Injective C`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `μ hμ`. Establish `h0 : c μ μ.2 = 0` using `hμ`. Establish `h1` using `hc μ μ.2`. Rewrite `h1` using `[h0]`. Simplify using `only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, sub_zero] at h1`.

Conclude with `Subtype.ext (hT μ μ.2 h1)`. Establish `hCj : ∀ j, ∃ y : N, ∀ μ : L, (μ : N →+ F) y = C μ j` using `fun j => hD ((LinearMap.proj j).comp C)`. Use `choose m hm using hCj`. Use `⟨m, fun μ hμ => ?_, ?_⟩` and prove the remaining obligations. Establish `e : ∀ j, μ (m j) = c μ hμ j` using `fun j => hm j ⟨μ, hμ⟩`.

Simplify using `only [e]`. Conclude with `hc μ hμ`. Apply `top_unique` to reduce the goal to its premises. Apply `Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson ⊥)` to reduce the goal to its premises. Introduce `y _`.

Set `ev : Module.Dual F L` to `{ toFun := fun μ => (μ : N →+ F) y map_add' := fun μ ν => rfl map_smul' := fun a μ => rfl }`. Take `⟨ψ, hψ⟩` from `LinearMap.dualMap_surjective_of_injective hCinj ev`. Set `a : Fin g → F` to `fun j => ψ fun i => if j = i then 1 else 0`. Establish `hev : ∀ μ : L, (μ : N →+ F) y = ∑ j, C μ j * a j`. Introduce `μ`.

Establish `h1` using `LinearMap.congr_fun hψ μ`. Rewrite `h1` using `[LinearMap.dualMap_apply, LinearMap.pi_apply_eq_sum_univ]`. Conclude with `h1.symm`. Set `b : Fin g → R` to `fun j => Function.surjInv hs (a j)`. Establish `hb : ∀ j, φ (b j) = a j` using `fun j => Function.surjInv_eq hs (a j)`.

Establish `hy : y - ∑ j, b j • m j ∈ maximalIdeal R • (⊤ : Submodule R N)`. Apply `hsep` to reduce the goal to its premises. Introduce `μ hμ`. Establish `e : ∀ j, μ (m j) = C ⟨μ, hμ⟩ j` using `fun j => hm j ⟨μ, hμ⟩`. Establish `ev2 : μ y = ∑ j, C ⟨μ, hμ⟩ j * a j` using `hev ⟨μ, hμ⟩`.

Rewrite using `[map_sub, map_sum, ev2]`. Simplify using `only [hL μ hμ, hb, e]`. Rewrite using `[sub_eq_zero]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `e : y = (y - ∑ j, b j • m j) + ∑ j, b j • m j` using `by abel`.

Rewrite using `[e]`. Use `Submodule.add_mem _ (Submodule.mem_sup_right hy) (Submodule.mem_sup_left ?_)` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
private theorem UpperTheory.V.Pa.exists_dual_functional_complement {R F N V : Type} [CommRing R] [IsLocalRing R] [Field F] [AddCommGroup N]
    [Module R N] [Module.Finite R N] [AddCommGroup V] [Module F V] {g : ℕ}
    (L : Submodule F (N →+ F)) (B : Submodule F V) (κ : Fin g → V) (T : (N →+ F) →ₗ[F] V) (φ : R →+* F)
    (hs : Function.Surjective φ)
    (hL : ∀ μ ∈ L, ∀ (b : R) y, μ (b • y) = φ b * μ y)
    (hK : ∀ μ ∈ L, ∃ c : Fin g → F, T μ - ∑ j, c j • κ j ∈ B)
    (hI : ∀ c : Fin g → F, ∑ j, c j • κ j ∈ B → c = 0)
    (hT : ∀ μ ∈ L, T μ ∈ B → μ = 0)
    [Module.Finite F L]
    (hsep : ∀ y : N, (∀ μ ∈ L, μ y = 0) → y ∈ maximalIdeal R • (⊤ : Submodule R N))
    (hD : ∀ ξ : Module.Dual F L, ∃ y : N, ∀ μ : L, (μ : N →+ F) y = ξ μ) :
    ∃ m : Fin g → N, (∀ μ ∈ L, T μ - ∑ j, μ (m j) • κ j ∈ B) ∧ Submodule.span R (Set.range m) = ⊤ := by
  classical
  have key : ∀ (a b : Fin g → F) (v : V), v - ∑ j, a j • κ j ∈ B → v - ∑ j, b j • κ j ∈ B → a = b := by
    intro a b v ha hb
    have h := hI (b - a) (by
      have e : ∑ j, (b - a) j • κ j = (v - ∑ j, a j • κ j) - (v - ∑ j, b j • κ j) := by
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
        abel
      rw [e]
      exact B.sub_mem ha hb)
    exact (sub_eq_zero.1 h).symm
  choose c hc using hK
  let C : L →ₗ[F] (Fin g → F) :=
    { toFun := fun μ => c μ μ.2
      map_add' := fun μ ν => by
        refine key _ _ _ (hc _ (μ + ν).2) ?_
        have e : T ((μ + ν : L) : N →+ F) - ∑ j, (c μ μ.2 + c ν ν.2) j • κ j
            = (T μ - ∑ j, c μ μ.2 j • κ j) + (T ν - ∑ j, c ν ν.2 j • κ j) := by
          simp only [Submodule.coe_add, map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
          abel
        rw [e]
        exact B.add_mem (hc _ μ.2) (hc _ ν.2)
      map_smul' := fun a μ => by
        refine key _ _ _ (hc _ (a • μ).2) ?_
        have e : T ((a • μ : L) : N →+ F) - ∑ j, (a • c μ μ.2) j • κ j
            = a • (T μ - ∑ j, c μ μ.2 j • κ j) := by
          simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_smul, smul_sub,
            Finset.smul_sum]
        rw [RingHom.id_apply, e]
        exact B.smul_mem a (hc _ μ.2) }
  have hCinj : Function.Injective C := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro μ hμ
    have h0 : c μ μ.2 = 0 := hμ
    have h1 := hc μ μ.2
    rw [h0] at h1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, sub_zero] at h1
    exact Subtype.ext (hT μ μ.2 h1)
  have hCj : ∀ j, ∃ y : N, ∀ μ : L, (μ : N →+ F) y = C μ j := fun j => hD ((LinearMap.proj j).comp C)
  choose m hm using hCj
  refine ⟨m, fun μ hμ => ?_, ?_⟩
  · have e : ∀ j, μ (m j) = c μ hμ j := fun j => hm j ⟨μ, hμ⟩
    simp only [e]
    exact hc μ hμ
  · apply top_unique
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson ⊥)
    intro y _
    let ev : Module.Dual F L :=
      { toFun := fun μ => (μ : N →+ F) y
        map_add' := fun μ ν => rfl
        map_smul' := fun a μ => rfl }
    obtain ⟨ψ, hψ⟩ := LinearMap.dualMap_surjective_of_injective hCinj ev
    let a : Fin g → F := fun j => ψ fun i => if j = i then 1 else 0
    have hev : ∀ μ : L, (μ : N →+ F) y = ∑ j, C μ j * a j := by
      intro μ
      have h1 := LinearMap.congr_fun hψ μ
      rw [LinearMap.dualMap_apply, LinearMap.pi_apply_eq_sum_univ] at h1
      exact h1.symm
    let b : Fin g → R := fun j => Function.surjInv hs (a j)
    have hb : ∀ j, φ (b j) = a j := fun j => Function.surjInv_eq hs (a j)
    have hy : y - ∑ j, b j • m j ∈ maximalIdeal R • (⊤ : Submodule R N) := by
      apply hsep
      intro μ hμ
      have e : ∀ j, μ (m j) = C ⟨μ, hμ⟩ j := fun j => hm j ⟨μ, hμ⟩
      have ev2 : μ y = ∑ j, C ⟨μ, hμ⟩ j * a j := hev ⟨μ, hμ⟩
      rw [map_sub, map_sum, ev2]
      simp only [hL μ hμ, hb, e]
      rw [sub_eq_zero]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have e : y = (y - ∑ j, b j • m j) + ∑ j, b j • m j := by abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_right hy) (Submodule.mem_sup_left ?_)
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Introduce `l _ S hK3`. Use `haveI := S.d6`. Use `haveI := S.U.fin`. Use `haveI : Module.Finite S.Bh S.U.N := inferInstance`. Set `Bs : Submodule S.F (S.G.G₀ → Matrix (Fin S.n) (Fin S.n) S.F)` to `{ carrier := BdM S.h S.x S.F add_mem' := by`.

Introduce and unpack `_ _ ⟨Y₁, h₁, t₁, rfl⟩ ⟨Y₂, h₂, t₂, rfl⟩`. Use `⟨Y₁ + Y₂, Submodule.add_mem _ h₁ h₂, by rw [Matrix.transpose_add, t₁, t₂, neg_add], ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Simplify using `only [dY, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]`. Normalize the expressions using the abelian group laws.

Use the proof step `zero_mem' := ⟨0, Submodule.zero_mem _, by simp, by funext g; simp [dY]⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `a _ ⟨Y, hY, t, rfl⟩`. Use `⟨a • Y, fun i j => ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩, by rw [Matrix.transpose_smul, t, smul_neg], ?_⟩` and prove the remaining obligations. Establish `h0` using `(hY i j).1 hij`.

Rewrite `h0`, the goal using `[Submodule.mem_bot]`. Simplify using `[h0]`. Use function extensionality and compare the values at `g`. Simplify using `only [dY, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_sub] }`. Set `T : (S.U.N →+ S.F) →ₗ[S.F] (S.G.G₀ → Matrix (Fin S.n) (Fin S.n) S.F)` to `{ toFun := S.laC map_add' := fun μ ν => by`.

Establish `h` using `(alSel l S).2.2.2 (Fin 2) ![1, 1] ![μ, ν]`. Simplify `h` using `[Fin.sum_univ_two]`. Use the proof step `map_smul' := fun a μ => by`. Establish `h` using `(alSel l S).2.2.2 Unit (fun _ => a) (fun _ => μ)`. Simplify using `using h }`.

Establish `hs : Function.Surjective S.rF` using `fun z => by`. Take `⟨o, ho⟩` from `S.oo_surj z`. Conclude with `⟨_, ho⟩`. Take `⟨hfin, hsep, hD⟩` from `laDual l S`. Take `⟨m, h1, h2⟩` from `UpperTheory.V.Pa.exists_dual_functional_complement (R := S.Bh) S.La Bs (kapF S.h S.k) T S.rF hs (fun μ hμ => hμ) (fun μ hμ => hK3 _ ((alSel l S).2.1 μ hμ).1 ((alSel l S).2.1 μ hμ).2) (indF l S.L S.G S.G0 S.h S.n S.x S.k) (laInj l S) hsep hD`.

Conclude with `⟨m, h1, h2⟩`.
-/
theorem UpperTheory.V.Pa.dualEx :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), SelmerSpannedByKappaLaurent S.h S.k → ∃ m : Fin S.k.g → S.U.N, S.DualM m ∧ Submodule.span S.Bh (Set.range m) = ⊤ := by
  intro l _ S hK3
  haveI := S.d6
  haveI := S.U.fin
  haveI : Module.Finite S.Bh S.U.N := inferInstance
  let Bs : Submodule S.F (S.G.G₀ → Matrix (Fin S.n) (Fin S.n) S.F) :=
    { carrier := BdM S.h S.x S.F
      add_mem' := by
        rintro _ _ ⟨Y₁, h₁, t₁, rfl⟩ ⟨Y₂, h₂, t₂, rfl⟩
        refine ⟨Y₁ + Y₂, Submodule.add_mem _ h₁ h₂, by rw [Matrix.transpose_add, t₁, t₂, neg_add], ?_⟩
        funext g
        simp only [dY, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
        abel
      zero_mem' := ⟨0, Submodule.zero_mem _, by simp, by funext g; simp [dY]⟩
      smul_mem' := by
        rintro a _ ⟨Y, hY, t, rfl⟩
        refine ⟨a • Y, fun i j => ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩,
          by rw [Matrix.transpose_smul, t, smul_neg], ?_⟩
        · have h0 := (hY i j).1 hij
          rw [Submodule.mem_bot] at h0 ⊢
          simp [h0]
        · funext g
          simp only [dY, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_sub] }
  let T : (S.U.N →+ S.F) →ₗ[S.F] (S.G.G₀ → Matrix (Fin S.n) (Fin S.n) S.F) :=
    { toFun := S.laC
      map_add' := fun μ ν => by
        have h := (alSel l S).2.2.2 (Fin 2) ![1, 1] ![μ, ν]
        simpa [Fin.sum_univ_two] using h
      map_smul' := fun a μ => by
        have h := (alSel l S).2.2.2 Unit (fun _ => a) (fun _ => μ)
        simpa using h }
  have hs : Function.Surjective S.rF := fun z => by
    obtain ⟨o, ho⟩ := S.oo_surj z
    exact ⟨_, ho⟩
  obtain ⟨hfin, hsep, hD⟩ := laDual l S
  obtain ⟨m, h1, h2⟩ := UpperTheory.V.Pa.exists_dual_functional_complement (R := S.Bh) S.La Bs (kapF S.h S.k) T S.rF hs
    (fun μ hμ => hμ)
    (fun μ hμ => hK3 _ ((alSel l S).2.1 μ hμ).1 ((alSel l S).2.1 μ hμ).2)
    (indF l S.L S.G S.G0 S.h S.n S.x S.k) (laInj l S) hsep hD
  exact ⟨m, h1, h2⟩

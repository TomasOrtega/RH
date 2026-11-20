import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

namespace CentralSplit

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

noncomputable def prodOp (ρ : Representation ℂ G V) (z : G) (a : ℕ → ℂ) : ℕ → Module.End ℂ V
  | 0 => 1
  | m + 1 => prodOp ρ z a m * (ρ z - a m • 1)

noncomputable def prodScal (c : ℂ) (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => prodScal c a m * (c - a m)

/- English proof (translation)
Simplify using `[prodOp]`.
-/
theorem prodOp_succ_apply (ρ : Representation ℂ G V) (z : G) (a : ℕ → ℂ) (m : ℕ) (v : V) :
    prodOp ρ z a (m + 1) v = prodOp ρ z a m (ρ z v - a m • v) := by
  simp [prodOp]

/- English proof (translation)
Proceed by induction on `m generalizing v with`. Consider the case `zero => rfl`. Consider the case `succ m ih`. Establish `hzg : ρ z (ρ g v) = ρ g (ρ z v)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply]`.

Rewrite using `[prodOp_succ_apply, prodOp_succ_apply, hzg, ← LinearMap.map_smul (ρ g), ← LinearMap.map_sub (ρ g), ih]`.
-/
theorem prodOp_comm (ρ : Representation ℂ G V) (z : G) (hz : ∀ g, g * z = z * g) (a : ℕ → ℂ)
    (m : ℕ) (g : G) (v : V) : prodOp ρ z a m (ρ g v) = ρ g (prodOp ρ z a m v) := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    have hzg : ρ z (ρ g v) = ρ g (ρ z v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply]
    rw [prodOp_succ_apply, prodOp_succ_apply, hzg, ← LinearMap.map_smul (ρ g),
      ← LinearMap.map_sub (ρ g), ih]

/- English proof (translation)
Introduce `m hm`. Proceed by induction on `m with`. Consider the case `zero => simp [prodScal]`. Consider the case `succ m ih`. Simplify using `only [prodScal]`.

Conclude with `mul_ne_zero (ih (by omega)) (sub_ne_zero.2 (h m (by omega)).symm)`.
-/
theorem prodScal_ne_zero (c : ℂ) (a : ℕ → ℂ) (M : ℕ) (h : ∀ m < M, a m ≠ c) :
    ∀ m ≤ M, prodScal c a m ≠ 0 := by
  intro m hm
  induction m with
  | zero => simp [prodScal]
  | succ m ih =>
    simp only [prodScal]
    exact mul_ne_zero (ih (by omega)) (sub_ne_zero.2 (h m (by omega)).symm)

end CentralSplit

open CentralSplit in

/- English proof (translation)
Introduce `G V Y _ _ _ _ _ ρ τ N S _ _ htop z hz t₀ c c' hc' hstep hΨ hτ _`. Take `⟨Ψ⟩` from `hΨ`. Use `set B := S t₀.succ with hBdef`. Use `set A := S t₀.castSucc with hAdef`. Set `a : ℕ → ℂ` to `fun i => if h : i < N then c' ⟨i, h⟩ else 0`.

Set `M` to `N - (t₀.val + 1)`. Establish `hZ : ∀ y, subQuot B A z y = c • y`. Introduce `y`. Apply `Ψ.toLinearEquiv.injective` to reduce the goal to its premises. Establish `h1` using `Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap z y`.

Rewrite using `[Representation.Equiv.toLinearEquiv_apply, h1, hτ, map_smul, Representation.Equiv.toLinearEquiv_apply]`. Establish `ha : ∀ m (hm : t₀.val + 1 + m < N), a (t₀.val + 1 + m) = c' ⟨t₀.val + 1 + m, by omega⟩`. Introduce `m hm`. Simplify using `[a, hm]`. Establish `L1 : ∀ m, ∀ (h : t₀.val + 1 + m < N + 1), ∀ v, v ∈ (S ⟨t₀.val + 1 + m, h⟩).toSubmodule → prodOp ρ z (fun i => a (t₀.val + 1 + i)) m v ∈ B.toSubmodule`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `h v hv`. Establish `e : (⟨t₀.val + 1 + 0, h⟩ : Fin (N + 1)) = t₀.succ` using `by ext; simp`.

Rewrite `hv` using `[e]`. Conclude with `hv`. Consider the case `succ m ih`. Introduce `h v hv`. Set `t : Fin N` to `⟨t₀.val + 1 + m, by omega⟩`.

Establish `ht : t ≠ t₀` using `fun e => by have := congrArg Fin.val e; simp only [t] at this; omega`. Establish `hvs : v ∈ (S t.succ).toSubmodule`. Establish `: t.succ = ⟨t₀.val + 1 + (m + 1), h⟩` using `by ext; simp [t]; omega`. Rewrite using `[this]`. Conclude with `hv`.

Establish `hq` using `hstep t ht (Submodule.Quotient.mk ⟨v, hvs⟩)`. Establish `hmem : ρ z v - c' t • v ∈ (S t.castSucc).toSubmodule`. Establish `e2 : subQuot (S t.succ) (S t.castSucc) z (Submodule.Quotient.mk ⟨v, hvs⟩) = Submodule.Quotient.mk ⟨ρ z v, (S t.succ).apply_mem_toSubmodule z hvs⟩` using `rfl`. Rewrite `hq` using `[e2, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]`. Simplify using `using hq`.

Rewrite using `[prodOp_succ_apply]`. Establish `e3 : a (t₀.val + 1 + m) = c' t` using `ha m (by omega)`. Simplify using `only [e3]`. Conclude with `ih (by omega) _ hmem`. Establish `L2 : ∀ m, ∀ b (hb : b ∈ B.toSubmodule), ∃ h' : prodOp ρ z (fun i => a (t₀.val + 1 + i)) m b ∈ B.toSubmodule, (Submodule.Quotient.mk ⟨_, h'⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) = prodScal c (fun i => a (t₀.val + 1 + i)) m • Submodule.Quotient.mk ⟨b, hb⟩`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro b hb; exact ⟨hb, by simp [prodOp, prodScal]⟩`. Consider the case `succ m ih`. Introduce `b hb`.

Establish `hb' : ρ z b - a (t₀.val + 1 + m) • b ∈ B.toSubmodule` using `B.toSubmodule.sub_mem (B.apply_mem_toSubmodule z hb) (B.toSubmodule.smul_mem _ hb)`. Take `⟨h', e⟩` from `ih _ hb'`. Use `⟨by rw [prodOp_succ_apply]; exact h', ?_⟩` and prove the remaining obligations. Establish `e4 : (Submodule.Quotient.mk ⟨_, hb'⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) = (c - a (t₀.val + 1 + m)) • Submodule.Quotient.mk ⟨b, hb⟩`. Establish `e5 : subQuot B A z (Submodule.Quotient.mk ⟨b, hb⟩) = Submodule.Quotient.mk ⟨ρ z b, B.apply_mem_toSubmodule z hb⟩` using `rfl`.

Rewrite using `[sub_smul, ← hZ, e5, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub]`. Both sides reduce to the same expression. Simplify using `only [prodOp_succ_apply, prodScal]`. Rewrite using `[mul_smul, ← e4, ← e]`. Use `set op := prodOp ρ z (fun i => a (t₀.val + 1 + i)) M with hop`.

Establish `hNM : t₀.val + 1 + M = N` using `by omega`. Establish `hM : ∀ v, op v ∈ B.toSubmodule`. Introduce `v`. Use `L1 M (by omega) v ?_` and prove the remaining obligations. Establish `e : (⟨t₀.val + 1 + M, by omega⟩ : Fin (N + 1)) = Fin.last N` using `by ext; simp [hNM]`.

Rewrite using `[e, htop]`. Discharge the goal by the elementary cases of `trivial`. Establish `hlam : prodScal c (fun i => a (t₀.val + 1 + i)) M ≠ 0`. Use `prodScal_ne_zero c _ M (fun m hm => ?_) M le_rfl` and prove the remaining obligations. Use `show a (t₀.val + 1 + m) ≠ c`.

Rewrite using `[ha m (by omega)]`. Conclude with `hc' _ (fun e => by have := congrArg Fin.val e; simp only at this; omega)`. Set `φlin : V →ₗ[ℂ] Y` to `Ψ.toLinearMap ∘ₗ (A.toSubmodule.comap B.toSubmodule.subtype).mkQ ∘ₗ LinearMap.codRestrict B.toSubmodule op hM`. Establish `hφ : ∀ g v, φlin (ρ g v) = τ g (φlin v)`. Introduce `g v`.

Establish `e6 : (LinearMap.codRestrict B.toSubmodule op hM) (ρ g v) = B.toRepresentation g (LinearMap.codRestrict B.toSubmodule op hM v)` using `Subtype.ext (prodOp_comm ρ z hz _ M g v)`. Use `show Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ op hM (ρ g v))) = τ g (Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ op hM v)))`. Establish `e8 : Submodule.mkQ (A.toSubmodule.comap B.toSubmodule.subtype) (B.toRepresentation g (LinearMap.codRestrict B.toSubmodule op hM v)) = subQuot B A g (Submodule.mkQ _ (LinearMap.codRestrict B.toSubmodule op hM v))` using `rfl`. Rewrite using `[e6, e8]`. Conclude with `Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap g _`.

Use `⟨φlin.intertwiningMap_of_isIntertwiningMap ρ τ hφ, ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `exists_ne (0 : Y)`. Take `⟨⟨b, hb⟩, hx⟩` from `Submodule.Quotient.mk_surjective _ (Ψ.toLinearEquiv.symm y)`. Take `⟨h', e⟩` from `L2 M b hb`. Use `⟨b, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.toIntertwiningMap]`. Establish `e7 : φlin b = Ψ.toLinearEquiv (Submodule.Quotient.mk ⟨op b, h'⟩)` using `rfl`. Rewrite using `[e7, e, hx, map_smul, LinearEquiv.apply_symm_apply]`. Conclude with `smul_ne_zero hlam hy`.
-/
theorem exists_intertwining_of_central_step : ∀ {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G Y) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ (z : G), (∀ g, g * z = z * g) →
    ∀ (t₀ : Fin N) (c : ℂ) (c' : Fin N → ℂ), (∀ t, t ≠ t₀ → c' t ≠ c) →
    (∀ t, t ≠ t₀ → ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' t • y) →
    Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv τ) → (∀ y, τ z y = c • y) → Nontrivial Y →
    ∃ (φ : ρ.IntertwiningMap τ) (v : V), φ v ≠ 0 := by
  intro G V Y _ _ _ _ _ ρ τ N S _ _ htop z hz t₀ c c' hc' hstep hΨ hτ _
  obtain ⟨Ψ⟩ := hΨ
  set B := S t₀.succ with hBdef
  set A := S t₀.castSucc with hAdef
  let a : ℕ → ℂ := fun i => if h : i < N then c' ⟨i, h⟩ else 0
  let M := N - (t₀.val + 1)

  have hZ : ∀ y, subQuot B A z y = c • y := by
    intro y
    apply Ψ.toLinearEquiv.injective
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap z y
    rw [Representation.Equiv.toLinearEquiv_apply, h1, hτ, map_smul, Representation.Equiv.toLinearEquiv_apply]
  have ha : ∀ m (hm : t₀.val + 1 + m < N), a (t₀.val + 1 + m) = c' ⟨t₀.val + 1 + m, by omega⟩ := by
    intro m hm; simp [a, hm]

  have L1 : ∀ m, ∀ (h : t₀.val + 1 + m < N + 1), ∀ v, v ∈ (S ⟨t₀.val + 1 + m, h⟩).toSubmodule →
      prodOp ρ z (fun i => a (t₀.val + 1 + i)) m v ∈ B.toSubmodule := by
    intro m
    induction m with
    | zero =>
      intro h v hv
      have e : (⟨t₀.val + 1 + 0, h⟩ : Fin (N + 1)) = t₀.succ := by ext; simp
      rw [e] at hv
      exact hv
    | succ m ih =>
      intro h v hv
      let t : Fin N := ⟨t₀.val + 1 + m, by omega⟩
      have ht : t ≠ t₀ := fun e => by have := congrArg Fin.val e; simp only [t] at this; omega
      have hvs : v ∈ (S t.succ).toSubmodule := by
        have : t.succ = ⟨t₀.val + 1 + (m + 1), h⟩ := by ext; simp [t]; omega
        rw [this]; exact hv
      have hq := hstep t ht (Submodule.Quotient.mk ⟨v, hvs⟩)
      have hmem : ρ z v - c' t • v ∈ (S t.castSucc).toSubmodule := by
        have e2 : subQuot (S t.succ) (S t.castSucc) z (Submodule.Quotient.mk ⟨v, hvs⟩) =
            Submodule.Quotient.mk ⟨ρ z v, (S t.succ).apply_mem_toSubmodule z hvs⟩ := rfl
        rw [e2, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hq
        simpa using hq
      rw [prodOp_succ_apply]
      have e3 : a (t₀.val + 1 + m) = c' t := ha m (by omega)
      simp only [e3]
      exact ih (by omega) _ hmem

  have L2 : ∀ m, ∀ b (hb : b ∈ B.toSubmodule), ∃ h' : prodOp ρ z (fun i => a (t₀.val + 1 + i)) m b ∈ B.toSubmodule,
      (Submodule.Quotient.mk ⟨_, h'⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) =
        prodScal c (fun i => a (t₀.val + 1 + i)) m • Submodule.Quotient.mk ⟨b, hb⟩ := by
    intro m
    induction m with
    | zero => intro b hb; exact ⟨hb, by simp [prodOp, prodScal]⟩
    | succ m ih =>
      intro b hb
      have hb' : ρ z b - a (t₀.val + 1 + m) • b ∈ B.toSubmodule :=
        B.toSubmodule.sub_mem (B.apply_mem_toSubmodule z hb) (B.toSubmodule.smul_mem _ hb)
      obtain ⟨h', e⟩ := ih _ hb'
      refine ⟨by rw [prodOp_succ_apply]; exact h', ?_⟩
      have e4 : (Submodule.Quotient.mk ⟨_, hb'⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) =
          (c - a (t₀.val + 1 + m)) • Submodule.Quotient.mk ⟨b, hb⟩ := by
        have e5 : subQuot B A z (Submodule.Quotient.mk ⟨b, hb⟩) =
            Submodule.Quotient.mk ⟨ρ z b, B.apply_mem_toSubmodule z hb⟩ := rfl
        rw [sub_smul, ← hZ, e5, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub]
        rfl
      simp only [prodOp_succ_apply, prodScal]
      rw [mul_smul, ← e4, ← e]
  set op := prodOp ρ z (fun i => a (t₀.val + 1 + i)) M with hop
  have hNM : t₀.val + 1 + M = N := by omega
  have hM : ∀ v, op v ∈ B.toSubmodule := by
    intro v
    refine L1 M (by omega) v ?_
    have e : (⟨t₀.val + 1 + M, by omega⟩ : Fin (N + 1)) = Fin.last N := by ext; simp [hNM]
    rw [e, htop]
    trivial
  have hlam : prodScal c (fun i => a (t₀.val + 1 + i)) M ≠ 0 := by
    refine prodScal_ne_zero c _ M (fun m hm => ?_) M le_rfl
    show a (t₀.val + 1 + m) ≠ c
    rw [ha m (by omega)]
    exact hc' _ (fun e => by have := congrArg Fin.val e; simp only at this; omega)
  let φlin : V →ₗ[ℂ] Y := Ψ.toLinearMap ∘ₗ (A.toSubmodule.comap B.toSubmodule.subtype).mkQ ∘ₗ
    LinearMap.codRestrict B.toSubmodule op hM
  have hφ : ∀ g v, φlin (ρ g v) = τ g (φlin v) := by
    intro g v
    have e6 : (LinearMap.codRestrict B.toSubmodule op hM) (ρ g v) =
        B.toRepresentation g (LinearMap.codRestrict B.toSubmodule op hM v) :=
      Subtype.ext (prodOp_comm ρ z hz _ M g v)
    show Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ op hM (ρ g v))) =
      τ g (Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ op hM v)))
    have e8 : Submodule.mkQ (A.toSubmodule.comap B.toSubmodule.subtype)
        (B.toRepresentation g (LinearMap.codRestrict B.toSubmodule op hM v)) =
        subQuot B A g (Submodule.mkQ _ (LinearMap.codRestrict B.toSubmodule op hM v)) := rfl
    rw [e6, e8]
    exact Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap g _
  refine ⟨φlin.intertwiningMap_of_isIntertwiningMap ρ τ hφ, ?_⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨⟨b, hb⟩, hx⟩ := Submodule.Quotient.mk_surjective _ (Ψ.toLinearEquiv.symm y)
  obtain ⟨h', e⟩ := L2 M b hb
  refine ⟨b, ?_⟩
  rw [LinearMap.toIntertwiningMap]
  have e7 : φlin b = Ψ.toLinearEquiv (Submodule.Quotient.mk ⟨op b, h'⟩) := rfl
  rw [e7, e, hx, map_smul, LinearEquiv.apply_symm_apply]
  exact smul_ne_zero hlam hy

end GlobalTheory

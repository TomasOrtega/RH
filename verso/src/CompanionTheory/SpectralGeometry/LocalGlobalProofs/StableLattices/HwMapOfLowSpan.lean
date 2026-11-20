import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICHWMap

open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)

variable {T V : Type} [NormedAddCommGroup T] [InnerProductSpace ℂ T] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def diagOp (A : Module.End ℂ T) (B : Module.End ℂ V) : Module.End ℂ (WithLp 2 (T × V)) :=
  (WithLp.linearEquiv 2 ℂ (T × V)).symm.toLinearMap ∘ₗ (A.prodMap B) ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagOp_fst (A : Module.End ℂ T) (B : Module.End ℂ V) (x : WithLp 2 (T × V)) :
    (WithLp.ofLp (diagOp A B x)).1 = A (WithLp.ofLp x).1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagOp_snd (A : Module.End ℂ T) (B : Module.End ℂ V) (x : WithLp 2 (T × V)) :
    (WithLp.ofLp (diagOp A B x)).2 = B (WithLp.ofLp x).2 := rfl

/- English proof (translation)
Apply `(WithLp.linearEquiv 2 ℂ (T × V)).injective` to reduce the goal to its premises. Conclude with `Prod.ext h1 h2`.
-/
theorem sum_ext {x y : WithLp 2 (T × V)} (h1 : (WithLp.ofLp x).1 = (WithLp.ofLp y).1)
    (h2 : (WithLp.ofLp x).2 = (WithLp.ofLp y).2) : x = y := by
  apply (WithLp.linearEquiv 2 ℂ (T × V)).injective
  exact Prod.ext h1 h2

/- English proof (translation)
Introduce `a b c d hab hcd`. Establish `e1` using `LinearMap.congr_fun (h1 a b c d hab hcd)`. Establish `e2` using `LinearMap.congr_fun (h2 a b c d hab hcd)`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Apply `sum_ext` to reduce the goal to its premises.

Apply the tactic sequence `have := e1 (WithLp.ofLp x).1 split_ifs at this ⊢ <;> exact this`. Apply the tactic sequence `have := e2 (WithLp.ofLp x).2 split_ifs at this ⊢ <;> exact this`.
-/
theorem diag_krel {n : ℕ} {ε : Fin n → Bool} {ET : Fin n → Fin n → Module.End ℂ T}
    {E : Fin n → Fin n → Module.End ℂ V} (h1 : KRel ε ET) (h2 : KRel ε E) :
    KRel ε (fun a b => diagOp (ET a b) (E a b)) := by
  intro a b c d hab hcd
  have e1 := LinearMap.congr_fun (h1 a b c d hab hcd)
  have e2 := LinearMap.congr_fun (h2 a b c d hab hcd)
  refine LinearMap.ext fun x => ?_
  apply sum_ext
  · have := e1 (WithLp.ofLp x).1
    split_ifs at this ⊢ <;> exact this
  · have := e2 (WithLp.ofLp x).2
    split_ifs at this ⊢ <;> exact this

/- English proof (translation)
Introduce `a b hab x y`. Rewrite using `[WithLp.prod_inner_apply, WithLp.prod_inner_apply, diagOp_fst, diagOp_snd, diagOp_fst, diagOp_snd, h1 a b hab, h2 a b hab]`.
-/
theorem diag_kunit {n : ℕ} {ε : Fin n → Bool} {ET : Fin n → Fin n → Module.End ℂ T}
    {E : Fin n → Fin n → Module.End ℂ V} (h1 : KUnit ε ET) (h2 : KUnit ε E) :
    KUnit ε (fun a b => diagOp (ET a b) (E a b)) := by
  intro a b hab x y
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, diagOp_fst, diagOp_snd, diagOp_fst, diagOp_snd,
    h1 a b hab, h2 a b hab]

/- English proof (translation)
Introduce `hLS n ε T _ _ _ V _ _ ET E μ t v S hRT hUT hR hU ht hHT hH hS hSt hvS`. Use `haveI := hS`. Set `Lm : (T × S) →ₗ[ℂ] WithLp 2 (T × V)` to `(WithLp.linearEquiv 2 ℂ (T × V)).symm.toLinearMap ∘ₗ LinearMap.prodMap LinearMap.id S.subtype`. Set `S' : Submodule ℂ (WithLp 2 (T × V))` to `LinearMap.range Lm`. Establish `memS' : ∀ x : WithLp 2 (T × V), x ∈ S' ↔ (WithLp.ofLp x).2 ∈ S`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, rfl⟩`. Conclude with `p.2.2`. Introduce `hx`.

Conclude with `⟨((WithLp.ofLp x).1, ⟨(WithLp.ofLp x).2, hx⟩), sum_ext rfl rfl⟩`. Set `w0 : WithLp 2 (T × V)` to `WithLp.toLp 2 (t, v)`. Establish `hw0 : w0 ≠ 0`. Introduce `h`. Apply `ht` to reduce the goal to its premises.

Conclude with `congrArg (fun x => (WithLp.ofLp x).1) h`. Establish `hKR : KRel ε (fun a b => diagOp (ET a b) (E a b))` using `diag_krel hRT hR`. Establish `hKU : KUnit ε (fun a b => diagOp (ET a b) (E a b))` using `diag_kunit hUT hU`. Establish `hHW : KHighest ε (fun a b => diagOp (ET a b) (E a b)) μ w0`. Use `⟨fun a => ?_, fun a b hab heq => ?_⟩` and prove the remaining obligations.

Apply `sum_ext` to reduce the goal to its premises. Conclude with `hHT.1 a`. Conclude with `hH.1 a`. Apply `sum_ext` to reduce the goal to its premises. Conclude with `hHT.2 a b hab heq`.

Conclude with `hH.2 a b hab heq`. Establish `hStab' : KStab ε (fun a b => diagOp (ET a b) (E a b)) S'`. Introduce `a b hab x hx`. Rewrite `hx`, the goal using `[memS']`. Conclude with `hSt a b hab _ hx`.

Establish `hw0S' : w0 ∈ S'` using `(memS' w0).2 hvS`. Take `⟨L0, -, hw0L, hL0stab, hirr, -, -⟩` from `hLS n ε (WithLp 2 (T × V)) (fun a b => diagOp (ET a b) (E a b)) μ w0 S' hKR hKU hw0 hHW inferInstance hStab' hw0S'`. Set `πT : WithLp 2 (T × V) →ₗ[ℂ] T` to `LinearMap.fst ℂ T V ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap`. Set `πV : WithLp 2 (T × V) →ₗ[ℂ] V` to `LinearMap.snd ℂ T V ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap`. Set `K : Submodule ℂ (WithLp 2 (T × V))` to `L0 ⊓ LinearMap.ker πT`.

Establish `hKstab : KStab ε (fun a b => diagOp (ET a b) (E a b)) K`. Introduce `a b hab x hx`. Use `⟨hL0stab a b hab x hx.1, ?_⟩` and prove the remaining obligations. Establish `hx2 : πT x = 0` using `hx.2`. Use `show ET a b (πT x) = 0`.

Rewrite using `[hx2, map_zero]`. Establish `hK : K = ⊥`. Break down `hirr K inf_le_left hKstab with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Apply `ht` to reduce the goal to its premises. Establish `hw0K : w0 ∈ K` using `h ▸ hw0L`. Conclude with `hw0K.2`. Set `g : L0 →ₗ[ℂ] T` to `πT ∘ₗ L0.subtype`. Establish `ginj : Function.Injective g`.

Use `LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx => ?_)` and prove the remaining obligations. Establish `hxK : (x : WithLp 2 (T × V)) ∈ K` using `⟨x.2, hx⟩`. Rewrite `hxK` using `[hK]`. Conclude with `Subtype.ext ((Submodule.mem_bot ℂ).1 hxK)`. Set `W0 : Submodule ℂ T` to `LinearMap.range g`.

Set `e : L0 ≃ₗ[ℂ] W0` to `LinearEquiv.ofInjective g ginj`. Establish `hW0stab : ∀ a b, ε a = ε b → ∀ y ∈ W0, ET a b y ∈ W0`. Introduce and unpack `a b hab _ ⟨x, rfl⟩`. Conclude with `⟨⟨diagOp (ET a b) (E a b) x, hL0stab a b hab x x.2⟩, rfl⟩`. Set `P : T →L[ℂ] W0` to `W0.orthogonalProjectionOnto`.

Establish `hP : ∀ a b, ε a = ε b → ∀ y : T, (P (ET a b y) : T) = ET a b (P y)`. Introduce `a b hab y`. Establish `hmem : ET a b (P y : T) ∈ W0` using `hW0stab a b hab _ (P y).2`. Rewrite using `[Submodule.coe_orthogonalProjectionOnto_apply]`. Use `Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_` and prove the remaining obligations.

Conclude with `hmem`. Rewrite using `[← map_sub, hUT a b hab, Submodule.coe_orthogonalProjectionOnto_apply]`. Conclude with `Submodule.inner_left_of_mem_orthogonal (hW0stab b a hab.symm w hw) (Submodule.sub_starProjection_mem_orthogonal y)`. Establish `hPe : ∀ x : L0, P (g x) = e x`. Introduce `x`.

Establish `h1 : ((e x : W0) : T) = g x` using `LinearEquiv.ofInjective_apply _ _`. Rewrite using `[← h1]`. Conclude with `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e x)`. Set `φ : T →ₗ[ℂ] V` to `πV ∘ₗ L0.subtype ∘ₗ e.symm.toLinearMap ∘ₗ (P : T →ₗ[ℂ] W0)`. Establish `hφ : ∀ y : T, φ y = πV (e.symm (P y) : WithLp 2 (T × V))` using `fun y => rfl`.

Use `⟨φ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ]`. Establish `hg0 : g ⟨w0, hw0L⟩ = t` using `rfl`. Rewrite using `[← hg0, hPe, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression.

Introduce `a b hab y`. Take `⟨x, hx⟩ : ∃ x : L0, x = e.symm (P y)` from `⟨_, rfl⟩`. Establish `hPy : P y = e x` using `by rw [hx, LinearEquiv.apply_symm_apply]`. Set `x' : L0` to `⟨diagOp (ET a b) (E a b) x, hL0stab a b hab x x.2⟩`. Establish `hgx' : g x' = ET a b (g x)` using `rfl`.

Establish `hPE : P (ET a b y) = e x'`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hP a b hab y, hPy, LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply, hgx']`. Rewrite using `[hφ, hφ, hPE, LinearEquiv.symm_apply_apply, ← hx]`. Both sides reduce to the same expression.
-/
theorem hwMap_of_lowSpan : LowSpan → HWMap := by
  intro hLS n ε T _ _ _ V _ _ ET E μ t v S hRT hUT hR hU ht hHT hH hS hSt hvS
  haveI := hS
  let Lm : (T × S) →ₗ[ℂ] WithLp 2 (T × V) :=
    (WithLp.linearEquiv 2 ℂ (T × V)).symm.toLinearMap ∘ₗ LinearMap.prodMap LinearMap.id S.subtype
  let S' : Submodule ℂ (WithLp 2 (T × V)) := LinearMap.range Lm
  have memS' : ∀ x : WithLp 2 (T × V), x ∈ S' ↔ (WithLp.ofLp x).2 ∈ S := by
    intro x
    constructor
    · rintro ⟨p, rfl⟩
      exact p.2.2
    · intro hx
      exact ⟨((WithLp.ofLp x).1, ⟨(WithLp.ofLp x).2, hx⟩), sum_ext rfl rfl⟩
  let w0 : WithLp 2 (T × V) := WithLp.toLp 2 (t, v)
  have hw0 : w0 ≠ 0 := by
    intro h
    apply ht
    exact congrArg (fun x => (WithLp.ofLp x).1) h
  have hKR : KRel ε (fun a b => diagOp (ET a b) (E a b)) := diag_krel hRT hR
  have hKU : KUnit ε (fun a b => diagOp (ET a b) (E a b)) := diag_kunit hUT hU
  have hHW : KHighest ε (fun a b => diagOp (ET a b) (E a b)) μ w0 := by
    refine ⟨fun a => ?_, fun a b hab heq => ?_⟩
    · apply sum_ext
      · exact hHT.1 a
      · exact hH.1 a
    · apply sum_ext
      · exact hHT.2 a b hab heq
      · exact hH.2 a b hab heq
  have hStab' : KStab ε (fun a b => diagOp (ET a b) (E a b)) S' := by
    intro a b hab x hx
    rw [memS'] at hx ⊢
    exact hSt a b hab _ hx
  have hw0S' : w0 ∈ S' := (memS' w0).2 hvS
  obtain ⟨L0, -, hw0L, hL0stab, hirr, -, -⟩ :=
    hLS n ε (WithLp 2 (T × V)) (fun a b => diagOp (ET a b) (E a b)) μ w0 S' hKR hKU hw0 hHW
      inferInstance hStab' hw0S'
  let πT : WithLp 2 (T × V) →ₗ[ℂ] T := LinearMap.fst ℂ T V ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap
  let πV : WithLp 2 (T × V) →ₗ[ℂ] V := LinearMap.snd ℂ T V ∘ₗ (WithLp.linearEquiv 2 ℂ (T × V)).toLinearMap
  let K : Submodule ℂ (WithLp 2 (T × V)) := L0 ⊓ LinearMap.ker πT
  have hKstab : KStab ε (fun a b => diagOp (ET a b) (E a b)) K := by
    intro a b hab x hx
    refine ⟨hL0stab a b hab x hx.1, ?_⟩
    have hx2 : πT x = 0 := hx.2
    show ET a b (πT x) = 0
    rw [hx2, map_zero]
  have hK : K = ⊥ := by
    rcases hirr K inf_le_left hKstab with h | h
    · exact h
    · exfalso
      apply ht
      have hw0K : w0 ∈ K := h ▸ hw0L
      exact hw0K.2
  let g : L0 →ₗ[ℂ] T := πT ∘ₗ L0.subtype
  have ginj : Function.Injective g := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx => ?_)
    have hxK : (x : WithLp 2 (T × V)) ∈ K := ⟨x.2, hx⟩
    rw [hK] at hxK
    exact Subtype.ext ((Submodule.mem_bot ℂ).1 hxK)
  let W0 : Submodule ℂ T := LinearMap.range g
  let e : L0 ≃ₗ[ℂ] W0 := LinearEquiv.ofInjective g ginj
  have hW0stab : ∀ a b, ε a = ε b → ∀ y ∈ W0, ET a b y ∈ W0 := by
    rintro a b hab _ ⟨x, rfl⟩
    exact ⟨⟨diagOp (ET a b) (E a b) x, hL0stab a b hab x x.2⟩, rfl⟩
  let P : T →L[ℂ] W0 := W0.orthogonalProjectionOnto
  have hP : ∀ a b, ε a = ε b → ∀ y : T, (P (ET a b y) : T) = ET a b (P y) := by
    intro a b hab y
    have hmem : ET a b (P y : T) ∈ W0 := hW0stab a b hab _ (P y).2
    rw [Submodule.coe_orthogonalProjectionOnto_apply]
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
    · exact hmem
    · rw [← map_sub, hUT a b hab, Submodule.coe_orthogonalProjectionOnto_apply]
      exact Submodule.inner_left_of_mem_orthogonal (hW0stab b a hab.symm w hw)
        (Submodule.sub_starProjection_mem_orthogonal y)
  have hPe : ∀ x : L0, P (g x) = e x := by
    intro x
    have h1 : ((e x : W0) : T) = g x := LinearEquiv.ofInjective_apply _ _
    rw [← h1]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e x)
  let φ : T →ₗ[ℂ] V := πV ∘ₗ L0.subtype ∘ₗ e.symm.toLinearMap ∘ₗ (P : T →ₗ[ℂ] W0)
  have hφ : ∀ y : T, φ y = πV (e.symm (P y) : WithLp 2 (T × V)) := fun y => rfl
  refine ⟨φ, ?_, ?_⟩
  · rw [hφ]
    have hg0 : g ⟨w0, hw0L⟩ = t := rfl
    rw [← hg0, hPe, LinearEquiv.symm_apply_apply]
    rfl
  · intro a b hab y
    obtain ⟨x, hx⟩ : ∃ x : L0, x = e.symm (P y) := ⟨_, rfl⟩
    have hPy : P y = e x := by rw [hx, LinearEquiv.apply_symm_apply]
    let x' : L0 := ⟨diagOp (ET a b) (E a b) x, hL0stab a b hab x x.2⟩
    have hgx' : g x' = ET a b (g x) := rfl
    have hPE : P (ET a b y) = e x' := by
      apply Subtype.ext
      rw [hP a b hab y, hPy, LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply, hgx']
    rw [hφ, hφ, hPE, LinearEquiv.symm_apply_apply, ← hx]
    rfl

end GlobalTheory.CompanionTheory.DSICHWMap

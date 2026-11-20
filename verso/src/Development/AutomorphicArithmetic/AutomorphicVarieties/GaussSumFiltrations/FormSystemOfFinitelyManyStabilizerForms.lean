import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertModerateGrowthUnnormalizedSlash

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.SysOfStab

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Establish `h : ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det = rhom γ.val.det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Unfold `Pos TP`. Rewrite using `[h]`.

Both sides reduce to the same expression.
-/
lemma pos_iff (γ : GL (Fin 2) F) : Pos (toInf γ) ↔ TP γ.val.det := by
  have h : ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det
      = rhom γ.val.det := by
    rw [RingHom.map_det]; rfl
  unfold Pos TP
  rw [h]
  rfl

/- English proof (translation)
Use `ext1`. Conclude with `((Matrix.scalar_commute (z : R) (fun _ => Commute.all _ _) g.val).eq).symm`.
-/
lemma scal_comm {R : Type} [CommRing R] (z : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  ext1
  exact ((Matrix.scalar_commute (z : R) (fun _ => Commute.all _ _) g.val).eq).symm

def Rel (g g' : GL (Fin 2) (Af F)) (γ : GL (Fin 2) F) : Prop :=
  TP γ.val.det ∧ ∃ (z : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ KLev F 2 1 ∧
    toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g' * u

/- English proof (translation)
Rewrite `h`, `h'`, the goal using `[← pos_iff]`. Rewrite using `[map_mul]`. Conclude with `(SlashCocycle.slash_cocycle F 0 _ _ 0 h h').1`.
-/
lemma tp_mul {γ γ' : GL (Fin 2) F} (h : TP γ.val.det) (h' : TP γ'.val.det) : TP (γ * γ').val.det := by
  rw [← pos_iff] at h h' ⊢
  rw [map_mul]
  exact (SlashCocycle.slash_cocycle F 0 _ _ 0 h h').1

/- English proof (translation)
Rewrite `h`, the goal using `[← pos_iff]`. Rewrite using `[map_inv]`. Conclude with `(SlashCocycle.slash_cocycle F 0 _ _ 0 h h).2.1`.
-/
lemma tp_inv {γ : GL (Fin 2) F} (h : TP γ.val.det) : TP (γ⁻¹).val.det := by
  rw [← pos_iff] at h ⊢
  rw [map_inv]
  exact (SlashCocycle.slash_cocycle F 0 _ _ 0 h h).2.1

/- English proof (translation)
Rewrite using `[← pos_iff, map_one]`. Introduce `v`. Simplify using the standard rewrite rules.
-/
lemma tp_one : TP (1 : GL (Fin 2) F).val.det := by
  rw [← pos_iff, map_one]
  intro v
  simp

/- English proof (translation)
Rewrite `h`, `h'` using `[← pos_iff]`. Rewrite using `[map_mul]`. Conclude with `(SlashCocycle.slash_cocycle F k _ _ f h h').2.2.2.1`.
-/
lemma sl_mul (k : ℕ) {γ γ' : GL (Fin 2) F} (h : TP γ.val.det) (h' : TP γ'.val.det) (f : Hn F → ℂ) :
    sl k (toInf (γ * γ')) f = sl k (toInf γ') (sl k (toInf γ) f) := by
  rw [← pos_iff] at h h'
  rw [map_mul]
  exact (SlashCocycle.slash_cocycle F k _ _ f h h').2.2.2.1

/- English proof (translation)
Establish `h` using `(pos_iff (1 : GL (Fin 2) F)).2 tp_one`. Rewrite using `[map_one]`. Conclude with `(SlashCocycle.slash_cocycle F k _ _ f h h).2.2.2.2.2`.
-/
lemma sl_one (k : ℕ) (f : Hn F → ℂ) : sl k (toInf (1 : GL (Fin 2) F)) f = f := by
  have h := (pos_iff (1 : GL (Fin 2) F)).2 tp_one
  rw [map_one]
  exact (SlashCocycle.slash_cocycle F k _ _ f h h).2.2.2.2.2

/- English proof (translation)
Take `⟨hγ, z, u, hu, e⟩` from `h`. Use `⟨tp_inv hγ, z⁻¹, u⁻¹, inv_mem hu, ?_⟩` and prove the remaining obligations. Establish `e' : g' = (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (toFin γ * g) * u⁻¹`. Rewrite using `[e]`. Use `group`.

Rewrite using `[e', map_inv, map_inv, ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)), ← mul_assoc, ← mul_assoc, scal_comm]`. Use `group`.
-/
lemma Rel.symm {g g' : GL (Fin 2) (Af F)} {γ : GL (Fin 2) F} (h : Rel g g' γ) : Rel g' g γ⁻¹ := by
  obtain ⟨hγ, z, u, hu, e⟩ := h
  refine ⟨tp_inv hγ, z⁻¹, u⁻¹, inv_mem hu, ?_⟩
  have e' : g' = (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (toFin γ * g) * u⁻¹ := by
    rw [e]; group
  rw [e', map_inv, map_inv, ← map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)), ← mul_assoc, ← mul_assoc,
    scal_comm]
  group

/- English proof (translation)
Take `⟨hγ, z, u, hu, e⟩` from `h`. Take `⟨hγ', z', u', hu', e'⟩` from `h'`. Use `⟨tp_mul hγ' hγ, z * z', u' * u, mul_mem hu' hu, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, mul_assoc, e, ← mul_assoc, ← mul_assoc, scal_comm, mul_assoc _ (toFin γ'), e', map_mul]`. Use `group`.
-/
lemma Rel.trans {g g' g'' : GL (Fin 2) (Af F)} {γ γ' : GL (Fin 2) F} (h : Rel g g' γ) (h' : Rel g' g'' γ') :
    Rel g g'' (γ' * γ) := by
  obtain ⟨hγ, z, u, hu, e⟩ := h
  obtain ⟨hγ', z', u', hu', e'⟩ := h'
  refine ⟨tp_mul hγ' hγ, z * z', u' * u, mul_mem hu' hu, ?_⟩
  rw [map_mul, mul_assoc, e, ← mul_assoc, ← mul_assoc, scal_comm, mul_assoc _ (toFin γ'), e', map_mul]
  group

/- English proof (translation)
Introduce `F _ _ _ k Y f hcov hf`. Set `P : GL (Fin 2) (Af F) → (Af F)ˣ → Prop` to `fun g y => y ∈ Y ∧ ∃ γ, Rel g (aff y 0) γ`. Set `y : GL (Fin 2) (Af F) → (Af F)ˣ` to `fun g => Classical.epsilon (P g)`. Establish `hy : ∀ g, P g (y g)`. Introduce `g`.

Apply `Classical.epsilon_spec (p := P g)` to reduce the goal to its premises. Take `⟨γ, hγ, y, hyY, u, hu, e⟩` from `hcov g`. Conclude with `⟨y, hyY, γ, hγ, 1, u, hu, by rw [map_one, one_mul, e]⟩`. Establish `hyeq : ∀ g g' γ, Rel g g' γ → y g = y g'`. Introduce `g g' γ h`.

Establish `: P g = P g'`. Use function extensionality and compare the values at `x`. Conclude with `propext ⟨fun ⟨a, δ, b⟩ => ⟨a, _, h.symm.trans b⟩, fun ⟨a, δ, b⟩ => ⟨a, _, h.trans b⟩⟩`. Simplify using `only [y, this]`. Use `choose c hc using fun g => (hy g).2`.

Set `Ψ : GL (Fin 2) (Af F) → Hn F → ℂ` to `fun g => sl k (toInf (c g)) (f (y g))`. Establish `key : ∀ g g' γ, Rel g g' γ → sl k (toInf γ) (Ψ g') = Ψ g`. Introduce `g g' γ h`. Establish `h1 : Rel g (aff (y g) 0) (c g' * γ)`. Rewrite using `[hyeq g g' γ h]`.

Conclude with `h.trans (hc g')`. Establish `h2 : Stab (aff (y g) 0) (c g' * γ * (c g)⁻¹)` using `(hc g).symm.trans h1`. Establish `h3` using `(hf _ (hy g).1).2.2 _ h2`. Simplify using `only [Ψ]`. Rewrite using `[← sl_mul k (hc g').1 h.1, ← hyeq g g' γ h]`.

Use `conv_rhs => rw [← h3, ← sl_mul k h2.1 (hc g).1, inv_mul_cancel_right]`. Use `⟨Ψ, ⟨fun g => ?_, fun g => ?_, fun γ hγ g => ?_, fun g u hu => ?_, fun z g => ?_⟩, fun g => ?_⟩` and prove the remaining obligations. Establish `h` using `(hf _ (hy g).1).1`. Conclude with `((HolKeep.main F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2`. Establish `h` using `(hf _ (hy g).1).2.1`.

Conclude with `((Growth.gr_closed F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2`. Conclude with `key _ _ _ ⟨hγ, 1, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩`. Use `key (g * u) g 1 ⟨tp_one, 1, u, hu, by rw [map_one, map_one, one_mul, one_mul]⟩` as an intermediate fact. Rewrite using `[← this, sl_one]`. Use `key (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) g 1 ⟨tp_one, z, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩` as an intermediate fact.

Rewrite using `[← this, sl_one]`. Take `⟨hγ, z, u, hu, e⟩` from `hc g`. Conclude with `⟨c g, z, hγ, y g, (hy g).1, u, hu, e, rfl⟩`.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Y : Finset (Af F)ˣ) (f : (Af F)ˣ → Hn F → ℂ), (∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u) → (∀ y ∈ Y, Hol (f y) ∧ Gr (f y) ∧ ∀ γ, Stab (aff y 0) γ → sl k (toInf γ) (f y) = f y) → ∃ Ψ : GL (Fin 2) (Af F) → Hn F → ℂ, Sys k Ψ ∧ ∀ g, ∃ (γ : GL (Fin 2) F) (z : (Af F)ˣ), TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y 0 * u ∧ Ψ g = sl k (toInf γ) (f y) := by
  intro F _ _ _ k Y f hcov hf
  let P : GL (Fin 2) (Af F) → (Af F)ˣ → Prop := fun g y => y ∈ Y ∧ ∃ γ, Rel g (aff y 0) γ
  let y : GL (Fin 2) (Af F) → (Af F)ˣ := fun g => Classical.epsilon (P g)
  have hy : ∀ g, P g (y g) := by
    intro g
    apply Classical.epsilon_spec (p := P g)
    obtain ⟨γ, hγ, y, hyY, u, hu, e⟩ := hcov g
    exact ⟨y, hyY, γ, hγ, 1, u, hu, by rw [map_one, one_mul, e]⟩
  have hyeq : ∀ g g' γ, Rel g g' γ → y g = y g' := by
    intro g g' γ h
    have : P g = P g' := by
      funext x
      exact propext ⟨fun ⟨a, δ, b⟩ => ⟨a, _, h.symm.trans b⟩, fun ⟨a, δ, b⟩ => ⟨a, _, h.trans b⟩⟩
    simp only [y, this]
  choose c hc using fun g => (hy g).2
  let Ψ : GL (Fin 2) (Af F) → Hn F → ℂ := fun g => sl k (toInf (c g)) (f (y g))
  have key : ∀ g g' γ, Rel g g' γ → sl k (toInf γ) (Ψ g') = Ψ g := by
    intro g g' γ h
    have h1 : Rel g (aff (y g) 0) (c g' * γ) := by
      rw [hyeq g g' γ h]; exact h.trans (hc g')
    have h2 : Stab (aff (y g) 0) (c g' * γ * (c g)⁻¹) := (hc g).symm.trans h1
    have h3 := (hf _ (hy g).1).2.2 _ h2
    simp only [Ψ]
    rw [← sl_mul k (hc g').1 h.1, ← hyeq g g' γ h]
    conv_rhs => rw [← h3, ← sl_mul k h2.1 (hc g).1, inv_mul_cancel_right]
  refine ⟨Ψ, ⟨fun g => ?_, fun g => ?_, fun γ hγ g => ?_, fun g u hu => ?_, fun z g => ?_⟩, fun g => ?_⟩
  · have h := (hf _ (hy g).1).1
    exact ((HolKeep.main F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2
  · have h := (hf _ (hy g).1).2.1
    exact ((Growth.gr_closed F k _ _ 0 h h).2.2.2.2.2 _ ((pos_iff _).2 (hc g).1)).2
  · exact key _ _ _ ⟨hγ, 1, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩
  · have := key (g * u) g 1 ⟨tp_one, 1, u, hu, by rw [map_one, map_one, one_mul, one_mul]⟩
    rw [← this, sl_one]
  · have := key (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) g 1
      ⟨tp_one, z, 1, one_mem _, by rw [map_one, one_mul, mul_one]⟩
    rw [← this, sl_one]
  · obtain ⟨hγ, z, u, hu, e⟩ := hc g
    exact ⟨c g, z, hγ, y g, (hy g).1, u, hu, e, rfl⟩

end GlobalTheory.HilbertThetaSeries.SysOfStab

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.SysOfStab.main | exact GlobalTheory.HilbertThetaSeries.SysOfStab.main | (intros; apply GlobalTheory.HilbertThetaSeries.SysOfStab.main <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.form_system_of_finitely_many_stabilizer_forms : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Y : Finset (Af F)ˣ) (f : (Af F)ˣ → Hn F → ℂ), (∀ g : GL (Fin 2) (Af F), ∃ γ : GL (Fin 2) F, TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = aff y 0 * u) → (∀ y ∈ Y, Hol (f y) ∧ Gr (f y) ∧ ∀ γ, Stab (aff y 0) γ → sl k (toInf γ) (f y) = f y) → ∃ Ψ : GL (Fin 2) (Af F) → Hn F → ℂ, Sys k Ψ ∧ ∀ g, ∃ (γ : GL (Fin 2) F) (z : (Af F)ˣ), TP γ.val.det ∧ ∃ y ∈ Y, ∃ u ∈ KLev F 2 1, toFin γ * g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y 0 * u ∧ Ψ g = sl k (toInf γ) (f y) := by
  first | exact @GlobalTheory.HilbertThetaSeries.SysOfStab.main | exact GlobalTheory.HilbertThetaSeries.SysOfStab.main | (intros; apply GlobalTheory.HilbertThetaSeries.SysOfStab.main <;> assumption)

import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Spanpsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Exbasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.DetPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnf
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Nearvx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.SimpSpan

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Establish `hs : Spans {y : Lat L N | ∀ j, q (t.1 j).1 y = 1}`. Use `spanpsd L N _ fun k hk H => ?_` and prove the remaining obligations. Use `ConeExtensionAcyclic.simp_span (good L N).locFin p t.1 t.2 k hk fun y hy => ?_` and prove the remaining obligations. Conclude with `H y.1 hy`. Take `⟨A, hA, hc⟩` from `exbasis L N _ hs`.

Conclude with `⟨A, hA, fun j a => hc a j⟩`.
-/
private theorem sx_basis (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N p : ℕ)
    (t : Sx L N p) :
    ∃ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 ∧ ∀ j, ColsMin A (t.1 j).1 := by
  have hs : Spans {y : Lat L N | ∀ j, q (t.1 j).1 y = 1} := by
    refine spanpsd L N _ fun k hk H => ?_
    refine ConeExtensionAcyclic.simp_span (good L N).locFin p t.1 t.2 k hk fun y hy => ?_
    exact H y.1 hy
  obtain ⟨A, hA, hc⟩ := exbasis L N _ hs
  exact ⟨A, hA, fun j a => hc a j⟩

/- English proof (translation)
Introduce `a`. Establish `e : (fun i => ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A) i a) = g • (fun i => A i a : Lat L N)`. Use extensionality with `i`. Simplify using `[smul_lat, Matrix.mul_apply, mulVec, dotProduct]`. Rewrite using `[e, q_smul, inv_smul_smul]`.

Conclude with `H a`.
-/
private theorem colsMin_smul {L : Type} [Field L] [NumberField L] {N : ℕ} (g : Gm L N)
    {A : Matrix (Fin N) (Fin N) (𝓞 L)} {h : HS L N} (H : ColsMin A h) :
    ColsMin ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A) (g • h) := by
  intro a
  have e : (fun i => ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A) i a) =
      g • (fun i => A i a : Lat L N) := by
    ext i
    simp [smul_lat, Matrix.mul_apply, mulVec, dotProduct]
  rw [e, q_smul, inv_smul_smul]
  exact H a

/- English proof (translation)
Introduce `L _ _ _ N p`. Take `⟨S, hS, hrep⟩` from `hnf L N (I0 L N)`. Set `S'` to `S.filter fun A => A.det ≠ 0`. Establish `hdet : ∀ A : S', A.1.det ≠ 0` using `fun A => (Finset.mem_filter.1 A.2).2`. Use `haveI : ∀ A : S', Finite (nearVx A.1) := fun A => (nearvx L N A.1 (hdet A)).1.to_subtype`.

Establish `key : ∀ c : MulAction.orbitRel.Quotient (Gm L N) (Sx L N p), ∃ s : (Σ A : S', (Fin (p + 1) → nearVx A.1)), ∃ t : Sx L N p, Quotient.mk _ t = c ∧ ∀ j, t.1 j = (s.2 j).1`. Introduce `c`. Proceed by induction on `c using Quotient.inductionOn with`. Consider the case `h t`. Take `⟨A, hA, hc⟩` from `sx_basis L N p t`.

Establish `hR : (t.1 0).1 ∈ Ry L N`. Rewrite using `[← poly_qc]`. Conclude with `(t.1 0).2.1`. Take `⟨g, hg⟩` from `hrep A hA (nrmle L N _ A hR (hc 0) hA).1`. Establish `hd : ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A).det ≠ 0`.

Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (Matrix.isUnits_det_units g).ne_zero hA`. Use `⟨⟨⟨_, Finset.mem_filter.2 ⟨hg, hd⟩⟩, fun j => ⟨g • t.1 j, colsMin_smul g (hc j)⟩⟩, g • t, ?_, fun j => rfl⟩` and prove the remaining obligations. Conclude with `Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, rfl⟩)`. Use `choose f t ht hf using key`.

Establish `hinj : Function.Injective f`. Introduce `c c' e`. Rewrite using `[← ht c, ← ht c']`. Use `congr 1`. Use `Subtype.ext (funext fun j => ?_)` and prove the remaining obligations.

Rewrite using `[hf, hf, e]`. Use `⟨Finite.of_injective f hinj, (Nat.card_le_card_of_injective f hinj).trans ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_sigma]`. Establish `hb : ∀ A : S', Nat.card (Fin (p + 1) → nearVx A.1) ≤ ((2 * RR L N + 1) ^ dd L N + 1) ^ (dd L N * N * (p + 1))`. Introduce `A`.

Rewrite using `[Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (p + 1)), Fintype.card_fin, pow_mul _ _ (p + 1)]`. Conclude with `Nat.pow_le_pow_left (nearvx L N A.1 (hdet A)).2 _`. Use `(Finset.sum_le_card_nsmul _ _ _ fun A _ => hb A).trans ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, Finset.card_univ, Fintype.card_coe]`. Conclude with `Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hS)`.
-/
theorem UpperTheory.V.KT.orb :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (p : ℕ),
    KH.OrbLe (Gm L N) (Sx L N p) (orbBound L N p) := by
  intro L _ _ _ N p
  classical
  obtain ⟨S, hS, hrep⟩ := hnf L N (I0 L N)
  let S' := S.filter fun A => A.det ≠ 0
  have hdet : ∀ A : S', A.1.det ≠ 0 := fun A => (Finset.mem_filter.1 A.2).2
  haveI : ∀ A : S', Finite (nearVx A.1) := fun A => (nearvx L N A.1 (hdet A)).1.to_subtype
  have key : ∀ c : MulAction.orbitRel.Quotient (Gm L N) (Sx L N p),
      ∃ s : (Σ A : S', (Fin (p + 1) → nearVx A.1)), ∃ t : Sx L N p,
        Quotient.mk _ t = c ∧ ∀ j, t.1 j = (s.2 j).1 := by
    intro c
    induction c using Quotient.inductionOn with
    | h t =>
      obtain ⟨A, hA, hc⟩ := sx_basis L N p t
      have hR : (t.1 0).1 ∈ Ry L N := by
        rw [← poly_qc]; exact (t.1 0).2.1
      obtain ⟨g, hg⟩ := hrep A hA (nrmle L N _ A hR (hc 0) hA).1
      have hd : ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A).det ≠ 0 := by
        rw [Matrix.det_mul]
        exact mul_ne_zero (Matrix.isUnits_det_units g).ne_zero hA
      refine ⟨⟨⟨_, Finset.mem_filter.2 ⟨hg, hd⟩⟩,
        fun j => ⟨g • t.1 j, colsMin_smul g (hc j)⟩⟩, g • t, ?_, fun j => rfl⟩
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, rfl⟩)
  choose f t ht hf using key
  have hinj : Function.Injective f := by
    intro c c' e
    rw [← ht c, ← ht c']
    congr 1
    refine Subtype.ext (funext fun j => ?_)
    rw [hf, hf, e]
  refine ⟨Finite.of_injective f hinj, (Nat.card_le_card_of_injective f hinj).trans ?_⟩
  rw [Nat.card_sigma]
  have hb : ∀ A : S', Nat.card (Fin (p + 1) → nearVx A.1) ≤
      ((2 * RR L N + 1) ^ dd L N + 1) ^ (dd L N * N * (p + 1)) := by
    intro A
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (p + 1)), Fintype.card_fin, pow_mul _ _ (p + 1)]
    exact Nat.pow_le_pow_left (nearvx L N A.1 (hdet A)).2 _
  refine (Finset.sum_le_card_nsmul _ _ _ fun A _ => hb A).trans ?_
  rw [smul_eq_mul, Finset.card_univ, Fintype.card_coe]
  exact Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hS)

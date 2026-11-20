import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge.ZeroReps
open GlobalTheory.SymBridge

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [toLoc, LinearMap.id_apply, Pi.single_apply, Matrix.one_apply, e.injective.eq_iff]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem toLoc_id {X : Fields} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : X.E →+* k) {A : Type} [DecidableEq A] {n : ℕ} (e : A ≃ Fin n) :
    toLoc ι e e (LinearMap.id : (Fin n → X.E) →ₗ[X.E] (Fin n → X.E)) = 1 := by
  ext i j
  simp only [toLoc, LinearMap.id_apply, Pi.single_apply, Matrix.one_apply, e.injective.eq_iff]
  split_ifs <;> simp

/- English proof (translation)
Establish `hN : R.N 0 = R.k` using `by simp [Ranks.N]`. Establish `hb : ∀ a : XIx (Fin R.k) (Fin R.t) 0 ⊕ Fin c, yPos xPos (R.N 0) a < R.N 0 + cOf R 0`. Introduce and unpack `(((i | i) | p) | i)`. Simplify using `only [yPos, Sum.elim_inl, xPos]`. Use linear arithmetic over natural numbers and integers.

Conclude with `i.elim0`. Conclude with `p.1.elim0`. Simplify using `only [yPos, Sum.elim_inr]`. Use linear arithmetic over natural numbers and integers. Set `f : XIx (Fin R.k) (Fin R.t) 0 ⊕ Fin c → Fin (R.N 0 + cOf R 0)` to `fun a => ⟨yPos xPos (R.N 0) a, hb a⟩`.

Establish `hf : Function.Bijective f`. Use `(Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rintro (((i | i) | p) | i) (((i' | i') | p') | i') hh <;>`. Simplify using `only [f, Fin.mk.injEq, yPos, Sum.elim_inl, Sum.elim_inr, xPos] at hh`. Apply the tactic sequence `all_goals first`.

Consider the case `exact i.elim0 | exact i'.elim0 | exact p.1.elim0 | exact p'.1.elim0`. Consider the case `(congr 1; first | (congr 2; exact Fin.ext hh) | exact Fin.ext (by omega))`. Consider the case `omega`. Simplify using `only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]`. Rewrite using `[hN]`.

Use linear arithmetic over natural numbers and integers. Conclude with `⟨Equiv.ofBijective f hf, fun a => rfl⟩`.
-/
theorem exists_isOrdY_zero (R : Ranks) (c : ℕ) (hc : c = cOf R 0) :
    ∃ e : XIx (Fin R.k) (Fin R.t) 0 ⊕ Fin c ≃ Fin (R.N 0 + cOf R 0), IsOrdY e := by
  classical
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hb : ∀ a : XIx (Fin R.k) (Fin R.t) 0 ⊕ Fin c, yPos xPos (R.N 0) a < R.N 0 + cOf R 0 := by
    rintro (((i | i) | p) | i)
    · simp only [yPos, Sum.elim_inl, xPos]; omega
    · exact i.elim0
    · exact p.1.elim0
    · simp only [yPos, Sum.elim_inr]; omega
  let f : XIx (Fin R.k) (Fin R.t) 0 ⊕ Fin c → Fin (R.N 0 + cOf R 0) := fun a => ⟨yPos xPos (R.N 0) a, hb a⟩
  have hf : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
    · rintro (((i | i) | p) | i) (((i' | i') | p') | i') hh <;>
        simp only [f, Fin.mk.injEq, yPos, Sum.elim_inl, Sum.elim_inr, xPos] at hh
      all_goals first
        | exact i.elim0 | exact i'.elim0 | exact p.1.elim0 | exact p'.1.elim0
        | (congr 1; first | (congr 2; exact Fin.ext hh) | exact Fin.ext (by omega))
        | omega
    · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      rw [hN]; omega
  exact ⟨Equiv.ofBijective f hf, fun a => rfl⟩

/- English proof (translation)
Introduce `X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _ _ hA L G hL _ c h`. Establish `hm : R.m = s + 2` using `hA.steps`. Establish `hcO : c + 1 = cOf R 0` using `by unfold cOf; omega`. Take `⟨b₀, -⟩` from `hL.zero_uniq`. Use extensionality with `g`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, e, -, hg⟩`. Rewrite `hg` using `[hL.zero_h]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[hg]`. Conclude with `toLoc_id ι e`. Introduce and unpack `rfl`. Take `⟨e, he⟩` from `exists_isOrdY_zero R (c + 1) hcO`. Use `⟨b₀, e, he, ?_⟩` and prove the remaining obligations.

Rewrite using `[hL.zero_h]`. Conclude with `(toLoc_id ι e).symm`.
-/
theorem reps_zero : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ c (h : 0 + c = s), {g : GL (XIx (Fin R.k) (Fin R.t) (0) ⊕ Fin (c + 1)) k | ∃ b : L.β 0, IsGL ι (L.h 0 b P) g} = {1} := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _ _ hA L G hL _ c h
  have hm : R.m = s + 2 := hA.steps
  have hcO : c + 1 = cOf R 0 := by unfold cOf; omega
  obtain ⟨b₀, -⟩ := hL.zero_uniq
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, e, -, hg⟩
    rw [hL.zero_h] at hg
    apply Units.ext
    rw [hg]
    exact toLoc_id ι e
  · rintro rfl
    obtain ⟨e, he⟩ := exists_isOrdY_zero R (c + 1) hcO
    refine ⟨b₀, e, he, ?_⟩
    rw [hL.zero_h]
    exact (toLoc_id ι e).symm

end GlobalTheory.TwBridge.ZeroReps

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ _ _ n _ _ i P c _hcard hc hlat hcl`. Use `set e : n → (n → k) := fun b => c • (Pi.single b (1:k) : n → k) with he_def`. Establish `hcoef : ∀ b j, c⁻¹ * e b j = (Pi.single b (1:k) : n → k) j`. Introduce `b j`. Distinguish the cases in `h : j = b`.

Substitute `h` using the available equality. Simplify using `[he_def, hc]`. Simplify using `[he_def, Pi.single_apply, h]`. Establish `hmem : ∀ b, e b ∈ P.lat` using `fun b => (hlat _).2 (fun j => by`. Rewrite using `[hcoef]`.

Distinguish the cases in `h : j = b`. Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same]`. Conclude with `one_mem _`. Simplify using `only [Pi.single_apply, h, if_false]`.

Conclude with `zero_mem _)`. Set `v : n → 𝓀[k]` to `fun b => P.fn ⟨e b, hmem b⟩`. Establish `hv : ∀ b, P.HasVal (e b) (v b)` using `fun b => P.hasVal_fn ⟨e b, hmem b⟩`. Establish `hzero : ∀ a, a ≠ i → v a = 0`. Introduce `a ha`.

Establish `h1` using `hcl (e i) (v i) (hv i) a i 1 ha (Or.inl ha)`. Establish `h2 : e i + Pi.single a (((1:𝒪[k]) : k) * e i i) = e i + e a`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = a`.

Substitute `h` using the available equality. Simplify using `[he_def]`. Simplify using `[he_def, Pi.single_apply, h]`. Rewrite `h1` using `[h2]`. Establish `h3` using `h1.sub (hv i)`.

Rewrite `h3` using `[add_sub_cancel_left, sub_self]`. Conclude with `(hv a).unique h3`. Establish `hsum : ∀ (s : n → 𝒪[k]) (S : Finset n), P.HasVal (∑ b ∈ S, s b • e b) (∑ b ∈ S, IsLocalRing.residue 𝒪[k] (s b) * v b)`. Introduce `s S`. Proceed by induction on `S using Finset.induction_on with`.

Consider the case `empty => simpa using (hv i).sub (hv i)`. Consider the case `insert b S hb ih`. Rewrite using `[Finset.sum_insert hb, Finset.sum_insert hb]`. Conclude with `((hv b).smul (s b)).add ih`. Establish `hval : ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]), P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * v i)`.

Introduce `x hx`. Set `s : n → 𝒪[k]` to `fun b => ⟨c⁻¹ * x b, hx b⟩`. Establish `hx' : (∑ b, s b • e b) = x`. Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single j]`.

Express the relevant statement in the definitionally equal form `((s j : 𝒪[k]) : k) * (c * (Pi.single j (1:k) : n → k) j) = x j`. Simplify using `only [s, Pi.single_eq_same, mul_one]`. Clear the denominators using the available nonvanishing facts. Introduce `b _ hb`. Express the relevant statement in the definitionally equal form `((s b : 𝒪[k]) : k) * (c * (Pi.single b (1:k) : n → k) j) = 0`.

Simplify using `[Pi.single_apply, Ne.symm hb]`. Simplify using the standard rewrite rules. Use `hsum s Finset.univ` as an intermediate fact. Rewrite `this` using `[hx', Finset.sum_eq_single i (fun b _ hb => by rw [hzero b hb, mul_zero]) (by simp)]`. Conclude with `this`.

Use `⟨v i, ?_, hval⟩` and prove the remaining obligations. Introduce `h0`. Apply `P.fn_ne` to reduce the goal to its premises. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Use `hval y ((hlat y).1 y.2)` as an intermediate fact.

Rewrite `this` using `[h0, mul_zero]`. Conclude with `(P.hasVal_fn y).unique this`.
-/
theorem latPair_hasVal_residue_of_transvections : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 2 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → ∃ ε : 𝓀[k], ε ≠ 0 ∧ ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]), P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * ε) := by
  intro k _ _ _ _ n _ _ i P c _hcard hc hlat hcl
  classical
  set e : n → (n → k) := fun b => c • (Pi.single b (1:k) : n → k) with he_def
  have hcoef : ∀ b j, c⁻¹ * e b j = (Pi.single b (1:k) : n → k) j := by
    intro b j
    by_cases h : j = b
    · subst h; simp [he_def, hc]
    · simp [he_def, Pi.single_apply, h]
  have hmem : ∀ b, e b ∈ P.lat := fun b => (hlat _).2 (fun j => by
    rw [hcoef]
    by_cases h : j = b
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_apply, h, if_false]; exact zero_mem _)
  let v : n → 𝓀[k] := fun b => P.fn ⟨e b, hmem b⟩
  have hv : ∀ b, P.HasVal (e b) (v b) := fun b => P.hasVal_fn ⟨e b, hmem b⟩
  have hzero : ∀ a, a ≠ i → v a = 0 := by
    intro a ha
    have h1 := hcl (e i) (v i) (hv i) a i 1 ha (Or.inl ha)
    have h2 : e i + Pi.single a (((1:𝒪[k]) : k) * e i i) = e i + e a := by
      congr 1
      funext j
      by_cases h : j = a
      · subst h; simp [he_def]
      · simp [he_def, Pi.single_apply, h]
    rw [h2] at h1
    have h3 := h1.sub (hv i)
    rw [add_sub_cancel_left, sub_self] at h3
    exact (hv a).unique h3
  have hsum : ∀ (s : n → 𝒪[k]) (S : Finset n),
      P.HasVal (∑ b ∈ S, s b • e b) (∑ b ∈ S, IsLocalRing.residue 𝒪[k] (s b) * v b) := by
    intro s S
    induction S using Finset.induction_on with
    | empty => simpa using (hv i).sub (hv i)
    | insert b S hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb]
      exact ((hv b).smul (s b)).add ih
  have hval : ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]),
      P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * v i) := by
    intro x hx
    let s : n → 𝒪[k] := fun b => ⟨c⁻¹ * x b, hx b⟩
    have hx' : (∑ b, s b • e b) = x := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · change ((s j : 𝒪[k]) : k) * (c * (Pi.single j (1:k) : n → k) j) = x j
        simp only [s, Pi.single_eq_same, mul_one]
        field_simp
      · intro b _ hb
        change ((s b : 𝒪[k]) : k) * (c * (Pi.single b (1:k) : n → k) j) = 0
        simp [Pi.single_apply, Ne.symm hb]
      · simp
    have := hsum s Finset.univ
    rw [hx', Finset.sum_eq_single i (fun b _ hb => by rw [hzero b hb, mul_zero]) (by simp)] at this
    exact this
  refine ⟨v i, ?_, hval⟩
  intro h0
  apply P.fn_ne
  refine LinearMap.ext fun y => ?_
  have := hval y ((hlat y).1 y.2)
  rw [h0, mul_zero] at this
  exact (P.hasVal_fn y).unique this

end GlobalTheory

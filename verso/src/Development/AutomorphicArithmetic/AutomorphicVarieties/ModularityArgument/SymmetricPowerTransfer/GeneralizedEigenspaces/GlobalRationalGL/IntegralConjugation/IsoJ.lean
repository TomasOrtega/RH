import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `k k' _ _ _ _ _ _ _ _ i hi`. Take `⟨hv, hu, -, -⟩` from `isoVal k k' i hi`. Establish `hent : ∀ (n : ℕ) (g : GL (Fin n) k) (a b : Fin n), (GeneralLinearGroup.map (i : k →+* k') g : Matrix (Fin n) (Fin n) k') a b = i ((g : Matrix (Fin n) (Fin n) k) a b)`. Introduce `n g a b`. Both sides reduce to the same expression.

Establish `h1 : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1` using `hi.int`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `V V' hc hH n g`. Rewrite using `[Sig.memJ, Sig.memJ]`. Simplify using `only [hent, h1]`.

Establish `hpow : ∀ x : k, valuation k' (i x) ≤ valuation k' ↑(Hi.unif k') ^ (V'.c + 1) ↔ valuation k x ≤ valuation k ↑(Hi.unif k) ^ (V.c + 1)`. Introduce `x`. Rewrite using `[← hu, hc, ← map_pow, ← map_pow, ← map_pow, hv]`. Simplify using `only [hpow]`. Establish `hd : ∀ x : k, (∃ u ∈ V'.H, (u : k') = i x) ↔ (∃ u ∈ V.H, (u : k) = x)`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu', he⟩`. Use `⟨Units.map (i.symm : k' →* k) u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hH]`.

Use `hu'` and compare the differences between its conclusion and the goal. Use `ext`. Simplify using the standard rewrite rules. Simplify using `[he]`. Introduce and unpack `⟨u, hu', he⟩`.

Use `⟨Units.map (i : k →* k') u, (hH u).2 hu', ?_⟩` and prove the remaining obligations. Simplify using `[he]`. Simplify using `only [hd]`. Introduce `n g`. Rewrite using `[Hi.GlAx.mem_KO, Hi.GlAx.mem_KO, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero, ← map_inv]`.

Conclude with `and_congr (forall_congr' fun a => forall_congr' fun b => h1 _) (forall_congr' fun a => forall_congr' fun b => h1 _)`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.isoJ :
    ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), IsoOk i → (∀ (V : Sig.Lev k) (V' : Sig.Lev k'), V.c = V'.c → (∀ a, Units.map (i : k →* k') a ∈ V'.H ↔ a ∈ V.H) → ∀ (n : ℕ) (g : GL (Fin n) k), GeneralLinearGroup.map (i : k →+* k') g ∈ V'.J n ↔ g ∈ V.J n) ∧ ∀ (n : ℕ) (g : GL (Fin n) k), GeneralLinearGroup.map (i : k →+* k') g ∈ KO k' (Fin n) ↔ g ∈ KO k (Fin n) := by
  intro k k' _ _ _ _ _ _ _ _ i hi
  obtain ⟨hv, hu, -, -⟩ := isoVal k k' i hi
  have hent : ∀ (n : ℕ) (g : GL (Fin n) k) (a b : Fin n),
      (GeneralLinearGroup.map (i : k →+* k') g : Matrix (Fin n) (Fin n) k') a b = i ((g : Matrix (Fin n) (Fin n) k) a b) := by
    intro n g a b
    rfl
  have h1 : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1 := hi.int
  refine ⟨?_, ?_⟩
  · intro V V' hc hH n g
    rw [Sig.memJ, Sig.memJ]
    simp only [hent, h1]
    have hpow : ∀ x : k, valuation k' (i x) ≤ valuation k' ↑(Hi.unif k') ^ (V'.c + 1) ↔
        valuation k x ≤ valuation k ↑(Hi.unif k) ^ (V.c + 1) := by
      intro x
      rw [← hu, hc, ← map_pow, ← map_pow, ← map_pow, hv]
    simp only [hpow]
    have hd : ∀ x : k, (∃ u ∈ V'.H, (u : k') = i x) ↔ (∃ u ∈ V.H, (u : k) = x) := by
      intro x
      constructor
      · rintro ⟨u, hu', he⟩
        refine ⟨Units.map (i.symm : k' →* k) u, ?_, ?_⟩
        · rw [← hH]
          convert hu'
          ext
          simp
        · simp [he]
      · rintro ⟨u, hu', he⟩
        refine ⟨Units.map (i : k →* k') u, (hH u).2 hu', ?_⟩
        simp [he]
    simp only [hd]
  · intro n g
    rw [Hi.GlAx.mem_KO, Hi.GlAx.mem_KO, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero, Hi.GlAx.bd_zero,
      ← map_inv]
    exact and_congr (forall_congr' fun a => forall_congr' fun b => h1 _)
      (forall_congr' fun a => forall_congr' fun b => h1 _)

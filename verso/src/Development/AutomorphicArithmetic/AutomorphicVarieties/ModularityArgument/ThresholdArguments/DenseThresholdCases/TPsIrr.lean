import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.EqOfTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Hi.PsIrr
open GlobalTheory.SplitRead
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
/- English proof (translation)
Use `MonoidHom.ext fun x => Units.ext ?_` and prove the remaining obligations. Set `g : GL (Fin 1) k` to `Matrix.GeneralLinearGroup.scalar _ x`. Establish `hg : Matrix.GeneralLinearGroup.det g = x` using `by ext; simp [g, Matrix.GeneralLinearGroup.scalar]`. Take `⟨y, hy⟩` from `φ.surjective 1`. Establish `h1` using `LinearMap.congr_fun (φ.isIntertwining' g) y`.

Establish `hy' : φ.toLinearMap y = 1` using `hy`. Establish `h2 : detRep (Fin 1) χ g y = (χ x : ℂ) • y` using `by simp [detRep, hg]`. Simplify using `only [LinearMap.comp_apply, h2, map_smul, hy'] at h1`. Simplify `h1` using `[twist, detRep, ofChar, hg, mul_comm]`.
-/
private theorem eq_of_twist {χ ψ η : kˣ →* ℂˣ}
    (φ : (detRep (Fin 1) χ).Equiv (twist (detRep (Fin 1) ψ) (detChar (Fin 1) η))) : χ = ψ * η := by
  refine MonoidHom.ext fun x => Units.ext ?_
  let g : GL (Fin 1) k := Matrix.GeneralLinearGroup.scalar _ x
  have hg : Matrix.GeneralLinearGroup.det g = x := by
    ext; simp [g, Matrix.GeneralLinearGroup.scalar]
  obtain ⟨y, hy⟩ := φ.surjective 1
  have h1 := LinearMap.congr_fun (φ.isIntertwining' g) y
  have hy' : φ.toLinearMap y = 1 := hy
  have h2 : detRep (Fin 1) χ g y = (χ x : ℂ) • y := by simp [detRep, hg]
  simp only [LinearMap.comp_apply, h2, map_smul, hy'] at h1
  simpa [twist, detRep, ofChar, hg, mul_comm] using h1
/- English proof (translation)
Establish `hg : ∀ g : GL (Fin 0) k, g = 1` using `fun g => Units.ext (Subsingleton.elim _ _)`. Set `f : ℂ →ₗ[ℂ] IndSp (points (Fin 0)) ((ofChar (torusChar ψ)).comp (leviTorus k (Fin 0)).symm.toMonoidHom)` to `{ toFun := fun c => ⟨⟨fun _ => c, fun p g => by`. Take `rfl : p = 1` from `Subtype.ext (hg _)`. Use the proof step `simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩`. Use the proof step `map_add' := fun a b => rfl`.

Use the proof step `map_smul' := fun a b => rfl }`. Establish `E : (detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (prinSeries ψ)` using `Representation.Equiv.mk' ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ (fun F => F.1.1 1) (fun c => rfl) (fun F => Subtype.ext (Subtype.ext (funext fun g => by rw [hg g])))`. Conclude with `GlobalTheory.Parabolic.isIrreducible_of_equiv E (isIrreducible_ofChar _)`.
-/
private theorem irr_zero (ψ : Fin 0 → kˣ →* ℂˣ) : (prinSeries ψ).IsIrreducible := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp (points (Fin 0)) ((ofChar (torusChar ψ)).comp (leviTorus k (Fin 0)).symm.toMonoidHom) :=
    { toFun := fun c => ⟨⟨fun _ => c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => rfl
      map_smul' := fun a b => rfl }
  have E : (detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (prinSeries ψ) :=
    Representation.Equiv.mk' ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ (fun F => F.1.1 1)
      (fun c => rfl) (fun F => Subtype.ext (Subtype.ext (funext fun g => by rw [hg g])))
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E (isIrreducible_ofChar _)
set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact fun ψ _ _ => irr_zero ψ`. Consider the case `succ n ih`. Introduce `ψ hψ hne`. Set `ψ₁ : Fin n → kˣ →* ℂˣ` to `fun i => ψ (Fin.castAdd 1 i)`.

Set `ψ₂ : Fin 1 → kˣ →* ℂˣ` to `fun _ => ψ (Fin.natAdd n 0)`. Establish `happ : Fin.append ψ₁ ψ₂ = ψ`. Establish `: ψ₂ = fun i => ψ (Fin.natAdd n i)` using `funext fun i => by rw [Subsingleton.elim i 0]`. Rewrite using `[this]`. Conclude with `Fin.append_castAdd_natAdd`.

Establish `h₁ : (prinSeries ψ₁).IsIrreducible` using `ih ψ₁ (fun i => hψ _) fun i j hij => hne _ _ fun h => hij (Fin.castAdd_injective _ _ h)`. Establish `h₂ : (prinSeries ψ₂).IsIrreducible` using `GlobalTheory.Parabolic.isIrreducible_of_equiv (GlobalTheory.PrinSat.oneEquiv _ (hψ _)) (isIrreducible_ofChar _)`. Set `σ₁ : Irr k n` to `⟨_, prinSeries ψ₁, isSmooth_parInd _ _, h₁⟩`. Set `σ₂ : Irr k 1` to `⟨_, prinSeries ψ₂, isSmooth_parInd _ _, h₂⟩`. Establish `hirr : (prod₂ σ₁.π σ₂.π).IsIrreducible`.

Use `H k n 1 n 1 σ₁ σ₂ _ _ _ _ (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries σ₁ (ψ := ψ₁) (fun i => hψ _) (.refl _)) (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries σ₂ (ψ := ψ₂) (fun i => hψ _) (.refl _)) ?_` and prove the remaining obligations. Introduce and unpack `a b h j hj ⟨φ⟩`. Establish `e : ψ (Fin.castAdd 1 a) = ψ (Fin.natAdd n 0) * absPow k (j : ℂ)` using `eq_of_twist φ`. Establish `hab : Fin.castAdd 1 a ≠ Fin.natAdd n 0` using `fun h => by`. Use `congrArg Fin.val h` as an intermediate fact.

Use `a.2` as an intermediate fact. Simplify using `at *`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `rfl | rfl | rfl : j = -1 ∨ j = 0 ∨ j = 1 := by`. Use `abs_le.1 hj` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `(hne _ _ hab.symm).2 ?_` and prove the remaining obligations. Rewrite using `[e, mul_assoc, ← absPow_add]`. Simplify using the standard rewrite rules. Conclude with `(hne _ _ hab).1 (by simpa using e)`.

Conclude with `(hne _ _ hab).2 (by simpa using e)`. Take `⟨E1⟩` from `PrinProd.stage_one (k := k) ψ₁ ψ₂`. Take `⟨E2⟩` from `PrinProd.stage_two (k := k) ψ₁ ψ₂`. Rewrite using `[← happ]`. Conclude with `GlobalTheory.Parabolic.isIrreducible_of_equiv (E1.trans E2) hirr`.
-/
private theorem irr_prin (H : GlobalTheory.Published.TotallyDisjointProductIrreducible) (n : ℕ) :
    ∀ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) →
      (∀ i j, i ≠ j → ψ i ≠ ψ j ∧ ψ i ≠ ψ j * absPow k 1) → (prinSeries ψ).IsIrreducible := by
  induction n with
  | zero => exact fun ψ _ _ => irr_zero ψ
  | succ n ih =>
    intro ψ hψ hne
    let ψ₁ : Fin n → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd 1 i)
    let ψ₂ : Fin 1 → kˣ →* ℂˣ := fun _ => ψ (Fin.natAdd n 0)
    have happ : Fin.append ψ₁ ψ₂ = ψ := by
      have : ψ₂ = fun i => ψ (Fin.natAdd n i) := funext fun i => by rw [Subsingleton.elim i 0]
      rw [this]
      exact Fin.append_castAdd_natAdd
    have h₁ : (prinSeries ψ₁).IsIrreducible :=
      ih ψ₁ (fun i => hψ _) fun i j hij => hne _ _ fun h => hij (Fin.castAdd_injective _ _ h)
    have h₂ : (prinSeries ψ₂).IsIrreducible :=
      GlobalTheory.Parabolic.isIrreducible_of_equiv (GlobalTheory.PrinSat.oneEquiv _ (hψ _)) (isIrreducible_ofChar _)
    let σ₁ : Irr k n := ⟨_, prinSeries ψ₁, isSmooth_parInd _ _, h₁⟩
    let σ₂ : Irr k 1 := ⟨_, prinSeries ψ₂, isSmooth_parInd _ _, h₂⟩
    have hirr : (prod₂ σ₁.π σ₂.π).IsIrreducible := by
      refine H k n 1 n 1 σ₁ σ₂ _ _ _ _
        (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries σ₁ (ψ := ψ₁) (fun i => hψ _) (.refl _))
        (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries σ₂ (ψ := ψ₂) (fun i => hψ _) (.refl _)) ?_
      rintro a b h j hj ⟨φ⟩
      have e : ψ (Fin.castAdd 1 a) = ψ (Fin.natAdd n 0) * absPow k (j : ℂ) := eq_of_twist φ
      have hab : Fin.castAdd 1 a ≠ Fin.natAdd n 0 := fun h => by
        have := congrArg Fin.val h
        have := a.2
        simp at *
        omega
      obtain rfl | rfl | rfl : j = -1 ∨ j = 0 ∨ j = 1 := by
        have := abs_le.1 hj
        omega
      · refine (hne _ _ hab.symm).2 ?_
        rw [e, mul_assoc, ← absPow_add]
        simp
      · exact (hne _ _ hab).1 (by simpa using e)
      · exact (hne _ _ hab).2 (by simpa using e)
    obtain ⟨E1⟩ := PrinProd.stage_one (k := k) ψ₁ ψ₂
    obtain ⟨E2⟩ := PrinProd.stage_two (k := k) ψ₁ ψ₂
    rw [← happ]
    exact GlobalTheory.Parabolic.isIrreducible_of_equiv (E1.trans E2) hirr
end UpperTheory.V.Hi.PsIrr
/- English proof (translation)
Introduce `H k _ _ _ _ n ω hω hne`. Establish `hi : (PS ω).IsIrreducible`. Use `PsIrr.irr_prin H.loc.disj n _ (fun i => (hω i).mul (isSmoothChar_of_isUnram (isUnram_absPow k _))) fun i j hij => ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Conclude with `(hne i j hij).1 (mul_right_cancel h)`. Rewrite `h` using `[mul_right_comm]`.

Conclude with `(hne i j hij).2 (mul_right_cancel h)`. Conclude with `⟨hi, fun V _ _ π hπ hs => (hs.nonempty_equiv hπ hi).map fun e => e.symm⟩`.
-/
theorem UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ω : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow k 1) → (PS ω).IsIrreducible ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), π.IsIrreducible → IsSubquotient π (PS ω) → Nonempty (π.Equiv (PS ω)) := by
  intro H k _ _ _ _ n ω hω hne
  have hi : (PS ω).IsIrreducible := by
    refine PsIrr.irr_prin H.loc.disj n _
      (fun i => (hω i).mul (isSmoothChar_of_isUnram (isUnram_absPow k _))) fun i j hij => ⟨fun h => ?_, fun h => ?_⟩
    · exact (hne i j hij).1 (mul_right_cancel h)
    · rw [mul_right_comm] at h
      exact (hne i j hij).2 (mul_right_cancel h)
  exact ⟨hi, fun V _ _ π hπ hs => (hs.nonempty_equiv hπ hi).map fun e => e.symm⟩
end

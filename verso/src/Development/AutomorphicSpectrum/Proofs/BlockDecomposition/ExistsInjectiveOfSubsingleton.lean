import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdMapInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMapLaw
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import BuildAid.D3
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

noncomputable section

namespace GlobalTheory.CompanionTheory.SubEmb

/- English proof (translation)
Use `haveI := hi`. Use `haveI : Nontrivial V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Take `⟨w, hw⟩` from `exists_ne (0 : Y)`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)`. Set `φ : π.IntertwiningMap τ` to `{ toFun := fun u => f u • w map_add' := fun a b => by simp [add_smul] map_smul' := fun c a => by simp [mul_smul] isIntertwining' := fun g => by`. Rewrite using `[Subsingleton.elim g 1, map_one, map_one]`.

Conclude with `LinearMap.ext fun _ => rfl }`. Use `⟨φ, (Representation.IsIrreducible.injective_or_eq_zero φ).resolve_right fun h => ?_⟩` and prove the remaining obligations. Establish `h1 : f v • w = 0` using `congrArg (fun ψ : π.IntertwiningMap τ => ψ v) h`. Conclude with `(smul_ne_zero hf hw) h1`.
-/
theorem exists_injective_of_subsingleton {G V Y : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Y] [Module ℂ Y] [Nontrivial Y] (π : Representation ℂ G V) (τ : Representation ℂ G Y)
    (hi : π.IsIrreducible) : ∃ φ : π.IntertwiningMap τ, Function.Injective φ := by
  classical
  haveI := hi
  haveI : Nontrivial V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : Y)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  let φ : π.IntertwiningMap τ :=
    { toFun := fun u => f u • w
      map_add' := fun a b => by simp [add_smul]
      map_smul' := fun c a => by simp [mul_smul]
      isIntertwining' := fun g => by
        rw [Subsingleton.elim g 1, map_one, map_one]
        exact LinearMap.ext fun _ => rfl }
  refine ⟨φ, (Representation.IsIrreducible.injective_or_eq_zero φ).resolve_right fun h => ?_⟩
  have h1 : f v • w = 0 := congrArg (fun ψ : π.IntertwiningMap τ => ψ v) h
  exact (smul_ne_zero hf hw) h1

/- English proof (translation)
Use `haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩`. Establish `hirr : (prodIrr x hd).IsIrreducible` using `GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _`. Use `haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr`. Conclude with `exists_injective_of_subsingleton π _ hi`.
-/
theorem zero_case {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin 0) k) V) (hi : π.IsIrreducible)
    (x : Fin 0 → IrrGL k) (hd : ∑ a, (x a).1 = 0) :
    ∃ φ : π.IntertwiningMap (prodIrr x hd), Function.Injective φ := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  have hirr : (prodIrr x hd).IsIrreducible := GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd_zero _ _
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hirr
  exact exists_injective_of_subsingleton π _ hi

/- English proof (translation)
Establish `hF0` using `GlobalTheory.CompanionTheory.ProdInj.prod₂_map_injective k a b _ _ W' σ _ ρ f hf`. Take `⟨F, hF⟩` from `hF0`. Set `y : Fin 1 → IrrGL k` to `fun _ => IrrGL.of ρ hρs hρi`. Establish `hy : ∑ i, (y i).1 = b` using `by simp [y, IrrGL.of]`. Establish `hy' : ∑ i : Fin 1, (IrrGL.of ρ hρs hρi).1 = (IrrGL.of ρ hρs hρi).1` using `by simp`.

Establish `e₁0` using `nonempty_equiv_prodIrr_one (IrrGL.of ρ hρs hρi) hy'`. Take `⟨e₁⟩` from `e₁0`. Establish `e₂ : ρ.Equiv (prodIrr y hy)` using `(IrrGL.equivOf ρ hρs hρi).trans e₁`. Establish `hd : ∑ i, (Fin.append x' y i).1 = a + b`. Rewrite using `[Fin.sum_univ_add]`.

Simplify using `only [Fin.append_left, Fin.append_right]`. Rewrite using `[hd', hy]`. Establish `e₃0` using `hstage k c 1 a b x' y hd' hy hd`. Take `⟨e₃⟩` from `e₃0`. Use `⟨c + 1, Fin.append x' y, hd, fun i => ?_, ?_⟩` and prove the remaining obligations.

Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.append_left]`. Conclude with `hcusp i`. Rewrite using `[Fin.append_right]`. Conclude with `IrrGL.isCusp_of.2 ⟨hb, hρc⟩`.

Set `E` to `(prod₂Equiv (Representation.Equiv.refl _) e₂).trans e₃`. Use `⟨E.toIntertwiningMap.comp F, ?_⟩` and prove the remaining obligations. Conclude with `E.toLinearEquiv.injective.comp hF`.
-/
theorem succ_case
    (hstage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t), Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h)))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b c : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W')
    (hb : 0 < b) (hρs : IsSmooth ρ) (hρi : ρ.IsIrreducible) (hρc : IsCuspidal ρ)
    (x' : Fin c → IrrGL k) (hd' : ∑ i, (x' i).1 = a) (hcusp : ∀ i, (x' i).IsCusp)
    (f : σ.IntertwiningMap (prodIrr x' hd')) (hf : Function.Injective f) :
    ∃ (c' : ℕ) (x : Fin c' → IrrGL k) (hd : ∑ i, (x i).1 = a + b), (∀ i, (x i).IsCusp) ∧
      ∃ Φ : (prod₂ σ ρ).IntertwiningMap (prodIrr x hd), Function.Injective Φ := by
  have hF0 := GlobalTheory.CompanionTheory.ProdInj.prod₂_map_injective k a b _ _ W' σ _ ρ f hf
  obtain ⟨F, hF⟩ := hF0
  let y : Fin 1 → IrrGL k := fun _ => IrrGL.of ρ hρs hρi
  have hy : ∑ i, (y i).1 = b := by simp [y, IrrGL.of]
  have hy' : ∑ i : Fin 1, (IrrGL.of ρ hρs hρi).1 = (IrrGL.of ρ hρs hρi).1 := by simp
  have e₁0 := nonempty_equiv_prodIrr_one (IrrGL.of ρ hρs hρi) hy'
  obtain ⟨e₁⟩ := e₁0
  have e₂ : ρ.Equiv (prodIrr y hy) := (IrrGL.equivOf ρ hρs hρi).trans e₁
  have hd : ∑ i, (Fin.append x' y i).1 = a + b := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hd', hy]
  have e₃0 := hstage k c 1 a b x' y hd' hy hd
  obtain ⟨e₃⟩ := e₃0
  refine ⟨c + 1, Fin.append x' y, hd, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hcusp i
    · rw [Fin.append_right]; exact IrrGL.isCusp_of.2 ⟨hb, hρc⟩
  · let E := (prod₂Equiv (Representation.Equiv.refl _) e₂).trans e₃
    refine ⟨E.toIntertwiningMap.comp F, ?_⟩
    exact E.toLinearEquiv.injective.comp hF

/- English proof (translation)
Introduce `k _ _ _ _ N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `V _ _ π hs hi`. Distinguish the cases in `hN0 : N = 0`.

Substitute `hN0` using the available equality. Conclude with `⟨0, Fin.elim0, by simp, fun a => a.elim0, zero_case π hi _ _⟩`. Establish `hN : 0 < N` using `Nat.pos_of_ne_zero hN0`. Establish `h0` using `GlobalTheory.JacFactor.exists_map_jac₂ k N V π hs hi hN`. Take `⟨a, b, h, W, W', _, _, _, _, σ, ρ, hb, hσs, hσi, hρs, hρi, hρc, φ, hφ⟩` from `h0`.

Substitute `h` using the available equality. Establish `h1` using `GlobalTheory.CompanionTheory.Frob.exists_injective_of_jac₂ k a b V W W' π σ ρ hs hi φ hφ`. Take `⟨ψ, hψ⟩` from `h1`. Establish `h2` using `ih a (by omega) W σ hσs hσi`. Take `⟨c, x', hd', hcusp, f, hf⟩` from `h2`.

Establish `h3` using `succ_case hstage σ ρ hb hρs hρi hρc x' hd' hcusp f hf`. Take `⟨c', x, hd, hx, Φ, hΦ⟩` from `h3`. Conclude with `⟨c', x, hd, hx, Φ.comp ψ, hΦ.comp hψ⟩`.
-/
theorem subEmbedding_of_stage
    (hstage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t), Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h))) :
    Ysupp.SubEmbedding := by
  intro k _ _ _ _ N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ π hs hi
    by_cases hN0 : N = 0
    · subst hN0
      exact ⟨0, Fin.elim0, by simp, fun a => a.elim0, zero_case π hi _ _⟩
    · have hN : 0 < N := Nat.pos_of_ne_zero hN0
      have h0 := GlobalTheory.JacFactor.exists_map_jac₂ k N V π hs hi hN
      obtain ⟨a, b, h, W, W', _, _, _, _, σ, ρ, hb, hσs, hσi, hρs, hρi, hρc, φ, hφ⟩ := h0
      subst h
      have h1 := GlobalTheory.CompanionTheory.Frob.exists_injective_of_jac₂ k a b V W W' π σ ρ hs hi φ hφ
      obtain ⟨ψ, hψ⟩ := h1
      have h2 := ih a (by omega) W σ hσs hσi
      obtain ⟨c, x', hd', hcusp, f, hf⟩ := h2
      have h3 := succ_case hstage σ ρ hb hρs hρi hρc x' hd' hcusp f hf
      obtain ⟨c', x, hd, hx, Φ, hΦ⟩ := h3
      exact ⟨c', x, hd, hx, Φ.comp ψ, hΦ.comp hψ⟩

end GlobalTheory.CompanionTheory.SubEmb

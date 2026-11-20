import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermProjectionStep
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermGeneralCoordinates
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def affineGerm {σ : Type} [Fintype σ] (w : σ → ℂ) (L : (σ → ℂ) →L[ℂ] ℂ) (c : ℂ) : holGerms w :=
  ⟨↑(fun z : σ → ℂ => L z + c), fun z => L z + c, (L.analyticAt w).add analyticAt_const, rfl⟩

/- English proof (translation)
Take `⟨f, hf, hφ⟩` from `φ.2`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e1 : ((germPull (B.comp π) ((B.comp π).analyticAt w) rfl φ : holGerms w) : Germ (𝓝 w) ℂ) = ↑(f ∘ (B.comp π))` using `germPull_coe (⇑(B.comp π)) ((B.comp π).analyticAt w) rfl φ f hφ`. Establish `e2 : ((germPull B (B.analyticAt (π w)) rfl φ : holGerms (π w)) : Germ (𝓝 (π w)) ℂ) = ↑(f ∘ B)` using `germPull_coe _ _ rfl φ f hφ`. Conclude with `e1.trans (germPull_coe π (π.analyticAt w) rfl _ (f ∘ B) e2.symm).symm`.
-/
theorem germPull_comp_apply {σ τ : Type} [Fintype σ] [Fintype τ] {d : ℕ} (w : σ → ℂ)
    (π : (σ → ℂ) →L[ℂ] (τ → ℂ)) (B : (τ → ℂ) →L[ℂ] (Fin d → ℂ)) (φ : holGerms (B (π w))) :
    germPull (B.comp π) ((B.comp π).analyticAt w) rfl φ =
      germPull π (π.analyticAt w) rfl (germPull B (B.analyticAt (π w)) rfl φ) := by
  obtain ⟨f, hf, hφ⟩ := φ.2
  apply Subtype.ext
  have e1 : ((germPull (B.comp π) ((B.comp π).analyticAt w) rfl φ : holGerms w) : Germ (𝓝 w) ℂ) =
      ↑(f ∘ (B.comp π)) := germPull_coe (⇑(B.comp π)) ((B.comp π).analyticAt w) rfl φ f hφ
  have e2 : ((germPull B (B.analyticAt (π w)) rfl φ : holGerms (π w)) : Germ (𝓝 (π w)) ℂ) = ↑(f ∘ B) :=
    germPull_coe _ _ rfl φ f hφ
  exact e1.trans (germPull_coe π (π.analyticAt w) rfl _ (f ∘ B) e2.symm).symm

/- English proof (translation)
Set `k : ℂ → holGerms (A w)` to `fun a => ⟨↑(fun _ : Fin d → ℂ => a), fun _ => a, analyticAt_const, rfl⟩`. Establish `hk : ∀ a, ((germPull A (A.analyticAt w) rfl (k a) : holGerms w) : Germ (𝓝 w) ℂ) = ↑((fun _ : Fin d → ℂ => a) ∘ A)` using `fun a => germPull_coe _ _ rfl (k a) _ rfl`. Use `⟨∑ i, MvPolynomial.C (k (L (fun j => if i = j then 1 else 0))) * MvPolynomial.X i + MvPolynomial.C (k c), ?_⟩` and prove the remaining obligations. Simplify using `only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Subring.coe_add, AddSubmonoidClass.coe_finsetSum]`. Simplify using `only [Subring.coe_mul, hk]`. Express the relevant statement in the definitionally equal form `∑ i, Germ.coeRingHom _ ((fun _ : Fin d → ℂ => L (fun j => if i = j then 1 else 0)) ∘ A) * Germ.coeRingHom _ (fun z : σ → ℂ => z i) + Germ.coeRingHom _ ((fun _ : Fin d → ℂ => c) ∘ A) = Germ.coeRingHom _ (fun z : σ → ℂ => L z + c)`. Simplify using `only [← map_mul, ← map_sum, ← map_add]`. Use `congr 1`.

Use function extensionality and compare the values at `z`. Establish `hL` using `(L : (σ → ℂ) →ₗ[ℂ] ℂ).pi_apply_eq_sum_univ z`. Simplify using `only [ContinuousLinearMap.coe_coe] at hL`. Simplify using `[hL, Finset.sum_apply, mul_comm]`.
-/
theorem affineGerm_eq_eval₂ {σ : Type} [Fintype σ] {d : ℕ} (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (L : (σ → ℂ) →L[ℂ] ℂ) (c : ℂ) :
    ∃ F : MvPolynomial σ (holGerms (A w)),
      MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F = affineGerm w L c := by
  classical
  let k : ℂ → holGerms (A w) := fun a => ⟨↑(fun _ : Fin d → ℂ => a), fun _ => a, analyticAt_const, rfl⟩
  have hk : ∀ a, ((germPull A (A.analyticAt w) rfl (k a) : holGerms w) : Germ (𝓝 w) ℂ) =
      ↑((fun _ : Fin d → ℂ => a) ∘ A) := fun a => germPull_coe _ _ rfl (k a) _ rfl
  refine ⟨∑ i, MvPolynomial.C (k (L (fun j => if i = j then 1 else 0))) * MvPolynomial.X i +
    MvPolynomial.C (k c), ?_⟩
  simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_X]
  apply Subtype.ext
  rw [Subring.coe_add, AddSubmonoidClass.coe_finsetSum]
  simp only [Subring.coe_mul, hk]
  change ∑ i, Germ.coeRingHom _ ((fun _ : Fin d → ℂ => L (fun j => if i = j then 1 else 0)) ∘ A) *
      Germ.coeRingHom _ (fun z : σ → ℂ => z i) + Germ.coeRingHom _ ((fun _ : Fin d → ℂ => c) ∘ A) =
    Germ.coeRingHom _ (fun z : σ → ℂ => L z + c)
  simp only [← map_mul, ← map_sum, ← map_add]
  congr 1
  funext z
  have hL := (L : (σ → ℂ) →ₗ[ℂ] ℂ).pi_apply_eq_sum_univ z
  simp only [ContinuousLinearMap.coe_coe] at hL
  simp [hL, Finset.sum_apply, mul_comm]

/- English proof (translation)
Set `eo : Option (Fin m) ≃ σ` to `(finSuccEquiv m).symm.trans (Fintype.equivFinOfCardEq hm).symm`. Set `e : (σ → ℂ) ≃L[ℂ] (Option (Fin m) → ℂ)` to `(LinearEquiv.funCongrLeft ℂ ℂ eo).toContinuousLinearEquiv`. Take `⟨f, hf, hfφ⟩` from `φ.2`. Set `F0 : (Option (Fin m) → ℂ) → ℂ` to `fun y => f (e.symm y + w)`. Establish `hF0 : AnalyticAt ℂ F0 0` using `hf.comp_of_eq ((e.symm.analyticAt 0).add analyticAt_const) (by simp)`.

Establish `he : Tendsto (fun z : σ → ℂ => e (z - w)) (𝓝 w) (𝓝 0)`. Use `((e : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ)).continuous.comp (continuous_sub_right w)).tendsto w` as an intermediate fact. Rewrite `this` using `[Function.comp_apply, sub_self, map_zero]`. Conclude with `this`. Establish `hnz : ¬ ∀ᶠ y in 𝓝 (0 : Option (Fin m) → ℂ), F0 y = 0`.

Introduce `h`. Apply `hφ` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hfφ]`. Conclude with `Germ.coe_eq.2 ((he.eventually h).mono fun z hz => by simpa [F0] using hz)`.

Take `⟨A, n, hAn⟩` from `hG (Fin m) F0 hF0 hnz`. Set `M : (σ → ℂ) ≃L[ℂ] (Option (Fin m) → ℂ)` to `e.trans A.symm`. Set `Pl : (Option (Fin m) → ℂ) →L[ℂ] (Fin m → ℂ)` to `ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin m) => ℂ) (some i)`. Set `π : (σ → ℂ) →L[ℂ] (Fin m → ℂ)` to `Pl.comp (M : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ))`. Set `T : (σ → ℂ) →L[ℂ] ℂ` to `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin m) => ℂ) none).comp (M : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ))`.

Establish `hMt : Tendsto (fun z : σ → ℂ => M (z - w)) (𝓝 w) (𝓝 0)`. Use `((M : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ)).continuous.comp (continuous_sub_right w)).tendsto w` as an intermediate fact. Rewrite `this` using `[Function.comp_apply, sub_self, map_zero]`. Conclude with `this`. Establish `hinv : ∀ z, e.symm (A (M (z - w))) + w = z` using `fun z => by simp [M]`.

Establish `hsome : ∀ z, (fun i => M (z - w) (some i)) = π z - π w` using `fun z => by`. Use function extensionality and compare the values at `i`. Simplify using `[π, Pl, map_sub]`. Establish `hnone : ∀ z, M (z - w) none = T z + -T w` using `fun z => by simp [T, sub_eq_add_neg]`. Use `⟨π, T, n, fun ψ => ?_⟩` and prove the remaining obligations.

Take `⟨h, hh, hhψ⟩` from `ψ.2`. Set `g : (Option (Fin m) → ℂ) → ℂ` to `fun y => F0 (A y)`. Set `H : (Option (Fin m) → ℂ) → ℂ` to `fun y => h (e.symm (A y) + w)`. Establish `hg : AnalyticAt ℂ g 0` using `hF0.comp_of_eq (A.analyticAt 0) (map_zero A)`. Establish `hH : AnalyticAt ℂ H 0` using `hh.comp_of_eq (((e.symm.analyticAt _).comp (A.analyticAt 0)).add analyticAt_const) (by simp)`.

Take `⟨q, a, hq, ha, hev⟩` from `hD (Fin m) n g H hg hH hAn`. Establish `hev' : ∀ᶠ z in 𝓝 w, h z = q (M (z - w)) * f z + ∑ j : Fin n, a j (π z - π w) * (T z + -T w) ^ (j : ℕ)` using `by filter_upwards [hMt.eventually hev] with z hz`. Simplify using `only [H, g, F0, hinv, hsome, hnone] at hz`. Conclude with `hz`. Set `a' : Fin n → holGerms (π w)` to `fun j => ⟨↑(fun u => a j (u - π w)), fun u => a j (u - π w), (ha j).comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self _), rfl⟩`.

Establish `hMa : AnalyticAt ℂ (fun z : σ → ℂ => M (z - w)) w` using `(M.analyticAt _).comp (analyticAt_id.sub analyticAt_const)`. Set `r : holGerms w` to `⟨↑(fun z => q (M (z - w))), fun z => q (M (z - w)), hq.comp_of_eq hMa (by simp), rfl⟩`. Use `⟨r, a', ?_⟩` and prove the remaining obligations. Establish `hι : ∀ j, ((germPull π (π.analyticAt w) rfl (a' j) : holGerms w) : Germ (𝓝 w) ℂ) = ↑((fun u => a j (u - π w)) ∘ π)` using `fun j => germPull_coe _ _ rfl (a' j) _ rfl`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Subring.coe_add, Subring.coe_mul, ← hfφ, ← hhψ]`. Rewrite using `[AddSubmonoidClass.coe_finsetSum]`. Simplify using `only [Subring.coe_mul, Subring.coe_pow, hι]`. Express the relevant statement in the definitionally equal form `(↑h : Germ (𝓝 w) ℂ) = Germ.coeRingHom _ (fun z => q (M (z - w))) * Germ.coeRingHom _ f + ∑ j : Fin n, Germ.coeRingHom _ ((fun u => a j (u - π w)) ∘ π) * Germ.coeRingHom _ (fun z : σ → ℂ => T z + -T w) ^ (j : ℕ)`. Simplify using `only [← map_mul, ← map_pow, ← map_sum, ← map_add]`.

Use `Germ.coe_eq.2 ?_` and prove the remaining obligations. Use `filter_upwards [hev'] with z hz`. Simplify using `[hz, Finset.sum_apply]`.
-/
theorem germ_division_after_coordinates (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) {σ : Type} [Fintype σ] {m : ℕ} (hm : Fintype.card σ = m + 1)
    (w : σ → ℂ) (φ : holGerms w) (hφ : φ ≠ 0) :
    ∃ (π : (σ → ℂ) →L[ℂ] (Fin m → ℂ)) (T : (σ → ℂ) →L[ℂ] ℂ) (n : ℕ),
      ∀ ψ : holGerms w, ∃ (r : holGerms w) (a : Fin n → holGerms (π w)),
        ψ = r * φ + ∑ j : Fin n, germPull π (π.analyticAt w) rfl (a j) * affineGerm w T (-T w) ^ (j : ℕ) := by
  classical
  let eo : Option (Fin m) ≃ σ := (finSuccEquiv m).symm.trans (Fintype.equivFinOfCardEq hm).symm
  let e : (σ → ℂ) ≃L[ℂ] (Option (Fin m) → ℂ) := (LinearEquiv.funCongrLeft ℂ ℂ eo).toContinuousLinearEquiv
  obtain ⟨f, hf, hfφ⟩ := φ.2
  let F0 : (Option (Fin m) → ℂ) → ℂ := fun y => f (e.symm y + w)
  have hF0 : AnalyticAt ℂ F0 0 :=
    hf.comp_of_eq ((e.symm.analyticAt 0).add analyticAt_const) (by simp)
  have he : Tendsto (fun z : σ → ℂ => e (z - w)) (𝓝 w) (𝓝 0) := by
    have := ((e : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ)).continuous.comp (continuous_sub_right w)).tendsto w
    rw [Function.comp_apply, sub_self, map_zero] at this
    exact this
  have hnz : ¬ ∀ᶠ y in 𝓝 (0 : Option (Fin m) → ℂ), F0 y = 0 := by
    intro h
    apply hφ
    apply Subtype.ext
    rw [← hfφ]
    exact Germ.coe_eq.2 ((he.eventually h).mono fun z hz => by simpa [F0] using hz)
  obtain ⟨A, n, hAn⟩ := hG (Fin m) F0 hF0 hnz
  let M : (σ → ℂ) ≃L[ℂ] (Option (Fin m) → ℂ) := e.trans A.symm
  let Pl : (Option (Fin m) → ℂ) →L[ℂ] (Fin m → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin m) => ℂ) (some i)
  let π : (σ → ℂ) →L[ℂ] (Fin m → ℂ) := Pl.comp (M : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ))
  let T : (σ → ℂ) →L[ℂ] ℂ := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin m) => ℂ) none).comp
    (M : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ))
  have hMt : Tendsto (fun z : σ → ℂ => M (z - w)) (𝓝 w) (𝓝 0) := by
    have := ((M : (σ → ℂ) →L[ℂ] (Option (Fin m) → ℂ)).continuous.comp (continuous_sub_right w)).tendsto w
    rw [Function.comp_apply, sub_self, map_zero] at this
    exact this
  have hinv : ∀ z, e.symm (A (M (z - w))) + w = z := fun z => by simp [M]
  have hsome : ∀ z, (fun i => M (z - w) (some i)) = π z - π w := fun z => by
    funext i; simp [π, Pl, map_sub]
  have hnone : ∀ z, M (z - w) none = T z + -T w := fun z => by simp [T, sub_eq_add_neg]
  refine ⟨π, T, n, fun ψ => ?_⟩
  obtain ⟨h, hh, hhψ⟩ := ψ.2
  let g : (Option (Fin m) → ℂ) → ℂ := fun y => F0 (A y)
  let H : (Option (Fin m) → ℂ) → ℂ := fun y => h (e.symm (A y) + w)
  have hg : AnalyticAt ℂ g 0 := hF0.comp_of_eq (A.analyticAt 0) (map_zero A)
  have hH : AnalyticAt ℂ H 0 :=
    hh.comp_of_eq (((e.symm.analyticAt _).comp (A.analyticAt 0)).add analyticAt_const) (by simp)
  obtain ⟨q, a, hq, ha, hev⟩ := hD (Fin m) n g H hg hH hAn
  have hev' : ∀ᶠ z in 𝓝 w, h z = q (M (z - w)) * f z +
      ∑ j : Fin n, a j (π z - π w) * (T z + -T w) ^ (j : ℕ) := by
    filter_upwards [hMt.eventually hev] with z hz
    simp only [H, g, F0, hinv, hsome, hnone] at hz
    exact hz
  let a' : Fin n → holGerms (π w) := fun j =>
    ⟨↑(fun u => a j (u - π w)), fun u => a j (u - π w),
      (ha j).comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self _), rfl⟩
  have hMa : AnalyticAt ℂ (fun z : σ → ℂ => M (z - w)) w :=
    (M.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  let r : holGerms w := ⟨↑(fun z => q (M (z - w))), fun z => q (M (z - w)),
    hq.comp_of_eq hMa (by simp), rfl⟩
  refine ⟨r, a', ?_⟩
  have hι : ∀ j, ((germPull π (π.analyticAt w) rfl (a' j) : holGerms w) : Germ (𝓝 w) ℂ) =
      ↑((fun u => a j (u - π w)) ∘ π) := fun j => germPull_coe _ _ rfl (a' j) _ rfl
  apply Subtype.ext
  simp only [Subring.coe_add, Subring.coe_mul, ← hfφ, ← hhψ]
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [Subring.coe_mul, Subring.coe_pow, hι]
  change (↑h : Germ (𝓝 w) ℂ) = Germ.coeRingHom _ (fun z => q (M (z - w))) * Germ.coeRingHom _ f +
    ∑ j : Fin n, Germ.coeRingHom _ ((fun u => a j (u - π w)) ∘ π) *
      Germ.coeRingHom _ (fun z : σ → ℂ => T z + -T w) ^ (j : ℕ)
  simp only [← map_mul, ← map_pow, ← map_sum, ← map_add]
  refine Germ.coe_eq.2 ?_
  filter_upwards [hev'] with z hz
  simp [hz, Finset.sum_apply]

/- English proof (translation)
Take `⟨hBinj, hBgen, hBint⟩` from `hB`. Establish `hcompR : germPull (B.comp π) ((B.comp π).analyticAt w) rfl = (germPull π (π.analyticAt w) rfl).comp (germPull B (B.analyticAt (π w)) rfl)` using `RingHom.ext fun x => germPull_comp_apply w π B x`. Establish `hcoordι : ∀ k, germPull π (π.analyticAt w) rfl (coordGerm (π w) k) = affineGerm w ((ContinuousLinearMap.proj (R` using `ℂ) (φ := fun _ : τ => ℂ) k).comp π) 0 := by`. Introduce `k`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[germPull_coe _ _ rfl _ (fun u : τ → ℂ => u k) rfl]`. Use `show (↑((fun u : τ → ℂ => u k) ∘ π) : Germ (𝓝 w) ℂ) = ↑(fun z : σ → ℂ => π z k + 0)`. Simplify using `only [add_zero]`. Both sides reduce to the same expression. Generalize the expression as in `germPull π (π.analyticAt w) rfl = ι at hdiv hBinj hBgen hBint hcompR hcoordι`.

Generalize the expression as in `germPull B (B.analyticAt (π w)) rfl = pB at hBinj hBgen hBint hcompR`. It suffices to establish `H : (∀ φ : holGerms (B (π w)), ι (pB φ) ∈ P → φ = 0) ∧ (∀ ψ : holGerms w, ∃ F : MvPolynomial σ (holGerms (B (π w))), ψ - MvPolynomial.eval₂ (ι.comp pB) (coordGerm w) F ∈ P) ∧ (∀ i : σ, ∃ q : Polynomial (holGerms (B (π w))), q.Monic ∧ q.eval₂ (ι.comp pB) (coordGerm w i) ∈ P) by`. Unfold `IsFiniteGermProjection`. Rewrite using `[hcompR]`. Conclude with `H`.

Set `_ : Algebra (holGerms (B (π w))) (holGerms w ⧸ P)` to `((Ideal.Quotient.mk P).comp (ι.comp pB)).toAlgebra`. Establish `hRH : ((Ideal.Quotient.mk P).comp ι).comp pB = algebraMap (holGerms (B (π w))) (holGerms w ⧸ P)` using `RingHom.ext fun _ => rfl`. Set `Adj` to `Algebra.adjoin (holGerms (B (π w))) (Set.range fun i => Ideal.Quotient.mk P (coordGerm w i))`. Establish `hAdj : Adj = (MvPolynomial.aeval fun i => Ideal.Quotient.mk P (coordGerm w i)).range` using `Algebra.adjoin_range_eq_range_aeval _ _`. Set `Icl` to `integralClosure (holGerms (B (π w))) (holGerms w ⧸ P)`.

Establish `hev : ∀ F : MvPolynomial σ (holGerms (B (π w))), Ideal.Quotient.mk P (MvPolynomial.eval₂ (ι.comp pB) (coordGerm w) F) = MvPolynomial.aeval (fun i => Ideal.Quotient.mk P (coordGerm w i)) F`. Introduce `F`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]`. Both sides reduce to the same expression. Establish `haff : ∀ (L : (σ → ℂ) →L[ℂ] ℂ) (c : ℂ), Ideal.Quotient.mk P (affineGerm w L c) ∈ Adj`.

Introduce `L c`. Choose the witnesses or unpack the hypotheses as in `⟨F, hF⟩ : ∃ F : MvPolynomial σ (holGerms (B (π w))), MvPolynomial.eval₂ (ι.comp pB) (coordGerm w) F = affineGerm w L c := by`. Establish `h` using `affineGerm_eq_eval₂ w (B.comp π) L c`. Rewrite `h` using `[hcompR]`. Conclude with `h`.

Rewrite using `[← hF, hev, hAdj]`. Conclude with `⟨F, rfl⟩`. Establish `hcoordAdj : ∀ k, Ideal.Quotient.mk P (ι (coordGerm (π w) k)) ∈ Adj`. Introduce `k`. Rewrite using `[hcoordι]`.

Conclude with `haff _ _`. Establish `hcoordInt : ∀ k, IsIntegral (holGerms (B (π w))) (Ideal.Quotient.mk P (ι (coordGerm (π w) k)))`. Introduce `k`. Take `⟨q, hq, hqP⟩` from `hBint k`. Use `⟨q, hq, ?_⟩` and prove the remaining obligations.

Establish `h1` using `Polynomial.hom_eval₂ q pB ((Ideal.Quotient.mk P).comp ι) (coordGerm (π w) k)`. Rewrite `h1` using `[RingHom.comp_apply, RingHom.comp_apply]`. Rewrite using `[← hRH, ← h1]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hqP`. Establish `hR : ∀ a : holGerms (π w), Ideal.Quotient.mk P (ι a) ∈ Adj ∧ Ideal.Quotient.mk P (ι a) ∈ Icl`.

Introduce `a`. Take `⟨F, hF⟩` from `hBgen a`. Establish `h1 : Ideal.Quotient.mk P (ι a) = MvPolynomial.aeval (fun k => Ideal.Quotient.mk P (ι (coordGerm (π w) k))) F`. Rewrite using `[MvPolynomial.aeval_def, ← hRH]`. Establish `h2` using `MvPolynomial.eval₂_comp_left ((Ideal.Quotient.mk P).comp ι) pB (coordGerm (π w)) F`.

Rewrite `h2` using `[RingHom.comp_apply]`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Conclude with `Ideal.Quotient.eq.2 (by rw [← map_sub]; exact hF)`. Establish `hmem : Ideal.Quotient.mk P (ι a) ∈ Algebra.adjoin (holGerms (B (π w))) (Set.range fun k => Ideal.Quotient.mk P (ι (coordGerm (π w) k)))`. Rewrite using `[h1, Algebra.adjoin_range_eq_range_aeval]`.

Conclude with `⟨F, rfl⟩`. Conclude with `⟨Algebra.adjoin_le (Set.range_subset_iff.2 hcoordAdj) hmem, Algebra.adjoin_le (Set.range_subset_iff.2 hcoordInt) hmem⟩`. Establish `hθInt : Ideal.Quotient.mk P (affineGerm w T c) ∈ Icl`. Take `⟨b, hb⟩` from `hdiv (affineGerm w T c ^ n)`. Set `b' : Fin n → Icl` to `fun j => ⟨Ideal.Quotient.mk P (ι (-b j)), (hR (-b j)).2⟩`.

Establish `hmon : (Polynomial.X ^ n + ∑ j : Fin n, Polynomial.C (b' j) * Polynomial.X ^ (j : ℕ)).Monic` using `Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)`. Establish `hI : IsIntegral Icl (Ideal.Quotient.mk P (affineGerm w T c))`. Use `⟨_, hmon, ?_⟩` and prove the remaining obligations. Establish `hS : affineGerm w T c ^ n + ∑ j : Fin n, ι (-b j) * affineGerm w T c ^ (j : ℕ) ∈ P`. Establish `e : affineGerm w T c ^ n + ∑ j : Fin n, ι (-b j) * affineGerm w T c ^ (j : ℕ) = affineGerm w T c ^ n - ∑ j : Fin n, ι (b j) * affineGerm w T c ^ (j : ℕ)`.

Simplify using `only [map_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]`. Rewrite using `[e]`. Conclude with `hb`. Establish `h0` using `Ideal.Quotient.eq_zero_iff_mem.2 hS`. Rewrite `h0` using `[map_add, map_sum, map_pow]`.

Simplify using `only [map_mul, map_pow] at h0`. Rewrite using `[Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]`. Simplify using `only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]`. Conclude with `h0`. Conclude with `isIntegral_trans (R := holGerms (B (π w))) (A := Icl) _ hI`.

Establish `hall : ∀ ψ : holGerms w, Ideal.Quotient.mk P ψ ∈ Adj ∧ Ideal.Quotient.mk P ψ ∈ Icl`. Introduce `ψ`. Take `⟨a, ha⟩` from `hdiv ψ`. Establish `hψ : Ideal.Quotient.mk P ψ = ∑ j : Fin n, Ideal.Quotient.mk P (ι (a j)) * Ideal.Quotient.mk P (affineGerm w T c) ^ (j : ℕ)`. Rewrite using `[Ideal.Quotient.eq.2 ha, map_sum]`.

Simplify using `only [map_mul, map_pow]`. Rewrite using `[hψ]`. Conclude with `⟨Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hR (a j)).1 (Subalgebra.pow_mem _ (haff T c) _), Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hR (a j)).2 (Subalgebra.pow_mem _ hθInt _)⟩`. Use `⟨fun φ hφ => hBinj φ hφ, fun ψ => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `(hall ψ).1`.

Rewrite `h` using `[hAdj]`. Take `⟨F, hF⟩` from `h`. Use `⟨F, Ideal.Quotient.eq.1 ?_⟩` and prove the remaining obligations. Rewrite using `[hev]`. Conclude with `hF.symm`.

Take `⟨q, hq, h0⟩` from `(hall (coordGerm w i)).2`. Use `⟨q, hq, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.hom_eval₂]`. Conclude with `h0`.
-/
theorem isFiniteGermProjection_comp {σ τ : Type} [Fintype σ] [Fintype τ] (w : σ → ℂ) (P : Ideal (holGerms w))
    (π : (σ → ℂ) →L[ℂ] (τ → ℂ)) (T : (σ → ℂ) →L[ℂ] ℂ) (c : ℂ) (n : ℕ)
    (hdiv : ∀ ψ : holGerms w, ∃ a : Fin n → holGerms (π w),
      ψ - ∑ j : Fin n, germPull π (π.analyticAt w) rfl (a j) * affineGerm w T c ^ (j : ℕ) ∈ P)
    {d : ℕ} (B : (τ → ℂ) →L[ℂ] (Fin d → ℂ))
    (hB : IsFiniteGermProjection (π w) (P.comap (germPull π (π.analyticAt w) rfl)) B) :
    IsFiniteGermProjection w P (B.comp π) := by
  classical
  obtain ⟨hBinj, hBgen, hBint⟩ := hB
  have hcompR : germPull (B.comp π) ((B.comp π).analyticAt w) rfl =
      (germPull π (π.analyticAt w) rfl).comp (germPull B (B.analyticAt (π w)) rfl) :=
    RingHom.ext fun x => germPull_comp_apply w π B x
  have hcoordι : ∀ k, germPull π (π.analyticAt w) rfl (coordGerm (π w) k) =
      affineGerm w ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) k).comp π) 0 := by
    intro k
    apply Subtype.ext
    rw [germPull_coe _ _ rfl _ (fun u : τ → ℂ => u k) rfl]
    show (↑((fun u : τ → ℂ => u k) ∘ π) : Germ (𝓝 w) ℂ) = ↑(fun z : σ → ℂ => π z k + 0)
    simp only [add_zero]
    rfl
  generalize germPull π (π.analyticAt w) rfl = ι at hdiv hBinj hBgen hBint hcompR hcoordι
  generalize germPull B (B.analyticAt (π w)) rfl = pB at hBinj hBgen hBint hcompR
  suffices H : (∀ φ : holGerms (B (π w)), ι (pB φ) ∈ P → φ = 0) ∧
      (∀ ψ : holGerms w, ∃ F : MvPolynomial σ (holGerms (B (π w))),
        ψ - MvPolynomial.eval₂ (ι.comp pB) (coordGerm w) F ∈ P) ∧
      (∀ i : σ, ∃ q : Polynomial (holGerms (B (π w))), q.Monic ∧
        q.eval₂ (ι.comp pB) (coordGerm w i) ∈ P) by
    unfold IsFiniteGermProjection
    rw [hcompR]
    exact H
  let _ : Algebra (holGerms (B (π w))) (holGerms w ⧸ P) := ((Ideal.Quotient.mk P).comp (ι.comp pB)).toAlgebra
  have hRH : ((Ideal.Quotient.mk P).comp ι).comp pB = algebraMap (holGerms (B (π w))) (holGerms w ⧸ P) :=
    RingHom.ext fun _ => rfl
  let Adj := Algebra.adjoin (holGerms (B (π w))) (Set.range fun i => Ideal.Quotient.mk P (coordGerm w i))
  have hAdj : Adj = (MvPolynomial.aeval fun i => Ideal.Quotient.mk P (coordGerm w i)).range :=
    Algebra.adjoin_range_eq_range_aeval _ _
  let Icl := integralClosure (holGerms (B (π w))) (holGerms w ⧸ P)
  have hev : ∀ F : MvPolynomial σ (holGerms (B (π w))),
      Ideal.Quotient.mk P (MvPolynomial.eval₂ (ι.comp pB) (coordGerm w) F) = MvPolynomial.aeval (fun i => Ideal.Quotient.mk P (coordGerm w i)) F := by
    intro F
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
    rfl
  have haff : ∀ (L : (σ → ℂ) →L[ℂ] ℂ) (c : ℂ), Ideal.Quotient.mk P (affineGerm w L c) ∈ Adj := by
    intro L c
    obtain ⟨F, hF⟩ : ∃ F : MvPolynomial σ (holGerms (B (π w))),
        MvPolynomial.eval₂ (ι.comp pB) (coordGerm w) F = affineGerm w L c := by
      have h := affineGerm_eq_eval₂ w (B.comp π) L c
      rw [hcompR] at h
      exact h
    rw [← hF, hev, hAdj]
    exact ⟨F, rfl⟩

  have hcoordAdj : ∀ k, Ideal.Quotient.mk P (ι (coordGerm (π w) k)) ∈ Adj := by
    intro k
    rw [hcoordι]
    exact haff _ _
  have hcoordInt : ∀ k, IsIntegral (holGerms (B (π w))) (Ideal.Quotient.mk P (ι (coordGerm (π w) k))) := by
    intro k
    obtain ⟨q, hq, hqP⟩ := hBint k
    refine ⟨q, hq, ?_⟩
    have h1 := Polynomial.hom_eval₂ q pB ((Ideal.Quotient.mk P).comp ι) (coordGerm (π w) k)
    rw [RingHom.comp_apply, RingHom.comp_apply] at h1
    rw [← hRH, ← h1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hqP

  have hR : ∀ a : holGerms (π w), Ideal.Quotient.mk P (ι a) ∈ Adj ∧ Ideal.Quotient.mk P (ι a) ∈ Icl := by
    intro a
    obtain ⟨F, hF⟩ := hBgen a
    have h1 : Ideal.Quotient.mk P (ι a) = MvPolynomial.aeval (fun k => Ideal.Quotient.mk P (ι (coordGerm (π w) k))) F := by
      rw [MvPolynomial.aeval_def, ← hRH]
      have h2 := MvPolynomial.eval₂_comp_left ((Ideal.Quotient.mk P).comp ι) pB (coordGerm (π w)) F
      rw [RingHom.comp_apply] at h2
      refine Eq.trans ?_ h2
      exact Ideal.Quotient.eq.2 (by rw [← map_sub]; exact hF)
    have hmem : Ideal.Quotient.mk P (ι a) ∈ Algebra.adjoin (holGerms (B (π w)))
        (Set.range fun k => Ideal.Quotient.mk P (ι (coordGerm (π w) k))) := by
      rw [h1, Algebra.adjoin_range_eq_range_aeval]
      exact ⟨F, rfl⟩
    exact ⟨Algebra.adjoin_le (Set.range_subset_iff.2 hcoordAdj) hmem,
      Algebra.adjoin_le (Set.range_subset_iff.2 hcoordInt) hmem⟩

  have hθInt : Ideal.Quotient.mk P (affineGerm w T c) ∈ Icl := by
    obtain ⟨b, hb⟩ := hdiv (affineGerm w T c ^ n)
    let b' : Fin n → Icl := fun j => ⟨Ideal.Quotient.mk P (ι (-b j)), (hR (-b j)).2⟩
    have hmon : (Polynomial.X ^ n + ∑ j : Fin n, Polynomial.C (b' j) * Polynomial.X ^ (j : ℕ)).Monic :=
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
    have hI : IsIntegral Icl (Ideal.Quotient.mk P (affineGerm w T c)) := by
      refine ⟨_, hmon, ?_⟩
      have hS : affineGerm w T c ^ n + ∑ j : Fin n, ι (-b j) * affineGerm w T c ^ (j : ℕ) ∈ P := by
        have e : affineGerm w T c ^ n + ∑ j : Fin n, ι (-b j) * affineGerm w T c ^ (j : ℕ) =
            affineGerm w T c ^ n - ∑ j : Fin n, ι (b j) * affineGerm w T c ^ (j : ℕ) := by
          simp only [map_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
        rw [e]
        exact hb
      have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hS
      rw [map_add, map_sum, map_pow] at h0
      simp only [map_mul, map_pow] at h0
      rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      exact h0
    exact isIntegral_trans (R := holGerms (B (π w))) (A := Icl) _ hI

  have hall : ∀ ψ : holGerms w, Ideal.Quotient.mk P ψ ∈ Adj ∧ Ideal.Quotient.mk P ψ ∈ Icl := by
    intro ψ
    obtain ⟨a, ha⟩ := hdiv ψ
    have hψ : Ideal.Quotient.mk P ψ = ∑ j : Fin n, Ideal.Quotient.mk P (ι (a j)) * Ideal.Quotient.mk P (affineGerm w T c) ^ (j : ℕ) := by
      rw [Ideal.Quotient.eq.2 ha, map_sum]
      simp only [map_mul, map_pow]
    rw [hψ]
    exact ⟨Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hR (a j)).1
        (Subalgebra.pow_mem _ (haff T c) _),
      Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (hR (a j)).2 (Subalgebra.pow_mem _ hθInt _)⟩
  refine ⟨fun φ hφ => hBinj φ hφ, fun ψ => ?_, fun i => ?_⟩
  · have h := (hall ψ).1
    rw [hAdj] at h
    obtain ⟨F, hF⟩ := h
    refine ⟨F, Ideal.Quotient.eq.1 ?_⟩
    rw [hev]
    exact hF.symm
  · obtain ⟨q, hq, h0⟩ := (hall (coordGerm w i)).2
    refine ⟨q, hq, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    rw [Polynomial.hom_eval₂]
    exact h0

/- English proof (translation)
Introduce `σ _ w P hP hP0 IH`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, Fintype.card σ = m + 1 := by`. Break down `h : Fintype.card σ with _ | m` into its components or cases. It suffices to derive a contradiction. Set `e : (Fin 0 → ℂ) ≃L[ℂ] (σ → ℂ)` to `(LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq h)).toContinuousLinearEquiv`.

Establish `hF : IsField (holGerms w)` using `(germAffineEquiv e w).toMulEquiv.isField isField_holGerms_fin_zero`. Set `_` to `hF.toField`. Break down `Ideal.eq_bot_or_top P with h' | h'` into its components or cases. Conclude with `hP0 h'`. Conclude with `hP.ne_top h'`.

Conclude with `⟨m, rfl⟩`. Take `⟨φ, hφP, hφ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP0`. Take `⟨π, T, n, hdiv⟩` from `germ_division_after_coordinates hD hG hm w φ hφ0`. Establish `hdivP : ∀ ψ : holGerms w, ∃ a : Fin n → holGerms (π w), ψ - ∑ j : Fin n, germPull π (π.analyticAt w) rfl (a j) * affineGerm w T (-T w) ^ (j : ℕ) ∈ P`. Introduce `ψ`.

Take `⟨r, a, h⟩` from `hdiv ψ`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[h, add_sub_cancel_right]`. Conclude with `P.mul_mem_left r hφP`. Establish `hP' : (P.comap (germPull π (π.analyticAt w) rfl)).IsPrime` using `Ideal.IsPrime.comap _`.

Take `⟨d, B, hB⟩` from `IH (Fin m) (by simp [hm]) (π w) _ hP'`. Conclude with `⟨d, B.comp π, isFiniteGermProjection_comp w P π T (-T w) n hdivP B hB⟩`.
-/
theorem PrimeGermProjectionStep.proof (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) : PrimeGermProjectionStep.Statement := by
  classical
  intro σ _ w P hP hP0 IH
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card σ = m + 1 := by
    rcases h : Fintype.card σ with _ | m
    · exfalso
      let e : (Fin 0 → ℂ) ≃L[ℂ] (σ → ℂ) :=
        (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq h)).toContinuousLinearEquiv
      have hF : IsField (holGerms w) := (germAffineEquiv e w).toMulEquiv.isField isField_holGerms_fin_zero
      let _ := hF.toField
      rcases Ideal.eq_bot_or_top P with h' | h'
      · exact hP0 h'
      · exact hP.ne_top h'
    · exact ⟨m, rfl⟩
  obtain ⟨φ, hφP, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨π, T, n, hdiv⟩ := germ_division_after_coordinates hD hG hm w φ hφ0
  have hdivP : ∀ ψ : holGerms w, ∃ a : Fin n → holGerms (π w),
      ψ - ∑ j : Fin n, germPull π (π.analyticAt w) rfl (a j) * affineGerm w T (-T w) ^ (j : ℕ) ∈ P := by
    intro ψ
    obtain ⟨r, a, h⟩ := hdiv ψ
    refine ⟨a, ?_⟩
    rw [h, add_sub_cancel_right]
    exact P.mul_mem_left r hφP
  have hP' : (P.comap (germPull π (π.analyticAt w) rfl)).IsPrime := Ideal.IsPrime.comap _
  obtain ⟨d, B, hB⟩ := IH (Fin m) (by simp [hm]) (π w) _ hP'
  exact ⟨d, B.comp π, isFiniteGermProjection_comp w P π T (-T w) n hdivP B hB⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

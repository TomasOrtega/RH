import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameEqLocalFunctionUnitScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallAlgHom

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.IndepCx

/- English proof (translation)
Take `⟨N, j, _, hj⟩` from `hX.isProjOver`. Use `isProper_str k N` as an intermediate fact. Establish `: IsProper p` using `hj ▸ inferInstance`. Establish `h1 : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).FiniteType` using `(p.finiteType_appLE (isAffineOpen_top _) hU _).comp (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)`. Use `hX.finite` as an intermediate fact.

Establish `h0 : (algebraMap ℤ k).FiniteType` using `RingHom.finiteType_algebraMap.2 inferInstance`. Establish `h2` using `h1.comp h0`. Rewrite `h2` using `[RingHom.ext_int ((ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).comp (algebraMap ℤ k)) (algebraMap ℤ Γ(X, U))]`. Conclude with `RingHom.finiteType_algebraMap.1 h2`.
-/
theorem finiteType_int {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have h1 : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).FiniteType :=
    (p.finiteType_appLE (isAffineOpen_top _) hU _).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  have := hX.finite
  have h0 : (algebraMap ℤ k).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h2 := h1.comp h0
  rw [RingHom.ext_int ((ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).comp (algebraMap ℤ k)) (algebraMap ℤ Γ(X, U))] at h2
  exact RingHom.finiteType_algebraMap.1 h2

end GlobalTheory.HSAmp.IndepCx

namespace GlobalTheory.HSAmp

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in

/- English proof (translation)
Introduce `k _ X _ p D hX P a b ι _ f hf hli c hc`. Take `⟨i, hi⟩` from `exists_chart P.L.isLB (genericPoint X)`. Take `⟨j, hj⟩` from `exists_chart P.A.isLB (genericPoint X)`. Take `⟨U, hU, hgU, hle⟩` from `exists_isAffineOpen_mem_and_subset (x := genericPoint X) (U := P.L.B.U i ⊓ P.A.B.U j) ⟨hi, hj⟩`. Establish `hl : U ≤ P.L.B.U i` using `fun x hx => (hle hx).1`.

Establish `hr : U ≤ P.A.B.U j` using `fun x hx => (hle hx).2`. Establish `: Nonempty U` using `⟨⟨_, hgU⟩⟩`. Establish `: CharZero Γ(X, U)` using `((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero`. Use `IndepCx.finiteType_int hX hU` as an intermediate fact. Use `choose g hg using fun l => exists_fnOf_eq hgU fun x hx => hf l x i j (hl hx) (hr hx)`.

Establish `hu0 : (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b ≠ 0` using `mul_ne_zero (zpow_ne_zero _ (P.r i).ne_zero) (zpow_ne_zero _ (P.r' j).ne_zero)`. Establish `hloc : ∀ l, P.loc a b (f l) i j = f l * ((P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b)` using `fun l => by simp only [Pair.loc]; ring`. Establish `hgli : LinearIndependent ℤ g`. Rewrite `hli`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `n hn`.

Apply `hli n` to reduce the goal to its premises. Establish `h1` using `congrArg (fnOf U hgU) hn`. Rewrite `h1` using `[map_sum, map_zero]`. Simplify using `only [map_zsmul, hg, hloc] at h1`. Establish `h2 : (∑ l, n l • f l) * ((P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b) = 0`.

Rewrite using `[Finset.sum_mul]`. Simplify `h1` using `only [smul_mul_assoc]`. Conclude with `(mul_eq_zero.1 h2).resolve_right hu0`. Use `set e := Fintype.equivFin ι`. Take `⟨x, hx⟩` from `GlobalTheory.CxPointsSep.exists_det_ne_zero Γ(X, U) (Fintype.card ι) (g ∘ e.symm) (hgli.comp _ e.symm.injective)`.

Establish `key : ∀ s, ∑ l, c l * x s (g l) = 0`. Introduce `s`. Establish `hy : ofHom (σ` using `(x s).comp (algX p U)) hU (x s) (fun _ => rfl) ∈ ptsIn p ((x s).comp (algX p U)) U := ofHom_mem hU _ _`. Take `⟨θ, hθ, hval⟩` from `GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b _ _ i j (ptsIn_mono hl hy) (ptsIn_mono hr hy)`. Establish `h0` using `hc _ (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl))`.

Establish `hθ0 : θ ≠ 0`. Introduce `h`. Rewrite `hθ` using `[h, norm_zero]`. Conclude with `zero_ne_one hθ`. Use `set E : ℂ := ((Real.exp (-(a * (P.L.φ ((x s).comp (algX p U))).φ i (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl)) + b * (P.A.φ ((x s).comp (algX p U))).φ j (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl))) / 2) : ℝ) : ℂ) with hEdef`.

Establish `hE : E ≠ 0` using `Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'`. Establish `hv : ∀ l, val P a b _ (ofHom (σ` using `(x s).comp (algX p U)) hU (x s) (fun _ => rfl)) (f l) = θ * E * x s (g l) := by`. Introduce `l`. Rewrite using `[hval (f l) (hf l), ← hg l, ratVal_fnOf hy hgU, ev_ofHom]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hv] at h0`. Establish `h3 : θ * E * ∑ l, c l * x s (g l) = 0`. Rewrite using `[Finset.mul_sum, ← h0]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`. Conclude with `(mul_eq_zero.1 h3).resolve_left (mul_ne_zero hθ0 hE)`.

Establish `hM : Matrix.mulVec (Matrix.of fun s t => x s ((g ∘ e.symm) t)) (c ∘ e.symm) = 0`. Use function extensionality and compare the values at `s`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp_apply, Pi.zero_apply]`. Rewrite using `[← key s, ← e.symm.sum_comp (fun l => c l * x s (g l))]`. Conclude with `Finset.sum_congr rfl fun t _ => mul_comm _ _`.

Establish `hz` using `Matrix.eq_zero_of_mulVec_eq_zero hx hM`. Use function extensionality and compare the values at `l`. Simplify using `using congrFun hz (e l)`.
-/
theorem linearIndependent_vals : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (ι : Type) [Fintype ι] (f : ι → X.functionField),
    (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → ∀ c : ι → ℂ,
    (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∑ i, c i * val P a b σ y (f i) = 0) → c = 0 := by
  intro k _ X _ p D hX P a b ι _ f hf hli c hc
  classical
  obtain ⟨i, hi⟩ := exists_chart P.L.isLB (genericPoint X)
  obtain ⟨j, hj⟩ := exists_chart P.A.isLB (genericPoint X)
  obtain ⟨U, hU, hgU, hle⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X)
    (U := P.L.B.U i ⊓ P.A.B.U j) ⟨hi, hj⟩
  have hl : U ≤ P.L.B.U i := fun x hx => (hle hx).1
  have hr : U ≤ P.A.B.U j := fun x hx => (hle hx).2
  have : Nonempty U := ⟨⟨_, hgU⟩⟩
  have : CharZero Γ(X, U) :=
    ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero
  have := IndepCx.finiteType_int hX hU
  choose g hg using fun l => exists_fnOf_eq hgU fun x hx => hf l x i j (hl hx) (hr hx)
  have hu0 : (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (P.r i).ne_zero) (zpow_ne_zero _ (P.r' j).ne_zero)
  have hloc : ∀ l, P.loc a b (f l) i j = f l * ((P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b) :=
    fun l => by simp only [Pair.loc]; ring
  have hgli : LinearIndependent ℤ g := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro n hn
    apply hli n
    have h1 := congrArg (fnOf U hgU) hn
    rw [map_sum, map_zero] at h1
    simp only [map_zsmul, hg, hloc] at h1
    have h2 : (∑ l, n l • f l) * ((P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b) = 0 := by
      rw [Finset.sum_mul]; simpa only [smul_mul_assoc] using h1
    exact (mul_eq_zero.1 h2).resolve_right hu0
  set e := Fintype.equivFin ι
  obtain ⟨x, hx⟩ := GlobalTheory.CxPointsSep.exists_det_ne_zero Γ(X, U) (Fintype.card ι) (g ∘ e.symm)
    (hgli.comp _ e.symm.injective)
  have key : ∀ s, ∑ l, c l * x s (g l) = 0 := by
    intro s
    have hy : ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl) ∈ ptsIn p ((x s).comp (algX p U)) U :=
      ofHom_mem hU _ _
    obtain ⟨θ, hθ, hval⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b _ _ i j (ptsIn_mono hl hy) (ptsIn_mono hr hy)
    have h0 := hc _ (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl))
    have hθ0 : θ ≠ 0 := by
      intro h; rw [h, norm_zero] at hθ; exact zero_ne_one hθ
    set E : ℂ := ((Real.exp (-(a * (P.L.φ ((x s).comp (algX p U))).φ i
      (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl)) +
      b * (P.A.φ ((x s).comp (algX p U))).φ j (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl))) / 2) : ℝ) : ℂ)
      with hEdef
    have hE : E ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    have hv : ∀ l, val P a b _ (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl)) (f l) =
        θ * E * x s (g l) := by
      intro l
      rw [hval (f l) (hf l), ← hg l, ratVal_fnOf hy hgU, ev_ofHom]
      ring
    simp only [hv] at h0
    have h3 : θ * E * ∑ l, c l * x s (g l) = 0 := by
      rw [Finset.mul_sum, ← h0]
      exact Finset.sum_congr rfl fun l _ => by ring
    exact (mul_eq_zero.1 h3).resolve_left (mul_ne_zero hθ0 hE)
  have hM : Matrix.mulVec (Matrix.of fun s t => x s ((g ∘ e.symm) t)) (c ∘ e.symm) = 0 := by
    funext s
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp_apply, Pi.zero_apply]
    rw [← key s, ← e.symm.sum_comp (fun l => c l * x s (g l))]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hx hM
  funext l
  simpa using congrFun hz (e l)

end GlobalTheory.HSAmp

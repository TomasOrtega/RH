import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEmbeddingDualInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalFrame

section Comb

variable {Ω : Type} [Field Ω] {Vs : Type} [AddCommGroup Vs] [Module Ω Vs] {R' : Subring Ω} {g : ℕ}

/- English proof (translation)
Simplify using `[comb, add_smul, Finset.sum_add_distrib]`.
-/
theorem comb_add (ℓ : Fin g → Vs) (x y : Fin g → R') : comb ℓ (x + y) = comb ℓ x + comb ℓ y := by
  simp [comb, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[comb, Finset.smul_sum, mul_smul]`.
-/
theorem comb_smul (ℓ : Fin g → Vs) (r : R') (x : Fin g → R') : comb ℓ (r • x) = (r : Ω) • comb ℓ x := by
  simp [comb, Finset.smul_sum, mul_smul]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [comb]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, comb_add, comb_smul, ih]`.
-/
theorem comb_sum {J : Type} (ℓ : Fin g → Vs) (s : Finset J) (c : J → R') (x : J → Fin g → R') :
    comb ℓ (s.sum fun i : J => c i • x i) = Finset.sum s (fun i : J => (c i : Ω) • comb ℓ (x i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [comb]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, comb_add, comb_smul, ih]

/- English proof (translation)
Unfold `comb`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`.

Simplify using the standard rewrite rules.
-/
theorem comb_single (ℓ : Fin g → Vs) (k : Fin g) : comb ℓ (Pi.single k (1 : R')) = ℓ k := by
  unfold comb
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/- English proof (translation)
Establish `h0 : ∑ i, ((x i : Ω) - (y i : Ω)) • ℓ i = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Conclude with `sub_eq_zero.mpr h`. Use function extensionality and compare the values at `i`. Conclude with `Subtype.ext (sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hl _ h0 i))`.
-/
theorem comb_inj {ℓ : Fin g → Vs} (hl : LinearIndependent Ω ℓ) {x y : Fin g → R'}
    (h : comb ℓ x = comb ℓ y) : x = y := by
  have h0 : ∑ i, ((x i : Ω) - (y i : Ω)) • ℓ i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  funext i
  exact Subtype.ext (sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hl _ h0 i))

/- English proof (translation)
The claim follows from `Submodule.mem_span_range_iff_exists_fun R'`.
-/
theorem mem_span_iff {ℓ : Fin g → Vs} {v : Vs} :
    v ∈ Submodule.span R' (Set.range ℓ) ↔ ∃ x : Fin g → R', comb ℓ x = v :=
  Submodule.mem_span_range_iff_exists_fun R'

end Comb

section Comparison₂

variable {E : Type} [Field E] [NumberField E] {Ω : Type} [Field Ω] {Vs : Type} [AddCommGroup Vs] [Module Ω Vs]
  {C : Type} [Field C] {R' : Subring Ω} {g : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, map_sum]`.
-/
theorem psi_sum {J : Type} (ψ : R' →+* C) (s : Finset J) (c : J → R') (x : J → Fin g → R') :
    (fun k => ψ ((s.sum fun i : J => c i • x i) k)) = Finset.sum s (fun i : J => ψ (c i) • fun k => ψ (x i k)) := by
  funext k
  simp [Finset.sum_apply, map_sum]

/- English proof (translation)
Unfold `comb`. Rewrite using `[map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ (x i) (hst a i)`.
-/
theorem rho_comb_mem {ρ : 𝓞 E →+* Module.End Ω Vs} {ℓ : Fin g → Vs}
    (hst : ∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) (a : 𝓞 E) (x : Fin g → R') :
    ρ a (comb ℓ x) ∈ Submodule.span R' (Set.range ℓ) := by
  unfold comb
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ (x i) (hst a i)

/- English proof (translation)
Unfold `HT.eigProj`. Rewrite using `[LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ (⟨_, hσ (HT.dualInt E k)⟩ : R') (rho_comb_mem hst _ x)`.
-/
theorem eigProj_comb_mem {ρ : 𝓞 E →+* Module.End Ω Vs} {σ : E →+* Ω} {ℓ : Fin g → Vs}
    (hst : ∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) (hσ : ∀ e : E, σ e ∈ R') (x : Fin g → R') :
    HT.eigProj ρ σ (comb ℓ x) ∈ Submodule.span R' (Set.range ℓ) := by
  unfold HT.eigProj
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  exact Submodule.smul_mem _ (⟨_, hσ (HT.dualInt E k)⟩ : R') (rho_comb_mem hst _ x)

/- English proof (translation)
Establish `h1 : ∀ k, ∃ x' : Fin g → R', comb ℓ x' = ρ (RingOfIntegers.basis E k) (comb ℓ x)` using `fun k => mem_span_iff.mp (rho_comb_mem hst _ x)`. Use `choose x' hx' using h1`. Establish `hy : y = ∑ k, (⟨σ (HT.dualInt E k), (hσ _).choose⟩ : R') • x' k`. Apply `comb_inj hl` to reduce the goal to its premises. Rewrite using `[← h, comb_sum]`.

Unfold `HT.eigProj`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hx']`. Both sides reduce to the same expression.

Establish `ht'` using `fun k => ht (RingOfIntegers.basis E k) x (x' k) (hx' k).symm`. Rewrite using `[hy, psi_sum]`. Unfold `HT.eigProj`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[(hσ (HT.dualInt E k)).choose_spec, ← ht' k]`. Both sides reduce to the same expression.
-/
theorem tied_eigProj {ρ : 𝓞 E →+* Module.End Ω Vs} {ρC : 𝓞 E →+* Module.End C (Fin g → C)} {σ : E →+* Ω}
    {σC : E →+* C} {ℓ : Fin g → Vs} {ψ : R' →+* C} (hl : LinearIndependent Ω ℓ)
    (hst : ∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) (ht : Tied ℓ ψ ρ ρC)
    (hσ : ∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) {x y : Fin g → R'}
    (h : HT.eigProj ρ σ (comb ℓ x) = comb ℓ y) :
    HT.eigProj ρC σC (fun i => ψ (x i)) = fun i => ψ (y i) := by
  have h1 : ∀ k, ∃ x' : Fin g → R', comb ℓ x' = ρ (RingOfIntegers.basis E k) (comb ℓ x) :=
    fun k => mem_span_iff.mp (rho_comb_mem hst _ x)
  choose x' hx' using h1
  have hy : y = ∑ k, (⟨σ (HT.dualInt E k), (hσ _).choose⟩ : R') • x' k := by
    apply comb_inj hl
    rw [← h, comb_sum]
    unfold HT.eigProj
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hx']
    rfl
  have ht' := fun k => ht (RingOfIntegers.basis E k) x (x' k) (hx' k).symm
  rw [hy, psi_sum]
  unfold HT.eigProj
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(hσ (HT.dualInt E k)).choose_spec, ← ht' k]
  rfl

end Comparison₂

/- English proof (translation)
Introduce `E _ _ Ω Vs C _ _ _ _ _ _ _ ρ R' g n ℓ ψ ρC σ σC b x hl hsp hst ht hσ hb _ hbs hn`. Establish `hσ' : ∀ e : E, σ e ∈ R'` using `fun e => (hσ e).choose`. Establish `hproj : ∀ k, ∃ c : Fin n → R', HT.eigProj ρ σ (ℓ k) = comb ℓ (∑ i, c i • x i)`. Introduce `k`. Establish `hm : HT.eigProj ρ σ (ℓ k) ∈ HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ))`.

Use `⟨?_, HT.LatBasic.eigProj_mem ρ σ _⟩` and prove the remaining obligations. Use `eigProj_comb_mem (ρ := ρ) (σ := σ) hst hσ' (Pi.single k (1 : R'))` as an intermediate fact. Rewrite `this` using `[comb_single]`. Then use the resulting hypothesis. Rewrite `hm` using `[← hbs]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun R').mp hm`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[comb_sum, ← hc]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hb i]`. Both sides reduce to the same expression.

Use `choose c hc using hproj`. Establish `hC : ∀ k, HT.eigProj ρC σC (Pi.single k 1) = ∑ i, ψ (c k i) • fun j => ψ (x i j)`. Introduce `k`. Establish `h1 : HT.eigProj ρ σ (comb ℓ (Pi.single k (1 : R'))) = comb ℓ (∑ i, c k i • x i)`. Rewrite using `[comb_single, hc]`.

Establish `h2` using `tied_eigProj hl hst ht hσ h1`. Establish `h3 : (fun i => ψ ((Pi.single k (1 : R') : Fin g → R') i)) = Pi.single k (1 : C)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = k`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`. Rewrite `h2` using `[h3, psi_sum]`. Conclude with `h2`. Establish `hmem : ∀ i, (fun k => ψ (x i k)) ∈ HT.eigSp ρC σC`.

Introduce `i`. Establish `hbi : b i ∈ HT.eigSp ρ σ`. Establish `: b i ∈ HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ))`. Rewrite using `[← hbs]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.

Conclude with `this.2`. Unfold `HT.eigSp at hbi ⊢`. Rewrite `hbi`, the goal using `[Submodule.mem_iInf]`. Introduce `a`. Establish `ha` using `hbi a`.

Rewrite `ha` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Establish `h1 : ρ a (comb ℓ (x i)) = comb ℓ ((⟨σ (a : E), hσ' _⟩ : R') • x i)`. Rewrite using `[comb_smul, ← hb i, ha]`. Both sides reduce to the same expression.

Rewrite using `[ht a (x i) _ h1]`. Use function extensionality and compare the values at `j`. Establish `h2 : ψ ⟨σ (a : E), hσ' _⟩ = σC (a : E)` using `(hσ (a : E)).choose_spec`. Simplify using `[h2]`. Establish `hspan : Submodule.span C (Set.range fun i k => ψ (x i k)) = HT.eigSp ρC σC`.

Use `le_antisymm (Submodule.span_le.mpr ?_) fun v hv => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hmem i`. Rewrite using `[← HT.LatBasic.eigProj_of_mem hv]`. Establish `hv' : v = ∑ k, v k • (Pi.single k (1 : C) : Fin g → C)`.

Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hv', map_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hC]`.

Use `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `B : Module.Basis (Fin g) Ω Vs` to `Module.Basis.mk hl hsp.ge`. Establish `hB : ∀ k, B k = ℓ k` using `fun k => Module.Basis.mk_apply hl hsp.ge k`. Establish `hrepr : ∀ (y : Fin g → R') (j : Fin g), B.repr (comb ℓ y) j = (y j : Ω)`.

Introduce `y j`. Establish `: comb ℓ y = ∑ i, (y i : Ω) • B i`. Unfold `comb`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hB]`. Rewrite using `[this, map_sum, Finsupp.finset_sum_apply]`.

Simplify using `[Finsupp.single_apply]`. Establish `htrΩ : (∑ k, ((∑ i, c k i • x i) k : R') : R') = (n : R')`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `HT.EigDim.trace_eigProj ρ σ`. Rewrite `h1` using `[LinearMap.trace_eq_matrix_trace Ω B, Matrix.trace, hn]`.

Use `push_cast`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, LinearMap.toMatrix_apply, hB, hc, hrepr]`. Establish `htrC : (Module.finrank C (HT.eigSp ρC σC) : C) = (n : C)`.

Establish `h1` using `HT.EigDim.trace_eigProj ρC σC`. Rewrite `h1` using `[LinearMap.trace_eq_matrix_trace C (Pi.basisFun C (Fin g)), Matrix.trace]`. Rewrite using `[← h1, ← map_natCast ψ n, ← htrΩ, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, hC]`.

Simplify using `[Finset.sum_apply, map_sum]`. Establish `hfr : Module.finrank C (HT.eigSp ρC σC) = n` using `by exact_mod_cast htrC`. Use `⟨?_, hspan⟩` and prove the remaining obligations. Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan, hfr, Fintype.card_fin]`.
-/
theorem values_basis : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] [Field C] [CharZero C] (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g n : ℕ)
    (ℓ : Fin g → Vs) (ψ : R' →+* C) (ρC : 𝓞 E →+* Module.End C (Fin g → C)) (σ : E →+* Ω) (σC : E →+* C)
    (b : Fin n → Vs) (x : Fin n → Fin g → R'),
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρC →
    (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) →
    (∀ i, b i = comb ℓ (x i)) → LinearIndependent Ω b →
    Submodule.span R' (Set.range b) = HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ)) →
    Module.finrank Ω (HT.eigSp ρ σ) = n →
    LinearIndependent C (fun i k => ψ (x i k)) ∧
      Submodule.span C (Set.range fun i k => ψ (x i k)) = HT.eigSp ρC σC := by
  intro E _ _ Ω Vs C _ _ _ _ _ _ _ ρ R' g n ℓ ψ ρC σ σC b x hl hsp hst ht hσ hb _ hbs hn
  have hσ' : ∀ e : E, σ e ∈ R' := fun e => (hσ e).choose

  have hproj : ∀ k, ∃ c : Fin n → R', HT.eigProj ρ σ (ℓ k) = comb ℓ (∑ i, c i • x i) := by
    intro k
    have hm : HT.eigProj ρ σ (ℓ k) ∈ HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ)) := by
      refine ⟨?_, HT.LatBasic.eigProj_mem ρ σ _⟩
      have := eigProj_comb_mem (ρ := ρ) (σ := σ) hst hσ' (Pi.single k (1 : R'))
      rwa [comb_single] at this
    rw [← hbs] at hm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R').mp hm
    refine ⟨c, ?_⟩
    rw [comb_sum, ← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hb i]
    rfl
  choose c hc using hproj

  have hC : ∀ k, HT.eigProj ρC σC (Pi.single k 1) = ∑ i, ψ (c k i) • fun j => ψ (x i j) := by
    intro k
    have h1 : HT.eigProj ρ σ (comb ℓ (Pi.single k (1 : R'))) = comb ℓ (∑ i, c k i • x i) := by
      rw [comb_single, hc]
    have h2 := tied_eigProj hl hst ht hσ h1
    have h3 : (fun i => ψ ((Pi.single k (1 : R') : Fin g → R') i)) = Pi.single k (1 : C) := by
      funext i
      by_cases h : i = k
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [h3, psi_sum] at h2
    exact h2

  have hmem : ∀ i, (fun k => ψ (x i k)) ∈ HT.eigSp ρC σC := by
    intro i
    have hbi : b i ∈ HT.eigSp ρ σ := by
      have : b i ∈ HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ)) := by
        rw [← hbs]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact this.2
    unfold HT.eigSp at hbi ⊢
    rw [Submodule.mem_iInf] at hbi ⊢
    intro a
    have ha := hbi a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at ha
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    have h1 : ρ a (comb ℓ (x i)) = comb ℓ ((⟨σ (a : E), hσ' _⟩ : R') • x i) := by
      rw [comb_smul, ← hb i, ha]
      rfl
    rw [ht a (x i) _ h1]
    funext j
    have h2 : ψ ⟨σ (a : E), hσ' _⟩ = σC (a : E) := (hσ (a : E)).choose_spec
    simp [h2]
  have hspan : Submodule.span C (Set.range fun i k => ψ (x i k)) = HT.eigSp ρC σC := by
    refine le_antisymm (Submodule.span_le.mpr ?_) fun v hv => ?_
    · rintro _ ⟨i, rfl⟩
      exact hmem i
    · rw [← HT.LatBasic.eigProj_of_mem hv]
      have hv' : v = ∑ k, v k • (Pi.single k (1 : C) : Fin g → C) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hv', map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [map_smul, hC]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  let B : Module.Basis (Fin g) Ω Vs := Module.Basis.mk hl hsp.ge
  have hB : ∀ k, B k = ℓ k := fun k => Module.Basis.mk_apply hl hsp.ge k
  have hrepr : ∀ (y : Fin g → R') (j : Fin g), B.repr (comb ℓ y) j = (y j : Ω) := by
    intro y j
    have : comb ℓ y = ∑ i, (y i : Ω) • B i := by
      unfold comb
      exact Finset.sum_congr rfl fun i _ => by rw [hB]
    rw [this, map_sum, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply]
  have htrΩ : (∑ k, ((∑ i, c k i • x i) k : R') : R') = (n : R') := by
    apply Subtype.ext
    have h1 := HT.EigDim.trace_eigProj ρ σ
    rw [LinearMap.trace_eq_matrix_trace Ω B, Matrix.trace, hn] at h1
    push_cast
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hB, hc, hrepr]
  have htrC : (Module.finrank C (HT.eigSp ρC σC) : C) = (n : C) := by
    have h1 := HT.EigDim.trace_eigProj ρC σC
    rw [LinearMap.trace_eq_matrix_trace C (Pi.basisFun C (Fin g)), Matrix.trace] at h1
    rw [← h1, ← map_natCast ψ n, ← htrΩ, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, hC]
    simp [Finset.sum_apply, map_sum]
  have hfr : Module.finrank C (HT.eigSp ρC σC) = n := by exact_mod_cast htrC
  refine ⟨?_, hspan⟩
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan, hfr, Fintype.card_fin]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalFrame

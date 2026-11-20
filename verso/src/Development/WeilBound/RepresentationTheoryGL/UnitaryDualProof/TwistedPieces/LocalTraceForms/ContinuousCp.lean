import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.LocChi
import GroundTheory.AutomorphicForms.WhittakerDistribution
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocalContinuity.LocalDescentHolds
import GroundTheory.AutomorphicForms.ContragredientTranspose.MatrixSimilarity

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Loc.Psplit

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def cp (x : Matrix (Fin n) (Fin n) k) : Fin (n + 1) → k := fun i => x.charpoly.coeff i

/- English proof (translation)
The claim follows from `continuous_pi fun i => GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff_of_fintype (i : ℕ)`.
-/
theorem continuous_cp : Continuous (cp : Matrix (Fin n) (Fin n) k → _) :=
  continuous_pi fun i => GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff_of_fintype (i : ℕ)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [cp]`. Rewrite using `[charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]`.
-/
theorem cp_conj (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) : cp (g.val * x * g⁻¹.val) = cp x := by
  funext i
  simp only [cp]
  rw [charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

def poly (y : Fin (n + 1) → k) : k[X] := ∑ i : Fin (n + 1), C (y i) * X ^ (i : ℕ)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Establish `h` using `as_sum_range' x.charpoly (n + 1) (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)`. Rewrite using `[h, poly, ← Fin.sum_univ_eq_sum_range (fun i => (monomial i) (x.charpoly.coeff i)) (n + 1)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← C_mul_X_pow_eq_monomial]`. Both sides reduce to the same expression. Introduce `h`. Use function extensionality and compare the values at `i`. Simplify using `only [cp, h, poly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]`.

Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (fun e => hj (Fin.ext e.symm)), mul_zero]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem cp_eq_iff (x : Matrix (Fin n) (Fin n) k) (y : Fin (n + 1) → k) : cp x = y ↔ x.charpoly = poly y := by
  constructor
  · rintro rfl
    have h := as_sum_range' x.charpoly (n + 1) (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)
    rw [h, poly, ← Fin.sum_univ_eq_sum_range (fun i => (monomial i) (x.charpoly.coeff i)) (n + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← C_mul_X_pow_eq_monomial]
    rfl
  · intro h
    funext i
    simp only [cp, h, poly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (fun e => hj (Fin.ext e.symm)), mul_zero]) (by simp)]
    simp

/- English proof (translation)
Introduce `n Z U hU hfib ξ hS hI`. Establish `: TotallyDisconnectedSpace k` using `totallyDisconnectedSpace_localField`. Set `p : Sp k n → _` to `fun q => cp q.1`. Establish `hp : Continuous p` using `continuous_cp.comp continuous_fst`. Establish `hpact : ∀ g ∈ Gz Z, ∀ q, p (act g q) = p q` using `fun g _ q => cp_conj g q.1`.

Set `C : Set (Sp k n)` to `Bz Z ×ˢ univ`. Establish `hC : IsClosed C` using `(PositivityTheory.RgUd.T.LocStepPf.isClosed_Bz Z).prod isClosed_univ`. Set `W : Submodule ℂ (Sp k n → ℂ)` to `{ carrier := {w | ∀ V, IsClopen V → ξ (fun x => (p ⁻¹' V).indicator 1 x * w x) = 0} add_mem' := fun {a b} ha hb V hV => by`. Establish `e : (fun x => (p ⁻¹' V).indicator 1 x * (a + b) x) = (fun x => (p ⁻¹' V).indicator 1 x * a x) + (fun x => (p ⁻¹' V).indicator 1 x * b x)`. Use function extensionality and compare the values at `x`.

Simplify using `[mul_add]`. Rewrite using `[e, map_add, ha V hV, hb V hV, add_zero]`. Use the proof step `zero_mem' := fun V _ => by`. Establish `e : (fun x => (p ⁻¹' V).indicator 1 x * (0 : Sp k n → ℂ) x) = 0`. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules. Rewrite using `[e, map_zero]`. Use the proof step `smul_mem' := fun c a ha V hV => by`. Establish `e : (fun x => (p ⁻¹' V).indicator 1 x * (c • a) x) = c • (fun x => (p ⁻¹' V).indicator 1 x * a x)`. Use function extensionality and compare the values at `x`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_smul, ha V hV, smul_zero] }`. Introduce `g hg`. Establish `key : g ∈ W`.

Use `mem_of_forall_fiber (U := univ) hC hp ?_ ?_ (supportedIn_mono (subset_univ _) hg) ?_` and prove the remaining obligations. Introduce and unpack `w ⟨hw1, hw2⟩ V hV`. Use `hS _ (indicator_mul_mem (hV.preimage hp) hw1) fun q hq => ?_` and prove the remaining obligations. Simplify using `[(mem_vanishingOn.1 hw2) q hq]`. Introduce `V hV w hw V' hV'`.

Use `hw (V' ∩ V) (hV'.inter hV)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Apply the tactic sequence `by_cases h1 : p x ∈ V' <;> by_cases h2 : p x ∈ V <;>`. Simplify using `[h1, h2]`.

Introduce `y`. Set `N : Submodule ℂ (Sp k n → ℂ)` to `Submodule.span ℂ {h | ∃ γ ∈ Gz Z, ∃ f ∈ supportedIn (univ : Set (Sp k n)), h = (fun q => f (act γ q)) - f}`. Establish `hmem : g ∈ N ⊔ (supportedIn univ ⊓ vanishingOn (C ∩ p ⁻¹' {y}))`. Assume the negation of the conclusion as `hn`. Take `⟨f, hf0, hle⟩` from `Submodule.exists_le_ker_of_notMem hn`.

Use `hf0 (hfib (poly y) f ?_ ?_ g hg)` and prove the remaining obligations. Introduce `u hu hu0`. Use `hle (Submodule.mem_sup_right ⟨hu, fun q hq => hu0 q ⟨⟨hq.1.1, ?_⟩, trivial⟩⟩)` and prove the remaining obligations. Conclude with `(cp_eq_iff q.1 y).1 hq.2`. Introduce `γ hγ u hu`.

Establish `h1 : (fun q => u (act γ q)) - u ∈ N` using `Submodule.subset_span ⟨γ, hγ, u, hu, rfl⟩`. Establish `h3` using `hle (Submodule.mem_sup_left h1)`. Rewrite `h3` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Conclude with `h3`. Establish `hNW : N ≤ W`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨γ, hγ, u, hu, rfl⟩ V hV`. Establish `hu'` using `indicator_mul_mem (hV.preimage hp) hu`. Establish `h3` using `hI γ hγ _ hu'`. Rewrite `h3` using `[← sub_eq_zero, ← map_sub]`.

Use `h3 using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `q`. Establish `e : p (act γ q) = p q` using `hpact γ hγ q`. Apply the tactic sequence `by_cases h1 : p q ∈ V <;> simp [h1, e]`. Conclude with `sup_le_sup_right hNW _ hmem`.

Use `key univ isClopen_univ` as an intermediate fact. Simplify using `using this`.
-/
theorem locChi_pf : PositivityTheory.RgUd.TP.Loc.LocChi k := by
  intro n Z U hU hfib ξ hS hI
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  let p : Sp k n → _ := fun q => cp q.1
  have hp : Continuous p := continuous_cp.comp continuous_fst
  have hpact : ∀ g ∈ Gz Z, ∀ q, p (act g q) = p q := fun g _ q => cp_conj g q.1
  let C : Set (Sp k n) := Bz Z ×ˢ univ
  have hC : IsClosed C := (PositivityTheory.RgUd.T.LocStepPf.isClosed_Bz Z).prod isClosed_univ
  let W : Submodule ℂ (Sp k n → ℂ) :=
    { carrier := {w | ∀ V, IsClopen V → ξ (fun x => (p ⁻¹' V).indicator 1 x * w x) = 0}
      add_mem' := fun {a b} ha hb V hV => by
        have e : (fun x => (p ⁻¹' V).indicator 1 x * (a + b) x) =
            (fun x => (p ⁻¹' V).indicator 1 x * a x) + (fun x => (p ⁻¹' V).indicator 1 x * b x) := by
          funext x
          simp [mul_add]
        rw [e, map_add, ha V hV, hb V hV, add_zero]
      zero_mem' := fun V _ => by
        have e : (fun x => (p ⁻¹' V).indicator 1 x * (0 : Sp k n → ℂ) x) = 0 := by
          funext x
          simp
        rw [e, map_zero]
      smul_mem' := fun c a ha V hV => by
        have e : (fun x => (p ⁻¹' V).indicator 1 x * (c • a) x) =
            c • (fun x => (p ⁻¹' V).indicator 1 x * a x) := by
          funext x
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [e, map_smul, ha V hV, smul_zero] }
  intro g hg
  have key : g ∈ W := by
    refine mem_of_forall_fiber (U := univ) hC hp ?_ ?_ (supportedIn_mono (subset_univ _) hg) ?_
    · rintro w ⟨hw1, hw2⟩ V hV
      refine hS _ (indicator_mul_mem (hV.preimage hp) hw1) fun q hq => ?_
      simp [(mem_vanishingOn.1 hw2) q hq]
    · intro V hV w hw V' hV'
      have := hw (V' ∩ V) (hV'.inter hV)
      convert this using 2
      funext x
      by_cases h1 : p x ∈ V' <;> by_cases h2 : p x ∈ V <;>
        simp [h1, h2]
    · intro y
      let N : Submodule ℂ (Sp k n → ℂ) := Submodule.span ℂ
        {h | ∃ γ ∈ Gz Z, ∃ f ∈ supportedIn (univ : Set (Sp k n)), h = (fun q => f (act γ q)) - f}
      have hmem : g ∈ N ⊔ (supportedIn univ ⊓ vanishingOn (C ∩ p ⁻¹' {y})) := by
        by_contra hn
        obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_notMem hn
        refine hf0 (hfib (poly y) f ?_ ?_ g hg)
        · intro u hu hu0
          refine hle (Submodule.mem_sup_right ⟨hu, fun q hq => hu0 q ⟨⟨hq.1.1, ?_⟩, trivial⟩⟩)
          exact (cp_eq_iff q.1 y).1 hq.2
        · intro γ hγ u hu
          have h1 : (fun q => u (act γ q)) - u ∈ N := Submodule.subset_span ⟨γ, hγ, u, hu, rfl⟩
          have h3 := hle (Submodule.mem_sup_left h1)
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h3
          exact h3
      have hNW : N ≤ W := by
        rw [Submodule.span_le]
        rintro _ ⟨γ, hγ, u, hu, rfl⟩ V hV
        have hu' := indicator_mul_mem (hV.preimage hp) hu
        have h3 := hI γ hγ _ hu'
        rw [← sub_eq_zero, ← map_sub] at h3
        convert h3 using 2
        funext q
        have e : p (act γ q) = p q := hpact γ hγ q
        by_cases h1 : p q ∈ V <;> simp [h1, e]
      exact sup_le_sup_right hNW _ hmem
  have := key univ isClopen_univ
  simpa using this

end PositivityTheory.RgUd.TP.Loc.Psplit

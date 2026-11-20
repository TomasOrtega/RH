import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.UniSol

/- English proof (translation)
Establish `key : ∀ (n : ℕ) (B : Submodule ℂ A), Module.finrank ℂ B = n → ∃ S : Finset K, ∀ c ∈ B, (∀ κ ∈ S, (c : K → ℂ) κ = 0) → c = 0`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `B hB`.

Distinguish the cases in `hbot : B = ⊥`. Use `⟨∅, fun c hc _ => ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[hbot]`. Conclude with `(Submodule.mem_bot ℂ).mp hc`. Take `⟨c0, hc0B, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hbot`.

Choose the witnesses or unpack the hypotheses as in `⟨κ0, hκ0⟩ : ∃ κ0, (c0 : K → ℂ) κ0 ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hc0 (Subtype.ext (funext hcon))`. Set `ev : A →ₗ[ℂ] ℂ` to `(LinearMap.proj κ0).comp A.subtype`.

Set `B' : Submodule ℂ A` to `B ⊓ LinearMap.ker ev`. Establish `hlt : B' < B`. Use `lt_of_le_of_ne inf_le_left (fun h => hκ0 ?_)` and prove the remaining obligations. Establish `hmem : c0 ∈ B'`. Rewrite using `[h]`.

Conclude with `hc0B`. Conclude with `LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2`. Establish `hrk : Module.finrank ℂ B' < n`. Use `Submodule.finrank_lt_finrank_of_lt hlt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨S', hS'⟩` from `ih _ hrk B' rfl`. Use `⟨insert κ0 S', fun c hc hvan => hS' c ?_ (fun κ hκ => hvan κ (Finset.mem_insert_of_mem hκ))⟩` and prove the remaining obligations. Use `Submodule.mem_inf.mpr ⟨hc, LinearMap.mem_ker.mpr ?_⟩` and prove the remaining obligations. Conclude with `hvan κ0 (Finset.mem_insert_self κ0 S')`. Take `⟨S, hS⟩` from `key _ ⊤ rfl`.

Use `⟨S, fun c hc hvan => ?_⟩` and prove the remaining obligations. Establish `h0` using `hS ⟨c, hc⟩ Submodule.mem_top hvan`. Conclude with `congrArg Subtype.val h0`.
-/
theorem exists_finset_separating {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ S : Finset K, ∀ c ∈ A, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  classical
  have key : ∀ (n : ℕ) (B : Submodule ℂ A), Module.finrank ℂ B = n →
      ∃ S : Finset K, ∀ c ∈ B, (∀ κ ∈ S, (c : K → ℂ) κ = 0) → c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro B hB
      by_cases hbot : B = ⊥
      · refine ⟨∅, fun c hc _ => ?_⟩
        rw [hbot] at hc
        exact (Submodule.mem_bot ℂ).mp hc
      · obtain ⟨c0, hc0B, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
        obtain ⟨κ0, hκ0⟩ : ∃ κ0, (c0 : K → ℂ) κ0 ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hc0 (Subtype.ext (funext hcon))
        let ev : A →ₗ[ℂ] ℂ := (LinearMap.proj κ0).comp A.subtype
        let B' : Submodule ℂ A := B ⊓ LinearMap.ker ev
        have hlt : B' < B := by
          refine lt_of_le_of_ne inf_le_left (fun h => hκ0 ?_)
          have hmem : c0 ∈ B' := by
            rw [h]
            exact hc0B
          exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2
        have hrk : Module.finrank ℂ B' < n := by
          have := Submodule.finrank_lt_finrank_of_lt hlt
          omega
        obtain ⟨S', hS'⟩ := ih _ hrk B' rfl
        refine ⟨insert κ0 S', fun c hc hvan => hS' c ?_ (fun κ hκ => hvan κ (Finset.mem_insert_of_mem hκ))⟩
        refine Submodule.mem_inf.mpr ⟨hc, LinearMap.mem_ker.mpr ?_⟩
        exact hvan κ0 (Finset.mem_insert_self κ0 S')
  obtain ⟨S, hS⟩ := key _ ⊤ rfl
  refine ⟨S, fun c hc hvan => ?_⟩
  have h0 := hS ⟨c, hc⟩ Submodule.mem_top hvan
  exact congrArg Subtype.val h0

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℂ W`. Set `m : (Module.Free.ChooseBasisIndex ℂ W) × (Module.Free.ChooseBasisIndex ℂ W) → (K → ℂ)` to `fun ij k => b.repr (ρ k (b ij.2)) ij.1`. Use `haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range m)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range m)`. Establish `hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ Submodule.span ℂ (Set.range m)`. Unfold `GlobalTheory.Published.AutFin.coeffSpan`.

Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `f ⟨ℓ, w, rfl⟩`. Establish `hw : ∀ v : W, ℓ v = ∑ i, b.repr v i * ℓ (b i)`. Introduce `v`. Use `conv_lhs => rw [← b.sum_repr v]`.

Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Establish `hf : (fun k => ℓ ((ρ k) w)) = ∑ ij, (b.repr w ij.2 * ℓ (b ij.1)) • m ij`. Use function extensionality and compare the values at `k`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, m]`.

Rewrite using `[Fintype.sum_prod_type]`. Simplify using `only`. Establish `h1 : ℓ (ρ k w) = ∑ j, b.repr w j * ℓ (ρ k (b j))` using `by conv_lhs => rw [← b.sum_repr w]`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Rewrite using `[h1, Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[hw (ρ k (b j)), Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hf]`.

Conclude with `Submodule.sum_mem _ (fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩))`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let m : (Module.Free.ChooseBasisIndex ℂ W) × (Module.Free.ChooseBasisIndex ℂ W) → (K → ℂ) :=
    fun ij k => b.repr (ρ k (b ij.2)) ij.1
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range m)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range m)
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ Submodule.span ℂ (Set.range m) := by
    unfold GlobalTheory.Published.AutFin.coeffSpan
    refine Submodule.span_le.mpr ?_
    rintro f ⟨ℓ, w, rfl⟩
    have hw : ∀ v : W, ℓ v = ∑ i, b.repr v i * ℓ (b i) := by
      intro v
      conv_lhs => rw [← b.sum_repr v]
      simp only [map_sum, map_smul, smul_eq_mul]
    have hf : (fun k => ℓ ((ρ k) w)) = ∑ ij, (b.repr w ij.2 * ℓ (b ij.1)) • m ij := by
      funext k
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, m]
      rw [Fintype.sum_prod_type]
      dsimp only
      have h1 : ℓ (ρ k w) = ∑ j, b.repr w j * ℓ (ρ k (b j)) := by
        conv_lhs => rw [← b.sum_repr w]
        simp only [map_sum, map_smul, smul_eq_mul]
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hw (ρ k (b j)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hf]
    exact Submodule.sum_mem _ (fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle

/- English proof (translation)
Introduce `K W _ _ _ _ ρ`. Use `haveI := finiteDimensional_coeffSpan ρ`. Conclude with `exists_finset_separating _`.
-/
theorem coeffSpan_unisolvent : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W), ∃ S : Finset K, ∀ c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  intro K W _ _ _ _ ρ
  haveI := finiteDimensional_coeffSpan ρ
  exact exists_finset_separating _

end GlobalTheory.CompanionTheory.CTFin.UniSol

end

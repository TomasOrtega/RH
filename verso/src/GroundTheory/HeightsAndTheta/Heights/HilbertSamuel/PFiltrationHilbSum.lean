import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFiltrationHilbSum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiltrationStepHilb
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGradedPieceQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u v

namespace FiltrationHilbSum

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction generalizing m y with`. Consider the case `zero`. Establish `h0 : (fun k => ((Finsupp.weight (blockWeight ι) (0 : (Σ k, ι k) →₀ ℕ)) k : ℤ)) = 0`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Rewrite using `[h0, add_zero, ← C_apply, ← algebraMap_eq, algebraMap_smul]`. Conclude with `(piece m).smul_mem a hy`. Consider the case `single_add v k d' _ _ ih`. Establish `hpow : ∀ (e : ℕ) (m' : K → ℤ) (z : M), z ∈ piece m' → (X v ^ e : MRing ι F) • z ∈ piece (m' + e • unitDeg v.1)`. Introduce `e`.

Proceed by induction on `e with`. Consider the case `zero => intro m' z hz`. Simplify using `using hz`. Consider the case `succ e ihe`. Introduce `m' z hz`.

Rewrite using `[pow_succ', mul_smul, succ_nsmul, ← add_assoc]`. Conclude with `hM.smul_mem v _ _ (ihe m' z hz)`. Rewrite using `[monomial_single_add, mul_smul]`. Establish `h2` using `hpow k _ _ (ih hy)`. Use `h2 using 2` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k'`. Simplify using `only [map_add, Finsupp.weight_single, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_mul, blockWeight, unitDeg, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
theorem monomial_smul_mem (hM : IsMultigrading ι M piece) (d : (Σ k, ι k) →₀ ℕ) (a : F)
    {m : K → ℤ} {y : M} (hy : y ∈ piece m) :
    (monomial d a : MRing ι F) • y ∈
      piece (m + fun k => (Finsupp.weight (blockWeight ι) d k : ℤ)) := by
  induction d using Finsupp.induction generalizing m y with
  | zero =>
    have h0 : (fun k => ((Finsupp.weight (blockWeight ι) (0 : (Σ k, ι k) →₀ ℕ)) k : ℤ)) = 0 := by
      funext k
      simp
    rw [h0, add_zero, ← C_apply, ← algebraMap_eq, algebraMap_smul]
    exact (piece m).smul_mem a hy
  | single_add v k d' _ _ ih =>
    have hpow : ∀ (e : ℕ) (m' : K → ℤ) (z : M), z ∈ piece m' →
        (X v ^ e : MRing ι F) • z ∈ piece (m' + e • unitDeg v.1) := by
      intro e
      induction e with
      | zero => intro m' z hz; simpa using hz
      | succ e ihe =>
        intro m' z hz
        rw [pow_succ', mul_smul, succ_nsmul, ← add_assoc]
        exact hM.smul_mem v _ _ (ihe m' z hz)
    rw [monomial_single_add, mul_smul]
    have h2 := hpow k _ _ (ih hy)
    convert h2 using 2
    funext k'
    simp only [map_add, Finsupp.weight_single, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Nat.cast_add, Nat.cast_mul, blockWeight, unitDeg, Pi.single_apply]
    split_ifs <;> push_cast <;> ring

/- English proof (translation)
Rewrite using `[f.as_sum, Finset.sum_smul]`. Use `Submodule.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Establish `hw : Finsupp.weight (blockWeight ι) d = b` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mp hf (mem_support_iff.mp hd)`. Establish `h` using `monomial_smul_mem hM d (coeff d f) hy`. Rewrite `h` using `[hw]`. Then use the resulting hypothesis.
-/
theorem form_smul_mem (hM : IsMultigrading ι M piece) {b : K → ℕ} {f : MRing ι F}
    (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) b) {m : K → ℤ} {y : M}
    (hy : y ∈ piece m) : f • y ∈ piece (m + fun k => (b k : ℤ)) := by
  rw [f.as_sum, Finset.sum_smul]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight (blockWeight ι) d = b :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp hf (mem_support_iff.mp hd)
  have h := monomial_smul_mem hM d (coeff d f) hy
  rwa [hw] at h

def comp [DirectSum.Decomposition piece] (m : K → ℤ) : M →ₗ[F] M :=
  (piece m).subtype ∘ₗ DirectSum.component F (K → ℤ) (fun i => piece i) m ∘ₗ
    (DirectSum.decomposeLinearEquiv piece).toLinearMap

omit [DecidableEq K] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem comp_apply [DirectSum.Decomposition piece] (m : K → ℤ) (y : M) :
    comp (piece := piece) m y = (DirectSum.decompose piece y m : M) := rfl

open Classical in

/- English proof (translation)
Use `conv_lhs => rw [s.as_sum]`. Rewrite using `[Finset.sum_smul, map_sum, Finset.sum_filter, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Establish `h` using `monomial_smul_mem hM d (coeff d s) hx`. Rewrite using `[comp_apply]`.

Use `split_ifs with hd`. Rewrite `h` using `[hd, add_sub_cancel]`. Conclude with `DirectSum.decompose_of_mem_same piece h`. Rewrite using `[zero_smul]`. Use `DirectSum.decompose_of_mem_ne piece h fun h' => hd ?_` and prove the remaining obligations.

Rewrite using `[← h', add_sub_cancel_left]`.
-/
theorem comp_smul (hM : IsMultigrading ι M piece) [DirectSum.Decomposition piece] {c : K → ℤ}
    {x : M} (hx : x ∈ piece c) (s : MRing ι F) (m : K → ℤ) :
    comp (piece := piece) m (s • x) =
      (∑ d ∈ s.support with (fun k => (Finsupp.weight (blockWeight ι) d k : ℤ)) = m - c,
        monomial d (coeff d s)) • x := by
  conv_lhs => rw [s.as_sum]
  rw [Finset.sum_smul, map_sum, Finset.sum_filter, Finset.sum_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h := monomial_smul_mem hM d (coeff d s) hx
  rw [comp_apply]
  split_ifs with hd
  · rw [hd, add_sub_cancel] at h
    exact DirectSum.decompose_of_mem_same piece h
  · rw [zero_smul]
    refine DirectSum.decompose_of_mem_ne piece h fun h' => hd ?_
    rw [← h', add_sub_cancel_left]

/- English proof (translation)
Take `⟨s, rfl⟩` from `Submodule.mem_span_singleton.mp hy`. Rewrite using `[comp_smul hM hx]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)`.
-/
theorem comp_mem_span (hM : IsMultigrading ι M piece) [DirectSum.Decomposition piece]
    {c : K → ℤ} {x : M} (hx : x ∈ piece c) {y : M}
    (hy : y ∈ Submodule.span (MRing ι F) {x}) (m : K → ℤ) :
    comp (piece := piece) m y ∈ Submodule.span (MRing ι F) {x} := by
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [comp_smul hM hx]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

omit [DecidableEq K] [IsScalarTower F (MRing ι F) M] in

/- English proof (translation)
Introduce `y hy m`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (h₁ a ha m) (h₂ b hb m)`.
-/
theorem comp_mem_sup [DirectSum.Decomposition piece] {N₁ N₂ : Submodule (MRing ι F) M}
    (h₁ : ∀ y ∈ N₁, ∀ m, comp (piece := piece) m y ∈ N₁)
    (h₂ : ∀ y ∈ N₂, ∀ m, comp (piece := piece) m y ∈ N₂) :
    ∀ y ∈ N₁ ⊔ N₂, ∀ m, comp (piece := piece) m y ∈ N₁ ⊔ N₂ := by
  intro y hy m
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add]
  exact Submodule.add_mem_sup (h₁ a ha m) (h₂ b hb m)

open Classical in

/- English proof (translation)
Use `set A := N.restrictScalars F ⊓ piece m with hA`. Establish `hNN' : N ≤ N'` using `hN' ▸ le_sup_left`. Establish `hAB : A ≤ N'.restrictScalars F ⊓ piece m` using `inf_le_inf_right _ hNN'`. Establish `hdec : ∀ y ∈ N'.restrictScalars F ⊓ piece m, ∃ n ∈ A, ∃ s : MRing ι F, y = n + comp (piece` using `piece) m (s • x) := by`. Introduce `y hy`.

Take `⟨hy1, hy2⟩` from `Submodule.mem_inf.mp hy`. Rewrite `hy1` using `[Submodule.restrictScalars_mem, hN']`. Take `⟨n, hn, z, hz, rfl⟩` from `Submodule.mem_sup.mp hy1`. Take `⟨s, rfl⟩` from `Submodule.mem_span_singleton.mp hz`. Use `⟨comp (piece := piece) m n, Submodule.mem_inf.mpr ⟨hgr n hn m, ?_⟩, s, ?_⟩` and prove the remaining obligations.

Rewrite using `[comp_apply]`. Conclude with `Submodule.coe_mem _`. Establish `h` using `DirectSum.decompose_of_mem_same piece hy2`. Rewrite `h` using `[← comp_apply]`. Rewrite using `[← map_add, h]`.

Distinguish the cases in `hb : ∀ k, 0 ≤ (m - c) k`. Use `set b : K → ℕ := fun k => ((m - c) k).toNat with hbdef`. Establish `hbm : m = c + fun k => (b k : ℤ)`. Use function extensionality and compare the values at `k`. Use `hb k` as an intermediate fact.

Simplify using `only [Pi.sub_apply] at this`. Simplify using `only [hbdef, Pi.add_apply, Pi.sub_apply]`. Use linear arithmetic over natural numbers and integers. Set `ψ : MRing ι F →ₗ[F] M` to `(LinearMap.toSpanSingleton (MRing ι F) M x).restrictScalars F`. Establish `hψ : ∀ s, ψ s = s • x` using `fun s => rfl`.

Use `set P := weightedHomogeneousSubmodule F (blockWeight ι) b with hP`. Use `set Q := P ⊓ q.restrictScalars F with hQ`. Establish `hPm : ∀ s ∈ P, s • x ∈ piece m`. Introduce `s hs`. Establish `h` using `form_smul_mem hM hs hx`.

Rewrite `h` using `[← hbm]`. Then use the resulting hypothesis. Establish `hsup : N'.restrictScalars F ⊓ piece m = A ⊔ P.map ψ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Take `⟨n, hn, s, rfl⟩` from `hdec y hy`.

Use `Submodule.add_mem_sup hn ⟨weightedHomogeneousComponent (blockWeight ι) b s, weightedHomogeneousComponent_mem _ s b, ?_⟩` and prove the remaining obligations. Rewrite using `[hψ, comp_smul hM hx, weightedHomogeneousComponent_apply]`. Use `congr 1`. Use `Finset.sum_congr (Finset.filter_congr fun d _ => ?_) fun _ _ => rfl` and prove the remaining obligations. Establish `h2 : ∀ k, 0 ≤ m k - c k` using `fun k => by simpa using hb k`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `k`. Use `show ((Finsupp.weight (blockWeight ι) d k : ℕ) : ℤ) = m k - c k`. Rewrite using `[h, hbdef]`.

Simplify using `only [Pi.sub_apply]`. Use `h2 k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `h`. Use function extensionality and compare the values at `k`.

Establish `h1 : ((Finsupp.weight (blockWeight ι) d k : ℕ) : ℤ) = m k - c k`. Simplify using `using congrFun h k`. Rewrite using `[hbdef]`. Use `show Finsupp.weight (blockWeight ι) d k = ((m - c) k).toNat`. Rewrite using `[Pi.sub_apply]`.

Use linear arithmetic over natural numbers and integers. Use `sup_le hAB ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem, hψ, hN']`.

Conclude with `Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))`. Conclude with `hPm s hs`. Establish `hinf : A ⊓ P.map ψ = Q.map ψ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨hA', ⟨s, hs, rfl⟩⟩`.

Use `⟨s, Submodule.mem_inf.mpr ⟨hs, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem, ← hq, ← hψ]`. Conclude with `(Submodule.mem_inf.mp hA').1`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Take `⟨hs1, hs2⟩` from `Submodule.mem_inf.mp hs`.

Use `Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ⟨s, hs1, rfl⟩⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem, hψ, hq]`. Conclude with `hs2`. Rewrite using `[hψ]`. Conclude with `hPm s hs1`.

Establish `: FiniteDimensional F P` using `FiltrationStepHilb.finiteDimensional_piece b`. Establish `e1` using `Submodule.finrank_sup_add_finrank_inf_eq A (P.map ψ)`. Establish `k1` using `LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict P)`. Establish `k2` using `LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict Q)`. Rewrite `k1`, `k2` using `[LinearMap.range_domRestrict]`.

Establish `hker : ∀ R : Submodule F (MRing ι F), Module.finrank F ↥(LinearMap.ker (ψ.domRestrict R)) = Module.finrank F ↥(R ⊓ LinearMap.ker ψ)`. Introduce `R`. Rewrite using `[LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]`. Establish `hPQ : P ⊓ LinearMap.ker ψ = Q ⊓ LinearMap.ker ψ`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `s hs`. Take `⟨hs1, hs2⟩` from `Submodule.mem_inf.mp hs`. Use `Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hs1, ?_⟩, hs2⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem, ← hq, ← hψ, LinearMap.mem_ker.mp hs2]`. Conclude with `N.zero_mem`.

Conclude with `inf_le_inf_right _ inf_le_left`. Rewrite `k1` using `[hker, hPQ]`. Rewrite `k2` using `[hker]`. Establish `hq'` using `GradedPieceQuot.proof F K ι q b`. Establish `hhilb : hilbFn q (m - c) = (Module.finrank F ↥(gradedPiece q b) : ℤ)`.

Unfold `hilbFn`. Rewrite using `[if_pos hb]`. Rewrite `*` using `[hsup, hinf]`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Establish `key : (Module.finrank F ↥(A ⊔ P.map ψ) : ℤ) = Module.finrank F A + (Module.finrank F P - Module.finrank F Q)`.

Establish `k1' : Module.finrank F ↥(P.map ψ) + Module.finrank F ↥(Q ⊓ LinearMap.ker ψ) = Module.finrank F P` using `k1`. Establish `k2' : Module.finrank F ↥(Q.map ψ) + Module.finrank F ↥(Q ⊓ LinearMap.ker ψ) = Module.finrank F Q` using `k2`. Establish `e1' : Module.finrank F ↥(A ⊔ P.map ψ) + Module.finrank F ↥(Q.map ψ) = Module.finrank F A + Module.finrank F ↥(P.map ψ)` using `e1`. Use `clear k1 k2 e1 hq' hhilb`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hhilb, hq', key]`. Establish `hsup : N'.restrictScalars F ⊓ piece m = A`. Use `le_antisymm (fun y hy => ?_) hAB` and prove the remaining obligations. Take `⟨n, hn, s, rfl⟩` from `hdec y hy`. Rewrite using `[comp_smul hM hx, Finset.filter_false_of_mem, Finset.sum_empty, zero_smul, add_zero]`.

Conclude with `hn`. Introduce `d _ h`. Use `hb fun k => ?_` and prove the remaining obligations. Rewrite using `[← h]`. Conclude with `Int.natCast_nonneg _`.

Establish `hhilb : hilbFn q (m - c) = 0`. Unfold `hilbFn`. Rewrite using `[if_neg hb]`. Rewrite using `[hsup, hhilb, add_zero]`. Conclude with `⟨inferInstance, rfl⟩`.
-/
theorem step [∀ k, Fintype (ι k)] (hM : IsMultigrading ι M piece) [DirectSum.Decomposition piece]
    {N N' : Submodule (MRing ι F) M} {x : M} {c : K → ℤ} {q : Ideal (MRing ι F)}
    (hx : x ∈ piece c) (hN' : N' = N ⊔ Submodule.span (MRing ι F) {x})
    (hq : ∀ s : MRing ι F, s • x ∈ N ↔ s ∈ q)
    (hgr : ∀ y ∈ N, ∀ m, comp (piece := piece) m y ∈ N) (m : K → ℤ)
    [FiniteDimensional F ↥(N.restrictScalars F ⊓ piece m)] :
    FiniteDimensional F ↥(N'.restrictScalars F ⊓ piece m) ∧
      (Module.finrank F ↥(N'.restrictScalars F ⊓ piece m) : ℤ) =
        Module.finrank F ↥(N.restrictScalars F ⊓ piece m) + hilbFn q (m - c) := by
  set A := N.restrictScalars F ⊓ piece m with hA
  have hNN' : N ≤ N' := hN' ▸ le_sup_left
  have hAB : A ≤ N'.restrictScalars F ⊓ piece m := inf_le_inf_right _ hNN'
  have hdec : ∀ y ∈ N'.restrictScalars F ⊓ piece m, ∃ n ∈ A, ∃ s : MRing ι F,
      y = n + comp (piece := piece) m (s • x) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
    rw [Submodule.restrictScalars_mem, hN'] at hy1
    obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨comp (piece := piece) m n, Submodule.mem_inf.mpr ⟨hgr n hn m, ?_⟩, s, ?_⟩
    · rw [comp_apply]
      exact Submodule.coe_mem _
    · have h := DirectSum.decompose_of_mem_same piece hy2
      rw [← comp_apply] at h
      rw [← map_add, h]
  by_cases hb : ∀ k, 0 ≤ (m - c) k
  · set b : K → ℕ := fun k => ((m - c) k).toNat with hbdef
    have hbm : m = c + fun k => (b k : ℤ) := by
      funext k
      have := hb k
      simp only [Pi.sub_apply] at this
      simp only [hbdef, Pi.add_apply, Pi.sub_apply]
      omega
    let ψ : MRing ι F →ₗ[F] M := (LinearMap.toSpanSingleton (MRing ι F) M x).restrictScalars F
    have hψ : ∀ s, ψ s = s • x := fun s => rfl
    set P := weightedHomogeneousSubmodule F (blockWeight ι) b with hP
    set Q := P ⊓ q.restrictScalars F with hQ
    have hPm : ∀ s ∈ P, s • x ∈ piece m := by
      intro s hs
      have h := form_smul_mem hM hs hx
      rwa [← hbm] at h
    have hsup : N'.restrictScalars F ⊓ piece m = A ⊔ P.map ψ := by
      apply le_antisymm
      · intro y hy
        obtain ⟨n, hn, s, rfl⟩ := hdec y hy
        refine Submodule.add_mem_sup hn ⟨weightedHomogeneousComponent (blockWeight ι) b s,
          weightedHomogeneousComponent_mem _ s b, ?_⟩
        rw [hψ, comp_smul hM hx, weightedHomogeneousComponent_apply]
        congr 1
        refine Finset.sum_congr (Finset.filter_congr fun d _ => ?_) fun _ _ => rfl
        have h2 : ∀ k, 0 ≤ m k - c k := fun k => by simpa using hb k
        constructor
        · intro h
          funext k
          show ((Finsupp.weight (blockWeight ι) d k : ℕ) : ℤ) = m k - c k
          rw [h, hbdef]
          simp only [Pi.sub_apply]
          have := h2 k
          omega
        · intro h
          funext k
          have h1 : ((Finsupp.weight (blockWeight ι) d k : ℕ) : ℤ) = m k - c k := by
            simpa using congrFun h k
          rw [hbdef]
          show Finsupp.weight (blockWeight ι) d k = ((m - c) k).toNat
          rw [Pi.sub_apply]
          omega
      · refine sup_le hAB ?_
        rintro _ ⟨s, hs, rfl⟩
        refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
        · rw [Submodule.restrictScalars_mem, hψ, hN']
          exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
        · exact hPm s hs
    have hinf : A ⊓ P.map ψ = Q.map ψ := by
      apply le_antisymm
      · rintro _ ⟨hA', ⟨s, hs, rfl⟩⟩
        refine ⟨s, Submodule.mem_inf.mpr ⟨hs, ?_⟩, rfl⟩
        rw [Submodule.restrictScalars_mem, ← hq, ← hψ]
        exact (Submodule.mem_inf.mp hA').1
      · rintro _ ⟨s, hs, rfl⟩
        obtain ⟨hs1, hs2⟩ := Submodule.mem_inf.mp hs
        refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ⟨s, hs1, rfl⟩⟩
        · rw [Submodule.restrictScalars_mem, hψ, hq]
          exact hs2
        · rw [hψ]
          exact hPm s hs1
    have : FiniteDimensional F P := FiltrationStepHilb.finiteDimensional_piece b
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq A (P.map ψ)
    have k1 := LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict P)
    have k2 := LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict Q)
    rw [LinearMap.range_domRestrict] at k1 k2
    have hker : ∀ R : Submodule F (MRing ι F), Module.finrank F ↥(LinearMap.ker (ψ.domRestrict R)) =
        Module.finrank F ↥(R ⊓ LinearMap.ker ψ) := by
      intro R
      rw [LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
    have hPQ : P ⊓ LinearMap.ker ψ = Q ⊓ LinearMap.ker ψ := by
      apply le_antisymm
      · intro s hs
        obtain ⟨hs1, hs2⟩ := Submodule.mem_inf.mp hs
        refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hs1, ?_⟩, hs2⟩
        rw [Submodule.restrictScalars_mem, ← hq, ← hψ, LinearMap.mem_ker.mp hs2]
        exact N.zero_mem
      · exact inf_le_inf_right _ inf_le_left
    rw [hker, hPQ] at k1
    rw [hker] at k2
    have hq' := GradedPieceQuot.proof F K ι q b
    have hhilb : hilbFn q (m - c) = (Module.finrank F ↥(gradedPiece q b) : ℤ) := by
      unfold hilbFn
      rw [if_pos hb]
    rw [hsup, hinf] at *
    refine ⟨inferInstance, ?_⟩
    have key : (Module.finrank F ↥(A ⊔ P.map ψ) : ℤ) =
        Module.finrank F A + (Module.finrank F P - Module.finrank F Q) := by
      have k1' : Module.finrank F ↥(P.map ψ) + Module.finrank F ↥(Q ⊓ LinearMap.ker ψ) =
          Module.finrank F P := k1
      have k2' : Module.finrank F ↥(Q.map ψ) + Module.finrank F ↥(Q ⊓ LinearMap.ker ψ) =
          Module.finrank F Q := k2
      have e1' : Module.finrank F ↥(A ⊔ P.map ψ) + Module.finrank F ↥(Q.map ψ) =
          Module.finrank F A + Module.finrank F ↥(P.map ψ) := e1
      clear k1 k2 e1 hq' hhilb
      omega
    rw [hhilb, hq', key]
  · have hsup : N'.restrictScalars F ⊓ piece m = A := by
      refine le_antisymm (fun y hy => ?_) hAB
      obtain ⟨n, hn, s, rfl⟩ := hdec y hy
      rw [comp_smul hM hx, Finset.filter_false_of_mem, Finset.sum_empty, zero_smul, add_zero]
      · exact hn
      · intro d _ h
        refine hb fun k => ?_
        rw [← h]
        exact Int.natCast_nonneg _
    have hhilb : hilbFn q (m - c) = 0 := by
      unfold hilbFn
      rw [if_neg hb]
    rw [hsup, hhilb, add_zero]
    exact ⟨inferInstance, rfl⟩

end FiltrationHilbSum

/- English proof (translation)
Introduce `F _ K _ _ ι _ M _ _ _ _ piece hM n N x c q h0 hlast hstep m`. Use `letI : DirectSum.Decomposition piece := hM.internal.chooseDecomposition`. Establish `hgr : ∀ (i : ℕ) (hi : i < n + 1), ∀ y ∈ N ⟨i, hi⟩, ∀ m', FiltrationHilbSum.comp (piece` using `piece) m' y ∈ N ⟨i, hi⟩ := by`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero`. Introduce `hi y hy m'`. Establish `hN0 : N ⟨0, hi⟩ = ⊥` using `h0`. Rewrite `hy`, the goal using `[hN0, Submodule.mem_bot]`. Rewrite using `[hy, map_zero]`.

Consider the case `succ i ih`. Introduce `hi`. Establish `hi' : i < n` using `by omega`. Take `⟨hx, hN', -⟩` from `hstep ⟨i, hi'⟩`. Establish `e1 : (⟨i, hi'⟩ : Fin n).succ = ⟨i + 1, hi⟩` using `rfl`.

Establish `e2 : (⟨i, hi'⟩ : Fin n).castSucc = ⟨i, by omega⟩` using `rfl`. Rewrite `hN'` using `[e1, e2]`. Rewrite using `[hN']`. Conclude with `FiltrationHilbSum.comp_mem_sup (ih _) (fun y hy m' => FiltrationHilbSum.comp_mem_span hM hx hy m')`. Establish `hcount : ∀ (i : ℕ) (hi : i < n + 1), FiniteDimensional F ↥((N ⟨i, hi⟩).restrictScalars F ⊓ piece m) ∧ (Module.finrank F ↥((N ⟨i, hi⟩).restrictScalars F ⊓ piece m) : ℤ) = ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i), hilbFn (q j) (m - c j)`.

Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `hi`. Establish `hN0 : N ⟨0, hi⟩ = ⊥` using `h0`.

Rewrite using `[hN0, Submodule.restrictScalars_bot, bot_inf_eq]`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[finrank_bot, Finset.filter_false_of_mem (fun j _ => Nat.not_lt_zero _), Finset.sum_empty]`. Both sides reduce to the same expression. Consider the case `succ i ih`.

Introduce `hi`. Establish `hi' : i < n` using `by omega`. Take `⟨hfd, hr⟩` from `ih (by omega)`. Take `⟨hx, hN', hq⟩` from `hstep ⟨i, hi'⟩`. Establish `e1 : (⟨i, hi'⟩ : Fin n).succ = ⟨i + 1, hi⟩` using `rfl`.

Establish `e2 : (⟨i, hi'⟩ : Fin n).castSucc = ⟨i, by omega⟩` using `rfl`. Rewrite `hN'` using `[e1, e2]`. Rewrite `hq` using `[e2]`. Take `⟨h1, h2⟩` from `FiltrationHilbSum.step hM hx hN' hq (hgr i (by omega)) m`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[h2, hr]`. Establish `hset : Finset.univ.filter (fun j : Fin n => j.val < i + 1) = insert ⟨i, hi'⟩ (Finset.univ.filter (fun j : Fin n => j.val < i))`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hset, Finset.sum_insert (by simp)]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨-, h⟩` from `hcount n (by omega)`. Establish `hN : N ⟨n, by omega⟩ = ⊤` using `hlast`. Rewrite `h` using `[hN, Submodule.restrictScalars_top, top_inf_eq]`.

Rewrite using `[h, Finset.filter_true_of_mem (fun j _ => j.isLt)]`.
-/
theorem FiltrationHilbSum.proof : FiltrationHilbSum.Statement.{u, v} := by
  intro F _ K _ _ ι _ M _ _ _ _ piece hM n N x c q h0 hlast hstep m
  classical
  letI : DirectSum.Decomposition piece := hM.internal.chooseDecomposition
  have hgr : ∀ (i : ℕ) (hi : i < n + 1), ∀ y ∈ N ⟨i, hi⟩, ∀ m',
      FiltrationHilbSum.comp (piece := piece) m' y ∈ N ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi y hy m'
      have hN0 : N ⟨0, hi⟩ = ⊥ := h0
      rw [hN0, Submodule.mem_bot] at hy ⊢
      rw [hy, map_zero]
    | succ i ih =>
      intro hi
      have hi' : i < n := by omega
      obtain ⟨hx, hN', -⟩ := hstep ⟨i, hi'⟩
      have e1 : (⟨i, hi'⟩ : Fin n).succ = ⟨i + 1, hi⟩ := rfl
      have e2 : (⟨i, hi'⟩ : Fin n).castSucc = ⟨i, by omega⟩ := rfl
      rw [e1, e2] at hN'
      rw [hN']
      exact FiltrationHilbSum.comp_mem_sup (ih _) (fun y hy m' =>
        FiltrationHilbSum.comp_mem_span hM hx hy m')
  have hcount : ∀ (i : ℕ) (hi : i < n + 1),
      FiniteDimensional F ↥((N ⟨i, hi⟩).restrictScalars F ⊓ piece m) ∧
        (Module.finrank F ↥((N ⟨i, hi⟩).restrictScalars F ⊓ piece m) : ℤ) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i), hilbFn (q j) (m - c j) := by
    intro i
    induction i with
    | zero =>
      intro hi
      have hN0 : N ⟨0, hi⟩ = ⊥ := h0
      rw [hN0, Submodule.restrictScalars_bot, bot_inf_eq]
      refine ⟨inferInstance, ?_⟩
      rw [finrank_bot, Finset.filter_false_of_mem (fun j _ => Nat.not_lt_zero _), Finset.sum_empty]
      rfl
    | succ i ih =>
      intro hi
      have hi' : i < n := by omega
      obtain ⟨hfd, hr⟩ := ih (by omega)
      obtain ⟨hx, hN', hq⟩ := hstep ⟨i, hi'⟩
      have e1 : (⟨i, hi'⟩ : Fin n).succ = ⟨i + 1, hi⟩ := rfl
      have e2 : (⟨i, hi'⟩ : Fin n).castSucc = ⟨i, by omega⟩ := rfl
      rw [e1, e2] at hN'
      rw [e2] at hq
      obtain ⟨h1, h2⟩ := FiltrationHilbSum.step hM hx hN' hq (hgr i (by omega)) m
      refine ⟨h1, ?_⟩
      rw [h2, hr]
      have hset : Finset.univ.filter (fun j : Fin n => j.val < i + 1) =
          insert ⟨i, hi'⟩ (Finset.univ.filter (fun j : Fin n => j.val < i)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hset, Finset.sum_insert (by simp)]
      ring
  obtain ⟨-, h⟩ := hcount n (by omega)
  have hN : N ⟨n, by omega⟩ = ⊤ := hlast
  rw [hN, Submodule.restrictScalars_top, top_inf_eq] at h
  rw [h, Finset.filter_true_of_mem (fun j _ => j.isLt)]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
